//! A small interpreter for the opcode subset these leaves emit, for fast
//! native debugging (regtest remains the source of truth). Elements are
//! byte vectors with minimal script-number encoding for arithmetic.

use bitcoin::opcodes::all::*;
use bitcoin::script::{Instruction, Script};

pub fn decode(v: &[u8]) -> i64 {
    if v.is_empty() {
        return 0;
    }
    let mut r: i64 = 0;
    for (i, b) in v.iter().enumerate() {
        r |= i64::from(*b & if i == v.len() - 1 { 0x7f } else { 0xff }) << (8 * i);
    }
    if v[v.len() - 1] & 0x80 != 0 { -r } else { r }
}

pub fn encode(mut n: i64) -> Vec<u8> {
    if n == 0 {
        return vec![];
    }
    let neg = n < 0;
    if neg {
        n = -n;
    }
    let mut v = Vec::new();
    while n > 0 {
        v.push((n & 0xff) as u8);
        n >>= 8;
    }
    if v[v.len() - 1] & 0x80 != 0 {
        v.push(if neg { 0x80 } else { 0 });
    } else if neg {
        let l = v.len() - 1;
        v[l] |= 0x80;
    }
    v
}

fn truthy(v: &[u8]) -> bool {
    v.iter().enumerate().any(|(i, b)| *b != 0 && !(i == v.len() - 1 && *b == 0x80))
}

/// Run `script` on `stack` (top = last). Returns the final main stack or an error string.
pub fn run(script: &Script, stack: Vec<Vec<u8>>) -> Result<Vec<Vec<u8>>, String> {
    run_trace(script, stack, false)
}

/// Convenience: numeric initial stack, numeric result.
pub fn run_nums(script: &Script, stack: Vec<i64>) -> Result<Vec<i64>, String> {
    Ok(run(script, stack.into_iter().map(encode).collect())?.iter().map(|v| decode(v)).collect())
}

/// Like [`run`]; with `trace` set, print the top of both stacks before every instruction.
pub fn run_trace(script: &Script, mut stack: Vec<Vec<u8>>, trace: bool) -> Result<Vec<Vec<u8>>, String> {
    let mut alt: Vec<Vec<u8>> = Vec::new();
    let mut skip: Vec<bool> = Vec::new();
    fn pop(s: &mut Vec<Vec<u8>>) -> Result<Vec<u8>, String> {
        s.pop().ok_or_else(|| "stack underflow".to_string())
    }
    fn popn(s: &mut Vec<Vec<u8>>) -> Result<i64, String> {
        let v = pop(s)?;
        if v.len() > 4 {
            return Err(format!("script number overflow ({} bytes)", v.len()));
        }
        Ok(decode(&v))
    }
    for (pc, ins) in script.instructions().enumerate() {
        let ins = ins.map_err(|e| e.to_string())?;
        if trace {
            let n = stack.len();
            let show = |v: &[Vec<u8>]| v.iter().map(|e| if e.len() <= 4 { decode(e).to_string() } else { format!("{}..", hex::encode(&e[..2])) }).collect::<Vec<_>>().join(" ");
            eprintln!("{pc:5} {ins:?}  main[{n}] top {}  alt[{}] {}", show(&stack[n.saturating_sub(12)..]), alt.len(), show(&alt[alt.len().saturating_sub(6)..]));
        }
        let skipping = skip.iter().any(|s| *s);
        match ins {
            Instruction::PushBytes(pb) => {
                if !skipping {
                    stack.push(pb.as_bytes().to_vec());
                }
            }
            Instruction::Op(op) => {
                if op == OP_IF || op == OP_NOTIF {
                    if skipping {
                        skip.push(true);
                    } else {
                        let v = pop(&mut stack)?;
                        // tapscript MINIMALIF: the condition must be exactly empty or 0x01
                        if !(v.is_empty() || v == [1]) {
                            return Err(format!("MINIMALIF: {op:?} on {} at instruction {pc}", hex::encode(&v)));
                        }
                        let c = truthy(&v);
                        skip.push(if op == OP_IF { !c } else { c });
                    }
                    continue;
                }
                if op == OP_ELSE {
                    let last = skip.last_mut().ok_or("ELSE without IF")?;
                    *last = !*last;
                    continue;
                }
                if op == OP_ENDIF {
                    skip.pop().ok_or("ENDIF without IF")?;
                    continue;
                }
                if skipping {
                    continue;
                }
                let n = op.to_u8();
                if (OP_PUSHNUM_1.to_u8()..=OP_PUSHNUM_16.to_u8()).contains(&n) {
                    stack.push(encode(i64::from(n - OP_PUSHNUM_1.to_u8()) + 1));
                    continue;
                }
                if op == OP_PUSHNUM_NEG1 {
                    stack.push(encode(-1));
                    continue;
                }
                let fail = |what: String| Err::<(), String>(format!("{what} at instruction {pc}"));
                match op {
                    OP_DUP => { let a = stack.last().ok_or("underflow")?.clone(); stack.push(a); }
                    OP_DROP => { pop(&mut stack)?; }
                    OP_2DROP => { pop(&mut stack)?; pop(&mut stack)?; }
                    OP_2DUP => { let l = stack.len(); if l < 2 { return Err("underflow".into()); } let (a, b) = (stack[l - 2].clone(), stack[l - 1].clone()); stack.push(a); stack.push(b); }
                    OP_SWAP => { let l = stack.len(); if l < 2 { return Err("underflow".into()); } stack.swap(l - 1, l - 2); }
                    OP_ROT => { let l = stack.len(); if l < 3 { return Err("underflow".into()); } let x = stack.remove(l - 3); stack.push(x); }
                    OP_TUCK => { let l = stack.len(); if l < 2 { return Err("underflow".into()); } let top = stack[l - 1].clone(); stack.insert(l - 2, top); }
                    OP_OVER => { let l = stack.len(); if l < 2 { return Err("underflow".into()); } stack.push(stack[l - 2].clone()); }
                    OP_NIP => { let l = stack.len(); if l < 2 { return Err("underflow".into()); } stack.remove(l - 2); }
                    OP_PICK | OP_ROLL => {
                        let d = popn(&mut stack)?;
                        if d < 0 || d as usize >= stack.len() { return Err(format!("{op:?} depth {d} out of range (len {}) at {pc}", stack.len())); }
                        let idx = stack.len() - 1 - d as usize;
                        let v = if op == OP_PICK { stack[idx].clone() } else { stack.remove(idx) };
                        stack.push(v);
                    }
                    OP_ADD => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; stack.push(encode(a + b)); }
                    OP_1ADD => { let a = popn(&mut stack)?; stack.push(encode(a + 1)); }
                    OP_1SUB => { let a = popn(&mut stack)?; stack.push(encode(a - 1)); }
                    OP_ABS => { let a = popn(&mut stack)?; stack.push(encode(a.abs())); }
                    OP_MAX => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; stack.push(encode(a.max(b))); }
                    OP_GREATERTHAN => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; stack.push(encode(i64::from(a > b))); }
                    OP_LESSTHANOREQUAL => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; stack.push(encode(i64::from(a <= b))); }
                    OP_0NOTEQUAL => { let a = popn(&mut stack)?; stack.push(encode(i64::from(a != 0))); }
                    OP_NUMNOTEQUAL => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; stack.push(encode(i64::from(a != b))); }
                    OP_WITHIN => { let max = popn(&mut stack)?; let min = popn(&mut stack)?; let x = popn(&mut stack)?; stack.push(encode(i64::from(min <= x && x < max))); }
                    OP_DEPTH => { stack.push(encode(stack.len() as i64)); }
                    OP_2SWAP => { let l = stack.len(); if l < 4 { return Err("underflow".into()); } stack.swap(l - 4, l - 2); stack.swap(l - 3, l - 1); }
                    OP_2OVER => { let l = stack.len(); if l < 4 { return Err("underflow".into()); } let (a, b) = (stack[l - 4].clone(), stack[l - 3].clone()); stack.push(a); stack.push(b); }
                    OP_3DUP => { let l = stack.len(); if l < 3 { return Err("underflow".into()); } for i in 0..3 { stack.push(stack[l - 3 + i].clone()); } }
                    OP_SUB => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; stack.push(encode(a - b)); }
                    OP_NEGATE => { let a = popn(&mut stack)?; stack.push(encode(-a)); }
                    OP_MIN => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; stack.push(encode(a.min(b))); }
                    OP_GREATERTHANOREQUAL => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; stack.push(encode(i64::from(a >= b))); }
                    OP_LESSTHAN => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; stack.push(encode(i64::from(a < b))); }
                    OP_BOOLAND => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; stack.push(encode(i64::from(a != 0 && b != 0))); }
                    OP_BOOLOR => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; stack.push(encode(i64::from(a != 0 || b != 0))); }
                    OP_NOT => { let a = popn(&mut stack)?; stack.push(encode(i64::from(a == 0))); }
                    OP_NUMEQUAL => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; stack.push(encode(i64::from(a == b))); }
                    OP_NUMEQUALVERIFY => { let b = popn(&mut stack)?; let a = popn(&mut stack)?; if a != b { fail(format!("NUMEQUALVERIFY {a} vs {b}"))?; } }
                    OP_EQUAL => { let b = pop(&mut stack)?; let a = pop(&mut stack)?; stack.push(encode(i64::from(a == b))); }
                    OP_EQUALVERIFY => {
                        let b = pop(&mut stack)?; let a = pop(&mut stack)?;
                        if a != b { fail(format!("EQUALVERIFY {} vs {} (stack depth {})", hex::encode(&a), hex::encode(&b), stack.len()))?; }
                    }
                    OP_SIZE => { let l = stack.last().ok_or("underflow")?.len(); stack.push(encode(l as i64)); }
                    OP_HASH160 => { let a = pop(&mut stack)?; stack.push(lngap_btc::hash160(&a).to_vec()); }
                    OP_SHA256 => { use sha2::Digest; let a = pop(&mut stack)?; stack.push(sha2::Sha256::digest(&a).to_vec()); }
                    OP_CHECKSIGVERIFY => { pop(&mut stack)?; pop(&mut stack)?; }
                    OP_CHECKSIG => { pop(&mut stack)?; pop(&mut stack)?; stack.push(encode(1)); }
                    OP_TOALTSTACK => { alt.push(pop(&mut stack)?); }
                    OP_FROMALTSTACK => { stack.push(alt.pop().ok_or("alt underflow")?); }
                    OP_VERIFY => { if !truthy(&pop(&mut stack)?) { fail("VERIFY".into())?; } }
                    _ => return Err(format!("unsupported opcode {op:?} at {pc}")),
                }
            }
        }
    }
    Ok(stack)
}
