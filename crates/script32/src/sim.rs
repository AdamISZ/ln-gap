//! A tiny interpreter for the opcode subset these gadgets emit, for fast
//! native debugging (the regtest tests remain the source of truth).
//! Elements are small script numbers.

use bitcoin::opcodes::all::*;
use bitcoin::opcodes::Opcode;
use bitcoin::script::{Instruction, Script};

fn decode(v: &[u8]) -> i64 {
    if v.is_empty() {
        return 0;
    }
    let mut r: i64 = 0;
    for (i, b) in v.iter().enumerate() {
        r |= i64::from(*b & if i == v.len() - 1 { 0x7f } else { 0xff }) << (8 * i);
    }
    if v[v.len() - 1] & 0x80 != 0 { -r } else { r }
}

/// Run `script` on `stack` (top = last). Returns the final main stack or an error string.
pub fn run(script: &Script, stack: Vec<i64>) -> Result<Vec<i64>, String> {
    run_trace(script, stack, false)
}

/// Like [`run`]; with `trace` set, print the top of both stacks after every instruction.
pub fn run_trace(script: &Script, mut stack: Vec<i64>, trace: bool) -> Result<Vec<i64>, String> {
    let mut alt: Vec<i64> = Vec::new();
    let mut skip: Vec<bool> = Vec::new(); // IF nesting: true when skipping
    let pop = |s: &mut Vec<i64>| s.pop().ok_or_else(|| "stack underflow".to_string());
    for (pc, ins) in script.instructions().enumerate() {
        let ins = ins.map_err(|e| e.to_string())?;
        if trace {
            let n = stack.len();
            eprintln!("{pc:5} {ins:?}  main[{n}] top {:?}  alt {:?}", &stack[n.saturating_sub(12)..], &alt[alt.len().saturating_sub(8)..]);
        }
        let skipping = skip.iter().any(|s| *s);
        match ins {
            Instruction::PushBytes(pb) => {
                if !skipping {
                    stack.push(decode(pb.as_bytes()));
                }
            }
            Instruction::Op(op) => {
                if op == OP_IF {
                    if skipping {
                        skip.push(true);
                    } else {
                        let c = pop(&mut stack)?;
                        skip.push(c == 0);
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
                    stack.push(i64::from(n - OP_PUSHNUM_1.to_u8()) + 1);
                    continue;
                }
                if op == OP_PUSHNUM_NEG1 {
                    stack.push(-1);
                    continue;
                }
                let err = |o: Opcode, pc: usize| format!("{o:?} failed at instruction {pc}");
                match op {
                    OP_DUP => { let a = *stack.last().ok_or("underflow")?; stack.push(a); }
                    OP_DROP => { pop(&mut stack)?; }
                    OP_2DROP => { pop(&mut stack)?; pop(&mut stack)?; }
                    OP_SWAP => { let l = stack.len(); if l < 2 { return Err("underflow".into()); } stack.swap(l - 1, l - 2); }
                    OP_ROT => { let l = stack.len(); if l < 3 { return Err("underflow".into()); } let x = stack.remove(l - 3); stack.push(x); }
                    OP_TUCK => { let l = stack.len(); if l < 2 { return Err("underflow".into()); } let top = stack[l - 1]; stack.insert(l - 2, top); }
                    OP_OVER => { let l = stack.len(); if l < 2 { return Err("underflow".into()); } stack.push(stack[l - 2]); }
                    OP_PICK | OP_ROLL => {
                        let d = pop(&mut stack)?;
                        if d < 0 || d as usize >= stack.len() { return Err(format!("{op:?} depth {d} out of range (len {}) at {pc}", stack.len())); }
                        let idx = stack.len() - 1 - d as usize;
                        let v = if op == OP_PICK { stack[idx] } else { stack.remove(idx) };
                        stack.push(v);
                    }
                    OP_ADD => { let b = pop(&mut stack)?; let a = pop(&mut stack)?; stack.push(a + b); }
                    OP_SUB => { let b = pop(&mut stack)?; let a = pop(&mut stack)?; stack.push(a - b); }
                    OP_GREATERTHANOREQUAL => { let b = pop(&mut stack)?; let a = pop(&mut stack)?; stack.push(i64::from(a >= b)); }
                    OP_LESSTHAN => { let b = pop(&mut stack)?; let a = pop(&mut stack)?; stack.push(i64::from(a < b)); }
                    OP_NUMEQUAL | OP_EQUAL => { let b = pop(&mut stack)?; let a = pop(&mut stack)?; stack.push(i64::from(a == b)); }
                    OP_NUMEQUALVERIFY | OP_EQUALVERIFY => {
                        let b = pop(&mut stack)?; let a = pop(&mut stack)?;
                        if a != b { return Err(format!("{} ({a} vs {b}, stack {:?})", err(op, pc), &stack[stack.len().saturating_sub(12)..])); }
                    }
                    OP_TOALTSTACK => { alt.push(pop(&mut stack)?); }
                    OP_FROMALTSTACK => { stack.push(alt.pop().ok_or("alt underflow")?); }
                    _ => return Err(format!("unsupported opcode {op:?} at {pc}")),
                }
            }
        }
    }
    Ok(stack)
}
