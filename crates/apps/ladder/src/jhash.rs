//! Step-hash checks for a jump list: `h(i) = BLAKE3(h(i-1) || h(jump(i))
//! || write_i || i)[..20]`, 57 bytes in one block (BitVMX's BLAKE3 gadget).

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use bitcoin_script_functions::hash::blake3;
use bitcoin_script_stack::stack::StackTracker;

/// Bytes a jump-list step hash covers.
pub const PREIMAGE_BYTES: usize = 57;

/// `[prev 40, jump 40, hash 40, write_addr 8, write_value 8, write_pc 8,
/// write_micro 2, step 8]` (nibbles): fails unless `hash` is the step hash
/// of the rest. Consumes them all. The inputs must be alone on the main
/// stack (BitVMX's gadget finds its tables by OP_DEPTH).
pub fn step_hash_jump_script() -> ScriptBuf {
    static S: std::sync::OnceLock<ScriptBuf> = std::sync::OnceLock::new();
    S.get_or_init(|| {
        let mut st = StackTracker::new();
        let prev = st.define(40, "prev");
        let jump = st.define(40, "jump");
        let hash = st.define(40, "hash");
        let wa = st.define(8, "write_add");
        let wd = st.define(8, "write_data");
        let wp = st.define(8, "write_pc");
        let wm = st.define(2, "write_micro");
        let step = st.define(8, "step");
        st.move_var(hash);
        st.to_altstack();
        for v in [prev, jump, wa, wd, wp, wm, step] {
            st.explode(v);
        }
        let result = blake3::blake3(&mut st, PREIMAGE_BYTES as u32, 5);
        let claimed = st.from_altstack();
        st.equals(result, true, claimed, true);
        st.get_script()
    })
    .clone()
}

/// The program-counter check under a jump list: `[prev 40, jump 40,
/// write_addr 8, write_value 8, write_pc 8, write_micro_hi 1,
/// write_micro_lo 1, t 8, read_pc 8, read_micro 1, hash 40]`: fails unless
/// `hash` (Alice's hash after step `t`) is the step hash of step `t` with
/// that write, AND step `t`'s next pc and micro-step aren't the ones the
/// disputed step read. Consumes them all; the inputs must be alone on the
/// main stack.
pub fn program_counter_jump_script() -> ScriptBuf {
    static S: std::sync::OnceLock<ScriptBuf> = std::sync::OnceLock::new();
    S.get_or_init(|| {
        // park the hash; compare (read_pc, read_micro) with (write_pc,
        // write_micro_lo): from the top, read_micro, then read_pc's nibbles
        // last first, each against the written one at a constant depth
        let mut b = Builder::new();
        for _ in 0..40 {
            b = b.push_opcode(OP_TOALTSTACK);
        }
        b = b.push_int(17).push_opcode(OP_PICK).push_opcode(OP_EQUAL);
        for _ in 0..8 {
            b = b.push_opcode(OP_SWAP).push_int(19).push_opcode(OP_PICK).push_opcode(OP_EQUAL).push_opcode(OP_BOOLAND);
        }
        b = b.push_opcode(OP_NOT).push_opcode(OP_VERIFY);
        for _ in 0..40 {
            b = b.push_opcode(OP_FROMALTSTACK);
        }
        // [prev, jump, wa, wd, wp, wm_hi, wm_lo, t, hash]: Alice's hash after
        // step t is step t's
        let mut st = StackTracker::new();
        let prev = st.define(40, "prev");
        let jump = st.define(40, "jump");
        let wa = st.define(8, "write_add");
        let wd = st.define(8, "write_data");
        let wp = st.define(8, "write_pc");
        let wm = st.define(2, "write_micro");
        let t = st.define(8, "t");
        let hash = st.define(40, "hash");
        st.move_var(hash);
        st.to_altstack();
        for v in [prev, jump, wa, wd, wp, wm, t] {
            st.explode(v);
        }
        let result = blake3::blake3(&mut st, PREIMAGE_BYTES as u32, 5);
        let claimed = st.from_altstack();
        st.equals(result, true, claimed, true);
        let mut bytes = b.into_script().into_bytes();
        bytes.extend_from_slice(st.get_script().as_bytes());
        ScriptBuf::from_bytes(bytes)
    })
    .clone()
}

/// A jump-list step hash, natively.
pub fn step_hash_jump(prev: &[u8; 20], jump: &[u8; 20], write: &lngap_zk::Step, step: u32) -> [u8; 20] {
    let mut b = prev.to_vec();
    b.extend_from_slice(jump);
    b.extend_from_slice(&write.to_bytes());
    b.extend_from_slice(&step.to_be_bytes());
    lngap_zk::blake3_160(&b)
}

/// A step's preimage (57 bytes): the hash before, the long jump's, the
/// write, the step.
pub fn preimage(prev: &[u8; 20], jump: &[u8; 20], write: &lngap_zk::Step, step: u32) -> Vec<u8> {
    let mut b = prev.to_vec();
    b.extend_from_slice(jump);
    b.extend_from_slice(&write.to_bytes());
    b.extend_from_slice(&step.to_be_bytes());
    b
}

#[allow(dead_code)]
fn _unused(b: Builder) -> Builder {
    b.push_opcode(OP_NOP)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::spends;
    use crate::script::nibbles;

    #[test]
    fn the_step_hash_checks() {
        let (prev, jump) = ([3u8; 20], [9u8; 20]);
        let w = lngap_zk::Step { write_addr: 0xf000_0004, write_value: 77, pc: 0x8000_0010, micro: 0 };
        let h = step_hash_jump(&prev, &jump, &w, 1234);
        let wire = |hash: &[u8; 20], step: u32| -> Vec<Vec<u8>> {
            let mut b = prev.to_vec();
            b.extend_from_slice(&jump);
            b.extend_from_slice(hash);
            b.extend_from_slice(&w.to_bytes());
            b.extend_from_slice(&step.to_be_bytes());
            nibbles(&b)
        };
        let s = Builder::from(step_hash_jump_script().into_bytes()).push_opcode(OP_PUSHNUM_1).into_script();
        let (ok, peak) = spends(&s, wire(&h, 1234));
        assert!(ok, "the hash holds (peak {peak})");
        assert!(!spends(&s, wire(&h, 1235)).0, "another step");
        println!("JHASH step hash: {} bytes, peak {peak}", s.len());
    }

    #[test]
    fn the_program_counter_checks() {
        let (prev, jump) = ([3u8; 20], [9u8; 20]);
        let w = lngap_zk::Step { write_addr: 0xf000_0004, write_value: 77, pc: 0x8000_0010, micro: 0 };
        let h = step_hash_jump(&prev, &jump, &w, 41);
        let wire = |hash: &[u8; 20], read_pc: u32, read_micro: u8| -> Vec<Vec<u8>> {
            let mut b = prev.to_vec();
            b.extend_from_slice(&jump);
            b.extend_from_slice(&w.to_bytes()[..12]);
            let mut n = nibbles(&b);
            n.extend(nibbles(&[w.micro]));
            n.extend(nibbles(&41u32.to_be_bytes()));
            n.extend(nibbles(&read_pc.to_be_bytes()));
            n.push(if read_micro == 0 { vec![] } else { vec![read_micro] });
            n.extend(nibbles(hash));
            n
        };
        let s = Builder::from(program_counter_jump_script().into_bytes()).push_opcode(OP_PUSHNUM_1).into_script();
        let (ok, peak) = spends(&s, wire(&h, 0x8000_0014, 0));
        assert!(ok, "a different pc read fires (peak {peak})");
        assert!(!spends(&s, wire(&h, 0x8000_0010, 0)).0, "the pc written was read");
        assert!(!spends(&s, wire(&[1; 20], 0x8000_0014, 0)).0, "not Alice's hash");
        println!("JHASH program counter: {} bytes, peak {peak}", s.len());
    }
}
