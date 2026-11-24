// A tiny stack VM for make.fun's tiny-stack-vm-01 ISA (generator/subject/ISA.md), following it exactly,
// including the rules ISA.md lists as hard: wrapping MUL via Math.imul, INT_MIN / -1, the sign of MOD,
// DIVU / MODU / LTU as unsigned, shift counts masked to 5 bits, PUSH8 sign extension, EXIT's low byte,
// every trap's own exit code (2..11), the step and output limits, falling off the end as trap 9. Each
// step checks, in ISA.md's order: step limit, pc in range, known opcode, immediate fits, stack
// underflow and overflow, then the instruction's own traps and effect.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per opcode byte: imm | pops << 3 | pushes << 5 (immediate bytes, values popped, values pushed).
// -1 marks a byte no opcode names (trap 5).
const META = new Int16Array(256).fill(-1);
{
  const put = (op, imm, pops, pushes) => { META[op] = imm | (pops << 3) | (pushes << 5); };
  put(0x00, 0, 0, 0); // HALT
  put(0x01, 1, 0, 1); // PUSH8
  put(0x02, 4, 0, 1); // PUSH32
  put(0x03, 0, 1, 0); // POP
  put(0x04, 0, 1, 2); // DUP
  put(0x05, 0, 2, 2); // SWAP
  put(0x06, 0, 2, 3); // OVER
  put(0x07, 0, 3, 3); // ROT
  for (let op = 0x10; op <= 0x22; op++) if (op !== 0x1f) put(op, 0, 2, 1); // binary operators
  put(0x17, 0, 1, 1); // NEG
  put(0x1b, 0, 1, 1); // NOT
  put(0x30, 2, 0, 0); // JMP
  put(0x31, 2, 1, 0); // JZ
  put(0x32, 2, 1, 0); // JNZ
  put(0x33, 2, 0, 0); // CALL
  put(0x34, 0, 0, 0); // RET
  put(0x40, 0, 1, 1); // LOAD
  put(0x41, 0, 2, 0); // STORE
  put(0x50, 0, 1, 0); // PRINT
  put(0x51, 0, 1, 0); // PUTC
  put(0x52, 0, 0, 1); // IN
  put(0x53, 0, 1, 0); // EXIT
}

function run(P, inp) {
  const n = P.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const buf = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const done = (code) => ({ out: buf.slice(0, olen), code });
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = P[pc];
    const meta = META[op];
    if (meta < 0) return done(5);
    const imm = meta & 7;
    if (pc + imm >= n) return done(9);
    steps++;
    const pops = (meta >> 3) & 3;
    if (sp < pops) return done(2);
    if (sp - pops + ((meta >> 5) & 3) > 256) return done(3);
    const next = pc + 1 + imm;
    pc = next;
    switch (op) {
      case 0x00: // HALT
        return done(0);
      case 0x01: // PUSH8
        D[sp++] = (P[next - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32
        D[sp++] = P[next - 4] | (P[next - 3] << 8) | (P[next - 2] << 16) | (P[next - 1] << 24);
        break;
      case 0x03: // POP
        sp--;
        break;
      case 0x04: // DUP
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: { // SWAP
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 0x06: // OVER
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: { // ROT ( a b c -- b c a )
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 0x17: // NEG, wraps
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 0x1b: // NOT
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: { // binary ops ( a b -- r )
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b); // MUL, exact low 32 bits
        else if (op === 0x13) { // DIV, truncated toward zero
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) { // MOD, sign of a; x % -1 is 0
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) { // DIVU, unsigned
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) { // MODU, unsigned
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31); // SHR, arithmetic
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0; // SHRU, logical
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0; // LT, signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
        D[sp - 2] = r;
        sp--;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // jumps, signed offset from next
        const rel = ((P[next - 2] | (P[next - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (!take) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL, absolute address
        if (csp === 64) return done(7);
        C[csp++] = next;
        pc = P[next - 2] | (P[next - 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 0x40: { // LOAD
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE ( v addr -- )
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        M[addr] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT; past the limit writes nothing, trap 11
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) buf[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC, one byte
        if (olen + 1 > 65536) return done(11);
        buf[olen++] = D[--sp] & 255;
        break;
      case 0x52: // IN; -1 past the end
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: // EXIT, low byte
        return done(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
