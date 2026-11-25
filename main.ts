// tinyvm — a faithful interpreter for make.fun's tiny stack ISA (tiny-stack-vm-01): exact wrapping
// 32-bit arithmetic, unsigned DIVU/MODU/LTU, 5-bit shift counts, and every trap with its own code.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [imm bytes, pops, pushes] outside the binary block (0x10..0x22 less NEG, NOT, 0x1f: [0,2,1]).
const META: { [op: number]: [number, number, number] } = {
  0x00: [0,0,0], 0x01: [1,0,1], 0x02: [4,0,1], 0x03: [0,1,0], 0x04: [0,1,2], 0x05: [0,2,2],
  0x06: [0,2,3], 0x07: [0,3,3], 0x17: [0,1,1], 0x1b: [0,1,1], 0x30: [2,0,0], 0x31: [2,1,0],
  0x32: [2,1,0], 0x33: [2,0,0], 0x34: [0,0,0], 0x40: [0,1,1], 0x41: [0,2,0], 0x50: [0,1,0],
  0x51: [0,1,0], 0x52: [0,0,1], 0x53: [0,1,0],
};

/** One program to its end: the bytes it wrote and its exit code (a trap's code included). */
function run(p: Uint8Array, inp: Uint8Array) {
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out: number[] = [];
  let sp = 0, csp = 0, pc = 0, ip = 0, steps = 0;
  const end = (code: number) => ({ out, code });
  for (;;) {
    // One step, in the ISA's order: step limit, pc, opcode, immediate fit, stack needs.
    if (steps === 1_000_000) return end(10);
    if (pc < 0 || pc >= p.length) return end(9);
    const op = p[pc];
    const meta = META[op] ?? (op >= 0x10 && op <= 0x22 && op !== 0x1f ? [0, 2, 1] : undefined);
    if (meta === undefined) return end(5);
    const [imm, pops, pushes] = meta;
    if (pc + imm >= p.length) return end(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return end(2);
    if (sp - pops + pushes > 256) return end(3);
    pc = next;
    switch (op) {
      case 0x00:
        return end(0);
      case 0x01:
        D[sp++] = (p[next - 1] << 24) >> 24;
        break;
      case 0x02:
        D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 0x06:
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: {
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 0x17:
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 0x1b:
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x30:
      case 0x31:
      case 0x32: {
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL: unsigned target
        if (csp === 64) return end(7);
        C[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return end(8);
        pc = C[--csp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return end(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return end(6);
        M[addr] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT decimal; past the limit it writes nothing
        const text = String(D[sp - 1]);
        if (out.length + text.length > 65_536) return end(11);
        sp--;
        for (let k = 0; k < text.length; k++) out.push(text.charCodeAt(k));
        break;
      }
      case 0x51: // PUTC
        if (out.length + 1 > 65_536) return end(11);
        out.push(D[--sp] & 255);
        break;
      case 0x52: // IN: -1 at end of input
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: // EXIT: the low byte
        return end(D[--sp] & 255);
      default: { // the binary block: ( a b -- r ), b the top of the stack
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break; // the exact product's low 32 bits
          case 0x13: // DIV truncates toward zero; -2^31 / -1 wraps to itself
            if (b === 0) return end(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14: // MOD takes the sign of a; x % -1 is 0
            if (b === 0) return end(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15: // DIVU / MODU / LTU read both operands unsigned
            if (b === 0) return end(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16:
            if (b === 0) return end(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break; // shift counts use the low 5 bits
          case 0x1d: r = a >> (b & 31); break; // arithmetic
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // logical
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
          default: return end(5);
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const { out, code } = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), Buffer.from(out));
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
