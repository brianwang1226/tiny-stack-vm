// Tiny stack VM for make.fun's tiny stack ISA: runs each program.bin on its
// input.bin, writes the bytes it writes and its exit code. 32-bit wrapping
// values; data stack 256, call stack 64, memory 256 words; ten traps.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STACK_MAX = 256, CALLS_MAX = 64, MEM_WORDS = 256, STEP_LIMIT = 1e6, OUT_MAX = 65536;

// Trap codes, the exit code of a program that traps.
const TRAP = { U: 2, O: 3, D: 4, B: 5, M: 6, C: 7, R: 8, P: 9, S: 10, T: 11 };

// Every opcode the ISA names: its byte, the bytes of its immediate, what it pops, what it pushes.
const OPS: [number, number, number, number][] = [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0], [0x04, 0, 1, 2],
  [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3], [0x10, 0, 2, 1], [0x11, 0, 2, 1],
  [0x12, 0, 2, 1], [0x13, 0, 2, 1], [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1],
  [0x17, 0, 1, 1], [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1], [0x21, 0, 2, 1],
  [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0], [0x32, 2, 1, 0], [0x33, 2, 0, 0],
  [0x34, 0, 0, 0], [0x40, 0, 1, 1], [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0],
  [0x52, 0, 0, 1], [0x53, 0, 1, 0],
];
const BY_BYTE = new Map(OPS.map((o) => [o[0], o]));

function run(program: Uint8Array, input: Uint8Array): { out: Uint8Array; code: number } {
  const n = program.length;
  const D = new Int32Array(STACK_MAX);
  let sp = 0;
  const C = new Int32Array(CALLS_MAX);
  let csp = 0;
  const M = new Int32Array(MEM_WORDS);
  const out = new Uint8Array(OUT_MAX);
  let olen = 0;
  let inPos = 0;
  let pc = 0;
  let steps = 0;
  const done = (code: number) => ({ out: out.slice(0, olen), code });

  for (;;) {
    // One step, in the order ISA.md states it.
    if (steps === STEP_LIMIT) return done(TRAP.S);
    if (pc < 0 || pc >= n) return done(TRAP.P);
    const spec = BY_BYTE.get(program[pc]);
    if (spec === undefined) return done(TRAP.B);
    const [, imm, pops, pushes] = spec;
    if (pc + imm >= n) return done(TRAP.P);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return done(TRAP.U);
    if (sp - pops + pushes > STACK_MAX) return done(TRAP.O);
    const op = program[pc];
    pc = next;
    switch (op) {
      case 0x00: return done(0);
      case 0x01: D[sp++] = (program[next - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = program[next - 4] | (program[next - 3] << 8) | (program[next - 2] << 16) | (program[next - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = (-D[sp - 1]) | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return done(TRAP.D);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14:
            if (b === 0) return done(TRAP.D);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15:
            if (b === 0) return done(TRAP.D);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16:
            if (b === 0) return done(TRAP.D);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((program[next - 2] | (program[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === CALLS_MAX) return done(TRAP.C);
        C[csp++] = next;
        pc = program[next - 2] | (program[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return done(TRAP.R);
        pc = C[--csp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return done(TRAP.M);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1];
        const v = D[sp - 2];
        if (addr < 0 || addr >= MEM_WORDS) return done(TRAP.M);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]);
        if (olen + s.length > OUT_MAX) return done(TRAP.T);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > OUT_MAX) return done(TRAP.T);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = inPos < input.length ? input[inPos++] : -1; break;
      case 0x53: return done(D[--sp] & 255);
      default: return done(TRAP.B);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const p = join(I, id), q = join(O, id);
  const r = run(new Uint8Array(readFileSync(join(p, 'program.bin'))), new Uint8Array(readFileSync(join(p, 'input.bin'))));
  mkdirSync(q, { recursive: true });
  writeFileSync(join(q, 'stdout.bin'), r.out);
  writeFileSync(join(q, 'exit.txt'), r.code + '\n');
}
