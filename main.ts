import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const IMM = new Int8Array(256).fill(-1);
const POP = new Int8Array(256);
const PSH = new Int8Array(256);
const TABLE: number[][] = [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0],
  [0x04, 0, 1, 2], [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1],
  [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1],
  [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1],
  [0x21, 0, 2, 1], [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0],
  [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0], [0x40, 0, 1, 1],
  [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1],
  [0x53, 0, 1, 0],
];
for (const [op, imm, pops, pushes] of TABLE) {
  IMM[op] = imm;
  POP[op] = pops;
  PSH[op] = pushes;
}

function run(prog: Uint8Array, input: Uint8Array): [Uint8Array, number] {
  const n = prog.length;
  const st = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, ip = 0, pc = 0, steps = 0, ol = 0;
  const stop = (code: number): [Uint8Array, number] => [out.slice(0, ol), code];

  for (;;) {
    if (steps === 1000000) return stop(10);
    if (pc < 0 || pc >= n) return stop(9);
    const op = prog[pc];
    const imm = IMM[op];
    if (imm < 0) return stop(5);
    if (pc + imm >= n) return stop(9);
    steps++;
    const next = pc + 1 + imm;
    const pops = POP[op];
    if (sp < pops) return stop(2);
    if (sp - pops + PSH[op] > 256) return stop(3);
    pc = next;

    switch (op) {
      case 0x00:
        return stop(0);
      case 0x01:
        st[sp++] = (prog[next - 1] << 24) >> 24;
        break;
      case 0x02:
        st[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        st[sp] = st[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = st[sp - 1];
        st[sp - 1] = st[sp - 2];
        st[sp - 2] = t;
        break;
      }
      case 0x06:
        st[sp] = st[sp - 2];
        sp++;
        break;
      case 0x07: {
        const a = st[sp - 3];
        st[sp - 3] = st[sp - 2];
        st[sp - 2] = st[sp - 1];
        st[sp - 1] = a;
        break;
      }
      case 0x17:
        st[sp - 1] = -st[sp - 1] | 0;
        break;
      case 0x1b:
        st[sp - 1] = ~st[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e: case 0x20:
      case 0x21: case 0x22: {
        const b = st[sp - 1], a = st[sp - 2];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return stop(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return stop(4);
          r = b === -1 ? 0 : a % b | 0;
        } else if (op === 0x15) {
          if (b === 0) return stop(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return stop(4);
          r = (a >>> 0) % (b >>> 0) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        st[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = st[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return stop(7);
        calls[cp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return stop(8);
        pc = calls[--cp];
        break;
      case 0x40: {
        const a = st[sp - 1];
        if (a < 0 || a >= 256) return stop(6);
        st[sp - 1] = mem[a];
        break;
      }
      case 0x41: {
        const a = st[sp - 1], v = st[sp - 2];
        if (a < 0 || a >= 256) return stop(6);
        sp -= 2;
        mem[a] = v;
        break;
      }
      case 0x50: {
        const v = st[sp - 1];
        const neg = v < 0;
        let d = neg ? -v : v;
        let digits = 1;
        for (let t = d; t >= 10; t = Math.floor(t / 10)) digits++;
        const len = digits + (neg ? 1 : 0);
        if (ol + len > 65536) return stop(11);
        sp--;
        let w = ol + len;
        for (let i = 0; i < digits; i++) {
          out[--w] = 48 + (d % 10);
          d = Math.floor(d / 10);
        }
        if (neg) out[ol] = 45;
        ol += len;
        break;
      }
      case 0x51:
        if (ol + 1 > 65536) return stop(11);
        out[ol++] = st[--sp] & 255;
        break;
      case 0x52:
        st[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 0x53:
        return stop(st[--sp] & 255);
    }
  }
}

for (const id of readdirSync(IN).sort()) {
  const [stdout, code] = run(
    new Uint8Array(readFileSync(join(IN, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(IN, id, 'input.bin'))),
  );
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'stdout.bin'), stdout);
  writeFileSync(join(OUT, id, 'exit.txt'), `${code}\n`);
}
