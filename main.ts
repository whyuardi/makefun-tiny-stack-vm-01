// Tiny stack VM, ISA v1: runs /input/<id>/program.bin against input.bin and
// writes /output/<id>/stdout.bin + exit.txt. Node 22, no deps, deterministic.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Instruction length (1 + immediate bytes) per opcode; 0 means "no such opcode".
const L = new Uint8Array(256);
for (const o of [0, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 52, 64, 65, 80, 81, 82, 83]) L[o] = 1;
L[1] = 2; L[2] = 5; L[48] = 3; L[49] = 3; L[50] = 3; L[51] = 3;

function run(p, d) {
  const m = new Int32Array(256), s = new Int32Array(256), r = new Int32Array(64);
  const o = new Uint8Array(65536);
  let sp = 0, rp = 0, pc = 0, n = 0, ip = 0, ol = 0, c = 0;
  outer: for (;;) {
    if (n >= 1e6) { c = 10; break; } // step limit
    if (pc < 0 || pc >= p.length) { c = 9; break; } // pc outside program
    const k = p[pc], ln = L[k];
    if (!ln) { c = 5; break; } // unknown opcode
    if (pc + ln > p.length) { c = 9; break; } // immediate cut off
    n++;
    if (k >= 16 && k <= 34) { // arithmetic, logic and compare group
      if (k === 23) { // NEG, wraps
        if (!sp) { c = 2; break outer; }
        s[sp - 1] = -s[sp - 1];
      } else if (k === 27) { // NOT
        if (!sp) { c = 2; break outer; }
        s[sp - 1] = ~s[sp - 1];
      } else {
        if (sp < 2) { c = 2; break outer; }
        const b = s[sp - 1], a = s[sp - 2];
        let v;
        switch (k) {
          case 16: v = (a + b) | 0; break; // ADD
          case 17: v = (a - b) | 0; break; // SUB
          case 18: v = Math.imul(a, b); break; // MUL, low 32 bits
          case 19: if (!b) { c = 4; break outer; } v = (a / b) | 0; break; // DIV
          case 20: if (!b) { c = 4; break outer; } v = a % b; break; // MOD
          case 21: { const u = a >>> 0, w = b >>> 0; if (!w) { c = 4; break outer; } v = (u / w) | 0; break; } // DIVU
          case 22: { const u = a >>> 0, w = b >>> 0; if (!w) { c = 4; break outer; } v = (u % w) | 0; break; } // MODU
          case 24: v = a & b; break; // AND
          case 25: v = a | b; break; // OR
          case 26: v = a ^ b; break; // XOR
          case 28: v = a << (b & 31); break; // SHL
          case 29: v = a >> (b & 31); break; // SHR, arithmetic
          case 30: v = a >>> (b & 31); break; // SHRU, logical
          case 32: v = a === b ? 1 : 0; break; // EQ
          case 33: v = a < b ? 1 : 0; break; // LT, signed
          case 34: v = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU
        }
        sp--; s[sp - 1] = v;
      }
      pc++;
      continue;
    }
    switch (k) {
      case 0: break outer; // HALT, code 0
      case 1: // PUSH8, sign-extended
        if (sp > 255) { c = 3; break outer; }
        s[sp++] = (p[pc + 1] << 24) >> 24; pc += 2; break;
      case 2: // PUSH32, little-endian
        if (sp > 255) { c = 3; break outer; }
        s[sp++] = p[pc + 1] | (p[pc + 2] << 8) | (p[pc + 3] << 16) | (p[pc + 4] << 24); pc += 5; break;
      case 3: // POP
        if (!sp) { c = 2; break outer; }
        sp--; pc++; break;
      case 4: // DUP
        if (!sp) { c = 2; break outer; }
        if (sp > 255) { c = 3; break outer; }
        s[sp] = s[sp - 1]; sp++; pc++; break;
      case 5: // SWAP
        if (sp < 2) { c = 2; break outer; }
        { const t = s[sp - 1]; s[sp - 1] = s[sp - 2]; s[sp - 2] = t; }
        pc++; break;
      case 6: // OVER
        if (sp < 2) { c = 2; break outer; }
        if (sp > 255) { c = 3; break outer; }
        s[sp] = s[sp - 2]; sp++; pc++; break;
      case 7: // ROT
        if (sp < 3) { c = 2; break outer; }
        { const a = s[sp - 3], b = s[sp - 2], x = s[sp - 1]; s[sp - 3] = b; s[sp - 2] = x; s[sp - 1] = a; }
        pc++; break;
      case 48: // JMP, offset from the next instruction
        pc += 3 + (((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16); break;
      case 49: case 50: // JZ / JNZ
        if (!sp) { c = 2; break outer; }
        { const v = s[--sp], f = ((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16;
          pc = (k === 49 ? v === 0 : v !== 0) ? pc + 3 + f : pc + 3; }
        break;
      case 51: // CALL
        if (rp > 63) { c = 7; break outer; }
        r[rp++] = pc + 3; pc = p[pc + 1] | (p[pc + 2] << 8); break;
      case 52: // RET
        if (!rp) { c = 8; break outer; }
        pc = r[--rp]; break;
      case 64: // LOAD
        if (!sp) { c = 2; break outer; }
        { const a = s[sp - 1];
          if (a < 0 || a > 255) { c = 6; break outer; }
          s[sp - 1] = m[a]; }
        pc++; break;
      case 65: // STORE, ( v addr -- )
        if (sp < 2) { c = 2; break outer; }
        { const a = s[sp - 1], v = s[sp - 2];
          if (a < 0 || a > 255) { c = 6; break outer; }
          m[a] = v; sp -= 2; }
        pc++; break;
      case 80: // PRINT, decimal ASCII, no newline
        if (!sp) { c = 2; break outer; }
        { const v = s[--sp];
          let x = v < 0 ? -v : v, nd = 1;
          for (let t = x; t >= 10; t = (t / 10) | 0) nd++;
          const need = nd + (v < 0 ? 1 : 0);
          if (ol + need > 65536) { c = 11; break outer; }
          let q = ol + need;
          if (!x) o[--q] = 48; else for (let t = x; t; t = (t / 10) | 0) o[--q] = 48 + (t % 10);
          if (v < 0) o[--q] = 45;
          ol += need; }
        pc++; break;
      case 81: // PUTC, one byte
        if (!sp) { c = 2; break outer; }
        { const v = s[--sp];
          if (ol > 65535) { c = 11; break outer; }
          o[ol++] = v & 255; }
        pc++; break;
      case 82: // IN, -1 once the input is used up
        if (sp > 255) { c = 3; break outer; }
        s[sp++] = ip < d.length ? d[ip++] : -1; pc++; break;
      case 83: // EXIT, low byte of the value
        if (!sp) { c = 2; break outer; }
        c = s[--sp] & 255; break outer;
    }
  }
  return { o: o.subarray(0, ol), c };
}

for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), r.c + '\n');
}
