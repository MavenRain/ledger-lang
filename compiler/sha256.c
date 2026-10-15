#include "ledger.h"

/* M1 part A (design item 1): FIPS 180-4 SHA-256 on a text of bytes, with no
   library. The padded message is not stored: padded_byte gives each byte of
   it from the text and its length. */

/* FIPS 180-4 section 4.2.2: the 64 round constants. */
static const uint32_t round_constants[64] = {
  0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u, 0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u,
  0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u, 0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u,
  0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu, 0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
  0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u, 0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u,
  0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u, 0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
  0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u, 0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
  0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u, 0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u,
  0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u, 0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u
};

/* FIPS 180-4 section 5.3.3: the initial hash value. */
static const uint32_t initial_hash[8] = {
  0x6a09e667u, 0xbb67ae85u, 0x3c6ef372u, 0xa54ff53au, 0x510e527fu, 0x9b05688cu, 0x1f83d9abu, 0x5be0cd19u
};

/* count is always from 1 to 31. */
static uint32_t rotate_right(uint32_t word, Nat count) { return (word >> count) | (word << (32 - count)); }

/* FIPS 180-4 section 5.1.1: the byte at position of the padded message. The
   padded message is the text, the byte 128, zero bytes, and the bit length
   of the text in the last 8 bytes, big endian. total is its size. */
static Nat padded_byte(Text text, uint64_t total, uint64_t position) {
  uint64_t bits = (uint64_t)text.size * 8;
  if (position < text.size) return text.items[position];
  if (position == text.size) return 128;
  if (position < total - 8) return 0;
  return (Nat)((bits >> (8 * (total - 1 - position))) & 255);
}

/* FIPS 180-4 section 6.2.2: one 64-byte block into the state. */
static void compress_block(Text text, uint64_t total, uint64_t block, uint32_t state[8]) {
  uint32_t schedule[64];
  for (Nat index = 0; index < 16; index++) {
    uint64_t start = block * 64 + 4 * index;
    schedule[index] = (padded_byte(text, total, start) << 24) | (padded_byte(text, total, start + 1) << 16) |
                      (padded_byte(text, total, start + 2) << 8) | padded_byte(text, total, start + 3);
  }
  for (Nat index = 16; index < 64; index++) {
    uint32_t early = schedule[index - 15];
    uint32_t late = schedule[index - 2];
    uint32_t small0 = rotate_right(early, 7) ^ rotate_right(early, 18) ^ (early >> 3);
    uint32_t small1 = rotate_right(late, 17) ^ rotate_right(late, 19) ^ (late >> 10);
    schedule[index] = schedule[index - 16] + small0 + schedule[index - 7] + small1;
  }
  uint32_t a = state[0], b = state[1], c = state[2], d = state[3];
  uint32_t e = state[4], f = state[5], g = state[6], h = state[7];
  for (Nat index = 0; index < 64; index++) {
    uint32_t big1 = rotate_right(e, 6) ^ rotate_right(e, 11) ^ rotate_right(e, 25);
    uint32_t choose = (e & f) ^ (~e & g);
    uint32_t first = h + big1 + choose + round_constants[index] + schedule[index];
    uint32_t big0 = rotate_right(a, 2) ^ rotate_right(a, 13) ^ rotate_right(a, 22);
    uint32_t majority = (a & b) ^ (a & c) ^ (b & c);
    uint32_t second = big0 + majority;
    h = g;
    g = f;
    f = e;
    e = d + first;
    d = c;
    c = b;
    b = a;
    a = first + second;
  }
  state[0] += a;
  state[1] += b;
  state[2] += c;
  state[3] += d;
  state[4] += e;
  state[5] += f;
  state[6] += g;
  state[7] += h;
}

/* Returns 0 when an item of the text is 256 or more. Else it writes the 32
   digest bytes and returns 1. */
int sha256(Text text, Nat digest[32]) {
  for (Nat index = 0; index < text.size; index++) {
    if (text.items[index] > 255) return 0;
  }
  uint32_t state[8];
  for (Nat index = 0; index < 8; index++) state[index] = initial_hash[index];
  uint64_t blocks = ((uint64_t)text.size + 8) / 64 + 1;
  for (uint64_t block = 0; block < blocks; block++) compress_block(text, blocks * 64, block, state);
  for (Nat index = 0; index < 32; index++) digest[index] = (state[index / 4] >> (24 - 8 * (index % 4))) & 255;
  return 1;
}

static Nat hex_digit(Nat digit) { return digit < 10 ? 48 + digit : 87 + digit; }

/* The digest as 64 lowercase hex digits. Returns 0 as sha256 does. */
int sha256_hex(Text text, Text *hex) {
  Nat digest[32];
  if (!sha256(text, digest)) return 0;
  TextBuilder done = builder_new();
  for (Nat index = 0; index < 32; index++) {
    builder_push(&done, hex_digit(digest[index] / 16));
    builder_push(&done, hex_digit(digest[index] % 16));
  }
  *hex = builder_text(&done);
  return 1;
}
