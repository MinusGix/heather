//! SHA-256 in Rust, in the shape of the Heather source the linked code is
//! compiled from: one Rust function per `runtime fn` of
//! `lib/native/crypto/sha256_block.hthr`, `sha256_round.hthr`,
//! `sha256_schedule.hthr`, `sha256_working.hthr`,
//! `sha256_compression.hthr`, `sha256_one_block.hthr`,
//! `sha256_filling.hthr`, `sha256_padding.hthr` and `sha256_stream.hthr`,
//! and of the span words they read and store with
//! (`lib/native/runtime/stored_words.hthr`, `rt.hthr`, `rt_file.hthr`).
//!
//! It is the reference for what the source's *shape* costs, apart from
//! what our compiler does with it: the context is the `Sha256` record's
//! bytes (`sha256_context.hthr`), every word of it read and stored a byte
//! at a time, most significant first, each byte under a test against the
//! length the span was lent with; the eight working variables are moved in
//! memory each round (`Sha256::shift`); the round constant is found by
//! halving (`sha256_k`); and the small functions are functions. A
//! `decreases` function that calls itself last is a loop here, as the
//! compiler makes it one.
//!
//! When the Heather source changes, this file changes with it, function for
//! function; `check` in `main.rs` holds the two to the same bytes of context
//! after every function the linked code exports.

/// Where each field of the `Sha256` record lies in its bytes
/// (`Sha256::hash_at`, … of `sha256_context.hthr`). `check` holds them to
/// the linked code's context.
const HASH_AT: u64 = 0;
const WORKING_AT: u64 = 32;
const SCHEDULE_AT: u64 = 64;
const COUNT_AT: u64 = 320;

/// `List::byte_within` (`rt.hthr`): the byte where the index is below the
/// length the span was lent with, 0 elsewhere.
fn byte_within(span: &[u8], length: u64, i: u64) -> u64 {
    if i < length { span[i as usize] as u64 } else { 0 }
}

/// `List::put_within` (`rt_file.hthr`).
fn put_within(span: &mut [u8], length: u64, i: u64, v: u64) {
    if i < length {
        span[i as usize] = v as u8;
    }
}

/// `List::u32_be_within` (`stored_words.hthr`).
fn u32_be_within(span: &[u8], length: u64, i: u64) -> u64 {
    byte_within(span, length, i) << 24
        | byte_within(span, length, i + 1) << 16
        | byte_within(span, length, i + 2) << 8
        | byte_within(span, length, i + 3)
}

/// `List::put_u32_be_within`.
fn put_u32_be_within(span: &mut [u8], length: u64, i: u64, word: u64) -> u64 {
    put_within(span, length, i, (word >> 24) & 0xff);
    put_within(span, length, i + 1, (word >> 16) & 0xff);
    put_within(span, length, i + 2, (word >> 8) & 0xff);
    put_within(span, length, i + 3, word & 0xff);
    word
}

/// `List::u64_be_within`.
fn u64_be_within(span: &[u8], length: u64, i: u64) -> u64 {
    u32_be_within(span, length, i) << 32 | u32_be_within(span, length, i + 4)
}

/// `List::put_u64_be_within`.
fn put_u64_be_within(span: &mut [u8], length: u64, i: u64, word: u64) -> u64 {
    put_u32_be_within(span, length, i, word >> 32);
    put_u32_be_within(span, length, i + 4, word);
    word
}

/// `sha256_k` (`sha256_block.hthr`): K(t), found by halving.
fn sha256_k(t: u64) -> u64 {
    if t < 32 {
        if t < 16 {
            if t < 8 {
                if t < 4 {
                    if t < 2 { if t < 1 { 0x428a2f98 } else { 0x71374491 } } else { if t < 3 { 0xb5c0fbcf } else { 0xe9b5dba5 } }
                } else {
                    if t < 6 { if t < 5 { 0x3956c25b } else { 0x59f111f1 } } else { if t < 7 { 0x923f82a4 } else { 0xab1c5ed5 } }
                }
            } else {
                if t < 12 {
                    if t < 10 { if t < 9 { 0xd807aa98 } else { 0x12835b01 } } else { if t < 11 { 0x243185be } else { 0x550c7dc3 } }
                } else {
                    if t < 14 { if t < 13 { 0x72be5d74 } else { 0x80deb1fe } } else { if t < 15 { 0x9bdc06a7 } else { 0xc19bf174 } }
                }
            }
        } else {
            if t < 24 {
                if t < 20 {
                    if t < 18 { if t < 17 { 0xe49b69c1 } else { 0xefbe4786 } } else { if t < 19 { 0x0fc19dc6 } else { 0x240ca1cc } }
                } else {
                    if t < 22 { if t < 21 { 0x2de92c6f } else { 0x4a7484aa } } else { if t < 23 { 0x5cb0a9dc } else { 0x76f988da } }
                }
            } else {
                if t < 28 {
                    if t < 26 { if t < 25 { 0x983e5152 } else { 0xa831c66d } } else { if t < 27 { 0xb00327c8 } else { 0xbf597fc7 } }
                } else {
                    if t < 30 { if t < 29 { 0xc6e00bf3 } else { 0xd5a79147 } } else { if t < 31 { 0x06ca6351 } else { 0x14292967 } }
                }
            }
        }
    } else {
        if t < 48 {
            if t < 40 {
                if t < 36 {
                    if t < 34 { if t < 33 { 0x27b70a85 } else { 0x2e1b2138 } } else { if t < 35 { 0x4d2c6dfc } else { 0x53380d13 } }
                } else {
                    if t < 38 { if t < 37 { 0x650a7354 } else { 0x766a0abb } } else { if t < 39 { 0x81c2c92e } else { 0x92722c85 } }
                }
            } else {
                if t < 44 {
                    if t < 42 { if t < 41 { 0xa2bfe8a1 } else { 0xa81a664b } } else { if t < 43 { 0xc24b8b70 } else { 0xc76c51a3 } }
                } else {
                    if t < 46 { if t < 45 { 0xd192e819 } else { 0xd6990624 } } else { if t < 47 { 0xf40e3585 } else { 0x106aa070 } }
                }
            }
        } else {
            if t < 56 {
                if t < 52 {
                    if t < 50 { if t < 49 { 0x19a4c116 } else { 0x1e376c08 } } else { if t < 51 { 0x2748774c } else { 0x34b0bcb5 } }
                } else {
                    if t < 54 { if t < 53 { 0x391c0cb3 } else { 0x4ed8aa4a } } else { if t < 55 { 0x5b9cca4f } else { 0x682e6ff3 } }
                }
            } else {
                if t < 60 {
                    if t < 58 { if t < 57 { 0x748f82ee } else { 0x78a5636f } } else { if t < 59 { 0x84c87814 } else { 0x8cc70208 } }
                } else {
                    if t < 62 { if t < 61 { 0x90befffa } else { 0xa4506ceb } } else { if t < 63 { 0xbef9a3f7 } else { 0xc67178f2 } }
                }
            }
        }
    }
}

/// `sha256_t1` (`sha256_round.hthr`).
fn sha256_t1(h: u64, e: u64, f: u64, g: u64, k: u64, w: u64) -> u64 {
    let h32 = h as u32;
    let e32 = e as u32;
    let f32 = f as u32;
    let g32 = g as u32;
    let k32 = k as u32;
    let w32 = w as u32;
    let big1 = e32.rotate_right(6) ^ e32.rotate_right(11) ^ e32.rotate_right(25);
    let ch = (e32 & f32) ^ (!e32 & g32);
    h32.wrapping_add(big1).wrapping_add(ch).wrapping_add(k32).wrapping_add(w32) as u64
}

/// `sha256_t2`.
fn sha256_t2(a: u64, b: u64, c: u64) -> u64 {
    let a32 = a as u32;
    let b32 = b as u32;
    let c32 = c as u32;
    let big0 = a32.rotate_right(2) ^ a32.rotate_right(13) ^ a32.rotate_right(22);
    let maj = (a32 & b32) ^ (a32 & c32) ^ (b32 & c32);
    big0.wrapping_add(maj) as u64
}

/// `sha256_next`.
fn sha256_next(w2: u64, w7: u64, w15: u64, w16: u64) -> u64 {
    let x = w2 as u32;
    let y = w15 as u32;
    let small1 = x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10);
    let small0 = y.rotate_right(7) ^ y.rotate_right(18) ^ (y >> 3);
    small1.wrapping_add(w7 as u32).wrapping_add(small0).wrapping_add(w16 as u32) as u64
}

/// The `Sha256` record laid over the span a function is lent, with the
/// length it was lent with: a `mut self s: Sha256` parameter as the
/// compiled code has it.
pub struct Sha256<'a> {
    span: &'a mut [u8],
    length: u64,
}

impl<'a> Sha256<'a> {
    pub fn over(span: &'a mut [u8]) -> Sha256<'a> {
        let length = span.len() as u64;
        Sha256 { span, length }
    }

    fn hash_at(&self, i: u64) -> u64 {
        u32_be_within(self.span, self.length, HASH_AT + i * 4)
    }

    fn put_hash(&mut self, i: u64, word: u64) {
        put_u32_be_within(self.span, self.length, HASH_AT + i * 4, word);
    }

    fn working_at(&self, i: u64) -> u64 {
        u32_be_within(self.span, self.length, WORKING_AT + i * 4)
    }

    fn put_working(&mut self, i: u64, word: u64) {
        put_u32_be_within(self.span, self.length, WORKING_AT + i * 4, word);
    }

    fn schedule_at(&self, i: u64) -> u64 {
        u32_be_within(self.span, self.length, SCHEDULE_AT + i * 4)
    }

    fn put_schedule(&mut self, i: u64, word: u64) {
        put_u32_be_within(self.span, self.length, SCHEDULE_AT + i * 4, word);
    }

    /// `s.schedule.put_byte_be(at, byte)`.
    fn put_schedule_byte(&mut self, at: u64, byte: u64) {
        put_within(self.span, self.length, SCHEDULE_AT + at, byte);
    }

    fn count(&self) -> u64 {
        u64_be_within(self.span, self.length, COUNT_AT)
    }

    fn put_count(&mut self, count: u64) {
        put_u64_be_within(self.span, self.length, COUNT_AT, count);
    }

    /// `Sha256::expand` (`sha256_schedule.hthr`).
    fn expand(&mut self, mut j: u64) -> u64 {
        while j < 48 {
            let word = sha256_next(self.schedule_at(j + 14), self.schedule_at(j + 9), self.schedule_at(j + 1), self.schedule_at(j));
            self.put_schedule(j + 16, word & 0xffff_ffff);
            j += 1;
        }
        j
    }

    /// `Sha256::begin`.
    fn begin(&mut self, mut i: u64) -> u64 {
        while i < 8 {
            let word = self.hash_at(i);
            self.put_working(i, word);
            i += 1;
        }
        i
    }

    /// `Sha256::t1`.
    fn t1(&mut self, t: u64, w: u64) -> u64 {
        sha256_t1(self.working_at(7), self.working_at(4), self.working_at(5), self.working_at(6), sha256_k(t), w)
    }

    /// `Sha256::shift` (`sha256_working.hthr`).
    fn shift(&mut self, mut i: u64) -> u64 {
        while i < 7 {
            let word = self.working_at(6 - i);
            self.put_working(7 - i, word);
            i += 1;
        }
        i
    }

    /// `Sha256::set`.
    fn set(&mut self, first: u64, fifth: u64) -> u64 {
        self.shift(0);
        self.put_working(0, first & 0xffff_ffff);
        self.put_working(4, fifth & 0xffff_ffff);
        fifth
    }

    /// `Sha256::turn`.
    fn turn(&mut self, t1: u64) -> u64 {
        let first = t1.wrapping_add(sha256_t2(self.working_at(0), self.working_at(1), self.working_at(2)));
        let fifth = self.working_at(3).wrapping_add(t1);
        self.set(first, fifth)
    }

    /// `Sha256::rounds` (`sha256_compression.hthr`).
    fn rounds(&mut self, mut i: u64) -> u64 {
        while i < 64 {
            let w = self.schedule_at(i);
            let t1 = self.t1(i, w);
            self.turn(t1);
            i += 1;
        }
        i
    }

    /// `Sha256::end`.
    fn end(&mut self, mut i: u64) -> u64 {
        while i < 8 {
            let word = self.hash_at(i).wrapping_add(self.working_at(i));
            self.put_hash(i, word & 0xffff_ffff);
            i += 1;
        }
        i
    }

    /// `Sha256::run`.
    fn run(&mut self) -> u64 {
        self.expand(0);
        self.begin(0);
        self.rounds(0);
        self.end(0)
    }

    /// `Sha256::take_block` (`sha256_one_block.hthr`).
    fn take_block(&mut self, block: &[u8], bn: u64, mut i: u64) -> u64 {
        while i < 64 {
            self.put(i, byte_within(block, bn, i));
            i += 1;
        }
        i
    }

    /// `Sha256::compress`, the linked `sha256_compress`.
    pub fn compress(&mut self, block: &[u8]) -> u64 {
        self.take_block(block, block.len() as u64, 0);
        self.run()
    }

    /// `Sha256::put` (`sha256_filling.hthr`).
    fn put(&mut self, at: u64, byte: u64) -> u64 {
        if at < 64 {
            self.put_schedule_byte(at, byte & 0xff);
        }
        at
    }

    /// `Sha256::push`.
    fn push(&mut self, fill: u64, byte: u64) -> u64 {
        self.put(fill, byte);
        if fill == 63 {
            self.run();
            0
        } else {
            fill + 1
        }
    }

    /// `Sha256::zero`.
    fn zero(&mut self, mut i: u64) -> u64 {
        while i < 64 {
            self.put(i, 0);
            i += 1;
        }
        i
    }

    /// `Sha256::pad` (`sha256_padding.hthr`).
    fn pad(&mut self, fill: u64) -> u64 {
        self.put(fill, 0x80);
        self.zero(fill + 1);
        if fill < 56 {
            fill
        } else {
            self.run();
            self.zero(0);
            fill
        }
    }

    /// `Sha256::close`.
    fn close(&mut self, count: u64) -> u64 {
        self.pad(count & 63);
        self.put_schedule(14, (count >> 29) & 0xffff_ffff);
        self.put_schedule(15, (count << 3) & 0xffff_ffff);
        self.run()
    }

    /// `Sha256::init` (`sha256_stream.hthr`), the linked `sha256_init`.
    pub fn init(&mut self) -> u64 {
        for (i, word) in [0x6a09e667u64, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19].into_iter().enumerate() {
            self.put_hash(i as u64, word);
        }
        self.put_count(0);
        0
    }

    /// `Sha256::absorb`.
    fn absorb(&mut self, message: &[u8], mn: u64, mut j: u64, mut fill: u64) -> u64 {
        while j < mn {
            fill = self.push(fill, byte_within(message, mn, j));
            j += 1;
        }
        fill
    }

    /// `Sha256::take`.
    fn take(&mut self, message: &[u8], mn: u64, count: u64) -> u64 {
        self.absorb(message, mn, 0, count & 63);
        self.put_count(count.wrapping_add(mn));
        count.wrapping_add(mn)
    }

    /// `Sha256::update`, the linked `sha256_update`.
    pub fn update(&mut self, message: &[u8]) -> u64 {
        let count = self.count();
        self.take(message, message.len() as u64, count)
    }

    /// `Sha256::finish`, the linked `sha256_finish`.
    pub fn finish(&mut self) -> u64 {
        let count = self.count();
        self.close(count)
    }
}
