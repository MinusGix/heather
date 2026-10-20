---
title: wc's words differ from GNU wc 9.x at byte 0xA0
status: open
labels: [native,examples]
area: heather-in-heather
created: 2026-10-01
updated: 2026-10-01
---

`examples/x86-native/wc.hthr` says it prints words "as GNU prints them".
GNU coreutils 9.11 also ends a word at byte 0xA0 (no-break space), even in
the C locale (`printf 'a\240a' | LC_ALL=C wc -w` is 2). Our `space_byte` is
the POSIX set (9–13, 32), so on 300 KB of random bytes the word counts differ
by about one per 0xA0 byte. Lines and bytes agree.

This was true before the 2026-10-01 round as well (the old and new
executables agree with each other). Either add 0xA0 to `space_byte`, with a
dated note on which coreutils behaviour is matched, or say "POSIX
whitespace" in the claim's prose and the README.
