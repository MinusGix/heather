---
title: Ty::holds_bytes says an enum holds no buffer whatever its payload
status: open
labels: [ownership, facts]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

`Ty::holds_bytes` (`lib/lang/facts/unique.hthr`) answers `False` at every `Enum(i)`, and `Program::owned` relies on it: a value of an enum never shares storage with a buffer. An enum's payload slots are flat codes (`EnumInfo.slots`), and nothing in `rt.hthr` keeps a `ByteList` out of them; the reflector's test for an enum (`rt_is_enum`, `rt_fields_flat` in `rt_reflect.hthr`) refuses only a field of the enum's own type.

`ownership-copy-clone`'s decider (`Ty::copies`, `lib/lang/facts/copy.hthr`) reads the slots, so it says an enum with a buffer slot does not copy, and agrees with `holds_bytes` at an enum exactly where its slots copy (`Ty::enum_agrees`). At an enum with a buffer slot the two disagree, and `holds_bytes` is the one that would be unsound.

## Scope

Find whether any route reaches an enum with a `List<u8>` field (a probe through `runtime fn`). If one does, make `holds_bytes` read the table at an enum (as `Ty::copies` does), or refuse such an enum where enums are built; if none does, state that as a fact the reflector proves and `holds_bytes` cites.

## Done when

`holds_bytes(Enum(i)) = False` is justified at every table a program can have, by a theorem or by a refusal with a probe.
