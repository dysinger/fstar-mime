# mime — Agent Guide & Handoff

`Network.MIME` — verified MIME media types (RFC 2045 §5.1), extracted from the
xeno monorepo (`mime/`) as a standalone repo.  Part of
`round2-custard-migration` (the Round-2 package after `uuid`).  F* source is
0-admit.

## Build commands

```bash
nix build .#checked    # F* verification gate (0-admit)
nix build .#native     # C11 shared/static lib (default)
nix build .#fsharp     # .NET library
nix build .#ocaml      # OCaml findlib package
nix fmt                 # format nix files (treefmt)
nix develop && make check   # dev loop (no nix)
```

## Module split

- **`Network.MIME`** (pure) — the `mime` record, the 2280-entry IANA
  media-type registry, and the `type "/" subtype` codec.  The codec is a
  **list-based** encode/decode (`encode_mime : mime -> list byte`,
  `decode_mime : list byte -> option mime`), NOT a record `codec a`
  combinator: the MIME token *run* is variable-length (1+ chars), the one
  case the codec library does not ship a generic roundtrip for (the same
  `take_until`/§60 "per-concrete-instantiation" limitation).  Roundtrip is
  proven by structural induction over the byte list
  (`lemma_mime_bytes_roundtrip`) plus concrete byte vectors; the `string`
  view (`mime_of_string`/`string_of_mime`) is carried as pure functions and
  is NOT given a general symbolic roundtrip (the `FStar.String.string_of_list`
  congruence barrier, fstar-proofs §45).
- **`Network.MIME.Pulse`** (`#lang-pulse`) — the extractable leaf: a 1-byte
  content-type tag dispatch over `Pulse.Lib.Array`.  `content_type` is a flat
  7-variant enum; the encode/decode `ensures` are POINTWISE
  (`Seq.index s1 off == tag_of t`), matching the `Data.UUID.Pulse` shape.

## Key gotchas (learned this session)

- **The variable-length token run has no generic codec roundtrip.**  A
  "one-or-more token chars" scanner cannot be a `custom` codec with a general
  symbolic `roundtrip` field — the `Seq.seq_to_list (seq_of_list bs ++ r)`
  rewrite is the §11 barrier.  Use the list-based encode/decode (mirroring
  `fstar-basen`'s base-N codecs) + structural-induction roundtrip instead.
- **Concrete byte vectors verify with a bare `()` body** — `token_run_scan`
  recurses on the list with literal bytes, so the prover unfolds them
  directly.  Concrete *string* vectors (`mime_of_string "text/plain" == …`)
  do NOT (the `String` reconstruction is §45-opaque) — keep `assert_norm`s at
  the byte level.
- **The old `lemma_mime_has_slash` `admit ()` was unsound** (a `mime` can hold
  empty strings); non-emptiness is now enforced structurally by
  `token_run_wfcv`, not a general `String.length` lemma.
- **`--split_queries` is removed in v2026.09.20** (one SMT query per
  obligation); don't reach for it.

## Reference

- Canonical shape: `../fstar-basen` (its `default.nix`, `flake.nix`, `Makefile`,
  `Data.BaseN.Pulse` is the library-with-codec-dep reference this repo mirrors).
- F\* skills: `~/.pi/agent/skills/fstar/fstar-2026.09.20/SKILL.md` (Custard/Pulse)
  and `fstar-proofs` §11/§45/§60 (Seq opacity + the token-run barrier).
- OpenSpec change: `xeno/openspec/changes/mime-custard-extraction/`.
