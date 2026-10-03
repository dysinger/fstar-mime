# Changelog

All notable changes to this project are documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed

- Renamed the C leaf `Network.MIME.Low` → `Network.MIME.Pulse` (the KaRaMeL
  `.Low` convention is retired; the Pulse/Custard layer is the successor).
- Migrated the codec off the deleted GADT API (`make_codec`/`encode_spec`/
  `decode_spec`/`Data.Codec.Lemmas`) onto the record `codec a` combinator API
  (`custom`/`product`/`map_`), 0-admit.
- Ported the content-type tag dispatch leaf from KaRaMeL Low\* (`Stack` +
  `LowStar.Buffer`) to Pulse (`fn` + `Pulse.Lib.Array`), 0-admit, extracting
  to C11 via Custard.
- Proved the roundtrip at the bytes level (`list byte` fields), with the
  `string` view (`mime_of_string`/`string_of_mime`) carried as pure functions
  proven on concrete vectors (the `FStar.String.string_of_list` congruence
  barrier precludes a general symbolic `string` roundtrip).
- Rolled F\* forward to `v2026.09.20+lsp` (first stable tag shipping the
  Custard extractor).
- Removed the KaRaMeL/Low\* toolchain and all its targets (`krml`, `native`,
  `rust`, `wasm`) — F\* `v2026.09.20` deleted the `FStar.HyperStack` /
  `LowStar.Buffer` stdlib.

### Source drift fixes

- Defined the ASCII `bytes ↔ string` bridges locally (they were unbound, and
  the dead `open Data.Text.Codec.UTF8` was removed).
- Removed `open FStar.Mul` and `Prims.op_Multiply` (both deleted upstream).
- Removed `--split_queries always` from `#push-options` (option deleted).

## [0.1.0] — initial extraction

### Added

- Extracted `Network.MIME` out of the original monorepo into a standalone
  repository built from `fstar-nix-flake-template`.
- Source modules:
  - `Network.MIME` — the `mime` record, the IANA media-type registry
    enumeration (2280 constants), and the `type "/" subtype` codec (RFC 2045
    §5.1).
  - `Network.MIME.Pulse` — C-extractable 1-byte content-type tag dispatch.
- Test module: `Network.MIME.Test.Integration`.
- Nix flake targets: `.#checked`, `.#ocaml`, `.#native`, `.#fsharp`.
- Dual licensing: AGPL-3.0-or-later, or a commercial license from the author.

### Notes

- Zero admits / zero magic / zero `assume` across all modules.
