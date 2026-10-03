# mime — RFC 2045 MIME media types

`Network.MIME` implements MIME media types per RFC 2045 §5.1.

## Modules

| Module | Purpose |
|--------|---------|
| `Network.MIME` | Pure spec: the `mime` record, the 2280-entry IANA media-type registry, the `type "/" subtype` codec, and 0-admit lemmas |
| `Network.MIME.Pulse` | C/OCaml/F#-extractable Pulse leaf: 1-byte content-type tag dispatch over `Pulse.Lib.Array` |

## RFC coverage

| Feature | RFC 2045 | Notes |
|---------|----------|-------|
| `mime` record (`type_` + `subtype`) | §5.1 | non-empty token strings |
| token character set | §5.1 | `A-Z a-z 0-9` + `! # $ % & ' * + - . ^ _ ` { | } ~` |
| `type "/" subtype` codec | §5.1 | `encode_mime` / `decode_mime` / `mime_of_string` / `string_of_mime` |
| IANA media-type registry | — | 2280 constants (`application__*`, `text__*`, `image__*`, `audio__*`, `video__*`, `multipart__*`, `font__*`, `message__*`, `model__*`) |

## Build

```bash
nix build .#checked   # F* verification gate (0-admit)
nix build .#native    # C11 shared/static lib (default)
nix build .#fsharp    # .NET library
nix build .#ocaml     # OCaml findlib package
nix fmt               # format nix files (treefmt)
nix develop && make check   # dev loop (no nix)
```

The `codec` dependency is injected as a flake input (`github:dysinger/fstar-codec`),
its source as `codec-src` and its pre-verified `.checked` set as `codec-checked`.
