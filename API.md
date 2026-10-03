# Network.MIME API Reference

## Types

### Network.MIME — Pure Spec
| Name | Kind | Description |
|------|------|-------------|
| `mime` | record | RFC 2045 §5.1 media type — `type_` + `subtype` (both `string`) |
| `mime_bytes` | record | bytes-level mirror — `type_bytes` + `subtype_bytes` (both `list byte`) |

### Network.MIME.Pulse — Extractable Leaf
| Name | Kind | Description |
|------|------|-------------|
| `content_type` | enum (7 variants) | `CT_Text_Plain` / `CT_Text_HTML` / `CT_App_JSON` / `CT_App_Octet` / `CT_Image_PNG` / `CT_Image_JPEG` / `CT_Unknown` |
| `opt_content_type` | sum | `OCO_None` / `OCO_Some of (content_type & U32.t)` |

## Codec

| Function | Signature | Description |
|----------|-----------|-------------|
| `encode_mime` | `mime -> list byte` | serialize a `mime` to its `type/subtype` byte list |
| `decode_mime` | `list byte -> option mime` | parse `type/subtype` (whole-input) |
| `mime_of_string` | `string -> option mime` | parse a MIME type string |
| `string_of_mime` | `mime -> string` | serialize to `"type/subtype"` |

## Registry access

| Function | Signature | Description |
|----------|-----------|-------------|
| `text_plain`, `text_html`, `application_json`, `image_png`, … | `mime` | 2280 IANA media-type constants (9 `*_` prefixes) |

## Char predicate + scan

| Function | Signature | Description |
|----------|-----------|-------------|
| `is_token_char` | `U8.t -> bool` | RFC 2045 §5.1 token-char predicate |
| `token_run_scan` | `list byte -> list byte & list byte` | maximal leading token-char run |
| `token_run_wfcv` | `list byte -> bool` | non-empty + all-token-char guard |

## Pulse leaf

| Function | Signature | Description |
|----------|-----------|-------------|
| `encode_content_type` | `fn (content_type) (A.array U8.t) (U32.t) -> U32.t` | write 1-byte tag, returns `1ul` |
| `decode_content_type` | `fn (A.array U8.t) (U32.t) -> opt_content_type` | read 1-byte tag |
| `lemma_pulse_content_type_roundtrip` | Pulse `fn` | encode then decode preserves the tag |
| `tag_of` / `tag_to_type` | `noextract` pure | tag byte ↔ content-type maps |

## Lemmas

| Lemma | Proves |
|-------|--------|
| `lemma_token_run_wfcv_nonempty` | a well-formed token run is non-empty |
| `lemma_token_run_scan_self` | scanning a token run + non-token suffix returns `(run, rest)` |
| `lemma_mime_bytes_roundtrip` | `decode (encode mb) == Some (mb, \|encode mb\|)` |
| `lemma_mime_bytes_text_plain_concrete` | `"text/plain"` byte vector decodes correctly |
| `lemma_mime_bytes_text_html_concrete` | `"text/html"` byte vector decodes correctly |
| `lemma_mime_bytes_reject_empty_type` | a missing `type` (`"/plain"`) is rejected |
| `lemma_mime_bytes_reject_empty_subtype` | a missing `subtype` (`"text/"`) is rejected |
| `lemma_tag_roundtrip` | `tag_to_type (tag_of t) == Some t` |
