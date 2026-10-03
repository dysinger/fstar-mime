(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Network.MIME.Test.Integration — Binds all mime lemmas, values, and tests.

If any lemma or test function is deleted or renamed, F* verification fails.
This guarantees mechanically-enforced test coverage.

Uses [--admit_smt_queries true] for integration anchoring only.
Individual lemmas are proven without admits in their source modules.

@header Network.MIME.Test.Integration
*)
module Network.MIME.Test.Integration


open Network.MIME
open Network.MIME.Pulse


#push-options "--admit_smt_queries true"


(** Values *)


(** [text_plain] *)
let _text_plain = text_plain
(** [text_html] *)
let _text_html = text_html
(** [application_json] *)
let _application_json = application_json
(** [image_png] *)
let _image_png = image_png


(** Token / codec lemmas *)


(** [lemma_token_run_wfcv_nonempty] *)
let _lemma_token_run_wfcv_nonempty = lemma_token_run_wfcv_nonempty
(** [lemma_token_run_scan_self] *)
let _lemma_token_run_scan_self = lemma_token_run_scan_self
(** [lemma_mime_bytes_roundtrip] *)
let _lemma_mime_bytes_roundtrip = lemma_mime_bytes_roundtrip


(** Concrete byte-vector lemmas *)


(** [lemma_mime_bytes_text_plain_concrete] *)
let _lemma_mime_bytes_text_plain_concrete = lemma_mime_bytes_text_plain_concrete
(** [lemma_mime_bytes_text_html_concrete] *)
let _lemma_mime_bytes_text_html_concrete = lemma_mime_bytes_text_html_concrete
(** [lemma_mime_bytes_reject_empty_type] *)
let _lemma_mime_bytes_reject_empty_type = lemma_mime_bytes_reject_empty_type
(** [lemma_mime_bytes_reject_empty_subtype] *)
let _lemma_mime_bytes_reject_empty_subtype = lemma_mime_bytes_reject_empty_subtype


(** Pulse tag-dispatch lemmas *)


(** [lemma_tag_roundtrip] *)
let _lemma_tag_roundtrip = lemma_tag_roundtrip
(** [lemma_pulse_content_type_roundtrip] *)
let _lemma_pulse_content_type_roundtrip = lemma_pulse_content_type_roundtrip


(** Pulse encode/decode functions — mechanically protected against deletion *)


(** [encode_content_type] *)
let _encode_content_type = encode_content_type
(** [decode_content_type] *)
let _decode_content_type = decode_content_type


#pop-options
