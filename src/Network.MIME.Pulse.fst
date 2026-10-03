(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Network.MIME.Pulse — C-extractable MIME content-type tag dispatch via Pulse
+ Custard.

A 1-byte content-type tag read/write over [Pulse.Lib.Array.array].  The tag is
a compact enumerated `content_type` (the well-known `text/plain`, `text/html`,
`application/json`, `application/octet-stream`, `image/png`, `image/jpeg` plus
an `unknown` catch-all), encoded as a single byte.  Each encode/decode carries
a POINTWISE post-condition tying the buffer contents to the pure spec
[tag_of]/[tag_to_type].

Written for F* v2026.09.20 (Custard `--custard_backend C`).  Zero admits.

@header Network.MIME.Pulse

@section Type
- [content_type] — the enumerated content-type subset
- [opt_content_type] — the tagged decode result ([OCO_None] (unreachable) | [OCO_Some] of ([content_type] & [U32.t]))

@section Spec
- [tag_of] / [tag_to_type] — the pure tag byte ↔ content-type maps

@section Encode
- [encode_content_type] — writes the 1-byte tag, returns [1ul]

@section Decode
- [decode_content_type] — reads the 1-byte tag, returns ([content_type], [1ul])

@section Roundtrip
- [lemma_tag_roundtrip] — the pure spec roundtrip
- [lemma_pulse_content_type_roundtrip] — encode then decode preserves the tag
*)
module Network.MIME.Pulse
#lang-pulse

open Pulse
open Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq

open FStar.Seq
open FStar.Int.Cast


(* ── Type ───────────────────────────────────────────────────────────── *)


(** [content_type] — the enumerated content-type subset for C extraction.

    [CT_Unknown] fallback maps any byte not in the well-known set. *)
type content_type =
  | CT_Text_Plain
  | CT_Text_HTML
  | CT_App_JSON
  | CT_App_Octet
  | CT_Image_PNG
  | CT_Image_JPEG
  | CT_Unknown


(** [opt_content_type] — the decode result: [OCO_None] (never, under the bounds
    precondition) or [OCO_Some] of ([content_type] & [U32.t]).

    [OCO_None] is constructively unreachable — the 1-byte read under a bounds
    precondition always succeeds, and [decode_content_type]'s body returns only
    [OCO_Some] — but it is REQUIRED for extraction: Custard's F# backend has no
    realization for a bare [tuple2] (`content_type & U32.t`), so the pair must
    be wrapped in a (multi-constructor) sum.  Do NOT delete [OCO_None] without
    an F# realization for the pair. *)
type opt_content_type =
  | OCO_None
  | OCO_Some of (content_type & U32.t)


(* ── Pure spec (noextract) ──────────────────────────────────────────── *)


(** [tag_of] — the pure mapping from [content_type] to its tag byte. *)
noextract
let tag_of (t: content_type) : U8.t =
  match t with
  | CT_Text_Plain -> 0x00uy
  | CT_Text_HTML -> 0x01uy
  | CT_App_JSON -> 0x02uy
  | CT_App_Octet -> 0x03uy
  | CT_Image_PNG -> 0x04uy
  | CT_Image_JPEG -> 0x05uy
  | CT_Unknown -> 0xFFuy


(** [tag_to_type] — the pure mapping from a tag byte to its [content_type];
    [None] for a byte that is not a valid tag. *)
noextract
let tag_to_type (b: U8.t) : option content_type =
  if U8.eq b 0x00uy then Some CT_Text_Plain
  else if U8.eq b 0x01uy then Some CT_Text_HTML
  else if U8.eq b 0x02uy then Some CT_App_JSON
  else if U8.eq b 0x03uy then Some CT_App_Octet
  else if U8.eq b 0x04uy then Some CT_Image_PNG
  else if U8.eq b 0x05uy then Some CT_Image_JPEG
  else if U8.eq b 0xFFuy then Some CT_Unknown
  else None


(** [lemma_tag_roundtrip] — the pure spec roundtrip: decoding the tag byte of
    [t] is [Some t]. *)
noextract
let lemma_tag_roundtrip (t: content_type) : Lemma (tag_to_type (tag_of t) == Some t) =
  match t with
  | CT_Text_Plain -> ()
  | CT_Text_HTML -> ()
  | CT_App_JSON -> ()
  | CT_App_Octet -> ()
  | CT_Image_PNG -> ()
  | CT_Image_JPEG -> ()
  | CT_Unknown -> ()


(* ── Encode ─────────────────────────────────────────────────────────── *)


(** [encode_content_type] writes the 1-byte tag of [t] into [buf] at [off].

    @param t The content type to write.
    @param buf The destination buffer (must hold at least 1 byte at [off]).
    @param off The write offset.
    @returns The number of bytes written (always [1ul]). *)
fn encode_content_type (t: content_type) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf /\ U32.v off < 4294967296)
    returns w: U32.t
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (U32.v off + 1 <= A.length buf /\
              Seq.length s1 == A.length buf /\
              Seq.index s1 (U32.v off) == tag_of t)) **
      pure (w == 1ul)
{
  let j = US.uint32_to_sizet off;
  A.pts_to_len buf;
  buf.(j) <- tag_of t;
  1ul
}


(* ── Decode ─────────────────────────────────────────────────────────── *)


(** [decode_content_type] reads the 1-byte tag at [off] from [buf].

    There is no rejection under the bounds precondition: the tag byte is read
    and mapped to the nearest [content_type] ([CT_Unknown] for a byte outside
    the well-known set).  The [ensures] ties the result to [tag_to_type]. *)
fn decode_content_type (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf /\ U32.v off < 4294967296 /\
            A.length buf == Seq.length s0)
    returns r: opt_content_type
    ensures
      A.pts_to buf s0 **
      pure (
        A.length buf == Seq.length s0 /\
        U32.v off + 1 <= A.length buf /\
        (match tag_to_type (Seq.index s0 (U32.v off)) with
         | Some ct -> r == OCO_Some (ct, 1ul)
         | None -> r == OCO_Some (CT_Unknown, 1ul)))
{
  A.pts_to_len buf;
  let j = US.uint32_to_sizet off;
  let b = buf.(j);
  if U8.eq b 0x00uy { OCO_Some (CT_Text_Plain, 1ul) }
  else if U8.eq b 0x01uy { OCO_Some (CT_Text_HTML, 1ul) }
  else if U8.eq b 0x02uy { OCO_Some (CT_App_JSON, 1ul) }
  else if U8.eq b 0x03uy { OCO_Some (CT_App_Octet, 1ul) }
  else if U8.eq b 0x04uy { OCO_Some (CT_Image_PNG, 1ul) }
  else if U8.eq b 0x05uy { OCO_Some (CT_Image_JPEG, 1ul) }
  else if U8.eq b 0xFFuy { OCO_Some (CT_Unknown, 1ul) }
  else { OCO_Some (CT_Unknown, 1ul) }
}


(* ── Roundtrip ──────────────────────────────────────────────────────── *)


(** [lemma_pulse_content_type_roundtrip]: encode then decode preserves the tag.

    @param t The content type to roundtrip.
    @param buf The buffer (must hold at least 1 byte at [off]).
    @param off The offset.
    Proves [decode_content_type buf off] after [encode_content_type t buf off]
    returns [OCO_Some (t, 1ul)]. *)
fn lemma_pulse_content_type_roundtrip (t: content_type) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf /\ U32.v off < 4294967296)
    returns res: (U32.t & opt_content_type)
    ensures
      exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (res == (1ul, OCO_Some (t, 1ul)))
{
  let w = encode_content_type t buf off;
  let r = decode_content_type buf off;
  (w, r)
}
