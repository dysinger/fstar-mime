(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Network.MIME — MIME media types (RFC 2045 §5.1), pure spec.

A MIME media type is a `type` and `subtype`, both non-empty token strings
joined by a `/` (e.g. `text/html`).  This module defines the [mime] record,
the full IANA media-type registry enumeration (2280 constants across
`application/*`, `audio/*`, `font/*`, `image/*`, `message/*`, `model/*`,
`multipart/*`, `text/*`, and `video/*`), and the `type "/" subtype` [codec].

The codec is built from the record [codec a] combinator API over a bytes-level
representation ([mime_bytes]: [list byte] fields) so the roundtrip proof reduces
from the combinators' computable projections.  The [string] view is carried as
pure functions ([mime_of_string]/[string_of_mime]) proven on concrete vectors —
a general symbolic `bytes → string → bytes` roundtrip is blocked by the
`FStar.String.string_of_list` congruence barrier (fstar-proofs §45).

The C-extractable content-type tag dispatch leaf lives in [Network.MIME.Pulse].

@header Network.MIME

@section Type
- [mime] — a media type (`type_` + `subtype`, both [string])
- [mime_bytes] — the bytes-level mirror (`type_bytes` + `subtype_bytes`)

@section Constants
- The 2280-entry IANA media-type registry (`application__*`, `text__*`,
  `image__*`, `audio__*`, `video__*`, `multipart__*`, `font__*`, `message__*`,
  `model__*`).

@section Identifier escaping
- Each registry constant is named `type__subtype` (the `/` separator becomes
  `__`).  Within [subtype], the IANA registry characters are escaped to valid
  F* identifiers: `-` becomes `_`; `+` becomes `_plus_` (so `amr-wb+` →
  `amr_wb_plus_`, trailing `+` yielding a trailing `_plus_`); a leading digit
  is prefixed with `_` (so `1d-interleaved-parityfec` →
  `_1d_interleaved_parityfec`, giving `application__1d_...` = `application` +
  `__` separator + `_1d_...`).  The `__` token is therefore overloaded: it is
  the type/subtype separator AND the leading-digit escape prefix.

@section Codec
- [token_codec] — one-or-more RFC 2045 token chars ([codec (list byte)])
- [mime_bytes_codec] — `type "/" subtype` over the bytes-level mirror
- [mime_codec] — `type "/" subtype` over [mime]

@section String view
- [mime_of_string] / [string_of_mime] — pure `string` conversions
- [ascii_bytes_to_string] / [string_to_ascii_bytes] — local ASCII bridges

@section Lemmas
- byte-list roundtrip + concrete vector lemmas (all 0-admit)
*)
module Network.MIME

open Data.Codec
open Data.Codec.Types

open FStar.Seq
open FStar.UInt8
open FStar.List.Tot

module U8 = FStar.UInt8
module Seq = FStar.Seq


(* ── Types ──────────────────────────────────────────────────────────── *)


(** A MIME media type: a `type` and `subtype`, both non-empty token strings.
    Case-INSENSITIVE for matching per RFC 2045 §5.1, but stored
    CASE-PRESERVING (the IANA registry constants keep their authoritative
    casing, e.g. `application/3gppHal+json`); a parser may downcase for
    canonical comparison. *)
type mime = {
  type_    : string;
  subtype  : string;
}


(** The bytes-level mirror of [mime], used as the codec's carried
    representation so the roundtrip proof reduces without touching
    [FStar.String]. *)
type mime_bytes = {
  type_bytes    : list byte;
  subtype_bytes : list byte;
}

(* ========================================================================
   IANA Media Types Registry (2280 entries)
   ======================================================================== *)

(* ---- application/* ---- *)
let application__1d_interleaved_parityfec : mime = {type_ = "application"; subtype = "1d-interleaved-parityfec"}
let application__3gpdash_qoe_report_plus_xml : mime = {type_ = "application"; subtype = "3gpdash-qoe-report+xml"}
let application__3gpp_ims_plus_xml : mime = {type_ = "application"; subtype = "3gpp-ims+xml"}
let application__3gpp_mbs_object_manifest_plus_json : mime = {type_ = "application"; subtype = "3gpp-mbs-object-manifest+json"}
let application__3gpp_mbs_user_service_descriptions_plus_json : mime = {type_ = "application"; subtype = "3gpp-mbs-user-service-descriptions+json"}
let application__3gpp_media_delivery_metrics_report_plus_json : mime = {type_ = "application"; subtype = "3gpp-media-delivery-metrics-report+json"}
let application__3gpphal_plus_json : mime = {type_ = "application"; subtype = "3gppHal+json"}
let application__3gpphalforms_plus_json : mime = {type_ = "application"; subtype = "3gppHalForms+json"}
let application_aas_plus_zip : mime = {type_ = "application"; subtype = "aas+zip"}
let application_a2l : mime = {type_ = "application"; subtype = "A2L"}
let application_ace_groupcomm_plus_cbor : mime = {type_ = "application"; subtype = "ace-groupcomm+cbor"}
let application_ace_trl_plus_cbor : mime = {type_ = "application"; subtype = "ace-trl+cbor"}
let application_ace_plus_cbor : mime = {type_ = "application"; subtype = "ace+cbor"}
let application_ace_plus_json : mime = {type_ = "application"; subtype = "ace+json"}
let application_activemessage : mime = {type_ = "application"; subtype = "activemessage"}
let application_activity_plus_json : mime = {type_ = "application"; subtype = "activity+json"}
let application_aif_plus_cbor : mime = {type_ = "application"; subtype = "aif+cbor"}
let application_aif_plus_json : mime = {type_ = "application"; subtype = "aif+json"}
let application_alto_cdni_plus_json : mime = {type_ = "application"; subtype = "alto-cdni+json"}
let application_alto_cdnifilter_plus_json : mime = {type_ = "application"; subtype = "alto-cdnifilter+json"}
let application_alto_costmap_plus_json : mime = {type_ = "application"; subtype = "alto-costmap+json"}
let application_alto_costmapfilter_plus_json : mime = {type_ = "application"; subtype = "alto-costmapfilter+json"}
let application_alto_directory_plus_json : mime = {type_ = "application"; subtype = "alto-directory+json"}
let application_alto_endpointprop_plus_json : mime = {type_ = "application"; subtype = "alto-endpointprop+json"}
let application_alto_endpointpropparams_plus_json : mime = {type_ = "application"; subtype = "alto-endpointpropparams+json"}
let application_alto_endpointcost_plus_json : mime = {type_ = "application"; subtype = "alto-endpointcost+json"}
let application_alto_endpointcostparams_plus_json : mime = {type_ = "application"; subtype = "alto-endpointcostparams+json"}
let application_alto_error_plus_json : mime = {type_ = "application"; subtype = "alto-error+json"}
let application_alto_networkmapfilter_plus_json : mime = {type_ = "application"; subtype = "alto-networkmapfilter+json"}
let application_alto_networkmap_plus_json : mime = {type_ = "application"; subtype = "alto-networkmap+json"}
let application_alto_propmap_plus_json : mime = {type_ = "application"; subtype = "alto-propmap+json"}
let application_alto_propmapparams_plus_json : mime = {type_ = "application"; subtype = "alto-propmapparams+json"}
let application_alto_tips_plus_json : mime = {type_ = "application"; subtype = "alto-tips+json"}
let application_alto_tipsparams_plus_json : mime = {type_ = "application"; subtype = "alto-tipsparams+json"}
let application_alto_updatestreamcontrol_plus_json : mime = {type_ = "application"; subtype = "alto-updatestreamcontrol+json"}
let application_alto_updatestreamparams_plus_json : mime = {type_ = "application"; subtype = "alto-updatestreamparams+json"}
let application_aml : mime = {type_ = "application"; subtype = "AML"}
let application_andrew_inset : mime = {type_ = "application"; subtype = "andrew-inset"}
let application_applefile : mime = {type_ = "application"; subtype = "applefile"}
let application_asyncapi_plus_json : mime = {type_ = "application"; subtype = "asyncapi+json"}
let application_asyncapi_plus_yaml : mime = {type_ = "application"; subtype = "asyncapi+yaml"}
let application_at_plus_jwt : mime = {type_ = "application"; subtype = "at+jwt"}
let application_atf : mime = {type_ = "application"; subtype = "ATF"}
let application_atfx : mime = {type_ = "application"; subtype = "ATFX"}
let application_atom_plus_xml : mime = {type_ = "application"; subtype = "atom+xml"}
let application_atomcat_plus_xml : mime = {type_ = "application"; subtype = "atomcat+xml"}
let application_atomdeleted_plus_xml : mime = {type_ = "application"; subtype = "atomdeleted+xml"}
let application_atomicmail : mime = {type_ = "application"; subtype = "atomicmail"}
let application_atomsvc_plus_xml : mime = {type_ = "application"; subtype = "atomsvc+xml"}
let application_atsc_dwd_plus_xml : mime = {type_ = "application"; subtype = "atsc-dwd+xml"}
let application_atsc_dynamic_event_message : mime = {type_ = "application"; subtype = "atsc-dynamic-event-message"}
let application_atsc_held_plus_xml : mime = {type_ = "application"; subtype = "atsc-held+xml"}
let application_atsc_rdt_plus_json : mime = {type_ = "application"; subtype = "atsc-rdt+json"}
let application_atsc_rsat_plus_xml : mime = {type_ = "application"; subtype = "atsc-rsat+xml"}
let application_atxml : mime = {type_ = "application"; subtype = "ATXML"}
let application_auth_policy_plus_xml : mime = {type_ = "application"; subtype = "auth-policy+xml"}
let application_automationml_aml_plus_xml : mime = {type_ = "application"; subtype = "automationml-aml+xml"}
let application_automationml_amlx_plus_zip : mime = {type_ = "application"; subtype = "automationml-amlx+zip"}
let application_bacnet_xdd_plus_zip : mime = {type_ = "application"; subtype = "bacnet-xdd+zip"}
let application_batch_smtp : mime = {type_ = "application"; subtype = "batch-SMTP"}
let application_beep_plus_xml : mime = {type_ = "application"; subtype = "beep+xml"}
let application_bufr : mime = {type_ = "application"; subtype = "bufr"}
let application_c2pa : mime = {type_ = "application"; subtype = "c2pa"}
let application_calendar_plus_json : mime = {type_ = "application"; subtype = "calendar+json"}
let application_calendar_plus_xml : mime = {type_ = "application"; subtype = "calendar+xml"}
let application_call_completion : mime = {type_ = "application"; subtype = "call-completion"}
let application_cals_1840 : mime = {type_ = "application"; subtype = "CALS-1840"}
let application_captive_plus_json : mime = {type_ = "application"; subtype = "captive+json"}
let application_cbor : mime = {type_ = "application"; subtype = "cbor"}
let application_cbor_seq : mime = {type_ = "application"; subtype = "cbor-seq"}
let application_cccex : mime = {type_ = "application"; subtype = "cccex"}
let application_ccmp_plus_xml : mime = {type_ = "application"; subtype = "ccmp+xml"}
let application_ccxml_plus_xml : mime = {type_ = "application"; subtype = "ccxml+xml"}
let application_cda_plus_xml : mime = {type_ = "application"; subtype = "cda+xml"}
let application_cdfx_plus_xml : mime = {type_ = "application"; subtype = "CDFX+XML"}
let application_cdmi_capability : mime = {type_ = "application"; subtype = "cdmi-capability"}
let application_cdmi_container : mime = {type_ = "application"; subtype = "cdmi-container"}
let application_cdmi_domain : mime = {type_ = "application"; subtype = "cdmi-domain"}
let application_cdmi_object : mime = {type_ = "application"; subtype = "cdmi-object"}
let application_cdmi_queue : mime = {type_ = "application"; subtype = "cdmi-queue"}
let application_cdni : mime = {type_ = "application"; subtype = "cdni"}
let application_ce_plus_cbor : mime = {type_ = "application"; subtype = "ce+cbor"}
let application_cea : mime = {type_ = "application"; subtype = "CEA"}
let application_cea_2018_plus_xml : mime = {type_ = "application"; subtype = "cea-2018+xml"}
let application_cellml_plus_xml : mime = {type_ = "application"; subtype = "cellml+xml"}
let application_cfw : mime = {type_ = "application"; subtype = "cfw"}
let application_cid : mime = {type_ = "application"; subtype = "cid"}
let application_cid_edhoc_plus_cbor_seq : mime = {type_ = "application"; subtype = "cid-edhoc+cbor-seq"}
let application_city_plus_json : mime = {type_ = "application"; subtype = "city+json"}
let application_city_plus_json_seq : mime = {type_ = "application"; subtype = "city+json-seq"}
let application_clr : mime = {type_ = "application"; subtype = "clr"}
let application_clue_info_plus_xml : mime = {type_ = "application"; subtype = "clue_info+xml"}
let application_clue_plus_xml : mime = {type_ = "application"; subtype = "clue+xml"}
let application_cms : mime = {type_ = "application"; subtype = "cms"}
let application_cmw_plus_cbor : mime = {type_ = "application"; subtype = "cmw+cbor"}
let application_cmw_plus_cose : mime = {type_ = "application"; subtype = "cmw+cose"}
let application_cmw_plus_json : mime = {type_ = "application"; subtype = "cmw+json"}
let application_cmw_plus_jws : mime = {type_ = "application"; subtype = "cmw+jws"}
let application_cnrp_plus_xml : mime = {type_ = "application"; subtype = "cnrp+xml"}
let application_coap_eap : mime = {type_ = "application"; subtype = "coap-eap"}
let application_coap_group_plus_json : mime = {type_ = "application"; subtype = "coap-group+json"}
let application_coap_payload : mime = {type_ = "application"; subtype = "coap-payload"}
let application_commonground : mime = {type_ = "application"; subtype = "commonground"}
let application_concise_problem_details_plus_cbor : mime = {type_ = "application"; subtype = "concise-problem-details+cbor"}
let application_conference_info_plus_xml : mime = {type_ = "application"; subtype = "conference-info+xml"}
let application_cpl_plus_xml : mime = {type_ = "application"; subtype = "cpl+xml"}
let application_cose : mime = {type_ = "application"; subtype = "cose"}
let application_cose_key : mime = {type_ = "application"; subtype = "cose-key"}
let application_cose_key_set : mime = {type_ = "application"; subtype = "cose-key-set"}
let application_cose_x509 : mime = {type_ = "application"; subtype = "cose-x509"}
let application_csrattrs : mime = {type_ = "application"; subtype = "csrattrs"}
let application_csta_plus_xml : mime = {type_ = "application"; subtype = "csta+xml"}
let application_cstadata_plus_xml : mime = {type_ = "application"; subtype = "CSTAdata+xml"}
let application_csvm_plus_json : mime = {type_ = "application"; subtype = "csvm+json"}
let application_cwl : mime = {type_ = "application"; subtype = "cwl"}
let application_cwl_plus_json : mime = {type_ = "application"; subtype = "cwl+json"}
let application_cwl_plus_yaml : mime = {type_ = "application"; subtype = "cwl+yaml"}
let application_cwt : mime = {type_ = "application"; subtype = "cwt"}
let application_cybercash : mime = {type_ = "application"; subtype = "cybercash"}
let application_dash_plus_xml : mime = {type_ = "application"; subtype = "dash+xml"}
let application_dash_patch_plus_xml : mime = {type_ = "application"; subtype = "dash-patch+xml"}
let application_dashdelta : mime = {type_ = "application"; subtype = "dashdelta"}
let application_davmount_plus_xml : mime = {type_ = "application"; subtype = "davmount+xml"}
let application_dca_rft : mime = {type_ = "application"; subtype = "dca-rft"}
let application_dcd : mime = {type_ = "application"; subtype = "DCD"}
let application_dec_dx : mime = {type_ = "application"; subtype = "dec-dx"}
let application_dialog_info_plus_xml : mime = {type_ = "application"; subtype = "dialog-info+xml"}
let application_dicom : mime = {type_ = "application"; subtype = "dicom"}
let application_dicom_plus_json : mime = {type_ = "application"; subtype = "dicom+json"}
let application_dicom_plus_xml : mime = {type_ = "application"; subtype = "dicom+xml"}
let application_did : mime = {type_ = "application"; subtype = "did"}
let application_dii : mime = {type_ = "application"; subtype = "DII"}
let application_dit : mime = {type_ = "application"; subtype = "DIT"}
let application_dns : mime = {type_ = "application"; subtype = "dns"}
let application_dns_plus_json : mime = {type_ = "application"; subtype = "dns+json"}
let application_dns_message : mime = {type_ = "application"; subtype = "dns-message"}
let application_dots_plus_cbor : mime = {type_ = "application"; subtype = "dots+cbor"}
let application_dpop_plus_jwt : mime = {type_ = "application"; subtype = "dpop+jwt"}
let application_dskpp_plus_xml : mime = {type_ = "application"; subtype = "dskpp+xml"}
let application_dssc_plus_der : mime = {type_ = "application"; subtype = "dssc+der"}
let application_dssc_plus_xml : mime = {type_ = "application"; subtype = "dssc+xml"}
let application_dvcs : mime = {type_ = "application"; subtype = "dvcs"}
let application_eat_plus_cwt : mime = {type_ = "application"; subtype = "eat+cwt"}
let application_eat_plus_jwt : mime = {type_ = "application"; subtype = "eat+jwt"}
let application_eat_bun_plus_cbor : mime = {type_ = "application"; subtype = "eat-bun+cbor"}
let application_eat_bun_plus_json : mime = {type_ = "application"; subtype = "eat-bun+json"}
let application_eat_ucs_plus_cbor : mime = {type_ = "application"; subtype = "eat-ucs+cbor"}
let application_eat_ucs_plus_json : mime = {type_ = "application"; subtype = "eat-ucs+json"}
let application_ecmascript : mime = {type_ = "application"; subtype = "ecmascript"}
let application_edhoc_plus_cbor_seq : mime = {type_ = "application"; subtype = "edhoc+cbor-seq"}
let application_edi_consent : mime = {type_ = "application"; subtype = "EDI-consent"}
let application_edifact : mime = {type_ = "application"; subtype = "EDIFACT"}
let application_edi_x12 : mime = {type_ = "application"; subtype = "EDI-X12"}
let application_efi : mime = {type_ = "application"; subtype = "efi"}
let application_elm_plus_json : mime = {type_ = "application"; subtype = "elm+json"}
let application_elm_plus_xml : mime = {type_ = "application"; subtype = "elm+xml"}
let application_emergencycalldata_dot_cap_plus_xml : mime = {type_ = "application"; subtype = "EmergencyCallData.cap+xml"}
let application_emergencycalldata_dot_comment_plus_xml : mime = {type_ = "application"; subtype = "EmergencyCallData.Comment+xml"}
let application_emergencycalldata_dot_control_plus_xml : mime = {type_ = "application"; subtype = "EmergencyCallData.Control+xml"}
let application_emergencycalldata_dot_deviceinfo_plus_xml : mime = {type_ = "application"; subtype = "EmergencyCallData.DeviceInfo+xml"}
let application_emergencycalldata_dot_ecall_dot_msd : mime = {type_ = "application"; subtype = "EmergencyCallData.eCall.MSD"}
let application_emergencycalldata_dot_legacyesn_plus_json : mime = {type_ = "application"; subtype = "EmergencyCallData.LegacyESN+json"}
let application_emergencycalldata_dot_providerinfo_plus_xml : mime = {type_ = "application"; subtype = "EmergencyCallData.ProviderInfo+xml"}
let application_emergencycalldata_dot_serviceinfo_plus_xml : mime = {type_ = "application"; subtype = "EmergencyCallData.ServiceInfo+xml"}
let application_emergencycalldata_dot_subscriberinfo_plus_xml : mime = {type_ = "application"; subtype = "EmergencyCallData.SubscriberInfo+xml"}
let application_emergencycalldata_dot_veds_plus_xml : mime = {type_ = "application"; subtype = "EmergencyCallData.VEDS+xml"}
let application_emma_plus_xml : mime = {type_ = "application"; subtype = "emma+xml"}
let application_emotionml_plus_xml : mime = {type_ = "application"; subtype = "emotionml+xml"}
let application_encaprtp : mime = {type_ = "application"; subtype = "encaprtp"}
let application_entity_statement_plus_jwt : mime = {type_ = "application"; subtype = "entity-statement+jwt"}
let application_epp_plus_xml : mime = {type_ = "application"; subtype = "epp+xml"}
let application_epub_plus_zip : mime = {type_ = "application"; subtype = "epub+zip"}
let application_eshop : mime = {type_ = "application"; subtype = "eshop"}
let application_example : mime = {type_ = "application"; subtype = "example"}
let application_exi : mime = {type_ = "application"; subtype = "exi"}
let application_expect_ct_report_plus_json : mime = {type_ = "application"; subtype = "expect-ct-report+json"}
let application_explicit_registration_response_plus_jwt : mime = {type_ = "application"; subtype = "explicit-registration-response+jwt"}
let application_express : mime = {type_ = "application"; subtype = "express"}
let application_fastinfoset : mime = {type_ = "application"; subtype = "fastinfoset"}
let application_fastsoap : mime = {type_ = "application"; subtype = "fastsoap"}
let application_fdf : mime = {type_ = "application"; subtype = "fdf"}
let application_fdt_plus_xml : mime = {type_ = "application"; subtype = "fdt+xml"}
let application_fhir_plus_json : mime = {type_ = "application"; subtype = "fhir+json"}
let application_fhir_plus_xml : mime = {type_ = "application"; subtype = "fhir+xml"}
let application_fits : mime = {type_ = "application"; subtype = "fits"}
let application_flexfec : mime = {type_ = "application"; subtype = "flexfec"}
let application_font_sfnt : mime = {type_ = "application"; subtype = "font-sfnt"}
let application_font_tdpfr : mime = {type_ = "application"; subtype = "font-tdpfr"}
let application_font_woff : mime = {type_ = "application"; subtype = "font-woff"}
let application_framework_attributes_plus_xml : mime = {type_ = "application"; subtype = "framework-attributes+xml"}
let application_geo_plus_json : mime = {type_ = "application"; subtype = "geo+json"}
let application_geo_plus_json_seq : mime = {type_ = "application"; subtype = "geo+json-seq"}
let application_geofeed_plus_csv : mime = {type_ = "application"; subtype = "geofeed+csv"}
let application_geopackage_plus_sqlite3 : mime = {type_ = "application"; subtype = "geopackage+sqlite3"}
let application_geopose_plus_json : mime = {type_ = "application"; subtype = "geopose+json"}
let application_geoxacml_plus_json : mime = {type_ = "application"; subtype = "geoxacml+json"}
let application_geoxacml_plus_xml : mime = {type_ = "application"; subtype = "geoxacml+xml"}
let application_gltf_buffer : mime = {type_ = "application"; subtype = "gltf-buffer"}
let application_gml_plus_xml : mime = {type_ = "application"; subtype = "gml+xml"}
let application_gnap_binding_jws : mime = {type_ = "application"; subtype = "gnap-binding-jws"}
let application_gnap_binding_jwsd : mime = {type_ = "application"; subtype = "gnap-binding-jwsd"}
let application_gnap_binding_rotation_jws : mime = {type_ = "application"; subtype = "gnap-binding-rotation-jws"}
let application_gnap_binding_rotation_jwsd : mime = {type_ = "application"; subtype = "gnap-binding-rotation-jwsd"}
let application_grib : mime = {type_ = "application"; subtype = "grib"}
let application_gzip : mime = {type_ = "application"; subtype = "gzip"}
let application_h224 : mime = {type_ = "application"; subtype = "H224"}
let application_held_plus_xml : mime = {type_ = "application"; subtype = "held+xml"}
let application_hl7v2_plus_xml : mime = {type_ = "application"; subtype = "hl7v2+xml"}
let application_http : mime = {type_ = "application"; subtype = "http"}
let application_hyperstudio : mime = {type_ = "application"; subtype = "hyperstudio"}
let application_ibe_key_request_plus_xml : mime = {type_ = "application"; subtype = "ibe-key-request+xml"}
let application_ibe_pkg_reply_plus_xml : mime = {type_ = "application"; subtype = "ibe-pkg-reply+xml"}
let application_ibe_pp_data : mime = {type_ = "application"; subtype = "ibe-pp-data"}
let application_iges : mime = {type_ = "application"; subtype = "iges"}
let application_im_iscomposing_plus_xml : mime = {type_ = "application"; subtype = "im-iscomposing+xml"}
let application_index : mime = {type_ = "application"; subtype = "index"}
let application_index_dot_cmd : mime = {type_ = "application"; subtype = "index.cmd"}
let application_index_dot_obj : mime = {type_ = "application"; subtype = "index.obj"}
let application_index_dot_response : mime = {type_ = "application"; subtype = "index.response"}
let application_index_dot_vnd : mime = {type_ = "application"; subtype = "index.vnd"}
let application_inkml_plus_xml : mime = {type_ = "application"; subtype = "inkml+xml"}
let application_iotp : mime = {type_ = "application"; subtype = "IOTP"}
let application_ipfix : mime = {type_ = "application"; subtype = "ipfix"}
let application_ipp : mime = {type_ = "application"; subtype = "ipp"}
let application_isup : mime = {type_ = "application"; subtype = "ISUP"}
let application_its_plus_xml : mime = {type_ = "application"; subtype = "its+xml"}
let application_java_archive : mime = {type_ = "application"; subtype = "java-archive"}
let application_javascript : mime = {type_ = "application"; subtype = "javascript"}
let application_jf2feed_plus_json : mime = {type_ = "application"; subtype = "jf2feed+json"}
let application_jose : mime = {type_ = "application"; subtype = "jose"}
let application_jose_plus_json : mime = {type_ = "application"; subtype = "jose+json"}
let application_jrd_plus_json : mime = {type_ = "application"; subtype = "jrd+json"}
let application_jscalendar_plus_json : mime = {type_ = "application"; subtype = "jscalendar+json"}
let application_jscontact_plus_json : mime = {type_ = "application"; subtype = "jscontact+json"}
let application_json : mime = {type_ = "application"; subtype = "json"}
let application_json_patch_plus_json : mime = {type_ = "application"; subtype = "json-patch+json"}
let application_json_patch_query_plus_json : mime = {type_ = "application"; subtype = "json-patch-query+json"}
let application_json_seq : mime = {type_ = "application"; subtype = "json-seq"}
let application_jsonpath : mime = {type_ = "application"; subtype = "jsonpath"}
let application_jwk_plus_json : mime = {type_ = "application"; subtype = "jwk+json"}
let application_jwk_set_plus_json : mime = {type_ = "application"; subtype = "jwk-set+json"}
let application_jwk_set_plus_jwt : mime = {type_ = "application"; subtype = "jwk-set+jwt"}
let application_jwt : mime = {type_ = "application"; subtype = "jwt"}
let application_kb_plus_jwt : mime = {type_ = "application"; subtype = "kb+jwt"}
let application_kbl_plus_xml : mime = {type_ = "application"; subtype = "kbl+xml"}
let application_kpml_request_plus_xml : mime = {type_ = "application"; subtype = "kpml-request+xml"}
let application_kpml_response_plus_xml : mime = {type_ = "application"; subtype = "kpml-response+xml"}
let application_ld_plus_json : mime = {type_ = "application"; subtype = "ld+json"}
let application_lgr_plus_xml : mime = {type_ = "application"; subtype = "lgr+xml"}
let application_link_format : mime = {type_ = "application"; subtype = "link-format"}
let application_linkset : mime = {type_ = "application"; subtype = "linkset"}
let application_linkset_plus_json : mime = {type_ = "application"; subtype = "linkset+json"}
let application_load_control_plus_xml : mime = {type_ = "application"; subtype = "load-control+xml"}
let application_logout_plus_jwt : mime = {type_ = "application"; subtype = "logout+jwt"}
let application_lost_plus_xml : mime = {type_ = "application"; subtype = "lost+xml"}
let application_lostsync_plus_xml : mime = {type_ = "application"; subtype = "lostsync+xml"}
let application_lpf_plus_zip : mime = {type_ = "application"; subtype = "lpf+zip"}
let application_lxf : mime = {type_ = "application"; subtype = "LXF"}
let application_mac_binhex40 : mime = {type_ = "application"; subtype = "mac-binhex40"}
let application_macwriteii : mime = {type_ = "application"; subtype = "macwriteii"}
let application_mads_plus_xml : mime = {type_ = "application"; subtype = "mads+xml"}
let application_manifest_plus_json : mime = {type_ = "application"; subtype = "manifest+json"}
let application_marc : mime = {type_ = "application"; subtype = "marc"}
let application_marcxml_plus_xml : mime = {type_ = "application"; subtype = "marcxml+xml"}
let application_mathematica : mime = {type_ = "application"; subtype = "mathematica"}
let application_mathml_plus_xml : mime = {type_ = "application"; subtype = "mathml+xml"}
let application_mathml_content_plus_xml : mime = {type_ = "application"; subtype = "mathml-content+xml"}
let application_mathml_presentation_plus_xml : mime = {type_ = "application"; subtype = "mathml-presentation+xml"}
let application_mbms_associated_procedure_description_plus_xml : mime = {type_ = "application"; subtype = "mbms-associated-procedure-description+xml"}
let application_mbms_deregister_plus_xml : mime = {type_ = "application"; subtype = "mbms-deregister+xml"}
let application_mbms_envelope_plus_xml : mime = {type_ = "application"; subtype = "mbms-envelope+xml"}
let application_mbms_msk_response_plus_xml : mime = {type_ = "application"; subtype = "mbms-msk-response+xml"}
let application_mbms_msk_plus_xml : mime = {type_ = "application"; subtype = "mbms-msk+xml"}
let application_mbms_protection_description_plus_xml : mime = {type_ = "application"; subtype = "mbms-protection-description+xml"}
let application_mbms_reception_report_plus_xml : mime = {type_ = "application"; subtype = "mbms-reception-report+xml"}
let application_mbms_register_response_plus_xml : mime = {type_ = "application"; subtype = "mbms-register-response+xml"}
let application_mbms_register_plus_xml : mime = {type_ = "application"; subtype = "mbms-register+xml"}
let application_mbms_schedule_plus_xml : mime = {type_ = "application"; subtype = "mbms-schedule+xml"}
let application_mbms_user_service_description_plus_xml : mime = {type_ = "application"; subtype = "mbms-user-service-description+xml"}
let application_mbox : mime = {type_ = "application"; subtype = "mbox"}
let application_measured_component_plus_cbor : mime = {type_ = "application"; subtype = "measured-component+cbor"}
let application_measured_component_plus_json : mime = {type_ = "application"; subtype = "measured-component+json"}
let application_media_control_plus_xml : mime = {type_ = "application"; subtype = "media_control+xml"}
let application_media_policy_dataset_plus_xml : mime = {type_ = "application"; subtype = "media-policy-dataset+xml"}
let application_mediaservercontrol_plus_xml : mime = {type_ = "application"; subtype = "mediaservercontrol+xml"}
let application_merge_patch_plus_json : mime = {type_ = "application"; subtype = "merge-patch+json"}
let application_metalink4_plus_xml : mime = {type_ = "application"; subtype = "metalink4+xml"}
let application_mets_plus_xml : mime = {type_ = "application"; subtype = "mets+xml"}
let application_mf4 : mime = {type_ = "application"; subtype = "MF4"}
let application_mikey : mime = {type_ = "application"; subtype = "mikey"}
let application_mipc : mime = {type_ = "application"; subtype = "mipc"}
let application_missing_blocks_plus_cbor_seq : mime = {type_ = "application"; subtype = "missing-blocks+cbor-seq"}
let application_mmt_aei_plus_xml : mime = {type_ = "application"; subtype = "mmt-aei+xml"}
let application_mmt_usd_plus_xml : mime = {type_ = "application"; subtype = "mmt-usd+xml"}
let application_mods_plus_xml : mime = {type_ = "application"; subtype = "mods+xml"}
let application_moss_keys : mime = {type_ = "application"; subtype = "moss-keys"}
let application_moss_signature : mime = {type_ = "application"; subtype = "moss-signature"}
let application_mosskey_data : mime = {type_ = "application"; subtype = "mosskey-data"}
let application_mosskey_request : mime = {type_ = "application"; subtype = "mosskey-request"}
let application_mp21 : mime = {type_ = "application"; subtype = "mp21"}
let application_mp4 : mime = {type_ = "application"; subtype = "mp4"}
let application_mpeg4_generic : mime = {type_ = "application"; subtype = "mpeg4-generic"}
let application_mpeg4_iod : mime = {type_ = "application"; subtype = "mpeg4-iod"}
let application_mpeg4_iod_xmt : mime = {type_ = "application"; subtype = "mpeg4-iod-xmt"}
let application_mrb_consumer_plus_xml : mime = {type_ = "application"; subtype = "mrb-consumer+xml"}
let application_mrb_publish_plus_xml : mime = {type_ = "application"; subtype = "mrb-publish+xml"}
let application_msc_ivr_plus_xml : mime = {type_ = "application"; subtype = "msc-ivr+xml"}
let application_msc_mixer_plus_xml : mime = {type_ = "application"; subtype = "msc-mixer+xml"}
let application_msword : mime = {type_ = "application"; subtype = "msword"}
let application_mud_plus_json : mime = {type_ = "application"; subtype = "mud+json"}
let application_multipart_core : mime = {type_ = "application"; subtype = "multipart-core"}
let application_mxf : mime = {type_ = "application"; subtype = "mxf"}
let application_n_quads : mime = {type_ = "application"; subtype = "n-quads"}
let application_n_triples : mime = {type_ = "application"; subtype = "n-triples"}
let application_nasdata : mime = {type_ = "application"; subtype = "nasdata"}
let application_news_checkgroups : mime = {type_ = "application"; subtype = "news-checkgroups"}
let application_news_groupinfo : mime = {type_ = "application"; subtype = "news-groupinfo"}
let application_news_transmission : mime = {type_ = "application"; subtype = "news-transmission"}
let application_nlsml_plus_xml : mime = {type_ = "application"; subtype = "nlsml+xml"}
let application_node : mime = {type_ = "application"; subtype = "node"}
let application_nss : mime = {type_ = "application"; subtype = "nss"}
let application_oauth_authz_req_plus_jwt : mime = {type_ = "application"; subtype = "oauth-authz-req+jwt"}
let application_oblivious_dns_message : mime = {type_ = "application"; subtype = "oblivious-dns-message"}
let application_ocsp_request : mime = {type_ = "application"; subtype = "ocsp-request"}
let application_ocsp_response : mime = {type_ = "application"; subtype = "ocsp-response"}
let application_octet_stream : mime = {type_ = "application"; subtype = "octet-stream"}
let application_oda : mime = {type_ = "application"; subtype = "ODA"}
let application_odm_plus_xml : mime = {type_ = "application"; subtype = "odm+xml"}
let application_odx : mime = {type_ = "application"; subtype = "ODX"}
let application_oebps_package_plus_xml : mime = {type_ = "application"; subtype = "oebps-package+xml"}
let application_ogg : mime = {type_ = "application"; subtype = "ogg"}
let application_ohttp_keys : mime = {type_ = "application"; subtype = "ohttp-keys"}
let application_opc_nodeset_plus_xml : mime = {type_ = "application"; subtype = "opc-nodeset+xml"}
let application_oscore : mime = {type_ = "application"; subtype = "oscore"}
let application_oxps : mime = {type_ = "application"; subtype = "oxps"}
let application_p21 : mime = {type_ = "application"; subtype = "p21"}
let application_p21_plus_zip : mime = {type_ = "application"; subtype = "p21+zip"}
let application_p2p_overlay_plus_xml : mime = {type_ = "application"; subtype = "p2p-overlay+xml"}
let application_parityfec : mime = {type_ = "application"; subtype = "parityfec"}
let application_passport : mime = {type_ = "application"; subtype = "passport"}
let application_patch_ops_error_plus_xml : mime = {type_ = "application"; subtype = "patch-ops-error+xml"}
let application_pdf : mime = {type_ = "application"; subtype = "pdf"}
let application_pdx : mime = {type_ = "application"; subtype = "PDX"}
let application_pem_certificate_chain : mime = {type_ = "application"; subtype = "pem-certificate-chain"}
let application_pgp_encrypted : mime = {type_ = "application"; subtype = "pgp-encrypted"}
let application_pgp_keys : mime = {type_ = "application"; subtype = "pgp-keys"}
let application_pgp_signature : mime = {type_ = "application"; subtype = "pgp-signature"}
let application_pidf_diff_plus_xml : mime = {type_ = "application"; subtype = "pidf-diff+xml"}
let application_pidf_plus_xml : mime = {type_ = "application"; subtype = "pidf+xml"}
let application_pkcs10 : mime = {type_ = "application"; subtype = "pkcs10"}
let application_pkcs7_mime : mime = {type_ = "application"; subtype = "pkcs7-mime"}
let application_pkcs7_signature : mime = {type_ = "application"; subtype = "pkcs7-signature"}
let application_pkcs8 : mime = {type_ = "application"; subtype = "pkcs8"}
let application_pkcs8_encrypted : mime = {type_ = "application"; subtype = "pkcs8-encrypted"}
let application_pkcs12 : mime = {type_ = "application"; subtype = "pkcs12"}
let application_pkix_attr_cert : mime = {type_ = "application"; subtype = "pkix-attr-cert"}
let application_pkix_cert : mime = {type_ = "application"; subtype = "pkix-cert"}
let application_pkix_crl : mime = {type_ = "application"; subtype = "pkix-crl"}
let application_pkix_pkipath : mime = {type_ = "application"; subtype = "pkix-pkipath"}
let application_pkixcmp : mime = {type_ = "application"; subtype = "pkixcmp"}
let application_pls_plus_xml : mime = {type_ = "application"; subtype = "pls+xml"}
let application_poc_settings_plus_xml : mime = {type_ = "application"; subtype = "poc-settings+xml"}
let application_postscript : mime = {type_ = "application"; subtype = "postscript"}
let application_ppsp_tracker_plus_json : mime = {type_ = "application"; subtype = "ppsp-tracker+json"}
let application_private_token_issuer_directory : mime = {type_ = "application"; subtype = "private-token-issuer-directory"}
let application_private_token_request : mime = {type_ = "application"; subtype = "private-token-request"}
let application_private_token_response : mime = {type_ = "application"; subtype = "private-token-response"}
let application_problem_plus_json : mime = {type_ = "application"; subtype = "problem+json"}
let application_problem_plus_xml : mime = {type_ = "application"; subtype = "problem+xml"}
let application_protobuf : mime = {type_ = "application"; subtype = "protobuf"}
let application_protobuf_plus_json : mime = {type_ = "application"; subtype = "protobuf+json"}
let application_provenance_plus_xml : mime = {type_ = "application"; subtype = "provenance+xml"}
let application_provided_claims_plus_jwt : mime = {type_ = "application"; subtype = "provided-claims+jwt"}
let application_prs_dot_alvestrand_dot_titrax_sheet : mime = {type_ = "application"; subtype = "prs.alvestrand.titrax-sheet"}
let application_prs_dot_bwtc32key : mime = {type_ = "application"; subtype = "prs.bwtc32key"}
let application_prs_dot_cww : mime = {type_ = "application"; subtype = "prs.cww"}
let application_prs_dot_cyn : mime = {type_ = "application"; subtype = "prs.cyn"}
let application_prs_dot_hpub_plus_zip : mime = {type_ = "application"; subtype = "prs.hpub+zip"}
let application_prs_dot_implied_document_plus_xml : mime = {type_ = "application"; subtype = "prs.implied-document+xml"}
let application_prs_dot_implied_executable : mime = {type_ = "application"; subtype = "prs.implied-executable"}
let application_prs_dot_implied_object_plus_json : mime = {type_ = "application"; subtype = "prs.implied-object+json"}
let application_prs_dot_implied_object_plus_json_seq : mime = {type_ = "application"; subtype = "prs.implied-object+json-seq"}
let application_prs_dot_implied_object_plus_yaml : mime = {type_ = "application"; subtype = "prs.implied-object+yaml"}
let application_prs_dot_implied_structure : mime = {type_ = "application"; subtype = "prs.implied-structure"}
let application_prs_dot_mayfile : mime = {type_ = "application"; subtype = "prs.mayfile"}
let application_prs_dot_nprend : mime = {type_ = "application"; subtype = "prs.nprend"}
let application_prs_dot_plucker : mime = {type_ = "application"; subtype = "prs.plucker"}
let application_prs_dot_rdf_xml_crypt : mime = {type_ = "application"; subtype = "prs.rdf-xml-crypt"}
let application_prs_dot_sclt : mime = {type_ = "application"; subtype = "prs.sclt"}
let application_prs_dot_vcfbzip2 : mime = {type_ = "application"; subtype = "prs.vcfbzip2"}
let application_prs_dot_xsf_plus_xml : mime = {type_ = "application"; subtype = "prs.xsf+xml"}
let application_pskc_plus_xml : mime = {type_ = "application"; subtype = "pskc+xml"}
let application_pvd_plus_json : mime = {type_ = "application"; subtype = "pvd+json"}
let application_rdf_plus_xml : mime = {type_ = "application"; subtype = "rdf+xml"}
let application_roughtime_malfeasance_plus_json : mime = {type_ = "application"; subtype = "roughtime-malfeasance+json"}
let application_roughtime_server_plus_json : mime = {type_ = "application"; subtype = "roughtime-server+json"}
let application_route_apd_plus_xml : mime = {type_ = "application"; subtype = "route-apd+xml"}
let application_route_s_tsid_plus_xml : mime = {type_ = "application"; subtype = "route-s-tsid+xml"}
let application_route_usd_plus_xml : mime = {type_ = "application"; subtype = "route-usd+xml"}
let application_qsig : mime = {type_ = "application"; subtype = "QSIG"}
let application_raptorfec : mime = {type_ = "application"; subtype = "raptorfec"}
let application_rdap_plus_json : mime = {type_ = "application"; subtype = "rdap+json"}
let application_reginfo_plus_xml : mime = {type_ = "application"; subtype = "reginfo+xml"}
let application_relax_ng_compact_syntax : mime = {type_ = "application"; subtype = "relax-ng-compact-syntax"}
let application_remote_printing : mime = {type_ = "application"; subtype = "remote-printing"}
let application_reputon_plus_json : mime = {type_ = "application"; subtype = "reputon+json"}
let application_resolve_response_plus_jwt : mime = {type_ = "application"; subtype = "resolve-response+jwt"}
let application_resource_lists_diff_plus_xml : mime = {type_ = "application"; subtype = "resource-lists-diff+xml"}
let application_resource_lists_plus_xml : mime = {type_ = "application"; subtype = "resource-lists+xml"}
let application_rfc_plus_xml : mime = {type_ = "application"; subtype = "rfc+xml"}
let application_riscos : mime = {type_ = "application"; subtype = "riscos"}
let application_rlmi_plus_xml : mime = {type_ = "application"; subtype = "rlmi+xml"}
let application_rls_services_plus_xml : mime = {type_ = "application"; subtype = "rls-services+xml"}
let application_rpki_checklist : mime = {type_ = "application"; subtype = "rpki-checklist"}
let application_rpki_ghostbusters : mime = {type_ = "application"; subtype = "rpki-ghostbusters"}
let application_rpki_manifest : mime = {type_ = "application"; subtype = "rpki-manifest"}
let application_rpki_publication : mime = {type_ = "application"; subtype = "rpki-publication"}
let application_rpki_roa : mime = {type_ = "application"; subtype = "rpki-roa"}
let application_rpki_signed_tal : mime = {type_ = "application"; subtype = "rpki-signed-tal"}
let application_rpki_updown : mime = {type_ = "application"; subtype = "rpki-updown"}
let application_rs_metadata_plus_xml : mime = {type_ = "application"; subtype = "rs-metadata+xml"}
let application_rtf : mime = {type_ = "application"; subtype = "rtf"}
let application_rtploopback : mime = {type_ = "application"; subtype = "rtploopback"}
let application_rtx : mime = {type_ = "application"; subtype = "rtx"}
let application_samlassertion_plus_xml : mime = {type_ = "application"; subtype = "samlassertion+xml"}
let application_samlmetadata_plus_xml : mime = {type_ = "application"; subtype = "samlmetadata+xml"}
let application_sarif_external_properties_plus_json : mime = {type_ = "application"; subtype = "sarif-external-properties+json"}
let application_sarif_plus_json : mime = {type_ = "application"; subtype = "sarif+json"}
let application_sbe : mime = {type_ = "application"; subtype = "sbe"}
let application_sbml_plus_xml : mime = {type_ = "application"; subtype = "sbml+xml"}
let application_scaip_plus_xml : mime = {type_ = "application"; subtype = "scaip+xml"}
let application_scim_plus_json : mime = {type_ = "application"; subtype = "scim+json"}
let application_scitt_receipt_plus_cose : mime = {type_ = "application"; subtype = "scitt-receipt+cose"}
let application_scitt_statement_plus_cose : mime = {type_ = "application"; subtype = "scitt-statement+cose"}
let application_scvp_cv_request : mime = {type_ = "application"; subtype = "scvp-cv-request"}
let application_scvp_cv_response : mime = {type_ = "application"; subtype = "scvp-cv-response"}
let application_scvp_vp_request : mime = {type_ = "application"; subtype = "scvp-vp-request"}
let application_scvp_vp_response : mime = {type_ = "application"; subtype = "scvp-vp-response"}
let application_sd_jwt : mime = {type_ = "application"; subtype = "sd-jwt"}
let application_sd_jwt_plus_json : mime = {type_ = "application"; subtype = "sd-jwt+json"}
let application_sdf_plus_json : mime = {type_ = "application"; subtype = "sdf+json"}
let application_sdp : mime = {type_ = "application"; subtype = "sdp"}
let application_secevent_plus_jwt : mime = {type_ = "application"; subtype = "secevent+jwt"}
let application_senml_etch_plus_cbor : mime = {type_ = "application"; subtype = "senml-etch+cbor"}
let application_senml_etch_plus_json : mime = {type_ = "application"; subtype = "senml-etch+json"}
let application_senml_exi : mime = {type_ = "application"; subtype = "senml-exi"}
let application_senml_plus_cbor : mime = {type_ = "application"; subtype = "senml+cbor"}
let application_senml_plus_json : mime = {type_ = "application"; subtype = "senml+json"}
let application_senml_plus_xml : mime = {type_ = "application"; subtype = "senml+xml"}
let application_sensml_exi : mime = {type_ = "application"; subtype = "sensml-exi"}
let application_sensml_plus_cbor : mime = {type_ = "application"; subtype = "sensml+cbor"}
let application_sensml_plus_json : mime = {type_ = "application"; subtype = "sensml+json"}
let application_sensml_plus_xml : mime = {type_ = "application"; subtype = "sensml+xml"}
let application_sep_exi : mime = {type_ = "application"; subtype = "sep-exi"}
let application_sep_plus_xml : mime = {type_ = "application"; subtype = "sep+xml"}
let application_session_info : mime = {type_ = "application"; subtype = "session-info"}
let application_set_payment : mime = {type_ = "application"; subtype = "set-payment"}
let application_set_payment_initiation : mime = {type_ = "application"; subtype = "set-payment-initiation"}
let application_set_registration : mime = {type_ = "application"; subtype = "set-registration"}
let application_set_registration_initiation : mime = {type_ = "application"; subtype = "set-registration-initiation"}
let application_sgml : mime = {type_ = "application"; subtype = "SGML"}
let application_sgml_open_catalog : mime = {type_ = "application"; subtype = "sgml-open-catalog"}
let application_shf_plus_xml : mime = {type_ = "application"; subtype = "shf+xml"}
let application_sieve : mime = {type_ = "application"; subtype = "sieve"}
let application_simple_filter_plus_xml : mime = {type_ = "application"; subtype = "simple-filter+xml"}
let application_simple_message_summary : mime = {type_ = "application"; subtype = "simple-message-summary"}
let application_simplesymbolcontainer : mime = {type_ = "application"; subtype = "simpleSymbolContainer"}
let application_sipc : mime = {type_ = "application"; subtype = "sipc"}
let application_slate : mime = {type_ = "application"; subtype = "slate"}
let application_smil : mime = {type_ = "application"; subtype = "smil"}
let application_smil_plus_xml : mime = {type_ = "application"; subtype = "smil+xml"}
let application_smpte336m : mime = {type_ = "application"; subtype = "smpte336m"}
let application_soap_plus_fastinfoset : mime = {type_ = "application"; subtype = "soap+fastinfoset"}
let application_soap_plus_xml : mime = {type_ = "application"; subtype = "soap+xml"}
let application_sparql_query : mime = {type_ = "application"; subtype = "sparql-query"}
let application_spdx_plus_json : mime = {type_ = "application"; subtype = "spdx+json"}
let application_sparql_results_plus_xml : mime = {type_ = "application"; subtype = "sparql-results+xml"}
let application_spirits_event_plus_xml : mime = {type_ = "application"; subtype = "spirits-event+xml"}
let application_sql : mime = {type_ = "application"; subtype = "sql"}
let application_srgs : mime = {type_ = "application"; subtype = "srgs"}
let application_srgs_plus_xml : mime = {type_ = "application"; subtype = "srgs+xml"}
let application_sru_plus_xml : mime = {type_ = "application"; subtype = "sru+xml"}
let application_sslkeylogfile : mime = {type_ = "application"; subtype = "sslkeylogfile"}
let application_ssml_plus_xml : mime = {type_ = "application"; subtype = "ssml+xml"}
let application_st2110_41 : mime = {type_ = "application"; subtype = "ST2110-41"}
let application_stix_plus_json : mime = {type_ = "application"; subtype = "stix+json"}
let application_stratum : mime = {type_ = "application"; subtype = "stratum"}
let application_suit_envelope_plus_cose : mime = {type_ = "application"; subtype = "suit-envelope+cose"}
let application_suit_report_plus_cose : mime = {type_ = "application"; subtype = "suit-report+cose"}
let application_swid_plus_cbor : mime = {type_ = "application"; subtype = "swid+cbor"}
let application_swid_plus_xml : mime = {type_ = "application"; subtype = "swid+xml"}
let application_syslog_msg : mime = {type_ = "application"; subtype = "syslog-msg"}
let application_tamp_apex_update : mime = {type_ = "application"; subtype = "tamp-apex-update"}
let application_tamp_apex_update_confirm : mime = {type_ = "application"; subtype = "tamp-apex-update-confirm"}
let application_tamp_community_update : mime = {type_ = "application"; subtype = "tamp-community-update"}
let application_tamp_community_update_confirm : mime = {type_ = "application"; subtype = "tamp-community-update-confirm"}
let application_tamp_error : mime = {type_ = "application"; subtype = "tamp-error"}
let application_tamp_sequence_adjust : mime = {type_ = "application"; subtype = "tamp-sequence-adjust"}
let application_tamp_sequence_adjust_confirm : mime = {type_ = "application"; subtype = "tamp-sequence-adjust-confirm"}
let application_tamp_status_query : mime = {type_ = "application"; subtype = "tamp-status-query"}
let application_tamp_status_response : mime = {type_ = "application"; subtype = "tamp-status-response"}
let application_tamp_update : mime = {type_ = "application"; subtype = "tamp-update"}
let application_tamp_update_confirm : mime = {type_ = "application"; subtype = "tamp-update-confirm"}
let application_taxii_plus_json : mime = {type_ = "application"; subtype = "taxii+json"}
let application_td_plus_json : mime = {type_ = "application"; subtype = "td+json"}
let application_teep_plus_cbor : mime = {type_ = "application"; subtype = "teep+cbor"}
let application_tei_plus_xml : mime = {type_ = "application"; subtype = "tei+xml"}
let application_tetra_isi : mime = {type_ = "application"; subtype = "TETRA_ISI"}
let application_texinfo : mime = {type_ = "application"; subtype = "texinfo"}
let application_thraud_plus_xml : mime = {type_ = "application"; subtype = "thraud+xml"}
let application_timestamp_query : mime = {type_ = "application"; subtype = "timestamp-query"}
let application_timestamp_reply : mime = {type_ = "application"; subtype = "timestamp-reply"}
let application_timestamped_data : mime = {type_ = "application"; subtype = "timestamped-data"}
let application_tlsrpt_plus_gzip : mime = {type_ = "application"; subtype = "tlsrpt+gzip"}
let application_tlsrpt_plus_json : mime = {type_ = "application"; subtype = "tlsrpt+json"}
let application_tm_plus_json : mime = {type_ = "application"; subtype = "tm+json"}
let application_tnauthlist : mime = {type_ = "application"; subtype = "tnauthlist"}
let application_toc_plus_cbor : mime = {type_ = "application"; subtype = "toc+cbor"}
let application_token_introspection_plus_jwt : mime = {type_ = "application"; subtype = "token-introspection+jwt"}
let application_toml : mime = {type_ = "application"; subtype = "toml"}
let application_trickle_ice_sdpfrag : mime = {type_ = "application"; subtype = "trickle-ice-sdpfrag"}
let application_trig : mime = {type_ = "application"; subtype = "trig"}
let application_trust_chain_plus_json : mime = {type_ = "application"; subtype = "trust-chain+json"}
let application_trust_mark_plus_jwt : mime = {type_ = "application"; subtype = "trust-mark+jwt"}
let application_trust_mark_delegation_plus_jwt : mime = {type_ = "application"; subtype = "trust-mark-delegation+jwt"}
let application_trust_mark_status_response_plus_jwt : mime = {type_ = "application"; subtype = "trust-mark-status-response+jwt"}
let application_ttml_plus_xml : mime = {type_ = "application"; subtype = "ttml+xml"}
let application_tve_trigger : mime = {type_ = "application"; subtype = "tve-trigger"}
let application_tzif : mime = {type_ = "application"; subtype = "tzif"}
let application_tzif_leap : mime = {type_ = "application"; subtype = "tzif-leap"}
let application_uccs_plus_cbor : mime = {type_ = "application"; subtype = "uccs+cbor"}
let application_ujcs_plus_json : mime = {type_ = "application"; subtype = "ujcs+json"}
let application_ulpfec : mime = {type_ = "application"; subtype = "ulpfec"}
let application_urc_grpsheet_plus_xml : mime = {type_ = "application"; subtype = "urc-grpsheet+xml"}
let application_urc_ressheet_plus_xml : mime = {type_ = "application"; subtype = "urc-ressheet+xml"}
let application_urc_targetdesc_plus_xml : mime = {type_ = "application"; subtype = "urc-targetdesc+xml"}
let application_urc_uisocketdesc_plus_xml : mime = {type_ = "application"; subtype = "urc-uisocketdesc+xml"}
let application_v3c : mime = {type_ = "application"; subtype = "v3c"}
let application_vc : mime = {type_ = "application"; subtype = "vc"}
let application_vc_plus_cose : mime = {type_ = "application"; subtype = "vc+cose"}
let application_vc_plus_jwt : mime = {type_ = "application"; subtype = "vc+jwt"}
let application_vc_plus_sd_jwt : mime = {type_ = "application"; subtype = "vc+sd-jwt"}
let application_vcard_plus_json : mime = {type_ = "application"; subtype = "vcard+json"}
let application_vcard_plus_xml : mime = {type_ = "application"; subtype = "vcard+xml"}
let application_vec_plus_xml : mime = {type_ = "application"; subtype = "vec+xml"}
let application_vec_package_plus_gzip : mime = {type_ = "application"; subtype = "vec-package+gzip"}
let application_vec_package_plus_zip : mime = {type_ = "application"; subtype = "vec-package+zip"}
let application_vemmi : mime = {type_ = "application"; subtype = "vemmi"}
let application_vnd_dot_1000minds_dot_decision_model_plus_xml : mime = {type_ = "application"; subtype = "vnd.1000minds.decision-model+xml"}
let application_vnd_dot_1ob : mime = {type_ = "application"; subtype = "vnd.1ob"}
let application_vnd_dot_3gpp_dot_5gnas : mime = {type_ = "application"; subtype = "vnd.3gpp.5gnas"}
let application_vnd_dot_3gpp_dot_5gsa2x : mime = {type_ = "application"; subtype = "vnd.3gpp.5gsa2x"}
let application_vnd_dot_3gpp_dot_5gsa2x_local_service_information : mime = {type_ = "application"; subtype = "vnd.3gpp.5gsa2x-local-service-information"}
let application_vnd_dot_3gpp_dot_5gsv2x : mime = {type_ = "application"; subtype = "vnd.3gpp.5gsv2x"}
let application_vnd_dot_3gpp_dot_5gsv2x_local_service_information : mime = {type_ = "application"; subtype = "vnd.3gpp.5gsv2x-local-service-information"}
let application_vnd_dot_3gpp_dot_access_transfer_events_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.access-transfer-events+xml"}
let application_vnd_dot_3gpp_dot_bsf_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.bsf+xml"}
let application_vnd_dot_3gpp_dot_crs_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.crs+xml"}
let application_vnd_dot_3gpp_dot_current_location_discovery_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.current-location-discovery+xml"}
let application_vnd_dot_3gpp_dot_gmop_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.GMOP+xml"}
let application_vnd_dot_3gpp_dot_gtpc : mime = {type_ = "application"; subtype = "vnd.3gpp.gtpc"}
let application_vnd_dot_3gpp_dot_interworking_data : mime = {type_ = "application"; subtype = "vnd.3gpp.interworking-data"}
let application_vnd_dot_3gpp_dot_lpp : mime = {type_ = "application"; subtype = "vnd.3gpp.lpp"}
let application_vnd_dot_3gpp_dot_mc_signalling_ear : mime = {type_ = "application"; subtype = "vnd.3gpp.mc-signalling-ear"}
let application_vnd_dot_3gpp_dot_mcdata_affiliation_command_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcdata-affiliation-command+xml"}
let application_vnd_dot_3gpp_dot_mcdata_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcdata-info+xml"}
let application_vnd_dot_3gpp_dot_mcdata_msgstore_ctrl_request_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcdata-msgstore-ctrl-request+xml"}
let application_vnd_dot_3gpp_dot_mcdata_payload : mime = {type_ = "application"; subtype = "vnd.3gpp.mcdata-payload"}
let application_vnd_dot_3gpp_dot_mcdata_regroup_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcdata-regroup+xml"}
let application_vnd_dot_3gpp_dot_mcdata_service_config_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcdata-service-config+xml"}
let application_vnd_dot_3gpp_dot_mcdata_signalling : mime = {type_ = "application"; subtype = "vnd.3gpp.mcdata-signalling"}
let application_vnd_dot_3gpp_dot_mcdata_ue_config_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcdata-ue-config+xml"}
let application_vnd_dot_3gpp_dot_mcdata_user_profile_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcdata-user-profile+xml"}
let application_vnd_dot_3gpp_dot_mcptt_affiliation_command_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcptt-affiliation-command+xml"}
let application_vnd_dot_3gpp_dot_mcptt_floor_request_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcptt-floor-request+xml"}
let application_vnd_dot_3gpp_dot_mcptt_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcptt-info+xml"}
let application_vnd_dot_3gpp_dot_mcptt_location_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcptt-location-info+xml"}
let application_vnd_dot_3gpp_dot_mcptt_mbms_usage_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcptt-mbms-usage-info+xml"}
let application_vnd_dot_3gpp_dot_mcptt_regroup_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcptt-regroup+xml"}
let application_vnd_dot_3gpp_dot_mcptt_service_config_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcptt-service-config+xml"}
let application_vnd_dot_3gpp_dot_mcptt_signed_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcptt-signed+xml"}
let application_vnd_dot_3gpp_dot_mcptt_ue_config_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcptt-ue-config+xml"}
let application_vnd_dot_3gpp_dot_mcptt_ue_init_config_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcptt-ue-init-config+xml"}
let application_vnd_dot_3gpp_dot_mcptt_user_profile_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcptt-user-profile+xml"}
let application_vnd_dot_3gpp_dot_mcs_location_user_config_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcs-location-user-config+xml"}
let application_vnd_dot_3gpp_dot_mcvideo_affiliation_command_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcvideo-affiliation-command+xml"}
let application_vnd_dot_3gpp_dot_mcvideo_affiliation_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcvideo-affiliation-info+xml"}
let application_vnd_dot_3gpp_dot_mcvideo_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcvideo-info+xml"}
let application_vnd_dot_3gpp_dot_mcvideo_location_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcvideo-location-info+xml"}
let application_vnd_dot_3gpp_dot_mcvideo_mbms_usage_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcvideo-mbms-usage-info+xml"}
let application_vnd_dot_3gpp_dot_mcvideo_regroup_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcvideo-regroup+xml"}
let application_vnd_dot_3gpp_dot_mcvideo_service_config_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcvideo-service-config+xml"}
let application_vnd_dot_3gpp_dot_mcvideo_transmission_request_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcvideo-transmission-request+xml"}
let application_vnd_dot_3gpp_dot_mcvideo_ue_config_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcvideo-ue-config+xml"}
let application_vnd_dot_3gpp_dot_mcvideo_user_profile_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mcvideo-user-profile+xml"}
let application_vnd_dot_3gpp_dot_mid_call_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.mid-call+xml"}
let application_vnd_dot_3gpp_dot_ngap : mime = {type_ = "application"; subtype = "vnd.3gpp.ngap"}
let application_vnd_dot_3gpp_dot_pfcp : mime = {type_ = "application"; subtype = "vnd.3gpp.pfcp"}
let application_vnd_dot_3gpp_dot_pic_bw_large : mime = {type_ = "application"; subtype = "vnd.3gpp.pic-bw-large"}
let application_vnd_dot_3gpp_dot_pic_bw_small : mime = {type_ = "application"; subtype = "vnd.3gpp.pic-bw-small"}
let application_vnd_dot_3gpp_dot_pic_bw_var : mime = {type_ = "application"; subtype = "vnd.3gpp.pic-bw-var"}
let application_vnd_dot_3gpp_dot_pinapp_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.pinapp-info+xml"}
let application_vnd_dot_3gpp_prose_pc3a_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp-prose-pc3a+xml"}
let application_vnd_dot_3gpp_prose_pc3ach_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp-prose-pc3ach+xml"}
let application_vnd_dot_3gpp_prose_pc3ch_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp-prose-pc3ch+xml"}
let application_vnd_dot_3gpp_prose_pc8_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp-prose-pc8+xml"}
let application_vnd_dot_3gpp_prose_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp-prose+xml"}
let application_vnd_dot_3gpp_dot_s1ap : mime = {type_ = "application"; subtype = "vnd.3gpp.s1ap"}
let application_vnd_dot_3gpp_dot_seal_app_comm_requirements_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-app-comm-requirements-info+xml"}
let application_vnd_dot_3gpp_dot_seal_data_delivery_info_plus_cbor : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-data-delivery-info+cbor"}
let application_vnd_dot_3gpp_dot_seal_data_delivery_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-data-delivery-info+xml"}
let application_vnd_dot_3gpp_dot_seal_group_doc_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-group-doc+xml"}
let application_vnd_dot_3gpp_dot_seal_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-info+xml"}
let application_vnd_dot_3gpp_dot_seal_location_info_plus_cbor : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-location-info+cbor"}
let application_vnd_dot_3gpp_dot_seal_location_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-location-info+xml"}
let application_vnd_dot_3gpp_dot_seal_mbms_usage_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-mbms-usage-info+xml"}
let application_vnd_dot_3gpp_dot_seal_mbs_usage_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-mbs-usage-info+xml"}
let application_vnd_dot_3gpp_dot_seal_network_qos_management_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-network-QoS-management-info+xml"}
let application_vnd_dot_3gpp_dot_seal_network_resource_info_plus_cbor : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-network-resource-info+cbor"}
let application_vnd_dot_3gpp_dot_seal_ue_config_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-ue-config-info+xml"}
let application_vnd_dot_3gpp_dot_seal_unicast_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-unicast-info+xml"}
let application_vnd_dot_3gpp_dot_seal_user_profile_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.seal-user-profile-info+xml"}
let application_vnd_dot_3gpp_dot_sms : mime = {type_ = "application"; subtype = "vnd.3gpp.sms"}
let application_vnd_dot_3gpp_dot_sms_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.sms+xml"}
let application_vnd_dot_3gpp_dot_srvcc_ext_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.srvcc-ext+xml"}
let application_vnd_dot_3gpp_dot_srvcc_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.SRVCC-info+xml"}
let application_vnd_dot_3gpp_dot_state_and_event_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.state-and-event-info+xml"}
let application_vnd_dot_3gpp_dot_ussd_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.ussd+xml"}
let application_vnd_dot_3gpp_dot_vae_info_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp.vae-info+xml"}
let application_vnd_dot_3gpp_v2x_local_service_information : mime = {type_ = "application"; subtype = "vnd.3gpp-v2x-local-service-information"}
let application_vnd_dot_3gpp2_dot_bcmcsinfo_plus_xml : mime = {type_ = "application"; subtype = "vnd.3gpp2.bcmcsinfo+xml"}
let application_vnd_dot_3gpp2_dot_sms : mime = {type_ = "application"; subtype = "vnd.3gpp2.sms"}
let application_vnd_dot_3gpp2_dot_tcap : mime = {type_ = "application"; subtype = "vnd.3gpp2.tcap"}
let application_vnd_dot_3gpp_dot_v2x : mime = {type_ = "application"; subtype = "vnd.3gpp.v2x"}
let application_vnd_dot_3lightssoftware_dot_imagescal : mime = {type_ = "application"; subtype = "vnd.3lightssoftware.imagescal"}
let application_vnd_dot_3m_dot_post_it_notes : mime = {type_ = "application"; subtype = "vnd.3M.Post-it-Notes"}
let application_vnd_dot_accpac_dot_simply_dot_aso : mime = {type_ = "application"; subtype = "vnd.accpac.simply.aso"}
let application_vnd_dot_accpac_dot_simply_dot_imp : mime = {type_ = "application"; subtype = "vnd.accpac.simply.imp"}
let application_vnd_dot_acm_dot_addressxfer_plus_json : mime = {type_ = "application"; subtype = "vnd.acm.addressxfer+json"}
let application_vnd_dot_acm_dot_chatbot_plus_json : mime = {type_ = "application"; subtype = "vnd.acm.chatbot+json"}
let application_vnd_dot_acucobol : mime = {type_ = "application"; subtype = "vnd.acucobol"}
let application_vnd_dot_acucorp : mime = {type_ = "application"; subtype = "vnd.acucorp"}
let application_vnd_dot_adobe_dot_flash_dot_movie : mime = {type_ = "application"; subtype = "vnd.adobe.flash.movie"}
let application_vnd_dot_adobe_dot_formscentral_dot_fcdt : mime = {type_ = "application"; subtype = "vnd.adobe.formscentral.fcdt"}
let application_vnd_dot_adobe_dot_fxp : mime = {type_ = "application"; subtype = "vnd.adobe.fxp"}
let application_vnd_dot_adobe_dot_partial_upload : mime = {type_ = "application"; subtype = "vnd.adobe.partial-upload"}
let application_vnd_dot_adobe_dot_xdp_plus_xml : mime = {type_ = "application"; subtype = "vnd.adobe.xdp+xml"}
let application_vnd_dot_aether_dot_imp : mime = {type_ = "application"; subtype = "vnd.aether.imp"}
let application_vnd_dot_afpc_dot_afplinedata : mime = {type_ = "application"; subtype = "vnd.afpc.afplinedata"}
let application_vnd_dot_afpc_dot_afplinedata_pagedef : mime = {type_ = "application"; subtype = "vnd.afpc.afplinedata-pagedef"}
let application_vnd_dot_afpc_dot_cmoca_cmresource : mime = {type_ = "application"; subtype = "vnd.afpc.cmoca-cmresource"}
let application_vnd_dot_afpc_dot_foca_charset : mime = {type_ = "application"; subtype = "vnd.afpc.foca-charset"}
let application_vnd_dot_afpc_dot_foca_codedfont : mime = {type_ = "application"; subtype = "vnd.afpc.foca-codedfont"}
let application_vnd_dot_afpc_dot_foca_codepage : mime = {type_ = "application"; subtype = "vnd.afpc.foca-codepage"}
let application_vnd_dot_afpc_dot_modca : mime = {type_ = "application"; subtype = "vnd.afpc.modca"}
let application_vnd_dot_afpc_dot_modca_cmtable : mime = {type_ = "application"; subtype = "vnd.afpc.modca-cmtable"}
let application_vnd_dot_afpc_dot_modca_formdef : mime = {type_ = "application"; subtype = "vnd.afpc.modca-formdef"}
let application_vnd_dot_afpc_dot_modca_mediummap : mime = {type_ = "application"; subtype = "vnd.afpc.modca-mediummap"}
let application_vnd_dot_afpc_dot_modca_objectcontainer : mime = {type_ = "application"; subtype = "vnd.afpc.modca-objectcontainer"}
let application_vnd_dot_afpc_dot_modca_overlay : mime = {type_ = "application"; subtype = "vnd.afpc.modca-overlay"}
let application_vnd_dot_afpc_dot_modca_pagesegment : mime = {type_ = "application"; subtype = "vnd.afpc.modca-pagesegment"}
let application_vnd_dot_age : mime = {type_ = "application"; subtype = "vnd.age"}
let application_vnd_dot_ah_barcode : mime = {type_ = "application"; subtype = "vnd.ah-barcode"}
let application_vnd_dot_ahead_dot_space : mime = {type_ = "application"; subtype = "vnd.ahead.space"}
let application_vnd_dot_aia : mime = {type_ = "application"; subtype = "vnd.aia"}
let application_vnd_dot_airzip_dot_filesecure_dot_azf : mime = {type_ = "application"; subtype = "vnd.airzip.filesecure.azf"}
let application_vnd_dot_airzip_dot_filesecure_dot_azs : mime = {type_ = "application"; subtype = "vnd.airzip.filesecure.azs"}
let application_vnd_dot_amadeus_plus_json : mime = {type_ = "application"; subtype = "vnd.amadeus+json"}
let application_vnd_dot_amazon_dot_mobi8_ebook : mime = {type_ = "application"; subtype = "vnd.amazon.mobi8-ebook"}
let application_vnd_dot_americandynamics_dot_acc : mime = {type_ = "application"; subtype = "vnd.americandynamics.acc"}
let application_vnd_dot_amiga_dot_ami : mime = {type_ = "application"; subtype = "vnd.amiga.ami"}
let application_vnd_dot_amundsen_dot_maze_plus_xml : mime = {type_ = "application"; subtype = "vnd.amundsen.maze+xml"}
let application_vnd_dot_android_dot_ota : mime = {type_ = "application"; subtype = "vnd.android.ota"}
let application_vnd_dot_anki : mime = {type_ = "application"; subtype = "vnd.anki"}
let application_vnd_dot_anser_web_certificate_issue_initiation : mime = {type_ = "application"; subtype = "vnd.anser-web-certificate-issue-initiation"}
let application_vnd_dot_antix_dot_game_component : mime = {type_ = "application"; subtype = "vnd.antix.game-component"}
let application_vnd_dot_apache_dot_arrow_dot_file : mime = {type_ = "application"; subtype = "vnd.apache.arrow.file"}
let application_vnd_dot_apache_dot_arrow_dot_stream : mime = {type_ = "application"; subtype = "vnd.apache.arrow.stream"}
let application_vnd_dot_apache_dot_parquet : mime = {type_ = "application"; subtype = "vnd.apache.parquet"}
let application_vnd_dot_apache_dot_thrift_dot_binary : mime = {type_ = "application"; subtype = "vnd.apache.thrift.binary"}
let application_vnd_dot_apache_dot_thrift_dot_compact : mime = {type_ = "application"; subtype = "vnd.apache.thrift.compact"}
let application_vnd_dot_apache_dot_thrift_dot_json : mime = {type_ = "application"; subtype = "vnd.apache.thrift.json"}
let application_vnd_dot_apexlang : mime = {type_ = "application"; subtype = "vnd.apexlang"}
let application_vnd_dot_api_plus_json : mime = {type_ = "application"; subtype = "vnd.api+json"}
let application_vnd_dot_aplextor_dot_warrp_plus_json : mime = {type_ = "application"; subtype = "vnd.aplextor.warrp+json"}
let application_vnd_dot_apothekende_dot_reservation_plus_json : mime = {type_ = "application"; subtype = "vnd.apothekende.reservation+json"}
let application_vnd_dot_apple_dot_installer_plus_xml : mime = {type_ = "application"; subtype = "vnd.apple.installer+xml"}
let application_vnd_dot_apple_dot_keynote : mime = {type_ = "application"; subtype = "vnd.apple.keynote"}
let application_vnd_dot_apple_dot_mpegurl : mime = {type_ = "application"; subtype = "vnd.apple.mpegurl"}
let application_vnd_dot_apple_dot_numbers : mime = {type_ = "application"; subtype = "vnd.apple.numbers"}
let application_vnd_dot_apple_dot_pages : mime = {type_ = "application"; subtype = "vnd.apple.pages"}
let application_vnd_dot_arastra_dot_swi : mime = {type_ = "application"; subtype = "vnd.arastra.swi"}
let application_vnd_dot_aristanetworks_dot_swi : mime = {type_ = "application"; subtype = "vnd.aristanetworks.swi"}
let application_vnd_dot_artisan_plus_json : mime = {type_ = "application"; subtype = "vnd.artisan+json"}
let application_vnd_dot_artsquare : mime = {type_ = "application"; subtype = "vnd.artsquare"}
let application_vnd_dot_as207960_dot_vas_dot_config_plus_jer : mime = {type_ = "application"; subtype = "vnd.as207960.vas.config+jer"}
let application_vnd_dot_as207960_dot_vas_dot_config_plus_uper : mime = {type_ = "application"; subtype = "vnd.as207960.vas.config+uper"}
let application_vnd_dot_as207960_dot_vas_dot_tap_plus_jer : mime = {type_ = "application"; subtype = "vnd.as207960.vas.tap+jer"}
let application_vnd_dot_as207960_dot_vas_dot_tap_plus_uper : mime = {type_ = "application"; subtype = "vnd.as207960.vas.tap+uper"}
let application_vnd_dot_astraea_software_dot_iota : mime = {type_ = "application"; subtype = "vnd.astraea-software.iota"}
let application_vnd_dot_audiograph : mime = {type_ = "application"; subtype = "vnd.audiograph"}
let application_vnd_dot_autopackage : mime = {type_ = "application"; subtype = "vnd.autopackage"}
let application_vnd_dot_avalon_plus_json : mime = {type_ = "application"; subtype = "vnd.avalon+json"}
let application_vnd_dot_avistar_plus_xml : mime = {type_ = "application"; subtype = "vnd.avistar+xml"}
let application_vnd_dot_balsamiq_dot_bmml_plus_xml : mime = {type_ = "application"; subtype = "vnd.balsamiq.bmml+xml"}
let application_vnd_dot_banana_accounting : mime = {type_ = "application"; subtype = "vnd.banana-accounting"}
let application_vnd_dot_bbf_dot_usp_dot_error : mime = {type_ = "application"; subtype = "vnd.bbf.usp.error"}
let application_vnd_dot_bbf_dot_usp_dot_msg : mime = {type_ = "application"; subtype = "vnd.bbf.usp.msg"}
let application_vnd_dot_bbf_dot_usp_dot_msg_plus_json : mime = {type_ = "application"; subtype = "vnd.bbf.usp.msg+json"}
let application_vnd_dot_balsamiq_dot_bmpr : mime = {type_ = "application"; subtype = "vnd.balsamiq.bmpr"}
let application_vnd_dot_bekitzur_stech_plus_json : mime = {type_ = "application"; subtype = "vnd.bekitzur-stech+json"}
let application_vnd_dot_belightsoft_dot_lhzd_plus_zip : mime = {type_ = "application"; subtype = "vnd.belightsoft.lhzd+zip"}
let application_vnd_dot_belightsoft_dot_lhzl_plus_zip : mime = {type_ = "application"; subtype = "vnd.belightsoft.lhzl+zip"}
let application_vnd_dot_bint_dot_med_content : mime = {type_ = "application"; subtype = "vnd.bint.med-content"}
let application_vnd_dot_biopax_dot_rdf_plus_xml : mime = {type_ = "application"; subtype = "vnd.biopax.rdf+xml"}
let application_vnd_dot_blink_idb_value_wrapper : mime = {type_ = "application"; subtype = "vnd.blink-idb-value-wrapper"}
let application_vnd_dot_blueice_dot_multipass : mime = {type_ = "application"; subtype = "vnd.blueice.multipass"}
let application_vnd_dot_bluetooth_dot_ep_dot_oob : mime = {type_ = "application"; subtype = "vnd.bluetooth.ep.oob"}
let application_vnd_dot_bluetooth_dot_le_dot_oob : mime = {type_ = "application"; subtype = "vnd.bluetooth.le.oob"}
let application_vnd_dot_bmi : mime = {type_ = "application"; subtype = "vnd.bmi"}
let application_vnd_dot_bpf : mime = {type_ = "application"; subtype = "vnd.bpf"}
let application_vnd_dot_bpf3 : mime = {type_ = "application"; subtype = "vnd.bpf3"}
let application_vnd_dot_businessobjects : mime = {type_ = "application"; subtype = "vnd.businessobjects"}
let application_vnd_dot_byu_dot_uapi_plus_json : mime = {type_ = "application"; subtype = "vnd.byu.uapi+json"}
let application_vnd_dot_bzip3 : mime = {type_ = "application"; subtype = "vnd.bzip3"}
let application_vnd_dot_c3voc_dot_schedule_plus_xml : mime = {type_ = "application"; subtype = "vnd.c3voc.schedule+xml"}
let application_vnd_dot_cab_jscript : mime = {type_ = "application"; subtype = "vnd.cab-jscript"}
let application_vnd_dot_canon_cpdl : mime = {type_ = "application"; subtype = "vnd.canon-cpdl"}
let application_vnd_dot_canon_lips : mime = {type_ = "application"; subtype = "vnd.canon-lips"}
let application_vnd_dot_capasystems_pg_plus_json : mime = {type_ = "application"; subtype = "vnd.capasystems-pg+json"}
let application_vnd_dot_cel : mime = {type_ = "application"; subtype = "vnd.cel"}
let application_vnd_dot_cendio_dot_thinlinc_dot_clientconf : mime = {type_ = "application"; subtype = "vnd.cendio.thinlinc.clientconf"}
let application_vnd_dot_century_systems_dot_tcp_stream : mime = {type_ = "application"; subtype = "vnd.century-systems.tcp_stream"}
let application_vnd_dot_chemdraw_plus_xml : mime = {type_ = "application"; subtype = "vnd.chemdraw+xml"}
let application_vnd_dot_chess_pgn : mime = {type_ = "application"; subtype = "vnd.chess-pgn"}
let application_vnd_dot_chipnuts_dot_karaoke_mmd : mime = {type_ = "application"; subtype = "vnd.chipnuts.karaoke-mmd"}
let application_vnd_dot_ciedi : mime = {type_ = "application"; subtype = "vnd.ciedi"}
let application_vnd_dot_cinderella : mime = {type_ = "application"; subtype = "vnd.cinderella"}
let application_vnd_dot_cirpack_dot_isdn_ext : mime = {type_ = "application"; subtype = "vnd.cirpack.isdn-ext"}
let application_vnd_dot_citationstyles_dot_style_plus_xml : mime = {type_ = "application"; subtype = "vnd.citationstyles.style+xml"}
let application_vnd_dot_claymore : mime = {type_ = "application"; subtype = "vnd.claymore"}
let application_vnd_dot_cloanto_dot_rp9 : mime = {type_ = "application"; subtype = "vnd.cloanto.rp9"}
let application_vnd_dot_clonk_dot_c4group : mime = {type_ = "application"; subtype = "vnd.clonk.c4group"}
let application_vnd_dot_cluetrust_dot_cartomobile_config : mime = {type_ = "application"; subtype = "vnd.cluetrust.cartomobile-config"}
let application_vnd_dot_cluetrust_dot_cartomobile_config_pkg : mime = {type_ = "application"; subtype = "vnd.cluetrust.cartomobile-config-pkg"}
let application_vnd_dot_cmmf_configuration_information_plus_json : mime = {type_ = "application"; subtype = "vnd.cmmf-configuration-information+json"}
let application_vnd_dot_cmmf_efd_plus_xml : mime = {type_ = "application"; subtype = "vnd.cmmf-efd+xml"}
let application_vnd_dot_cmmf_encoder_configuration_plus_json : mime = {type_ = "application"; subtype = "vnd.cmmf-encoder-configuration+json"}
let application_vnd_dot_cncf_dot_helm_dot_chart_dot_content_dot_v1_dot_tar_plus_gzip : mime = {type_ = "application"; subtype = "vnd.cncf.helm.chart.content.v1.tar+gzip"}
let application_vnd_dot_cncf_dot_helm_dot_chart_dot_provenance_dot_v1_dot_prov : mime = {type_ = "application"; subtype = "vnd.cncf.helm.chart.provenance.v1.prov"}
let application_vnd_dot_cncf_dot_helm_dot_config_dot_v1_plus_json : mime = {type_ = "application"; subtype = "vnd.cncf.helm.config.v1+json"}
let application_vnd_dot_coffeescript : mime = {type_ = "application"; subtype = "vnd.coffeescript"}
let application_vnd_dot_collabio_dot_xodocuments_dot_document : mime = {type_ = "application"; subtype = "vnd.collabio.xodocuments.document"}
let application_vnd_dot_collabio_dot_xodocuments_dot_document_template : mime = {type_ = "application"; subtype = "vnd.collabio.xodocuments.document-template"}
let application_vnd_dot_collabio_dot_xodocuments_dot_presentation : mime = {type_ = "application"; subtype = "vnd.collabio.xodocuments.presentation"}
let application_vnd_dot_collabio_dot_xodocuments_dot_presentation_template : mime = {type_ = "application"; subtype = "vnd.collabio.xodocuments.presentation-template"}
let application_vnd_dot_collabio_dot_xodocuments_dot_spreadsheet : mime = {type_ = "application"; subtype = "vnd.collabio.xodocuments.spreadsheet"}
let application_vnd_dot_collabio_dot_xodocuments_dot_spreadsheet_template : mime = {type_ = "application"; subtype = "vnd.collabio.xodocuments.spreadsheet-template"}
let application_vnd_dot_collection_dot_doc_plus_json : mime = {type_ = "application"; subtype = "vnd.collection.doc+json"}
let application_vnd_dot_collection_plus_json : mime = {type_ = "application"; subtype = "vnd.collection+json"}
let application_vnd_dot_collection_dot_next_plus_json : mime = {type_ = "application"; subtype = "vnd.collection.next+json"}
let application_vnd_dot_comicbook_rar : mime = {type_ = "application"; subtype = "vnd.comicbook-rar"}
let application_vnd_dot_comicbook_plus_zip : mime = {type_ = "application"; subtype = "vnd.comicbook+zip"}
let application_vnd_dot_commerce_battelle : mime = {type_ = "application"; subtype = "vnd.commerce-battelle"}
let application_vnd_dot_commonspace : mime = {type_ = "application"; subtype = "vnd.commonspace"}
let application_vnd_dot_coreos_dot_ignition_plus_json : mime = {type_ = "application"; subtype = "vnd.coreos.ignition+json"}
let application_vnd_dot_cosmocaller : mime = {type_ = "application"; subtype = "vnd.cosmocaller"}
let application_vnd_dot_contact_dot_cmsg : mime = {type_ = "application"; subtype = "vnd.contact.cmsg"}
let application_vnd_dot_crick_dot_clicker : mime = {type_ = "application"; subtype = "vnd.crick.clicker"}
let application_vnd_dot_crick_dot_clicker_dot_keyboard : mime = {type_ = "application"; subtype = "vnd.crick.clicker.keyboard"}
let application_vnd_dot_crick_dot_clicker_dot_palette : mime = {type_ = "application"; subtype = "vnd.crick.clicker.palette"}
let application_vnd_dot_crick_dot_clicker_dot_template : mime = {type_ = "application"; subtype = "vnd.crick.clicker.template"}
let application_vnd_dot_crick_dot_clicker_dot_wordbank : mime = {type_ = "application"; subtype = "vnd.crick.clicker.wordbank"}
let application_vnd_dot_criticaltools_dot_wbs_plus_xml : mime = {type_ = "application"; subtype = "vnd.criticaltools.wbs+xml"}
let application_vnd_dot_cryptii_dot_pipe_plus_json : mime = {type_ = "application"; subtype = "vnd.cryptii.pipe+json"}
let application_vnd_dot_crypto_shade_file : mime = {type_ = "application"; subtype = "vnd.crypto-shade-file"}
let application_vnd_dot_cryptomator_dot_encrypted : mime = {type_ = "application"; subtype = "vnd.cryptomator.encrypted"}
let application_vnd_dot_cryptomator_dot_vault : mime = {type_ = "application"; subtype = "vnd.cryptomator.vault"}
let application_vnd_dot_ctc_posml : mime = {type_ = "application"; subtype = "vnd.ctc-posml"}
let application_vnd_dot_ctct_dot_ws_plus_xml : mime = {type_ = "application"; subtype = "vnd.ctct.ws+xml"}
let application_vnd_dot_cups_pdf : mime = {type_ = "application"; subtype = "vnd.cups-pdf"}
let application_vnd_dot_cups_postscript : mime = {type_ = "application"; subtype = "vnd.cups-postscript"}
let application_vnd_dot_cups_ppd : mime = {type_ = "application"; subtype = "vnd.cups-ppd"}
let application_vnd_dot_cups_raster : mime = {type_ = "application"; subtype = "vnd.cups-raster"}
let application_vnd_dot_cups_raw : mime = {type_ = "application"; subtype = "vnd.cups-raw"}
let application_vnd_dot_curl : mime = {type_ = "application"; subtype = "vnd.curl"}
let application_vnd_dot_cyan_dot_dean_dot_root_plus_xml : mime = {type_ = "application"; subtype = "vnd.cyan.dean.root+xml"}
let application_vnd_dot_cybank : mime = {type_ = "application"; subtype = "vnd.cybank"}
let application_vnd_dot_cyclonedx_plus_json : mime = {type_ = "application"; subtype = "vnd.cyclonedx+json"}
let application_vnd_dot_cyclonedx_plus_xml : mime = {type_ = "application"; subtype = "vnd.cyclonedx+xml"}
let application_vnd_dot_d2l_dot_coursepackage1p0_plus_zip : mime = {type_ = "application"; subtype = "vnd.d2l.coursepackage1p0+zip"}
let application_vnd_dot_d3m_dataset : mime = {type_ = "application"; subtype = "vnd.d3m-dataset"}
let application_vnd_dot_d3m_problem : mime = {type_ = "application"; subtype = "vnd.d3m-problem"}
let application_vnd_dot_dart : mime = {type_ = "application"; subtype = "vnd.dart"}
let application_vnd_dot_data_vision_dot_rdz : mime = {type_ = "application"; subtype = "vnd.data-vision.rdz"}
let application_vnd_dot_datalog : mime = {type_ = "application"; subtype = "vnd.datalog"}
let application_vnd_dot_datapackage_plus_json : mime = {type_ = "application"; subtype = "vnd.datapackage+json"}
let application_vnd_dot_dataresource_plus_json : mime = {type_ = "application"; subtype = "vnd.dataresource+json"}
let application_vnd_dot_dbf : mime = {type_ = "application"; subtype = "vnd.dbf"}
let application_vnd_dot_dcmp_plus_xml : mime = {type_ = "application"; subtype = "vnd.dcmp+xml"}
let application_vnd_dot_debian_dot_binary_package : mime = {type_ = "application"; subtype = "vnd.debian.binary-package"}
let application_vnd_dot_dece_dot_data : mime = {type_ = "application"; subtype = "vnd.dece.data"}
let application_vnd_dot_dece_dot_ttml_plus_xml : mime = {type_ = "application"; subtype = "vnd.dece.ttml+xml"}
let application_vnd_dot_dece_dot_unspecified : mime = {type_ = "application"; subtype = "vnd.dece.unspecified"}
let application_vnd_dot_dece_dot_zip : mime = {type_ = "application"; subtype = "vnd.dece.zip"}
let application_vnd_dot_denovo_dot_fcselayout_link : mime = {type_ = "application"; subtype = "vnd.denovo.fcselayout-link"}
let application_vnd_dot_desmume_dot_movie : mime = {type_ = "application"; subtype = "vnd.desmume.movie"}
let application_vnd_dot_deut_plus_json : mime = {type_ = "application"; subtype = "vnd.deut+json"}
let application_vnd_dot_dir_bi_dot_plate_dl_nosuffix : mime = {type_ = "application"; subtype = "vnd.dir-bi.plate-dl-nosuffix"}
let application_vnd_dot_dm_dot_delegation_plus_xml : mime = {type_ = "application"; subtype = "vnd.dm.delegation+xml"}
let application_vnd_dot_dna : mime = {type_ = "application"; subtype = "vnd.dna"}
let application_vnd_dot_document_plus_json : mime = {type_ = "application"; subtype = "vnd.document+json"}
let application_vnd_dot_dolby_dot_mobile_dot_1 : mime = {type_ = "application"; subtype = "vnd.dolby.mobile.1"}
let application_vnd_dot_dolby_dot_mobile_dot_2 : mime = {type_ = "application"; subtype = "vnd.dolby.mobile.2"}
let application_vnd_dot_doremir_dot_scorecloud_binary_document : mime = {type_ = "application"; subtype = "vnd.doremir.scorecloud-binary-document"}
let application_vnd_dot_dpgraph : mime = {type_ = "application"; subtype = "vnd.dpgraph"}
let application_vnd_dot_dreamfactory : mime = {type_ = "application"; subtype = "vnd.dreamfactory"}
let application_vnd_dot_drive_plus_json : mime = {type_ = "application"; subtype = "vnd.drive+json"}
let application_vnd_dot_dtg_dot_local : mime = {type_ = "application"; subtype = "vnd.dtg.local"}
let application_vnd_dot_dtg_dot_local_dot_flash : mime = {type_ = "application"; subtype = "vnd.dtg.local.flash"}
let application_vnd_dot_dtg_dot_local_dot_html : mime = {type_ = "application"; subtype = "vnd.dtg.local.html"}
let application_vnd_dot_dvb_dot_ait : mime = {type_ = "application"; subtype = "vnd.dvb.ait"}
let application_vnd_dot_dvb_dot_dvbisl_plus_xml : mime = {type_ = "application"; subtype = "vnd.dvb.dvbisl+xml"}
let application_vnd_dot_dvb_dot_dvbj : mime = {type_ = "application"; subtype = "vnd.dvb.dvbj"}
let application_vnd_dot_dvb_dot_esgcontainer : mime = {type_ = "application"; subtype = "vnd.dvb.esgcontainer"}
let application_vnd_dot_dvb_dot_ipdcdftnotifaccess : mime = {type_ = "application"; subtype = "vnd.dvb.ipdcdftnotifaccess"}
let application_vnd_dot_dvb_dot_ipdcesgaccess : mime = {type_ = "application"; subtype = "vnd.dvb.ipdcesgaccess"}
let application_vnd_dot_dvb_dot_ipdcesgaccess2 : mime = {type_ = "application"; subtype = "vnd.dvb.ipdcesgaccess2"}
let application_vnd_dot_dvb_dot_ipdcesgpdd : mime = {type_ = "application"; subtype = "vnd.dvb.ipdcesgpdd"}
let application_vnd_dot_dvb_dot_ipdcroaming : mime = {type_ = "application"; subtype = "vnd.dvb.ipdcroaming"}
let application_vnd_dot_dvb_dot_iptv_dot_alfec_base : mime = {type_ = "application"; subtype = "vnd.dvb.iptv.alfec-base"}
let application_vnd_dot_dvb_dot_iptv_dot_alfec_enhancement : mime = {type_ = "application"; subtype = "vnd.dvb.iptv.alfec-enhancement"}
let application_vnd_dot_dvb_dot_notif_aggregate_root_plus_xml : mime = {type_ = "application"; subtype = "vnd.dvb.notif-aggregate-root+xml"}
let application_vnd_dot_dvb_dot_notif_container_plus_xml : mime = {type_ = "application"; subtype = "vnd.dvb.notif-container+xml"}
let application_vnd_dot_dvb_dot_notif_generic_plus_xml : mime = {type_ = "application"; subtype = "vnd.dvb.notif-generic+xml"}
let application_vnd_dot_dvb_dot_notif_ia_msglist_plus_xml : mime = {type_ = "application"; subtype = "vnd.dvb.notif-ia-msglist+xml"}
let application_vnd_dot_dvb_dot_notif_ia_registration_request_plus_xml : mime = {type_ = "application"; subtype = "vnd.dvb.notif-ia-registration-request+xml"}
let application_vnd_dot_dvb_dot_notif_ia_registration_response_plus_xml : mime = {type_ = "application"; subtype = "vnd.dvb.notif-ia-registration-response+xml"}
let application_vnd_dot_dvb_dot_notif_init_plus_xml : mime = {type_ = "application"; subtype = "vnd.dvb.notif-init+xml"}
let application_vnd_dot_dvb_dot_pfr : mime = {type_ = "application"; subtype = "vnd.dvb.pfr"}
let application_vnd_dot_dvb_dot_service : mime = {type_ = "application"; subtype = "vnd.dvb.service"}
let application_vnd_dot_dxr : mime = {type_ = "application"; subtype = "vnd.dxr"}
let application_vnd_dot_dynageo : mime = {type_ = "application"; subtype = "vnd.dynageo"}
let application_vnd_dot_dzr : mime = {type_ = "application"; subtype = "vnd.dzr"}
let application_vnd_dot_easykaraoke_dot_cdgdownload : mime = {type_ = "application"; subtype = "vnd.easykaraoke.cdgdownload"}
let application_vnd_dot_ecip_dot_rlp : mime = {type_ = "application"; subtype = "vnd.ecip.rlp"}
let application_vnd_dot_edulith_dot_edux_plus_json : mime = {type_ = "application"; subtype = "vnd.edulith.edux+json"}
let application_vnd_dot_ecdis_update : mime = {type_ = "application"; subtype = "vnd.ecdis-update"}
let application_vnd_dot_eclipse_dot_ditto_plus_json : mime = {type_ = "application"; subtype = "vnd.eclipse.ditto+json"}
let application_vnd_dot_ecowin_dot_chart : mime = {type_ = "application"; subtype = "vnd.ecowin.chart"}
let application_vnd_dot_ecowin_dot_filerequest : mime = {type_ = "application"; subtype = "vnd.ecowin.filerequest"}
let application_vnd_dot_ecowin_dot_fileupdate : mime = {type_ = "application"; subtype = "vnd.ecowin.fileupdate"}
let application_vnd_dot_ecowin_dot_series : mime = {type_ = "application"; subtype = "vnd.ecowin.series"}
let application_vnd_dot_ecowin_dot_seriesrequest : mime = {type_ = "application"; subtype = "vnd.ecowin.seriesrequest"}
let application_vnd_dot_ecowin_dot_seriesupdate : mime = {type_ = "application"; subtype = "vnd.ecowin.seriesupdate"}
let application_vnd_dot_efi_dot_img : mime = {type_ = "application"; subtype = "vnd.efi.img"}
let application_vnd_dot_efi_dot_iso : mime = {type_ = "application"; subtype = "vnd.efi.iso"}
let application_vnd_dot_eln_plus_zip : mime = {type_ = "application"; subtype = "vnd.eln+zip"}
let application_vnd_dot_emclient_dot_accessrequest_plus_xml : mime = {type_ = "application"; subtype = "vnd.emclient.accessrequest+xml"}
let application_vnd_dot_enliven : mime = {type_ = "application"; subtype = "vnd.enliven"}
let application_vnd_dot_enphase_dot_envoy : mime = {type_ = "application"; subtype = "vnd.enphase.envoy"}
let application_vnd_dot_eprints_dot_data_plus_xml : mime = {type_ = "application"; subtype = "vnd.eprints.data+xml"}
let application_vnd_dot_epson_dot_esf : mime = {type_ = "application"; subtype = "vnd.epson.esf"}
let application_vnd_dot_epson_dot_msf : mime = {type_ = "application"; subtype = "vnd.epson.msf"}
let application_vnd_dot_epson_dot_quickanime : mime = {type_ = "application"; subtype = "vnd.epson.quickanime"}
let application_vnd_dot_epson_dot_salt : mime = {type_ = "application"; subtype = "vnd.epson.salt"}
let application_vnd_dot_epson_dot_ssf : mime = {type_ = "application"; subtype = "vnd.epson.ssf"}
let application_vnd_dot_ericsson_dot_quickcall : mime = {type_ = "application"; subtype = "vnd.ericsson.quickcall"}
let application_vnd_dot_erofs : mime = {type_ = "application"; subtype = "vnd.erofs"}
let application_vnd_dot_espass_espass_plus_zip : mime = {type_ = "application"; subtype = "vnd.espass-espass+zip"}
let application_vnd_dot_eszigno3_plus_xml : mime = {type_ = "application"; subtype = "vnd.eszigno3+xml"}
let application_vnd_dot_etsi_dot_aoc_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.aoc+xml"}
let application_vnd_dot_etsi_dot_asic_s_plus_zip : mime = {type_ = "application"; subtype = "vnd.etsi.asic-s+zip"}
let application_vnd_dot_etsi_dot_asic_e_plus_zip : mime = {type_ = "application"; subtype = "vnd.etsi.asic-e+zip"}
let application_vnd_dot_etsi_dot_cug_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.cug+xml"}
let application_vnd_dot_etsi_dot_iptvcommand_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.iptvcommand+xml"}
let application_vnd_dot_etsi_dot_iptvdiscovery_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.iptvdiscovery+xml"}
let application_vnd_dot_etsi_dot_iptvprofile_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.iptvprofile+xml"}
let application_vnd_dot_etsi_dot_iptvsad_bc_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.iptvsad-bc+xml"}
let application_vnd_dot_etsi_dot_iptvsad_cod_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.iptvsad-cod+xml"}
let application_vnd_dot_etsi_dot_iptvsad_npvr_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.iptvsad-npvr+xml"}
let application_vnd_dot_etsi_dot_iptvservice_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.iptvservice+xml"}
let application_vnd_dot_etsi_dot_iptvsync_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.iptvsync+xml"}
let application_vnd_dot_etsi_dot_iptvueprofile_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.iptvueprofile+xml"}
let application_vnd_dot_etsi_dot_mcid_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.mcid+xml"}
let application_vnd_dot_etsi_dot_mheg5 : mime = {type_ = "application"; subtype = "vnd.etsi.mheg5"}
let application_vnd_dot_etsi_dot_overload_control_policy_dataset_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.overload-control-policy-dataset+xml"}
let application_vnd_dot_etsi_dot_pstn_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.pstn+xml"}
let application_vnd_dot_etsi_dot_sci_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.sci+xml"}
let application_vnd_dot_etsi_dot_simservs_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.simservs+xml"}
let application_vnd_dot_etsi_dot_timestamp_token : mime = {type_ = "application"; subtype = "vnd.etsi.timestamp-token"}
let application_vnd_dot_etsi_dot_tsl_plus_xml : mime = {type_ = "application"; subtype = "vnd.etsi.tsl+xml"}
let application_vnd_dot_etsi_dot_tsl_dot_der : mime = {type_ = "application"; subtype = "vnd.etsi.tsl.der"}
let application_vnd_dot_eu_dot_kasparian_dot_car_plus_json : mime = {type_ = "application"; subtype = "vnd.eu.kasparian.car+json"}
let application_vnd_dot_eudora_dot_data : mime = {type_ = "application"; subtype = "vnd.eudora.data"}
let application_vnd_dot_evolv_dot_ecig_dot_profile : mime = {type_ = "application"; subtype = "vnd.evolv.ecig.profile"}
let application_vnd_dot_evolv_dot_ecig_dot_settings : mime = {type_ = "application"; subtype = "vnd.evolv.ecig.settings"}
let application_vnd_dot_evolv_dot_ecig_dot_theme : mime = {type_ = "application"; subtype = "vnd.evolv.ecig.theme"}
let application_vnd_dot_exstream_empower_plus_zip : mime = {type_ = "application"; subtype = "vnd.exstream-empower+zip"}
let application_vnd_dot_exstream_package : mime = {type_ = "application"; subtype = "vnd.exstream-package"}
let application_vnd_dot_ezpix_album : mime = {type_ = "application"; subtype = "vnd.ezpix-album"}
let application_vnd_dot_ezpix_package : mime = {type_ = "application"; subtype = "vnd.ezpix-package"}
let application_vnd_dot_f_secure_dot_mobile : mime = {type_ = "application"; subtype = "vnd.f-secure.mobile"}
let application_vnd_dot_faf_plus_yaml : mime = {type_ = "application"; subtype = "vnd.faf+yaml"}
let application_vnd_dot_fastcopy_disk_image : mime = {type_ = "application"; subtype = "vnd.fastcopy-disk-image"}
let application_vnd_dot_familysearch_dot_gedcom_plus_zip : mime = {type_ = "application"; subtype = "vnd.familysearch.gedcom+zip"}
let application_vnd_dot_fdsn_dot_mseed : mime = {type_ = "application"; subtype = "vnd.fdsn.mseed"}
let application_vnd_dot_fdsn_dot_seed : mime = {type_ = "application"; subtype = "vnd.fdsn.seed"}
let application_vnd_dot_fdsn_dot_stationxml_plus_xml : mime = {type_ = "application"; subtype = "vnd.fdsn.stationxml+xml"}
let application_vnd_dot_ffsns : mime = {type_ = "application"; subtype = "vnd.ffsns"}
let application_vnd_dot_fgb : mime = {type_ = "application"; subtype = "vnd.fgb"}
let application_vnd_dot_ficlab_dot_flb_plus_zip : mime = {type_ = "application"; subtype = "vnd.ficlab.flb+zip"}
let application_vnd_dot_filmit_dot_zfc : mime = {type_ = "application"; subtype = "vnd.filmit.zfc"}
let application_vnd_dot_fints : mime = {type_ = "application"; subtype = "vnd.fints"}
let application_vnd_dot_firemonkeys_dot_cloudcell : mime = {type_ = "application"; subtype = "vnd.firemonkeys.cloudcell"}
let application_vnd_dot_flographit : mime = {type_ = "application"; subtype = "vnd.FloGraphIt"}
let application_vnd_dot_fluxtime_dot_clip : mime = {type_ = "application"; subtype = "vnd.fluxtime.clip"}
let application_vnd_dot_font_fontforge_sfd : mime = {type_ = "application"; subtype = "vnd.font-fontforge-sfd"}
let application_vnd_dot_foritech_dot_container : mime = {type_ = "application"; subtype = "vnd.foritech.container"}
let application_vnd_dot_framemaker : mime = {type_ = "application"; subtype = "vnd.framemaker"}
let application_vnd_dot_freelog_dot_comic : mime = {type_ = "application"; subtype = "vnd.freelog.comic"}
let application_vnd_dot_frogans_dot_fnc : mime = {type_ = "application"; subtype = "vnd.frogans.fnc"}
let application_vnd_dot_frogans_dot_ltf : mime = {type_ = "application"; subtype = "vnd.frogans.ltf"}
let application_vnd_dot_fsc_dot_weblaunch : mime = {type_ = "application"; subtype = "vnd.fsc.weblaunch"}
let application_vnd_dot_fujifilm_dot_fb_dot_docuworks : mime = {type_ = "application"; subtype = "vnd.fujifilm.fb.docuworks"}
let application_vnd_dot_fujifilm_dot_fb_dot_docuworks_dot_binder : mime = {type_ = "application"; subtype = "vnd.fujifilm.fb.docuworks.binder"}
let application_vnd_dot_fujifilm_dot_fb_dot_docuworks_dot_container : mime = {type_ = "application"; subtype = "vnd.fujifilm.fb.docuworks.container"}
let application_vnd_dot_fujifilm_dot_fb_dot_jfi_plus_xml : mime = {type_ = "application"; subtype = "vnd.fujifilm.fb.jfi+xml"}
let application_vnd_dot_fujitsu_dot_oasys : mime = {type_ = "application"; subtype = "vnd.fujitsu.oasys"}
let application_vnd_dot_fujitsu_dot_oasys2 : mime = {type_ = "application"; subtype = "vnd.fujitsu.oasys2"}
let application_vnd_dot_fujitsu_dot_oasys3 : mime = {type_ = "application"; subtype = "vnd.fujitsu.oasys3"}
let application_vnd_dot_fujitsu_dot_oasysgp : mime = {type_ = "application"; subtype = "vnd.fujitsu.oasysgp"}
let application_vnd_dot_fujitsu_dot_oasysprs : mime = {type_ = "application"; subtype = "vnd.fujitsu.oasysprs"}
let application_vnd_dot_fujixerox_dot_art4 : mime = {type_ = "application"; subtype = "vnd.fujixerox.ART4"}
let application_vnd_dot_fujixerox_dot_art_ex : mime = {type_ = "application"; subtype = "vnd.fujixerox.ART-EX"}
let application_vnd_dot_fujixerox_dot_ddd : mime = {type_ = "application"; subtype = "vnd.fujixerox.ddd"}
let application_vnd_dot_fujixerox_dot_docuworks : mime = {type_ = "application"; subtype = "vnd.fujixerox.docuworks"}
let application_vnd_dot_fujixerox_dot_docuworks_dot_binder : mime = {type_ = "application"; subtype = "vnd.fujixerox.docuworks.binder"}
let application_vnd_dot_fujixerox_dot_docuworks_dot_container : mime = {type_ = "application"; subtype = "vnd.fujixerox.docuworks.container"}
let application_vnd_dot_fujixerox_dot_hbpl : mime = {type_ = "application"; subtype = "vnd.fujixerox.HBPL"}
let application_vnd_dot_fut_misnet : mime = {type_ = "application"; subtype = "vnd.fut-misnet"}
let application_vnd_dot_futoin_plus_cbor : mime = {type_ = "application"; subtype = "vnd.futoin+cbor"}
let application_vnd_dot_futoin_plus_json : mime = {type_ = "application"; subtype = "vnd.futoin+json"}
let application_vnd_dot_fuzzysheet : mime = {type_ = "application"; subtype = "vnd.fuzzysheet"}
let application_vnd_dot_g3pix_dot_g3fc : mime = {type_ = "application"; subtype = "vnd.g3pix.g3fc"}
let application_vnd_dot_ga4gh_dot_passport_plus_jwt : mime = {type_ = "application"; subtype = "vnd.ga4gh.passport+jwt"}
let application_vnd_dot_genomatix_dot_tuxedo : mime = {type_ = "application"; subtype = "vnd.genomatix.tuxedo"}
let application_vnd_dot_genozip : mime = {type_ = "application"; subtype = "vnd.genozip"}
let application_vnd_dot_gentics_dot_grd_plus_json : mime = {type_ = "application"; subtype = "vnd.gentics.grd+json"}
let application_vnd_dot_gentoo_dot_catmetadata_plus_xml : mime = {type_ = "application"; subtype = "vnd.gentoo.catmetadata+xml"}
let application_vnd_dot_gentoo_dot_ebuild : mime = {type_ = "application"; subtype = "vnd.gentoo.ebuild"}
let application_vnd_dot_gentoo_dot_eclass : mime = {type_ = "application"; subtype = "vnd.gentoo.eclass"}
let application_vnd_dot_gentoo_dot_gpkg : mime = {type_ = "application"; subtype = "vnd.gentoo.gpkg"}
let application_vnd_dot_gentoo_dot_manifest : mime = {type_ = "application"; subtype = "vnd.gentoo.manifest"}
let application_vnd_dot_gentoo_dot_xpak : mime = {type_ = "application"; subtype = "vnd.gentoo.xpak"}
let application_vnd_dot_gentoo_dot_pkgmetadata_plus_xml : mime = {type_ = "application"; subtype = "vnd.gentoo.pkgmetadata+xml"}
let application_vnd_dot_geo_plus_json : mime = {type_ = "application"; subtype = "vnd.geo+json"}
let application_vnd_dot_geocube_plus_xml : mime = {type_ = "application"; subtype = "vnd.geocube+xml"}
let application_vnd_dot_geogebra_dot_file : mime = {type_ = "application"; subtype = "vnd.geogebra.file"}
let application_vnd_dot_geogebra_dot_pinboard : mime = {type_ = "application"; subtype = "vnd.geogebra.pinboard"}
let application_vnd_dot_geogebra_dot_slides : mime = {type_ = "application"; subtype = "vnd.geogebra.slides"}
let application_vnd_dot_geogebra_dot_tool : mime = {type_ = "application"; subtype = "vnd.geogebra.tool"}
let application_vnd_dot_geometry_explorer : mime = {type_ = "application"; subtype = "vnd.geometry-explorer"}
let application_vnd_dot_geonext : mime = {type_ = "application"; subtype = "vnd.geonext"}
let application_vnd_dot_geoplan : mime = {type_ = "application"; subtype = "vnd.geoplan"}
let application_vnd_dot_geospace : mime = {type_ = "application"; subtype = "vnd.geospace"}
let application_vnd_dot_gerber : mime = {type_ = "application"; subtype = "vnd.gerber"}
let application_vnd_dot_globalplatform_dot_card_content_mgt : mime = {type_ = "application"; subtype = "vnd.globalplatform.card-content-mgt"}
let application_vnd_dot_globalplatform_dot_card_content_mgt_response : mime = {type_ = "application"; subtype = "vnd.globalplatform.card-content-mgt-response"}
let application_vnd_dot_gmx : mime = {type_ = "application"; subtype = "vnd.gmx"}
let application_vnd_dot_gnu_dot_taler_dot_exchange_plus_json : mime = {type_ = "application"; subtype = "vnd.gnu.taler.exchange+json"}
let application_vnd_dot_gnu_dot_taler_dot_merchant_plus_json : mime = {type_ = "application"; subtype = "vnd.gnu.taler.merchant+json"}
let application_vnd_dot_google_earth_dot_kml_plus_xml : mime = {type_ = "application"; subtype = "vnd.google-earth.kml+xml"}
let application_vnd_dot_google_earth_dot_kmz : mime = {type_ = "application"; subtype = "vnd.google-earth.kmz"}
let application_vnd_dot_gov_dot_sk_dot_e_form_plus_xml : mime = {type_ = "application"; subtype = "vnd.gov.sk.e-form+xml"}
let application_vnd_dot_gov_dot_sk_dot_e_form_plus_zip : mime = {type_ = "application"; subtype = "vnd.gov.sk.e-form+zip"}
let application_vnd_dot_gov_dot_sk_dot_xmldatacontainer_plus_xml : mime = {type_ = "application"; subtype = "vnd.gov.sk.xmldatacontainer+xml"}
let application_vnd_dot_gp3 : mime = {type_ = "application"; subtype = "vnd.gp3"}
let application_vnd_dot_gpxsee_dot_map_plus_xml : mime = {type_ = "application"; subtype = "vnd.gpxsee.map+xml"}
let application_vnd_dot_grafeq : mime = {type_ = "application"; subtype = "vnd.grafeq"}
let application_vnd_dot_gridmp : mime = {type_ = "application"; subtype = "vnd.gridmp"}
let application_vnd_dot_groove_account : mime = {type_ = "application"; subtype = "vnd.groove-account"}
let application_vnd_dot_groove_help : mime = {type_ = "application"; subtype = "vnd.groove-help"}
let application_vnd_dot_groove_identity_message : mime = {type_ = "application"; subtype = "vnd.groove-identity-message"}
let application_vnd_dot_groove_injector : mime = {type_ = "application"; subtype = "vnd.groove-injector"}
let application_vnd_dot_groove_tool_message : mime = {type_ = "application"; subtype = "vnd.groove-tool-message"}
let application_vnd_dot_groove_tool_template : mime = {type_ = "application"; subtype = "vnd.groove-tool-template"}
let application_vnd_dot_groove_vcard : mime = {type_ = "application"; subtype = "vnd.groove-vcard"}
let application_vnd_dot_hal_plus_json : mime = {type_ = "application"; subtype = "vnd.hal+json"}
let application_vnd_dot_hal_plus_xml : mime = {type_ = "application"; subtype = "vnd.hal+xml"}
let application_vnd_dot_handheld_entertainment_plus_xml : mime = {type_ = "application"; subtype = "vnd.HandHeld-Entertainment+xml"}
let application_vnd_dot_hbci : mime = {type_ = "application"; subtype = "vnd.hbci"}
let application_vnd_dot_hc_plus_json : mime = {type_ = "application"; subtype = "vnd.hc+json"}
let application_vnd_dot_hcl_bireports : mime = {type_ = "application"; subtype = "vnd.hcl-bireports"}
let application_vnd_dot_hdfgroup_dot_hdf4 : mime = {type_ = "application"; subtype = "vnd.hdfgroup.hdf4"}
let application_vnd_dot_hdfgroup_dot_hdf5 : mime = {type_ = "application"; subtype = "vnd.hdfgroup.hdf5"}
let application_vnd_dot_hdt : mime = {type_ = "application"; subtype = "vnd.hdt"}
let application_vnd_dot_heroku_plus_json : mime = {type_ = "application"; subtype = "vnd.heroku+json"}
let application_vnd_dot_hhe_dot_lesson_player : mime = {type_ = "application"; subtype = "vnd.hhe.lesson-player"}
let application_vnd_dot_hp_hpgl : mime = {type_ = "application"; subtype = "vnd.hp-HPGL"}
let application_vnd_dot_hp_hpid : mime = {type_ = "application"; subtype = "vnd.hp-hpid"}
let application_vnd_dot_hp_hps : mime = {type_ = "application"; subtype = "vnd.hp-hps"}
let application_vnd_dot_hp_jlyt : mime = {type_ = "application"; subtype = "vnd.hp-jlyt"}
let application_vnd_dot_hp_pcl : mime = {type_ = "application"; subtype = "vnd.hp-PCL"}
let application_vnd_dot_hp_pclxl : mime = {type_ = "application"; subtype = "vnd.hp-PCLXL"}
let application_vnd_dot_hsl : mime = {type_ = "application"; subtype = "vnd.hsl"}
let application_vnd_dot_httphone : mime = {type_ = "application"; subtype = "vnd.httphone"}
let application_vnd_dot_hydrostatix_dot_sof_data : mime = {type_ = "application"; subtype = "vnd.hydrostatix.sof-data"}
let application_vnd_dot_hyper_item_plus_json : mime = {type_ = "application"; subtype = "vnd.hyper-item+json"}
let application_vnd_dot_hyper_plus_json : mime = {type_ = "application"; subtype = "vnd.hyper+json"}
let application_vnd_dot_hyperdrive_plus_json : mime = {type_ = "application"; subtype = "vnd.hyperdrive+json"}
let application_vnd_dot_hzn_3d_crossword : mime = {type_ = "application"; subtype = "vnd.hzn-3d-crossword"}
let application_vnd_dot_ibm_dot_afplinedata : mime = {type_ = "application"; subtype = "vnd.ibm.afplinedata"}
let application_vnd_dot_ibm_dot_electronic_media : mime = {type_ = "application"; subtype = "vnd.ibm.electronic-media"}
let application_vnd_dot_ibm_dot_minipay : mime = {type_ = "application"; subtype = "vnd.ibm.MiniPay"}
let application_vnd_dot_ibm_dot_modcap : mime = {type_ = "application"; subtype = "vnd.ibm.modcap"}
let application_vnd_dot_ibm_dot_rights_management : mime = {type_ = "application"; subtype = "vnd.ibm.rights-management"}
let application_vnd_dot_ibm_dot_secure_container : mime = {type_ = "application"; subtype = "vnd.ibm.secure-container"}
let application_vnd_dot_iccprofile : mime = {type_ = "application"; subtype = "vnd.iccprofile"}
let application_vnd_dot_ieee_dot_1905 : mime = {type_ = "application"; subtype = "vnd.ieee.1905"}
let application_vnd_dot_igloader : mime = {type_ = "application"; subtype = "vnd.igloader"}
let application_vnd_dot_imagemeter_dot_folder_plus_zip : mime = {type_ = "application"; subtype = "vnd.imagemeter.folder+zip"}
let application_vnd_dot_imagemeter_dot_image_plus_zip : mime = {type_ = "application"; subtype = "vnd.imagemeter.image+zip"}
let application_vnd_dot_immervision_ivp : mime = {type_ = "application"; subtype = "vnd.immervision-ivp"}
let application_vnd_dot_immervision_ivu : mime = {type_ = "application"; subtype = "vnd.immervision-ivu"}
let application_vnd_dot_ims_dot_imsccv1p1 : mime = {type_ = "application"; subtype = "vnd.ims.imsccv1p1"}
let application_vnd_dot_ims_dot_imsccv1p2 : mime = {type_ = "application"; subtype = "vnd.ims.imsccv1p2"}
let application_vnd_dot_ims_dot_imsccv1p3 : mime = {type_ = "application"; subtype = "vnd.ims.imsccv1p3"}
let application_vnd_dot_ims_dot_lis_dot_v2_dot_result_plus_json : mime = {type_ = "application"; subtype = "vnd.ims.lis.v2.result+json"}
let application_vnd_dot_ims_dot_lti_dot_v2_dot_toolconsumerprofile_plus_json : mime = {type_ = "application"; subtype = "vnd.ims.lti.v2.toolconsumerprofile+json"}
let application_vnd_dot_ims_dot_lti_dot_v2_dot_toolproxy_dot_id_plus_json : mime = {type_ = "application"; subtype = "vnd.ims.lti.v2.toolproxy.id+json"}
let application_vnd_dot_ims_dot_lti_dot_v2_dot_toolproxy_plus_json : mime = {type_ = "application"; subtype = "vnd.ims.lti.v2.toolproxy+json"}
let application_vnd_dot_ims_dot_lti_dot_v2_dot_toolsettings_plus_json : mime = {type_ = "application"; subtype = "vnd.ims.lti.v2.toolsettings+json"}
let application_vnd_dot_ims_dot_lti_dot_v2_dot_toolsettings_dot_simple_plus_json : mime = {type_ = "application"; subtype = "vnd.ims.lti.v2.toolsettings.simple+json"}
let application_vnd_dot_informedcontrol_dot_rms_plus_xml : mime = {type_ = "application"; subtype = "vnd.informedcontrol.rms+xml"}
let application_vnd_dot_infotech_dot_project : mime = {type_ = "application"; subtype = "vnd.infotech.project"}
let application_vnd_dot_infotech_dot_project_plus_xml : mime = {type_ = "application"; subtype = "vnd.infotech.project+xml"}
let application_vnd_dot_informix_visionary : mime = {type_ = "application"; subtype = "vnd.informix-visionary"}
let application_vnd_dot_innopath_dot_wamp_dot_notification : mime = {type_ = "application"; subtype = "vnd.innopath.wamp.notification"}
let application_vnd_dot_insors_dot_igm : mime = {type_ = "application"; subtype = "vnd.insors.igm"}
let application_vnd_dot_intercon_dot_formnet : mime = {type_ = "application"; subtype = "vnd.intercon.formnet"}
let application_vnd_dot_intergeo : mime = {type_ = "application"; subtype = "vnd.intergeo"}
let application_vnd_dot_intertrust_dot_digibox : mime = {type_ = "application"; subtype = "vnd.intertrust.digibox"}
let application_vnd_dot_intertrust_dot_nncp : mime = {type_ = "application"; subtype = "vnd.intertrust.nncp"}
let application_vnd_dot_intu_dot_qbo : mime = {type_ = "application"; subtype = "vnd.intu.qbo"}
let application_vnd_dot_intu_dot_qfx : mime = {type_ = "application"; subtype = "vnd.intu.qfx"}
let application_vnd_dot_ipfs_dot_ipns_record : mime = {type_ = "application"; subtype = "vnd.ipfs.ipns-record"}
let application_vnd_dot_ipld_dot_car : mime = {type_ = "application"; subtype = "vnd.ipld.car"}
let application_vnd_dot_ipld_dot_dag_cbor : mime = {type_ = "application"; subtype = "vnd.ipld.dag-cbor"}
let application_vnd_dot_ipld_dot_dag_json : mime = {type_ = "application"; subtype = "vnd.ipld.dag-json"}
let application_vnd_dot_ipld_dot_raw : mime = {type_ = "application"; subtype = "vnd.ipld.raw"}
let application_vnd_dot_iptc_dot_g2_dot_catalogitem_plus_xml : mime = {type_ = "application"; subtype = "vnd.iptc.g2.catalogitem+xml"}
let application_vnd_dot_iptc_dot_g2_dot_conceptitem_plus_xml : mime = {type_ = "application"; subtype = "vnd.iptc.g2.conceptitem+xml"}
let application_vnd_dot_iptc_dot_g2_dot_knowledgeitem_plus_xml : mime = {type_ = "application"; subtype = "vnd.iptc.g2.knowledgeitem+xml"}
let application_vnd_dot_iptc_dot_g2_dot_newsitem_plus_xml : mime = {type_ = "application"; subtype = "vnd.iptc.g2.newsitem+xml"}
let application_vnd_dot_iptc_dot_g2_dot_newsmessage_plus_xml : mime = {type_ = "application"; subtype = "vnd.iptc.g2.newsmessage+xml"}
let application_vnd_dot_iptc_dot_g2_dot_packageitem_plus_xml : mime = {type_ = "application"; subtype = "vnd.iptc.g2.packageitem+xml"}
let application_vnd_dot_iptc_dot_g2_dot_planningitem_plus_xml : mime = {type_ = "application"; subtype = "vnd.iptc.g2.planningitem+xml"}
let application_vnd_dot_ipunplugged_dot_rcprofile : mime = {type_ = "application"; subtype = "vnd.ipunplugged.rcprofile"}
let application_vnd_dot_irepository_dot_package_plus_xml : mime = {type_ = "application"; subtype = "vnd.irepository.package+xml"}
let application_vnd_dot_is_xpr : mime = {type_ = "application"; subtype = "vnd.is-xpr"}
let application_vnd_dot_isac_dot_fcs : mime = {type_ = "application"; subtype = "vnd.isac.fcs"}
let application_vnd_dot_jam : mime = {type_ = "application"; subtype = "vnd.jam"}
let application_vnd_dot_iso11783_10_plus_zip : mime = {type_ = "application"; subtype = "vnd.iso11783-10+zip"}
let application_vnd_dot_japannet_directory_service : mime = {type_ = "application"; subtype = "vnd.japannet-directory-service"}
let application_vnd_dot_japannet_jpnstore_wakeup : mime = {type_ = "application"; subtype = "vnd.japannet-jpnstore-wakeup"}
let application_vnd_dot_japannet_payment_wakeup : mime = {type_ = "application"; subtype = "vnd.japannet-payment-wakeup"}
let application_vnd_dot_japannet_registration : mime = {type_ = "application"; subtype = "vnd.japannet-registration"}
let application_vnd_dot_japannet_registration_wakeup : mime = {type_ = "application"; subtype = "vnd.japannet-registration-wakeup"}
let application_vnd_dot_japannet_setstore_wakeup : mime = {type_ = "application"; subtype = "vnd.japannet-setstore-wakeup"}
let application_vnd_dot_japannet_verification : mime = {type_ = "application"; subtype = "vnd.japannet-verification"}
let application_vnd_dot_japannet_verification_wakeup : mime = {type_ = "application"; subtype = "vnd.japannet-verification-wakeup"}
let application_vnd_dot_jcp_dot_javame_dot_midlet_rms : mime = {type_ = "application"; subtype = "vnd.jcp.javame.midlet-rms"}
let application_vnd_dot_jisp : mime = {type_ = "application"; subtype = "vnd.jisp"}
let application_vnd_dot_joost_dot_joda_archive : mime = {type_ = "application"; subtype = "vnd.joost.joda-archive"}
let application_vnd_dot_jsk_dot_isdn_ngn : mime = {type_ = "application"; subtype = "vnd.jsk.isdn-ngn"}
let application_vnd_dot_kahootz : mime = {type_ = "application"; subtype = "vnd.kahootz"}
let application_vnd_dot_kde_dot_karbon : mime = {type_ = "application"; subtype = "vnd.kde.karbon"}
let application_vnd_dot_kde_dot_kchart : mime = {type_ = "application"; subtype = "vnd.kde.kchart"}
let application_vnd_dot_kde_dot_kformula : mime = {type_ = "application"; subtype = "vnd.kde.kformula"}
let application_vnd_dot_kde_dot_kivio : mime = {type_ = "application"; subtype = "vnd.kde.kivio"}
let application_vnd_dot_kde_dot_kontour : mime = {type_ = "application"; subtype = "vnd.kde.kontour"}
let application_vnd_dot_kde_dot_kpresenter : mime = {type_ = "application"; subtype = "vnd.kde.kpresenter"}
let application_vnd_dot_kde_dot_kspread : mime = {type_ = "application"; subtype = "vnd.kde.kspread"}
let application_vnd_dot_kde_dot_kword : mime = {type_ = "application"; subtype = "vnd.kde.kword"}
let application_vnd_dot_kdl : mime = {type_ = "application"; subtype = "vnd.kdl"}
let application_vnd_dot_kenameaapp : mime = {type_ = "application"; subtype = "vnd.kenameaapp"}
let application_vnd_dot_keyman_dot_kmp_plus_zip : mime = {type_ = "application"; subtype = "vnd.keyman.kmp+zip"}
let application_vnd_dot_keyman_dot_kmx : mime = {type_ = "application"; subtype = "vnd.keyman.kmx"}
let application_vnd_dot_kidspiration : mime = {type_ = "application"; subtype = "vnd.kidspiration"}
let application_vnd_dot_kinar : mime = {type_ = "application"; subtype = "vnd.Kinar"}
let application_vnd_dot_koan : mime = {type_ = "application"; subtype = "vnd.koan"}
let application_vnd_dot_kodak_descriptor : mime = {type_ = "application"; subtype = "vnd.kodak-descriptor"}
let application_vnd_dot_las : mime = {type_ = "application"; subtype = "vnd.las"}
let application_vnd_dot_las_dot_las_plus_json : mime = {type_ = "application"; subtype = "vnd.las.las+json"}
let application_vnd_dot_las_dot_las_plus_xml : mime = {type_ = "application"; subtype = "vnd.las.las+xml"}
let application_vnd_dot_laszip : mime = {type_ = "application"; subtype = "vnd.laszip"}
let application_vnd_dot_ldev_dot_productlicensing : mime = {type_ = "application"; subtype = "vnd.ldev.productlicensing"}
let application_vnd_dot_leap_plus_json : mime = {type_ = "application"; subtype = "vnd.leap+json"}
let application_vnd_dot_liberty_request_plus_xml : mime = {type_ = "application"; subtype = "vnd.liberty-request+xml"}
let application_vnd_dot_llamagraphics_dot_life_balance_dot_desktop : mime = {type_ = "application"; subtype = "vnd.llamagraphics.life-balance.desktop"}
let application_vnd_dot_llamagraphics_dot_life_balance_dot_exchange_plus_xml : mime = {type_ = "application"; subtype = "vnd.llamagraphics.life-balance.exchange+xml"}
let application_vnd_dot_logipipe_dot_circuit_plus_zip : mime = {type_ = "application"; subtype = "vnd.logipipe.circuit+zip"}
let application_vnd_dot_loom : mime = {type_ = "application"; subtype = "vnd.loom"}
let application_vnd_dot_lotus_1_2_3 : mime = {type_ = "application"; subtype = "vnd.lotus-1-2-3"}
let application_vnd_dot_lotus_approach : mime = {type_ = "application"; subtype = "vnd.lotus-approach"}
let application_vnd_dot_lotus_freelance : mime = {type_ = "application"; subtype = "vnd.lotus-freelance"}
let application_vnd_dot_lotus_notes : mime = {type_ = "application"; subtype = "vnd.lotus-notes"}
let application_vnd_dot_lotus_organizer : mime = {type_ = "application"; subtype = "vnd.lotus-organizer"}
let application_vnd_dot_lotus_screencam : mime = {type_ = "application"; subtype = "vnd.lotus-screencam"}
let application_vnd_dot_lotus_wordpro : mime = {type_ = "application"; subtype = "vnd.lotus-wordpro"}
let application_vnd_dot_macports_dot_portpkg : mime = {type_ = "application"; subtype = "vnd.macports.portpkg"}
let application_vnd_dot_majikah_dot_bundle : mime = {type_ = "application"; subtype = "vnd.majikah.bundle"}
let application_vnd_dot_maml : mime = {type_ = "application"; subtype = "vnd.maml"}
let application_vnd_dot_mapbox_vector_tile : mime = {type_ = "application"; subtype = "vnd.mapbox-vector-tile"}
let application_vnd_dot_marlin_dot_drm_dot_actiontoken_plus_xml : mime = {type_ = "application"; subtype = "vnd.marlin.drm.actiontoken+xml"}
let application_vnd_dot_marlin_dot_drm_dot_conftoken_plus_xml : mime = {type_ = "application"; subtype = "vnd.marlin.drm.conftoken+xml"}
let application_vnd_dot_marlin_dot_drm_dot_license_plus_xml : mime = {type_ = "application"; subtype = "vnd.marlin.drm.license+xml"}
let application_vnd_dot_marlin_dot_drm_dot_mdcf : mime = {type_ = "application"; subtype = "vnd.marlin.drm.mdcf"}
let application_vnd_dot_mason_plus_json : mime = {type_ = "application"; subtype = "vnd.mason+json"}
let application_vnd_dot_maxar_dot_archive_dot_3tz_plus_zip : mime = {type_ = "application"; subtype = "vnd.maxar.archive.3tz+zip"}
let application_vnd_dot_maxmind_dot_maxmind_db : mime = {type_ = "application"; subtype = "vnd.maxmind.maxmind-db"}
let application_vnd_dot_mcd : mime = {type_ = "application"; subtype = "vnd.mcd"}
let application_vnd_dot_mdl : mime = {type_ = "application"; subtype = "vnd.mdl"}
let application_vnd_dot_mdl_mbsdf : mime = {type_ = "application"; subtype = "vnd.mdl-mbsdf"}
let application_vnd_dot_medcalcdata : mime = {type_ = "application"; subtype = "vnd.medcalcdata"}
let application_vnd_dot_mediastation_dot_cdkey : mime = {type_ = "application"; subtype = "vnd.mediastation.cdkey"}
let application_vnd_dot_medicalholodeck_dot_recordxr : mime = {type_ = "application"; subtype = "vnd.medicalholodeck.recordxr"}
let application_vnd_dot_meridian_slingshot : mime = {type_ = "application"; subtype = "vnd.meridian-slingshot"}
let application_vnd_dot_mermaid : mime = {type_ = "application"; subtype = "vnd.mermaid"}
let application_vnd_dot_mfer : mime = {type_ = "application"; subtype = "vnd.MFER"}
let application_vnd_dot_mfmp : mime = {type_ = "application"; subtype = "vnd.mfmp"}
let application_vnd_dot_micro_plus_json : mime = {type_ = "application"; subtype = "vnd.micro+json"}
let application_vnd_dot_micrografx_dot_flo : mime = {type_ = "application"; subtype = "vnd.micrografx.flo"}
let application_vnd_dot_micrografx_dot_igx : mime = {type_ = "application"; subtype = "vnd.micrografx.igx"}
let application_vnd_dot_microsoft_dot_portable_executable : mime = {type_ = "application"; subtype = "vnd.microsoft.portable-executable"}
let application_vnd_dot_microsoft_dot_windows_dot_thumbnail_cache : mime = {type_ = "application"; subtype = "vnd.microsoft.windows.thumbnail-cache"}
let application_vnd_dot_miele_plus_json : mime = {type_ = "application"; subtype = "vnd.miele+json"}
let application_vnd_dot_mif : mime = {type_ = "application"; subtype = "vnd.mif"}
let application_vnd_dot_minisoft_hp3000_save : mime = {type_ = "application"; subtype = "vnd.minisoft-hp3000-save"}
let application_vnd_dot_mitsubishi_dot_misty_guard_dot_trustweb : mime = {type_ = "application"; subtype = "vnd.mitsubishi.misty-guard.trustweb"}
let application_vnd_dot_mobius_dot_daf : mime = {type_ = "application"; subtype = "vnd.Mobius.DAF"}
let application_vnd_dot_mobius_dot_dis : mime = {type_ = "application"; subtype = "vnd.Mobius.DIS"}
let application_vnd_dot_mobius_dot_mbk : mime = {type_ = "application"; subtype = "vnd.Mobius.MBK"}
let application_vnd_dot_mobius_dot_mqy : mime = {type_ = "application"; subtype = "vnd.Mobius.MQY"}
let application_vnd_dot_mobius_dot_msl : mime = {type_ = "application"; subtype = "vnd.Mobius.MSL"}
let application_vnd_dot_mobius_dot_plc : mime = {type_ = "application"; subtype = "vnd.Mobius.PLC"}
let application_vnd_dot_mobius_dot_txf : mime = {type_ = "application"; subtype = "vnd.Mobius.TXF"}
let application_vnd_dot_modl : mime = {type_ = "application"; subtype = "vnd.modl"}
let application_vnd_dot_mophun_dot_application : mime = {type_ = "application"; subtype = "vnd.mophun.application"}
let application_vnd_dot_mophun_dot_certificate : mime = {type_ = "application"; subtype = "vnd.mophun.certificate"}
let application_vnd_dot_motorola_dot_flexsuite : mime = {type_ = "application"; subtype = "vnd.motorola.flexsuite"}
let application_vnd_dot_motorola_dot_flexsuite_dot_adsi : mime = {type_ = "application"; subtype = "vnd.motorola.flexsuite.adsi"}
let application_vnd_dot_motorola_dot_flexsuite_dot_fis : mime = {type_ = "application"; subtype = "vnd.motorola.flexsuite.fis"}
let application_vnd_dot_motorola_dot_flexsuite_dot_gotap : mime = {type_ = "application"; subtype = "vnd.motorola.flexsuite.gotap"}
let application_vnd_dot_motorola_dot_flexsuite_dot_kmr : mime = {type_ = "application"; subtype = "vnd.motorola.flexsuite.kmr"}
let application_vnd_dot_motorola_dot_flexsuite_dot_ttc : mime = {type_ = "application"; subtype = "vnd.motorola.flexsuite.ttc"}
let application_vnd_dot_motorola_dot_flexsuite_dot_wem : mime = {type_ = "application"; subtype = "vnd.motorola.flexsuite.wem"}
let application_vnd_dot_motorola_dot_iprm : mime = {type_ = "application"; subtype = "vnd.motorola.iprm"}
let application_vnd_dot_mozilla_dot_xul_plus_xml : mime = {type_ = "application"; subtype = "vnd.mozilla.xul+xml"}
let application_vnd_dot_ms_artgalry : mime = {type_ = "application"; subtype = "vnd.ms-artgalry"}
let application_vnd_dot_ms_asf : mime = {type_ = "application"; subtype = "vnd.ms-asf"}
let application_vnd_dot_ms_cab_compressed : mime = {type_ = "application"; subtype = "vnd.ms-cab-compressed"}
let application_vnd_dot_ms_3mfdocument : mime = {type_ = "application"; subtype = "vnd.ms-3mfdocument"}
let application_vnd_dot_ms_excel : mime = {type_ = "application"; subtype = "vnd.ms-excel"}
let application_vnd_dot_ms_excel_dot_addin_dot_macroenabled_dot_12 : mime = {type_ = "application"; subtype = "vnd.ms-excel.addin.macroEnabled.12"}
let application_vnd_dot_ms_excel_dot_sheet_dot_binary_dot_macroenabled_dot_12 : mime = {type_ = "application"; subtype = "vnd.ms-excel.sheet.binary.macroEnabled.12"}
let application_vnd_dot_ms_excel_dot_sheet_dot_macroenabled_dot_12 : mime = {type_ = "application"; subtype = "vnd.ms-excel.sheet.macroEnabled.12"}
let application_vnd_dot_ms_excel_dot_template_dot_macroenabled_dot_12 : mime = {type_ = "application"; subtype = "vnd.ms-excel.template.macroEnabled.12"}
let application_vnd_dot_ms_fontobject : mime = {type_ = "application"; subtype = "vnd.ms-fontobject"}
let application_vnd_dot_ms_htmlhelp : mime = {type_ = "application"; subtype = "vnd.ms-htmlhelp"}
let application_vnd_dot_ms_ims : mime = {type_ = "application"; subtype = "vnd.ms-ims"}
let application_vnd_dot_ms_lrm : mime = {type_ = "application"; subtype = "vnd.ms-lrm"}
let application_vnd_dot_ms_office_dot_activex_plus_xml : mime = {type_ = "application"; subtype = "vnd.ms-office.activeX+xml"}
let application_vnd_dot_ms_officetheme : mime = {type_ = "application"; subtype = "vnd.ms-officetheme"}
let application_vnd_dot_ms_playready_dot_initiator_plus_xml : mime = {type_ = "application"; subtype = "vnd.ms-playready.initiator+xml"}
let application_vnd_dot_ms_powerpoint : mime = {type_ = "application"; subtype = "vnd.ms-powerpoint"}
let application_vnd_dot_ms_powerpoint_dot_addin_dot_macroenabled_dot_12 : mime = {type_ = "application"; subtype = "vnd.ms-powerpoint.addin.macroEnabled.12"}
let application_vnd_dot_ms_powerpoint_dot_presentation_dot_macroenabled_dot_12 : mime = {type_ = "application"; subtype = "vnd.ms-powerpoint.presentation.macroEnabled.12"}
let application_vnd_dot_ms_powerpoint_dot_slide_dot_macroenabled_dot_12 : mime = {type_ = "application"; subtype = "vnd.ms-powerpoint.slide.macroEnabled.12"}
let application_vnd_dot_ms_powerpoint_dot_slideshow_dot_macroenabled_dot_12 : mime = {type_ = "application"; subtype = "vnd.ms-powerpoint.slideshow.macroEnabled.12"}
let application_vnd_dot_ms_powerpoint_dot_template_dot_macroenabled_dot_12 : mime = {type_ = "application"; subtype = "vnd.ms-powerpoint.template.macroEnabled.12"}
let application_vnd_dot_ms_printdevicecapabilities_plus_xml : mime = {type_ = "application"; subtype = "vnd.ms-PrintDeviceCapabilities+xml"}
let application_vnd_dot_ms_printschematicket_plus_xml : mime = {type_ = "application"; subtype = "vnd.ms-PrintSchemaTicket+xml"}
let application_vnd_dot_ms_project : mime = {type_ = "application"; subtype = "vnd.ms-project"}
let application_vnd_dot_ms_tnef : mime = {type_ = "application"; subtype = "vnd.ms-tnef"}
let application_vnd_dot_ms_windows_dot_devicepairing : mime = {type_ = "application"; subtype = "vnd.ms-windows.devicepairing"}
let application_vnd_dot_ms_windows_dot_nwprinting_dot_oob : mime = {type_ = "application"; subtype = "vnd.ms-windows.nwprinting.oob"}
let application_vnd_dot_ms_windows_dot_printerpairing : mime = {type_ = "application"; subtype = "vnd.ms-windows.printerpairing"}
let application_vnd_dot_ms_windows_dot_wsd_dot_oob : mime = {type_ = "application"; subtype = "vnd.ms-windows.wsd.oob"}
let application_vnd_dot_ms_wmdrm_dot_lic_chlg_req : mime = {type_ = "application"; subtype = "vnd.ms-wmdrm.lic-chlg-req"}
let application_vnd_dot_ms_wmdrm_dot_lic_resp : mime = {type_ = "application"; subtype = "vnd.ms-wmdrm.lic-resp"}
let application_vnd_dot_ms_wmdrm_dot_meter_chlg_req : mime = {type_ = "application"; subtype = "vnd.ms-wmdrm.meter-chlg-req"}
let application_vnd_dot_ms_wmdrm_dot_meter_resp : mime = {type_ = "application"; subtype = "vnd.ms-wmdrm.meter-resp"}
let application_vnd_dot_ms_word_dot_document_dot_macroenabled_dot_12 : mime = {type_ = "application"; subtype = "vnd.ms-word.document.macroEnabled.12"}
let application_vnd_dot_ms_word_dot_template_dot_macroenabled_dot_12 : mime = {type_ = "application"; subtype = "vnd.ms-word.template.macroEnabled.12"}
let application_vnd_dot_ms_works : mime = {type_ = "application"; subtype = "vnd.ms-works"}
let application_vnd_dot_ms_wpl : mime = {type_ = "application"; subtype = "vnd.ms-wpl"}
let application_vnd_dot_ms_xpsdocument : mime = {type_ = "application"; subtype = "vnd.ms-xpsdocument"}
let application_vnd_dot_msa_disk_image : mime = {type_ = "application"; subtype = "vnd.msa-disk-image"}
let application_vnd_dot_mseq : mime = {type_ = "application"; subtype = "vnd.mseq"}
let application_vnd_dot_msgpack : mime = {type_ = "application"; subtype = "vnd.msgpack"}
let application_vnd_dot_msign : mime = {type_ = "application"; subtype = "vnd.msign"}
let application_vnd_dot_multiad_dot_creator : mime = {type_ = "application"; subtype = "vnd.multiad.creator"}
let application_vnd_dot_multiad_dot_creator_dot_cif : mime = {type_ = "application"; subtype = "vnd.multiad.creator.cif"}
let application_vnd_dot_musician : mime = {type_ = "application"; subtype = "vnd.musician"}
let application_vnd_dot_music_niff : mime = {type_ = "application"; subtype = "vnd.music-niff"}
let application_vnd_dot_muvee_dot_style : mime = {type_ = "application"; subtype = "vnd.muvee.style"}
let application_vnd_dot_mynfc : mime = {type_ = "application"; subtype = "vnd.mynfc"}
let application_vnd_dot_nacamar_dot_ybrid_plus_json : mime = {type_ = "application"; subtype = "vnd.nacamar.ybrid+json"}
let application_vnd_dot_nato_dot_bindingdataobject_plus_cbor : mime = {type_ = "application"; subtype = "vnd.nato.bindingdataobject+cbor"}
let application_vnd_dot_nato_dot_bindingdataobject_plus_json : mime = {type_ = "application"; subtype = "vnd.nato.bindingdataobject+json"}
let application_vnd_dot_nato_dot_bindingdataobject_plus_xml : mime = {type_ = "application"; subtype = "vnd.nato.bindingdataobject+xml"}
let application_vnd_dot_nato_dot_openxmlformats_package_dot_iepd_plus_zip : mime = {type_ = "application"; subtype = "vnd.nato.openxmlformats-package.iepd+zip"}
let application_vnd_dot_ncd_dot_control : mime = {type_ = "application"; subtype = "vnd.ncd.control"}
let application_vnd_dot_ncd_dot_reference : mime = {type_ = "application"; subtype = "vnd.ncd.reference"}
let application_vnd_dot_nearst_dot_inv_plus_json : mime = {type_ = "application"; subtype = "vnd.nearst.inv+json"}
let application_vnd_dot_nebumind_dot_line : mime = {type_ = "application"; subtype = "vnd.nebumind.line"}
let application_vnd_dot_nervana : mime = {type_ = "application"; subtype = "vnd.nervana"}
let application_vnd_dot_netfpx : mime = {type_ = "application"; subtype = "vnd.netfpx"}
let application_vnd_dot_neurolanguage_dot_nlu : mime = {type_ = "application"; subtype = "vnd.neurolanguage.nlu"}
let application_vnd_dot_nimn : mime = {type_ = "application"; subtype = "vnd.nimn"}
let application_vnd_dot_nintendo_dot_snes_dot_rom : mime = {type_ = "application"; subtype = "vnd.nintendo.snes.rom"}
let application_vnd_dot_nintendo_dot_nitro_dot_rom : mime = {type_ = "application"; subtype = "vnd.nintendo.nitro.rom"}
let application_vnd_dot_nitf : mime = {type_ = "application"; subtype = "vnd.nitf"}
let application_vnd_dot_noblenet_directory : mime = {type_ = "application"; subtype = "vnd.noblenet-directory"}
let application_vnd_dot_noblenet_sealer : mime = {type_ = "application"; subtype = "vnd.noblenet-sealer"}
let application_vnd_dot_noblenet_web : mime = {type_ = "application"; subtype = "vnd.noblenet-web"}
let application_vnd_dot_nokia_dot_catalogs : mime = {type_ = "application"; subtype = "vnd.nokia.catalogs"}
let application_vnd_dot_nokia_dot_conml_plus_wbxml : mime = {type_ = "application"; subtype = "vnd.nokia.conml+wbxml"}
let application_vnd_dot_nokia_dot_conml_plus_xml : mime = {type_ = "application"; subtype = "vnd.nokia.conml+xml"}
let application_vnd_dot_nokia_dot_iptv_dot_config_plus_xml : mime = {type_ = "application"; subtype = "vnd.nokia.iptv.config+xml"}
let application_vnd_dot_nokia_dot_isds_radio_presets : mime = {type_ = "application"; subtype = "vnd.nokia.iSDS-radio-presets"}
let application_vnd_dot_nokia_dot_landmark_plus_wbxml : mime = {type_ = "application"; subtype = "vnd.nokia.landmark+wbxml"}
let application_vnd_dot_nokia_dot_landmark_plus_xml : mime = {type_ = "application"; subtype = "vnd.nokia.landmark+xml"}
let application_vnd_dot_nokia_dot_landmarkcollection_plus_xml : mime = {type_ = "application"; subtype = "vnd.nokia.landmarkcollection+xml"}
let application_vnd_dot_nokia_dot_ncd : mime = {type_ = "application"; subtype = "vnd.nokia.ncd"}
let application_vnd_dot_nokia_dot_n_gage_dot_ac_plus_xml : mime = {type_ = "application"; subtype = "vnd.nokia.n-gage.ac+xml"}
let application_vnd_dot_nokia_dot_n_gage_dot_data : mime = {type_ = "application"; subtype = "vnd.nokia.n-gage.data"}
let application_vnd_dot_nokia_dot_n_gage_dot_symbian_dot_install : mime = {type_ = "application"; subtype = "vnd.nokia.n-gage.symbian.install"}
let application_vnd_dot_nokia_dot_pcd_plus_wbxml : mime = {type_ = "application"; subtype = "vnd.nokia.pcd+wbxml"}
let application_vnd_dot_nokia_dot_pcd_plus_xml : mime = {type_ = "application"; subtype = "vnd.nokia.pcd+xml"}
let application_vnd_dot_nokia_dot_radio_preset : mime = {type_ = "application"; subtype = "vnd.nokia.radio-preset"}
let application_vnd_dot_nokia_dot_radio_presets : mime = {type_ = "application"; subtype = "vnd.nokia.radio-presets"}
let application_vnd_dot_novadigm_dot_edm : mime = {type_ = "application"; subtype = "vnd.novadigm.EDM"}
let application_vnd_dot_novadigm_dot_edx : mime = {type_ = "application"; subtype = "vnd.novadigm.EDX"}
let application_vnd_dot_novadigm_dot_ext : mime = {type_ = "application"; subtype = "vnd.novadigm.EXT"}
let application_vnd_dot_ntt_local_dot_content_share : mime = {type_ = "application"; subtype = "vnd.ntt-local.content-share"}
let application_vnd_dot_ntt_local_dot_file_transfer : mime = {type_ = "application"; subtype = "vnd.ntt-local.file-transfer"}
let application_vnd_dot_ntt_local_dot_ogw_remote_access : mime = {type_ = "application"; subtype = "vnd.ntt-local.ogw_remote-access"}
let application_vnd_dot_ntt_local_dot_sip_ta_remote : mime = {type_ = "application"; subtype = "vnd.ntt-local.sip-ta_remote"}
let application_vnd_dot_ntt_local_dot_sip_ta_tcp_stream : mime = {type_ = "application"; subtype = "vnd.ntt-local.sip-ta_tcp_stream"}
let application_vnd_dot_nubaltec_dot_nudoku_game : mime = {type_ = "application"; subtype = "vnd.nubaltec.nudoku-game"}
let application_vnd_dot_oai_dot_workflows : mime = {type_ = "application"; subtype = "vnd.oai.workflows"}
let application_vnd_dot_oai_dot_workflows_plus_json : mime = {type_ = "application"; subtype = "vnd.oai.workflows+json"}
let application_vnd_dot_oai_dot_workflows_plus_yaml : mime = {type_ = "application"; subtype = "vnd.oai.workflows+yaml"}
let application_vnd_dot_oasis_dot_opendocument_dot_base : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.base"}
let application_vnd_dot_oasis_dot_opendocument_dot_chart : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.chart"}
let application_vnd_dot_oasis_dot_opendocument_dot_chart_template : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.chart-template"}
let application_vnd_dot_oasis_dot_opendocument_dot_database : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.database"}
let application_vnd_dot_oasis_dot_opendocument_dot_formula : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.formula"}
let application_vnd_dot_oasis_dot_opendocument_dot_formula_template : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.formula-template"}
let application_vnd_dot_oasis_dot_opendocument_dot_graphics : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.graphics"}
let application_vnd_dot_oasis_dot_opendocument_dot_graphics_template : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.graphics-template"}
let application_vnd_dot_oasis_dot_opendocument_dot_image : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.image"}
let application_vnd_dot_oasis_dot_opendocument_dot_image_template : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.image-template"}
let application_vnd_dot_oasis_dot_opendocument_dot_presentation : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.presentation"}
let application_vnd_dot_oasis_dot_opendocument_dot_presentation_template : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.presentation-template"}
let application_vnd_dot_oasis_dot_opendocument_dot_spreadsheet : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.spreadsheet"}
let application_vnd_dot_oasis_dot_opendocument_dot_spreadsheet_template : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.spreadsheet-template"}
let application_vnd_dot_oasis_dot_opendocument_dot_text : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.text"}
let application_vnd_dot_oasis_dot_opendocument_dot_text_master : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.text-master"}
let application_vnd_dot_oasis_dot_opendocument_dot_text_master_template : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.text-master-template"}
let application_vnd_dot_oasis_dot_opendocument_dot_text_template : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.text-template"}
let application_vnd_dot_oasis_dot_opendocument_dot_text_web : mime = {type_ = "application"; subtype = "vnd.oasis.opendocument.text-web"}
let application_vnd_dot_obn : mime = {type_ = "application"; subtype = "vnd.obn"}
let application_vnd_dot_ocf_plus_cbor : mime = {type_ = "application"; subtype = "vnd.ocf+cbor"}
let application_vnd_dot_oci_dot_image_dot_manifest_dot_v1_plus_json : mime = {type_ = "application"; subtype = "vnd.oci.image.manifest.v1+json"}
let application_vnd_dot_oftn_dot_l10n_plus_json : mime = {type_ = "application"; subtype = "vnd.oftn.l10n+json"}
let application_vnd_dot_oipf_dot_contentaccessdownload_plus_xml : mime = {type_ = "application"; subtype = "vnd.oipf.contentaccessdownload+xml"}
let application_vnd_dot_oipf_dot_contentaccessstreaming_plus_xml : mime = {type_ = "application"; subtype = "vnd.oipf.contentaccessstreaming+xml"}
let application_vnd_dot_oipf_dot_cspg_hexbinary : mime = {type_ = "application"; subtype = "vnd.oipf.cspg-hexbinary"}
let application_vnd_dot_oipf_dot_dae_dot_svg_plus_xml : mime = {type_ = "application"; subtype = "vnd.oipf.dae.svg+xml"}
let application_vnd_dot_oipf_dot_dae_dot_xhtml_plus_xml : mime = {type_ = "application"; subtype = "vnd.oipf.dae.xhtml+xml"}
let application_vnd_dot_oipf_dot_mippvcontrolmessage_plus_xml : mime = {type_ = "application"; subtype = "vnd.oipf.mippvcontrolmessage+xml"}
let application_vnd_dot_oipf_dot_pae_dot_gem : mime = {type_ = "application"; subtype = "vnd.oipf.pae.gem"}
let application_vnd_dot_oipf_dot_spdiscovery_plus_xml : mime = {type_ = "application"; subtype = "vnd.oipf.spdiscovery+xml"}
let application_vnd_dot_oipf_dot_spdlist_plus_xml : mime = {type_ = "application"; subtype = "vnd.oipf.spdlist+xml"}
let application_vnd_dot_oipf_dot_ueprofile_plus_xml : mime = {type_ = "application"; subtype = "vnd.oipf.ueprofile+xml"}
let application_vnd_dot_oipf_dot_userprofile_plus_xml : mime = {type_ = "application"; subtype = "vnd.oipf.userprofile+xml"}
let application_vnd_dot_olpc_sugar : mime = {type_ = "application"; subtype = "vnd.olpc-sugar"}
let application_vnd_dot_oma_dot_bcast_dot_associated_procedure_parameter_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.bcast.associated-procedure-parameter+xml"}
let application_vnd_dot_oma_dot_bcast_dot_drm_trigger_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.bcast.drm-trigger+xml"}
let application_vnd_dot_oma_dot_bcast_dot_imd_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.bcast.imd+xml"}
let application_vnd_dot_oma_dot_bcast_dot_ltkm : mime = {type_ = "application"; subtype = "vnd.oma.bcast.ltkm"}
let application_vnd_dot_oma_dot_bcast_dot_notification_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.bcast.notification+xml"}
let application_vnd_dot_oma_dot_bcast_dot_provisioningtrigger : mime = {type_ = "application"; subtype = "vnd.oma.bcast.provisioningtrigger"}
let application_vnd_dot_oma_dot_bcast_dot_sgboot : mime = {type_ = "application"; subtype = "vnd.oma.bcast.sgboot"}
let application_vnd_dot_oma_dot_bcast_dot_sgdd_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.bcast.sgdd+xml"}
let application_vnd_dot_oma_dot_bcast_dot_sgdu : mime = {type_ = "application"; subtype = "vnd.oma.bcast.sgdu"}
let application_vnd_dot_oma_dot_bcast_dot_simple_symbol_container : mime = {type_ = "application"; subtype = "vnd.oma.bcast.simple-symbol-container"}
let application_vnd_dot_oma_dot_bcast_dot_smartcard_trigger_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.bcast.smartcard-trigger+xml"}
let application_vnd_dot_oma_dot_bcast_dot_sprov_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.bcast.sprov+xml"}
let application_vnd_dot_oma_dot_bcast_dot_stkm : mime = {type_ = "application"; subtype = "vnd.oma.bcast.stkm"}
let application_vnd_dot_oma_dot_cab_address_book_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.cab-address-book+xml"}
let application_vnd_dot_oma_dot_cab_feature_handler_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.cab-feature-handler+xml"}
let application_vnd_dot_oma_dot_cab_pcc_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.cab-pcc+xml"}
let application_vnd_dot_oma_dot_cab_subs_invite_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.cab-subs-invite+xml"}
let application_vnd_dot_oma_dot_cab_user_prefs_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.cab-user-prefs+xml"}
let application_vnd_dot_oma_dot_dcd : mime = {type_ = "application"; subtype = "vnd.oma.dcd"}
let application_vnd_dot_oma_dot_dcdc : mime = {type_ = "application"; subtype = "vnd.oma.dcdc"}
let application_vnd_dot_oma_dot_dd2_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.dd2+xml"}
let application_vnd_dot_oma_dot_drm_dot_risd_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.drm.risd+xml"}
let application_vnd_dot_oma_dot_group_usage_list_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.group-usage-list+xml"}
let application_vnd_dot_oma_dot_lwm2m_plus_cbor : mime = {type_ = "application"; subtype = "vnd.oma.lwm2m+cbor"}
let application_vnd_dot_oma_dot_lwm2m_plus_json : mime = {type_ = "application"; subtype = "vnd.oma.lwm2m+json"}
let application_vnd_dot_oma_dot_lwm2m_plus_tlv : mime = {type_ = "application"; subtype = "vnd.oma.lwm2m+tlv"}
let application_vnd_dot_oma_dot_pal_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.pal+xml"}
let application_vnd_dot_oma_dot_poc_dot_detailed_progress_report_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.poc.detailed-progress-report+xml"}
let application_vnd_dot_oma_dot_poc_dot_final_report_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.poc.final-report+xml"}
let application_vnd_dot_oma_dot_poc_dot_groups_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.poc.groups+xml"}
let application_vnd_dot_oma_dot_poc_dot_invocation_descriptor_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.poc.invocation-descriptor+xml"}
let application_vnd_dot_oma_dot_poc_dot_optimized_progress_report_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.poc.optimized-progress-report+xml"}
let application_vnd_dot_oma_dot_push : mime = {type_ = "application"; subtype = "vnd.oma.push"}
let application_vnd_dot_oma_dot_scidm_dot_messages_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.scidm.messages+xml"}
let application_vnd_dot_oma_dot_xcap_directory_plus_xml : mime = {type_ = "application"; subtype = "vnd.oma.xcap-directory+xml"}
let application_vnd_dot_omads_email_plus_xml : mime = {type_ = "application"; subtype = "vnd.omads-email+xml"}
let application_vnd_dot_omads_file_plus_xml : mime = {type_ = "application"; subtype = "vnd.omads-file+xml"}
let application_vnd_dot_omads_folder_plus_xml : mime = {type_ = "application"; subtype = "vnd.omads-folder+xml"}
let application_vnd_dot_omaloc_supl_init : mime = {type_ = "application"; subtype = "vnd.omaloc-supl-init"}
let application_vnd_dot_oma_scws_config : mime = {type_ = "application"; subtype = "vnd.oma-scws-config"}
let application_vnd_dot_oma_scws_http_request : mime = {type_ = "application"; subtype = "vnd.oma-scws-http-request"}
let application_vnd_dot_oma_scws_http_response : mime = {type_ = "application"; subtype = "vnd.oma-scws-http-response"}
let application_vnd_dot_oms_dot_cellular_cose_content_plus_cbor : mime = {type_ = "application"; subtype = "vnd.oms.cellular-cose-content+cbor"}
let application_vnd_dot_onepager : mime = {type_ = "application"; subtype = "vnd.onepager"}
let application_vnd_dot_onepagertamp : mime = {type_ = "application"; subtype = "vnd.onepagertamp"}
let application_vnd_dot_onepagertamx : mime = {type_ = "application"; subtype = "vnd.onepagertamx"}
let application_vnd_dot_onepagertat : mime = {type_ = "application"; subtype = "vnd.onepagertat"}
let application_vnd_dot_onepagertatp : mime = {type_ = "application"; subtype = "vnd.onepagertatp"}
let application_vnd_dot_onepagertatx : mime = {type_ = "application"; subtype = "vnd.onepagertatx"}
let application_vnd_dot_onvif_dot_metadata : mime = {type_ = "application"; subtype = "vnd.onvif.metadata"}
let application_vnd_dot_openblox_dot_game_binary : mime = {type_ = "application"; subtype = "vnd.openblox.game-binary"}
let application_vnd_dot_openblox_dot_game_plus_xml : mime = {type_ = "application"; subtype = "vnd.openblox.game+xml"}
let application_vnd_dot_openeye_dot_oeb : mime = {type_ = "application"; subtype = "vnd.openeye.oeb"}
let application_vnd_dot_openprinttag : mime = {type_ = "application"; subtype = "vnd.openprinttag"}
let application_vnd_dot_openstreetmap_dot_data_plus_xml : mime = {type_ = "application"; subtype = "vnd.openstreetmap.data+xml"}
let application_vnd_dot_opentimestamps_dot_ots : mime = {type_ = "application"; subtype = "vnd.opentimestamps.ots"}
let application_vnd_dot_openvpi_dot_dspx_plus_json : mime = {type_ = "application"; subtype = "vnd.openvpi.dspx+json"}
let application_vnd_dot_openxmlformats_officedocument_dot_custom_properties_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.custom-properties+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_customxmlproperties_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.customXmlProperties+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_drawing_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.drawing+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_drawingml_dot_chart_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.drawingml.chart+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_drawingml_dot_chartshapes_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.drawingml.chartshapes+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_drawingml_dot_diagramcolors_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.drawingml.diagramColors+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_drawingml_dot_diagramdata_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.drawingml.diagramData+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_drawingml_dot_diagramlayout_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.drawingml.diagramLayout+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_drawingml_dot_diagramstyle_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.drawingml.diagramStyle+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_extended_properties_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.extended-properties+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_commentauthors_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.commentAuthors+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_comments_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.comments+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_handoutmaster_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.handoutMaster+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_notesmaster_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.notesMaster+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_notesslide_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.notesSlide+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_presentation : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.presentation"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_presentation_dot_main_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.presentation.main+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_presprops_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.presProps+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_slide : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.slide"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_slide_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.slide+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_slidelayout_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.slideLayout+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_slidemaster_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.slideMaster+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_slideshow : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.slideshow"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_slideshow_dot_main_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.slideshow.main+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_slideupdateinfo_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.slideUpdateInfo+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_tablestyles_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.tableStyles+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_tags_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.tags+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_template : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.template"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_template_dot_main_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.template.main+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_presentationml_dot_viewprops_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.presentationml.viewProps+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_calcchain_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.calcChain+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_chartsheet_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.chartsheet+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_comments_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.comments+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_connections_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.connections+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_dialogsheet_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.dialogsheet+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_externallink_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.externalLink+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_pivotcachedefinition_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.pivotCacheDefinition+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_pivotcacherecords_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.pivotCacheRecords+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_pivottable_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.pivotTable+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_querytable_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.queryTable+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_revisionheaders_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.revisionHeaders+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_revisionlog_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.revisionLog+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_sharedstrings_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.sharedStrings+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_sheet : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.sheet"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_sheet_dot_main_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_sheetmetadata_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.sheetMetadata+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_styles_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_table_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.table+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_tablesinglecells_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.tableSingleCells+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_template : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.template"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_template_dot_main_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.template.main+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_usernames_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.userNames+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_volatiledependencies_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.volatileDependencies+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_spreadsheetml_dot_worksheet_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_theme_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.theme+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_themeoverride_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.themeOverride+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_vmldrawing : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.vmlDrawing"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_comments_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.comments+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_document : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.document"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_document_dot_glossary_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.document.glossary+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_document_dot_main_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_endnotes_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.endnotes+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_fonttable_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.fontTable+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_footer_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.footer+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_footnotes_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.footnotes+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_numbering_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.numbering+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_settings_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.settings+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_styles_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.styles+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_template : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.template"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_template_dot_main_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.template.main+xml"}
let application_vnd_dot_openxmlformats_officedocument_dot_wordprocessingml_dot_websettings_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-officedocument.wordprocessingml.webSettings+xml"}
let application_vnd_dot_openxmlformats_package_dot_core_properties_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-package.core-properties+xml"}
let application_vnd_dot_openxmlformats_package_dot_digital_signature_xmlsignature_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-package.digital-signature-xmlsignature+xml"}
let application_vnd_dot_openxmlformats_package_dot_relationships_plus_xml : mime = {type_ = "application"; subtype = "vnd.openxmlformats-package.relationships+xml"}
let application_vnd_dot_oracle_dot_resource_plus_json : mime = {type_ = "application"; subtype = "vnd.oracle.resource+json"}
let application_vnd_dot_orange_dot_indata : mime = {type_ = "application"; subtype = "vnd.orange.indata"}
let application_vnd_dot_osa_dot_netdeploy : mime = {type_ = "application"; subtype = "vnd.osa.netdeploy"}
let application_vnd_dot_osgeo_dot_mapguide_dot_package : mime = {type_ = "application"; subtype = "vnd.osgeo.mapguide.package"}
let application_vnd_dot_osgi_dot_bundle : mime = {type_ = "application"; subtype = "vnd.osgi.bundle"}
let application_vnd_dot_osgi_dot_dp : mime = {type_ = "application"; subtype = "vnd.osgi.dp"}
let application_vnd_dot_osgi_dot_subsystem : mime = {type_ = "application"; subtype = "vnd.osgi.subsystem"}
let application_vnd_dot_otps_dot_ct_kip_plus_xml : mime = {type_ = "application"; subtype = "vnd.otps.ct-kip+xml"}
let application_vnd_dot_oxli_dot_countgraph : mime = {type_ = "application"; subtype = "vnd.oxli.countgraph"}
let application_vnd_dot_pagerduty_plus_json : mime = {type_ = "application"; subtype = "vnd.pagerduty+json"}
let application_vnd_dot_palm : mime = {type_ = "application"; subtype = "vnd.palm"}
let application_vnd_dot_panoply : mime = {type_ = "application"; subtype = "vnd.panoply"}
let application_vnd_dot_paos_dot_xml : mime = {type_ = "application"; subtype = "vnd.paos.xml"}
let application_vnd_dot_patentdive : mime = {type_ = "application"; subtype = "vnd.patentdive"}
let application_vnd_dot_patientecommsdoc : mime = {type_ = "application"; subtype = "vnd.patientecommsdoc"}
let application_vnd_dot_pawaafile : mime = {type_ = "application"; subtype = "vnd.pawaafile"}
let application_vnd_dot_pcos : mime = {type_ = "application"; subtype = "vnd.pcos"}
let application_vnd_dot_pg_dot_format : mime = {type_ = "application"; subtype = "vnd.pg.format"}
let application_vnd_dot_pg_dot_osasli : mime = {type_ = "application"; subtype = "vnd.pg.osasli"}
let application_vnd_dot_phbk_plus_xml : mime = {type_ = "application"; subtype = "vnd.phbk+xml"}
let application_vnd_dot_piaccess_dot_application_licence : mime = {type_ = "application"; subtype = "vnd.piaccess.application-licence"}
let application_vnd_dot_picsel : mime = {type_ = "application"; subtype = "vnd.picsel"}
let application_vnd_dot_pmi_dot_widget : mime = {type_ = "application"; subtype = "vnd.pmi.widget"}
let application_vnd_dot_pmtiles : mime = {type_ = "application"; subtype = "vnd.pmtiles"}
let application_vnd_dot_poc_dot_group_advertisement_plus_xml : mime = {type_ = "application"; subtype = "vnd.poc.group-advertisement+xml"}
let application_vnd_dot_pocketlearn : mime = {type_ = "application"; subtype = "vnd.pocketlearn"}
let application_vnd_dot_powerbuilder6 : mime = {type_ = "application"; subtype = "vnd.powerbuilder6"}
let application_vnd_dot_powerbuilder6_s : mime = {type_ = "application"; subtype = "vnd.powerbuilder6-s"}
let application_vnd_dot_powerbuilder7 : mime = {type_ = "application"; subtype = "vnd.powerbuilder7"}
let application_vnd_dot_powerbuilder75 : mime = {type_ = "application"; subtype = "vnd.powerbuilder75"}
let application_vnd_dot_powerbuilder75_s : mime = {type_ = "application"; subtype = "vnd.powerbuilder75-s"}
let application_vnd_dot_powerbuilder7_s : mime = {type_ = "application"; subtype = "vnd.powerbuilder7-s"}
let application_vnd_dot_pp_dot_systemverify_plus_xml : mime = {type_ = "application"; subtype = "vnd.pp.systemverify+xml"}
let application_vnd_dot_preminet : mime = {type_ = "application"; subtype = "vnd.preminet"}
let application_vnd_dot_previewsystems_dot_box : mime = {type_ = "application"; subtype = "vnd.previewsystems.box"}
let application_vnd_dot_project_graph : mime = {type_ = "application"; subtype = "vnd.project-graph"}
let application_vnd_dot_proteus_dot_magazine : mime = {type_ = "application"; subtype = "vnd.proteus.magazine"}
let application_vnd_dot_psfs : mime = {type_ = "application"; subtype = "vnd.psfs"}
let application_vnd_dot_pt_dot_mundusmundi : mime = {type_ = "application"; subtype = "vnd.pt.mundusmundi"}
let application_vnd_dot_publishare_delta_tree : mime = {type_ = "application"; subtype = "vnd.publishare-delta-tree"}
let application_vnd_dot_pvi_dot_ptid1 : mime = {type_ = "application"; subtype = "vnd.pvi.ptid1"}
let application_vnd_dot_pwg_multiplexed : mime = {type_ = "application"; subtype = "vnd.pwg-multiplexed"}
let application_vnd_dot_pwg_xhtml_print_plus_xml : mime = {type_ = "application"; subtype = "vnd.pwg-xhtml-print+xml"}
let application_vnd_dot_pyon_plus_json : mime = {type_ = "application"; subtype = "vnd.pyon+json"}
let application_vnd_dot_qualcomm_dot_brew_app_res : mime = {type_ = "application"; subtype = "vnd.qualcomm.brew-app-res"}
let application_vnd_dot_quarantainenet : mime = {type_ = "application"; subtype = "vnd.quarantainenet"}
let application_vnd_dot_quark_dot_quarkxpress : mime = {type_ = "application"; subtype = "vnd.Quark.QuarkXPress"}
let application_vnd_dot_quobject_quoxdocument : mime = {type_ = "application"; subtype = "vnd.quobject-quoxdocument"}
let application_vnd_dot_r74n_dot_sandboxels_plus_json : mime = {type_ = "application"; subtype = "vnd.R74n.sandboxels+json"}
let application_vnd_dot_radisys_dot_moml_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.moml+xml"}
let application_vnd_dot_radisys_dot_msml_audit_conf_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-audit-conf+xml"}
let application_vnd_dot_radisys_dot_msml_audit_conn_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-audit-conn+xml"}
let application_vnd_dot_radisys_dot_msml_audit_dialog_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-audit-dialog+xml"}
let application_vnd_dot_radisys_dot_msml_audit_stream_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-audit-stream+xml"}
let application_vnd_dot_radisys_dot_msml_audit_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-audit+xml"}
let application_vnd_dot_radisys_dot_msml_conf_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-conf+xml"}
let application_vnd_dot_radisys_dot_msml_dialog_base_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-dialog-base+xml"}
let application_vnd_dot_radisys_dot_msml_dialog_fax_detect_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-dialog-fax-detect+xml"}
let application_vnd_dot_radisys_dot_msml_dialog_fax_sendrecv_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-dialog-fax-sendrecv+xml"}
let application_vnd_dot_radisys_dot_msml_dialog_group_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-dialog-group+xml"}
let application_vnd_dot_radisys_dot_msml_dialog_speech_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-dialog-speech+xml"}
let application_vnd_dot_radisys_dot_msml_dialog_transform_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-dialog-transform+xml"}
let application_vnd_dot_radisys_dot_msml_dialog_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml-dialog+xml"}
let application_vnd_dot_radisys_dot_msml_plus_xml : mime = {type_ = "application"; subtype = "vnd.radisys.msml+xml"}
let application_vnd_dot_rainstor_dot_data : mime = {type_ = "application"; subtype = "vnd.rainstor.data"}
let application_vnd_dot_rapid : mime = {type_ = "application"; subtype = "vnd.rapid"}
let application_vnd_dot_rar : mime = {type_ = "application"; subtype = "vnd.rar"}
let application_vnd_dot_realvnc_dot_bed : mime = {type_ = "application"; subtype = "vnd.realvnc.bed"}
let application_vnd_dot_recordare_dot_musicxml : mime = {type_ = "application"; subtype = "vnd.recordare.musicxml"}
let application_vnd_dot_recordare_dot_musicxml_plus_xml : mime = {type_ = "application"; subtype = "vnd.recordare.musicxml+xml"}
let application_vnd_dot_rego : mime = {type_ = "application"; subtype = "vnd.rego"}
let application_vnd_dot_relpipe : mime = {type_ = "application"; subtype = "vnd.relpipe"}
let application_vnd_dot_renlearn_dot_rlprint : mime = {type_ = "application"; subtype = "vnd.RenLearn.rlprint"}
let application_vnd_dot_resilient_dot_logic : mime = {type_ = "application"; subtype = "vnd.resilient.logic"}
let application_vnd_dot_restful_plus_json : mime = {type_ = "application"; subtype = "vnd.restful+json"}
let application_vnd_dot_rig_dot_cryptonote : mime = {type_ = "application"; subtype = "vnd.rig.cryptonote"}
let application_vnd_dot_route66_dot_link66_plus_xml : mime = {type_ = "application"; subtype = "vnd.route66.link66+xml"}
let application_vnd_dot_rs_274x : mime = {type_ = "application"; subtype = "vnd.rs-274x"}
let application_vnd_dot_ruckus_dot_download : mime = {type_ = "application"; subtype = "vnd.ruckus.download"}
let application_vnd_dot_s3sms : mime = {type_ = "application"; subtype = "vnd.s3sms"}
let application_vnd_dot_sailingtracker_dot_track : mime = {type_ = "application"; subtype = "vnd.sailingtracker.track"}
let application_vnd_dot_sar : mime = {type_ = "application"; subtype = "vnd.sar"}
let application_vnd_dot_sbm_dot_cid : mime = {type_ = "application"; subtype = "vnd.sbm.cid"}
let application_vnd_dot_sbm_dot_mid2 : mime = {type_ = "application"; subtype = "vnd.sbm.mid2"}
let application_vnd_dot_scribus : mime = {type_ = "application"; subtype = "vnd.scribus"}
let application_vnd_dot_sealed_dot_3df : mime = {type_ = "application"; subtype = "vnd.sealed.3df"}
let application_vnd_dot_sealed_dot_csf : mime = {type_ = "application"; subtype = "vnd.sealed.csf"}
let application_vnd_dot_sealed_dot_doc : mime = {type_ = "application"; subtype = "vnd.sealed.doc"}
let application_vnd_dot_sealed_dot_eml : mime = {type_ = "application"; subtype = "vnd.sealed.eml"}
let application_vnd_dot_sealed_dot_mht : mime = {type_ = "application"; subtype = "vnd.sealed.mht"}
let application_vnd_dot_sealed_dot_net : mime = {type_ = "application"; subtype = "vnd.sealed.net"}
let application_vnd_dot_sealed_dot_ppt : mime = {type_ = "application"; subtype = "vnd.sealed.ppt"}
let application_vnd_dot_sealed_dot_tiff : mime = {type_ = "application"; subtype = "vnd.sealed.tiff"}
let application_vnd_dot_sealed_dot_xls : mime = {type_ = "application"; subtype = "vnd.sealed.xls"}
let application_vnd_dot_sealedmedia_dot_softseal_dot_html : mime = {type_ = "application"; subtype = "vnd.sealedmedia.softseal.html"}
let application_vnd_dot_sealedmedia_dot_softseal_dot_pdf : mime = {type_ = "application"; subtype = "vnd.sealedmedia.softseal.pdf"}
let application_vnd_dot_seemail : mime = {type_ = "application"; subtype = "vnd.seemail"}
let application_vnd_dot_seis_plus_json : mime = {type_ = "application"; subtype = "vnd.seis+json"}
let application_vnd_dot_sema : mime = {type_ = "application"; subtype = "vnd.sema"}
let application_vnd_dot_semd : mime = {type_ = "application"; subtype = "vnd.semd"}
let application_vnd_dot_semf : mime = {type_ = "application"; subtype = "vnd.semf"}
let application_vnd_dot_shade_save_file : mime = {type_ = "application"; subtype = "vnd.shade-save-file"}
let application_vnd_dot_shana_dot_informed_dot_formdata : mime = {type_ = "application"; subtype = "vnd.shana.informed.formdata"}
let application_vnd_dot_shana_dot_informed_dot_formtemplate : mime = {type_ = "application"; subtype = "vnd.shana.informed.formtemplate"}
let application_vnd_dot_shana_dot_informed_dot_interchange : mime = {type_ = "application"; subtype = "vnd.shana.informed.interchange"}
let application_vnd_dot_shana_dot_informed_dot_package : mime = {type_ = "application"; subtype = "vnd.shana.informed.package"}
let application_vnd_dot_shootproof_plus_json : mime = {type_ = "application"; subtype = "vnd.shootproof+json"}
let application_vnd_dot_shopkick_plus_json : mime = {type_ = "application"; subtype = "vnd.shopkick+json"}
let application_vnd_dot_shp : mime = {type_ = "application"; subtype = "vnd.shp"}
let application_vnd_dot_shx : mime = {type_ = "application"; subtype = "vnd.shx"}
let application_vnd_dot_sigrok_dot_session : mime = {type_ = "application"; subtype = "vnd.sigrok.session"}
let application_vnd_dot_simtech_mindmapper : mime = {type_ = "application"; subtype = "vnd.SimTech-MindMapper"}
let application_vnd_dot_siren_plus_json : mime = {type_ = "application"; subtype = "vnd.siren+json"}
let application_vnd_dot_sirtx_dot_vmv0 : mime = {type_ = "application"; subtype = "vnd.sirtx.vmv0"}
let application_vnd_dot_sketchometry : mime = {type_ = "application"; subtype = "vnd.sketchometry"}
let application_vnd_dot_smaf : mime = {type_ = "application"; subtype = "vnd.smaf"}
let application_vnd_dot_smart_dot_notebook : mime = {type_ = "application"; subtype = "vnd.smart.notebook"}
let application_vnd_dot_smart_dot_teacher : mime = {type_ = "application"; subtype = "vnd.smart.teacher"}
let application_vnd_dot_smintio_dot_portals_dot_archive : mime = {type_ = "application"; subtype = "vnd.smintio.portals.archive"}
let application_vnd_dot_snesdev_page_table : mime = {type_ = "application"; subtype = "vnd.snesdev-page-table"}
let application_vnd_dot_software602_dot_filler_dot_form_plus_xml : mime = {type_ = "application"; subtype = "vnd.software602.filler.form+xml"}
let application_vnd_dot_software602_dot_filler_dot_form_xml_zip : mime = {type_ = "application"; subtype = "vnd.software602.filler.form-xml-zip"}
let application_vnd_dot_solent_dot_sdkm_plus_xml : mime = {type_ = "application"; subtype = "vnd.solent.sdkm+xml"}
let application_vnd_dot_spotfire_dot_dxp : mime = {type_ = "application"; subtype = "vnd.spotfire.dxp"}
let application_vnd_dot_spotfire_dot_sfs : mime = {type_ = "application"; subtype = "vnd.spotfire.sfs"}
let application_vnd_dot_sqlite3 : mime = {type_ = "application"; subtype = "vnd.sqlite3"}
let application_vnd_dot_sri : mime = {type_ = "application"; subtype = "vnd.sri"}
let application_vnd_dot_sss_cod : mime = {type_ = "application"; subtype = "vnd.sss-cod"}
let application_vnd_dot_sss_dtf : mime = {type_ = "application"; subtype = "vnd.sss-dtf"}
let application_vnd_dot_sss_ntf : mime = {type_ = "application"; subtype = "vnd.sss-ntf"}
let application_vnd_dot_stepmania_dot_package : mime = {type_ = "application"; subtype = "vnd.stepmania.package"}
let application_vnd_dot_stepmania_dot_stepchart : mime = {type_ = "application"; subtype = "vnd.stepmania.stepchart"}
let application_vnd_dot_street_stream : mime = {type_ = "application"; subtype = "vnd.street-stream"}
let application_vnd_dot_sun_dot_wadl_plus_xml : mime = {type_ = "application"; subtype = "vnd.sun.wadl+xml"}
let application_vnd_dot_superfile_dot_super : mime = {type_ = "application"; subtype = "vnd.superfile.super"}
let application_vnd_dot_sus_calendar : mime = {type_ = "application"; subtype = "vnd.sus-calendar"}
let application_vnd_dot_svd : mime = {type_ = "application"; subtype = "vnd.svd"}
let application_vnd_dot_swiftview_ics : mime = {type_ = "application"; subtype = "vnd.swiftview-ics"}
let application_vnd_dot_sybyl_dot_mol2 : mime = {type_ = "application"; subtype = "vnd.sybyl.mol2"}
let application_vnd_dot_sycle_plus_xml : mime = {type_ = "application"; subtype = "vnd.sycle+xml"}
let application_vnd_dot_syft_plus_json : mime = {type_ = "application"; subtype = "vnd.syft+json"}
let application_vnd_dot_syncml_dot_dm_dot_notification : mime = {type_ = "application"; subtype = "vnd.syncml.dm.notification"}
let application_vnd_dot_syncml_dot_dmddf_plus_xml : mime = {type_ = "application"; subtype = "vnd.syncml.dmddf+xml"}
let application_vnd_dot_syncml_dot_dmtnds_plus_wbxml : mime = {type_ = "application"; subtype = "vnd.syncml.dmtnds+wbxml"}
let application_vnd_dot_syncml_dot_dmtnds_plus_xml : mime = {type_ = "application"; subtype = "vnd.syncml.dmtnds+xml"}
let application_vnd_dot_syncml_dot_dmddf_plus_wbxml : mime = {type_ = "application"; subtype = "vnd.syncml.dmddf+wbxml"}
let application_vnd_dot_syncml_dot_dm_plus_wbxml : mime = {type_ = "application"; subtype = "vnd.syncml.dm+wbxml"}
let application_vnd_dot_syncml_dot_dm_plus_xml : mime = {type_ = "application"; subtype = "vnd.syncml.dm+xml"}
let application_vnd_dot_syncml_dot_ds_dot_notification : mime = {type_ = "application"; subtype = "vnd.syncml.ds.notification"}
let application_vnd_dot_syncml_plus_xml : mime = {type_ = "application"; subtype = "vnd.syncml+xml"}
let application_vnd_dot_tableschema_plus_json : mime = {type_ = "application"; subtype = "vnd.tableschema+json"}
let application_vnd_dot_tao_dot_intent_module_archive : mime = {type_ = "application"; subtype = "vnd.tao.intent-module-archive"}
let application_vnd_dot_tcpdump_dot_pcap : mime = {type_ = "application"; subtype = "vnd.tcpdump.pcap"}
let application_vnd_dot_think_cell_dot_ppttc_plus_json : mime = {type_ = "application"; subtype = "vnd.think-cell.ppttc+json"}
let application_vnd_dot_tml : mime = {type_ = "application"; subtype = "vnd.tml"}
let application_vnd_dot_tmd_dot_mediaflex_dot_api_plus_xml : mime = {type_ = "application"; subtype = "vnd.tmd.mediaflex.api+xml"}
let application_vnd_dot_tmobile_livetv : mime = {type_ = "application"; subtype = "vnd.tmobile-livetv"}
let application_vnd_dot_tri_dot_onesource : mime = {type_ = "application"; subtype = "vnd.tri.onesource"}
let application_vnd_dot_trid_dot_tpt : mime = {type_ = "application"; subtype = "vnd.trid.tpt"}
let application_vnd_dot_triscape_dot_mxs : mime = {type_ = "application"; subtype = "vnd.triscape.mxs"}
let application_vnd_dot_trueapp : mime = {type_ = "application"; subtype = "vnd.trueapp"}
let application_vnd_dot_truedoc : mime = {type_ = "application"; subtype = "vnd.truedoc"}
let application_vnd_dot_ubisoft_dot_webplayer : mime = {type_ = "application"; subtype = "vnd.ubisoft.webplayer"}
let application_vnd_dot_ufdl : mime = {type_ = "application"; subtype = "vnd.ufdl"}
let application_vnd_dot_uic_dot_dosipas_dot_v1 : mime = {type_ = "application"; subtype = "vnd.uic.dosipas.v1"}
let application_vnd_dot_uic_dot_dosipas_dot_v2 : mime = {type_ = "application"; subtype = "vnd.uic.dosipas.v2"}
let application_vnd_dot_uic_dot_osdm_plus_json : mime = {type_ = "application"; subtype = "vnd.uic.osdm+json"}
let application_vnd_dot_uic_dot_tlb_fcb : mime = {type_ = "application"; subtype = "vnd.uic.tlb-fcb"}
let application_vnd_dot_uiq_dot_theme : mime = {type_ = "application"; subtype = "vnd.uiq.theme"}
let application_vnd_dot_umajin : mime = {type_ = "application"; subtype = "vnd.umajin"}
let application_vnd_dot_unity : mime = {type_ = "application"; subtype = "vnd.unity"}
let application_vnd_dot_uoml_plus_xml : mime = {type_ = "application"; subtype = "vnd.uoml+xml"}
let application_vnd_dot_uplanet_dot_alert : mime = {type_ = "application"; subtype = "vnd.uplanet.alert"}
let application_vnd_dot_uplanet_dot_alert_wbxml : mime = {type_ = "application"; subtype = "vnd.uplanet.alert-wbxml"}
let application_vnd_dot_uplanet_dot_bearer_choice : mime = {type_ = "application"; subtype = "vnd.uplanet.bearer-choice"}
let application_vnd_dot_uplanet_dot_bearer_choice_wbxml : mime = {type_ = "application"; subtype = "vnd.uplanet.bearer-choice-wbxml"}
let application_vnd_dot_uplanet_dot_cacheop : mime = {type_ = "application"; subtype = "vnd.uplanet.cacheop"}
let application_vnd_dot_uplanet_dot_cacheop_wbxml : mime = {type_ = "application"; subtype = "vnd.uplanet.cacheop-wbxml"}
let application_vnd_dot_uplanet_dot_channel : mime = {type_ = "application"; subtype = "vnd.uplanet.channel"}
let application_vnd_dot_uplanet_dot_channel_wbxml : mime = {type_ = "application"; subtype = "vnd.uplanet.channel-wbxml"}
let application_vnd_dot_uplanet_dot_list : mime = {type_ = "application"; subtype = "vnd.uplanet.list"}
let application_vnd_dot_uplanet_dot_listcmd : mime = {type_ = "application"; subtype = "vnd.uplanet.listcmd"}
let application_vnd_dot_uplanet_dot_listcmd_wbxml : mime = {type_ = "application"; subtype = "vnd.uplanet.listcmd-wbxml"}
let application_vnd_dot_uplanet_dot_list_wbxml : mime = {type_ = "application"; subtype = "vnd.uplanet.list-wbxml"}
let application_vnd_dot_uri_map : mime = {type_ = "application"; subtype = "vnd.uri-map"}
let application_vnd_dot_uplanet_dot_signal : mime = {type_ = "application"; subtype = "vnd.uplanet.signal"}
let application_vnd_dot_valve_dot_source_dot_material : mime = {type_ = "application"; subtype = "vnd.valve.source.material"}
let application_vnd_dot_vcx : mime = {type_ = "application"; subtype = "vnd.vcx"}
let application_vnd_dot_vd_study : mime = {type_ = "application"; subtype = "vnd.vd-study"}
let application_vnd_dot_vectorworks : mime = {type_ = "application"; subtype = "vnd.vectorworks"}
let application_vnd_dot_vel_plus_json : mime = {type_ = "application"; subtype = "vnd.vel+json"}
let application_vnd_dot_veraison_dot_tsm_report_plus_cbor : mime = {type_ = "application"; subtype = "vnd.veraison.tsm-report+cbor"}
let application_vnd_dot_veraison_dot_tsm_report_plus_json : mime = {type_ = "application"; subtype = "vnd.veraison.tsm-report+json"}
let application_vnd_dot_verifier_attestation_plus_jwt : mime = {type_ = "application"; subtype = "vnd.verifier-attestation+jwt"}
let application_vnd_dot_verimatrix_dot_vcas : mime = {type_ = "application"; subtype = "vnd.verimatrix.vcas"}
let application_vnd_dot_veritone_dot_aion_plus_json : mime = {type_ = "application"; subtype = "vnd.veritone.aion+json"}
let application_vnd_dot_vertifile_dot_pvf : mime = {type_ = "application"; subtype = "vnd.vertifile.pvf"}
let application_vnd_dot_veryant_dot_thin : mime = {type_ = "application"; subtype = "vnd.veryant.thin"}
let application_vnd_dot_ves_dot_encrypted : mime = {type_ = "application"; subtype = "vnd.ves.encrypted"}
let application_vnd_dot_vidsoft_dot_vidconference : mime = {type_ = "application"; subtype = "vnd.vidsoft.vidconference"}
let application_vnd_dot_visio : mime = {type_ = "application"; subtype = "vnd.visio"}
let application_vnd_dot_visionary : mime = {type_ = "application"; subtype = "vnd.visionary"}
let application_vnd_dot_vividence_dot_scriptfile : mime = {type_ = "application"; subtype = "vnd.vividence.scriptfile"}
let application_vnd_dot_vocalshaper_dot_vsp4 : mime = {type_ = "application"; subtype = "vnd.vocalshaper.vsp4"}
let application_vnd_dot_vsf : mime = {type_ = "application"; subtype = "vnd.vsf"}
let application_vnd_dot_vuq : mime = {type_ = "application"; subtype = "vnd.vuq"}
let application_vnd_dot_wantverse : mime = {type_ = "application"; subtype = "vnd.wantverse"}
let application_vnd_dot_wap_dot_sic : mime = {type_ = "application"; subtype = "vnd.wap.sic"}
let application_vnd_dot_wap_dot_slc : mime = {type_ = "application"; subtype = "vnd.wap.slc"}
let application_vnd_dot_wap_dot_wbxml : mime = {type_ = "application"; subtype = "vnd.wap.wbxml"}
let application_vnd_dot_wap_dot_wmlc : mime = {type_ = "application"; subtype = "vnd.wap.wmlc"}
let application_vnd_dot_wap_dot_wmlscriptc : mime = {type_ = "application"; subtype = "vnd.wap.wmlscriptc"}
let application_vnd_dot_wasmflow_dot_wafl : mime = {type_ = "application"; subtype = "vnd.wasmflow.wafl"}
let application_vnd_dot_webturbo : mime = {type_ = "application"; subtype = "vnd.webturbo"}
let application_vnd_dot_wfa_dot_dpp : mime = {type_ = "application"; subtype = "vnd.wfa.dpp"}
let application_vnd_dot_wfa_dot_p2p : mime = {type_ = "application"; subtype = "vnd.wfa.p2p"}
let application_vnd_dot_wfa_dot_wsc : mime = {type_ = "application"; subtype = "vnd.wfa.wsc"}
let application_vnd_dot_windows_dot_devicepairing : mime = {type_ = "application"; subtype = "vnd.windows.devicepairing"}
let application_vnd_dot_wmap : mime = {type_ = "application"; subtype = "vnd.wmap"}
let application_vnd_dot_wmc : mime = {type_ = "application"; subtype = "vnd.wmc"}
let application_vnd_dot_wmf_dot_bootstrap : mime = {type_ = "application"; subtype = "vnd.wmf.bootstrap"}
let application_vnd_dot_wolfram_dot_mathematica : mime = {type_ = "application"; subtype = "vnd.wolfram.mathematica"}
let application_vnd_dot_wolfram_dot_mathematica_dot_package : mime = {type_ = "application"; subtype = "vnd.wolfram.mathematica.package"}
let application_vnd_dot_wolfram_dot_player : mime = {type_ = "application"; subtype = "vnd.wolfram.player"}
let application_vnd_dot_wordlift : mime = {type_ = "application"; subtype = "vnd.wordlift"}
let application_vnd_dot_wordperfect : mime = {type_ = "application"; subtype = "vnd.wordperfect"}
let application_vnd_dot_wqd : mime = {type_ = "application"; subtype = "vnd.wqd"}
let application_vnd_dot_wrq_hp3000_labelled : mime = {type_ = "application"; subtype = "vnd.wrq-hp3000-labelled"}
let application_vnd_dot_wt_dot_stf : mime = {type_ = "application"; subtype = "vnd.wt.stf"}
let application_vnd_dot_wv_dot_csp_plus_xml : mime = {type_ = "application"; subtype = "vnd.wv.csp+xml"}
let application_vnd_dot_wv_dot_csp_plus_wbxml : mime = {type_ = "application"; subtype = "vnd.wv.csp+wbxml"}
let application_vnd_dot_wv_dot_ssp_plus_xml : mime = {type_ = "application"; subtype = "vnd.wv.ssp+xml"}
let application_vnd_dot_xacml_plus_json : mime = {type_ = "application"; subtype = "vnd.xacml+json"}
let application_vnd_dot_xara : mime = {type_ = "application"; subtype = "vnd.xara"}
let application_vnd_dot_xarin_dot_cpj : mime = {type_ = "application"; subtype = "vnd.xarin.cpj"}
let application_vnd_dot_xcdn : mime = {type_ = "application"; subtype = "vnd.xcdn"}
let application_vnd_dot_xecrets_encrypted : mime = {type_ = "application"; subtype = "vnd.xecrets-encrypted"}
let application_vnd_dot_xfdl : mime = {type_ = "application"; subtype = "vnd.xfdl"}
let application_vnd_dot_xfdl_dot_webform : mime = {type_ = "application"; subtype = "vnd.xfdl.webform"}
let application_vnd_dot_xmi_plus_xml : mime = {type_ = "application"; subtype = "vnd.xmi+xml"}
let application_vnd_dot_xmpie_dot_cpkg : mime = {type_ = "application"; subtype = "vnd.xmpie.cpkg"}
let application_vnd_dot_xmpie_dot_dpkg : mime = {type_ = "application"; subtype = "vnd.xmpie.dpkg"}
let application_vnd_dot_xmpie_dot_plan : mime = {type_ = "application"; subtype = "vnd.xmpie.plan"}
let application_vnd_dot_xmpie_dot_ppkg : mime = {type_ = "application"; subtype = "vnd.xmpie.ppkg"}
let application_vnd_dot_xmpie_dot_xlim : mime = {type_ = "application"; subtype = "vnd.xmpie.xlim"}
let application_vnd_dot_yamaha_dot_hv_dic : mime = {type_ = "application"; subtype = "vnd.yamaha.hv-dic"}
let application_vnd_dot_yamaha_dot_hv_script : mime = {type_ = "application"; subtype = "vnd.yamaha.hv-script"}
let application_vnd_dot_yamaha_dot_hv_voice : mime = {type_ = "application"; subtype = "vnd.yamaha.hv-voice"}
let application_vnd_dot_yamaha_dot_openscoreformat_dot_osfpvg_plus_xml : mime = {type_ = "application"; subtype = "vnd.yamaha.openscoreformat.osfpvg+xml"}
let application_vnd_dot_yamaha_dot_openscoreformat : mime = {type_ = "application"; subtype = "vnd.yamaha.openscoreformat"}
let application_vnd_dot_yamaha_dot_remote_setup : mime = {type_ = "application"; subtype = "vnd.yamaha.remote-setup"}
let application_vnd_dot_yamaha_dot_smaf_audio : mime = {type_ = "application"; subtype = "vnd.yamaha.smaf-audio"}
let application_vnd_dot_yamaha_dot_smaf_phrase : mime = {type_ = "application"; subtype = "vnd.yamaha.smaf-phrase"}
let application_vnd_dot_yamaha_dot_through_ngn : mime = {type_ = "application"; subtype = "vnd.yamaha.through-ngn"}
let application_vnd_dot_yamaha_dot_tunnel_udpencap : mime = {type_ = "application"; subtype = "vnd.yamaha.tunnel-udpencap"}
let application_vnd_dot_yaoweme : mime = {type_ = "application"; subtype = "vnd.yaoweme"}
let application_vnd_dot_yellowriver_custom_menu : mime = {type_ = "application"; subtype = "vnd.yellowriver-custom-menu"}
let application_vnd_dot_youtube_dot_yt : mime = {type_ = "application"; subtype = "vnd.youtube.yt"}
let application_vnd_dot_zoho_document_dot_writer : mime = {type_ = "application"; subtype = "vnd.zoho-document.writer"}
let application_vnd_dot_zoho_presentation_dot_show : mime = {type_ = "application"; subtype = "vnd.zoho-presentation.show"}
let application_vnd_dot_zoho_dot_spreadsheetml_dot_sheet : mime = {type_ = "application"; subtype = "vnd.zoho.spreadsheetml.sheet"}
let application_vnd_dot_zul : mime = {type_ = "application"; subtype = "vnd.zul"}
let application_vnd_dot_zzazz_dot_deck_plus_xml : mime = {type_ = "application"; subtype = "vnd.zzazz.deck+xml"}
let application_voicexml_plus_xml : mime = {type_ = "application"; subtype = "voicexml+xml"}
let application_voucher_cms_plus_json : mime = {type_ = "application"; subtype = "voucher-cms+json"}
let application_voucher_jws_plus_json : mime = {type_ = "application"; subtype = "voucher-jws+json"}
let application_vp : mime = {type_ = "application"; subtype = "vp"}
let application_vp_plus_cose : mime = {type_ = "application"; subtype = "vp+cose"}
let application_vp_plus_jwt : mime = {type_ = "application"; subtype = "vp+jwt"}
let application_vp_plus_sd_jwt : mime = {type_ = "application"; subtype = "vp+sd-jwt"}
let application_vq_rtcpxr : mime = {type_ = "application"; subtype = "vq-rtcpxr"}
let application_wasm : mime = {type_ = "application"; subtype = "wasm"}
let application_watcherinfo_plus_xml : mime = {type_ = "application"; subtype = "watcherinfo+xml"}
let application_webpush_options_plus_json : mime = {type_ = "application"; subtype = "webpush-options+json"}
let application_whoispp_query : mime = {type_ = "application"; subtype = "whoispp-query"}
let application_whoispp_response : mime = {type_ = "application"; subtype = "whoispp-response"}
let application_widget : mime = {type_ = "application"; subtype = "widget"}
let application_wita : mime = {type_ = "application"; subtype = "wita"}
let application_wordperfect5_dot_1 : mime = {type_ = "application"; subtype = "wordperfect5.1"}
let application_wsdl_plus_xml : mime = {type_ = "application"; subtype = "wsdl+xml"}
let application_wspolicy_plus_xml : mime = {type_ = "application"; subtype = "wspolicy+xml"}
let application_x_pki_message : mime = {type_ = "application"; subtype = "x-pki-message"}
let application_x_www_form_urlencoded : mime = {type_ = "application"; subtype = "x-www-form-urlencoded"}
let application_x_x509_ca_cert : mime = {type_ = "application"; subtype = "x-x509-ca-cert"}
let application_x_x509_ca_ra_cert : mime = {type_ = "application"; subtype = "x-x509-ca-ra-cert"}
let application_x_x509_next_ca_cert : mime = {type_ = "application"; subtype = "x-x509-next-ca-cert"}
let application_x400_bp : mime = {type_ = "application"; subtype = "x400-bp"}
let application_xacml_plus_xml : mime = {type_ = "application"; subtype = "xacml+xml"}
let application_xcap_att_plus_xml : mime = {type_ = "application"; subtype = "xcap-att+xml"}
let application_xcap_caps_plus_xml : mime = {type_ = "application"; subtype = "xcap-caps+xml"}
let application_xcap_diff_plus_xml : mime = {type_ = "application"; subtype = "xcap-diff+xml"}
let application_xcap_el_plus_xml : mime = {type_ = "application"; subtype = "xcap-el+xml"}
let application_xcap_error_plus_xml : mime = {type_ = "application"; subtype = "xcap-error+xml"}
let application_xcap_ns_plus_xml : mime = {type_ = "application"; subtype = "xcap-ns+xml"}
let application_xcon_conference_info_diff_plus_xml : mime = {type_ = "application"; subtype = "xcon-conference-info-diff+xml"}
let application_xcon_conference_info_plus_xml : mime = {type_ = "application"; subtype = "xcon-conference-info+xml"}
let application_xenc_plus_xml : mime = {type_ = "application"; subtype = "xenc+xml"}
let application_xfdf : mime = {type_ = "application"; subtype = "xfdf"}
let application_xhtml_plus_xml : mime = {type_ = "application"; subtype = "xhtml+xml"}
let application_xliff_plus_xml : mime = {type_ = "application"; subtype = "xliff+xml"}
let application_xml : mime = {type_ = "application"; subtype = "xml"}
let application_xml_dtd : mime = {type_ = "application"; subtype = "xml-dtd"}
let application_xml_external_parsed_entity : mime = {type_ = "application"; subtype = "xml-external-parsed-entity"}
let application_xml_patch_plus_xml : mime = {type_ = "application"; subtype = "xml-patch+xml"}
let application_xmpp_plus_xml : mime = {type_ = "application"; subtype = "xmpp+xml"}
let application_xop_plus_xml : mime = {type_ = "application"; subtype = "xop+xml"}
let application_xslt_plus_xml : mime = {type_ = "application"; subtype = "xslt+xml"}
let application_xv_plus_xml : mime = {type_ = "application"; subtype = "xv+xml"}
let application_yaml : mime = {type_ = "application"; subtype = "yaml"}
let application_yang : mime = {type_ = "application"; subtype = "yang"}
let application_yang_data_plus_cbor : mime = {type_ = "application"; subtype = "yang-data+cbor"}
let application_yang_data_plus_json : mime = {type_ = "application"; subtype = "yang-data+json"}
let application_yang_data_plus_xml : mime = {type_ = "application"; subtype = "yang-data+xml"}
let application_yang_patch_plus_json : mime = {type_ = "application"; subtype = "yang-patch+json"}
let application_yang_patch_plus_xml : mime = {type_ = "application"; subtype = "yang-patch+xml"}
let application_yang_sid_plus_json : mime = {type_ = "application"; subtype = "yang-sid+json"}
let application_yin_plus_xml : mime = {type_ = "application"; subtype = "yin+xml"}
let application_zip : mime = {type_ = "application"; subtype = "zip"}
let application_zlib : mime = {type_ = "application"; subtype = "zlib"}
let application_zstd : mime = {type_ = "application"; subtype = "zstd"}

(* ---- audio/* ---- *)
let audio__1d_interleaved_parityfec : mime = {type_ = "audio"; subtype = "1d-interleaved-parityfec"}
let audio__32kadpcm : mime = {type_ = "audio"; subtype = "32kadpcm"}
let audio__3gpp : mime = {type_ = "audio"; subtype = "3gpp"}
let audio__3gpp2 : mime = {type_ = "audio"; subtype = "3gpp2"}
let audio_aac : mime = {type_ = "audio"; subtype = "aac"}
let audio_ac3 : mime = {type_ = "audio"; subtype = "ac3"}
let audio_amr : mime = {type_ = "audio"; subtype = "AMR"}
let audio_amr_wb : mime = {type_ = "audio"; subtype = "AMR-WB"}
let audio_amr_wb_plus_ : mime = {type_ = "audio"; subtype = "amr-wb+"}
let audio_aptx : mime = {type_ = "audio"; subtype = "aptx"}
let audio_asc : mime = {type_ = "audio"; subtype = "asc"}
let audio_atrac_advanced_lossless : mime = {type_ = "audio"; subtype = "ATRAC-ADVANCED-LOSSLESS"}
let audio_atrac_x : mime = {type_ = "audio"; subtype = "ATRAC-X"}
let audio_atrac3 : mime = {type_ = "audio"; subtype = "ATRAC3"}
let audio_basic : mime = {type_ = "audio"; subtype = "basic"}
let audio_bv16 : mime = {type_ = "audio"; subtype = "BV16"}
let audio_bv32 : mime = {type_ = "audio"; subtype = "BV32"}
let audio_clearmode : mime = {type_ = "audio"; subtype = "clearmode"}
let audio_cn : mime = {type_ = "audio"; subtype = "CN"}
let audio_dat12 : mime = {type_ = "audio"; subtype = "DAT12"}
let audio_dls : mime = {type_ = "audio"; subtype = "dls"}
let audio_dsr_es201108 : mime = {type_ = "audio"; subtype = "dsr-es201108"}
let audio_dsr_es202050 : mime = {type_ = "audio"; subtype = "dsr-es202050"}
let audio_dsr_es202211 : mime = {type_ = "audio"; subtype = "dsr-es202211"}
let audio_dsr_es202212 : mime = {type_ = "audio"; subtype = "dsr-es202212"}
let audio_dv : mime = {type_ = "audio"; subtype = "DV"}
let audio_dvi4 : mime = {type_ = "audio"; subtype = "DVI4"}
let audio_eac3 : mime = {type_ = "audio"; subtype = "eac3"}
let audio_encaprtp : mime = {type_ = "audio"; subtype = "encaprtp"}
let audio_evrc : mime = {type_ = "audio"; subtype = "EVRC"}
let audio_evrc_qcp : mime = {type_ = "audio"; subtype = "EVRC-QCP"}
let audio_evrc0 : mime = {type_ = "audio"; subtype = "EVRC0"}
let audio_evrc1 : mime = {type_ = "audio"; subtype = "EVRC1"}
let audio_evrcb : mime = {type_ = "audio"; subtype = "EVRCB"}
let audio_evrcb0 : mime = {type_ = "audio"; subtype = "EVRCB0"}
let audio_evrcb1 : mime = {type_ = "audio"; subtype = "EVRCB1"}
let audio_evrcnw : mime = {type_ = "audio"; subtype = "EVRCNW"}
let audio_evrcnw0 : mime = {type_ = "audio"; subtype = "EVRCNW0"}
let audio_evrcnw1 : mime = {type_ = "audio"; subtype = "EVRCNW1"}
let audio_evrcwb : mime = {type_ = "audio"; subtype = "EVRCWB"}
let audio_evrcwb0 : mime = {type_ = "audio"; subtype = "EVRCWB0"}
let audio_evrcwb1 : mime = {type_ = "audio"; subtype = "EVRCWB1"}
let audio_evs : mime = {type_ = "audio"; subtype = "EVS"}
let audio_example : mime = {type_ = "audio"; subtype = "example"}
let audio_flac : mime = {type_ = "audio"; subtype = "flac"}
let audio_flexfec : mime = {type_ = "audio"; subtype = "flexfec"}
let audio_fwdred : mime = {type_ = "audio"; subtype = "fwdred"}
let audio_g711_0 : mime = {type_ = "audio"; subtype = "G711-0"}
let audio_g719 : mime = {type_ = "audio"; subtype = "G719"}
let audio_g7221 : mime = {type_ = "audio"; subtype = "G7221"}
let audio_g722 : mime = {type_ = "audio"; subtype = "G722"}
let audio_g723 : mime = {type_ = "audio"; subtype = "G723"}
let audio_g726_16 : mime = {type_ = "audio"; subtype = "G726-16"}
let audio_g726_24 : mime = {type_ = "audio"; subtype = "G726-24"}
let audio_g726_32 : mime = {type_ = "audio"; subtype = "G726-32"}
let audio_g726_40 : mime = {type_ = "audio"; subtype = "G726-40"}
let audio_g728 : mime = {type_ = "audio"; subtype = "G728"}
let audio_g729 : mime = {type_ = "audio"; subtype = "G729"}
let audio_g7291 : mime = {type_ = "audio"; subtype = "G7291"}
let audio_g729d : mime = {type_ = "audio"; subtype = "G729D"}
let audio_g729e : mime = {type_ = "audio"; subtype = "G729E"}
let audio_gsm : mime = {type_ = "audio"; subtype = "GSM"}
let audio_gsm_efr : mime = {type_ = "audio"; subtype = "GSM-EFR"}
let audio_gsm_hr_08 : mime = {type_ = "audio"; subtype = "GSM-HR-08"}
let audio_ilbc : mime = {type_ = "audio"; subtype = "iLBC"}
let audio_ip_mr_v2_dot_5 : mime = {type_ = "audio"; subtype = "ip-mr_v2.5"}
let audio_l8 : mime = {type_ = "audio"; subtype = "L8"}
let audio_l16 : mime = {type_ = "audio"; subtype = "L16"}
let audio_l20 : mime = {type_ = "audio"; subtype = "L20"}
let audio_l24 : mime = {type_ = "audio"; subtype = "L24"}
let audio_lpc : mime = {type_ = "audio"; subtype = "LPC"}
let audio_matroska : mime = {type_ = "audio"; subtype = "matroska"}
let audio_melp : mime = {type_ = "audio"; subtype = "MELP"}
let audio_melp600 : mime = {type_ = "audio"; subtype = "MELP600"}
let audio_melp1200 : mime = {type_ = "audio"; subtype = "MELP1200"}
let audio_melp2400 : mime = {type_ = "audio"; subtype = "MELP2400"}
let audio_mhas : mime = {type_ = "audio"; subtype = "mhas"}
let audio_midi_clip : mime = {type_ = "audio"; subtype = "midi-clip"}
let audio_mobile_xmf : mime = {type_ = "audio"; subtype = "mobile-xmf"}
let audio_mpa : mime = {type_ = "audio"; subtype = "MPA"}
let audio_mp4 : mime = {type_ = "audio"; subtype = "mp4"}
let audio_mp4a_latm : mime = {type_ = "audio"; subtype = "MP4A-LATM"}
let audio_mpa_robust : mime = {type_ = "audio"; subtype = "mpa-robust"}
let audio_mpeg : mime = {type_ = "audio"; subtype = "mpeg"}
let audio_mpeg4_generic : mime = {type_ = "audio"; subtype = "mpeg4-generic"}
let audio_ogg : mime = {type_ = "audio"; subtype = "ogg"}
let audio_opus : mime = {type_ = "audio"; subtype = "opus"}
let audio_parityfec : mime = {type_ = "audio"; subtype = "parityfec"}
let audio_pcma : mime = {type_ = "audio"; subtype = "PCMA"}
let audio_pcma_wb : mime = {type_ = "audio"; subtype = "PCMA-WB"}
let audio_pcmu : mime = {type_ = "audio"; subtype = "PCMU"}
let audio_pcmu_wb : mime = {type_ = "audio"; subtype = "PCMU-WB"}
let audio_prs_dot_sid : mime = {type_ = "audio"; subtype = "prs.sid"}
let audio_qcelp : mime = {type_ = "audio"; subtype = "QCELP"}
let audio_raptorfec : mime = {type_ = "audio"; subtype = "raptorfec"}
let audio_red : mime = {type_ = "audio"; subtype = "RED"}
let audio_rtp_enc_aescm128 : mime = {type_ = "audio"; subtype = "rtp-enc-aescm128"}
let audio_rtploopback : mime = {type_ = "audio"; subtype = "rtploopback"}
let audio_rtp_midi : mime = {type_ = "audio"; subtype = "rtp-midi"}
let audio_rtx : mime = {type_ = "audio"; subtype = "rtx"}
let audio_scip : mime = {type_ = "audio"; subtype = "scip"}
let audio_smv : mime = {type_ = "audio"; subtype = "SMV"}
let audio_smv0 : mime = {type_ = "audio"; subtype = "SMV0"}
let audio_smv_qcp : mime = {type_ = "audio"; subtype = "SMV-QCP"}
let audio_sofa : mime = {type_ = "audio"; subtype = "sofa"}
let audio_soundfont : mime = {type_ = "audio"; subtype = "soundfont"}
let audio_sp_midi : mime = {type_ = "audio"; subtype = "sp-midi"}
let audio_speex : mime = {type_ = "audio"; subtype = "speex"}
let audio_t140c : mime = {type_ = "audio"; subtype = "t140c"}
let audio_t38 : mime = {type_ = "audio"; subtype = "t38"}
let audio_telephone_event : mime = {type_ = "audio"; subtype = "telephone-event"}
let audio_tetra_acelp : mime = {type_ = "audio"; subtype = "TETRA_ACELP"}
let audio_tetra_acelp_bb : mime = {type_ = "audio"; subtype = "TETRA_ACELP_BB"}
let audio_tone : mime = {type_ = "audio"; subtype = "tone"}
let audio_tsvcis : mime = {type_ = "audio"; subtype = "TSVCIS"}
let audio_uemclip : mime = {type_ = "audio"; subtype = "UEMCLIP"}
let audio_ulpfec : mime = {type_ = "audio"; subtype = "ulpfec"}
let audio_usac : mime = {type_ = "audio"; subtype = "usac"}
let audio_vdvi : mime = {type_ = "audio"; subtype = "VDVI"}
let audio_vmr_wb : mime = {type_ = "audio"; subtype = "VMR-WB"}
let audio_vnd_dot_3gpp_dot_iufp : mime = {type_ = "audio"; subtype = "vnd.3gpp.iufp"}
let audio_vnd_dot_4sb : mime = {type_ = "audio"; subtype = "vnd.4SB"}
let audio_vnd_dot_audiokoz : mime = {type_ = "audio"; subtype = "vnd.audiokoz"}
let audio_vnd_dot_blockfact_dot_facta : mime = {type_ = "audio"; subtype = "vnd.blockfact.facta"}
let audio_vnd_dot_celp : mime = {type_ = "audio"; subtype = "vnd.CELP"}
let audio_vnd_dot_cisco_dot_nse : mime = {type_ = "audio"; subtype = "vnd.cisco.nse"}
let audio_vnd_dot_cmles_dot_radio_events : mime = {type_ = "audio"; subtype = "vnd.cmles.radio-events"}
let audio_vnd_dot_cns_dot_anp1 : mime = {type_ = "audio"; subtype = "vnd.cns.anp1"}
let audio_vnd_dot_cns_dot_inf1 : mime = {type_ = "audio"; subtype = "vnd.cns.inf1"}
let audio_vnd_dot_dece_dot_audio : mime = {type_ = "audio"; subtype = "vnd.dece.audio"}
let audio_vnd_dot_digital_winds : mime = {type_ = "audio"; subtype = "vnd.digital-winds"}
let audio_vnd_dot_dlna_dot_adts : mime = {type_ = "audio"; subtype = "vnd.dlna.adts"}
let audio_vnd_dot_dolby_dot_heaac_dot_1 : mime = {type_ = "audio"; subtype = "vnd.dolby.heaac.1"}
let audio_vnd_dot_dolby_dot_heaac_dot_2 : mime = {type_ = "audio"; subtype = "vnd.dolby.heaac.2"}
let audio_vnd_dot_dolby_dot_mlp : mime = {type_ = "audio"; subtype = "vnd.dolby.mlp"}
let audio_vnd_dot_dolby_dot_mps : mime = {type_ = "audio"; subtype = "vnd.dolby.mps"}
let audio_vnd_dot_dolby_dot_pl2 : mime = {type_ = "audio"; subtype = "vnd.dolby.pl2"}
let audio_vnd_dot_dolby_dot_pl2x : mime = {type_ = "audio"; subtype = "vnd.dolby.pl2x"}
let audio_vnd_dot_dolby_dot_pl2z : mime = {type_ = "audio"; subtype = "vnd.dolby.pl2z"}
let audio_vnd_dot_dolby_dot_pulse_dot_1 : mime = {type_ = "audio"; subtype = "vnd.dolby.pulse.1"}
let audio_vnd_dot_dra : mime = {type_ = "audio"; subtype = "vnd.dra"}
let audio_vnd_dot_dts : mime = {type_ = "audio"; subtype = "vnd.dts"}
let audio_vnd_dot_dts_dot_hd : mime = {type_ = "audio"; subtype = "vnd.dts.hd"}
let audio_vnd_dot_dts_dot_uhd : mime = {type_ = "audio"; subtype = "vnd.dts.uhd"}
let audio_vnd_dot_dvb_dot_file : mime = {type_ = "audio"; subtype = "vnd.dvb.file"}
let audio_vnd_dot_everad_dot_plj : mime = {type_ = "audio"; subtype = "vnd.everad.plj"}
let audio_vnd_dot_hns_dot_audio : mime = {type_ = "audio"; subtype = "vnd.hns.audio"}
let audio_vnd_dot_lucent_dot_voice : mime = {type_ = "audio"; subtype = "vnd.lucent.voice"}
let audio_vnd_dot_ms_playready_dot_media_dot_pya : mime = {type_ = "audio"; subtype = "vnd.ms-playready.media.pya"}
let audio_vnd_dot_nokia_dot_mobile_xmf : mime = {type_ = "audio"; subtype = "vnd.nokia.mobile-xmf"}
let audio_vnd_dot_nortel_dot_vbk : mime = {type_ = "audio"; subtype = "vnd.nortel.vbk"}
let audio_vnd_dot_nuera_dot_ecelp4800 : mime = {type_ = "audio"; subtype = "vnd.nuera.ecelp4800"}
let audio_vnd_dot_nuera_dot_ecelp7470 : mime = {type_ = "audio"; subtype = "vnd.nuera.ecelp7470"}
let audio_vnd_dot_nuera_dot_ecelp9600 : mime = {type_ = "audio"; subtype = "vnd.nuera.ecelp9600"}
let audio_vnd_dot_octel_dot_sbc : mime = {type_ = "audio"; subtype = "vnd.octel.sbc"}
let audio_vnd_dot_presonus_dot_multitrack : mime = {type_ = "audio"; subtype = "vnd.presonus.multitrack"}
let audio_vnd_dot_qcelp : mime = {type_ = "audio"; subtype = "vnd.qcelp"}
let audio_vnd_dot_rhetorex_dot_32kadpcm : mime = {type_ = "audio"; subtype = "vnd.rhetorex.32kadpcm"}
let audio_vnd_dot_rip : mime = {type_ = "audio"; subtype = "vnd.rip"}
let audio_vnd_dot_sealedmedia_dot_softseal_dot_mpeg : mime = {type_ = "audio"; subtype = "vnd.sealedmedia.softseal.mpeg"}
let audio_vnd_dot_vmx_dot_cvsd : mime = {type_ = "audio"; subtype = "vnd.vmx.cvsd"}
let audio_vorbis : mime = {type_ = "audio"; subtype = "vorbis"}
let audio_vorbis_config : mime = {type_ = "audio"; subtype = "vorbis-config"}

(* ---- font/* ---- *)
let font_collection : mime = {type_ = "font"; subtype = "collection"}
let font_otf : mime = {type_ = "font"; subtype = "otf"}
let font_sfnt : mime = {type_ = "font"; subtype = "sfnt"}
let font_ttf : mime = {type_ = "font"; subtype = "ttf"}
let font_woff : mime = {type_ = "font"; subtype = "woff"}
let font_woff2 : mime = {type_ = "font"; subtype = "woff2"}

(* ---- image/* ---- *)
let image_aces : mime = {type_ = "image"; subtype = "aces"}
let image_apng : mime = {type_ = "image"; subtype = "apng"}
let image_avci : mime = {type_ = "image"; subtype = "avci"}
let image_avcs : mime = {type_ = "image"; subtype = "avcs"}
let image_avif : mime = {type_ = "image"; subtype = "avif"}
let image_bmp : mime = {type_ = "image"; subtype = "bmp"}
let image_cgm : mime = {type_ = "image"; subtype = "cgm"}
let image_dicom_rle : mime = {type_ = "image"; subtype = "dicom-rle"}
let image_dpx : mime = {type_ = "image"; subtype = "dpx"}
let image_emf : mime = {type_ = "image"; subtype = "emf"}
let image_example : mime = {type_ = "image"; subtype = "example"}
let image_fits : mime = {type_ = "image"; subtype = "fits"}
let image_g3fax : mime = {type_ = "image"; subtype = "g3fax"}
let image_gif : mime = {type_ = "image"; subtype = "gif"}
let image_heic : mime = {type_ = "image"; subtype = "heic"}
let image_heic_sequence : mime = {type_ = "image"; subtype = "heic-sequence"}
let image_heif : mime = {type_ = "image"; subtype = "heif"}
let image_heif_sequence : mime = {type_ = "image"; subtype = "heif-sequence"}
let image_hej2k : mime = {type_ = "image"; subtype = "hej2k"}
let image_hsj2 : mime = {type_ = "image"; subtype = "hsj2"}
let image_ief : mime = {type_ = "image"; subtype = "ief"}
let image_j2c : mime = {type_ = "image"; subtype = "j2c"}
let image_jaii : mime = {type_ = "image"; subtype = "jaii"}
let image_jais : mime = {type_ = "image"; subtype = "jais"}
let image_jls : mime = {type_ = "image"; subtype = "jls"}
let image_jp2 : mime = {type_ = "image"; subtype = "jp2"}
let image_jpeg : mime = {type_ = "image"; subtype = "jpeg"}
let image_jph : mime = {type_ = "image"; subtype = "jph"}
let image_jphc : mime = {type_ = "image"; subtype = "jphc"}
let image_jpm : mime = {type_ = "image"; subtype = "jpm"}
let image_jpx : mime = {type_ = "image"; subtype = "jpx"}
let image_jxl : mime = {type_ = "image"; subtype = "jxl"}
let image_jxr : mime = {type_ = "image"; subtype = "jxr"}
let image_jxra : mime = {type_ = "image"; subtype = "jxrA"}
let image_jxrs : mime = {type_ = "image"; subtype = "jxrS"}
let image_jxs : mime = {type_ = "image"; subtype = "jxs"}
let image_jxsc : mime = {type_ = "image"; subtype = "jxsc"}
let image_jxsi : mime = {type_ = "image"; subtype = "jxsi"}
let image_jxss : mime = {type_ = "image"; subtype = "jxss"}
let image_ktx : mime = {type_ = "image"; subtype = "ktx"}
let image_ktx2 : mime = {type_ = "image"; subtype = "ktx2"}
let image_naplps : mime = {type_ = "image"; subtype = "naplps"}
let image_png : mime = {type_ = "image"; subtype = "png"}
let image_prs_dot_btif : mime = {type_ = "image"; subtype = "prs.btif"}
let image_prs_dot_pti : mime = {type_ = "image"; subtype = "prs.pti"}
let image_pwg_raster : mime = {type_ = "image"; subtype = "pwg-raster"}
let image_svg_plus_xml : mime = {type_ = "image"; subtype = "svg+xml"}
let image_t38 : mime = {type_ = "image"; subtype = "t38"}
let image_tiff : mime = {type_ = "image"; subtype = "tiff"}
let image_tiff_fx : mime = {type_ = "image"; subtype = "tiff-fx"}
let image_vnd_dot_adobe_dot_photoshop : mime = {type_ = "image"; subtype = "vnd.adobe.photoshop"}
let image_vnd_dot_airzip_dot_accelerator_dot_azv : mime = {type_ = "image"; subtype = "vnd.airzip.accelerator.azv"}
let image_vnd_dot_blockfact_dot_facti : mime = {type_ = "image"; subtype = "vnd.blockfact.facti"}
let image_vnd_dot_clip : mime = {type_ = "image"; subtype = "vnd.clip"}
let image_vnd_dot_cns_dot_inf2 : mime = {type_ = "image"; subtype = "vnd.cns.inf2"}
let image_vnd_dot_dece_dot_graphic : mime = {type_ = "image"; subtype = "vnd.dece.graphic"}
let image_vnd_dot_djvu : mime = {type_ = "image"; subtype = "vnd.djvu"}
let image_vnd_dot_dwg : mime = {type_ = "image"; subtype = "vnd.dwg"}
let image_vnd_dot_dxf : mime = {type_ = "image"; subtype = "vnd.dxf"}
let image_vnd_dot_dvb_dot_subtitle : mime = {type_ = "image"; subtype = "vnd.dvb.subtitle"}
let image_vnd_dot_fastbidsheet : mime = {type_ = "image"; subtype = "vnd.fastbidsheet"}
let image_vnd_dot_fpx : mime = {type_ = "image"; subtype = "vnd.fpx"}
let image_vnd_dot_fst : mime = {type_ = "image"; subtype = "vnd.fst"}
let image_vnd_dot_fujixerox_dot_edmics_mmr : mime = {type_ = "image"; subtype = "vnd.fujixerox.edmics-mmr"}
let image_vnd_dot_fujixerox_dot_edmics_rlc : mime = {type_ = "image"; subtype = "vnd.fujixerox.edmics-rlc"}
let image_vnd_dot_globalgraphics_dot_pgb : mime = {type_ = "image"; subtype = "vnd.globalgraphics.pgb"}
let image_vnd_dot_microsoft_dot_icon : mime = {type_ = "image"; subtype = "vnd.microsoft.icon"}
let image_vnd_dot_mix : mime = {type_ = "image"; subtype = "vnd.mix"}
let image_vnd_dot_ms_modi : mime = {type_ = "image"; subtype = "vnd.ms-modi"}
let image_vnd_dot_mozilla_dot_apng : mime = {type_ = "image"; subtype = "vnd.mozilla.apng"}
let image_vnd_dot_net_fpx : mime = {type_ = "image"; subtype = "vnd.net-fpx"}
let image_vnd_dot_pco_dot_b16 : mime = {type_ = "image"; subtype = "vnd.pco.b16"}
let image_vnd_dot_radiance : mime = {type_ = "image"; subtype = "vnd.radiance"}
let image_vnd_dot_sealed_dot_png : mime = {type_ = "image"; subtype = "vnd.sealed.png"}
let image_vnd_dot_sealedmedia_dot_softseal_dot_gif : mime = {type_ = "image"; subtype = "vnd.sealedmedia.softseal.gif"}
let image_vnd_dot_sld : mime = {type_ = "image"; subtype = "vnd.sld"}
let image_vnd_dot_sealedmedia_dot_softseal_dot_jpg : mime = {type_ = "image"; subtype = "vnd.sealedmedia.softseal.jpg"}
let image_vnd_dot_svf : mime = {type_ = "image"; subtype = "vnd.svf"}
let image_vnd_dot_tencent_dot_tap : mime = {type_ = "image"; subtype = "vnd.tencent.tap"}
let image_vnd_dot_valve_dot_source_dot_texture : mime = {type_ = "image"; subtype = "vnd.valve.source.texture"}
let image_vnd_dot_wap_dot_wbmp : mime = {type_ = "image"; subtype = "vnd.wap.wbmp"}
let image_vnd_dot_xiff : mime = {type_ = "image"; subtype = "vnd.xiff"}
let image_vnd_dot_zbrush_dot_pcx : mime = {type_ = "image"; subtype = "vnd.zbrush.pcx"}
let image_webp : mime = {type_ = "image"; subtype = "webp"}
let image_wmf : mime = {type_ = "image"; subtype = "wmf"}
let image_x_emf : mime = {type_ = "image"; subtype = "x-emf"}
let image_x_wmf : mime = {type_ = "image"; subtype = "x-wmf"}

(* ---- message/* ---- *)
let message_bhttp : mime = {type_ = "message"; subtype = "bhttp"}
let message_cpim : mime = {type_ = "message"; subtype = "CPIM"}
let message_delivery_status : mime = {type_ = "message"; subtype = "delivery-status"}
let message_disposition_notification : mime = {type_ = "message"; subtype = "disposition-notification"}
let message_example : mime = {type_ = "message"; subtype = "example"}
let message_external_body : mime = {type_ = "message"; subtype = "external-body"}
let message_feedback_report : mime = {type_ = "message"; subtype = "feedback-report"}
let message_global : mime = {type_ = "message"; subtype = "global"}
let message_global_delivery_status : mime = {type_ = "message"; subtype = "global-delivery-status"}
let message_global_disposition_notification : mime = {type_ = "message"; subtype = "global-disposition-notification"}
let message_global_headers : mime = {type_ = "message"; subtype = "global-headers"}
let message_http : mime = {type_ = "message"; subtype = "http"}
let message_imdn_plus_xml : mime = {type_ = "message"; subtype = "imdn+xml"}
let message_mls : mime = {type_ = "message"; subtype = "mls"}
let message_news : mime = {type_ = "message"; subtype = "news"}
let message_ohttp_chunked_req : mime = {type_ = "message"; subtype = "ohttp-chunked-req"}
let message_ohttp_chunked_res : mime = {type_ = "message"; subtype = "ohttp-chunked-res"}
let message_ohttp_req : mime = {type_ = "message"; subtype = "ohttp-req"}
let message_ohttp_res : mime = {type_ = "message"; subtype = "ohttp-res"}
let message_partial : mime = {type_ = "message"; subtype = "partial"}
let message_rfc822 : mime = {type_ = "message"; subtype = "rfc822"}
let message_s_http : mime = {type_ = "message"; subtype = "s-http"}
let message_sip : mime = {type_ = "message"; subtype = "sip"}
let message_sipfrag : mime = {type_ = "message"; subtype = "sipfrag"}
let message_tracking_status : mime = {type_ = "message"; subtype = "tracking-status"}
let message_vnd_dot_si_dot_simp : mime = {type_ = "message"; subtype = "vnd.si.simp"}
let message_vnd_dot_wfa_dot_wsc : mime = {type_ = "message"; subtype = "vnd.wfa.wsc"}

(* ---- model/* ---- *)
let model__3mf : mime = {type_ = "model"; subtype = "3mf"}
let model_e57 : mime = {type_ = "model"; subtype = "e57"}
let model_example : mime = {type_ = "model"; subtype = "example"}
let model_gltf_binary : mime = {type_ = "model"; subtype = "gltf-binary"}
let model_gltf_plus_json : mime = {type_ = "model"; subtype = "gltf+json"}
let model_jt : mime = {type_ = "model"; subtype = "JT"}
let model_iges : mime = {type_ = "model"; subtype = "iges"}
let model_mesh : mime = {type_ = "model"; subtype = "mesh"}
let model_mtl : mime = {type_ = "model"; subtype = "mtl"}
let model_obj : mime = {type_ = "model"; subtype = "obj"}
let model_prc : mime = {type_ = "model"; subtype = "prc"}
let model_step : mime = {type_ = "model"; subtype = "step"}
let model_step_plus_xml : mime = {type_ = "model"; subtype = "step+xml"}
let model_step_plus_zip : mime = {type_ = "model"; subtype = "step+zip"}
let model_step_xml_plus_zip : mime = {type_ = "model"; subtype = "step-xml+zip"}
let model_stl : mime = {type_ = "model"; subtype = "stl"}
let model_u3d : mime = {type_ = "model"; subtype = "u3d"}
let model_vnd_dot_bary : mime = {type_ = "model"; subtype = "vnd.bary"}
let model_vnd_dot_cld : mime = {type_ = "model"; subtype = "vnd.cld"}
let model_vnd_dot_collada_plus_xml : mime = {type_ = "model"; subtype = "vnd.collada+xml"}
let model_vnd_dot_dwf : mime = {type_ = "model"; subtype = "vnd.dwf"}
let model_vnd_dot_flatland_dot_3dml : mime = {type_ = "model"; subtype = "vnd.flatland.3dml"}
let model_vnd_dot_gdl : mime = {type_ = "model"; subtype = "vnd.gdl"}
let model_vnd_dot_gs_gdl : mime = {type_ = "model"; subtype = "vnd.gs-gdl"}
let model_vnd_dot_gtw : mime = {type_ = "model"; subtype = "vnd.gtw"}
let model_vnd_dot_moml_plus_xml : mime = {type_ = "model"; subtype = "vnd.moml+xml"}
let model_vnd_dot_mts : mime = {type_ = "model"; subtype = "vnd.mts"}
let model_vnd_dot_opengex : mime = {type_ = "model"; subtype = "vnd.opengex"}
let model_vnd_dot_parasolid_dot_transmit_dot_binary : mime = {type_ = "model"; subtype = "vnd.parasolid.transmit.binary"}
let model_vnd_dot_parasolid_dot_transmit_dot_text : mime = {type_ = "model"; subtype = "vnd.parasolid.transmit.text"}
let model_vnd_dot_pytha_dot_pyox : mime = {type_ = "model"; subtype = "vnd.pytha.pyox"}
let model_vnd_dot_rosette_dot_annotated_data_model : mime = {type_ = "model"; subtype = "vnd.rosette.annotated-data-model"}
let model_vnd_dot_sap_dot_vds : mime = {type_ = "model"; subtype = "vnd.sap.vds"}
let model_vnd_dot_usda : mime = {type_ = "model"; subtype = "vnd.usda"}
let model_vnd_dot_usdz_plus_zip : mime = {type_ = "model"; subtype = "vnd.usdz+zip"}
let model_vnd_dot_valve_dot_source_dot_compiled_map : mime = {type_ = "model"; subtype = "vnd.valve.source.compiled-map"}
let model_vnd_dot_vtu : mime = {type_ = "model"; subtype = "vnd.vtu"}
let model_vrml : mime = {type_ = "model"; subtype = "vrml"}
let model_x3d_vrml : mime = {type_ = "model"; subtype = "x3d-vrml"}
let model_x3d_plus_fastinfoset : mime = {type_ = "model"; subtype = "x3d+fastinfoset"}
let model_x3d_plus_xml : mime = {type_ = "model"; subtype = "x3d+xml"}

(* ---- multipart/* ---- *)
let multipart_alternative : mime = {type_ = "multipart"; subtype = "alternative"}
let multipart_appledouble : mime = {type_ = "multipart"; subtype = "appledouble"}
let multipart_byteranges : mime = {type_ = "multipart"; subtype = "byteranges"}
let multipart_digest : mime = {type_ = "multipart"; subtype = "digest"}
let multipart_encrypted : mime = {type_ = "multipart"; subtype = "encrypted"}
let multipart_example : mime = {type_ = "multipart"; subtype = "example"}
let multipart_form_data : mime = {type_ = "multipart"; subtype = "form-data"}
let multipart_header_set : mime = {type_ = "multipart"; subtype = "header-set"}
let multipart_mixed : mime = {type_ = "multipart"; subtype = "mixed"}
let multipart_multilingual : mime = {type_ = "multipart"; subtype = "multilingual"}
let multipart_parallel : mime = {type_ = "multipart"; subtype = "parallel"}
let multipart_related : mime = {type_ = "multipart"; subtype = "related"}
let multipart_report : mime = {type_ = "multipart"; subtype = "report"}
let multipart_signed : mime = {type_ = "multipart"; subtype = "signed"}
let multipart_vnd_dot_bint_dot_med_plus : mime = {type_ = "multipart"; subtype = "vnd.bint.med-plus"}
let multipart_voice_message : mime = {type_ = "multipart"; subtype = "voice-message"}
let multipart_x_mixed_replace : mime = {type_ = "multipart"; subtype = "x-mixed-replace"}

(* ---- text/* ---- *)
let text__1d_interleaved_parityfec : mime = {type_ = "text"; subtype = "1d-interleaved-parityfec"}
let text_cache_manifest : mime = {type_ = "text"; subtype = "cache-manifest"}
let text_calendar : mime = {type_ = "text"; subtype = "calendar"}
let text_cql : mime = {type_ = "text"; subtype = "cql"}
let text_cql_expression : mime = {type_ = "text"; subtype = "cql-expression"}
let text_cql_identifier : mime = {type_ = "text"; subtype = "cql-identifier"}
let text_css : mime = {type_ = "text"; subtype = "css"}
let text_csv : mime = {type_ = "text"; subtype = "csv"}
let text_csv_schema : mime = {type_ = "text"; subtype = "csv-schema"}
let text_directory : mime = {type_ = "text"; subtype = "directory"}
let text_dns : mime = {type_ = "text"; subtype = "dns"}
let text_ecmascript : mime = {type_ = "text"; subtype = "ecmascript"}
let text_encaprtp : mime = {type_ = "text"; subtype = "encaprtp"}
let text_enriched : mime = {type_ = "text"; subtype = "enriched"}
let text_example : mime = {type_ = "text"; subtype = "example"}
let text_fhirpath : mime = {type_ = "text"; subtype = "fhirpath"}
let text_flexfec : mime = {type_ = "text"; subtype = "flexfec"}
let text_fwdred : mime = {type_ = "text"; subtype = "fwdred"}
let text_gff3 : mime = {type_ = "text"; subtype = "gff3"}
let text_grammar_ref_list : mime = {type_ = "text"; subtype = "grammar-ref-list"}
let text_hl7v2 : mime = {type_ = "text"; subtype = "hl7v2"}
let text_html : mime = {type_ = "text"; subtype = "html"}
let text_javascript : mime = {type_ = "text"; subtype = "javascript"}
let text_jcr_cnd : mime = {type_ = "text"; subtype = "jcr-cnd"}
let text_markdown : mime = {type_ = "text"; subtype = "markdown"}
let text_mizar : mime = {type_ = "text"; subtype = "mizar"}
let text_n3 : mime = {type_ = "text"; subtype = "n3"}
let text_org : mime = {type_ = "text"; subtype = "org"}
let text_parameters : mime = {type_ = "text"; subtype = "parameters"}
let text_parityfec : mime = {type_ = "text"; subtype = "parityfec"}
let text_plain : mime = {type_ = "text"; subtype = "plain"}
let text_provenance_notation : mime = {type_ = "text"; subtype = "provenance-notation"}
let text_prs_dot_fallenstein_dot_rst : mime = {type_ = "text"; subtype = "prs.fallenstein.rst"}
let text_prs_dot_lines_dot_tag : mime = {type_ = "text"; subtype = "prs.lines.tag"}
let text_prs_dot_prop_dot_logic : mime = {type_ = "text"; subtype = "prs.prop.logic"}
let text_prs_dot_texi : mime = {type_ = "text"; subtype = "prs.texi"}
let text_raptorfec : mime = {type_ = "text"; subtype = "raptorfec"}
let text_red : mime = {type_ = "text"; subtype = "RED"}
let text_rfc822_headers : mime = {type_ = "text"; subtype = "rfc822-headers"}
let text_richtext : mime = {type_ = "text"; subtype = "richtext"}
let text_rtf : mime = {type_ = "text"; subtype = "rtf"}
let text_rtp_enc_aescm128 : mime = {type_ = "text"; subtype = "rtp-enc-aescm128"}
let text_rtploopback : mime = {type_ = "text"; subtype = "rtploopback"}
let text_rtx : mime = {type_ = "text"; subtype = "rtx"}
let text_sgml : mime = {type_ = "text"; subtype = "SGML"}
let text_shaclc : mime = {type_ = "text"; subtype = "shaclc"}
let text_shex : mime = {type_ = "text"; subtype = "shex"}
let text_spdx : mime = {type_ = "text"; subtype = "spdx"}
let text_strings : mime = {type_ = "text"; subtype = "strings"}
let text_t140 : mime = {type_ = "text"; subtype = "t140"}
let text_tab_separated_values : mime = {type_ = "text"; subtype = "tab-separated-values"}
let text_troff : mime = {type_ = "text"; subtype = "troff"}
let text_turtle : mime = {type_ = "text"; subtype = "turtle"}
let text_ulpfec : mime = {type_ = "text"; subtype = "ulpfec"}
let text_uri_list : mime = {type_ = "text"; subtype = "uri-list"}
let text_vcard : mime = {type_ = "text"; subtype = "vcard"}
let text_vnd_dot_a : mime = {type_ = "text"; subtype = "vnd.a"}
let text_vnd_dot_abc : mime = {type_ = "text"; subtype = "vnd.abc"}
let text_vnd_dot_ascii_art : mime = {type_ = "text"; subtype = "vnd.ascii-art"}
let text_vnd_dot_curl : mime = {type_ = "text"; subtype = "vnd.curl"}
let text_vnd_dot_debian_dot_copyright : mime = {type_ = "text"; subtype = "vnd.debian.copyright"}
let text_vnd_dot_dmclientscript : mime = {type_ = "text"; subtype = "vnd.DMClientScript"}
let text_vnd_dot_dvb_dot_subtitle : mime = {type_ = "text"; subtype = "vnd.dvb.subtitle"}
let text_vnd_dot_esmertec_dot_theme_descriptor : mime = {type_ = "text"; subtype = "vnd.esmertec.theme-descriptor"}
let text_vnd_dot_exchangeable : mime = {type_ = "text"; subtype = "vnd.exchangeable"}
let text_vnd_dot_familysearch_dot_gedcom : mime = {type_ = "text"; subtype = "vnd.familysearch.gedcom"}
let text_vnd_dot_ficlab_dot_flt : mime = {type_ = "text"; subtype = "vnd.ficlab.flt"}
let text_vnd_dot_fly : mime = {type_ = "text"; subtype = "vnd.fly"}
let text_vnd_dot_fmi_dot_flexstor : mime = {type_ = "text"; subtype = "vnd.fmi.flexstor"}
let text_vnd_dot_gml : mime = {type_ = "text"; subtype = "vnd.gml"}
let text_vnd_dot_graphviz : mime = {type_ = "text"; subtype = "vnd.graphviz"}
let text_vnd_dot_hans : mime = {type_ = "text"; subtype = "vnd.hans"}
let text_vnd_dot_hgl : mime = {type_ = "text"; subtype = "vnd.hgl"}
let text_vnd_dot_in3d_dot_3dml : mime = {type_ = "text"; subtype = "vnd.in3d.3dml"}
let text_vnd_dot_in3d_dot_spot : mime = {type_ = "text"; subtype = "vnd.in3d.spot"}
let text_vnd_dot_iptc_dot_newsml : mime = {type_ = "text"; subtype = "vnd.IPTC.NewsML"}
let text_vnd_dot_iptc_dot_nitf : mime = {type_ = "text"; subtype = "vnd.IPTC.NITF"}
let text_vnd_dot_latex_z : mime = {type_ = "text"; subtype = "vnd.latex-z"}
let text_vnd_dot_longform : mime = {type_ = "text"; subtype = "vnd.longform"}
let text_vnd_dot_motorola_dot_reflex : mime = {type_ = "text"; subtype = "vnd.motorola.reflex"}
let text_vnd_dot_ms_mediapackage : mime = {type_ = "text"; subtype = "vnd.ms-mediapackage"}
let text_vnd_dot_net2phone_dot_commcenter_dot_command : mime = {type_ = "text"; subtype = "vnd.net2phone.commcenter.command"}
let text_vnd_dot_radisys_dot_msml_basic_layout : mime = {type_ = "text"; subtype = "vnd.radisys.msml-basic-layout"}
let text_vnd_dot_senx_dot_warpscript : mime = {type_ = "text"; subtype = "vnd.senx.warpscript"}
let text_vnd_dot_si_dot_uricatalogue : mime = {type_ = "text"; subtype = "vnd.si.uricatalogue"}
let text_vnd_dot_sun_dot_j2me_dot_app_descriptor : mime = {type_ = "text"; subtype = "vnd.sun.j2me.app-descriptor"}
let text_vnd_dot_sosi : mime = {type_ = "text"; subtype = "vnd.sosi"}
let text_vnd_dot_tps : mime = {type_ = "text"; subtype = "vnd.tps"}
let text_vnd_dot_typst : mime = {type_ = "text"; subtype = "vnd.typst"}
let text_vnd_dot_trolltech_dot_linguist : mime = {type_ = "text"; subtype = "vnd.trolltech.linguist"}
let text_vnd_dot_vcf : mime = {type_ = "text"; subtype = "vnd.vcf"}
let text_vnd_dot_vri : mime = {type_ = "text"; subtype = "vnd.vri"}
let text_vnd_dot_wap_dot_si : mime = {type_ = "text"; subtype = "vnd.wap.si"}
let text_vnd_dot_wap_dot_sl : mime = {type_ = "text"; subtype = "vnd.wap.sl"}
let text_vnd_dot_wap_dot_wml : mime = {type_ = "text"; subtype = "vnd.wap.wml"}
let text_vnd_dot_wap_dot_wmlscript : mime = {type_ = "text"; subtype = "vnd.wap.wmlscript"}
let text_vnd_dot_zoo_dot_kcl : mime = {type_ = "text"; subtype = "vnd.zoo.kcl"}
let text_vtt : mime = {type_ = "text"; subtype = "vtt"}
let text_wgsl : mime = {type_ = "text"; subtype = "wgsl"}
let text_xml : mime = {type_ = "text"; subtype = "xml"}
let text_xml_external_parsed_entity : mime = {type_ = "text"; subtype = "xml-external-parsed-entity"}

(* ---- video/* ---- *)
let video__1d_interleaved_parityfec : mime = {type_ = "video"; subtype = "1d-interleaved-parityfec"}
let video__3gpp : mime = {type_ = "video"; subtype = "3gpp"}
let video__3gpp2 : mime = {type_ = "video"; subtype = "3gpp2"}
let video__3gpp_tt : mime = {type_ = "video"; subtype = "3gpp-tt"}
let video_av1 : mime = {type_ = "video"; subtype = "AV1"}
let video_bmpeg : mime = {type_ = "video"; subtype = "BMPEG"}
let video_bt656 : mime = {type_ = "video"; subtype = "BT656"}
let video_celb : mime = {type_ = "video"; subtype = "CelB"}
let video_dv : mime = {type_ = "video"; subtype = "DV"}
let video_encaprtp : mime = {type_ = "video"; subtype = "encaprtp"}
let video_evc : mime = {type_ = "video"; subtype = "evc"}
let video_example : mime = {type_ = "video"; subtype = "example"}
let video_ffv1 : mime = {type_ = "video"; subtype = "FFV1"}
let video_flexfec : mime = {type_ = "video"; subtype = "flexfec"}
let video_h261 : mime = {type_ = "video"; subtype = "H261"}
let video_h263 : mime = {type_ = "video"; subtype = "H263"}
let video_h263_1998 : mime = {type_ = "video"; subtype = "H263-1998"}
let video_h263_2000 : mime = {type_ = "video"; subtype = "H263-2000"}
let video_h264 : mime = {type_ = "video"; subtype = "H264"}
let video_h264_rcdo : mime = {type_ = "video"; subtype = "H264-RCDO"}
let video_h264_svc : mime = {type_ = "video"; subtype = "H264-SVC"}
let video_h265 : mime = {type_ = "video"; subtype = "H265"}
let video_h266 : mime = {type_ = "video"; subtype = "H266"}
let video_iso_dot_segment : mime = {type_ = "video"; subtype = "iso.segment"}
let video_jpeg : mime = {type_ = "video"; subtype = "JPEG"}
let video_jpeg2000 : mime = {type_ = "video"; subtype = "jpeg2000"}
let video_jpeg2000_scl : mime = {type_ = "video"; subtype = "jpeg2000-scl"}
let video_jxsv : mime = {type_ = "video"; subtype = "jxsv"}
let video_lottie_plus_json : mime = {type_ = "video"; subtype = "lottie+json"}
let video_matroska : mime = {type_ = "video"; subtype = "matroska"}
let video_matroska_3d : mime = {type_ = "video"; subtype = "matroska-3d"}
let video_mj2 : mime = {type_ = "video"; subtype = "mj2"}
let video_mp1s : mime = {type_ = "video"; subtype = "MP1S"}
let video_mp2p : mime = {type_ = "video"; subtype = "MP2P"}
let video_mp2t : mime = {type_ = "video"; subtype = "MP2T"}
let video_mp4 : mime = {type_ = "video"; subtype = "mp4"}
let video_mp4v_es : mime = {type_ = "video"; subtype = "MP4V-ES"}
let video_mpv : mime = {type_ = "video"; subtype = "MPV"}
let video_mpeg : mime = {type_ = "video"; subtype = "mpeg"}
let video_mpeg4_generic : mime = {type_ = "video"; subtype = "mpeg4-generic"}
let video_nv : mime = {type_ = "video"; subtype = "nv"}
let video_ogg : mime = {type_ = "video"; subtype = "ogg"}
let video_parityfec : mime = {type_ = "video"; subtype = "parityfec"}
let video_pointer : mime = {type_ = "video"; subtype = "pointer"}
let video_quicktime : mime = {type_ = "video"; subtype = "quicktime"}
let video_raptorfec : mime = {type_ = "video"; subtype = "raptorfec"}
let video_raw : mime = {type_ = "video"; subtype = "raw"}
let video_rtp_enc_aescm128 : mime = {type_ = "video"; subtype = "rtp-enc-aescm128"}
let video_rtploopback : mime = {type_ = "video"; subtype = "rtploopback"}
let video_rtx : mime = {type_ = "video"; subtype = "rtx"}
let video_scip : mime = {type_ = "video"; subtype = "scip"}
let video_smpte291 : mime = {type_ = "video"; subtype = "smpte291"}
let video_smpte292m : mime = {type_ = "video"; subtype = "SMPTE292M"}
let video_ulpfec : mime = {type_ = "video"; subtype = "ulpfec"}
let video_vc1 : mime = {type_ = "video"; subtype = "vc1"}
let video_vc2 : mime = {type_ = "video"; subtype = "vc2"}
let video_vnd_dot_blockfact_dot_factv : mime = {type_ = "video"; subtype = "vnd.blockfact.factv"}
let video_vnd_dot_cctv : mime = {type_ = "video"; subtype = "vnd.CCTV"}
let video_vnd_dot_dece_dot_hd : mime = {type_ = "video"; subtype = "vnd.dece.hd"}
let video_vnd_dot_dece_dot_mobile : mime = {type_ = "video"; subtype = "vnd.dece.mobile"}
let video_vnd_dot_dece_dot_mp4 : mime = {type_ = "video"; subtype = "vnd.dece.mp4"}
let video_vnd_dot_dece_dot_pd : mime = {type_ = "video"; subtype = "vnd.dece.pd"}
let video_vnd_dot_dece_dot_sd : mime = {type_ = "video"; subtype = "vnd.dece.sd"}
let video_vnd_dot_dece_dot_video : mime = {type_ = "video"; subtype = "vnd.dece.video"}
let video_vnd_dot_directv_dot_mpeg : mime = {type_ = "video"; subtype = "vnd.directv.mpeg"}
let video_vnd_dot_directv_dot_mpeg_tts : mime = {type_ = "video"; subtype = "vnd.directv.mpeg-tts"}
let video_vnd_dot_dlna_dot_mpeg_tts : mime = {type_ = "video"; subtype = "vnd.dlna.mpeg-tts"}
let video_vnd_dot_dvb_dot_file : mime = {type_ = "video"; subtype = "vnd.dvb.file"}
let video_vnd_dot_fvt : mime = {type_ = "video"; subtype = "vnd.fvt"}
let video_vnd_dot_hns_dot_video : mime = {type_ = "video"; subtype = "vnd.hns.video"}
let video_vnd_dot_iptvforum_dot_1dparityfec_1010 : mime = {type_ = "video"; subtype = "vnd.iptvforum.1dparityfec-1010"}
let video_vnd_dot_iptvforum_dot_1dparityfec_2005 : mime = {type_ = "video"; subtype = "vnd.iptvforum.1dparityfec-2005"}
let video_vnd_dot_iptvforum_dot_2dparityfec_1010 : mime = {type_ = "video"; subtype = "vnd.iptvforum.2dparityfec-1010"}
let video_vnd_dot_iptvforum_dot_2dparityfec_2005 : mime = {type_ = "video"; subtype = "vnd.iptvforum.2dparityfec-2005"}
let video_vnd_dot_iptvforum_dot_ttsavc : mime = {type_ = "video"; subtype = "vnd.iptvforum.ttsavc"}
let video_vnd_dot_iptvforum_dot_ttsmpeg2 : mime = {type_ = "video"; subtype = "vnd.iptvforum.ttsmpeg2"}
let video_vnd_dot_motorola_dot_video : mime = {type_ = "video"; subtype = "vnd.motorola.video"}
let video_vnd_dot_motorola_dot_videop : mime = {type_ = "video"; subtype = "vnd.motorola.videop"}
let video_vnd_dot_mpegurl : mime = {type_ = "video"; subtype = "vnd.mpegurl"}
let video_vnd_dot_ms_playready_dot_media_dot_pyv : mime = {type_ = "video"; subtype = "vnd.ms-playready.media.pyv"}
let video_vnd_dot_nokia_dot_interleaved_multimedia : mime = {type_ = "video"; subtype = "vnd.nokia.interleaved-multimedia"}
let video_vnd_dot_nokia_dot_mp4vr : mime = {type_ = "video"; subtype = "vnd.nokia.mp4vr"}
let video_vnd_dot_nokia_dot_videovoip : mime = {type_ = "video"; subtype = "vnd.nokia.videovoip"}
let video_vnd_dot_objectvideo : mime = {type_ = "video"; subtype = "vnd.objectvideo"}
let video_vnd_dot_planar : mime = {type_ = "video"; subtype = "vnd.planar"}
let video_vnd_dot_radgamettools_dot_bink : mime = {type_ = "video"; subtype = "vnd.radgamettools.bink"}
let video_vnd_dot_radgamettools_dot_smacker : mime = {type_ = "video"; subtype = "vnd.radgamettools.smacker"}
let video_vnd_dot_sealed_dot_mpeg1 : mime = {type_ = "video"; subtype = "vnd.sealed.mpeg1"}
let video_vnd_dot_sealed_dot_mpeg4 : mime = {type_ = "video"; subtype = "vnd.sealed.mpeg4"}
let video_vnd_dot_sealed_dot_swf : mime = {type_ = "video"; subtype = "vnd.sealed.swf"}
let video_vnd_dot_sealedmedia_dot_softseal_dot_mov : mime = {type_ = "video"; subtype = "vnd.sealedmedia.softseal.mov"}
let video_vnd_dot_uvvu_dot_mp4 : mime = {type_ = "video"; subtype = "vnd.uvvu.mp4"}
let video_vnd_dot_youtube_dot_yt : mime = {type_ = "video"; subtype = "vnd.youtube.yt"}
let video_vnd_dot_vivo : mime = {type_ = "video"; subtype = "vnd.vivo"}
let video_vp8 : mime = {type_ = "video"; subtype = "VP8"}
let video_vp9 : mime = {type_ = "video"; subtype = "VP9"}

(* ========================================================================
   MIME Codec
   ======================================================================== *)


(* ── Token predicate + run ─────────────────────────────────────────── *)


(** [is_token_char] — RFC 2045 §5.1 token character predicate.
    Accept: `A-Z a-z 0-9` and `! # $ % & ' * + - . ^ _ ` { | } ~`.
    The `/` (0x2F) separator is deliberately NOT accepted — it delimits
    [type_]/[subtype] and never appears inside a token. *)
let is_token_char (b: U8.t) : bool =
  let v = U8.v b in
  (0x41 <= v && v <= 0x5A) || (0x61 <= v && v <= 0x7A) || (0x30 <= v && v <= 0x39) ||
  v = 0x21 || v = 0x23 || v = 0x24 || v = 0x25 || v = 0x26 || v = 0x27 ||
  v = 0x2A || v = 0x2B || v = 0x2D || v = 0x2E || v = 0x5E || v = 0x5F ||
  v = 0x60 || v = 0x7B || v = 0x7C || v = 0x7D || v = 0x7E


(** [token_run_wfcv] — a token run is well-formed iff it is non-empty and every
    byte is a token char.  A boolean mirror of [token_codec]'s [wfcv] (i.e.
    [satisfy_many1]'s `Cons? && for_all`), kept so the roundtrip lemmas read in
    domain terms.  NOT a parser — it is the well-formedness predicate only. *)
let token_run_wfcv (bs: list byte) : Tot bool =
  Cons? bs && FStar.List.Tot.for_all is_token_char bs


(** [token_codec] — one-or-more RFC 2045 token chars, as a [codec (list byte)].

    Built from [satisfy_many1 is_token_char]: a non-empty run of token chars.
    The `/` (0x2F) separator is deliberately not a token char, so a run always
    stops exactly at the type/subtype boundary. *)
let token_codec : codec (list byte) = satisfy_many1 is_token_char


(* ── bytes-level codec (type "/" subtype) ──────────────────────────── *)


(** [mime_bytes_codec] — `type "/" subtype` over the bytes-level mirror, as a
    [codec mime_bytes].

    Built from the combinators: [product] of [token_codec] (the [type]),
    [byte_val 0x2Fuy] (the `/`), and [token_codec] (the [subtype]), then
    [map_]ped into [mime_bytes].  The well-formedness guard is the conjunction
    of both token runs (non-empty + all token chars), which is exactly
    [satisfy_many1]'s [wfcv]. *)
let mime_bytes_codec : codec mime_bytes =
  map_
    (fun (((t, _), s) : (list byte & unit) & list byte) ->
      if Cons? t && Cons? s
      then Some ({ type_bytes = t; subtype_bytes = s })
      else None)
    (fun (mb: mime_bytes) ->
      Some ((mb.type_bytes, ()), mb.subtype_bytes))
    (product (product token_codec (byte_val 0x2Fuy)) token_codec)


(** [mime_bytes_enc] — serialize the bytes-level mirror to its byte list
    (`type / subtype`) via [mime_bytes_codec.enc]. *)
let mime_bytes_enc (mb: mime_bytes) : list byte =
  Seq.seq_to_list (mime_bytes_codec.enc mb)


(** [mime_bytes_dec] — parse `type "/" subtype` via [mime_bytes_codec.dec],
    returning the consumed length.  [None] on malformed input. *)
let mime_bytes_dec (input: list byte) : option (mime_bytes & nat) =
  match mime_bytes_codec.dec (Seq.seq_of_list input) with
  | Inr (mb, consumed) -> Some (mb, consumed)
  | Inl _ -> None


(** [lemma_mime_bytes_roundtrip] — the bytes-level roundtrip, via the generic
    [mime_bytes_codec.roundtrip] (no bespoke scanner). *)
let lemma_mime_bytes_roundtrip (mb: mime_bytes) : Lemma
  (requires token_run_wfcv mb.type_bytes /\ token_run_wfcv mb.subtype_bytes)
  (ensures mime_bytes_codec.dec (mime_bytes_codec.enc mb `Seq.append` Seq.empty)
           == Inr (mb, Seq.length (mime_bytes_codec.enc mb)))
  = mime_bytes_codec.roundtrip mb Seq.empty


(* ── string ↔ bytes bridges (local ASCII) ──────────────────────────── *)


(** [ascii_bytes_to_string] — ASCII [list byte] to [string] (code points < 128). *)
let ascii_bytes_to_string (bs: list byte) : string =
  FStar.String.string_of_list
    (List.Tot.map (fun (b: byte) -> FStar.Char.char_of_int (U8.v b)) bs)


(** [string_to_ascii_bytes] — [string] to [list byte], truncating code points
    via `% 256`.  Only valid for ASCII strings (guard with [string_is_ascii]). *)
let string_to_ascii_bytes (s: string) : list byte =
  List.Tot.map (fun (c: FStar.Char.char) -> U8.uint_to_t (FStar.Char.int_of_char c % 256))
    (FStar.String.list_of_string s)


(** [mime_of_bytes] — bytes-level mirror to [mime] (via the ASCII bridges). *)
let mime_of_bytes (mb: mime_bytes) : mime =
  { type_ = ascii_bytes_to_string mb.type_bytes
  ; subtype = ascii_bytes_to_string mb.subtype_bytes
  }


(** [mime_to_bytes] — [mime] to its bytes-level mirror. *)
let mime_to_bytes (m: mime) : mime_bytes =
  { type_bytes = string_to_ascii_bytes m.type_
  ; subtype_bytes = string_to_ascii_bytes m.subtype
  }


(* ── public string view ────────────────────────────────────────────── *)


(** [encode_mime] — serialize a [mime] to its `type/subtype` byte list. *)
let encode_mime (m: mime) : list byte =
  mime_bytes_enc (mime_to_bytes m)


(** [string_of_mime] — serialize a [mime] to `"type/subtype"`. *)
let string_of_mime (m: mime) : Tot string =
  ascii_bytes_to_string (encode_mime m)


(** [decode_mime] — parse a `type/subtype` byte list to a [mime]; [None] unless
    the whole input is consumed. *)
let decode_mime (input: list byte) : option mime =
  match mime_bytes_dec input with
  | Some (mb, consumed) ->
    if consumed = List.Tot.length input then Some (mime_of_bytes mb) else None
  | None -> None


(** [mime_of_string] — parse a MIME type string (`"text/html"`) into a [mime];
    [None] unless the whole input is consumed. *)
let mime_of_string (s: string) : GTot (option mime) =
  decode_mime (string_to_ascii_bytes s)


(* ── Lemmas ─────────────────────────────────────────────────────────── *)


(** [lemma_create_is_singleton] — [Seq.create 1 b] is the singleton [b].
    (Local [Seq]-level bridge so the encoder reduces.) *)
let lemma_create_is_singleton (b: byte) : Lemma
  (ensures Seq.create 1 b == seq_of_list [b])
  = Seq.lemma_eq_intro (Seq.create 1 b) (seq_of_list [b])


(** [lemma_mime_bytes_text_plain_concrete] — encoding [text/plain] produces the
    exact `type "/" subtype` byte list. *)
let lemma_mime_bytes_text_plain_concrete () : Lemma
  (ensures
    mime_bytes_enc { type_bytes = [0x74uy;0x65uy;0x78uy;0x74uy]
                   ; subtype_bytes = [0x70uy;0x6Cuy;0x61uy;0x69uy;0x6Euy] }
    == [0x74uy;0x65uy;0x78uy;0x74uy;0x2Fuy;0x70uy;0x6Cuy;0x61uy;0x69uy;0x6Euy])
  = Seq.lemma_eq_intro
      (mime_bytes_codec.enc { type_bytes = [0x74uy;0x65uy;0x78uy;0x74uy]
                            ; subtype_bytes = [0x70uy;0x6Cuy;0x61uy;0x69uy;0x6Euy] })
      (seq_of_list [0x74uy;0x65uy;0x78uy;0x74uy;0x2Fuy;0x70uy;0x6Cuy;0x61uy;0x69uy;0x6Euy]);
    ()


(** [lemma_mime_bytes_text_html_concrete] — encoding [text/html] produces the
    exact `type "/" subtype` byte list. *)
let lemma_mime_bytes_text_html_concrete () : Lemma
  (ensures
    mime_bytes_enc { type_bytes = [0x74uy;0x65uy;0x78uy;0x74uy]
                   ; subtype_bytes = [0x68uy;0x74uy;0x6Duy;0x6Cuy] }
    == [0x74uy;0x65uy;0x78uy;0x74uy;0x2Fuy;0x68uy;0x74uy;0x6Duy;0x6Cuy])
  = Seq.lemma_eq_intro
      (mime_bytes_codec.enc { type_bytes = [0x74uy;0x65uy;0x78uy;0x74uy]
                            ; subtype_bytes = [0x68uy;0x74uy;0x6Duy;0x6Cuy] })
      (seq_of_list [0x74uy;0x65uy;0x78uy;0x74uy;0x2Fuy;0x68uy;0x74uy;0x6Duy;0x6Cuy]);
    ()


(** [lemma_mime_bytes_reject_empty_type] — the codec's well-formedness guard
    is false for a missing [type] (`"/plain"`): the empty leading token run
    fails [mime_bytes_codec.wfcv]. *)
let lemma_mime_bytes_reject_empty_type () : Lemma
  (ensures
    (match mime_bytes_codec.wfcv { type_bytes = []; subtype_bytes = [0x70uy;0x6Cuy;0x61uy;0x69uy;0x6Euy] } with
     | true -> False
     | false -> True))
  = ()


(** [lemma_mime_bytes_reject_empty_subtype] — the codec's well-formedness guard
    is false for a missing [subtype] (`"text/"`): the empty trailing token run
    fails [mime_bytes_codec.wfcv]. *)
let lemma_mime_bytes_reject_empty_subtype () : Lemma
  (ensures
    (match mime_bytes_codec.wfcv { type_bytes = [0x74uy;0x65uy;0x78uy;0x74uy]; subtype_bytes = [] } with
     | true -> False
     | false -> True))
  = ()
