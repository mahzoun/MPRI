module Demo.Crypto

open FStar.HyperStack
open FStar.HyperStack.All
module ST = FStar.HyperStack.ST

(* A type for byte arrays *)
val bytes: Type0
val concat: bytes -> bytes -> bytes
val split: bytes -> option (bytes * bytes)
val concat_split_lemma: b1:bytes -> b2:bytes ->
  Lemma (split (concat b1 b2) == Some (b1,b2))
  [SMTPat (split (concat b1 b2))]



(* Authenticated Encryption - Symmetric *)
val ae_key: Type0
val ae_keygen: unit -> ST ae_key
		      (requires (fun h0 -> True))
		      (ensures (fun h0 _ h1 -> h0 == h1))
val ae_enc: k:ae_key -> p:bytes -> c:bytes
val ae_dec: k:ae_key -> c:bytes -> option bytes
val ae_enc_dec_lemma: k:ae_key -> p:bytes ->
  Lemma (ae_dec k (ae_enc k p) == Some p)
  [SMTPat (ae_dec k (ae_enc k p))]


(* Public Key Encryption - Asymmetric *)
val pub_key: Type0
val priv_key: Type0
val priv_keygen: unit -> ST priv_key
		      (requires (fun h0 -> True))
		      (ensures (fun h0 _ h1 -> h0 == h1))
val priv_to_pub: priv_key -> pub_key
val pke_enc: pk:pub_key -> k:ae_key -> c:bytes
val pke_dec: sk:priv_key -> c:bytes -> option ae_key
val pke_enc_dec_lemma: sk:priv_key -> k:ae_key ->
  Lemma (pke_dec sk (pke_enc (priv_to_pub sk) k) == Some k)
  [SMTPat (pke_dec sk (pke_enc (priv_to_pub sk) k))]

(* Signatures - Asymmetric *)
val sig_key: Type0
val verif_key: Type0
val sig_keygen: unit -> ST sig_key
		      (requires (fun h0 -> True))
		      (ensures (fun h0 _ h1 -> h0 == h1))
val sig_to_verif: sig_key -> verif_key
val sign: sk:sig_key -> msg:bytes -> sg:bytes
val verify: vk:verif_key -> msg:bytes -> sg:bytes -> bool
val sign_verify_lemma: sk:sig_key -> msg:bytes ->
  Lemma (verify (sig_to_verif sk) msg (sign sk msg) == true)
  [SMTPat (verify (sig_to_verif sk) msg (sign sk msg))]

