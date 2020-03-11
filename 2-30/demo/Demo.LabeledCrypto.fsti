module Demo.LabeledCrypto

open FStar.HyperStack
open FStar.HyperStack.All
module ST = FStar.HyperStack.ST


(* Principals: participants in protocols *)
val principal: eqtype

(* Raw bytes *)
val bytes: Type0

(* Secrecy Labels: sets of principals *)
type label =
  | Public: label
  | Secret: list principal -> label
let includes l1 l2 =
  match l1,l2 with
  | Public,_ -> True
  | Secret pl1, Secret pl2 -> forall p. List.Tot.mem p pl2 ==> List.Tot.mem p pl1
  | _,_ -> False

(* A type for *labeled* byte arrays *)
val lbytes: label -> Type0
val coerce: l1:label -> l2:label{includes l1 l2} -> b1:lbytes l1 -> b2:lbytes l2

(* Concatenation preserves labels *)
val concat: l:label -> lbytes l -> lbytes l -> lbytes l
val split: l:label -> lbytes l -> option (lbytes l * lbytes l)
val concat_split_lemma: l:label -> b1:lbytes l -> b2:lbytes l ->
  Lemma (split l (concat l b1 b2) == Some (b1,b2))
  [SMTPat (split l (concat l b1 b2))]

val concat_coerce_split_lemma: l1:label -> l2:label -> b1:lbytes l1 -> b2:lbytes l1 ->
  Lemma (requires (includes l1 l2))
	(ensures (split l2 (coerce l1 l2 (concat l1 b1 b2)) == Some (coerce l1 l2 b1, coerce l1 l2 b2)))
  [SMTPat (split l2 (coerce l1 l2 (concat l1 b1 b2)))]

(* Authenticated Encryption - Symmetric *)
val ae_key: l:label -> Type0
val coerce_ae_key: l1:label -> l2:label{includes l1 l2} -> ae_key l1 -> ae_key l2
val ae_keygen: l:label -> ST (ae_key l)
		      (requires (fun h0 -> True))
		      (ensures (fun h0 _ h1 -> h0 == h1))

val ae_enc: kl:label -> ml:label{includes ml kl} -> k:ae_key kl -> m:lbytes ml -> c:lbytes Public
val ae_dec: kl:label -> k:ae_key kl -> c:lbytes Public -> option (lbytes kl)

val ae_enc_dec_lemma: kl:label -> ml:label -> k:ae_key kl -> m:lbytes ml ->
  Lemma (requires (includes ml kl))
	(ensures (ae_dec kl k (ae_enc kl ml k m) == Some (coerce ml kl m)))
  [SMTPat (ae_dec kl k (ae_enc kl ml k m))]

(* Decrypt with a coerced key, needed for protocol *)
val ae_enc_coerce_dec_lemma: kl1:label -> kl2:label -> ml:label ->
			     k:ae_key kl1 -> m:lbytes ml ->
  Lemma (requires (includes ml kl1 /\ includes kl1 kl2))
	(ensures (ae_dec kl2 (coerce_ae_key kl1 kl2 k) (ae_enc kl1 ml k m) ==
		  Some (coerce ml kl2 m)))
  [SMTPat (ae_dec kl2 (coerce_ae_key kl1 kl2 k) (ae_enc kl1 ml k m))]

(* Public Key Encryption - Asymmetric *)
val pub_key: a:principal -> Type0
val priv_key: a:principal -> Type0
val priv_keygen: a:principal -> ST (priv_key a)
		      (requires (fun h0 -> True))
		      (ensures (fun h0 _ h1 -> h0 == h1))
val priv_to_pub: a:principal -> priv_key a -> pub_key a
val pke_enc: r:principal -> kl:label{includes kl (Secret [r])} ->
	     pk:pub_key r -> k:ae_key kl -> c:lbytes Public

val pke_dec: r:principal -> sk:priv_key r -> c:lbytes Public -> option (ae_key (Secret [r]))
val pke_enc_dec_lemma: kl:label -> r:principal -> sk:priv_key r -> k:ae_key kl ->
  Lemma (requires (includes kl (Secret [r])))
	(ensures (pke_dec r sk (pke_enc r kl (priv_to_pub r sk) k) == Some (coerce_ae_key kl (Secret [r]) k)))
  [SMTPat (pke_dec r sk (pke_enc r kl (priv_to_pub r sk) k))]

(* Signatures - Asymmetric *)

val sig_key: a:principal -> Type0
val verif_key: a:principal -> Type0
val sig_keygen: a:principal -> ST (sig_key a)
		      (requires (fun h0 -> True))
		      (ensures (fun h0 _ h1 -> h0 == h1))
val sig_to_verif: a:principal -> sig_key a -> verif_key a
val sign: a:principal -> ml:label -> sk:sig_key a -> msg:lbytes ml -> sg:lbytes ml
val verify: a:principal -> ml:label -> vk:verif_key a -> msg:lbytes ml -> sg:lbytes ml -> bool
val sign_verify_lemma: a:principal -> ml:label -> sk:sig_key a -> msg:lbytes ml ->
  Lemma (verify a ml (sig_to_verif a sk) msg (sign a ml sk msg) == true)
  [SMTPat (verify a ml (sig_to_verif a sk) msg (sign a ml sk msg))]

val sign_coerce_verify_lemma: a:principal -> ml1:label -> ml2:label ->
			      sk:sig_key a -> msg:lbytes ml1 ->
  Lemma (requires (includes ml1 ml2))
        (ensures (verify a ml2 (sig_to_verif a sk) (coerce ml1 ml2 msg) (coerce ml1 ml2 (sign a ml1 sk msg)) == true))
  [SMTPat (verify a ml2 (sig_to_verif a sk) (coerce ml1 ml2 msg) (coerce ml1 ml2 (sign a ml1 sk msg)))]


