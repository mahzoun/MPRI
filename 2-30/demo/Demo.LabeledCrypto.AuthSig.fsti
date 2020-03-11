module Demo.LabeledCrypto.AuthSig

open FStar.HyperStack
open FStar.HyperStack.All
module ST = FStar.HyperStack.ST

open Demo.LabeledCrypto
(* Signatures with Authentication - Asymmetric *)
let sig_pred = ml:label -> lbytes ml -> Type0
val sig_key: a:principal -> p:sig_pred -> Type
val verif_key: a:principal -> p:sig_pred -> Type0
val sig_keygen: a:principal -> p:sig_pred -> ST (sig_key a p)
		      (requires (fun h0 -> True))
		      (ensures (fun h0 _ h1 -> h0 == h1))
val sig_to_verif: a:principal -> p:sig_pred -> sig_key a p -> verif_key a p


val sign: a:principal -> p:sig_pred -> ml:label ->
	  sk:sig_key a p -> msg:lbytes ml{p ml msg} -> sg:lbytes ml

val verify: a:principal -> p:sig_pred -> ml:label ->
	    vk:verif_key a p -> msg:lbytes ml -> sg:lbytes ml ->
	    b:bool
val sign_verify_auth_lemma: a:principal -> p:sig_pred -> ml:label -> vk:verif_key a p -> msg:lbytes ml -> sg:lbytes ml ->
  Lemma (requires (verify a p ml vk msg sg == true))
	(ensures (exists ml' msg'. includes ml' ml /\ coerce ml' ml msg' == msg /\ p ml' msg'))
  [SMTPat (verify a p ml vk msg sg)]


val sign_verify_lemma: a:principal -> p:sig_pred -> ml:label -> sk:sig_key a p -> msg:lbytes ml ->
  Lemma (requires (p ml msg))
	(ensures (verify a p ml (sig_to_verif a p sk) msg (sign a p ml sk msg) == true))
  [SMTPat (verify a p ml (sig_to_verif a p sk) msg (sign a p ml sk msg))]



val sign_coerce_verify_lemma: a:principal -> p:sig_pred -> ml1:label -> ml2:label ->
			      sk:sig_key a p -> msg:lbytes ml1 ->
  Lemma (requires (includes ml1 ml2 /\ p ml1 msg))
        (ensures (verify a p ml2 (sig_to_verif a p sk) (coerce ml1 ml2 msg) (coerce ml1 ml2 (sign a p ml1 sk msg)) == true))
  [SMTPat (verify a p ml2 (sig_to_verif a p sk) (coerce ml1 ml2 msg) (coerce ml1 ml2 (sign a p ml1 sk msg)))]

