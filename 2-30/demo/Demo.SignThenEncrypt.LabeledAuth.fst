module Demo.SignThenEncrypt.LabeledAuth

open FStar.HyperStack
open FStar.HyperStack.All
module ST = FStar.HyperStack.ST

open Demo.LabeledCrypto
open Demo.LabeledCrypto.AuthSig


(*  C -> S: pkC, pke_enc(pkS,k),ae_enc(k,(msg,sign(skC,msg))) *)

(* AUTHENTICATION GOAL: if S accepts (C,msg) then C must have sent msg to S *)

assume val sent: c:principal -> s:principal -> msg:lbytes (Secret [c;s]) -> Type0
let can_sign (c:principal) (ml:label) (m:lbytes ml) =
    exists s. ml == Secret [c;s] /\ sent c s m

val client_send: c:principal -> s:principal ->
		 sig_key c (can_sign c) -> pub_key s ->
		 ae_key (Secret [c;s]) ->
		 m:lbytes (Secret [c;s]){sent c s m} ->
		 (c:principal & verif_key c (can_sign c) & lbytes Public)

let client_send c s skC pkS k m =
    let sg = sign c (can_sign c) (Secret [c;s]) skC m in
    let em = ae_enc (Secret [c;s]) (Secret [c;s]) k (concat (Secret [c;s]) m sg) in
    let ek = pke_enc s (Secret [c;s]) pkS k in
    let cip = concat Public ek em in
    let vkC = sig_to_verif c (can_sign c) skC in
    (|c,vkC,cip|)

val server_recv: s:principal -> priv_key s ->
		 (c:principal & verif_key c (can_sign c) & lbytes Public) ->
		 option (principal * lbytes (Secret [s]))

let server_recv s skS (|c,vkC,m|) =
    match split Public m with
    | Some (ek,em) ->
      (match pke_dec s skS ek with
       | Some k ->
	 (match ae_dec (Secret [s]) k em with
	  | Some msg ->
	    (match split (Secret [s]) msg with
	     | Some (m,sg) ->
	       if verify c (can_sign c) (Secret [s]) vkC m sg then
		  (Some (c,m))
	       else None
	     | None -> None)
	 | None -> None)
      | None -> None)
   | None -> None

val client_server_lemma: c:principal -> s:principal ->
			 skC:sig_key c (can_sign c) -> skS:priv_key s ->
			 k:ae_key (Secret [c;s]) -> m:lbytes (Secret [c;s]) ->
  Lemma (requires (sent c s m))
	(ensures (server_recv s skS (client_send c s skC (priv_to_pub s skS) k m) ==
		  Some (c,coerce (Secret [c;s]) (Secret [s]) m)))
let client_server_lemma c s skC skS k m = ()

val client_server_auth_lemma: s:principal -> skS:priv_key s ->
			      m:(c:principal & verif_key c (can_sign c) & lbytes Public) ->
    Lemma (match server_recv s skS m with
	   | Some (c,msg) -> exists s' msg'. includes (Secret [c;s']) (Secret [s]) /\
				       msg == coerce (Secret [c;s']) (Secret [s]) msg' /\
				       sent c s' msg'
	   | None -> True)
let client_server_auth_lemma s skS m =
  match server_recv s skS m with
  | Some (c,msg) -> ()
  | None -> ()
