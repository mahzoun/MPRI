module Demo.SignThenEncrypt.Concrete

open FStar.HyperStack
open FStar.HyperStack.All
module ST = FStar.HyperStack.ST

open Demo.Crypto


(*  C -> S: pkC, pke_enc(pkS,k),ae_enc(k,(msg,sign(skC,msg))) *)

(* SECRECY GOAL: keep msg secret between C and S *)

val client_send: sig_key -> pub_key -> ae_key -> bytes -> (verif_key * bytes)
let client_send (skC:sig_key) (pkS:pub_key) (k:ae_key) (msg:bytes) =
    let sg = sign skC msg in
    let em = ae_enc k (concat msg sg) in
    let ek = pke_enc pkS k in
    let c = concat ek em in
    let vkC = sig_to_verif skC in
    (vkC,c)

val server_recv: priv_key -> (verif_key * bytes) -> option bytes

let server_recv skS (vkC,c) =
    match split c with
    | Some (ek,em) ->
      (match pke_dec skS ek with
       | Some k ->
	 (match ae_dec k em with
	  | Some msg ->
	    (match split msg with
	     | Some (m,sg) ->
	       if verify vkC m sg then
		  Some m
	       else None
	     | None -> None)
	 | None -> None)
      | None -> None)
   | None -> None


val client_server_lemma: skC:sig_key -> skS:priv_key -> k:ae_key -> m:bytes ->
  Lemma (server_recv skS (client_send skC (priv_to_pub skS) k m) == Some m)
let client_server_lemma skC skS k m = ()
