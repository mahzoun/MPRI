module Demo.SignThenEncrypt.Labeled

open FStar.HyperStack
open FStar.HyperStack.All
module ST = FStar.HyperStack.ST

open Demo.LabeledCrypto


(*  C -> S: pkC, pke_enc(pkS,k),ae_enc(k,(msg,sign(skC,msg))) *)

val client_send: c:principal -> s:principal ->
		 sig_key c -> pub_key s ->
		 ae_key (Secret [c;s]) ->
		 lbytes (Secret [c;s]) ->
		 (c:principal & verif_key c & lbytes Public)

let client_send c s skC pkS k m =
    let sg : lbytes (Secret [c;s]) = sign c (Secret [c;s]) skC m in
    let cc : lbytes (Secret [c;s]) = concat (Secret [c;s]) m sg in
    let em : lbytes Public = ae_enc (Secret [c;s]) (Secret [c;s]) k cc in
    let ek : lbytes Public = pke_enc s (Secret [c;s]) pkS k in
    let cip : lbytes Public = concat Public ek em in
    let vkC : verif_key c = sig_to_verif c skC in
    (|c,vkC,cip|)

val server_recv: s:principal -> priv_key s ->
		 (c:principal & verif_key c & lbytes Public) ->
		 option (lbytes (Secret [s]))

let server_recv s skS (|c,vkC,m|) =
    match split Public m with
    | Some (ek,em) ->
      (match pke_dec s skS ek with
       | Some k ->
	 (match ae_dec (Secret [s]) k em with
	  | Some msg ->
	    (match split (Secret [s]) msg with
	     | Some (msg,sg) ->
	       if verify c (Secret [s]) vkC msg sg then
		  Some msg
	       else None
	     | None -> None)
	 | None -> None)
      | None -> None)
   | None -> None

val client_server_lemma: c:principal -> s:principal ->
			 skC:sig_key c -> skS:priv_key s ->
			 k:ae_key (Secret [c;s]) -> m:lbytes (Secret [c;s]) ->
  Lemma (server_recv s skS (client_send c s skC (priv_to_pub s skS) k m) ==
	 Some (coerce (Secret [c;s]) (Secret [s]) m))
let client_server_lemma c s skC skS k m = ()


assume val net_send: lbytes Public -> ST unit (requires (fun h0 -> True)) (ensures (fun _ _ _ -> True))
assume val net_recv: unit -> ST (lbytes Public) (requires (fun h0 -> True)) (ensures (fun _ _ _ -> True))
assume val serialize_message: c:principal -> vkC: verif_key c -> lbytes Public -> lbytes Public
assume val parse_message: lbytes Public -> option (c:principal & vkC: verif_key c & lbytes Public)


let client c s skC pkS msg =
  let k = ae_keygen (Secret [c;s]) in
  let (|c,vkC,m|) = client_send c s skC pkS k msg in
  let w = serialize_message c vkC m in
  net_send w

let server s skS =
  let w = net_recv () in
  match parse_message w with
  | Some m -> server_recv s skS m
  | None -> None
