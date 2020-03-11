module Demo.Chacha20

open FStar.HyperStack
open FStar.HyperStack.All
module ST = FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.ByteBuffer

module Spec = Spec.Chacha20
#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let state = lbuffer uint32 16ul
let index = i:size_t{size_v i < 16}

let spec_state (h:mem) (st:state) : GTot (Spec.state) =
    as_seq h st

val line:
    st:state
  -> a:index
  -> b:index
  -> d:index
  -> r:rotval U32 ->
  Stack unit
  (requires fun h -> live h st /\ v a <> v d)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    spec_state h1 st ==
    Spec.line (v a) (v b) (v d) r (spec_state h0 st))

let line st a b d r =
  let sta = st.(a) in
  let stb = st.(b) in
  let std = st.(d) in
  let sta = sta +. stb in
  let std = std ^. sta in
  let std = std <<<. r in
  st.(a) <- sta;
  st.(d) <- std


val quarter_round:
    st:state
  -> a:index
  -> b:index
  -> c:index
  -> d:index ->
  Stack unit
  (requires fun h -> live h st /\ v a <> v d /\ v c <> v b)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    spec_state h1 st ==
    Spec.quarter_round (v a) (v b) (v c) (v d) (spec_state h0 st))

let quarter_round st a b c d =
  line st a b d (size 16);
  line st c d b (size 12);
  line st a b d (size 8);
  line st c d b (size 7)

val double_round:
  st:state ->
  Stack unit
  (requires fun h -> live h st)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    spec_state h1 st == Spec.double_round (spec_state h0 st))

let double_round st =
  quarter_round st (size 0) (size 4) (size 8) (size 12);
  quarter_round st (size 1) (size 5) (size 9) (size 13);
  quarter_round st (size 2) (size 6) (size 10) (size 14);
  quarter_round st (size 3) (size 7) (size 11) (size 15);

  quarter_round st (size 0) (size 5) (size 10) (size 15);
  quarter_round st (size 1) (size 6) (size 11) (size 12);
  quarter_round st (size 2) (size 7) (size 8) (size 13);
  quarter_round st (size 3) (size 4) (size 9) (size 14)
