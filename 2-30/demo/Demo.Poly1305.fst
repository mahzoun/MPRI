module Demo.Poly1305

open FStar.HyperStack
open FStar.HyperStack.All
module ST = FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.ByteBuffer

module Spec = Spec.Poly1305
#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let felem_p = lbuffer uint32 5ul

val fadd1:
    out:felem_p
  -> f1:felem_p
  -> f2:felem_p
  -> Stack unit
    (requires fun h0 ->
      live h0 f1 /\ live h0 f2 /\ live h0 out)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1)
let fadd1 out f1 f2 =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let f14 = f1.(4ul) in
  let f20 = f2.(0ul) in
  let f21 = f2.(1ul) in
  let f22 = f2.(2ul) in
  let f23 = f2.(3ul) in
  let f24 = f2.(4ul) in
  let r0 = f10 +. f20 in
  let r1 = f11 +. f21 in
  let r2 = f12 +. f22 in
  let r3 = f13 +. f23 in
  let r4 = f14 +. f24 in
  out.(0ul) <- r0;
  out.(1ul) <- r1;
  out.(2ul) <- r2;
  out.(3ul) <- r3;
  out.(4ul) <- r4



let pow26: (pow26: pos { pow2 32 == 64 * pow26 /\ pow2 64 == 4096 * pow26 * pow26 /\ pow26 == pow2 26 }) =
  let pow26: pos = pow2 26 in
  assert_norm (pow2 32 == 64 * pow26);
  assert_norm (pow2 64 == 4096 * pow26 * pow26);
  pow26
let max26 = pow26 - 1

let pow52: (pow52:pos {pow52 == pow2 52}) = normalize_term (pow2 52)
let pow78: (pow78:pos {pow78 == pow2 78}) = normalize_term (pow2 78)
let pow104: (pow104:pos {pow104 == pow2 104}) = normalize_term (pow2 104)

let feval (h:mem) (f:felem_p) : GTot Spec.felem =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  (v s0 + v s1 * pow26 + v s2 * pow52 + v s3 * pow78 + v s4 * pow104) % Spec.prime

let felem_fits (h:mem) (f:felem_p) (n:nat) =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  (v s0 <= n * max26) /\
  (v s1 <= n * max26) /\
  (v s2 <= n * max26) /\
  (v s3 <= n * max26) /\
  (v s4 <= n * max26)

val fadd:
    n:nat
  -> m:nat{m + n < 64}
  -> out:felem_p
  -> f1:felem_p
  -> f2:felem_p
  -> Stack unit
    (requires fun h0 ->
      live h0 f1 /\ live h0 f2 /\ live h0 out /\
      felem_fits h0 f1 n /\
      felem_fits h0 f2 m)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (m+n) /\
      feval h1 out == Spec.fadd (feval h0 f1) (feval h0 f2))
let fadd n m out f1 f2 =
  let h0 = ST.get() in
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let f14 = f1.(4ul) in
  let f20 = f2.(0ul) in
  let f21 = f2.(1ul) in
  let f22 = f2.(2ul) in
  let f23 = f2.(3ul) in
  let f24 = f2.(4ul) in
  assert (v f10 + v f20 < pow2 32);
  assert (v f11 + v f21 < pow2 32);
  assert (v f12 + v f22 < pow2 32);
  assert (v f13 + v f23 < pow2 32);
  assert (v f14 + v f24 < pow2 32);
  let r0 = f10 +! f20 in
  let r1 = f11 +! f21 in
  let r2 = f12 +! f22 in
  let r3 = f13 +! f23 in
  let r4 = f14 +! f24 in
  out.(0ul) <- r0;
  out.(1ul) <- r1;
  out.(2ul) <- r2;
  out.(3ul) <- r3;
  out.(4ul) <- r4;
  let h1 = ST.get () in
  assert (felem_fits h1 out (m+n));
  assert (feval h0 f1 == (v f10 + v f11 * pow26 + v f12 * pow52 + v f13 * pow78 + v f14 * pow104) % Spec.prime);
  assert (feval h0 f2 == (v f20 + v f21 * pow26 + v f22 * pow52 + v f23 * pow78 + v f24 * pow104) % Spec.prime);
  assert (feval h1 out == ((v f10 + v f20) + (v f11 + v f21) * pow26 + (v f12 + v f22) * pow52 + (v f13 + v f23) * pow78 + (v f14 + v f24) * pow104) % Spec.prime);
  assert (feval h1 out == ((v f10 + v f11 * pow26 + v f12 * pow52 + v f13 * pow78 + v f14 * pow104) + (v f20 + v f21 * pow26 + v f22 * pow52 + v f23 * pow78 + v f24 * pow104)) % Spec.prime);
  FStar.Math.Lemmas.modulo_distributivity (v f10 + v f11 * pow26 + v f12 * pow52 + v f13 * pow78 + v f14 * pow104) (v f20 + v f21 * pow26 + v f22 * pow52 + v f23 * pow78 + v f24 * pow104) Spec.prime;
  assert (Spec.fadd (feval h0 f1) (feval h0 f2) == feval h1 out)


