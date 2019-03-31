(* randomly generated positive definite matrix *)

From Bignums Require Import BigZ.
Require Import mathcomp.ssreflect.seq.
Require Import Interval.Interval_bigint_carrier.
Require Import Interval.Interval_definitions.
Require Import Interval.Interval_specific_ops.
Require Import CoqEAL.refinements.seqmx.
Require Import CoqEAL.refinements.refinements.
Require Import CoqEAL.refinements.hrel.
Require Import CoqEAL.refinements.seqmx_complements.
From ValidSDP Require Import cholesky_prog iteri_ord posdef_check.
Import Refinements.Op.
Require Import Float.

Module F := SpecificFloat BigIntRadix2.

From FloatBench Require Import §mat§.

(* Profile floating-point arithmetic operations. *)

(* Tip to avoid the pretty-printing overhead when doing "Time Eval" *)
Lemma qed A (t : A) : unit.
exact tt.
Qed.
Notation "§" := (@qed _ _).

Definition select_intvl (a b : F.type) := a.
Definition select_float (a b : float) := a.

Notation doubling1 f := (let r1 := (f) in
                        let r2 := (f) in
                        select_intvl r1 r2) (only parsing).

Notation no_doubling1 f := (f) (only parsing).

Section test_CoqInterval.
Local Notation T := F.type (only parsing).
Definition two := Eval compute in
      let one := Float 1%bigZ 0%bigZ in
      F.add rnd_NE 53%bigZ one one.

Instance : add_of T := fun a b => no_doubling1 (F.add rnd_NE 53%bigZ a b).
Instance : mul_of T := fun a b => no_doubling1 (F.mul rnd_NE 53%bigZ a b).
Instance : sqrt_of T := fun a => (F.sqrt rnd_NE 53%bigZ a).
Instance : div_of T := fun a b => (F.div rnd_NE 53%bigZ a b).
Instance : opp_of T := fun a => (F.neg a).
Instance : zero_of T := F.zero.
Instance : one_of T := Float 1%bigZ 0%bigZ.

Time Eval vm_compute in qed _ (cholesky_seqmx (n := seq.size matrix) matrix).
End test_CoqInterval.
