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
(* Definition select_float (a b : float) := a. *)
Definition select_float10a (a b c d e f g h i j : float) := a.
Definition select_float10b (a b c d e f g h i j : float) := a.
Definition select_float11c (a b c d e f g h i j k : float) := a.

Definition doubling' f (x y : float) := (let r1 := (f x y) in
                         let r2 := (f x y) in
                         let r3 := (f x y) in
                         let r4 := (f x y) in
                         let r5 := (f x y) in
                         let r6 := (f x y) in
                         let r7 := (f x y) in
                         let r8 := (f x y) in
                         let r9 := (f x y) in
                         let r10 := (f x y) in
                        select_float10a r1 r2 r3 r4 r5 r6 r7 r8 r9 r10).
Definition doubling'' f (x y : float) := (let r1 := (doubling' f x y) in
                         let r2 := (doubling' f x y) in
                         let r3 := (doubling' f x y) in
                         let r4 := (doubling' f x y) in
                         let r5 := (doubling' f x y) in
                         let r6 := (doubling' f x y) in
                         let r7 := (doubling' f x y) in
                         let r8 := (doubling' f x y) in
                         let r9 := (doubling' f x y) in
                         let r10 := (doubling' f x y) in
                        select_float10b r1 r2 r3 r4 r5 r6 r7 r8 r9 r10).
Notation doubling2 f x y := (let r1 := (doubling'' f x y) in
                         let r2 := (doubling'' f x y) in
                         let r3 := (doubling'' f x y) in
                         let r4 := (doubling'' f x y) in
                         let r5 := (doubling'' f x y) in
                         let r6 := (doubling'' f x y) in
                         let r7 := (doubling'' f x y) in
                         let r8 := (doubling'' f x y) in
                         let r9 := (doubling'' f x y) in
                         let r10 := (doubling'' f x y) in
                         let r11 := f%function x%float y%float in
                         select_float11c r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (only parsing).

(* doubling2 evaluates (f x y) 1001 times *)

Notation no_doubling2 f x y := (f x y) (only parsing).

Section test_Prim.
Local Notation T := float (only parsing).

Instance : add_of T := fun a b => no_doubling2 add a b.
Instance : mul_of T := fun a b => no_doubling2 mul a b.
Instance : sqrt_of T := fun a => sqrt a.
Instance : div_of T := fun a b => div a b.
Instance : opp_of T := fun a => opp a.
Instance : zero_of T := zero.
Instance : one_of T := one.

Time Eval vm_compute in qed _ (cholesky_seqmx (n := seq.size matrix_float) matrix_float).
End test_Prim.
