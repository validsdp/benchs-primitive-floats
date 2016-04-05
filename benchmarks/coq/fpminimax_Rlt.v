Require Import Reals Interval.Interval_tactic.
Open Scope R_scope.

(** Facilities to parse negative powers and pre-compute powers of 2 *)
Notation "a * b ^(- n )" := (a / b ^ n)%R
  (at level 40, b at next level, only parsing) : R_scope.

(** FP minimax polynomials for cos(3/2 * cos(x)), generated using Sollya *)
Notation f x := (cos (3/2 * cos x)) (only parsing).
Notation D x := (-1 <= x <= 1/2) (only parsing).

(** Degree-2 *)
Notation p2 x := (5009597 * 2^(-26) + x * (-3452481 * 2^(-36) + x * (10948483 * 2^(-24)))) (only parsing).
Notation eps2 := (57 * 2^(-10)) (only parsing).

Lemma cos_cos_d2__1 :
  forall x, D x -> (p2 x - f x) / f x > - eps2.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

Lemma cos_cos_d2__2 :
  forall x, D x -> (p2 x - f x) / f x < eps2.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(** Degree-3 *)
Notation p3 x := (9578005 * 2^(-27) + x * (-8411879 * 2^(-29) + x * (6079307 * 2^(-23) + x * (14167647 * 2^(-27))))) (only parsing).
Notation eps3 := (51 * 2^(-11)) (only parsing).

Lemma cos_cos_d3__1 :
  forall x, D x -> (p3 x - f x) / f x > - eps3.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

Lemma cos_cos_d3__2 :
  forall x, D x -> (p3 x - f x) / f x < eps3.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(** Degree-4 *)
Notation p4 x := (2366509 * 2^(-25) + x * (10537089 * 2^(-34) + x * (1593929 * 2^(-21) + x * (-3609977 * 2^(-29) + x * (-609875 * 2^(-22)))))) (only parsing).
Notation eps4 := (51 * 2^(-14)) (only parsing).

Lemma cos_cos_d4__1 :
  forall x, D x -> (p4 x - f x) / f x > - eps4.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

Lemma cos_cos_d4__2 :
  forall x, D x -> (p4 x - f x) / f x < eps4.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(** Degree-5 *)
Notation p5 x := (9491875 * 2^(-27) + x * (1388077 * 2^(-31) + x * (12575645 * 2^(-24) + x * (-3473267 * 2^(-28) + x * (-13477879 * 2^(-27) + x * (11406127 * 2^(-28))))))) (only parsing).
Notation eps5 := (3 * 2^(-12)) (only parsing).

Lemma cos_cos_d5__1 :
  forall x, D x -> (p5 x - f x) / f x > - eps5.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

Lemma cos_cos_d5__2 :
  forall x, D x -> (p5 x - f x) / f x < eps5.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(** Degree-6 *)
Notation p6 x := (9492545 * 2^(-27) + x * (12716483 * 2^(-36) + x * (3142515 * 2^(-22) + x * (-8980587 * 2^(-31) + x * (-12736139 * 2^(-27) + x * (8061261 * 2^(-29) + x * (-13450525 * 2^(-29)))))))) (only parsing).
Notation eps6 := (17 * 2^(-16)) (only parsing).

Lemma cos_cos_d6__1 :
  forall x, D x -> (p6 x - f x) / f x > - eps6.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

Lemma cos_cos_d6__2 :
  forall x, D x -> (p6 x - f x) / f x < eps6.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(** Degree-7 *)
Notation p7 x := (4747227 * 2^(-26) + x * (5795109 * 2^(-37) + x * (784233 * 2^(-20) + x * (-6099871 * 2^(-32) + x * (-10729417 * 2^(-27) + x * (12242037 * 2^(-30) + x * (-8892053 * 2^(-27) + x * (-14339757 * 2^(-29))))))))) (only parsing).
Notation eps7 := (25 * 2^(-19)) (only parsing).

Lemma cos_cos_d7__1 :
  forall x, D x -> (p7 x - f x) / f x > - eps7.
Proof.
Time intros x H; interval with (i_bisect_taylor x 4).
Qed.

Lemma cos_cos_d7__2 :
  forall x, D x -> (p7 x - f x) / f x < eps7.
Proof.
Time intros x H; interval with (i_bisect_taylor x 4).
Qed.

(** Degree-8 *)
Notation p8 x := (9494185 * 2^(-27) + x * (12149587 * 2^(-41) + x * (6275713 * 2^(-23) + x * (-14107149 * 2^(-36) + x * (-2763427 * 2^(-25) + x * (14503039 * 2^(-33) + x * (-530509 * 2^(-23) + x * (-8256955 * 2^(-31) + x * (3638503 * 2^(-28)))))))))) (only parsing).
Notation eps8 := (5 * 2^(-20)) (only parsing).

Lemma cos_cos_d8__1 :
  forall x, D x -> (p8 x - f x) / f x > - eps8.
Proof.
Time intros x H; interval with (i_bisect_taylor x 4).
Qed.

Lemma cos_cos_d8__2 :
  forall x, D x -> (p8 x - f x) / f x < eps8.
Proof.
Time intros x H; interval with (i_bisect_taylor x 4).
Qed.
