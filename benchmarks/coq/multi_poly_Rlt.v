Require Import Reals Interval_tactic.
Local Open Scope R_scope.

(** Munoz_Narkawicz_JAR2013 paper *)
Lemma RD : forall x1 x2 x3 : R, -5 <= x1 <= 5 -> -5 <= x2 <= 5 -> -5 <= x3 <= 5 -> -367126907/10000000 < -x1 + 2*x2 - x3 - 835634534/1000000000 * x2 * (1 + x2).
Time intros x1 x2 x3 H1 H2 H3; interval with (i_bisect_diff x2, i_prec 50).
Qed.

Lemma adaptiveLV : forall x1 x2 x3 x4 : R,
  -2 <= x1 <= 2 -> -2 <= x2 <= 2 -> -2 <= x3 <= 2 -> -2 <= x4 <= 2 ->
  -20801/1000 < x1*x2^2 + x1 * x3^2 + x1*x4^2 - 11/10 * x1 + 1.
Time intros x1 x2 x3 x4 H1 H2 H3 H4; interval with (i_bisect_diff x1).
Qed.

Lemma butcher : forall x1 x2 x3 x4 x5 x6 : R,
  -1 <= x1 <= 0 -> -1/10 <= x2 <= 9/10 -> -1/10 <= x3 <= 1/2 ->
  -1 <= x4 <= -1/10 -> -1/10 <= x5 <= -5/100 -> -1/10 <= x6 <= -3/100 ->
  -144/100 < x6 * x2^2 + x5 * x3 ^2 - x1 * x4^2 + x4^3 + x4^2 - x1/3 + 4*x4/3.
Time intros x1 x2 x3 x4 x5 x6 H1 H2 H3 H4 H5 H6;
  interval with (i_bisect_diff x4).
Qed.

Lemma magnetism : forall x1 x2 x3 x4 x5 x6 x7 : R,
  -1 <= x1 <= 1 -> -1 <= x2 <= 1 -> -1 <= x3 <= 1 -> -1 <= x4 <= 1 ->
  -1 <= x5 <= 1 -> -1 <= x6 <= 1 -> -1 <= x7 <= 1 ->
   -25001/100000 < x1^2 + 2*x2^2 + 2*x3^2 + 2*x4^2 + 2*x5^2 + 2*x6^2 + 2*x7^2 - x1.
Time intros x1 x2 x3 x4 x5 x6 x7 H1 H2 H3 H4 H5 H6 H7;
  interval with (i_bisect_diff x1).
Qed.
