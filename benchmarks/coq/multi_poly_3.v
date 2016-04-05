Require Import Reals Interval.Interval_tactic.
Local Open Scope R_scope.

(** Munoz_Narkawicz_JAR2013 paper *)
Lemma butcher : forall x1 x2 x3 x4 x5 x6 : R,
  -1 <= x1 <= 0 -> -1/10 <= x2 <= 9/10 -> -1/10 <= x3 <= 1/2 ->
  -1 <= x4 <= -1/10 -> -1/10 <= x5 <= -5/100 -> -1/10 <= x6 <= -3/100 ->
  -144/100 <= x6 * x2^2 + x5 * x3 ^2 - x1 * x4^2 + x4^3 + x4^2 - x1/3 + 4*x4/3.
Time intros x1 x2 x3 x4 x5 x6 H1 H2 H3 H4 H5 H6;
  interval with (i_bisect_diff x4).
Qed.
