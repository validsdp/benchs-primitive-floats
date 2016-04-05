Require Import Reals Interval.Interval_tactic.
Local Open Scope R_scope.

(** Munoz_Narkawicz_JAR2013 paper *)
Lemma adaptiveLV : forall x1 x2 x3 x4 : R,
  -2 <= x1 <= 2 -> -2 <= x2 <= 2 -> -2 <= x3 <= 2 -> -2 <= x4 <= 2 ->
  -20801/1000 <= x1*x2^2 + x1 * x3^2 + x1*x4^2 - 11/10 * x1 + 1.
Time intros x1 x2 x3 x4 H1 H2 H3 H4; interval with (i_bisect_diff x1).
Qed.
