Require Import Reals Interval_tactic.
Local Open Scope R_scope.

(** Munoz_Narkawicz_JAR2013 paper *)
Lemma magnetism : forall x1 x2 x3 x4 x5 x6 x7 : R,
  -1 <= x1 <= 1 -> -1 <= x2 <= 1 -> -1 <= x3 <= 1 -> -1 <= x4 <= 1 ->
  -1 <= x5 <= 1 -> -1 <= x6 <= 1 -> -1 <= x7 <= 1 ->
   -25001/100000 <= x1^2 + 2*x2^2 + 2*x3^2 + 2*x4^2 + 2*x5^2 + 2*x6^2 + 2*x7^2 - x1.
Time intros x1 x2 x3 x4 x5 x6 x7 H1 H2 H3 H4 H5 H6 H7;
  interval with (i_bisect_diff x1).
Qed.
