Require Import Reals Interval_tactic.
Local Open Scope R_scope.

(** Munoz_Narkawicz_JAR2013 paper *)
Lemma RD : forall x1 x2 x3 : R, -5 <= x1 <= 5 -> -5 <= x2 <= 5 -> -5 <= x3 <= 5 -> -367126907/10000000 <= -x1 + 2*x2 - x3 - 835634534/1000000000 * x2 * (1 + x2).
Time intros x1 x2 x3 H1 H2 H3; interval with (i_bisect_diff x2, i_prec 50).
Qed.
