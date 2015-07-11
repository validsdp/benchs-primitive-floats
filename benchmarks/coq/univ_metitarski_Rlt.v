Require Import Reals Interval_tactic.
Local Open Scope R_scope.

Notation eps := (1/1024)%R (only parsing).
Notation meps := (-1/1024)%R (only parsing).

(** MetiTarski_JAR2010 paper *)

(* plot(abs(sin(x)) - 6/5 * abs(x), [-1, 1]); *)
Lemma MT16__1 : forall x : R, (-1 <= x <= 0) -> (sin x) > - (6/5 * - x + eps).
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

Lemma MT16__2 : forall x : R, (-1 <= x <= 0) -> (sin x) < 6/5 * - x + eps.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

Lemma MT16__3 : forall x : R, (0 <= x <= 1) -> (sin x) > - (6/5 * x + eps).
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

Lemma MT16__4 : forall x : R, (0 <= x <= 1) -> (sin x) < 6/5 * x + eps.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* plot(1 - 2 * x - cos(pi * x), [0, 1/2]); *)
Lemma MT17 : forall x : R, eps <= x <= 100/201 -> cos (PI * x) > 1 - 2 * x.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* plot(cos(x) - 1 + x^2/2, [-10,10]); *)
Lemma MT18 : forall x : R, -10 <= x <= 10 -> cos x - 1 + x^2 / 2 + eps > 0.
Proof.
Time intros x H; interval with (i_bisect_taylor x 2).
Qed.

(* plot(8 * sqrt(3) * x / (3 * sqrt(3) + sqrt(75 + 80 * x^2)) - atan(x), [0, 10]); *)
Lemma MT19 :
  forall x : R, 0 <= x <= 10 ->
  eps + atan x > 8 * sqrt 3 * x / (3 * sqrt 3 + sqrt (75 + 80 * x^2)).
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* plot((x + 1/x) * arctan(x) - 1, [0,5]); *)
Lemma MT20 : forall x : R, eps <= x <= 10 -> (x + 1 / x) * atan x > 1.
Proof.
Time intros x H; interval with (i_bisect_diff x, i_depth 25).
Qed.

(* plot(3 * x / (1 + 2 * sqrt(1 + x^2)) - atan(x), [0, 10]); *)
Lemma MT21 :
  forall x : R, 0 <= x <= 10 -> eps + atan x > 3 * x / (1 + 2 * sqrt (1 + x^2)).
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* plot(cos(x)-sin(x)/x, [0, pi]); *)
Lemma MT22 : forall x : R, eps <= x <= PI -> cos x < sin x / x.
Time intros x H; interval with (i_bisect_taylor x 5, i_depth 16).
Qed.

(* plot(cos(x) - (sin(x)/x)^2, [0, pi/2]); *)
Lemma MT23 : forall x : R, eps <= x <= PI / 2 -> cos x < (sin x / x) ^ 2.
Proof.
Time intros x H; interval with (i_bisect_taylor x 5).
Qed.

(* plot(sin(x)/3 + sin(3*x)/6, [pi/3-1, 2*pi/3+1]); *)
Lemma MT24 :
  forall x : R, PI/3 <= x <= 2*PI/3 - eps -> (sin x) / 3 + (sin (3*x)) / 6 > 0.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.
