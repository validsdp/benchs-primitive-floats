Require Import Reals Interval.Interval_tactic.
Local Open Scope R_scope.

Notation eps := (1/1024)%R (only parsing).
Notation meps := (-1/1024)%R (only parsing).

(** MetiTarski_JAR2010 paper *)

(* plot(2 * abs(x) / (2 + x) - abs(log(1+x)), [-1, 10]); *)
Lemma MT1 :
  forall x : R, -1 + eps <= x <= 10 ->
  2 * Rabs x / (2 + x) <= Rabs (ln (1 + x)) + eps.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(* plot(abs(log(1+x)) + log(1 - abs(x)), [-1, 1]); *)
Lemma MT2 :
  forall x : R, -1 + eps <= x <= 1 - eps ->
  Rabs (ln (1 + x)) <= - ln (1 - Rabs x) + eps.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(* plot(abs(x)/(1 + abs(x)) - abs(log(1+x)), [-1, 1]); *)
Lemma MT3 :
  forall x : R, -1 + eps <= x <= 1 ->
  Rabs x / (1 + Rabs x) <= Rabs (ln (1 + x)) + eps.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* plot(abs(log(1+x)) - abs(x)*(1+abs(x))/abs(1+x), [-1, 10]); *)
Lemma MT4 :
  forall x : R, -1 + eps <= x <= 1 ->
  Rabs (ln (1 + x)) <= (Rabs x) * (1 + Rabs x) / Rabs (1 + x) + eps.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* plot(abs(x) / 4 - abs(exp(x) - 1), [-1, 1]); *)
Lemma MT5 :
  forall x : R, (-1 <= x <= meps \/ eps <= x <= 1) ->
  Rabs x / 4 < Rabs (exp x - 1).
Proof.
Time intros x [H|H]; interval with (i_bisect_diff x).
Qed.

(* plot(abs(exp(x) - 1) - 7 * abs(x)/4, [0, 1]); *)
Lemma MT6 :
  forall x : R, (-1 <= x <= meps \/ eps <= x <= 1) ->
  Rabs (exp x - 1) < 7 * (Rabs x) / 4.
Proof.
Time intros x [H|H]; interval with (i_bisect_diff x).
Qed.

(* plot(abs(exp(x) - 1) - (exp(abs(x)) - 1), [-10, 10]); *)
Lemma MT7 : forall x : R, -10 <= x <= meps -> Rabs (exp x - 1) <= exp (Rabs x) - 1.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* plot(abs(exp(x)-(1+x)) - abs(exp(abs(x))-(1+abs(x))), [-10, 10]); *)
Lemma MT8 :
  forall x : R, -10 <= x <= meps ->
  Rabs (exp x - (1 + x)) <= Rabs (exp (Rabs x) - (1 + Rabs x)).
Proof.
Time intros x H; interval with (i_bisect_taylor x 2, i_prec 40).
Qed.

(* plot(abs(exp(x)-(1+x/2)^2) - abs(exp(abs(x))-(1+abs(x)/2)^2), [-10, 10]); *)
Lemma MT9 :
  forall x : R, -10 <= x <= meps ->
  Rabs (exp x - (1 + x / 2) ^ 2) <= Rabs (exp (Rabs x) - (1 + (Rabs x) / 2) ^ 2).
Proof.
Time intros x H; interval with (i_bisect_taylor x 3, i_prec 40).
Qed.

(* plot(2*x/(2+x) - log(1+x), [0, 10]); *)
Lemma MT10 :
  forall x : R, 0 <= x <= 10 -> 2 * x / (2 + x) <= ln (1 + x) + eps.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(* plot(x/sqrt(1+x) - log(1+x), [-1/3,0]); *)
Lemma MT11 :
  forall x : R, -1/3 <= x <= 0 -> x / sqrt (1 + x) <= ln (1 + x) + eps.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3, i_prec 40).
Qed.

(* plot(log((1+x)/x)-(12*x^2 + 12*x + 1)/(12*x^3 + 18*x^2 + 6*x), [1/3, 10]); *)
Lemma MT12 :
  forall x : R, 1/3 <= x <= 10 ->
  ln ((1 + x) / x) <= (12*x^2 + 12*x + 1) / (12*x^3 + 18*x^2 + 6*x).
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(* plot(log((1+x)/x)-1/sqrt(x^2 + x), [1/3, 10]); *)
Lemma MT13 :
  forall x : R, 1/3 <= x <= 10 ->
  ln ((1 + x) / x) <= 1 / sqrt (x ^ 2 + x).
Proof.
Time intros x H; interval with (i_bisect_taylor x 3, i_prec 40).
Qed.

(* plot(exp(x - x^2) - 1 - x, [0, 1]); *)
Lemma MT14 : forall x : R, 0 <= x <= 1 -> exp (x - x^2) <= 1 + x + eps.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* plot(exp(-x/(1-x))-(1-x), [-10,1/2]); *)
Lemma MT15 : forall x : R, -10 <= x <= 1/2 -> exp(-x/(1 - x)) <= 1 - x + eps.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* plot(abs(sin(x)) - 6/5 * abs(x), [-1, 1]); *)
Lemma MT16 : forall x : R, -1 <= x <= 1 -> Rabs (sin x) <= 6/5 * Rabs x + eps.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* plot(1 - 2 * x - cos(pi * x), [0, 1/2]); *)
Lemma MT17 : forall x : R, eps <= x <= 100/201 -> cos (PI * x) > 1 - 2 * x.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* plot(cos(x) - 1 + x^2/2, [-10,10]); *)
Lemma MT18 : forall x : R, -10 <= x <= 10 -> cos x - 1 + x^2 / 2 + eps >= 0.
Proof.
Time intros x H; interval with (i_bisect_taylor x 2).
Qed.

(* plot(8 * sqrt(3) * x / (3 * sqrt(3) + sqrt(75 + 80 * x^2)) - atan(x), [0, 10]); *)
Lemma MT19 :
  forall x : R, 0 <= x <= 10 ->
  eps + atan x >= 8 * sqrt 3 * x / (3 * sqrt 3 + sqrt (75 + 80 * x^2)).
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
Lemma MT22 : forall x : R, eps <= x <= PI -> cos x <= sin x / x.
Proof.
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

(* plot(12-14.2*exp(-.318*x)+(3.25*cos(1.16*x)-.155*sin(1.16*x))*exp(-1.34*x),[-1/2,2]); *)
Lemma MT25 :
  forall x : R, 0 <= x <= 2 ->
  12 - 142/10 * exp(-318/1000*x) + (325/100*cos(116/100*x) - 155/1000*sin(116/100*x)) * exp(-134/100*x) > 0.
Proof.
Time intros x H; interval with (i_bisect x).
Qed.
