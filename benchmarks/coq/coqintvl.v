Require Import Reals Interval.Interval_tactic.
Local Open Scope R_scope.

(* From bench-ineqs/benchmarks/coq/multi_poly.v *)

Lemma RD : forall x1 x2 x3 : R, -5 <= x1 <= 5 -> -5 <= x2 <= 5 -> -5 <= x3 <= 5 -> -367126907/10000000 <= -x1 + 2*x2 - x3 - 835634534/1000000000 * x2 * (1 + x2).
Time intros x1 x2 x3 H1 H2 H3; interval with (i_bisect_diff x2, i_prec 50).
Qed.

Lemma adaptiveLV : forall x1 x2 x3 x4 : R,
    -2 <= x1 <= 2 -> -2 <= x2 <= 2 -> -2 <= x3 <= 2 -> -2 <= x4 <= 2 ->
    -20801/1000 <= x1*x2^2 + x1 * x3^2 + x1*x4^2 - 11/10 * x1 + 1.
Time intros x1 x2 x3 x4 H1 H2 H3 H4; interval with (i_bisect_diff x1).
Qed.

Lemma butcher : forall x1 x2 x3 x4 x5 x6 : R,
    -1 <= x1 <= 0 -> -1/10 <= x2 <= 9/10 -> -1/10 <= x3 <= 1/2 ->
    -1 <= x4 <= -1/10 -> -1/10 <= x5 <= -5/100 -> -1/10 <= x6 <= -3/100 ->
    -144/100 <= x6 * x2^2 + x5 * x3 ^2 - x1 * x4^2 + x4^3 + x4^2 - x1/3 + 4*x4/3.
Time intros x1 x2 x3 x4 x5 x6 H1 H2 H3 H4 H5 H6;
  interval with (i_bisect_diff x4).
Qed.

Lemma magnetism : forall x1 x2 x3 x4 x5 x6 x7 : R,
    -1 <= x1 <= 1 -> -1 <= x2 <= 1 -> -1 <= x3 <= 1 -> -1 <= x4 <= 1 ->
    -1 <= x5 <= 1 -> -1 <= x6 <= 1 -> -1 <= x7 <= 1 ->
    -25001/100000 <= x1^2 + 2*x2^2 + 2*x3^2 + 2*x4^2 + 2*x5^2 + 2*x6^2 + 2*x7^2 - x1.
Time intros x1 x2 x3 x4 x5 x6 x7 H1 H2 H3 H4 H5 H6 H7;
  interval with (i_bisect_diff x1).
Qed.

(* From bench-ineqs/benchmarks/coq/univ_metitarski.v *)

Notation eps := (1/1024)%R (only parsing).
Notation meps := (-1/1024)%R (only parsing).

(** MetiTarski_JAR2010 paper *)

(* plot(2 * abs(x) / (2 + x) - abs(log(1+x)), [-1, 10]); *)
Lemma MT1 :
  forall x : R, -1 + eps <= x <= 10 ->
           2 * Rabs x / (2 + x) <= Rabs (ln (1 + x)) + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x 3).
Qed.

(* plot(abs(log(1+x)) + log(1 - abs(x)), [-1, 1]); *)
Lemma MT2 :
  forall x : R, -1 + eps <= x <= 1 - eps ->
           Rabs (ln (1 + x)) <= - ln (1 - Rabs x) + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x 3).
Qed.

(* plot(abs(x)/(1 + abs(x)) - abs(log(1+x)), [-1, 1]); *)
Lemma MT3 :
  forall x : R, -1 + eps <= x <= 1 ->
           Rabs x / (1 + Rabs x) <= Rabs (ln (1 + x)) + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_diff x).
Qed.

(* plot(abs(log(1+x)) - abs(x)*(1+abs(x))/abs(1+x), [-1, 10]); *)
Lemma MT4 :
  forall x : R, -1 + eps <= x <= 1 ->
                Rabs (ln (1 + x)) <= (Rabs x) * (1 + Rabs x) / Rabs (1 + x) + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_diff x).
Qed.

(* plot(abs(x) / 4 - abs(exp(x) - 1), [-1, 1]); *)
Lemma MT5 :
  forall x : R, (-1 <= x <= meps \/ eps <= x <= 1) ->
           Rabs x / 4 < Rabs (exp x - 1).
Proof.
Time intros x [H|H]; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* plot(abs(exp(x) - 1) - 7 * abs(x)/4, [0, 1]); *)
Lemma MT6 :
  forall x : R, (-1 <= x <= meps \/ eps <= x <= 1) ->
                Rabs (exp x - 1) < 7 * (Rabs x) / 4.
Proof.
Time intros x [H|H]; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* plot(abs(exp(x) - 1) - (exp(abs(x)) - 1), [-10, 10]); *)
Lemma MT7 : forall x : R, -10 <= x <= meps -> Rabs (exp x - 1) <= exp (Rabs x) - 1.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_diff x).
Qed.

(* plot(abs(exp(x)-(1+x)) - abs(exp(abs(x))-(1+abs(x))), [-10, 10]); *)
Lemma MT8 :
  forall x : R, -10 <= x <= meps ->
  Rabs (exp x - (1 + x)) <= Rabs (exp (Rabs x) - (1 + Rabs x)).
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x 2, i_prec 40).
Qed.

(* plot(abs(exp(x)-(1+x/2)^2) - abs(exp(abs(x))-(1+abs(x)/2)^2), [-10, 10]); *)
Lemma MT9 :
  forall x : R, -10 <= x <= meps ->
  Rabs (exp x - (1 + x / 2) ^ 2) <= Rabs (exp (Rabs x) - (1 + (Rabs x) / 2) ^ 2).
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x 3, i_prec 40).
Qed.

(* plot(2*x/(2+x) - log(1+x), [0, 10]); *)
Lemma MT10 :
  forall x : R, 0 <= x <= 10 -> 2 * x / (2 + x) <= ln (1 + x) + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x 3).
Qed.

(* plot(x/sqrt(1+x) - log(1+x), [-1/3,0]); *)
Lemma MT11 :
  forall x : R, -1/3 <= x <= 0 -> x / sqrt (1 + x) <= ln (1 + x) + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x 3, i_prec 40).
Qed.

(* plot(log((1+x)/x)-(12*x^2 + 12*x + 1)/(12*x^3 + 18*x^2 + 6*x), [1/3, 10]); *)
Lemma MT12 :
  forall x : R, 1/3 <= x <= 10 ->
  ln ((1 + x) / x) <= (12*x^2 + 12*x + 1) / (12*x^3 + 18*x^2 + 6*x).
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x 3).
Qed.

(* plot(log((1+x)/x)-1/sqrt(x^2 + x), [1/3, 10]); *)
Lemma MT13 :
  forall x : R, 1/3 <= x <= 10 ->
  ln ((1 + x) / x) <= 1 / sqrt (x ^ 2 + x).
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x 3, i_prec 40).
Qed.

(* plot(exp(x - x^2) - 1 - x, [0, 1]); *)
Lemma MT14 : forall x : R, 0 <= x <= 1 -> exp (x - x^2) <= 1 + x + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_diff x).
Qed.

(* plot(exp(-x/(1-x))-(1-x), [-10,1/2]); *)
Lemma MT15 : forall x : R, -10 <= x <= 1/2 -> exp(-x/(1 - x)) <= 1 - x + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_diff x).
Qed.

(* plot(abs(sin(x)) - 6/5 * abs(x), [-1, 1]); *)
Lemma MT16 : forall x : R, -1 <= x <= 1 -> Rabs (sin x) <= 6/5 * Rabs x + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_diff x).
Qed.

(* plot(1 - 2 * x - cos(pi * x), [0, 1/2]); *)
Lemma MT17 : forall x : R, eps <= x <= 100/201 -> cos (PI * x) > 1 - 2 * x.
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* plot(cos(x) - 1 + x^2/2, [-10,10]); *)
Lemma MT18 : forall x : R, -10 <= x <= 10 -> cos x - 1 + x^2 / 2 + eps >= 0.
Proof.
Time intros x H; apply Rminus_ge; interval with (i_bisect_taylor x 2).
Qed.

(* plot(8 * sqrt(3) * x / (3 * sqrt(3) + sqrt(75 + 80 * x^2)) - atan(x), [0, 10]); *)
Lemma MT19 :
  forall x : R, 0 <= x <= 10 ->
  eps + atan x >= 8 * sqrt 3 * x / (3 * sqrt 3 + sqrt (75 + 80 * x^2)).
Proof.
Time intros x H; apply Rminus_ge; interval with (i_bisect_diff x).
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
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* foire en flottant primitifs *)
(* plot(cos(x)-sin(x)/x, [0, pi]); *)
(* Lemma MT22 : forall x : R, eps <= x <= PI -> cos x <= sin x / x. *)
(* Proof. *)
(* Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x 5, i_depth 16). *)
(* Qed. *)

(* plot(cos(x) - (sin(x)/x)^2, [0, pi/2]); *)
Lemma MT23 : forall x : R, eps <= x <= PI / 2 -> cos x < (sin x / x) ^ 2.
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_taylor x 5).
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

(* From bench-ineqs/benchmarks/coq/univ_transcend.v *)

(** http://lipforge.ens-lyon.fr/www/crlibm/ *)
(** http://lipforge.ens-lyon.fr/frs/download.php/162/crlibm-1.0beta4.tar.gz *)

Section CRlibm_exp.
Let p_2_55 : R := 36028797018963968.
Let c3 := 6004799504235417 / p_2_55.
Let c4 := 1501199876148417 / p_2_55.
Notation p x := (x + 1/2 * x^2 + c3 * x^3 + c4 * x^4)%R (only parsing).
Notation eps' := (1/1048576)%R (only parsing).
Notation meps' := (-1/1048576)%R (only parsing).

(* foire : normal vu la précision *)
(* Lemma crlibm_exp : *)
(*   forall x : R, *)
(*   (-355/4194304 <= x <= meps') \/ (eps' <= x <= 355/4194304) -> *)
(*   Rabs ((p x - exp x + 1) / (exp x - 1)) <= 1/4611686018427387904. *)
(* Time intros x [H|H]; unfold c3, c4, p_2_55; *)
(*   interval with (i_bisect_taylor x, i_prec 90). *)
(* Qed. *)
End CRlibm_exp.

(** Melquiond_IJCAR2008 paper *)

(* plot(abs(sqrt(x) - (((((122 / 7397 * x + (-1733) / 13547) * x
  + 529 / 1274) * x + (-767) / 999) * x
  + 407 / 334) * x + 227 / 925)) - 5/65536, [1/2, 2]); *)
Lemma remez_sqrt :
  forall x, 1/2 <= x <= 2 ->
  Rabs (sqrt x - (((((122 / 7397 * x + (-1733) / 13547) * x
                   + 529 / 1274) * x + (-767) / 999) * x
                   + 407 / 334) * x + 227 / 925))
    <= 5/65536.
Time intros x H;
  (* interval with (i_bisect_diff x). *)
  interval with (i_bisect_taylor x 5).
Qed.

(** Daumas_Lester_Munoz_TC2009 paper with a tighter bound *)

(* plot(abs(atan(x)-(x-(11184811/33554432)*x^3-(13421773/67108864)*x^5))-5/2^28, [-1/30, 1/30]); *)
Lemma abs_err_atan :
  forall x : R, -1/30 <= x <= 1/30 ->
  Rabs (atan x - (x - (11184811/33554432) * x^3 - (13421773/67108864) * x^5))
  <= 5/268435456.
Time intros x H;
  interval with (i_bisect_diff x).
Qed.

(** Daumas_Melquiond_Munoz_ARITH2005 paper *)

Section Rel_err_geodesic.
Let a := 6378137.
Let f := 1000000000/298257223563.
Let umf2 := (1 - f) ^ 2.
Let max := 715/512.
Notation rp phi := (a / sqrt (1 + umf2 * (tan phi) ^ 2)) (only parsing).
Notation arp phi :=
  (let: x := max ^ 2 - phi ^ 2 in
  4439091/4 + x * (9023647/4 + x * (
    13868737/64 + x * (13233647/2048 + x * (
      -1898597/16384 + x * (-6661427/131072)))))) (only parsing).

Lemma rel_err_geodesic :
  forall phi, 0 <= phi <= max ->
  Rabs ((rp phi - arp phi) / rp phi) <= 23/16777216.
Proof.
Time unfold (*rp, arp,*) a, umf2, f, max; intros phi Hphi;
(* interval with (i_bisect_diff phi). *)
  interval with (i_bisect_taylor phi 5).
Qed.
End Rel_err_geodesic.

(** Harrison_TPHOLs1997 paper *)

(* plot(abs((exp(x)-1)-(x+(8388676/2^24)*x^2+(11184876/2^26)*x^3))-((23/27)/(2^33)), [-10831/1000000, 10831/1000000]); *)
Lemma harrison97 :
  forall x : R,
  (-10831/1000000 <= x <= 10831/1000000) ->
  Rabs ((exp x - 1) - (x + (8388676/2^24) * x^2 + (11184876/2^26) * x^3))
  <= ((23/27) / (2^33)).
Time intros x H;
  interval with (i_bisect_taylor x 3, i_prec 50).
Qed.

(* From bench-ineqs/benchmarks/coq/univ_metitarski_Rlt.v *)

(** MetiTarski_JAR2010 paper *)

(* plot(abs(sin(x)) - 6/5 * abs(x), [-1, 1]); *)
Lemma MT16__1 : forall x : R, (-1 <= x <= 0) -> (sin x) > - (6/5 * - x + eps).
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

Lemma MT16__2 : forall x : R, (-1 <= x <= 0) -> (sin x) < 6/5 * - x + eps.
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

Lemma MT16__3 : forall x : R, (0 <= x <= 1) -> (sin x) > - (6/5 * x + eps).
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

Lemma MT16__4 : forall x : R, (0 <= x <= 1) -> (sin x) < 6/5 * x + eps.
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* plot(1 - 2 * x - cos(pi * x), [0, 1/2]); *)
Lemma MT17' : forall x : R, eps <= x <= 100/201 -> cos (PI * x) > 1 - 2 * x.
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* plot(cos(x) - 1 + x^2/2, [-10,10]); *)
Lemma MT18' : forall x : R, -10 <= x <= 10 -> cos x - 1 + x^2 / 2 + eps > 0.
Proof.
Time intros x H; interval with (i_bisect_taylor x 2).
Qed.

(* plot(8 * sqrt(3) * x / (3 * sqrt(3) + sqrt(75 + 80 * x^2)) - atan(x), [0, 10]); *)
Lemma MT19' :
  forall x : R, 0 <= x <= 10 ->
  eps + atan x > 8 * sqrt 3 * x / (3 * sqrt 3 + sqrt (75 + 80 * x^2)).
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* plot((x + 1/x) * arctan(x) - 1, [0,5]); *)
Lemma MT20' : forall x : R, eps <= x <= 10 -> (x + 1 / x) * atan x > 1.
Proof.
Time intros x H; interval with (i_bisect_diff x, i_depth 25).
Qed.

(* plot(3 * x / (1 + 2 * sqrt(1 + x^2)) - atan(x), [0, 10]); *)
Lemma MT21' :
  forall x : R, 0 <= x <= 10 -> eps + atan x > 3 * x / (1 + 2 * sqrt (1 + x^2)).
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* foire en flottants primitifs *)
(* plot(cos(x)-sin(x)/x, [0, pi]); *)
(* Lemma MT22' : forall x : R, eps <= x <= PI -> cos x < sin x / x. *)
(* Time intros x H; apply Rminus_lt; interval with (i_bisect_taylor x 5, i_depth 16). *)
(* Qed. *)

(* plot(cos(x) - (sin(x)/x)^2, [0, pi/2]); *)
Lemma MT23' : forall x : R, eps <= x <= PI / 2 ->
  cos x < (sin x / x) * (sin x / x).
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_taylor x 5).
Qed.

(* plot(sin(x)/3 + sin(3*x)/6, [pi/3-1, 2*pi/3+1]); *)
Lemma MT24' :
  forall x : R, PI/3 <= x <= 2*PI/3 - eps -> (sin x) / 3 + (sin (3*x)) / 6 > 0.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* From bench-ineqs/benchmarks/coq/fpminmax.v *)

(** Facilities to parse negative powers and pre-compute powers of 2 *)
Notation "a * b ^(- n )" := (a / b ^ n)%R
  (at level 40, b at next level, only parsing) : R_scope.

(** FP minimax polynomials for cos(3/2 * cos(x)), generated using Sollya *)
Notation f x := (cos (3/2 * cos x)) (only parsing).
Notation D x := (-1 <= x <= 1/2) (only parsing).

(** Degree-2 *)
Notation p2 x := (5009597 * 2^(-26) + x * (-3452481 * 2^(-36) + x * (10948483 * 2^(-24)))) (only parsing).
Notation eps2 := (57 * 2^(-10)) (only parsing).

Lemma cos_cos_d2 :
  forall x, D x -> Rabs ((p2 x - f x) / f x) <= eps2.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(** Degree-3 *)
Notation p3 x := (9578005 * 2^(-27) + x * (-8411879 * 2^(-29) + x * (6079307 * 2^(-23) + x * (14167647 * 2^(-27))))) (only parsing).
Notation eps3 := (51 * 2^(-11)) (only parsing).

Lemma cos_cos_d3 :
  forall x, D x -> Rabs ((p3 x - f x) / f x) <= eps3.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(** Degree-4 *)
Notation p4 x := (2366509 * 2^(-25) + x * (10537089 * 2^(-34) + x * (1593929 * 2^(-21) + x * (-3609977 * 2^(-29) + x * (-609875 * 2^(-22)))))) (only parsing).
Notation eps4 := (51 * 2^(-14)) (only parsing).

Lemma cos_cos_d4 :
  forall x, D x -> Rabs ((p4 x - f x) / f x) <= eps4.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(** Degree-5 *)
Notation p5 x := (9491875 * 2^(-27) + x * (1388077 * 2^(-31) + x * (12575645 * 2^(-24) + x * (-3473267 * 2^(-28) + x * (-13477879 * 2^(-27) + x * (11406127 * 2^(-28))))))) (only parsing).
Notation eps5 := (3 * 2^(-12)) (only parsing).

Lemma cos_cos_d5 :
  forall x, D x -> Rabs ((p5 x - f x) / f x) <= eps5.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(** Degree-6 *)
Notation p6 x := (9492545 * 2^(-27) + x * (12716483 * 2^(-36) + x * (3142515 * 2^(-22) + x * (-8980587 * 2^(-31) + x * (-12736139 * 2^(-27) + x * (8061261 * 2^(-29) + x * (-13450525 * 2^(-29)))))))) (only parsing).
Notation eps6 := (17 * 2^(-16)) (only parsing).

Lemma cos_cos_d6 :
  forall x, D x -> Rabs ((p6 x - f x) / f x) <= eps6.
Proof.
Time intros x H; interval with (i_bisect_taylor x 3).
Qed.

(** Degree-7 *)
Notation p7 x := (4747227 * 2^(-26) + x * (5795109 * 2^(-37) + x * (784233 * 2^(-20) + x * (-6099871 * 2^(-32) + x * (-10729417 * 2^(-27) + x * (12242037 * 2^(-30) + x * (-8892053 * 2^(-27) + x * (-14339757 * 2^(-29))))))))) (only parsing).
Notation eps7 := (25 * 2^(-19)) (only parsing).

Lemma cos_cos_d7 :
  forall x, D x -> Rabs ((p7 x - f x) / f x) <= eps7.
Proof.
Time intros x H; interval with (i_bisect_taylor x 4).
Qed.

(** Degree-8 *)
Notation p8 x := (9494185 * 2^(-27) + x * (12149587 * 2^(-41) + x * (6275713 * 2^(-23) + x * (-14107149 * 2^(-36) + x * (-2763427 * 2^(-25) + x * (14503039 * 2^(-33) + x * (-530509 * 2^(-23) + x * (-8256955 * 2^(-31) + x * (3638503 * 2^(-28)))))))))) (only parsing).
Notation eps8 := (5 * 2^(-20)) (only parsing).

Lemma cos_cos_d8 :
  forall x, D x -> Rabs ((p8 x - f x) / f x) <= eps8.
Proof.
Time intros x H; interval with (i_bisect_taylor x 4).
Qed.

(* From bench-ineqs/benchmarks/coq/fpminmax.v *)

(** Facilities to parse negative powers and pre-compute powers of 2 *)
Notation "a * b ^(- n )" := (a / b ^ n)%R
  (at level 40, b at next level, only parsing) : R_scope.

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
