(* Deprecated file with minimal-working precision with BigZ/Int63 floats,
   which is kept for informative purpose only, because the corresponding
   timings are not intended to be optimal in any sense. *)

Require Import Reals Interval.Tactic.
Local Open Scope R_scope.

(* From bench-ineqs/benchmarks/coq/multi_poly.v *)

Optimize Heap.
Lemma RD : forall x1 x2 x3 : R, -5 <= x1 <= 5 -> -5 <= x2 <= 5 -> -5 <= x3 <= 5 -> -367126907/10000000 <= -x1 + 2*x2 - x3 - 835634534/1000000000 * x2 * (1 + x2).
idtac "RD".
Time intros x1 x2 x3 H1 H2 H3; interval with (i_prec 32, i_bisect x2).
Qed.

Optimize Heap.
Lemma adaptiveLV : forall x1 x2 x3 x4 : R,
    -2 <= x1 <= 2 -> -2 <= x2 <= 2 -> -2 <= x3 <= 2 -> -2 <= x4 <= 2 ->
    -20801/1000 <= x1*x2^2 + x1 * x3^2 + x1*x4^2 - 11/10 * x1 + 1.
idtac "adaptiveLV".
Time intros x1 x2 x3 x4 H1 H2 H3 H4; interval with (i_prec 13, i_bisect x1, i_autodiff x1).
Qed.

Optimize Heap.
Lemma butcher : forall x1 x2 x3 x4 x5 x6 : R,
    -1 <= x1 <= 0 -> -1/10 <= x2 <= 9/10 -> -1/10 <= x3 <= 1/2 ->
    -1 <= x4 <= -1/10 -> -1/10 <= x5 <= -5/100 -> -1/10 <= x6 <= -3/100 ->
    -144/100 <= x6 * x2^2 + x5 * x3 ^2 - x1 * x4^2 + x4^3 + x4^2 - x1/3 + 4*x4/3.
idtac "butcher".
Time intros x1 x2 x3 x4 x5 x6 H1 H2 H3 H4 H5 H6;
  interval with (i_prec 12, i_bisect x4, i_autodiff x4).
Qed.

Optimize Heap.
Lemma magnetism : forall x1 x2 x3 x4 x5 x6 x7 : R,
    -1 <= x1 <= 1 -> -1 <= x2 <= 1 -> -1 <= x3 <= 1 -> -1 <= x4 <= 1 ->
    -1 <= x5 <= 1 -> -1 <= x6 <= 1 -> -1 <= x7 <= 1 ->
    -25001/100000 <= x1^2 + 2*x2^2 + 2*x3^2 + 2*x4^2 + 2*x5^2 + 2*x6^2 + 2*x7^2 - x1.
idtac "magnetism".
Time intros x1 x2 x3 x4 x5 x6 x7 H1 H2 H3 H4 H5 H6 H7;
interval with (i_prec 1, i_bisect x1, i_autodiff x1).
Qed.

(* From bench-ineqs/benchmarks/coq/univ_metitarski.v *)

Notation eps := (1/1024)%R (only parsing).
Notation meps := (-1/1024)%R (only parsing).

(** MetiTarski_JAR2010 paper *)

(* plot(2 * abs(x) / (2 + x) - abs(log(1+x)), [-1, 10]); *)
Optimize Heap.
Lemma MT1 :
  forall x : R, -1 + eps <= x <= 10 ->
           2 * Rabs x / (2 + x) <= Rabs (ln (1 + x)) + eps.
Proof.
idtac "MT1".
Time intros x H; apply Rminus_le; interval with (i_prec 17, i_bisect x).
Qed.

(* plot(abs(log(1+x)) + log(1 - abs(x)), [-1, 1]); *)
Optimize Heap.
Lemma MT2 :
  forall x : R, -1 + eps <= x <= 1 - eps ->
           Rabs (ln (1 + x)) <= - ln (1 - Rabs x) + eps.
Proof.
idtac "MT2".
Time intros x H; apply Rminus_le; interval with (i_prec 16, i_bisect x, i_taylor x).
Qed.

(* plot(abs(x)/(1 + abs(x)) - abs(log(1+x)), [-1, 1]); *)
Optimize Heap.
Lemma MT3 :
  forall x : R, -1 + eps <= x <= 1 ->
           Rabs x / (1 + Rabs x) <= Rabs (ln (1 + x)) + eps.
Proof.
idtac "MT3".
Time intros x H; apply Rminus_le; interval with (i_prec 12, i_bisect x).
Qed.

(* plot(abs(log(1+x)) - abs(x)*(1+abs(x))/abs(1+x), [-1, 10]); *)
Optimize Heap.
Lemma MT4 :
  forall x : R, -1 + eps <= x <= 1 ->
                Rabs (ln (1 + x)) <= (Rabs x) * (1 + Rabs x) / Rabs (1 + x) + eps.
Proof.
idtac "MT4".
Time intros x H; apply Rminus_le; interval with (i_prec 12, i_bisect x).
Qed.

(* plot(abs(x) / 4 - abs(exp(x) - 1), [-1, 1]); *)
Optimize Heap.
Lemma MT5 :
  forall x : R, (-1 <= x <= meps \/ eps <= x <= 1) ->
           Rabs x / 4 < Rabs (exp x - 1).
Proof.
idtac "MT5".
Time intros x [H|H]; apply Rminus_lt; interval with (i_prec 11, i_bisect x).
Qed.

(* plot(abs(exp(x) - 1) - 7 * abs(x)/4, [0, 1]); *)
Optimize Heap.
Lemma MT6 :
  forall x : R, (-1 <= x <= meps \/ eps <= x <= 1) ->
                Rabs (exp x - 1) < 7 * (Rabs x) / 4.
Proof.
idtac "MT6".
Time intros x [H|H]; apply Rminus_lt; interval with (i_prec 11, i_bisect x).
Qed.

(* plot(abs(exp(x) - 1) - (exp(abs(x)) - 1), [-10, 10]); *)
Optimize Heap.
Lemma MT7 : forall x : R, -10 <= x <= meps -> Rabs (exp x - 1) <= exp (Rabs x) - 1.
Proof.
idtac "MT7".
Time intros x H; apply Rminus_le; interval with (i_prec 19, i_bisect x, i_autodiff x).
Qed.

(* plot(abs(exp(x)-(1+x)) - abs(exp(abs(x))-(1+abs(x))), [-10, 10]); *)
Optimize Heap.
Lemma MT8 :
  forall x : R, -10 <= x <= meps ->
  Rabs (exp x - (1 + x)) <= Rabs (exp (Rabs x) - (1 + Rabs x)).
Proof.
idtac "MT8".
Time intros x H; apply Rminus_le; interval with (i_prec 35, i_bisect x, i_taylor x).
Qed.

(* plot(abs(exp(x)-(1+x/2)^2) - abs(exp(abs(x))-(1+abs(x)/2)^2), [-10, 10]); *)
Optimize Heap.
Lemma MT9 :
  forall x : R, -10 <= x <= meps ->
  Rabs (exp x - (1 + x / 2) ^ 2) <= Rabs (exp (Rabs x) - (1 + (Rabs x) / 2) ^ 2).
Proof.
idtac "MT9".
Time intros x H; apply Rminus_le; interval with (i_prec 35, i_bisect x, i_taylor x).
Qed.

(* plot(2*x/(2+x) - log(1+x), [0, 10]); *)
Optimize Heap.
Lemma MT10 :
  forall x : R, 0 <= x <= 10 -> 2 * x / (2 + x) <= ln (1 + x) + eps.
Proof.
idtac "MT10".
Time intros x H; apply Rminus_le; interval with (i_prec 15, i_bisect x).
Qed.

(* plot(x/sqrt(1+x) - log(1+x), [-1/3,0]); *)
Optimize Heap.
Lemma MT11 :
  forall x : R, -1/3 <= x <= 0 -> x / sqrt (1 + x) <= ln (1 + x) + eps.
Proof.
idtac "MT11".
Time intros x H; apply Rminus_le; interval with (i_prec 13, i_bisect x).
Qed.

(* plot(log((1+x)/x)-(12*x^2 + 12*x + 1)/(12*x^3 + 18*x^2 + 6*x), [1/3, 10]); *)
Optimize Heap.
Lemma MT12 :
  forall x : R, 1/3 <= x <= 10 ->
  ln ((1 + x) / x) <= (12*x^2 + 12*x + 1) / (12*x^3 + 18*x^2 + 6*x).
Proof.
idtac "MT12".
Time intros x H; apply Rminus_le; interval with (i_prec 28, i_bisect x, i_taylor x).
Qed.

(* plot(log((1+x)/x)-1/sqrt(x^2 + x), [1/3, 10]); *)
Optimize Heap.
Lemma MT13 :
  forall x : R, 1/3 <= x <= 10 ->
  ln ((1 + x) / x) <= 1 / sqrt (x ^ 2 + x).
Proof.
idtac "MT13".
Time intros x H; apply Rminus_le; interval with (i_prec 23, i_bisect x).
Qed.

(* plot(exp(x - x^2) - 1 - x, [0, 1]); *)
Optimize Heap.
Lemma MT14 : forall x : R, 0 <= x <= 1 -> exp (x - x^2) <= 1 + x + eps.
Proof.
idtac "MT14".
Time intros x H; apply Rminus_le; interval with (i_prec 11, i_bisect x, i_autodiff x).
Qed.

(* plot(exp(-x/(1-x))-(1-x), [-10,1/2]); *)
Optimize Heap.
Lemma MT15 : forall x : R, -10 <= x <= 1/2 -> exp(-x/(1 - x)) <= 1 - x + eps.
Proof.
idtac "MT15".
Time intros x H; apply Rminus_le; interval with (i_prec 11, i_bisect x, i_autodiff x).
Qed.

(* plot(abs(sin(x)) - 6/5 * abs(x), [-1, 1]); *)
Optimize Heap.
Lemma MT16 : forall x : R, -1 <= x <= 1 -> Rabs (sin x) <= 6/5 * Rabs x + eps.
Proof.
idtac "MT16".
Time intros x H; apply Rminus_le; interval with (i_prec 1, i_bisect x, i_autodiff x).
Qed.

(* plot(1 - 2 * x - cos(pi * x), [0, 1/2]); *)
Optimize Heap.
Lemma MT17 : forall x : R, eps <= x <= 100/201 -> cos (PI * x) > 1 - 2 * x.
Proof.
idtac "MT17".
Time intros x H; apply Rminus_lt; interval with (i_prec 11, i_bisect x).
Qed.

(* plot(cos(x) - 1 + x^2/2, [-10,10]); *)
Optimize Heap.
Lemma MT18 : forall x : R, -10 <= x <= 10 -> cos x - 1 + x^2 / 2 + eps >= 0.
Proof.
idtac "MT18".
Time intros x H; apply Rminus_ge; interval with (i_prec 12, i_bisect x).
Qed.

(* plot(8 * sqrt(3) * x / (3 * sqrt(3) + sqrt(75 + 80 * x^2)) - atan(x), [0, 10]); *)
Optimize Heap.
Lemma MT19 :
  forall x : R, 0 <= x <= 10 ->
  eps + atan x >= 8 * sqrt 3 * x / (3 * sqrt 3 + sqrt (75 + 80 * x^2)).
Proof.
idtac "MT19".
Time intros x H; apply Rminus_ge; interval with (i_prec 12, i_bisect x, i_autodiff x).
Qed.

(* plot((x + 1/x) * arctan(x) - 1, [0,5]); *)
Optimize Heap.
Lemma MT20 : forall x : R, eps <= x <= 10 -> (x + 1 / x) * atan x > 1.
Proof.
idtac "MT20".
Time intros x H; interval with (i_prec 25, i_bisect x, i_autodiff x, i_depth 25).
Qed.

(* TODO: try to remove Rminus_alt etc. *)
(* plot(3 * x / (1 + 2 * sqrt(1 + x^2)) - atan(x), [0, 10]); *)
Optimize Heap.
Lemma MT21 :
  forall x : R, 0 <= x <= 10 -> eps + atan x > 3 * x / (1 + 2 * sqrt (1 + x^2)).
Proof.
idtac "MT21".
Time intros x H; apply Rminus_lt; interval with (i_prec 11, i_bisect x, i_autodiff x).
Qed.

(* plot(cos(x)-sin(x)/x, [0, pi]); *)
(* TODO Plot *)
Optimize Heap.
Lemma MT22 : forall x : R, eps <= x <= PI -> cos x <= sin x / x.
Proof.
idtac "MT22".
Time intros x H; apply Rminus_le; interval with (i_prec 27, i_bisect x, i_taylor x, i_depth 16).
Qed.

(* plot(cos(x) - (sin(x)/x)^2, [0, pi/2]); *)
Optimize Heap.
Lemma MT23 : forall x : R, eps <= x <= PI / 2 -> cos x < (sin x / x) ^ 2.
Proof.
idtac "MT23".
Time intros x H; apply Rminus_lt; interval with (i_prec 29, i_bisect x, i_taylor x).
Qed.

(* plot(sin(x)/3 + sin(3*x)/6, [pi/3-1, 2*pi/3+1]); *)
Optimize Heap.
Lemma MT24 :
  forall x : R, PI/3 <= x <= 2*PI/3 - eps -> (sin x) / 3 + (sin (3*x)) / 6 > 0.
Proof.
idtac "MT24".
Time intros x H; interval with (i_prec 3, i_bisect x).
Qed.

(* plot(12-14.2*exp(-.318*x)+(3.25*cos(1.16*x)-.155*sin(1.16*x))*exp(-1.34*x),[-1/2,2]); *)
Optimize Heap.
Lemma MT25 :
  forall x : R, 0 <= x <= 2 ->
  12 - 142/10 * exp(-318/1000*x) + (325/100*cos(116/100*x) - 155/1000*sin(116/100*x)) * exp(-134/100*x) > 0.
Proof.
idtac "MT25".
Time intros x H; interval with (i_prec 6, i_bisect x).
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

(* TODO: try to remove the unfold here *)
Optimize Heap.
Lemma crlibm_exp :
  forall x : R,
  (-355/4194304 <= x <= meps') \/ (eps' <= x <= 355/4194304) ->
  Rabs ((p x - exp x + 1) / (exp x - 1)) <= 1/4611686018427387904.
idtac "crlibm_exp".
Time intros x [H|H]; unfold c3, c4, p_2_55;
  interval with (i_bisect x, i_taylor x, i_prec 90). (* NOT i_prec 53 *)
Qed.
End CRlibm_exp.

(** Melquiond_IJCAR2008 paper *)

(* plot(abs(sqrt(x) - (((((122 / 7397 * x + (-1733) / 13547) * x
  + 529 / 1274) * x + (-767) / 999) * x
  + 407 / 334) * x + 227 / 925)) - 5/65536, [1/2, 2]); *)
Optimize Heap.
Lemma remez_sqrt :
  forall x, 1/2 <= x <= 2 ->
  Rabs (sqrt x - (((((122 / 7397 * x + (-1733) / 13547) * x
                   + 529 / 1274) * x + (-767) / 999) * x
                   + 407 / 334) * x + 227 / 925))
    <= 5/65536.
idtac "remez_sqrt".
Time intros x H;
  (* interval with (i_prec 53, i_bisect x, i_autodiff x). OK but slower *)
  interval with (i_prec 22, i_bisect x, i_taylor x).
Qed.

(** Daumas_Lester_Munoz_TC2009 paper with a tighter bound *)

(* plot(abs(atan(x)-(x-(11184811/33554432)*x^3-(13421773/67108864)*x^5))-5/2^28, [-1/30, 1/30]); *)
Optimize Heap.
Lemma abs_err_atan :
  forall x : R, -1/30 <= x <= 1/30 ->
  Rabs (atan x - (x - (11184811/33554432) * x^3 - (13421773/67108864) * x^5))
  <= 5/268435456.
idtac "abs_err_atan".
Time intros x H;
  interval with (i_prec 26, i_bisect x, i_autodiff x).
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

Optimize Heap.
Lemma rel_err_geodesic :
  forall phi, 0 <= phi <= max ->
  Rabs ((rp phi - arp phi) / rp phi) <= 23/16777216.
Proof.
idtac "rel_err_geodesic".
Time unfold (*rp, arp,*) a, umf2, f, max; intros phi Hphi;
  interval with (i_prec 24, i_bisect phi, i_autodiff phi).
Qed.

Optimize Heap.
Lemma rel_err_geodesic' :
  forall phi, 0 <= phi <= max ->
  Rabs ((rp phi - arp phi) / rp phi) <= 23/16777216.
Proof.
idtac "rel_err_geodesic'".
Time unfold (*rp, arp,*) a, umf2, f, max; intros phi Hphi;
  interval with (i_prec 25, i_bisect phi, i_taylor phi).
Qed.
End Rel_err_geodesic.

(* From bench-ineqs/benchmarks/coq/univ_metitarski_Rlt.v *)

(** MetiTarski_JAR2010 paper *)

(* TODO Maybe merge lemmas if there's too many lines in the array *)
(* plot(abs(sin(x)) - 6/5 * abs(x), [-1, 1]); *)
Optimize Heap.
Lemma MT16__1 : forall x : R, (-1 <= x <= 0) -> (sin x) > - (6/5 * - x + eps).
Proof.
idtac "MT16__1".
Time intros x H; apply Rminus_lt; interval with (i_prec 1, i_bisect x, i_autodiff x).
Qed.

Optimize Heap.
Lemma MT16__2 : forall x : R, (-1 <= x <= 0) -> (sin x) < 6/5 * - x + eps.
Proof.
idtac "MT16__2".
Time intros x H; apply Rminus_lt; interval with (i_prec 1, i_bisect x).
Qed.

Optimize Heap.
Lemma MT16__3 : forall x : R, (0 <= x <= 1) -> (sin x) > - (6/5 * x + eps).
Proof.
idtac "MT16__3".
Time intros x H; apply Rminus_lt; interval with (i_prec 1, i_bisect x).
Qed.

Optimize Heap.
Lemma MT16__4 : forall x : R, (0 <= x <= 1) -> (sin x) < 6/5 * x + eps.
Proof.
idtac "MT16__4".
Time intros x H; apply Rminus_lt; interval with (i_prec 1, i_bisect x, i_autodiff x).
Qed.

(* plot(1 - 2 * x - cos(pi * x), [0, 1/2]); *)
Optimize Heap.
Lemma MT17' : forall x : R, eps <= x <= 100/201 -> cos (PI * x) > 1 - 2 * x.
Proof.
idtac "MT17'".
Time intros x H; apply Rminus_lt; interval with (i_prec 11, i_bisect x).
Qed.

(* plot(cos(x) - 1 + x^2/2, [-10,10]); *)
Optimize Heap.
Lemma MT18' : forall x : R, -10 <= x <= 10 -> cos x - 1 + x^2 / 2 + eps > 0.
Proof.
idtac "MT18'".
Time intros x H; interval with (i_prec 12, i_bisect x).
Qed.

(* plot(8 * sqrt(3) * x / (3 * sqrt(3) + sqrt(75 + 80 * x^2)) - atan(x), [0, 10]); *)
Optimize Heap.
Lemma MT19' :
  forall x : R, 0 <= x <= 10 ->
  eps + atan x > 8 * sqrt 3 * x / (3 * sqrt 3 + sqrt (75 + 80 * x^2)).
Proof.
idtac "MT19'".
Time intros x H; apply Rminus_lt; interval with (i_prec 12, i_bisect x, i_autodiff x).
Qed.

(* plot((x + 1/x) * arctan(x) - 1, [0,5]); *)
Optimize Heap.
Lemma MT20' : forall x : R, eps <= x <= 10 -> (x + 1 / x) * atan x > 1.
Proof.
idtac "MT20'".
Time intros x H; interval with (i_prec 25, i_bisect x, i_autodiff x, i_depth 25).
Qed.

(* plot(3 * x / (1 + 2 * sqrt(1 + x^2)) - atan(x), [0, 10]); *)
Optimize Heap.
Lemma MT21' :
  forall x : R, 0 <= x <= 10 -> eps + atan x > 3 * x / (1 + 2 * sqrt (1 + x^2)).
Proof.
idtac "MT21'".
Time intros x H; apply Rminus_lt; interval with (i_prec 11, i_bisect x, i_autodiff x).
Qed.

(* OK en flottants primitifs *)
(* plot(cos(x)-sin(x)/x, [0, pi]); *)
Optimize Heap.
Lemma MT22' : forall x : R, eps <= x <= PI -> cos x < sin x / x.
idtac "MT22'".
Time intros x H; apply Rminus_lt; interval with (i_prec 27, i_bisect x, i_taylor x, i_depth 16).
Qed.

(* plot(cos(x) - (sin(x)/x)^2, [0, pi/2]); *)
Optimize Heap.
Lemma MT23' : forall x : R, eps <= x <= PI / 2 ->
  cos x < (sin x / x) * (sin x / x).
Proof.
idtac "MT23'".
Time intros x H; apply Rminus_lt; interval with (i_prec 29, i_bisect x, i_taylor x).
Qed.

(* plot(sin(x)/3 + sin(3*x)/6, [pi/3-1, 2*pi/3+1]); *)
Optimize Heap.
Lemma MT24' :
  forall x : R, PI/3 <= x <= 2*PI/3 - eps -> (sin x) / 3 + (sin (3*x)) / 6 > 0.
Proof.
idtac "MT24'".
Time intros x H; interval with (i_prec 3, i_bisect x).
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

Optimize Heap.
Lemma cos_cos_d2 :
  forall x, D x -> Rabs ((p2 x - f x) / f x) <= eps2.
Proof.
idtac "cos_cos_d2".
Time intros x H; interval with (i_prec 17, i_bisect x, i_taylor x).
Qed.

(** Degree-3 *)
Notation p3 x := (9578005 * 2^(-27) + x * (-8411879 * 2^(-29) + x * (6079307 * 2^(-23) + x * (14167647 * 2^(-27))))) (only parsing).
Notation eps3 := (51 * 2^(-11)) (only parsing).

Optimize Heap.
Lemma cos_cos_d3 :
  forall x, D x -> Rabs ((p3 x - f x) / f x) <= eps3.
Proof.
idtac "cos_cos_d3".
Time intros x H; interval with (i_prec 20, i_bisect x, i_taylor x).
Qed.

(** Degree-4 *)
Notation p4 x := (2366509 * 2^(-25) + x * (10537089 * 2^(-34) + x * (1593929 * 2^(-21) + x * (-3609977 * 2^(-29) + x * (-609875 * 2^(-22)))))) (only parsing).
Notation eps4 := (51 * 2^(-14)) (only parsing).

Optimize Heap.
Lemma cos_cos_d4 :
  forall x, D x -> Rabs ((p4 x - f x) / f x) <= eps4.
Proof.
idtac "cos_cos_d4".
Time intros x H; interval with (i_prec 22, i_bisect x, i_taylor x).
Qed.

(** Degree-5 *)
Notation p5 x := (9491875 * 2^(-27) + x * (1388077 * 2^(-31) + x * (12575645 * 2^(-24) + x * (-3473267 * 2^(-28) + x * (-13477879 * 2^(-27) + x * (11406127 * 2^(-28))))))) (only parsing).
Notation eps5 := (3 * 2^(-12)) (only parsing).

Optimize Heap.
Lemma cos_cos_d5 :
  forall x, D x -> Rabs ((p5 x - f x) / f x) <= eps5.
Proof.
idtac "cos_cos_d5".
Time intros x H; interval with (i_prec 24, i_bisect x, i_taylor x).
Qed.

(** Degree-6 *)
Notation p6 x := (9492545 * 2^(-27) + x * (12716483 * 2^(-36) + x * (3142515 * 2^(-22) + x * (-8980587 * 2^(-31) + x * (-12736139 * 2^(-27) + x * (8061261 * 2^(-29) + x * (-13450525 * 2^(-29)))))))) (only parsing).
Notation eps6 := (17 * 2^(-16)) (only parsing).

Optimize Heap.
Lemma cos_cos_d6 :
  forall x, D x -> Rabs ((p6 x - f x) / f x) <= eps6.
Proof.
idtac "cos_cos_d6".
Time intros x H; interval with (i_prec 24, i_bisect x, i_taylor x).
Qed.

(** Degree-7 *)
Notation p7 x := (4747227 * 2^(-26) + x * (5795109 * 2^(-37) + x * (784233 * 2^(-20) + x * (-6099871 * 2^(-32) + x * (-10729417 * 2^(-27) + x * (12242037 * 2^(-30) + x * (-8892053 * 2^(-27) + x * (-14339757 * 2^(-29))))))))) (only parsing).
Notation eps7 := (25 * 2^(-19)) (only parsing).

Optimize Heap.
Lemma cos_cos_d7 :
  forall x, D x -> Rabs ((p7 x - f x) / f x) <= eps7.
Proof.
idtac "cos_cos_d7".
Time intros x H; interval with (i_prec 27, i_bisect x, i_taylor x).
Qed.

(** Degree-8 *)
Notation p8 x := (9494185 * 2^(-27) + x * (12149587 * 2^(-41) + x * (6275713 * 2^(-23) + x * (-14107149 * 2^(-36) + x * (-2763427 * 2^(-25) + x * (14503039 * 2^(-33) + x * (-530509 * 2^(-23) + x * (-8256955 * 2^(-31) + x * (3638503 * 2^(-28)))))))))) (only parsing).
Notation eps8 := (5 * 2^(-20)) (only parsing).

Optimize Heap.
Lemma cos_cos_d8 :
  forall x, D x -> Rabs ((p8 x - f x) / f x) <= eps8.
Proof.
idtac "cos_cos_d8".
Time intros x H; interval with (i_prec 30, i_bisect x, i_taylor x).
Qed.

(* From bench-ineqs/benchmarks/coq/fpminmax.v *)

(** Facilities to parse negative powers and pre-compute powers of 2 *)
Notation "a * b ^(- n )" := (a / b ^ n)%R
  (at level 40, b at next level, only parsing) : R_scope.

Optimize Heap.
Lemma cos_cos_d2__1 :
  forall x, D x -> (p2 x - f x) / f x > - eps2.
Proof.
idtac "cos_cos_d2__1".
Time intros x H; interval with (i_prec 16, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d2__2 :
  forall x, D x -> (p2 x - f x) / f x < eps2.
Proof.
idtac "cos_cos_d2__2".
Time intros x H; interval with (i_prec 17, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d3__1 :
  forall x, D x -> (p3 x - f x) / f x > - eps3.
Proof.
idtac "cos_cos_d3__1".
Time intros x H; interval with (i_prec 18, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d3__2 :
  forall x, D x -> (p3 x - f x) / f x < eps3.
Proof.
idtac "cos_cos_d3__2".
Time intros x H; interval with (i_prec 20, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d4__1 :
  forall x, D x -> (p4 x - f x) / f x > - eps4.
Proof.
idtac "cos_cos_d4__1".
Time intros x H; interval with (i_prec 22, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d4__2 :
  forall x, D x -> (p4 x - f x) / f x < eps4.
Proof.
idtac "cos_cos_d4__2".
Time intros x H; interval with (i_prec 20, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d5__1 :
  forall x, D x -> (p5 x - f x) / f x > - eps5.
Proof.
idtac "cos_cos_d5__1".
Time intros x H; interval with (i_prec 23, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d5__2 :
  forall x, D x -> (p5 x - f x) / f x < eps5.
Proof.
idtac "cos_cos_d5__2".
Time intros x H; interval with (i_prec 24, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d6__1 :
  forall x, D x -> (p6 x - f x) / f x > - eps6.
Proof.
idtac "cos_cos_d6__1".
Time intros x H; interval with (i_prec 23, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d6__2 :
  forall x, D x -> (p6 x - f x) / f x < eps6.
Proof.
idtac "cos_cos_d6__2".
Time intros x H; interval with (i_prec 24, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d7__1 :
  forall x, D x -> (p7 x - f x) / f x > - eps7.
Proof.
idtac "cos_cos_d7__1".
Time intros x H; interval with (i_prec 27, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d7__2 :
  forall x, D x -> (p7 x - f x) / f x < eps7.
Proof.
idtac "cos_cos_d7__2".
Time intros x H; interval with (i_prec 27, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d8__1 :
  forall x, D x -> (p8 x - f x) / f x > - eps8.
Proof.
idtac "cos_cos_d8__1".
Time intros x H; interval with (i_prec 30, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma cos_cos_d8__2 :
  forall x, D x -> (p8 x - f x) / f x < eps8.
Proof.
idtac "cos_cos_d8__2".
Time intros x H; interval with (i_prec 30, i_bisect x, i_taylor x).
Qed.

(* From coq-interval/testsuite/bug-20120927.v *)

(* TODO: Remove these lemmas from the "optimal prec" column *)
Optimize Heap.
Lemma bug20120927 :
  forall x, (-1/2 <= x <= 0)%R ->
  True.
Proof.
intros x Hx.
idtac "bug20120927".
Time interval_intro (Rabs x + x)%R upper with (i_prec 53, i_bisect x, i_autodiff x, i_depth 5).
exact I.
Qed.

(* From coq-interval/testsuite/bug-20140723.v *)

Optimize Heap.
Lemma bug20140723_1 : True.
idtac "bug20140723_1".
Time interval_intro PI lower with (i_prec 53).
exact I.
Qed.

Optimize Heap.
Lemma bug20140723_2 : True.
idtac "bug20140723_2".
Time interval_intro (PI/2)%R upper with (i_prec 53).
exact I.
Qed.

(* From coq-interval/testsuite/bug-20140728.v *)

Optimize Heap.
Lemma bug20140728 : forall x : R, exp x >= 0.
idtac "bug20140728".
Time intros; interval with (i_prec 1).
Qed.

(* OK with emulated floats *)

(* From coq-interval/testsuite/bug-20150924.v *)

Optimize Heap.
Lemma bug20150924 : forall x : R,
  (Rabs (x - x) <= 1/5)%R.
Proof.
intros x.
idtac "bug20150924".
Time interval with (i_prec 1, i_autodiff x).
Qed.

(* From coq-interval/testsuite/bug-20150925.v *)

Optimize Heap.
Lemma bug20150925 : forall x, (-1 / 3 <= x - x <= 1 / 7)%R.
Proof.
intros x.
idtac "bug20150925".
Time interval with (i_prec 1, i_autodiff x).
Qed.
*

(* From coq-interval/testsuite/example_20071016.v *)

Optimize Heap.
Lemma example20071016_1 :
  forall x, -1 <= x <= 1 ->
  sqrt (1 - x) <= 3/2.
Proof.
  intros.
idtac "example20071016_1".
  Time interval with (i_prec 2).
Qed.

Optimize Heap.
Lemma example20071016_2 :
  forall x, -1 <= x <= 1 ->
  sqrt (1 - x) <= 141422/100000.
Proof.
  intros.
idtac "example20071016_2".
  Time interval with (i_prec 16).
Qed.

Optimize Heap.
Lemma example20071016_3 :
  forall x, -1 <= x <= 1 ->
  sqrt (1 - x) <= 141422/100000.
Proof.
  intros.
idtac "example20071016_3".
  Time interval_intro (sqrt (1 - x)) upper with (i_prec 53) as H'.
  apply Rle_trans with (1 := H').
idtac "example20071016_3'".
  Time interval with (i_prec 16).
Qed.

Optimize Heap.
Lemma example20071016_4 :
  forall x, 3/2 <= x <= 2 ->
  forall y, 1 <= y <= 33/32 ->
  Rabs (sqrt(1 + x/sqrt(x+y)) - 144/1000*x - 118/100) <= 71/32768.
Proof.
  intros.
idtac "example20071016_4".
  Time interval with (i_prec 19, i_bisect x).
Qed.

Optimize Heap.
Lemma example20071016_5 :
  forall x, 1/2 <= x <= 2 ->
  Rabs (sqrt x - (((((122 / 7397 * x + (-1733) / 13547) * x
                   + 529 / 1274) * x + (-767) / 999) * x
                   + 407 / 334) * x + 227 / 925))
    <= 5/65536.
Proof.
  intros.
idtac "example20071016_5".
  Time interval with (i_prec 22, i_bisect x, i_taylor x).
Qed.

Optimize Heap.
Lemma example20071016_6 :
  forall x, -1 <= x ->
  x < 1 + powerRZ x 3.
Proof.
  intros.
  apply Rminus_lt.
idtac "example20071016_6".
  Time interval with (i_prec 1, i_bisect x, i_autodiff x).
Qed.

Require Import Coquelicot.Coquelicot.

Optimize Heap.
Lemma example20071016_7 :
  Rabs (RInt (fun x => atan (sqrt (x*x + 2)) / (sqrt (x*x + 2) * (x*x + 1))) 0 1
        - 5/96*PI*PI) <= 1/1000.
Proof.
idtac "example20071016_7".
(* Time interval with (i_prec 53, i_integral_prec 9, i_integral_depth 1, i_integral_deg 5). **)
Time integral with (i_prec 14, i_fuel 2, i_degree 5).
Qed.

Optimize Heap.
Lemma example20071016_8 :
  RInt_gen (fun x => 1 * (powerRZ x 3 * ln x^2))
           (at_right 0) (at_point 1) = 1/32.
Proof.
  refine ((fun H => Rle_antisym _ _ (proj2 H) (proj1 H)) _).
idtac "example20071016_8".
  Time integral with (i_prec 1).
Qed.

(* TODO/FIXME: Ltac bug?
Optimize Heap.
Lemma example20071016_9 :
  Rabs (RInt_gen (fun t => 1/sqrt t * exp (-(1*t)))
                 (at_point 1) (Rbar_locally p_infty)
        - 2788/10000) <= 1/1000.
Proof.
idtac "example20071016_9".
Time integral .
Qed. *)

(* From coq-interval/testsuite/example-20120205.v *)

Optimize Heap.
Lemma example20120205_1 :
  forall x, (1 <= x)%R -> (0 < x)%R.
Proof.
intros.
idtac "example20120205_1".
Time interval with (i_prec 1).
Qed.

Optimize Heap.
Lemma example20120205_2 : forall x, (1 <= x)%R -> (x <= x * x)%R.
Proof.
intros.
apply Rminus_le.
idtac "example20120205_2".
Time interval with (i_prec 1, i_bisect x, i_autodiff x).
Qed.

Optimize Heap.
Lemma example20120205_3 : forall x, (2 <= x)%R -> (x < x * x)%R.
Proof.
intros.
apply Rminus_lt.
idtac "example20120205_3".
Time interval with (i_prec 1, i_bisect x, i_autodiff x).
Qed.

Optimize Heap.
Lemma example20120205_4 : forall x, (-1 <= x)%R -> (x < 1 + powerRZ x 3)%R.
Proof.
intros.
apply Rminus_lt.
idtac "example20120205_4".
Time interval with (i_prec 1, i_bisect x, i_autodiff x).
Qed.

(* From coq-interval/testsuite/example-20140221.v *)

(* plot(abs((exp(x)-1)-(x+(8388676/2^24)*x^2+(11184876/2^26)*x^3))-((23/27)/(2^33)), [-10831/1000000, 10831/1000000]); *)

(*
Example taken from:
John Harrison, Verifying the Accuracy of Polynomial Approximations in HOL.
In TPHOLs, pages 137-152, 1997.
*)

Optimize Heap.
Lemma example20140221_1 :
  forall x : R,
    (-10831/1000000 <= x /\ x <= 10831/1000000) -> (* TODO Rabs *)
    Rabs ((exp x - 1) - (x + (8388676/2^24) * x^2 + (11184876/2^26) * x^3))
    <= (23/27) / (2^33).
Proof.
intros x H.
idtac "example20140221_1".
Time interval with (i_prec 43, i_bisect x, i_autodiff x, i_depth 16).
Qed.

Optimize Heap.
Lemma example20140221_2 :
  forall x : R,
    (-10831/1000000 <= x /\ x <= 10831/1000000) ->
    Rabs ((exp x - 1) - (x + (8388676/2^24) * x^2 + (11184876/2^26) * x^3))
    <= (23/27) / (2^33).
Proof.
intros x H.
idtac "example20140221_2".
Time interval with (i_prec 43, i_bisect x, i_taylor x).
Qed.

(* From coq-interval/testsuite/example-20140610.v *)

(*
Example taken from:
Marc Daumas and Guillaume Melquiond and César Muñoz,
Guaranteed Proofs Using Interval Arithmetic.
In IEEE ARITH 17, pages 188-195, 2005.
*)

Definition a := 6378137.
Definition f' := 1000000000/298257223563.
Definition umf2 := (1 - f')².
Definition max := 715/512.
Definition rp phi := a / sqrt (1 + umf2 * (tan phi)²).
Definition arp phi :=
  let x := max² - phi² in
  4439091/4 + x * (9023647/4 + x * (
    13868737/64 + x * (13233647/2048 + x * (
      -1898597/16384 + x * (-6661427/131072))))).

Optimize Heap.
Lemma example20140610_1 : forall phi, 0 <= phi <= max ->
  Rabs ((rp phi - arp phi) / rp phi) <= 23/16777216.
Proof.
unfold rp, arp, umf2, a, f', max.
intros phi Hphi.
idtac "example20140610_1".
Time interval with (i_prec 25, i_bisect phi, i_autodiff phi).
Qed.

Optimize Heap.
Lemma example20140610_2 : forall phi, 0 <= phi <= max ->
  Rabs ((rp phi - arp phi) / rp phi) <= 23/16777216.
Proof.
unfold rp, arp, umf2, a, f', max.
intros phi Hphi.
idtac "example20140610_2".
Time interval with (i_prec 25, i_bisect phi, i_taylor phi).
Qed.

(* From coq-interval/testsuite/example-20150105.v *)

Notation pow2 := (Raux.bpow Zaux.radix2).

(*
Example taken from:
William J. Cody Jr. and William Waite
Software Manual for the Elementary Functions
*)

Optimize Heap.
Lemma example20150105 : forall x : R, Rabs x <= 35/100 ->
  let p := fun t => 1 * pow2 (-2) + t * (1116769 * pow2 (-28)) in
  let q := fun t => 1 * pow2 (-1) + t * (13418331 * pow2 (-28)) in
  let r := 2 * (x * p (x^2) / (q (x^2) - x * p (x^2)) + 1 * pow2 (-1)) in
  Rabs ((r - exp x) / exp x) <= 17 * pow2 (-34).
Proof.
intros x Hx p q r.
unfold r, p, q.
idtac "example20150105".
Time interval with (i_prec 40, i_bisect x, i_taylor x).
Qed.

(* From coq-interval/testsuite/example-20160218.v *)

Optimize Heap.
Lemma exp_0_3 :
  Rabs (RInt (fun x => exp x) 0 3 - (exp(1) ^ 3 - 1)) <= 1/(1000*1000).
Proof.
idtac "exp_0_3".
Time integral with (i_prec 28, i_fuel 1).
Qed.

Optimize Heap.
Lemma x_ln1p_0_1 :
  Rabs (RInt (fun x => x * ln(1 + x)) 0 1 - 1/4) <= 1/1000.
Proof.
idtac "x_ln1p_0_1".
Time integral with (i_prec 12, i_fuel 1).
Qed.

Optimize Heap.
Lemma circle :
  Rabs (RInt (fun x => sqrt(1 - x * x)) 0 1 - PI / 4) <= 1/100.
Proof.
idtac "circle".
Time integral with (i_prec 17, i_fuel 7, i_degree 1).
Qed.

Optimize Heap.
Lemma exp_cos_0_1 :
  Rabs (RInt (fun x => sin(x) * exp(cos x)) 0 1 - (exp 1 - exp(cos 1))) <= 1/1000.
Proof.
idtac "exp_cos_0_1".
Time integral with (i_prec 15, i_fuel 1).
Qed.

Optimize Heap.
Lemma arctan_0_1 :
  Rabs (RInt (fun x => 1 / (1 + x*x)) 0 1 - PI / 4) <= 1/1000.
Proof.
idtac "arctan_0_1".
Time integral with (i_prec 13, i_fuel 1).
Qed.

(* From coq-interval/testsuite/example-20171018.v *)

Optimize Heap.
Lemma h_54_ln_2  h :
  -53 <= h <= 0 ->
  -  Basic.Rnearbyint Basic.rnd_DN (h * ln 2 / ln 5) * ln 5 <= 54 * ln 2.
Proof.
intros.
idtac "h_54_ln_2 ".
Time interval with (i_prec 9).
Qed.

(* From coq-interval/testsuite/example_ln.v *)

Optimize Heap.
Lemma example_ln_1 : forall x : R, (0 <= x <= 1 -> ln (exp x) <= 1 + 1/1024)%R.
idtac "example_ln_1".
Time intros; interval with (i_prec 11).
Qed.

Optimize Heap.
Lemma example_ln_2 : (693/1000 < ln 2 < 694/1000)%R.
idtac "example_ln_2".
Time split; interval with (i_prec 14).
Qed.

(* From [Formally Verified Approx. of Definite Integrals by Mahboubi, Melquiond, Sibut-Pinote] *)

Optimize Heap.
Lemma bissect :
  Rabs (RInt (fun x => x * sin x / (1 + cos x * cos x)) 0 PI - PI*PI/4) <= 1/1000000000000.
idtac "bissect".
Time integral with (i_degree 13, i_fuel 13, i_prec 46).
Qed.

Optimize Heap.
Lemma Chebyshev :
  (RInt (fun x => (2048 * x^12 - 6144 * x^10 + 6912 * x^8 - 3584 * x^6 + 840 * x^4 - 72 * x^2 + 1) * exp (-(x - 3/4)^2) * sqrt (1 - x*x)) (-1) 1 + 32555895745 / 10000000000000000) <= 1/100000000000.
idtac "Chebyshev".
Time integral with (i_degree 10, i_fuel 100, i_prec 49).
Qed.

Optimize Heap.
Lemma Rump_Tucker :
  Rabs (RInt (fun x => sin (x + exp x)) 0 8 - 3474/10000) <= 1/1000000.
idtac "Rump_Tucker".
Time integral with (i_degree 7, i_fuel 4000, i_prec 53).
Qed.
