Require Import Reals Interval.Interval_tactic.
Local Open Scope R_scope.

(** http://lipforge.ens-lyon.fr/www/crlibm/ *)
(** http://lipforge.ens-lyon.fr/frs/download.php/162/crlibm-1.0beta4.tar.gz *)

Section CRlibm_exp.
Let p_2_55 : R := 36028797018963968.
Let c3 := 6004799504235417 / p_2_55.
Let c4 := 1501199876148417 / p_2_55.
Notation p x := (x + 1/2 * x^2 + c3 * x^3 + c4 * x^4)%R (only parsing).
Notation eps' := (1/1048576)%R (only parsing).
Notation meps' := (-1/1048576)%R (only parsing).

Lemma crlibm_exp :
  forall x : R,
  (-355/4194304 <= x <= meps') \/ (eps' <= x <= 355/4194304) ->
  Rabs ((p x - exp x + 1) / (exp x - 1)) <= 1/4611686018427387904.
Time intros x [H|H]; unfold c3, c4, p_2_55;
  interval with (i_bisect_taylor x 5, i_prec 90).
Qed.
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
  interval with (i_bisect_taylor x 3).
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
