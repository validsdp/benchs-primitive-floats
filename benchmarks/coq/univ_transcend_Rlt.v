Require Import Reals Interval.Interval_tactic.
Local Open Scope R_scope.

(** Melquiond_IJCAR2008 paper *)

(* plot(abs(sqrt(x) - (((((122 / 7397 * x + (-1733) / 13547) * x
  + 529 / 1274) * x + (-767) / 999) * x
  + 407 / 334) * x + 227 / 925)) - 5/65536, [1/2, 2]); *)
Lemma remez_sqrt__1 :
  forall x, 1/2 <= x <= 2 ->
  (sqrt x - (((((122 / 7397 * x + (-1733) / 13547) * x
                   + 529 / 1274) * x + (-767) / 999) * x
                   + 407 / 334) * x + 227 / 925))
    > - 5/65536.
Time intros x H;
  (* interval with (i_bisect_diff x). *)
  interval with (i_bisect_taylor x 3).
Qed.

Lemma remez_sqrt__2 :
  forall x, 1/2 <= x <= 2 ->
  (sqrt x - (((((122 / 7397 * x + (-1733) / 13547) * x
                   + 529 / 1274) * x + (-767) / 999) * x
                   + 407 / 334) * x + 227 / 925))
    < 5/65536.
Time intros x H;
  (* interval with (i_bisect_diff x). *)
  interval with (i_bisect_taylor x 3).
Qed.

(** Daumas_Lester_Munoz_TC2009 paper with a tighter bound *)

(* plot(abs(atan(x)-(x-(11184811/33554432)*x^3-(13421773/67108864)*x^5))-5/2^28, [-1/30, 1/30]); *)
Lemma abs_err_atan__1 :
  forall x : R, -1/30 <= x <= 1/30 ->
  (atan x - (x - (11184811/33554432) * x^3 - (13421773/67108864) * x^5))
  > - 5/268435456.
Time intros x H;
  interval with (i_bisect_diff x).
Qed.

Lemma abs_err_atan__2 :
  forall x : R, -1/30 <= x <= 1/30 ->
  (atan x - (x - (11184811/33554432) * x^3 - (13421773/67108864) * x^5))
  < 5/268435456.
Time intros x H;
  interval with (i_bisect_diff x).
Qed.

(** Daumas_Melquiond_Munoz_ARITH2005 paper *)

Section Rel_err_geodesic.
Let a := 6378137.
Let f := 1000000000/298257223563.
Let umf2 := (1 - f) ^ 2.
Let max := 715/512.
Notation rp phi := (a / sqrt (1 + umf2 * (sin phi / cos phi) * (sin phi / cos phi))) (only parsing).
Notation arp phi :=
  (let: x := max ^ 2 - phi ^ 2 in
  4439091/4 + x * (9023647/4 + x * (
    13868737/64 + x * (13233647/2048 + x * (
      -1898597/16384 + x * (-6661427/131072)))))) (only parsing).

Lemma rel_err_geodesic__1 :
  forall phi, 0 <= phi <= max ->
  ((rp phi - arp phi) / rp phi) > - 23/16777216.
Proof.
Time unfold (*rp, arp,*) a, umf2, f, max; intros phi Hphi;
(* interval with (i_bisect_diff phi). *)
  interval with (i_bisect_taylor phi 5).
Qed.

Lemma rel_err_geodesic__2 :
  forall phi, 0 <= phi <= max ->
  ((rp phi - arp phi) / rp phi) < 23/16777216.
Proof.
Time unfold (*rp, arp,*) a, umf2, f, max; intros phi Hphi;
(* interval with (i_bisect_diff phi). *)
  interval with (i_bisect_taylor phi 5).
Qed.
End Rel_err_geodesic.
