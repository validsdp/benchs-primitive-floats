Require Import Reals Interval.Interval_tactic.
Local Open Scope R_scope.
Require Import Coquelicot.Coquelicot.

(* From [Formally Verified Approx. of Definite Integrals by Mahboubi, Melquiond, Sibut-Pinote] *)
(*
Lemma bissect :
  Rabs (RInt (fun x => x * sin x / (1 + cos x * cos x)) 0 PI - PI*PI/4) <= 1/1000000000000.
idtac "bissect".
Time integral with (i_degree 13, i_fuel 13, i_prec 53).
Qed.

Lemma Chebyshev :
  (RInt (fun x => (2048 * x^12 - 6144 * x^10 + 6912 * x^8 - 3584 * x^6 + 840 * x^4 - 72 * x^2 + 1) * exp (-(x - 3/4)^2) * sqrt (1 - x*x)) (-1) 1 + 32555895745 / 10000000000000000) <= 1/100000000000.
idtac "Chebyshev".
Time integral with (i_degree 10, i_fuel 100, i_prec 53).
Qed.
*)

Lemma Rump_Tucker :
  Rabs (RInt (fun x => sin (x + exp x)) 0 8 - 3474/10000) <= 1/1000000.
idtac "Rump_Tucker".
(* Time integral with (i_degree 7, i_fuel 4000, i_prec 53). *)
(* Finished transaction in 10.982 secs (10.979u,0.s) (successful) *)
(* Time integral with (i_native_compute, i_degree 7, i_fuel 4000, i_prec 53). *)
(* Finished transaction in 3.335 secs (3.251u,0.027s) (successful) *)
(* Finished transaction in 3.427 secs (3.32u,0.047s) (successful) *)

Time integral with (i_degree 7, i_fuel 4000, i_prec 53).
(* Finished transaction in 11.024 secs (11.016u,0.008s) (successful) *)

(* x10 directed add *)
(* Finished transaction in 12.932 secs (12.932u,0.s) (successful) *)

(* x10 directed mul *)
(* Finished transaction in 13.318 secs (13.316u,0.004s) (successful) *)

(* x10 cmp *)
(* Finished transaction in 19.103 secs (19.092u,0.008s) (successful) *)

(* x10 fromZ_default *)
(* Finished transaction in 44.336 secs (44.327u,0.004s) (successful) *)

(* x10 min, subsumed by cmp *)
(* Finished transaction in 11.202 secs (11.196u,0.008s) (successful) *)

(* x10 div *)
(* Finished transaction in 11.613 secs (11.608u,0.004s) (successful) *)

(* x10 scale *)
(* Finished transaction in 11.352 secs (11.34u,0.012s) (successful) *)

Qed.
