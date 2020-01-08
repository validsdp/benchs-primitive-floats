Require Import Reals.
From Interval Require Import Tactic.
From Interval Require Import Specific_bigint.
From Interval Require Import Specific_ops.

Module SFBI20 := SpecificFloat BigIntRadix2.
Module ITSFBI20 := IntervalTactic SFBI20.
Import ITSFBI20.

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
(* Finished transaction in 108.225 secs (108.196u,0.02s) (successful) *)
Time integral with (i_native_compute, i_degree 7, i_fuel 4000, i_prec 53).
Qed.
