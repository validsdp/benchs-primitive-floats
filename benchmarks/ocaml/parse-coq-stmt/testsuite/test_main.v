Require Import ZArith Reals.
Local Open Scope R_scope.

Lemma t1 : ~ True <-> (True -> False).
tauto.
Qed.

Lemma t2 : forall a b : R, (a * (a - b) + a * b = a ^ 2)%R.
intros; ring.
Qed.

Lemma t3 : forall a : Z, IZR (Z.abs a) = Rabs (IZR a).
now intros; rewrite abs_IZR.
Qed.

Lemma t4 : forall a : R, (0 <= a -> (sqrt a) ^ 2 = a)%R.
intros a Ha.
unfold pow.
now rewrite Rmult_1_r, sqrt_sqrt.
Qed.

Lemma t5 : sin R0 = R0 /\ tan R0 = R0 /\ atan R0 = R0.
repeat split.
now rewrite sin_0.
now rewrite tan_0.
now rewrite atan_0.
Qed.

Lemma t6 : sin (atan (tan R0)) = R0.
now rewrite tan_0,atan_0,sin_0.
Qed.

Lemma t7 : cos R0 = exp R0.
now rewrite cos_0, exp_0.
Qed.

Lemma t8 : ln R1 = R0.
now rewrite ln_1.
Qed.

Lemma t9 : forall a b c : R, (a - b <= c -> a - c <= b)%R.
intros a b c H.
apply (Rplus_le_compat_r (b - c))%R in H.
now ring_simplify in H.
Qed.

Lemma t10 : forall x : R, exists n : Z, (IZR n <= x < IZR (n + 1))%R.
intros x.
exists (up x - 1)%Z.
ring_simplify (up x - 1 + 1)%Z.
pose proof (archimed x) as [H1 H2].
split; auto with real.
rewrite minus_IZR; simpl.
clear H1.
now apply t9.
Qed.

Lemma t11 : exists x_0 x_1 : R, (x_0 <> x_1 /\ x_0 ^ 2 = x_0 /\ x_1 ^ 2 = x_1)%R.
exists R0; exists R1.
repeat split; unfold pow; auto with real.
now rewrite !Rmult_1_l.
Qed.

Lemma t12 : (- (/ 2) = / (- 2))%R.
now rewrite Ropp_inv_permute; discrR.
Qed.

Lemma t13 : (0 < powerRZ 2 (2 ^ 2))%R.
now auto with real.
Qed.

Check (t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13).
