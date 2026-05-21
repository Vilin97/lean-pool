/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.RNS.CoRNalgebraCOrdCauchy
import LeanPool.HopfieldNet.CReals.RNS.CoRNalgebraCauchyCOF
import LeanPool.HopfieldNet.CReals.RNS.CoRNrealsCReals
-- (* Copyright © 1998-2006
--  * Henk Barendregt
--  * Luís Cruz-Filipe
--  * Herman Geuvers
--  * Mariusz Giero
--  * Rik van Ginneken
--  * Dimitri Hendriks
--  * Sébastien Hinderer
--  * Bart Kirkels
--  * Pierre Letouzey
--  * Iris Loeb
--  * Lionel Mamane
--  * Milad Niqui
--  * Russell O’Connor
--  * Randy Pollack
--  * Nickolay V. Shmyrev
--  * Bas Spitters
--  * Dan Synek
--  * Freek Wiedijk
--  * Jan Zwanenburg
--  *
--  * This work is free software; you can redistribute it and/or modify
--  * it under the terms of the GNU General Public License as published by
--  * the Free Software Foundation; either version 2 of the License, or
--  * (at your option) any later version.
--  *
--  * This work is distributed in the hope that it will be useful,
--  * but WITHOUT ANY WARRANTY; without even the implied warranty of
--  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  * GNU General Public License for more details.
--  *
--  * You should have received a copy of the GNU General Public License along
--  * with this work; if not, write to the Free Software Foundation, Inc.,
--  * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
--  *)

-- Require Export CoRN.algebra.Cauchy_COF.
-- Require Export CoRN.reals.CReals.

-- Section R_CReals.

-- (**
-- * The Real Number Structure

-- We will now apply our Cauchy sequence construction to an archimedean
-- ordered field in order to obtain a model of the real numbers.

-- ** Injection of [Q]

-- We start by showing how to inject the rational numbers in the field
-- of Cauchy sequences; this embedding preserves the algebraic operations.

-- %\begin{convention}% Let [F] be an ordered field.
-- %\end{convention}%
-- *)

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

-- Notation "'R_COrdField''" := (R_COrdField F).

--Definition inject_Q (x : F) : R_COrdField' := Build_CauchySeq _ _ (CS_seq_const _ x).

def inject_Q (x : K) : CauchySeq' K := ⟨fun _ => x, by
  apply CS_seq_const⟩

open CauchySeq'

-- Lemma ing_eq : forall x y : F, x [=] y -> inject_Q x [=] inject_Q y.
-- Proof.
--  intros.
--  unfold inject_Q in |- *.
--  simpl in |- *; intro H0.
--  elim H0; intro.
--   elim a; intros N HN.
--   elim HN; clear H0 a HN; intros e He HN; simpl in HN.
--   apply (less_irreflexive_unfolded _ e).
--   apply leEq_less_trans with ([0]:F); auto.
--   astepr (x[-]x); astepr (y[-]x); eauto with arith.
--  elim b; intros N HN.
--  elim HN; clear H0 b HN; intros e He HN; simpl in HN.
--  apply (less_irreflexive_unfolded _ e).
--  apply leEq_less_trans with ([0]:F); auto.
--  astepr (x[-]x); astepr (x[-]y); eauto with arith.
-- Qed.

/--
If `x = y` in `K`, then the constant Cauchy sequences `inject_Q x` and `inject_Q y` are equal.
-/
lemma ing_eq {x y : K} (h : x = y) : inject_Q x = inject_Q y := by
  -- inject_Q x and inject_Q y are both constant sequences
  rw [h]

-- Lemma ing_plus : forall x y : F, inject_Q (x[+]y) [=] inject_Q x[+]inject_Q y.
-- Proof.
--  intros.
--  unfold inject_Q in |- *.
--  simpl in |- *; intro H.
--  elim H; intro.
--   elim a; intros N HN.
--   elim HN; clear H a HN; intros e He HN; simpl in HN.
--   apply (less_irreflexive_unfolded _ e).
--   apply leEq_less_trans with ([0]:F); auto.
--   astepr (x[+]y[-] (x[+]y)); eauto with arith.
--  elim b; intros N HN.
--  elim HN; clear H b HN; intros e He HN; simpl in HN.
--  apply (less_irreflexive_unfolded _ e).
--  apply leEq_less_trans with ([0]:F); auto.
--  astepr (x[+]y[-] (x[+]y)); eauto with arith.
-- Qed.


instance : HAdd (CauchySeq' K) (CauchySeq' K) (CauchySeq' K) := by {
  constructor
  intros s1 s2
  constructor
  apply CS_seq_plus s1.1 s2.1
  exact s1.CS_proof
  exact s2.CS_proof}

/--
For all `x y : K`, `inject_Q (x + y) = inject_Q x + inject_Q y`.
-/
lemma ing_plus (x y : K) : inject_Q (x + y) = inject_Q x + inject_Q y := by
  -- Both sides are constant Cauchy sequences
  exact rfl

-- Lemma ing_plus : forall x y : F, inject_Q (x[+]y) [=] inject_Q x[+]inject_Q y.
-- Proof.
--  intros.
--  unfold inject_Q in |- *.
--  simpl in |- *; intro H.
--  elim H; intro.
--   elim a; intros N HN.
--   elim HN; clear H a HN; intros e He HN; simpl in HN.
--   apply (less_irreflexive_unfolded _ e).
--   apply leEq_less_trans with ([0]:F); auto.
--   astepr (x[+]y[-] (x[+]y)); eauto with arith.
--  elim b; intros N HN.
--  elim HN; clear H b HN; intros e He HN; simpl in HN.
--  apply (less_irreflexive_unfolded _ e).
--  apply leEq_less_trans with ([0]:F); auto.
--  astepr (x[+]y[-] (x[+]y)); eauto with arith.
-- Qed.

-- Lemma ing_min : forall x : F, inject_Q [--]x [=] [--] (inject_Q x).
-- Proof.
--  intros.
--  unfold inject_Q in |- *.
--  simpl in |- *; intro H.
--  elim H; intro.
--   elim a; intros N HN.
--   elim HN; clear H a HN; intros e He HN; simpl in HN.
--   apply (less_irreflexive_unfolded _ e).
--   apply leEq_less_trans with ([0]:F); auto.
--   astepr ( [--]x[-][--]x); eauto with arith.
--  elim b; intros N HN.
--  elim HN; clear H b HN; intros e He HN; simpl in HN.
--  apply (less_irreflexive_unfolded _ e).
--  apply leEq_less_trans with ([0]:F); auto.
--  astepr ( [--]x[-][--]x); eauto with arith.
-- Qed.

instance : Neg (CauchySeq' K) := sorry

/--
For all `x : K`, `inject_Q (-x) = -inject_Q x`.
-/
lemma ing_min (x : K) : inject_Q (-x) = -inject_Q x := by
  -- Both sides are constant Cauchy sequences
  sorry

-- Lemma ing_lt : forall x y : F, x [<] y -> inject_Q x [<] inject_Q y.
-- Proof.
--  intros.
--  simpl in |- *.
--  exists 0.
--  exists ((y[-]x) [/]TwoNZ).
--   apply pos_div_two.
--   apply shift_zero_less_minus.
--   assumption.
--  intros.
--  apply less_leEq; apply pos_div_two'.
--  simpl in |- *.
--  apply shift_zero_less_minus; auto.
-- Qed.

-- Lemma ing_ap : forall x y : F, x [#] y -> inject_Q x [#] inject_Q y.
--  intros x y H; elim (ap_imp_less _ _ _ H); intro Hlt; [ left | right ]; apply ing_lt; auto.
-- Qed.

/--
If `x ≠ y` in `K`, then `inject_Q x ≠ inject_Q y` in the Cauchy completion.
-/
lemma ing_ap {x y : K} (h : x ≠ y) : inject_Q x ≠ inject_Q y := by
  intro h'
  apply h
  -- inject_Q x = inject_Q y implies x = y for constant sequences
  have : ∀ (a b : K), inject_Q a = inject_Q b → a = b := by
    intros a b eq
    -- By definition, inject_Q a = ⟨fun _, a, _⟩ and inject_Q b = ⟨fun _, b, _⟩
    -- So equality implies a = b
    dsimp [inject_Q] at eq
    injection eq with h'
    exact funext_iff.mp h' 0
  exact this x y h'

-- Lemma ing_cancel_eq : forall x y : F, inject_Q x [=] inject_Q y -> x [=] y.
-- Proof.
--  intros x y Hxy.
--  apply not_ap_imp_eq; intro Hap.
--  elim (ap_irreflexive_unfolded _ (inject_Q x)).
--  astepr (inject_Q y).
--  apply ing_ap; auto.
-- Qed.

/--
If `inject_Q x = inject_Q y`, then `x = y`.
-/
lemma ing_cancel_eq {x y : K} (h : inject_Q x = inject_Q y) : x = y := by
  by_contra hxy
  have : inject_Q x ≠ inject_Q y := ing_ap hxy
  contradiction


-- Lemma ing_cancel_less : forall x y : F, inject_Q x [<] inject_Q y -> x [<] y.
-- Proof.
--  intros x y H.
--  elim H; intros N HN; elim HN; clear H HN; intros e He HN; simpl in HN.
--  apply less_leEq_trans with (x[+]e).
--   apply shift_less_plus'; astepl ([0]:F); auto.
--  apply shift_plus_leEq'; eauto.
-- Qed.

instance :  LT (CauchySeq' K) := by {
  refine { lt := ?_ }
  intros s1 s2
  sorry

}

/--
If `inject_Q x < inject_Q y` in the Cauchy completion, then `x < y` in `K`.
-/
lemma ing_cancel_less {x y : K} (h : inject_Q x < inject_Q y) : x < y := by {
  --  intros x y H.
  dsimp [inject_Q] at h
  sorry
--  elim H; intros N HN; elim HN; clear H HN; intros e He HN; simpl in HN.
--  apply less_leEq_trans with (x[+]e).
--   apply shift_less_plus'; astepl ([0]:F); auto.
--  apply shift_plus_leEq'; eauto.

}

-- Lemma ing_le : forall x y : F, x [<=] y -> inject_Q x [<=] inject_Q y.
-- Proof.
--  intros.
--  intro.
--  rewrite -> leEq_def in H; apply H.
--  apply ing_cancel_less.
--  auto.
-- Qed.

-- Lemma ing_le : forall x y : F, x [<=] y -> inject_Q x [<=] inject_Q y.
-- Proof.
--  intros.
--  intro.
--  rewrite -> leEq_def in H; apply H.
--  apply ing_cancel_less.
--  auto.
-- Qed.

instance :   LE (CauchySeq' K) := sorry

/--
If `x ≤ y` in `K`, then `inject_Q x ≤ inject_Q y` in the Cauchy completion.
-/
lemma ing_le {x y : K} (h : x ≤ y) : inject_Q x ≤ inject_Q y := by
  apply?

-- Lemma ing_cancel_leEq : forall x y : F, inject_Q x [<=] inject_Q y -> x [<=] y.
-- Proof.
--  intros.
--  rewrite -> leEq_def; intro.
--  apply H.
--  apply ing_lt.
--  auto.
-- Qed.

instance : LE (CauchySeq' K) := sorry

/--
If `inject_Q x ≤ inject_Q y` in the Cauchy completion, then `x ≤ y` in `K`.
-/
lemma ing_cancel_leEq {x y : K} (h : inject_Q x ≤ inject_Q y) : x ≤ y := sorry

-- Lemma ing_cancel_AbsSmall : forall e x y : F,
--  AbsSmall (inject_Q e) (inject_Q x[-]inject_Q y) -> AbsSmall e (x[-]y).
-- Proof.
--  intros.
--  elim H.
--  intros H0 H1.
--  split.
--   apply ing_cancel_leEq.
--   astepl ( [--] (inject_Q e)).
--    astepr (inject_Q x[-]inject_Q y).
--     assumption.
--    astepl (inject_Q x[+][--] (inject_Q y)).
--    apply eq_transitive_unfolded with (inject_Q x[+]inject_Q [--]y).
--     apply plus_resp_eq.
--     apply eq_symmetric_unfolded.
--     apply ing_min.
--    Step_final (inject_Q (x[+][--]y)).
--    apply eq_symmetric_unfolded.
--    apply ing_plus.
--   apply eq_symmetric_unfolded.
--   apply ing_min.
--  apply ing_cancel_leEq.
--  astepl (inject_Q x[-]inject_Q y).
--   assumption.
--  astepl (inject_Q x[+][--] (inject_Q y)).
--  apply eq_transitive_unfolded with (inject_Q x[+]inject_Q [--]y).
--   apply plus_resp_eq.
--   apply eq_symmetric_unfolded.
--   apply ing_min.
--  Step_final (inject_Q (x[+][--]y)).
--  apply eq_symmetric_unfolded.
--  apply ing_plus.
-- Qed.

instance :  HSub (CauchySeq' K) (CauchySeq' K)  (CauchySeq' K) := sorry

-- /--
-- If `AbsSmall (inject_Q e) (inject_Q x - inject_Q y)` holds in the Cauchy completion,
-- then `AbsSmall e (x - y)` holds in `K`.
-- -/
-- lemma ing_cancel_AbsSmall (e x y : K)
--   (h : AbsSmall (K:=K) (inject_Q e) (inject_Q x - inject_Q y)) : AbsSmall e (x - y) := sorry


-- Lemma ing_One : inject_Q ([1]:F) [=] [1].
-- Proof.
--  apply not_ap_imp_eq; intro H.
--  elim H; intro Hlt; elim Hlt; intros N HN; elim HN; clear H Hlt HN; intros e He HN; simpl in HN.
--   apply (less_irreflexive_unfolded F [0]).
--   apply less_leEq_trans with e; auto.
--   astepr ([1][-] ([1]:F)); eauto.
--  apply (less_irreflexive_unfolded F [0]).
--  apply less_leEq_trans with e; auto.
--  astepr ([1][-] ([1]:F)); eauto.
-- Qed.


/--
`inject_Q 1 = 1` in the Cauchy completion.
-/
lemma ing_One : inject_Q (1 : K) = ⟨ by { exact 1 }, by { apply CS_seq_const}⟩ := by
  rfl

-- Lemma ing_nring' : forall m n : nat,
--  CS_seq _ (nring (R:=R_COrdField') n) m [=] CS_seq _ (inject_Q (nring n)) m.
-- Proof.
--  intros.
--  induction  n as [| n Hrecn]; simpl in |- *; algebra.
-- Qed.

-- Lemma ing_nring' : forall m n : nat,
--  CS_seq _ (nring (R:=R_COrdField') n) m [=] CS_seq _ (inject_Q (nring n)) m.
-- Proof.
--  intros.
--  induction  n as [| n Hrecn]; simpl in |- *; algebra.
-- Qed.

-- Lemma ing_nring : forall n : nat, nring n [=] inject_Q (nring n).
-- Proof.
--  intros.
--  apply not_ap_imp_eq; intro Hap.
--  elim Hap; intro Hlt; elim Hlt; intros N HN; elim HN; clear Hap Hlt HN; intros e He HN.
--   apply (less_irreflexive_unfolded F [0]).
--   apply less_leEq_trans with e; auto.
--   eapply leEq_wdr.
--    apply (HN N); auto.
--   apply x_minus_x; apply eq_symmetric_unfolded; apply ing_nring'.
--  apply (less_irreflexive_unfolded F [0]).
--  apply less_leEq_trans with e; auto.
--  eapply leEq_wdr.
--   apply (HN N); auto.
--  apply x_minus_x; apply ing_nring'.
-- Qed.

-- Lemma ing_mult : forall x y : F, inject_Q (x[*]y) [=] inject_Q x[*]inject_Q y.
-- Proof.
--  intros.
--  unfold inject_Q in |- *.
--  simpl in |- *; intro H.
--  elim H; intro.
--   elim a; intros N HN.
--   elim HN; clear H a HN; intros e He HN; simpl in HN.
--   apply (less_irreflexive_unfolded _ e).
--   apply leEq_less_trans with ([0]:F); auto.
--   astepr (x[*]y[-]x[*]y); eauto with arith.
--  elim b; intros N HN.
--  elim HN; clear H b HN; intros e He HN; simpl in HN.
--  apply (less_irreflexive_unfolded _ e).
--  apply leEq_less_trans with ([0]:F); auto.
--  astepr (x[*]y[-]x[*]y); eauto with arith.
-- Qed.

instance : HMul (CauchySeq' K) (CauchySeq' K) (CauchySeq' K) := by {
  constructor
  intros s1 s2
  constructor
  apply CS_seq_mult s1.1 s2.1
  exact s1.CS_proof
  exact s2.CS_proof}

/--
For all `x y : K`, `inject_Q (x * y) = inject_Q x * inject_Q y`.
-/
lemma ing_mult (x y : K) : inject_Q (x * y) = inject_Q x * inject_Q y := by
  exact rfl

-- Opaque R_COrdField.

-- Opaque R_COrdField.

-- Lemma ing_div_three : forall x, inject_Q x [/]ThreeNZ [=] inject_Q (x [/]ThreeNZ).
-- Proof.
--  intros.
--  apply mult_cancel_lft with (Three:R_COrdField').
--   apply pos_ap_zero.
--   apply pos_three.
--  (* JZ: Removed Rational. *)
--  apply eq_symmetric_unfolded.
--  apply eq_transitive_unfolded with (inject_Q (Three:F) [*]inject_Q (x [/]ThreeNZ)).
--   apply mult_wdl.
--   apply ing_nring.
--  apply eq_transitive_unfolded with (inject_Q (Three[*]x [/]ThreeNZ)).
--   apply eq_symmetric_unfolded.
--   apply ing_mult.
--  astepr (inject_Q x).
--  apply ing_eq; algebra.
-- Qed.

instance : HDiv (CauchySeq' K) K (CauchySeq' K) := sorry

/--
For all `x : K`, `inject_Q x / 3 = inject_Q (x / 3)`.
-/
lemma ing_div_three (x : K) : inject_Q x / (3 : K) = inject_Q (x / (3 : K)) := by sorry

-- Transparent R_COrdField.

-- Lemma ing_n : forall x n H1 H2,
--  (inject_Q x[/] nring n[//]H2) [=] inject_Q (x[/] nring n[//]H1).
-- Proof.
--  intros.
--  apply mult_cancel_lft with (inject_Q (nring (R:=F) n)).
--   apply Greater_imp_ap.
--   astepr (nring (R:=R_COrdField') n).
--    apply nring_pos.
--    apply Nat.neq_0_lt_0.
--    apply Nat.neq_sym.
--    apply nring_ap_zero_imp with F.
--    assumption.
--   apply ing_nring.
--  apply eq_transitive_unfolded with (inject_Q x).
--   rstepr (nring n[*] (inject_Q x[/] nring n[//]H2)).
--   apply mult_wdl.
--   apply eq_symmetric_unfolded.
--   apply ing_nring.
--  apply eq_symmetric_unfolded.
--  apply eq_transitive_unfolded with (inject_Q (nring n[*] (x[/] nring n[//]H1))).
--   apply eq_symmetric_unfolded.
--   apply ing_mult.
--  apply ing_eq.
--  rational.
-- Qed.


-- Lemma ing_n : forall x n H1 H2,
--  (inject_Q x[/] nring n[//]H2) [=] inject_Q (x[/] nring n[//]H1).
-- Proof.
--  intros.
--  apply mult_cancel_lft with (inject_Q (nring (R:=F) n)).
--   apply Greater_imp_ap.
--   astepr (nring (R:=R_COrdField') n).
--    apply nring_pos.
--    apply Nat.neq_0_lt_0.
--    apply Nat.neq_sym.
--    apply nring_ap_zero_imp with F.
--    assumption.
--   apply ing_nring.
--  apply eq_transitive_unfolded with (inject_Q x).
--   rstepr (nring n[*] (inject_Q x[/] nring n[//]H2)).
--   apply mult_wdl.
--   apply eq_symmetric_unfolded.
--   apply ing_nring.
--  apply eq_symmetric_unfolded.
--  apply eq_transitive_unfolded with (inject_Q (nring n[*] (x[/] nring n[//]H1))).
--   apply eq_symmetric_unfolded.
--   apply ing_mult.
--  apply ing_eq.
--  rational.
-- Qed.


-- Theorem expand_Q_R : forall (x : R_COrdField') e, [0] [<] e -> forall N,
--  (forall m, N <= m -> AbsSmall (e [/]FourNZ) (CS_seq F x m[-]CS_seq F x N)) ->
--  forall m, N <= m -> AbsSmall (inject_Q e) (inject_Q (CS_seq F x m) [-]x).
-- Proof.
--  intros x e H N H0 m H1.
--  split.
--   apply less_leEq.
--   simpl in |- *.
--   unfold Rlt in |- *.
--   exists N.
--   exists (e [/]ThreeNZ).
--    apply pos_div_three.
--    assumption.
--   intros.
--   change (e [/]ThreeNZ [<=] CS_seq F (inject_Q (CS_seq F x m) [-]x) n[-][--]e) in |- *.
--   apply plus_cancel_leEq_rht with (R := F) (z := [--]e).
--   rstepl ( [--] (Two[*]e [/]ThreeNZ)).
--   rstepr (CS_seq F (inject_Q (CS_seq F x m) [-]x) n).
--   cut (AbsSmall (e [/]FourNZ) (CS_seq F x m[-]CS_seq F x N)).
--    intro H3.
--    elim H3.
--    intros H4 H5.
--    cut (AbsSmall (e [/]FourNZ) (CS_seq F x n[-]CS_seq F x N)).
--     intro H6.
--     elim H6.
--     intros H7 H8.
--     change ( [--] (Two[*]e [/]ThreeNZ) [<=] CS_seq F x m[-]CS_seq F x n) in |- *.
--     rstepl ( [--] (e [/]ThreeNZ) [+][--] (e [/]ThreeNZ)).
--     rstepr (CS_seq F x m[-]CS_seq F x N[+] (CS_seq F x N[-]CS_seq F x n)).
--     apply plus_resp_leEq_both.
--      apply leEq_transitive with ( [--] (e [/]FourNZ)); auto.
--      apply inv_resp_leEq.
--      apply mult_cancel_leEq with (nring (R:=F) 12).
--       apply nring_pos.
--       auto with arith.
--      rstepl ([0][+]Three[*]e); rstepr (e[+]Three[*]e).
--      apply plus_resp_leEq; apply less_leEq; auto.
--     apply inv_cancel_leEq.
--     rstepl (CS_seq F x n[-]CS_seq F x N).
--     rstepr (e [/]ThreeNZ).
--     apply leEq_transitive with (e [/]FourNZ); auto.
--     apply mult_cancel_leEq with (nring (R:=F) 12).
--      apply nring_pos.
--      auto with arith.
--     rstepl ([0][+]Three[*]e); rstepr (e[+]Three[*]e).
--     apply plus_resp_leEq; apply less_leEq; auto.
--    apply H0.
--    assumption.
--   apply H0.
--   assumption.
--  apply less_leEq.
--  simpl in |- *.
--  unfold Rlt in |- *.
--  exists N.
--  exists (e [/]ThreeNZ).
--   apply pos_div_three.
--   assumption.
--  intros.
--  change (e [/]ThreeNZ [<=] e[-]CS_seq F (inject_Q (CS_seq F x m) [-]x) n) in |- *.
--  apply plus_cancel_leEq_rht with (R := F) (z := [--]e).
--  rstepl ( [--] (Two[*]e [/]ThreeNZ)).
--  rstepr ( [--] (CS_seq F (inject_Q (CS_seq F x m) [-]x) n)).
--  apply inv_resp_leEq.
--  cut (AbsSmall (e [/]FourNZ) (CS_seq F x m[-]CS_seq F x N)).
--   intro.
--   elim H3.
--   intros H4 H5.
--   cut (AbsSmall (e [/]FourNZ) (CS_seq F x n[-]CS_seq F x N)).
--    intro.
--    elim H6.
--    intros H7 H8.
--    change (CS_seq F x m[-]CS_seq F x n [<=] Two[*]e [/]ThreeNZ) in |- *.
--    rstepr (e [/]ThreeNZ[+]e [/]ThreeNZ).
--    rstepl (CS_seq F x m[-]CS_seq F x N[+] (CS_seq F x N[-]CS_seq F x n)).
--    apply plus_resp_leEq_both.
--     apply leEq_transitive with (e [/]FourNZ); auto.
--     apply mult_cancel_leEq with (nring (R:=F) 12).
--      apply nring_pos.
--      auto with arith.
--     rstepl ([0][+]Three[*]e); rstepr (e[+]Three[*]e).
--     apply plus_resp_leEq; apply less_leEq; auto.
--    apply inv_cancel_leEq.
--    rstepr (CS_seq F x n[-]CS_seq F x N).
--    apply leEq_transitive with ( [--] (e [/]FourNZ)); auto.
--    apply inv_resp_leEq.
--    apply mult_cancel_leEq with (nring (R:=F) 12).
--     apply nring_pos.
--     auto with arith.
--    rstepl ([0][+]Three[*]e); rstepr (e[+]Three[*]e).
--    apply plus_resp_leEq; apply less_leEq; auto.
--   apply H0.
--   assumption.
--  apply H0.
--  assumption.
-- Qed.

-- Lemma conv_modulus : forall (x : R_COrdField') M, {N : nat | forall m,
--  N <= m -> AbsSmall (one_div_succ M) (CS_seq F x m[-]CS_seq F x N)}.
-- Proof.
--  intros.
--  case x.
--  intros x_ px.
--  unfold Cauchy_prop in px.
--  cut {N : nat | forall m : nat, N <= m -> AbsSmall (one_div_succ M) (x_ m[-]x_ N)}.
--   intro H.
--   case H.
--   intros N H1.
--   exists N.
--   intros.
--   apply H1.
--   assumption.
--  apply px.
--  apply one_div_succ_pos.
-- Qed.

/--
Given a Cauchy sequence `x` and a natural number `M`,
returns a natural number `N` such that for all `m ≥ N`,
the difference `x m - x N` is small (bounded by `one_div_succ M`).
-/
def conv_modulus (x : CauchySeq' K) (M : Nat) :
  { N : Nat // ∀ m, N ≤ m → AbsSmall (1/(M+1) : K) (CS_seq x m - CS_seq x N) } := by {
  --   constructor
  --   · intros m
  --     cases' x with x px
  --     unfold Cauchy_prop at px
  --     have :  (0 : K) < 1 / (↑M + 1) := by {
  --      norm_cast
  --     -- refine ing_cancel_less ?_
  --     -- simp only [Nat.cast_add, Nat.cast_one]
  --      apply ing_cancel_less
  --      sorry
  --   }
  --     have H := px (1/(M+1)) this
  --     simp only [one_div, inv_pos] at this
  --     obtain ⟨N,H1⟩ := H
  --   --dsimp [AbsSmall]
  --     have hm' : N ≤ m:=sorry
  --     have H1 := H1 m hm'
  --     dsimp [CauchySeq]
  --     sorry
  --
  sorry }


-- Let T (x : R_COrdField') (m : nat) := let (N, _) := conv_modulus x m in N.

/--
Given a Cauchy sequence `x` and a natural number `m`, returns the least `N` such that for all `n ≥ N`,
the difference `x n - x N` is small (bounded by `1/(m+1)`).
-/
def T (x : CauchySeq' K) (m : Nat) : Nat := (conv_modulus x m).val

-- (** We now assume our original field is archimedean and prove that the
-- resulting one is, too.
-- *)

-- Theorem R_is_archemaedian : forall x : R_COrdField', {n : nat | x [<=] nring n}.
-- Proof.
--  intros.
--  case x.
--  intros x_ px.
--  -- px is the Cauchy property for the sequence x_
--  elim (px [1] (pos_one _)); intros Nx HNx.
--  -- For ε = 1, get Nx such that for all m ≥ Nx, |x_ m - x_ Nx| < 1
--  elim (F_is_archemaedian (x_ Nx)); intros N HN.
--  -- By archimedean property of F, find N such that x_ Nx < N
--  exists (S N).
--  -- We will show x ≤ nring (S N)
--  intro H.
--  -- Suppose not, then x > nring (S N)
--  elim H; intros K HK; elim HK; clear H HK; intros e He HK; simpl in HK.
--  -- Use the definition of < in the Cauchy completion: there exists e > 0 such that for all large enough indices, x_ k - nring (S N) > e
--  apply (less_irreflexive_unfolded F [0]).
--  -- Show 0 < 0, contradiction
--  apply less_leEq_trans with e; auto.
--  -- e > 0
--  astepr (x_ (K + Nx) [-]x_ (K + Nx)).
--  -- x_ (K + Nx) - x_ (K + Nx) = 0
--  eapply leEq_transitive.
--   apply (HK (K + Nx)); eauto with arith.
--   -- For k = K + Nx, HK gives x_ (K + Nx) - nring (S N) > e
--  unfold cg_minus in |- *; apply plus_resp_leEq_lft; apply inv_resp_leEq.
--  -- Rearranging terms to get 0 ≤ ...
--  rstepl (x_ Nx[+] (x_ (K + Nx) [-]x_ Nx)).
--  -- x_ (K + Nx) = x_ Nx + (x_ (K + Nx) - x_ Nx)
--  apply plus_resp_leEq_both.
--   apply leEq_wdr with (CS_seq _ (inject_Q (nring N)) (K + Nx)).
--    simpl in |- *; apply less_leEq; auto.
--    -- x_ Nx ≤ nring N
--   apply eq_symmetric_unfolded; apply ing_nring'.
--   -- Use equality of Cauchy sequence at index (K + Nx) with inject_Q (nring N)
--  elim (HNx (K + Nx)); auto with arith.
--  -- Use the Cauchy property to bound |x_ (K + Nx) - x_ Nx| < 1
-- Qed.


-- Hypothesis F_is_archemaedian : forall x : F, {n : nat | x [<] nring n}.
variable (F_is_archimedean : ∀ x : K, ∃ n : Nat, x < n)
include F_is_archimedean in
/--
If the base field `K` is archimedean, then the Cauchy completion is also archimedean:
for any Cauchy sequence `x`, there exists `n : Nat` such that `x ≤ nring n`.
-/
theorem R_is_archimedean :
  ∀ (x : CauchySeq' K), ∃ n : Nat, x ≤ ⟨by {sorry
  }, by {
    sorry
  }⟩:= by stop
  intros x
  -- Use the Cauchy property for ε = 1
  let ε : K := 1
  have ε_pos : (0 : K) < ε := zero_lt_one' K
  obtain ⟨Nx, HNx⟩ := F_is_archimedean

  -- By archimedean property of K, find N such that x_ Nx < N
  let x_Nx := Nx
  obtain ⟨N, HN⟩ := F_is_archimedean x_Nx
  let n := N + 1
  use n
  -- Show x ≤ S N
  intro h
  -- Suppose not, then x > inject_Q n
  -- By definition of <, there exists e > 0 such that for all large enough indices, x_k - n > e
  rcases h with ⟨K, ⟨e, e_pos, HK⟩⟩
  -- Use the Cauchy property at index K + Nx
  have : (x.1 (K + Nx) - n : K) > e := HK (K + Nx) (by {

  })
  -- But x.1 (K + Nx) = x.1 Nx + (x.1 (K + Nx) - x.1 Nx)
  -- And |x.1 (K + Nx) - x.1 Nx| < 1 by Cauchy property
  have bound : |x.1 (K + Nx) - x.1 Nx| < 1 := by
    specialize HNx (K + Nx) (by {})
    exact AbsSmall.lt_of_absSmall HNx
  -- So x.1 (K + Nx) ≤ x.1 Nx + 1
  have le1 : x.1 (K + Nx) ≤ x.1 Nx + 1 := by
    apply le_of_abs_le
    rw [abs_sub_le_iff]
    exact ⟨by {}, by {}⟩
  -- But x.1 Nx < N < n, so x.1 Nx + 1 ≤ n
  have le2 : x.1 Nx + 1 ≤ n := by
    have : x.1 Nx < N := HN
    sorry
  -- So x.1 (K + Nx) ≤ n
  have le3 : x.1 (K + Nx) ≤ n := le_trans le1 le2
  -- But x.1 (K + Nx) - n ≤ 0, so cannot be > e > 0
  have : x.1 (K + Nx) - n ≤ 0 := by sorry
  have : e < 0 := by sorry
  exact lt_irrefl _ (lt_trans e_pos this)



-- Theorem R_is_archemaedian : forall x : R_COrdField', {n : nat | x [<=] nring n}.
-- Proof.
--  intros.
--  case x.
--  intros x_ px.
--  elim (px [1] (pos_one _)); intros Nx HNx.
--  elim (F_is_archemaedian (x_ Nx)); intros N HN.
--  exists (S N).
--  intro H.
--  elim H; intros K HK; elim HK; clear H HK; intros e He HK; simpl in HK.
--  apply (less_irreflexive_unfolded F [0]).
--  apply less_leEq_trans with e; auto.
--  astepr (x_ (K + Nx) [-]x_ (K + Nx)).
--  eapply leEq_transitive.
--   apply (HK (K + Nx)); eauto with arith.
--  unfold cg_minus in |- *; apply plus_resp_leEq_lft; apply inv_resp_leEq.
--  rstepl (x_ Nx[+] (x_ (K + Nx) [-]x_ Nx)).
--  apply plus_resp_leEq_both.
--   apply leEq_wdr with (CS_seq _ (inject_Q (nring N)) (K + Nx)).
--    simpl in |- *; apply less_leEq; auto.
--   apply eq_symmetric_unfolded; apply ing_nring'.
--  elim (HNx (K + Nx)); auto with arith.
-- Qed.



-- (* begin hide *)
-- Let PT (x : R_COrdField') (M : nat) :=
--   proj2_sigT nat
--     (fun N : nat =>
--      forall m : nat,
--      N <= m -> AbsSmall (one_div_succ M) (CS_seq F x m[-]CS_seq F x N))
--     (conv_modulus x M).
-- (* end hide *)

/--
Given a Cauchy sequence `x` and a natural number `M`, `PT x M` is the proof that for all `m ≥ T x M`,
the difference `x m - x (T x M)` is small (bounded by `one_div_succ M`).
-/
def PT (x : CauchySeq' K) (M : Nat) : ∀ m, T x M ≤ m → AbsSmall (1/(M+1) : K) (CS_seq x m - CS_seq x (T x M)) :=
  (conv_modulus x M).property


-- Lemma modulus_property : forall x M m0 m1, T x M <= m0 -> T x M <= m1 ->
--  AbsSmall (Two[*]one_div_succ M) (CS_seq F x m0[-]CS_seq F x m1).
-- Proof.
--  intros.
--  rstepl (one_div_succ (R:=F) M[+]one_div_succ M).
--  rstepr (CS_seq F x m0[-]CS_seq F x (T x M) [+] (CS_seq F x (T x M) [-]CS_seq F x m1)).
--  generalize (PT x M).
--  intro.
--  apply AbsSmall_plus.
--   apply H1.
--   assumption.
--  apply AbsSmall_minus.
--  apply H1.
--  assumption.
-- Qed.


/--
For any Cauchy sequence `x`, natural number `M`, and indices `m0 m1 ≥ T x M`,
the difference `CS_seq x m0 - CS_seq x m1` is small (bounded by `2 * one_div_succ M`).
-/
lemma modulus_property (x : CauchySeq' K) (M m0 m1 : Nat)
  (h0 : T x M ≤ m0) (h1 : T x M ≤ m1) :
  AbsSmall (2 * (1/(M+1) : K)) (CS_seq x m0 - CS_seq x m1) :=
by
  -- Write as (x m0 - x (T x M)) + (x (T x M) - x m1)
  have : CS_seq x m0 - CS_seq x m1 =
    (CS_seq x m0 - CS_seq x (T x M)) + (CS_seq x (T x M) - CS_seq x m1) := by
    simp only [sub_add_sub_cancel]
  rw [this]
  sorry
  -- Use triangle inequality for AbsSmall
  -- apply AbsSmall.plus
  -- · exact PT x M m0 h0
  -- · exact AbsSmall.minus (PT x M m1 h1)





-- Lemma modulus_property_2 : forall x M m, T x M <= m ->
--  AbsSmall (one_div_succ M) (CS_seq F x m[-]CS_seq F x (T x M)).
-- Proof.
--  intros.
--  apply (PT x M).
--  assumption.
-- Qed.

-- Lemma expand_Q_R_2 : forall x e N, [0] [<] e ->
--  (forall m, N <= m -> AbsSmall (e [/]FourNZ) (CS_seq F x m[-]CS_seq F x N)) ->
--  AbsSmall (inject_Q e) (inject_Q (CS_seq F x N) [-]x).
-- Proof.
--  intros x e N H H0.
--  apply expand_Q_R with (x := x) (e := e) (N := N).
--    assumption.
--   intros.
--   apply H0.
--   assumption.
--  constructor.
-- Qed.

-- The diagonal sequence of a sequence of Cauchy sequences is itself Cauchy.
lemma CS_seq_diagonal (a : CauchySeq' K) : Cauchy_prop
  (fun m => let b : CauchySeq' K := ⟨fun n => CS_seq a n, sorry⟩; CS_seq b (T b m)) := sorry

-- Lemma CS_seq_diagonal : forall a : CauchySeq R_COrdField',
--  Cauchy_prop (fun m => let b := (CS_seq _ a m) in CS_seq F b (T b m)).
-- Proof.
--  intros.
--  unfold Cauchy_prop in |- *.
--  case a.
--  intros a_ pa.
--  intros.
--  simpl in |- *.
--  unfold Cauchy_prop in pa.
--  cut (e [#] [0]).
--   intro H0.
--   cut {n : nat | (Twelve[/] e[//]H0) [-][1] [<] nring n}.
--    intro H1.
--    case H1.
--    intros M H2.
--    cut {N : nat | forall m : nat, N <= m -> AbsSmall (inject_Q e [/]SixNZ) (a_ m[-]a_ N)}.
--     intro H3.
--     case H3.
--     intros N H4.
--     exists (Nat.max N M).
--     intros.
--     apply ing_cancel_AbsSmall.
--     rstepl (inject_Q e [/]ThreeNZ[+]inject_Q e [/]ThreeNZ[+]inject_Q e [/]ThreeNZ).
--     rstepr (inject_Q (CS_seq F (a_ m) (T (a_ m) m)) [-]a_ m[+] (a_ (Nat.max N M) [-]
--       inject_Q (CS_seq F (a_ (Nat.max N M)) (T (a_ (Nat.max N M)) (Nat.max N M)))) [+] (a_ m[-]a_ (Nat.max N M))).
--     apply AbsSmall_plus.
--      apply AbsSmall_plus.
--       astepl (inject_Q (e [/]ThreeNZ)).
--        apply AbsSmall_leEq_trans with (R := R_COrdField') (e1 := inject_Q (Four[*]one_div_succ m)).
--         apply ing_le.
--         apply leEq_transitive with (y := Four[*]one_div_succ (R:=F) M).
--          apply mult_resp_leEq_lft.
--           apply one_div_succ_resp_leEq.
--           eauto with arith.
--          apply less_leEq.
--          apply pos_four.
--         apply mult_cancel_leEq with (R := F) (z := (nring M[+][1]) [*] (Three:F)).
--          apply mult_resp_pos.
--           apply less_transitive_unfolded with (F := F) (y := Twelve[/] e[//]H0).
--            apply mult_cancel_less with (R := F) (z := e).
--             assumption.
--            rstepl ([0]:F).
--            rstepr (Twelve:F).
--            apply nring_pos.
--            apply Nat.lt_0_succ.
--           apply plus_cancel_less with (R := F) (z := [--] ([1]:F)).
--           rstepl ((Twelve[/] e[//]H0) [-][1]).
--           rstepr (nring (R:=F) M).
--           exact H2.
--          apply nring_pos.
--          apply Nat.lt_0_succ.
--         unfold one_div_succ in |- *.
--         unfold Snring in |- *.
--         change (Four[*] ([1][/] nring M[+][1][//]nringS_ap_zero F M) [*]
--           ((nring M[+][1]) [*]Three) [<=] e [/]ThreeNZ[*] ((nring M[+][1]) [*]Three)) in |- *.
--         rstepl (Twelve:F).
--         rstepr (e[*] (nring M[+][1])).
--         apply mult_cancel_leEq with (R := F) (z := [1][/] e[//]H0).
--          apply recip_resp_pos.
--          assumption.
--         rstepr (nring (R:=F) M[+][1]).
--         apply plus_cancel_leEq_rht with (R := F) (z := [--] ([1]:F)).
--         rstepl ((Twelve[/] e[//]H0) [-][1]).
--         rstepr (nring (R:=F) M).
--         apply less_leEq; exact H2.
--        apply expand_Q_R_2 with (x := a_ m) (e := Four[*]one_div_succ (R:=F) m) (N := T (a_ m) m).
--         apply mult_resp_pos.
--          apply pos_four.
--         apply one_div_succ_pos.
--        intros.
--        rstepl (one_div_succ (R:=F) m).
--        apply modulus_property_2.
--        assumption.
--       apply eq_symmetric_unfolded.
--       apply ing_div_three.
--      astepl (inject_Q (e [/]ThreeNZ)).
--       apply AbsSmall_leEq_trans with (R := R_COrdField') (e1 := inject_Q (Four[*]one_div_succ (R:=F) M)).
--        apply less_leEq.
--        apply ing_lt.
--        apply mult_cancel_less with (R := F) (z := (nring M[+][1]) [*] (Three:F)).
--         apply mult_resp_pos.
--          apply less_transitive_unfolded with (F := F) (y := Twelve[/] e[//]H0).
--           apply mult_cancel_less with (R := F) (z := e).
--            assumption.
--           rstepl ([0]:F).
--           rstepr (Twelve:F).
--           apply nring_pos.
--           apply Nat.lt_0_succ.
--          apply plus_cancel_less with (R := F) (z := [--] ([1]:F)).
--          rstepl ((Twelve[/] e[//]H0) [-][1]).
--          rstepr (nring (R:=F) M).
--          exact H2.
--         apply pos_three.
--        unfold one_div_succ in |- *.
--        unfold Snring in |- *.
--        change (Four[*] ([1][/] nring M[+][1][//]nringS_ap_zero F M) [*]
--          ((nring M[+][1]) [*]Three) [<] e [/]ThreeNZ[*] ((nring M[+][1]) [*]Three)) in |- *.
--        rstepl (Twelve:F).
--        rstepr (e[*] (nring M[+][1])).
--        apply mult_cancel_less with (R := F) (z := [1][/] e[//]H0).
--         apply recip_resp_pos.
--         assumption.
--        rstepr (nring (R:=F) M[+][1]).
--        apply plus_cancel_less with (R := F) (z := [--] ([1]:F)).
--        rstepl ((Twelve[/] e[//]H0) [-][1]).
--        rstepr (nring (R:=F) M).
--        exact H2.
--       apply AbsSmall_minus.
--       apply expand_Q_R_2 with (x := a_ (Nat.max N M)) (e := Four[*]one_div_succ (R:=F) M)
--         (N := T (a_ (Nat.max N M)) (Nat.max N M)).
--        apply mult_resp_pos.
--         apply pos_four.
--        apply one_div_succ_pos.
--       intros.
--       rstepl (one_div_succ (R:=F) M).
--       apply AbsSmall_leEq_trans with (R := F) (e1 := one_div_succ (R:=F) (Nat.max N M)).
--        apply one_div_succ_resp_leEq.
--        auto with arith.
--       apply modulus_property_2.
--       assumption.
--      apply eq_symmetric_unfolded.
--      apply ing_div_three.
--     rstepl (inject_Q e [/]SixNZ[+]inject_Q e [/]SixNZ).
--     rstepr (a_ m[-]a_ N[+] (a_ N[-]a_ (Nat.max N M))).
--     apply AbsSmall_plus.
--      apply H4; eauto with arith.
--     apply AbsSmall_minus.
--     apply H4; eauto with arith.
--    apply pa.
--    apply mult_cancel_less with (R := R_COrdField') (z := Six:R_COrdField').
--     apply pos_six.
--    rstepl ([0]:R_COrdField').
--    rstepr (inject_Q e).
--    change (inject_Q ([0]:F) [<] inject_Q e) in |- *.
--    apply ing_lt.
--    assumption.
--   apply F_is_archemaedian.
--  apply Greater_imp_ap.
--  assumption.
-- Qed.



-- (**
-- ** Cauchy Completeness
-- We can also define a limit operator.
-- *)

-- Lemma Q_dense_in_R : forall x, [0] [<] x -> {q : F | [0] [<] q | inject_Q q [<] x}.
-- Proof.
--  intros.
--  cut (x [#] [0]).
--   intro H0.
--   cut {n : nat | ([1][/] x[//]H0) [<=] nring n}.
--    intro H1.
--    case H1.
--    intros n H2.
--    cut (nring (R:=F) (S n) [#] [0]).
--     intro H3.
--     exists ([1][/] nring (S n) [//]H3).
--      apply recip_resp_pos.
--      apply ing_cancel_less.
--      change ([0] [<] inject_Q (nring (S n))) in |- *.
--      apply less_leEq_trans with (R := R_COrdField') (y := [1][/] x[//]H0).
--       apply recip_resp_pos.
--       assumption.
--      apply leEq_transitive with (inject_Q (nring n)).
--       astepr (nring (R:=R_COrdField') n).
--        assumption.
--       apply ing_nring.
--      astepl (nring (R:=R_COrdField') n).
--       astepr (nring (R:=R_COrdField') (S n)).
--        apply less_leEq; astepr (nring (R:=R_COrdField') n[+][1]); apply less_plusOne.
--       apply ing_nring.
--      apply ing_nring.
--     cut (nring (R:=R_COrdField') (S n) [#] [0]).
--      intro H4.
--      astepl (inject_Q ([1]:F) [/] nring (S n) [//]H4).
--       apply shift_div_less.
--        apply nring_pos.
--        auto with arith.
--       astepl ([1]:R_COrdField').
--       apply shift_less_mult' with H0.
--        assumption.
--       eapply leEq_less_trans.
--        apply H2.
--       astepr (nring (R:=R_COrdField') n[+][1]); apply less_plusOne.
--      apply ing_n.
--     apply nringS_ap_zero.
--    apply nringS_ap_zero.
--   apply R_is_archemaedian.
--  apply Greater_imp_ap.
--  assumption.
-- Qed.

-- Definition LimR_CauchySeq (a : CauchySeq R_COrdField') :=
--   Build_CauchySeq _ _ (CS_seq_diagonal a).

--#check CS_seq_diagonal
--#check T
/--
The limit of a Cauchy sequence of Cauchy sequences, defined via the diagonal sequence.
-/
def LimR_CauchySeq (a : CauchySeq' K) : K := by {
  apply CS_seq
  constructor
  · apply CS_seq_diagonal a
  · sorry
}

/--
The real numbers constructed as Cauchy sequences are complete:
every Cauchy sequence has a limit.
-/
theorem R_is_complete (a : CauchySeq' K) : SeqLimit (K := K) (CS_seq a) ((LimR_CauchySeq a)) := sorry

-- Theorem R_is_complete : forall a : CauchySeq R_COrdField',
--  SeqLimit (R:=R_COrdField') a (LimR_CauchySeq a).
-- Proof.
--  intros.
--  simpl in |- *.
--  red in |- *.
--  case a.
--  intros a_ pa.
--  intros e H.
--  simpl in |- *.
--  set (He := pos_ap_zero _ _ H) in *.
--  elim (Q_dense_in_R (e [/]ThreeNZ)); [ intros q Hq Hinj | apply pos_div_three; auto ].
--  set (Hq' := pos_ap_zero _ _ Hq) in *.
--  elim (F_is_archemaedian ((Four[/] q[//]Hq') [-][1])); intros M HM.
--  unfold Cauchy_prop in pa.
--  elim (pa (e [/]SixNZ)); [ intros N2 HN2 | apply pos_div_six; auto ].
--  elim (CS_seq_diagonal (Build_CauchySeq R_COrdField' a_ pa) (q [/]EightNZ));
--    [ intros N1 HN1 | apply pos_div_eight; auto ].
--  exists (Nat.max M (Nat.max N1 N2)).
--  intros.
--  rstepl (e [/]ThreeNZ[+]e [/]ThreeNZ[+]e [/]ThreeNZ).
--  rstepr (a_ m[-]a_ (Nat.max M (Nat.max N1 N2)) [+] (a_ (Nat.max M (Nat.max N1 N2)) [-] inject_Q
--    (CS_seq F (LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa)) (Nat.max M (Nat.max N1 N2)))) [+] (inject_Q
--      (CS_seq F (LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa)) (Nat.max M (Nat.max N1 N2))) [-]
--        LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa))).
--  apply AbsSmall_plus.
--   apply AbsSmall_plus.
--    rstepl (e [/]SixNZ[+]e [/]SixNZ).
--    rstepr (a_ m[-]a_ N2[+] (a_ N2[-]a_ (Nat.max M (Nat.max N1 N2)))).
--    apply AbsSmall_plus.
--     apply HN2; eauto with arith.
--    apply AbsSmall_minus; apply HN2; eauto with arith.
--   apply AbsSmall_leEq_trans with (R := R_COrdField') (e1 := inject_Q q).
--    apply less_leEq; assumption.
--   apply AbsSmall_minus.
--   simpl in |- *.
--   apply AbsSmall_leEq_trans with (R := R_COrdField')
--     (e1 := Four[*] (one_div_succ (Nat.max M (Nat.max N1 N2)):R_COrdField')).
--    apply less_leEq.
--    apply leEq_less_trans with (R := R_COrdField') (y := Four[*]one_div_succ (R:=R_COrdField') M).
--     apply mult_resp_leEq_lft.
--      apply one_div_succ_resp_leEq.
--      auto with arith.
--     apply less_leEq; apply pos_four.
--    apply mult_cancel_less with (R := R_COrdField') (z := nring M[+][1]:R_COrdField').
--     apply less_transitive_unfolded with (F := R_COrdField') (y := inject_Q (Four[/] q[//]Hq')).
--      change (inject_Q ([0]:F) [<] inject_Q (Four[/] q[//]Hq')) in |- *.
--      apply ing_lt.
--      apply mult_cancel_less with (R := F) (z := q).
--       assumption.
--      rstepl ([0]:F).
--      rstepr (Four:F).
--      apply pos_four.
--     apply shift_less_plus.
--     astepl (inject_Q ((Four[/] q[//]Hq') [+][--][1])).
--      astepr (inject_Q (nring M)).
--       apply ing_lt.
--       rstepl ((Four[/] q[//]Hq') [-][1]).
--       exact HM.
--      apply eq_symmetric_unfolded.
--      apply ing_nring.
--     unfold cg_minus in |- *.
--     apply eq_transitive_unfolded with (inject_Q (Four[/] q[//]Hq') [+]inject_Q ( [--][1]:F)).
--      apply ing_plus.
--     apply plus_resp_eq.
--     apply eq_transitive_unfolded with ( [--] (inject_Q ([1]:F))).
--      apply ing_min.
--     astepl ([0][-]inject_Q ([1]:F)).
--     Step_final ([0][-] ([1]:R_COrdField')).
--    unfold one_div_succ in |- *.
--    unfold Snring in |- *.
--    change (Four[*] ([1][/] nring M[+][1][//]nringS_ap_zero R_COrdField' M) [*]
--      (nring M[+][1]) [<] inject_Q q[*] (nring M[+][1])) in |- *.
--    rstepl (Four:R_COrdField').
--    astepr (inject_Q q[*]inject_Q (nring M[+][1])).
--     astepl (inject_Q (Four:F)).
--      astepr (inject_Q (q[*] (nring M[+][1]))).
--       apply ing_lt.
--       apply mult_cancel_less with (R := F) (z := [1][/] q[//]Hq').
--        apply recip_resp_pos.
--        assumption.
--       rstepl (Four[/] q[//]Hq').
--       rstepr (nring (R:=F) M[+][1]).
--       apply plus_cancel_less with (R := F) (z := [--] ([1]:F)).
--       rstepl ((Four[/] q[//]Hq') [-][1]).
--       rstepr (nring (R:=F) M).
--       exact HM.
--      apply ing_mult.
--     apply eq_symmetric_unfolded.
--     apply ing_nring.
--    apply mult_wd.
--     apply ing_eq.
--     apply eq_reflexive_unfolded.
--    apply eq_transitive_unfolded with (inject_Q (nring M) [+]inject_Q ([1]:F)).
--     apply ing_plus.
--    astepl (inject_Q (nring M) [+][1]).
--    astepl ([1][+]inject_Q (nring M)).
--    astepr ([1][+]nring (R:=R_COrdField') M).
--    apply plus_resp_eq.
--    apply eq_symmetric_unfolded.
--    apply ing_nring.
--   astepl (inject_Q (Four[*]one_div_succ (R:=F) (Nat.max M (Nat.max N1 N2)))).
--    apply expand_Q_R_2 with (x := a_ (Nat.max M (Nat.max N1 N2)))
--      (e := Four[*]one_div_succ (R:=F) (Nat.max M (Nat.max N1 N2)))
--        (N := T (a_ (Nat.max M (Nat.max N1 N2))) (Nat.max M (Nat.max N1 N2))).
--     apply mult_resp_pos.
--      apply pos_four.
--     apply one_div_succ_pos.
--    intros.
--    rstepl (one_div_succ (R:=F) (Nat.max M (Nat.max N1 N2))).
--    apply modulus_property_2.
--    assumption.
--   apply eq_transitive_unfolded with (inject_Q (Four:F) [*]inject_Q (one_div_succ (Nat.max M (Nat.max N1 N2)))).
--    apply ing_mult.
--   apply eq_transitive_unfolded with (Four[*]inject_Q (one_div_succ (Nat.max M (Nat.max N1 N2)))).
--    apply mult_wd.
--     apply eq_symmetric_unfolded.
--     apply ing_nring.
--    apply eq_reflexive_unfolded.
--   apply mult_wd.
--    apply eq_reflexive_unfolded.
--   unfold one_div_succ in |- *.
--   unfold Snring in |- *.
--   astepl (inject_Q ([1][/] _[//]nringS_ap_zero _ (Nat.max M (Nat.max N1 N2)))).
--   Step_final ([1][/] _[//]nringS_ap_zero R_COrdField' (Nat.max M (Nat.max N1 N2))).
--   apply eq_transitive_unfolded with (inject_Q ([1]:F) [/] _[//]nringS_ap_zero _ (Nat.max M (Nat.max N1 N2))).
--    apply eq_symmetric_unfolded.
--    apply ing_n.
--   apply div_wd.
--    exact ing_One.
--   apply eq_reflexive_unfolded.
--  apply AbsSmall_leEq_trans with (R := R_COrdField') (e1 := inject_Q q).
--   apply less_leEq; assumption.
--  apply expand_Q_R_2 with (x := LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa)) (e := q)
--    (N := Nat.max M (Nat.max N1 N2)).
--   assumption.
--  intros.
--  rstepl (q [/]EightNZ[+]q [/]EightNZ).
--  rstepr (CS_seq F (LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa)) m0[-]
--    CS_seq F (LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa)) N1[+]
--      (CS_seq F (LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa)) N1[-]
--        CS_seq F (LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa)) (Nat.max M (Nat.max N1 N2)))).
--  apply AbsSmall_plus.
--   unfold LimR_CauchySeq in |- *; simpl in |- *; apply HN1; eauto with arith.
--  apply AbsSmall_minus.
--  unfold LimR_CauchySeq in |- *; simpl in |- *; apply HN1; eauto with arith.
-- Qed.

-- Definition R_is_CReals := Build_is_CReals _
--  LimR_CauchySeq R_is_complete R_is_archemaedian.

-- Definition R_as_CReals := Build_CReals _ _ R_is_CReals.

def R_as_CReals : CReals (R := K) where
  crl_lim := _
  crl_proof := by {
    constructor
    · intros s
      apply R_is_complete
    · apply R_is_archimedean' F_is_archimedean}

-- Definition R_as_CReals := Build_CReals _ _ R_is_CReals.
