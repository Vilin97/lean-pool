/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.RNS.CoRNalgebraCOrdCauchy
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

-- Require Export CoRN.algebra.COrdCauchy.
-- Require Export CoRN.tactics.RingReflection.

-- (**
-- * The Field of Cauchy Sequences

-- In this chapter we will prove that whenever we start from an ordered
-- field [F], we can define a new ordered field of Cauchy sequences over [F].

-- %\begin{convention}% Let [F] be an ordered field.
-- %\end{convention}%
-- *)

-- Section Structure.

-- Variable F : COrdField.

variable [Field F] [LinearOrder F] [IsStrictOrderedRing F]


-- (**
-- ** Setoid Structure

-- [R_Set] is the setoid of Cauchy sequences over [F]; given two sequences
-- [x,y] over [F], we say that [x] is smaller than [y] if from some point
-- onwards [(y n) [-] (x n)] is greater than some fixed, positive
-- [e].  Apartness of two sequences means that one of them is smaller
-- than the other, equality is the negation of the apartness.
-- *)

-- Definition R_Set := CauchySeq F.

def R_Set (F: Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F] := CauchySeq' F

-- Section CSetoid_Structure.

-- Definition R_lt (x y : R_Set) := {N : nat |
--   {e : F | [0] [<] e | forall n, N <= n -> e [<=] CS_seq _ y n[-]CS_seq _ x n}}.

def R_lt (F: Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F] (x y : R_Set F) : Prop :=
    ∃ N : ℕ, ∃ e : F, (0 < e) ∧ ∀ n, N ≤ n → e ≤ (y.CS_seq n - x.CS_seq n)

-- Definition R_ap (x y : R_Set) := R_lt x y or R_lt y x.

def R_ap (F: Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F] (x y : R_Set F) : Prop :=
    R_lt F x y ∨ R_lt F y x

-- Definition R_eq (x y : R_Set) := Not (R_ap x y).

def R_eq (F: Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F] (x y : R_Set F) : Prop :=
    ¬ (R_lt F x y ∨ R_lt F y x)

-- Lemma R_lt_cotrans : cotransitive R_lt.
-- Proof.
--  red in |- *.
--  intros x y.
--  elim x; intros x_ px.
--  elim y; intros y_ py.
--  intros Hxy z.
--  elim z; intros z_ pz.
--  elim Hxy; intros N H.
--  elim H; clear Hxy H; intros e He HN.
--  simpl in HN.
--  set (e3 := e [/]ThreeNZ) in *.
--  cut ([0] [<] e3); [ intro He3 | unfold e3 in |- *; apply pos_div_three; auto ].
--  set (e6 := e [/]SixNZ) in *.
--  cut ([0] [<] e6); [ intro He6 | unfold e6 in |- *; apply pos_div_six; auto ].
--  set (e12 := e [/]TwelveNZ) in *.
--  cut ([0] [<] e12); [ intro He12 | unfold e12 in |- *; apply pos_div_twelve; auto ].
--  set (e24 := e [/]TwentyFourNZ) in *.
--  cut ([0] [<] e24); [ intro He24 | unfold e24 in |- *; apply pos_div_twentyfour; auto ].
--  elim (px e24 He24); intros Nx HNx.
--  elim (py e24 He24); intros Ny HNy.
--  elim (pz e24 He24); intros Nz HNz.
--  set (NN := Nat.max N (Nat.max Nx (Nat.max Ny Nz))) in *.
--  set (x0 := x_ NN) in *.
--  set (y0 := y_ NN) in *.
--  set (z0 := z_ NN) in *.
--  elim (less_cotransitive_unfolded _ (x0[+]e3) (y0[-]e3)) with z0.
--    intro Hyz.
--    left.
--    exists NN; exists e6; auto.
--    intros n Hn; simpl in |- *.
--    apply leEq_wdl with (e3[-] (e24[+]e24[+]e24[+]e24)).
--     2: unfold e3, e6, e12, e24 in |- *; rational.
--    apply leEq_transitive
--      with (e3[-] (z0[-]z_ Nz[+] (z_ Nz[-]z_ n) [+] (x_ n[-]x_ Nx) [+] (x_ Nx[-]x0))).
--     apply minus_resp_leEq_rht.
--     repeat apply plus_resp_leEq_both.
--        unfold z0 in |- *; elim (HNz NN); auto; unfold NN in |- *; eauto with arith.
--       apply shift_minus_leEq; apply shift_leEq_plus'.
--       unfold cg_minus in |- *; apply shift_plus_leEq'.
--       elim (HNz n); auto; apply Nat.le_trans with NN; auto; unfold NN in |- *; eauto with arith.
--      elim (HNx n); auto; apply Nat.le_trans with NN; auto; unfold NN in |- *; eauto with arith.
--     apply shift_minus_leEq; apply shift_leEq_plus'.
--     unfold cg_minus in |- *; apply shift_plus_leEq'.
--     unfold x0 in |- *; elim (HNx NN); auto; unfold NN in |- *; eauto with arith.
--    apply shift_minus_leEq.
--    rstepr (z0[-]x0).
--    apply shift_leEq_minus; astepl (x0[+]e3); apply less_leEq; auto.
--   intro Hzx.
--   right.
--   exists NN; exists e6; auto.
--   intros n Hn; simpl in |- *.
--   apply leEq_wdl with (e3[-] (e24[+]e24[+]e24[+]e24)).
--    2: unfold e3, e6, e12, e24 in |- *; rational.
--   apply leEq_transitive
--     with (e3[-] (z_ Nz[-]z0[+] (z_ n[-]z_ Nz) [+] (y_ Ny[-]y_ n) [+] (y0[-]y_ Ny))).
--    apply minus_resp_leEq_rht.
--    repeat apply plus_resp_leEq_both.
--       apply shift_minus_leEq; apply shift_leEq_plus'.
--       unfold cg_minus in |- *; apply shift_plus_leEq'.
--       unfold z0 in |- *; elim (HNz NN); auto; unfold NN in |- *; eauto with arith.
--      elim (HNz n); auto; apply Nat.le_trans with NN; auto; unfold NN in |- *; eauto with arith.
--     apply shift_minus_leEq; apply shift_leEq_plus'.
--     unfold cg_minus in |- *; apply shift_plus_leEq'.
--     elim (HNy n); auto; apply Nat.le_trans with NN; auto; unfold NN in |- *; eauto with arith.
--    unfold y0 in |- *; elim (HNy NN); auto; unfold NN in |- *; eauto with arith.
--   apply shift_minus_leEq.
--   rstepr (y0[-]z0).
--   apply shift_leEq_minus; apply shift_plus_leEq'; apply less_leEq; auto.
--  apply shift_less_minus.
--  astepl (x0[+] (e3[+]e3)); apply shift_plus_less'.
--  apply less_leEq_trans with e.
--   apply shift_plus_less.
--   apply less_wdl with ((e[-]e3) [/]TwoNZ).
--    2: unfold e3 in |- *; rational.
--   apply pos_div_two'.
--   apply shift_less_minus; astepl e3; unfold e3 in |- *; apply pos_div_three'; auto.
--  unfold x0, y0, NN in |- *; apply HN; eauto with arith.
-- Qed.

-- Cotransitivity of R_lt: if R_lt x y, then for any z, R_lt x z or R_lt z y.
theorem R_lt_cotrans (F : Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F] :
  ∀ x y z : R_Set F, R_lt F x y → (R_lt F x z ∨ R_lt F z y) := sorry

-- Lemma R_lt_cotrans : cotransitive R_lt.
-- Proof.
--  red in |- *.
--  intros x y.
--  elim x; intros x_ px.
--  elim y; intros y_ py.
--  intros Hxy z.
--  elim z; intros z_ pz.
--  elim Hxy; intros N H.
--  elim H; clear Hxy H; intros e He HN.
--  simpl in HN.
--  set (e3 := e [/]ThreeNZ) in *.
--  cut ([0] [<] e3); [ intro He3 | unfold e3 in |- *; apply pos_div_three; auto ].
--  set (e6 := e [/]SixNZ) in *.
--  cut ([0] [<] e6); [ intro He6 | unfold e6 in |- *; apply pos_div_six; auto ].
--  set (e12 := e [/]TwelveNZ) in *.
--  cut ([0] [<] e12); [ intro He12 | unfold e12 in |- *; apply pos_div_twelve; auto ].
--  set (e24 := e [/]TwentyFourNZ) in *.
--  cut ([0] [<] e24); [ intro He24 | unfold e24 in |- *; apply pos_div_twentyfour; auto ].
--  elim (px e24 He24); intros Nx HNx.
--  elim (py e24 He24); intros Ny HNy.
--  elim (pz e24 He24); intros Nz HNz.
--  set (NN := Nat.max N (Nat.max Nx (Nat.max Ny Nz))) in *.
--  set (x0 := x_ NN) in *.
--  set (y0 := y_ NN) in *.
--  set (z0 := z_ NN) in *.
--  elim (less_cotransitive_unfolded _ (x0[+]e3) (y0[-]e3)) with z0.
--    intro Hyz.
--    left.
--    exists NN; exists e6; auto.
--    intros n Hn; simpl in |- *.
--    apply leEq_wdl with (e3[-] (e24[+]e24[+]e24[+]e24)).
--     2: unfold e3, e6, e12, e24 in |- *; rational.
--    apply leEq_transitive
--      with (e3[-] (z0[-]z_ Nz[+] (z_ Nz[-]z_ n) [+] (x_ n[-]x_ Nx) [+] (x_ Nx[-]x0))).
--     apply minus_resp_leEq_rht.
--     repeat apply plus_resp_leEq_both.
--        unfold z0 in |- *; elim (HNz NN); auto; unfold NN in |- *; eauto with arith.
--       apply shift_minus_leEq; apply shift_leEq_plus'.
--       unfold cg_minus in |- *; apply shift_plus_leEq'.
--       elim (HNz n); auto; apply Nat.le_trans with NN; auto; unfold NN in |- *; eauto with arith.
--      elim (HNx n); auto; apply Nat.le_trans with NN; auto; unfold NN in |- *; eauto with arith.
--     apply shift_minus_leEq; apply shift_leEq_plus'.
--     unfold cg_minus in |- *; apply shift_plus_leEq'.
--     unfold x0 in |- *; elim (HNx NN); auto; unfold NN in |- *; eauto with arith.
--    apply shift_minus_leEq.
--    rstepr (z0[-]x0).
--    apply shift_leEq_minus; astepl (x0[+]e3); apply less_leEq; auto.
--   intro Hzx.
--   right.
--   exists NN; exists e6; auto.
--   intros n Hn; simpl in |- *.
--   apply leEq_wdl with (e3[-] (e24[+]e24[+]e24[+]e24)).
--    2: unfold e3, e6, e12, e24 in |- *; rational.
--   apply leEq_transitive
--     with (e3[-] (z_ Nz[-]z0[+] (z_ n[-]z_ Nz) [+] (y_ Ny[-]y_ n) [+] (y0[-]y_ Ny))).
--    apply minus_resp_leEq_rht.
--    repeat apply plus_resp_leEq_both.
--       apply shift_minus_leEq; apply shift_leEq_plus'.
--       unfold cg_minus in |- *; apply shift_plus_leEq'.
--       unfold z0 in |- *; elim (HNz NN); auto; unfold NN in |- *; eauto with arith.
--      elim (HNz n); auto; apply Nat.le_trans with NN; auto; unfold NN in |- *; eauto with arith.
--     apply shift_minus_leEq; apply shift_leEq_plus'.
--     unfold cg_minus in |- *; apply shift_plus_leEq'.
--     elim (HNy n); auto; apply Nat.le_trans with NN; auto; unfold NN in |- *; eauto with arith.
--    unfold y0 in |- *; elim (HNy NN); auto; unfold NN in |- *; eauto with arith.
--   apply shift_minus_leEq.
--   rstepr (y0[-]z0).
--   apply shift_leEq_minus; apply shift_plus_leEq'; apply less_leEq; auto.
--  apply shift_less_minus.
--  astepl (x0[+] (e3[+]e3)); apply shift_plus_less'.
--  apply less_leEq_trans with e.
--   apply shift_plus_less.
--   apply less_wdl with ((e[-]e3) [/]TwoNZ).
--    2: unfold e3 in |- *; rational.
--   apply pos_div_two'.
--   apply shift_less_minus; astepl e3; unfold e3 in |- *; apply pos_div_three'; auto.
--  unfold x0, y0, NN in |- *; apply HN; eauto with arith.
-- Qed.

-- Lemma R_ap_cotrans : cotransitive R_ap.
-- Proof.
--  red in |- *; intros x y Hxy z.
--  elim Hxy; intro H; elim (R_lt_cotrans _ _ H z); unfold R_ap in |- *; auto.
-- Qed.

-- Cotransitivity of R_ap: if R_ap x y, then for any z, R_ap x z or R_ap z y.
theorem R_ap_cotrans (F : Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F] :
    ∀ x y z : R_Set F, R_ap F x y → (R_ap F x z ∨ R_ap F z y) := by
    intros x y z Hxy
    cases' Hxy with Hxy_lt Hxy_lt
    · cases' R_lt_cotrans F x y z Hxy_lt with Hxz Hzy
      · left; left; exact Hxz
      · right; left; exact Hzy
    · cases' R_lt_cotrans F y x z Hxy_lt with Hyz Hzx
      · right; right; exact Hyz
      · left; right; exact Hzx

-- Lemma R_ap_symmetric : Csymmetric R_ap.
-- Proof.
--  red in |- *; intros x y Hxy.
--  elim Hxy; unfold R_ap in |- *; auto.
-- Qed.

-- Symmetry of R_ap: if R_ap x y then R_ap y x.
theorem R_ap_symmetric (F : Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F] :
    ∀ x y : R_Set F, R_ap F x y → R_ap F y x := by
    intros x y Hxy
    cases Hxy with
    | inl H => exact Or.inr H
    | inr H => exact Or.inl H

-- Lemma R_lt_irreflexive : irreflexive R_lt.
-- Proof.
--  red in |- *; intros x Hx.
--  elim Hx; intros N HN.
--  elim HN; clear Hx HN; intros e He HN.
--  apply (ap_irreflexive_unfolded _ (x N)).
--  apply less_imp_ap.
--  apply less_leEq_trans with (x N[+]e).
--   astepl (x N[+][0]); apply plus_resp_less_lft; auto.
--  apply shift_plus_leEq'; auto with arith.
-- Qed.

-- Lemma R_lt_irreflexive : irreflexive R_lt.
-- Proof.
--  red in |- *; intros x Hx.
--  elim Hx; intros N HN.
--  elim HN; clear Hx HN; intros e He HN.
--  apply (ap_irreflexive_unfolded _ (x N)).
--  apply less_imp_ap.
--  apply less_leEq_trans with (x N[+]e).
--   astepl (x N[+][0]); apply plus_resp_less_lft; auto.
--  apply shift_plus_leEq'; auto with arith.
-- Qed.

-- Lemma R_ap_irreflexive : irreflexive R_ap.
-- Proof.
--  red in |- *; intros x Hx.
--  elim (R_lt_irreflexive x).
--  elim Hx; auto.
-- Qed.

-- Lemma R_ap_irreflexive : irreflexive R_ap.
-- Proof.
--  red in |- *; intros x Hx.
--  elim (R_lt_irreflexive x).
--  elim Hx; auto.
-- Qed.

-- Lemma R_ap_eq_tight : tight_apart R_eq R_ap.
-- Proof.
--  split; auto.
-- Qed.

-- Definition R_CSetoid : CSetoid.
-- Proof.
--  apply Build_CSetoid with R_Set R_eq R_ap.
--  split.
--     exact R_ap_irreflexive.
--    exact R_ap_symmetric.
--   exact R_ap_cotrans.
--  exact R_ap_eq_tight.
-- Defined.

-- End CSetoid_Structure.

-- Section Group_Structure.

-- (**
-- ** Group Structure
-- The group structure is just the expected one; the lemmas which
-- are specifically proved are just the necessary ones to get the group axioms.
-- *)

-- Definition R_plus (x y : R_CSetoid) : R_CSetoid :=
--   Build_CauchySeq _ _ (CS_seq_plus F _ _ (CS_proof _ x) (CS_proof _ y)).

-- Definition R_zero := Build_CauchySeq _ _ (CS_seq_const F [0]).

-- Lemma R_plus_lft_ext : forall x y z, R_plus x z [#] R_plus y z -> x [#] y.
-- Proof.
--  intros x y z Hxy.
--  elim Hxy; clear Hxy; intro H; [ left | right ]; elim H; intros N HN; elim HN;
--    clear H HN; intros e He HN; exists N; exists e; auto; intros n Hn; simpl in HN.
--   rstepr (CS_seq _ y n[+]CS_seq _ z n[-] (CS_seq _ x n[+]CS_seq _ z n)); auto.
--  rstepr (CS_seq _ x n[+]CS_seq _ z n[-] (CS_seq _ y n[+]CS_seq _ z n)); auto.
-- Qed.

-- Lemma R_plus_assoc : associative R_plus.
-- Proof.
--  intros x y z Hap.
--  elim Hap; clear Hap; intro H; elim H; intros N HN; elim HN; clear H HN;
--    intros e He HN; simpl in HN; apply (less_irreflexive_unfolded _ e).
--   apply leEq_less_trans with (CS_seq _ x N[+]CS_seq _ y N[+]CS_seq _ z N[-]
--     (CS_seq _ x N[+] (CS_seq _ y N[+]CS_seq _ z N))); auto.
--   rstepl ([0]:F); auto.
--  apply leEq_less_trans with (CS_seq _ x N[+] (CS_seq _ y N[+]CS_seq _ z N) [-]
--    (CS_seq _ x N[+]CS_seq _ y N[+]CS_seq _ z N)); auto.
--  rstepl ([0]:F); auto.
-- Qed.

-- Lemma R_zero_lft_unit : forall x, R_plus R_zero x [=] x.
-- Proof.
--  intro x; intro x_ap.
--  apply (R_lt_irreflexive x).
--  elim x_ap; clear x_ap; intro x_lt; elim x_lt; intros N H; elim H;
--    clear x_lt H; intros e He HN; exists N; exists e; auto; simpl in HN; intros n Hn.
--   astepr (CS_seq _ x n[-] ([0][+]CS_seq _ x n)); auto.
--  astepr ([0][+]CS_seq _ x n[-]CS_seq _ x n); auto.
-- Qed.

-- Lemma R_plus_comm : forall x y, R_plus x y [=] R_plus y x.
-- Proof.
--  intros x y Hxy.
--  elim Hxy; clear Hxy; intro H; elim H; intros N HN; elim HN; clear H HN;
--    intros e He HN; simpl in HN; apply (less_irreflexive_unfolded _ e).
--   apply leEq_less_trans with (CS_seq _ y N[+]CS_seq _ x N[-] (CS_seq _ x N[+]CS_seq _ y N)); auto.
--   rstepl ([0]:F); auto.
--  apply leEq_less_trans with (CS_seq _ x N[+]CS_seq _ y N[-] (CS_seq _ y N[+]CS_seq _ x N)); auto.
--  rstepl ([0]:F); auto.
-- Qed.

-- Definition R_inv (x : R_CSetoid) : R_CSetoid :=
--   Build_CauchySeq _ _ (CS_seq_inv F _ (CS_proof _ x)).

-- Lemma R_inv_is_inv : forall x, R_plus x (R_inv x) [=] R_zero.
-- Proof.
--  intro x; intro x_ap.
--  apply (R_lt_irreflexive R_zero).
--  elim x_ap; clear x_ap; intro x_lt; elim x_lt; intros N H; elim H;
--    clear x_lt H; intros e He HN; exists N; exists e; auto; simpl in HN; intros n Hn.
--   simpl in |- *; astepr ([0][-] (CS_seq _ x n[+][--] (CS_seq _ x n))); auto.
--  simpl in |- *; astepr (CS_seq _ x n[+][--] (CS_seq _ x n) [-][0]); auto.
-- Qed.

-- Lemma R_inv_ext : un_op_strext _ R_inv.
-- Proof.
--  intros x y Hxy.
--  elim Hxy; clear Hxy; intro x_lt; [ right | left ]; elim x_lt; intros N H;
--    elim H; clear x_lt H; intros e He HN; exists N; exists e; auto; simpl in HN; intros n Hn.
--   rstepr ([--] (CS_seq _ y n) [-][--] (CS_seq _ x n)); auto.
--  rstepr ([--] (CS_seq _ x n) [-][--] (CS_seq _ y n)); auto.
-- Qed.

-- Definition Rinv : CSetoid_un_op R_CSetoid.
-- Proof.
--  red in |- *.
--  apply Build_CSetoid_un_op with R_inv.
--  exact R_inv_ext.
-- Defined.

-- Definition R_CAbGroup : CAbGroup.
-- Proof.
--  apply Build_CAbGroup' with R_CSetoid R_zero R_plus Rinv.
--      exact R_plus_lft_ext.
--     exact R_zero_lft_unit.
--    exact R_plus_comm.
--   exact R_plus_assoc.
--  exact R_inv_is_inv.
-- Defined.

-- End Group_Structure.

-- Section Ring_Structure.

-- (**
-- ** Ring Structure
-- Same comments as previously.
-- *)

-- Definition R_mult (x y : R_CAbGroup) : R_CAbGroup :=
--   Build_CauchySeq _ _ (CS_seq_mult F _ _ (CS_proof _ x) (CS_proof _ y)).
-- Definition R_one : R_CAbGroup := Build_CauchySeq _ _ (CS_seq_const F [1]).

-- Lemma R_one_ap_zero : R_one [#] [0].
-- Proof.
--  right; exists 0; exists ([1]:F).
--   apply pos_one.
--  intros; simpl in |- *; astepr ([1]:F); apply leEq_reflexive.
-- Qed.

-- Lemma R_mult_dist_plus : forall x y z, R_mult x (y[+]z) [=] R_mult x y[+]R_mult x z.
-- Proof.
--  intros x y z H.
--  elim H; intro Hlt; elim Hlt; intros N HN; elim HN; clear H Hlt HN;
--    intros e He HN; simpl in HN; apply (less_irreflexive_unfolded _ e).
--   eapply leEq_less_trans.
--    apply (HN N (le_n _)).
--   rstepl ([0]:F); auto.
--  eapply leEq_less_trans.
--   apply (HN N (le_n _)).
--  rstepl ([0]:F); auto.
-- Qed.

-- Lemma R_mult_dist_minus : forall x y z, R_mult x (y[-]z) [=] R_mult x y[-]R_mult x z.
-- Proof.
--  intros x y z H.
--  elim H; intro Hlt; elim Hlt; intros N HN; elim HN; clear H Hlt HN;
--    intros e He HN; simpl in HN; apply (less_irreflexive_unfolded _ e).
--   eapply leEq_less_trans.
--    apply (HN N (le_n _)).
--   rstepl ([0]:F); auto.
--  eapply leEq_less_trans.
--   apply (HN N (le_n _)).
--  rstepl ([0]:F); auto.
-- Qed.

-- Lemma R_one_rht_unit : forall x, R_mult x R_one [=] x.
-- Proof.
--  intro x; intro x_ap.
--  apply (R_lt_irreflexive x).
--  elim x_ap; clear x_ap; intro x_lt; elim x_lt; intros N H; elim H;
--    clear x_lt H; intros e He HN; exists N; exists e; auto; simpl in HN; intros n Hn.
--   astepr (CS_seq _ x n[-]CS_seq _ x n[*][1]); auto.
--  astepr (CS_seq _ x n[*][1][-]CS_seq _ x n); auto.
-- Qed.

-- Lemma R_mult_comm : forall x y, R_mult x y [=] R_mult y x.
-- Proof.
--  intros x y Hxy.
--  elim Hxy; clear Hxy; intro H; elim H; intros N HN; elim HN; clear H HN;
--    intros e He HN; simpl in HN; apply (less_irreflexive_unfolded _ e).
--   apply leEq_less_trans with (CS_seq _ y N[*]CS_seq _ x N[-]CS_seq _ x N[*]CS_seq _ y N); auto.
--   rstepl ([0]:F); auto.
--  apply leEq_less_trans with (CS_seq _ x N[*]CS_seq _ y N[-]CS_seq _ y N[*]CS_seq _ x N); auto.
--  rstepl ([0]:F); auto.
-- Qed.

-- Lemma R_mult_ap_zero' : forall x y, R_mult x y [#] [0] -> x [#] [0].
-- Proof.
--  intros x y Hxy.
--  elim (CS_seq_bounded _ (CS_seq _ y) (CS_proof _ y)); intros K HK Hy; elim Hy;
--    clear Hy; intros Ny HNY.
--  set (z := Build_CauchySeq _ _ (CS_seq_mult _ _ _ (CS_seq_const _ (Two[*]K)) (CS_proof _ x))
--    :R_CAbGroup) in *.
--  elim (ap_cotransitive_unfolded _ _ _ Hxy z); intro Hap; elim Hap; intro Hlt;
--    elim Hlt; intros N HN; elim HN; clear Hap Hlt HN; intros e He HN.
--     right.
--     cut (forall n : nat, Ny <= n -> [0] [<] Two[*]K[-]CS_seq _ y n); [ intro Hy' | intros n Hn ].
--      set (KK := e[/] _[//]mult_resp_ap_zero _ _ _ (three_ap_zero _) (pos_ap_zero _ _ HK)) in *.
--      exists (Nat.max N Ny); exists KK.
--       unfold KK in |- *; apply div_resp_pos; auto.
--       apply mult_resp_pos; auto; apply pos_three.
--      intros; simpl in |- *; unfold KK in |- *.
--      cut (N <= n); [ intro Hn | apply Nat.le_trans with (Nat.max N Ny); auto with arith ].
--      cut (Ny <= n); [ intro Hn' | apply Nat.le_trans with (Nat.max N Ny); auto with arith ].
--      apply leEq_transitive with (e[/] _[//]pos_ap_zero _ _ (Hy' n Hn')).
--       apply mult_cancel_leEq with ([1][/] _[//]pos_ap_zero _ _ He).
--        apply recip_resp_pos; auto.
--       rstepl ([1][/] _[//]mult_resp_ap_zero _ _ _ (three_ap_zero _) (pos_ap_zero _ _ HK)).
--       rstepr ([1][/] _[//]pos_ap_zero _ _ (Hy' n Hn')).
--       apply recip_resp_leEq; auto.
--       unfold cg_minus in |- *; apply shift_plus_leEq'; rstepr ([--][--]K).
--       apply inv_resp_leEq; elim (HNY n); auto.
--      apply shift_div_leEq; auto.
--      eapply leEq_wdr.
--       apply (HN n); auto.
--      simpl in |- *; rational.
--     apply shift_zero_less_minus; apply leEq_less_trans with K.
--      elim (HNY n); auto.
--     astepl ([0][+]K); astepr (K[+]K); apply plus_resp_less_rht; auto.
--    left.
--    cut (forall n : nat, Ny <= n -> [0] [<] Two[*]K[-]CS_seq _ y n); [ intro Hy' | intros n Hn ].
--     set (KK := e[/] _[//]mult_resp_ap_zero _ _ _ (three_ap_zero _) (pos_ap_zero _ _ HK)) in *.
--     exists (Nat.max N Ny); exists KK.
--      unfold KK in |- *; apply div_resp_pos; auto.
--      apply mult_resp_pos; auto; apply pos_three.
--     intros; simpl in |- *; unfold KK in |- *.
--     cut (N <= n); [ intro Hn | apply Nat.le_trans with (Nat.max N Ny); auto with arith ].
--     cut (Ny <= n); [ intro Hn' | apply Nat.le_trans with (Nat.max N Ny); auto with arith ].
--     apply leEq_transitive with (e[/] _[//]pos_ap_zero _ _ (Hy' n Hn')).
--      apply mult_cancel_leEq with ([1][/] _[//]pos_ap_zero _ _ He).
--       apply recip_resp_pos; auto.
--      rstepl ([1][/] _[//]mult_resp_ap_zero _ _ _ (three_ap_zero _) (pos_ap_zero _ _ HK)).
--      rstepr ([1][/] _[//]pos_ap_zero _ _ (Hy' n Hn')).
--      apply recip_resp_leEq; auto.
--      unfold cg_minus in |- *; apply shift_plus_leEq'; rstepr ([--][--]K).
--      apply inv_resp_leEq; elim (HNY n); auto.
--     apply shift_div_leEq; auto.
--     eapply leEq_wdr.
--      apply (HN n); auto.
--     simpl in |- *; rational.
--    apply shift_zero_less_minus; apply leEq_less_trans with K.
--     elim (HNY n); auto.
--    astepl ([0][+]K); astepr (K[+]K); apply plus_resp_less_rht; auto.
--   left.
--   set (KK := e[/] _[//]mult_resp_ap_zero _ _ _ (two_ap_zero _) (pos_ap_zero _ _ HK)) in *.
--   exists N; exists KK.
--    unfold KK in |- *; apply div_resp_pos; auto.
--    apply mult_resp_pos; auto; apply pos_two.
--   intros; simpl in |- *; unfold KK in |- *.
--   apply shift_div_leEq.
--    apply mult_resp_pos; auto; apply pos_two.
--   eapply leEq_wdr.
--    apply (HN n H).
--   simpl in |- *; rational.
--  right.
--  set (KK := e[/] _[//]mult_resp_ap_zero _ _ _ (two_ap_zero _) (pos_ap_zero _ _ HK)) in *.
--  exists N; exists KK.
--   unfold KK in |- *; apply div_resp_pos; auto.
--   apply mult_resp_pos; auto; apply pos_two.
--  intros; simpl in |- *; unfold KK in |- *.
--  apply shift_div_leEq.
--   apply mult_resp_pos; auto; apply pos_two.
--  eapply leEq_wdr.
--   apply (HN n H).
--  simpl in |- *; rational.
-- Qed.

-- Lemma R_mult_lft_ext : forall x y z, R_mult x z [#] R_mult y z -> x [#] y.
-- Proof.
--  intros x y z Hxy.
--  apply zero_minus_apart.
--  apply R_mult_ap_zero' with z.
--  apply ap_wdl_unfolded with (R_mult x z[-]R_mult y z).
--   apply minus_ap_zero; auto.
--  apply eq_symmetric_unfolded.
--  eapply eq_transitive_unfolded.
--   apply R_mult_comm.
--  eapply eq_transitive_unfolded.
--   apply R_mult_dist_minus.
--  apply cg_minus_wd; apply R_mult_comm.
-- Qed.

-- Lemma R_mult_rht_ext : forall x y z, R_mult x y [#] R_mult x z -> y [#] z.
-- Proof.
--  intros x y z Hxy.
--  apply R_mult_lft_ext with x.
--  eapply ap_wdl_unfolded.
--   eapply ap_wdr_unfolded.
--    apply Hxy.
--   apply R_mult_comm.
--  apply R_mult_comm.
-- Qed.

-- Lemma R_mult_strext : bin_op_strext _ R_mult.
-- Proof.
--  red in |- *; red in |- *.
--  intros x y a b Hap.
--  elim (ap_cotransitive_unfolded _ _ _ Hap (R_mult x b)); intro H.
--   right; apply R_mult_rht_ext with x; auto.
--  left; apply R_mult_lft_ext with b; auto.
-- Qed.

-- Definition Rmult : CSetoid_bin_op R_CAbGroup.
-- Proof.
--  red in |- *.
--  apply Build_CSetoid_bin_fun with R_mult.
--  apply R_mult_strext.
-- Defined.

-- Lemma R_mult_assoc : associative Rmult.
-- Proof.
--  intros x y z Hap.
--  elim Hap; clear Hap; intro H; elim H; intros N HN; elim HN; clear H HN;
--    intros e He HN; simpl in HN; apply (less_irreflexive_unfolded _ e).
--   apply leEq_less_trans with (CS_seq _ x N[*]CS_seq _ y N[*]CS_seq _ z N[-]
--     CS_seq _ x N[*] (CS_seq _ y N[*]CS_seq _ z N)); auto.
--   rstepl ([0]:F); auto.
--  apply leEq_less_trans with (CS_seq _ x N[*] (CS_seq _ y N[*]CS_seq _ z N) [-]
--    CS_seq _ x N[*]CS_seq _ y N[*]CS_seq _ z N); auto.
--  rstepl ([0]:F); auto.
-- Qed.

-- Lemma R_one_lft_unit : forall x, R_mult R_one x [=] x.
-- Proof.
--  intro.
--  eapply eq_transitive_unfolded.
--   apply R_mult_comm.
--  apply R_one_rht_unit.
-- Qed.

-- Definition R_CRing : CRing.
-- Proof.
--  apply Build_CRing with R_CAbGroup R_one Rmult.
--  apply Build_is_CRing with R_mult_assoc.
--     apply Build_is_CMonoid.
--      exact R_one_rht_unit.
--     exact R_one_lft_unit.
--    exact R_mult_comm.
--   exact R_mult_dist_plus.
--  exact R_one_ap_zero.
-- Defined.

-- End Ring_Structure.

-- Add Ring R_CRing: (CRing_Ring R_CRing).

-- Section Field_Structure.

-- (**
-- ** Field Structure
-- For the field structure, it is technically easier to first prove
-- that our ring is actually an integral domain.  The rest then follows
-- quite straightforwardly.
-- *)

-- Lemma R_integral_domain :
--  forall x y : R_CRing, x [#] [0] -> y [#] [0] -> x[*]y [#] [0].
-- Proof.
--  intros x y Hx Hy.
--  elim Hx; intro Hlt; elim Hlt; intros Nx HN; elim HN; clear Hx Hlt HN;
--    intros ex Hex HNx; simpl in HNx; elim Hy; intro Hlt;
--      elim Hlt; intros Ny HN; elim HN; clear Hy Hlt HN; intros ey Hey HNy; simpl in HNy.
--     right.
--     exists (Nat.max Nx Ny); exists (ex[*]ey).
--      apply mult_resp_pos; auto.
--     intros; simpl in |- *; rstepr ([--] (CS_seq _ x n) [*][--] (CS_seq _ y n)).
--     apply mult_resp_leEq_both; try (apply less_leEq; assumption).
--      astepr ([0][-]CS_seq _ x n); eauto with arith.
--     astepr ([0][-]CS_seq _ y n); eauto with arith.
--    left.
--    exists (Nat.max Nx Ny); exists (ex[*]ey).
--     apply mult_resp_pos; auto.
--    intros; simpl in |- *; rstepr ([--] (CS_seq _ x n) [*]CS_seq _ y n).
--    apply mult_resp_leEq_both; try (apply less_leEq; assumption).
--     astepr ([0][-]CS_seq _ x n); eauto with arith.
--    astepr (CS_seq _ y n[-][0]); eauto with arith.
--   left.
--   exists (Nat.max Nx Ny); exists (ex[*]ey).
--    apply mult_resp_pos; auto.
--   intros; simpl in |- *; rstepr (CS_seq _ x n[*][--] (CS_seq _ y n)).
--   apply mult_resp_leEq_both; try (apply less_leEq; assumption).
--    astepr (CS_seq _ x n[-][0]); eauto with arith.
--   astepr ([0][-]CS_seq _ y n); eauto with arith.
--  right.
--  exists (Nat.max Nx Ny); exists (ex[*]ey).
--   apply mult_resp_pos; auto.
--  intros; simpl in |- *; astepr (CS_seq _ x n[*]CS_seq _ y n).
--  apply mult_resp_leEq_both; try (apply less_leEq; assumption).
--   astepr (CS_seq _ x n[-][0]); eauto with arith.
--  astepr (CS_seq _ y n[-][0]); eauto with arith.
-- Qed.

-- Definition R_recip : forall x : R_CRing, x [#] [0] -> R_CRing.
--  intros x Hx; elim Hx; intro Hlt; elim Hlt; intros N HN; elim HN; clear Hx Hlt HN; intros e He HN.
-- Proof.
--   cut (forall n : nat, N <= n -> e [<=] [--] (CS_seq _ x n)); intros.
--    apply (Build_CauchySeq _ _ (CS_seq_inv _ _
--      (CS_seq_recip _ _ (CS_seq_inv _ _ (CS_proof _ x)) e He N H))).
--   astepr ([0][-]CS_seq _ x n); simpl in HN; auto.
--  cut (forall n : nat, N <= n -> e [<=] CS_seq _ x n); intros.
--   apply (Build_CauchySeq _ _ (CS_seq_recip _ _ (CS_proof _ x) e He N H)).
--  astepr (CS_seq _ x n[-][0]); simpl in HN; auto.
-- Defined.

-- Lemma R_recip_inverse : forall x x_, x[*]R_recip x x_ [=] [1].
-- Proof.
--  intros x Hx; elim Hx; intro Hlt; elim Hlt; intros N HN; elim HN;
--    clear Hx Hlt HN; simpl in |- *; intros e He HN Hap;
--      elim Hap; intro Hlt; elim Hlt; intros K HK; elim HK;
--        clear Hap Hlt HK; intros d Hd HM; simpl in HM.
--     apply (less_irreflexive_unfolded _ d).
--     apply leEq_less_trans with ([0]:F); auto.
--     simpl in HM.
--     eapply leEq_wdr.
--      apply (HM (Nat.max K N)); auto with arith.
--     unfold CS_seq_recip_seq in |- *; elim lt_le_dec; intro.
--      exfalso; apply Nat.le_ngt with N (Nat.max K N); auto with arith.
--     simpl in |- *; rational.
--    apply (less_irreflexive_unfolded _ d).
--    apply leEq_less_trans with ([0]:F); auto.
--    simpl in HM.
--    eapply leEq_wdr.
--     apply (HM (Nat.max K N)); auto with arith.
--    unfold CS_seq_recip_seq in |- *; elim lt_le_dec; intro.
--     exfalso; apply Nat.le_ngt with N (Nat.max K N); auto with arith.
--    simpl in |- *; rational.
--   apply (less_irreflexive_unfolded _ d).
--   apply leEq_less_trans with ([0]:F); auto.
--   simpl in HM.
--   eapply leEq_wdr.
--    apply (HM (Nat.max K N)); auto with arith.
--   unfold CS_seq_recip_seq in |- *; elim lt_le_dec; intro.
--    exfalso; apply Nat.le_ngt with N (Nat.max K N); auto with arith.
--   simpl in |- *; rational.
--  apply (less_irreflexive_unfolded _ d).
--  apply leEq_less_trans with ([0]:F); auto.
--  simpl in HM.
--  eapply leEq_wdr.
--   apply (HM (Nat.max K N)); auto with arith.
--  unfold CS_seq_recip_seq in |- *; elim lt_le_dec; intro.
--   exfalso; apply Nat.le_ngt with N (Nat.max K N); auto with arith.
--  simpl in |- *; rational.
-- Qed.

-- Lemma R_recip_strext : forall x y x_ y_, R_recip x x_ [#] R_recip y y_ -> x [#] y.
-- Proof.
--  intros.
--  apply zero_minus_apart.
--  apply ap_wdl with (x[*]y[*] (R_recip y y_[-]R_recip x x_)).
--   apply R_integral_domain.
--    apply R_integral_domain; auto.
--   apply minus_ap_zero; apply ap_symmetric_unfolded; auto.
--  stepl (y[*]R_recip y y_[*]x[-]x[*]R_recip x x_[*]y). 2: unfold cg_minus; ring.
--  stepr ([1][*]x[-][1][*]y). 2: unfold cg_minus; ring.
--  apply cg_minus_wd; apply mult_wdl; apply R_recip_inverse.
-- Qed.

-- Lemma R_recip_inverse' : forall x x_, R_recip x x_[*]x [=] [1].
-- Proof.
--  intros.
--  astepl (x[*]R_recip x x_).
--  apply R_recip_inverse.
-- Qed.

-- Definition R_CField : CField.
-- Proof.
--  apply Build_CField with R_CRing R_recip.
--   split.
--    apply R_recip_inverse.
--   apply R_recip_inverse'.
--  exact R_recip_strext.
-- Defined.

-- End Field_Structure.

-- Section Order.

-- (**
-- ** Order Structure
-- Finally, we extend the field structure with the ordering we
-- defined at the beginning.
-- *)

-- Lemma R_lt_strext : Crel_strext R_CSetoid R_lt.
-- Proof.
--  intros x a y b Hxy.
--  elim (R_lt_cotrans x y Hxy a); intro H.
--   right; left; left; auto.
--  elim (R_lt_cotrans a y H b); intro H'.
--   left; auto.
--  right; right; right; auto.
-- Qed.

-- Definition Rlt : CCSetoid_relation R_CField.
-- Proof.
--  apply Build_CCSetoid_relation with R_lt.
--  exact R_lt_strext.
-- Defined.

-- Lemma Rlt_transitive : Ctransitive Rlt.
-- Proof.
--  intros x y z H H'.
--  simpl in H, H'.
--  elim H; intros N1 HN1; elim HN1; clear H HN1; intros e1 He1 HN1.
--  elim H'; intros N2 HN2; elim HN2; clear H' HN2; intros e2 He2 HN2.
--  exists (Nat.max N1 N2); exists (e1[+]e2).
--   apply plus_resp_pos; auto.
--  intros; rstepr (CS_seq _ y n[-]CS_seq _ x n[+] (CS_seq _ z n[-]CS_seq _ y n)).
--  apply plus_resp_leEq_both; eauto with arith.
-- Qed.

-- Lemma Rlt_strict : strictorder Rlt.
-- Proof.
--  apply Build_strictorder.
--   exact Rlt_transitive.
--  intros x y H H'.
--  apply R_lt_irreflexive with x.
--  apply Rlt_transitive with y; auto.
-- Qed.

-- Lemma R_plus_resp_lt : forall x y, Rlt x y -> forall z, Rlt (x[+]z) (y[+]z).
-- Proof.
--  intros x y Hxy z.
--  elim Hxy; intros N HN; elim HN; clear Hxy HN; intros e He HN; exists N; exists e; auto; intros n Hn.
--  simpl in |- *; rstepr (CS_seq _ y n[-]CS_seq _ x n); auto.
-- Qed.

-- Lemma R_mult_resp_lt : forall x y, Rlt [0] x -> Rlt [0] y -> Rlt [0] (x[*]y).
-- Proof.
--  intros x y Hx Hy.
--  elim Hx; intros Nx HN; elim HN; clear Hx HN; intros ex Hex HNx; simpl in HNx;
--    elim Hy; intros Ny HN; elim HN; clear Hy HN; intros ey Hey HNy; simpl in HNy.
--  exists (Nat.max Nx Ny); exists (ex[*]ey).
--   apply mult_resp_pos; auto.
--  intros; simpl in |- *; astepr (CS_seq _ x n[*]CS_seq _ y n).
--  apply mult_resp_leEq_both; try (apply less_leEq; assumption).
--   astepr (CS_seq _ x n[-][0]); eauto with arith.
--  astepr (CS_seq _ y n[-][0]); eauto with arith.
-- Qed.

-- Definition R_COrdField : COrdField.
-- Proof.
--  apply Build_COrdField with R_CField Rlt (default_leEq _ Rlt) (default_greater _ Rlt) (default_grEq _ (default_leEq _ Rlt)).
--  apply Build_is_COrdField; try solve [unfold Iff; tauto].
--     exact Rlt_strict.
--    exact R_plus_resp_lt.
--   exact R_mult_resp_lt.
--  split; auto.
-- Defined.

-- End Order.

-- (**
-- ** Other Results
-- Auxiliary characterizations of the main relations on [R_Set].
-- *)

-- Section Auxiliary.

-- Lemma Rlt_alt_1 : forall x y : R_Set, {e : F | [0] [<] e |
--  {N : nat | forall m, N <= m -> e [<=] CS_seq F y m[-]CS_seq F x m}} -> Rlt x y.
-- Proof.
--  intros x y H.
--  case H.
--  intro e1.
--  intros H1 H2.
--  case H2.
--  intro N1.
--  intros H3.
--  unfold Rlt in |- *.
--  exists N1.
--  exists (e1 [/]TwoNZ).
--   apply pos_div_two.
--   assumption.
--  intros.
--  apply leEq_transitive with e1.
--   apply mult_cancel_leEq with (Two:F).
--    apply pos_two.
--   rstepl (e1[+] ([0]:F)).
--   rstepr (e1[+]e1).
--   apply plus_resp_leEq_lft.
--   apply less_leEq; assumption.
--  apply H3.
--  assumption.
-- Qed.

-- Lemma Rlt_alt_2 : forall x y : R_Set, Rlt x y -> {e : F | [0] [<] e |
--  {N : nat | forall m, N <= m -> e [<=] CS_seq F y m[-]CS_seq F x m}}.
-- Proof.
--  intros x y H.
--  unfold Rlt in H.
--  case H.
--  intros N H2.
--  case H2.
--  intros e H1 H0.
--  exists e.
--   assumption.
--  exists N.
--  auto.
-- Qed.

-- Lemma R_ap_alt_1 : forall x y : R_CSetoid, x [#] y -> {e : F | [0] [<] e |
--  {N : nat | forall m, N <= m -> AbsBig e (CS_seq F x m[-]CS_seq F y m)}}.
-- Proof.
--  intros x y H.
--  case H; intros H0.
--   case H0; intros N1 HN1.
--   case HN1; intros e1 H2 H31.
--   exists e1.
--    assumption.
--   exists N1.
--   split.
--    assumption.
--   right.
--   apply inv_cancel_leEq.
--   rstepl e1.
--   rstepr (CS_seq F y m[-]CS_seq F x m).
--   apply H31.
--   assumption.
--  case H0; intros N1 HN1.
--  case HN1; intros e1 H2 H31.
--  exists e1.
--   assumption.
--  exists N1.
--  split; try left; auto.
-- Qed.

-- Lemma Eq_alt_1 : forall (x y : R_Set) (e : F), [0] [<] e ->
--  Not {N : nat | forall m,   N <= m -> AbsBig (e [/]FourNZ) (CS_seq F x m[-]CS_seq F y m)} ->
--  {N : nat | forall m, N <= m -> AbsSmall e (CS_seq F x m[-]CS_seq F y m)}.
-- Proof.
--  intros x y e H.
--  set (e2 := e [/]TwoNZ) in *.
--  set (e4 := e [/]FourNZ) in *.
--  set (e8 := e [/]EightNZ) in *.
--  set (e16 := e [/]SixteenNZ) in *.
--  assert (He2 : [0] [<] e2).
--   unfold e2 in |- *; apply pos_div_two; assumption.
--  assert (He4 : [0] [<] e4).
--   unfold e4 in |- *; apply pos_div_four; assumption.
--  assert (He8 : [0] [<] e8).
--   unfold e8 in |- *; apply pos_div_eight; assumption.
--  assert (He16 : [0] [<] e16).
--   unfold e16 in |- *; apply pos_div_sixteen; assumption.
--  case x; intros x_ px.
--  case y; intros y_ py.
--  unfold CS_seq in |- *; intro.
--  case (px e16 He16); intros N1 px2.
--  case (py e16 He16); intros N2 py2.
--  set (NN := Nat.max N1 N2) in *.
--  assert (N1_NN : N1 <= NN).
--   unfold NN in |- *; auto with arith.
--  assert (N2_NN : N2 <= NN).
--   unfold NN in |- *; auto with arith.
--  exists NN.
--  cut (forall m : nat, Not (NN <= m and AbsBig e2 (x_ m[-]y_ m))).
--   intros.
--   unfold AbsSmall in |- *.
--   assert (H3 : Not (AbsBig e2 (x_ m[-]y_ m))).
--    intro; elim (H1 m); split; assumption.
--   assert (H4 : ~ e2 [<=] x_ m[-]y_ m).
--    intro; apply H3; split; try left; assumption.
--   assert (H5 : ~ x_ m[-]y_ m [<=] [--]e2).
--    intro; apply H3; split; try right; assumption.
--   split; rewrite -> leEq_def; intro.
--    apply H5.
--    apply leEq_transitive with ([--]e).
--     apply less_leEq; assumption.
--    apply less_leEq; apply inv_resp_less.
--    unfold e2 in |- *; apply pos_div_two'; assumption.
--   apply H4.
--   apply leEq_transitive with e.
--    apply less_leEq; unfold e2 in |- *; apply pos_div_two'; auto.
--   apply less_leEq; assumption.
--  intro.
--  intro H1.
--  elim H1; intros X Y.
--  elim H0.
--  exists NN.
--  intros.
--  apply AbsBig_wdl with (e2[-]e8[-]e8).
--   2: unfold e2, e4, e8 in |- *; rational.
--  apply AbsBig_wdr with (x_ m[-]y_ m[-] (x_ m[-]x_ m0) [-] (y_ m0[-]y_ m)).
--   2: rational.
--  assert (e8 [<] e2).
--   unfold e2, e8 in |- *.
--   rstepl ((e [/]TwoNZ) [/]FourNZ).
--   rstepr (e [/]TwoNZ).
--   apply pos_div_four'.
--   assumption.
--  assert ([0] [<] e2[-]e8).
--   apply plus_cancel_less with e8.
--   rstepl e8.
--   rstepr e2.
--   assumption.
--  assert (e8 [<] e2[-]e8).
--   apply plus_cancel_less with e8.
--   rstepr e2.
--   unfold e2, e8 in |- *; rstepl (e [/]FourNZ).
--   rstepl ((e [/]TwoNZ) [/]TwoNZ).
--   apply pos_div_two'.
--   assumption.
--  apply AbsBigSmall_minus; auto.
--   apply AbsBigSmall_minus; auto.
--   unfold e8 in |- *.
--   rstepl (e [/]SixteenNZ[+]e [/]SixteenNZ).
--   rstepr (x_ m[-]x_ N1[+] (x_ N1[-]x_ m0)).
--   apply AbsSmall_plus.
--    apply px2.
--    apply Nat.le_trans with NN; assumption.
--   apply AbsSmall_minus.
--   apply px2.
--   apply Nat.le_trans with NN; assumption.
--  unfold e8 in |- *.
--  rstepl (e [/]SixteenNZ[+]e [/]SixteenNZ).
--  rstepr (y_ m0[-]y_ N2[+] (y_ N2[-]y_ m)).
--  apply AbsSmall_plus.
--   apply py2.
--   apply Nat.le_trans with NN; assumption.
--  apply AbsSmall_minus.
--  apply py2.
--  apply Nat.le_trans with NN; assumption.
-- Qed.

-- Lemma R_ap_alt_2 : forall x y : R_CSetoid, {e : F | [0] [<] e |
--  {N : nat | forall m, N <= m -> AbsBig e (CS_seq F x m[-]CS_seq F y m)}} -> x [#] y.
-- Proof.
--  intros x y H.
--  case H.
--  intros e H0.
--  set (e2 := e [/]TwoNZ) in *.
--  set (e4 := e [/]FourNZ) in *.
--  set (e8 := e [/]EightNZ) in *.
--  set (e16 := e [/]SixteenNZ) in *.
--  assert (He2 : [0] [<] e2).
--   unfold e2 in |- *; apply pos_div_two; assumption.
--  assert (He4 : [0] [<] e4).
--   unfold e4 in |- *; apply pos_div_four; assumption.
--  assert (He8 : [0] [<] e8).
--   unfold e8 in |- *; apply pos_div_eight; assumption.
--  assert (He16 : [0] [<] e16).
--   unfold e16 in |- *; apply pos_div_sixteen; assumption.
--  case x; intros x_ px.
--  case y; intros y_ py.
--  case (px e16 He16); intros N1 H31.
--  case (py e16 He16); intros N2 H41.
--  simpl in |- *; intro H2; case H2; intros N H21.
--  set (NN := Nat.max N (Nat.max N1 N2)) in *.
--  assert (N_NN : N <= NN).
--   unfold NN in |- *; auto with arith.
--  assert (N1_NN : N1 <= NN).
--   unfold NN in |- *; apply Nat.le_trans with (Nat.max N1 N2); auto with arith.
--  assert (N2_NN : N2 <= NN).
--   unfold NN in |- *; apply Nat.le_trans with (Nat.max N1 N2); auto with arith.
--  set (x0 := x_ NN) in *.
--  set (y0 := y_ NN) in *.
--  simpl in |- *.
--  unfold R_ap in |- *.
--  unfold R_lt in |- *.
--  simpl in |- *.
--  assert (H5 : AbsBig e2 (x0[-]y0)).
--   assert (e2 [<=] e).
--    unfold e2 in |- *; apply less_leEq; apply pos_div_two'; auto.
--   split; auto.
--   elim (H21 NN).
--    intros H' Haux; elim Haux; intros; [ left | right ].
--     apply leEq_transitive with e; auto.
--    apply leEq_transitive with ([--]e); auto; apply inv_resp_leEq; auto.
--   unfold NN in |- *; auto with arith.
--  case H5; intros Hx s; case s; intro H6.
--   right.
--   exists NN.
--   exists e4.
--    assumption.
--   intro m; intros.
--   astepl ([--]e8[+]e2[+][--]e8).
--    2: unfold e2, e8, e4 in |- *; rational.
--   rstepr (x_ m[-]x0[+] (x0[-]y0) [+] (y0[-]y_ m)).
--   apply plus_resp_leEq_both.
--    apply plus_resp_leEq_both.
--     astepl ([--]e16[+][--]e16).
--      2: unfold e16, e8 in |- *; rational.
--     rstepr (x_ m[-]x_ N1[+] (x_ N1[-]x0)).
--     apply plus_resp_leEq_both.
--      assert (H7 : AbsSmall e16 (x_ m[-]x_ N1)).
--       apply H31; apply Nat.le_trans with NN; auto.
--      elim H7; intros.
--      rstepl ([--]e16).
--      assumption.
--     assert (H7 : AbsSmall e16 (x_ N1[-]x0)).
--      apply AbsSmall_minus.
--      unfold x0 in |- *; auto.
--     elim H7; intros.
--     rstepl ([--]e16).
--     assumption.
--    (* e *)
--    assumption.
--   (* e *)
--   astepl ([--]e16[+][--]e16).
--    2: unfold e16, e8 in |- *; rational.
--   rstepr (y0[-]y_ N2[+] (y_ N2[-]y_ m)).
--   apply plus_resp_leEq_both.
--    assert (H7 : AbsSmall e16 (y0[-]y_ N2)).
--     unfold y0 in |- *; auto.
--    elim H7; intros.
--    rstepl ([--]e16).
--    assumption.
--   assert (H7 : AbsSmall e16 (y_ N2[-]y_ m)).
--    apply AbsSmall_minus.
--    apply H41.
--    apply Nat.le_trans with NN; auto.
--   elim H7; intros.
--   rstepl ([--]e16).
--   assumption.
--  left.
--  exists NN.
--  exists e4.
--   assumption.
--  intro m; intros.
--  astepl ([--]e8[+]e2[+][--]e8).
--   2: unfold e8, e2, e4 in |- *; rational.
--  rstepr (y_ m[-]y0[+] (y0[-]x0) [+] (x0[-]x_ m)).
--  apply plus_resp_leEq_both.
--   apply plus_resp_leEq_both.
--    astepl ([--]e16[+][--]e16).
--     2: unfold e16, e8 in |- *; rational.
--    rstepr (y_ m[-]y_ N2[+] (y_ N2[-]y0)).
--    apply plus_resp_leEq_both.
--     assert (H8 : AbsSmall e16 (y_ m[-]y_ N2)).
--      apply H41.
--      apply Nat.le_trans with NN; auto.
--     elim H8; intros.
--     rstepl ([--]e16).
--     assumption.
--    assert (H8 : AbsSmall e16 (y_ N2[-]y0)).
--     apply AbsSmall_minus.
--     unfold y0 in |- *; auto.
--    elim H8; intros.
--    rstepl ([--]e16).
--    assumption.
--   (* e *)
--   apply inv_cancel_leEq.
--   rstepl (x0[-]y0).
--   assumption.
--  (* e *)
--  astepl ([--]e16[+][--]e16).
--   2: unfold e16, e8 in |- *; rational.
--  rstepr (x0[-]x_ N1[+] (x_ N1[-]x_ m)).
--  apply plus_resp_leEq_both.
--   assert (H8 : AbsSmall e16 (x0[-]x_ N1)).
--    unfold x0 in |- *; auto.
--   elim H8; intros.
--   rstepl ([--]e16).
--   assumption.
--  assert (H8 : AbsSmall e16 (x_ N1[-]x_ m)).
--   apply AbsSmall_minus.
--   apply H31.
--   apply Nat.le_trans with NN; auto.
--  elim H8; intros.
--  rstepl ([--]e16).
--  assumption.
-- Qed.

-- Lemma Eq_alt_2_1 : forall x y : R_Set, Not (R_ap x y) -> forall e : F, [0] [<] e ->
--  {N : nat | forall m, N <= m -> AbsSmall e (CS_seq F x m[-]CS_seq F y m)}.
-- Proof.
--  intros.
--  apply Eq_alt_1.
--   assumption.
--  intro.
--  apply H.
--  apply R_ap_alt_2.
--  exists (e [/]FourNZ).
--   apply pos_div_four; auto.
--  assumption.
-- Qed.

-- Lemma Eq_alt_2_2 : forall x y : R_Set, (forall e : F, [0] [<] e ->
--  {N : nat | forall m, N <= m -> AbsSmall e (CS_seq F x m[-]CS_seq F y m)}) -> Not (R_ap x y).
-- Proof.
--  intros x y.
--  case x; intros x_ px.
--  case y; intros y_ py.
--  simpl in |- *.
--  intros H. intro H0.
--  assert (H1 : {e : F | [0] [<] e |
--    {N : nat | forall m : nat, N <= m -> AbsBig (Two[*]e) (x_ m[-]y_ m)}}).
--   elim (R_ap_alt_1 _ _ H0).
--   intros e H1 H2.
--   exists (e [/]TwoNZ).
--    apply pos_div_two; assumption.
--   elim H2; intros N HN.
--   exists N. intros.
--   apply AbsBig_wdl with e; [ auto | rational ].
--  case H1.
--  intros e H2 H3.
--  case H3; intros N1 A.
--  case (H e H2); intros N2 B.
--  set (NN := Nat.max N1 N2) in *.
--  assert (N1_NN : N1 <= NN).
--   unfold NN in |- *; auto with arith.
--  assert (N2_NN : N2 <= NN).
--   unfold NN in |- *; auto with arith.
--  assert (H4 := A NN N1_NN).
--  assert (H5 := B NN N2_NN).
--  unfold AbsSmall in H5.
--  rewrite -> leEq_def in H5.
--  elim H5; intros.
--  elim H4; intros.
--  elim b; intros.
--   rewrite ->  leEq_def in H7; apply H7.
--   apply less_leEq_trans with (Two[*]e).
--    astepl ([0][+]e).  rstepr (e[+]e).
--    apply plus_resp_less_rht; auto.
--   assumption.
--  apply H6.
--  apply leEq_less_trans with ([--] (Two[*]e)).
--   auto.
--  apply inv_resp_less.
--  astepl ([0][+]e); rstepr (e[+]e).
--  apply plus_resp_less_rht; auto.
-- Qed.

-- End Auxiliary.

-- End Structure.
