/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Analysis.Normed.Field.Lemmas
import LeanPool.HopfieldNet.CReals.CompReals2
import LeanPool.HopfieldNet.CReals.Core.CornQposMinMax

/-- QAbsSmall (e : ℚ) (x : ℚ) holds if |x| ≤ e. -/
def QAbsSmall (e x : ℚ) : Prop := |x| ≤ e
-- (*
-- Copyright © 2006-2008 Russell O’Connor
-- Copyright © 2020 Vincent Semeria

-- Permission is hereby granted, free of charge, to any person obtaining a copy of
-- this proof and associated documentation files (the "Proof"), to deal in
-- the Proof without restriction, including without limitation the rights to
-- use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
-- the Proof, and to permit persons to whom the Proof is furnished to do so,
-- subject to the following conditions:

-- The above copyright notice and this permission notice shall be included in all
-- copies or substantial portions of the Proof.

-- THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
-- IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
-- FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
-- COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
-- IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
-- CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
-- *)

-- Require Import CoRN.metric2.Metric.
-- Require Import CoRN.metric2.UniformContinuity.
-- Require Import CoRN.model.totalorder.QposMinMax.
-- Require Export CoRN.model.lattice.CRlattice.
-- Require Import CoRN.model.totalorder.QMinMax.
-- From Coq Require Import Qabs.
-- Require Import CoRN.model.metric2.Qmetric.
-- Require Import CoRN.metric2.ProductMetric.
-- Require Import MathClasses.interfaces.canonical_names.

-- (* Backwards compatibility for Hint Rewrite locality attributes *)
-- Set Warnings "-unsupported-attributes".

-- Set Implicit Arguments.

-- Local Open Scope Q_scope.
-- Local Open Scope uc_scope.
-- Opaque Qmin Qmax Qred.

-- (**
-- ** Strict Inequality
-- First we defined positivity.  We define positivity to contain a
-- positive rational witness of a lower bound on x.  This seems the best
-- way because this witness contains exactly the information needed
-- for functions (such as inverse and logorithm) that have domains
-- restricted to the positive reals.
-- *)

def CRpos (x : CReal) : Prop := ∃ (e : ℚ), 0 < e ∧ (e) ≤ x.approx (by {
  constructor
  exact e
})

lemma CRpos_wd {x y : CReal} (hxy : x = y) (h : CRpos x) : CRpos y :=
  let ⟨e, he₀, he⟩ := h
  ⟨e, he₀, by rw [←hxy]; exact he⟩

-- (** This is a characterization closer to Bishop's definiton.  If we
-- replace [2*e] with [e], the theorem still holds, but it could be
-- very expensive to call.  We prefer to avoid that. *)

/--
A characterization of CRpos: if (2 * e) ≤ x.approx ⟨e⟩, then x is positive.
-/
lemma CRpos_char {x : CReal} {e : ℚ} (he : 0 < e)
   (H : (2 : ℚ) * e ≤ x.approx ⟨e⟩) :
  CRpos x := by
  use e
  constructor
  { exact he }
  { -- (2 : ℚ) * e ≤ x.approx ⟨e⟩ ⇒ e ≤ x.approx ⟨e⟩
    -- Since 0 < e, (2 : ℚ) * e = e + e ≥ e
    apply le_trans (by linarith) H }

-- (** Negative reals are defined similarly. *)
/--
A real number `x : CReal` is negative if there exists
 a positive rational `e` such that `x ≤ -e`.
-/
def CRneg (x : CReal) : Prop := ∃ (e : ℚ), 0 < e ∧ x.approx ⟨e⟩ ≤ -e

lemma CRneg_wd {x y : CReal} (hxy : x = y) (h : CRneg x) : CRneg y :=
  let ⟨e, he₀, he⟩ := h
  ⟨e, he₀, by rw [←hxy]; exact he⟩

/--
A characterization of CRneg: if `approx x e ≤ -2 * e` for some
  positive rational `e`, then `x` is negative.
-/
lemma CRneg_char {x : CReal} {e : ℚ} (he : 0 < e) (H : x.approx ⟨e⟩ ≤ -(2 : ℚ) * e) :
  CRneg x :=
  ⟨e, he, by
    have : x.approx ⟨e⟩ ≤ -e := by
      calc
        x.approx ⟨e⟩ ≤ -(2 : ℚ) * e := H
        _ = -e + -e := by ring
        _ ≤ -e     := by linarith [he]
    exact this⟩


-- Next Obligation.
--  change (x <= '(-proj1_sig e)%Q)%CR.
--  intros a; simpl; unfold Cap_raw; simpl; apply Qle_trans with (-(1#2)*proj1_sig a).
--   rewrite -> Qle_minus_iff; ring_simplify.
--   apply Qmult_le_0_compat; auto with *.
--  rewrite -> Qle_minus_iff.
--  destruct (regFun_prf x e ((1#2)*a)%Qpos) as [X _].
--  apply (Qle_trans _ ( - proj1_sig e + - approximate x ((1 # 2) * a)%Qpos
--                       + (1 # 2) * proj1_sig a + approximate x e + - approximate x e)).
--  2: simpl; ring_simplify; apply Qle_refl.
--  rewrite <- Qle_minus_iff.
--  apply Qle_trans with (-(2#1)*proj1_sig e); try assumption.
--  simpl in X. rewrite -> Qle_minus_iff in X.
--  rewrite -> Qle_minus_iff.
--  apply (Qle_trans _ _ _ X).
--  simpl. ring_simplify. apply Qle_refl.
-- Qed.

/-- Strict inequality on CReal: `x < y` iff `y - x` is positive. -/
def CRltT (x y : CReal) : Prop := CRpos (y - x)

instance : LT CReal where
  lt := CRltT

lemma CRltT_wd {x1 x2 y1 y2 : CReal} (Hx : x1 = x2) (Hy : y1 = y2) (h : x1 < y1) : x2 < y2 :=
  CRpos_wd (by rw [Hy, ←Hx]) h

-- (**
-- ** Apartness
-- *)
/-- Apartness on CReal: `x >< y` iff `x < y` or `y < x`. -/
def CRapartT (x y : CReal) : Prop := x < y ∨ y < x

/-- Notation for apartness on CReal: `x >< y` means `CRapartT x y`. -/
infix:70 " >< " => CRapartT

/--
If `x1 = x2` and `y1 = y2`, then `x1 >< y1` iff `x2 >< y2`.
-/
lemma CRapartT_wd {x1 x2 y1 y2 : CReal} (Hx : x1 = x2) (Hy : y1 = y2) (h : x1 >< y1) : x2 >< y2 :=
  h.elim
    (fun hlt => Or.inl (CRltT_wd Hx Hy hlt))
    (fun hgt => Or.inr (CRltT_wd Hy Hx hgt))

/--
The modulus of continuity for multiplication by a constant.
-/
def Qscale_modulus (a : ℚ) (e : ℚ) : Option ℚ :=
  if a = 0 then none
  else
    match a.num, a.den with
    | Int.ofNat an, ad =>
      if an = 0 then none
      else some ((ad / an) * e)
    | Int.negSucc an, ad =>
      some ((ad / (-(an : ℚ) - 1)) * e)

/--
Elimination principle for `Qscale_modulus`.
If `x = 0`, then `Qscale_modulus x e = none` (corresponds to `QposInfinity`).
Otherwise, for any positive rational `y`, if `|e / y|` is "small" compared to `x`, then `P y` holds.
-/
def Qscale_modulus_elim
  (P : Option ℚ → Sort*)
  (x : ℚ) (e : ℚ)
  (h0 : x = 0 → P none)
  (hpos : ∀ y : ℚ, 0 < y → QAbsSmall (e / y) x → P (some y)) :
  P (Qscale_modulus x e) :=
by sorry

/--
If `a` and `e` are positive rationals, then `Qscale_modulus a e` is `some (e / a)`.
-/
lemma Qscale_modulus_pos (a e : ℚ) (ha : 0 < a) (he : 0 < e) :
  Qscale_modulus a e = some (e / a) :=
by
  unfold Qscale_modulus
  split_ifs with h
  · exfalso;
    rw [h] at ha; exact lt_irrefl 0 ha
  · cases a.num
    case neg.ofNat an => sorry
    case neg.negSucc an => sorry

/--
The function `b ↦ a * b` is uniformly continuous on ℚ, with modulus `Qscale_modulus a`.
-/
lemma Qscale_uc_prf (a : ℚ) :
  ∀ {e : ℚ}, 0 < e → ∀ {b₀ b₁ : ℚ}, QAbsSmall e (b₀ - b₁) →
    match Qscale_modulus a e with
    | none => True
    | some δ => QAbsSmall δ (a * b₀ - a * b₁) := by sorry

-- Proof.
--  revert a.
--  intros [[|an|an] ad] e b0 b1 H.
--  - simpl in *.
--    setoid_replace ((0 # ad)) with 0 by constructor.
--    rewrite Qmult_0_l, Qmult_0_l.
--    apply Qball_Reflexive, Qpos_nonneg.
--  - simpl.
--   simpl in *.
--   unfold Qball in *.
--   unfold QAbsSmall.
--   setoid_replace ((Zpos an # ad) * b0 - (Zpos an # ad) * b1)
--     with (b0 * (Zpos an # ad) - b1 * (Zpos an # ad))
--     by (unfold equiv, stdlib_rationals.Q_eq; ring).
--   unfold QAbsSmall in H.
--   setoid_replace ((Zpos ad # an) * ` e)
--     with (` e / (Zpos an # ad)) in H.
--   apply (Qball_Qmult_r e (an#ad)) in H.
--   exact H.
--   rewrite Qmult_comm. apply Qmult_comp; reflexivity.
--  - simpl.
--    setoid_replace ((Z.neg an # ad) * b0)
--      with (-((Z.pos an # ad) * b0)).
--    setoid_replace ((Z.neg an # ad) * b1)
--      with (-((Z.pos an # ad) * b1)).
--    apply Qball_opp.
--    simpl in H.
--    unfold Qball, QAbsSmall.
--   setoid_replace ((Zpos an # ad) * b0 - (Zpos an # ad) * b1)
--     with (b0*(Zpos an#ad)-b1*(Zpos an#ad))
--      by (unfold equiv, stdlib_rationals.Q_eq; ring).
--   setoid_replace ((Zpos ad # an) * ` e)
--     with (` e / (Zpos an # ad)) in H.
--   apply (Qball_Qmult_r e (an#ad)) in H. simpl in H.
--   apply H.
--   rewrite Qmult_comm. apply Qmult_comp; reflexivity.
--   destruct b1, Qnum; reflexivity.
--   destruct b0, Qnum; reflexivity.
-- Qed.

/-- Scaling by a constant is `Qscale_uc_prf` lifted to a uniformly continuous function. -/
def Qscale_uc (a : ℚ) : ℚ → ℚ := fun b => a * b

/-- Scaling a constructive real by a rational constant. -/
def scale (a : ℚ) : CReal → CReal := sorry
  --Cmap QPrelengthSpace (Qscale_uc a)

@[simp]
theorem Qscale_uc_congr {a₁ a₂ : ℚ} (h : a₁ = a₂) : Qscale_uc a₁ = Qscale_uc a₂ :=
  by rw [h]

-- #[global]
-- Instance scale_Proper: Proper (Qeq ==> @msp_eq (UniformlyContinuousSpace CR CR)) scale.
-- Proof.
--   intros x y E.
--   apply ucEq_equiv.
--   intro z. simpl ucFun. rewrite E.
--   reflexivity.
-- Qed.

/--
`QboundAbs c` clamps a rational number between `-c` and `c`, where `c` is positive.
-/
def QboundAbs (c : ℚ) (hc : 0 < c) : ℚ → ℚ :=
  fun x => max (-c) (min c x)

/--
A constructive real number, represented by an approximation function
and an integer approximation.
-/
structure CReal' where
  approx : Complete Base
  intApprox : ℤ
deriving Nonempty

/--
`CRboundAbs c x` clamps a constructive real `x`
between `-c` and `c`, where `c` is a positive rational.
-/
def CRboundAbs (c : ℚ) (hc : 0 < c) : CReal → CReal :=
  --fun x =>  QPrelengthSpace (QboundAbs c hc)

-- Lemma QboundAbs_absorb: forall (a b:Qpos) (c:Q),
--  proj1_sig a <= proj1_sig b ->
--  QboundAbs b (QboundAbs a c) == QboundAbs a c.
-- Proof.
--  intros a b c H.
--  simpl.
--  rewrite -> Qmin_max_distr_r.
--  setoid_replace (Qmin (proj1_sig b) (-proj1_sig a)) with (-proj1_sig a).
--   rewrite -> Qmax_assoc.
--   rewrite <- Qmin_max_de_morgan.
--   rewrite -> Qmin_assoc.
--   setoid_replace (Qmin (proj1_sig b) (proj1_sig a)) with (proj1_sig a).
--    reflexivity.
--   rewrite <- Qle_min_r.
--   assumption.
--  rewrite <- Qle_min_r.
--  rewrite -> Qle_minus_iff.
--  ring_simplify.
--  destruct a,b. simpl. rewrite <- (Qplus_0_l 0).
--  apply Qplus_le_compat; apply Qlt_le_weak; assumption.
-- Qed.

-- (** Properties of CRboundAbs. *)
-- Lemma CRboundAbs_Eq : forall (a:Qpos) (x:CR),
--  ('(-proj1_sig a)%Q <= x -> x <= ' proj1_sig a ->
--  CRboundAbs a x == x)%CR.
-- Proof.
--  intros a x Ha Hb.
--  unfold CRboundAbs.
--  transitivity (uc_compose (Cmap QPrelengthSpace (QboundBelow_uc (-proj1_sig a))) (Cmap QPrelengthSpace (QboundAbove_uc (proj1_sig a))) x).
--  simpl (Cmap QPrelengthSpace (QboundAbs a) x).
--  simpl ((Cmap QPrelengthSpace (QboundBelow_uc (- ` a))
--       ∘ Cmap QPrelengthSpace (QboundAbove_uc (` a))) x).
--   repeat rewrite -> Cmap_fun_correct.
--   apply MonadLaw2.
--  simpl ((Cmap QPrelengthSpace (QboundBelow_uc (- ` a))
--       ∘ Cmap QPrelengthSpace (QboundAbove_uc (` a))) x).
--  change (boundBelow (-proj1_sig a) (boundAbove (proj1_sig a) x) == x)%CR.
--  assert (X:(boundAbove (proj1_sig a) x==x)%CR).
--   rewrite <- CRmin_boundAbove.
--   rewrite <- CRle_min_r.
--   assumption.
--  rewrite -> X.
--  rewrite <- CRmax_boundBelow.
--  rewrite <- CRle_max_r.
--  assumption.
-- Qed.

-- Lemma QboundAbs_elim : forall (z:Qpos) (a:Q) (P:Q->Prop),
-- ((proj1_sig z <= a)%Q -> P (proj1_sig z)) ->
-- ((a <= -proj1_sig z)%Q -> P (- proj1_sig z)%Q) ->
-- (QAbsSmall (proj1_sig z) a -> P (a)) ->
-- P (QboundAbs z a).
-- Proof.
--  intros z a P H1 H2 H3.
--  simpl.
--  apply Qmax_case; apply Qmin_case; intros Z0 Z1; try solve [apply H1;assumption|apply H2;assumption].
--   elim (Qle_not_lt _ _ Z1).
--   rewrite -> Qlt_minus_iff.
--   ring_simplify.
--   apply (Qpos_ispos ((2#1)*z)).
--  apply H3.
--  split;assumption.
-- Qed.

-- Lemma QboundAbs_abs : forall (z:Qpos) (a:Q),
--     Qabs (QboundAbs z a) == Qmin (Qabs a) (proj1_sig z).
-- Proof.
--   intros. apply QboundAbs_elim.
--   - intros. symmetry. rewrite Qabs_pos, Qabs_pos.
--     apply Qle_min_r, H. apply Qpos_nonneg.
--     apply (Qle_trans _ (`z)). apply Qpos_nonneg. exact H.
--   - intros. symmetry. rewrite Qabs_opp.
--     rewrite (Qabs_pos (`z)). apply Qle_min_r.
--     rewrite Qabs_neg, <- Qopp_involutive.
--     apply Qopp_le_compat, H.
--     apply (Qle_trans _ _ _ H). apply (Qopp_le_compat 0), Qpos_nonneg.
--     apply Qpos_nonneg.
--   - intros. symmetry. apply Qle_min_l.
--     apply AbsSmall_Qabs in H. exact H.
-- Qed.


-- (** The modulus of continuity for multiplication depends on the
-- bound, c, on the second argument. *)
-- Definition Qmult_modulus (c:Qpos)(e:Qpos) : QposInf
--   := Qpos2QposInf (e * Qpos_inv c).

-- Lemma Qmult_uc_prf (c:Qpos)
--   : @is_UniformlyContinuousFunction
--       Q_as_MetricSpace (Q_as_MetricSpace --> Q_as_MetricSpace)
--       (fun a:Q => uc_compose (Qscale_uc a) (QboundAbs c)) (Qmult_modulus c).
-- Proof with simpl in *; auto with *.
--  intros e a0 a1 H. split. apply Qpos_nonneg. intro b.
--  simpl in *.
--  set (b' := Qmax (- proj1_sig c) (Qmin (proj1_sig c) b)).
--  repeat rewrite -> (fun x => Qmult_comm x b').
--  apply Qscale_uc_prf.
--  assert (QposEq (e * Qpos_inv c) (Qpos_inv c*e)%Qpos)
--    by (unfold QposEq; simpl; ring).
--  apply (ball_wd _ H0 _ _ (reflexivity _) _ _ (reflexivity _)) in H. clear H0.
--  apply ball_ex_weak_le with (Qpos_inv c*e)%Qpos;[|assumption].
--  unfold b'.
--  destruct c as [[cn cd] cpos].
--  destruct cn as [|cn|cn]. inversion cpos. 2: inversion cpos.
--  apply Qmax_case. intros. apply Qle_refl. simpl.
--  apply Qmin_case. intros. apply Qle_refl.
--  intros H1 H2.
--  destruct b as [[|bn|bn] bd]...
--  - apply Qmult_le_r. destruct e; exact q.
--  apply Qle_shift_inv_r. reflexivity.
--  rewrite <- Qmult_1_l in H1.
--  apply Qle_shift_div_l in H1.
--  apply (Qle_trans _ _ _ H1). rewrite Qmult_comm.
--  apply Qmult_le_l. reflexivity. apply Z.le_refl. reflexivity.
--  - apply Qmult_le_r. destruct e; exact q.
--  apply Qle_shift_inv_r. reflexivity.
--  apply Qopp_le_compat in H2. rewrite Qopp_involutive in H2.
--  rewrite <- Qmult_1_l in H2.
--  apply Qle_shift_div_l in H2. 2: reflexivity.
--  apply (Qle_trans _ _ _ H2). rewrite Qmult_comm.
--  apply Qmult_le_l. reflexivity. apply Z.le_refl.
-- Qed.

-- (* begin hide *)
-- Arguments Qmult_uc_prf : clear implicits.
-- (* end hide *)
-- Definition Qmult_uc (c:Qpos)
--   : Q_as_MetricSpace --> Q_as_MetricSpace --> Q_as_MetricSpace
--   := Build_UniformlyContinuousFunction (Qmult_uc_prf c).

-- (** This multiplication function is correct when yBound is a bound
--     on the absolute value of the second CR argument. *)
-- Definition CRmult_bounded (yBound : Qpos) : CR --> CR --> CR
--   := Cmap2 QPrelengthSpace QPrelengthSpace (Qmult_uc yBound).

-- #[global]
-- Instance: Proper (QposEq ==> @msp_eq _) Qmult_uc.
-- Proof.
--   intros e1 e2 E.
--   simpl. split. discriminate.
--   intro a. simpl. split. discriminate.
--   intro b. simpl.
--   apply Qball_0.
--   unfold QposEq in E. rewrite E.
--   reflexivity.
-- Qed.

-- #[global]
-- Instance CRmult_bounded_wd : Proper (QposEq ==> @msp_eq _) CRmult_bounded.
-- Proof.
--   intros e1 e2 E.
--   simpl. split. discriminate.
--   intro x1. split. discriminate.
--   intro x2.
--   simpl (CRmult_bounded e1 x1 x2).
--   simpl (CRmult_bounded e2 x1 x2).
--   rewrite E. reflexivity.
-- Qed.

-- (** CR_b computes a rational bound on the absolute value of x *)

-- Lemma CR_b_pos (e : Qpos) (x : CR) : 0 < Qabs (approximate x e) + proj1_sig e.
-- Proof.
--   apply (Qle_lt_trans _ (Qabs (approximate x e) + 0)).
--   rewrite Qplus_0_r. apply Qabs_nonneg.
--   apply Qplus_lt_r, Qpos_ispos.
-- Qed.

-- Definition CR_b (e:Qpos) (x:CR) : Qpos
--   := exist (Qlt 0) (Qabs (approximate x e) + proj1_sig e)
--            (CR_b_pos _ _).

-- Lemma CR_b_lowerBound : forall e x, (' (-proj1_sig (CR_b e x))%Q <= x)%CR.
-- Proof.
--  intros e x e'.
--  unfold CR_b.
--  simpl.
--  unfold Cap_raw.
--  simpl.
--  rewrite -> Qle_minus_iff, Qopp_involutive, Qopp_involutive.
--  destruct (regFun_prf x ((1#2)*e')%Qpos e) as [H _].
--  simpl in H.
--  rewrite -> Qle_minus_iff in H.
--  ring_simplify in H.
--  apply (Qle_trans _ _ _ H).
--  rewrite -> Qle_minus_iff.
--  ring_simplify.
--  clear H.
--  apply Qabs_case; intros H.
--  apply (Qle_trans _ (approximate x e + 0)).
--  rewrite Qplus_0_r. exact H. rewrite <- Qplus_assoc.
--  apply Qplus_le_r.
--  apply (Qle_trans _ (0+approximate x e)).
--  rewrite Qplus_0_l. exact H.
--  apply Qplus_le_l. apply (Qpos_nonneg ((1#2)*e')).
--  ring_simplify. apply (Qpos_nonneg ((1#2)*e')).
-- Qed.

-- Lemma CR_b_upperBound : forall e x, (x <= 'proj1_sig (CR_b e x))%CR.
-- Proof.
--  intros e x e'.
--  unfold CR_b.
--  simpl.
--  unfold Cap_raw.
--  simpl.
--  rewrite -> Qle_minus_iff.
--  ring_simplify.
--  destruct (regFun_prf x ((1#2)*e')%Qpos e) as [_ H].
--  simpl in H.
--  rewrite -> Qle_minus_iff in H.
--  ring_simplify in H.
--  eapply Qle_trans.
--   apply H.
--  rewrite -> Qle_minus_iff.
--  ring_simplify.
--  clear H.
--  apply Qabs_case; intros H.
--  ring_simplify. apply (Qpos_nonneg ((1#2)*e')).
--  apply (Qplus_le_r _ _ ((2#1)*approximate x e)).
--  simpl. ring_simplify.
--  apply (Qle_trans _ 0).
--  rewrite <- (Qmult_0_r (2#1)). apply Qmult_le_l.
--  reflexivity. exact H. apply (Qpos_nonneg ((1#2)*e')).
-- Qed.

-- (** This version of multiply computes a bound on the second argument
-- just in time.  It should be avoided in favour of the bounded version
-- whenever possible. *)
-- #[global]
-- Instance CRmult: Mult CR := λ x y, ucFun2 (CRmult_bounded (CR_b (1#1) y)) x y.

-- Infix "*" := CRmult : CR_scope.

-- Lemma CRmult_bounded_weaken : forall (c1 c2:Qpos) x y,
--     ((' (-proj1_sig c1)%Q <= y) -> (y <= ' proj1_sig c1)
--      -> (proj1_sig c1 <= proj1_sig c2)%Q ->
-- CRmult_bounded c1 x y == CRmult_bounded c2 x y)%CR.
-- Proof.
--  intros c1 c2 x y Hc1a Hc1b Hc2.
--  assert (Hy:=CRboundAbs_Eq _ Hc1a Hc1b).
--  set (y':= (CRboundAbs c1 y)) in *.
--  transitivity (ucFun2 (CRmult_bounded c2) x y'); [|rewrite -> Hy;reflexivity].
--  assert (H:forall x:Qpos, proj1_sig (x*c1*Qpos_inv c2)%Qpos <= proj1_sig x).
--  { intros a.
--   simpl.
--   rewrite <- (Qmult_1_r (`a)), <- Qmult_assoc, <- Qmult_assoc.
--   apply Qmult_le_l. destruct a; exact q.
--   rewrite Qmult_1_l. apply Qle_shift_div_r.
--   destruct c2; exact q. rewrite Qmult_1_l. exact Hc2. }
--  change (ucFun2 (CRmult_bounded c1) x y == ucFun2 (CRmult_bounded c2) x y')%CR.
--  rewrite <- (QreduceApprox_Eq x).
--  set (x''':=(QreduceApprox x)).
--  set (x':=faster x''' (fun x => (x * c1 * Qpos_inv c2)%Qpos) H).
--  transitivity (ucFun2 (CRmult_bounded c1) x' y).
--   unfold x'.
--   rewrite -> fasterIsEq.
--   reflexivity.
--  apply regFunEq_equiv, regFunEq_e; intros e.
--  intros.
--  simpl.
--  do 3 (unfold Cap_raw; simpl).
--  assert (X:=fun c => QboundAbs_absorb _ _ c Hc2).
--  unfold QboundAbs in X.
--  simpl in X.
--  rewrite -> X.
--  clear X.
--  assert (eq (Qpos_red ((1 # 2) * e * Qpos_inv c1 * c1 * Qpos_inv c2))
--             (Qpos_red ((1 # 2) * e * Qpos_inv c2))).
--  { apply Qpos_red_eq. unfold QposEq. simpl. field.
--    split. intro abs. destruct c2. simpl in abs.
--    apply (Qlt_not_le _ _ q). rewrite abs. apply Qle_refl.
--    intro abs. destruct c1. simpl in abs.
--    apply (Qlt_not_le _ _ q). rewrite abs. apply Qle_refl. }
--  simpl. simpl in H0. rewrite H0.
--  do 2 rewrite QposInf_bind_id. apply Qball_Reflexive.
--  apply (Qpos_nonneg (e+e)).
-- Qed.

-- Lemma CRmult_bounded_mult : forall (c:Qpos) (x y:CR),
--  (' (-proj1_sig c)%Q <= y -> y <= ' proj1_sig c ->
--   CRmult_bounded c x y == x*y)%CR.
-- Proof.
--  intros c x y Hc1 Hc2.
--  unfold CRmult.
--  set (d:=(CR_b (1 # 1) y)).
--  destruct (Qle_total (proj1_sig c) (proj1_sig d)).
--   apply CRmult_bounded_weaken; assumption.
--  symmetry.
--  apply CRmult_bounded_weaken; try assumption.
--   apply CR_b_lowerBound.
--  apply CR_b_upperBound.
-- Qed.
-- (* begin hide *)
-- Add Morphism CRmult with signature (@msp_eq _) ==> (@msp_eq _) ==> (@msp_eq _)
--       as CRmult_wd.
-- Proof.
--  intros x1 x2 Hx y1 y2 Hy.
--  unfold CRmult.
--  set (c:=(CR_b (1 # 1) y1)).
--  set (d:=(CR_b (1 # 1) y2)).
--  rewrite -> Hx.
--  rewrite -> Hy.
--  unfold d.
--  apply CRmult_bounded_mult; rewrite <- Hy.
--   apply CR_b_lowerBound.
--  apply CR_b_upperBound.
-- Qed.
-- (* end hide *)
-- Lemma CRmult_scale : forall (a:Q) (y:CR), ((' a)*y==scale a y)%CR.
-- Proof.
--  intros a y.
--  unfold CRmult.
--  unfold CRmult_bounded.
--  unfold ucFun2.
--  unfold Cmap2.
--  unfold inject_Q_CR.
--  change (msp_eq
--     (Cap_fun QPrelengthSpace
--        (Cmap_fun QPrelengthSpace (Qmult_uc (CR_b (1 ↾ eq_refl) y))
--           (Cunit_fun Q_as_MetricSpace a)) y)
--     (Cmap_fun QPrelengthSpace (Qscale_uc a) y)).
--  rewrite -> Cap_fun_correct.
--  repeat rewrite -> Cmap_fun_correct.
--  rewrite -> MonadLaw3.
--  rewrite -> StrongMonadLaw1.
--  change (msp_eq (Cmap_slow_fun (Qscale_uc a ∘ QboundAbs (CR_b (1 ↾ eq_refl) y)) y)
--     (Cmap_slow_fun (Qscale_uc a) y)).
--  transitivity (uc_compose (Cmap QPrelengthSpace (Qscale_uc a))
--    (Cmap QPrelengthSpace (QboundAbs (CR_b (1#1) y))) y).
--  simpl ((Cmap QPrelengthSpace (Qscale_uc a)
--       ∘ Cmap QPrelengthSpace (QboundAbs (CR_b (1 ↾ eq_refl) y))) y).
--   repeat rewrite -> Cmap_fun_correct.
--   apply MonadLaw2.
--  simpl ((Cmap QPrelengthSpace (Qscale_uc a)
--       ∘ Cmap QPrelengthSpace (QboundAbs (CR_b (1 ↾ eq_refl) y))) y).
--  repeat rewrite -> Cmap_fun_correct.
--  change (Cmap_slow (Qscale_uc a) (Cmap_slow_fun (QboundAbs (CR_b (1 # 1) y)) y) ==
--    Cmap_slow (Qscale_uc a) y)%CR.
--  apply uc_wd.
--  rewrite <- (Cmap_fun_correct (Y:=Q_as_MetricSpace) QPrelengthSpace).
--  apply CRboundAbs_Eq.
--   apply CR_b_lowerBound.
--  apply CR_b_upperBound.
-- Qed.
-- (* begin hide *)
-- #[global]
-- Hint Rewrite CRmult_scale : CRfast_compute.
-- (* end hide *)
-- Lemma scale_Qmult : forall a b:Q, (scale a ('b)=='(a*b)%Q)%CR.
-- Proof.
--  intros a b.
--  unfold scale.
--  change (msp_eq (Cmap_fun QPrelengthSpace (Qscale_uc a) (' b)%CR) (' (a * b)%Q)%CR).
--  rewrite -> Cmap_fun_correct.
--  apply MonadLaw3.
-- Qed.
-- (* begin hide *)
-- #[global]
-- Hint Rewrite scale_Qmult : CRfast_compute.
-- (* end hide *)
-- (**
-- ** Inverse
-- The modulus of continuity for inverse depends on a rational bound
-- away from 0 of x. *)
-- Definition Qinv_modulus (c:Qpos) (e:Qpos) : Qpos := (c*c*e)%Qpos.

-- Lemma Qpos_Qmax : forall (a:Qpos) (b:Q), 0<Qmax (proj1_sig a) b.
-- Proof.
--  intros a b.
--  apply Qmax_case; intros H.
--  destruct a; exact q.
--  apply Qlt_le_trans with (proj1_sig a).
--  destruct a; exact q.
--  assumption.
-- Qed.

-- Lemma Qinv_pos_uc_prf (c:Qpos) :
--   @is_UniformlyContinuousFunction
--     Q_as_MetricSpace Q_as_MetricSpace
--     (fun a:Q => /(Qmax (proj1_sig c) a) ) (Qinv_modulus c).
-- Proof.
--  intros e a0 a1 Ha.
--  simpl in *.
--  unfold Qball in *.
--  assert (forall (a:Qpos) (b:Q), 0 < Qmax (`a) b) as max_pos.
--  { intros. apply (Qlt_le_trans _ (`a)).
--    destruct a; exact q. apply Qmax_ub_l. }
--  assert ( 0 < Qmax (` c) a0 * Qmax (` c) a1).
--  { apply (Qle_lt_trans _ (Qmax (`c) a0 * 0)).
--    rewrite Qmult_0_r. apply Qle_refl.
--    apply Qmult_lt_l. apply max_pos. apply max_pos. }
--  apply AbsSmall_Qabs.
--  setoid_replace (/ Qmax (` c) a0 - / Qmax (` c) a1)
--    with ((Qmax (` c) a1 - Qmax (` c) a0) / (Qmax (` c) a0 * Qmax (` c) a1)).
--  2: unfold equiv, stdlib_rationals.Q_eq; field.
--  unfold Qdiv. rewrite Qabs_Qmult.
--  rewrite (Qabs_pos (/ ( Qmax (` c) a0 * Qmax (` c) a1))).
--  2: apply Qlt_le_weak, Qinv_lt_0_compat, H.
--  apply Qle_shift_div_r. exact H.
--  apply (Qle_trans _ _ _ (Qmax_contract _ _ _)).
--  apply AbsSmall_Qabs in Ha. rewrite Qabs_Qminus.
--  apply (Qle_trans _ _ _ Ha).
--  rewrite (Qmult_comm (`e)). apply Qmult_le_r.
--  apply Qpos_ispos.
--  apply (Qle_trans _ (`c * Qmax (`c) a1)).
--  apply Qmult_le_l. apply Qpos_ispos. apply Qmax_ub_l.
--  apply Qmult_le_r. apply max_pos. apply Qmax_ub_l.
--  split; intro abs. specialize (max_pos c a1).
--  rewrite abs in max_pos. exact (Qlt_irrefl 0 max_pos).
--  specialize (max_pos c a0).
--  rewrite abs in max_pos. exact (Qlt_irrefl 0 max_pos).
-- Qed.

-- Arguments Qinv_pos_uc_prf : clear implicits.

-- Definition Qinv_pos_uc (c:Qpos) : Q_as_MetricSpace --> Q_as_MetricSpace :=
-- Build_UniformlyContinuousFunction (Qinv_pos_uc_prf c).

-- Lemma Qinv_pos_uc_wd : forall (c1 c2:Qpos),
--     (proj1_sig c1 <= proj1_sig c2)
--     -> forall x, (proj1_sig c2 <= x) -> msp_eq (Qinv_pos_uc c1 x) (Qinv_pos_uc c2 x).
-- Proof.
--  intros c1 c2 Hc x Hx.
--  simpl.
--  setoid_replace (Qmax (proj1_sig c2) x) with x by (rewrite <- Qle_max_r; assumption).
--  setoid_replace (Qmax (proj1_sig c1) x) with x.
--  apply Qball_Reflexive. discriminate.
--  rewrite <- Qle_max_r.
--  apply Qle_trans with (proj1_sig c2); assumption.
-- Qed.

-- (** [CRinv_pos] works for inputs greater than c *)
-- Definition CRinv_pos (c:Qpos) : CR --> CR := (Cmap QPrelengthSpace (Qinv_pos_uc c)).

-- Lemma CRinv_pos_weaken : forall (c1 c2:Qpos),
--     proj1_sig c1 <= proj1_sig c2
--     -> forall (x:CR), (' proj1_sig c2 <= x -> CRinv_pos c1 x == CRinv_pos c2 x)%CR.
-- Proof.
--  intros c1 c2 Hc x Hx.
--  assert (X:((boundBelow (proj1_sig c2) x)==x)%CR).
--   rewrite <- CRmax_boundBelow.
--   rewrite <- CRle_max_r.
--   assumption.
--  rewrite <- X.
--  rewrite <- (QreduceApprox_Eq x).
--  pose (f:=(fun e:Qpos => (c1*c1*Qpos_inv c2*Qpos_inv c2)*e)%Qpos).
--  assert (Y:forall e:Qpos, proj1_sig (f e) <= proj1_sig e).
--  { intros e.
--    unfold f. simpl.
--    rewrite <- (Qmult_1_l (`e)) at 2.
--    apply Qmult_le_r. apply Qpos_ispos.
--    apply Qle_shift_div_r. apply Qpos_ispos.
--    apply Qle_shift_div_r. apply Qpos_ispos.
--    rewrite Qmult_1_l.
--    apply (Qle_trans _ (`c1*`c2)).
--    apply Qmult_le_l. apply Qpos_ispos. exact Hc.
--    apply Qmult_le_r. apply Qpos_ispos. exact Hc. }
--  transitivity (CRinv_pos c2 (boundBelow (proj1_sig c2) (faster (QreduceApprox x) f Y))).
--   apply regFunEq_equiv, regFunEq_e.
--   intros e.
--   assert (Z:=Qinv_pos_uc_wd _ _ Hc).
--   simpl in Z.
--   simpl.
--   rewrite -> Z;[|apply Qmax_ub_l].
--   unfold Qinv_modulus.
--   replace (Qpos_red (c1 * c1 * e)) with (Qpos_red (f (c2 * c2 * e)%Qpos)); [apply ball_refl|].
--   apply (Qpos_nonneg (e+e)).
--   apply Qpos_red_eq.
--   unfold f.
--   unfold QposEq.
--   simpl.
--   field.
--   apply Qpos_nonzero.
--  rewrite -> fasterIsEq.
--  reflexivity.
-- Qed.

-- #[global]
-- Instance CRinv_pos_uc_Proper : Proper (QposEq ==> @msp_eq _ ==> @msp_eq _) Qinv_pos_uc.
-- Proof.
--   intros [c1 ?] [c2 ?] E x1 x2 F. unfold QposEq in E. simpl in *.
--   apply Qball_0. apply Qball_0 in F.
--   rewrite E, F. reflexivity.
-- Qed.

-- #[global]
-- Instance: Proper (QposEq ==> @msp_eq _) CRinv_pos.
-- Proof.
--   intros c1 c2 E.
--   apply ucEq_equiv. intro x.
--   simpl (CRinv_pos c1 x).
--   simpl (CRinv_pos c2 x).
--   setoid_replace (Qinv_pos_uc c1) with (Qinv_pos_uc c2).
--    easy.
--   apply ucEq_equiv.
--   intros y. now apply CRinv_pos_uc_Proper.
-- Qed.

-- Lemma CRinv_pos_Qinv : forall (c:Qpos) x,
--     (proj1_sig c <= x)%Q -> (CRinv_pos c (' x) == (' (/x)))%CR.
-- Proof.
--  intros c x H.
--  apply regFunEq_equiv, regFunEq_e.
--  intros e.
--  simpl.
--  setoid_replace (Qmax (proj1_sig c) x) with x.
--   apply Qball_Reflexive.
--   apply (Qpos_nonneg (e+e)).
--  rewrite <- Qle_max_r.
--  assumption.
-- Qed.

-- (** [CRinvT] works for inputs apart from 0 *)
-- Definition CRinvT (x:CR)(x_: (x >< 0)%CR) : CR.
-- Proof.
--  revert x_.
--  intros [[c H]|[c H]].
--   exact ((-(CRinv_pos c (-x)))%CR).
--  exact (CRinv_pos c x).
-- Defined.

-- Arguments CRinvT : clear implicits.

-- Lemma CRinvT_pos_inv : forall (c:Qpos) (x:CR) x_,
--  ('proj1_sig c <= x ->
--   CRinv_pos c x == CRinvT x x_)%CR.
-- Proof.
--  intros c x [[e He]|[e He]] H.
--   assert (X:(' proj1_sig e <= -x)%CR).
--    rewrite <- (doubleSpeed_Eq x).
--    intros d.
--    eapply Qle_trans.
--     apply He.
--    simpl.
--    do 2 (unfold Cap_raw;simpl).
--    ring_simplify.
--    apply Qle_refl.
--   assert (' proj1_sig c <= ' (- proj1_sig e)%Q)%CR.
--    eapply CRle_trans.
--     apply H.
--    intros d.
--    eapply Qle_trans.
--     apply X.
--    simpl.
--    do 2 (unfold Cap_raw;simpl).
--    rewrite -> Qle_minus_iff.
--    ring_simplify.
--    apply Qle_refl.
--    assert (0 < proj1_sig c) as cpos.
--    { destruct c; exact q. }
--   elim (Qlt_not_le _ _ cpos).
--   assert (Y:=H0 (e)%Qpos).
--   simpl in Y.
--   do 2 (unfold Cap_raw in Y ;simpl in Y).
--   rewrite -> Qle_minus_iff in Y.
--   ring_simplify in Y.
--   rewrite -> Qle_minus_iff.
--   ring_simplify;assumption.
--  assert (' proj1_sig e <= x)%CR.
--   rewrite <- (doubleSpeed_Eq x).
--   intros d.
--   eapply Qle_trans.
--    apply He.
--   simpl.
--   do 2 (unfold Cap_raw;simpl).
--   ring_simplify.
--   apply Qle_refl.
--   destruct (Qle_total (proj1_sig c) (proj1_sig e));
--     [|symmetry]; apply CRinv_pos_weaken; assumption.
-- Qed.

-- Lemma CRinvT_wd : forall (x y:CR) x_ y_, (x == y -> CRinvT x x_ == CRinvT y y_)%CR.
-- Proof.
--  assert (X:forall x, (0 + x == x)%CR).
--   intros x.
--   transitivity (doubleSpeed x);[|apply doubleSpeed_Eq].
--   apply regFunEq_equiv, regFunEq_e.
--   intros e.
--   simpl.
--   unfold Cap_raw; simpl.
--   rewrite Qplus_0_l.
--   apply Qball_Reflexive. apply (Qpos_nonneg (e+e)).
--  assert (Y:forall x, (x + - 0 == x)%CR).
--   intros x.
--   transitivity (doubleSpeed x);[|apply doubleSpeed_Eq].
--   apply regFunEq_equiv, regFunEq_e.
--   intros e.
--   simpl.
--   unfold Cap_raw; simpl.
--   rewrite Qplus_0_r.
--   apply Qball_Reflexive. apply (Qpos_nonneg (e+e)).
--  intros x y [[c x_]|[c x_]] [[d y_]|[d y_]] H.
--     change (-(CRinv_pos c (-x))== (-(CRinv_pos d (-y))))%CR.
--     rewrite -> H in *.
--     rewrite -> X in *. intros.
--     apply CRopp_wd.
--     destruct (Qle_total (proj1_sig c) (proj1_sig d));
--       [|symmetry]; apply CRinv_pos_weaken; try assumption.
--     assert (0 < proj1_sig c) as cpos.
--    { destruct c; exact q. }
--    elim (Qlt_not_le _ _ cpos).
--    rewrite -> X in *.
--    rewrite -> Y in *.
--    rewrite -> H in *.
--    assert (Z:=Qplus_le_compat _ _ _ _ (x_ ((1#2)*d)%Qpos) (y_ ((1#2)*d)%Qpos)).
--    simpl in Z.
--    unfold Cap_raw in Z; simpl in Z.
--    autorewrite with QposElim in Z.
--    rewrite -> Qle_minus_iff in Z.
--    ring_simplify in Z.
--    rewrite -> Qle_minus_iff.
--    ring_simplify.
--    assumption.
--     assert (0 < proj1_sig c) as cpos.
--    { destruct c; exact q. }
--   elim (Qlt_not_le _ _ cpos).
--   rewrite -> X in *.
--   rewrite -> Y in *.
--   rewrite -> H in *.
--   assert (Z:=Qplus_le_compat _ _ _ _ (x_ ((1#2)*d)%Qpos) (y_ ((1#2)*d)%Qpos)).
--   simpl in Z.
--   unfold Cap_raw in Z; simpl in Z.
--   autorewrite with QposElim in Z.
--   rewrite -> Qle_minus_iff in Z.
--   ring_simplify in Z.
--   rewrite -> Qle_minus_iff.
--   ring_simplify.
--   assumption.
--  change (CRinv_pos c x== (CRinv_pos d y))%CR.
--  rewrite -> H in *.
--  rewrite -> Y in *.
--  destruct (Qle_total (proj1_sig c) (proj1_sig d));
--    [|symmetry]; apply CRinv_pos_weaken; try assumption.
-- Qed.

-- Lemma CRinvT_irrelevant : forall x x_ x__, (CRinvT x x_ == CRinvT x x__)%CR.
-- Proof.
--  intros.
--  apply CRinvT_wd.
--  reflexivity.
-- Qed.

-- (* Non-curried equivalent version of multiplication. *)

-- Lemma QboundAbs_contract : forall (c : Qpos) (j k : Q),
--     Qabs (QboundAbs c j - QboundAbs c k) <= Qabs (j-k).
-- Proof.
--   intros. apply QboundAbs_elim.
--   - intros. apply QboundAbs_elim.
--     + intros. unfold Qminus. rewrite Qplus_opp_r. apply Qabs_nonneg.
--     + intros. unfold Qminus. rewrite Qopp_involutive.
--       rewrite Qabs_pos, Qabs_pos.
--       apply Qplus_le_compat. exact H.
--       rewrite <- Qopp_involutive. apply Qopp_le_compat. exact H0.
--       apply (Qle_trans _ (`c + `c)).
--       apply (Qpos_nonneg (c+c)).
--       apply Qplus_le_compat. exact H.
--       rewrite <- Qopp_involutive. apply Qopp_le_compat. exact H0.
--       apply (Qpos_nonneg (c+c)).
--     + intros [H0 H1]. rewrite Qabs_pos.
--       2: unfold Qminus; rewrite <- Qle_minus_iff; exact H1.
--       apply (Qle_trans _ (j-k)).
--       apply Qplus_le_l. exact H. apply Qle_Qabs.
--   - intros. apply QboundAbs_elim.
--     + intros.
--       setoid_replace (- `c - `c) with (-(`c+`c))
--         by (unfold equiv, stdlib_rationals.Q_eq; ring).
--       rewrite Qabs_opp.
--       rewrite Qabs_pos. 2: apply (Qpos_nonneg (c+c)).
--       rewrite Qabs_Qminus. rewrite Qabs_pos.
--       apply Qplus_le_compat. exact H0.
--       rewrite <- Qopp_involutive. apply Qopp_le_compat. exact H.
--       apply (Qle_trans _ (`c + `c)).
--       apply (Qpos_nonneg (c+c)).
--       apply Qplus_le_compat. exact H0.
--       rewrite <- Qopp_involutive. apply Qopp_le_compat. exact H.
--     + intros. unfold Qminus.
--       rewrite Qopp_involutive, Qplus_comm, Qplus_opp_r.
--       apply Qabs_nonneg.
--     + intros [H0 H1].
--       setoid_replace (- `c - k) with (-(`c+k))
--         by (unfold equiv, stdlib_rationals.Q_eq; ring).
--       rewrite Qabs_opp. rewrite Qabs_pos, Qabs_Qminus.
--       apply (Qle_trans _ (k-j)).
--       rewrite Qplus_comm.
--       apply Qplus_le_r. rewrite <- Qopp_involutive.
--       apply Qopp_le_compat. exact H. apply Qle_Qabs.
--       apply (Qplus_le_l _ _ (-`c)). ring_simplify.
--       ring_simplify in H0. exact H0.
--   - intros [H0 H1]. apply QboundAbs_elim.
--     + intros. rewrite Qabs_Qminus, Qabs_pos.
--       rewrite Qabs_Qminus, Qabs_pos. apply Qplus_le_l, H.
--       unfold Qminus. rewrite <- Qle_minus_iff.
--       exact (Qle_trans _ _ _ H1 H). unfold Qminus.
--       rewrite <- Qle_minus_iff. exact H1.
--     + intros. unfold Qminus. rewrite Qopp_involutive, Qabs_pos.
--       apply (Qle_trans _ (j-k)). apply Qplus_le_r.
--       rewrite <- Qopp_involutive. apply Qopp_le_compat. exact H.
--       apply Qle_Qabs. apply (Qplus_le_l _ _ (`c)) in H0.
--       ring_simplify in H0. rewrite Qplus_comm. exact H0.
--     + intros [H2 H3]. apply Qle_refl.
-- Qed.

-- Lemma Qmult_uc_uncurry (c:Qpos)
--   : @is_UniformlyContinuousFunction
--       (ProductMS Q_as_MetricSpace Q_as_MetricSpace)
--       Q_as_MetricSpace
--       (fun ab => QboundAbs c (fst ab) * QboundAbs c (snd ab))
--       (fun e => Qmult_modulus c ((1#2)*e)).
-- Proof.
--   assert (forall i j k l : Q, Qabs (i*j-k*l) <= Qabs j * Qabs(i-k) + Qabs(j-l)*Qabs k)%Q
--     as multMaj.
--   { intros.
--     setoid_replace (i*j-k*l)%Q with (j*(i-k)+ (j-l)*k)%Q
--       by (unfold equiv, stdlib_rationals.Q_eq; ring).
--     apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
--     rewrite Qabs_Qmult, Qabs_Qmult. apply Qle_refl. }
--   assert (forall i:Q, Qabs (QboundAbs c i) <= ` c) as bound.
--   { intro i. apply Qabs_Qle_condition. split.
--     apply Qmax_ub_l. apply Qmax_lub.
--     apply (Qle_trans _ 0). apply (Qopp_le_compat 0).
--     apply Qpos_nonneg. apply Qpos_nonneg. apply Qmin_lb_l. }
--   simpl. unfold Qmult_modulus.
--   intros e1 [i j] [k l] [H H0]. simpl.
--   simpl in H, H0.
--   apply AbsSmall_Qabs.
--   apply AbsSmall_Qabs in H.
--   apply AbsSmall_Qabs in H0.
--   apply (Qle_trans _ _ _ (multMaj _ _ _ _)).
--   apply (Qle_trans _ (`c * (Qabs (QboundAbs c i - QboundAbs c k))
--                       + `c * (Qabs (QboundAbs c j - QboundAbs c l)))).
--   - apply Qplus_le_compat.
--     apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
--     apply bound.
--     rewrite Qmult_comm. apply Qmult_le_compat_r.
--     2: apply Qabs_nonneg. apply bound.
--   - apply (Qle_trans _ ((1#2)*`e1+(1#2)*`e1)).
--     apply Qplus_le_compat.
--     apply (Qle_trans _ (`c * Qabs (i-k))).
--     apply Qmult_le_l. apply Qpos_ispos. apply QboundAbs_contract.
--     rewrite Qmult_comm.
--     apply (Qmult_le_r _ _ (/ `c)).
--     apply Qinv_lt_0_compat, Qpos_ispos.
--     rewrite <- Qmult_assoc, Qmult_inv_r, Qmult_1_r.
--     exact H. apply Qpos_nonzero.
--     apply (Qle_trans _ (`c * Qabs (j-l))).
--     apply Qmult_le_l. apply Qpos_ispos. apply QboundAbs_contract.
--     rewrite Qmult_comm.
--     apply (Qmult_le_r _ _ (/ `c)).
--     apply Qinv_lt_0_compat, Qpos_ispos.
--     rewrite <- Qmult_assoc, Qmult_inv_r, Qmult_1_r.
--     exact H0. apply Qpos_nonzero.
--     ring_simplify. apply Qle_refl.
-- Qed.

-- Definition Qmult_uncurry (c : Qpos)
--   : (ProductMS Q_as_MetricSpace Q_as_MetricSpace) --> Q_as_MetricSpace
--   := Build_UniformlyContinuousFunction (@Qmult_uc_uncurry c).

-- Lemma CRmult_uncurry_eq : forall (c:Qpos) (x y : CR),
--     (' (-proj1_sig c)%Q <= x)%CR
--     -> (x <= ' (proj1_sig c)%Q)%CR
--     -> (CRmult_bounded c x y
--        == (Cmap (ProductMS_prelength QPrelengthSpace QPrelengthSpace)
--                 (Qmult_uncurry c) (undistrib_Complete (x,y))))%CR.
-- Proof.
--   (* Cannot use Cmap2_curry, because CRmult_bounded is not
--      exactly Qmult_uc_uncurry, the first factor is not bounded. *)
--   intros.
--   transitivity (CRmult_bounded c (CRboundAbs c x) y).
--   apply (ucFun2_wd (CRmult_bounded c) x (CRboundAbs c x)).
--   symmetry. apply (CRboundAbs_Eq c H H0). reflexivity.
--   intros e1 e2. rewrite Qplus_0_r. simpl.
--   unfold Cap_raw; simpl.
--   assert (forall i, eq (QposInf_bind (λ e : Qpos, e) i) i) as bind_id.
--   { intro i. destruct i; reflexivity. }
--   rewrite bind_id. clear bind_id.
--   assert (forall i j k l : Q, Qabs (i*j-k*l) <= Qabs i * Qabs(j-l) + Qabs(i-k)*Qabs l)%Q
--     as multMaj.
--   { intros.
--     setoid_replace (i*j-k*l)%Q with (i*(j-l)+ (i-k)*l)%Q
--       by (unfold equiv, stdlib_rationals.Q_eq; ring).
--     apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
--     rewrite Qabs_Qmult, Qabs_Qmult. apply Qle_refl. }
--   apply AbsSmall_Qabs.
--   apply (Qle_trans _ _ _ (multMaj _ _ _ _)).
--   apply (Qle_trans _ ((1#2)*`e1 + (1#2)*`e2 +((1#2)*`e1 +(1#2)*`e2))).
--   2: ring_simplify; apply Qle_refl.
--   apply Qplus_le_compat.
--   - apply (Qle_trans
--              _ ( Qabs
--           (approximate y
--              (Qscale_modulus
--                 (QboundAbs c (approximate x (Qmult_modulus c ((1 # 2) * e1))))
--                 ((1 # 2) * e1)) -
--            (approximate y (Qmult_modulus c ((1 # 2) * e2))))
--           * Qabs (QboundAbs c (approximate x (Qmult_modulus c ((1 # 2) * e1)))))).
--     rewrite Qmult_comm.
--     apply Qmult_le_compat_r.
--     apply QboundAbs_contract. apply Qabs_nonneg.
--     unfold Qscale_modulus.
--     simpl (Qmult_modulus c ((1 # 2) * e1)).
--     destruct (QboundAbs c (approximate x (Qmult_modulus c ((1 # 2) ↾ @eq_refl comparison Datatypes.Lt * e1)))) eqn:des.
--     destruct Qnum.
--     + setoid_replace (0#Qden) with (0#1) by reflexivity.
--       rewrite Qmult_0_r. apply (Qpos_nonneg ((1#2)*e1+(1#2)*e2)).
--     + rewrite Qmult_comm, Qabs_pos. 2: discriminate.
--       apply (Qle_trans _ ((Zpos p#Qden) *
--                           ((Zpos Qden # p)%Q * ((1 # 2)%Q * `e1)
--                            + (1 # 2) * `e2 / `c))).
--       apply Qmult_le_l. reflexivity.
--       pose proof (regFun_prf y ((Zpos Qden # p)%Q ↾ eq_refl * ((1 # 2)%Q ↾ eq_refl * e1))%Qpos
--                              ((1 # 2) * e2 * Qpos_inv c)%Qpos) as H3.
--       apply AbsSmall_Qabs in H3. exact H3.
--       rewrite Qmult_plus_distr_r.
--       rewrite Qmult_assoc.
--       setoid_replace ((Zpos p # Qden) * (Zpos Qden # p))%Q with (1#1)%Q
--         by (unfold equiv, stdlib_rationals.Q_eq; unfold Qeq; simpl; rewrite Pos.mul_1_r, Pos.mul_comm; reflexivity).
--       rewrite Qmult_1_l. apply Qplus_le_r.
--       unfold Qdiv. rewrite Qmult_assoc.
--       apply Qle_shift_div_r. apply Qpos_ispos.
--       rewrite Qmult_comm. apply Qmult_le_l.
--       apply (Qpos_ispos ((1#2)*e2)).
--       rewrite <- des. apply Qmax_lub.
--       apply (Qle_trans _ 0). apply (Qopp_le_compat 0).
--       apply Qpos_nonneg. apply Qpos_nonneg. apply Qmin_lb_l.
--     + rewrite Qmult_comm, Qabs_neg. 2: discriminate.
--       setoid_replace (- (Z.neg p # Qden)) with (Zpos p # Qden) by reflexivity.
--       apply (Qle_trans _ ((Zpos p#Qden) *
--                           ((Zpos Qden # p)%Q * ((1 # 2)%Q * `e1)
--                            + (1 # 2) * `e2 / `c))).
--       apply Qmult_le_l. reflexivity.
--       pose proof (regFun_prf y ((Zpos Qden # p)%Q ↾ eq_refl * ((1 # 2)%Q ↾ eq_refl * e1))%Qpos
--                              ((1 # 2) * e2 * Qpos_inv c)%Qpos) as H3.
--       apply AbsSmall_Qabs in H3. exact H3.
--       rewrite Qmult_plus_distr_r.
--       rewrite Qmult_assoc.
--       setoid_replace ((Zpos p # Qden) * (Zpos Qden # p))%Q with (1#1)%Q
--         by (unfold equiv, stdlib_rationals.Q_eq; unfold Qeq; simpl; rewrite Pos.mul_1_r, Pos.mul_comm; reflexivity).
--       rewrite Qmult_1_l. apply Qplus_le_r.
--       unfold Qdiv. rewrite Qmult_assoc.
--       apply Qle_shift_div_r. apply Qpos_ispos.
--       rewrite Qmult_comm. apply Qmult_le_l.
--       apply (Qpos_ispos ((1#2)*e2)).
--       rewrite <- (Qopp_involutive (`c)).
--       setoid_replace (Zpos p # Qden) with (-(Z.neg p # Qden)) by reflexivity.
--       apply Qopp_le_compat.
--       rewrite <- des. apply Qmax_ub_l.
--   - apply (Qle_trans _ (Qabs
--     (approximate x (Qmult_modulus c ((1 # 2) * e1)) -
--      approximate x (Qmult_modulus c ((1 # 2) * e2)))
--           * Qabs (QboundAbs c (approximate y (Qmult_modulus c ((1 # 2) ↾ eq_refl * e2)))))).
--     apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
--     apply QboundAbs_contract.
--     rewrite QboundAbs_abs.
--     apply (Qle_trans _ (`c * Qabs
--     (approximate x (Qmult_modulus c ((1 # 2) * e1)) -
--      approximate x (Qmult_modulus c ((1 # 2) * e2))))).
--     rewrite Qmult_comm.
--     apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
--     apply Qmin_lb_r.
--     apply (Qle_trans _ (`c * ((1#2)*`e1 / `c + (1#2)*`e2 / `c))).
--     apply Qmult_le_l. apply Qpos_ispos.
--     unfold Qmult_modulus.
--     pose proof (regFun_prf x ((1 # 2) * e1 * Qpos_inv c)%Qpos
--                            ((1 # 2) * e2 * Qpos_inv c)%Qpos) as H3.
--     apply AbsSmall_Qabs in H3. exact H3.
--     rewrite Qmult_plus_distr_r.
--     apply Qplus_le_compat.
--     unfold Qdiv. rewrite Qmult_assoc.
--     apply Qle_shift_div_r. apply Qpos_ispos.
--     rewrite Qmult_comm. apply Qle_refl.
--     unfold Qdiv. rewrite Qmult_assoc.
--     apply Qle_shift_div_r. apply Qpos_ispos.
--     rewrite Qmult_comm. apply Qle_refl.
-- Qed.

-- (* Request bounds on all left factors : x and CRmult_bounded c x y. *)
-- Lemma CRmult_uncurry_eq_3 : forall (c:Qpos) (x y z : CR),
--     (' (- ` c)%Q <= x)%CR
--     -> (x <= 'proj1_sig c)%CR
--     -> (' (- ` c)%Q <= CRmult_bounded c x y)%CR
--     -> (CRmult_bounded c x y <= 'proj1_sig c)%CR
--     -> (CRmult_bounded c (CRmult_bounded c x y) z
--        == Cmap (ProductMS_prelength
--                   (ProductMS_prelength QPrelengthSpace QPrelengthSpace)
--                   QPrelengthSpace)
--                (uc_compose (Qmult_uncurry c) (together (Qmult_uncurry c) (uc_id Q_as_MetricSpace)))
--                (undistrib_Complete (undistrib_Complete (x,y), z)))%CR.
-- Proof.
--   intros.
--   assert (forall a, Qabs (QboundAbs c a) <= `c) as qbound_bound.
--   { intros a. rewrite QboundAbs_abs. apply Qmin_lb_r. }
--   rewrite (@CRmult_uncurry_eq c (CRmult_bounded c x y) z); try assumption.
--   assert (msp_eq (undistrib_Complete (CRmult_bounded c x y, z))
--                 (undistrib_Complete ((Cmap (ProductMS_prelength QPrelengthSpace QPrelengthSpace)
--                   (Qmult_uncurry c) (undistrib_Complete (x,y))), z))) as H4.
--   { intros e1 e2. split.
--     apply (@CRmult_uncurry_eq c x y H H0).
--     rewrite Qplus_0_r.
--     apply regFun_prf. }
--   rewrite H4. clear H4.
--   rewrite fast_MonadLaw2.
--   apply Cmap_wd. reflexivity.
--   intros e1 e2. split.
--   - simpl. apply AbsSmall_Qabs.
--     assert (forall i j k l : Q, Qabs (i*j-k*l) <= Qabs i * Qabs(j-l) + Qabs(i-k)*Qabs l)%Q
--       as multMaj.
--     { intros.
--       setoid_replace (i*j-k*l)%Q with (i*(j-l)+ (i-k)*l)%Q
--         by (unfold equiv, stdlib_rationals.Q_eq; ring).
--       apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
--       rewrite Qabs_Qmult, Qabs_Qmult. apply Qle_refl. }
--     apply (Qle_trans _ ((1#2)*`e1 + (1#2)*`e2 +((1#2)*`e1 +(1#2)*`e2))).
--     2: ring_simplify; apply Qle_refl.
--     apply (Qle_trans _ _ _ (multMaj _ _ _ _)). clear multMaj.
--     apply Qplus_le_compat.
--     + apply (Qle_trans _ (`c *
--                         (Qabs
--     (Qmax (- ` c)
--        (Qmin (` c) (approximate y (Qmult_modulus c ((1 # 2) ↾ eq_refl * e1)))) -
--      Qmax (- ` c)
--        (Qmin (` c)
--              (approximate y (Qpos_min ((1 # 2) ↾ eq_refl * e2 * Qpos_inv c) e2))))))).
--       apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
--       apply qbound_bound.
--       rewrite Qmult_comm.
--       apply (Qle_trans _ (Qabs (approximate y (Qmult_modulus c ((1 # 2) ↾ eq_refl * e1)) - approximate y (Qpos_min ((1 # 2) ↾ eq_refl * e2 * Qpos_inv c) e2)) * `c)).
--       apply Qmult_le_compat_r. 2: apply Qpos_nonneg.
--       apply QboundAbs_contract.
--       apply (Qle_trans _ (((1#2)*`e1 / `c + (1#2)*`e2 / `c) * `c)).
--       apply Qmult_le_r. apply Qpos_ispos.
--       unfold Qmult_modulus.
--       pose proof (regFun_prf y ((1 # 2) * e1 * Qpos_inv c)%Qpos
--                              (Qpos_min ((1 # 2) * e2 * Qpos_inv c)%Qpos e2)) as H4.
--       apply AbsSmall_Qabs in H4.
--       apply (Qle_trans _ _ _ H4). clear H4. apply Qplus_le_r.
--       rewrite Q_Qpos_min. simpl. apply Qmin_lb_l.
--       rewrite Qmult_plus_distr_l.
--       apply Qplus_le_compat.
--       unfold Qdiv. rewrite Qmult_comm, Qmult_assoc.
--       apply Qle_shift_div_r. apply Qpos_ispos.
--       rewrite Qmult_comm. apply Qle_refl.
--       unfold Qdiv. rewrite Qmult_comm, Qmult_assoc.
--       apply Qle_shift_div_r. apply Qpos_ispos.
--       rewrite Qmult_comm. apply Qle_refl.
--     + rewrite Qmult_comm. apply (Qle_trans _ (`c *
--                         (Qabs
--     (Qmax (- ` c)
--        (Qmin (` c) (approximate x (Qmult_modulus c ((1 # 2) ↾ eq_refl * e1)))) -
--      Qmax (- ` c)
--        (Qmin (` c)
--              (approximate x (Qpos_min ((1 # 2) ↾ eq_refl * e2 * Qpos_inv c) e2))))))).
--       apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
--       apply qbound_bound.
--       rewrite Qmult_comm.
--       apply (Qle_trans _ (Qabs (approximate x (Qmult_modulus c ((1 # 2) ↾ eq_refl * e1)) - approximate x (Qpos_min ((1 # 2) ↾ eq_refl * e2 * Qpos_inv c) e2)) * `c)).
--       apply Qmult_le_compat_r. 2: apply Qpos_nonneg.
--       apply QboundAbs_contract.
--       apply (Qle_trans _ (((1#2)*`e1 / `c + (1#2)*`e2 / `c) * `c)).
--       apply Qmult_le_r. apply Qpos_ispos.
--       unfold Qmult_modulus.
--       pose proof (regFun_prf x ((1 # 2) * e1 * Qpos_inv c)%Qpos
--                              (Qpos_min ((1 # 2) * e2 * Qpos_inv c)%Qpos e2)) as H4.
--       apply AbsSmall_Qabs in H4.
--       apply (Qle_trans _ _ _ H4). clear H4. apply Qplus_le_r.
--       rewrite Q_Qpos_min. simpl. apply Qmin_lb_l.
--       rewrite Qmult_plus_distr_l.
--       apply Qplus_le_compat.
--       unfold Qdiv. rewrite Qmult_comm, Qmult_assoc.
--       apply Qle_shift_div_r. apply Qpos_ispos.
--       rewrite Qmult_comm. apply Qle_refl.
--       unfold Qdiv. rewrite Qmult_comm, Qmult_assoc.
--       apply Qle_shift_div_r. apply Qpos_ispos.
--       rewrite Qmult_comm. apply Qle_refl.
--   - simpl.
--     assert (`e1 + proj1_sig (Qpos_min ((1 # 2) ↾ eq_refl * e2 * Qpos_inv c) e2)
--             <= `e1 + `e2) as H4.
--     { apply Qplus_le_r. apply Qpos_min_lb_r. }
--     rewrite Qplus_0_r.
--     apply (ball_weak_le _ _ _ H4). apply regFun_prf.
-- Qed.

-- (* Request bounds on all left factors : x and y. *)
-- Lemma CRmult_uncurry_eq_3r : forall (c:Qpos) (x y z : CR),
--     (' (- ` c)%Q <= x)%CR
--     -> (x <= 'proj1_sig c)%CR
--     -> (' (- ` c)%Q <= y)%CR
--     -> (y <= 'proj1_sig c)%CR
--     -> (CRmult_bounded c x (CRmult_bounded c y z)
--        == Cmap (ProductMS_prelength
--                   (ProductMS_prelength QPrelengthSpace QPrelengthSpace)
--                   QPrelengthSpace)
--                (uc_compose (Qmult_uncurry c)
--                            (uc_compose (together (uc_id Q_as_MetricSpace) (Qmult_uncurry c)) (uc_assoc _ _ _)))
--                (undistrib_Complete (undistrib_Complete (x,y), z)))%CR.
-- Proof.
--   intros.
--   assert (forall a, Qabs (QboundAbs c a) <= `c) as qbound_bound.
--   { intros a. rewrite QboundAbs_abs. apply Qmin_lb_r. }
--   rewrite (@CRmult_uncurry_eq c x (CRmult_bounded c y z)); try assumption.
--   assert (msp_eq (undistrib_Complete (x, CRmult_bounded c y z))
--                 (undistrib_Complete
--                    (x, Cmap (ProductMS_prelength QPrelengthSpace QPrelengthSpace)
--                             (Qmult_uncurry c) (undistrib_Complete (y,z))))) as H4.
--   { intros e1 e2. split.
--     rewrite Qplus_0_r.
--     apply regFun_prf.
--     apply (@CRmult_uncurry_eq c y z H1 H2). }
--   rewrite H4. clear H4.
--   rewrite fast_MonadLaw2.
--   apply Cmap_wd. reflexivity.
--   intros e1 e2. rewrite Qplus_0_r. split.
--   - simpl.
--     assert (`e1 + proj1_sig (Qpos_min e2 ((1 # 2) ↾ eq_refl * e2 * Qpos_inv c))
--             <= `e1 + `e2) as H4.
--     { apply Qplus_le_r. apply Qpos_min_lb_l. }
--     apply (ball_weak_le _ _ _ H4). apply regFun_prf.
--   - simpl. apply AbsSmall_Qabs.
--     assert (forall i j k l : Q, Qabs (i*j-k*l) <= Qabs i * Qabs(j-l) + Qabs(i-k)*Qabs l)%Q
--       as multMaj.
--     { intros.
--       setoid_replace (i*j-k*l)%Q with (i*(j-l)+ (i-k)*l)%Q
--         by (unfold equiv, stdlib_rationals.Q_eq; ring).
--       apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
--       rewrite Qabs_Qmult, Qabs_Qmult. apply Qle_refl. }
--     apply (Qle_trans _ ((1#2)*`e1 + (1#2)*`e2 +((1#2)*`e1 +(1#2)*`e2))).
--     2: ring_simplify; apply Qle_refl.
--     apply (Qle_trans _ _ _ (multMaj _ _ _ _)). clear multMaj.
--     apply Qplus_le_compat.
--     + apply (Qle_trans _ (`c *
--                         (Qabs
--     (Qmax (- ` c)
--        (Qmin (` c) (approximate z (Qmult_modulus c ((1 # 2) ↾ eq_refl * e1)))) -
--      Qmax (- ` c)
--        (Qmin (` c)
--              (approximate z (Qpos_min e2 ((1 # 2) ↾ eq_refl * e2 * Qpos_inv c)))))))).
--       apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
--       apply qbound_bound.
--       rewrite Qmult_comm.
--       apply (Qle_trans _ (Qabs (approximate z (Qmult_modulus c ((1 # 2) ↾ eq_refl * e1)) - approximate z (Qpos_min e2 ((1 # 2) ↾ eq_refl * e2 * Qpos_inv c))) * `c)).
--       apply Qmult_le_compat_r. 2: apply Qpos_nonneg.
--       apply QboundAbs_contract.
--       apply (Qle_trans _ (((1#2)*`e1 / `c + (1#2)*`e2 / `c) * `c)).
--       apply Qmult_le_r. apply Qpos_ispos.
--       unfold Qmult_modulus.
--       pose proof (regFun_prf z ((1 # 2) * e1 * Qpos_inv c)%Qpos
--                              (Qpos_min e2 ((1 # 2) * e2 * Qpos_inv c)%Qpos)) as H4.
--       apply AbsSmall_Qabs in H4.
--       apply (Qle_trans _ _ _ H4). clear H4. apply Qplus_le_r.
--       rewrite Q_Qpos_min. simpl. apply Qmin_lb_r.
--       rewrite Qmult_plus_distr_l.
--       apply Qplus_le_compat.
--       unfold Qdiv. rewrite Qmult_comm, Qmult_assoc.
--       apply Qle_shift_div_r. apply Qpos_ispos.
--       rewrite Qmult_comm. apply Qle_refl.
--       unfold Qdiv. rewrite Qmult_comm, Qmult_assoc.
--       apply Qle_shift_div_r. apply Qpos_ispos.
--       rewrite Qmult_comm. apply Qle_refl.
--     + rewrite Qmult_comm. apply (Qle_trans _ (`c *
--                         (Qabs
--     (Qmax (- ` c)
--        (Qmin (` c) (approximate y (Qmult_modulus c ((1 # 2) ↾ eq_refl * e1)))) -
--      Qmax (- ` c)
--        (Qmin (` c)
--              (approximate y (Qpos_min e2 ((1 # 2) ↾ eq_refl * e2 * Qpos_inv c)))))))).
--       apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
--       apply qbound_bound.
--       rewrite Qmult_comm.
--       apply (Qle_trans _ (Qabs (approximate y (Qmult_modulus c ((1 # 2) ↾ eq_refl * e1)) - approximate y (Qpos_min e2 ((1 # 2) ↾ eq_refl * e2 * Qpos_inv c))) * `c)).
--       apply Qmult_le_compat_r. 2: apply Qpos_nonneg.
--       apply QboundAbs_contract.
--       apply (Qle_trans _ (((1#2)*`e1 / `c + (1#2)*`e2 / `c) * `c)).
--       apply Qmult_le_r. apply Qpos_ispos.
--       unfold Qmult_modulus.
--       pose proof (regFun_prf y ((1 # 2) * e1 * Qpos_inv c)%Qpos
--                              (Qpos_min e2 ((1 # 2) * e2 * Qpos_inv c)%Qpos)) as H4.
--       apply AbsSmall_Qabs in H4.
--       apply (Qle_trans _ _ _ H4). clear H4. apply Qplus_le_r.
--       rewrite Q_Qpos_min. simpl. apply Qmin_lb_r.
--       rewrite Qmult_plus_distr_l.
--       apply Qplus_le_compat.
--       unfold Qdiv. rewrite Qmult_comm, Qmult_assoc.
--       apply Qle_shift_div_r. apply Qpos_ispos.
--       rewrite Qmult_comm. apply Qle_refl.
--       unfold Qdiv. rewrite Qmult_comm, Qmult_assoc.
--       apply Qle_shift_div_r. apply Qpos_ispos.
--       rewrite Qmult_comm. apply Qle_refl.
-- Qed.

-- Lemma Qmult_uncurry_assoc : forall (i j k:Q) (b : Qpos),
--     Qabs i <= `b
--     -> Qabs j <= `b
--     -> Qabs k <= `b
--     -> Qabs (j*k) <= `b
--     -> Qabs (i*j) <= `b
--     -> Qmult_uncurry b (Qmult_uncurry b (i, j), k)
--       == Qmult_uncurry b (i, Qmult_uncurry b (j,k)).
-- Proof.
--   intros. simpl.
--   apply Qabs_Qle_condition in H.
--   destruct H as [ilower iupper].
--   apply Qabs_Qle_condition in H0.
--   destruct H0 as [jlower jupper].
--   apply Qabs_Qle_condition in H1.
--   destruct H1 as [klower kupper].
--   apply Qabs_Qle_condition in H2.
--   destruct H2 as [jklower jkupper].
--   apply Qabs_Qle_condition in H3.
--   destruct H3 as [ijlower ijupper].
--   assert (forall a:Q, a <= `b -> Qmin (`b) a == a)%Q as elim_min.
--   { apply Qle_min_r. }
--   assert (forall a:Q, -(`b) <= a -> Qmax (-(`b)) a == a)%Q as elim_max.
--   { intros. apply Qle_max_r, H. }
--   rewrite (elim_min j jupper).
--   rewrite (elim_min i iupper).
--   rewrite (elim_min k kupper).
--   rewrite (elim_max j jlower).
--   rewrite (elim_max i ilower).
--   rewrite (elim_max k klower).
--   rewrite (elim_min (j*k) jkupper).
--   rewrite (elim_min (i*j) ijupper).
--   rewrite (elim_max (j*k) jklower).
--   rewrite (elim_max (i*j) ijlower).
--   rewrite Qmult_assoc. reflexivity.
-- Qed.

-- Lemma quarter_approx_le_abs_1 :
--   forall (x : CR) (q : Q),
--     Qabs (q - approximate x (Qpos2QposInf (1 # 4))) <= (3#4)
--     -> Qabs q <= ` (CR_b (1 ↾ eq_refl) x + 1 ↾ eq_refl)%Qpos.
-- Proof.
--   intros. simpl.
--   apply (Qle_trans _ _ _ (Qabs_triangle_reverse _ _)) in H.
--   apply (Qplus_le_l _ _ (-Qabs (approximate x (Qpos2QposInf (1#4))))).
--   apply (Qle_trans _ _ _ H). clear H q.
--   pose proof (regFun_prf x (1#4)%Qpos (1#1)%Qpos).
--   apply AbsSmall_Qabs in H.
--   apply Qopp_le_compat in H. apply (Qplus_le_r _ _ (2#1)) in H.
--   setoid_replace (2 + - (` ((1 # 4) ↾ eq_refl) + ` (1 ↾ eq_refl)))
--     with (3#4) in H by reflexivity.
--   rewrite <- Qplus_assoc, <- Qplus_assoc, Qplus_comm, Qplus_assoc.
--   setoid_replace ((1#1)+(1#1)) with (2#1) by reflexivity.
--   apply (Qle_trans _ _ _ H). clear H.
--   rewrite <- Qplus_assoc. apply Qplus_le_r.
--   setoid_replace (- Qabs (approximate x (Qpos2QposInf (1 # 4)))
--                   + Qabs (approximate x (Qpos2QposInf (1#1))))%Q
--     with (- (Qabs (approximate x (Qpos2QposInf (1 # 4)))
--                   - Qabs (approximate x (Qpos2QposInf (1#1)))))
--     by (unfold equiv, stdlib_rationals.Q_eq; ring).
--   apply Qopp_le_compat, Qabs_triangle_reverse.
-- Qed.

-- Lemma QboundAbs_lowerBound_2 : forall (a b : Qpos) (c d : Q),
--     (- (`a * `b) <= QboundAbs a c * QboundAbs b d)%Q.
-- Proof.
--   intros. apply (Qle_trans _ (-Qabs (QboundAbs a c * QboundAbs b d))).
--   apply Qopp_le_compat.
--   rewrite Qabs_Qmult. rewrite QboundAbs_abs, QboundAbs_abs.
--   apply (Qle_trans _ (`a * Qmin (Qabs d) (`b))).
--   apply Qmult_le_compat_r. apply Qmin_lb_r.
--   apply Qmin_glb. apply Qabs_nonneg. apply Qpos_nonneg.
--   apply Qmult_le_l. apply Qpos_ispos. apply Qmin_lb_r.
--   rewrite <- (Qopp_involutive (QboundAbs a c * QboundAbs b d)) at 2.
--   apply Qopp_le_compat. rewrite <- Qabs_opp.
--   apply Qle_Qabs.
-- Qed.

-- Lemma QboundAbs_upperBound_2 : forall (a b : Qpos) (c d : Q),
--     (QboundAbs a c * QboundAbs b d <= `a * `b)%Q.
-- Proof.
--   intros. apply (Qle_trans _ _ _ (Qle_Qabs _)).
--   rewrite Qabs_Qmult. rewrite QboundAbs_abs, QboundAbs_abs.
--   apply (Qle_trans _ (`a * Qmin (Qabs d) (`b))).
--   apply Qmult_le_compat_r. apply Qmin_lb_r.
--   apply Qmin_glb. apply Qabs_nonneg. apply Qpos_nonneg.
--   apply Qmult_le_l. apply Qpos_ispos. apply Qmin_lb_r.
-- Qed.

-- Lemma CR_b_lowerBound_2 : forall x y : CR,
--     ('(-proj1_sig ((CR_b (1#1) x) * CR_b (1#1) y)%Qpos)%Q <= x * y)%CR.
-- Proof.
--   intros.
--   rewrite <- (CRboundAbs_Eq (CR_b (1#1) x)
--                            (CR_b_lowerBound (1#1) x) (CR_b_upperBound (1#1) x)) at 2.
--   unfold CRmult, ucFun2.
--   intros e. simpl. unfold Cap_raw; simpl.
--   unfold Cap_raw; simpl.
--   apply (Qle_trans _ 0). apply (Qopp_le_compat 0), Qpos_nonneg.
--   unfold Qminus. rewrite <- Qle_minus_iff.
--   apply (QboundAbs_lowerBound_2 (CR_b (1#1) x) (CR_b (1#1) y)).
-- Qed.

-- Lemma CR_b_upperBound_2 : forall x y : CR,
--     (x * y <= 'proj1_sig ((CR_b (1#1) x) * CR_b (1#1) y)%Qpos)%CR.
-- Proof.
--   intros.
--   rewrite <- (CRboundAbs_Eq (CR_b (1#1) x)
--                            (CR_b_lowerBound (1#1) x) (CR_b_upperBound (1#1) x)) at 1.
--   unfold CRmult, ucFun2.
--   intros e. simpl. unfold Cap_raw; simpl.
--   unfold Cap_raw; simpl.
--   apply (Qle_trans _ 0). apply (Qopp_le_compat 0), Qpos_nonneg.
--   unfold Qminus. rewrite <- Qle_minus_iff.
--   apply (QboundAbs_upperBound_2 (CR_b (1#1) x) (CR_b (1#1) y)).
-- Qed.

-- Lemma CRle_Qle : forall (x y:Q), (inject_Q_CR x <= inject_Q_CR y)%CR <-> (x <= y)%Q.
-- Proof.
--  split.
--   intros H.
--   destruct (Qlt_le_dec y x) as [X|X];[|assumption].
--   destruct (Qpos_sub _ _ X) as [c Hc].
--   assert (Y:=(H ((1#2)*c)%Qpos)).
--   simpl in Y.
--   unfold Cap_raw in Y; simpl in Y.
--   rewrite -> Qle_minus_iff in Y.
--   rewrite -> Hc in Y.
--   autorewrite with QposElim in Y.
--   ring_simplify in Y.
--   elim (Qle_not_lt _ _ Y).
--   rewrite -> Qlt_minus_iff.
--   ring_simplify.
--   apply Q.Qmult_lt_0_compat; auto with *.
--  intros H e.
--  simpl.
--  unfold Cap_raw; simpl.
--  rewrite -> Qle_minus_iff in H.
--  apply Qle_trans with (0%Q);[|assumption].
--  rewrite -> Qle_minus_iff; ring_simplify.
--  apply Qpos_nonneg.
-- Qed.

-- Lemma CRmult_assoc_yfactor_le
--   : forall (x y z : CR),
--     let b := ((CR_b (1#1) x + (1#1))
--             * (CR_b (1#1) y + (1#1)) * (CR_b (1#1) z + (1#1)))%Qpos in
--     (` (CR_b (1 ↾ eq_refl) y) + 1 <= ` b)%Q.
-- Proof.
--   intros. unfold b. simpl.
--   rewrite <- Qmult_assoc, (Qmult_comm (Qabs (approximate y (Qpos2QposInf (1#1))) + 1 + 1)).
--   rewrite Qmult_assoc.
--   rewrite <- Qmult_1_l, <- Qmult_1_l.
--   rewrite Qmult_assoc.
--   apply Qmult_le_compat_r.
--   apply (Qpos_mult_le_compat (1#1) (1#1)).
--   rewrite <- Qplus_0_l. apply Qplus_le_l, (Qpos_nonneg (CR_b (1#1) x)).
--   rewrite <- Qplus_0_l. apply Qplus_le_l, (Qpos_nonneg (CR_b (1#1) z)).
--   rewrite <- Qplus_assoc. apply (Qle_trans _ (0+2)).
--   discriminate. apply Qplus_le_l. apply Qabs_nonneg.
-- Qed.

-- Lemma CRmult_assoc_xfactor_le
--   : forall (x y z : CR),
--     let b := ((CR_b (1#1) x + (1#1))
--             * (CR_b (1#1) y + (1#1)) * (CR_b (1#1) z + (1#1)))%Qpos in
--     (` (CR_b (1 ↾ eq_refl) x) + 1 <= ` b)%Q.
-- Proof.
--   intros. unfold b. simpl.
--   rewrite <- Qmult_assoc, Qmult_comm.
--   rewrite <- Qmult_1_l, <- Qmult_1_l at 1.
--   rewrite Qmult_assoc.
--   apply Qmult_le_compat_r.
--   apply (Qpos_mult_le_compat (1#1) (1#1)).
--   rewrite <- Qplus_0_l. apply Qplus_le_l, (Qpos_nonneg (CR_b (1#1) y)).
--   rewrite <- Qplus_0_l. apply Qplus_le_l, (Qpos_nonneg (CR_b (1#1) z)).
--   rewrite <- Qplus_assoc. apply (Qle_trans _ (0+2)).
--   discriminate. apply Qplus_le_l. apply Qabs_nonneg.
-- Qed.

-- Lemma CRmult_assoc_zfactor_le
--   : forall (x y z : CR),
--     let b := ((CR_b (1#1) x + (1#1))
--             * (CR_b (1#1) y + (1#1)) * (CR_b (1#1) z + (1#1)))%Qpos in
--     (` (CR_b (1 ↾ eq_refl) z) + 1 <= ` b)%Q.
-- Proof.
--   intros. rewrite <- Qmult_1_l, <- Qmult_1_l, Qmult_assoc.
--   apply Qmult_le_compat_r. 2: apply Qpos_nonneg.
--   apply (Qpos_mult_le_compat (1#1) (1#1)).
--   rewrite <- Qplus_0_l. apply Qplus_le_l, Qpos_nonneg.
--   rewrite <- Qplus_0_l. apply Qplus_le_l, Qpos_nonneg.
-- Qed.

-- (* Request bounds on all left factors : x, CRmult_bounded b x y, and y. *)
-- Lemma CRmult_assoc_bounded (x y z : CR) :
--   let b := ((CR_b (1#1) x + (1#1))
--             * (CR_b (1#1) y + (1#1)) * (CR_b (1#1) z + (1#1)))%Qpos in
--   (CRmult_bounded b (CRmult_bounded b x y) z
--    == CRmult_bounded b x (CRmult_bounded b y z))%CR.
-- Proof.
--   intros.
--   assert (' (- ` b)%Q <= x)%CR as xlower.
--   { apply (@CRle_trans _ (' (-proj1_sig (CR_b (1#1) x))%Q)).
--     2: apply (CR_b_lowerBound _ _).
--     apply CRle_Qle. apply Qopp_le_compat.
--     apply (Qle_trans _ ((` (CR_b (1#1)%Qpos x) + (1#1)))).
--     rewrite <- Qplus_0_r at 1. apply Qplus_le_r. discriminate.
--     apply CRmult_assoc_xfactor_le. }
--   assert (x <= ' (` b)%Q)%CR as xupper.
--   { apply (@CRle_trans _ (' (proj1_sig (CR_b (1#1) x))%Q)).
--     apply CR_b_upperBound.
--     apply CRle_Qle.
--     apply (Qle_trans _ ((` (CR_b (1#1)%Qpos x) + (1#1)))).
--     rewrite <- Qplus_0_r at 1. apply Qplus_le_r. discriminate.
--     apply CRmult_assoc_xfactor_le. }
--   assert (' (- ` b)%Q <= y)%CR as ylower.
--   { apply (@CRle_trans _ (' (-proj1_sig (CR_b (1#1) y))%Q)).
--     2: apply (CR_b_lowerBound _ _).
--     apply CRle_Qle. apply Qopp_le_compat.
--     apply (Qle_trans _ ((` (CR_b (1#1)%Qpos y) + (1#1)))).
--     rewrite <- Qplus_0_r at 1. apply Qplus_le_r. discriminate.
--     apply CRmult_assoc_yfactor_le. }
--   assert (y <= ' (` b)%Q)%CR as yupper.
--   { apply (@CRle_trans _ (' (proj1_sig (CR_b (1#1) y))%Q)).
--     apply CR_b_upperBound.
--     apply CRle_Qle.
--     apply (Qle_trans _ ((` (CR_b (1#1)%Qpos y) + (1#1)))).
--     rewrite <- Qplus_0_r at 1. apply Qplus_le_r. discriminate.
--     apply CRmult_assoc_yfactor_le. }
--   assert (` (CR_b (1 ↾ eq_refl) x + 1 ↾ eq_refl)%Qpos *
--           ` (CR_b (1 ↾ eq_refl) y + 1 ↾ eq_refl)%Qpos <= ` b) as xyfactor_le.
--   { rewrite <- Qmult_1_l.
--     unfold b. simpl.
--     rewrite (Qmult_comm ((Qabs (approximate x (Qpos2QposInf (1 ↾ eq_refl))) + 1 + 1) *
--                          (Qabs (approximate y (Qpos2QposInf (1 ↾ eq_refl))) + 1 + 1))).
--     apply Qmult_le_compat_r.
--     apply (Qle_trans _ (0+2)). discriminate.
--     rewrite <- Qplus_assoc.
--     apply Qplus_le_l, Qabs_nonneg.
--     apply Qmult_le_0_compat.
--     apply (Qle_trans _ (0+2)). discriminate.
--     rewrite <- Qplus_assoc.
--     apply Qplus_le_l, Qabs_nonneg.
--     apply (Qle_trans _ (0+2)). discriminate.
--     rewrite <- Qplus_assoc.
--     apply Qplus_le_l, Qabs_nonneg. }
--   rewrite CRmult_uncurry_eq_3r.
--   rewrite CRmult_uncurry_eq_3.
--   2: exact xlower. 2: exact xupper.
--   4: exact xlower. 4: exact xupper.
--   4: exact ylower. 4: exact yupper.
--   (* Qmult_uncurry is not associative everywhere,
--      so use Cmap_wd_loc. *)
--   apply Cmap_wd_loc with (e:=(1#4)%Qpos). intros [[i j] k].
--   intros H.
--   specialize (H (1#4)%Qpos (1#4)%Qpos).
--   destruct H,H.
--   simpl in H1. simpl in H0.
--   apply Qball_0.
--   apply (@Qmult_uncurry_assoc i j k b).
--   - clear H0 H1. simpl in H. apply AbsSmall_Qabs in H.
--     apply (Qle_trans _ (proj1_sig (CR_b (1#1) x + (1#1))%Qpos)).
--     setoid_replace ((1#4)+(1#4)+(1#4)) with (3#4) in H by reflexivity.
--     apply quarter_approx_le_abs_1, H. clear H.
--     apply CRmult_assoc_xfactor_le.
--   - clear H H0.
--     apply (Qle_trans _ (proj1_sig (CR_b (1#1) y + (1#1))%Qpos)).
--     apply AbsSmall_Qabs in H1.
--     setoid_replace ((1#4)+(1#4)+(1#4)) with (3#4) in H1 by reflexivity.
--     apply quarter_approx_le_abs_1, H1. apply CRmult_assoc_yfactor_le.
--   - clear H H1.
--     apply (Qle_trans _ (proj1_sig (CR_b (1#1) z + (1#1))%Qpos)).
--     apply AbsSmall_Qabs in H0.
--     setoid_replace ((1#4)+(1#4)+(1#4)) with (3#4) in H0 by reflexivity.
--     apply quarter_approx_le_abs_1, H0.
--     apply CRmult_assoc_zfactor_le.
--   - apply (Qle_trans _ (proj1_sig (CR_b (1#1) y + (1#1))%Qpos
--                         * proj1_sig (CR_b (1#1) z + (1#1))%Qpos)).
--     rewrite Qabs_Qmult.
--     apply (Qle_trans _ (proj1_sig (CR_b (1#1) y + (1#1))%Qpos * Qabs k)).
--     apply Qmult_le_compat_r.
--     apply AbsSmall_Qabs in H1.
--     setoid_replace ((1#4)+(1#4)+(1#4)) with (3#4) in H1 by reflexivity.
--     apply quarter_approx_le_abs_1, H1. apply Qabs_nonneg.
--     apply Qmult_le_l. apply Qpos_ispos.
--     apply AbsSmall_Qabs in H0.
--     setoid_replace ((1#4)+(1#4)+(1#4)) with (3#4) in H0 by reflexivity.
--     apply quarter_approx_le_abs_1, H0.
--     rewrite <- Qmult_1_l, Qmult_assoc.
--     apply Qmult_le_compat_r. 2: apply Qpos_nonneg.
--     apply Qmult_le_compat_r. 2: apply Qpos_nonneg.
--     simpl. rewrite <- Qplus_assoc.
--     apply (Qle_trans _ (0+2)). discriminate.
--     apply Qplus_le_l, Qabs_nonneg.
--   - apply (Qle_trans _ (proj1_sig (CR_b (1#1) x + (1#1))%Qpos
--                         * proj1_sig (CR_b (1#1) y + (1#1))%Qpos)).
--     rewrite Qabs_Qmult.
--     apply (Qle_trans _ (proj1_sig (CR_b (1#1) x + (1#1))%Qpos * Qabs j)).
--     apply Qmult_le_compat_r.
--     simpl in H.
--     apply AbsSmall_Qabs in H.
--     setoid_replace ((1#4)+(1#4)+(1#4)) with (3#4) in H by reflexivity.
--     apply quarter_approx_le_abs_1, H. apply Qabs_nonneg.
--     apply Qmult_le_l. apply Qpos_ispos.
--     apply AbsSmall_Qabs in H1.
--     setoid_replace ((1#4)+(1#4)+(1#4)) with (3#4) in H1 by reflexivity.
--     apply quarter_approx_le_abs_1, H1.
--     exact xyfactor_le.
--   - rewrite (@CRmult_bounded_mult b).
--     2: exact ylower. 2: exact yupper.
--     apply (@CRle_trans _ ('(-proj1_sig ((CR_b (1#1) x) * CR_b (1#1) y)%Qpos)%Q)).
--     2: apply CR_b_lowerBound_2.
--     apply CRle_Qle, Qopp_le_compat.
--     apply (Qle_trans _ (proj1_sig (CR_b (1#1) x + (1#1))%Qpos
--                         * proj1_sig ((CR_b (1#1) y) + (1#1))%Qpos)).
--     apply (Qpos_mult_le_compat (CR_b (1#1) x) (CR_b (1#1) y)).
--     rewrite <- Qplus_0_r at 1. apply Qplus_le_r. discriminate.
--     rewrite <- Qplus_0_r at 1. apply Qplus_le_r. discriminate.
--     exact xyfactor_le.
--   - rewrite (@CRmult_bounded_mult b).
--     2: exact ylower. 2: exact yupper.
--     apply (@CRle_trans _ ('(proj1_sig ((CR_b (1#1) x) * CR_b (1#1) y)%Qpos)%Q)).
--     apply CR_b_upperBound_2.
--     apply CRle_Qle.
--     apply (Qle_trans _ (proj1_sig (CR_b (1#1) x + (1#1))%Qpos
--                         * proj1_sig ((CR_b (1#1) y) + (1#1))%Qpos)).
--     apply (Qpos_mult_le_compat (CR_b (1#1) x) (CR_b (1#1) y)).
--     rewrite <- Qplus_0_r at 1. apply Qplus_le_r. discriminate.
--     rewrite <- Qplus_0_r at 1. apply Qplus_le_r. discriminate.
--     exact xyfactor_le.
-- Qed.
