/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Generic
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.ZeroConcentrated.DP

/-!
# Postprocessing

This file proves zCDP for ``privPostProcess``.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

variable {T : Type}
variable [t1 : MeasurableSpace T]
variable [t2 : MeasurableSingletonClass T]

variable {U V : Type}
variable [m2 : MeasurableSpace U]
variable [count : Countable U]
variable [disc : DiscreteMeasurableSpace U]
variable [Inhabited U]

/--
privPostProcess preserves absolute continuity between neighbours
-/
def privPostProcess_AC {f : U -> V} (nq : Mechanism T U) (Hac : ACNeighbour nq) : ACNeighbour (privPostProcess nq f) := by
  rw [ACNeighbour] at *
  unfold AbsCts at *
  intro l₁ l₂ Hn v
  have Hac := Hac l₁ l₂ Hn
  simp [privPostProcess]
  intro Hppz i fi
  apply Hac
  apply Hppz
  apply fi

/--
Normalized fiber
-/
def δ (nq : SLang U) (f : U → V) (a : V)  : {n : U | a = f n} → ENNReal :=
  fun x : {n : U | a = f n} => nq x * (∑' (x : {n | a = f n}), nq x)⁻¹

lemma δ_normalizes (nq : SLang U) (f : U → V) (a : V) (h1 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ 0) (h2 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ ⊤) :
  HasSum (δ nq f a) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold δ
  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.mul_inv_cancel h1 h2]

/--
Normalized fiber distribution
-/
def δpmf (nq : SLang U) (f : U → V) (a : V) (h1 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ 0) (h2 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ ⊤) : PMF {n : U | a = f n} :=
  ⟨ δ nq f a , δ_normalizes nq f a h1 h2 ⟩

theorem δpmf_conv (nq : SLang U) (a : V) (x : {n | a = f n}) (h1 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ 0) (h2 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ ⊤) :
  nq x * (∑' (x : {n | a = f n}), nq x)⁻¹ = (δpmf nq f a h1 h2) x := by
  simp [δpmf]
  conv =>
    right
    left
    left
  rfl

theorem δpmf_conv' (nq : SLang U) (f : U → V) (a : V) (h1 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ 0) (h2 : ∑' (i : ↑{n | a = f n}), nq ↑i ≠ ⊤) :
  (fun x : {n | a = f n} => nq x * (∑' (x : {n | a = f n}), nq x)⁻¹) = (δpmf nq f a h1 h2) := by
  ext x
  rw [δpmf_conv]

theorem witness {f : U → V} {i : V} (h : ¬{b | i = f b} = ∅) :
  ∃ x : U, i = f x := by
  rw [← nonempty_subtype]
  exact Set.nonempty_iff_ne_empty'.mpr h

theorem norm_simplify (x : ENNReal) (h : x ≠ ⊤) :
  @nnnorm ℝ SeminormedAddGroup.toNNNorm x.toReal = x := by
  simp [nnnorm]
  cases x
  · contradiction
  · rename_i v
    simp
    rfl


theorem convergent_subset {p : T → ENNReal} (f : T → V) (conv : ∑' (x : T), p x ≠ ⊤) :
  ∑' (x : { y : T| x = f y }), p x ≠ ⊤ := by
  rw [← condition_to_subset]
  have A : (∑' (y : T), if x = f y  then p y else 0) ≤ ∑' (x : T), p x := by
    apply tsum_le_tsum
    · intro i
      split
      · trivial
      · simp only [_root_.zero_le]
    · exact ENNReal.summable
    · exact ENNReal.summable
  rw [← lt_top_iff_ne_top]
  apply lt_of_le_of_lt A
  rw [lt_top_iff_ne_top]
  trivial

theorem ENNReal.tsum_pos {f : T → ENNReal} (h1 : ∑' x : T, f x ≠ ⊤) (h2 : ∀ x : T, f x ≠ 0) (i : T) :
  0 < ∑' x : T, f x := by
  apply (toNNReal_lt_toNNReal ENNReal.zero_ne_top h1).mp
  simp only [zero_toNNReal]
  rw [ENNReal.tsum_toNNReal_eq (ENNReal.ne_top_of_tsum_ne_top h1)]
  have S : Summable fun a => (f a).toNNReal := by
    rw [← tsum_coe_ne_top_iff_summable]
    conv =>
      left
      right
      intro b
      rw [ENNReal.coe_toNNReal (ENNReal.ne_top_of_tsum_ne_top h1 b)]
    trivial
  have B:= @NNReal.tsum_pos T (fun (a : T) => (f a).toNNReal) S i
  apply B
  apply ENNReal.toNNReal_pos (h2 i) (ENNReal.ne_top_of_tsum_ne_top h1 i)

theorem ENNReal.tsum_pos_int {f : ℤ → ENNReal} (h1 : ∑' x : ℤ, f x ≠ ⊤) (h2 : ∀ x : ℤ, f x ≠ 0) :
  0 < ∑' x : ℤ, f x := by
  apply ENNReal.tsum_pos h1 h2 42

theorem tsum_pos_int {f : ℤ → ENNReal} (h1 : ∑' x : ℤ, f x ≠ ⊤) (h2 : ∀ x : ℤ, f x ≠ 0) :
  0 < (∑' x : ℤ, f x).toReal := by
  have X : 0 = (0 : ENNReal).toReal := rfl
  rw [X]
  clear X
  apply toReal_strict_mono h1
  apply ENNReal.tsum_pos_int h1 h2


lemma rpow_nonzero (x : ENNReal) (y : ℝ) (H : ¬(x = 0 ∧ 0 < y ∨ x = ⊤ ∧ y < 0)) : x ^ y ≠ 0 := by
  intro Hk
  apply H
  apply (ENNReal.rpow_eq_zero_iff).mp
  apply Hk


/--
Jensen's inequality for privPostProcess, restructed to types where ``nq l₁`` is nonzero
-/
theorem privPostPocess_DP_pre_reduct {U : Type} [m2 : MeasurableSpace U] [count : Countable U] [disc : DiscreteMeasurableSpace U] [Inhabited U]
  {nq : List T → SLang U}
  (f : U → V) {α : ℝ} (h1 : 1 < α) {l₁ l₂ : List T}
  (HNorm1 : HasSum (nq l₁) 1)
  (HNorm2 : HasSum (nq l₂) 1)
  (Habs : AbsCts (nq l₁) (nq l₂))
  (Hnq2 : ∀ (u : U), nq l₁ u ≠ 0)
  (h2 : Neighbour l₁ l₂) :
  (∑' (x : V), (∑' (a : U), if x = f a then nq l₁ a else 0) ^ α * (∑' (a : U), if x = f a then nq l₂ a else 0) ^ (1 - α)) ≤ (∑' (x : U), nq l₁ x ^ α * nq l₂ x ^ (1 - α)) := by

  -- By absolute continuity, nq1 is nonzero
  have Hnql1 : (∀ (u : U), nq l₂ u ≠ 0) := by
    rw [AbsCts] at Habs
    intro u HK
    apply Hnq2
    apply Habs
    apply HK

  -- Noised query is not ⊤
  have nq_nts1 : ∑' n : U, nq l₁ n ≠ ⊤ := by simp [HasSum.tsum_eq HNorm1]
  have nq_nts2 : ∑' n : U, nq l₂ n ≠ ⊤ := by simp [HasSum.tsum_eq HNorm2]

  -- Rewrite as cascading expectations
  rw [RenyiDivergenceExpectation]
  case h => apply h1
  case H =>
    simp [AbsCts]
    intro v Hv i vEq
    apply Habs
    apply Hv
    apply vEq
  simp
  rw [RenyiDivergenceExpectation (fun x => nq l₁ x) (fun x => nq l₂ x) h1 Habs]

  -- Shuffle the sum
  rw [fiberwisation (fun x => (nq l₁ x / nq l₂ x) ^ α * nq l₂ x) f]
  apply ENNReal.tsum_le_tsum
  intro i
  simp

  -- Eliminate elements with probability zero
  split
  case h.isTrue =>
    rename_i H
    repeat rw [condition_to_subset]
    rw [H]
    simp

  -- Normalize each fiber into a PMF
  rename_i NotEmpty
  repeat rw [condition_to_subset]

  have nq_restriction_nts1 : ∑' (a : ↑{a | i = f a}), nq l₁ ↑a ≠ ⊤ := by exact convergent_subset (fun y => f y) nq_nts1
  have nq_restriction_nts2 : ∑' (a : ↑{a | i = f a}), nq l₂ ↑a ≠ ⊤ := by exact convergent_subset (fun y => f y) nq_nts2

  have nq_restriction_nzs (l' : List T) (Hl : ∀ u : U, nq l' u ≠ 0) : ∑' (a : ↑{a | i = f a}), nq l' ↑a ≠ 0 := by
    simp
    have T := witness NotEmpty
    cases T
    rename_i z w
    exists z
    constructor
    · trivial
    · exact Hl z
  simp

  let δF₁ := (δpmf (nq l₁) f i (nq_restriction_nzs l₁ Hnq2) nq_restriction_nts1)
  let δF₂ := (δpmf (nq l₂) f i (nq_restriction_nzs l₂ Hnql1) nq_restriction_nts2)
  have δF₁_Eq : δF₁ = (δpmf (nq l₁) f i (nq_restriction_nzs l₁ Hnq2) nq_restriction_nts1) := by exact rfl
  have δF₂_Eq : δF₂ = (δpmf (nq l₂) f i (nq_restriction_nzs l₂ Hnql1) nq_restriction_nts2) := by exact rfl

  -- Normalized fibers are absolutely continuous
  have HAC_Fiber : AbsCts δF₁ δF₂ := by
    simp [AbsCts]
    rw [δF₁_Eq]
    rw [δF₂_Eq]
    intro a b
    repeat rw [δpmf]
    unfold δ
    simp
    rw [DFunLike.coe]
    simp [PMF.instFunLike]
    intro H
    cases H
    · rename_i Hl2z
      left
      apply Habs
      apply Hl2z
    · exfalso
      apply nq_restriction_nts2
      simp
      assumption

  have δF₂_NT (x : { x // i = f x }) : δF₂ x ≠ ⊤ := by
    rw [δF₂_Eq]
    exact PMF.apply_ne_top ((nq l₂).δpmf f i (nq_restriction_nzs l₂ Hnql1) (nq_restriction_nts2)) x

  -- Normalized fibers avoid the bad case for rewriting the Jensen term
  have Hspecial (x : { x // i = f x }) : ¬(δF₁ x ≠ 0 ∧ δF₂ x = ⊤) := by
    simp
    intro _ Hcont
    exfalso
    apply δF₂_NT
    apply Hcont

  -- Apply Jensen's inequality to the normalized fibers
  have HJ := Renyi_Jensen_ENNReal δF₁ δF₂ h1 HAC_Fiber

  -- Cancel and simplify the LHS of HJ to 1
  conv at HJ =>
    lhs
    arg 1
    arg 1
    intro x
    rw [division_def]
    rw [mul_mul_inv_eq_mul_cancel (HAC_Fiber x) (Hspecial x)]
  conv at HJ =>
    lhs
    arg 1
    rw [PMF.tsum_coe]
  simp at HJ

  -- Name the normalization constants for each fiber
  let N (l : List T) := (∑' (x : {n // i = f n}), nq l x)⁻¹
  have N_def (l : List T) : N l =  (∑' (x : {n // i = f n}), nq l x)⁻¹ := by exact rfl
  have N_inv (l : List T) : (∑' (x : {n // i = f n}), nq l x) = (N l)⁻¹ := by
    exact Eq.symm (inv_inv (∑' (x : { n // i = f n }), (nq l) ↑x))
  have N1_nz : N l₁ ≠ 0 := ENNReal.inv_ne_zero.mpr (nq_restriction_nts1)
  have N2_nz : N l₂ ≠ 0 := ENNReal.inv_ne_zero.mpr (nq_restriction_nts2)

  -- Unfold normalization constants in HJ
  conv at HJ =>
    rhs
    arg 1
    intro x
    repeat rw [DFunLike.coe]
    repeat rw [PMF.instFunLike]
    simp
    rw [δF₁_Eq]
    rw [δF₂_Eq]
    simp [δpmf]
    unfold δ
    repeat rw [DFunLike.coe]
    repeat rw [PMF.instFunLike]
    simp
    rw [<- N_def]
    rw [<- N_def]

  -- Fold constants in goal
  rw [N_inv]
  rw [N_inv]

  -- Pull out constants from the sum in HJ
  have conv1  (x : { x // i = f x }) : (nq l₁ x.val * N l₁ / (nq l₂ x.val * N l₂)) ^ α = (N l₁ / N l₂) ^ α * (nq l₁ x.val / nq l₂ x.val) ^ α := by
    simp [division_def]
    rw [ENNReal.mul_rpow_of_ne_top ?G1 ?G2]
    case G1 =>
      apply mul_ne_top
      · exact ENNReal.ne_top_of_tsum_ne_top (nq_nts1) ↑x
      · exact inv_ne_top.mpr (nq_restriction_nzs l₁ Hnq2)
    case G2 =>
      apply inv_ne_top.mpr
      exact mul_ne_zero (Hnql1 ↑x) N2_nz
    rw [ENNReal.mul_rpow_of_ne_top ?G1 ?G2]
    case G1 =>
      exact ENNReal.ne_top_of_tsum_ne_top (nq_nts1) ↑x
    case G2 =>
      exact inv_ne_top.mpr (nq_restriction_nzs l₁ Hnq2)
    rw [ENNReal.mul_rpow_of_ne_top ?G1 ?G2]
    case G1 =>
      exact inv_ne_top.mpr (nq_restriction_nzs l₁ Hnq2)
    case G2 =>
      exact inv_ne_top.mpr N2_nz
    rw [ENNReal.mul_rpow_of_ne_top ?G1 ?G2]
    case G1 =>
      exact ENNReal.ne_top_of_tsum_ne_top (nq_nts1) ↑x
    case G2 =>
      exact inv_ne_top.mpr (Hnql1 ↑x)
    conv =>
      arg 1
      rw [mul_assoc]
      rw [mul_comm]
      skip
    repeat rw [mul_assoc]
    congr 1
    conv =>
      arg 2
      arg 2
      rw [mul_comm]
    rw [<- mul_assoc]
    congr 1
    rw [ENNReal.mul_inv ?G1 ?G2]
    case G1 =>
      right
      exact inv_ne_top.mpr (nq_restriction_nzs l₂ Hnql1)
    case G2 =>
      right
      exact N2_nz
    rw [ENNReal.mul_rpow_of_ne_top ?G1 ?G2]
    case G1 => exact inv_ne_top.mpr (Hnql1 ↑x)
    case G2 => exact inv_ne_top.mpr N2_nz
    rw [mul_comm]
  conv at HJ =>
    rhs
    arg 1
    intro x
    rw [conv1 x]
    rw [mul_assoc]
    arg 2
    rw [mul_comm]
    rw [mul_assoc]
    rw [mul_comm]
    rw [mul_assoc]
  clear conv1
  rw [ENNReal.tsum_mul_left] at HJ
  rw [ENNReal.tsum_mul_left] at HJ
  rw [<- mul_assoc] at HJ

  -- Move constants to the left-hand side of HJ
  -- Super haunted bug: When I apply this as normal to HJ (with placeholders)
  -- Lean it lights up all of my "have" and "let" statements because it \"doesn't
  -- know how to synthesize\" a placeholder. The placeholder it points me to is in
  -- Pure/Postprocessing, where the same lemma is also applied with placeholders.
  have W :=
    @ENNReal.div_le_iff_le_mul
      1
      ((N l₁ / N l₂) ^ α * N l₂)
      (∑' (i_1 : { x // i = f x }), (nq l₁ i_1.val / nq l₂ i_1.val) ^ α * nq l₂ i_1.val)
      ?G1
      ?G2
  case G1 =>
    left
    apply mul_ne_zero_iff.mpr
    apply And.intro
    · apply (rpow_nonzero (N l₁ / N l₂) α)
      intro Hk
      rcases Hk with ⟨ H1 , _ ⟩ | ⟨ _ , H2 ⟩
      · have Hk' : 0 < N l₁ / N l₂ := by
          apply ENNReal.div_pos_iff.mpr
          apply And.intro
          · exact N1_nz
          · exact inv_ne_top.mpr (nq_restriction_nzs l₂ Hnql1)
        rw [H1] at Hk'
        simp at Hk'
      · linarith
    · apply N2_nz
  case G2 =>
    left
    apply mul_ne_top
    · apply rpow_ne_top_of_nonneg
      · linarith
      · intro Hk
        have Hk' : (N l₁ / N l₂ < ⊤) := by
          apply ENNReal.div_lt_top
          · exact inv_ne_top.mpr (nq_restriction_nzs l₁ Hnq2)
          · exact N2_nz
        rw [Hk] at Hk'
        simp at Hk'
    · exact inv_ne_top.mpr (nq_restriction_nzs l₂ Hnql1)
  rw [mul_comm] at HJ
  apply W.mpr at HJ
  clear W

  -- Apply transitivity
  apply (le_trans ?G3 HJ)
  clear HJ

  -- These terms are equal
  apply Eq.le
  repeat rw [division_def]
  simp
  rw [ENNReal.mul_inv ?G1 ?G2]
  case G1 =>
    right
    exact inv_ne_top.mpr (nq_restriction_nzs l₂ Hnql1)
  case G2 =>
    right
    exact N2_nz
  congr
  rw [<- ENNReal.inv_rpow]
  congr
  rw [ENNReal.mul_inv ?G1 ?G2]
  case G1 =>
    left
    exact N1_nz
  case G2 =>
    left
    exact inv_ne_top.mpr (nq_restriction_nzs l₁ Hnq2)
  simp


theorem tsum_ne_zero_of_ne_zero {T : Type} [Inhabited T] (f : T → ENNReal) (h : ∀ x : T, f x ≠ 0) :
  ∑' x : T, f x ≠ 0 := by
  by_contra CONTRA
  rw [ENNReal.tsum_eq_zero] at CONTRA
  have A := h default
  have B := CONTRA default
  contradiction

/--
Jensen's inequality for privPostProcess.

Implementation note: This reduction only works because neighbours are symmetric. A different reduction may
be able to relax this requirement.
-/
theorem privPostPocess_DP_pre {nq : List T → PMF U} (HNorm : ∀ l, HasSum (nq l) 1)
  (f : U → V) {α : ℝ} (h1 : 1 < α) {l₁ l₂ : List T} (HN : Neighbour l₁ l₂)
  (Habs : AbsCts (nq l₁) (nq l₂)) (Habs' : AbsCts (nq l₂) (nq l₁)) :
  (∑' (x : V),
      (∑' (a : U), if x = f a then nq l₁ a else 0) ^ α *
        (∑' (a : U), if x = f a then nq l₂ a else 0) ^ (1 - α)) ≤
  (∑' (x : U), nq l₁ x ^ α * nq l₂ x ^ (1 - α)) := by
  -- Restruct the sum to a type where nq l₁ is nonzero
  have HSup1 (x : V) : Function.support (fun (a : U) => if x = f a then nq l₁ a else 0) ⊆ { u : U | nq l₁ u ≠ 0 } := by simp [Function.support]
  have HSup2 (x : V) : Function.support (fun (a : U) => if x = f a then nq l₂ a else 0) ⊆ { u : U | nq l₁ u ≠ 0 } := by
    simp [Function.support]
    exact fun a _ a_2 a_3 => a_2 (Habs' a a_3)
  have HSup3 : Function.support (fun (a : U) => nq l₁ a ^ α * nq l₂ a ^ (1 - α)) ⊆ { u : U | nq l₁ u ≠ 0 } := by
    simp only [Function.support, Set.setOf_subset_setOf]
    intro a Hnz
    apply mul_ne_zero_iff.mp at Hnz
    rcases Hnz with ⟨ H1 , _ ⟩
    intro Hk
    apply H1
    apply (ENNReal.rpow_eq_zero_iff).mpr
    left
    apply And.intro
    · apply Hk
    · linarith
  rw [<- tsum_subtype_eq_of_support_subset HSup3]
  conv =>
    lhs
    arg 1
    intro v
    rw [<- tsum_subtype_eq_of_support_subset (HSup1 v)]
    rw [<- tsum_subtype_eq_of_support_subset (HSup2 v)]
  clear HSup1
  clear HSup2
  clear HSup3
  simp

  cases (Classical.em (∃ x : U, ¬ nq l₁ x = 0))
  · rename_i x_witness
    have HR := @privPostPocess_DP_pre_reduct T V {x // ¬ nq l₁ x = 0}
                 _ _ _ ?TC
                 (fun t u => nq t u) (fun x => f x) α h1
                 l₁ l₂ ?GNorm1 ?GNorm2 ?Gac ?Gnz HN
    case TC =>
      apply inhabited_of_nonempty
      exact Set.Nonempty.to_subtype x_witness
    case GNorm1 =>
      simp
      rw [<- HasSum.tsum_eq (HNorm l₁)]
      have HSup4 : Function.support (fun u => nq l₁ u) ⊆ { u | nq l₁ u ≠ 0 } := by simp [Function.support]
      rw [<- tsum_subtype_eq_of_support_subset HSup4]
      simp
      apply Summable.hasSum
      exact ENNReal.summable
    case GNorm2 =>
      simp
      rw [<- HasSum.tsum_eq (HNorm l₂)]
      have HSup4 : Function.support (fun u => nq l₂ u) ⊆ { u | nq l₁ u ≠ 0 } := by
        simp [Function.support]
        intro a Hk1 Hk2
        apply Hk1
        apply Habs'
        apply Hk2
      rw [<- tsum_subtype_eq_of_support_subset HSup4]
      simp
      apply Summable.hasSum
      exact ENNReal.summable
    case Gac =>
      rw [AbsCts]
      simp
      intro a _ H2
      exact Habs a (Habs' a (Habs a H2))
    case Gnz => simp
    simp at HR
    apply HR
  · rename_i x_empty
    simp at *
    have Hempty : IsEmpty {x // ¬nq l₁ x = 0} := by
      exact Subtype.isEmpty_of_false fun a a_1 => a_1 (x_empty a)
    rw [@tsum_empty _ _ _ _ _ Hempty]
    conv =>
      lhs
      arg 1
      intro
      rw [@tsum_empty _ _ _ _ _ Hempty]
      rw [@tsum_empty _ _ _ _ _ Hempty]
    simp
    intro
    left
    linarith

/--
privPostProcess satisfies the zCDP bound
-/
theorem privPostProcess_zCDPBound {nq : Mechanism T U} {ε : ℝ}
  (h : zCDPBound nq ε) (f : U → V) (Hac : ACNeighbour nq) :
  zCDPBound (privPostProcess nq f) ε := by
  simp [privPostProcess, zCDPBound, RenyiDivergence]
  intro α h1 l₁ l₂ h2
  have h' := h
  simp [zCDPBound, RenyiDivergence] at h'
  replace h' := h' α h1 l₁ l₂ h2
  apply le_trans _ h'
  clear h'
  unfold RenyiDivergence_def
  rw [DFunLike.coe]
  rw [PMF.instFunLike]
  simp
  conv =>
    enter [1, 1, 2, 1, 1, x]
    repeat rw [SLang.toPMF]
    simp
  conv =>
    enter [2, 1, 2, 1, 1, x]
    repeat rw [SLang.toPMF]
    repeat rw [DFunLike.coe]
    repeat rw [PMF.instFunLike]
    simp
  apply ofEReal_le_mono
  apply mul_le_mul_of_nonneg_left ?G1 ?G2
  case G2 =>
    apply EReal.coe_nonneg.mpr
    apply inv_nonneg_of_nonneg
    linarith
  apply elog_mono_le.mp
  simp [PMF.bind, PMF.pure]
  simp [PMF.instFunLike]
  apply privPostPocess_DP_pre
  · exact fun l => PMF.hasSum_coe_one (nq l)
  · exact h1
  · exact h2
  · exact Hac l₁ l₂ h2
  · apply Hac l₂ l₁
    exact Neighbour_symm l₁ l₂ h2


/--
Postprocessing preserves zCDP
-/
theorem privPostProcess_zCDP {f : U → V}
  (nq : Mechanism T U) (ε : NNReal) (h : zCDP nq ε) :
  zCDP (privPostProcess nq f) ε := by
  rcases h with ⟨ Hac1, Hb1 ⟩
  simp [zCDP] at *
  apply And.intro
  · exact privPostProcess_AC nq Hac1
  · exact privPostProcess_zCDPBound Hb1 f Hac1

end SLang
