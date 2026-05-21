/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Generic
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.ZeroConcentrated.DP

/-!
# zCDP Adaptive Composition

This file builds up to a zCDP bound on adaptively composed zCDP queries.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

variable { T U V : Type }
variable [HU : Inhabited U] [HU_meas : MeasurableSpace U] [HU_discr : MeasurableSingletonClass U] [HU_count : Countable U]
variable [HV : Inhabited V] [HV_meas : MeasurableSpace V] [HV_discr : MeasurableSingletonClass V] [HV_count : Countable V]


lemma sup_lemma {s : EReal} (HS0 : 0 < s) (HS1 : s < ⊤) (f : U -> EReal) :
    eexp (s * ⨆ (u : U), f u) =  ⨆ (u : U), eexp (s * f u) := by
  rw [@GaloisConnection.l_iSup _ _ _ _ _ _ _ (galois_connection_smul_l HS0 HS1) f]
  apply GaloisConnection.l_iSup galois_connection_eexp

/--
Bound on Renyi divergence on adaptively composed queries
-/
lemma privComposeAdaptive_renyi_bound {nq1 : List T → PMF U} {nq2 : U -> List T → PMF V}
    {α : ℝ} (Hα : 1 < α) {l₁ l₂ : List T} (HN : Neighbour l₁ l₂)
    (HAC1 : ACNeighbour nq1) (HAC2 : ∀ u, ACNeighbour (nq2 u)) :
    RenyiDivergence (privComposeAdaptive nq1 nq2 l₁) (privComposeAdaptive nq1 nq2 l₂) α ≤
    RenyiDivergence (nq1 l₁) (nq1 l₂) α + (⨆ (u : U), RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) := by
  -- Open the definition of Renyi divergence
  unfold RenyiDivergence
  rw [<- (GaloisConnection.l_iSup galois_connection_ofReal)]
  rw [<- ofEReal_plus_nonneg ?G1 ?G2]
  case G1 => exact RenyiDivergence_def_nonneg (nq1 l₁) (nq1 l₂) (HAC1 l₁ l₂ HN) Hα
  case G2 =>
    apply le_iSup_iff.mpr
    intro b Hb
    -- Can use the fact that U is nonempty and RD is nonnegative
    rcases HU with ⟨ u' ⟩
    have Hb := Hb u'
    apply le_trans ?G3 ?G4
    case G4 => apply Hb
    exact RenyiDivergence_def_nonneg (nq2 u' l₁) (nq2 u' l₂) (HAC2 u' l₁ l₂ HN) Hα
  apply ofEReal_le_mono


  -- Rewrite to series inequality
  have Hα' : ((1 : ℝ).toEReal < α.toEReal ) := by exact EReal.coe_lt_coe_iff.mpr Hα
  simp at Hα'
  have Hanz : 0 < α.toEReal - 1 := by
    have X : (0 : EReal) = (Real.toEReal 1) - (Real.toEReal 1) := by
      rw [SubNegMonoid.sub_eq_add_neg]
      rw [<- EReal.coe_neg]
      rw [<- EReal.coe_add]
      simp
    rw [X]
    apply EReal.sub_lt_sub_of_lt_of_le
    · apply Hα'
    · simp
    · exact ne_of_beq_false rfl
    · exact ne_of_beq_false rfl
  have Hant : α.toEReal - 1 < ⊤ := by
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl

  apply ereal_smul_le_left (α.toEReal - 1) Hanz Hant
  rw [ereal_smul_distr_le_left _ Hanz Hant]
  apply eexp_mono_le.mpr
  rw [<- eexp_add]
  rw [RenyiDivergence_def_exp _ _ Hα]
  rw [RenyiDivergence_def_exp _ _ Hα]

  rw [sup_lemma Hanz Hant]
  conv =>
    enter [2, 2, 1, u]
    rw [RenyiDivergence_def_exp _ _ Hα]

  -- Split series
  rw [ENNReal.tsum_prod']

  -- Apply chain rule, and simplify powers
  conv =>
    enter [1, 1, a, 1, b]
    rw [privComposeChainRule]
    rw [privComposeChainRule]
    rw [ENNReal.mul_rpow_of_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
    rw [ENNReal.mul_rpow_of_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]

  -- Bring sup into the sum
  rw [<- ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro a

  -- Commute and cancel the non-adaptive nq l₁ terms
  conv =>
    enter [1, 1, b]
    rw [mul_assoc]
    right
    rw [mul_comm]
    rw [mul_assoc]
    skip
  conv =>
    enter [1, 1, b]
    rw [<- mul_assoc]
    skip
  rw [ENNReal.tsum_mul_left]
  apply mul_le_mul_left'

  -- Apply upper bound lemma
  conv =>
    enter [1, 1, b]
    rw [mul_comm]
  exact le_iSup_iff.mpr fun b a_1 => a_1 a


/--
Adaptively Composed queries satisfy zCDP Renyi divergence bound.
-/
theorem privComposeAdaptive_zCDPBound {nq1 : List T → PMF U} {nq2 : U -> List T → PMF V} {ε₁ ε₂ : ℝ}
  (Hε₁ : 0 ≤ ε₁) (Hε₂ : 0 ≤ ε₂)
  (HAC1 : ACNeighbour nq1) (HAC2 : ∀ u, ACNeighbour (nq2 u))
  (h1 : zCDPBound nq1 ε₁) (h2 : ∀ u, zCDPBound (nq2 u) ε₂) :
  zCDPBound (privComposeAdaptive nq1 nq2) (ε₁ + ε₂) := by
  rw [zCDPBound]
  intro α Hα l₁ l₂ Hneighbours
  -- This step is loose
  apply (@LE.le.trans _ _ _ (ENNReal.ofReal (1/2 * (ε₁)^2 * α + 1/2 * (ε₂)^2 * α : ℝ)) _ _ ?case_sq)
  case case_sq =>
    apply ofReal_le_ofReal
    -- Binomial bound
    rw [add_sq]
    rw [<- right_distrib]
    apply (mul_le_mul_of_nonneg_right _ ?goal1)
    case goal1 => linarith
    rw [<- left_distrib]
    apply (mul_le_mul_of_nonneg_left _ ?goal1)
    case goal1 => linarith
    apply add_le_add_right
    have hrw :  ε₁ ^ 2 = ε₁ ^ 2 + 0 := by linarith
    conv =>
      lhs
      rw [hrw]
    clear hrw
    apply add_le_add_left
    refine mul_nonneg ?bc.bc.ha Hε₂
    refine mul_nonneg ?G Hε₁
    simp
  -- Rewrite the upper bounds in terms of Renyi divergences of nq1/nq2
  rw [zCDPBound] at h1
  -- have marginal_ub := h1 α Hα l₁ l₂ Hneighbours
  have conditional_ub : (⨆ (u : U),  RenyiDivergence (nq2 u l₁) (nq2 u l₂) α ≤ ENNReal.ofReal (1 / 2 * ε₂ ^ 2 * α)) :=
    ciSup_le fun x => h2 x α Hα l₁ l₂ Hneighbours
  apply (@LE.le.trans _ _ _ (RenyiDivergence (nq1 l₁) (nq1 l₂) α + ⨆ (u : U), RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) _ _ ?case_alg)
  case case_alg =>
    rw [ENNReal.ofReal_add ?G1 ?G2]
    case G1 =>
      simp
      apply mul_nonneg
      · apply mul_nonneg
        · simp
        · exact sq_nonneg ε₁
      · linarith
    case G2 =>
      simp
      apply mul_nonneg
      · apply mul_nonneg
        · simp
        · exact sq_nonneg ε₂
      · linarith
    exact _root_.add_le_add (h1 α Hα l₁ l₂ Hneighbours) conditional_ub
  exact privComposeAdaptive_renyi_bound Hα Hneighbours HAC1 HAC2



/--
Adaptive composition preserves absolute continuity
-/
def privComposeAdaptive_AC (nq1 : Mechanism T U) (nq2 : U -> Mechanism T V) (Hac1 : ACNeighbour nq1) (Hac2 : ∀ u, ACNeighbour (nq2 u)) :
    ACNeighbour (privComposeAdaptive nq1 nq2) := by
  rw [ACNeighbour]
  simp [privComposeAdaptive]
  intro l₁ l₂ HN x Hx
  rcases x with ⟨ u, v ⟩
  simp [DFunLike.coe, PMF.bind, PMF.pure] at *
  intro u'
  rcases Hx u' with A | B
  · left
    exact Hac1 l₁ l₂ HN u' A
  · right
    intro v'
    simp_all
    exact Hac2 u' l₁ l₂ HN v B


/--
``privComposeAdaptive`` satisfies zCDP
-/
theorem privComposeAdaptive_zCDP (nq1 : List T → PMF U) {nq2 : U -> List T → PMF V} {ε₁ ε₂ : NNReal}
    (h : zCDP nq1 ε₁) (h' : ∀ u, zCDP (nq2 u) ε₂) :
    zCDP (privComposeAdaptive nq1 nq2) (ε₁ + ε₂) := by
  simp [zCDP] at *
  apply And.intro
  · apply privComposeAdaptive_AC <;> aesop
  · apply privComposeAdaptive_zCDPBound  <;> aesop
end SLang
