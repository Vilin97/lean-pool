/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.ChannelCapacity.ChainRule
import LeanPool.ChannelCapacity.NonDegeneracy
import Mathlib.Order.Filter.Extr

/-!
# ChannelCapacity.StrictConcavity

Strict concavity infrastructure on the simplex of probability measures.

Mathlib does not currently equip `ProbabilityMeasure α` with an affine or vector-space structure, so
strict concavity is phrased directly in terms of the explicit operation
`ProbabilityMeasure.convexCombination`.
-/

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

namespace ProbabilityMeasure

variable {α : Type*} [MeasurableSpace α]

/-- Two global maximizers coincide if the function is strictly concave along convex combinations of
probability measures. -/
lemma eq_of_isMaxOn_univ_of_strictConcave
    {f : ProbabilityMeasure α → ℝ}
    (hStrict : ∀ (p q : ProbabilityMeasure α) (_h_ne : p ≠ q) (t : NNReal)
      (_ht_pos : 0 < t) (ht_lt_one : t < 1),
        f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) >
          (t : ℝ) * f p + (1 - (t : ℝ)) * f q)
    {p q : ProbabilityMeasure α}
    (hp : IsMaxOn f Set.univ p) (hq : IsMaxOn f Set.univ q) : p = q := by
  by_contra hne
  have hp' : ∀ r, f r ≤ f p := isMaxOn_univ_iff.mp hp
  have hq' : ∀ r, f r ≤ f q := isMaxOn_univ_iff.mp hq
  let t : NNReal := 1 / 2
  have ht_pos : 0 < t := by norm_num [t]
  have ht_lt_one : t < 1 := by norm_num [t]
  have hMixLe :
      f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) ≤ f p :=
    hp' _
  have hpq : f p = f q := le_antisymm (hq' _) (hp' _)
  have hMixGt :
      f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) >
        (t : ℝ) * f p + (1 - (t : ℝ)) * f q := by
    simpa [t] using hStrict p q hne t ht_pos ht_lt_one
  have hMixGt' :
      f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) > f p := by
    have hRewrite :
        (t : ℝ) * f p + (1 - (t : ℝ)) * f q = f p := by
      calc
        (t : ℝ) * f p + (1 - (t : ℝ)) * f q =
            (t : ℝ) * f p + (1 - (t : ℝ)) * f p := by simp [hpq]
        _ = ((t : ℝ) + (1 - (t : ℝ))) * f p := by ring
        _ = f p := by ring
    simpa [hRewrite] using hMixGt
  exact (not_lt_of_ge hMixLe) hMixGt'

lemma convexCombination_comm (p q : ProbabilityMeasure α) (t : NNReal) (ht : t ≤ 1) :
    ProbabilityMeasure.convexCombination p q t ht =
      ProbabilityMeasure.convexCombination q p (1 - t) (tsub_le_self) := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  rw [ProbabilityMeasure.convexCombination_apply _ _ _ _ hs,
    ProbabilityMeasure.convexCombination_apply _ _ _ _ hs]
  have htsub : ((((1 : NNReal) - ((1 : NNReal) - t) : NNReal) : NNReal) : ENNReal) =
      (t : ENNReal) := by
    exact_mod_cast tsub_tsub_cancel_of_le ht
  rw [htsub, add_comm]

lemma eq_left_of_convexCombination_eq {p q : ProbabilityMeasure α} {t : NNReal}
    (ht_lt_one : t < 1)
    (h : ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one) = p) :
    q = p := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  have hs_eq : (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)).toMeasure s =
      p.toMeasure s := by
    simpa using congrArg (fun μ : ProbabilityMeasure α => μ.toMeasure s) h
  rw [ProbabilityMeasure.convexCombination_apply _ _ _ _ hs] at hs_eq
  have hp_fin : p.toMeasure s ≠ ∞ := measure_ne_top _ _
  have hq_fin : q.toMeasure s ≠ ∞ := measure_ne_top _ _
  have hleft_fin : ((t : ENNReal) * p.toMeasure s) ≠ ∞ := by
    exact ENNReal.mul_ne_top (by simp) hp_fin
  have hright_fin : ((((1 : NNReal) - t : NNReal) : ENNReal) * q.toMeasure s) ≠ ∞ := by
    exact ENNReal.mul_ne_top (by simp) hq_fin
  have hs_real := congrArg ENNReal.toReal hs_eq
  rw [ENNReal.toReal_add hleft_fin hright_fin, ENNReal.toReal_mul, ENNReal.toReal_mul] at hs_real
  have hcoeff : (1 - (t : ENNReal)).toReal = 1 - (t : ℝ) := by
    rw [ENNReal.toReal_sub_of_le]
    · simp
    · exact_mod_cast (le_of_lt ht_lt_one)
    · simp
  have hs_real' :
      (1 - (t : ℝ)) * (q.toMeasure s).toReal = (1 - (t : ℝ)) * (p.toMeasure s).toReal := by
    have hs_real_simp :
        (t : ℝ) * (p.toMeasure s).toReal + (1 - (t : ENNReal)).toReal * (q.toMeasure s).toReal =
          (p.toMeasure s).toReal := by
      simpa using hs_real
    rw [hcoeff] at hs_real_simp
    linarith
  have ht_ne : 1 - (t : ℝ) ≠ 0 := by
    linarith [show (t : ℝ) < 1 by exact_mod_cast ht_lt_one]
  have hs_toReal : (q.toMeasure s).toReal = (p.toMeasure s).toReal := by
    exact mul_left_cancel₀ ht_ne hs_real'
  exact (ENNReal.toReal_eq_toReal_iff' hq_fin hp_fin).mp hs_toReal

lemma eq_right_of_convexCombination_eq {p q : ProbabilityMeasure α} {t : NNReal}
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (h : ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one) = q) :
    p = q := by
  have htsub_lt_one : (1 : NNReal) - t < 1 := by
    simpa using tsub_lt_self (show 0 < (1 : NNReal) by simp) ht_pos
  have hswap :
      ProbabilityMeasure.convexCombination q p (1 - t) (tsub_le_self) = q := by
    calc
      ProbabilityMeasure.convexCombination q p (1 - t) (tsub_le_self) =
          ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one) := by
            simpa using (ProbabilityMeasure.convexCombination_comm p q t (le_of_lt ht_lt_one)).symm
      _ = q := h
  exact eq_left_of_convexCombination_eq (p := q) (q := p) htsub_lt_one hswap

lemma convexCombination_ne_left {p q : ProbabilityMeasure α} (h_ne : p ≠ q) {t : NNReal}
    (ht_lt_one : t < 1) :
    ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one) ≠ p := by
  intro h
  exact h_ne ((eq_left_of_convexCombination_eq ht_lt_one h).symm)

lemma convexCombination_ne_right {p q : ProbabilityMeasure α} (h_ne : p ≠ q) {t : NNReal}
    (ht_pos : 0 < t) (ht_lt_one : t < 1) :
    ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one) ≠ q := by
  intro h
  exact h_ne (eq_right_of_convexCombination_eq ht_pos ht_lt_one h)

end ProbabilityMeasure

namespace ChannelCapacity

open ProbabilityMeasure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace Kernel

private lemma mutualInformation_strictlyConcave_aux
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (k : Kernel α β) [IsMarkovKernel k]
    (h : Kernel.InjectivePriorPushforward k)
    (hWC : Kernel.WellConditionedForCapacity k)
    (p q : ProbabilityMeasure α) (h_ne : p ≠ q) (t : NNReal)
    (ht_pos : 0 < t) (ht_lt_one : t < 1) :
    mutualInformation (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) k >
      (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k := by
  let r := ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)
  let ν := (outputPrior k r).toMeasure
  let Kp :=
    InformationTheory.klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν)
  let Kq :=
    InformationTheory.klDiv (jointLaw k q).toMeasure (q.toMeasure ⊗ₘ Kernel.const α ν)
  let Kr :=
    InformationTheory.klDiv (jointLaw k r).toMeasure (r.toMeasure ⊗ₘ Kernel.const α ν)
  let Dp := InformationTheory.klDiv (outputPrior k p).toMeasure ν
  let Dq := InformationTheory.klDiv (outputPrior k q).toMeasure ν
  have ht_ne_zero : (t : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt ht_pos)
  have hs_pos : 0 < (1 : NNReal) - t := by
    exact tsub_pos_iff_lt.mpr ht_lt_one
  have hs_ne_zero : ((((1 : NNReal) - t : NNReal) : ENNReal)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hs_pos)
  have hp_ac_r : p.toMeasure ≪ r.toMeasure := by
    refine (Measure.absolutelyContinuous_smul ht_ne_zero).trans ?_
    dsimp [r]
    simpa using
      (Measure.absolutelyContinuous_of_le
        (μ := t • p.toMeasure)
        (ν := t • p.toMeasure + ((1 : NNReal) - t) • q.toMeasure)
        (le_add_of_nonneg_right bot_le))
  have hq_ac_r : q.toMeasure ≪ r.toMeasure := by
    refine (Measure.absolutelyContinuous_smul hs_ne_zero).trans ?_
    dsimp [r]
    simpa using
      (Measure.absolutelyContinuous_of_le
        (μ := ((1 : NNReal) - t) • q.toMeasure)
        (ν := t • p.toMeasure + ((1 : NNReal) - t) • q.toMeasure)
        (le_add_of_nonneg_left bot_le))
  have hr_rows : ∀ᵐ x ∂r.toMeasure, k x ≪ ν := by
    simpa [ν] using hWC.hRowAC r
  have hp_rows : ∀ᵐ x ∂p.toMeasure, k x ≪ ν := by
    rw [ae_iff]
    exact hp_ac_r (by simpa [ae_iff] using hr_rows)
  have hq_rows : ∀ᵐ x ∂q.toMeasure, k x ≪ ν := by
    rw [ae_iff]
    exact hq_ac_r (by simpa [ae_iff] using hr_rows)
  have hKp_eq :
      Kp = ∫⁻ x, InformationTheory.klDiv (k x) ν ∂p.toMeasure := by
    apply klDiv_compProd_right
    exact Measure.AbsolutelyContinuous.compProd_right hp_rows
  have hKq_eq :
      Kq = ∫⁻ x, InformationTheory.klDiv (k x) ν ∂q.toMeasure := by
    apply klDiv_compProd_right
    exact Measure.AbsolutelyContinuous.compProd_right hq_rows
  have hKr_eq :
      Kr = ∫⁻ x, InformationTheory.klDiv (k x) ν ∂r.toMeasure := by
    apply klDiv_compProd_right
    exact Measure.AbsolutelyContinuous.compProd_right hr_rows
  have hν_ref_p : Kernel.OutputMarginalReference k p ν := by
    exact ⟨r, hp_ac_r, rfl⟩
  have hν_ref_q : Kernel.OutputMarginalReference k q ν := by
    exact ⟨r, hq_ac_r, rfl⟩
  have hν_ref_r : Kernel.OutputMarginalReference k r ν := by
    exact Kernel.outputMarginalReference_self k r
  have hKp_fin : Kp ≠ ∞ := hWC.hFiniteRefKL p ν hν_ref_p
  have hKq_fin : Kq ≠ ∞ := hWC.hFiniteRefKL q ν hν_ref_q
  have hKr_fin : Kr ≠ ∞ := hWC.hFiniteRefKL r ν hν_ref_r
  have hMIp_fin :
      InformationTheory.klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure ≠ ∞ := by
    simpa [independentJointLaw_toMeasure] using
      hWC.hFiniteRefKL p (outputPrior k p).toMeasure
        (Kernel.outputMarginalReference_self k p)
  have hMIq_fin :
      InformationTheory.klDiv (jointLaw k q).toMeasure (independentJointLaw k q).toMeasure ≠ ∞ := by
    simpa [independentJointLaw_toMeasure] using
      hWC.hFiniteRefKL q (outputPrior k q).toMeasure
        (Kernel.outputMarginalReference_self k q)
  have hMIr_fin :
      InformationTheory.klDiv (jointLaw k r).toMeasure (independentJointLaw k r).toMeasure ≠ ∞ := by
    simpa [independentJointLaw_toMeasure] using
      hWC.hFiniteRefKL r (outputPrior k r).toMeasure
        (Kernel.outputMarginalReference_self k r)
  have hChain_p :
      Kp =
        InformationTheory.klDiv
            (jointLaw k p).toMeasure
            (independentJointLaw k p).toMeasure +
          Dp := by
    simpa [Kp, Dp] using hWC.hChainRule p ν hν_ref_p
  have hChain_q :
      Kq =
        InformationTheory.klDiv
            (jointLaw k q).toMeasure
            (independentJointLaw k q).toMeasure +
          Dq := by
    simpa [Kq, Dq] using hWC.hChainRule q ν hν_ref_q
  have hChain_r :
      Kr =
        InformationTheory.klDiv (jointLaw k r).toMeasure (independentJointLaw k r).toMeasure +
          InformationTheory.klDiv (outputPrior k r).toMeasure ν := by
    simpa [Kr] using hWC.hChainRule r ν hν_ref_r
  have hDp_fin : Dp ≠ ∞ := by
    intro hDp_top
    have : Kp = ∞ := by
      rw [hChain_p, hDp_top, add_top]
    exact hKp_fin this
  have hDq_fin : Dq ≠ ∞ := by
    intro hDq_top
    have : Kq = ∞ := by
      rw [hChain_q, hDq_top, add_top]
    exact hKq_fin this
  have hKr_real :
      Kr.toReal = (t : ℝ) * Kp.toReal + (1 - (t : ℝ)) * Kq.toReal := by
    have hr_toMeasure :
        r.toMeasure = t • p.toMeasure + ((1 : NNReal) - t) • q.toMeasure := by
      simp [r, ProbabilityMeasure.convexCombination_toMeasure]
    have hleft_fin :
        t • ∫⁻ x, InformationTheory.klDiv (k x) ν ∂p.toMeasure ≠ ∞ := by
      rw [← hKp_eq]
      simpa [ENNReal.smul_def, smul_eq_mul] using ENNReal.mul_ne_top (by simp) hKp_fin
    have hright_fin :
        ((1 : NNReal) - t) • ∫⁻ x, InformationTheory.klDiv (k x) ν ∂q.toMeasure ≠ ∞ := by
      rw [← hKq_eq]
      have hcoeff : ((((1 : NNReal) - t : NNReal) : ENNReal)) ≠ ∞ := by simp
      simpa [ENNReal.smul_def, smul_eq_mul] using ENNReal.mul_ne_top hcoeff hKq_fin
    rw [hKr_eq, hKp_eq, hKq_eq]
    rw [hr_toMeasure]
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      ENNReal.toReal_add hleft_fin hright_fin, ENNReal.toReal_smul, ENNReal.toReal_smul]
    simp [NNReal.smul_def, NNReal.coe_sub (le_of_lt ht_lt_one), sub_eq_add_neg]
  have hKp_real :
      Kp.toReal = mutualInformation p k + Dp.toReal := by
    rw [hChain_p, ENNReal.toReal_add hMIp_fin hDp_fin, mutualInformation]
  have hKq_real :
      Kq.toReal = mutualInformation q k + Dq.toReal := by
    rw [hChain_q, ENNReal.toReal_add hMIq_fin hDq_fin, mutualInformation]
  have hKr_real' : Kr.toReal = mutualInformation r k := by
    have hOutSelf : InformationTheory.klDiv (outputPrior k r).toMeasure ν = 0 := by simp [ν]
    calc
      Kr.toReal =
          (InformationTheory.klDiv (jointLaw k r).toMeasure (independentJointLaw k r).toMeasure +
            0).toReal := by rw [hChain_r, hOutSelf]
      _ =
          (InformationTheory.klDiv
              (jointLaw k r).toMeasure
              (independentJointLaw k r).toMeasure).toReal +
            0 := by simp
      _ = mutualInformation r k := by simp [mutualInformation]
  have hr_ne_p : r ≠ p := ProbabilityMeasure.convexCombination_ne_left h_ne ht_lt_one
  have hr_ne_q : r ≠ q := ProbabilityMeasure.convexCombination_ne_right h_ne ht_pos ht_lt_one
  have hOutp_ne : outputPrior k p ≠ outputPrior k r := by
    intro h_eq
    exact hr_ne_p ((h <| by simpa [Kernel.priorPushforward] using h_eq).symm)
  have hOutq_ne : outputPrior k q ≠ outputPrior k r := by
    intro h_eq
    exact hr_ne_q ((h <| by simpa [Kernel.priorPushforward] using h_eq).symm)
  have hDp_ne_zero : Dp ≠ 0 := by
    intro hDp_zero
    exact hOutp_ne <| ProbabilityMeasure.toMeasure_injective
      ((InformationTheory.klDiv_eq_zero_iff).mp hDp_zero)
  have hDq_ne_zero : Dq ≠ 0 := by
    intro hDq_zero
    exact hOutq_ne <| ProbabilityMeasure.toMeasure_injective
      ((InformationTheory.klDiv_eq_zero_iff).mp hDq_zero)
  have hDp_pos : 0 < Dp.toReal := ENNReal.toReal_pos hDp_ne_zero hDp_fin
  have hDq_pos : 0 < Dq.toReal := ENNReal.toReal_pos hDq_ne_zero hDq_fin
  have hExtra_pos :
      0 < (t : ℝ) * Dp.toReal + (1 - (t : ℝ)) * Dq.toReal := by
    have ht_real : 0 < (t : ℝ) := by exact_mod_cast ht_pos
    have hs_real : 0 < 1 - (t : ℝ) := by
      linarith [show (t : ℝ) < 1 by exact_mod_cast ht_lt_one]
    nlinarith [hDp_pos, hDq_pos, ht_real, hs_real]
  calc
    mutualInformation r k = Kr.toReal := hKr_real'.symm
    _ = (t : ℝ) * Kp.toReal + (1 - (t : ℝ)) * Kq.toReal := hKr_real
    _ = (t : ℝ) * (mutualInformation p k + Dp.toReal) +
          (1 - (t : ℝ)) * (mutualInformation q k + Dq.toReal) := by
          rw [hKp_real, hKq_real]
    _ = (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k +
          ((t : ℝ) * Dp.toReal + (1 - (t : ℝ)) * Dq.toReal) := by ring
    _ > (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k := by
      linarith

theorem mutualInformation_strictlyConcave_of_injectivePriorPushforward
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (k : Kernel α β) [IsMarkovKernel k]
    (h : Kernel.InjectivePriorPushforward k)
    (hWC : Kernel.WellConditionedForCapacity k) :
    ∀ (p q : ProbabilityMeasure α) (_h_ne : p ≠ q) (t : NNReal)
      (_ht_pos : 0 < t) (ht_lt_one : t < 1),
      mutualInformation (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) k >
        (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k := by
  intro p q h_ne t ht_pos ht_lt_one
  simpa using mutualInformation_strictlyConcave_aux k h hWC p q h_ne t ht_pos ht_lt_one

end Kernel

end ChannelCapacity
