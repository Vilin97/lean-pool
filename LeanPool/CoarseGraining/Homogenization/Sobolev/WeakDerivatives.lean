/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Weak Derivatives -/

@[expose] public section

namespace Homogenization

def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

@[simp] theorem basisVec_apply {d : ℕ} (i j : Fin d) :
    basisVec i j = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp [basisVec]
  · simp [basisVec, h]

/-- The coordinate dot product against a basis vector reads off the matching coordinate. -/
theorem vecDot_basisVec_left {d : ℕ} (i : Fin d) (x : Vec d) :
    vecDot (basisVec i) x = x i := by
  unfold vecDot basisVec
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    simp at hi

/-- The coordinate dot product against a basis vector reads off the matching coordinate. -/
theorem vecDot_basisVec_right {d : ℕ} (x : Vec d) (i : Fin d) :
    vecDot x (basisVec i) = x i := by
  unfold vecDot basisVec
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    simp at hi

/-- A coordinate basis vector has squared coordinate norm one. -/
theorem vecNormSq_basisVec {d : ℕ} (i : Fin d) :
    vecNormSq (basisVec i) = 1 := by
  rw [vecNormSq, vecDot_basisVec_left]
  simp [basisVec]

def HasWeakPartialDerivOn {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * φ x ∂MeasureTheory.volume

def HasWeakGradientOn {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)

namespace HasWeakPartialDerivOn

/-- Weak partial derivatives are unique a.e. on open sets. -/
theorem ae_eq {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {i : Fin d} {u gi hi : Vec d → ℝ}
    (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
    (hhiLoc : MeasureTheory.LocallyIntegrableOn hi U MeasureTheory.volume)
    (hgi : HasWeakPartialDerivOn U i u gi)
    (hhi : HasWeakPartialDerivOn U i u hi) :
    gi =ᵐ[MeasureTheory.volume.restrict U] hi := by
  have hdiff_zero :
      ∀ᵐ x ∂MeasureTheory.volume, x ∈ U → gi x - hi x = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (f := fun x => gi x - hi x) (hgiLoc.sub hhiLoc) ?_
    intro φ hφ_smooth hφ_compact hφ_sub
    have hφ_cont : Continuous φ := hφ_smooth.continuous
    have hgi_K :
        MeasureTheory.IntegrableOn gi (tsupport φ) MeasureTheory.volume :=
      hgiLoc.integrableOn_compact_subset hφ_sub hφ_compact.isCompact
    have hhi_K :
        MeasureTheory.IntegrableOn hi (tsupport φ) MeasureTheory.volume :=
      hhiLoc.integrableOn_compact_subset hφ_sub hφ_compact.isCompact
    have hgiφ_K :
        MeasureTheory.IntegrableOn (fun x => gi x * φ x) (tsupport φ)
          MeasureTheory.volume := by
      simpa [smul_eq_mul] using
        hgi_K.smul_continuousOn hφ_cont.continuousOn hφ_compact.isCompact
    have hhiφ_K :
        MeasureTheory.IntegrableOn (fun x => hi x * φ x) (tsupport φ)
          MeasureTheory.volume := by
      simpa [smul_eq_mul] using
        hhi_K.smul_continuousOn hφ_cont.continuousOn hφ_compact.isCompact
    have hgiφ_zero :
        ∀ x ∈ U \ tsupport φ, gi x * φ x = 0 := by
      intro x hx
      simp [image_eq_zero_of_notMem_tsupport hx.2]
    have hhiφ_zero :
        ∀ x ∈ U \ tsupport φ, hi x * φ x = 0 := by
      intro x hx
      simp [image_eq_zero_of_notMem_tsupport hx.2]
    have hgi_int :
        MeasureTheory.Integrable (fun x => gi x * φ x)
          (MeasureTheory.volume.restrict U) := by
      simpa [MeasureTheory.IntegrableOn] using
        hgiφ_K.of_forall_sdiff_eq_zero hU.measurableSet hgiφ_zero
    have hhi_int :
        MeasureTheory.Integrable (fun x => hi x * φ x)
          (MeasureTheory.volume.restrict U) := by
      simpa [MeasureTheory.IntegrableOn] using
        hhiφ_K.of_forall_sdiff_eq_zero hU.measurableSet hhiφ_zero
    have hset_eq :
        ∫ x in U, gi x * φ x ∂MeasureTheory.volume =
          ∫ x in U, hi x * φ x ∂MeasureTheory.volume := by
      have hgi' := hgi φ hφ_smooth hφ_compact hφ_sub
      have hhi' := hhi φ hφ_smooth hφ_compact hφ_sub
      apply neg_injective
      rw [← hgi', ← hhi']
    have hset_zero :
        ∫ x in U, φ x * (gi x - hi x) ∂MeasureTheory.volume = 0 := by
      calc
        ∫ x in U, φ x * (gi x - hi x) ∂MeasureTheory.volume
            = ∫ x in U, (gi x * φ x - hi x * φ x) ∂MeasureTheory.volume := by
                apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
                intro x hx
                ring
        _ = ∫ x in U, gi x * φ x ∂MeasureTheory.volume -
              ∫ x in U, hi x * φ x ∂MeasureTheory.volume := by
                rw [MeasureTheory.integral_sub hgi_int hhi_int]
        _ = 0 := by rw [hset_eq, sub_self]
    have hzero_out :
        ∀ x, x ∉ U → φ x * (gi x - hi x) = 0 := by
      intro x hx
      have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
      simp [image_eq_zero_of_notMem_tsupport hx_notin]
    calc
      ∫ x, φ x • (gi x - hi x) ∂MeasureTheory.volume
          = ∫ x, φ x * (gi x - hi x) ∂MeasureTheory.volume := by
              simp [smul_eq_mul]
      _ = ∫ x in U, φ x * (gi x - hi x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero_out]
      _ = 0 := hset_zero
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hU.measurableSet]
  filter_upwards [hdiff_zero] with x hx hxu
  exact sub_eq_zero.mp (hx hxu)

end HasWeakPartialDerivOn

end Homogenization
