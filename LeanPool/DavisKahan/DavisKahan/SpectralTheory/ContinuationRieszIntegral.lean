/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ContinuationContour
import Mathlib.Analysis.Normed.Operator.NormedSpace
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Riesz integrals on proof-carrying continuation contours

This module proves that a continuous complex one-form is curve integrable along
`PiecewiseC1ClosedContour`.  Mathlib already supplies the corresponding result
for a globally `C1` path; the proof below applies that analytic argument on each
piece and joins the finitely many interval-integrability statements.

The general result is then specialized to the operator-valued resolvent
one-form.  A `SpectralSeparatingContour` supplies exactly the common positive
spectral distance needed for continuity of the resolvent on the contour image.
The normalized Bochner curve integral defines the Riesz operator selected by
the contour.

**Promoted 2026-07-30 under lane `EXP-PROMOTE-MISC`**, in the same cascade: it became
promotable only after the modules it imported were promoted earlier in this lane.  Nothing is
restated; names and namespace are unchanged.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open Set
open MeasureTheory
open scoped InnerProductSpace Interval unitInterval

universe u v

namespace PiecewiseC1ClosedContour

/-- The partition point function extended from finite indices to natural
indices.  Only indices at most `pieceCount` are used in the integration proof;
the value outside that range makes the function total. -/
def breakPointNat (Γ : PiecewiseC1ClosedContour) (k : ℕ) : ℝ :=
  if hk : k ≤ Γ.pieceCount then
    Γ.breakPoint ⟨k, Nat.lt_succ_iff.mpr hk⟩
  else
    1

/-- The natural-indexed partition starts at zero. -/
@[simp] theorem breakPointNat_zero (Γ : PiecewiseC1ClosedContour) :
    Γ.breakPointNat 0 = 0 := by
  rw [breakPointNat, dite_eq_left (Nat.zero_le Γ.pieceCount)]
  simpa using Γ.breakPoint_zero

/-- The natural-indexed partition ends at one. -/
@[simp] theorem breakPointNat_pieceCount (Γ : PiecewiseC1ClosedContour) :
    Γ.breakPointNat Γ.pieceCount = 1 := by
  rw [breakPointNat, dite_eq_left le_rfl]
  have hindex :
      (⟨Γ.pieceCount, Nat.lt_succ_iff.mpr le_rfl⟩ :
        Fin (Γ.pieceCount + 1)) = Fin.last Γ.pieceCount := by
    apply Fin.ext
    rfl
  rw [hindex, Γ.breakPoint_last]

/-- Every partition point belongs to the unit interval. -/
theorem breakPoint_mem_unitInterval (Γ : PiecewiseC1ClosedContour)
    (i : Fin (Γ.pieceCount + 1)) : Γ.breakPoint i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [← Γ.breakPoint_zero]
    exact Γ.breakPoint_strictMono.monotone (Fin.zero_le i)
  · rw [← Γ.breakPoint_last]
    exact Γ.breakPoint_strictMono.monotone (Fin.le_last i)

/-- Consecutive partition points are strictly ordered. -/
theorem breakPoint_castSucc_lt_succ (Γ : PiecewiseC1ClosedContour)
    (i : Fin Γ.pieceCount) :
    Γ.breakPoint i.castSucc < Γ.breakPoint i.succ :=
  Γ.breakPoint_strictMono Fin.castSucc_lt_succ

section PiecewiseCurveIntegrability

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The curve-integral integrand using the derivative local to one partition
piece.  On the interior of the piece it agrees with Mathlib's
`curveIntegralFun`, whose derivative is taken within the whole unit interval. -/
noncomputable def localCurveIntegralFun
    (Γ : PiecewiseC1ClosedContour) (ω : ℂ → ℂ →L[ℂ] F)
    (i : Fin Γ.pieceCount) (t : ℝ) : F :=
  ω (Γ.param t)
    (derivWithin Γ.param
      (Set.Icc (Γ.breakPoint i.castSucc) (Γ.breakPoint i.succ)) t)

/-- A continuous one-form gives an interval-integrable local curve integrand
on each differentiable piece. -/
theorem intervalIntegrable_localCurveIntegralFun

    (Γ : PiecewiseC1ClosedContour) (ω : ℂ → ℂ →L[ℂ] F)
    (hω : ContinuousOn ω Γ.image) (i : Fin Γ.pieceCount) :
    IntervalIntegrable (Γ.localCurveIntegralFun ω i) volume
      (Γ.breakPoint i.castSucc) (Γ.breakPoint i.succ) := by
  let a : ℝ := Γ.breakPoint i.castSucc
  let b : ℝ := Γ.breakPoint i.succ
  have hab : a < b := by
    simpa only [a, b] using Γ.breakPoint_castSucc_lt_succ i
  have haI : a ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [a] using Γ.breakPoint_mem_unitInterval i.castSucc
  have hbI : b ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [b] using Γ.breakPoint_mem_unitInterval i.succ
  have hparam : ContinuousOn Γ.param (Set.Icc a b) :=
    Γ.path.continuous_extend.continuousOn
  have hparam_image : MapsTo Γ.param (Set.Icc a b) Γ.image := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨haI.1.trans ht.1, ht.2.trans hbI.2⟩
    refine ⟨(⟨t, htI⟩ : unitInterval), ?_⟩
    simpa only [image, param] using (Γ.path.extend_apply htI).symm
  have hωparam : ContinuousOn (fun t ↦ ω (Γ.param t)) (Set.Icc a b) :=
    hω.comp hparam hparam_image
  have hderiv : ContinuousOn
      (derivWithin Γ.param (Set.Icc a b)) (Set.Icc a b) := by
    have hpiece := Γ.contDiffOn_piece i
    simpa only [a, b, param] using
      hpiece.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  change IntervalIntegrable
    (fun t ↦ ω (Γ.param t)
      (derivWithin Γ.param (Set.Icc a b) t)) volume a b
  apply ContinuousOn.intervalIntegrable_of_Icc hab.le
  exact ContinuousOn.clm_apply hωparam hderiv

/-- On the open interior of a partition piece, the local derivative and the
derivative within the full unit interval agree. -/
theorem localCurveIntegralFun_eq_curveIntegralFun_on_uIoo
    (Γ : PiecewiseC1ClosedContour) (ω : ℂ → ℂ →L[ℂ] F)
    (i : Fin Γ.pieceCount) :
    Set.EqOn (Γ.localCurveIntegralFun ω i)
      (curveIntegralFun ω Γ.path)
      (Set.uIoo (Γ.breakPoint i.castSucc) (Γ.breakPoint i.succ)) := by
  intro t ht
  have hab : Γ.breakPoint i.castSucc < Γ.breakPoint i.succ :=
    Γ.breakPoint_castSucc_lt_succ i
  rw [Set.uIoo_of_le hab.le] at ht
  have haI := Γ.breakPoint_mem_unitInterval i.castSucc
  have hbI := Γ.breakPoint_mem_unitInterval i.succ
  have htI : t ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_lt haI.1 ht.1, lt_of_lt_of_le ht.2 hbI.2⟩
  simp only [localCurveIntegralFun, curveIntegralFun_def, param]
  rw [derivWithin_of_mem_nhds (by simpa using ht)]
  rw [derivWithin_of_mem_nhds (by simpa using htI)]

/-- A continuous complex one-form is curve integrable along every finitely
piecewise-`C1` closed contour. -/
theorem curveIntegrable_of_continuousOn

    (Γ : PiecewiseC1ClosedContour) (ω : ℂ → ℂ →L[ℂ] F)
    (hω : ContinuousOn ω Γ.image) : CurveIntegrable ω Γ.path := by
  change IntervalIntegrable (curveIntegralFun ω Γ.path) volume 0 1
  have hpiece : ∀ k < Γ.pieceCount,
      IntervalIntegrable (curveIntegralFun ω Γ.path) volume
        (Γ.breakPointNat k) (Γ.breakPointNat (k + 1)) := by
    intro k hk
    let i : Fin Γ.pieceCount := ⟨k, hk⟩
    have hlocal := Γ.intervalIntegrable_localCurveIntegralFun ω hω i
    have hcurve := hlocal.congr_uIoo
      (Γ.localCurveIntegralFun_eq_curveIntegralFun_on_uIoo ω i)
    have hk0 : k ≤ Γ.pieceCount := Nat.le_of_lt hk
    have hk1 : k + 1 ≤ Γ.pieceCount := Nat.succ_le_iff.mpr hk
    have hleft : Γ.breakPointNat k = Γ.breakPoint i.castSucc := by
      rw [breakPointNat, dite_eq_left hk0]
      apply congrArg Γ.breakPoint
      apply Fin.ext
      rfl
    have hright : Γ.breakPointNat (k + 1) = Γ.breakPoint i.succ := by
      rw [breakPointNat, dite_eq_left hk1]
      apply congrArg Γ.breakPoint
      apply Fin.ext
      rfl
    rw [hleft, hright]
    exact hcurve
  have htotal := IntervalIntegrable.trans_iterate
    (a := Γ.breakPointNat) hpiece
  simpa using htotal

end PiecewiseCurveIntegrability

end PiecewiseC1ClosedContour

section ResolventRieszIntegral

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The operator-valued resolvent one-form `v ↦ v R_A(z)`. -/
noncomputable def resolventOneForm (A : H →L[ℂ] H) (z : ℂ) :
    ℂ →L[ℂ] (H →L[ℂ] H) :=
  (1 : ℂ →L[ℂ] ℂ).smulRight (resolventOperator A z)

/-- Evaluation of the resolvent one-form. -/
@[simp] theorem resolventOneForm_apply (A : H →L[ℂ] H) (z v : ℂ) :
    resolventOneForm A z v = v • resolventOperator A z := by
  simp [resolventOneForm, ContinuousLinearMap.smulRight_apply]

/-- Normalization compatible with `resolventOperator A z = (A - z • 1)⁻¹`.
The standard Riesz formula uses `(z • 1 - A)⁻¹`, hence the leading minus. -/
noncomputable def rieszNormalization : ℂ :=
  -(((2 : ℂ) * Real.pi * Complex.I)⁻¹)

/-- The sign correction does not change the normalization norm. -/
@[simp] theorem norm_rieszNormalization :
    ‖rieszNormalization‖ = ‖(((2 : ℂ) * Real.pi * Complex.I)⁻¹)‖ := by
  simp only [rieszNormalization, norm_neg]

namespace SpectralSeparatingContour

variable [CompleteSpace H]

/-- The resolvent one-form is continuous on the separated contour image. -/
theorem continuousOn_resolventOneForm
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    ContinuousOn (resolventOneForm A) Γ.image := by
  have hsep : ∀ z ∈ Γ.image, ∀ lam ∈ realSpectrum A,
      Γ.spectralMargin ≤ ‖z - (lam : ℂ)‖ := by
    rintro z ⟨t, rfl⟩ lam hlam
    exact Γ.spectrum_separated t lam hlam
  have hres : ContinuousOn (resolventOperator A) Γ.image :=
    complex_continuousOn_resolventOperator_of_distance
      A Γ.selfAdjoint Γ.image Γ.spectralMargin Γ.spectralMargin_pos hsep
  let L : (H →L[ℂ] H) →L[ℂ] (ℂ →L[ℂ] (H →L[ℂ] H)) :=
    ContinuousLinearMap.smulRightL ℂ ℂ (H →L[ℂ] H)
      (1 : ℂ →L[ℂ] ℂ)
  have hcomp : ContinuousOn (fun z ↦ L (resolventOperator A z)) Γ.image :=
    L.continuous.continuousOn.comp hres (fun _ _ ↦ Set.mem_univ _)
  refine hcomp.congr ?_
  intro z hz
  change L (resolventOperator A z) = resolventOneForm A z
  rfl

/-- The operator-valued resolvent one-form is Bochner curve integrable around
a proof-carrying separating contour. -/
theorem curveIntegrable_resolventOneForm
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    CurveIntegrable (resolventOneForm A) Γ.path :=
  Γ.geometric.curveIntegrable_of_continuousOn
    (resolventOneForm A) Γ.continuousOn_resolventOneForm

/-- The unnormalized operator-valued resolvent integral around the contour. -/
noncomputable def resolventCurveIntegral
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) : H →L[ℂ] H :=
  ∫ᶜ z in Γ.path, resolventOneForm A z

/-- The normalized Riesz operator selected by the contour. -/
noncomputable def contourRieszProjection
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) : H →L[ℂ] H :=
  rieszNormalization • Γ.resolventCurveIntegral

/-- The Riesz operator is the normalized Bochner curve integral of the
resolvent one-form. -/
theorem contourRieszProjection_eq
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    Γ.contourRieszProjection =
      rieszNormalization •
        ∫ᶜ z in Γ.path, resolventOneForm A z :=
  rfl

end SpectralSeparatingContour

end ResolventRieszIntegral

end DavisKahanExt
end TauCeti
