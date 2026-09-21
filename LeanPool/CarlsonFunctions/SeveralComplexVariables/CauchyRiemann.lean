/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Conformal
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Derivatives

/-!
# Coordinate Cauchy–Riemann equations

Real differentiability and the coordinate Cauchy–Riemann equations characterize holomorphy
on an open finite-dimensional domain. The proof uses Mathlib's one-variable conversion
theorem and Osgood, rather than constructing a second complex derivative theory.

The domain `ι → ℂ` is intentional: each Wirtinger derivative and each displayed
Cauchy–Riemann equation singles out a coordinate. The codomain may be a complex normed
space, with completeness assumed for the analyticity results. Coordinate-free holomorphy
is expressed by the usual complex Fréchet derivative; these results describe it in
coordinates and relate the real derivative to the existing `partialDeriv` interface.
-/

@[expose] public noncomputable section

open Complex Filter Function Set
open scoped Classical Topology

namespace SeveralComplexVariables

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The holomorphic Wirtinger derivative, defined from the real Fréchet derivative. -/
def wirtingerDeriv (i : ι) (f : (ι → ℂ) → F) (z : ι → ℂ) : F :=
  (1 / 2 : ℂ) • (fderiv ℝ f z (Pi.single i 1) - I • fderiv ℝ f z (Pi.single i I))

/-- The antiholomorphic Wirtinger derivative, defined from the real Fréchet derivative. -/
def conjWirtingerDeriv (i : ι) (f : (ι → ℂ) → F) (z : ι → ℂ) : F :=
  (1 / 2 : ℂ) • (fderiv ℝ f z (Pi.single i 1) + I • fderiv ℝ f z (Pi.single i I))

/-- The real derivative of a coordinate slice is the restriction of the real derivative
to that coordinate's complex plane. -/
theorem hasFDerivAt_update_real {f : (ι → ℂ) → F} (z : ι → ℂ) (i : ι) (w : ℂ)
    (hf : DifferentiableAt ℝ f (update z i w)) :
    HasFDerivAt (fun v => f (update z i v))
      ((fderiv ℝ f (update z i w)).comp
        ((ContinuousLinearMap.single ℂ (fun _ : ι => ℂ) i).restrictScalars ℝ)) w := by
  have hs : HasFDerivAt (update z i)
      ((ContinuousLinearMap.single ℂ (fun _ : ι => ℂ) i).restrictScalars ℝ) w := by
    convert! (hasDerivAt_update z i w).hasFDerivAt.restrictScalars ℝ using 1
    ext v j
    simp [Pi.single_apply, smul_eq_mul]
  exact hf.hasFDerivAt.comp w hs

variable [CompleteSpace F]

/-- On an open set, holomorphy is equivalent to real differentiability together with the
coordinate Cauchy–Riemann equations. Continuous real differentiability is not needed. -/
theorem analyticOnNhd_iff_differentiableAt_real_cauchyRiemann
    {U : Set (ι → ℂ)} (hU : IsOpen U) {f : (ι → ℂ) → F} :
    AnalyticOnNhd ℂ f U ↔
      (∀ z ∈ U, DifferentiableAt ℝ f z) ∧
        ∀ z ∈ U, ∀ i, fderiv ℝ f z (Pi.single i I) = I • fderiv ℝ f z (Pi.single i 1) := by
  constructor
  · intro hf
    refine ⟨fun z hz => (hf z hz).differentiableAt.restrictScalars ℝ, ?_⟩
    intro z hz i
    rw [(hf z hz).differentiableAt.fderiv_restrictScalars ℝ]
    change fderiv ℂ f z (Pi.single i I) = I • fderiv ℂ f z (Pi.single i 1)
    rw [show Pi.single i I = I • (Pi.single i (1 : ℂ)) by
      ext j; by_cases hji : j = i <;> simp [hji]]
    exact map_smul _ _ _
  · rintro ⟨hreal, hCR⟩
    apply analyticOnNhd_pi_of_analyticOnNhd_update hU
      (fun z hz => (hreal z hz).continuousAt.continuousWithinAt)
    intro z hz i
    rw [analyticAt_iff_eventually_differentiableAt]
    have hmem : ∀ᶠ w in 𝓝 (z i), update z i w ∈ U := by
      exact ((hasDerivAt_update z i (z i)).continuousAt.preimage_mem_nhds
        (by simpa using hU.mem_nhds hz))
    filter_upwards [hmem] with w hw
    have H := hasFDerivAt_update_real z i w (hreal _ hw)
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨H.differentiableAt, ?_⟩
    rw [H.fderiv]
    simpa using hCR (update z i w) hw i

/-- The antiholomorphic Wirtinger derivative vanishes for a holomorphic function. -/
theorem _root_.AnalyticOnNhd.conjWirtingerDeriv_eq_zero {U : Set (ι → ℂ)}
    {f : (ι → ℂ) → F} (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U)
    {z : ι → ℂ} (hz : z ∈ U) (i : ι) : conjWirtingerDeriv i f z = 0 := by
  have hCR := (analyticOnNhd_iff_differentiableAt_real_cauchyRiemann hU).mp hf |>.2 z hz i
  simp [conjWirtingerDeriv, hCR, smul_smul]

/-- For holomorphic functions the holomorphic Wirtinger derivative agrees with the
complex coordinate derivative `partialDeriv`. -/
theorem _root_.AnalyticOnNhd.wirtingerDeriv_eq_partialDeriv {U : Set (ι → ℂ)}
    {f : (ι → ℂ) → F} (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U)
    {z : ι → ℂ} (hz : z ∈ U) (i : ι) : wirtingerDeriv i f z = partialDeriv i f z := by
  have hCR := (analyticOnNhd_iff_differentiableAt_real_cauchyRiemann hU).mp hf |>.2 z hz i
  rw [wirtingerDeriv, hCR, smul_smul, I_mul_I, neg_one_smul, sub_neg_eq_add,
    ← two_smul ℂ, smul_smul]
  norm_num
  rw [partialDeriv_eq_fderiv (hf z hz).differentiableAt,
    (hf z hz).differentiableAt.fderiv_restrictScalars ℝ]
  rfl

end SeveralComplexVariables

end
