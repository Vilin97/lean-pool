/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.WeakHarmonic.Subsolution

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Viscosity harmonic functions are weakly harmonic

A continuous viscosity solution `u` of the Laplace equation `-Δu = 0` on an
open set `C` satisfies `∫ Δχ · u = 0` for every smooth test function `χ` with
compact support in `C`
(`integral_lapTrace_mul_eq_zero_of_viscositySolution_laplace`).

The subsolution half gives `∫ Δχ · u ≥ 0` for `χ ≥ 0`
(`integral_lapTrace_mul_nonneg_of_viscositySubsolution_laplace`). Since the
Laplace operator is odd, `-u` is again a subsolution when `u` is a
supersolution, which gives the reverse inequality. A general test function is
the difference `χ = (χ + M θ) - M θ` of two nonnegative ones, where `θ` is a
smooth cutoff equal to `1` on `supp χ` and `M ≥ sup |χ|`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Metric Set
open scoped Topology ContDiff Manifold

namespace ViscositySolns

variable {n : Nat}

/-! ### Algebra of the trace Laplacian -/

/-- The trace Laplacian is additive on differences of `C²` functions. -/
theorem lapTrace_sub {χ ψ : Point n → ℝ} (hχ : ContDiff ℝ 2 χ) (hψ : ContDiff ℝ 2 ψ)
    (x : Point n) :
    lapTrace (fun y => χ y - ψ y) x = lapTrace χ x - lapTrace ψ x := by
  have hdχ : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hdDχ : Differentiable ℝ (fderiv ℝ χ) :=
    (hχ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdDψ : Differentiable ℝ (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : fderiv ℝ (fun y => χ y - ψ y) = fun y => fderiv ℝ χ y - fderiv ℝ ψ y := by
    funext y
    exact fderiv_sub (hdχ y) (hdψ y)
  have h2 : fderiv ℝ (fun y => fderiv ℝ χ y - fderiv ℝ ψ y) x =
      fderiv ℝ (fderiv ℝ χ) x - fderiv ℝ (fderiv ℝ ψ) x :=
    fderiv_sub (hdDχ x) (hdDψ x)
  rw [lapTrace, h1, h2, lapTrace, lapTrace, ← Finset.sum_sub_distrib]
  rfl

/--
For `u` continuous on `C` and `χ` continuous with compact support in `C`, the
product `Δχ · u` is integrable.
-/
theorem integrable_lapTrace_mul {C : Set (Point n)} {u : Point n → ℝ}
    (hcont : ContinuousOn u C) {χ : Point n → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (hχC : tsupport χ ⊆ C) :
    Integrable (fun x => lapTrace χ x * u x) := by
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero
    (((continuous_lapTrace hχ).continuousOn.mul (hcont.mono hχC)).integrableOn_compact hχc) ?_
  intro x hx
  rw [lapTrace_eq_zero_of_notMem_tsupport hx, zero_mul]

/-! ### Supersolutions and nonnegative test functions -/

/--
If `u` is a continuous viscosity supersolution of `-Δu = 0` on an open set
`C`, then `∫ Δχ · u ≤ 0` for every nonnegative `C²` function `χ` with compact
support in `C`.
-/
theorem integral_lapTrace_mul_nonpos_of_viscositySupersolution_laplace
    {C : Set (Point n)} (hC : IsOpen C) {u : Point n → ℝ}
    (hu : ViscositySupersolution C laplaceOperator u) (hcont : ContinuousOn u C)
    {χ : Point n → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχC : tsupport χ ⊆ C) (hχ0 : 0 ≤ χ) :
    ∫ x, lapTrace χ x * u x ≤ 0 := by
  have hneg : ViscositySubsolution C laplaceOperator (fun y => -u y) := by
    have := viscositySupersolution_neg_iff.mp hu
    rwa [negOperator_laplaceOperator] at this
  have h := integral_lapTrace_mul_nonneg_of_viscositySubsolution_laplace hC hneg hcont.neg
    hχ hχc hχC hχ0
  simp only [mul_neg, integral_neg] at h
  linarith

/--
A continuous viscosity solution of `-Δu = 0` annihilates `Δχ` for every
nonnegative `C²` test function `χ` with compact support in `C`.
-/
theorem integral_lapTrace_mul_eq_zero_of_viscositySolution_laplace_of_nonneg
    {C : Set (Point n)} (hC : IsOpen C) {u : Point n → ℝ}
    (hu : ViscositySolution C laplaceOperator u) (hcont : ContinuousOn u C)
    {χ : Point n → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχC : tsupport χ ⊆ C) (hχ0 : 0 ≤ χ) :
    ∫ x, lapTrace χ x * u x = 0 :=
  le_antisymm
    (integral_lapTrace_mul_nonpos_of_viscositySupersolution_laplace hC hu.2 hcont
      hχ hχc hχC hχ0)
    (integral_lapTrace_mul_nonneg_of_viscositySubsolution_laplace hC hu.1 hcont hχ hχc hχC hχ0)

/-! ### General test functions -/

/--
A smooth cutoff: for a compact set `K₀` inside an open set `C`, there is a
smooth `θ : R^n → [0, 1]` with compact support in `C` and `θ = 1` on `K₀`.
-/
theorem exists_contDiff_cutoff {C K₀ : Set (Point n)} (hC : IsOpen C) (hK₀ : IsCompact K₀)
    (hK₀C : K₀ ⊆ C) :
    ∃ θ : Point n → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ C ∧
      (∀ x, 0 ≤ θ x) ∧ ∀ x ∈ K₀, θ x = 1 := by
  obtain ⟨r, hr, hrC⟩ := hK₀.exists_cthickening_subset_open hC hK₀C
  have hsub : K₀ ⊆ interior (cthickening r K₀) :=
    (self_subset_thickening hr K₀).trans
      (interior_maximal (thickening_subset_cthickening r K₀) isOpen_thickening)
  obtain ⟨f, hf1, hf0, hf01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := ⊤) 𝓘(ℝ, Point n) hK₀.isClosed hsub
  have hsupp : Function.support f ⊆ cthickening r K₀ := fun x hx => by
    by_contra hno
    exact hx (hf0 x hno)
  have htsupp : tsupport f ⊆ cthickening r K₀ := closure_minimal hsupp isClosed_cthickening
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff,
    HasCompactSupport.intro hK₀.cthickening hf0, htsupp.trans hrC, fun x => (hf01 x).1,
    fun x hx => hf1.self_of_nhdsSet x hx⟩

/--
**Viscosity harmonic functions are weakly harmonic.**

If `u` is a continuous viscosity solution of the Laplace equation `-Δu = 0` on
an open set `C`, then `∫ Δχ · u = 0` for every smooth `χ` with compact support
in `C`, where `Δχ = lapTrace χ = ∑ i, D²χ(eᵢ, eᵢ)`.
-/
theorem integral_lapTrace_mul_eq_zero_of_viscositySolution_laplace
    {C : Set (Point n)} (hC : IsOpen C) {u : Point n → ℝ}
    (hu : ViscositySolution C laplaceOperator u) (hcont : ContinuousOn u C)
    {χ : Point n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχC : tsupport χ ⊆ C) :
    ∫ x, lapTrace χ x * u x = 0 := by
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨θ, hθ, hθc, hθC, hθ0, hθ1⟩ := exists_contDiff_cutoff hC hχc hχC
  have hθ2 : ContDiff ℝ 2 θ := hθ.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨M₀, hM₀⟩ := hχc.exists_bound_of_continuousOn hχ.continuous.continuousOn
  set M := max M₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  set χ₁ : Point n → ℝ := fun x => χ x + M * θ x with hχ₁def
  set χ₂ : Point n → ℝ := fun x => M * θ x with hχ₂def
  have hχ₁ : ContDiff ℝ 2 χ₁ := hχ2.add (contDiff_const.mul hθ2)
  have hχ₂ : ContDiff ℝ 2 χ₂ := contDiff_const.mul hθ2
  have hχ₂c : HasCompactSupport χ₂ := hθc.mul_left
  have hχ₁c : HasCompactSupport χ₁ := hχc.add hχ₂c
  have hsupp₂ : tsupport χ₂ ⊆ C := (tsupport_mul_subset_right).trans hθC
  have hsupp₁ : tsupport χ₁ ⊆ C := by
    refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport χ).union (isClosed_tsupport θ))
      |>.trans (union_subset hχC hθC)
    by_contra hno
    have h1 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hno (Or.inl h))
    have h2 : θ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hno (Or.inr h))
    exact hx (by simp [χ₁, h1, h2])
  have hχ₂0 : 0 ≤ χ₂ := fun x => mul_nonneg hM (hθ0 x)
  have hχ₁0 : 0 ≤ χ₁ := by
    intro x
    by_cases hx : x ∈ tsupport χ
    · have hb : |χ x| ≤ M := by
        have := hM₀ x hx
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _)
      simp only [χ₁, hθ1 x hx, mul_one]
      have := neg_abs_le (χ x)
      change 0 ≤ χ x + M
      linarith
    · simp only [χ₁, image_eq_zero_of_notMem_tsupport hx, zero_add]
      exact mul_nonneg hM (hθ0 x)
  have hdecomp : χ = fun x => χ₁ x - χ₂ x := by
    funext x
    simp only [χ₁, χ₂]
    ring
  have hL : ∀ x, lapTrace χ x = lapTrace χ₁ x - lapTrace χ₂ x := by
    intro x
    rw [hdecomp]
    exact lapTrace_sub hχ₁ hχ₂ x
  have h₁ := integral_lapTrace_mul_eq_zero_of_viscositySolution_laplace_of_nonneg hC hu hcont
    hχ₁ hχ₁c hsupp₁ hχ₁0
  have h₂ := integral_lapTrace_mul_eq_zero_of_viscositySolution_laplace_of_nonneg hC hu hcont
    hχ₂ hχ₂c hsupp₂ hχ₂0
  have hsplit : (fun x => lapTrace χ x * u x) =
      fun x => lapTrace χ₁ x * u x - lapTrace χ₂ x * u x := by
    funext x
    rw [hL x, sub_mul]
  rw [hsplit, integral_sub (integrable_lapTrace_mul hcont hχ₁ hχ₁c hsupp₁)
    (integrable_lapTrace_mul hcont hχ₂ hχ₂c hsupp₂), h₁, h₂, sub_zero]

end ViscositySolns
