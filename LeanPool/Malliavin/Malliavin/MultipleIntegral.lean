/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.IteratedIntegral

/-!
# Symmetrized multiple-integral operators

Rung 3 of the Clark--Ocone ladder.  For the selected law-level family associated with `B`, define
the order-`n` multiple operator by the usual formula

`Iₙ(f) = n! • Jₙ(symmetrizeL f)`,

where `Jₙ` is the selected law-level operator from `Malliavin.IteratedIntegral`.  The simplex
tiling identity then turns the `Jₙ` isometry into

`⟪Iₙ(f), Iₙ(g)⟫ = n! * ⟪symmetrizeL f, symmetrizeL g⟫`.

Different orders are orthogonal, positive orders are centered, and order zero consists of
constants.  These are the Hilbert-space laws consumed by the next rung.  Identifying these
operators with genuine multiple Wiener--Itô integrals additionally requires the Brownian
ordered-box property; that property is not part of `IteratedIntegralFamily` itself.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace Malliavin

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- Tiling identity for the pointwise inner product of two `L²` symmetrizations. -/
theorem integral_inner_symmetrizeL_eq_factorial_smul_setIntegral (n : ℕ)
    (f g : IteratedKernel n) :
    (∫ t, inner ℝ
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f t)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g t)
        ∂iteratedKernelMeasure n) =
      n.factorial • ∫ t in simplex ℝ≥0 n, inner ℝ
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f t)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g t)
        ∂iteratedKernelMeasure n := by
  let sf := symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f
  let sg := symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g
  have hf := coeFn_symmetrizeL (E := ℝ) (μ := nonnegativeLebesgueMeasure) n 2 f
  have hg := coeFn_symmetrizeL (E := ℝ) (μ := nonnegativeLebesgueMeasure) n 2 g
  have hinner :
      (fun t => inner ℝ (sf t) (sg t)) =ᵐ[iteratedKernelMeasure n]
        fun t => inner ℝ (symmetrize n (⇑f) t) (symmetrize n (⇑g) t) := by
    filter_upwards [hf, hg] with t hft hgt
    exact congrArg₂ (inner ℝ) hft hgt
  have hsym : IsSymmetric n
      (fun t => inner ℝ (symmetrize n (⇑f) t) (symmetrize n (⇑g) t)) := by
    intro σ t
    change inner ℝ (symmetrize n (⇑f) (t ∘ σ)) (symmetrize n (⇑g) (t ∘ σ)) =
      inner ℝ (symmetrize n (⇑f) t) (symmetrize n (⇑g) t)
    rw [isSymmetric_symmetrize n (⇑f) σ t, isSymmetric_symmetrize n (⇑g) σ t]
  have hint : Integrable
      (fun t => inner ℝ (symmetrize n (⇑f) t) (symmetrize n (⇑g) t))
      (iteratedKernelMeasure n) :=
    (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) sf sg).congr hinner
  have htile := integral_eq_factorial_smul_setIntegral_simplex
    (μ := nonnegativeLebesgueMeasure) hsym hint
  calc
    (∫ t, inner ℝ (sf t) (sg t) ∂iteratedKernelMeasure n) =
        ∫ t, inner ℝ (symmetrize n (⇑f) t) (symmetrize n (⇑g) t)
          ∂iteratedKernelMeasure n := integral_congr_ae hinner
    _ = n.factorial • ∫ t in simplex ℝ≥0 n,
          inner ℝ (symmetrize n (⇑f) t) (symmetrize n (⇑g) t)
          ∂iteratedKernelMeasure n := htile
    _ = n.factorial • ∫ t in simplex ℝ≥0 n, inner ℝ (sf t) (sg t)
          ∂iteratedKernelMeasure n := by
      congr 1
      exact integral_congr_ae hinner.restrict.symm

/-- The selected law-level order-`n` multiple operator `Iₙ = n! Jₙ ∘ symmetrizeL`. -/
noncomputable def multipleIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ) :
    IteratedKernel n →L[ℝ] RandomL2 P :=
  (n.factorial : ℝ) • (iteratedIntegralCLM hB n).comp
    (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2)

/-- Evaluation formula for `Iₙ`. -/
theorem multipleIntegralCLM_apply (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    multipleIntegralCLM hB n f = (n.factorial : ℝ) •
      iteratedIntegralCLM hB n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) :=
  rfl

/-- The selected multiple operator only depends on the symmetric part of its kernel. -/
theorem multipleIntegralCLM_symmetrize (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    multipleIntegralCLM hB n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) =
      multipleIntegralCLM hB n f := by
  simp only [multipleIntegralCLM, smul_apply,
    ContinuousLinearMap.comp_apply, symmetrizeL_symmetrizeL]

/-- Every vector in the `n + 1` simplex summand of the global positive tower is the value of the
selected order-`n + 1` multiple operator. -/
theorem exists_multipleIntegralCLM_eq_simplexIntegralLI
    (hB : IsPreBrownianReal B P) (n : ℕ)
    (g : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    ∃ f : IteratedKernel (n + 1),
      multipleIntegralCLM hB (n + 1) f =
        IteratedIntegralConstruction.simplexIntegralLI hB n g := by
  let c : ℝ := ((n + 1).factorial : ℕ)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact_mod_cast (n + 1).factorial_ne_zero
  obtain ⟨f, hf⟩ :=
    IteratedIntegralConstruction.symmetrizeRestrict_surjective (n + 1) (c⁻¹ • g)
  refine ⟨f, ?_⟩
  rw [multipleIntegralCLM_apply, iteratedIntegralCLM_symmetrized, hf, map_smul]
  change c • c⁻¹ • IteratedIntegralConstruction.simplexIntegralLI hB n g = _
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- Same-order isometry for the selected multiple operators, in polarized form. -/
theorem inner_multipleIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ)
    (f g : IteratedKernel n) :
    inner ℝ (multipleIntegralCLM hB n f) (multipleIntegralCLM hB n g) =
      (n.factorial : ℝ) * inner ℝ
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g) := by
  rw [multipleIntegralCLM]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, real_inner_smul_left,
    real_inner_smul_right]
  rw [inner_iteratedIntegralCLM, MeasureTheory.L2.inner_def]
  have htile := integral_inner_symmetrizeL_eq_factorial_smul_setIntegral n f g
  rw [← Nat.cast_smul_eq_nsmul ℝ] at htile
  rw [htile]
  simp only [smul_eq_mul]

/-- On symmetric kernels, the same-order isometry has its conventional `n!` normalization. -/
theorem inner_multipleIntegralCLM_of_fixed (hB : IsPreBrownianReal B P) (n : ℕ)
    (f g : IteratedKernel n)
    (hf : symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f = f)
    (hg : symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g = g) :
    inner ℝ (multipleIntegralCLM hB n f) (multipleIntegralCLM hB n g) =
      (n.factorial : ℝ) * inner ℝ f g := by
  simpa only [hf, hg] using inner_multipleIntegralCLM hB n f g

/-- Squared-norm form of the selected-operator isometry. -/
theorem norm_sq_multipleIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    ‖multipleIntegralCLM hB n f‖ ^ 2 = (n.factorial : ℝ) *
      ‖symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_multipleIntegralCLM hB n f f

/-- Exact norm of the selected multiple operator. -/
theorem norm_multipleIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    ‖multipleIntegralCLM hB n f‖ = Real.sqrt (n.factorial : ℝ) *
      ‖symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f‖ := by
  have h := congrArg Real.sqrt (norm_sq_multipleIntegralCLM hB n f)
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] using h

/-- Operator-level bound inherited from the symmetrization contraction. -/
theorem norm_multipleIntegralCLM_le (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    ‖multipleIntegralCLM hB n f‖ ≤ Real.sqrt (n.factorial : ℝ) * ‖f‖ := by
  rw [norm_multipleIntegralCLM]
  exact mul_le_mul_of_nonneg_left
    (norm_symmetrizeL_apply_le (E := ℝ) (μ := nonnegativeLebesgueMeasure) n 2 f)
    (Real.sqrt_nonneg _)

/-- Outputs of selected multiple operators of different orders are orthogonal. -/
theorem inner_multipleIntegralCLM_ne (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) (f : IteratedKernel m) (g : IteratedKernel n) :
    inner ℝ (multipleIntegralCLM hB m f) (multipleIntegralCLM hB n g) = 0 := by
  rw [multipleIntegralCLM_apply, multipleIntegralCLM_apply, real_inner_smul_left,
    real_inner_smul_right, inner_iteratedIntegralCLM_ne hB hmn, mul_zero, mul_zero]

/-- Positive-order selected multiple operators have centered output. -/
theorem integral_multipleIntegralCLM (hB : IsPreBrownianReal B P) {n : ℕ} (hn : 0 < n)
    (f : IteratedKernel n) :
    ∫ ω, multipleIntegralCLM hB n f ω ∂P = 0 := by
  let sf := symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f
  have hcoe : (fun ω => multipleIntegralCLM hB n f ω) =ᵐ[P]
      fun ω => (n.factorial : ℝ) * iteratedIntegralCLM hB n sf ω := by
    change (⇑(multipleIntegralCLM hB n f) : Ω → ℝ) =ᵐ[P]
      (n.factorial : ℝ) • ⇑(iteratedIntegralCLM hB n sf)
    rw [multipleIntegralCLM_apply]
    exact Lp.coeFn_smul (n.factorial : ℝ) (iteratedIntegralCLM hB n sf)
  calc
    (∫ ω, multipleIntegralCLM hB n f ω ∂P) =
        ∫ ω, (n.factorial : ℝ) * iteratedIntegralCLM hB n sf ω ∂P :=
      integral_congr_ae hcoe
    _ = (n.factorial : ℝ) * ∫ ω, iteratedIntegralCLM hB n sf ω ∂P :=
      integral_const_mul _ _
    _ = 0 := by rw [integral_iteratedIntegralCLM hB hn sf, mul_zero]

/-- The kernel of `Iₙ` is exactly the kernel of symmetrization. -/
theorem multipleIntegralCLM_eq_zero_iff (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    multipleIntegralCLM hB n f = 0 ↔
      symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f = 0 := by
  constructor
  · intro hI
    have hnorm := norm_sq_multipleIntegralCLM hB n f
    rw [hI, norm_zero, zero_pow (by decide)] at hnorm
    have hprod : (n.factorial : ℝ) *
        ‖symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f‖ ^ 2 = 0 := hnorm.symm
    rcases mul_eq_zero.mp hprod with hfac | hsq
    · exact absurd hfac (by exact_mod_cast n.factorial_ne_zero)
    · exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro hs
    rw [← multipleIntegralCLM_symmetrize hB n f, hs, map_zero]

/-- Order zero is the constant embedding, hence the selected zeroth homogeneous range. -/
theorem multipleIntegralCLM_zeroOrder (hB : IsPreBrownianReal B P)
    (f : IteratedKernel 0) :
    (fun ω => multipleIntegralCLM hB 0 f ω) =ᵐ[P]
      fun _ => ∫ t, f t ∂iteratedKernelMeasure 0 := by
  have hfixed : symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) 0 2 f = f := by
    rw [symmetrizeL_eq_self_iff]
    intro σ
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst σ
    exact Filter.Eventually.of_forall fun _ => rfl
  simpa only [multipleIntegralCLM_apply, Nat.factorial_zero, Nat.cast_one, one_smul, hfixed] using
    iteratedIntegralCLM_zeroOrder hB f

end Malliavin

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
