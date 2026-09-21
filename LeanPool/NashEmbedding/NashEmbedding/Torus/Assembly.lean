/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.Main
import LeanPool.NashEmbedding.NashEmbedding.Torus.RealizableMetrics

/-!
# Glue for the final assembly of Nash's theorem on the torus

Small facts connecting Theorem A's interface (`integrationEmbed`, `sobolevNormSqDistrib`),
Theorem B's smallness measure `hSize`, and the metric-splitting step of Wassermann §7:

* `hSize` is the sum of the squared `H^r` norms of the integration embeddings of the
  entries, and it scales quadratically;
* the Gram matrix `∂u·∂u` of a smooth periodic map is smooth periodic and symmetric, and
  positive definite when `u` is free (the first derivatives are linearly independent);
* for a positive-definite smooth metric `g` and any smooth periodic symmetric `g₀`, there is
  `δ > 0` with `g - δ • g₀` still positive definite (compactness of the period cube and
  `posDefSmoothMetric_stability`).
-/

open scoped BigOperators ContDiff
open NashEmbedding.Sobolev Matrix

noncomputable
section

namespace NashEmbedding

variable {n N : ℕ}

/-! ## `hSize` and Theorem A's residual -/

/-- `hSize` as a sum of `sobolevNormSqDistrib` of integration embeddings. -/
lemma hSize_eq_sum_sobolevNormSqDistrib (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) :
    hSize n h = ∑ i, ∑ j, sobolevNormSqDistrib n (bLevel n)
      (integrationEmbed n (fun x => ((h x i j : ℝ) : ℂ))) := by
  unfold hSize sobolevNormSqDistrib
  simp only [fourierCoeffDistrib_integrationEmbed]

/-- `hSize (c • h) = c² · hSize h`. -/
lemma hSize_smul (c : ℝ) (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) :
    hSize n (c • h) = c ^ 2 * hSize n h := by
  unfold hSize
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : (fun x => (((c • h) x i j : ℝ) : ℂ)) = fun x => (c : ℂ) * ((h x i j : ℝ) : ℂ) := by
    funext x; simp
  rw [this, stdFourierCoeff_const_mul, sobolevNormSq_smul]
  simp

/-! ## Gram matrices -/

/-- The Gram matrix `∂ᵢu · ∂ⱼu` of a map. -/
def gramMetric (u : (Fin n → ℝ) → (Fin N → ℝ)) : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
  fun x i j => pderiv i u x ⬝ᵥ pderiv j u x

lemma gramMetric_symm (u : (Fin n → ℝ) → (Fin N → ℝ)) (x : Fin n → ℝ) :
    (gramMetric u x).IsSymm := by
  ext i j
  simp [gramMetric, transpose_apply, dotProduct_comm]

lemma gramMetric_smoothPeriodic {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u) :
    SmoothPeriodic (gramMetric u) := by
  refine ⟨?_, ?_⟩
  · refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
    exact contDiff_dotProduct (pderiv_contDiff hu.smooth i) (pderiv_contDiff hu.smooth j)
  · intro x k
    funext i j
    simp only [gramMetric]
    rw [isPeriodic2Pi_pderiv hu.periodic i x k, isPeriodic2Pi_pderiv hu.periodic j x k]

/-- The Gram matrix of a free map is positive definite (its first partials are linearly
independent at every point). -/
lemma gramMetric_posDef_of_free {u : (Fin n → ℝ) → (Fin N → ℝ)} (hfree : IsFree u) (x : Fin n → ℝ) :
    (gramMetric u x).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · change (gramMetric u x)ᴴ = gramMetric u x
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact gramMetric_symm u x
  · intro v hv
    set w : Fin N → ℝ := ∑ i, v i • pderiv i u x with hw
    have hL : w ⬝ᵥ w = ∑ i, v i * ∑ j, (pderiv i u x ⬝ᵥ pderiv j u x) * v j := by
      simp only [hw, sum_dotProduct, smul_dotProduct, dotProduct_sum, dotProduct_smul,
        smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dotProduct_comm, mul_comm]
    have hR : v ⬝ᵥ (gramMetric u x).mulVec v = ∑ i, v i * ∑ j, (pderiv i u x ⬝ᵥ pderiv j u x) *
        v j := by
      simp only [mulVec, dotProduct, gramMetric]
    have hw0 : w ≠ 0 := by
      intro h0
      have hli := (hfree x).comp Sum.inl Sum.inl_injective
      have hcoef := (Fintype.linearIndependent_iff.mp hli) v (by
        simpa [hw, frame, Function.comp] using h0)
      exact hv (funext hcoef)
    have hstar : star v = v := star_trivial v
    have hnn : 0 ≤ w ⬝ᵥ w := by
      simpa [dotProduct] using Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
        mul_self_nonneg (w i))
    rw [hstar, hR, ← hL]
    exact lt_of_le_of_ne hnn fun h => hw0 (dotProduct_self_eq_zero.mp h.symm)

lemma gramMetric_isPosDefSmoothMetric {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u)
    (hfree : IsFree u) : IsPosDefSmoothMetric (gramMetric u) :=
  ⟨gramMetric_smoothPeriodic hu, gramMetric_posDef_of_free hfree⟩

/-- `u` realizes its own Gram matrix. -/
lemma realizes_gramMetric (u : (Fin n → ℝ) → (Fin N → ℝ)) : Realizes u
    (gramMetric u) := fun _ _ _ => rfl

/-! ## The splitting step -/

/-- `matOpNorm` is absolutely homogeneous. -/
private lemma matOpNorm_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    matOpNorm (c • A) = |c| * matOpNorm A := by
  unfold matOpNorm
  rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]

/-- `A ↦ matOpNorm A` is continuous. -/
private lemma continuous_matOpNorm :
    Continuous (matOpNorm : Matrix (Fin n) (Fin n) ℝ → ℝ) := by
  refine continuous_norm.comp ?_
  exact (LinearMap.toContinuousLinearMap.toLinearMap.comp
    (Matrix.toLin' (R := ℝ) (n := Fin n) (m := Fin n)).toLinearMap).continuous_of_finiteDimensional

/-- A continuous `2πℤⁿ`-periodic real function is bounded above (by a nonnegative constant):
every value is attained on the compact period cube. -/
private lemma exists_le_of_continuous_periodic {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) (hp : IsPeriodic2Pi f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, f x ≤ M := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 2 * Real.pi)) hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set k : Fin n → ℤ := fun i => -⌊x i / (2 * Real.pi)⌋ with hk
  have hmem : x + periodicShift n k ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi) := by
    constructor <;> intro i <;>
      simp only [periodicShift, hk, Pi.add_apply, Pi.zero_apply, Int.cast_neg]
    · have := Int.floor_le (x i / (2 * Real.pi))
      have hx : (⌊x i / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ x i := by
        calc (⌊x i / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ (x i / (2 * Real.pi)) * (2 * Real.pi) :=
              mul_le_mul_of_nonneg_right this hpi.le
          _ = x i := by field_simp
      nlinarith [hx]
    · have := Int.lt_floor_add_one (x i / (2 * Real.pi))
      have hx : x i < ((⌊x i / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) := by
        have h2 : (x i / (2 * Real.pi)) * (2 * Real.pi) < ((⌊x i / (2 * Real.pi)⌋ : ℝ) + 1) *
            (2 * Real.pi) := by
          exact mul_lt_mul_of_pos_right this hpi
        rwa [div_mul_cancel₀ _ (ne_of_gt hpi)] at h2
      nlinarith [hx]
  have hbd := hC _ hmem
  rw [hp x k] at hbd
  exact le_trans (le_trans (le_abs_self _) (by rwa [Real.norm_eq_abs] at hbd)) (le_max_left _ _)

/-- For a positive-definite smooth metric `g` and a smooth periodic symmetric `g₀`, some
`g - δ • g₀` with `δ > 0` is still a positive-definite smooth metric. -/
theorem exists_delta_posDef_sub {g g₀ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsPosDefSmoothMetric g) (hg₀ : SmoothPeriodic g₀) (hsymm : ∀ x, (g₀ x).IsSymm) :
    ∃ δ : ℝ, 0 < δ ∧ IsPosDefSmoothMetric (g - δ • g₀) := by
  obtain ⟨η, hη, hstab⟩ := posDefSmoothMetric_stability hg
  obtain ⟨M, hM0, hM⟩ := exists_le_of_continuous_periodic
    (f := fun x => matOpNorm (g₀ x)) (continuous_matOpNorm.comp hg₀.smooth.continuous)
    (fun x k => by simp only [hg₀.periodic x k])
  set δ : ℝ := η / (M + 1) with hδdef
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have hδ : 0 < δ := div_pos hη hM1
  set h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun x => (-δ) • g₀ x with hhdef
  have hcont : Continuous h := by
    refine continuous_matrix fun i j => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp
        hg₀.smooth.continuous)).const_smul (-δ)
  have hper : IsPeriodic2Pi h := fun x k => by simp only [hhdef, hg₀.periodic x k]
  have hherm : ∀ x, (h x).IsHermitian := by
    intro x
    change ((-δ) • g₀ x)ᴴ = (-δ) • g₀ x
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_smul, (hsymm x).eq]
  have hnorm : ∀ x, matOpNorm (h x) < η := by
    intro x
    change matOpNorm ((-δ) • g₀ x) < η
    rw [matOpNorm_smul, abs_neg, abs_of_pos hδ]
    have h1 : δ * matOpNorm (g₀ x) ≤ δ * M := mul_le_mul_of_nonneg_left (hM x) hδ.le
    have h2 : δ * (M + 1) = η := by
      rw [hδdef, div_mul_cancel₀ _ (ne_of_gt hM1)]
    nlinarith [hδ]
  have hposdef := hstab h hcont hper hherm hnorm
  refine ⟨δ, hδ, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · have hdiff : ContDiff ℝ ∞ (fun x => δ • g₀ x) := by
      refine contDiff_matrix fun i j => ?_
      exact contDiff_const.mul ((contDiff_apply _ _ j).comp ((contDiff_apply _ _ i).comp
          hg₀.smooth))
    exact hg.smoothPeriodic.smooth.sub hdiff
  · intro x k
    change g (x + periodicShift n k) - δ • g₀ (x + periodicShift n k) = g x - δ • g₀ x
    rw [hg.smoothPeriodic.periodic x k, hg₀.periodic x k]
  · intro x
    have := hposdef x
    have heq : g x + h x = (g - δ • g₀) x := by
      change g x + (-δ) • g₀ x = g x - δ • g₀ x
      rw [neg_smul, ← sub_eq_add_neg]
    rwa [heq] at this

end NashEmbedding

end
