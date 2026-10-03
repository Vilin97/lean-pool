/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.WeakHarmonic.SecondDifference
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Basic.Core.JetsAndFTC

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Second differences of semiconvex functions and sup-convolutions

This file collects the pointwise facts about the compact sup-convolution

`w(ξ) = sup { u(x) - (λ / 2) |x - ξ|² | x ∈ K }`

used in the proof that viscosity subharmonic functions are distributionally
subharmonic:

* a `λ`-semiconvex function has coordinate second differences bounded below
  by `-n λ` (`neg_mul_le_coordSecondDifference_of_coordinateSemiconvexOn`);
* at a point where a function has a two-sided second-order jet `(p, X)`, its
  coordinate second differences converge to `trace X`
  (`tendsto_coordSecondDifference_of_hasSecondOrderJet`);
* maximizers in the definition of `w(η)` lie within `O(λ^{-1/2})` of `η`
  (`dist_lt_of_isMaxOn_supConvolutionKernel`), so `w` converges to `u`
  uniformly on `K` as `λ → ∞` (`exists_lambda_abs_compactSupConvolution_sub_le`).
-/

@[expose] public noncomputable section

open Filter Metric Set Asymptotics
open scoped Topology

namespace ViscositySolns

variable {n : Nat}

/-! ### Semiconvexity bounds second differences from below -/

/--
A `λ`-semiconvex function has central second differences bounded below by
`-λ |v|²`.
-/
theorem neg_mul_dotProduct_le_centralSecondDifference_of_coordinateSemiconvexOn
    {lambda : ℝ} {f : Point n → ℝ} (hf : CoordinateSemiconvexOn lambda Set.univ f)
    (v x : Point n) :
    -(lambda * dotProduct v v) ≤ centralSecondDifference f v x := by
  have h := hf (x + v) trivial (x - v) trivial (1 / 2) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) trivial
  have hmid : (1 / 2 : ℝ) • (x + v) + (1 / 2 : ℝ) • (x - v) = x := by
    rw [← smul_add, add_add_sub_cancel, ← two_smul ℝ x, smul_smul]
    norm_num
  have hdiff : x + v - (x - v) = (2 : ℝ) • v := by
    rw [add_sub_sub_cancel, two_smul]
  rw [hmid, hdiff, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
  unfold centralSecondDifference
  set d := dotProduct v v
  nlinarith [h]

theorem dotProduct_smul_single_self (h : ℝ) (i : Fin n) :
    dotProduct (h • (Pi.single i 1 : Point n)) (h • Pi.single i 1) = h ^ 2 := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  simp [dotProduct, Pi.single_apply]
  ring

/--
A `λ`-semiconvex function has coordinate second differences bounded below by
`-n λ`.
-/
theorem neg_mul_le_coordSecondDifference_of_coordinateSemiconvexOn
    {lambda : ℝ} {f : Point n → ℝ} (hf : CoordinateSemiconvexOn lambda Set.univ f)
    {h : ℝ} (hh : h ≠ 0) (x : Point n) :
    -(n * lambda) ≤ coordSecondDifference f h x := by
  have hterm : ∀ i : Fin n,
      -(lambda * h ^ 2) ≤ centralSecondDifference f (h • Pi.single i 1) x := by
    intro i
    have := neg_mul_dotProduct_le_centralSecondDifference_of_coordinateSemiconvexOn hf
      (h • Pi.single i 1) x
    rwa [dotProduct_smul_single_self] at this
  have hsum : ∑ _i : Fin n, -(lambda * h ^ 2) ≤
      ∑ i, centralSecondDifference f (h • Pi.single i 1) x :=
    Finset.sum_le_sum fun i _ => hterm i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hh2 : 0 < h ^ 2 := by positivity
  unfold coordSecondDifference
  rw [le_inv_mul_iff₀ hh2]
  linarith

/-! ### Second differences at points with a second-order jet -/

/--
If `(p, X)` is a two-sided second-order jet of `f` at `x`, then the coordinate
second differences of `f` at `x` converge to `trace X`.
-/
theorem tendsto_coordSecondDifference_of_hasSecondOrderJet {f : Point n → ℝ}
    {x p : Point n} {X : Hessian n} (hJ : HasSecondOrderJet f x p X) :
    Tendsto (fun h => coordSecondDifference f h x) (𝓝[≠] 0) (𝓝 (Matrix.trace X)) := by
  obtain ⟨⟨ρ₁, hρ₁, hup⟩, ⟨ρ₂, hρ₂, hlow⟩⟩ := hJ
  set Q : Point n → ℝ := quadraticModel x (f x) p X with hQ
  set σ : Point n → ℝ := fun y => f y - Q y with hσ
  have hσrem : SemijetRemainder Set.univ x σ := by
    have hsum := hρ₁.norm_left.add hρ₂.norm_left
    refine IsBigO.trans_isLittleO ?_ hsum
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hup, hlow] with y hy1 hy2
    simp only [one_mul, Real.norm_eq_abs, σ]
    have h1 : f y - Q y ≤ ρ₁ y := by simp only [Q]; linarith
    have h2 : ρ₂ y ≤ f y - Q y := by simp only [Q]; linarith
    rw [abs_le]
    constructor
    · have := neg_abs_le (ρ₂ y)
      have := abs_nonneg (ρ₁ y)
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |ρ₁ y| + |ρ₂ y|)]
      linarith
    · have := le_abs_self (ρ₁ y)
      have := abs_nonneg (ρ₂ y)
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |ρ₁ y| + |ρ₂ y|)]
      linarith
  have hline : ∀ a : Point n,
      Tendsto (fun t : ℝ => σ (x + t • a) / t ^ 2) (𝓝[≠] 0) (𝓝 0) := fun a =>
    (semijetRemainder_along_affine_isLittleO_sq (a := a) hσrem).tendsto_div_nhds_zero.mono_left
      nhdsWithin_le_nhds
  -- the quadratic part
  have hQline : ∀ (t : ℝ) (i : Fin n),
      Q (x + t • Pi.single i 1) + Q (x + t • -Pi.single i 1) - 2 * f x = t ^ 2 * X i i := by
    intro t i
    have hdiag : dotProduct (X.mulVec (Pi.single i 1)) (Pi.single i 1) = X i i := by
      simp [dotProduct, Matrix.mulVec, Pi.single_apply]
    simp only [Q, quadraticModel, add_sub_cancel_left, Matrix.mulVec_smul, Matrix.mulVec_neg,
      smul_dotProduct, dotProduct_smul, neg_dotProduct, dotProduct_neg, smul_eq_mul, hdiag]
    ring
  have hident : ∀ h : ℝ, h ≠ 0 →
      coordSecondDifference f h x =
        (∑ i : Fin n, (σ (x + h • Pi.single i 1) / h ^ 2 +
          σ (x + h • -Pi.single i 1) / h ^ 2)) + Matrix.trace X := by
    intro h hh
    have hterm : ∀ i : Fin n, centralSecondDifference f (h • Pi.single i 1) x =
        σ (x + h • Pi.single i 1) + σ (x + h • -Pi.single i 1) + h ^ 2 * X i i := by
      intro i
      have hq := hQline h i
      have hneg : x - h • Pi.single i (1 : ℝ) = x + h • -Pi.single i 1 := by
        rw [smul_neg, ← sub_eq_add_neg]
      simp only [centralSecondDifference, σ, hneg]
      linarith
    have hh2 : h ^ 2 ≠ 0 := by positivity
    rw [coordSecondDifference, Finset.sum_congr rfl fun i _ => hterm i, Matrix.trace,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply]
    field_simp
  have hlim : Tendsto (fun h : ℝ => (∑ i : Fin n, (σ (x + h • Pi.single i 1) / h ^ 2 +
      σ (x + h • -Pi.single i 1) / h ^ 2)) + Matrix.trace X) (𝓝[≠] 0)
      (𝓝 ((∑ _i : Fin n, ((0 : ℝ) + 0)) + Matrix.trace X)) := by
    refine Tendsto.add_const _ (tendsto_finsetSum _ fun i _ => ?_)
    exact (hline _).add (hline _)
  simp only [add_zero, Finset.sum_const_zero, zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (hident h hh).symm

/-! ### Localization and uniform approximation for sup-convolutions -/

theorem supConvolutionKernel_self (lambda : ℝ) (u : Point n → ℝ) (η : Point n) :
    supConvolutionKernel lambda u η η = u η := by
  simp [supConvolutionKernel]

/--
Maximizers in the sup-convolution are close to the base point: if
`4 (M + 1) ≤ λ δ²` and `|u| ≤ M` on `K`, then every maximizer `y ∈ K` of the
kernel at a base point `η ∈ K` satisfies `dist y η < δ`.
-/
theorem dist_lt_of_isMaxOn_supConvolutionKernel {K : Set (Point n)}
    {u : Point n → ℝ} {lambda M δ : ℝ} (hδ : 0 < δ)
    (hlam : 4 * (M + 1) ≤ lambda * δ ^ 2) (hM : ∀ z ∈ K, |u z| ≤ M)
    {η y : Point n} (hη : η ∈ K) (hy : y ∈ K)
    (hmax : IsMaxOn (fun z : Point n => supConvolutionKernel lambda u η z) K y) :
    dist y η < δ := by
  have hle : supConvolutionKernel lambda u η η ≤ supConvolutionKernel lambda u η y := hmax hη
  rw [supConvolutionKernel_self] at hle
  have hdot := norm_sq_le_dotProduct_self (y - η)
  have hMη := abs_le.mp (hM η hη)
  have hMy := abs_le.mp (hM y hy)
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM η hη)
  have hlampos : 0 < lambda := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    nlinarith [sq_nonneg δ]
  unfold supConvolutionKernel at hle
  set d := dotProduct (y - η) (y - η)
  rw [dist_eq_norm]
  by_contra hge
  replace hge := not_lt.mp hge
  have hsq : δ ^ 2 ≤ ‖y - η‖ ^ 2 := pow_le_pow_left₀ hδ.le hge 2
  have h1 : lambda * δ ^ 2 ≤ lambda * d := by
    have := hsq.trans hdot
    exact mul_le_mul_of_nonneg_left this hlampos.le
  nlinarith

/-- The compact sup-convolution dominates `u` on `K`. -/
theorem le_compactSupConvolution_of_isCompact {K : Set (Point n)} {u : Point n → ℝ}
    {lambda : ℝ} (hKne : K.Nonempty) (hK : IsCompact K) (hu : UpperSemicontinuousOn u K)
    {η : Point n} (hη : η ∈ K) :
    u η ≤ compactSupConvolution lambda K u η := by
  have := supConvolutionKernel_le_compactSupConvolution_of_exists_isMaxOn
    (lambda := lambda) (ξ := η)
    (fun ξ => exists_isMaxOn_supConvolutionKernel_of_isCompact hKne hK hu) hη
  rwa [supConvolutionKernel_self] at this

/--
Uniform approximation by sup-convolutions: if `u` is continuous on the compact
set `K` with `|u| ≤ M` there, then for every `ε > 0` and every `δ₀ > 0` there
is `λ > 0` with `4 (M + 1) ≤ λ δ₀²` and `|w_λ - u| ≤ ε` on `K`.
-/
theorem exists_lambda_abs_compactSupConvolution_sub_le {K : Set (Point n)}
    {u : Point n → ℝ} (hKne : K.Nonempty) (hK : IsCompact K) (hu : ContinuousOn u K)
    {M : ℝ} (hM : ∀ z ∈ K, |u z| ≤ M) {ε δ₀ : ℝ} (hε : 0 < ε) (hδ₀ : 0 < δ₀) :
    ∃ lambda > 0, 4 * (M + 1) ≤ lambda * δ₀ ^ 2 ∧
      ∀ η ∈ K, |compactSupConvolution lambda K u η - u η| ≤ ε := by
  obtain ⟨δ₁, hδ₁, hδ₁u⟩ :=
    Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hu) ε hε
  set δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM _ hKne.some_mem)
  set lambda := 4 * (M + 1) / δ ^ 2
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hlampos : 0 < lambda := by positivity
  have hlamδ : 4 * (M + 1) ≤ lambda * δ ^ 2 := by
    simp only [lambda]
    rw [div_mul_cancel₀ _ hδ2.ne']
  have hδle : δ ^ 2 ≤ δ₀ ^ 2 := pow_le_pow_left₀ hδ.le (min_le_left _ _) 2
  refine ⟨lambda, hlampos, hlamδ.trans (mul_le_mul_of_nonneg_left hδle hlampos.le), ?_⟩
  intro η hη
  have husc : UpperSemicontinuousOn u K :=
    (continuousOn_iff_lower_upperSemicontinuousOn.mp hu).2
  obtain ⟨y, hy, hmax⟩ := exists_isMaxOn_supConvolutionKernel_of_isCompact
    (lambda := lambda) (ξ := η) hKne hK husc
  have hdist : dist y η < δ := dist_lt_of_isMaxOn_supConvolutionKernel hδ hlamδ hM hη hy hmax
  have hclose : dist (u y) (u η) < ε :=
    hδ₁u y hy η hη (hdist.trans_le (min_le_right _ _))
  have hlow := le_compactSupConvolution_of_isCompact (lambda := lambda) hKne hK husc hη
  have hval := compactSupConvolution_eq_of_isMaxOn hy hmax
  have hkernel : supConvolutionKernel lambda u η y ≤ u y := by
    unfold supConvolutionKernel
    have hdot : 0 ≤ dotProduct (y - η) (y - η) :=
      (sq_nonneg ‖y - η‖).trans (norm_sq_le_dotProduct_self _)
    have : 0 ≤ lambda / 2 * dotProduct (y - η) (y - η) := by positivity
    linarith
  rw [Real.dist_eq] at hclose
  have hup := (le_abs_self _).trans hclose.le
  rw [abs_of_nonneg (by linarith)]
  linarith

end ViscositySolns
