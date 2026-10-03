/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebra
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.SpaceErgodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds

/-! # Pointwise bounds for the remainder fields of `e.grad.tildetheta.again`

Componentwise (entrywise) bounds, valid at every point `(t, x)` with `ξ_{m,k}(t) ≠ 0`, for the sum
`E¹ + E² + E³` of the three remainder fields in terms of `gT ≥ |∂_p T|` and `h_p ≥ |∂_i∂_p T|`:

`|(E¹ + E² + E³)_i| ≤ 20 e c gT + ε_m c (4 (h₀ + h₁) + 16 D gT)`,

with `e = ε_{m-1}^{2δ}`, `c = a_m ε_m²/κ_m` and `D = 2^16 ε_{m-1}⁻¹`.  Source: `enhance.tex`
8146–8200 (the second through fourth displays after `e.grad.tildetheta.again`). -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5

/-! ### Elementary entry calculus on `2 × 2` matrices -/

theorem abs_mul_le_of_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem abs_add_le_of_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a + b| ≤ A + B :=
  (abs_add_le _ _).trans (add_le_add ha hb)

theorem abs_mulVec_le {M : Matrix (Fin 2) (Fin 2) ℝ} {μ gT : ℝ} {g : Vec 2}
    (hM : ∀ i j, |M i j| ≤ μ) (hg : ∀ j, |g j| ≤ gT) (i : Fin 2) :
    |M.mulVec g i| ≤ 2 * μ * gT := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have := abs_add_le_of_le (abs_mul_le_of_le (hM i 0) (hg 0)) (abs_mul_le_of_le (hM i 1) (hg 1))
  linarith

theorem abs_matMul_le {M N : Matrix (Fin 2) (Fin 2) ℝ} {μ ν : ℝ}
    (hM : ∀ i j, |M i j| ≤ μ) (hN : ∀ i j, |N i j| ≤ ν) (i j : Fin 2) :
    |(M * N) i j| ≤ 2 * μ * ν := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  have := abs_add_le_of_le (abs_mul_le_of_le (hM i 0) (hN 0 j)) (abs_mul_le_of_le (hM i 1) (hN 1 j))
  linarith

theorem abs_le_two_of_sub_one {A : Matrix (Fin 2) (Fin 2) ℝ} {e : ℝ} (he1 : e ≤ 1)
    (hA : ∀ i j, |(A - 1) i j| ≤ e) (i j : Fin 2) : |A i j| ≤ 2 := by
  have h1 : A i j = (A - 1) i j + (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    simp
  have h2 : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [h1]
  have := abs_add_le_of_le (hA i j) h2
  linarith

/-- Componentwise bounds for the second and third remainder fields. -/
theorem flowInv_flowFwd_component_le {A C Fl : Matrix (Fin 2) (Fin 2) ℝ} {e c gT : ℝ}
    {g : Vec 2} (he1 : e ≤ 1) (hA : ∀ i j, |(A - 1) i j| ≤ e) (hC : ∀ i j, |C i j| ≤ c)
    (hFl : ∀ i j, |(Fl - 1) i j| ≤ e) (hg : ∀ j, |g j| ≤ gT) (i : Fin 2) :
    |((A - 1) * C).mulVec g i| ≤ 4 * e * c * gT ∧
      |(A * C * (Fl - 1)).mulVec g i| ≤ 16 * e * c * gT := by
  have hA2 := abs_le_two_of_sub_one he1 hA
  have hc : 0 ≤ c := (abs_nonneg _).trans (hC 0 0)
  have he : 0 ≤ e := (abs_nonneg _).trans (hA 0 0)
  have hAC := abs_matMul_le hA2 hC
  have h1 := abs_mulVec_le (abs_matMul_le hA hC) hg i
  have h2 := abs_mulVec_le (abs_matMul_le hAC hFl) hg i
  constructor
  · linarith
  · linarith

/-- Componentwise bound for the Hessian remainder field. -/
theorem hessian_component_le {χ g : Vec 2} {Fl : Matrix (Fin 2) (Fin 2) ℝ} {a : Fin 2 → ℝ}
    {Dd : Fin 2 → Fin 2 → Fin 2 → ℝ} {Hs h : Fin 2 → ℝ} {cχ D gT : ℝ}
    (hχ : ∀ j, |χ j| ≤ cχ) (hFl : ∀ j p, |Fl j p| ≤ 2) (ha : ∀ q, |a q| ≤ 2)
    (hD : ∀ p j q, |Dd p j q| ≤ D) (hH : ∀ p, |Hs p| ≤ h p) (hg : ∀ p, |g p| ≤ gT) :
    |∑ j : Fin 2, χ j * ∑ p : Fin 2, (Fl j p * Hs p + (∑ q : Fin 2, a q * Dd p j q) * g p)| ≤
      cχ * (4 * (h 0 + h 1) + 16 * D * gT) := by
  have hq : ∀ p j, |∑ q : Fin 2, a q * Dd p j q| ≤ 4 * D := by
    intro p j
    simp only [Fin.sum_univ_two]
    have := abs_add_le_of_le (abs_mul_le_of_le (ha 0) (hD p j 0))
      (abs_mul_le_of_le (ha 1) (hD p j 1))
    linarith
  have hp : ∀ j p, |Fl j p * Hs p + (∑ q : Fin 2, a q * Dd p j q) * g p| ≤
      2 * h p + 4 * D * gT := fun j p =>
    abs_add_le_of_le (abs_mul_le_of_le (hFl j p) (hH p)) (abs_mul_le_of_le (hq p j) (hg p))
  have hj : ∀ j, |∑ p : Fin 2, (Fl j p * Hs p + (∑ q : Fin 2, a q * Dd p j q) * g p)| ≤
      2 * (h 0 + h 1) + 8 * D * gT := by
    intro j
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => hp j p).trans ?_
    simp only [Fin.sum_univ_two]
    linarith
  have hterm : ∀ j, |χ j * ∑ p : Fin 2, (Fl j p * Hs p +
      (∑ q : Fin 2, a q * Dd p j q) * g p)| ≤ cχ * (2 * (h 0 + h 1) + 8 * D * gT) :=
    fun j => abs_mul_le_of_le (hχ j) (hj j)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
  simp only [Fin.sum_univ_two]
  linarith

/-! ### The second derivative of the flow -/

theorem fderiv_apply_const_eq {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) (z : Vec 2) (v w : Vec 2) :
    fderiv ℝ (fun y => fderiv ℝ f y w) z v = iteratedFDeriv ℝ 2 f z ![v, w] := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) z
  rw [iteratedFDeriv_two_apply]
  have := (h1.hasFDerivAt.clm_apply (hasFDerivAt_const w z))
  rw [this.fderiv]
  simp

variable {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The second derivative `xFlowHess` as an iterated Fréchet derivative. -/
theorem xFlowHess_eq_iteratedFDeriv (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ)
    (z : Vec 2) (p j q : Fin 2) :
    xFlowHess I hΦ m l t z p j q =
      iteratedFDeriv ℝ 2 (fun y => I.xFlow hΦ m l t y p) z ![basisVec q, basisVec j] := by
  have hf : ContDiff ℝ ∞ (fun y => I.xFlow hΦ m l t y p) :=
    (contDiff_apply ℝ ℝ p).comp (contDiff_xFlow_slice I hΦ m l t)
  unfold xFlowHess
  simp only [spaceGrad]
  exact fderiv_apply_const_eq hf z (basisVec q) (basisVec j)

/-- Entry bound `|∂_q∂_j X^p| ≤ 2^16 ε_{m-1}⁻¹` on `supp ξ_{m,k}`. -/
theorem abs_xFlowHess_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ) {t : ℝ}
    (hξ : I.xiMK m k t ≠ 0) (z : Vec 2) (p j q : Fin 2) :
    |xFlowHess I hΦ m (lIdx β I.Λ m k) t z p j q| ≤ 2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹ := by
  rw [xFlowHess_eq_iteratedFDeriv]
  exact xFlow_second_deriv_le hΦ hm k hξ z q j p

end AVenhance.Infra.Section5.RelativeError
