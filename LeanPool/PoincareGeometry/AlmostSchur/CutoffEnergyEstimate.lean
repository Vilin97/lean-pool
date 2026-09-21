/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.L2MatrixForm
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyAbsorption

/-! # Absorption of the four actual cutoff energy terms

The fields `r,s` represent the weighted derivative quotient and the cutoff
derivative term. The fields `rη,sη` are their further cutoff multiples.
This is the integrated estimate; the local PDE supplies its tested identity.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace AlmostSchur

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bound the four-term energy expression using only actual L² field norms. -/
theorem cutoff_energy_quadratic_bound
    (A B : α → Matrix ι ι ℝ)
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) μ)
    (hB : ∀ i j, AEStronglyMeasurable (fun x => B x i j) μ)
    (r s rη sη D : Lp (EuclideanSpace ℝ ι) 2 μ)
    {ell Lam L H R G Z : ℝ} (hLam : 0 ≤ Lam) (hL : 0 ≤ L)
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hbA : ∀ᵐ x ∂μ, ∀ u v : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * u i * v j| ≤ Lam * ‖u‖ * ‖v‖)
    (hbB : ∀ᵐ x ∂μ, ∀ u v : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, B x i j * u i * v j| ≤ L * ‖u‖ * ‖v‖)
    (hco : ∀ᵐ x ∂μ, ell * ‖r x‖ ^ 2 ≤ ∑ i, ∑ j, A x i j * r x i * r x j)
    (hs : ‖s‖ ≤ H * R) (hrη : ‖rη‖ ≤ ‖r‖) (hsη : ‖sη‖ ≤ ‖s‖) (hD : ‖D‖ ≤ G)
    (htest : |l2MatrixForm A r r + 2 * l2MatrixForm A r s +
      l2MatrixForm B D rη + 2 * l2MatrixForm B D sη| ≤ Z * (‖r‖ + 2 * H * R)) :
    ell * ‖r‖ ^ 2 ≤
      (2 * Lam * H * R + L * G + Z) * ‖r‖ +
        (2 * L * H * G * R + 2 * H * Z * R) := by
  have hp := l2MatrixForm_self_lower A hA r hbA hco
  have h1 : |l2MatrixForm A r s| ≤ Lam * ‖r‖ * (H * R) :=
    (abs_l2MatrixForm_le A hA r s hLam hbA).trans
      (mul_le_mul_of_nonneg_left hs (mul_nonneg hLam (norm_nonneg _)))
  have h2 : |l2MatrixForm B D rη| ≤ L * G * ‖r‖ :=
    (abs_l2MatrixForm_le B hB D rη hL hbB).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hD hL) hrη (norm_nonneg _)
        (mul_nonneg hL hG))
  have h3 : |l2MatrixForm B D sη| ≤ L * G * (H * R) :=
    (abs_l2MatrixForm_le B hB D sη hL hbB).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hD hL) (hsη.trans hs) (norm_nonneg _)
        (mul_nonneg hL hG))
  have ht := (le_abs_self _).trans htest
  have hn1 := (neg_le_abs (l2MatrixForm A r s)).trans h1
  have hn2 := (neg_le_abs (l2MatrixForm B D rη)).trans h2
  have hn3 := (neg_le_abs (l2MatrixForm B D sη)).trans h3
  nlinarith

/-- An explicit step-independent bound follows once the tested field identities hold. -/
theorem cutoff_energy_norm_bound
    (A B : α → Matrix ι ι ℝ)
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) μ)
    (hB : ∀ i j, AEStronglyMeasurable (fun x => B x i j) μ)
    (r s rη sη D : Lp (EuclideanSpace ℝ ι) 2 μ)
    {ell Lam L H R G Z : ℝ} (hell : 0 < ell) (hLam : 0 ≤ Lam) (hL : 0 ≤ L)
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hbA : ∀ᵐ x ∂μ, ∀ u v : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * u i * v j| ≤ Lam * ‖u‖ * ‖v‖)
    (hbB : ∀ᵐ x ∂μ, ∀ u v : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, B x i j * u i * v j| ≤ L * ‖u‖ * ‖v‖)
    (hco : ∀ᵐ x ∂μ, ell * ‖r x‖ ^ 2 ≤ ∑ i, ∑ j, A x i j * r x i * r x j)
    (hs : ‖s‖ ≤ H * R) (hrη : ‖rη‖ ≤ ‖r‖) (hsη : ‖sη‖ ≤ ‖s‖) (hD : ‖D‖ ≤ G)
    (htest : |l2MatrixForm A r r + 2 * l2MatrixForm A r s +
      l2MatrixForm B D rη + 2 * l2MatrixForm B D sη| ≤ Z * (‖r‖ + 2 * H * R)) :
    ‖r‖ ≤ Real.sqrt ((2 * Lam * H * R + L * G + Z) ^ 2 +
      2 * ell * (2 * L * H * G * R + 2 * H * Z * R)) / ell :=
  norm_bound_of_quadratic_energy hell
    (cutoff_energy_quadratic_bound A B hA hB r s rη sη D hLam hL hH hR hG
      hbA hbB hco hs hrη hsη hD htest)

end AlmostSchur
