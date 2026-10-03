/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.SMat
public import Mathlib.Analysis.Matrix.Normed

/-! # Structural coarse-coefficient interface for

The polynomial family is linear in K and κ and quadratic in F. Its two
scalar coefficients are bounded by one. Both the left-Jacobian coefficient and its
Infra candidate belong to this family; no analytic estimate is assumed.
-/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- Real two-by-two matrices used for the coarse effective coefficients. -/
abbrev CoarseMatrix := Matrix (Fin 2) (Fin 2) ℝ

/-- Polynomial combining the coarse matrix, flow matrix, diffusivity, and cutoff weights. -/
def coarseCoeffPolynomial (a b κ : ℝ) (K F : CoarseMatrix) : CoarseMatrix :=
  a • (K * (F - 1)) + b • ((F.transpose - 1) * (K - κ • (1 : CoarseMatrix)) * F)

/-- The split form is meaningful even at m = 0, where no cutoff partition
hypothesis is available. At positive m it is the single polynomial window sum. -/
def coarseCoeffWindow {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ a b t : ℝ) (x : Vec 2) : CoarseMatrix :=
  a • (I.Kmat κ m t * ∑' l : ℤ, I.hatXiML m l t • (I.flowGrad hΦ m l t x - 1)) +
    b • ∑' l : ℤ, I.hatXiML m l t •
      (((I.flowGrad hΦ m l t x).transpose - 1) *
        (I.Kmat κ m t - κ • (1 : CoarseMatrix)) * I.flowGrad hΦ m l t x)

/-- A structural polynomial description, not an assumption of regularity or bounds. -/
structure CoarseCoeffForm {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ)
    (s : ℝ → Vec 2 → CoarseMatrix) : Prop where
  window_form : ∃ a b : ℝ, |a| ≤ 1 ∧ |b| ≤ 1 ∧
    ∀ t x, s t x = coarseCoeffWindow I hΦ m κ a b t x

/-- coefficient as the quadratic structural window. -/
theorem sMat_eq_coarseCoeffWindow {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ t : ℝ) (x : Vec 2) :
    I.sMat hΦ m κ t x = coarseCoeffWindow I hΦ m κ 1 1 t x := by
  simp only [coarseCoeffWindow, one_smul, Ingredients.sMat]

/-- sMat instance of the common interface. -/
theorem sMat_coarseCoeffForm {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ) :
    CoarseCoeffForm I hΦ m κ (I.sMat hΦ m κ) :=
  ⟨1, 1, by norm_num, by norm_num, sMat_eq_coarseCoeffWindow I hΦ m κ⟩

namespace LeftJacobian

end LeftJacobian
end AVenhance.Infra.Section4
