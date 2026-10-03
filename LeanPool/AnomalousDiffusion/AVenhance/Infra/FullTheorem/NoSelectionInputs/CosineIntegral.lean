/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.UnitCube
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.L2NormSq
public import LeanPool.AnomalousDiffusion.Homogenization.Sobolev.H1.Definitions
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Integrals of functions of `x₀` over the unit cube, and `∫ cos²` of the cosine data -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSelectionInputs

open AVenhance

/-- A function of the first coordinate integrates over the unit cube as a one-dimensional
integral over `(0,1)`. -/
theorem integral_unitCube_coord0 (G : ℝ → ℝ) :
    ∫ x in unitCube, G (x 0) = ∫ s in Set.Ioo (0 : ℝ) 1, G s := by
  have hpre : unitCube =
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹'
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
    ext x
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_preimage,
      Set.mem_prod, MeasurableEquiv.finTwoArrow_apply, Fin.forall_fin_two]
  have hmp := volume_preserving_finTwoArrow ℝ
  have h := hmp.setIntegral_preimage_emb (MeasurableEquiv.finTwoArrow.measurableEmbedding)
    (fun p : ℝ × ℝ => G p.1 * (fun _ : ℝ => (1 : ℝ)) p.2)
    (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)
  rw [← hpre] at h
  have h2 : ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1, G p.1 * (fun _ : ℝ => (1 : ℝ)) p.2
      ∂(volume : Measure (ℝ × ℝ)) = ∫ s in Set.Ioo (0 : ℝ) 1, G s := by
    rw [Measure.volume_eq_prod, setIntegral_prod_mul (μ := volume) (ν := volume)
      G (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 1) (Set.Ioo 0 1)]
    simp
  simp only [MeasurableEquiv.finTwoArrow_apply, mul_one] at h
  rw [← h2]
  simpa using h

/-- `∫_0^1 cos²(2π n s + φ) ds = 1/2`. -/
theorem integral_cos_sq_phase (n : ℕ) (hn : 1 ≤ n) (φ : ℝ) :
    ∫ s in Set.Ioo (0 : ℝ) 1, Real.cos (2 * Real.pi * n * s + φ) ^ 2 = 1 / 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hpos : 0 < 2 * Real.pi * (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have h := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1)
    (fun x : ℝ => Real.cos x ^ 2) hpos.ne' φ
  rw [h, integral_cos_sq]
  have hc : Real.cos (2 * Real.pi * n * 1 + φ) = Real.cos φ := by
    rw [mul_one, show 2 * Real.pi * n + φ = φ + (n : ℕ) * (2 * Real.pi) by ring,
      Real.cos_add_nat_mul_two_pi]
  have hs : Real.sin (2 * Real.pi * n * 1 + φ) = Real.sin φ := by
    rw [mul_one, show 2 * Real.pi * n + φ = φ + (n : ℕ) * (2 * Real.pi) by ring,
      Real.sin_add_nat_mul_two_pi]
  rw [hc, hs]
  simp only [mul_zero, zero_add, smul_eq_mul]
  field_simp
  ring

/-- `∫_{cube} (A cos(2π n x₀ + φ))² = A²/2`. -/
theorem integral_unitCube_cos_sq (n : ℕ) (hn : 1 ≤ n) (A φ : ℝ) :
    ∫ x in unitCube, (A * Real.cos (2 * Real.pi * n * x 0 + φ)) ^ 2 = A ^ 2 / 2 := by
  have h := integral_unitCube_coord0 (fun s => (A * Real.cos (2 * Real.pi * n * s + φ)) ^ 2)
  rw [h]
  have : ∀ s : ℝ, (A * Real.cos (2 * Real.pi * n * s + φ)) ^ 2 =
      A ^ 2 * Real.cos (2 * Real.pi * n * s + φ) ^ 2 := fun s => by ring
  simp_rw [this]
  rw [integral_const_mul, integral_cos_sq_phase n hn φ]
  ring

end AVenhance.Infra.FullTheorem.NoSelectionInputs
