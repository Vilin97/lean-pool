/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum

/-! # Tensor-indexed pressure estimates

The pressure is identified with the sum of nine separately indexed operator
outputs. Component estimates then give an extended-valued norm bound and the
real pressure norm bound. Compact support is not needed for this consumption
step once the component estimates are supplied.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Endgame

/-- Component bounds and the actual tensor-sum identification give pressure
membership and an extended-valued norm estimate at exponent `3/2`. -/
theorem pressure_memLp_and_eLpNorm_le_of_tensor_bounds
    (T : Fin 3 → Fin 3 → (Vec3 → ℝ) → Vec3 → ℝ)
    (G : Fin 3 → Fin 3 → Vec3 → ℝ) {p₁ : Vec3 → ℝ} {C : ℝ}
    (hTG : ∀ i j, MemLp (T i j (G i j)) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hbound : ∀ i j, eLpNorm (T i j (G i j)) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      ENNReal.ofReal C * eLpNorm (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hident : p₁ =ᵐ[volume] fun x => ∑ i, ∑ j, T i j (G i j) x) :
    MemLp p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      eLpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ ENNReal.ofReal C *
        ∑ i, ∑ j, eLpNorm (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  have hm (i : Fin 3) := memLp_finsetSum Finset.univ (fun j _ => hTG i j)
  have hsum := memLp_finsetSum Finset.univ (fun i _ => hm i)
  refine ⟨(memLp_congr_ae hident).mpr hsum, ?_⟩
  rw [eLpNorm_congr_ae hident]
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ) := by norm_num
  calc
    _ ≤ ∑ i, eLpNorm (fun x => ∑ j, T i j (G i j) x)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
      change eLpNorm (∑ i, fun x => ∑ j, T i j (G i j) x)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ _
      exact eLpNorm_sum_le hp
    _ ≤ ∑ i, ∑ j, eLpNorm (T i j (G i j)) (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
      apply Finset.sum_le_sum
      intro i _
      change eLpNorm (∑ j, T i j (G i j)) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ _
      exact eLpNorm_sum_le hp
    _ ≤ ∑ i, ∑ j, ENNReal.ofReal C *
        eLpNorm (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hbound i j
    _ = _ := by simp only [Finset.mul_sum]

/-- A summed tensor-input norm bound yields the literal real pressure norm
estimate, retaining each operator and source index. -/
theorem pressure_lpNorm_le_of_tensor_bounds
    (T : Fin 3 → Fin 3 → (Vec3 → ℝ) → Vec3 → ℝ)
    (G : Fin 3 → Fin 3 → Vec3 → ℝ) {p₁ : Vec3 → ℝ} {C C₁₁ E : ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hTG : ∀ i j, MemLp (T i j (G i j)) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hbound : ∀ i j, eLpNorm (T i j (G i j)) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      ENNReal.ofReal C * eLpNorm (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hident : p₁ =ᵐ[volume] fun x => ∑ i, ∑ j, T i j (G i j) x)
    (hsource : (∑ i, ∑ j, lpNorm (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume) ≤
      E ^ (2 / 3 : ℝ))
    (hC : 0 ≤ C) (hconst : C ≤ C₁₁) (hE : 0 ≤ E) :
    lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ C₁₁ * E ^ (2 / 3 : ℝ) := by
  have hsum := (pressure_memLp_and_eLpNorm_le_of_tensor_bounds T G hTG hbound hident).2
  have hfinite : (∑ i, ∑ j,
      eLpNorm (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ => (hG i j).eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
    ENNReal.toReal_sum (fun i _ => ENNReal.sum_ne_top.mpr
      (fun j _ => (hG i j).eLpNorm_ne_top))] at hreal
  simp_rw [ENNReal.toReal_sum (fun j _ => (hG _ j).eLpNorm_ne_top)] at hreal
  exact hreal.trans ((mul_le_mul_of_nonneg_left hsource hC).trans
    (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hE _)))

end CKN.Core.Endgame
