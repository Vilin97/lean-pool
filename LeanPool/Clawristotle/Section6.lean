/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.VMLStructures
import LeanPool.Clawristotle.FlatTorus3Lemmas

/-!
# Bulk Velocity Vanishes (Section 6)

Proves that the drift velocity u_inf = 0 using Ampere's law, Stokes' theorem
on the torus, and positivity of the charge density.
-/

open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Section 6: Bulk Velocity (Section 6 of tex)
-- Reference: Lemmas 18-19
-- ============================================================================

/-- Helper: dotProduct with scalar multiplication -/
lemma dotProduct_smul_self (c : ℝ) (v : Fin 3 → ℝ) :
    dotProduct v (c • v) = c * normSq v := by
  unfold normSq dotProduct
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

/-- Lemma 19: The drift velocity vanishes: u∞ = 0.
    Reference: lem:u_zero

    Proof: From Ampère (∇×B = J = ρ u∞) and ∫ u∞ · ∇×B dx = 0 (Stokes),
    we get |u∞|² ∫ ρ dx = 0. Since ∫ ρ > 0, u∞ = 0. -/
theorem bulk_velocity_zero {X : Type*} [FlatTorus3 X] (ss : VMLSteadyState X) :
    ss.b₀ = 0 := by
  -- Step 1: ∫ b₀ · curlX B dx = 0 (by hCurlIntZero)
  have h1 : FlatTorus3.spatialIntegral (fun x => dotProduct ss.b₀ (FlatTorus3.curlX ss.B x)) = 0 :=
    FlatTorus3.hCurlIntZero ss.B ss.b₀ (fun i => (ss.hDiff_B i).of_le (by decide))
  -- Step 2: b₀ · curlX B x = b₀ · (ρ x • b₀) = ρ x * |b₀|²
  have h2 : ∀ x, dotProduct ss.b₀ (FlatTorus3.curlX ss.B x) = ss.ρ x * normSq ss.b₀ := by
    intro x
    rw [ss.hAmpere, ss.hJ_def]
    exact dotProduct_smul_self (ss.ρ x) ss.b₀
  -- Step 3: ∫ ρ * |b₀|² dx = |b₀|² * ∫ ρ = 0
  have h3 : FlatTorus3.spatialIntegral (fun x => ss.ρ x * normSq ss.b₀) = 0 := by
    rwa [show (fun x => ss.ρ x * normSq ss.b₀) =
      (fun x => dotProduct ss.b₀ (FlatTorus3.curlX ss.B x)) from funext (fun x => (h2 x).symm)]
  have h4 : FlatTorus3.spatialIntegral ss.ρ * normSq ss.b₀ = 0 := by
    rwa [← FlatTorus3.hSpatialMul]
  -- Step 4: Since ∫ ρ > 0, we get |b₀|² = 0, hence b₀ = 0
  have h5 : 0 < FlatTorus3.spatialIntegral ss.ρ := FlatTorus3.hSpatialPos ss.ρ ss.hρ_cont ss.hρ_pos
  exact normSq_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left (ne_of_gt h5))

end VML
