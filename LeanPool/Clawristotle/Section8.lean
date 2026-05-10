/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.VMLStructures
import LeanPool.Clawristotle.Section6

/-!
set_option linter.style.longLine false

# Magnetic Field and Final Assembly (Section 8)

Proves the magnetic field is spatially constant (from curl B = 0 and div B = 0),
derives E = 0 from the Poisson-Boltzmann equation, and assembles the abstract
`ConcreteTheorem42` combining all sections.
-/

open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Section 5e: Magnetic Field and Compatibility (Section 8 of tex)
-- Reference: Lemma 23
-- ============================================================================

/-- Lemma 22: Magnetic field is spatially constant.
    Reference: lem:B_constant

    With u∞ = 0, J = 0 so ∇×B = 0. Combined with ∇·B = 0,
    each Bᵢ is harmonic on T³, hence constant. -/
theorem magnetic_field_constant {X : Type*} [FlatTorus3 X] (ss : VMLSteadyState X) :
    ∃ B₀ : Fin 3 → ℝ, ∀ x, ss.B x = B₀ := by
  have hb0 := bulk_velocity_zero ss
  -- Step 1: J = 0
  have hJ_zero : ∀ x, ss.J x = 0 := by
    intro x; rw [ss.hJ_def, hb0, smul_zero]
  -- Step 2: curl B = 0
  have hcurl_zero : ∀ x, FlatTorus3.curlX ss.B x = 0 := by
    intro x
    rw [ss.hAmpere]
    exact hJ_zero x
  -- Step 3: Each component is harmonic
  -- Derive C² condition for B from hDiff_grad ⊤ + C¹ differentiability of B components
  have hDiff_B_C2 : ∀ i j, FlatTorus3.IsSpatiallySmooth 1 (fun x =>
      FlatTorus3.gradX (fun y => ss.B y i) x j) :=
    fun i j => FlatTorus3.hDiff_grad 1 (fun y => ss.B y i) j (ss.hDiff_B i)
  have hBi_harmonic :=
    FlatTorus3.hCurlZeroDivZeroHarmonic ss.B
      (fun i => FlatTorus3.IsSpatiallySmooth.of_le
        (ss.hDiff_B i) (by decide))
      (fun i j => FlatTorus3.IsSpatiallySmooth.of_le
        (hDiff_B_C2 i j) (by decide))
      hcurl_zero ss.hDivB
  -- Step 4: Each component is constant
  have hBi_const : ∀ i, ∀ x y, ss.B x i = ss.B y i := by
    intro i
    exact FlatTorus3.hHarmonic_const (fun y => ss.B y i)
      (FlatTorus3.IsSpatiallySmooth.of_le
        (ss.hDiff_B i) (by decide))
      (hBi_harmonic i)
  -- Extract the constant value from x₀
  exact ⟨fun i => ss.B ss.x₀ i, fun x => funext (fun i => hBi_const i x ss.x₀)⟩

end VML
