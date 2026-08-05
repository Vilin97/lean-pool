/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Core
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Topology of the collision-free parameter domain

A shear `u = x + μ` makes the two moving primaries into the fixed punctures `(0, 0)` and
`(1, 0)`.  In these coordinates the parameter domain is a product of an open mass interval, a
twice-punctured plane, and the unrestricted momentum plane.  This proves that the full domain is
path-connected whenever the mass interval is nonempty.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody Set

/-- A two-dimensional real coordinate plane. -/
abbrev Plane := Fin 2 → ℝ

/-- Coordinates consisting of mass, the sheared position `(x + μ, y)`, and momentum. -/
def parameterCoordinateEquiv : (ℝ × PhaseSpace) ≃ ((ℝ × Plane) × Plane) where
  toFun z := ((z.1, ![z.2 0 + z.1, z.2 1]), ![z.2 2, z.2 3])
  invFun w := (w.1.1,
    ![w.1.2 0 - w.1.1, w.1.2 1, w.2 0, w.2 1])
  left_inv z := by
    rcases z with ⟨mass, state⟩
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp
  right_inv w := by
    rcases w with ⟨⟨mass, position⟩, momentum⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        fin_cases i <;> simp
    · funext i
      fin_cases i <;> simp

/-- The shear and coordinate splitting as a homeomorphism. -/
noncomputable def parameterCoordinateHomeomorph :
    (ℝ × PhaseSpace) ≃ₜ ((ℝ × Plane) × Plane) :=
  Homeomorph.mk parameterCoordinateEquiv (by fun_prop) (by fun_prop)

/-- The two primary positions after straightening the moving coordinates. -/
def primaryConfigurations : Set Plane := {![0, 0], ![1, 0]}

/-- Product form of the mass-restricted, collision-free domain. -/
def straightenedParameterDomain (δ : ℝ) : Set ((ℝ × Plane) × Plane) :=
  (Set.Ioo (-δ) δ ×ˢ primaryConfigurationsᶜ) ×ˢ Set.univ

/-- The original parameter domain is the preimage of its product form under the shear. -/
lemma parameterCoordinateHomeomorph_preimage_straightenedParameterDomain (δ : ℝ) :
    parameterCoordinateHomeomorph ⁻¹' straightenedParameterDomain δ = parameterDomain δ := by
  ext z
  dsimp [parameterCoordinateHomeomorph, parameterCoordinateEquiv, straightenedParameterDomain,
    parameterDomain, collisionFree]
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioo, Set.mem_compl_iff,
    Set.mem_univ, and_true]
  change ((-δ < z.1 ∧ z.1 < δ) ∧
    (![z.2 0 + z.1, z.2 1] : Plane) ∉ primaryConfigurations) ↔
      |z.1| < δ ∧ firstPrimaryDistanceSq z.1 z.2 ≠ 0 ∧
        secondPrimaryDistanceSq z.1 z.2 ≠ 0
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hposition⟩
    constructor
    · rw [abs_lt]
      exact ⟨by linarith, hupper⟩
    · constructor
      · intro hfirst
        apply hposition
        right
        funext i
        fin_cases i
        · dsimp [firstPrimaryDistanceSq] at hfirst ⊢
          nlinarith [sq_nonneg (z.2 1)]
        · dsimp [firstPrimaryDistanceSq] at hfirst ⊢
          nlinarith [sq_nonneg (z.2 0 - 1 + z.1)]
      · intro hsecond
        apply hposition
        left
        funext i
        fin_cases i
        · dsimp [secondPrimaryDistanceSq] at hsecond ⊢
          nlinarith [sq_nonneg (z.2 1)]
        · dsimp [secondPrimaryDistanceSq] at hsecond ⊢
          nlinarith [sq_nonneg (z.2 0 + z.1)]
  · rintro ⟨hmass, hfirst, hsecond⟩
    rw [abs_lt] at hmass
    constructor
    · exact hmass
    · intro hposition
      rcases hposition with hzero | hone
      · apply hsecond
        have hx : z.2 0 + z.1 = 0 := by
          have := congrFun hzero 0
          simpa using this
        have hy : z.2 1 = 0 := by
          have := congrFun hzero 1
          simpa using this
        simp [secondPrimaryDistanceSq, hx, hy]
      · apply hfirst
        have hx : z.2 0 + z.1 = 1 := by
          have := congrFun hone 0
          simpa using this
        have hy : z.2 1 = 0 := by
          have := congrFun hone 1
          simpa using this
        simp [firstPrimaryDistanceSq, hy]
        nlinarith

/-- The plane with the two primary positions removed is path-connected. -/
lemma isPathConnected_primaryConfigurations_compl :
    IsPathConnected primaryConfigurationsᶜ := by
  apply Set.Countable.isPathConnected_compl_of_one_lt_rank
  · rw [← Module.finrank_eq_rank]
    norm_num [Module.finrank_fin_fun]
  · have hfinite : Set.Finite primaryConfigurations := by
      simp [primaryConfigurations]
    exact hfinite.countable

/-- The straightened parameter domain is path-connected for a positive mass radius. -/
lemma isPathConnected_straightenedParameterDomain {δ : ℝ} (hδ : 0 < δ) :
    IsPathConnected (straightenedParameterDomain δ) := by
  apply IsPathConnected.prod
  · apply IsPathConnected.prod
    · exact (convex_Ioo (-δ) δ).isPathConnected ⟨0, by simpa using hδ⟩
    · exact isPathConnected_primaryConfigurations_compl
  · exact isPathConnected_univ

/-- The collision-free parameter domain in the challenge is preconnected. -/
theorem isPreconnected_parameterDomain {δ : ℝ} (hδ : 0 < δ) :
    IsPreconnected (parameterDomain δ) := by
  rw [← parameterCoordinateHomeomorph_preimage_straightenedParameterDomain δ]
  exact (parameterCoordinateHomeomorph.isPathConnected_preimage.mpr
    (isPathConnected_straightenedParameterDomain hδ)).isConnected.isPreconnected

end LeanPool.PoincareThreeBody
