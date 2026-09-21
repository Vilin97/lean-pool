/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # The radial extension of a map between unit spheres -/

@[expose] public noncomputable section
open Set Metric
namespace LichnerowiczObata

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Extend a sphere map by preserving the radial coordinate, sending zero
to zero. No regularity at the origin is assumed in this definition. -/
def sphereRadialExtension (A : sphere (0 : P) 1 → sphere (0 : V) 1) (x : P) : V := by
  classical
  exact if hx : x = 0 then 0 else
    ‖x‖ • (A ((homeomorphUnitSphereProd P ⟨x, by simpa using hx⟩).1) : V)

@[simp] theorem sphereRadialExtension_zero (A : sphere (0 : P) 1 → sphere (0 : V) 1) :
    sphereRadialExtension A 0 = 0 := by simp [sphereRadialExtension]

@[simp] theorem norm_sphereRadialExtension (A : sphere (0 : P) 1 → sphere (0 : V) 1)
    (x : P) : ‖sphereRadialExtension A x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [sphereRadialExtension, hx, norm_smul, norm_eq_of_mem_sphere]

/-- Positive rays retain their radial parameter exactly. -/
theorem sphereRadialExtension_smul (A : sphere (0 : P) 1 → sphere (0 : V) 1)
    (u : sphere (0 : P) 1) {r : ℝ} (hr : 0 < r) :
    sphereRadialExtension A (r • (u : P)) = r • (A u : V) := by
  have hne : r • (u : P) ≠ 0 := smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u)
  have hn : ‖r • (u : P)‖ = r := by
    simp [norm_smul, norm_eq_of_mem_sphere, abs_of_pos hr]
  have hdir : (homeomorphUnitSphereProd P ⟨r • (u : P), by simpa using hne⟩).1 = u := by
    apply Subtype.ext
    simp [homeomorphUnitSphereProd_apply_fst_coe, hn, smul_smul, hr.ne']
  simp only [sphereRadialExtension, dif_neg hne, hn, hdir]

@[simp] theorem sphereRadialExtension_sphere (A : sphere (0 : P) 1 → sphere (0 : V) 1)
    (u : sphere (0 : P) 1) : sphereRadialExtension A (u : P) = (A u : V) := by
  simpa only [one_smul] using sphereRadialExtension_smul A u (r := 1) one_pos

theorem sphereRadialExtension_leftInverse
    (A : sphere (0 : P) 1 ≃ sphere (0 : V) 1) :
    Function.LeftInverse (sphereRadialExtension A.symm) (sphereRadialExtension A) := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · let q := homeomorphUnitSphereProd P ⟨x, by simpa using hx⟩
    have hr : 0 < (q.2 : ℝ) := q.2.property
    have hq : (q.2 : ℝ) • (q.1 : P) = x := by
      exact congrArg Subtype.val ((homeomorphUnitSphereProd P).symm_apply_apply
        ⟨x, by simpa using hx⟩)
    rw [← hq, sphereRadialExtension_smul A q.1 hr,
      sphereRadialExtension_smul A.symm (A q.1) hr, A.symm_apply_apply]

/-- A sphere equivalence induces an equivalence of the whole vector spaces. -/
def sphereRadialEquiv (A : sphere (0 : P) 1 ≃ sphere (0 : V) 1) : P ≃ V where
  toFun := sphereRadialExtension A
  invFun := sphereRadialExtension A.symm
  left_inv := sphereRadialExtension_leftInverse A
  right_inv := sphereRadialExtension_leftInverse A.symm

end LichnerowiczObata
