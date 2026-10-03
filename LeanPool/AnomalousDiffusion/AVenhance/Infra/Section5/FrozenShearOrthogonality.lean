/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ChiMKCorrector
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenFlowRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ShearOrthogonality

/-! The corrector and stream profile use the same scalar shear
coordinate after composition with the inverse flow. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The coordinate vector with value `r` in coordinate `c` and zero in the
other coordinate. -/
def FrozenShearOrthogonality.coordinateVector (c : Fin 2) (r : ℝ) : Vec 2 :=
  fun j => if j = c then r else 0

theorem FrozenShearOrthogonality.coordinateVector_contDiff (c : Fin 2) :
    ContDiff ℝ ∞ (FrozenShearOrthogonality.coordinateVector c) := by
  apply contDiff_pi.2
  intro j
  by_cases h : j = c <;> simp only [coordinateVector, ↓reduceIte, coordinateVector, h,
      ↓reduceIte] <;> fun_prop

theorem FrozenShearOrthogonality.psi_spatial_contDiff (m : ℕ) (k : ℤ) :
    ContDiff ℝ ∞ (psi β I.Λ m k) := by
  unfold psi
  have hprofile : ContDiff ℝ ∞
      (fun x : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • x)) := by
    unfold psi0
    split_ifs <;> fun_prop
  exact contDiff_const.mul hprofile

/-- Orthogonality `e.ortho.tilde` for every component of the twisted
corrector, with the exact common coordinate selected by `k mod 4`. -/
theorem frozen_shear_orthogonality_component
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) (i : Fin 2) :
    vecDot
        (spaceGrad (fun y => psi β I.Λ m k
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) x)
        (sigmaMat.mulVec (spaceGrad
          (fun y => I.chiTilde hΦ m κ k t y i) x)) = 0 := by
  let c : Fin 2 := if k % 4 = 1 then 0 else 1
  let η : Vec 2 → ℝ := fun y =>
    I.xFlowInv hΦ m (lIdx β I.Λ m k) t y c
  let f : ℝ → ℝ := fun r => psi β I.Λ m k (FrozenShearOrthogonality.coordinateVector c r)
  let g : ℝ → ℝ := fun r => I.chiMK κ m k t (FrozenShearOrthogonality.coordinateVector c r) i
  have hpsi : (fun y => psi β I.Λ m k
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) = fun y => f (η y) := by
    funext y
    by_cases h1 : k % 4 = 1
    · simp [f, η, c, FrozenShearOrthogonality.coordinateVector, psi, psi0, h1]
    · by_cases h3 : k % 4 = 3
      · simp [f, η, c, FrozenShearOrthogonality.coordinateVector, psi, psi0, h3]
      · simp [f, η, c, psi, psi0, h1, h3]
  have hchi : (fun y => I.chiTilde hΦ m κ k t y i) = fun y => g (η y) := by
    funext y
    by_cases h1 : k % 4 = 1
    · fin_cases i <;>
        simp [g, η, c, FrozenShearOrthogonality.coordinateVector, Ingredients.chiTilde,
          Ingredients.chiMK, uShear, h1]
    · by_cases h3 : k % 4 = 3
      · fin_cases i <;>
          simp [g, η, c, FrozenShearOrthogonality.coordinateVector, Ingredients.chiTilde,
            Ingredients.chiMK, uShear, h3]
      · fin_cases i <;>
          simp [g, η, c, Ingredients.chiTilde,
            Ingredients.chiMK, uShear, h1, h3]
  have hInv := (xFlowInv_spatial_contDiff_two I hΦ m
    (lIdx β I.Λ m k) t).differentiable (by norm_num) x
  let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj c
  have hη : HasFDerivAt η (P.comp (fderiv ℝ
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x)) x := by
    have h := P.hasFDerivAt.comp x hInv.hasFDerivAt
    simpa [η, P, Function.comp_def] using h
  have hf : HasDerivAt f (deriv f (η x)) (η x) := by
    have hcomp := (FrozenShearOrthogonality.psi_spatial_contDiff I m k).comp
      (FrozenShearOrthogonality.coordinateVector_contDiff c)
    exact (hcomp.differentiable (by norm_num) (η x)).hasDerivAt
  have hg : HasDerivAt g (deriv g (η x)) (η x) := by
    have hchiSpace : ContDiff ℝ 2
        (fun z => I.chiMK κ m k t z i) := by
      let E : Vec 2 → ℝ × Vec 2 := fun z => (t, z)
      have hE : ContDiff ℝ 2 E := by fun_prop
      have h := (Infra.Section3.chiMK_component_contDiff_two
        I (m := m) κ k i).comp hE
      simpa [E, Function.comp_def] using h
    have hcomp := hchiSpace.comp
      ((FrozenShearOrthogonality.coordinateVector_contDiff c).of_le (by norm_num))
    exact (hcomp.differentiable (by norm_num) (η x)).hasDerivAt
  rw [hpsi, hchi]
  exact composed_gradients_sigma_orthogonal hη hf hg

end AVenhance.Infra.Section5
