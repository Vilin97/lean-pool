/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol

/-! Pointwise regularity consequences of the classical-solution
definition on the open positive-time region. -/

@[expose] public section

open Homogenization Filter
open scoped ContDiff Topology

namespace AVenhance.Infra.Section5

open AVenhance

/-- A classical solution is jointly smooth at every positive-time
space-time point. The boundary value at time zero is not used. -/
theorem classicalSol_contDiffAt_of_pos
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F θ₀ θ)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    ContDiffAt ℝ ∞ (Function.uncurry θ) (t, x) := by
  have hprod : Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) ∈ 𝓝 (t, x) :=
    prod_mem_nhds (Ioi_mem_nhds ht)
      (Filter.univ_mem : (Set.univ : Set (Vec 2)) ∈ 𝓝 x)
  have hmem : Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) ∈ 𝓝 (t, x) :=
    Filter.mem_of_superset hprod (by
      rintro ⟨s, y⟩ ⟨hs, hy⟩
      exact ⟨Set.mem_Ici.mpr (le_of_lt hs), Set.mem_univ y⟩)
  exact hsol.1.contDiffAt hmem

/-- The spacetime Fréchet derivative of a classical solution exists at
each point with positive time. -/
theorem classicalSol_hasFDerivAt_of_pos
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F θ₀ θ)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    HasFDerivAt (Function.uncurry θ)
      (fderiv ℝ (Function.uncurry θ) (t, x)) (t, x) := by
  exact ((classicalSol_contDiffAt_of_pos hsol ht x).differentiableAt
    (by norm_num)).hasFDerivAt

/-- At each nonnegative time, the spatial slice of a classical solution
is globally smooth. -/
theorem classicalSol_space_contDiff_of_nonneg
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F θ₀ θ)
    {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (θ t) := by
  let embed : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
  have hembed : ContDiff ℝ ∞ embed := by fun_prop
  have hmaps : Set.MapsTo embed Set.univ
      (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) := by
    intro y hy
    exact ⟨Set.mem_Ici.mpr ht, Set.mem_univ y⟩
  have hcomp : ContDiffOn ℝ ∞ (Function.uncurry θ ∘ embed) Set.univ :=
    hsol.1.comp hembed.contDiffOn hmaps
  have hslice : (Function.uncurry θ ∘ embed) = θ t := by
    funext y
    rfl
  rw [hslice] at hcomp
  exact contDiffOn_univ.mp hcomp

/-- The spatial gradient of a classical solution is itself smooth on
every nonnegative time slice. -/
theorem classicalSol_spaceGrad_contDiff_of_nonneg
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F θ₀ θ)
    {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (spaceGrad (θ t)) := by
  have hslice := classicalSol_space_contDiff_of_nonneg hsol ht
  have hderiv : ContDiff ℝ ∞ (fderiv ℝ (θ t)) :=
    hslice.fderiv_right (by simp)
  change ContDiff ℝ ∞ (fun x i => fderiv ℝ (θ t) x (basisVec i))
  apply contDiff_pi.2
  intro i
  exact hderiv.clm_apply contDiff_const

/-- The spatial slice of a classical solution is Fréchet
differentiable at every positive-time point. -/
theorem classicalSol_space_hasFDerivAt_of_pos
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F θ₀ θ)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    HasFDerivAt (θ t)
      ((fderiv ℝ (Function.uncurry θ) (t, x)).comp
        ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2)))) x := by
  have hspace : HasFDerivAt (fun y : Vec 2 => (t, y))
      ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))) x := by
    exact (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have h := (classicalSol_hasFDerivAt_of_pos hsol ht x).comp x hspace
  simpa [Function.uncurry, Function.comp_def] using h

/-- Along any spatial curve, a positive-time slice gradient agrees locally
with the spatial restriction of the spacetime derivative. -/
theorem classicalSol_spaceGrad_eq_jointFDeriv_eventually
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F θ₀ θ)
    {t : ℝ} (ht : 0 < t) (γ : ℝ → Vec 2) (i : Fin 2) :
    (fun r => spaceGrad (θ r) (γ r) i) =ᶠ[𝓝 t]
      fun r => fderiv ℝ (Function.uncurry θ) (r, γ r) (0, basisVec i) := by
  filter_upwards [Ioi_mem_nhds ht] with r hr
  have hslice := classicalSol_space_hasFDerivAt_of_pos hsol hr (γ r)
  have hderiv := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) hslice.fderiv
  change fderiv ℝ (θ r) (γ r) (basisVec i) = _
  rw [hderiv]
  simp

end AVenhance.Infra.Section5
