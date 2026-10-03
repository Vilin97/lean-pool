/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ClassicalRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad

/-!
# Joint regularity of a classical solution up to time zero

A classical solution is smooth on the closed half-space `t ≥ 0`. Its space-time derivative
(taken inside the half-space) is continuous up to `t = 0`, and its spatial gradient and time
derivative are the corresponding components of that joint derivative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

/-- The closed half-space `t ≥ 0`. -/
def classicalHalfSpace : Set (ℝ × Vec 2) := Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))

theorem classicalHalfSpace_uniqueDiffOn : UniqueDiffOn ℝ classicalHalfSpace :=
  (uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ

/-- The joint derivative of a classical solution inside the closed half-space. -/
def classicalJointFDeriv (θ : ℝ → Vec 2 → ℝ) : ℝ × Vec 2 → (ℝ × Vec 2) →L[ℝ] ℝ :=
  fderivWithin ℝ (Function.uncurry θ) classicalHalfSpace

theorem classicalJointFDeriv_continuousOn {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) classicalHalfSpace) :
    ContinuousOn (classicalJointFDeriv θ) classicalHalfSpace :=
  hθ.continuousOn_fderivWithin classicalHalfSpace_uniqueDiffOn (by simp)

theorem classicalHasFDerivWithinAt {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) classicalHalfSpace)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec 2) :
    HasFDerivWithinAt (Function.uncurry θ) (classicalJointFDeriv θ (t, x))
      classicalHalfSpace (t, x) :=
  (hθ.differentiableOn (by simp) (t, x) ⟨ht, mem_univ x⟩).hasFDerivWithinAt

/-- The spatial gradient of a classical solution is a component of the joint derivative. -/
theorem classical_spaceGrad_eq_joint {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) classicalHalfSpace)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec 2) (i : Fin 2) :
    AVenhance.spaceGrad (θ t) x i = classicalJointFDeriv θ (t, x) (0, basisVec i) := by
  have hf := classicalHasFDerivWithinAt hθ ht x
  have hline : HasFDerivAt (fun y : Vec 2 => (t, y))
      (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) x := hasFDerivAt_prodMk_right t x
  have hmaps : MapsTo (fun y : Vec 2 => (t, y)) (Set.univ : Set (Vec 2)) classicalHalfSpace :=
    fun y _ => ⟨ht, mem_univ y⟩
  have hcomp := hf.comp x hline.hasFDerivWithinAt hmaps
  rw [hasFDerivWithinAt_univ] at hcomp
  change fderiv ℝ (θ t) x (basisVec i) = _
  have : θ t = Function.uncurry θ ∘ fun y : Vec 2 => (t, y) := rfl
  rw [this, hcomp.fderiv]
  simp [ContinuousLinearMap.inr]

/-- The time derivative of a classical solution is a component of the joint derivative. -/
theorem classical_deriv_eq_joint {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) classicalHalfSpace)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    HasDerivAt (fun s => θ s x) (classicalJointFDeriv θ (t, x) (1, 0)) t := by
  have hmem : classicalHalfSpace ∈ 𝓝 (t, x) :=
    prod_mem_nhds (Ici_mem_nhds ht) Filter.univ_mem
  have hf : HasFDerivAt (Function.uncurry θ) (classicalJointFDeriv θ (t, x)) (t, x) :=
    (classicalHasFDerivWithinAt hθ ht.le x).hasFDerivAt hmem
  have hline : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Vec 2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact hf.comp_hasDerivAt t hline

end AVenhance.Infra.Section5.RelativeError

end
