/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Genuine time derivatives of the inverse deformation and its transported normal. -/

@[expose] public section


noncomputable section

namespace EulerDeformationTime

open Set ContinuousLinearMap EulerSmoothLimit

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instDeformationTimeInverse1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instDeformationTimeInverse2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

/-- Inverse unit, bundling `val`, `inv`, `val_inv`, `inv_val`. -/
def inverseUnit (F G : Space →L[ℝ] Space)
    (hFG : F.comp G = ContinuousLinearMap.id ℝ Space)
    (hGF : G.comp F = ContinuousLinearMap.id ℝ Space) : (Space →L[ℝ] Space)ˣ where
  val := F
  inv := G
  val_inv := hFG
  inv_val := hGF

theorem inverse_hasDerivWithinAt (s : Set ℝ) (t : ℝ) (ht : t ∈ s)
    (F G : ℝ → Space →L[ℝ] Space) (F₁ : Space →L[ℝ] Space)
    (hFG : ∀ r ∈ s, (F r).comp (G r) = ContinuousLinearMap.id ℝ Space)
    (hGF : ∀ r ∈ s, (G r).comp (F r) = ContinuousLinearMap.id ℝ Space)
    (hF : HasDerivWithinAt F F₁ s t) :
    HasDerivWithinAt G (-((G t).comp (F₁.comp (G t)))) s t := by
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ)
    (inverseUnit (F t) (G t) (hFG t ht) (hGF t ht))).comp_hasDerivWithinAt t hF
  change HasDerivWithinAt (fun r => Ring.inverse (F r)) (-((G t).comp (F₁.comp (G t)))) s t at h
  apply h.congr_of_mem _ ht
  intro r hr
  exact (Ring.inverse_unit (inverseUnit (F r) (G r) (hFG r hr) (hGF r hr))).symm

/-- F_t=MF implies (F⁻¹)_t=−F⁻¹M on the same closed time set. -/
theorem inverse_strain_hasDerivWithinAt (s : Set ℝ) (t : ℝ) (ht : t ∈ s)
    (F G : ℝ → Space →L[ℝ] Space) (M : Space →L[ℝ] Space)
    (hFG : ∀ r ∈ s, (F r).comp (G r) = ContinuousLinearMap.id ℝ Space)
    (hGF : ∀ r ∈ s, (G r).comp (F r) = ContinuousLinearMap.id ℝ Space)
    (hF : HasDerivWithinAt F (M.comp (F t)) s t) :
    HasDerivWithinAt G (-((G t).comp M)) s t := by
  have h := inverse_hasDerivWithinAt s t ht F G (M.comp (F t)) hFG hGF hF
  rwa [ContinuousLinearMap.comp_assoc M (F t) (G t), hFG t ht, ContinuousLinearMap.comp_id] at h

/-- Adjoint vector as an element of `(Space →L[ℝ] Space) →L[ℝ] Space`. -/
def adjointVector (m₀ : Space) : (Space →L[ℝ] Space) →L[ℝ] Space :=
  (ContinuousLinearMap.apply ℝ Space m₀).comp
    (ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
      : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space))

/-- The actual transported normal satisfies m_t=−M* m. -/
theorem normal_hasDerivWithinAt (s : Set ℝ) (t : ℝ) (ht : t ∈ s)
    (F G : ℝ → Space →L[ℝ] Space) (M : Space →L[ℝ] Space) (m₀ : Space)
    (hFG : ∀ r ∈ s, (F r).comp (G r) = ContinuousLinearMap.id ℝ Space)
    (hGF : ∀ r ∈ s, (G r).comp (F r) = ContinuousLinearMap.id ℝ Space)
    (hF : HasDerivWithinAt F (M.comp (F t)) s t) :
    HasDerivWithinAt (fun r => (G r).adjoint m₀) (-(M.adjoint ((G t).adjoint m₀))) s t := by
  have h := (adjointVector m₀).hasFDerivAt.comp_hasDerivWithinAt t
    (inverse_strain_hasDerivWithinAt s t ht F G M hFG hGF hF)
  convert h using 1 <;> try rfl
  change -(M.adjoint ((G t).adjoint m₀)) = (-((G t).comp M)).adjoint m₀
  simp only [map_neg, adjoint_comp, neg_apply, comp_apply]

end EulerDeformationTime
