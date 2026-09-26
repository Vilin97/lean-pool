/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LeviConvexity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LeviForm.Holomorphic

/-!
# Invariance of the Levi condition under holomorphic maps

A local defining function pulls back along a holomorphic map with surjective derivative to a
local defining function of the preimage. Complex tangent vectors correspond under the
derivative, and the Levi form transforms by the chain rule of `LeviForm.Holomorphic`.
Consequently, for a holomorphic map with invertible derivative at `p`, the Levi condition for a
defining function at `Φ p` is equivalent to the Levi condition for its pullback at `p`.

References: [Fritzsche–Grauert][FritzscheGrauert2002] (2002), Chapter II, Section 4, Remark
after the definition of Levi convexity; [Range][Range1986] (1986), Chapter II, Lemma 2.12.

## Main results

* `leviCondition_comp_iff`: **Invariance of the Levi condition.** For a holomorphic map with
  invertible derivative at `p`, the Levi condition for a defining function at `Φ p` holds exactly
  when it holds for the pullback at `p`.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
-/

public noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The derivative of a composition with a holomorphic map, over the reals. -/
theorem fderiv_comp_analytic {ρ : F → ℝ} {Φ : E → F} {p : E} (hΦ : AnalyticAt ℂ Φ p)
    (hρ : DifferentiableAt ℝ ρ (Φ p)) :
    fderiv ℝ (ρ ∘ Φ) p = (fderiv ℝ ρ (Φ p)).comp ((fderiv ℂ Φ p).restrictScalars ℝ) :=
  (hρ.hasFDerivAt.comp p (hΦ.differentiableAt.hasFDerivAt.restrictScalars ℝ)).fderiv

/-- Complex tangent vectors of a pullback correspond to complex tangent vectors of the image under
the derivative. -/
theorem isComplexTangent_comp_iff {ρ : F → ℝ} {Φ : E → F} {p : E} (hΦ : AnalyticAt ℂ Φ p)
    (hρ : DifferentiableAt ℝ ρ (Φ p)) (w : E) :
    IsComplexTangent (ρ ∘ Φ) p w ↔ IsComplexTangent ρ (Φ p) (fderiv ℂ Φ p w) := by
  simp only [IsComplexTangent, fderiv_comp_analytic hΦ hρ, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul]

variable {U : Set F} {q : F} {ρ : F → ℝ} {V : Set F}

/-- A local defining function pulls back along a holomorphic map with surjective derivative to a
local defining function of the preimage. -/
theorem IsLocalDefiningFunction.comp_analytic (h : IsLocalDefiningFunction U q ρ V)
    {Φ : E → F} {W : Set E} (hW : IsOpen W) {p : E} (hp : p ∈ W) (hΦ : AnalyticOnNhd ℂ Φ W)
    (hΦp : Φ p = q) (hsurj : Function.Surjective (fderiv ℂ Φ p)) :
    IsLocalDefiningFunction (Φ ⁻¹' U) p (ρ ∘ Φ) (W ∩ Φ ⁻¹' V) := by
  have hρd : DifferentiableAt ℝ ρ (Φ p) := by
    rw [hΦp]
    exact (h.contDiffOn.contDiffAt (h.isOpen.mem_nhds h.mem)).differentiableAt (by norm_num)
  refine ⟨hΦ.continuousOn.isOpen_inter_preimage hW h.isOpen, ⟨hp, by simp [hΦp, h.mem]⟩, ?_,
    by simp [Function.comp, hΦp, h.eq_zero], ?_, ?_⟩
  · exact h.contDiffOn.comp
      (((hΦ.contDiffOn hW.uniqueDiffOn (n := 2)).restrict_scalars ℝ).mono inter_subset_left)
      fun z hz => hz.2
  · intro hzero
    apply h.fderiv_ne
    ext v
    obtain ⟨u, hu⟩ := hsurj v
    have := congrArg (fun L : E →L[ℝ] ℝ => L u) hzero
    simp only [fderiv_comp_analytic (hΦ p hp) hρd, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', zero_apply] at this
    rw [hΦp, hu] at this
    simpa using this
  · ext z
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, Function.comp]
    constructor
    · rintro ⟨hzU, hzW, hzV⟩
      exact ⟨h.neg_of_mem hzV hzU, hzW, hzV⟩
    · rintro ⟨hneg, hzW, hzV⟩
      exact ⟨h.mem_of_neg hzV hneg, hzW, hzV⟩

/-- **Invariance of the Levi condition.** For a holomorphic map with invertible derivative
at `p`, the Levi condition for a defining function at `Φ p` holds exactly when it holds for
the pullback at `p`. -/
theorem leviCondition_comp_iff [CompleteSpace F] (h : IsLocalDefiningFunction U q ρ V)
    {Φ : E → F} {p : E}
    (hΦ : AnalyticAt ℂ Φ p) (hΦp : Φ p = q) (L : E ≃L[ℂ] F)
    (hL : HasFDerivAt Φ (L : E →L[ℂ] F) p) :
    (∀ w, IsComplexTangent (ρ ∘ Φ) p w → 0 ≤ leviForm (ρ ∘ Φ) p w) ↔
      (∀ v, IsComplexTangent ρ q v → 0 ≤ leviForm ρ q v) := by
  subst hΦp
  have hρ2 : ContDiffAt ℝ 2 ρ (Φ p) := h.contDiffOn.contDiffAt (h.isOpen.mem_nhds h.mem)
  have hfd : fderiv ℂ Φ p = L := hL.fderiv
  have hlev : ∀ w, leviForm (ρ ∘ Φ) p w = leviForm ρ (Φ p) (L w) := fun w => by
    rw [leviForm_comp_analytic hρ2 hΦ, hfd]
    rfl
  have htan : ∀ w, IsComplexTangent (ρ ∘ Φ) p w ↔ IsComplexTangent ρ (Φ p) (L w) := fun w => by
    rw [isComplexTangent_comp_iff hΦ (hρ2.differentiableAt (by norm_num)), hfd]
    rfl
  constructor
  · intro hcond v hv
    have := hcond (L.symm v) ((htan _).mpr (by simpa using hv))
    rwa [hlev, L.apply_symm_apply] at this
  · intro hcond w hw
    rw [hlev]
    exact hcond _ ((htan w).mp hw)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
