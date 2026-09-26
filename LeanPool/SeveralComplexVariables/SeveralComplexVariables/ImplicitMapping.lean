/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Derivatives
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Topology.Graph

/-!
# Holomorphic implicit mappings

For `f : P × Q → R`, invertibility of the derivative in the `Q` variable gives a local
holomorphic solution `y = g x` of the level equation `f (x, y) = f (a, b)`. The conclusion uses
open product neighborhoods inside the original domain, includes uniqueness of every solution
there, and identifies the derivative of `g`.

The analytic theorem works in complex Banach spaces. The holomorphic version uses the project's
finite-dimensional holomorphic–analytic equivalence. No connectedness assumptions or positive
dimension restrictions are imposed; zero-dimensional parameter spaces include isolated
solutions. We reuse Mathlib's implicit function theorem at regularity `ω`.

Reference: [Range][Range1986] (1986), I §2.3, Theorem 2.4.

## Main results

* `exists_analytic_implicit_mapping`: **Analytic implicit mapping theorem.** Near a point where the
  partial derivative in the second variable is invertible, the level set is precisely an analytic
  graph.
* `exists_holomorphic_implicit_mapping`: **Holomorphic implicit mapping theorem.** The level set of
  a holomorphic map with invertible partial derivative is locally a unique holomorphic graph.

## References

* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
-/

public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SeveralComplexVariables

variable {P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [NormedAddCommGroup R] [NormedSpace ℂ R]

section Analytic

variable [CompleteSpace P] [CompleteSpace Q] [CompleteSpace R]

/-- **Analytic implicit mapping theorem.** Near a point where the partial derivative
in the second variable is invertible, the level set is precisely an analytic graph.
Both neighborhoods lie in the supplied domain, and the derivative is `-(D₂f)⁻¹ ∘ D₁f`. -/
theorem exists_analytic_implicit_mapping {D : Set (P × Q)} (hD : IsOpen D)
    {f : P × Q → R} {a : P} {b : Q} (hab : (a, b) ∈ D)
    (hf : AnalyticAt ℂ f (a, b))
    (hi : ((fderiv ℂ f (a, b)).comp (ContinuousLinearMap.inr ℂ P Q)).IsInvertible) :
    ∃ (U : Set P) (V : Set Q) (g : P → Q),
      IsOpen U ∧ a ∈ U ∧ IsOpen V ∧ b ∈ V ∧ U ×ˢ V ⊆ D ∧
      AnalyticOnNhd ℂ g U ∧ MapsTo g U V ∧ g a = b ∧
      HasFDerivAt g
        (-((fderiv ℂ f (a, b)).comp (ContinuousLinearMap.inr ℂ P Q)).inverse |>.comp
          ((fderiv ℂ f (a, b)).comp (ContinuousLinearMap.inl ℂ P Q))) a ∧
      ∀ x ∈ U, ∀ y ∈ V, f (x, y) = f (a, b) ↔ y = g x := by
  have hc : ContDiffAt ℂ ω f (a, b) := hf.contDiffAt
  let g := hc.implicitFunction (by simp) hi
  have hga : g a = b := hc.implicitFunction_apply_self (by simp) hi
  have hg : AnalyticAt ℂ g a := (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  have heq : ∀ᶠ p in 𝓝 (a, b), f p = f (a, b) ↔ g p.1 = p.2 :=
    hc.eventually_apply_eq_iff_implicitFunction (by simp) hi
  obtain ⟨U₀, V, hU₀, ha₀, hV, hb, hsub⟩ :=
    mem_nhds_prod_iff'.mp (inter_mem (hD.mem_nhds hab) heq)
  have hgV : g ⁻¹' V ∈ 𝓝 a :=
    hg.continuousAt.preimage_mem_nhds (hga.symm ▸ hV.mem_nhds hb)
  obtain ⟨U, hUU, hU, ha⟩ := mem_nhds_iff.mp
    (inter_mem (inter_mem (hU₀.mem_nhds ha₀) hg.eventually_analyticAt) hgV)
  refine ⟨U, V, g, hU, ha, hV, hb, ?_, ?_, ?_, hga, ?_, ?_⟩
  · exact fun p hp => (hsub ⟨(hUU hp.1).1.1, hp.2⟩).1
  · exact fun x hx => (hUU hx).1.2
  · exact fun x hx => (hUU hx).2
  · exact (hc.hasStrictFDerivAt_implicitFunction (by simp) hi).hasFDerivAt
  · intro x hx y hy
    exact (hsub ⟨(hUU hx).1.1, hy⟩).2.trans eq_comm

end Analytic

section Holomorphic

variable [FiniteDimensional ℂ P] [FiniteDimensional ℂ Q] [CompleteSpace R]

/-- **Holomorphic implicit mapping theorem.** The level set of a holomorphic map
with invertible partial derivative is locally a unique holomorphic graph.
The target may be a complex Banach space; invertibility supplies the required dimension match. -/
theorem exists_holomorphic_implicit_mapping {D : Set (P × Q)} (hD : IsOpen D)
    {f : P × Q → R} (hf : DifferentiableOn ℂ f D) {a : P} {b : Q}
    (hab : (a, b) ∈ D)
    (hi : ((fderiv ℂ f (a, b)).comp (ContinuousLinearMap.inr ℂ P Q)).IsInvertible) :
    ∃ (U : Set P) (V : Set Q) (g : P → Q),
      IsOpen U ∧ a ∈ U ∧ IsOpen V ∧ b ∈ V ∧ U ×ˢ V ⊆ D ∧
      DifferentiableOn ℂ g U ∧ MapsTo g U V ∧ g a = b ∧
      HasFDerivAt g
        (-((fderiv ℂ f (a, b)).comp (ContinuousLinearMap.inr ℂ P Q)).inverse |>.comp
          ((fderiv ℂ f (a, b)).comp (ContinuousLinearMap.inl ℂ P Q))) a ∧
      ∀ x ∈ U, ∀ y ∈ V, f (x, y) = f (a, b) ↔ y = g x := by
  let := FiniteDimensional.complete ℂ P
  let := FiniteDimensional.complete ℂ Q
  obtain ⟨U, V, g, hU, ha, hV, hb, hsub, hg, hm, hga, hd, heq⟩ :=
    exists_analytic_implicit_mapping hD hab (hf.analyticOnNhd_of_finiteDimensional hD _ hab) hi
  exact ⟨U, V, g, hU, ha, hV, hb, hsub, hg.differentiableOn, hm, hga, hd, heq⟩

/-- [Range][Range1986]'s zero-set formulation: near a regular zero the zero set is a holomorphic
graph. -/
theorem exists_holomorphic_implicit_zero {D : Set (P × Q)} (hD : IsOpen D)
    {f : P × Q → R} (hf : DifferentiableOn ℂ f D) {a : P} {b : Q}
    (hab : (a, b) ∈ D) (hzero : f (a, b) = 0)
    (hi : ((fderiv ℂ f (a, b)).comp (ContinuousLinearMap.inr ℂ P Q)).IsInvertible) :
    ∃ (U : Set P) (V : Set Q) (g : P → Q),
      IsOpen U ∧ a ∈ U ∧ IsOpen V ∧ b ∈ V ∧ U ×ˢ V ⊆ D ∧
      DifferentiableOn ℂ g U ∧ MapsTo g U V ∧ g a = b ∧
      ∀ x ∈ U, ∀ y ∈ V, f (x, y) = 0 ↔ y = g x := by
  obtain ⟨U, V, g, hU, ha, hV, hb, hsub, hg, hm, hga, _, heq⟩ :=
    exists_holomorphic_implicit_mapping hD hf hab hi
  exact ⟨U, V, g, hU, ha, hV, hb, hsub, hg, hm, hga, by simpa only [hzero] using heq⟩

end Holomorphic

/-- The determinant-of-a-minor formulation of the implicit mapping theorem. The chosen coordinates
are the second factor; their Jacobian is the Jacobian of the corresponding slice. -/
theorem exists_holomorphic_implicit_zero_of_det [FiniteDimensional ℂ P]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {D : Set (P × (ι → ℂ))} (hD : IsOpen D)
    {f : P × (ι → ℂ) → (ι → ℂ)} (hf : DifferentiableOn ℂ f D)
    {a : P} {b : ι → ℂ} (hab : (a, b) ∈ D) (hzero : f (a, b) = 0)
    (hdet : (complexJacobian (fun y => f (a, y)) b).det ≠ 0) :
    ∃ (U : Set P) (V : Set (ι → ℂ)) (g : P → (ι → ℂ)),
      IsOpen U ∧ a ∈ U ∧ IsOpen V ∧ b ∈ V ∧ U ×ˢ V ⊆ D ∧
      DifferentiableOn ℂ g U ∧ MapsTo g U V ∧ g a = b ∧
      ∀ x ∈ U, ∀ y ∈ V, f (x, y) = 0 ↔ y = g x := by
  have hd := ((hf (a, b) hab).differentiableAt (hD.mem_nhds hab)).hasFDerivAt
  have hs := hd.comp b (hasFDerivAt_prodMk_right a b (𝕜 := ℂ))
  apply exists_holomorphic_implicit_zero hD hf hab hzero
  have hi := (det_complexJacobian_ne_zero_iff hs.differentiableAt).mp hdet
  rwa [hs.fderiv] at hi


end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
