/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-! # Differentiability of an existing manifold inverse -/

@[expose] public noncomputable section
open scoped Manifold Topology
open Set
namespace LichnerowiczObata
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [I.Boundaryless] [J.Boundaryless]

/-- An existing continuous local inverse is differentiable wherever the
forward map has an invertible manifold derivative. -/
theorem mdifferentiableAt_local_inverse_of_equiv
    (f : M → N) (g : N → M) (x : M)
    (e : TangentSpace I x ≃L[ℝ] TangentSpace J (f x))
    (hf : HasMFDerivAt I J f x (e : _ →L[ℝ] _))
    (hg : ContinuousAt g (f x)) (hgx : g (f x) = x)
    (hfg : ∀ᶠ y in 𝓝 (f x), f (g y) = y) :
    MDifferentiableAt J I g (f x) := by
  change E ≃L[ℝ] E' at e
  let F := writtenInExtChartAt I J x f
  let G := (extChartAt I x) ∘ g ∘ (extChartAt J (f x)).symm
  let a := extChartAt J (f x) (f x)
  have h0 : (extChartAt J (f x)).symm a = f x :=
    (extChartAt J (f x)).left_inv (mem_extChartAt_source (f x))
  have hg0 : G a = extChartAt I x x := by
    simp only [G, Function.comp_apply, h0, hgx]
  have hc0 : ContinuousAt (extChartAt J (f x)).symm a := continuousAt_extChartAt_symm (f x)
  have hmid : ContinuousAt (g ∘ (extChartAt J (f x)).symm) a := by
    have hg' : ContinuousAt g ((extChartAt J (f x)).symm a) := by rw [h0]; exact hg
    exact hg'.comp hc0
  have hG : ContinuousAt G a := by
    have hc : ContinuousAt (extChartAt I x)
        ((g ∘ (extChartAt J (f x)).symm) a) := by
      simpa only [Function.comp_apply, h0, hgx] using
        (continuousAt_extChartAt (I := I) x)
    exact hc.comp hmid
  have he : HasFDerivAt F (e : E →L[ℝ] E') (extChartAt I x x) := by
    simpa only [I.range_eq_univ, hasFDerivWithinAt_univ] using hf.2
  have he' : HasFDerivAt F (e : E →L[ℝ] E') (G a) := by rw [hg0]; exact he
  have ht : ∀ᶠ y in 𝓝 a, y ∈ (extChartAt J (f x)).target :=
    extChartAt_target_mem_nhds (f x)
  have hm : ∀ᶠ y in 𝓝 a, g ((extChartAt J (f x)).symm y) ∈
      (extChartAt I x).source := by
    have hh := hmid.preimage_mem_nhds (t := (extChartAt I x).source)
    apply hh
    simpa only [Function.comp_apply, h0, hgx] using extChartAt_source_mem_nhds (I := I) x
  have hcancel : ∀ᶠ y in 𝓝 a,
      f (g ((extChartAt J (f x)).symm y)) = (extChartAt J (f x)).symm y := by
    have htend : Filter.Tendsto (extChartAt J (f x)).symm (𝓝 a) (𝓝 (f x)) := by
      have hh : Filter.Tendsto (extChartAt J (f x)).symm (𝓝 a)
          (𝓝 ((extChartAt J (f x)).symm a)) := hc0
      simpa only [h0] using hh
    exact htend.eventually hfg
  have hcoord : ∀ᶠ y in 𝓝 a, F (G y) = y := by
    filter_upwards [ht, hm, hcancel] with y hy hm hh
    change (extChartAt J (f x)) (f ((extChartAt I x).symm
      ((extChartAt I x) (g ((extChartAt J (f x)).symm y))))) = y
    rw [(extChartAt I x).left_inv hm, hh,
      (extChartAt J (f x)).right_inv hy]
  have hi := HasFDerivAt.of_local_left_inverse (f' := (e : E ≃L[ℝ] E')) hG he' hcoord
  apply (mdifferentiableAt_iff _ _).mpr
  refine ⟨hg, ?_⟩
  simpa only [J.range_eq_univ, differentiableWithinAt_univ,
    writtenInExtChartAt, hgx] using hi.differentiableAt

/-- An existing homeomorphic inverse is differentiable wherever the forward
map has an invertible manifold derivative. No extra smoothness is assumed. -/
theorem mdifferentiableAt_homeomorph_symm_of_equiv
    (f : M ≃ₜ N) (x : M) (e : TangentSpace I x ≃L[ℝ] TangentSpace J (f x))
    (hf : HasMFDerivAt I J f x (e : _ →L[ℝ] _)) :
    MDifferentiableAt J I f.symm (f x) :=
  mdifferentiableAt_local_inverse_of_equiv f f.symm x e hf f.symm.continuous.continuousAt
    (f.symm_apply_apply x) (Filter.Eventually.of_forall f.apply_symm_apply)

/-- The inverse theorem applies on the source and target of a partial
homeomorphism, as needed for regular polar domains. -/
theorem mdifferentiableAt_partialHomeomorph_symm_of_equiv
    (f : OpenPartialHomeomorph M N) (x : M) (hx : x ∈ f.source)
    (e : TangentSpace I x ≃L[ℝ] TangentSpace J (f x))
    (hf : HasMFDerivAt I J f x (e : _ →L[ℝ] _)) :
    MDifferentiableAt J I f.symm (f x) := by
  apply mdifferentiableAt_local_inverse_of_equiv f f.symm x e hf
    (f.symm.continuousAt (f.map_source hx)) (f.left_inv hx)
  filter_upwards [f.open_target.mem_nhds (f.map_source hx)] with y hy
  exact f.right_inv hy

end LichnerowiczObata
