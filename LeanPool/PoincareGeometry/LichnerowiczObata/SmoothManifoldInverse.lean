/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Smoothness of an existing manifold inverse -/

@[expose] public noncomputable section
open scoped Manifold ContDiff Topology
open Set
namespace LichnerowiczObata
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [I.Boundaryless] [J.Boundaryless]

/-- A continuous right inverse agrees locally with the smooth inverse-function construction. -/
theorem contDiffAt_local_inverse_of_equiv [CompleteSpace E]
    (f : E → E') (g : E' → E) (x : E) (e : E ≃L[ℝ] E')
    (hf : ContDiffAt ℝ ∞ f x) (hd : HasFDerivAt f (e : E →L[ℝ] E') x)
    (hg : ContinuousAt g (f x)) (hgx : g (f x) = x)
    (hfg : ∀ᶠ y in 𝓝 (f x), f (g y) = y) :
    ContDiffAt ℝ ∞ g (f x) := by
  let u := hf.toOpenPartialHomeomorph f hd (by norm_num)
  have hx : x ∈ u.source := hf.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  have hi : ContDiffAt ℝ ∞ u.symm (f x) := hf.to_localInverse hd (by norm_num)
  have hnear : ∀ᶠ y in 𝓝 (f x), g y ∈ u.source :=
    hg.preimage_mem_nhds (by simpa only [hgx] using u.open_source.mem_nhds hx)
  apply hi.congr_of_eventuallyEq
  filter_upwards [hnear, hfg] with y hy heq
  exact (u.left_inv hy).symm.trans (congrArg u.symm heq)

/-- An existing continuous local inverse is smooth wherever the forward map
is smooth and has an invertible manifold derivative. -/
theorem contMDiffAt_local_inverse_of_equiv [CompleteSpace E]
    (f : M → N) (g : N → M) (x : M)
    (e : TangentSpace I x ≃L[ℝ] TangentSpace J (f x))
    (hf : HasMFDerivAt I J f x (e : _ →L[ℝ] _))
    (hSmooth : ContMDiffAt I J ∞ f x)
    (hg : ContinuousAt g (f x)) (hgx : g (f x) = x)
    (hfg : ∀ᶠ y in 𝓝 (f x), f (g y) = y) :
    ContMDiffAt J I ∞ g (f x) := by
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
  have hSmoothF : ContDiffAt ℝ ∞ F (G a) := by
    rw [hg0]
    simpa only [I.range_eq_univ, contDiffWithinAt_univ, F, writtenInExtChartAt] using
      (contMDiffAt_iff.mp hSmooth).2
  have hFa : F (G a) = a := hcoord.self_of_nhds
  have hGc : ContinuousAt G (F (G a)) := by rw [hFa]; exact hG
  have hGi : G (F (G a)) = G a := congrArg G hFa
  have hFg : ∀ᶠ y in 𝓝 (F (G a)), F (G y) = y := by rw [hFa]; exact hcoord
  have hi := contDiffAt_local_inverse_of_equiv F G (G a) e hSmoothF he' hGc hGi hFg
  rw [hFa] at hi
  apply contMDiffAt_iff.mpr
  refine ⟨hg, ?_⟩
  simpa only [J.range_eq_univ, contDiffWithinAt_univ,
    G, a, hgx] using hi

end LichnerowiczObata
