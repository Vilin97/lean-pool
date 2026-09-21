/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothLocalFlow
public import LeanPool.PoincareGeometry.LichnerowiczObata.UniformManifoldODE

/-! # Jointly smooth local manifold flows

The chart-lifting derivative calculation follows Mathlib's
`exists_isMIntegralCurveAt_of_contMDiffAt`, by Winston Yin, at commit
`db584cd6d46c92f209a44c0f1c829460d327499d`, as in `UniformManifoldODE`.
Joint smoothness comes from the constructed Picard path-space solution.
-/

@[expose] public noncomputable section
open Function Manifold Set
open scoped Topology ContDiff

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [HasContDiffBump E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

/-- Finite-order joint smoothness of a local manifold flow, without an
assumed smooth-dependence hypothesis. -/
theorem exists_smooth_local_manifold_flow (n : ℕ) (hn : n ≠ 0)
    {v : Π x : M, TangentSpace I x} {x : M}
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (fun y => (⟨y, v y⟩ : TangentBundle I M)) x) :
    ∃ V ∈ 𝓝 x, ∃ δ : ℝ, 0 < δ ∧
      ∃ α : M × ℝ → M, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I n α (V ×ˢ Metric.ball 0 δ) ∧
        ∀ y ∈ V, α (y, 0) = y ∧
          IsMIntegralCurveOn (fun t => α (y, t)) v (Metric.ball 0 δ) := by
  let φ := extChartAt I x
  let w : E → E := fun z => tangentCoordChange I (φ.symm z) x (φ.symm z) (v (φ.symm z))
  rw [contMDiffAt_iff] at hv
  have hw : ContDiffAt ℝ n w (φ x) :=
    (hv.2.contDiffAt (by simp [I.range_eq_univ])).snd
  have htarget : φ.target ∈ 𝓝 (φ x) :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds (φ.map_source (mem_extChartAt_source x))
  obtain ⟨W, hW, δ, hδ, α, hαc, hsol⟩ := exists_smooth_local_flow n hn hw htarget
  let V := φ.source ∩ φ ⁻¹' W
  have hV : V ∈ 𝓝 x :=
    Filter.inter_mem ((isOpen_extChartAt_source (I := I) x).mem_nhds (mem_extChartAt_source x))
      ((continuousAt_extChartAt (I := I) x) hW)
  refine ⟨V, hV, δ, hδ, fun z => φ.symm (α (φ z.1, z.2)), ?_, ?_⟩
  · have hcoord : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) n
        (fun z : M × ℝ => (φ z.1, z.2)) (V ×ˢ Metric.ball 0 δ) := by
      apply (contMDiffOn_prod_module_iff _).mpr
      exact ⟨(contMDiffOn_extChartAt (I := I) (x := x)).comp contMDiffOn_fst
        (fun z hz => by simpa only [φ, extChartAt_source, mem_preimage] using hz.1.1),
        contMDiffOn_snd⟩
    have hα' := hαc.contMDiffOn.comp hcoord (fun z hz => ⟨hz.1.2, hz.2⟩)
    exact (contMDiffOn_extChartAt_symm (I := I) (n := n) x).comp hα'
      (fun z hz => ((hsol (φ z.1) hz.1.2).2 z.2 hz.2).1)
  intro y hy
  let f : ℝ → E := fun t => α (φ y, t)
  obtain ⟨hf0, hf⟩ := hsol (φ y) hy.2
  change φ.symm (f 0) = y ∧ IsMIntegralCurveOn (φ.symm ∘ f) v (Metric.ball 0 δ)
  refine ⟨?_, ?_⟩
  · simp only [f, hf0, φ.left_inv hy.1]
  · intro t ht
    let z : M := φ.symm (f t)
    have h : HasDerivAt f (tangentCoordChange I z x z (v z)) t := (hf t ht).2
    have hf3' : f t ∈ φ.target := (hf t ht).1
    have hft1 : z ∈ φ.source := φ.map_target hf3'
    have hft2 := mem_extChartAt_source (I := I) z
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
      HasDerivWithinAt.hasFDerivWithinAt ?_⟩
    simp only [mfld_simps, hasDerivWithinAt_univ]
    change HasDerivAt ((extChartAt I z ∘ φ.symm) ∘ f) (v z) t
    rw [← tangentCoordChange_self (I := I) (x := z) (z := z) (v := v z) hft2,
      ← tangentCoordChange_comp (x := x) ⟨⟨hft2, hft1⟩, hft2⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ h
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ (by simp [I.range_eq_univ])
    rw [← φ.right_inv hf3']
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

end LichnerowiczObata
