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

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyMean
public import Mathlib.Topology.Algebra.Module.PerfectSpace

/-! # Nontrivial mean-zero energy from positive manifold dimension -/

@[expose] public noncomputable section
open Bundle Set MeasureTheory AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [Nonempty M]

include I in
omit [IsManifold I ∞ M] in
/-- A positive-dimensional nonempty boundaryless manifold has distinct points. -/
theorem nontrivial_manifold_of_finrank_pos (hd : 0 < Module.finrank ℝ E) : Nontrivial M := by
  classical
  let : Nontrivial E := Module.finrank_pos_iff.mp hd
  let : PerfectSpace E := perfectSpace_of_module ℝ E
  rcases subsingleton_or_nontrivial M with h | h
  · let : Subsingleton M := h
    let x : M := Classical.choice ‹Nonempty M›
    have ht : (extChartAt I x).target = {(extChartAt I x) x} := by
      apply subset_antisymm
      · intro z hz
        have he : (extChartAt I x).symm z = x := Subsingleton.elim _ _
        have hi := (extChartAt I x).right_inv hz
        rw [he] at hi
        exact mem_singleton_iff.mpr hi.symm
      · exact singleton_subset_iff.mpr ((extChartAt I x).map_source (mem_extChartAt_source x))
    have hi := interior_singleton ((extChartAt I x) x)
    rw [← ht, (isOpen_extChartAt_target x).interior_eq] at hi
    have hm := (extChartAt I x).map_source (mem_extChartAt_source x)
    rw [hi] at hm
    exact False.elim hm
  · exact h

variable [T2Space M] [CompactSpace M] [LindelofSpace M]

omit [I.Boundaryless] [Nonempty M] [LindelofSpace M] in
/-- Smooth separation supplies a nonconstant function; it is not a spectral assumption. -/
theorem exists_nonconstant_smooth [Nontrivial M] :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ ∃ x y, f x ≠ f y := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  obtain ⟨f, hs, hf, _⟩ :=
    (isClosed_singleton (x := y)).isOpen_compl.exists_contMDiff_support_eq (n := (⊤ : ℕ∞)) I
  refine ⟨f, hf, x, y, ?_⟩
  have hx : f x ≠ 0 := by
    apply Function.mem_support.mp
    rw [hs]
    exact hxy
  have hy : f y = 0 := by
    apply Function.notMem_support.mp
    rw [hs]
    simp
  simpa [hy] using hx

variable
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [PreconnectedSpace M]

/-- The completed energy space is nontrivial, derived from positive dimension. -/
theorem nontrivial_energyCompletion (hd : 0 < Module.finrank ℝ E) :
    Nontrivial (EnergyCompletion (I := I) (M := M)) := by
  let : Nontrivial M := nontrivial_manifold_of_finrank_pos (I := I) hd
  obtain ⟨f, hf, x, y, hxy⟩ := exists_nonconstant_smooth (I := I) (M := M)
  let u := meanCorrectedEnergyTest f (hf.of_le (by simp))
  have hu : u ≠ 0 := by
    intro h
    have hx := congrArg (fun g : EnergySpace (I := I) (M := M) => g.val x) h
    have hy := congrArg (fun g : EnergySpace (I := I) (M := M) => g.val y) h
    change f x - riemannianMean (I := I) f = 0 at hx
    change f y - riemannianMean (I := I) f = 0 at hy
    exact hxy (by linarith)
  have hc : energyToCompletion u ≠ 0 := by
    intro h
    apply hu
    apply (energyToCompletion (I := I) (M := M)).injective
    simpa using h
  exact ⟨⟨energyToCompletion u, 0, hc⟩⟩

end LichnerowiczObata
