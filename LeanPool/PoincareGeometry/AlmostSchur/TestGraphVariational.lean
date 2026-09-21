/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyCutoffGraph

/-! # Continuity of the local variational equation on the actual test graph

The flux and forcing are genuine L² classes. Once their pairing identity is
proved on classical tests, continuity proves it on the graph closure.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A finite L² flux/forcing identity extends to strongly approximable tests,
including the derivative components of their actual test graphs. -/
theorem variational_eq_on_closure_c1SupportedTestGraph
    {ι : Type*} [Fintype ι] (b : ι → E) (U : Set E)
    (F : ι → Lp ℝ 2 (volume : Measure E)) (f : Lp ℝ 2 (volume : Measure E))
    (h : ∀ p ∈ c1SupportedTestGraph b U,
      (∑ i, inner ℝ (F i) (p.2 i)) = inner ℝ f p.1)
    {p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))}
    (hp : p ∈ closure (c1SupportedTestGraph b U)) :
    (∑ i, inner ℝ (F i) (p.2 i)) = inner ℝ f p.1 := by
  apply closure_minimal (t := {q : Lp ℝ 2 (volume : Measure E) ×
      (ι → Lp ℝ 2 (volume : Measure E)) |
      (∑ i, inner ℝ (F i) (q.2 i)) = inner ℝ f q.1}) h ?_ hp
  apply isClosed_eq
  · exact continuous_finsetSum _ fun i _ =>
      continuous_const.inner ((continuous_apply i).comp continuous_snd)
  · exact continuous_const.inner continuous_fst

end AlmostSchur
