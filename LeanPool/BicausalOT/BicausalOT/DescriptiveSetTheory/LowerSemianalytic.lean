/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Lower Semianalytic Functions

  Reference: Bertsekas–Shreve, Definition 7.21, Lemma 7.30, Props 7.47–7.48
-/
module

public import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.AnalyticSet
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Tactic.Measurability
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Measure.Prod


/-! ### On BS Prop 7.48 (integration of lower semianalytic functions)

An earlier draft stated Bertsekas–Shreve Prop 7.48 as an `axiom`
(`lintegral_lowerSemianalytic`). It is now a fully verified THEOREM —
see `BicausalOT.DescriptiveSetTheory.KernelIntegral`. The missing
ingredient, Choquet's capacitability theorem for analytic sets
(μ(A) = sup{μ(K) | K compact ⊆ A}, not available in Mathlib), is proved
from scratch in `BicausalOT.DescriptiveSetTheory.Capacitability`
(`MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact`), together with
universal measurability (`MeasureTheory.AnalyticSet.nullMeasurableSet`)
and the parametrized kernel version
(`MeasureTheory.AnalyticSet.kernel_section_gt`). -/

@[expose] public section

open MeasureTheory Set ENNReal

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- A function f : X → ℝ≥0∞ is lower semianalytic if its strict sublevel
    sets {f < c} are analytic for all c. (BS, Definition 7.21) -/
def IsLowerSemianalytic (f : X → ENNReal) : Prop :=
  ∀ c : ENNReal, AnalyticSet {x | f x < c}

/-- l.s.c. functions are lower semianalytic.
    Proof: {f < c} is open for l.s.c. f, hence Borel, hence analytic. -/
theorem LowerSemicontinuous.isLowerSemianalytic
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {f : X → ENNReal} (hf : LowerSemicontinuous f) :
    IsLowerSemianalytic f := by
  intro c
  have hmeas : MeasurableSet {x | f x < c} := by
    exact measurableSet_lt hf.measurable measurable_const
  exact hmeas.analyticSet

/-- inf of lower semianalytic is lower semianalytic. (BS, Prop 7.47)
    Proof: {x | inf < c} = projₓ({(x,y) ∈ D | f(x,y) < c}).
    Intersection of two analytic sets is analytic; projection preserves analytic. -/
theorem IsLowerSemianalytic.iInf_fiber
    {Y : Type*} [TopologicalSpace Y] [PolishSpace Y]
    [T2Space X]
    {D : Set (X × Y)} (hD : AnalyticSet D)
    {f : X × Y → ENNReal} (hf : IsLowerSemianalytic (X := X × Y) f) :
    IsLowerSemianalytic (fun x => ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y)) := by
  intro c
  have h_sub : {x | ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y) < c} =
      Prod.fst '' (D ∩ {p | f p < c}) := by
    ext x; simp only [mem_ofPred_eq, mem_image, Prod.exists]
    constructor
    · intro hlt
      rw [iInf_lt_iff] at hlt
      obtain ⟨y, hy⟩ := hlt
      rw [iInf_lt_iff] at hy
      obtain ⟨hm, hfc⟩ := hy
      exact ⟨x, y, ⟨hm, hfc⟩, rfl⟩
    · rintro ⟨x', y, ⟨hm, hfc⟩, rfl⟩
      exact lt_of_le_of_lt (iInf₂_le y hm) hfc
  rw [h_sub]
  have h_inter : AnalyticSet (D ∩ {p | f p < c}) := by
    have h1 := hD
    have h2 := hf c
    rw [show D ∩ {p | f p < c} = ⋂ (i : Fin 2),
        (![D, {p | f p < c}]) i from by ext x; simp [Fin.forall_fin_two, Matrix.cons_val_zero,
            Matrix.cons_val_one]]
    apply AnalyticSet.iInter
    intro i
    fin_cases i
    · exact h1
    · exact h2
  exact h_inter.image_of_continuous continuous_fst



end
