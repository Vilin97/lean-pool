/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.Definitions
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
The “three-parameter recursive cutoff” construction (a radius-1 factor-of-i.i.d. triple rule).

This file defines the explicit rule (as a `ClassicalAlgorithm`) for a convenient rational choice of
parameters `(t, t1, t2)`. Later files will prove the quantitative bound
`ClassicalAlgorithm.p recursive3ParamAlg < 24118/100000`.
-/

namespace Distributed2Coloring

open MeasureTheory
open scoped unitInterval

namespace UpperBound
namespace Recursive3Param


/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def t : Rand :=
  (⟨(5 / 8 : ℝ), by constructor <;> norm_num⟩ : I)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def t1 : Rand :=
  (⟨(3 / 8 : ℝ), by constructor <;> norm_num⟩ : I)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def t2 : Rand :=
  (⟨(17 / 32 : ℝ), by constructor <;> norm_num⟩ : I)

lemma t1_lt_t2 : (t1 : ℝ) < t2 := by norm_num [t1, t2]

lemma t2_lt_t : (t2 : ℝ) < t := by norm_num [t2, t]

lemma t_lt_one : (t : ℝ) < 1 := by norm_num [t]

lemma zero_lt_t : (0 : ℝ) < t := by simp [t]

lemma t1_le_t2 : (t1 : ℝ) ≤ t2 := (t1_lt_t2).le
lemma t2_le_t : (t2 : ℝ) ≤ t := (t2_lt_t).le

/-!
### Base surface `z_base` (one parameter)

This is the base cutoff surface `z_base(x,y;t)` described in the project write-up.
-/

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def zBase (x y : Rand) : ℝ :=
  if (y : ℝ) ∈ Set.Ici (t : ℝ) then
    if (x : ℝ) ∈ Set.Iio (t : ℝ) then 1 else (t : ℝ)
  else
    if (x : ℝ) ∈ Set.Ici (t : ℝ) then 0
    else if ((x : ℝ), (y : ℝ)) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} then (t : ℝ) else (y : ℝ)

/-!
### Recursive surface at the chosen parameters

For these concrete dyadic-rational parameters, the rescaling maps `phi` and `psi` from the tex are
both globally linear, which simplifies the “inside square” formula substantially.

We implement the recursive surface directly using the induced partition (this is definitionally a
3-parameter rule with parameters `(t,t1,t2)`).
-/

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def z0 (x y : Rand) : ℝ :=
  if ((x : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (y : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)) then
    -- Inside `[t1,t] × [t1,t]`, the recursion collapses to the base rule with threshold `t2`.
    if (y : ℝ) ∈ Set.Iio (t2 : ℝ) then
      if (x : ℝ) ∈ Set.Ici (t2 : ℝ) then (t1 : ℝ)
      else if ((x : ℝ), (y : ℝ)) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} then (t2 : ℝ) else (y : ℝ)
    else
      if (x : ℝ) ∈ Set.Iio (t2 : ℝ) then (t : ℝ) else (t2 : ℝ)
  else
    zBase x y

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def g (x y z : Rand) : Color :=
  if (z : ℝ) < z0 x y then 1 else 0

lemma measurable_zBase : Measurable fun xy : Rand × Rand => zBase xy.1 xy.2 := by
  classical
  -- `zBase` is piecewise defined using comparisons against constants and projections.
  have mx : Measurable fun xy : Rand × Rand => (xy.1 : ℝ) := by
    exact measurable_subtype_coe.comp measurable_fst
  have my : Measurable fun xy : Rand × Rand => (xy.2 : ℝ) := by
    exact measurable_subtype_coe.comp measurable_snd
  have mxy : Measurable fun xy : Rand × Rand => ((xy.1 : ℝ), (xy.2 : ℝ)) := mx.prodMk my
  let leSet : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ p.2}
  have hxy_le : MeasurableSet {xy : Rand × Rand | ((xy.1 : ℝ), (xy.2 : ℝ)) ∈ leSet} := by
    have hclosed : IsClosed leSet := isClosed_le continuous_fst continuous_snd
    have hset : MeasurableSet leSet := hclosed.measurableSet
    exact hset.preimage mxy
  refine Measurable.ite (hp := ?_) ?_ ?_
  · -- `(t : ℝ) ≤ y`
    exact (measurableSet_Ici : MeasurableSet (Set.Ici (t : ℝ))).preimage my
  · refine Measurable.ite (hp := ?_) ?_ ?_
    · exact (measurableSet_Iio : MeasurableSet (Set.Iio (t : ℝ))).preimage mx
    · exact measurable_const
    · exact measurable_const
  · refine Measurable.ite (hp := ?_) ?_ ?_
    · exact (measurableSet_Ici : MeasurableSet (Set.Ici (t : ℝ))).preimage mx
    · exact measurable_const
    · refine Measurable.ite (hp := hxy_le) ?_ ?_
      · exact measurable_const
      · exact my

lemma measurable_z0 : Measurable fun xy : Rand × Rand => z0 xy.1 xy.2 := by
  classical
  have mx : Measurable fun xy : Rand × Rand => (xy.1 : ℝ) := by
    exact measurable_subtype_coe.comp measurable_fst
  have my : Measurable fun xy : Rand × Rand => (xy.2 : ℝ) := by
    exact measurable_subtype_coe.comp measurable_snd
  have mxy : Measurable fun xy : Rand × Rand => ((xy.1 : ℝ), (xy.2 : ℝ)) := mx.prodMk my
  let leSet : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ p.2}
  have hxy_le : MeasurableSet {xy : Rand × Rand | ((xy.1 : ℝ), (xy.2 : ℝ)) ∈ leSet} := by
    have hclosed : IsClosed leSet := isClosed_le continuous_fst continuous_snd
    have hset : MeasurableSet leSet := hclosed.measurableSet
    exact hset.preimage mxy
  have hxIcc : MeasurableSet {xy : Rand × Rand | (xy.1 : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)} := by
    exact (measurableSet_Icc : MeasurableSet (Set.Icc (t1 : ℝ) (t : ℝ))).preimage mx
  have hyIcc : MeasurableSet {xy : Rand × Rand | (xy.2 : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)} := by
    exact (measurableSet_Icc : MeasurableSet (Set.Icc (t1 : ℝ) (t : ℝ))).preimage my
  have hsq :
      MeasurableSet
        {xy : Rand × Rand |
            (xy.1 : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (xy.2 : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)} :=
    hxIcc.inter hyIcc
  refine Measurable.ite (hp := hsq) ?inside ?outside
  · -- Inside-square branch
    have hy_lt : MeasurableSet {xy : Rand × Rand | (xy.2 : ℝ) ∈ Set.Iio (t2 : ℝ)} :=
      (measurableSet_Iio : MeasurableSet (Set.Iio (t2 : ℝ))).preimage my
    refine Measurable.ite (hp := hy_lt) ?ylt ?yge
    · -- `y < t2`
      have hx_ge : MeasurableSet {xy : Rand × Rand | (xy.1 : ℝ) ∈ Set.Ici (t2 : ℝ)} :=
        (measurableSet_Ici : MeasurableSet (Set.Ici (t2 : ℝ))).preimage mx
      refine Measurable.ite (hp := hx_ge) ?_ ?_
      · exact measurable_const
      · refine Measurable.ite (hp := hxy_le) ?_ ?_
        · exact measurable_const
        · exact my
    · -- `¬ y < t2`
      have hx_lt : MeasurableSet {xy : Rand × Rand | (xy.1 : ℝ) ∈ Set.Iio (t2 : ℝ)} :=
        (measurableSet_Iio : MeasurableSet (Set.Iio (t2 : ℝ))).preimage mx
      refine Measurable.ite (hp := hx_lt) ?_ ?_
      · exact measurable_const
      · exact measurable_const
  · -- Outside-square branch
    exact measurable_zBase

lemma measurable_g : Measurable fun xyz : Rand × Rand × Rand => g xyz.1 xyz.2.1 xyz.2.2 := by
  classical
  have mz : Measurable fun xyz : Rand × Rand × Rand => (xyz.2.2 : ℝ) := by
    exact measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  let xy : Rand × Rand × Rand → Rand × Rand := fun xyz => (xyz.1, xyz.2.1)
  have mxy : Measurable xy := by exact measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have mcut : Measurable fun xyz : Rand × Rand × Rand => z0 (xy xyz).1 (xy xyz).2 := by
    exact measurable_z0.comp mxy
  have hset :
      MeasurableSet {xyz : Rand × Rand × Rand | (xyz.2.2 : ℝ) < z0 xyz.1 xyz.2.1} := by
    -- express the predicate as the preimage of `{p | p.1 < p.2}` under a measurable map to `ℝ × ℝ`
    have m : Measurable fun xyz : Rand × Rand × Rand => ((xyz.2.2 : ℝ), z0 xyz.1 xyz.2.1) :=
      mz.prodMk mcut
    have hopen : IsOpen {p : ℝ × ℝ | p.1 < p.2} := isOpen_lt continuous_fst continuous_snd
    have hmeas : MeasurableSet ({p : ℝ × ℝ | p.1 < p.2} : Set (ℝ × ℝ)) := hopen.measurableSet
    exact hmeas.preimage m
  refine Measurable.ite (hp := hset) ?_ ?_
  · exact measurable_const
  · exact measurable_const

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def recursive3ParamAlg : ClassicalAlgorithm where
  f := fun xyz => g xyz.1 xyz.2.1 xyz.2.2
  measurable_f := measurable_g

/-!
### Range lemmas

For probability computations, it is convenient to view `z0 x y` as an element of the unit interval.
-/

lemma zBase_mem_Icc (x y : Rand) : zBase x y ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  have ht : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := t.property
  have hy : (y : ℝ) ∈ Set.Icc (0 : ℝ) 1 := y.property
  by_cases hyt : (y : ℝ) ∈ Set.Ici (t : ℝ)
  · by_cases hxt : (x : ℝ) ∈ Set.Iio (t : ℝ)
    · simp [zBase, hyt, hxt]
    · simp [zBase, hyt, hxt, ht]
  · by_cases hxt : (x : ℝ) ∈ Set.Ici (t : ℝ)
    · simp [zBase, hyt, hxt]
    · by_cases hxy : ((x : ℝ), (y : ℝ)) ∈ {p : ℝ × ℝ | p.1 ≤ p.2}
      · simp [zBase, hyt, hxt, hxy, ht]
      · simp [zBase, hyt, hxt, hxy, hy]

lemma z0_mem_Icc (x y : Rand) : z0 x y ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  have ht : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := t.property
  have ht1 : (t1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := t1.property
  have ht2 : (t2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := t2.property
  have hy : (y : ℝ) ∈ Set.Icc (0 : ℝ) 1 := y.property
  by_cases hsq :
      ((x : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ) ∧ (y : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ))
  · by_cases hy_lt : (y : ℝ) ∈ Set.Iio (t2 : ℝ)
    · by_cases hx_ge : (x : ℝ) ∈ Set.Ici (t2 : ℝ)
      · simp [z0, hsq, hy_lt, hx_ge, ht1]
      · by_cases hxy : ((x : ℝ), (y : ℝ)) ∈ {p : ℝ × ℝ | p.1 ≤ p.2}
        · simp [z0, hsq, hy_lt, hx_ge, hxy, ht2]
        · simp [z0, hsq, hy_lt, hx_ge, hxy, hy]
    · by_cases hx_lt : (x : ℝ) ∈ Set.Iio (t2 : ℝ)
      · simp [z0, hsq, hy_lt, hx_lt, ht]
      · simp [z0, hsq, hy_lt, hx_lt, ht2]
  · unfold z0
    rw [if_neg hsq]
    exact zBase_mem_Icc x y

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def z0I (x y : Rand) : Rand :=
  ⟨z0 x y, z0_mem_Icc x y⟩

lemma g_eq_one_iff (x y z : Rand) : g x y z = 1 ↔ (z : ℝ) < z0 x y := by
  by_cases h : (z : ℝ) < z0 x y <;> simp [g, h]

lemma g_eq_zero_iff (x y z : Rand) : g x y z = 0 ↔ ¬ (z : ℝ) < z0 x y := by
  by_cases h : (z : ℝ) < z0 x y <;> simp [g, h]

end Recursive3Param
end UpperBound

end Distributed2Coloring
