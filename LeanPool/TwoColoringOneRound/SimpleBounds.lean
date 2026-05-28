/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Tactic

namespace Distributed2Coloring

open MeasureTheory
open scoped BigOperators
open scoped unitInterval

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def half : Rand :=
  (⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩ : I)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def threshold (x : Rand) : Color :=
  if x < half then 0 else 1

lemma threshold_eq_zero_iff (x : Rand) : threshold x = 0 ↔ x < half := by
  by_cases hx : x < half <;> simp [threshold, hx]

lemma threshold_eq_one_iff (x : Rand) : threshold x = 1 ↔ half ≤ x := by
  by_cases hx : x < half
  · simp [threshold, hx, hx.not_ge]
  · simp [threshold, hx, not_lt.mp hx]

lemma measurable_threshold : Measurable threshold := by
  classical
  refine Measurable.ite (hp := (measurableSet_Iio : MeasurableSet (Set.Iio half))) ?_ ?_
  · simp
  · simp

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def g : Color → Color → Color → Color
  | 0, 0, 0 => 1
  | 1, 1, 1 => 0
  | _, b, _ => b

lemma measurable_g : Measurable (fun t : Color × Color × Color => g t.1 t.2.1 t.2.2) := by
  classical
  exact measurable_of_finite _

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def simpleUpperAlg : ClassicalAlgorithm where
  f := fun abc =>
    g (threshold abc.1) (threshold abc.2.1) (threshold abc.2.2)
  measurable_f := by
    classical
    have h0 : Measurable fun abc : Rand × Rand × Rand => threshold abc.1 :=
      measurable_threshold.comp measurable_fst
    have h1 : Measurable fun abc : Rand × Rand × Rand => threshold abc.2.1 :=
      measurable_threshold.comp (measurable_fst.comp measurable_snd)
    have h2 : Measurable fun abc : Rand × Rand × Rand => threshold abc.2.2 :=
      measurable_threshold.comp (measurable_snd.comp measurable_snd)
    simpa using measurable_g.comp (h0.prodMk (h1.prodMk h2))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def side (b : Color) : Set Rand :=
  if b = 0 then Set.Iio half else Set.Ici half

lemma fin2_eq_one_of_ne_zero {b : Color} (hb : b ≠ 0) : b = 1 := by
  fin_cases b <;> first | cases hb rfl | rfl

lemma side_measure (b : Color) : (volume : Measure Rand) (side b) = (1 / 2 : ENNReal) := by
  fin_cases b
  · simp [side, half]
  · have hhalf : (1 - (half : ℝ)) = (1 / 2 : ℝ) := by
      simp [half]
      norm_num
    calc
      (volume : Measure Rand) (side (1 : Color)) = ENNReal.ofReal (1 - (half : ℝ)) := by
        simp [side]
      _ = ENNReal.ofReal (1 / 2 : ℝ) := by simp [hhalf]
      _ = (1 / 2 : ENNReal) := by simp

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def cell (w : Fin 4 → Color) : Set (Samples 4) :=
  Set.univ.pi fun i => side (w i)

lemma measurableSet_cell (w : Fin 4 → Color) : MeasurableSet (cell w) := by
  classical
  refine MeasurableSet.univ_pi fun i => ?_
  by_cases h : w i = 0 <;> simp [side, h, measurableSet_Iio, measurableSet_Ici]

lemma one_half_pow_four : ((1 / 2 : ENNReal) ^ 4) = (1 / 16 : ENNReal) := by
  calc
    ((1 / 2 : ENNReal) ^ 4) = ((2⁻¹ : ENNReal) ^ 4) := by simp [div_eq_mul_inv]
    _ = ((2 : ENNReal) ^ 4)⁻¹ := by
          simpa using (ENNReal.inv_pow (a := (2 : ENNReal)) (n := 4)).symm
    _ = (16⁻¹ : ENNReal) := by norm_num
    _ = (1 / 16 : ENNReal) := by simp [div_eq_mul_inv]

lemma cell_measure (w : Fin 4 → Color) :
    (volume : Measure (Samples 4)) (cell w) = (1 / 16 : ENNReal) := by
  classical
  have hrect :
      (volume : Measure (Samples 4)) (cell w) =
        ∏ i : Fin 4, (volume : Measure Rand) (side (w i)) := by
    -- `volume` on `Samples 4` is definitional equal to a product measure.
    change (Measure.pi (fun _ : Fin 4 => (volume : Measure Rand))) (cell w) = _
    simp [cell]
  have :
      (volume : Measure (Samples 4)) (cell w) = ∏ _i : Fin 4, (1 / 2 : ENNReal) := by
    simp [hrect, side_measure]
  calc
    (volume : Measure (Samples 4)) (cell w)
        = ∏ _i : Fin 4, (1 / 2 : ENNReal) := this
    _ = (1 / 2 : ENNReal) ^ 4 := by simp
    _ = (1 / 16 : ENNReal) := one_half_pow_four

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def good (w : Fin 4 → Color) : Prop :=
  g (w 0) (w 1) (w 2) = g (w 1) (w 2) (w 3)

lemma mem_cell_iff_threshold_eq (x : Samples 4) (w : Fin 4 → Color) :
    x ∈ cell w ↔ ∀ i, threshold (x i) = w i := by
  classical
  constructor
  · intro hx i
    have hx' := hx i (by trivial)
    by_cases hw : w i = 0
    · have : x i < half := by simpa [cell, side, hw] using hx'
      simpa [hw] using (threshold_eq_zero_iff (x := x i)).2 this
    · have hwi : w i = 1 := fin2_eq_one_of_ne_zero (b := w i) (by simpa using hw)
      have : half ≤ x i := by simpa [cell, side, hw, hwi] using hx'
      simpa [hwi] using (threshold_eq_one_iff (x := x i)).2 this
  · intro hx i _
    by_cases hw : w i = 0
    · have : x i < half := (threshold_eq_zero_iff (x := x i)).1 (by simpa [hw] using hx i)
      simpa [cell, side, hw] using this
    · have hwi : w i = 1 := fin2_eq_one_of_ne_zero (b := w i) (by simpa using hw)
      have : half ≤ x i := (threshold_eq_one_iff (x := x i)).1 (by simpa [hwi] using hx i)
      simpa [cell, side, hw, hwi] using this

lemma pEvent_inter_cell_of_good {w : Fin 4 → Color} (hw : good w) :
    ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w = cell w := by
  classical
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxC
    have hxW : ∀ i, threshold (x i) = w i := (mem_cell_iff_threshold_eq x w).1 hxC
    have hxE : x ∈ ClassicalAlgorithm.pEvent simpleUpperAlg := by
      have : g (threshold (x 0)) (threshold (x 1)) (threshold (x 2)) =
          g (threshold (x 1)) (threshold (x 2)) (threshold (x 3)) := by
        simpa [good, hxW 0, hxW 1, hxW 2, hxW 3] using hw
      simpa [ClassicalAlgorithm.pEvent, simpleUpperAlg] using this
    exact ⟨hxE, hxC⟩

lemma pEvent_inter_cell_of_not_good {w : Fin 4 → Color} (hw : ¬ good w) :
    ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w = ∅ := by
  classical
  ext x
  constructor
  · rintro ⟨hxE, hxC⟩
    have hxW : ∀ i, threshold (x i) = w i := (mem_cell_iff_threshold_eq x w).1 hxC
    have hw' : good w := by
      have : g (threshold (x 0)) (threshold (x 1)) (threshold (x 2)) =
          g (threshold (x 1)) (threshold (x 2)) (threshold (x 3)) := by
        simpa [ClassicalAlgorithm.pEvent, simpleUpperAlg] using hxE
      simpa [good, hxW 0, hxW 1, hxW 2, hxW 3] using this
    exact (hw hw').elim
  · intro hx
    exact hx.elim

theorem p_simpleUpperAlg : ClassicalAlgorithm.p simpleUpperAlg = (1 / 4 : ENNReal) := by
  classical
  let all : Finset (Fin 4 → Color) := Finset.univ
  letI : DecidablePred good := fun w => by
    simpa [good] using
      (decEq (g (w 0) (w 1) (w 2)) (g (w 1) (w 2) (w 3)))
  have hcover :
      ClassicalAlgorithm.pEvent simpleUpperAlg =
        ⋃ w ∈ all, ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w := by
    ext x
    constructor
    · intro hx
      let w : Fin 4 → Color := fun i => threshold (x i)
      have hxC : x ∈ cell w := (mem_cell_iff_threshold_eq x w).2 (fun _ => rfl)
      refine Set.mem_iUnion.2 ⟨w, ?_⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨by simp [all], ?_⟩
      exact ⟨hx, hxC⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨w, hx⟩
      rcases Set.mem_iUnion.1 hx with ⟨_, hx⟩
      exact hx.1
  have hdisj :
      ∀ {w1 w2 : Fin 4 → Color},
        w1 ∈ all → w2 ∈ all → w1 ≠ w2 →
          Disjoint (ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w1)
            (ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w2) := by
    intro w1 w2 _ _ hne
    refine Set.disjoint_left.2 ?_
    intro x hx1 hx2
    have hw1 : ∀ i, threshold (x i) = w1 i := (mem_cell_iff_threshold_eq x w1).1 hx1.2
    have hw2 : ∀ i, threshold (x i) = w2 i := (mem_cell_iff_threshold_eq x w2).1 hx2.2
    apply hne
    funext i
    exact (hw1 i).symm.trans (hw2 i)
  have hmeas (w : Fin 4 → Color) :
      MeasurableSet (ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w) :=
    (ClassicalAlgorithm.measurableSet_pEvent simpleUpperAlg).inter (measurableSet_cell w)
  have hsum :
      (volume : Measure (Samples 4)) (ClassicalAlgorithm.pEvent simpleUpperAlg) =
        all.sum fun w =>
          (volume : Measure (Samples 4)) (ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w) := by
    have hd :
        Set.PairwiseDisjoint (↑all) (fun w => ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w) :=
      by
      intro w1 hw1 w2 hw2 hne
      exact hdisj hw1 hw2 hne
    have :=
      measure_biUnion_finset (μ := (volume : Measure (Samples 4))) (s := all)
        (f := fun w => ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w) hd fun w hw => hmeas w
    simpa [hcover.symm] using this
  let goodSet : Finset (Fin 4 → Color) := all.filter good
  have hsum' :
      (all.sum fun w =>
          (volume : Measure (Samples 4)) (ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w)) =
        (goodSet.card : ENNReal) * (1 / 16 : ENNReal) := by
    classical
    have hterm (w : Fin 4 → Color) :
        (volume : Measure (Samples 4)) (ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w) =
          if good w then (1 / 16 : ENNReal) else 0 := by
      by_cases hw : good w
      · have hcell :
          ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w = cell w :=
          pEvent_inter_cell_of_good (w := w) hw
        simp [hw, hcell, cell_measure]
      · have hempty :
          ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w = ∅ :=
          pEvent_inter_cell_of_not_good (w := w) hw
        simp [hw, hempty]
    calc
      all.sum (fun w =>
          (volume : Measure (Samples 4)) (ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w)) =
          all.sum (fun w => if good w then (1 / 16 : ENNReal) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro w _
            simp [hterm w]
      _ = goodSet.sum (fun _ => (1 / 16 : ENNReal)) := by
            symm
            simpa [goodSet] using
              (Finset.sum_filter (s := all) (p := good) (f := fun _ => (1 / 16 : ENNReal)))
      _ = (goodSet.card : ENNReal) * (1 / 16 : ENNReal) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hcard : goodSet.card = 4 := by decide
  calc
    ClassicalAlgorithm.p simpleUpperAlg
        = (volume : Measure (Samples 4)) (ClassicalAlgorithm.pEvent simpleUpperAlg) := rfl
    _ =
        all.sum (fun w =>
          (volume : Measure (Samples 4)) (ClassicalAlgorithm.pEvent simpleUpperAlg ∩ cell w)) :=
        hsum
    _ = (goodSet.card : ENNReal) * (1 / 16 : ENNReal) := hsum'
    _ = (4 : ENNReal) * (1 / 16 : ENNReal) := by simp [hcard]
    _ = (1 / 4 : ENNReal) := by
      have : (4 : ENNReal) / 16 = (1 : ENNReal) / 4 := by
        have h16 : (16 : ENNReal) = (4 : ENNReal) * 4 := by norm_num
        have :
            (4 : ENNReal) * (1 : ENNReal) / ((4 : ENNReal) * 4) = (1 : ENNReal) / 4 := by
          simpa using
            (ENNReal.mul_div_mul_left (a := (1 : ENNReal)) (b := (4 : ENNReal))
              (c := (4 : ENNReal)) (by norm_num) (by norm_num))
        simpa [h16, div_eq_mul_inv] using this
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this

theorem exists_algorithm_p_le_one_quarter :
    ∃ alg : ClassicalAlgorithm, ClassicalAlgorithm.p alg ≤ (1 / 4 : ENNReal) :=
  ⟨simpleUpperAlg, by simp [p_simpleUpperAlg]⟩

lemma eq_of_ne_of_ne {x y z : Color} (hxy : x ≠ y) (hyz : y ≠ z) : z = x := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp at hxy hyz <;> decide

lemma exists_monochromatic_edge (c : Fin 5 → Color) : ∃ i : Fin 5, c i = c (i + 1) := by
  classical
  by_contra h
  have h' : ∀ i : Fin 5, c i ≠ c (i + 1) := by simpa [not_exists] using h
  have h01 : c 0 ≠ c 1 := by simpa using h' 0
  have h12 : c 1 ≠ c 2 := by simpa using h' 1
  have hc2 : c 2 = c 0 := eq_of_ne_of_ne h01 h12
  have h23 : c 2 ≠ c 3 := by simpa using h' 2
  have hc3 : c 3 = c 1 := by simpa [hc2] using eq_of_ne_of_ne h12 h23
  have h34 : c 3 ≠ c 4 := by simpa using h' 3
  have h14 : c 1 ≠ c 4 := by simpa [hc3] using h34
  have hc4 : c 4 = c 0 := eq_of_ne_of_ne h01 h14
  exact (h' 4) (by simp [hc4])

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def nodeColor (alg : ClassicalAlgorithm) (x : Samples 5) (i : Fin 5) : Color :=
  alg.f (x (i - 1), x i, x (i + 1))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeEvent (alg : ClassicalAlgorithm) (i : Fin 5) : Set (Samples 5) :=
  {x | nodeColor alg x i = nodeColor alg x (i + 1)}

lemma measurable_nodeColor (alg : ClassicalAlgorithm) (i : Fin 5) :
    Measurable fun x : Samples 5 => nodeColor alg x i := by
  have htriple :
      Measurable (fun x : Samples 5 => (x (i - 1), x i, x (i + 1)) :
        Samples 5 → Rand × Rand × Rand) :=
    (measurable_pi_apply (i - 1)).prodMk
      ((measurable_pi_apply i).prodMk (measurable_pi_apply (i + 1)))
  simpa [nodeColor] using alg.measurable_f.comp htriple

lemma measurableSet_edgeEvent (alg : ClassicalAlgorithm) (i : Fin 5) :
    MeasurableSet (edgeEvent alg i) := by
  classical
  simpa [edgeEvent] using
    measurableSet_eq_fun (measurable_nodeColor alg i) (measurable_nodeColor alg (i + 1))

lemma iUnion_edgeEvent_eq_univ (alg : ClassicalAlgorithm) :
    (⋃ i : Fin 5, edgeEvent alg i) = Set.univ := by
  classical
  ext x
  constructor
  · intro _; trivial
  · intro _
    rcases exists_monochromatic_edge (fun i => nodeColor alg x i) with ⟨i, hi⟩
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    simpa [edgeEvent] using hi

lemma edgeEvent_one_measure_eq_p (alg : ClassicalAlgorithm) :
    (volume : Measure (Samples 5)) (edgeEvent alg 1) = ClassicalAlgorithm.p alg := by
  classical
  -- Split off the last coordinate; the remaining `Fin 4` coordinates are independent and uniform.
  let iLast : Fin 5 := Fin.last 4
  let e : (Samples 5) ≃ᵐ Rand × Samples 4 :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => Rand) iLast
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 5 => Rand) iLast
  have hmp_snd : MeasurePreserving (Prod.snd : Rand × Samples 4 → Samples 4) volume volume :=
    measurePreserving_snd (μ := (volume : Measure Rand)) (ν := (volume : Measure (Samples 4)))
  have hproj : MeasurePreserving (fun x : Samples 5 => (e x).2) volume volume :=
    hmp_snd.comp hmp
  have hnull :
      NullMeasurableSet (ClassicalAlgorithm.pEvent alg) (volume : Measure (Samples 4)) :=
    (ClassicalAlgorithm.measurableSet_pEvent alg).nullMeasurableSet
  have hevent :
      edgeEvent alg 1 =
        (fun x : Samples 5 => (e x).2) ⁻¹' ClassicalAlgorithm.pEvent alg := by
    ext x
    have hs : iLast.succAbove = Fin.castSucc := by
      simpa [iLast] using (Fin.succAbove_last (n := 4))
    -- `(e x).2` is `removeNth` at the last coordinate.
    simp [edgeEvent, nodeColor, ClassicalAlgorithm.pEvent, e, Fin.removeNth_apply, hs]
  calc
    (volume : Measure (Samples 5)) (edgeEvent alg 1)
        = (volume : Measure (Samples 5))
          ((fun x : Samples 5 => (e x).2) ⁻¹' ClassicalAlgorithm.pEvent alg) := by
          simp [hevent]
    _ = (volume : Measure (Samples 4)) (ClassicalAlgorithm.pEvent alg) := by
          simpa using hproj.measure_preimage hnull
    _ = ClassicalAlgorithm.p alg := rfl

lemma edgeEvent_measure_eq_edgeEvent_one (alg : ClassicalAlgorithm) (i : Fin 5) :
    (volume : Measure (Samples 5)) (edgeEvent alg i) =
      (volume : Measure (Samples 5)) (edgeEvent alg 1) := by
  classical
  -- Shift indices so that the edge `(i, i+1)` moves to `(1, 2)`.
  let k : Fin 5 := 1 - i
  let perm : Equiv.Perm (Fin 5) := Equiv.addRight k
  let φ : (Samples 5) ≃ᵐ (Samples 5) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin 5 => Rand) perm
  have hmp : MeasurePreserving φ volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin 5 => Rand) perm
  have hpre : φ ⁻¹' edgeEvent alg 1 = edgeEvent alg i := by
    ext x
    -- `φ` is a coordinate shift: `(φ x) j = x (j - k)`.
    have hφ (j : Fin 5) : (φ x) j = x (j - k) := by
      simpa [φ, MeasurableEquiv.coe_piCongrLeft, perm, Equiv.addRight, sub_eq_add_neg] using
        (Equiv.piCongrLeft_apply_apply (fun _ : Fin 5 => Rand) perm x (perm.symm j))
    have hnode (j : Fin 5) : nodeColor alg (φ x) j = nodeColor alg x (j - k) := by
      have hsub₁ : (j - 1) - k = (j - k) - 1 := by
        simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      have hadd₁ : (j + 1) - k = j - k + 1 := by
        simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      simp [nodeColor, hφ, hsub₁, hadd₁]
    have hk1 : (1 : Fin 5) - k = i := by simp [k]
    have hk2 : (2 : Fin 5) - k = i + 1 := by
      fin_cases i <;> decide
    simp [edgeEvent, hnode, hk1, hk2]
  have hnull : NullMeasurableSet (edgeEvent alg 1) (volume : Measure (Samples 5)) :=
    (measurableSet_edgeEvent alg 1).nullMeasurableSet
  have := hmp.measure_preimage (s := edgeEvent alg 1) hnull
  -- `measure_preimage` gives `volume (φ ⁻¹' s) = volume s`.
  simpa [hpre] using this

theorem no_algorithm_p_lt_one_fifth :
    ¬ ∃ alg : ClassicalAlgorithm, ClassicalAlgorithm.p alg < (1 / 5 : ENNReal) := by
  classical
  rintro ⟨alg, halg⟩
  have hUnion : (⋃ i : Fin 5, edgeEvent alg i) = Set.univ := iUnion_edgeEvent_eq_univ alg
  have hle :
      (volume : Measure (Samples 5)) Set.univ ≤
        ∑' i : Fin 5, (volume : Measure (Samples 5)) (edgeEvent alg i) := by
    have :
        (volume : Measure (Samples 5)) (⋃ i : Fin 5, edgeEvent alg i) ≤
          ∑' i : Fin 5, (volume : Measure (Samples 5)) (edgeEvent alg i) :=
      measure_iUnion_le fun i => edgeEvent alg i
    simpa [hUnion] using this
  have hedge :
      ∀ i : Fin 5, (volume : Measure (Samples 5)) (edgeEvent alg i) = ClassicalAlgorithm.p alg := by
    intro i
    have hi :
        (volume : Measure (Samples 5)) (edgeEvent alg i) =
          (volume : Measure (Samples 5)) (edgeEvent alg 1) :=
      edgeEvent_measure_eq_edgeEvent_one alg i
    simpa [edgeEvent_one_measure_eq_p alg] using hi
  have hsum :
      (∑' i : Fin 5, (volume : Measure (Samples 5)) (edgeEvent alg i)) =
        (5 : ENNReal) * ClassicalAlgorithm.p alg := by
    simp [hedge, tsum_fintype, Finset.sum_const, nsmul_eq_mul]
  have hone : (volume : Measure (Samples 5)) Set.univ = (1 : ENNReal) := by simp
  have hineq : (1 : ENNReal) ≤ (5 : ENNReal) * ClassicalAlgorithm.p alg := by
    have hle' :
        (1 : ENNReal) ≤ ∑' i : Fin 5, (volume : Measure (Samples 5)) (edgeEvent alg i) := by
      calc
        (1 : ENNReal) = (volume : Measure (Samples 5)) Set.univ := hone.symm
        _ ≤ ∑' i : Fin 5, (volume : Measure (Samples 5)) (edgeEvent alg i) := hle
    have hle'' := hle'
    rw [hsum] at hle''
    exact hle''
  have hbound : (1 / 5 : ENNReal) ≤ ClassicalAlgorithm.p alg := by
    have hineq' : (1 : ENNReal) ≤ ClassicalAlgorithm.p alg * (5 : ENNReal) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hineq
    refine (ENNReal.div_le_iff (by norm_num : (5 : ENNReal) ≠ 0)
      (by norm_num : (5 : ENNReal) ≠ ⊤)).2 hineq'
  exact (not_lt_of_ge hbound) halg

end Distributed2Coloring
