/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.UpperBound.Recursive3Param.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
Computation of `ClassicalAlgorithm.p` for `recursive3ParamAlg`.

This file will prove that the 3-parameter recursive cutoff algorithm from
`Distributed2Coloring/UpperBound/Recursive3Param.lean` satisfies
`ClassicalAlgorithm.p recursive3ParamAlg < 24118/100000`.
-/

namespace Distributed2Coloring

open MeasureTheory
open scoped unitInterval

namespace UpperBound
namespace Recursive3Param


open scoped ENNReal

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def μ4 (i : Fin 4) : Measure Rand :=
  if i = i then (volume : Measure Rand) else (volume : Measure Rand)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev E : Set (Samples 4) := ClassicalAlgorithm.pEvent recursive3ParamAlg

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def pInd : Samples 4 → ℝ≥0∞ :=
  Set.indicator E (fun _ => (1 : ℝ≥0∞))

lemma measurable_pInd : Measurable pInd := by
  classical
  simpa [pInd] using
    (measurable_const.indicator (ClassicalAlgorithm.measurableSet_pEvent recursive3ParamAlg))

lemma p_eq_lintegral_pInd :
    ClassicalAlgorithm.p recursive3ParamAlg =
      ∫⁻ x : Samples 4, pInd x ∂(volume : Measure (Samples 4)) := by
  classical
  unfold ClassicalAlgorithm.p
  symm
  change
    (∫⁻ x : Samples 4, E.indicator (fun _ => (1 : ℝ≥0∞)) x
        ∂(volume : Measure (Samples 4))) =
      volume E
  exact MeasureTheory.lintegral_indicator_one (μ := (volume : Measure (Samples 4)))
    (ClassicalAlgorithm.measurableSet_pEvent recursive3ParamAlg)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def dSlice (x : Samples 4) : Set Rand :=
  {d | Function.update x 3 d ∈ E}

lemma measurableSet_dSlice (x : Samples 4) : MeasurableSet (dSlice x) := by
  classical
  have hE : MeasurableSet E := ClassicalAlgorithm.measurableSet_pEvent recursive3ParamAlg
  have hupd : Measurable (Function.update x (3 : Fin 4)) := by fun_prop
  -- `dSlice x` is exactly the preimage of `E` under the measurable map `d ↦ update x 3 d`.
  change MeasurableSet ((fun d : Rand => Function.update x (3 : Fin 4) d) ⁻¹' E)
  simpa [Set.preimage, E] using hE.preimage hupd

lemma dSlice_eq (x : Samples 4) :
    dSlice x =
      if x 2 < z0I (x 0) (x 1) then Set.Iio (z0I (x 1) (x 2)) else Set.Ici (z0I (x 1) (x 2)) := by
  classical
  ext d
  by_cases hc : (x 2 : ℝ) < z0 (x 0) (x 1)
  · have hc' : x 2 < z0I (x 0) (x 1) := by
      -- `z0I` is a subtype wrapper of `z0`.
      exact_mod_cast hc
    have hL : d ∈ dSlice x ↔ (d : ℝ) < z0 (x 1) (x 2) := by
      simp [dSlice, E, ClassicalAlgorithm.pEvent, recursive3ParamAlg, g, hc]
    have hR :
        d ∈
          (if x 2 < z0I (x 0) (x 1) then Set.Iio (z0I (x 1) (x 2)) else Set.Ici (z0I (x 1) (x 2))) ↔
          d < z0I (x 1) (x 2) := by
      simp [hc']
    calc
      d ∈ dSlice x ↔ (d : ℝ) < z0 (x 1) (x 2) := hL
      _ ↔ d < z0I (x 1) (x 2) := by rfl
      _ ↔
          d ∈
            (if x 2 < z0I (x 0) (x 1) then Set.Iio (z0I (x 1) (x 2))
              else Set.Ici (z0I (x 1) (x 2))) :=
        hR.symm
  · have hc' : ¬ x 2 < z0I (x 0) (x 1) := by
      exact_mod_cast hc
    have hL : d ∈ dSlice x ↔ z0 (x 1) (x 2) ≤ (d : ℝ) := by
      simp [dSlice, E, ClassicalAlgorithm.pEvent, recursive3ParamAlg, g, hc, not_lt]
    have hR :
        d ∈
          (if x 2 < z0I (x 0) (x 1) then Set.Iio (z0I (x 1) (x 2)) else Set.Ici (z0I (x 1) (x 2))) ↔
          z0I (x 1) (x 2) ≤ d := by
      simp [hc']
    calc
      d ∈ dSlice x ↔ z0 (x 1) (x 2) ≤ (d : ℝ) := hL
      _ ↔ z0I (x 1) (x 2) ≤ d := by rfl
      _ ↔
          d ∈
            (if x 2 < z0I (x 0) (x 1) then Set.Iio (z0I (x 1) (x 2))
              else Set.Ici (z0I (x 1) (x 2))) :=
        hR.symm

lemma lmarginal_D (x : Samples 4) :
    (∫⋯∫⁻_{(3 : Fin 4)}, pInd ∂μ4) x =
      if x 2 < z0I (x 0) (x 1) then ENNReal.ofReal (z0I (x 1) (x 2))
      else ENNReal.ofReal (1 - (z0I (x 1) (x 2) : ℝ)) := by
  classical
  -- Rewrite the singleton marginal as an integral over the last coordinate,
  -- then evaluate it as the measure of an interval slice.
  have hsingle :
      (∫⋯∫⁻_{(3 : Fin 4)}, pInd ∂μ4) x =
        ∫⁻ d : Rand, pInd (Function.update x (3 : Fin 4) d) ∂(volume : Measure Rand) := by
    simp [MeasureTheory.lmarginal_singleton, μ4]
  rw [hsingle]
  have hslice :
      (fun d : Rand => pInd (Function.update x (3 : Fin 4) d)) =
        (dSlice x).indicator (1 : Rand → ℝ≥0∞) := by
    funext d
    by_cases hd : Function.update x (3 : Fin 4) d ∈ E <;> simp [pInd, dSlice, E, hd]
  simp_rw [hslice]
  -- Turn the integral of the indicator into a measure, then compute the slice.
  have hmeas : MeasurableSet (dSlice x) := measurableSet_dSlice x
  rw [MeasureTheory.lintegral_indicator_one (μ := (volume : Measure Rand)) hmeas]
  rw [dSlice_eq (x := x)]
  split_ifs <;> simp

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def aSlice (b c : Rand) : Set Rand :=
  {a | c < z0I a b}

/-!
### Explicit descriptions of `aSlice`

For our concrete dyadic parameters, `aSlice b c = {a | c < z0(a,b)}` is (away from boundary values)
always an interval in `a`. The following lemmas give exact set descriptions under hypotheses on `b`.
-/

lemma aSlice_eq_of_b_lt_t1 {b c : Rand} (hb : b < t1) :
    aSlice b c =
      if c < b then Set.Iio t else if c < t then Set.Iic b else ∅ := by
  classical
  ext a
  have hbt : (b : ℝ) < t := lt_trans hb (lt_trans t1_lt_t2 t2_lt_t)
  have hbIcc : ¬ ((b : ℝ) ∈ Set.Icc (t1 : ℝ) (t : ℝ)) := by
    simp [Set.mem_Icc, not_le_of_gt hb]
  have hbIci : ¬ ((b : ℝ) ∈ Set.Ici (t : ℝ)) := by
    simp [Set.mem_Ici, not_le_of_gt hbt]
  have hz0 :
      z0 a b =
        if (t : ℝ) ≤ a then 0 else if (a : ℝ) ≤ b then (t : ℝ) else (b : ℝ) := by
    simp [z0, zBase, hbIcc, hbIci, Set.mem_Ici]
  by_cases hcb : c < b
  · -- `c < b`: the slice is `a < t`.
    have hR : (a ∈ if c < b then Set.Iio t else if c < t then Set.Iic b else ∅) ↔ a < t := by
      simp [hcb]
    -- Reduce to the real inequality `c < z0(a,b) ↔ a < t`.
    have hcbR : (c : ℝ) < b := hcb
    have hctR : (c : ℝ) < t := lt_trans hcbR hbt
    have hL : (a ∈ aSlice b c) ↔ (a : ℝ) < t := by
      change ((c : ℝ) < z0 a b) ↔ (a : ℝ) < t
      rw [hz0]
      constructor
      · intro hc
        by_contra hat
        have hta : (t : ℝ) ≤ a := le_of_not_gt hat
        have : (c : ℝ) < 0 := by simpa [hta] using hc
        exact (not_lt_of_ge (show (0 : ℝ) ≤ c from c.property.1) this)
      · intro hat
        have hta : ¬ (t : ℝ) ≤ a := not_le_of_gt hat
        by_cases hab : (a : ℝ) ≤ b
        · simpa [hta, hab] using hctR
        · simpa [hta, hab] using hcbR
    -- Finish by rewriting the RHS.
    exact (hL.trans hR.symm)
  · -- `¬ c < b`: split on `c < t`.
    by_cases hct : c < t
    · have hR : (a ∈ if c < b then Set.Iio t else if c < t then Set.Iic b else ∅) ↔ a ≤ b := by
        simp [hcb, hct]
      have hctR : (c : ℝ) < t := hct
      have hL : (a ∈ aSlice b c) ↔ a ≤ b := by
        change ((c : ℝ) < z0 a b) ↔ a ≤ b
        rw [hz0]
        constructor
        · intro hc
          by_contra hab
          have hab' : (b : ℝ) < a := lt_of_not_ge hab
          by_cases hta : (t : ℝ) ≤ a
          · have : (c : ℝ) < 0 := by simpa [hta] using hc
            exact (not_lt_of_ge (show (0 : ℝ) ≤ c from c.property.1) this)
          · have : (c : ℝ) < b := by simpa [hta, hab] using hc
            exact hcb (show c < b from this)
        · intro hab
          have hta : ¬ (t : ℝ) ≤ a := by
            exact not_le_of_gt (lt_of_le_of_lt hab hbt)
          have hab' : (a : ℝ) ≤ b := hab
          simpa [hta, hab'] using hctR
      exact (hL.trans hR.symm)
    · have hR : a ∈ (if c < b then Set.Iio t else if c < t then Set.Iic b else ∅) ↔ False := by
        simp [hcb, hct]
      have hz0_le : z0 a b ≤ t := by
        rw [hz0]
        by_cases hta : (t : ℝ) ≤ a
        · have ht0 : (0 : ℝ) ≤ t := t.property.1
          simp [hta, ht0]
        · by_cases hab : (a : ℝ) ≤ b
          · simp [hta, hab]
          · have : (b : ℝ) ≤ t := le_of_lt hbt
            simp [hta, hab, this]
      have hL : (a ∈ aSlice b c) ↔ False := by
        change ((c : ℝ) < z0 a b) ↔ False
        constructor
        · intro hc
          have : (c : ℝ) < t := lt_of_lt_of_le hc hz0_le
          exact hct (show c < t from this)
        · intro hf
          exact False.elim hf
      exact (hL.trans hR.symm)

lemma measurableSet_aSlice (b c : Rand) : MeasurableSet (aSlice b c) := by
  classical
  have mz0 : Measurable fun ab : Rand × Rand => z0 ab.1 ab.2 := measurable_z0
  have mPair : Measurable fun a : Rand => ((c : ℝ), z0 a b) := by
    have mc : Measurable fun _a : Rand => (c : ℝ) := measurable_const
    have mb : Measurable fun a : Rand => (a, b) := measurable_id.prodMk measurable_const
    have mz : Measurable fun a : Rand => z0 a b := by
      change Measurable (fun a : Rand => (fun ab : Rand × Rand => z0 ab.1 ab.2) (a, b))
      exact mz0.comp mb
    exact mc.prodMk mz
  have hopen : IsOpen {p : ℝ × ℝ | p.1 < p.2} := isOpen_lt continuous_fst continuous_snd
  have hmeas : MeasurableSet ({p : ℝ × ℝ | p.1 < p.2} : Set (ℝ × ℝ)) := hopen.measurableSet
  -- `c < z0I a b` is definitional equal to `(c : ℝ) < z0 a b`.
  have :
      aSlice b c =
        {a : Rand | ((c : ℝ), z0 a b) ∈ ({p : ℝ × ℝ | p.1 < p.2} : Set (ℝ × ℝ))} := by
    ext a
    change (c < z0I a b) ↔ (c : ℝ) < z0 a b
    rfl
  simpa [this] using hmeas.preimage mPair

lemma lintegral_ite_const {α : Type*} [MeasurableSpace α] (μ : Measure α) {s : Set α}
    [DecidablePred (· ∈ s)] (hs : MeasurableSet s) (a b : ℝ≥0∞) :
    (∫⁻ x, (if x ∈ s then a else b) ∂μ) = a * μ s + b * μ sᶜ := by
  have h :
      (fun x : α => (if x ∈ s then a else b)) =
        (s.indicator (fun _ : α => a) + sᶜ.indicator (fun _ : α => b)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [h]
  have hf : Measurable (s.indicator (fun _ : α => a)) := measurable_const.indicator hs
  change
    (∫⁻ x,
        (s.indicator (fun _ : α => a) x + sᶜ.indicator (fun _ : α => b) x) ∂μ) =
      a * μ s + b * μ sᶜ
  rw [MeasureTheory.lintegral_add_left (μ := μ) hf (g := fun x => sᶜ.indicator (fun _ : α => b) x)]
  simp [hs]

lemma lmarginal_AD (x : Samples 4) :
    (∫⋯∫⁻_({0, 3} : Finset (Fin 4)), pInd ∂μ4) x =
      ENNReal.ofReal (z0I (x 1) (x 2)) * (volume : Measure Rand) (aSlice (x 1) (x 2)) +
        ENNReal.ofReal (1 - (z0I (x 1) (x 2) : ℝ)) *
          (volume : Measure Rand) (aSlice (x 1) (x 2))ᶜ := by
  classical
  haveI : ∀ i : Fin 4, SigmaFinite (μ4 i) := fun _ => by
    dsimp [μ4]
    infer_instance
  have hunion :
      (∫⋯∫⁻_({0, 3} : Finset (Fin 4)), pInd ∂μ4) =
        ∫⋯∫⁻_({0} : Finset (Fin 4)), ∫⋯∫⁻_({3} : Finset (Fin 4)), pInd ∂μ4 ∂μ4 := by
    simpa [Finset.union_assoc] using
      (MeasureTheory.lmarginal_union (μ := μ4) (s := ({0} : Finset (Fin 4)))
        (t := ({3} : Finset (Fin 4))) pInd measurable_pInd (by decide))
  have hunion_x := congrArg (fun g => g x) hunion
  -- Peel off the `A`-integral (index `0`).
  have h0 :
      (∫⋯∫⁻_({0} : Finset (Fin 4)), ∫⋯∫⁻_({3} : Finset (Fin 4)), pInd ∂μ4 ∂μ4) x =
        ∫⁻ a : Rand, (∫⋯∫⁻_({3} : Finset (Fin 4)), pInd ∂μ4) (Function.update x 0 a)
          ∂(volume : Measure Rand) := by
    simp [MeasureTheory.lmarginal_singleton, μ4]
  -- Evaluate the inner `D`-integral using `lmarginal_D`.
  have hinner :
      (fun a : Rand => (∫⋯∫⁻_{(3 : Fin 4)}, pInd ∂μ4) (Function.update x 0 a)) =
        fun a : Rand =>
          if x 2 < z0I a (x 1) then
            ENNReal.ofReal (z0I (x 1) (x 2))
          else
            ENNReal.ofReal (1 - (z0I (x 1) (x 2) : ℝ)) := by
    funext a
    simpa [Function.update, μ4] using (lmarginal_D (x := Function.update x 0 a))
  -- Turn the remaining integral into the measure of `aSlice`.
  have hs : MeasurableSet (aSlice (x 1) (x 2)) := measurableSet_aSlice (b := x 1) (c := x 2)
  -- Put everything together.
  calc
    (∫⋯∫⁻_({0, 3} : Finset (Fin 4)), pInd ∂μ4) x =
        (∫⋯∫⁻_({0} : Finset (Fin 4)), ∫⋯∫⁻_({3} : Finset (Fin 4)), pInd ∂μ4 ∂μ4) x := by
          simpa using hunion_x
    _ = ∫⁻ a : Rand, (∫⋯∫⁻_({3} : Finset (Fin 4)), pInd ∂μ4) (Function.update x 0 a)
          ∂(volume : Measure Rand) := h0
    _ = ∫⁻ a : Rand,
          (if x 2 < z0I a (x 1) then ENNReal.ofReal (z0I (x 1) (x 2))
            else ENNReal.ofReal (1 - (z0I (x 1) (x 2) : ℝ))) ∂(volume : Measure Rand) := by
          simp_rw [hinner]
    _ =
        ENNReal.ofReal (z0I (x 1) (x 2)) * (volume : Measure Rand) (aSlice (x 1) (x 2)) +
          ENNReal.ofReal (1 - (z0I (x 1) (x 2) : ℝ)) *
            (volume : Measure Rand) (aSlice (x 1) (x 2))ᶜ := by
          -- Convert the `ite` to an `if a ∈ aSlice ...` to apply `lintegral_ite_const`.
          have :
              (fun a : Rand =>
                  if x 2 < z0I a (x 1) then ENNReal.ofReal (z0I (x 1) (x 2))
                  else ENNReal.ofReal (1 - (z0I (x 1) (x 2) : ℝ))) =
                fun a : Rand =>
                  if a ∈ aSlice (x 1) (x 2) then ENNReal.ofReal (z0I (x 1) (x 2))
                  else ENNReal.ofReal (1 - (z0I (x 1) (x 2) : ℝ)) := by
              funext a
              simp [aSlice]
          -- Now apply the `lintegral` computation lemma.
          simpa [this] using
            (lintegral_ite_const (μ := (volume : Measure Rand)) (s := aSlice (x 1) (x 2)) hs
              (ENNReal.ofReal (z0I (x 1) (x 2)))
              (ENNReal.ofReal (1 - (z0I (x 1) (x 2) : ℝ))))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def innerBC (b c : Rand) : ℝ≥0∞ :=
  ENNReal.ofReal (z0I b c) * (volume : Measure Rand) (aSlice b c) +
    ENNReal.ofReal (1 - (z0I b c : ℝ)) * (volume : Measure Rand) (aSlice b c)ᶜ

lemma lmarginal_AD_eq_innerBC (x : Samples 4) :
    (∫⋯∫⁻_({0, 3} : Finset (Fin 4)), pInd ∂μ4) x = innerBC (x 1) (x 2) := by
  classical
  simpa [innerBC] using (lmarginal_AD (x := x))

lemma p_eq_lintegral_innerBC :
    ClassicalAlgorithm.p recursive3ParamAlg =
      ∫⁻ b : Rand, ∫⁻ c : Rand, innerBC b c ∂(volume : Measure Rand) ∂(volume : Measure Rand) := by
  classical
  haveI : ∀ i : Fin 4, SigmaFinite (μ4 i) := fun _ => by
    dsimp [μ4]
    infer_instance
  -- Start from the definition of `p` as a `lintegral` on `Samples 4` (with an explicit product
  -- measure), then rewrite it as a full marginal over all indices.
  have hp' :
      ClassicalAlgorithm.p recursive3ParamAlg =
        ∫⁻ x : Samples 4, pInd x ∂(Measure.pi μ4) := by
    -- `volume` on `Samples 4` is definitional equal to a product measure.
    have hμ4 : μ4 = fun _ : Fin 4 => (volume : Measure Rand) := by
      funext i
      simp [μ4]
    have hvol : (volume : Measure (Samples 4)) = Measure.pi μ4 := by
      rw [hμ4]
      rfl
    -- Rewrite `p` as a `lintegral` under `volume`, then change the measure to `Measure.pi μ4`.
    simpa [hvol] using p_eq_lintegral_pInd
  let x0 : Samples 4 := fun _ => (0 : Rand)
  have hlm :
      (∫⁻ x : Samples 4, pInd x ∂(Measure.pi μ4)) =
        (∫⋯∫⁻_(Finset.univ : Finset (Fin 4)), pInd ∂μ4) x0 := by
    exact MeasureTheory.lintegral_eq_lmarginal_univ (μ := μ4) (f := pInd) x0
  -- Split the full marginal into `{1,2}` and `{0,3}` (Tonelli/Fubini via `lmarginal_union`).
  have hsplit :
      (∫⋯∫⁻_(Finset.univ : Finset (Fin 4)), pInd ∂μ4) =
        ∫⋯∫⁻_({1, 2} : Finset (Fin 4)),
          (∫⋯∫⁻_({0, 3} : Finset (Fin 4)), pInd ∂μ4) ∂μ4 := by
    have h :=
      (MeasureTheory.lmarginal_union (μ := μ4) (s := ({1, 2} : Finset (Fin 4)))
        (t := ({0, 3} : Finset (Fin 4))) pInd measurable_pInd (by decide))
    have huniv : ({1, 2} ∪ {0, 3} : Finset (Fin 4)) = Finset.univ := by
      decide
    simpa [huniv] using h
  have hsplit_x0 : (∫⋯∫⁻_(Finset.univ : Finset (Fin 4)), pInd ∂μ4) x0 =
        (∫⋯∫⁻_({1, 2} : Finset (Fin 4)),
            (∫⋯∫⁻_({0, 3} : Finset (Fin 4)), pInd ∂μ4) ∂μ4) x0 := by
    simpa using congrArg (fun g => g x0) hsplit
  -- Define the `{0,3}` marginal as a measurable function of the remaining coordinates.
  let f03 : Samples 4 → ℝ≥0∞ := ∫⋯∫⁻_({0, 3} : Finset (Fin 4)), pInd ∂μ4
  have hf03 : Measurable f03 := by
    -- `lmarginal` preserves measurability under sigma-finiteness.
    simpa [f03] using (Measurable.lmarginal (μ := μ4) (s := ({0, 3} : Finset (Fin 4)))
      (hf := measurable_pInd))
  -- Split `{1,2}` into `{1}` then `{2}`, applied to the measurable function `f03`.
  have hsplit12 :
      (∫⋯∫⁻_({1, 2} : Finset (Fin 4)), f03 ∂μ4) =
        ∫⋯∫⁻_({1} : Finset (Fin 4)), (∫⋯∫⁻_({2} : Finset (Fin 4)), f03 ∂μ4) ∂μ4 := by
    have h :=
      (MeasureTheory.lmarginal_union (μ := μ4) (s := ({1} : Finset (Fin 4)))
        (t := ({2} : Finset (Fin 4))) f03 hf03 (by decide))
    have hunion : (({1} : Finset (Fin 4)) ∪ {2}) = ({1, 2} : Finset (Fin 4)) := by
      decide
    simpa [hunion] using h
  have hsplit12_x0 :
      (∫⋯∫⁻_({1, 2} : Finset (Fin 4)), f03 ∂μ4) x0 =
        (∫⋯∫⁻_({1} : Finset (Fin 4)),
              (∫⋯∫⁻_({2} : Finset (Fin 4)), f03 ∂μ4) ∂μ4) x0 := by
    simpa using congrArg (fun g => g x0) hsplit12
  -- Expand the singleton marginals into nested `lintegral`s.
  have hsingleton1 :
      (∫⋯∫⁻_({1} : Finset (Fin 4)),
            (∫⋯∫⁻_({2} : Finset (Fin 4)), f03 ∂μ4) ∂μ4) x0 =
        ∫⁻ b : Rand,
          (∫⋯∫⁻_({2} : Finset (Fin 4)), f03 ∂μ4) (Function.update x0 1 b)
            ∂(volume : Measure Rand) := by
    simp [MeasureTheory.lmarginal_singleton, μ4]
  have hsingleton2 (b : Rand) :
      (∫⋯∫⁻_({2} : Finset (Fin 4)), f03 ∂μ4) (Function.update x0 1 b) =
        ∫⁻ c : Rand, f03 (Function.update (Function.update x0 1 b) 2 c)
          ∂(volume : Measure Rand) := by
    simp [MeasureTheory.lmarginal_singleton, μ4]
  -- Evaluate `f03` using the explicit `{0,3}` computation.
  have hf03_eval (b c : Rand) :
      f03 (Function.update (Function.update x0 1 b) 2 c) = innerBC b c := by
    -- `f03` is the `{0,3}` marginal, and it depends only on indices `1,2`.
    have := lmarginal_AD_eq_innerBC (x := Function.update (Function.update x0 1 b) 2 c)
    -- simplify the coordinates after updates
    simpa [f03, Function.update, innerBC] using this
  -- Put everything together.
  calc
    ClassicalAlgorithm.p recursive3ParamAlg
        = ∫⁻ x : Samples 4, pInd x ∂(Measure.pi μ4) := hp'
    _ = (∫⋯∫⁻_(Finset.univ : Finset (Fin 4)), pInd ∂μ4) x0 := hlm
    _ = (∫⋯∫⁻_({1, 2} : Finset (Fin 4)), f03 ∂μ4) x0 := by
          -- rewrite the inner marginal and use `hsplit_x0`
          simpa [f03] using hsplit_x0
    _ =
        (∫⋯∫⁻_({1} : Finset (Fin 4)),
              (∫⋯∫⁻_({2} : Finset (Fin 4)), f03 ∂μ4) ∂μ4) x0 := hsplit12_x0
    _ = ∫⁻ b : Rand,
          (∫⋯∫⁻_({2} : Finset (Fin 4)), f03 ∂μ4) (Function.update x0 1 b)
            ∂(volume : Measure Rand) := hsingleton1
    _ = ∫⁻ b : Rand,
          (∫⁻ c : Rand, innerBC b c ∂(volume : Measure Rand)) ∂(volume : Measure Rand) := by
          refine MeasureTheory.lintegral_congr_ae ?_
          refine Filter.Eventually.of_forall fun b => ?_
          -- expand the `c`-integral and rewrite the integrand using `hf03_eval`
          have := hsingleton2 b
          simp [this, hf03_eval, f03]
    _ =
        ∫⁻ b : Rand,
          ∫⁻ c : Rand, innerBC b c ∂(volume : Measure Rand) ∂(volume : Measure Rand) := rfl

end Recursive3Param
end UpperBound

end Distributed2Coloring
