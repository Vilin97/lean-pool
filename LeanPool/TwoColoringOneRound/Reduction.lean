/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.Definitions
import LeanPool.TwoColoringOneRound.LowerBound.Defs
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Main
import LeanPool.TwoColoringOneRound.UpperBound.Recursive3Param.Final
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Reduction: local rules → finite coloring bound

This file formalizes the bridge in `theory/report/manuscript.tex`,
Section "A reduction to an extremal digraph problem":

* a measurable `ClassicalAlgorithm` induces (from i.i.d. seeds) a random `Coloring n` of the
  finite digraph `G_n` from `Distributed2Coloring.LowerBound.Defs`,
* the local monochromatic-edge probability `ClassicalAlgorithm.p` is the expectation of the
  monochromatic-edge fraction `monoFraction` of that induced coloring,
* hence any certified lower bound on `monoFraction` transfers to a lower bound on `p`.

We use the already-formalized certified bound at `n = 1_000_000` to conclude
`0.23879 ≤ p` for all `ClassicalAlgorithm`s (we use `≤` rather than `<` throughout), and the
already-formalized explicit construction to
conclude `p ≤ 0.24118` for some `ClassicalAlgorithm`.
-/

namespace Distributed2Coloring

open MeasureTheory
open scoped unitInterval BigOperators

namespace Reduction

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n1000000 : ℕ := LowerBound.N1000000.n

/-- Convert `Fin 2` colors to `Bool`. -/
def colorToBool : Color → Bool := finTwoEquiv

lemma colorToBool_injective : Function.Injective colorToBool :=
  finTwoEquiv.injective

/-- The deterministic `LowerBound.Coloring n` induced by a seed assignment `S : Fin n → [0,1]`. -/
def coloringOfSeeds {n : ℕ} (alg : ClassicalAlgorithm) (S : Samples n) : LowerBound.Coloring n :=
  fun v =>
    colorToBool
      (alg.f (S (LowerBound.Vertex.a v), S (LowerBound.Vertex.b v), S (LowerBound.Vertex.c v)))

/-- Pick out the 4 coordinates of a seed assignment indexed by an embedding. -/
def pick4 {n : ℕ} (emb : Fin 4 ↪ Fin n) : Samples n → Samples 4 :=
  fun S i => S (emb i)

lemma measurable_pick4 {n : ℕ} (emb : Fin 4 ↪ Fin n) : Measurable (pick4 emb) := by
  classical
  rw [measurable_pi_iff]
  exact fun i => by simpa [pick4] using (measurable_pi_apply (emb i))

lemma measurePreserving_pick4 {n : ℕ} (emb : Fin 4 ↪ Fin n) :
    MeasurePreserving
      (pick4 emb)
      (volume : Measure (Samples n))
      (volume : Measure (Samples 4)) := by
  classical
  let f : Fin 4 → Fin n := fun i => emb i
  let p : Fin n → Prop := fun j => j ∈ Set.range f
  haveI : DecidablePred p := Classical.decPred _
  -- Avoid using the `Set.range`-specialized fintype instance: use the default one for subtypes.
  -- This keeps definitional equalities for `volume` / product measures stable.
  letI : Fintype (Subtype p) := Subtype.fintype p
  -- Split `Samples n` into the coordinates in `range f` and its complement.
  let eSplit :
      Samples n ≃ᵐ (∀ i : { j // p j }, Rand) × ∀ i : { j // ¬ p j }, Rand :=
    MeasurableEquiv.piEquivPiSubtypeProd (π := fun _ : Fin n => Rand) p
  have hSplit : MeasurePreserving eSplit (volume : Measure (Samples n)) (volume : Measure _) := by
    simpa [eSplit] using
      (MeasureTheory.volume_preserving_piEquivPiSubtypeProd (α := fun _ : Fin n => Rand) p)
  have hFst :
      MeasurePreserving
        Prod.fst
        (volume :
          Measure ((∀ i : { j // p j }, Rand) × ∀ i : { j // ¬ p j }, Rand))
        (volume : Measure (∀ i : { j // p j }, Rand)) := by
    simpa [MeasureSpace.volume] using
      (MeasureTheory.measurePreserving_fst
        (μ := (volume : Measure (∀ i : { j // p j }, Rand)))
        (ν := (volume : Measure (∀ i : { j // ¬ p j }, Rand))))
  -- Reindex the `range f` coordinates by `Fin 4`.
  let eRange : Fin 4 ≃ { j : Fin n // p j } :=
    Equiv.ofInjective f emb.injective
  let eCongr : (∀ i : { j : Fin n // p j }, Rand) ≃ᵐ Samples 4 :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => Rand) eRange.symm
  have hCongr :
      MeasurePreserving eCongr (volume : Measure (∀ i : { j : Fin n // p j }, Rand))
        (volume : Measure (Samples 4)) := by
    simpa [eCongr] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (α := fun _ : Fin 4 => Rand)
        (f := eRange.symm))
  have hcomp : (fun S : Samples n => eCongr (Prod.fst (eSplit S))) = pick4 emb := by
    funext S i
    -- `eSplit` is restriction to subtypes (`Equiv.piEquivPiSubtypeProd`);
    -- `eCongr` is reindexing along `eRange.symm` (`Equiv.piCongrLeft`).
    simp [eSplit, eCongr, eRange, pick4, f, p, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft]
  have :
      MeasurePreserving (fun S : Samples n => eCongr (Prod.fst (eSplit S)))
        (volume : Measure (Samples n)) (volume : Measure (Samples 4)) :=
    hCongr.comp (hFst.comp hSplit)
  simpa [hcomp] using this

/-- The `pEvent` pulled back along the coordinates of an injective `4`-tuple. -/
def edgeEvent (alg : ClassicalAlgorithm) {n : ℕ} (e : LowerBound.Edge n) : Set (Samples n) :=
  (pick4 ⟨e.1, e.2⟩) ⁻¹' ClassicalAlgorithm.pEvent alg

lemma measurableSet_edgeEvent (alg : ClassicalAlgorithm) {n : ℕ} (e : LowerBound.Edge n) :
    MeasurableSet (edgeEvent alg e) := by
  classical
  simpa [edgeEvent] using
    (ClassicalAlgorithm.measurableSet_pEvent alg).preimage
      (measurable_pick4 (n := n) ⟨e.1, e.2⟩)

lemma edgeEvent_measure_eq_p (alg : ClassicalAlgorithm) {n : ℕ} (e : LowerBound.Edge n) :
    (volume : Measure (Samples n)) (edgeEvent alg e) = ClassicalAlgorithm.p alg := by
  classical
  have hmp :
      MeasurePreserving (pick4 (n := n) ⟨e.1, e.2⟩)
        (volume : Measure (Samples n)) (volume : Measure (Samples 4)) :=
    measurePreserving_pick4 (n := n) ⟨e.1, e.2⟩
  have hnull :
      NullMeasurableSet (ClassicalAlgorithm.pEvent alg) (volume : Measure (Samples 4)) :=
    (ClassicalAlgorithm.measurableSet_pEvent alg).nullMeasurableSet
  simpa [edgeEvent, ClassicalAlgorithm.p] using
    hmp.measure_preimage (s := ClassicalAlgorithm.pEvent alg) hnull

lemma edgeMonochromatic_iff {n : ℕ} (alg : ClassicalAlgorithm) (S : Samples n)
    (e : LowerBound.Edge n) :
    LowerBound.Edge.monochromatic (coloringOfSeeds alg S) e ↔ S ∈ edgeEvent alg e := by
  classical
  have hinj : Function.Injective colorToBool := colorToBool_injective
  let srcT : Rand × Rand × Rand :=
    (S (LowerBound.Vertex.a (LowerBound.Edge.src e)),
      S (LowerBound.Vertex.b (LowerBound.Edge.src e)),
      S (LowerBound.Vertex.c (LowerBound.Edge.src e)))
  let dstT : Rand × Rand × Rand :=
    (S (LowerBound.Vertex.a (LowerBound.Edge.dst e)),
      S (LowerBound.Vertex.b (LowerBound.Edge.dst e)),
      S (LowerBound.Vertex.c (LowerBound.Edge.dst e)))
  have hrew :
      (pick4 (n := n) ⟨e.1, e.2⟩ S) ∈ ClassicalAlgorithm.pEvent alg ↔ alg.f srcT = alg.f dstT := by
    -- `Edge.src` uses indices `0,1,2`; `Edge.dst` uses indices `1,2,3`.
    simp
      [ ClassicalAlgorithm.pEvent
      , pick4
      , srcT
      , dstT
      , LowerBound.Edge.src
      , LowerBound.Edge.dst
      , LowerBound.Edge.srcIndex
      , LowerBound.Edge.dstIndex
      , LowerBound.Vertex.a
      , LowerBound.Vertex.b
      , LowerBound.Vertex.c
      ]
  constructor
  · intro h
    have hEq : alg.f srcT = alg.f dstT := hinj
      (by simpa [LowerBound.Edge.monochromatic, coloringOfSeeds, colorToBool, srcT, dstT] using h)
    simpa [edgeEvent] using (hrew).2 hEq
  · intro h
    have hEq : alg.f srcT = alg.f dstT := (hrew).1 (by simpa [edgeEvent] using h)
    simp [LowerBound.Edge.monochromatic, coloringOfSeeds, colorToBool, srcT, dstT, hEq]

/-!
Instead of directly identifying `p alg` with the expectation of the *fraction*
`monoFraction (coloringOfSeeds alg S)`, we work with the (Nat-valued) count `monoCount`.

This avoids casting/division lemmas for `ENNReal.ofReal` that can lead to kernel-recursion issues
when `n` is very large (here `n = 1_000_000`).
-/

lemma monoCount_eq_sum_edgeEvent_indicator {n : ℕ} (alg : ClassicalAlgorithm) (S : Samples n) :
    (LowerBound.monoCount (coloringOfSeeds alg S) : ENNReal) =
      (Finset.univ : Finset (LowerBound.Edge n)).sum (fun e =>
        (edgeEvent alg e).indicator (fun _ => (1 : ENNReal)) S) := by
  classical
  -- `monoCount` is the cardinality of the filtered finset of monochromatic edges, which
  -- `Finset.natCast_card_filter` expresses as a sum of `0/1`-indicators in `ENNReal`.
  have hcard :
      (LowerBound.monoCount (coloringOfSeeds alg S) : ENNReal) =
        (Finset.univ : Finset (LowerBound.Edge n)).sum (fun e =>
          if LowerBound.Edge.monochromatic (coloringOfSeeds alg S) e then (1 : ENNReal) else
            0) := by
    unfold LowerBound.monoCount LowerBound.monoEdges
    exact Finset.natCast_card_filter (R := ENNReal)
      (s := (Finset.univ : Finset (LowerBound.Edge n)))
      (p := LowerBound.Edge.monochromatic (coloringOfSeeds alg S))
  refine hcard.trans (Finset.sum_congr rfl fun e _ => ?_)
  by_cases hme : LowerBound.Edge.monochromatic (coloringOfSeeds alg S) e
  · simp [hme, Set.indicator_of_mem, (edgeMonochromatic_iff (alg := alg) S e).1 hme]
  · have : S ∉ edgeEvent alg e :=
      fun hs => hme ((edgeMonochromatic_iff (alg := alg) S e).2 hs)
    simp [hme, Set.indicator_of_notMem, this]

lemma lintegral_monoCount_eq_edgeCount_mul_p {n : ℕ} (_hn : 4 ≤ n) (alg : ClassicalAlgorithm) :
    (∫⁻ S : Samples n, (LowerBound.monoCount (coloringOfSeeds alg S) : ENNReal)) =
      (LowerBound.edgeCount n : ENNReal) * ClassicalAlgorithm.p alg := by
  classical
  have hrewrite :
      (∫⁻ S : Samples n, (LowerBound.monoCount (coloringOfSeeds alg S) : ENNReal)) =
        ∫⁻ S : Samples n,
          (Finset.univ : Finset (LowerBound.Edge n)).sum (fun e =>
            (edgeEvent alg e).indicator (fun _ => (1 : ENNReal)) S) := by
    exact MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall
      fun S => monoCount_eq_sum_edgeEvent_indicator (alg := alg) S)
  rw [hrewrite]
  -- Pull out the constant factor.
  have hmeas (e : LowerBound.Edge n) :
      Measurable fun S : Samples n => (edgeEvent alg e).indicator (fun _ => (1 : ENNReal)) S :=
    measurable_const.indicator (measurableSet_edgeEvent (alg := alg) e)
  calc
    (∫⁻ S : Samples n,
        (Finset.univ : Finset (LowerBound.Edge n)).sum (fun e =>
          (edgeEvent alg e).indicator (fun _ => (1 : ENNReal)) S)) =
        (Finset.univ : Finset (LowerBound.Edge n)).sum (fun e =>
          (volume : Measure (Samples n)) (edgeEvent alg e)) := by
      -- Swap `lintegral` and finite sum, and evaluate each term as a set measure.
      rw [MeasureTheory.lintegral_finsetSum (μ := (volume : Measure (Samples n)))
        (s := (Finset.univ : Finset (LowerBound.Edge n)))
        (f := fun e S => (edgeEvent alg e).indicator (fun _ => (1 : ENNReal)) S)
        (fun e _he => hmeas e)]
      exact Finset.sum_congr rfl fun e _ =>
        MeasureTheory.lintegral_indicator_one (μ := (volume : Measure (Samples n)))
          (measurableSet_edgeEvent (alg := alg) e)
    _ =
        (Finset.univ : Finset (LowerBound.Edge n)).sum (fun _e => ClassicalAlgorithm.p alg) := by
      exact Finset.sum_congr rfl fun e _ => edgeEvent_measure_eq_p (alg := alg) (e := e)
    _ =
        (LowerBound.edgeCount n : ENNReal) * ClassicalAlgorithm.p alg := by
      -- Sum of a constant over a finite type equals `card * constant`.
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      rfl

theorem p_ge_23879 (alg : ClassicalAlgorithm) :
    ENNReal.ofReal (23879 / 100000 : ℝ) ≤ ClassicalAlgorithm.p alg := by
  classical
  have hn : 4 ≤ n1000000 := by
    dsimp [n1000000, LowerBound.N1000000.n, LowerBound.N1000000Data.n]
    omega
  have hedgeCount_pos : 0 < LowerBound.edgeCount n1000000 := by
    refine Fintype.card_pos_iff.2 ⟨⟨fun i => ⟨i.1, lt_of_lt_of_le i.2 hn⟩, fun i j hij => ?_⟩⟩
    exact Fin.ext (congrArg (fun x : Fin n1000000 => x.1) hij)
  have hedgeCount_ne_zero : (LowerBound.edgeCount n1000000 : ENNReal) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.ne_of_gt hedgeCount_pos)
  have hedgeCount_ne_top : (LowerBound.edgeCount n1000000 : ENNReal) ≠ (⊤ : ENNReal) :=
    ENNReal.natCast_ne_top _
  have hedgeCount_pos_q : (0 : ℚ) < (LowerBound.edgeCount n1000000 : ℚ) := by
    exact_mod_cast hedgeCount_pos
  -- Pointwise, apply the certified finite bound to the induced coloring and clear the division.
  have hpointwiseQ (S : Samples n1000000) :
      ((23879 : ℚ) / 100000) * (LowerBound.edgeCount n1000000 : ℚ) ≤
        (LowerBound.monoCount (coloringOfSeeds (n := n1000000) alg S) : ℚ) := by
    have hb :
        ((23879 : ℚ) / 100000) ≤
          LowerBound.monoFraction (coloringOfSeeds (n := n1000000) alg S) :=
      LowerBound.N1000000.monoFraction_ge_23879 (f := coloringOfSeeds (n := n1000000) alg S)
    dsimp [LowerBound.monoFraction] at hb
    exact (le_div_iff₀ hedgeCount_pos_q).1 hb
  -- Convert pointwise bound to an `ENNReal` inequality.
  have hpointwiseENN (S : Samples n1000000) :
      ENNReal.ofReal (((23879 : ℝ) / 100000) * (LowerBound.edgeCount n1000000 : ℝ)) ≤
        (LowerBound.monoCount (coloringOfSeeds (n := n1000000) alg S) : ENNReal) := by
    have hr :
        ((((23879 : ℚ) / 100000) * (LowerBound.edgeCount n1000000 : ℚ) : ℝ)) ≤
          (LowerBound.monoCount (coloringOfSeeds (n := n1000000) alg S) : ℝ) := by
      exact_mod_cast hpointwiseQ S
    have hENN := ENNReal.ofReal_le_ofReal hr
    rwa [show (((((23879 : ℚ) / 100000) * (LowerBound.edgeCount n1000000 : ℚ)) : ℝ)) =
        ((23879 : ℝ) / 100000) * (LowerBound.edgeCount n1000000 : ℝ) from rfl,
      ENNReal.ofReal_natCast] at hENN
  -- Integrate the pointwise inequality and evaluate the `monoCount` integral.
  have hint :
      ENNReal.ofReal (((23879 : ℝ) / 100000) * (LowerBound.edgeCount n1000000 : ℝ)) ≤
        ∫⁻ S : Samples n1000000,
          (LowerBound.monoCount (coloringOfSeeds (n := n1000000) alg S) : ENNReal) := by
    simpa only [lintegral_const, measure_univ, mul_one] using
      lintegral_mono (μ := (volume : Measure (Samples n1000000))) fun S => hpointwiseENN S
  have hcalc :
      (∫⁻ S : Samples n1000000,
          (LowerBound.monoCount (coloringOfSeeds (n := n1000000) alg S) : ENNReal)) =
        (LowerBound.edgeCount n1000000 : ENNReal) * ClassicalAlgorithm.p alg :=
    lintegral_monoCount_eq_edgeCount_mul_p (n := n1000000) hn alg
  have hbound :
      ENNReal.ofReal (((23879 : ℝ) / 100000) * (LowerBound.edgeCount n1000000 : ℝ)) ≤
        (LowerBound.edgeCount n1000000 : ENNReal) * ClassicalAlgorithm.p alg := by
    rwa [hcalc] at hint
  -- Rewrite the left side as `edgeCount * 0.23879` and cancel `edgeCount`.
  have hleft :
      ENNReal.ofReal (((23879 : ℝ) / 100000) * (LowerBound.edgeCount n1000000 : ℝ)) =
        (LowerBound.edgeCount n1000000 : ENNReal) * ENNReal.ofReal ((23879 : ℝ) / 100000) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_comm]
  have hbound' :
      (LowerBound.edgeCount n1000000 : ENNReal) * ENNReal.ofReal ((23879 : ℝ) / 100000) ≤
        (LowerBound.edgeCount n1000000 : ENNReal) * ClassicalAlgorithm.p alg := by
    rwa [hleft] at hbound
  -- Cancel the common positive, finite factor `edgeCount`.
  rw [mul_comm _ (ENNReal.ofReal _), mul_comm _ (ClassicalAlgorithm.p alg)] at hbound'
  exact (ENNReal.mul_le_mul_iff_left hedgeCount_ne_zero hedgeCount_ne_top).1 hbound'

theorem exists_algorithm_p_le_24118 :
    ∃ alg : ClassicalAlgorithm, ClassicalAlgorithm.p alg ≤ ENNReal.ofReal (24118 / 100000 : ℝ) := by
  rcases UpperBound.Recursive3Param.exists_algorithm_p_lt with ⟨alg, hlt⟩
  exact ⟨alg, le_of_lt hlt⟩

end Reduction

/-- Certified lower bound: every one-round `ClassicalAlgorithm` satisfies `0.23879 ≤ p`. -/
theorem p_ge_23879 (alg : ClassicalAlgorithm) :
    ENNReal.ofReal (23879 / 100000 : ℝ) ≤ ClassicalAlgorithm.p alg :=
  Reduction.p_ge_23879 alg

/-- A one-round `ClassicalAlgorithm` exists with `p ≤ 0.24118`. -/
theorem exists_algorithm_p_le_24118 :
    ∃ alg : ClassicalAlgorithm, ClassicalAlgorithm.p alg ≤ ENNReal.ofReal (24118 / 100000 : ℝ) :=
  Reduction.exists_algorithm_p_le_24118

end Distributed2Coloring
