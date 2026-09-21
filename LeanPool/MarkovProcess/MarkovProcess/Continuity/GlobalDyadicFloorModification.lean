/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Continuity.ShiftedUnitModification
import Mathlib.Topology.LocallyFinite

/-!
# A global continuous modification assembled from canonical unit paths

The nonnegative real half-line is covered by the closed unit intervals `[n, n + 1]`.  On each
piece we use the canonical dyadic-floor limit of the process shifted by `n`.  Exact endpoint
identities make these pieces compatible, so `Set.liftCover` gives an honest raw global path.
On the simultaneous probability-one event where every canonical unit piece is continuous, local
finiteness of the closed cover makes the raw path continuous.  A single constant global fallback
then gives a total path which is continuous for every sample.

No measurability of the path-valued map, path-space law, Markov property, or Hunt-process claim is
asserted here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The `n`th closed unit interval in `ℝ≥0`. -/
def nnrealUnitInterval (n : ℕ) : Set ℝ≥0 := Set.Icc n (n + 1)

/-- Local coordinate in `[0,1]` on the `n`th closed unit interval. -/
def nnrealUnitCoordinate (n : ℕ) (x : nnrealUnitInterval n) : Set.Icc (0 : ℝ) 1 :=
  ⟨(x.1 : ℝ) - n, by
    constructor
    · exact sub_nonneg.mpr (by exact_mod_cast x.2.1)
    · rw [sub_le_iff_le_add]
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using! x.2.2⟩

/-- The canonical shifted unit path, expressed on the corresponding closed interval of `ℝ≥0`. -/
def globalDyadicFloorPiece (X : NNRat → Ω → E) (ω : Ω) (n : ℕ) :
    nnrealUnitInterval n → E :=
  fun x ↦ shiftedUnitDyadicFloorLimit n X ω (nnrealUnitCoordinate n x)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem continuous_nnrealUnitCoordinate (n : ℕ) : Continuous (nnrealUnitCoordinate n) := by
  apply continuous_induced_rng.2
  exact (NNReal.continuous_coe.comp continuous_subtype_val).sub continuous_const

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Canonical pieces agree wherever two closed unit intervals overlap. -/
theorem globalDyadicFloorPiece_eq_of_mem
    (X : NNRat → Ω → E) (ω : Ω) (n m : ℕ) (x : ℝ≥0)
    (hn : x ∈ nnrealUnitInterval n) (hm : x ∈ nnrealUnitInterval m) :
    globalDyadicFloorPiece X ω n ⟨x, hn⟩ = globalDyadicFloorPiece X ω m ⟨x, hm⟩ := by
  have hnm : n ≤ m + 1 := by exact_mod_cast hn.1.trans hm.2
  have hmn : m ≤ n + 1 := by exact_mod_cast hm.1.trans hn.2
  by_cases heq : n = m
  · subst m
    rfl
  by_cases hlt : n < m
  · have hmn' : m = n + 1 := by omega
    subst m
    have hmleft : (n : ℝ≥0) + 1 ≤ x := by
      simpa only [Nat.cast_add, Nat.cast_one] using hm.1
    have hx : x = (n : ℝ≥0) + 1 := le_antisymm hn.2 hmleft
    subst x
    have hleft : nnrealUnitCoordinate n ⟨(n + 1 : ℝ≥0), hn⟩ =
        (1 : Set.Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      norm_num [nnrealUnitCoordinate]
    have hright : nnrealUnitCoordinate (n + 1) ⟨(n + 1 : ℝ≥0), hm⟩ =
        (0 : Set.Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      norm_num [nnrealUnitCoordinate]
    rw [globalDyadicFloorPiece, globalDyadicFloorPiece, hleft, hright,
      shiftedUnitDyadicFloorLimit_one, shiftedUnitDyadicFloorLimit_zero]
    simp only [Nat.cast_add, Nat.cast_one]
  · have hnm' : n = m + 1 := by omega
    subst n
    exact (globalDyadicFloorPiece_eq_of_mem X ω m (m + 1) x hm hn).symm

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The closed unit intervals cover `ℝ≥0`. -/
theorem iUnion_nnrealUnitInterval : ⋃ n : ℕ, nnrealUnitInterval n = Set.univ := by
  apply Set.iUnion_eq_univ_iff.2
  intro x
  let n := ⌊(x : ℝ)⌋₊
  refine ⟨n, ?_⟩
  constructor
  · exact_mod_cast Nat.floor_le x.2
  · exact_mod_cast (Nat.lt_floor_add_one (x : ℝ)).le

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The cover of `ℝ≥0` by closed unit intervals is locally finite. -/
theorem locallyFinite_nnrealUnitInterval : LocallyFinite nnrealUnitInterval := by
  intro x
  let N := ⌊(x : ℝ)⌋₊ + 2
  refine ⟨Set.Iio (N : ℝ≥0), ?_, ?_⟩
  · apply Iio_mem_nhds
    have hxlt : (x : ℝ) < (N : ℕ) := by
      calc
        (x : ℝ) < ⌊(x : ℝ)⌋₊ + 1 := Nat.lt_floor_add_one (x : ℝ)
        _ < (N : ℕ) := by simp only [N]; norm_num
    exact_mod_cast hxlt
  · apply Set.Finite.subset (Set.finite_Iio N)
    intro n hn
    obtain ⟨y, hy, hyN⟩ := hn
    have hny : (n : ℝ≥0) ≤ y := hy.1
    have hnN : n < N := by exact_mod_cast hny.trans_lt hyN
    exact hnN

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The raw global path obtained by gluing the compatible canonical unit pieces. -/
def globalDyadicFloorLimit (X : NNRat → Ω → E) (ω : Ω) : ℝ≥0 → E :=
  Set.liftCover nnrealUnitInterval (globalDyadicFloorPiece X ω)
    (globalDyadicFloorPiece_eq_of_mem X ω) iUnion_nnrealUnitInterval

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
@[simp]
theorem globalDyadicFloorLimit_coe
    (X : NNRat → Ω → E) (ω : Ω) (n : ℕ) (x : nnrealUnitInterval n) :
    globalDyadicFloorLimit X ω x = globalDyadicFloorPiece X ω n x :=
  Set.liftCover_coe x

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- If every canonical unit piece is continuous, then the raw global path is continuous. -/
theorem continuous_globalDyadicFloorLimit_of_forall
    {X : NNRat → Ω → E} {ω : Ω}
    (h : ∀ n : ℕ, Continuous (shiftedUnitDyadicFloorLimit n X ω)) :
    Continuous (globalDyadicFloorLimit X ω) := by
  apply locallyFinite_nnrealUnitInterval.continuous iUnion_nnrealUnitInterval
  · exact fun n ↦ isClosed_Icc
  · intro n
    rw [continuousOn_iff_continuous_domRestrict]
    have hpiece : Continuous (globalDyadicFloorPiece X ω n) :=
      (h n).comp (continuous_nnrealUnitCoordinate n)
    apply hpiece.congr
    intro x
    simpa only [Set.domRestrict_apply] using (globalDyadicFloorLimit_coe X ω n x).symm

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Almost surely, all natural-shift canonical pieces are simultaneously continuous. -/
theorem IsKolmogorovProcess.ae_forall_continuous_shiftedUnitDyadicFloorLimit
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, Continuous (shiftedUnitDyadicFloorLimit n X ω) := by
  rw [ae_all_iff]
  intro n
  simpa only [shiftedUnitDyadicFloorLimit] using
    IsKolmogorovProcess.ae_continuous_unitDyadicFloorLimit
      (IsKolmogorovProcess.timeShift hX n) hγ hγq

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Almost surely, the raw global dyadic-floor path is continuous. -/
theorem IsKolmogorovProcess.ae_continuous_globalDyadicFloorLimit
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, Continuous (globalDyadicFloorLimit X ω) := by
  filter_upwards
    [IsKolmogorovProcess.ae_forall_continuous_shiftedUnitDyadicFloorLimit hX hγ hγq]
      with ω hω
  exact continuous_globalDyadicFloorLimit_of_forall hω

/-- A single global totalization: keep the raw path when it is continuous and otherwise use the
constant initial sample on the whole half-line. -/
def continuousGlobalDyadicFloorLimit (X : NNRat → Ω → E) (ω : Ω) : ℝ≥0 → E := by
  classical
  exact if Continuous (globalDyadicFloorLimit X ω) then globalDyadicFloorLimit X ω
    else fun _ ↦ X 0 ω

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The globally totalized path is continuous for every sample. -/
theorem continuous_continuousGlobalDyadicFloorLimit
    (X : NNRat → Ω → E) (ω : Ω) :
    Continuous (continuousGlobalDyadicFloorLimit X ω) := by
  by_cases h : Continuous (globalDyadicFloorLimit X ω)
  · simpa only [continuousGlobalDyadicFloorLimit, if_pos h] using h
  · simp only [continuousGlobalDyadicFloorLimit, if_neg h]
    exact continuous_const

/-- At a fixed rational time written as a natural shift plus a local time in `[0,1]`, the
globally totalized continuous path is a modification of the original process. -/
theorem IsKolmogorovProcess.ae_eq_continuousGlobalDyadicFloorLimit_nat_add
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) (n : ℕ) (t : NNRat) (ht : t ≤ 1) :
    X (n + t) =ᵐ[P] fun ω ↦
      continuousGlobalDyadicFloorLimit X ω (↑((n : NNRat) + t) : ℝ≥0) := by
  let x : ℝ≥0 := ↑((n : NNRat) + t)
  have hx : x ∈ nnrealUnitInterval n := by
    have hl : (n : NNRat) ≤ (n : NNRat) + t := le_add_of_nonneg_right t.2
    have hu : (n : NNRat) + t ≤ (n : NNRat) + 1 := by
      simpa only [add_comm] using add_le_add_left ht (n : NNRat)
    constructor
    · dsimp only [x]
      exact_mod_cast hl
    · dsimp only [x]
      exact_mod_cast hu
  have hcoord : nnrealUnitCoordinate n ⟨x, hx⟩ = unitIccOfNNRat t ht := by
    apply Subtype.ext
    simp only [nnrealUnitCoordinate, unitIccOfNNRat_val, x]
    push_cast
    ring_nf
    change (((t : NNRat) : ℝ≥0) : ℝ) = (t : ℝ)
    exact_mod_cast rfl
  filter_upwards
    [IsKolmogorovProcess.ae_eq_unitDyadicFloorLimit
      (IsKolmogorovProcess.timeShift hX n) hγ hγq t ht,
      IsKolmogorovProcess.ae_continuous_globalDyadicFloorLimit hX hγ hγq]
      with ω hident hcont
  rw [continuousGlobalDyadicFloorLimit, if_pos hcont]
  rw [show (↑((n : NNRat) + t) : ℝ≥0) = x by rfl,
    globalDyadicFloorLimit_coe X ω n ⟨x, hx⟩, globalDyadicFloorPiece, hcoord]
  simpa only [timeShift_apply] using! hident

/-- The natural part of a nonnegative rational time. -/
def nnratNatFloor (t : NNRat) : ℕ := ⌊(t : ℝ)⌋₊

/-- The unit-interval remainder of a nonnegative rational time. -/
def nnratUnitRemainder (t : NNRat) : NNRat := t - nnratNatFloor t

theorem nnratNatFloor_le (t : NNRat) : (nnratNatFloor t : NNRat) ≤ t := by
  unfold nnratNatFloor
  exact_mod_cast Nat.floor_le (show 0 ≤ (t : ℝ) by positivity)

theorem nnratNatFloor_add_unitRemainder (t : NNRat) :
    (nnratNatFloor t : NNRat) + nnratUnitRemainder t = t := by
  exact add_tsub_cancel_of_le (nnratNatFloor_le t)

theorem nnratUnitRemainder_le_one (t : NNRat) : nnratUnitRemainder t ≤ 1 := by
  apply le_of_lt
  rw [nnratUnitRemainder, tsub_lt_iff_left (nnratNatFloor_le t)]
  unfold nnratNatFloor
  exact_mod_cast Nat.lt_floor_add_one (t : ℝ)

/-- At every fixed nonnegative rational time, the globally totalized continuous path is a
modification of the original process. -/
theorem IsKolmogorovProcess.ae_eq_continuousGlobalDyadicFloorLimit
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) (t : NNRat) :
    X t =ᵐ[P] fun ω ↦ continuousGlobalDyadicFloorLimit X ω (t : ℝ≥0) := by
  have hdecomp := nnratNatFloor_add_unitRemainder t
  simpa only [hdecomp] using
    IsKolmogorovProcess.ae_eq_continuousGlobalDyadicFloorLimit_nat_add
      hX hγ hγq (nnratNatFloor t) (nnratUnitRemainder t) (nnratUnitRemainder_le_one t)

end

end MarkovProcess
