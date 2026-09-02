/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import LeanPool.CommonNeighbourConjecture.Examples.EveryBase.Main
import LeanPool.CommonNeighbourConjecture.Examples.MainTheorems.Definitions
import LeanPool.CommonNeighbourConjecture.Saxl.Generalized

/-!
# Internal implementation of the main theorem

Construction parameters, bridge lemmas, and proof machinery used by the
minimal public module `Examples.MainTheorems`.
-/

noncomputable section

namespace SaxlCounterexamples.MainTheorems.Internal

open Core Core.FinitePermutationGroup

private theorem isBase_range_iff_isBaseTuple
    (P : FinitePermutationGroup) {n : Nat} (b : Fin n → P.Point) :
    P.IsBase (Set.range b) ↔ Saxl.IsBaseTuple P.G P.Point b := by
  constructor
  · intro h g hg
    apply h g
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact hg i
  · intro h g hg
    apply h g
    intro i
    exact hg (b i) ⟨i, rfl⟩

private theorem baseSize_eq_of_exactBaseSize
    (P : FinitePermutationGroup) {n : Nat}
    (h : Saxl.ExactBaseSize P.G P.Point n) : P.baseSize = n := by
  let sizes : Set Nat :=
    {m : Nat | ∃ b : Fin m → P.Point,
      Function.Injective b ∧ P.IsBase (Set.range b)}
  have hn : n ∈ sizes := by
    obtain ⟨b, hinj, hbase⟩ := h.1
    exact ⟨b, hinj, (isBase_range_iff_isBaseTuple P b).2 hbase⟩
  change sInf sizes = n
  apply le_antisymm (Nat.sInf_le hn)
  by_contra hle
  have hlt : sInf sizes < n := Nat.lt_of_not_ge hle
  obtain ⟨b, hinj, hbase⟩ := Nat.sInf_mem (⟨n, hn⟩ : sizes.Nonempty)
  exact h.2 (sInf sizes) hlt
    ⟨b, hinj, (isBase_range_iff_isBaseTuple P b).1 hbase⟩

private theorem faithfulSMul_of_exactBaseSize
    {G Ω : Type} [Group G] [MulAction G Ω] {n : Nat}
    (h : Saxl.ExactBaseSize G Ω n) : FaithfulSMul G Ω := by
  rw [faithfulSMul_iff]
  intro g hfix
  obtain ⟨b, _hinj, hbase⟩ := h.1
  exact hbase g (fun i ↦ hfix (b i))

private theorem saxlGraph_adj_iff_generalizedAdjacent
    (P : FinitePermutationGroup) (tail : Nat)
    (hsize : P.baseSize = tail + 2) (x y : P.Point) :
    P.saxlGraph.Adj x y ↔
      Saxl.GeneralizedAdjacent P.G P.Point tail x y := by
  change
    (x ≠ y ∧ ∃ b : Fin P.baseSize → P.Point,
      Function.Injective b ∧ P.IsBase (Set.range b) ∧
        x ∈ Set.range b ∧ y ∈ Set.range b) ↔ _
  rw [hsize, Saxl.generalizedAdjacent_iff_mem_base]
  constructor
  · rintro ⟨hxy, b, hinj, hbase, hx, hy⟩
    exact ⟨hxy, b, ⟨hinj, (isBase_range_iff_isBaseTuple P b).1 hbase⟩,
      hx, hy⟩
  · rintro ⟨hxy, b, ⟨hinj, hbase⟩, hx, hy⟩
    exact ⟨hxy, b, hinj, (isBase_range_iff_isBaseTuple P b).2 hbase,
      hx, hy⟩

private theorem pointDegrees_unbounded (tail degreeBound : Nat) :
    ∃ (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d),
      degreeBound <
        Nat.card (EveryBase.HqProductModule d hd hd3 tail) := by
  let d := 2 * degreeBound + 3
  have hd : Odd d := by
    refine ⟨degreeBound + 1, ?_⟩
    simp [d]
    omega
  have hd3 : 3 ≤ d := by simp [d]
  have hbound : degreeBound ≤ 3 ^ d - 1 := by
    have hp : 1 + d * (3 - 1) ≤ 3 ^ d := by
      simpa using
        (one_add_le_pow_of_two_add_nonneg
          (R := Nat) (a := 2) (by omega) d)
    omega
  have hpow : 2 ^ degreeBound ≤ 2 ^ (3 ^ d - 1) :=
    Nat.pow_le_pow_right (by omega) hbound
  refine ⟨d, hd, hd3, degreeBound.lt_two_pow_self.trans_le (hpow.trans ?_)⟩
  rw [← EveryBase.vq_card d hd]
  exact EveryBase.vq_card_le_productModule_card d hd hd3 tail

private theorem hqBadVector_ne_zero
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :
    EveryBase.hqBadVector d hd hd3 tail ≠ 0 := by
  classical
  let c0 : EveryBase.HqColourType d hd hd3 tail :=
    EveryBase.hqFirstColour d hd hd3 tail
  have hbad_at :
      EveryBase.hqBadVector d hd hd3 tail c0 =
        EveryBase.hqBadSeedVector d hd := by
    change
      EveryBase.badVector (EveryBase.hqSeed d hd hd3)
          (EveryBase.hqColours d hd hd3 tail) c0 c0 =
        EveryBase.hqBadSeedVector d hd
    rw [EveryBase.badVector_at]
    rfl
  have hseed_ne_zero : EveryBase.hqBadSeedVector d hd ≠ 0 := by
    change (EveryBase.hqSeed d hd hd3).u ≠ 0
    simpa using
      (EveryBase.u_ne_add_smul (EveryBase.hqSeed d hd hd3)
        (1 : (EveryBase.hqSeed d hd hd3).H)
        (0 : (EveryBase.hqSeed d hd hd3).V))
  intro hbad
  apply hseed_ne_zero
  have hat : EveryBase.hqBadVector d hd hd3 tail c0 =
      (0 : EveryBase.Vq d) := by
    simpa using congrFun hbad c0
  rw [hbad_at] at hat
  exact hat

private theorem familyFacts
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) (tail : Nat) :
    ∃ P : FinitePermutationGroup,
      Nat.card P.Point =
          Nat.card (EveryBase.HqProductModule d hd hd3 tail) ∧
        MulAction.IsPreprimitive P.G P.Point ∧
        P.baseSize = tail + 2 ∧
        ∃ x y : P.Point, x ≠ y ∧
          (tail = 0 → ¬ P.saxlGraph.Adj x y) ∧
          P.saxlGraph.commonNeighbors x y = ∅ := by
  have hcore := EveryBase.hq_coreFamily d hd hd3 tail
  let _ : FaithfulSMul
      (EveryBase.GBd d hd hd3 tail)
      (EveryBase.HqProductModule d hd hd3 tail) :=
    faithfulSMul_of_exactBaseSize hcore.1
  let _ : Finite (EveryBase.GBd d hd hd3 tail) :=
    Finite.of_injective
      (MulAction.toPerm : EveryBase.GBd d hd hd3 tail →
        Equiv.Perm (EveryBase.HqProductModule d hd hd3 tail))
      MulAction.toPerm_injective
  let P : FinitePermutationGroup := {
    G := EveryBase.GBd d hd hd3 tail
    Point := EveryBase.HqProductModule d hd hd3 tail }
  have hsize : P.baseSize = tail + 2 :=
    baseSize_eq_of_exactBaseSize P (by simpa [P] using hcore.1)
  have hcommon :
      P.saxlGraph.commonNeighbors
          0 (EveryBase.hqBadVector d hd hd3 tail) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro z hz
    rw [SimpleGraph.mem_commonNeighbors] at hz
    apply hcore.2.2
    refine ⟨z, ?_, ?_⟩
    · exact (saxlGraph_adj_iff_generalizedAdjacent
        P tail hsize 0 z).1 hz.1
    · exact (saxlGraph_adj_iff_generalizedAdjacent
        P tail hsize z (EveryBase.hqBadVector d hd hd3 tail)).1
          hz.2.symm
  have hnonadj : tail = 0 →
      ¬ P.saxlGraph.Adj 0 (EveryBase.hqBadVector d hd hd3 tail) := by
    intro htail hadj
    subst tail
    apply EveryBase.hq_zero_not_generalizedAdjacent_badVector d hd hd3
    exact (saxlGraph_adj_iff_generalizedAdjacent
      P 0 hsize 0 (EveryBase.hqBadVector d hd hd3 0)).1 hadj
  refine ⟨P, rfl, ?_, hsize,
    0, EveryBase.hqBadVector d hd hd3 tail, ?_, hnonadj, hcommon⟩
  · simpa [P] using hcore.2.1
  · simpa [P] using (hqBadVector_ne_zero d hd hd3 tail).symm

/-- In a generalised Saxl graph at base size at least three, adjacent vertices
have a common neighbour coming from any minimum base containing them. -/
private theorem not_adj_of_three_le_baseSize_of_no_commonNeighbours
    (P : FinitePermutationGroup) {x y : P.Point}
    (hsize : 3 ≤ P.baseSize)
    (hcommon : P.saxlGraph.commonNeighbors x y = ∅) :
    ¬ P.saxlGraph.Adj x y := by
  rintro ⟨_hxy, b, hinj, hbase, hx, hy⟩
  have hrange : (Set.range b).ncard = P.baseSize := by
    simpa using Set.ncard_range_of_injective hinj
  have hthree : 2 < (Set.range b).ncard := by omega
  have hextra : ∃ z ∈ Set.range b, z ≠ x ∧ z ≠ y := by
    by_contra h
    push Not at h
    have hsubset : Set.range b ⊆ ({x, y} : Set P.Point) := by
      intro z hz
      have hzxy := h z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hle := Set.ncard_le_ncard hsubset
    have hpair : ({x, y} : Set P.Point).ncard ≤ 2 := by
      calc
        ({x, y} : Set P.Point).ncard ≤ ({y} : Set P.Point).ncard + 1 :=
          Set.ncard_insert_le x {y}
        _ = 2 := by simp
    omega
  obtain ⟨z, hz, hzx, hzy⟩ := hextra
  have hzcommon : z ∈ P.saxlGraph.commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    constructor
    · exact ⟨hzx.symm, b, hinj, hbase, hx, hz⟩
    · exact ⟨hzy.symm, b, hinj, hbase, hy, hz⟩
  rw [hcommon] at hzcommon
  exact hzcommon

/-- For every base size `B ≥ 2` and every prescribed bound there is a primitive
permutation group of degree at least that bound and base size `B` whose
generalised Saxl graph has two nonadjacent vertices with no common neighbour. -/
theorem mainTheorem (B degreeBound : Nat) (hB : 2 ≤ B) :
    ∃ P : FinitePermutationGroup,
      degreeBound ≤ Nat.card P.Point ∧
        MulAction.IsPreprimitive P.G P.Point ∧
        P.baseSize = B ∧
        ∃ x y : P.Point,
          ¬ P.saxlGraph.Adj x y ∧
          P.saxlGraph.commonNeighbors x y = ∅ := by
  obtain ⟨d, hd, hd3, hdegree⟩ :=
    pointDegrees_unbounded (B - 2) degreeBound
  obtain ⟨P, hcard, hprimitive, hsize, x, y, _hxy, hnonadj_two, hcommon⟩ :=
    familyFacts d hd hd3 (B - 2)
  have htail : B - 2 + 2 = B := by omega
  have hsizeB : P.baseSize = B := hsize.trans htail
  have hnonadj : ¬ P.saxlGraph.Adj x y := by
    by_cases hB2 : B = 2
    · apply hnonadj_two
      omega
    · apply not_adj_of_three_le_baseSize_of_no_commonNeighbours P
      · rw [hsizeB]
        omega
      · exact hcommon
  refine ⟨P, ?_, hprimitive, hsizeB, x, y, hnonadj, hcommon⟩
  simpa [hcard] using hdegree.le

end SaxlCounterexamples.MainTheorems.Internal
