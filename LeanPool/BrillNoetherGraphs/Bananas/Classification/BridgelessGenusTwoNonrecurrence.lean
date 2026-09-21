/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Classification.BridgelessDegreeOneClasses
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaInversionCount

/-!
# Nonrecurrence on bridgeless genus-two graphs

The finite-orbit part of the proof of Theorem 4.8 does not use a theta
presentation.  What it needs is precisely Lemma 2.3: on a nontrivial
bridgeless graph, every effective divisor of degree one has rank zero and a
unique vertex representative.  This module packages that argument with the
library's `TwoEdgeCutCondition` as the no-bridge hypothesis.
-/

namespace Bananas

open Utilities

/-- On a nontrivial connected graph with no one-edge cut, an effective
degree-one divisor has rank zero. -/
theorem rank_eq_zero_of_degree_one_rank_nonneg_of_twoEdgeCutCondition
    (G : CFGraph) (hConnected : _root_.graph_connected G)
    (hCut : TwoEdgeCutCondition G) (hNontrivial : ∃ p q : G.V, p ≠ q)
    (X : CFDiv G) (hDegree : deg X = 1) (hRank : 0 ≤ rank G X) :
    rank G X = 0 := by
  obtain ⟨E, hEff, hXE⟩ := (rank_nonneg_iff_winnable G X).mp
    ((rank_geq_iff G X 0).mpr hRank)
  have hEDegree : deg E = 1 := by
    rw [← linear_equiv_preserves_deg G X E hXE, hDegree]
  obtain ⟨w, hw⟩ := effective_degree_one_eq_one_chip E hEff hEDegree
  have hRankEq := rank_eq_of_linear_equiv G hXE
  rw [hw, rank_one_chip_eq_zero_of_twoEdgeCutCondition G hConnected hCut
    hNontrivial] at hRankEq
  exact hRankEq

/-- The effective degree-one members of a finite exact torsion orbit are at
most two when the marked difference is nonrecurrent.  This is the cardinality
estimate in the proof of Theorem 4.8, stated without a theta presentation. -/
theorem effectiveDegreeOneTwistResidues_ncard_le_two_of_nonRecurrent_bridgeless
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (k : ℕ)
    (hConnected : _root_.graph_connected G) (hCut : TwoEdgeCutCondition G)
    (hNontrivial : ∃ p q : G.V, p ≠ q)
    (hTO : IsTorsionOrder (mark G u v) k)
    (hNonrec : NonRecurrent (mark G u v) k) :
    (effectiveDegreeOneTwistResidues (mark G u v) D k).ncard ≤ 2 := by
  let M := mark G u v
  let S := effectiveDegreeOneTwistResidues M D k
  by_cases hEmpty : S = ∅
  · change S.ncard ≤ 2
    rw [hEmpty]
    simp
  obtain ⟨c, hcS⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
  have hRankC : rank G (degreeTwistInt M D 1 c.val) = 0 := by
    apply rank_eq_zero_of_degree_one_rank_nonneg_of_twoEdgeCutCondition
      G hConnected hCut hNontrivial
    · exact deg_effectiveDegreeOneTwistResidue M D k c
    · exact hcS
  obtain ⟨w, hw⟩ :=
    exists_one_chip_representative_of_rank_zero_degree_one G
      (degreeTwistInt M D 1 c.val) hRankC
      (deg_effectiveDegreeOneTwistResidue M D k c)
  let T : Set (Fin k) := {r | 0 ≤ rank G
    (one_chip w + (r.val : ℤ) • (one_chip u - one_chip v))}
  have hMap : ∀ b ∈ S, residueShift k b c ∈ T := by
    intro b hb
    have h := rank_nonneg_rebased_residue_of_effectiveDegreeOneTwist
      hTO.1 D b c w hw (by simpa [S] using hb)
    change 0 ≤ rank G
      (one_chip w + ((residueShift k b c).val : ℤ) •
        (one_chip u - one_chip v))
    rw [residueShift_val]
    exact h
  have hTtwo : T.ncard ≤ 2 := by
    let z : Fin k := ⟨0, hTO.1.1⟩
    apply Set.ncard_le_two_of_zero_or_eq T z
    intro x y hx hy
    rcases hNonrec.zero_or_eq_of_two_rank_nonneg w x y hx hy with hx0 | hy0 | hxy
    · exact Or.inl (Fin.ext (by simpa [z] using hx0))
    · exact Or.inr (Or.inl (Fin.ext (by simpa [z] using hy0)))
    · exact Or.inr (Or.inr hxy)
  have hle := Set.ncard_le_ncard_of_injOn
    (s := S) (t := T) (fun b : Fin k => residueShift k b c)
    hMap (residueShift_injective k c).injOn
  exact le_trans hle hTtwo

/-- A finite set of cardinality at most two containing a distinguished
element has at most one further element. -/
private theorem fin_eq_of_ncard_le_two_of_mem_three
    {α : Type*} [Finite α] {S : Set α} (h : S.ncard ≤ 2)
    {z n m : α} (hz : z ∈ S) (hn : n ∈ S) (hm : m ∈ S)
    (hnz : n ≠ z) (hmz : m ≠ z) : n = m := by
  classical
  by_contra hnm
  have hSub : ({z, n, m} : Set α) ⊆ S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hz
    · exact hn
    · exact hm
  have hTriple : ({z, n, m} : Set α).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨z, n, m, Ne.symm hnz, Ne.symm hmz, hnm, rfl⟩
  have hLe := Set.ncard_le_ncard hSub (Set.toFinite S)
  omega

/-- Degree-one twists of a single chip are the marked residue twists used in
the definition of nonrecurrence. -/
private theorem mem_effectiveDegreeOneTwistResidues_one_chip_iff'
    (G : CFGraph) (u v w : G.V) (k : ℕ) (b : Fin k) :
    b ∈ effectiveDegreeOneTwistResidues (mark G u v) (one_chip w) k ↔
      0 ≤ rank G (one_chip w + (b : ℤ) • (one_chip u - one_chip v)) := by
  rw [mem_effectiveDegreeOneTwistResidues_iff]
  unfold degreeTwistInt
  change 0 ≤ rank G
    (one_chip w + (1 - deg (one_chip w) + (b : ℤ)) • one_chip u -
      (b : ℤ) • one_chip v) ↔ _
  rw [deg_one_chip]
  have hDiv :
      (one_chip w + (1 - 1 + (b : ℤ)) • one_chip u -
        (b : ℤ) • one_chip v : CFDiv G) =
        one_chip w + (b : ℤ) • (one_chip u - one_chip v) := by
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  rw [hDiv]
/-- The converse implication in Theorem 4.8, factored from its
genus-two inversion identity.  The formula hypothesis is exactly the
correction-free conclusion of Lemma 4.10 for the single-chip divisors used
in the argument.  Thus this theorem applies to any nontrivial bridgeless
genus-two graph as soon as its corresponding inversion formula is supplied.
-/
theorem nonRecurrent_of_kGeneralTransmission_of_effectiveResidueFormula
    (G : CFGraph) (u v : G.V) (k : ℕ)
    (hConnected : _root_.graph_connected G)
    (hCut : TwoEdgeCutCondition G) (hNontrivial : ∃ p q : G.V, p ≠ q)
    (hGenus : genus G = 2)
    (hFormula : ∀ w τ,
      IsTransmissionPermutation (mark G u v) (one_chip w) τ →
      IsKAffine k τ →
      kInversionCount k τ =
        (effectiveDegreeOneTwistResidues (mark G u v) (one_chip w) k).ncard)
    (hKGT : KGeneralTransmission (mark G u v) k) :
    NonRecurrent (mark G u v) k := by
  obtain ⟨hTorsion, -, hData⟩ := hKGT
  intro w n m hn hm hnRank hmRank
  obtain ⟨tau, hTau, hAffine, -, hCount⟩ := hData (one_chip w)
  have hEq := hFormula w tau hTau hAffine
  have hGenusNat : Int.toNat (genus (mark G u v).graph) = 2 := by
    change Int.toNat (genus G) = 2
    rw [hGenus]
    rfl
  rw [hGenusNat, hEq] at hCount
  have hzero : (⟨0, hTorsion.1⟩ : Fin k) ∈
      effectiveDegreeOneTwistResidues (mark G u v) (one_chip w) k := by
    rw [mem_effectiveDegreeOneTwistResidues_one_chip_iff']
    have hRank : rank G (one_chip w) = 0 :=
      rank_one_chip_eq_zero_of_twoEdgeCutCondition G
        hConnected hCut hNontrivial w
    simpa using hRank.ge
  have hnMem : n ∈
      effectiveDegreeOneTwistResidues (mark G u v) (one_chip w) k := by
    rw [mem_effectiveDegreeOneTwistResidues_one_chip_iff']
    exact hnRank
  have hmMem : m ∈
      effectiveDegreeOneTwistResidues (mark G u v) (one_chip w) k := by
    rw [mem_effectiveDegreeOneTwistResidues_one_chip_iff']
    exact hmRank
  exact fin_eq_of_ncard_le_two_of_mem_three hCount hzero hnMem hmMem
    (fun h => hn (congrArg Fin.val h)) (fun h => hm (congrArg Fin.val h))

end Bananas
