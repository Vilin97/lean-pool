/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.BananaEndpointRankCriterion

/-!
# Restricted rank and rank-determining sets

This file formalizes the definitions preceding paper Lemma 2.21 and the
rank-one characterization used in its proof.  We use the lower-bound relation
for restricted rank, which is the literal quantified content of `r_A(D) ≥ k`
and avoids making a second noncomputable choice of an integer rank.
-/

namespace Bananas

open Utilities

open Utilities Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- A divisor is supported on `A` when every vertex with nonzero coefficient
belongs to `A`. -/
def DivisorSupportedOn {G : CFGraph} (A : Set G.V) (E : CFDiv G) : Prop :=
  ∀ v, E v ≠ 0 → v ∈ A

/-- The literal restricted-rank lower-bound relation from the paper:
`r_A(D) ≥ k` means that subtracting every effective degree-`k` divisor
supported on `A` leaves a winnable divisor. -/
def restrictedRankGeq (G : CFGraph) (A : Set G.V)
    (D : CFDiv G) (k : ℤ) : Prop :=
  ∀ E : CFDiv G, effective E → deg E = k → DivisorSupportedOn A E →
    winnable G (D - E)

/-- A set is rank determining when restricted rank agrees with ordinary rank
at every integer lower bound, equivalently when `r_A(D) = r(D)` for every
divisor `D`. -/
def RankDetermining (G : CFGraph) (A : Set G.V) : Prop :=
  ∀ (D : CFDiv G) (k : ℤ), restrictedRankGeq G A D k ↔ rank_geq G D k

theorem restrictedRankGeq_of_rank_geq
    {G : CFGraph} {A : Set G.V} {D : CFDiv G} {k : ℤ}
    (h : rank_geq G D k) : restrictedRankGeq G A D k := by
  intro E hEff hDeg _hSupport
  exact h E ⟨hEff, hDeg⟩

private theorem supportedOn_zero {G : CFGraph} (A : Set G.V) :
    DivisorSupportedOn A (0 : CFDiv G) := by
  intro v h
  simp at h

private theorem supportedOn_add_one_chip
    {G : CFGraph} {A : Set G.V} {E : CFDiv G} {a : G.V}
    (hE : DivisorSupportedOn A E) (ha : a ∈ A) :
    DivisorSupportedOn A (E + one_chip a) := by
  intro v hv
  by_cases hva : v = a
  · simpa [hva] using ha
  · have hEv : E v ≠ 0 := by
      intro hZero
      apply hv
      simp [Pi.add_apply, one_chip, hva, hZero]
    exact hE v hEv

private theorem supportedOn_left_of_effective_add
    {G : CFGraph} {A : Set G.V} {E F : CFDiv G}
    (hE : effective E) (hF : effective F)
    (hEF : DivisorSupportedOn A (E + F)) :
    DivisorSupportedOn A E := by
  intro v hEv
  apply hEF v
  have hEpos : 0 < E v := lt_of_le_of_ne (hE v) (Ne.symm hEv)
  have hFnonneg := hF v
  simp only [Pi.add_apply]
  omega

section Generic

/-- Luo's rank-one characterization, in the direction used by the paper.
If the tests obtained by subtracting one chip at every member of `A` force
ordinary rank at least one, then `A` is rank determining. -/
theorem rankDetermining_of_rank_one_test
    {G : CFGraph} (A : Set G.V)
    (hOne : ∀ D : CFDiv G,
      (∀ a ∈ A, winnable G (D - one_chip a)) → 1 ≤ rank G D) :
    RankDetermining G A := by
  have hNat : ∀ n : ℕ, ∀ D : CFDiv G,
      restrictedRankGeq G A D (n : ℤ) → rank_geq G D (n : ℤ) := by
    intro n
    induction n with
    | zero =>
        intro D hRestricted
        have hWin := hRestricted 0 (by intro v; simp) (by simp)
          (supportedOn_zero A)
        exact (rank_nonneg_iff_winnable G D).mpr (by simpa using hWin)
    | succ n ih =>
        intro D hRestricted
        have hSubtractA : ∀ a ∈ A,
            rank_geq G (D - one_chip a) (n : ℤ) := by
          intro a ha
          apply ih
          intro E hEff hDeg hSupport
          have hEffAdd : effective (E + one_chip a) :=
            fun v => add_nonneg (hEff v) (eff_one_chip a v)
          have hDegAdd : deg (E + one_chip a) = ((n + 1 : ℕ) : ℤ) := by
            rw [deg.map_add, deg_one_chip, hDeg]
            norm_num
          have hWin := hRestricted (E + one_chip a) hEffAdd hDegAdd
            (supportedOn_add_one_chip hSupport ha)
          convert hWin using 1
          abel_nf
        intro E hE
        rcases hE with ⟨hEff, hDeg⟩
        obtain ⟨E₁, E₂, hE₁Eff, hE₂Eff, hE₁Deg, hE₂Deg, hESplit⟩ :=
          effective_divisor_decomposition G E n 1 hEff (by
            exact_mod_cast hDeg)
        let X : CFDiv G := D - E₁
        have hXOne : 1 ≤ rank G X := by
          apply hOne
          intro a ha
          have hRankA := hSubtractA a ha
          have hWinA := hRankA E₁ ⟨hE₁Eff, by exact_mod_cast hE₁Deg⟩
          simpa [X, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hWinA
        have hXGeq : rank_geq G X 1 :=
          (rank_geq_iff G X 1).mpr hXOne
        have hWin := hXGeq E₂ ⟨hE₂Eff, by exact_mod_cast hE₂Deg⟩
        rw [hESplit]
        simpa [X, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hWin
  intro D k
  constructor
  · intro hRestricted
    by_cases hkNeg : k < 0
    · exact (rank_geq_iff G D k).mpr
        (le_trans (by omega : k ≤ -1) (rank_geq_neg_one G D))
    · have hkNonneg : 0 ≤ k := by omega
      let n : ℕ := k.toNat
      have hn : (n : ℤ) = k := Int.toNat_of_nonneg hkNonneg
      rw [← hn] at hRestricted ⊢
      exact hNat n D hRestricted
  · exact restrictedRankGeq_of_rank_geq

end Generic

/-- Paper Lemma 2.21 (`lem-BananaRDS`): the two multivalent endpoints of a
banana graph form a rank-determining set. -/
theorem banana_endpoints_rankDetermining {g : ℕ} (B : Banana g) :
    RankDetermining B.graph {leftEndpoint B, rightEndpoint B} := by
  apply rankDetermining_of_rank_one_test
  intro D hEndpoints
  apply banana_rank_one_of_endpoint_residuals B D
  · exact (rank_geq_iff B.graph _ 0).mp
      ((rank_nonneg_iff_winnable B.graph _).mpr
        (hEndpoints (leftEndpoint B) (by simp)))
  · exact (rank_geq_iff B.graph _ 0).mp
      ((rank_nonneg_iff_winnable B.graph _).mpr
        (hEndpoints (rightEndpoint B) (by simp)))

end Bananas
