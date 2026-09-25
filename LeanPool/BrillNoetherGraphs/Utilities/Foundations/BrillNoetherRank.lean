/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankInvariance
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.RankOne
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.LaplacianEquiv
import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# The Brill--Noether rank of a finite graph

Lim, Payne and Potashnik introduced the **Brill--Noether rank** `w^r_d` of a
metric graph as a well-behaved substitute for `dim W^r_d`, which is *not*
upper semicontinuous on the moduli space of metric graphs
(arXiv:1106.5519, Definition 3.1):

> `w^r_d(Γ)` is the largest integer `k` such that, for every effective divisor
> `E` of degree `r + k`, there exists a divisor `D` of degree `d` and rank at
> least `r` on `Γ` such that `D - E` is effective.  If `W^r_d(Γ)` is empty,
> `w^r_d(Γ)` is `-1`.

Len extended the definition to weighted tropical curves and proved upper
semicontinuity there (arXiv:1209.6309, §6).  Both papers prove a
specialization inequality `dim W^r_d(X) ≤ w^r_d(Γ)`, from which LPP deduce
`w^r_d(Γ) ≥ min {ρ(g,r,d), g}` for *every* metric graph — by transfer from
algebraic geometry, never combinatorially.

This file records the **discrete** analogue, in which both `E` and `D` are
supported on the vertices of a finite graph.  Note the degree bookkeeping:
`w^r_d ≥ k` tests effective divisors of degree `r + k`, not `k`.  Consequently

* `w^r_d(G) ≥ 0` is *exactly* Brill--Noether existence (`bnRankGe_zero_iff_bnExists`):
  a single divisor of rank at least `r` already absorbs every effective divisor
  of degree `r`, by the definition of rank.  Nothing is gained at `k = 0`.
* `w^r_d(G) ≥ 1` is genuinely more.  It splits into a *ramification* half
  (`E = 2•v`) and a *secant* half (`E = v + w`, `v ≠ w`), and neither half
  implies the other in general.

Besides the definition and its basic reformulations, this file proves that the
predicate is downward closed in `k` (`bnRankGe_of_le`), that it fails once the
degree drops below `r + k` (`not_bnRankGe_of_lt`), and that it is invariant
under an adjacency-preserving relabeling of vertices
(`Certificate.LaplacianEquiv.bnRankGe_iff`).  These combine into the numerical
invariant `bnRank`, normalized as in Len to be `-1` when `W^r_d` is empty.

The descent of this predicate along an odd subdivision lives in
`Utilities/Subdivision/SubdivisionChipDescent.lean` and is not imported here.
-/

namespace Utilities

universe u v

/-! ## The definition -/

/-- `BNRankGe G r d k` is the discrete Brill--Noether rank inequality
`w^r_d(G) ≥ k` of Lim--Payne--Potashnik and Len: every effective divisor `E` of
degree `r + k` is contained, up to linear equivalence, in a divisor of degree
`d` and rank at least `r`.

The literature says "`E` is contained in an effective divisor `D` of degree `d`
and rank at least `r`"; since rank is a class invariant, that is the same as
asking for `D - E` to be winnable, which is the form stated here.  The
containment form is recovered by `bnRankGe_iff_contained`. -/
def BNRankGe (G : CFGraph) (r d k : ℤ) : Prop :=
  ∀ E : CFDiv G, effective E → deg E = r + k →
    ∃ D : CFDiv G, deg D = d ∧ rank G D ≥ r ∧ winnable G (D - E)

/-- The literal Lim--Payne--Potashnik phrasing: every effective `E` of degree
`r + k` is *contained in* an effective divisor of degree `d` and rank at least
`r`. -/
theorem bnRankGe_iff_contained (G : CFGraph) (r d k : ℤ) :
    BNRankGe G r d k ↔
      ∀ E : CFDiv G, effective E → deg E = r + k →
        ∃ D : CFDiv G, effective D ∧ deg D = d ∧ rank G D ≥ r ∧ effective (D - E) := by
  constructor
  · intro h E hEffective hDegree
    obtain ⟨D, hDegD, hRankD, hWin⟩ := h E hEffective hDegree
    obtain ⟨F, hFEffective, hEquiv⟩ := hWin
    refine ⟨F + E, (Eff G).add_mem hFEffective hEffective, ?_, ?_, ?_⟩
    · have hDegF : deg F = deg (D - E) :=
        (linear_equiv_preserves_deg G (D - E) F hEquiv).symm
      rw [deg.map_add, hDegF, deg.map_sub, hDegD]
      ring
    · have hEquiv' : linearEquiv G D (F + E) := by
        have hDifference : (F + E) - D = F - (D - E) := by abel
        unfold linearEquiv at hEquiv ⊢
        rw [hDifference]
        exact hEquiv
      rw [← rank_eq_of_linear_equiv G hEquiv']
      exact hRankD
    · have hDifference : F + E - E = F := by abel
      rw [hDifference]
      exact hFEffective
  · intro h E hEffective hDegree
    obtain ⟨D, _hDEffective, hDegD, hRankD, hResidual⟩ := h E hEffective hDegree
    exact ⟨D, hDegD, hRankD, winnable_of_effective G _ hResidual⟩

/-! ## The rank-zero case is exactly Brill--Noether existence -/

/-- **The `k = 0` case is not new information.**  `w^r_d(G) ≥ 0` says that
every effective divisor of degree `r` can be absorbed, and that is precisely
the definition of a divisor of rank at least `r`.  So the Brill--Noether rank
inequality at `k = 0` is equivalent to plain Brill--Noether existence. -/
theorem bnRankGe_zero_iff_bnExists
    (G : CFGraph) (r d : ℤ) (hr : 0 ≤ r) :
    BNRankGe G r d 0 ↔ BNExists G r d := by
  constructor
  · intro h
    let v : G.V := Classical.arbitrary G.V
    let E : CFDiv G := r.toNat • oneChip v
    have hEffective : effective E := (Eff G).nsmul_mem (eff_one_chip v) r.toNat
    have hDegree : deg E = r + 0 := by
      dsimp [E]
      simpa [Int.toNat_of_nonneg hr] using
        (AddMonoidHom.map_nsmul deg r.toNat (oneChip v))
    obtain ⟨D, hDegD, hRankD, _⟩ := h E hEffective hDegree
    exact ⟨D, hDegD, hRankD⟩
  · rintro ⟨D, hDegD, hRankD⟩ E hEffective hDegree
    refine ⟨D, hDegD, hRankD, ?_⟩
    exact (rank_geq_iff G D r).mpr hRankD E ⟨hEffective, by simpa using hDegree⟩

/-! ## Degree slack

Brill--Noether existence one degree lower buys one unit of Brill--Noether rank
for free: split `E` into a degree-`r` piece, absorbed by the rank of the
smaller witness, and a degree-one remainder, simply added on. -/

/-- If `G` carries a divisor of degree `d - 1` and rank at least `r`, then
`w^r_d(G) ≥ 1`. -/
theorem bnRankGe_of_bnExists_pred
    (G : CFGraph) (r d : ℤ) (hr : 0 ≤ r)
    (hExists : BNExists G r (d - 1)) :
    BNRankGe G r d 1 := by
  obtain ⟨D₀, hDegD₀, hRankD₀⟩ := hExists
  intro E hEffective hDegree
  have hDegree' : deg E = (r.toNat : ℕ) + (1 : ℕ) := by
    have : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr
    push_cast
    omega
  obtain ⟨E₁, E₂, hE₁, hE₂, hDegE₁, hDegE₂, hSplit⟩ :=
    effective_divisor_decomposition G E r.toNat 1 hEffective hDegree'
  have hDegE₁' : deg E₁ = r := by
    rw [hDegE₁]
    exact Int.toNat_of_nonneg hr
  refine ⟨D₀ + E₂, ?_, ?_, ?_⟩
  · rw [deg.map_add, hDegD₀, hDegE₂]; ring
  · exact rank_add_effective_ge G D₀ E₂ hE₂ r hRankD₀
  · have hDifference : D₀ + E₂ - E = D₀ - E₁ := by
      rw [hSplit]; abel
    rw [hDifference]
    exact (rank_geq_iff G D₀ r).mpr hRankD₀ E₁ ⟨hE₁, hDegE₁'⟩

/-! ## Effective divisors of degree two -/

/-- An effective divisor of degree two is a sum of two vertex chips. -/
theorem exists_chip_pair_of_effective_deg_two
    (G : CFGraph) (A : CFDiv G) (hEffective : effective A) (hDegree : deg A = 2) :
    ∃ x y : G.V, A = oneChip x + oneChip y := by
  have hDegree' : deg A = (1 : ℕ) + (1 : ℕ) := by
    norm_num
    exact hDegree
  obtain ⟨E, F, hE, hF, hDegE, hDegF, hSplit⟩ :=
    effective_divisor_decomposition G A 1 1 hEffective hDegree'
  obtain ⟨x, hx⟩ := Certificate.effective_degree_one_eq_one_chip hE hDegE
  obtain ⟨y, hy⟩ := Certificate.effective_degree_one_eq_one_chip hF hDegF
  exact ⟨x, y, by rw [hSplit, hx, hy]⟩

/-- Gonality at most three already forces `w^1_4(G) ≥ 1`, whatever the genus.
The open genus-five cases are therefore exactly the graphs of gonality four. -/
theorem bnRankGe_one_of_bnExists_one_three
    (G : CFGraph) (hExists : BNExists G 1 3) :
    BNRankGe G 1 4 1 :=
  bnRankGe_of_bnExists_pred G 1 4 (by norm_num) (by simpa using hExists)

/-! ## Monotonicity in the Brill--Noether rank parameter -/

/-- **Downward closure in `k`.**  An effective divisor `E'` of degree `r + k'`
is padded to degree `r + k` by heaping the missing `k - k'` chips on a single
vertex; the residual of the padded divisor is winnable, hence so is the
residual of `E'`, which differs from it by an effective divisor.

The hypothesis `0 ≤ r + k'` is not needed — below that range the statement is
vacuous, since there are no effective divisors of negative degree — but it is
kept in the interface, as every intended use supplies it. -/
theorem bnRankGe_of_le {G : CFGraph} {r d k k' : ℤ}
    (_hk : 0 ≤ r + k') (hkk : k' ≤ k) (h : BNRankGe G r d k) :
    BNRankGe G r d k' := by
  have hSlack : (0 : ℤ) ≤ k - k' := by omega
  intro E hEffective hDegree
  let v : G.V := Classical.arbitrary G.V
  let F : CFDiv G := (k - k').toNat • oneChip v
  have hFEffective : effective F := (Eff G).nsmul_mem (eff_one_chip v) (k - k').toNat
  have hFDegree : deg F = k - k' := by
    dsimp [F]
    simpa [Int.toNat_of_nonneg hSlack] using
      (AddMonoidHom.map_nsmul deg (k - k').toNat (oneChip v))
  have hPaddedDegree : deg (E + F) = r + k := by
    rw [deg.map_add, hDegree, hFDegree]
    ring
  obtain ⟨D, hDegD, hRankD, hWin⟩ :=
    h (E + F) ((Eff G).add_mem hEffective hFEffective) hPaddedDegree
  refine ⟨D, hDegD, hRankD, ?_⟩
  have hDifference : D - E = (D - (E + F)) + F := by abel
  rw [hDifference]
  exact winnable_add_winnable G _ _ hWin (winnable_of_effective G F hFEffective)

/-- **The degree ceiling.**  A divisor of degree `d` cannot absorb an effective
divisor of larger degree: the residual would be winnable of negative degree.
Since `hk` guarantees that an effective divisor of degree `r + k` exists, the
Brill--Noether rank inequality fails outright once `d < r + k`. -/
theorem not_bnRankGe_of_lt {G : CFGraph} {r d k : ℤ}
    (hr : 0 ≤ r) (hk : 0 ≤ k) (hdk : d < r + k) :
    ¬ BNRankGe G r d k := by
  intro h
  let v : G.V := Classical.arbitrary G.V
  let E : CFDiv G := (r + k).toNat • oneChip v
  have hEffective : effective E := (Eff G).nsmul_mem (eff_one_chip v) (r + k).toNat
  have hDegree : deg E = r + k := by
    dsimp [E]
    simpa [Int.toNat_of_nonneg (show (0 : ℤ) ≤ r + k by omega)] using
      (AddMonoidHom.map_nsmul deg (r + k).toNat (oneChip v))
  obtain ⟨D, hDegD, _, hWin⟩ := h E hEffective hDegree
  obtain ⟨B, hBEffective, hEquiv⟩ := hWin
  have hDegB : deg B ≥ 0 := deg_of_eff_nonneg B hBEffective
  rw [← linear_equiv_preserves_deg G (D - E) B hEquiv, deg.map_sub, hDegD,
    hDegree] at hDegB
  omega

/-! ## The numerical Brill--Noether rank -/

open Classical in
/-- The Brill--Noether rank `w^r_d(G)`, normalized as in Len: it is `-1` when
`W^r_d(G)` is empty, and otherwise the largest `k ≥ 0` for which the inequality
`BNRankGe G r d k` holds.  The supremum is attained because the set of such `k`
is a nonempty set of integers bounded above by `d - r`
(`bnRankGe_iff_le_bnRank`). -/
noncomputable def bnRank (G : CFGraph) (r d : ℤ) : ℤ :=
  if BNExists G r d then sSup {k : ℤ | 0 ≤ k ∧ BNRankGe G r d k} else -1

/-- Len's normalization: an empty `W^r_d` has Brill--Noether rank `-1`. -/
theorem bnRank_eq_neg_one_of_not_bnExists {G : CFGraph} {r d : ℤ}
    (hExists : ¬ BNExists G r d) :
    bnRank G r d = -1 := by
  rw [bnRank, if_neg hExists]

/-- **The defining property of `bnRank`.**  For nonnegative parameters the
predicate `BNRankGe` is exactly the comparison `k ≤ w^r_d(G)`. -/
theorem bnRankGe_iff_le_bnRank {G : CFGraph} {r d k : ℤ} (hr : 0 ≤ r) (hk : 0 ≤ k) :
    BNRankGe G r d k ↔ k ≤ bnRank G r d := by
  by_cases hExists : BNExists G r d
  · have hValue : bnRank G r d = sSup {k : ℤ | 0 ≤ k ∧ BNRankGe G r d k} := by
      rw [bnRank, if_pos hExists]
    have hBdd : BddAbove {k : ℤ | 0 ≤ k ∧ BNRankGe G r d k} := by
      refine ⟨d - r, ?_⟩
      rintro m ⟨hm, hRank⟩
      by_contra hContra
      exact not_bnRankGe_of_lt hr hm (by omega) hRank
    have hNonempty : Set.Nonempty {k : ℤ | 0 ≤ k ∧ BNRankGe G r d k} :=
      ⟨0, le_rfl, (bnRankGe_zero_iff_bnExists G r d hr).mpr hExists⟩
    have hMem := Int.csSup_mem hNonempty hBdd
    constructor
    · intro hRank
      rw [hValue]
      exact le_csSup hBdd ⟨hk, hRank⟩
    · intro hLe
      rw [hValue] at hLe
      exact bnRankGe_of_le (show (0 : ℤ) ≤ r + k by omega) hLe hMem.2
  · rw [bnRank_eq_neg_one_of_not_bnExists hExists]
    constructor
    · intro hRank
      exact absurd ((bnRankGe_zero_iff_bnExists G r d hr).mp
        (bnRankGe_of_le (show (0 : ℤ) ≤ r + 0 by omega) hk hRank)) hExists
    · intro hLe
      exact absurd hLe (by omega)

/-- Nonnegativity of the Brill--Noether rank is Brill--Noether existence. -/
theorem bnRank_nonneg_iff {G : CFGraph} {r d : ℤ} (hr : 0 ≤ r) :
    0 ≤ bnRank G r d ↔ BNExists G r d := by
  constructor
  · intro hNonneg
    by_contra hExists
    rw [bnRank_eq_neg_one_of_not_bnExists hExists] at hNonneg
    omega
  · intro hExists
    exact (bnRankGe_iff_le_bnRank hr le_rfl).mp
      ((bnRankGe_zero_iff_bnExists G r d hr).mpr hExists)

/-! ## Transport along an adjacency-preserving relabeling -/

namespace Certificate.LaplacianEquiv

/-- The Brill--Noether rank inequality transports backwards along an
adjacency-preserving vertex equivalence. -/
theorem bnRankGe_of_mapDiv {G : CFGraph.{u}} {H : CFGraph.{v}}
    (equivalence : LaplacianEquiv G H) {r d k : ℤ}
    (hRank : BNRankGe H r d k) :
    BNRankGe G r d k := by
  intro E hEffective hDegree
  obtain ⟨D, hDegD, hRankD, hWin⟩ :=
    hRank (equivalence.mapDiv E)
      ((equivalence.effective_mapDiv_iff E).2 hEffective) (by simpa using hDegree)
  refine ⟨equivalence.symm.mapDiv D, by simpa using hDegD, ?_, ?_⟩
  · exact (equivalence.symm.rank_mapDiv_ge_iff D r).2 hRankD
  · simpa using equivalence.symm.winnable_mapDiv hWin

/-- The Brill--Noether rank inequality is unchanged by relabeling vertices. -/
theorem bnRankGe_iff {G : CFGraph.{u}} {H : CFGraph.{v}}
    (equivalence : LaplacianEquiv G H) (r d k : ℤ) :
    BNRankGe H r d k ↔ BNRankGe G r d k :=
  ⟨fun hRank => equivalence.bnRankGe_of_mapDiv hRank,
    fun hRank => equivalence.symm.bnRankGe_of_mapDiv hRank⟩

end Certificate.LaplacianEquiv

end Utilities
