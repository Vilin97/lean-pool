/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossingInversionCount
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionAPI
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.TwoVertexPencilCore

/-!
# Large-period general transmission implies Brill--Noether generality

This is Proposition 6.1 (`prop:kgt-bngenl`) of the paper.  The paper writes
the threshold as `k ≥ g / 2 + 1`.  For natural-number parameters its exact,
parity-independent form is `g + 2 ≤ 2 * k`.

The proof separates the graph theory from the combinatorics.  The two rank
formulas of `lem:tauChars` identify a rectangular family of crossing
inversions.  If that family has more than `g` members, two normalize to the
same `k`-inversion.  The interval between those representatives then supplies
at least `2k - 1` distinct `k`-inversions, contradicting the defining bound.
-/

namespace Bananas

open Utilities

/-- Normalize an ordinary inversion by moving its first coordinate into the
fundamental interval `[0,k)`. -/
def normalizeFirstInversion (k : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 % k, p.2 - (p.1 / k) * k)

/-- The rectangular family of inversions crossing both coordinate axes. -/
def crossingInversions (τ : ℤ → ℤ) : Set (ℤ × ℤ) :=
  northwestSet τ 1 0 ×ˢ southeastSet τ 1 0

theorem crossingInversions_ncard (τ : ℤ → ℤ) :
    (crossingInversions τ).ncard =
      (northwestSet τ 1 0).ncard * (southeastSet τ 1 0).ncard := by
  exact Set.ncard_prod

theorem normalizeFirstInversion_mem_kInversions_of_crossing
    {k : ℕ} {τ : ℤ → ℤ} (hk : 0 < k) (hAffine : IsKAffine k τ)
    {p : ℤ × ℤ} (hp : p ∈ crossingInversions τ) :
    normalizeFirstInversion k p ∈ kInversions k τ := by
  apply inversion_normalize_first_coordinate hk hAffine
  rcases hp with ⟨hpNW, hpSE⟩
  change p.1 < 0 ∧ 1 ≤ τ p.1 at hpNW
  change 0 ≤ p.2 ∧ τ p.2 < 1 at hpSE
  exact ⟨by omega, by omega⟩

/-- Pigeonhole step in Proposition 6.1: too many crossing inversions give two
distinct ordinary inversions representing the same `k`-inversion. -/
theorem exists_crossing_collision
    {k : ℕ} {τ : ℤ → ℤ} (hk : 0 < k) (hAffine : IsKAffine k τ)
    (hfinite : (kInversions k τ).Finite)
    (hlarge : kInversionCount k τ < (crossingInversions τ).ncard) :
    ∃ p ∈ crossingInversions τ, ∃ q ∈ crossingInversions τ,
      p ≠ q ∧ normalizeFirstInversion k p = normalizeFirstInversion k q := by
  exact Set.exists_ne_map_eq_of_ncard_lt_of_maps_to (ht := hfinite) hlarge
    (fun p hp =>
      normalizeFirstInversion_mem_kInversions_of_crossing hk hAffine hp)

/-- The combinatorial core of Proposition 6.1.  Two different axis-crossing
inversions in one affine-equivalence class force a block of at least `2k-1`
different classes. -/
theorem crossing_collision_inversion_lower_bound
    {k : ℕ} {τ : ℤ → ℤ} (hk : 0 < k) (hAffine : IsKAffine k τ)
    (hfinite : (kInversions k τ).Finite)
    {p q : ℤ × ℤ} (hp : p ∈ crossingInversions τ)
    (hq : q ∈ crossingInversions τ) (hpq : p ≠ q)
    (hnorm : normalizeFirstInversion k p = normalizeFirstInversion k q) :
    2 * k - 1 ≤ kInversionCount k τ := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨a', b'⟩
  rcases hp with ⟨hpNW, hpSE⟩
  rcases hq with ⟨hqNW, hqSE⟩
  change a < 0 ∧ 1 ≤ τ a at hpNW
  change 0 ≤ b ∧ τ b < 1 at hpSE
  change a' < 0 ∧ 1 ≤ τ a' at hqNW
  change 0 ≤ b' ∧ τ b' < 1 at hqSE
  have _ := hfinite
  apply kInversionCount_ge_two_mul_sub_one_of_crossing_collision
    hk hAffine hpNW.1 hpSE.1 (by omega) (by omega)
      hqNW.1 hqSE.1 (by omega) (by omega) hpq
  simpa [normalizeFirstInversion, normalizeInversionFirst] using hnorm

/-- Paper Proposition 6.1 (`prop:kgt-bngenl`), with the corrected natural
threshold `g + 2 ≤ 2k`.

The paper's standing convention is that graphs are connected; it is explicit
here because `CFGraph` itself does not bundle connectedness. -/
theorem kGeneralTransmission_brillNoetherGeneral
    {M : TwiceMarked} {g k : ℕ}
    (hconn : _root_.graphConnected M.graph)
    (hgenus : genus M.graph = g)
    (hK : KGeneralTransmission M k)
    (hthreshold : g + 2 ≤ 2 * k) :
    BrillNoetherGeneral M.graph := by
  intro r d hr hExists
  rcases hExists with ⟨D, hdeg, hRank⟩
  by_contra hBN
  have hBNneg : bnNumber M.graph r d < 0 := by omega
  obtain ⟨τ, hτ, hAffine, hfinite, hCount⟩ := hK.2.2 D
  have hk : 0 < k := hK.1.1
  have hSE := transmission_rank_eq_southeast_ncard
    M D hconn τ hτ 0 0
  have hNW := transmission_complement_rank_eq_northwest_ncard
    M D hconn τ hτ 0 0
  have hRR := riemann_roch_for_graphs hconn D
  have hSEcard : ((southeastSet τ 1 0).ncard : ℤ) = rank M.graph D + 1 := by
    simpa using hSE.symm
  have hNWcard : ((northwestSet τ 1 0).ncard : ℤ) =
      genus M.graph - d + rank M.graph D := by
    have hComplement : canonicalDivisor M.graph - D -
        (0 : ℤ) • oneChip M.u + (0 : ℤ) • oneChip M.v =
          canonicalDivisor M.graph - D := by simp
    rw [hComplement] at hNW
    norm_num at hNW
    rw [hdeg] at hRR
    omega
  have hCrossCard : ((crossingInversions τ).ncard : ℤ) =
      (rank M.graph D + 1) *
        (genus M.graph - d + rank M.graph D) := by
    rw [crossingInversions_ncard]
    push_cast
    rw [hNWcard, hSEcard]
    ring
  have hgenusNonneg : 0 ≤ genus M.graph := by rw [hgenus]; omega
  have hTarget : genus M.graph <
      (r + 1) * (genus M.graph - d + r) := by
    unfold bnNumber rectangleWidth at hBNneg
    omega
  have hWidthPos : 0 < genus M.graph - d + r := by
    nlinarith
  have hActual : genus M.graph <
      (rank M.graph D + 1) *
        (genus M.graph - d + rank M.graph D) := by
    nlinarith
  have hCrossGtZ : genus M.graph < ((crossingInversions τ).ncard : ℤ) := by
    rw [hCrossCard]
    exact hActual
  have hCrossGt : g < (crossingInversions τ).ncard := by
    rw [hgenus] at hCrossGtZ
    exact_mod_cast hCrossGtZ
  have hlarge : kInversionCount k τ < (crossingInversions τ).ncard :=
    lt_of_le_of_lt hCount (by simpa [hgenus] using hCrossGt)
  obtain ⟨p, hp, q, hq, hpq, hnorm⟩ :=
    exists_crossing_collision hk hAffine hfinite hlarge
  have hLower := crossing_collision_inversion_lower_bound
    hk hAffine hfinite hp hq hpq hnorm
  omega

/-- TeX label: none (Remark 1.18 is unlabeled); the same deduction is the last
step of `cor:bananasWithKGT` (Corollary 6.4).

Every banana of genus at least three is not Brill--Noether general: its
endpoint pencil has degree two and rank one although its Brill--Noether number
is `2 - g < 0`.  This formalizes the final observation in the introduction. -/
theorem banana_not_brillNoetherGeneral {g : ℕ} (hg : 3 ≤ g) (B : Banana g) :
    ¬ BrillNoetherGeneral B.graph := by
  intro hGeneral
  have hPredicted : 0 ≤ bnNumber B.graph 1 2 :=
    hGeneral 1 2 (by norm_num) B.bnExists_one_two_of_two_core_vertices
  unfold bnNumber rectangleWidth at hPredicted
  rw [B.genus_graph] at hPredicted
  norm_num at hPredicted
  omega

end Bananas
