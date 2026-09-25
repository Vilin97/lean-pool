/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaInversionCount

/-!
# Exact torsion order from `k`-general transmission

Paper source: `lem:kgtImpliesTorsionOrder` (Lemma 4.2).  A twice-marked graph
with `k`-general transmission has `k` *equal* to its torsion order, not
merely divisible by it (`TorsionWitness M k`, which is already `hK.1`, only
records divisibility).

The proof follows the published argument: using the transmission permutation
`τ` of the zero divisor, `τ 0 = 0` (from `r(0) = 0` and two negative-degree
rank vanishings), and Riemann-Roch identifies a set `A` of exactly `genus`
many negative integers `a` with `τ a > 0`, each giving a distinct ordinary
inversion `(a, 0)`.  Since `k`-general transmission bounds the number of
`k`-inversions by the genus, these `genus`-many inversions already exhaust
`Inv_k(τ)`; periodicity at any further torsion witness `n` then produces a
new inversion `(a + n, n)` whose normalization forces `k ∣ n`.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Any transmission permutation of `D` is periodic (`IsKAffine`) at *every*
torsion witness of `M`, not only a distinguished one.  This is the
periodicity half of `exists_affineTransmissionPermutation_of_submodular`,
extracted so that it applies to a `τ` obtained by other means (here: the
package supplied by `KGeneralTransmission`), without redoing the
`Submodular`-based construction of `τ`. -/
theorem IsTransmissionPermutation.isKAffine_of_torsionWitness
    {M : TwiceMarked} {D : CFDiv M.graph} {τ : ℤ → ℤ}
    (hτ : IsTransmissionPermutation M D τ) {m : ℕ} (hm : TorsionWitness M m) :
    IsKAffine m τ := by
  intro n
  have hBase := hτ.2 (τ n) n
  simp only [ite_true] at hBase
  have hShift := hτ.2 (τ n + m) (n + m)
  rw [rankDelta_marked_twist_add_torsion hm D (τ n) n] at hShift
  rw [← hBase] at hShift
  by_contra hne
  rw [ite_eq_right hne] at hShift
  norm_num at hShift

/-- Paper source: `lem:kgtImpliesTorsionOrder` (Lemma 4.2).

`k`-general transmission forces `k` to be the *exact* torsion order.

Two hypotheses beyond `KGeneralTransmission` are needed, and both are
genuine (not merely convenient) restrictions:

* `huv : M.u ≠ M.v`.  At the diagonal marking `u = v`, every positive `k` is
  a `TorsionWitness` (`TransmissionAPI.torsionWitness_diagonal`), so
  minimality can fail without distinctness.
* `hg : 0 < genus M.graph`.  At genus `0`, Riemann-Roch forces
  `rank D = max (deg D) (-1)` for *every* divisor `D` (since
  `deg (canonicalDivisor - D) < 0` whenever `deg D ≥ 0`), which makes every
  transmission permutation a pure shift with no inversions at all. In that
  case `KGeneralTransmission M k` holds simultaneously for *every* positive
  `k` (the inversion bound `≤ 0` and the periodicity clause are both
  vacuous, and the torsion condition is automatic since the Jacobian is
  trivial), so `k` is never pinned down to the torsion order `1`.  The paper
  implicitly works with graphs of nontrivial genus throughout this section;
  this hypothesis makes that explicit.

`hconn : graphConnected M.graph` is also required, matching the
connectivity hypothesis already threaded through
`exists_affine_transmission_of_allSubmodular` and the Riemann-Roch API. -/
theorem KGeneralTransmission.isTorsionOrder
    {M : TwiceMarked} {k : ℕ} (hK : KGeneralTransmission M k)
    (_huv : M.u ≠ M.v) (hconn : _root_.graphConnected M.graph)
    (hg : 0 < genus M.graph) :
    IsTorsionOrder M k := by
  obtain ⟨hTW, _hSub, hAll⟩ := hK
  have hk0 : 0 < k := hTW.1
  obtain ⟨τ, hτTP, hτAffineK, hτFinite, hτCount⟩ := hAll (0 : CFDiv M.graph)
  obtain ⟨σ, hστ, -⟩ := transmissionPermutation_rankSlipFace M 0 hconn τ hτTP
  have hSEfin : ∀ m n : ℤ, (southeastSet τ m n).Finite := by
    intro m n
    have h := σ.se_finite m n
    rwa [hστ] at h
  have hNWfin : ∀ m n : ℤ, (northwestSet τ m n).Finite := by
    intro m n
    have h := σ.nw_finite m n
    rwa [hστ] at h
  have hDegX : ∀ a b : ℤ,
      deg ((0 : CFDiv M.graph) + a • oneChip M.u - b • oneChip M.v) = a - b := by
    intro a b
    rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul, deg_one_chip, deg_one_chip, map_zero]
    ring
  -- `rank 0 = 0`, and the two neighboring degree-`(-1)` twists have rank `-1`.
  have hRank0 : rank M.graph (0 : CFDiv M.graph) = 0 := zero_divisor_rank M.graph
  have hRankNegU : rank M.graph
      ((0 : CFDiv M.graph) + (-1 : ℤ) • oneChip M.u - (0 : ℤ) • oneChip M.v) = -1 :=
    rank_neg_one_of_deg_neg M.graph _ (by rw [hDegX]; norm_num)
  have hRankNegV : rank M.graph
      ((0 : CFDiv M.graph) + (0 : ℤ) • oneChip M.u - (1 : ℤ) • oneChip M.v) = -1 :=
    rank_neg_one_of_deg_neg M.graph _ (by rw [hDegX]; norm_num)
  -- `southeastSet τ 0 0` is empty: no `ℓ ≥ 0` has `τ ℓ < 0`.
  have hSE_neg1_0 := transmission_rank_eq_southeast_ncard M 0 hconn τ hτTP (-1) 0
  rw [hRankNegU] at hSE_neg1_0
  have hSEempty1 : southeastSet τ 0 0 = ∅ := by
    have hfin := hSEfin 0 0
    rw [show (-1 : ℤ) + 1 = 0 from by ring] at hSE_neg1_0
    exact (Set.ncard_eq_zero hfin).mp (by omega)
  have hτNonneg : ∀ ℓ : ℤ, 0 ≤ ℓ → 0 ≤ τ ℓ := by
    intro ℓ hℓ
    by_contra hlt
    push Not at hlt
    have : ℓ ∈ southeastSet τ 0 0 := ⟨hℓ, hlt⟩
    rw [hSEempty1] at this
    exact this
  -- `southeastSet τ 1 1` is empty: no `ℓ ≥ 1` has `τ ℓ < 1`, i.e. `τ ℓ ≤ 0`.
  have hSE_0_1 := transmission_rank_eq_southeast_ncard M 0 hconn τ hτTP 0 1
  rw [hRankNegV] at hSE_0_1
  have hSEempty2 : southeastSet τ 1 1 = ∅ := by
    have hfin := hSEfin 1 1
    rw [show (0 : ℤ) + 1 = 1 from by ring] at hSE_0_1
    exact (Set.ncard_eq_zero hfin).mp (by omega)
  have hτPosFromOne : ∀ ℓ : ℤ, 1 ≤ ℓ → 1 ≤ τ ℓ := by
    intro ℓ hℓ
    by_contra hlt
    push Not at hlt
    have : ℓ ∈ southeastSet τ 1 1 := ⟨hℓ, hlt⟩
    rw [hSEempty2] at this
    exact this
  -- The unique `ℓ ≥ 0` with `τ ℓ ≤ 0` is `ℓ = 0`, forcing `τ 0 = 0`.
  have hX00 : (0 : CFDiv M.graph) + (0 : ℤ) • oneChip M.u - (0 : ℤ) • oneChip M.v = 0 := by
    simp
  have hSE_0_0 := transmission_rank_eq_southeast_ncard M 0 hconn τ hτTP 0 0
  rw [hX00, hRank0] at hSE_0_0
  have hSEcard1 : (southeastSet τ 1 0).ncard = 1 := by
    rw [show (0 : ℤ) + 1 = 1 from by ring] at hSE_0_0
    omega
  obtain ⟨ℓ0, hℓ0eq⟩ := Set.ncard_eq_one.mp hSEcard1
  have hℓ0mem : ℓ0 ∈ southeastSet τ 1 0 := by rw [hℓ0eq]; exact Set.mem_singleton _
  have hℓ0 : 0 ≤ ℓ0 ∧ τ ℓ0 < 1 := hℓ0mem
  have hℓ0eq0 : ℓ0 = 0 := by
    by_contra hne
    have hge1 : 1 ≤ ℓ0 := by omega
    have : ℓ0 ∈ southeastSet τ 1 1 := ⟨hge1, hℓ0.2⟩
    rw [hSEempty2] at this
    exact this
  have hτ0 : τ 0 = 0 := by
    have := hℓ0.2
    rw [hℓ0eq0] at this
    have hnn := hτNonneg 0 le_rfl
    omega
  -- `rank (canonicalDivisor) = genus - 1`.
  have hRankK : rank M.graph (canonicalDivisor M.graph) = genus M.graph - 1 := by
    have hRR := riemann_roch_for_graphs hconn (canonicalDivisor M.graph)
    have hKK : canonicalDivisor M.graph - canonicalDivisor M.graph = (0 : CFDiv M.graph) :=
      sub_self _
    rw [hKK, zero_divisor_rank] at hRR
    have hdegK := degree_of_canonical_divisor M.graph
    omega
  -- `northwestSet τ 1 0` has cardinality `genus M.graph` and is
  -- nonempty since `0 < genus M.graph`.
  have hNW := transmission_complement_rank_eq_northwest_ncard M 0 hconn τ hτTP 0 0
  have hXK : canonicalDivisor M.graph - (0 : CFDiv M.graph) -
      (0 : ℤ) • oneChip M.u + (0 : ℤ) • oneChip M.v = canonicalDivisor M.graph := by
    simp
  rw [hXK, hRankK] at hNW
  have hAcard : ((northwestSet τ 1 0).ncard : ℤ) = genus M.graph := by
    rw [show (0 : ℤ) + 1 = 1 from by ring] at hNW
    omega
  have hAnonempty : (northwestSet τ 1 0).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    intro hzero
    rw [hzero] at hAcard
    simp at hAcard
    omega
  obtain ⟨a0, ha0⟩ := hAnonempty
  have ha0' : a0 < 0 ∧ 1 ≤ τ a0 := ha0
  -- Every `a ∈ northwestSet τ 1 0` yields an ordinary inversion `(a, 0)`,
  -- and their normalizations are pairwise distinct elements of
  -- `kInversions k τ`.
  have hAinv : ∀ a ∈ northwestSet τ 1 0, (a, (0:ℤ)) ∈ invSet τ := by
    intro a ha
    have ha' : a < 0 ∧ 1 ≤ τ a := ha
    exact ⟨ha'.1, by omega⟩
  set φ : ℤ → ℤ × ℤ := fun a => (a % k, (0 : ℤ) - (a / k) * k) with hφ_def
  have hφmem : ∀ a ∈ northwestSet τ 1 0, φ a ∈ kInversions k τ := by
    intro a ha
    exact inversion_normalize_first_coordinate hk0 hτAffineK (hAinv a ha)
  have hφInj : Set.InjOn φ (northwestSet τ 1 0) := by
    intro a _ha a' _ha' heq
    simp only [hφ_def, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
    have hdk : a / k = a' / k := by
      have : (a / k) * (k : ℤ) = (a' / k) * (k : ℤ) := by linarith [h2]
      exact mul_right_cancel₀ hkz this
    have e1 : a = a % k + (a / k) * k := by
      simpa [add_comm, mul_comm] using int_eq_emod_add_ediv_period (k := k) hk0 (b := a)
    have e2 : a' = a' % k + (a' / k) * k := by
      simpa [add_comm, mul_comm] using int_eq_emod_add_ediv_period (k := k) hk0 (b := a')
    rw [e1, e2, h1, hdk]
  have hSubset : φ '' (northwestSet τ 1 0) ⊆ kInversions k τ := by
    rintro p ⟨a, ha, rfl⟩
    exact hφmem a ha
  have hCardImage : (φ '' (northwestSet τ 1 0)).ncard = (northwestSet τ 1 0).ncard :=
    Set.InjOn.ncard_image hφInj
  have hAcardNat : ((northwestSet τ 1 0).ncard : ℤ) = (Int.toNat (genus M.graph) : ℤ) := by
    rw [hAcard, Int.toNat_of_nonneg (by omega)]
  have hleft : (northwestSet τ 1 0).ncard ≤ (kInversions k τ).ncard := by
    rw [← hCardImage]
    exact Set.ncard_le_ncard hSubset hτFinite
  have hright : (kInversions k τ).ncard ≤ (northwestSet τ 1 0).ncard := by
    have h := hτCount
    unfold kInversionCount at h
    have heq : (Int.toNat (genus M.graph) : ℤ) = ((northwestSet τ 1 0).ncard : ℤ) :=
      hAcardNat.symm
    have hnat : Int.toNat (genus M.graph) = (northwestSet τ 1 0).ncard := by exact_mod_cast heq
    omega
  have hSetEq : φ '' (northwestSet τ 1 0) = kInversions k τ :=
    Set.eq_of_subset_of_ncard_le hSubset (by omega) hτFinite
  -- For every torsion witness `n`, periodicity of `τ` produces an inversion
  -- `(a0 + n, n)` whose normalization forces `k ∣ n`.
  refine ⟨hTW, ?_⟩
  intro n hn
  have hAffineN : IsKAffine n τ := hτTP.isKAffine_of_torsionWitness hn
  have hτn : τ (n : ℤ) = n := by
    have h := hAffineN 0
    rw [zero_add, hτ0, zero_add] at h
    exact h
  have hτa0n : τ (a0 + n) = τ a0 + n := hAffineN a0
  have hInv : (a0 + (n : ℤ), (n : ℤ)) ∈ invSet τ := by
    refine ⟨by linarith [ha0'.1], ?_⟩
    rw [hτa0n, hτn]
    linarith [ha0'.2]
  have hNorm := inversion_normalize_first_coordinate hk0 hτAffineK hInv
  rw [← hSetEq] at hNorm
  obtain ⟨a, ha, hEq⟩ := hNorm
  simp only [hφ_def, Prod.mk.injEq] at hEq
  obtain ⟨_, hEq2⟩ := hEq
  have hDvdZ : (k : ℤ) ∣ (n : ℤ) := by
    refine ⟨((a0 + n) / k) - (a / k), ?_⟩
    linarith [hEq2]
  have hDvd : k ∣ n := by exact_mod_cast hDvdZ
  exact Nat.le_of_dvd hn.1 hDvd

/-- TeX label: `lem:kgtImpliesTorsionOrder` (Lemma 4.2).

`k`-general transmission forces `k` to be the *exact* torsion order of
`(G, u, v)`, not merely a period that annihilates `u - v`
(`KGeneralTransmission.to_torsionWitness` already gives that weaker fact for
free).  The full mechanized argument is `KGeneralTransmission.isTorsionOrder`
above; this is a thin restatement at the `mark` API used by the rest of the
library.

Two hypotheses beyond the paper statement are required — see the docstring
of `KGeneralTransmission.isTorsionOrder` for why both are genuine gaps in a
literal reading of the lemma (not artificial strengthenings): `hconn`
(connectivity, needed for the Riemann-Roch input used throughout this
section) and `hg` (positive genus, since at genus `0` every positive `k`
satisfies `KGeneralTransmission` simultaneously, so `k` is never pinned to
the torsion order `1` there). `huv` matches the paper's own distinctness
convention (`FORMALIZATION_NOTES.md`, "Distinctness of the two marks"); the diagonal
marking `u = v` has a `TorsionWitness` at *every* period
(`torsionWitness_diagonal`), so minimality can fail without it. -/
theorem banana_kGeneral_isTorsionOrder
    {g k : ℕ} (B : Banana g) (u v : B.graph.V) (huv : u ≠ v)
    (hg : 0 < genus B.graph)
    (hK : KGeneralTransmission (mark B.graph u v) k) :
    IsTorsionOrder (mark B.graph u v) k :=
  hK.isTorsionOrder huv (banana_graph_connected B) hg

end Bananas
