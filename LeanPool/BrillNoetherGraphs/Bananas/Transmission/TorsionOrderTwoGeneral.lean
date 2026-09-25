/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionAPI

/-!
# Torsion order two plus submodularity gives `2`-general transmission

Paper source: `lem-TO2GenTrans` (Lemma 4.3).  This is the (only) partial
converse to `lem:kgtImpliesTorsionOrder` (Lemma 4.2, `TorsionOrderExact.lean`):
at `k = 2` exactly, torsion order plus all-divisor submodularity is already
enough to force `2`-general transmission, without any further geometric input.

The proof follows the published argument.  The existence/periodicity half of
`KGeneralTransmission` is already available from
`exists_affine_transmission_of_allSubmodular`.  What remains is the
`2`-inversion count bound `kInversionCount 2 τ ≤ genus`, which the paper
derives from the Riemann-Roch inequality `eq-RRTauBounds`:
`b - deg D ≤ τ_D(b) ≤ 2g + b - deg D`.  We prove this bound directly (as
`transmissionPermutation_ge` / `transmissionPermutation_le`, valid for *any*
transmission permutation of *any* connected twice-marked graph, no
submodularity needed), then combine the two consecutive instances at `b = 0`
and `b = 1` with the periodicity `τ(n + 2) = τ(n) + 2` to bound the
`2`-inversion count.
-/

@[expose] public section

namespace Bananas

open Utilities

/-! ## The Riemann-Roch bound on a transmission permutation -/

private theorem deg_markedTwist (M : TwiceMarked) (D : CFDiv M.graph) (x y : ℤ) :
    deg (D + x • oneChip M.u - y • oneChip M.v) = deg D + x - y := by
  rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul, deg_one_chip, deg_one_chip]
  simp only [smul_eq_mul, mul_one]

private theorem markedTwist_sub_u (M : TwiceMarked) (D : CFDiv M.graph) (x y : ℤ) :
    D + x • oneChip M.u - y • oneChip M.v - oneChip M.u =
      D + (x - 1) • oneChip M.u - y • oneChip M.v := by
  rw [sub_smul, one_smul]
  abel

private theorem markedTwist_sub_v (M : TwiceMarked) (D : CFDiv M.graph) (x y : ℤ) :
    D + x • oneChip M.u - y • oneChip M.v - oneChip M.v =
      D + x • oneChip M.u - (y + 1) • oneChip M.v := by
  rw [add_smul, one_smul]
  ext w
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- Paper source: `eq-RRTauBounds`, lower half.  No submodularity is needed:
this is a direct consequence of the two-term rank-vanishing pattern below the
degree-`0` threshold. -/
theorem transmissionPermutation_ge
    {M : TwiceMarked} {D : CFDiv M.graph} {τ : ℤ → ℤ}
    (hτ : IsTransmissionPermutation M D τ) (b : ℤ) :
    b - deg D ≤ τ b := by
  by_contra hlt
  push Not at hlt
  have hInd := hτ.2 (τ b) b
  rw [if_pos rfl] at hInd
  set a := τ b with ha_def
  have hd0 : deg (D + a • oneChip M.u - b • oneChip M.v) < 0 := by
    rw [deg_markedTwist]; omega
  have hd1 : deg (D + (a - 1) • oneChip M.u - b • oneChip M.v) < 0 := by
    rw [deg_markedTwist]; omega
  have hd2 : deg (D + a • oneChip M.u - (b + 1) • oneChip M.v) < 0 := by
    rw [deg_markedTwist]; omega
  have hd3 : deg (D + (a - 1) • oneChip M.u - (b + 1) • oneChip M.v) < 0 := by
    rw [deg_markedTwist]; omega
  have hR0 := rank_neg_one_of_deg_neg M.graph _ hd0
  have hR1 := rank_neg_one_of_deg_neg M.graph _ hd1
  have hR2 := rank_neg_one_of_deg_neg M.graph _ hd2
  have hR3 := rank_neg_one_of_deg_neg M.graph _ hd3
  have hDelta : rankDelta M (D + a • oneChip M.u - b • oneChip M.v) = 0 := by
    unfold rankDelta
    simp only [markedTwist_sub_u, markedTwist_sub_v]
    rw [hR0, hR1, hR2, hR3]
    norm_num
  rw [hDelta] at hInd
  norm_num at hInd

/-- Paper source: `eq-RRTauBounds`, upper half.  Uses `rank_nonspecial_range`
(Riemann's part of Riemann-Roch) rather than submodularity. -/
theorem transmissionPermutation_le
    {M : TwiceMarked} {D : CFDiv M.graph} {τ : ℤ → ℤ}
    (hconn : _root_.graphConnected M.graph)
    (hτ : IsTransmissionPermutation M D τ) (b : ℤ) :
    τ b ≤ 2 * genus M.graph + b - deg D := by
  by_contra hlt
  push Not at hlt
  have hInd := hτ.2 (τ b) b
  rw [if_pos rfl] at hInd
  set a := τ b with ha_def
  have hd0 : deg (D + a • oneChip M.u - b • oneChip M.v) > 2 * genus M.graph - 2 := by
    rw [deg_markedTwist]; omega
  have hd1 : deg (D + (a - 1) • oneChip M.u - b • oneChip M.v) > 2 * genus M.graph - 2 := by
    rw [deg_markedTwist]; omega
  have hd2 : deg (D + a • oneChip M.u - (b + 1) • oneChip M.v) > 2 * genus M.graph - 2 := by
    rw [deg_markedTwist]; omega
  have hd3 : deg (D + (a - 1) • oneChip M.u - (b + 1) • oneChip M.v) >
      2 * genus M.graph - 2 := by
    rw [deg_markedTwist]; omega
  have hR0 := (rank_nonspecial_range hconn _).2.2 hd0
  have hR1 := (rank_nonspecial_range hconn _).2.2 hd1
  have hR2 := (rank_nonspecial_range hconn _).2.2 hd2
  have hR3 := (rank_nonspecial_range hconn _).2.2 hd3
  have hDelta : rankDelta M (D + a • oneChip M.u - b • oneChip M.v) = 0 := by
    unfold rankDelta
    simp only [markedTwist_sub_u, markedTwist_sub_v]
    rw [hR0, hR1, hR2, hR3]
    simp only [deg_markedTwist]
    ring
  rw [hDelta] at hInd
  norm_num at hInd

/-! ## The `2`-inversion count bound -/

/-- Paper source: proof of `lem-TO2GenTrans`.  Any affine transmission
permutation at period `2` has `2`-inversion count at most the genus,
regardless of submodularity: the bound only uses `transmissionPermutation_ge`
/ `transmissionPermutation_le` at `b = 0, 1` together with the periodicity
`τ(n + 2) = τ(n) + 2`. -/
theorem kInversionCount_two_le_genus
    {M : TwiceMarked} {D : CFDiv M.graph} {τ : ℤ → ℤ}
    (hconn : _root_.graphConnected M.graph)
    (hτ : IsTransmissionPermutation M D τ) (hAff : IsKAffine 2 τ) :
    kInversionCount 2 τ ≤ Int.toNat (genus M.graph) := by
  have hA0 := transmissionPermutation_ge hτ 0
  have hA1 := transmissionPermutation_ge hτ 1
  have hB0 := transmissionPermutation_le hconn hτ 0
  have hB1 := transmissionPermutation_le hconn hτ 1
  have hDiff01 : τ 0 - τ 1 ≤ 2 * genus M.graph - 1 := by omega
  have hDiff10 : τ 1 - τ 0 ≤ 2 * genus M.graph + 1 := by omega
  have hShift : ∀ r k : ℤ, τ (r + k * 2) = τ r + k * 2 := by
    intro r k
    have h := hAff.iterate_int r k
    push_cast at h
    exact h
  set f : ℤ × ℤ → ℤ := fun p => if p.1 = 0 then (p.2 - 1) / 2 else (p.2 - 2) / 2 with hf_def
  have hne10 : (1 : ℤ) ≠ 0 := by norm_num
  -- Every `n : ℤ` is either `r + k * 2` for `r = 0` (even) or `r = 1` (odd),
  -- with `k` an explicit witness; substituting this form (rather than
  -- rewriting `n % 2` inside a periodicity hypothesis) keeps every later
  -- occurrence of `τ (r + k * 2)` syntactically identical, so `omega` can
  -- match it against `hShift r k` directly.
  have hSplit : ∀ n : ℤ, (∃ k : ℤ, n = 0 + k * 2) ∨ (∃ k : ℤ, n = 1 + k * 2) := by
    intro n
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h | h
    · exact Or.inl ⟨n / 2, by omega⟩
    · exact Or.inr ⟨n / 2, by omega⟩
  have hMem : ∀ p ∈ kInversions 2 τ, f p ∈ (↑(Finset.Ico (0 : ℤ) (genus M.graph)) : Set ℤ) := by
    rintro ⟨m, n⟩ hp
    obtain ⟨hmn, hτmn, hm0, hmk⟩ := hp
    simp only at hmn hτmn hm0 hmk
    simp only [Finset.coe_Ico, Set.mem_Ico, hf_def]
    have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with hm' | hm'
    · subst hm'
      rw [if_pos rfl]
      rcases hSplit n with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;>
        have hτ2k0 := hShift 0 k <;> have hτ2k1 := hShift 1 k <;> omega
    · subst hm'
      rw [if_neg hne10]
      rcases hSplit n with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;>
        have hτ2k0 := hShift 0 k <;> have hτ2k1 := hShift 1 k <;> omega
  have hInj : Set.InjOn f (kInversions 2 τ) := by
    rintro ⟨m, n⟩ hp ⟨m', n'⟩ hp' hEq
    obtain ⟨hmn, hτmn, hm0, hmk⟩ := hp
    obtain ⟨hmn', hτmn', hm0', hmk'⟩ := hp'
    simp only at hmn hτmn hm0 hmk hmn' hτmn' hm0' hmk'
    simp only [hf_def] at hEq
    have hm01 : m = 0 ∨ m = 1 := by omega
    have hm01' : m' = 0 ∨ m' = 1 := by omega
    rcases hm01 with hm' | hm' <;> subst hm' <;>
      rcases hm01' with hm'' | hm'' <;> subst hm'' <;>
      first
        | rw [if_pos rfl, if_pos rfl] at hEq
        | rw [if_pos rfl, if_neg hne10] at hEq
        | rw [if_neg hne10, if_pos rfl] at hEq
        | rw [if_neg hne10, if_neg hne10] at hEq
    all_goals
      rcases hSplit n with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;>
        rcases hSplit n' with ⟨k', hk'⟩ | ⟨k', hk'⟩ <;> subst hk' <;>
        have hτk0 := hShift 0 k <;> have hτk1 := hShift 1 k <;>
        have hτk0' := hShift 0 k' <;> have hτk1' := hShift 1 k' <;>
        simp only [Prod.mk.injEq, true_and] <;> omega
  have hFinite : ((↑(Finset.Ico (0 : ℤ) (genus M.graph)) : Set ℤ)).Finite :=
    (Finset.Ico _ _).finite_toSet
  have hle := Set.ncard_le_ncard_of_injOn f hMem hInj hFinite
  have hCard : ((↑(Finset.Ico (0 : ℤ) (genus M.graph)) : Set ℤ)).ncard =
      Int.toNat (genus M.graph) := by
    rw [Set.ncard_coe_finset, Int.card_Ico, sub_zero]
  show (kInversions 2 τ).ncard ≤ Int.toNat (genus M.graph)
  rw [← hCard]
  exact hle

/-! ## Main theorem -/

/-- Paper source: `lem-TO2GenTrans` (Lemma 4.3).

If `(G, u, v)` has torsion order exactly `2` and every divisor is
submodular, then `(G, u, v)` has `2`-general transmission.  This is a
genuine partial converse to `lem:kgtImpliesTorsionOrder`
(`KGeneralTransmission.isTorsionOrder` in `TorsionOrderExact.lean`), valid
only at `k = 2`: connectivity is the only hypothesis needed beyond the paper
statement, matching every other theorem in this file's dependency chain. -/
theorem torsionOrder_two_allSubmodular_isKGeneral
    {M : TwiceMarked} (hconn : _root_.graphConnected M.graph)
    (hTO : IsTorsionOrder M 2) (hSub : AllSubmodular M) :
    KGeneralTransmission M 2 := by
  refine ⟨hTO.1, hSub, ?_⟩
  intro D
  obtain ⟨τ, hτ, hAff, hFin⟩ :=
    exists_affine_transmission_of_allSubmodular hconn hTO.1 hSub D
  exact ⟨τ, hτ, hAff, hFin, kInversionCount_two_le_genus hconn hτ hAff⟩

end Bananas
