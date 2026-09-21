/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.SignChangingInversions
import LeanPool.BrillNoetherGraphs.Bananas.Classification.WeierstrassPartition
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Sign-changing inversions and Weierstrass partitions

This file proves Proposition 6.10 (`prop:sciLambda`) of
the twice-marked banana paper: the number of sign-changing inversions of a
transmission permutation is the size of the Weierstrass partition at its
second marked point.
-/

namespace Bananas

open Utilities

/-- At every pole order the transmission permutation takes a nonpositive
value.  The relevant position is `-s_i`, correcting the missing minus sign in
the prose proof of Proposition 6.10. -/
theorem transmission_neg_poleOrder_nonpos
    {G : CFGraph} (u v : G.V) (hG : _root_.graph_connected G)
    (D : CFDiv G) (tau : ℤ → ℤ)
    (hTau : IsTransmissionPermutation (mark G u v) D tau) (i : ℕ) :
    tau (-poleOrder G v D i) ≤ 0 := by
  obtain ⟨sigma, hFunc, hRank⟩ :=
    exists_aspPerm_rank_eq_of_isTransmissionPermutation u v hG D tau hTau
  rw [← hFunc]
  have hAt := rank_poleOrder_eq hG v D i
  have hBefore := rank_poleOrder_sub_one_eq hG v D i
  have hAtFormula := hRank 0 (-poleOrder G v D i)
  have hBeforeFormula := hRank 0 (-(poleOrder G v D i - 1))
  have hAtDiv :
      D + (0 : ℤ) • one_chip u - (-poleOrder G v D i) • one_chip v =
        D + poleOrder G v D i • one_chip v := by
    funext w
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hBeforeDiv :
      D + (0 : ℤ) • one_chip u - (-(poleOrder G v D i - 1)) • one_chip v =
        D + (poleOrder G v D i - 1) • one_chip v := by
    funext w
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hAtDiv, hAt] at hAtFormula
  rw [hBeforeDiv, hBefore] at hBeforeFormula
  have hAtFormula' : (i : ℤ) = sigma.s 1 (-poleOrder G v D i) - 1 := by
    simpa using hAtFormula
  have hBeforeFormula' : (i : ℤ) - 1 =
      sigma.s 1 (-(poleOrder G v D i - 1)) - 1 := by
    simpa using hBeforeFormula
  have hArg : -(poleOrder G v D i - 1) = -poleOrder G v D i + 1 := by
    ring
  rw [hArg] at hBeforeFormula'
  have hDrop : sigma.s 1 (-poleOrder G v D i + 1) <
      sigma.s 1 (-poleOrder G v D i) := by
    omega
  have hValue := (sigma.b_step_lt_iff 1 (-poleOrder G v D i)).mp hDrop
  omega

/-- Every nonpositive transmission value occurs at exactly one negated pole
order. -/
theorem exists_eq_neg_poleOrder_of_transmission_nonpos
    {G : CFGraph} (u v : G.V) (hG : _root_.graph_connected G)
    (D : CFDiv G) (tau : ℤ → ℤ)
    (hTau : IsTransmissionPermutation (mark G u v) D tau)
    {b : ℤ} (hb : tau b ≤ 0) :
    ∃ i : ℕ, b = -poleOrder G v D i := by
  obtain ⟨sigma, hFunc, hRank⟩ :=
    exists_aspPerm_rank_eq_of_isTransmissionPermutation u v hG D tau hTau
  have hbSigma : sigma b < 1 := by rw [hFunc]; omega
  have hStep := (sigma.b_step_one_iff 1 b).mpr hbSigma
  let ell : ℤ := -b
  let r : ℤ := rank G (D + ell • one_chip v)
  have hAtFormula := hRank 0 b
  have hBeforeFormula := hRank 0 (b + 1)
  have hAtDiv :
      D + (0 : ℤ) • one_chip u - b • one_chip v =
        D + ell • one_chip v := by
    dsimp [ell]
    funext w
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hBeforeDiv :
      D + (0 : ℤ) • one_chip u - (b + 1) • one_chip v =
        D + (ell - 1) • one_chip v := by
    dsimp [ell]
    funext w
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hAtDiv] at hAtFormula
  rw [hBeforeDiv] at hBeforeFormula
  have hAtFormula' : rank G (D + ell • one_chip v) =
      sigma.s 1 b - 1 := by simpa using hAtFormula
  have hBeforeFormula' : rank G (D + (ell - 1) • one_chip v) =
      sigma.s 1 (b + 1) - 1 := by simpa using hBeforeFormula
  have hrFormula : r = sigma.s 1 b - 1 := by
    dsimp [r]
    exact hAtFormula'
  have hBeforeRank :
      rank G (D + (ell - 1) • one_chip v) = r - 1 := by
    rw [hStep] at hBeforeFormula'
    omega
  have hrNonneg : 0 ≤ r := by
    have hsNonneg := sigma.s_nonneg 1 (b + 1)
    omega
  let i : ℕ := r.toNat
  have hiCast : (i : ℤ) = r := by
    dsimp [i]
    rw [Int.toNat_of_nonneg hrNonneg]
  refine ⟨i, ?_⟩
  have hPole := poleOrder_eq_of_rank_crossing hG v D i ell
    (by dsimp [r] at hiCast; dsimp [r] at hrFormula; omega)
    (by rw [hBeforeRank]; omega)
  dsimp [ell] at hPole ⊢
  omega

/-- The northwest fiber at the negated `i`th pole has cardinality the `i`th
Weierstrass part. -/
theorem northwest_ncard_neg_poleOrder_eq_weierstrassPart
    {G : CFGraph} (u v : G.V) (hG : _root_.graph_connected G)
    (D : CFDiv G) (tau : ℤ → ℤ)
    (hTau : IsTransmissionPermutation (mark G u v) D tau) (i : ℕ) :
    (northwest_set tau 1 (-poleOrder G v D i)).ncard =
      weierstrassPart G v D i := by
  have hNW := transmission_complement_rank_eq_northwest_ncard
    (mark G u v) D hG tau hTau 0 (-poleOrder G v D i)
  change rank G
      (canonical_divisor G - D - (0 : ℤ) • one_chip u +
        (-poleOrder G v D i) • one_chip v) + 1 =
      ((northwest_set tau 1 (-poleOrder G v D i)).ncard : ℤ) at hNW
  have hXRank := rank_poleOrder_eq hG v D i
  let X : CFDiv G := D + poleOrder G v D i • one_chip v
  have hRR := riemann_roch_for_graphs hG X
  have hDegree : deg X = deg D + poleOrder G v D i := by
    dsimp [X]
    rw [deg.map_add, map_zsmul, deg_one_chip]
    norm_num
  have hComplement :
      canonical_divisor G - D - (0 : ℤ) • one_chip u +
          (-poleOrder G v D i) • one_chip v =
        canonical_divisor G - X := by
    dsimp [X]
    funext w
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hPart := weierstrassPart_cast hG v D i
  unfold weierstrassPartInt at hPart
  rw [hComplement] at hNW
  rw [hXRank, hDegree] at hRR
  exact_mod_cast (show
    ((northwest_set tau 1 (-poleOrder G v D i)).ncard : ℤ) =
      (weierstrassPart G v D i : ℤ) by omega)

/-- The sign-changing inversions in the row with second coordinate `b`. -/
def sciRow (tau : ℤ → ℤ) (b : ℤ) : Set (ℤ × ℤ) :=
  (fun a : ℤ => (a, b)) '' northwest_set tau 1 b

theorem sciRow_ncard (tau : ℤ → ℤ) (b : ℤ) :
    (sciRow tau b).ncard = (northwest_set tau 1 b).ncard := by
  exact Set.ncard_image_of_injective _ (fun _ _ h => by simpa using congrArg Prod.fst h)

theorem sci_eq_weierstrassSize
    {G : CFGraph} (u v : G.V) (hG : _root_.graph_connected G)
    (D : CFDiv G) (tau : ℤ → ℤ)
    (hTau : IsTransmissionPermutation (mark G u v) D tau) :
    sci tau = weierstrassSize hG v D := by
  classical
  obtain ⟨sigma, hFunc, _hRank⟩ :=
    exists_aspPerm_rank_eq_of_isTransmissionPermutation u v hG D tau hTau
  let rows : Fin (genus G).toNat → Set (ℤ × ℤ) := fun i =>
    sciRow tau (-poleOrder G v D i)
  have hRowsFinite : ∀ i, (rows i).Finite := by
    intro i
    apply Set.Finite.image
    rw [← hFunc]
    exact sigma.nw_finite 1 (-poleOrder G v D i)
  have hRowsDisjoint : Pairwise (fun i j => Disjoint (rows i) (rows j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro p hpi hpj
    rcases hpi with ⟨a, _ha, rfl⟩
    rcases hpj with ⟨a', _ha', hEq⟩
    have hPoleEq := congrArg Prod.snd hEq
    have hPoleEq' : poleOrder G v D i = poleOrder G v D j :=
      neg_injective hPoleEq.symm
    have hIndexEq : (i : ℕ) = j :=
      (poleOrder_strictMono hG v D).injective hPoleEq'
    exact hij (Fin.ext hIndexEq)
  have hUnion : sciSet tau = ⋃ i, rows i := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨hpLt, hpPos, hpNonpos⟩
      obtain ⟨i, hiPole⟩ :=
        exists_eq_neg_poleOrder_of_transmission_nonpos u v hG D tau hTau hpNonpos
      have hNWmem : p.1 ∈ northwest_set tau 1 p.2 := by
        exact ⟨hpLt, by omega⟩
      have hNWfinite : (northwest_set tau 1 p.2).Finite := by
        rw [← hFunc]
        exact sigma.nw_finite 1 p.2
      have hNWpos : 0 < (northwest_set tau 1 p.2).ncard :=
        (Set.ncard_pos hNWfinite).mpr ⟨p.1, hNWmem⟩
      have hPartPos : 0 < weierstrassPart G v D i := by
        rw [hiPole,
          northwest_ncard_neg_poleOrder_eq_weierstrassPart u v hG D tau hTau i]
          at hNWpos
        exact hNWpos
      have hiGenus : i < (genus G).toNat := by
        by_contra hi
        have hZero := weierstrassPart_eq_zero_of_genus_le hG v D i
          (Nat.le_of_not_gt hi)
        omega
      apply Set.mem_iUnion.mpr
      refine ⟨⟨i, hiGenus⟩, ?_⟩
      refine ⟨p.1, ?_, Prod.ext rfl ?_⟩
      · simpa [hiPole] using hNWmem
      · simp only
        exact hiPole.symm
    · intro hp
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
      rcases hi with ⟨a, ha, rfl⟩
      change a < -poleOrder G v D i ∧ 0 < tau a ∧
        tau (-poleOrder G v D i) ≤ 0
      exact ⟨ha.1, lt_of_lt_of_le Int.zero_lt_one ha.2,
        transmission_neg_poleOrder_nonpos u v hG D tau hTau i⟩
  rw [sci, hUnion, Set.ncard_iUnion_of_finite hRowsFinite hRowsDisjoint,
    finsum_eq_sum_of_fintype, weierstrassSize_eq_sum]
  calc
    (∑ i, (rows i).ncard) =
        ∑ i : Fin (genus G).toNat, weierstrassPart G v D i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [sciRow_ncard,
        northwest_ncard_neg_poleOrder_eq_weierstrassPart u v hG D tau hTau]
    _ = ∑ i ∈ Finset.range (genus G).toNat,
        weierstrassPart G v D i :=
      Fin.sum_univ_eq_sum_range (weierstrassPart G v D) _

end Bananas
