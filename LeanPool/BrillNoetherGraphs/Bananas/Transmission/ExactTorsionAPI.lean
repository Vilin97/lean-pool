/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaNonrecurrence
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.AffineInversionFinite

/-!
# Exact torsion period API

The definition `IsTorsionOrder` records minimal positive annihilation.  This
file derives the group-theoretic consequence used throughout the paper: its
period divides every other annihilating period.
-/

namespace Bananas

open Utilities

/-- Any positive torsion witness has a least positive witness below it.  This
is the elementary well-ordering bridge from a period calculation to the
paper's exact torsion order. -/
theorem exists_isTorsionOrder_of_torsionWitness
    {M : TwiceMarked} {k : ℕ} (hWitness : TorsionWitness M k) :
    ∃ n : ℕ, IsTorsionOrder M n := by
  classical
  let P : ℕ → Prop := fun n => TorsionWitness M n
  have hExists : ∃ n : ℕ, P n := ⟨k, hWitness⟩
  refine ⟨Nat.find hExists, Nat.find_spec hExists, ?_⟩
  intro m hm
  exact Nat.find_min' hExists hm

/-- The Euclidean remainder of an annihilating marked difference is again
principal. -/
theorem marked_difference_remainder_linearEquiv_zero
    {M : TwiceMarked} {k m : ℕ}
    (hk : TorsionWitness M k)
    (hm : linearEquiv M.graph
      ((m : ℤ) • (oneChip M.u - oneChip M.v)) 0) :
    linearEquiv M.graph
      ((m % k : ℤ) • (oneChip M.u - oneChip M.v)) 0 := by
  rcases hk with ⟨_hkPos, hkEq⟩
  unfold linearEquiv at hkEq hm ⊢
  let q : ℕ := m / k
  let diff : CFDiv M.graph := oneChip M.u - oneChip M.v
  have hq : 0 - ((q * k : ℕ) : ℤ) • diff ∈ principalDivisors M.graph := by
    have hScale := AddSubgroup.zsmul_mem (principalDivisors M.graph) hkEq (q : ℤ)
    have hEq : (q : ℤ) • (0 - (k : ℤ) • diff) =
        0 - ((q * k : ℕ) : ℤ) • diff := by
      dsimp [diff]
      rw [smul_sub, smul_zero, smul_smul]
    rw [hEq] at hScale
    exact hScale
  have hSubtract := (principalDivisors M.graph).sub_mem hm hq
  have hDiv : m = q * k + m % k := by
    simpa [q, Nat.mul_comm] using (Nat.div_add_mod m k).symm
  have hDiff :
      (0 - (m : ℤ) • diff) - (0 - ((q * k : ℕ) : ℤ) • diff) =
        0 - ((m % k : ℕ) : ℤ) • diff := by
    have hCast : (m : ℤ) = (q * k : ℕ) + m % k := by
      exact_mod_cast hDiv
    rw [hCast, add_smul]
    abel
  rw [hDiff] at hSubtract
  exact hSubtract

/-- The least positive torsion period divides every other positive torsion
period. -/
theorem isTorsionOrder_dvd_of_torsionWitness
    {M : TwiceMarked} {k m : ℕ}
    (hk : IsTorsionOrder M k) (hm : TorsionWitness M m) :
    k ∣ m := by
  by_contra hNotDvd
  have hkPos := hk.1.1
  have hRemPos : 0 < m % k := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      apply hNotDvd
      exact (Nat.dvd_iff_mod_eq_zero).mpr hzero)
  have hRemEq := marked_difference_remainder_linearEquiv_zero hk.1 hm.2
  have hRem : TorsionWitness M (m % k) := ⟨hRemPos, hRemEq⟩
  have hMin := hk.2 (m % k) hRem
  have hRemLt : m % k < k := Nat.mod_lt _ hkPos
  omega

/-- Linear-equivalent degree twists have an annihilating difference index. -/
theorem marked_difference_linearEquiv_zero_of_degreeTwistInt_linearEquiv
    {M : TwiceMarked} (D : CFDiv M.graph) (d b c : ℤ)
    (hbc : linearEquiv M.graph
      (degreeTwistInt M D d b) (degreeTwistInt M D d c)) :
    linearEquiv M.graph
      ((b - c) • (oneChip M.u - oneChip M.v)) 0 := by
  unfold degreeTwistInt at hbc
  unfold linearEquiv at hbc ⊢
  convert hbc using 1
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply]
  ring

/-- At an exact torsion order, two distinct integer degree-twist indices can
represent the same class only when their difference is a multiple of the
period. -/
theorem isTorsionOrder_dvd_natAbs_sub_of_degreeTwistInt_linearEquiv
    {M : TwiceMarked} {k : ℕ} (hk : IsTorsionOrder M k)
    (D : CFDiv M.graph) (d b c : ℤ)
    (hbc : linearEquiv M.graph
      (degreeTwistInt M D d b) (degreeTwistInt M D d c)) :
    k ∣ (b - c).natAbs := by
  by_cases hzero : b = c
  · subst c
    simp
  have hSigned :=
    marked_difference_linearEquiv_zero_of_degreeTwistInt_linearEquiv D d b c hbc
  have hPos : 0 < (b - c).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hzero)
  have hAbs : linearEquiv M.graph
      (((b - c).natAbs : ℤ) • (oneChip M.u - oneChip M.v)) 0 := by
    by_cases hNonneg : 0 ≤ b - c
    · have hCast : ((b - c).natAbs : ℤ) = b - c := by
        rw [Int.natCast_natAbs, abs_of_nonneg hNonneg]
      rw [hCast]
      exact hSigned
    · unfold linearEquiv at hSigned ⊢
      have hNeg := (principalDivisors M.graph).neg_mem hSigned
      have hCast : ((b - c).natAbs : ℤ) = -(b - c) := by
        rw [Int.natCast_natAbs, abs_of_nonpos (by omega)]
      rw [hCast]
      rw [show 0 - (-(b - c)) • (oneChip M.u - oneChip M.v) =
          -(0 - (b - c) • (oneChip M.u - oneChip M.v)) by
        rw [neg_smul]
        abel]
      exact hNeg
  exact isTorsionOrder_dvd_of_torsionWitness hk ⟨hPos, hAbs⟩

/-- On one half-open fundamental period, fixed-degree twist representatives
are pairwise inequivalent. -/
theorem degreeTwistInt_injective_on_fundamental_period
    {M : TwiceMarked} {k : ℕ} (hk : IsTorsionOrder M k)
    (D : CFDiv M.graph) (d b c : ℤ)
    (hb0 : 0 ≤ b) (hb : b < k)
    (hc0 : 0 ≤ c) (hc : c < k)
    (hbc : linearEquiv M.graph
      (degreeTwistInt M D d b) (degreeTwistInt M D d c)) :
    b = c := by
  have hDvd := isTorsionOrder_dvd_natAbs_sub_of_degreeTwistInt_linearEquiv
    hk D d b c hbc
  by_contra hne
  have hAbsPos : 0 < (b - c).natAbs :=
    Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hAbsLt : (b - c).natAbs < k := by
    have hAbsLtZ : ((b - c).natAbs : ℤ) < k := by
      rw [Int.natCast_natAbs, abs_lt]
      omega
    exact_mod_cast hAbsLtZ
  have hkle : k ≤ (b - c).natAbs := Nat.le_of_dvd hAbsPos hDvd
  omega

/-- A signed marked-difference twist is linearly equivalent to its Euclidean
residue modulo any torsion witness. -/
theorem marked_difference_mod_period_linearEquiv
    {M : TwiceMarked} {k : ℕ} (hk : TorsionWitness M k) (z : ℤ) :
    linearEquiv M.graph
      (z • (oneChip M.u - oneChip M.v))
      ((z % k) • (oneChip M.u - oneChip M.v)) := by
  rcases hk with ⟨hkPos, hkEq⟩
  let q : ℤ := z / k
  let r : ℤ := z % k
  let diff : CFDiv M.graph := oneChip M.u - oneChip M.v
  have hRepr : z = r + q * k := by
    dsimp [r, q]
    simpa [add_comm, mul_comm] using int_eq_emod_add_ediv_period (k := k) hkPos (b := z)
  unfold linearEquiv at hkEq ⊢
  have hScale := AddSubgroup.zsmul_mem (principalDivisors M.graph) hkEq q
  have hScale' : 0 - (q * k) • diff ∈ principalDivisors M.graph := by
    convert hScale using 1
    dsimp [diff]
    ext x
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply]
    ring
  have hDiff : r • diff - z • diff = 0 - (q * k) • diff := by
    rw [hRepr, add_smul]
    abel
  rw [hDiff]
  exact hScale'

/-- Adding a fixed divisor preserves linear equivalence. -/
theorem linearEquiv_add_left_of_linearEquiv
    {G : CFGraph} {A B C : CFDiv G}
    (hAB : linearEquiv G A B) :
    linearEquiv G (C + A) (C + B) := by
  unfold linearEquiv at hAB ⊢
  have h : (C + B) - (C + A) = B - A := by abel
  rw [h]
  exact hAB

/-- In the half-open fundamental interval, congruence modulo a positive
period is equality. -/
theorem int_eq_of_emod_sub_eq_zero_of_fundamental
    {k b c : ℤ} (hk : 0 < k)
    (hb0 : 0 ≤ b) (hb : b < k)
    (hc0 : 0 ≤ c) (hc : c < k)
    (hmod : (b - c) % k = 0) :
    b = c := by
  have hDvd : k ∣ b - c := (Int.dvd_iff_emod_eq_zero).mpr hmod
  by_contra hne
  have hAbsPos : 0 < (b - c).natAbs :=
    Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hAbsLt : (b - c).natAbs < k.natAbs := by
    have hCast : ((b - c).natAbs : ℤ) < (k.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_pos hk, abs_lt]
      omega
    exact_mod_cast hCast
  have hzero : b - c = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hDvd hAbsLt
  exact hne (sub_eq_zero.mp hzero)

end Bananas
