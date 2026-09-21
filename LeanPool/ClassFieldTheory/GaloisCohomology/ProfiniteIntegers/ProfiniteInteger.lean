/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Neighborhoods
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Index
import LeanPool.ClassFieldTheory.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore

/-! # Profinite Integer -/
namespace ClassFormation

/-!
# normalized degree and Frobenius theory: the profinite integers

This file supplies the source-producing facts about `ℤ̂` used to normalize the
surjection in the opening datum of abstract valuation theory.  In particular,
multiplication by a positive integer identifies `ℤ̂` with the closed subgroup
`n ℤ̂`, which is the kernel of reduction modulo `n`.
-/

noncomputable section

/-- Distinct natural powers of the canonical positive generator of `ℤ̂` are
distinct.  This common exponent-uniqueness fact is independent of the later
reciprocity constructions that use it. -/
theorem proCIntegerOne_pow_nat_injective :
    Function.Injective (fun n : ℕ =>
      (Multiplicative.ofAdd (1 : ZHat)) ^ n) := by
  intro a b hab
  let m := a + b + 1
  have hm : 0 < m := by simp [m]
  have ha : a < m := by omega
  have hb : b < m := by omega
  have habAdd := congrArg Multiplicative.toAdd hab
  have habAdd' : a • (1 : ZHat) = b • (1 : ZHat) := by
    simpa using habAdd
  have habRed := congrArg (fun z : ZHat => zHatReduction m hm z) habAdd'
  have hredOne : zHatReduction m hm (1 : ZHat) = 1 :=
    rfl
  change zHatReduction m hm (a • (1 : ZHat)) =
      zHatReduction m hm (b • (1 : ZHat)) at habRed
  rw [map_nsmul, map_nsmul, hredOne] at habRed
  have hval := congrArg ZMod.val habRed
  simpa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hval

/-- Multiplication by `n` on the additive group of the profinite integers. -/
def zHatMulNat (n : ℕ) : ContinuousAddMonoidHom ZHat ZHat where
  toFun := fun x => n • x
  map_zero' := nsmul_zero n
  map_add' := fun x y => nsmul_add x y n
  continuous_toFun := continuous_nsmul n

/-- The defining evaluation formula for `zHatMulNat` is `zHatMulNat n x = n • x`. -/
@[simp]
theorem zHatMulNat_apply (n : ℕ) (x : ZHat) :
    zHatMulNat n x = n • x :=
  rfl

private theorem zmod_cast_eq_of_nsmul_eq
    {n m : ℕ} (hn : 0 < n) {a b : ZMod (n * m)}
    (h : n • a = n • b) :
    ZMod.castHom (show m ∣ n * m from ⟨n, by simp [Nat.mul_comm]⟩) (ZMod m) a =
      ZMod.castHom (show m ∣ n * m from ⟨n, by simp [Nat.mul_comm]⟩) (ZMod m) b := by
  rcases ZMod.intCast_surjective a with ⟨a, rfl⟩
  rcases ZMod.intCast_surjective b with ⟨b, rfl⟩
  rw [ZMod.castHom_apply, ZMod.castHom_apply]
  rw [ZMod.cast_intCast
      (R := ZMod m) (n := n * m) (m := m)
      (show m ∣ n * m from ⟨n, by simp [Nat.mul_comm]⟩) a,
    ZMod.cast_intCast
      (R := ZMod m) (n := n * m) (m := m)
      (show m ∣ n * m from ⟨n, by simp [Nat.mul_comm]⟩) b]
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hzero : (n • ((a - b : ℤ) : ZMod (n * m))) = 0 := by
    rw [Int.cast_sub, nsmul_sub, h, sub_self]
  have hdiv : ((n * m : ℕ) : ℤ) ∣ (n : ℤ) * (a - b) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [nsmul_eq_mul, Int.cast_natCast, Int.cast_mul] using hzero
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  apply (mul_dvd_mul_iff_left hn0).mp
  simpa [Nat.cast_mul] using hdiv

/-- Multiplication by a positive integer is injective on `ℤ̂`. -/
theorem zHatMulNat_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (zHatMulNat n) := by
  intro x y hxy
  apply ZHat.ext
  intro m hm
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have hdiv : m ∣ n * m := ⟨n, by simp [Nat.mul_comm]⟩
  have hj : n • zHatReduction (n * m) hnm x =
      n • zHatReduction (n * m) hnm y := by
    simpa only [zHatMulNat_apply, map_nsmul] using
      congrArg (fun z : ZHat => zHatReduction (n * m) hnm z) hxy
  rw [← zHatReduction_transition hm hnm hdiv x,
    ← zHatReduction_transition hm hnm hdiv y]
  exact zmod_cast_eq_of_nsmul_eq hn hj

/-- The image `n ℤ̂` is closed. -/
theorem isClosed_zHatMulNat_range (n : ℕ) :
    IsClosed ((zHatMulNat n).toAddMonoidHom.range : Set ZHat) := by
  rw [AddMonoidHom.coe_range]
  exact (isCompact_range (map_continuous (zHatMulNat n))).isClosed

/-- Establishes the identity `zHatReduction n hn ((Int.castRingHom ZHat) a) = (a : ZMod n)`. -/
@[simp]
theorem zHatReduction_int (n : ℕ) (hn : 0 < n) (a : ℤ) :
    zHatReduction n hn
        ((Int.castRingHom ZHat) a) =
      (a : ZMod n) :=
  rfl

/-- Reduction modulo a positive integer is onto. -/
theorem zHatReduction_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (zHatReduction n hn) := by
  intro a
  rcases ZMod.intCast_surjective a with ⟨a, rfl⟩
  exact ⟨(Int.castRingHom ZHat) a, rfl⟩

/--
Establishes the identity `zHatMulNat n ((Int.castRingHom ZHat) a) = (Int.castRingHom ZHat) ((n :
ℤ) * a)`.
-/
@[simp]
theorem zHatMulNat_int (n : ℕ) (a : ℤ) :
    zHatMulNat n ((Int.castRingHom ZHat) a) =
      (Int.castRingHom ZHat) ((n : ℤ) * a) := by
  apply ZHat.ext
  intro m hm
  change n • (a : ZMod m) = (((n : ℤ) * a : ℤ) : ZMod m)
  simp [nsmul_eq_mul]

/-- The subgroup `n ℤ̂` is exactly the kernel of reduction modulo `n`. -/
theorem zHatMulNat_range_eq_ker_reduction (n : ℕ) (hn : 0 < n) :
    (zHatMulNat n).toAddMonoidHom.range =
      (zHatReduction n hn).toAddMonoidHom.ker := by
  apply AddSubgroup.ext
  intro y
  constructor
  · rintro ⟨x, rfl⟩
    change zHatReduction n hn (zHatMulNat n x) = 0
    change n • zHatReduction n hn x = 0
    simp [nsmul_eq_mul]
  · intro hy
    let K : Set ZHat :=
      ((zHatReduction n hn).toAddMonoidHom.ker : Set ZHat)
    let D : Set ZHat :=
      Set.range (Int.castRingHom ZHat)
    have hKopen : IsOpen K := by
      change IsOpen ((zHatReduction n hn) ⁻¹' ({0} : Set (ZMod n)))
      have hzeroOpen : IsOpen ({0} : Set (ZMod n)) := isOpen_discrete _
      exact hzeroOpen.preimage (map_continuous (zHatReduction n hn))
    have hDdense : Dense D := by
      exact denseRange_intCast_zHat
    have hKD : K ∩ D ⊆
        ((zHatMulNat n).toAddMonoidHom.range : Set ZHat) := by
      rintro _ ⟨hzK, a, rfl⟩
      have ha0 : (a : ZMod n) = 0 := by
        simpa [K] using hzK
      have hna : (n : ℤ) ∣ a :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd a n).mp ha0
      rcases hna with ⟨b, rfl⟩
      refine ⟨(Int.castRingHom ZHat) b, ?_⟩
      exact zHatMulNat_int n b
    have hyClosure : y ∈ closure (K ∩ D) :=
      (hDdense.open_subset_closure_inter hKopen) hy
    exact (closure_minimal hKD (isClosed_zHatMulNat_range n)) hyClosure

/-- The additive index of `n ℤ̂` in `ℤ̂` is `n`. -/
theorem zHatMulNat_range_index (n : ℕ) (hn : 0 < n) :
    (zHatMulNat n).toAddMonoidHom.range.index = n := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [zHatMulNat_range_eq_ker_reduction n hn,
    AddSubgroup.index_ker]
  rw [AddMonoidHom.range_eq_top_of_surjective
    (zHatReduction n hn).toAddMonoidHom (zHatReduction_surjective n hn)]
  calc
    Nat.card (↑(⊤ : AddSubgroup (ZMod n))) = Nat.card (ZMod n) :=
      Nat.card_congr
        { toFun := fun x => x.1
          invFun := fun x => ⟨x, AddSubgroup.mem_top x⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun _ => rfl }
    _ = n := Nat.card_zmod n

/-- Every additive subgroup of finite nonzero index in `ℤ̂` is the expected
principal subgroup.  Closedness is not needed: the quotient is abelian, so its
cardinality annihilates every quotient class, and comparison of indices forces
equality. -/
theorem zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero
    (H : AddSubgroup ZHat) (hH : H.index ≠ 0) :
    H = (zHatMulNat H.index).toAddMonoidHom.range := by
  have hle : (zHatMulNat H.index).toAddMonoidHom.range ≤ H := by
    rintro y ⟨x, rfl⟩
    exact H.nsmul_index_mem x
  have hrangeIndex :
      (zHatMulNat H.index).toAddMonoidHom.range.index = H.index :=
    zHatMulNat_range_index H.index (Nat.pos_of_ne_zero hH)
  have hrel :
      (zHatMulNat H.index).toAddMonoidHom.range.relIndex H = 1 := by
    have heq :
        (zHatMulNat H.index).toAddMonoidHom.range.relIndex H * H.index =
          H.index :=
      (AddSubgroup.relIndex_mul_index hle).trans hrangeIndex
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hH)
    simpa only [one_mul] using heq
  exact le_antisymm (AddSubgroup.relIndex_eq_one.mp hrel) hle

/-- Index-explicit form of the classification of finite-index additive
subgroups of `ℤ̂`. -/
theorem zHatAddSubgroup_eq_mulNat_range_of_index_eq
    (H : AddSubgroup ZHat) {n : ℕ} (hn : 0 < n) (hindex : H.index = n) :
    H = (zHatMulNat n).toAddMonoidHom.range := by
  subst n
  exact zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero H
    (Nat.ne_of_gt hn)

/-- A subgroup with finite quotient is the subgroup obtained by multiplying by
its index. -/
theorem zHatAddSubgroup_eq_mulNat_range_of_finite_quotient
    (H : AddSubgroup ZHat) [Finite (ZHat ⧸ H)] :
    H = (zHatMulNat H.index).toAddMonoidHom.range :=
  zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero H
    H.index_ne_zero_of_finite

/-- Multiplication by `n > 0` identifies `ℤ̂` continuously with its image. -/
noncomputable def zHatMulNatRangeEquiv (n : ℕ) (hn : 0 < n) :
    ZHat ≃ₜ+ (zHatMulNat n).toAddMonoidHom.range := by
  let e : ZHat ≃+ (zHatMulNat n).toAddMonoidHom.range :=
    AddMonoidHom.ofInjective (zHatMulNat_injective hn)
  have he : Continuous e := by
    change Continuous fun x : ZHat =>
      (⟨zHatMulNat n x, ⟨x, rfl⟩⟩ : (zHatMulNat n).toAddMonoidHom.range)
    exact Continuous.subtype_mk (map_continuous (zHatMulNat n)) fun x => ⟨x, rfl⟩
  let h : ZHat ≃ₜ (zHatMulNat n).toAddMonoidHom.range :=
    he.homeoOfEquivCompactToT2
  exact
    { e with
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }

/-- Division by `n` on the subgroup `n ℤ̂`. -/
noncomputable def zHatDivide (n : ℕ) (hn : 0 < n) :
    ContinuousAddMonoidHom ((zHatMulNat n).toAddMonoidHom.range) ZHat :=
  (zHatMulNatRangeEquiv n hn).symm

/-- Establishes the identity `zHatMulNat n (zHatDivide n hn y) = y.1`. -/
@[simp]
theorem zHatMulNat_zHatDivide (n : ℕ) (hn : 0 < n)
    (y : (zHatMulNat n).toAddMonoidHom.range) :
    zHatMulNat n (zHatDivide n hn y) = y.1 := by
  change ((zHatMulNatRangeEquiv n hn)
    ((zHatMulNatRangeEquiv n hn).symm y)).1 = y.1
  exact congrArg Subtype.val ((zHatMulNatRangeEquiv n hn).apply_symm_apply y)

/-- Establishes the identity `zHatDivide n hn ⟨zHatMulNat n x, ⟨x, rfl⟩⟩ = x`. -/
@[simp]
theorem zHatDivide_zHatMulNat (n : ℕ) (hn : 0 < n) (x : ZHat) :
    zHatDivide n hn
      ⟨zHatMulNat n x, ⟨x, rfl⟩⟩ = x := by
  change (zHatMulNatRangeEquiv n hn).symm
    ((zHatMulNatRangeEquiv n hn) x) = x
  exact (zHatMulNatRangeEquiv n hn).symm_apply_apply x

end
end ClassFormation
