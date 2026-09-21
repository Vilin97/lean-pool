/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring
import Mathlib.Algebra.BigOperators.Field
/-!
# Prime-to-residue torsion in the actual ramification group

A ramification automorphism whose order is nonzero in the residue field is
trivial. For a moved element, divide its successive conjugate differences by
the first nonzero difference. Ramification makes every resulting quotient a
principal unit, whereas their sum vanishes by telescoping. Reduction would
then send the number of terms to zero.

The argument uses the existing ramification subgroup and its principal-unit
condition. It requires no discreteness, Henselianity, or finite extension.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

open scoped BigOperators

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- An element of the actual ramification group killed by an integer which
is nonzero in the residue field is the identity. -/
theorem ramificationGroup_eq_one_of_pow_eq_one_of_residue_natCast_ne_zero
    (A : _root_.ValuationSubring L) (σ : ramificationGroup K A)
    (n : ℕ) (hn : (n : IsLocalRing.ResidueField A) ≠ 0)
    (hσ : σ ^ n = 1) : σ = 1 := by
  classical
  let ρ : ramificationGroup K A →* (L ≃ₐ[K] L) :=
    (inertiaGroupToAut (K := K) A).comp (ramificationGroup K A).subtype
  have hρ : Function.Injective ρ := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (Subtype.ext hab))
  apply hρ
  rw [map_one]
  apply AlgEquiv.ext
  intro x
  change ρ σ x = x
  by_contra hx
  let γ : L ≃ₐ[K] L := ρ σ
  have hγn : γ ^ n = 1 := by
    rw [← map_pow ρ, hσ, map_one]
  let y : L := γ x - x
  have hy : y ≠ 0 := sub_ne_zero.mpr hx
  let q : ℕ → Lˣ := fun i =>
    automorphismUnitQuotient K A
      (((σ ^ i : ramificationGroup K A) : inertiaGroup K A) :
        decompositionGroup K A) (Units.mk0 y hy)
  have hq (i : ℕ) : q i ∈ A.principalUnitGroup :=
    (σ ^ i : ramificationGroup K A).property (Units.mk0 y hy)
  let a : ℕ → A := fun i =>
    A.unitGroupMulEquiv ⟨q i, A.principal_units_le_units (hq i)⟩
  have ha (i : ℕ) : (a i : L) = (γ ^ i) y / y := by
    change ((q i : Lˣ) : L) = (γ ^ i) y / y
    simp only [q, automorphismUnitQuotient, Units.val_div_eq_div_val, Units.val_mk0]
    change ρ (σ ^ i) y / y = (γ ^ i) y / y
    rw [map_pow ρ]
  have hred (i : ℕ) : IsLocalRing.residue A (a i) = 1 := by
    have hker : A.unitGroupMulEquiv
          ⟨q i, A.principal_units_le_units (hq i)⟩ ∈
        (Units.map (IsLocalRing.residue A).toMonoidHom).ker :=
      (A.coe_mem_principalUnitGroup_iff).mp (hq i)
    exact congrArg (fun z : (IsLocalRing.ResidueField A)ˣ =>
      (z : IsLocalRing.ResidueField A)) (MonoidHom.mem_ker.mp hker)
  have horbit (i : ℕ) :
      (γ ^ i) y = (γ ^ (i + 1)) x - (γ ^ i) x := by
    change (γ ^ i).toRingHom.toAddMonoidHom (γ x - x) =
      (γ ^ (i + 1)) x - (γ ^ i) x
    rw [map_sub (γ ^ i).toRingHom.toAddMonoidHom, pow_succ, AlgEquiv.mul_apply]
    rfl
  have htel (m : ℕ) :
      ∑ i ∈ Finset.range m, (γ ^ i) y = (γ ^ m) x - x := by
    calc
      ∑ i ∈ Finset.range m, (γ ^ i) y =
          ∑ i ∈ Finset.range m, ((γ ^ (i + 1)) x - (γ ^ i) x) :=
        Finset.sum_congr rfl (fun i _hi => horbit i)
      _ = (γ ^ m) x - x := by
        rw [Finset.sum_range_sub (fun i : ℕ => (γ ^ i) x) m, pow_zero, AlgEquiv.one_apply]
  have horbitSum : ∑ i ∈ Finset.range n, (γ ^ i) y = 0 := by
    rw [htel, hγn, AlgEquiv.one_apply, sub_self]
  have hsum : ∑ i ∈ Finset.range n, a i = 0 := by
    apply Subtype.ext
    change A.subtype.toAddMonoidHom (∑ i ∈ Finset.range n, a i) =
      A.subtype.toAddMonoidHom 0
    rw [map_sum A.subtype.toAddMonoidHom, map_zero]
    calc
      ∑ i ∈ Finset.range n, A.subtype (a i) =
          ∑ i ∈ Finset.range n, (γ ^ i) y / y :=
        Finset.sum_congr rfl (fun i _hi => ha i)
      _ = (∑ i ∈ Finset.range n, (γ ^ i) y) / y :=
        (Finset.sum_div (Finset.range n) (fun i => (γ ^ i) y) y).symm
      _ = 0 := by rw [horbitSum, zero_div]
  have hredSum : IsLocalRing.residue A (∑ i ∈ Finset.range n, a i) =
      (n : IsLocalRing.ResidueField A) := by
    change (IsLocalRing.residue A).toAddMonoidHom
      (∑ i ∈ Finset.range n, a i) = (n : IsLocalRing.ResidueField A)
    rw [map_sum (IsLocalRing.residue A).toAddMonoidHom]
    calc
      ∑ i ∈ Finset.range n, IsLocalRing.residue A (a i) =
          ∑ i ∈ Finset.range n, (1 : IsLocalRing.ResidueField A) :=
        Finset.sum_congr rfl (fun i _hi => hred i)
      _ = (n : IsLocalRing.ResidueField A) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hsum, map_zero] at hredSum
  exact hn hredSum.symm

end RamificationTheory.HilbertRamification.ValuationSubring
