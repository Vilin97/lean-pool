/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.FiniteRamificationPrimary
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.FiniteOrderValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.CharacterMap
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.GroupTheory.Sylow
/-!
# Structure of finite inertia

The actual residue-unit character has ramification kernel. Finite inertia fixes
values, so this character is defined on all inertia. In residue characteristic
zero its kernel is trivial and inertia is commutative. In residue characteristic
p every p-subgroup lies in the ramification kernel, which is itself a p-group.
-/

@[expose] public section

namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Finite inertia is commutative in residue characteristic zero. -/
theorem inertiaGroup_isMulCommutative_of_residueCharZero
    (A : _root_.ValuationSubring L) [Finite (inertiaGroup K A)]
    [CharZero (IsLocalRing.ResidueField A)] :
    IsMulCommutative (inertiaGroup K A) := by
  have htop := valueTrivialInertiaGroup_eq_top_of_finite K A
  have hinj : Function.Injective (valueTrivialInertiaCharacterHom K A) := by
    apply (injective_iff_map_eq_one (valueTrivialInertiaCharacterHom K A)).mpr
    intro σ hσ
    apply Subtype.ext
    have hmem : (σ : inertiaGroup K A) ∈ ramificationGroup K A :=
      (valueTrivialInertiaCharacterHom_mem_ker_iff K A σ).mp hσ
    rw [ramificationGroup_eq_bot_of_residueCharZero K A] at hmem
    exact hmem
  apply IsMulCommutative.of_comm
  intro σ τ
  let s : valueTrivialInertiaGroup K A := ⟨σ, htop.symm ▸ Subgroup.mem_top σ⟩
  let t : valueTrivialInertiaGroup K A := ⟨τ, htop.symm ▸ Subgroup.mem_top τ⟩
  have hst : s * t = t * s := hinj (by
    apply MonoidHom.ext
    intro x
    simp only [map_mul, MonoidHom.mul_apply]
    exact mul_comm _ _)
  exact congrArg (fun a : valueTrivialInertiaGroup K A => (a : inertiaGroup K A)) hst

/-- Every p-subgroup of inertia lies in the actual ramification group. -/
theorem pSubgroup_le_ramificationGroup_of_residueChar
    (A : _root_.ValuationSubring L) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p]
    (P : Subgroup (inertiaGroup K A)) (hP : IsPGroup p P) :
    P ≤ ramificationGroup K A := by
  intro σ hσ
  obtain ⟨a, ha⟩ := hP ⟨σ, hσ⟩
  have hpow : σ ^ (p ^ a) = 1 :=
    congrArg (fun x : P => (x : inertiaGroup K A)) ha
  have hfinite : IsOfFinOrder σ :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨p ^ a, pow_pos (Fact.out : p.Prime).pos a, hpow⟩
  let s : valueTrivialInertiaGroup K A :=
    ⟨σ, mem_valueTrivialInertiaGroup_of_isOfFinOrder K A σ hfinite⟩
  have hs : s ^ (p ^ a) = 1 := Subtype.ext hpow
  apply (valueTrivialInertiaCharacterHom_mem_ker_iff K A s).mp
  change valueTrivialInertiaCharacterHom K A s = 1
  apply MonoidHom.ext
  intro x
  apply Units.ext
  have hchar : (valueTrivialInertiaCharacterHom K A s x :
      IsLocalRing.ResidueField A) ^ (p ^ a) = 1 := by
    have h := congrArg (fun f => (f x : IsLocalRing.ResidueField A))
      (congrArg (valueTrivialInertiaCharacterHom K A) hs)
    simpa only [map_pow, map_one, MonoidHom.pow_apply, MonoidHom.one_apply,
      Units.val_pow_eq_pow_val, Units.val_one] using h
  have h := (ExpChar.pow_prime_pow_mul_eq_one_iff p a 1
    (valueTrivialInertiaCharacterHom K A s x : IsLocalRing.ResidueField A)).mp
    (by simpa only [mul_one] using hchar)
  simpa only [pow_one, MonoidHom.one_apply, Units.val_one] using h

/-- The actual ramification group is the unique Sylow p-subgroup of finite inertia. -/
theorem sylow_eq_ramificationGroup_of_residueChar
    (A : _root_.ValuationSubring L) (p : ℕ) [Fact p.Prime]
    [Finite (inertiaGroup K A)] [CharP (IsLocalRing.ResidueField A) p]
    (P : Sylow p (inertiaGroup K A)) :
    (P : Subgroup (inertiaGroup K A)) = ramificationGroup K A := by
  exact (P.is_maximal' (ramificationGroup_isPGroup_of_residueChar K A p)
    (pSubgroup_le_ramificationGroup_of_residueChar K A p P P.isPGroup')).symm

/-- In positive residue characteristic, the actual finite ramification group
is trivial exactly when the residue characteristic does not divide the order
of inertia. -/
theorem ramificationGroup_eq_bot_iff_residueChar_not_dvd_inertia_card
    (A : _root_.ValuationSubring L) (p : ℕ) [Fact p.Prime]
    [Finite (inertiaGroup K A)]
    [CharP (IsLocalRing.ResidueField A) p] :
    ramificationGroup K A = ⊥ ↔
      ¬ p ∣ Nat.card (inertiaGroup K A) := by
  classical
  let P : Sylow p (inertiaGroup K A) :=
    Classical.choice (inferInstance : Nonempty (Sylow p (inertiaGroup K A)))
  have hP : (P : Subgroup (inertiaGroup K A)) = ramificationGroup K A :=
    sylow_eq_ramificationGroup_of_residueChar K A p P
  rw [← hP]
  constructor
  · intro hbot hp
    exact (Sylow.ne_bot_of_dvd_card P hp) hbot
  · intro hp
    apply Subgroup.eq_bot_of_card_eq
    rw [P.card_eq_multiplicity,
      Nat.factorization_eq_zero_of_not_dvd hp, pow_zero]

end RamificationTheory.HilbertRamification.ValuationSubring
