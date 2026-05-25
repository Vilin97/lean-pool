/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeiBichang
-/

/-
Lemmas irrelavant to `PowerSeries` or `Padic`.
-/

import Mathlib.Tactic

-- noncomputable section
noncomputable section noncom
open Classical

section ideal

variable {R : Type u} [CommRing R]

def Ring.quot_bot (R : Type u) [CommRing R] :
    R ⧸ (⊥ : Ideal R) ≃+* R :=
  RingHom.quotientKerEquivOfSurjective (f := RingHom.id R) fun b ↦ ⟨b, rfl⟩

def Ideal.quotientMap_bot  {S : Type v} [CommRing S] {I : Ideal R} (f : R →+* S) (hI : I ≤ RingHom.ker f) :
    R ⧸ I →+* S :=
  (Ring.quot_bot S).toRingHom.comp (Ideal.quotientMap (0 : Ideal S) f hI)

end ideal

section nilp

variable {R : Type u} [CommRing R]

-- `a` is nilpotent in `ℤ ⧸ a ^ n`.
lemma nat_mod_pow_nilp {a n : ℕ} : IsNilpotent (a : ZMod (a ^ n)) :=
  ⟨n, (Trans.trans (Nat.cast_pow a n).symm (ZMod.nat_cast_self (a ^ n)))⟩

theorem choose_IsNilpotent_ne_zero {r : R} [Nontrivial R] (h : IsNilpotent r) : choose h ≠ 0 := by
  intro x
  have : r ^ (choose h) ≠ 0 := by rw [x, pow_zero r]; exact one_ne_zero
  exact this (choose_spec h)

theorem nilp_pow_ge_choose_eq_zero {r : nilradical R} {n : ℕ} (h : n ≥ choose r.2) : r.1 ^ n = 0 := by
  calc
    _ = r.1 ^ (choose r.2) * r.1 ^ (n - choose r.2) := (pow_mul_pow_sub r.1 h).symm
    _ = 0 * r.1 ^ (n - choose r.2) := by rw [choose_spec r.2]
    _ = 0 := zero_mul _

end nilp

end noncom

-- computable sectino
section com

end com
