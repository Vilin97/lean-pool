/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# The fundamental identity in the quotient-based formulation

Mathlib's `Ideal.sum_ramification_inertia_eq_finrank` states the fundamental identity
`∑ e · f = [L : K]` for the localization-based `Ideal.ramificationIdx` and `Ideal.inertiaDeg`,
summed over the subtype `p.primesOver S`.  The rest of this development works with the
quotient-based `Ideal.ramificationIdx'` and `Ideal.inertiaDeg'` over the finite set
`IsDedekindDomain.primesOverFinset`, so this file transports the identity to that form and
records the resulting bound `e ≤ [L : K]` for a single prime.
-/

@[expose] public section

open Module

namespace Ideal

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L]

/-- The fundamental identity `∑ e · f = [L : K]` for the quotient-based ramification index and
inertia degree, summed over the finite set of primes above a nonzero maximal ideal `p`. -/
theorem sum_ramificationIdx'_mul_inertiaDeg' {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S, ramificationIdx' p P * inertiaDeg' p P =
      finrank K L := by
  classical
  rw [IsFractionRing.finrank_eq R K S L, ← sum_ramification_inertia_eq_finrank p S,
    Finset.sum_subtype (IsDedekindDomain.primesOverFinset p S)
      (fun P => IsDedekindDomain.mem_primesOverFinset_iff hp0 S (P := P))]
  refine Finset.sum_congr rfl fun q _ => ?_
  have : q.1.IsMaximal := IsMaximal.of_liesOver_isMaximal q.1 p
  rw [ramificationIdx'_eq_ramificationIdx p q.1 hp0, inertiaDeg'_eq_inertiaDeg p q.1]

/-- The quotient-based ramification index of a prime above a nonzero maximal ideal is bounded by
the degree of the extension of fraction fields. -/
theorem ramificationIdx'_le_finrank {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) (P : Ideal S)
    [hP₁ : P.IsPrime] [hP₂ : P.LiesOver p] : ramificationIdx' p P ≤ finrank K L := by
  classical
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 S).mpr ⟨hP₁, hP₂⟩
  rw [← sum_ramificationIdx'_mul_inertiaDeg' (S := S) K L hp0, ← Finset.add_sum_erase _ _ hP]
  exact le_trans (Nat.le_mul_of_pos_right _ (inertiaDeg'_pos p P)) (Nat.le_add_right _ _)

end Ideal
