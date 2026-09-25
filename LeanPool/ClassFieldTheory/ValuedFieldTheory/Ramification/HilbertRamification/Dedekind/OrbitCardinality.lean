/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
/-!
# Hilbert ramification theory: prime-decomposition cardinalities

This file records the parts of the prime-decomposition tower identity that are
already available from the Dedekind-domain Galois action and mathlib's
ramification/inertia API.
-/

@[expose] public section

noncomputable section

namespace HilbertRamification
namespace Dedekind

open scoped Pointwise
open Algebra Module

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

private theorem orbit_eq_singleton_of_le_stabilizer
    {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) {x : X} (hH : H ≤ MulAction.stabilizer G x) :
    MulAction.orbit H x = {x} := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_singleton_iff]
    rcases MulAction.mem_orbit_iff.mp hy with ⟨σ, hσ⟩
    rw [← hσ]
    exact (MulAction.mem_stabilizer_iff.mp (hH σ.property))
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact MulAction.mem_orbit_self x

/-- The prime-decomposition tower identity:
under the decomposition group `G_P`, the orbit of `P` is a singleton.  This is
the group-action core of the assertion that over the decomposition field
`Z_P`, the prime `P` is nonsplit. -/
theorem dedekindTower_decompositionGroup_orbit_eq_singleton
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    MulAction.orbit (decompositionGroup P G) P = {P} := by
  exact orbit_eq_singleton_of_le_stabilizer
    (decompositionGroup P G)
    (fun σ hσ => (mem_decompositionGroup_iff (P := P) (G := G) (σ := σ)).1 hσ)

/-- The prime-decomposition tower identity:
the decomposition-group orbit of `P` has one element. -/
theorem dedekindTower_decompositionGroup_orbit_ncard_eq_one
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    (MulAction.orbit (decompositionGroup P G) P).ncard = 1 := by
  rw [dedekindTower_decompositionGroup_orbit_eq_singleton (B := B) P G]
  simp

/-- A prime-decomposition consequence:
under the inertia group `I_P`, the orbit of `P` is a singleton. -/
theorem dedekindRamification_inertiaGroup_orbit_eq_singleton
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    MulAction.orbit (inertiaGroup P G) P = {P} := by
  exact orbit_eq_singleton_of_le_stabilizer
    (inertiaGroup P G)
    (fun σ hσ => Ideal.inertia_le_stabilizer (M := G) P hσ)

/-- A prime-decomposition consequence:
the inertia-group orbit of `P` has one element. -/
theorem dedekindRamification_inertiaGroup_orbit_ncard_eq_one
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    (MulAction.orbit (inertiaGroup P G) P).ncard = 1 := by
  rw [dedekindRamification_inertiaGroup_orbit_eq_singleton (B := B) P G]
  simp

/-- A prime-decomposition consequence:
when `I_P` itself is viewed as the acting Galois group, every element fixes
`P`, so the decomposition group is the whole group. -/
theorem dedekindRamification_inertiaGroup_decompositionGroup_eq_top
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    decompositionGroup P (inertiaGroup P G) = ⊤ := by
  apply le_antisymm le_top
  intro σ _hσ
  rw [mem_decompositionGroup_iff]
  change (σ : G) • P = P
  exact Ideal.inertia_le_stabilizer (M := G) P σ.property

/-- A prime-decomposition consequence:
when `I_P` itself is viewed as the acting Galois group, its inertia group is
the whole group. -/
theorem dedekindRamification_inertiaGroup_inertiaGroup_eq_top
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    inertiaGroup P (inertiaGroup P G) = ⊤ := by
  apply le_antisymm le_top
  intro σ _hσ
  rw [mem_inertiaGroup_iff]
  intro x
  exact σ.property x

/-- The prime-decomposition tower identity:
the decomposition group has cardinality `e(P/p) * f(P/p)` for the chosen
prime `P` over `p`, not just for the Galois-invariant representatives
`ramificationIdxIn` and `inertiaDegIn`. -/
theorem dedekindTower_decomposition_card_eq_ramificationIdx_mul_inertiaDeg
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Nat.card (decompositionGroup P G) =
      P.ramificationIdx A * P.inertiaDeg A := by
  rw [dedekindRamification_decomposition_card_eq_ramificationIdxIn_mul_inertiaDegIn
    (A := A) (B := B) p hp P G]
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G,
    Ideal.inertiaDegIn_eq_inertiaDeg p P G]

/-- The prime-decomposition tower identity:
if a prime is nonsplit in a finite Galois Dedekind extension, then the product
`e * f` equals the order of the Galois group. -/
theorem dedekindTower_ramificationIdxIn_mul_inertiaDegIn_eq_card_of_nonsplit
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]
    (hnonsplit : (p.primesOver B).ncard = 1) :
    Ideal.ramificationIdxIn p B * Ideal.inertiaDegIn p B = Nat.card G := by
  have hfund :=
    dedekindRamification_galois_fundamental_identity
      (A := A) p hp B G
  rwa [hnonsplit, one_mul] at hfund

/-- The prime-decomposition tower identity:
chosen-prime form of `e * f = #G` under nonsplitting. -/
theorem dedekindTower_ramificationIdx_mul_inertiaDeg_eq_card_of_nonsplit
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]
    (hnonsplit : (p.primesOver B).ncard = 1) :
    P.ramificationIdx A * P.inertiaDeg A =
      Nat.card G := by
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p P G,
    ← Ideal.inertiaDegIn_eq_inertiaDeg p P G]
  exact
    dedekindTower_ramificationIdxIn_mul_inertiaDegIn_eq_card_of_nonsplit
      (A := A) (B := B) p hp G hnonsplit

/-- The separable-residue cardinality relation:
when the residue extension is separable, the inertia group has cardinality
equal to the ramification index of the chosen prime. -/
theorem inertia_card_eq_ramificationIdx
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] [P.IsPrime] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (hp : p ≠ ⊥) :
    Nat.card (inertiaGroup P G) =
      P.ramificationIdx A := by
  rw [dedekindRamification_inertia_card_eq_ramificationIdxIn
    (A := A) (B := B) p P G hp]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx p P G

/-- The separable-residue cardinality relation:
the separable-residue cardinality conclusions
`#I_P = e(P/p)` and `#(G_P/I_P) = f(P/p)`. -/
theorem dedekindRamification_separable_residue_cardinalities
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) [p.IsMaximal] (P : Ideal B)
    [P.IsPrime] [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (hp : p ≠ ⊥) :
    Nat.card (inertiaGroup P G) =
        P.ramificationIdx A ∧
      Nat.card
          (decompositionGroup P G ⧸
            (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
        P.inertiaDeg A := by
  exact
    ⟨inertia_card_eq_ramificationIdx
        (A := A) (B := B) p P G hp,
      dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDeg
        (A := A) (B := B) p P G⟩

end Dedekind
end HilbertRamification
