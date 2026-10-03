/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
/-!
# Hilbert ramification theory: Dedekind-domain layer

This file manages the Dedekind-domain part of Hilbert ramification theory in
prime-decomposition theory.

The implementation uses mathlib's ramification/inertia theorems where those
are already the source proof, but the decomposition/inertia/residue-action
interface is proved here: membership criteria, residue-action formula,
normality of inertia in the decomposition group, exactness, and quotient form.
-/

@[expose] public section

noncomputable
section

namespace HilbertRamification
namespace Dedekind

open scoped Pointwise
open Algebra Module

attribute [local instance] Ideal.Quotient.field

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The decomposition and inertia definition:
the decomposition group of a prime ideal. -/
abbrev decompositionGroup
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    Subgroup G :=
  MulAction.stabilizer G P

/-- Membership in the decomposition group is exactly stabilization of the prime
ideal. -/
theorem mem_decompositionGroup_iff
    {P : Ideal B} {G : Type*} [Group G] [MulSemiringAction G B] {σ : G} :
    σ ∈ decompositionGroup P G ↔ σ • P = P :=
  Iff.rfl

/-- The inertia-field definition:
the inertia group of a prime ideal. -/
abbrev inertiaGroup
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    Subgroup G :=
  P.toAddSubgroup.inertia G

/-- Membership in the inertia group is trivial action on the residue ring. -/
theorem mem_inertiaGroup_iff
    {P : Ideal B} {G : Type*} [Group G] [MulSemiringAction G B] {σ : G} :
    σ ∈ inertiaGroup P G ↔ ∀ x : B, σ • x - x ∈ P :=
  Iff.rfl

/-- prime-decomposition theory:
the residue-field action of the decomposition group. -/
abbrev residueStabilizerHom
    (p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] :
    decompositionGroup P G →* (B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P :=
  Ideal.Quotient.stabilizerHom P p G

/-- prime-decomposition theory:
the residue action is concretely `a mod P ↦ σ a mod P`. -/
@[simp] theorem residueStabilizerHom_apply
    (p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (σ : decompositionGroup P G) (b : B) :
    residueStabilizerHom p P G σ b = ↑(σ • b) :=
  Ideal.Quotient.stabilizerHom_apply P p G σ b

/-- Inertia is normal inside the decomposition group.  The proof is the
intrinsic conjugation argument: if `σ` is trivial mod `P`, then
`τ σ τ⁻¹` is also trivial mod `P` because `τ` stabilizes `P`. -/
instance inertiaSubgroupOfDecomposition_normal
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    ((inertiaGroup P G).subgroupOf (decompositionGroup P G)).Normal := by
  refine ⟨?_⟩
  intro σ hσ τ
  rw [Subgroup.mem_subgroupOf] at hσ ⊢
  rw [mem_inertiaGroup_iff] at hσ ⊢
  intro x
  let y : B := (σ : G) • ((τ : G)⁻¹ • x) - ((τ : G)⁻¹ • x)
  have hy : y ∈ P := hσ ((τ : G)⁻¹ • x)
  have hτy : (τ : G) • y ∈ (τ : G) • P :=
    Ideal.smul_mem_pointwise_smul (τ : G) y P hy
  rw [τ.property] at hτy
  simpa [y, smul_sub, mul_smul, inv_smul_smul] using hτy

/-- The valuation-conjugacy theorem:
the Galois group acts transitively on primes over a fixed prime. -/
theorem exists_smul_eq_of_isGaloisGroup
    (p : Ideal A) (P Q : Ideal B)
    [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    ∃ σ : G, σ • P = Q := by
  exact Ideal.exists_smul_eq_of_isGaloisGroup p P Q G

/-- prime-decomposition theory: in the Galois case the ramification index is
independent of the prime above `p`. -/
theorem dedekindRamification_ramificationIdx_eq
    (p : Ideal A) (P Q : Ideal B)
    [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    P.ramificationIdx A = Q.ramificationIdx A := by
  exact Ideal.ramificationIdx_eq_of_isGaloisGroup p P Q G

/-- prime-decomposition theory: in the Galois case the inertia degree is
independent of the prime above `p`. -/
theorem dedekindRamification_inertiaDeg_eq
    (p : Ideal A) (P Q : Ideal B)
    [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    P.inertiaDeg A = Q.inertiaDeg A := by
  exact Ideal.inertiaDeg_eq_of_isGaloisGroup p P Q G


/-- Decomposition and inertia groups satisfy:
the primes above `p` are identified with the cosets `G/G_P`. -/
noncomputable def dedekindDecompositionPrimesOverEquivQuotientDecompositionGroup
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    p.primesOver B ≃ G ⧸ decompositionGroup P G :=
  (Set.equivOfEq
      (IsInvariant.orbit_eq_primesOver A B G p P).symm).trans
    (MulAction.orbitEquivQuotientStabilizer G P)

/-- Decomposition and inertia groups satisfy:
the number of primes above `p` is the index `(G : G_P)`. -/
theorem dedekindDecomposition_ncard_primesOver_eq_decomposition_index
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    (p.primesOver B).ncard = (decompositionGroup P G).index := by
  rw [← IsInvariant.orbit_eq_primesOver A B G p P]
  exact (MulAction.index_stabilizer G P).symm

/-- Decomposition and inertia groups satisfy:
the group-action form of nonsplitting, `G_P = G` iff there is one prime above
`p`. -/
theorem dedekindDecomposition_decompositionGroup_eq_top_iff_primesOver_ncard_eq_one
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    decompositionGroup P G = ⊤ ↔ (p.primesOver B).ncard = 1 := by
  rw [dedekindDecomposition_ncard_primesOver_eq_decomposition_index (A := A) (B := B) p P G]
  exact Iff.symm Subgroup.index_eq_one

/-- Decomposition and inertia groups satisfy:
the group-action form of total splitting, `G_P = 1` iff the number of primes
above `p` is `#G`. -/
theorem dedekindDecomposition_decompositionGroup_eq_bot_iff_primesOver_ncard_eq_card
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    decompositionGroup P G = ⊥ ↔ (p.primesOver B).ncard = Nat.card G := by
  constructor
  · intro hG
    rw [dedekindDecomposition_ncard_primesOver_eq_decomposition_index
      (A := A) (B := B) p P G, hG, Subgroup.index_bot]
  · intro hp
    have hindex : (decompositionGroup P G).index = Nat.card G := by
      rw [← dedekindDecomposition_ncard_primesOver_eq_decomposition_index
        (A := A) (B := B) p P G, hp]
    apply Subgroup.eq_bot_of_card_eq
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G))
      (by simpa [hindex] using (decompositionGroup P G).index_mul_card)



/-- prime-decomposition theory:
the kernel of the residue action is the inertia group. -/
theorem dedekindRamification_residueAction_ker
    (p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] :
    MonoidHom.ker (residueStabilizerHom p P G) =
      (inertiaGroup P G).subgroupOf (decompositionGroup P G) := by
  exact Ideal.Quotient.ker_stabilizerHom P p G

/-- prime-decomposition theory:
`I_P -> G_P -> Aut(kappa(P)/kappa(p))` is exact at `G_P`. -/
theorem dedekindRamification_residueAction_mulExact
    (p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] :
    Function.MulExact
      ((inertiaGroup P G).subgroupOf (decompositionGroup P G)).subtype
      (residueStabilizerHom p P G) := by
  rw [MonoidHom.mulExact_iff, dedekindRamification_residueAction_ker]
  exact (Subgroup.range_subtype _).symm

/-- prime-decomposition theory:
for a finite invariant Galois action, the residue action is surjective. -/
theorem dedekindRamification_residueAction_surjective
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] :
    Function.Surjective (residueStabilizerHom p P G) := by
  exact Ideal.Quotient.stabilizerHom_surjective G p P

/-- prime-decomposition theory:
the residue class field extension is normal. -/
theorem dedekindRamification_residueExtension_normal
    (p : Ideal A) [p.IsMaximal] (P : Ideal B)
    [P.IsMaximal] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [Algebra.IsInvariant A B G] :
    Normal (A ⧸ p) (B ⧸ P) := by
  exact Ideal.Quotient.normal (A := A) G p P

/-- prime-decomposition theory:
if the residue class field extension is separable, then it is Galois. -/
theorem dedekindRamification_residueExtension_isGalois
    (p : Ideal A) [p.IsMaximal] (P : Ideal B)
    [P.IsMaximal] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [Algebra.IsInvariant A B G] [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] :
    IsGalois (A ⧸ p) (B ⧸ P) := by
  exact isGalois_iff.mpr
    ⟨inferInstance, dedekindRamification_residueExtension_normal (A := A) (B := B) p P G⟩

/-- The conjugation and base-change law:
the residue extension is normal and the decomposition group maps onto its
residue Galois group. -/
theorem dedekindResidue_residueExtension_normal_and_residueAction_surjective
    (p : Ideal A) [p.IsMaximal] (P : Ideal B)
    [P.IsMaximal] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] :
    Normal (A ⧸ p) (B ⧸ P) ∧
      Function.Surjective (residueStabilizerHom p P G) := by
  exact
    ⟨dedekindRamification_residueExtension_normal (A := A) (B := B) p P G,
      dedekindRamification_residueAction_surjective (A := A) (B := B) p P G⟩

/-- The localization and decomposition comparison gives:
`1 -> I_P -> G_P -> Gal(kappa(P)/kappa(p)) -> 1`, in the finite invariant
Galois-action form. -/
theorem dedekindRamification_residueAction_shortExact
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] :
    Function.Injective
        ((inertiaGroup P G).subgroupOf (decompositionGroup P G)).subtype ∧
      Function.MulExact
        ((inertiaGroup P G).subgroupOf (decompositionGroup P G)).subtype
        (residueStabilizerHom p P G) ∧
      Function.Surjective (residueStabilizerHom p P G) := by
  exact
    ⟨Subtype.coe_injective, dedekindRamification_residueAction_mulExact p P G,
      dedekindRamification_residueAction_surjective p P G⟩

/-- The localization and decomposition comparison gives:
the quotient of the decomposition group by inertia is the residue Galois group.
-/
def dedekindRamificationDecompositionQuotientInertiaEquivResidueGalois
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] :
    decompositionGroup P G ⧸
        (inertiaGroup P G).subgroupOf (decompositionGroup P G) ≃*
      (B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P :=
  (QuotientGroup.quotientMulEquivOfEq
      (dedekindRamification_residueAction_ker p P G).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (residueStabilizerHom p P G)
      (dedekindRamification_residueAction_surjective p P G))

/-- A trivial-inertia special case:
if the inertia group is trivial, then the residue action is injective. -/
theorem dedekindRamification_residueAction_injective_of_inertiaGroup_eq_bot
    (p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (hI : inertiaGroup P G = ⊥) :
    Function.Injective (residueStabilizerHom p P G) :=
  (MonoidHom.ker_eq_bot_iff (residueStabilizerHom p P G)).mp <| by
    rw [dedekindRamification_residueAction_ker, hI, Subgroup.bot_subgroupOf]

/-- A trivial-inertia special case:
if the inertia group is trivial, then the residue action identifies `G_P` with
the residue Galois group. -/
theorem dedekindRamification_residueAction_bijective_of_inertiaGroup_eq_bot
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] (hI : inertiaGroup P G = ⊥) :
    Function.Bijective (residueStabilizerHom p P G) :=
  ⟨dedekindRamification_residueAction_injective_of_inertiaGroup_eq_bot p P G hI,
    dedekindRamification_residueAction_surjective p P G⟩

/-- A trivial-inertia special case:
when `I_P = 1`, the residue Galois group is isomorphic to `G_P`. -/
noncomputable def dedekindRamificationDecompositionGroupEquivResidueGaloisOfInertiaGroupEqBot
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] (hI : inertiaGroup P G = ⊥) :
    decompositionGroup P G ≃*
      (B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P :=
  MulEquiv.ofBijective (residueStabilizerHom p P G)
    (dedekindRamification_residueAction_bijective_of_inertiaGroup_eq_bot p P G hI)

/-- A trivial-inertia special case:
when `I_P = 1`, the residue Galois group embeds into `G` through the
decomposition group. -/
noncomputable def dedekindRamificationResidueGaloisEmbeddingIntoGOfInertiaGroupEqBot
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] (hI : inertiaGroup P G = ⊥) :
    ((B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P) →* G :=
  (decompositionGroup P G).subtype.comp
    (dedekindRamificationDecompositionGroupEquivResidueGaloisOfInertiaGroupEqBot
      p P G hI).symm.toMonoidHom

/-- The residue-Galois embedding into `G` from the preceding declaration is
injective. -/
theorem dedekindRamification_residueGaloisEmbeddingIntoG_of_inertiaGroup_eq_bot_injective
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] (hI : inertiaGroup P G = ⊥) :
    Function.Injective
      (dedekindRamificationResidueGaloisEmbeddingIntoGOfInertiaGroupEqBot p P G hI) := by
  intro σ τ hστ
  apply (dedekindRamificationDecompositionGroupEquivResidueGaloisOfInertiaGroupEqBot
    p P G hI).symm.injective
  exact Subtype.ext <| by
    simpa [dedekindRamificationResidueGaloisEmbeddingIntoGOfInertiaGroupEqBot] using hστ



/-- prime-decomposition theory:
in the Galois case the prime decomposition has a common ramification index,
`p B = ∏ P|p P^e`. -/
theorem dedekindRamification_galois_prime_decomposition
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Ideal.map (algebraMap A B) p =
      ∏ P ∈ p.primesOver B, P ^ Ideal.ramificationIdxIn p B := by
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  rw [Ideal.map_algebraMap_eq_finsetProd_pow (R := B) (S := A) (p := p) hp]
  apply Finset.prod_congr rfl
  intro P hP
  have hP' : P ∈ p.primesOver B := by
    simpa [Set.mem_toFinset] using hP
  have : P.IsPrime := hP'.1
  have : P.LiesOver p := hP'.2
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G]

/-- prime-decomposition theory, Galois fundamental identity:
`r * e * f = |G|`, with `e` and `f` independent of the chosen prime above `p`.
-/
theorem dedekindRamification_galois_fundamental_identity
    [IsDedekindDomain A] (p : Ideal A) [p.IsMaximal] (_hpb : p ≠ ⊥)
    (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [IsTorsionFree A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    (p.primesOver B).ncard *
        (Ideal.ramificationIdxIn p B * Ideal.inertiaDegIn p B) =
      Nat.card G := by
  exact Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G

/-- At an unramified prime, the Galois fundamental identity reduces to
`r * f = |G|`. -/
theorem dedekindRamification_unramified_decomposition_law
    [IsDedekindDomain A]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [IsTorsionFree A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]
    (hunramified : Ideal.ramificationIdxIn p B = 1) :
    (p.primesOver B).ncard * Ideal.inertiaDegIn p B =
      Nat.card G := by
  have hfund :=
    dedekindRamification_galois_fundamental_identity
      (A := A) p hp B G
  simpa [hunramified] using hfund

/-- Division form of the unramified Galois decomposition law. -/
theorem
    dedekindRamification_unramified_numberOfPrimes_eq_degree_div_inertiaDegree
    [IsDedekindDomain A]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [IsTorsionFree A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]
    (hunramified : Ideal.ramificationIdxIn p B = 1) :
    (p.primesOver B).ncard =
      Nat.card G / Ideal.inertiaDegIn p B := by
  have h :=
    dedekindRamification_unramified_decomposition_law
      (A := A) p hp B G hunramified
  rw [← h]
  symm
  simpa [Nat.mul_comm] using
    (Nat.mul_div_cancel_left
      (p.primesOver B).ncard
      (Nat.pos_of_ne_zero
        (Ideal.inertiaDegIn_ne_zero
          (A := A) (B := B) (p := p) G)))

/-- The prime-decomposition tower identity:
orbit-stabilizer for the action on primes above `p`,
`r * #G_P = #G`. -/
theorem dedekindRamification_ncard_primesOver_mul_decomposition_card
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    (p.primesOver B).ncard * Nat.card (decompositionGroup P G) =
      Nat.card G := by
  rw [← IsInvariant.orbit_eq_primesOver A B G p P]
  simpa [decompositionGroup] using
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

/-- The prime-decomposition tower identity:
the decomposition group has cardinality `e * f`. -/
theorem dedekindRamification_decomposition_card_eq_ramificationIdxIn_mul_inertiaDegIn
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Nat.card (decompositionGroup P G) =
      Ideal.ramificationIdxIn p B * Ideal.inertiaDegIn p B := by
  have hdec :=
    dedekindRamification_ncard_primesOver_mul_decomposition_card
      (A := A) (B := B) p P G
  have hfund :=
    dedekindRamification_galois_fundamental_identity
      (A := A) p hp B G
  exact
    Nat.mul_left_cancel
      (Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero p B))
      (hdec.trans hfund.symm)



/-- Prime-decomposition statement:
the quotient of the decomposition group by inertia has cardinality equal to
the inertia degree. -/
theorem dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDeg
    (p : Ideal A) [p.IsMaximal]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
  Nat.card
        (decompositionGroup P G ⧸
          (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
      P.inertiaDeg A := by
  have h : IsGalois (A ⧸ p) (B ⧸ P) :=
    isGalois_iff.mpr ⟨inferInstance, Ideal.Quotient.normal (A := A) G p P⟩
  let : Module.Finite (A ⧸ p) (B ⧸ P) := Ideal.Quotient.finite_of_isInvariant G p P
  let : FiniteDimensional (A ⧸ p) (B ⧸ P) := IsGalois.finiteDimensional_of_finite
    (F := A ⧸ p) (E := B ⧸ P)
  calc
    Nat.card
        (decompositionGroup P G ⧸
          (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
        Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P) := by
      exact
        Nat.card_congr
          (dedekindRamificationDecompositionQuotientInertiaEquivResidueGalois
            (A := A) (B := B) p P G).toEquiv
    _ = Module.finrank (A ⧸ p) (B ⧸ P) := by
      simpa using (IsGalois.card_aut_eq_finrank (F := A ⧸ p) (E := B ⧸ P))
    _ = P.inertiaDeg A := by
      rw [Ideal.inertiaDeg_eq_of_isMaximal p P]

/-- Prime-decomposition statement:
the quotient cardinality is the Galois-invariant inertia degree `f`. -/
theorem dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDegIn
    (p : Ideal A) [p.IsMaximal]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Nat.card
        (decompositionGroup P G ⧸
          (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
      Ideal.inertiaDegIn p B := by
  rw [dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDeg
    (A := A) (B := B) p P G]
  exact (Ideal.inertiaDegIn_eq_inertiaDeg p P G).symm

/-- Prime-decomposition statement:
`#G_P = #(G_P/I_P) * #I_P` for the exact residue sequence. -/
theorem dedekindRamification_decomposition_card_eq_quotient_card_mul_inertia_card
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    Nat.card (decompositionGroup P G) =
      Nat.card
          (decompositionGroup P G ⧸
            (inertiaGroup P G).subgroupOf (decompositionGroup P G)) *
        Nat.card (inertiaGroup P G) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((inertiaGroup P G).subgroupOf (decompositionGroup P G))]
  congr 1
  exact
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv

/-- Prime-decomposition statement:
`#G_P = #I_P * f`, with `f` the Galois-invariant inertia degree. -/
theorem dedekindRamification_decomposition_card_eq_inertia_card_mul_inertiaDegIn
    (p : Ideal A) [p.IsMaximal]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Nat.card (decompositionGroup P G) =
      Nat.card (inertiaGroup P G) * Ideal.inertiaDegIn p B := by
  rw [dedekindRamification_decomposition_card_eq_quotient_card_mul_inertia_card
    (B := B) P G,
    dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDegIn
      (A := A) (B := B) p P G,
    mul_comm]


/-- prime-decomposition theory: the inertia subgroup has cardinality equal to the
Galois ramification index. -/
theorem dedekindRamification_inertia_card_eq_ramificationIdxIn
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (hp : p ≠ ⊥) :
    Nat.card (P.toAddSubgroup.inertia G) = Ideal.ramificationIdxIn p B := by
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : p.IsMaximal := Ideal.IsMaximal.of_isMaximal_liesOver P p
  have hdecomp_inertia :=
    dedekindRamification_decomposition_card_eq_inertia_card_mul_inertiaDegIn
      (A := A) (B := B) p P G
  have hdecomp_ramification :=
    dedekindRamification_decomposition_card_eq_ramificationIdxIn_mul_inertiaDegIn
      (A := A) (B := B) p hp P G
  have hinertiaDeg_pos : 0 < Ideal.inertiaDegIn p B := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg p P G]
    exact P.inertiaDeg_pos A
  apply Nat.mul_left_cancel hinertiaDeg_pos
  calc
    Ideal.inertiaDegIn p B * Nat.card (P.toAddSubgroup.inertia G) =
        Nat.card (P.toAddSubgroup.inertia G) * Ideal.inertiaDegIn p B := by
      rw [mul_comm]
    _ = Nat.card (decompositionGroup P G) := hdecomp_inertia.symm
    _ = Ideal.ramificationIdxIn p B * Ideal.inertiaDegIn p B :=
      hdecomp_ramification
    _ = Ideal.inertiaDegIn p B * Ideal.ramificationIdxIn p B := by
      rw [mul_comm]

end Dedekind
end HilbertRamification
