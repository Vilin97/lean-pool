/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.GaloisCohomology
/-!
# Root characters for Kummer theory

Support API for root-quotient constructions in concrete Kummer extensions.
-/

namespace KummerTheory

open groupCohomology

section RootQuotientPrelim

variable {L : Type*} [Field L]

/-- Two unit roots with the same `n`-th power differ by an `n`-th root of unity. -/
theorem div_pow_eq_one_of_pow_eq_pow
    {n : ℕ} {u v : Lˣ} (h : u ^ n = v ^ n) :
    (u / v) ^ n = 1 := by
  rw [div_pow, h]
  exact div_self' (v ^ n)

end RootQuotientPrelim

section TorsionSubgroups

variable (L : Type*) [Field L]

/-- The subgroup of units whose `n`-th power is `1`. -/
def nthRootsSubgroup (n : ℕ) : Subgroup Lˣ where
  carrier := {u | u ^ n = 1}
  one_mem' := by
    simp
  mul_mem' := by
    intro u v hu hv
    change (u * v) ^ n = 1
    rw [mul_pow, hu, hv, one_mul]
  inv_mem' := by
    intro u hu
    change u⁻¹ ^ n = 1
    rw [inv_pow, hu, inv_one]

/-- Membership in the roots subgroup is equivalent to satisfying the `n`th-root equation. -/
@[simp] theorem mem_nthRootsSubgroup_iff {n : ℕ} {u : Lˣ} :
    u ∈ nthRootsSubgroup L n ↔ u ^ n = 1 :=
  Iff.rfl

/-- If two units have the same `n`-th power, then their quotient lies in `μₙ(L)`. -/
theorem div_mem_nthRootsSubgroup_of_pow_eq_pow
    {n : ℕ} {u v : Lˣ} (h : u ^ n = v ^ n) :
    u / v ∈ nthRootsSubgroup L n := by
  rw [mem_nthRootsSubgroup_iff]
  exact div_pow_eq_one_of_pow_eq_pow (n := n) h

/-- Galois automorphisms preserve the subgroup of `n`-torsion units. -/
theorem smul_mem_nthRootsSubgroup
    {K : Type*} [Field K] [Algebra K L]
    (n : ℕ) (σ : Gal(L/K)) {u : Lˣ}
    (hu : u ∈ nthRootsSubgroup L n) :
    σ • u ∈ nthRootsSubgroup L n := by
  rw [mem_nthRootsSubgroup_iff] at hu ⊢
  calc
    (σ • u) ^ n = σ • (u ^ n) := by
      exact (map_pow (MulDistribMulAction.toMonoidHom Lˣ σ) u n).symm
    _ = 1 := by simp [hu]

end TorsionSubgroups

section RootQuotients

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The basic root-quotient attached to a unit `β` and a Galois automorphism `σ`. -/
def rootQuotient (β : Lˣ) (σ : Gal(L/K)) : Lˣ :=
  σ • β / β

/-- The root-quotient attached to the identity automorphism is trivial. -/
@[simp] theorem rootQuotient_one (β : Lˣ) :
    rootQuotient (K := K) (L := L) β 1 = 1 := by
  simp [rootQuotient]

/-- Multiplying the root-quotient by the chosen root recovers its Galois transform. -/
@[simp] theorem rootQuotient_mul_right (β : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β σ * β = σ • β := by
  simp [rootQuotient]

/-- Base-field units have trivial root-quotient. -/
@[simp] theorem rootQuotient_algebraMap_unit (u : Kˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) (Units.map (algebraMap K L).toMonoidHom u) σ = 1 := by
  unfold rootQuotient
  ext
  simp

/-- The root-quotient attached to a product is the product of the root-quotients. -/
theorem rootQuotient_mul_root (u v : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) (u * v) σ =
      rootQuotient (K := K) (L := L) u σ *
        rootQuotient (K := K) (L := L) v σ := by
  simp [rootQuotient, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The root-quotient is trivial exactly when the chosen root is fixed by `σ`. -/
theorem rootQuotient_eq_one_iff (β : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β σ = 1 ↔ σ • β = β := by
  unfold rootQuotient
  exact div_eq_one

/-- The root-quotient construction satisfies the multiplicative cocycle identity. -/
theorem rootQuotient_mul (β : Lˣ) (σ τ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β (σ * τ) =
      σ • rootQuotient (K := K) (L := L) β τ *
        rootQuotient (K := K) (L := L) β σ := by
  rw [rootQuotient]
  rw [mul_smul]
  simp [rootQuotient, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Reformulation: `σ ↦ σ(β) / β` is a multiplicative `1`-cocycle. -/
theorem isMulCocycle₁_rootQuotient (β : Lˣ) :
    IsMulCocycle₁ (rootQuotient (K := K) (L := L) β) := by
  intro σ τ
  exact rootQuotient_mul (K := K) (L := L) β σ τ

/-- The root-quotient at `σ⁻¹` is determined by the value at `σ`. -/
theorem rootQuotient_inv (β : Lˣ) (σ : Gal(L/K)) :
    σ • rootQuotient (K := K) (L := L) β σ⁻¹ =
      (rootQuotient (K := K) (L := L) β σ)⁻¹ := by
  exact groupCohomology.map_inv_of_isMulCocycle₁
    (isMulCocycle₁_rootQuotient (K := K) (L := L) β) σ

/-- The root-quotient of a quotient is the quotient of the root-quotients. -/
theorem rootQuotient_div (u v : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) (u / v) σ =
      rootQuotient (K := K) (L := L) u σ /
        rootQuotient (K := K) (L := L) v σ := by
  simp [rootQuotient, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Changing the chosen root changes the corresponding quotient cocycle by a coboundary. -/
theorem rootQuotient_changeRoot (u v : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) u σ /
        rootQuotient (K := K) (L := L) v σ =
      rootQuotient (K := K) (L := L) (u / v) σ := by
  exact (rootQuotient_div (K := K) (L := L) u v σ).symm

/-- If `β ^ n` is fixed by Galois, then `σ(β) / β` is `n`-torsion. -/
theorem rootQuotient_pow_eq_one_of_pow_fixed
    {n : ℕ} {β : Lˣ} (hβ : ∀ σ : Gal(L/K), σ • (β ^ n) = β ^ n)
    (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β σ ^ n = 1 := by
  unfold rootQuotient
  apply div_pow_eq_one_of_pow_eq_pow
  exact (map_pow (MulDistribMulAction.toMonoidHom Lˣ σ) β n).symm.trans (hβ σ)

/-- If `β ^ n` is fixed by Galois, then the root-quotient lands in `μₙ(L)`. -/
theorem rootQuotient_mem_nthRootsSubgroup_of_pow_fixed
    {n : ℕ} {β : Lˣ} (hβ : ∀ σ : Gal(L/K), σ • (β ^ n) = β ^ n)
    (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β σ ∈ nthRootsSubgroup L n := by
  rw [mem_nthRootsSubgroup_iff]
  exact rootQuotient_pow_eq_one_of_pow_fixed (K := K) (L := L) hβ σ

end RootQuotients

section RadicalData

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/--
A radical datum of exponent `n` consists of a subgroup of `Kˣ` together with a chosen
`n`-th root in `Lˣ` for each of its elements.
-/
structure RadicalDatum (n : ℕ+) where
  /-- The subgroup of base-field units for which roots are chosen. -/
  carrier : Subgroup Kˣ
  /-- A chosen `n`-th root in `Lˣ` for each unit in `carrier`. -/
  root : carrier → Lˣ
  /-- Each chosen root has `n`-th power equal to the image of its base-field unit in `Lˣ`. -/
  root_pow_eq : ∀ a : carrier,
    root a ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1

namespace RadicalDatum

variable {n : ℕ+} (D : RadicalDatum (K := K) (L := L) n)

/-- The chosen root witness has the prescribed `n`-th power. -/
@[simp] theorem root_pow_eq_map (a : D.carrier) :
    D.root a ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1 :=
  D.root_pow_eq a

/-- Two `n`-th roots of the same radical element differ by an `n`-th root of unity. -/
theorem div_pow_eq_one_of_same_image
    {u v : Lˣ} (a : D.carrier)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (hv : v ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1) :
    (u / v) ^ (n : ℕ) = 1 := by
  exact div_pow_eq_one_of_pow_eq_pow (n := (n : ℕ)) (hu.trans hv.symm)

/-- The root-quotient map `σ ↦ σ(β) / β` attached to the chosen root witness of `a`. -/
def rootCocycle (a : D.carrier) (σ : Gal(L/K)) : Lˣ :=
  rootQuotient (K := K) (L := L) (D.root a) σ

/-- The chosen root-quotient is trivial at the identity automorphism. -/
@[simp] theorem rootCocycle_one (a : D.carrier) :
    D.rootCocycle a 1 = 1 := by
  simp [rootCocycle]

/-- The chosen root-quotient satisfies the multiplicative cocycle identity. -/
theorem rootCocycle_mul (a : D.carrier) (σ τ : Gal(L/K)) :
    D.rootCocycle a (σ * τ) =
      σ • D.rootCocycle a τ * D.rootCocycle a σ := by
  exact rootQuotient_mul (K := K) (L := L) (D.root a) σ τ

/-- Reformulation: the chosen root-quotient is a multiplicative `1`-cocycle. -/
theorem isMulCocycle₁_rootCocycle (a : D.carrier) :
    IsMulCocycle₁ (D.rootCocycle a) := by
  exact isMulCocycle₁_rootQuotient (K := K) (L := L) (D.root a)

/-- Galois automorphisms fix units coming from the base field. -/
@[simp] theorem smul_algebraMap_unit (σ : Gal(L/K)) (u : Kˣ) :
    σ • Units.map (algebraMap K L).toMonoidHom u =
      Units.map (algebraMap K L).toMonoidHom u := by
  ext
  simp

/-- The chosen root-quotient of `a` lands in the `n`-torsion subgroup of `Lˣ`. -/
theorem rootCocycle_pow_eq_one (a : D.carrier) (σ : Gal(L/K)) :
    D.rootCocycle a σ ^ (n : ℕ) = 1 := by
  refine rootQuotient_pow_eq_one_of_pow_fixed (K := K) (L := L)
      (β := D.root a) ?_ σ
  intro τ
  rw [D.root_pow_eq_map]
  exact smul_algebraMap_unit (K := K) (L := L) τ a.1

/-- The chosen root-quotient of `a` belongs to `μₙ(L)`. -/
theorem rootCocycle_mem_nthRootsSubgroup (a : D.carrier) (σ : Gal(L/K)) :
    D.rootCocycle a σ ∈ nthRootsSubgroup L (n : ℕ) := by
  rw [mem_nthRootsSubgroup_iff]
  exact D.rootCocycle_pow_eq_one a σ

/-- If two root choices are used for the same radical element, their quotient is `n`-torsion. -/
theorem changeRoot_rootQuotient_pow_eq_one
    {u v : Lˣ} (a : D.carrier)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (hv : v ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (σ : Gal(L/K)) :
    (rootQuotient (K := K) (L := L) u σ /
        rootQuotient (K := K) (L := L) v σ) ^ (n : ℕ) = 1 := by
  rw [rootQuotient_changeRoot]
  refine rootQuotient_pow_eq_one_of_pow_fixed (K := K) (L := L)
      (β := u / v) ?_ σ
  intro τ
  have hpow : (u / v) ^ (n : ℕ) = 1 :=
    D.div_pow_eq_one_of_same_image a hu hv
  rw [hpow]
  simp

/-- Change-of-root quotient cocycles land in `μₙ(L)`. -/
theorem changeRoot_rootQuotient_mem_nthRootsSubgroup
    {u v : Lˣ} (a : D.carrier)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (hv : v ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) u σ /
        rootQuotient (K := K) (L := L) v σ ∈ nthRootsSubgroup L (n : ℕ) := by
  rw [mem_nthRootsSubgroup_iff]
  exact D.changeRoot_rootQuotient_pow_eq_one a hu hv σ

/-- If `μₙ(L)` is fixed by Galois, root-quotients for the same radical element agree. -/
theorem rootQuotient_eq_rootCocycle_of_same_pow
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    {u : Lˣ} (a : D.carrier)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) u σ = D.rootCocycle a σ := by
  have hpow : (u / D.root a) ^ (n : ℕ) = 1 := by
    exact D.div_pow_eq_one_of_same_image a hu (D.root_pow_eq_map a)
  have hfixed_delta : σ • (u / D.root a) = u / D.root a :=
    hfixed σ (u / D.root a) hpow
  have hquot_one : rootQuotient (K := K) (L := L) (u / D.root a) σ = 1 :=
    (rootQuotient_eq_one_iff (K := K) (L := L) (u / D.root a) σ).2 hfixed_delta
  have hdiv_one : rootQuotient (K := K) (L := L) u σ / D.rootCocycle a σ = 1 := by
    rw [rootCocycle, rootQuotient_changeRoot]
    exact hquot_one
  exact div_eq_one.mp hdiv_one

/-- If `μₙ(L)` is fixed by Galois, the chosen root-quotient is a character. -/
def rootCharacter (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    Gal(L/K) →* Lˣ where
  toFun := D.rootCocycle a
  map_one' := by
    exact D.rootCocycle_one a
  map_mul' := by
    intro σ τ
    rw [D.rootCocycle_mul]
    rw [hfixed σ (D.rootCocycle a τ) (D.rootCocycle_pow_eq_one a τ)]
    exact mul_comm _ _

/-- The Kummer root character evaluates as the Galois translate divided by the chosen root. -/
@[simp] theorem rootCharacter_apply (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (σ : Gal(L/K)) :
    D.rootCharacter a hfixed σ = D.rootCocycle a σ :=
  rfl

/-- The canonical character agrees with any root quotient having the same `n`-th power. -/
theorem rootCharacter_eq_of_same_pow
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    {u : Lˣ} (a : D.carrier)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) u σ = D.rootCharacter a hfixed σ := by
  rw [D.rootCharacter_apply]
  exact D.rootQuotient_eq_rootCocycle_of_same_pow hfixed a hu σ

/-- The character obtained from a chosen root still takes values in `μₙ(L)`. -/
theorem rootCharacter_pow_eq_one (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (σ : Gal(L/K)) :
    D.rootCharacter a hfixed σ ^ (n : ℕ) = 1 := by
  rw [D.rootCharacter_apply]
  exact D.rootCocycle_pow_eq_one a σ

/-- The character obtained from a chosen root lands in `μₙ(L)`. -/
theorem rootCharacter_mem_nthRootsSubgroup (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (σ : Gal(L/K)) :
    D.rootCharacter a hfixed σ ∈ nthRootsSubgroup L (n : ℕ) := by
  rw [mem_nthRootsSubgroup_iff]
  exact D.rootCharacter_pow_eq_one a hfixed σ

end RadicalDatum
end RadicalData

end KummerTheory
