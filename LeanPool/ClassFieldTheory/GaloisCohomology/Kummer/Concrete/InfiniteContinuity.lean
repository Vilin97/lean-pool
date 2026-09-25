/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.FiniteCharacterEquiv
/-!
# continuity of Kummer characters for infinite extensions

For an infinite Galois extension `Ω/K`, a Kummer character attached to a
chosen root `β` is already determined on the finite Galois normal closure of
`K(β)`.  Equivalently, its kernel contains the fixing subgroup of that finite
Galois intermediate field.  This makes the kernel open in the Krull topology
and proves continuity into the discrete group of `n`-th roots of unity.

The final construction descends these continuous characters through the
ambient-power quotient `Δ / (Δ ∩ Kˣⁿ)`.  No surjectivity or lattice correspondence is
asserted here.
-/

@[expose] public section

noncomputable section

namespace KummerTheory

open scoped Topology
open Filter

/-- The group `μₙ(L)` equipped explicitly with the discrete topology used for
continuous characters in the infinite form of the finite Kummer character equivalence. -/
def DiscreteNthRootsSubgroup (L : Type*) [Field L] (n : ℕ) :=
  nthRootsSubgroup L n

namespace DiscreteNthRootsSubgroup

variable (L : Type*) [Field L] (n : ℕ)

/-- The discrete copy of the roots-of-unity subgroup retains its commutative group structure. -/
instance : CommGroup (DiscreteNthRootsSubgroup L n) :=
  inferInstanceAs (CommGroup (nthRootsSubgroup L n))

/-- The discrete roots-of-unity copy is equipped with the bottom topology. -/
instance : TopologicalSpace (DiscreteNthRootsSubgroup L n) := ⊥

/-- The bottom topology makes the roots-of-unity copy discrete. -/
instance : DiscreteTopology (DiscreteNthRootsSubgroup L n) :=
  discreteTopology_bot _

end DiscreteNthRootsSubgroup

section InfiniteKummerContinuity

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The Kummer root character with codomain given its intended discrete
topology. -/
def infiniteKummerRootCharacter
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier) :
    Gal(Ω/K) →* DiscreteNthRootsSubgroup Ω (n : ℕ) :=
  (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).rootCharacterToMuWithoutSection
    a (nthRootsOfUnity_fixed (K := K) (L := Ω) n hmu)

/-- The infinite Kummer root character evaluates by the usual Galois ratio. -/
@[simp] theorem infiniteKummerRootCharacter_apply
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier)
    (σ : Gal(Ω/K)) :
    infiniteKummerRootCharacter n hmu a σ =
      (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).rootCharacterToMuWithoutSection
        a (nthRootsOfUnity_fixed (K := K) (L := Ω) n hmu) σ :=
  rfl

variable [IsGalois K Ω]

/-- The fixing subgroup of the finite Galois normal closure of the chosen
root lies in the kernel of its Kummer character. -/
theorem fixingSubgroup_adjoin_root_le_infiniteKummerRootCharacter_ker
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier) :
    (FiniteGaloisIntermediateField.adjoin K
      {((chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).root a : Ω)}).fixingSubgroup ≤
        MonoidHom.ker (infiniteKummerRootCharacter n hmu a) := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n
  let E := FiniteGaloisIntermediateField.adjoin K {(D.root a : Ω)}
  intro σ hσ
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  change D.rootCharacter a
      (nthRootsOfUnity_fixed (K := K) (L := Ω) n hmu) σ = 1
  rw [D.rootCharacter_apply]
  apply (rootQuotient_eq_one_iff (K := K) (L := Ω) (D.root a) σ).2
  apply Units.ext
  exact ((IntermediateField.mem_fixingSubgroup_iff E.toIntermediateField σ).mp hσ)
    (D.root a : Ω)
    (FiniteGaloisIntermediateField.subset_adjoin K {(D.root a : Ω)}
      (Set.mem_singleton (D.root a : Ω)))

/-- The kernel of an infinite Kummer root character is open in the Krull
topology. -/
theorem infiniteKummerRootCharacter_isOpen_ker
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier) :
    IsOpen (MonoidHom.ker (infiniteKummerRootCharacter n hmu a) :
      Set Gal(Ω/K)) := by
  exact Subgroup.isOpen_mono
    (fixingSubgroup_adjoin_root_le_infiniteKummerRootCharacter_ker n hmu a)
    (IntermediateField.fixingSubgroup_isOpen
      (FiniteGaloisIntermediateField.adjoin K
        {((chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).root a : Ω)}).toIntermediateField)

/-- Every Kummer root character for an infinite actual-field Galois extension
is continuous into the discrete group `μₙ(Ω)`. -/
theorem infiniteKummerRootCharacter_continuous
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier) :
    Continuous (infiniteKummerRootCharacter n hmu a) := by
  apply continuous_of_continuousAt_one (infiniteKummerRootCharacter n hmu a)
  rw [ContinuousAt, map_one]
  rw [show (𝓝 : DiscreteNthRootsSubgroup Ω (n : ℕ) →
      Filter (DiscreteNthRootsSubgroup Ω (n : ℕ))) = pure from nhds_discrete _,
    tendsto_pure]
  exact (infiniteKummerRootCharacter_isOpen_ker n hmu a).mem_nhds (by simp)

/-- The continuous Kummer character attached to one radical element. -/
def infiniteKummerContinuousRootCharacter
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier) :
    Gal(Ω/K) →ₜ* DiscreteNthRootsSubgroup Ω (n : ℕ) :=
  ⟨infiniteKummerRootCharacter n hmu a,
    infiniteKummerRootCharacter_continuous n hmu a⟩

/-- Radical elements map multiplicatively to continuous Kummer characters. -/
def infiniteKummerContinuousCharacter
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n) :
    (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier →*
      (Gal(Ω/K) →ₜ* DiscreteNthRootsSubgroup Ω (n : ℕ)) where
  toFun := infiniteKummerContinuousRootCharacter n hmu
  map_one' := by
    apply ContinuousMonoidHom.ext
    intro σ
    exact congrArg
      (fun χ : Gal(Ω/K) →* nthRootsSubgroup Ω (n : ℕ) => χ σ)
      (map_one
        ((chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).kummerCharacterWithoutSection
          (nthRootsOfUnity_fixed (K := K) (L := Ω) n hmu)))
  map_mul' := by
    intro a b
    apply ContinuousMonoidHom.ext
    intro σ
    exact congrArg
      (fun χ : Gal(Ω/K) →* nthRootsSubgroup Ω (n : ℕ) => χ σ)
      (map_mul
        ((chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).kummerCharacterWithoutSection
          (nthRootsOfUnity_fixed (K := K) (L := Ω) n hmu)) a b)

/-- The infinite continuous Kummer character map on the ambient-power quotient
`Δ / (Δ ∩ Kˣⁿ)`.  This is the canonical map; surjectivity is not asserted,
and injectivity is proved below from the existing algebraic kernel result. -/
def infiniteKummerContinuousQuotientCharacter
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n) :
    (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).RadicalQuotient →*
      (Gal(Ω/K) →ₜ* DiscreteNthRootsSubgroup Ω (n : ℕ)) :=
  (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).radicalQuotientLift
    (infiniteKummerContinuousCharacter n hmu)
    (by
      let D := chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n
      let hfixed := nthRootsOfUnity_fixed (K := K) (L := Ω) n hmu
      intro a ha
      change infiniteKummerContinuousRootCharacter n hmu a = 1
      apply ContinuousMonoidHom.ext
      intro σ
      have hker : D.kummerCharacterWithoutSection hfixed a = 1 :=
        D.ambientNthPowersSubgroup_le_ker hfixed ha
      exact congrArg
        (fun χ : Gal(Ω/K) →* nthRootsSubgroup Ω (n : ℕ) => χ σ) hker)

/-- Forgetting continuity recovers the previously constructed algebraic
Kummer character on the same ambient-power quotient. -/
theorem infiniteKummerContinuousQuotientCharacter_toMonoidHom
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n)
    (q : (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).RadicalQuotient) :
    (infiniteKummerContinuousQuotientCharacter n hmu q).toMonoidHom =
      (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).quotientKummerCharacterWithoutSection
        (nthRootsOfUnity_fixed (K := K) (L := Ω) n hmu) q := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n
  obtain ⟨a, rfl⟩ := D.radicalQuotientMk_surjective q
  apply MonoidHom.ext
  intro σ
  rfl

/-- The continuous character map on the ambient-power quotient is injective.  This is
the existing algebraic kernel computation with the continuity structure
forgotten; it does not use or assert surjectivity. -/
theorem infiniteKummerContinuousQuotientCharacter_injective
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n) :
    Function.Injective (infiniteKummerContinuousQuotientCharacter n hmu) := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n
  let hfixed := nthRootsOfUnity_fixed (K := K) (L := Ω) n hmu
  intro q r hqr
  apply D.quotientKummerCharacterWithoutSection_injective hfixed
  have hforget := congrArg
    (fun χ : Gal(Ω/K) →ₜ* DiscreteNthRootsSubgroup Ω (n : ℕ) => χ.toMonoidHom) hqr
  change (infiniteKummerContinuousQuotientCharacter n hmu q).toMonoidHom =
    (infiniteKummerContinuousQuotientCharacter n hmu r).toMonoidHom at hforget
  rw [infiniteKummerContinuousQuotientCharacter_toMonoidHom n hmu q,
    infiniteKummerContinuousQuotientCharacter_toMonoidHom n hmu r] at hforget
  exact hforget

end InfiniteKummerContinuity

end KummerTheory
