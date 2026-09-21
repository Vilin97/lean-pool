/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.SimpleExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
/-!
# Local Hilbert symbols

This file constructs the local Hilbert symbol from the public Kummer-theory
and local-reciprocity APIs.

For `b : Kˣ`, a root `β` of `X ^ n - b` is chosen in the separable closure
and the literal simple extension `K(β)` is formed.  If `K` contains the
`n`-th roots of unity, Kummer theory makes this extension finite abelian
Galois.  The Hilbert symbol is the root quotient of the local Artin
automorphism, transported back to `μₙ(K)`.
-/

noncomputable section

namespace LocalClassFieldTheory
namespace Kummer

open CyclicCohomology KummerTheory ClassFormation
open LocalFieldTheory LocalClassFieldTheory

variable (K : Type) [Field K]

variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The local Artin automorphism of the concrete Kummer extension. -/
noncomputable def chosenSimpleKummerNormResidueAutomorphism
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    Kˣ →* Gal((chosenSimpleKummerExtension K n hnK b)/K) := by
  let E := chosenSimpleKummerExtension K n hnK b
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  exact abelianLocalArtinMonoidHom K E

/-- The local Hilbert symbol `(a,b)ₙ`, valued in the actual subgroup
`μₙ(K)`. -/
noncomputable def localHilbertSymbol
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    nthRootsSubgroup K (n : ℕ) :=
  (nthRootsSubgroupEquivOfPrimitiveRoots
    K (chosenSimpleKummerExtension K n hnK b) n hmu).symm
      (chosenSimpleKummerRootCharacter K n hnK hmu b
        (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a))

/-- For fixed `b`, the local Hilbert symbol is a homomorphism in its first
argument. -/
noncomputable def localHilbertSymbolHom
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    Kˣ →* nthRootsSubgroup K (n : ℕ) :=
  (nthRootsSubgroupEquivOfPrimitiveRoots
      K (chosenSimpleKummerExtension K n hnK b) n hmu).symm.toMonoidHom.comp
    ((chosenSimpleKummerRootCharacter K n hnK hmu b).comp
      (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b))

@[simp]
theorem localHilbertSymbolHom_apply
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    localHilbertSymbolHom K n hnK hmu b a =
      localHilbertSymbol K n hnK hmu a b :=
  rfl

/-- Base change sends the Hilbert symbol to its defining root quotient. -/
theorem localHilbertSymbol_map_eq_rootQuotient
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    nthRootsSubgroupMap K (chosenSimpleKummerExtension K n hnK b) (n : ℕ)
        (localHilbertSymbol K n hnK hmu a b) =
      ⟨rootQuotient
          (K := K) (L := chosenSimpleKummerExtension K n hnK b)
          (chosenSimpleKummerRootUnit K n hnK b)
          (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a),
        chosenSimpleKummer_rootQuotient_mem K n hnK b
          (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a)⟩ := by
  change
    (nthRootsSubgroupEquivOfPrimitiveRoots
      K (chosenSimpleKummerExtension K n hnK b) n hmu)
        ((nthRootsSubgroupEquivOfPrimitiveRoots
          K (chosenSimpleKummerExtension K n hnK b) n hmu).symm
            (chosenSimpleKummerRootCharacter K n hnK hmu b
              (chosenSimpleKummerNormResidueAutomorphism
                K n hnK hmu b a))) = _
  rw [(nthRootsSubgroupEquivOfPrimitiveRoots
    K (chosenSimpleKummerExtension K n hnK b) n hmu).apply_symm_apply]
  exact
    chosenSimpleKummerRootCharacter_apply K n hnK hmu b
      (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a)

/-- The local Artin automorphism acts on the chosen radical by
multiplication with the Hilbert symbol. -/
theorem normResidueAutomorphism_map_rootUnit_eq_hilbertSymbol_mul
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    let E := chosenSimpleKummerExtension K n hnK b
    let sigma : Gal(E/K) :=
      chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a
    let beta : Eˣ := chosenSimpleKummerRootUnit K n hnK b
    Units.map sigma beta =
      Units.map (algebraMap K E).toMonoidHom
          (localHilbertSymbol K n hnK hmu a b).1 * beta := by
  let E := chosenSimpleKummerExtension K n hnK b
  let sigma : Gal(E/K) :=
    chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a
  let beta : Eˣ := chosenSimpleKummerRootUnit K n hnK b
  change Units.map sigma beta =
    Units.map (algebraMap K E).toMonoidHom
      (localHilbertSymbol K n hnK hmu a b).1 * beta
  have hmap0 := congrArg Subtype.val
    (localHilbertSymbol_map_eq_rootQuotient K n hnK hmu a b)
  have hmap :
      Units.map (algebraMap K E).toMonoidHom
          (localHilbertSymbol K n hnK hmu a b).1 =
        rootQuotient (K := K) (L := E) beta sigma := by
    change
      Units.map
          (algebraMap K (chosenSimpleKummerExtension K n hnK b)).toMonoidHom
          (localHilbertSymbol K n hnK hmu a b).1 =
        rootQuotient
          (K := K) (L := chosenSimpleKummerExtension K n hnK b)
          (chosenSimpleKummerRootUnit K n hnK b)
          (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a) at hmap0
    simpa only [E, beta, sigma] using hmap0
  rw [hmap]
  simpa only [AlgEquiv.smul_units_def] using
    (rootQuotient_mul_right
      (K := K) (L := E) beta sigma).symm

/-- Element-valued form of the defining Artin action. -/
theorem normResidueAutomorphism_apply_root_eq_hilbertSymbol_mul
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    let E := chosenSimpleKummerExtension K n hnK b
    let beta : E := (chosenSimpleKummerRootUnit K n hnK b : Eˣ)
    chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a beta =
      algebraMap K E ((localHilbertSymbol K n hnK hmu a b).1 : K) * beta := by
  let E := chosenSimpleKummerExtension K n hnK b
  let betaUnit : Eˣ := chosenSimpleKummerRootUnit K n hnK b
  have hunit :
      Units.map
          (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a) betaUnit =
        Units.map (algebraMap K E).toMonoidHom
            (localHilbertSymbol K n hnK hmu a b).1 * betaUnit := by
    simpa only [E, betaUnit] using
      (normResidueAutomorphism_map_rootUnit_eq_hilbertSymbol_mul
        K n hnK hmu a b)
  exact congrArg (fun u : Eˣ => (u : E)) hunit

/-- The concrete Artin homomorphism has precisely the local norm subgroup
as its kernel. -/
theorem chosenSimpleKummerNormResidueAutomorphism_ker
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b).ker =
      LocalFieldTheory.localNormSubgroup K
        (chosenSimpleKummerExtension K n hnK b) := by
  let E := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  change (abelianLocalArtinMonoidHom K E).ker =
    LocalFieldTheory.localNormSubgroup K E
  exact abelianLocalArtinMonoidHom_ker K E

/-- Every norm from `K(ⁿ√b)` is killed by the Hilbert-symbol character. -/
theorem localNormSubgroup_le_localHilbertSymbolHom_ker
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    LocalFieldTheory.localNormSubgroup K
        (chosenSimpleKummerExtension K n hnK b) ≤
      (localHilbertSymbolHom K n hnK hmu b).ker := by
  intro a ha
  have hartin :
      chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b a = 1 := by
    have hker :
        a ∈ (chosenSimpleKummerNormResidueAutomorphism K n hnK hmu b).ker := by
      rw [chosenSimpleKummerNormResidueAutomorphism_ker K n hnK hmu b]
      exact ha
    exact hker
  change localHilbertSymbolHom K n hnK hmu b a = 1
  simp [localHilbertSymbolHom, hartin]

/-- The local Hilbert symbol descended to the concrete local norm
quotient. -/
noncomputable def localHilbertSymbolFromNormQuotient
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    LocalFieldTheory.NormQuotient K
        (chosenSimpleKummerExtension K n hnK b) →*
      nthRootsSubgroup K (n : ℕ) :=
  LocalFieldTheory.normQuotientLift
    (localHilbertSymbolHom K n hnK hmu b)
    (localNormSubgroup_le_localHilbertSymbolHom_ker
      K n hnK hmu b)

@[simp]
theorem localHilbertSymbolFromNormQuotient_normClass
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    localHilbertSymbolFromNormQuotient K n hnK hmu b
        (LocalFieldTheory.normClass K
          (chosenSimpleKummerExtension K n hnK b) a) =
      localHilbertSymbol K n hnK hmu a b := by
  rw [localHilbertSymbolFromNormQuotient]
  exact localHilbertSymbolHom_apply K n hnK hmu a b

end Kummer
end LocalClassFieldTheory
