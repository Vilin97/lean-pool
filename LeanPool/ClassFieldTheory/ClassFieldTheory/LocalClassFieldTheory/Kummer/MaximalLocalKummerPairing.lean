/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol
/-!
# The maximal local Kummer pairing

The maximal exponent-`n` Kummer extension of a nonarchimedean local field is
finite.  Evaluating its Kummer pairing at the local Artin automorphism therefore
gives a multiplicative character in the radical variable.  This file packages
that evaluation as a right-variable monoid homomorphism.  Its comparison with
the simple-extension definition of the local Hilbert symbol remains separate.
-/

noncomputable section

namespace LocalClassFieldTheory
namespace Kummer

open KummerTheory LocalFieldTheory RamificationTheory

variable (K : Type) [Field K]
variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The extension obtained by adjoining all exponent-`n` Kummer radicals of
the local field. -/
abbrev maximalLocalKummerExtension (n : ℕ+) :=
  kummerRadicalExtension
    (K := K) (Omega := SeparableClosure K) n
      (maximalKummerSubgroup K n).1

/-- The local Artin homomorphism valued in the maximal exponent-`n` Kummer
extension. -/
noncomputable def maximalLocalKummerNormResidueAutomorphism
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Kˣ →* Gal((maximalLocalKummerExtension K n)/K) := by
  let Delta := maximalKummerSubgroup K n
  let E := maximalLocalKummerExtension K n
  letI : FiniteDimensional K E :=
    maximalKummerRadicalExtension_finiteDimensional K n hnK hmu
  letI : IsAbelianGalois K E :=
    kummerRadicalExtension_isAbelianGalois
      (K := K) (Omega := SeparableClosure K) n hmu Delta.1
  exact abelianLocalArtinMonoidHom K E

private noncomputable def maximalLocalKummerPairingSource
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ) :
    Kˣ →* nthRootsSubgroup (maximalLocalKummerExtension K n) (n : ℕ) := by
  let Delta := maximalKummerSubgroup K n
  let E := maximalLocalKummerExtension K n
  let hDelta : Delta.1 ≤
      finiteKummerRadicalSubgroup (K := K) (L := E) n :=
    le_finiteKummerRadicalSubgroup_kummerRadicalExtension n hnK Delta.1
  let incl : Kˣ →* Delta.1 :=
    { toFun := fun b => ⟨b, by simp [Delta, maximalKummerSubgroup]⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let sigma : Gal(E/K) :=
    maximalLocalKummerNormResidueAutomorphism K n hnK hmu a
  let evaluate : (Gal(E/K) →* nthRootsSubgroup E (n : ℕ)) →*
      nthRootsSubgroup E (n : ℕ) :=
    { toFun := fun chi => chi sigma
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact evaluate.comp
    ((restrictedSubgroupKummerCharacter n hmu Delta hDelta).comp incl)

/-- The maximal finite Kummer pairing, evaluated at the local Artin
automorphism of `a`, is multiplicative in its radical variable. -/
noncomputable def maximalLocalKummerPairingRightHom
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ) :
    Kˣ →* nthRootsSubgroup K (n : ℕ) :=
  (nthRootsSubgroupEquivOfPrimitiveRoots
      K (maximalLocalKummerExtension K n) n hmu).symm.toMonoidHom.comp
    (maximalLocalKummerPairingSource K n hnK hmu a)

@[simp]
theorem maximalLocalKummerPairingRightHom_apply
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    maximalLocalKummerPairingRightHom K n hnK hmu a b =
      (nthRootsSubgroupEquivOfPrimitiveRoots
        K (maximalLocalKummerExtension K n) n hmu).symm
        (maximalLocalKummerPairingSource K n hnK hmu a b) :=
  rfl

/-- Mapping the maximal pairing into its defining extension identifies its
value with the root quotient of any radical having the prescribed power. -/
theorem maximalLocalKummerPairingRightHom_map_eq_rootQuotient_of_pow
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ)
    (beta : (maximalLocalKummerExtension K n)ˣ)
    (hbeta : beta ^ (n : ℕ) =
      Units.map
        (algebraMap K (maximalLocalKummerExtension K n)).toMonoidHom b) :
    nthRootsSubgroupMap K (maximalLocalKummerExtension K n) (n : ℕ)
        (maximalLocalKummerPairingRightHom K n hnK hmu a b) =
      ⟨rootQuotient
          (K := K) (L := maximalLocalKummerExtension K n) beta
          (maximalLocalKummerNormResidueAutomorphism K n hnK hmu a),
        by
          apply rootQuotient_mem_nthRootsSubgroup_of_pow_fixed
          intro tau
          rw [hbeta]
          exact RadicalDatum.smul_algebraMap_unit
            (K := K) (L := maximalLocalKummerExtension K n) tau b⟩ := by
  let Delta := maximalKummerSubgroup K n
  let E := maximalLocalKummerExtension K n
  let hDelta : Delta.1 ≤
      finiteKummerRadicalSubgroup (K := K) (L := E) n :=
    le_finiteKummerRadicalSubgroup_kummerRadicalExtension n hnK Delta.1
  let incl : Kˣ →* Delta.1 :=
    { toFun := fun c => ⟨c, by simp [Delta, maximalKummerSubgroup]⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let sigma : Gal(E/K) :=
    maximalLocalKummerNormResidueAutomorphism K n hnK hmu a
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := E) n
  let delta : D.carrier :=
    restrictedRadicalInclusion n Delta hDelta (incl b)
  let hfixed :=
    restrictedKummerFixed (K := K) (L := E) n hmu
  have hbeta' :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K E).toMonoidHom delta.1 := by
    change beta ^ (n : ℕ) =
      Units.map (algebraMap K E).toMonoidHom b
    exact hbeta
  change
    (nthRootsSubgroupEquivOfPrimitiveRoots K E n hmu)
        ((nthRootsSubgroupEquivOfPrimitiveRoots K E n hmu).symm
          (maximalLocalKummerPairingSource K n hnK hmu a b)) = _
  rw [(nthRootsSubgroupEquivOfPrimitiveRoots K E n hmu).apply_symm_apply]
  apply Subtype.ext
  change D.rootCharacter delta hfixed sigma =
    rootQuotient (K := K) (L := E) beta sigma
  exact (D.rootCharacter_eq_of_same_pow hfixed delta hbeta' sigma).symm

theorem maximalLocalKummerPairing_mul_right
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b c : Kˣ) :
    maximalLocalKummerPairingRightHom K n hnK hmu a (b * c) =
      maximalLocalKummerPairingRightHom K n hnK hmu a b *
        maximalLocalKummerPairingRightHom K n hnK hmu a c :=
  map_mul (maximalLocalKummerPairingRightHom K n hnK hmu a) b c

end Kummer
end LocalClassFieldTheory
