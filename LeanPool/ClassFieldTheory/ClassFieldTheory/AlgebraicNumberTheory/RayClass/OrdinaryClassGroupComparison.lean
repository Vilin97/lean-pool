/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.OrdinaryRayClassModulus
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayPrincipalIdealSubgroup
public import Mathlib.RingTheory.ClassGroup.Basic
/-!
# The ordinary ray class group and the ideal class group

The ray modulus with zero finite part and no real conditions gives precisely
the ordinary ideal class group.  The equivalence below also identifies their
finite-prime classes.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

private theorem ordinary_rayClassPrimeToIdeals_eq_top :
    rayClassPrimeToIdeals (ordinaryRayClassModulus K) = ⊤ := by
  ext I
  simp [rayClassPrimeToIdeals, ordinaryRayClassModulus]

private theorem ordinary_rayPrincipalIdealSubgroup_eq_range :
    rayPrincipalIdealSubgroup (ordinaryRayClassModulus K) =
      (toPrincipalIdeal (𝓞 K) K).range := by
  have hSet :
      {I : NumberFieldFractionalIdealGroup K |
        ∃ x : Kˣ,
          IsRayCongruent (ordinaryRayClassModulus K) x ∧
            toPrincipalIdeal (𝓞 K) K x = I} =
        ((toPrincipalIdeal (𝓞 K) K).range : Set _) := by
    ext I
    simp [IsRayCongruent, ordinaryRayClassModulus]
  calc
    rayPrincipalIdealSubgroup (ordinaryRayClassModulus K) =
        Subgroup.closure ((toPrincipalIdeal (𝓞 K) K).range : Set _) := by
      rw [rayPrincipalIdealSubgroup, hSet]
    _ = _ := Subgroup.closure_eq _

/-- For the trivial modulus, every fractional ideal is prime to the modulus. -/
noncomputable def ordinaryRayIdealsEquiv :
    rayClassPrimeToIdeals (ordinaryRayClassModulus K) ≃*
      NumberFieldFractionalIdealGroup K :=
  (MulEquiv.subgroupCongr (by exact ordinary_rayClassPrimeToIdeals_eq_top)).trans
    Subgroup.topEquiv

private theorem ordinaryRayIdealsEquiv_apply
    (I : rayClassPrimeToIdeals (ordinaryRayClassModulus K)) :
    ordinaryRayIdealsEquiv I = I.1 := rfl

private theorem ordinary_rayPrincipalIdealSubgroup_map :
    (rayPrincipalIdealSubgroupInPrimeTo
      (ordinaryRayClassModulus K)).map
        (ordinaryRayIdealsEquiv (K := K) : _ →* _) =
      (toPrincipalIdeal (𝓞 K) K).range := by
  ext I
  constructor
  · rintro ⟨J, hJ, rfl⟩
    change J.1 ∈ rayPrincipalIdealSubgroup (ordinaryRayClassModulus K) at hJ
    rw [ordinary_rayPrincipalIdealSubgroup_eq_range (K := K)] at hJ
    change ordinaryRayIdealsEquiv J ∈ (toPrincipalIdeal (𝓞 K) K).range
    rw [ordinaryRayIdealsEquiv_apply]
    exact hJ
  · intro hI
    let J : rayClassPrimeToIdeals (ordinaryRayClassModulus K) :=
      ⟨I, by rw [ordinary_rayClassPrimeToIdeals_eq_top]; trivial⟩
    refine ⟨J, ?_, ?_⟩
    · change I ∈ rayPrincipalIdealSubgroup (ordinaryRayClassModulus K)
      rw [ordinary_rayPrincipalIdealSubgroup_eq_range (K := K)]
      exact hI
    · exact ordinaryRayIdealsEquiv_apply J

/-- The ideal-theoretic ray class group at the trivial modulus is the
ordinary ideal class group. -/
noncomputable def ordinaryRayClassGroupEquivClassGroup :
    RayClassGroup (ordinaryRayClassModulus K) ≃* ClassGroup (𝓞 K) :=
  (QuotientGroup.congr
      (rayPrincipalIdealSubgroupInPrimeTo (ordinaryRayClassModulus K))
      (toPrincipalIdeal (𝓞 K) K).range
      ordinaryRayIdealsEquiv
      (by exact ordinary_rayPrincipalIdealSubgroup_map)).trans
    (ClassGroup.equiv K).symm

/-- The equivalence takes the ordinary ray class of a finite prime to the
usual prime ideal class. -/
theorem ordinaryRayClassGroupEquivClassGroup_prime
    (v : HeightOneSpectrum (𝓞 K)) :
    ordinaryRayClassGroupEquivClassGroup
        (ordinaryRayClassOfFinitePrime v) =
      ClassGroup.mk K (finitePrimeFractionalIdeal v) := by
  apply (ClassGroup.equiv K).injective
  simp only [ordinaryRayClassGroupEquivClassGroup, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, ordinaryRayClassOfFinitePrime,
    rayClassOfFinitePrime, ClassGroup.equiv_mk]
  rw [QuotientGroup.congr_mk']
  simp only [ordinaryRayIdealsEquiv_apply]
  simp only [FractionalIdeal.canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl]
  congr 1

end ClassFieldTheory
