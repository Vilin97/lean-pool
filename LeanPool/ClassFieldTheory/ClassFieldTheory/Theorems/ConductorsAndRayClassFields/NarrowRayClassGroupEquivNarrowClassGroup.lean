/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowClassGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal
/-!
# The narrow ray class group and the narrow ideal class group

At the modulus with no finite part and every real place selected, the
ideal-theoretic ray class group is the narrow class group.  The comparison
preserves the class of each finite prime.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

universe u

variable {K : Type u} [Field K] [NumberField K]

private theorem narrow_rayClassPrimeToIdeals_eq_top :
    rayClassPrimeToIdeals (narrowRayClassModulus K) = ⊤ := by
  ext I
  simp [rayClassPrimeToIdeals, narrowRayClassModulus]

private theorem narrow_rayPrincipalIdealSubgroup_eq_positive :
    rayPrincipalIdealSubgroup (narrowRayClassModulus K) =
      narrowPrincipalIdealSubgroup K := by
  classical
  have hSet :
      {I : NumberFieldFractionalIdealGroup K |
        ∃ x : Kˣ,
          IsRayCongruent (narrowRayClassModulus K) x ∧
            toPrincipalIdeal (𝓞 K) K x = I} =
        (narrowPrincipalIdealSubgroup K : Set _) := by
    ext I
    constructor
    · rintro ⟨x, hx, rfl⟩
      change toPrincipalIdeal (𝓞 K) K x ∈
        (totallyPositiveFieldUnits K).map (toPrincipalIdeal (𝓞 K) K)
      refine ⟨x, ?_, rfl⟩
      intro v
      exact hx.2 v (Finset.mem_univ v)
    · intro hI
      change I ∈
        (totallyPositiveFieldUnits K).map (toPrincipalIdeal (𝓞 K) K) at hI
      obtain ⟨x, hx, rfl⟩ := hI
      refine ⟨x, ?_, rfl⟩
      constructor
      · intro v hv
        simp [narrowRayClassModulus] at hv
      · intro v _
        exact hx v
  calc
    rayPrincipalIdealSubgroup (narrowRayClassModulus K) =
        Subgroup.closure (narrowPrincipalIdealSubgroup K : Set _) := by
      rw [rayPrincipalIdealSubgroup, hSet]
    _ = _ := Subgroup.closure_eq _

private noncomputable def narrowRayIdealsEquiv :
    rayClassPrimeToIdeals (narrowRayClassModulus K) ≃*
      NumberFieldFractionalIdealGroup K :=
  (MulEquiv.subgroupCongr narrow_rayClassPrimeToIdeals_eq_top).trans
    Subgroup.topEquiv

private theorem narrowRayIdealsEquiv_apply
    (I : rayClassPrimeToIdeals (narrowRayClassModulus K)) :
    narrowRayIdealsEquiv I = I.1 := rfl

private theorem narrow_rayPrincipalIdealSubgroup_map :
    (rayPrincipalIdealSubgroupInPrimeTo
      (narrowRayClassModulus K)).map
        (narrowRayIdealsEquiv (K := K) : _ →* _) =
      narrowPrincipalIdealSubgroup K := by
  ext I
  constructor
  · rintro ⟨J, hJ, rfl⟩
    change J.1 ∈ rayPrincipalIdealSubgroup (narrowRayClassModulus K) at hJ
    rw [narrow_rayPrincipalIdealSubgroup_eq_positive (K := K)] at hJ
    change narrowRayIdealsEquiv J ∈ narrowPrincipalIdealSubgroup K
    rw [narrowRayIdealsEquiv_apply]
    exact hJ
  · intro hI
    let J : rayClassPrimeToIdeals (narrowRayClassModulus K) :=
      ⟨I, by rw [narrow_rayClassPrimeToIdeals_eq_top]; trivial⟩
    refine ⟨J, ?_, ?_⟩
    · change I ∈ rayPrincipalIdealSubgroup (narrowRayClassModulus K)
      rw [narrow_rayPrincipalIdealSubgroup_eq_positive (K := K)]
      exact hI
    · exact narrowRayIdealsEquiv_apply J

/-- The narrow ray class group is canonically isomorphic to the independent
ideal-theoretic narrow class group. -/
private noncomputable def narrowRayClassGroupEquivNarrowClassGroup :
    RayClassGroup (narrowRayClassModulus K) ≃* NarrowClassGroup K :=
  QuotientGroup.congr
    (rayPrincipalIdealSubgroupInPrimeTo (narrowRayClassModulus K))
    (narrowPrincipalIdealSubgroup K)
    narrowRayIdealsEquiv
    narrow_rayPrincipalIdealSubgroup_map

/-- The comparison sends a finite-prime ray class to its narrow ideal class. -/
private theorem narrowRayClassGroupEquivNarrowClassGroup_prime
    (v : HeightOneSpectrum (𝓞 K)) :
    narrowRayClassGroupEquivNarrowClassGroup
        (narrowRayClassOfFinitePrime v) =
      QuotientGroup.mk' (narrowPrincipalIdealSubgroup K)
        (finitePrimeFractionalIdeal v) := by
  simp only [narrowRayClassGroupEquivNarrowClassGroup,
    narrowRayClassOfFinitePrime, rayClassOfFinitePrime]
  rw [QuotientGroup.congr_mk']
  simp only [narrowRayIdealsEquiv_apply]

/-- The public narrow class-group comparison, including its action on every
finite-prime class. -/
theorem exists_narrowRayClassGroupEquivNarrowClassGroup
    (K : Type u) [Field K] [NumberField K] :
    ∃ e : RayClassGroup (narrowRayClassModulus K) ≃* NarrowClassGroup K,
      ∀ v : HeightOneSpectrum (𝓞 K),
        e (narrowRayClassOfFinitePrime v) =
          QuotientGroup.mk' (narrowPrincipalIdealSubgroup K)
            (finitePrimeFractionalIdeal v) := by
  refine ⟨narrowRayClassGroupEquivNarrowClassGroup (K := K), ?_⟩
  intro v
  exact narrowRayClassGroupEquivNarrowClassGroup_prime (K := K) v

end ClassFieldTheory
