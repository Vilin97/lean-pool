/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.InfiniteGeneration
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.RadicalExtension
/-!
# extension-side round trip

For an abelian Galois intermediate extension `E/K` of exponent dividing
`n`, adjoining in the ambient algebraic closure all `n`-th roots belonging
to the actual radical subgroup of `E` recovers `E` itself.
-/

@[expose] public section

noncomputable section

namespace KummerTheory

variable {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]

/-- Every ambient root belonging to the actual radical subgroup of `E`
already lies in `E`.  Its ratio with a root chosen in `E` is an `n`-th root
of unity, hence belongs to `K`. -/
theorem kummerRootSet_finiteKummerRadicalSubgroup_le
    (E : IntermediateField K Omega) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    kummerRootSet (K := K) (Omega := Omega) n
        (finiteKummerRadicalSubgroup (K := K) (L := E) n) ⊆ E := by
  intro beta hbeta
  have hbeta_ne : beta ≠ 0 :=
    kummerRootSet_ne_zero n
      (finiteKummerRadicalSubgroup (K := K) (L := E) n) hbeta
  obtain ⟨a, hbeta_pow⟩ := hbeta
  obtain ⟨gamma, hgamma_pow⟩ := a.property
  let gammaOmega : Omegaˣ := Units.map E.val.toMonoidHom gamma
  let betaUnit : Omegaˣ := Units.mk0 beta hbeta_ne
  have hbetaUnit_pow : betaUnit ^ (n : ℕ) =
      Units.map (algebraMap K Omega).toMonoidHom a.1 := by
    apply Units.ext
    exact hbeta_pow
  have hgammaOmega_pow : gammaOmega ^ (n : ℕ) =
      Units.map (algebraMap K Omega).toMonoidHom a.1 := by
    apply Units.ext
    exact congrArg E.val (congrArg Units.val hgamma_pow)
  have hratio_pow : (betaUnit / gammaOmega) ^ (n : ℕ) = 1 := by
    rw [div_pow, hbetaUnit_pow, hgammaOmega_pow]
    exact div_self' _
  let hbase : NthRootsOfUnityInBase (K := K) (L := Omega) n :=
    nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := Omega) n hmu
  obtain ⟨zeta, hzeta⟩ := hbase (betaUnit / gammaOmega) hratio_pow
  have hbeta_eq : betaUnit =
      Units.map (algebraMap K Omega).toMonoidHom zeta * gammaOmega := by
    rw [hzeta]
    exact (div_mul_cancel betaUnit gammaOmega).symm
  have hbeta_val := congrArg Units.val hbeta_eq
  change (betaUnit : Omega) ∈ E
  rw [hbeta_val]
  exact E.mul_mem (E.algebraMap_mem (zeta : K)) gamma.1.property

/-- The radical extension constructed from the actual radical subgroup of
`E` is contained in `E`. -/
theorem kummerRadicalExtension_finiteKummerRadicalSubgroup_le
    (E : IntermediateField K Omega) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    kummerRadicalExtension (K := K) (Omega := Omega) n
        (finiteKummerRadicalSubgroup (K := K) (L := E) n) ≤ E := by
  exact IntermediateField.adjoin_le_iff.mpr
    (kummerRootSet_finiteKummerRadicalSubgroup_le E n hmu)

/-- The internal generation theorem for `E/K`, transported through
`E.val`, gives the reverse inclusion into the ambient radical extension. -/
theorem le_kummerRadicalExtension_finiteKummerRadicalSubgroup
    (E : IntermediateField K Omega)
    [IsGalois K E] [IsMulCommutative Gal(E/K)]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1) :
    E ≤ kummerRadicalExtension (K := K) (Omega := Omega) n
      (finiteKummerRadicalSubgroup (K := K) (L := E) n) := by
  let R : IntermediateField K Omega :=
    kummerRadicalExtension (K := K) (Omega := Omega) n
      (finiteKummerRadicalSubgroup (K := K) (L := E) n)
  have hgeneration :
      IntermediateField.adjoin K
        (finiteKummerRootSet (K := K) (L := E) n) = ⊤ :=
    kummerRootSet_adjoin_eq_top
      (K := K) (Ω := E) n hmu hexponent
  have hroot_subset :
      finiteKummerRootSet (K := K) (L := E) n ⊆ R.comap E.val := by
    intro beta hbeta
    change (beta : Omega) ∈ R
    apply IntermediateField.subset_adjoin K
      (kummerRootSet (K := K) (Omega := Omega) n
        (finiteKummerRadicalSubgroup (K := K) (L := E) n))
    obtain ⟨hbeta_ne, a, hbeta_pow⟩ := hbeta
    let betaUnit : Eˣ := Units.mk0 beta hbeta_ne
    have ha : a ∈ finiteKummerRadicalSubgroup (K := K) (L := E) n := by
      refine ⟨betaUnit, ?_⟩
      apply Units.ext
      exact hbeta_pow
    refine ⟨⟨a, ha⟩, ?_⟩
    exact congrArg E.val hbeta_pow
  have htop_le : (⊤ : IntermediateField K E) ≤ R.comap E.val := by
    rw [← hgeneration]
    exact IntermediateField.adjoin_le_iff.mpr hroot_subset
  intro x hx
  let xE : E := ⟨x, hx⟩
  exact htop_le (Set.mem_univ xE)

/-- **the Kummer correspondence, extension-side round trip.**  For an abelian Galois
intermediate extension of exponent dividing `n`, taking its actual radical
subgroup and adjoining all corresponding roots in the ambient closure
recovers the original intermediate field. -/
theorem kummerRadicalExtension_finiteKummerRadicalSubgroup_eq
    (E : IntermediateField K Omega)
    [IsGalois K E] [IsMulCommutative Gal(E/K)]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1) :
    kummerRadicalExtension (K := K) (Omega := Omega) n
        (finiteKummerRadicalSubgroup (K := K) (L := E) n) = E := by
  apply le_antisymm
  · exact kummerRadicalExtension_finiteKummerRadicalSubgroup_le E n hmu
  · exact le_kummerRadicalExtension_finiteKummerRadicalSubgroup
      E n hmu hexponent

end KummerTheory
