/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.ArithmeticIdealDecompositionLaw
/-!
# Ideal norms and arithmetic Artin exactness

For a finite abelian extension `L / K` and a defining modulus `m`, the
genuine ideal group

`N_{L/K} J_L^m P_K^m`

is `RayClass.idealNormSubgroup`.  This module identifies it with the
kernel of the arithmetic ideal Artin map, descends that map to the
corresponding quotient, and states the unramified decomposition law
entirely in terms of this norm-defined ideal group.
-/

@[expose] public section

open scoped NumberField IsMulCommutative

noncomputable
section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

attribute [local instance]
  ideleClassSubgroupNormal idealArtinKernelNormal

open scoped Classical in
/-- The kernel of the arithmetic, Galois-valued ideal Artin map is the
genuine norm-defined ideal group `N_{L/K} J_L^m P_K^m`. -/
theorem arithmeticIdealArtinGaloisMap_ker_eq_idealNormSubgroup
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    (arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm).ker =
      RayClass.idealNormSubgroup
        (K := K) (L := L) m := by
  rw [arithmeticIdealArtinGaloisMap_ker,
    idealArtinKernel_eq_idealNormSubgroup]

open scoped Classical in
/-- An ideal prime to `m` has trivial arithmetic Artin symbol exactly
when it belongs to `N_{L/K} J_L^m P_K^m`. -/
theorem arithmeticIdealArtinGaloisMap_eq_one_iff_mem_idealNormSubgroup
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    arithmeticIdealArtinGaloisMap
          (K := K) (L := L) m hm a =
        1 ↔
      a ∈ RayClass.idealNormSubgroup
        (K := K) (L := L) m := by
  change
    a ∈
        (arithmeticIdealArtinGaloisMap
          (K := K) (L := L) m hm).ker ↔
      a ∈ RayClass.idealNormSubgroup
        (K := K) (L := L) m
  rw [arithmeticIdealArtinGaloisMap_ker_eq_idealNormSubgroup]

open scoped Classical in
/-- Exactness of the arithmetic ideal Artin sequence with its kernel
written as the actual norm-defined ideal group. -/
theorem arithmeticIdealArtin_norm_exact
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    (arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm).ker =
        RayClass.idealNormSubgroup
          (K := K) (L := L) m ∧
      Function.Surjective
        (arithmeticIdealArtinGaloisMap
          (K := K) (L := L) m hm) :=
  ⟨arithmeticIdealArtinGaloisMap_ker_eq_idealNormSubgroup m hm,
    arithmeticIdealArtinGaloisMap_surjective m hm⟩

open scoped Classical in
/-- The vertical isomorphism in the ideal/idèle Artin diagram:

`J_K^m / (N_{L/K} J_L^{m_L} P_K^m) ≃ C_K / N_{L/K} C_L`.

It is the first-isomorphism-theorem comparison for the ideal Artin
map, transported across the equality between its kernel and the
genuine norm-defined ideal group. -/
noncomputable def idealNormQuotientEquivIdeleClassNormQuotient
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m ⧸
        RayClass.idealNormSubgroup
          (K := K) (L := L) m ≃*
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (idealArtinKernel_eq_idealNormSubgroup
        (K := K) (L := L) m hm).symm).trans
    (idealClassQuotientEquivNormQuotient m
      ((_root_.ideleClassNorm K L).range) hm)

omit [IsAbelianGalois K L] in
open scoped Classical in
/-- The ideal-norm quotient comparison sends an ideal representative to its
class in the idèle-class norm quotient. -/
theorem idealNormQuotientEquivIdeleClassNormQuotient_mk
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    idealNormQuotientEquivIdeleClassNormQuotient
        (K := K) (L := L) m hm
        (QuotientGroup.mk'
          (RayClass.idealNormSubgroup
            (K := K) (L := L) m) a) =
      idealArtinMap m
        ((_root_.ideleClassNorm K L).range) hm a := by
  let h :=
    (idealArtinKernel_eq_idealNormSubgroup
      (K := K) (L := L) m hm).symm
  change
    idealClassQuotientEquivNormQuotient m
        ((_root_.ideleClassNorm K L).range) hm
        (QuotientGroup.quotientMulEquivOfEq h
          (QuotientGroup.mk'
            (RayClass.idealNormSubgroup
              (K := K) (L := L) m) a)) =
      idealArtinMap m
        ((_root_.ideleClassNorm K L).range) hm a
  calc
    _ = idealClassQuotientEquivNormQuotient m
          ((_root_.ideleClassNorm K L).range) hm
          (QuotientGroup.mk'
            (idealArtinKernel m
              ((_root_.ideleClassNorm K L).range) hm) a) :=
      congrArg
        (idealClassQuotientEquivNormQuotient m
          ((_root_.ideleClassNorm K L).range) hm)
        (QuotientGroup.quotientMulEquivOfEq_mk h a)
    _ = idealArtinMap m
          ((_root_.ideleClassNorm K L).range) hm a :=
      idealClassQuotientEquivNormQuotient_mk m
        ((_root_.ideleClassNorm K L).range) hm a

open scoped Classical in
/-- The arithmetic ideal Artin map descended through the concrete
norm-defined ideal group. -/
noncomputable def arithmeticIdealNormQuotientArtinMap
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m ⧸
        RayClass.idealNormSubgroup
          (K := K) (L := L) m →*
      (L ≃ₐ[K] L) :=
  QuotientGroup.lift
    (RayClass.idealNormSubgroup
      (K := K) (L := L) m)
    (arithmeticIdealArtinGaloisMap
      (K := K) (L := L) m hm)
    (by
      intro a ha
      rw [arithmeticIdealArtinGaloisMap_ker_eq_idealNormSubgroup]
      exact ha)

open scoped Classical in
/-- The descended arithmetic ideal Artin map evaluates on quotient
representatives as the original arithmetic ideal Artin map. -/
theorem arithmeticIdealNormQuotientArtinMap_mk
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    arithmeticIdealNormQuotientArtinMap
        (K := K) (L := L) m hm
        (QuotientGroup.mk'
          (RayClass.idealNormSubgroup
            (K := K) (L := L) m) a) =
      arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm a :=
  QuotientGroup.lift_mk _ _ _

open scoped Classical in
/-- The arithmetic ideal Artin map on the concrete norm quotient is
injective. -/
theorem arithmeticIdealNormQuotientArtinMap_injective
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    Function.Injective
      (arithmeticIdealNormQuotientArtinMap
        (K := K) (L := L) m hm) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (RayClass.idealNormSubgroup
        (K := K) (L := L) m) x
  obtain ⟨b, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (RayClass.idealNormSubgroup
        (K := K) (L := L) m) y
  rw [arithmeticIdealNormQuotientArtinMap_mk,
    arithmeticIdealNormQuotientArtinMap_mk] at hxy
  apply
    (QuotientGroup.eq_iff_div_mem
      (N := RayClass.idealNormSubgroup
        (K := K) (L := L) m)
      (x := a) (y := b)).2
  rw [← arithmeticIdealArtinGaloisMap_ker_eq_idealNormSubgroup]
  change
    arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm (a / b) =
      1
  rw [map_div, hxy]
  exact div_self' _

open scoped Classical in
/-- The arithmetic ideal Artin map on the concrete norm quotient is
surjective. -/
theorem arithmeticIdealNormQuotientArtinMap_surjective
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    Function.Surjective
      (arithmeticIdealNormQuotientArtinMap
        (K := K) (L := L) m hm) := by
  intro σ
  obtain ⟨a, ha⟩ :=
    arithmeticIdealArtinGaloisMap_surjective
      (K := K) (L := L) m hm σ
  refine
    ⟨QuotientGroup.mk'
        (RayClass.idealNormSubgroup
          (K := K) (L := L) m) a, ?_⟩
  rw [arithmeticIdealNormQuotientArtinMap_mk]
  exact ha

open scoped Classical in
/-- The descended ideal Artin map is the arithmetic global
norm-residue map after the vertical ideal/idèle quotient
isomorphism.  This is the commutative square in the ideal-theoretic
Artin reciprocity theorem. -/
theorem arithmeticIdealNormQuotientArtinMap_eq_normResidue
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (q :
      RayClass.primeToModulusIdeals m ⧸
        RayClass.idealNormSubgroup
          (K := K) (L := L) m) :
    arithmeticIdealNormQuotientArtinMap
        (K := K) (L := L) m hm q =
      Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
        K L
        (idealNormQuotientEquivIdeleClassNormQuotient
          (K := K) (L := L) m hm q) := by
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (RayClass.idealNormSubgroup
        (K := K) (L := L) m) q
  rw [arithmeticIdealNormQuotientArtinMap_mk,
    idealNormQuotientEquivIdeleClassNormQuotient_mk]
  rfl

open scoped Classical in
/-- The canonical arithmetic ideal class-field isomorphism

`J_K^m / (N_{L/K} J_L^m P_K^m) ≃ Gal(L/K)`.

Both the source subgroup and the target Galois group are the concrete
objects occurring in the extension `L / K`. -/
noncomputable def arithmeticIdealNormQuotientEquivGaloisGroup
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m ⧸
        RayClass.idealNormSubgroup
          (K := K) (L := L) m ≃*
      (L ≃ₐ[K] L) :=
  MulEquiv.ofBijective
    (arithmeticIdealNormQuotientArtinMap
      (K := K) (L := L) m hm)
    ⟨arithmeticIdealNormQuotientArtinMap_injective m hm,
      arithmeticIdealNormQuotientArtinMap_surjective m hm⟩

open scoped Classical in
/-- The arithmetic ideal norm-quotient equivalence sends a quotient
representative to its arithmetic ideal Artin symbol. -/
theorem arithmeticIdealNormQuotientEquivGaloisGroup_mk
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    arithmeticIdealNormQuotientEquivGaloisGroup
        (K := K) (L := L) m hm
        (QuotientGroup.mk'
          (RayClass.idealNormSubgroup
            (K := K) (L := L) m) a) =
      arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm a :=
  arithmeticIdealNormQuotientArtinMap_mk m hm a

open scoped Classical in
/-- The canonical quotient equivalence makes the full arithmetic
ideal/idèle reciprocity diagram commute. -/
theorem arithmeticIdealNormQuotientEquivGaloisGroup_eq_normResidue
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (q :
      RayClass.primeToModulusIdeals m ⧸
        RayClass.idealNormSubgroup
          (K := K) (L := L) m) :
    arithmeticIdealNormQuotientEquivGaloisGroup
        (K := K) (L := L) m hm q =
      Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
        K L
        (idealNormQuotientEquivIdeleClassNormQuotient
          (K := K) (L := L) m hm q) :=
  arithmeticIdealNormQuotientArtinMap_eq_normResidue
    (K := K) (L := L) m hm q

open scoped Classical in
/-- For an unramified prime outside `m`, the order of its class modulo
the norm-defined ideal group is the common residue degree upstairs. -/
theorem
    orderOf_arithmeticIdealNormPrimeClass_eq_inertiaDegree_of_chosenUnramified
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support)
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    orderOf
        (QuotientGroup.mk'
          (RayClass.idealNormSubgroup
            (K := K) (L := L) m)
          (RayClass.primeToModulusIdeal m v hv)) =
      Ideal.inertiaDegIn v.asIdeal (𝓞 L) := by
  rw [← idealArtinKernel_eq_idealNormSubgroup
    (K := K) (L := L) m hm]
  exact
    orderOf_idealPrimeClass_eq_inertiaDegree_of_chosenUnramified
      (K := K) (L := L) m hm v hv hunram

open scoped Classical in
/-- A power of an unramified prime lies in the norm-defined ideal
group exactly when its common residue degree divides the exponent. -/
theorem
    unramifiedPrime_pow_mem_idealNormSubgroup_iff_inertiaDegree_dvd
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support)
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v)
    (n : ℕ) :
    (RayClass.primeToModulusIdeal m v hv) ^ n ∈
        RayClass.idealNormSubgroup
          (K := K) (L := L) m ↔
      Ideal.inertiaDegIn v.asIdeal (𝓞 L) ∣ n := by
  rw [← idealArtinKernel_eq_idealNormSubgroup
    (K := K) (L := L) m hm]
  exact
    unramifiedPrime_pow_mem_idealArtinKernel_iff_inertiaDegree_dvd
      (K := K) (L := L) m hm v hv hunram n

open scoped Classical in
/-- The full unramified decomposition law, with `f` defined as the
order of the prime class modulo the genuine norm-defined ideal group. -/
theorem unramifiedPrime_idealNormDecompositionLaw
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support)
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    let f :=
      orderOf
        (QuotientGroup.mk'
          (RayClass.idealNormSubgroup
            (K := K) (L := L) m)
          (RayClass.primeToModulusIdeal m v hv))
    Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal =
        ∏ P ∈ v.asIdeal.primesOver (𝓞 L), P ∧
      (∀ P : Ideal (𝓞 L),
        P ∈ v.asIdeal.primesOver (𝓞 L) →
          P.inertiaDeg (𝓞 K) = f) ∧
      (v.asIdeal.primesOver (𝓞 L)).ncard =
        Module.finrank K L / f := by
  rw [← idealArtinKernel_eq_idealNormSubgroup
    (K := K) (L := L) m hm]
  exact
    unramifiedPrime_idealDecompositionLaw
      (K := K) (L := L) m hm v hv hunram

open scoped Classical in
open GlobalClassFields renaming
  arithmeticFinitePlacePrimeArtin_eq_one_iff_splitsCompletely_of_chosenUnramified →
    primeArtin_eq_one_iff_splitsCompletely_of_unramified in
/-- An unramified prime outside `m` splits completely exactly when its
ideal class belongs to `N_{L/K} J_L^m P_K^m`. -/
theorem
    finitePlaceSplitsCompletely_iff_primeIdeal_mem_idealNormSubgroup
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support)
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    _root_.FinitePlaceSplitsCompletely
          (K := K) (L := L) v ↔
      RayClass.primeToModulusIdeal m v hv ∈
        RayClass.idealNormSubgroup
          (K := K) (L := L) m := by
  calc
    _root_.FinitePlaceSplitsCompletely
          (K := K) (L := L) v ↔
        GlobalClassFields.arithmeticFinitePlacePrimeArtin
            (K := K) (L := L) v =
          1 :=
      (primeArtin_eq_one_iff_splitsCompletely_of_unramified
          (K := K) (L := L) v hunram).symm
    _ ↔
        arithmeticIdealArtinGaloisMap
            (K := K) (L := L) m hm
            (RayClass.primeToModulusIdeal m v hv) =
          1 := by
      rw [
        arithmeticIdealArtinGaloisMap_primeIdeal_eq_arithmeticFinitePlacePrimeArtin]
    _ ↔
        RayClass.primeToModulusIdeal m v hv ∈
          RayClass.idealNormSubgroup
            (K := K) (L := L) m :=
      arithmeticIdealArtinGaloisMap_eq_one_iff_mem_idealNormSubgroup
        m hm (RayClass.primeToModulusIdeal m v hv)

end IdealClassFieldTheory
end GlobalClassFieldTheory

namespace ClassFieldTheory

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

open scoped Classical in
/-- The arithmetic ideal Artin kernel is the join of the genuine ideal-norm
image with the ray-principal ideal subgroup. -/
theorem arithmeticIdealArtin_ker_eq_norm_range_sup_ray_principal
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    (GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm).ker =
      (RayClass.primeToModulusIdealNorm
        (K := K) (L := L) m).range ⊔
        RayClass.principalRayIdealSubgroup m := by
  simpa only [RayClass.idealNormSubgroup] using
    (GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap_ker_eq_idealNormSubgroup
      (K := K) (L := L) m hm)

open scoped Classical in
/-- An ideal has trivial arithmetic Artin symbol precisely when it lies in
the group generated by ideal norms and ray-principal ideals. -/
theorem arithmeticIdealArtin_eq_one_iff_norm_range_sup_ray_principal
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap
          (K := K) (L := L) m hm a = 1 ↔
      a ∈ (RayClass.primeToModulusIdealNorm
        (K := K) (L := L) m).range ⊔
          RayClass.principalRayIdealSubgroup m := by
  change
    a ∈
        (GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap
          (K := K) (L := L) m hm).ker ↔
      a ∈ (RayClass.primeToModulusIdealNorm
        (K := K) (L := L) m).range ⊔
          RayClass.principalRayIdealSubgroup m
  rw [arithmeticIdealArtin_ker_eq_norm_range_sup_ray_principal]

end ClassFieldTheory
