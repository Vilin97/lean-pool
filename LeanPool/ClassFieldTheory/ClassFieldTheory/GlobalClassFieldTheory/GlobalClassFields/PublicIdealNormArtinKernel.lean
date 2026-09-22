/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.PrimeGeneration
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
/-!
# Ideal norms lie in the normalized Artin kernel

The forward inclusion of the ideal-theoretic norm-kernel formula follows
prime by prime.  The reverse inclusion needs a separate approximation
argument and is not asserted here.
-/

open scoped NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory.GlobalClassFieldComparison

open scoped Classical in
private theorem publicIdealNormDomain_eq_source
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

    (m : RayClassModulus K) :
    rayClassPrimeToIdealNormDomain K L m =
      RayClass.primeToModulusIdeals
        (RayClass.idealNormLiftedModulus (K := K) (L := L)
          (rayClassModulusToOriginal K m)) := by
  apply Subgroup.ext
  intro I
  change (∀ W, fractionalIdealNormPrimeBelow K L W ∈
      m.finitePart.support →
        FractionalIdeal.count L W
          (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = 0) ↔
    (∀ W, W ∈ (RayClass.idealNormLiftedModulus
      (K := K) (L := L) (rayClassModulusToOriginal K m)).finitePart.support →
        FractionalIdeal.count L W
          (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = 0)
  have hbelow (W : HeightOneSpectrum (𝓞 L)) :
      fractionalIdealNormPrimeBelow K L W =
        _root_.finitePlaceBelow (K := K) W := by
    ext
    rfl
  constructor
  · intro h W hW
    apply h W
    rw [hbelow]
    exact (RayClass.mem_idealNormLiftedModulus_support_iff
      (K := K) (L := L) (rayClassModulusToOriginal K m) W).mp hW
  · intro h W hW
    apply h W
    rw [RayClass.mem_idealNormLiftedModulus_support_iff, ← hbelow]
    exact hW

open scoped Classical in
private theorem fractionalIdealNorm_prime
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (W : HeightOneSpectrum (𝓞 L)) :
    fractionalIdealNorm K L (finitePrimeFractionalIdeal W) =
      finitePrimeFractionalIdeal (fractionalIdealNormPrimeBelow K L W) ^
        (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) := by
  apply NumberFieldFractionalIdealGroup.ext_count
  intro v
  rw [fractionalIdealNorm_count]
  have hcount : NumberFieldFractionalIdealGroup.countVector
      (finitePrimeFractionalIdeal W) = Finsupp.single W 1 := by
    ext V
    rw [NumberFieldFractionalIdealGroup.countVector_apply]
    change FractionalIdeal.count L V
      (W.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = _
    classical
    simp only [FractionalIdeal.count_maximal, Finsupp.single_apply]
  rw [hcount]
  change (Finsupp.single W (1 : ℤ)).sum
      (fun U n => if fractionalIdealNormPrimeBelow K L U = v then
        (U.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n else 0) =
      FractionalIdeal.count K v
        ((finitePrimeFractionalIdeal (fractionalIdealNormPrimeBelow K L W) ^
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) :
          NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  rw [Finsupp.sum_single_index]
  · rw [Units.val_zpow_eq_zpow_val, FractionalIdeal.count_zpow]
    change (if fractionalIdealNormPrimeBelow K L W = v then
      (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * 1 else 0) =
      (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
        FractionalIdeal.count K v
          ((fractionalIdealNormPrimeBelow K L W).asIdeal :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    classical
    rw [FractionalIdeal.count_maximal]
    split_ifs with h
    · simp only [mul_one]
    · simp only [mul_zero]
  · split_ifs <;> simp only [mul_zero]

open scoped Classical in
/-- Every ideal norm prime to a modulus is killed by the Frobenius-normalized
Artin map. This is the forward half of the ideal-theoretic norm-kernel
formula, with no idèle norm substituted for an ideal norm. -/
theorem idealNormImage_le_finiteAbelianReciprocityArtinKer
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    rayClassIdealNormImage K L D.modulus ≤ D.artin.ker := by
  let mL := RayClass.idealNormLiftedModulus (K := K) (L := L)
    (rayClassModulusToOriginal K D.modulus)
  have hdomain := publicIdealNormDomain_eq_source K L D.modulus
  let ι : RayClass.primeToModulusIdeals mL →*
      rayClassPrimeToIdealNormDomain K L D.modulus := by
    let h : RayClass.primeToModulusIdeals mL ≤
        rayClassPrimeToIdealNormDomain K L D.modulus := by
      rw [hdomain]
    exact Subgroup.inclusion h
  have hι : Function.Surjective ι := by
    intro I
    refine ⟨⟨I, ?_⟩, ?_⟩
    · rw [← hdomain]
      exact I.property
    · exact Subtype.ext rfl
  have hzero : D.artin.comp (rayClassIdealNorm K L D.modulus |>.comp ι) =
      1 := by
    apply RayClass.primeToModulusIdeals_hom_ext mL
    intro W hW
    let v := fractionalIdealNormPrimeBelow K L W
    have hv : v ∉ D.modulus.finitePart.support := by
      intro hv
      have hbelow : v = _root_.finitePlaceBelow (K := K) W := by
        ext
        rfl
      apply hW
      rw [RayClass.mem_idealNormLiftedModulus_support_iff, ← hbelow]
      exact hv
    have hw : W.asIdeal.LiesOver v.asIdeal := by
      change W.asIdeal.LiesOver (W.asIdeal.under (𝓞 K))
      infer_instance
    have hunram : Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal :=
      (D.unramifiedOutsideModulus.1 v hv) W.asIdeal inferInstance hw
    have horder := GlobalClassFieldComparison.orderOf_arithmeticFrobeniusAt_eq_inertiaDegree
      v W hw hunram
    change D.artin (rayClassIdealNorm K L D.modulus
      (ι (RayClass.primeToModulusIdeal mL W hW))) = 1
    have hprime : (ι (RayClass.primeToModulusIdeal mL W hW) :
        NumberFieldFractionalIdealGroup L) = finitePrimeFractionalIdeal W := rfl
    change D.artin (QuotientGroup.mk'
      (rayPrincipalIdealSubgroupInPrimeTo D.modulus)
      (rayClassPrimeToIdealNorm K L D.modulus
        (ι (RayClass.primeToModulusIdeal mL W hW)))) = 1
    have hnorm :
        (rayClassPrimeToIdealNorm K L D.modulus
          (ι (RayClass.primeToModulusIdeal mL W hW)) :
          NumberFieldFractionalIdealGroup K) =
        finitePrimeFractionalIdeal v ^
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) := by
      change fractionalIdealNorm K L
        (ι (RayClass.primeToModulusIdeal mL W hW) :
          NumberFieldFractionalIdealGroup L) = _
      rw [hprime]
      exact fractionalIdealNorm_prime K L W
    have hclass : QuotientGroup.mk'
        (rayPrincipalIdealSubgroupInPrimeTo D.modulus)
        (rayClassPrimeToIdealNorm K L D.modulus
          (ι (RayClass.primeToModulusIdeal mL W hW))) =
        rayClassOfFinitePrime D.modulus v hv ^
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) := by
      let p : rayClassPrimeToIdeals D.modulus :=
        ⟨finitePrimeFractionalIdeal v, by
          intro w hw
          exact FractionalIdeal.count_maximal_coprime K w
            (fun h => hv (h ▸ hw))⟩
      have hp : QuotientGroup.mk'
          (rayPrincipalIdealSubgroupInPrimeTo D.modulus) p =
          rayClassOfFinitePrime D.modulus v hv := rfl
      calc
        _ = QuotientGroup.mk'
              (rayPrincipalIdealSubgroupInPrimeTo D.modulus)
              (p ^ (W.asIdeal.inertiaDeg (𝓞 K) : ℤ)) := by
            congr 1
            apply Subtype.ext
            exact hnorm
        _ = (QuotientGroup.mk'
              (rayPrincipalIdealSubgroupInPrimeTo D.modulus) p) ^
              (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) :=
            map_zpow
              (QuotientGroup.mk'
                (rayPrincipalIdealSubgroupInPrimeTo D.modulus))
              p (W.asIdeal.inertiaDeg (𝓞 K) : ℤ)
        _ = _ := by rw [hp]
    rw [hclass, map_zpow, D.artin_frobenius v hv W hw]
    rw [← horder]
    simp only [zpow_natCast, pow_orderOf_eq_one]
  intro x hx
  obtain ⟨I, rfl⟩ := hx
  obtain ⟨J, hJ⟩ := hι I
  rw [← hJ]
  change D.artin ((rayClassIdealNorm K L D.modulus |>.comp ι) J) = 1
  exact DFunLike.congr_fun hzero J

end ClassFieldTheory.GlobalClassFieldComparison
