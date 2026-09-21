/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FinitePlaceTensorNormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.ExtendingAbsoluteValue
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayFrobeniusRigidity
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
/-!
# Ray Artin values at a finite place

The canonical one-place map into an ideal-theoretic ray class group has the
actual local norm subgroup as its Artin kernel. Its Artin values preserve
the absolute-value class of one extension of that place to the top field,
including when the place divides the ray modulus.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- A Frobenius-normalized ray Artin map restricts at every finite place to
the local norm quotient and lands in a decomposition group. The extension
absolute value and the local-to-ray map are chosen independently of `D`'s
Artin values. -/
theorem exists_finitePlaceRayArtin_decomposition
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ (w : ExtendingAbsoluteValue
        (NumberField.HeightOneSpectrum.adicAbv K v) L)
      (ι : (v.adicCompletion K)ˣ →* RayClassGroup D.modulus),
      (D.artin.comp ι).ker = finitePlaceTensorNormSubgroup K L v ∧
      ∀ (x : (v.adicCompletion K)ˣ) (y : L),
        w.1 ((D.artin (ι x)) y) < 1 ↔ w.1 y < 1 := by
  classical
  let m := GlobalClassFieldComparison.rayClassModulusToOriginal K D.modulus
  let e := GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K D.modulus
  let a : RayClass.RayClassGroup m →* (L ≃ₐ[K] L) :=
    D.artin.comp e.symm.toMonoidHom
  have hprime :
      ∀ (p : HeightOneSpectrum (𝓞 K))
        (_hp : p ∉ m.finitePart.support),
        a (QuotientGroup.mk' m.congruenceSubgroup
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (IdeleGroup.finitePrimeIdele p))) =
          GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
            (K := K) (L := L) p := by
    intro p hp
    have hpD : p ∉ D.modulus.finitePart.support := hp
    change D.artin (e.symm (QuotientGroup.mk' m.congruenceSubgroup
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
        (IdeleGroup.finitePrimeIdele p)))) = _
    rw [← GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime
      K D.modulus p hpD]
    have hFrob :
        D.artin (rayClassOfFinitePrime D.modulus p hpD) =
          GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
            (K := K) (L := L) p := by
      let w₀ := _root_.chosenFinitePlaceExtension (L := L) p
      let w := _root_.finitePlaceExtensionCentre (K := K) (L := L) p w₀
      have hw : w.asIdeal.LiesOver p.asIdeal :=
        _root_.finitePlaceExtensionCentre_liesOver
          (K := K) (L := L) p w₀
      have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
        (D.unramifiedOutsideModulus.1 p hpD) w.asIdeal inferInstance hw
      calc
        D.artin (rayClassOfFinitePrime D.modulus p hpD) =
            arithmeticFrobeniusAt (K := K) w :=
          D.artin_frobenius p hpD w hw
        _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
              (K := K) (L := L) p :=
          (GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
            (K := K) (L := L) p w hw hunram).symm
    simpa only [e, MulEquiv.symm_apply_apply] using hFrob
  let w : ExtendingAbsoluteValue
      (NumberField.HeightOneSpectrum.adicAbv K v) L :=
    _root_.chosenFinitePlaceExtension (L := L) v
  let ι : (v.adicCompletion K)ˣ →* RayClassGroup D.modulus :=
    e.symm.toMonoidHom.comp
      ((QuotientGroup.mk' m.congruenceSubgroup).comp
        (IdeleGroup.finitePlaceIdeleClass v))
  have hvalue (x : (v.adicCompletion K)ˣ) :
      D.artin (ι x) =
        GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
          K L v x := by
    calc
      D.artin (ι x) =
          GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom
            K L (IdeleGroup.finitePlaceIdeleClass v x) :=
        GlobalClassFieldTheory.GlobalClassFields.rayArtin_comp_ideleClass_eq_arithmeticGlobalNormResidue
          m a hprime (IdeleGroup.finitePlaceIdeleClass v x)
      _ = GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
            K L v x := by
        exact DFunLike.congr_fun
          (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
            (K := K) (L := L) v) x
  refine ⟨w, ι, ?_, ?_⟩
  · ext x
    change D.artin (ι x) = 1 ↔
      x ∈ finitePlaceTensorNormSubgroup K L v
    rw [hvalue x,
      GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply,
      inv_eq_one,
      GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm,
      ← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
        (K := K) (L := L) v]
    rfl
  · intro x y
    rw [hvalue x,
      GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply]
    have hgeo :
        GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v x ∈
          HilbertRamification.absoluteValueDecompositionGroup K w.1 := by
      change GlobalClassFieldTheory.Reciprocity.finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w x ∈ _
      rw [GlobalClassFieldTheory.Reciprocity.finitePlaceArtinMonoidHomOfExtension_factor,
        MonoidHom.comp_apply]
      change ((HilbertRamification.absoluteValueDecompositionGroup K w.1).subtype
        _) ∈ _
      exact Subtype.property _
    have hinv :=
      (HilbertRamification.absoluteValueDecompositionGroup K w.1).inv_mem hgeo
    exact hinv y

end ClassFieldTheory
