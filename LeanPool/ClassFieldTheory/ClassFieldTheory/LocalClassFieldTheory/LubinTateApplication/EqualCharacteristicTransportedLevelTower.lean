/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicTransportedUpperRamification
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
/-!
# Towers of transported equal-characteristic Lubin--Tate levels

The explicit level fields form a tower inside the Laurent separable closure.
After transporting their base algebra to the target local field, the same
inclusions are target-field linear.  This file packages the resulting
restriction homomorphism and its compatibility with the unchanged
underlying Galois automorphisms.
-/

noncomputable section

open scoped LaurentSeries ValuativeRel

namespace LubinTate

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate.EqualCharacteristic
open RamificationTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Restriction between two transported Lubin--Tate levels, viewed as
extensions of the target equal-characteristic local field. -/
noncomputable def
    equalCharacteristicTransportedLubinTateRestrictNormalHom
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    {m n : ℕ} (hmn : m ≤ n) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    let L := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F m
    letI : Algebra B L :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ m
    letI : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    Gal(L/K) →* Gal(E/K) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  letI hKq : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let L := equalCharacteristicLubinTateLevelField F n
  letI : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F m
  letI : Algebra B L :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let hEL : E ≤ L :=
    equalCharacteristicLubinTateLevelField_mono F hmn
  letI : IsGalois B E :=
    equalCharacteristicLubinTateLevelField_isGalois F m
  let restrictB :=
    intermediateFieldRestrictNormalHom E L hEL
  letI : CharP K p := hKp
  letI : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ m
  letI : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  exact
    (equalCharacteristicTransportedLubinTateGaloisEquiv
        K p ϖ hϖ m).toMonoidHom.comp
      (restrictB.comp
        (equalCharacteristicTransportedLubinTateGaloisEquiv
          K p ϖ hϖ n).symm.toMonoidHom)

/-- Evaluation of transported restriction agrees in the common Laurent
separable closure with restricting the underlying automorphism. -/
theorem
    equalCharacteristicTransportedLubinTateRestrictNormalHom_apply_val
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    {m n : ℕ} (hmn : m ≤ n)
    (σ :
      let F := equalCharacteristicTargetLocalField K
      letI : CharP K F.residueCharacteristic :=
        equalCharacteristicTargetResidueCharacteristicCharP K p
      let L := equalCharacteristicLubinTateLevelField F n
      letI : CharP K p := hKp
      letI : Algebra K L :=
        equalCharacteristicTransportedLubinTateLevelAlgebra
          K p ϖ hϖ n
      Gal(L/K))
    (x :
      let F := equalCharacteristicTargetLocalField K
      letI : CharP K F.residueCharacteristic :=
        equalCharacteristicTargetResidueCharacteristicCharP K p
      equalCharacteristicLubinTateLevelField F m) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    let L := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F m
    letI : Algebra B L :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ m
    letI : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let hEL : E ≤ L :=
      equalCharacteristicLubinTateLevelField_mono F hmn
    letI : CharP K p := hKp
    E.val
        (equalCharacteristicTransportedLubinTateRestrictNormalHom
          K p ϖ hϖ hmn σ x) =
      L.val (σ (IntermediateField.inclusion hEL x)) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let hKq : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let L := equalCharacteristicLubinTateLevelField F n
  let : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F m
  let : Algebra B L :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let hEL : E ≤ L :=
    equalCharacteristicLubinTateLevelField_mono F hmn
  let : IsGalois B E :=
    equalCharacteristicLubinTateLevelField_isGalois F m
  let restrictB :=
    intermediateFieldRestrictNormalHom E L hEL
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ m
  let : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  let qE :=
    equalCharacteristicTransportedLubinTateGaloisEquiv
      K p ϖ hϖ m
  let qL :=
    equalCharacteristicTransportedLubinTateGaloisEquiv
      K p ϖ hϖ n
  have hrestrict :
      E.val (restrictB (qL.symm σ) x) =
        L.val (qL.symm σ (IntermediateField.inclusion hEL x)) :=
    intermediateFieldRestrictNormalHom_apply_val
      E L hEL (qL.symm σ) x
  have hqL :
      L.val (qL.symm σ (IntermediateField.inclusion hEL x)) =
        L.val (σ (IntermediateField.inclusion hEL x)) := by
    have h :=
      congrArg
        (fun τ : Gal(L/K) =>
          L.val (τ (IntermediateField.inclusion hEL x)))
        (qL.apply_symm_apply σ)
    rw [equalCharacteristicTransportedLubinTateGaloisEquiv_apply] at h
    exact h
  change E.val (qE (restrictB (qL.symm σ)) x) =
    L.val (σ (IntermediateField.inclusion hEL x))
  rw [equalCharacteristicTransportedLubinTateGaloisEquiv_apply]
  exact hrestrict.trans hqL

/-- The Galois-group identifications at two levels commute with restriction
between those levels. -/
theorem
    equalCharacteristicTransportedLubinTateGaloisEquiv_restrict
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    {m n : ℕ} (hmn : m ≤ n)
    (σ :
      let F := equalCharacteristicTargetLocalField K
      let B := F.residueField⸨X⸩
      letI : CharP K F.residueCharacteristic :=
        equalCharacteristicTargetResidueCharacteristicCharP K p
      let L := equalCharacteristicLubinTateLevelField F n
      letI : Algebra B L :=
        equalCharacteristicLubinTateLevelAlgebra F n
      Gal(L/B)) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    let L := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F m
    letI : Algebra B L :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ m
    letI : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let hEL : E ≤ L :=
      equalCharacteristicLubinTateLevelField_mono F hmn
    letI : CharP K p := hKp
    equalCharacteristicTransportedLubinTateRestrictNormalHom
        K p ϖ hϖ hmn
        (equalCharacteristicTransportedLubinTateGaloisEquiv
          K p ϖ hϖ n σ) =
      equalCharacteristicTransportedLubinTateGaloisEquiv
        K p ϖ hϖ m
        (intermediateFieldRestrictNormalHom E L hEL σ) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let hKq : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let L := equalCharacteristicLubinTateLevelField F n
  let : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F m
  let : Algebra B L :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let hEL : E ≤ L :=
    equalCharacteristicLubinTateLevelField_mono F hmn
  let : IsGalois B E :=
    equalCharacteristicLubinTateLevelField_isGalois F m
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ m
  let : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  apply AlgEquiv.ext
  intro x
  apply E.val.injective
  calc
    E.val
        (equalCharacteristicTransportedLubinTateRestrictNormalHom
          K p ϖ hϖ hmn
          (equalCharacteristicTransportedLubinTateGaloisEquiv
            K p ϖ hϖ n σ) x) =
        L.val
          (equalCharacteristicTransportedLubinTateGaloisEquiv
            K p ϖ hϖ n σ
            (IntermediateField.inclusion hEL x)) :=
      equalCharacteristicTransportedLubinTateRestrictNormalHom_apply_val
        K p ϖ hϖ hmn _ x
    _ = L.val (σ (IntermediateField.inclusion hEL x)) := by
      rw [equalCharacteristicTransportedLubinTateGaloisEquiv_apply]
    _ =
        E.val
          (intermediateFieldRestrictNormalHom E L hEL σ x) :=
      (intermediateFieldRestrictNormalHom_apply_val
        E L hEL σ x).symm
    _ =
        E.val
          (equalCharacteristicTransportedLubinTateGaloisEquiv
            K p ϖ hϖ m
            (intermediateFieldRestrictNormalHom E L hEL σ) x) := by
      rw [equalCharacteristicTransportedLubinTateGaloisEquiv_apply]

end LubinTate
