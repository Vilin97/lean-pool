/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Compositum
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalFieldTheory.Padic.Cyclotomic.Unramified.CanonicalExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.CyclotomicDegreeBound
/-!
# A p-primary ramification bound for p-adic cyclotomic fields

A cyclotomic field of order `r * p ^ n`, with `r` prime to `p`, splits into
an unramified prime-to-`p` branch and a `p`-power branch. This file records
that only the latter contributes to the local ramification index.
-/

noncomputable section

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open Polynomial

/-- If `r` is prime to `p`, the local ramification index of the cyclotomic
field of order `r * p ^ n` is controlled only by its `p`-power factor. -/
theorem coprimeLocalCyclotomic_exponentialRamificationIndex_le_totient_primePow
    (p r n : ℕ) [Fact p.Prime] (hpr : p.Coprime r) :
    let a := r
    let b := p ^ n
    let m := a * b
    letI : NeZero m := ⟨(mul_pos
      (Nat.pos_of_ne_zero (fun hr =>
        (Fact.out : Nat.Prime p).ne_one
          ((Nat.coprime_zero_right p).mp (hr ▸ hpr))))
      (pow_pos (Fact.out : Nat.Prime p).pos n)).ne'⟩
    let D := CyclotomicField m ℚ_[p]
    letI : IsCyclotomicExtension {m} ℚ_[p] D :=
      CyclotomicField.isCyclotomicExtension m ℚ_[p]
    letI : FiniteDimensional ℚ_[p] D :=
      IsCyclotomicExtension.finiteDimensional {m} ℚ_[p] D
    exponentialRamificationIndex
        (padicFieldExponentialValuation p)
      (padicFiniteExtensionExponentialValuation p D) ≤
      Nat.totient (p ^ n) := by
  dsimp only
  let a := r
  let b := p ^ n
  let m := a * b
  have ha : 0 < a := by
    exact Nat.pos_of_ne_zero (fun hr =>
      (Fact.out : Nat.Prime p).ne_one
        ((Nat.coprime_zero_right p).mp (hr ▸ hpr)))
  have hb : 0 < b := by
    exact pow_pos (Fact.out : Nat.Prime p).pos n
  have hm : 0 < m := mul_pos ha hb
  have hab : a.Coprime b := by
    dsimp [a, b]
    exact (hpr.pow_left n).symm
  let : NeZero a := ⟨ha.ne'⟩
  let : NeZero b := ⟨hb.ne'⟩
  let : NeZero m := ⟨hm.ne'⟩
  let D := CyclotomicField m ℚ_[p]
  let hDcyclo : IsCyclotomicExtension {m} ℚ_[p] D :=
    CyclotomicField.isCyclotomicExtension m ℚ_[p]
  let : FiniteDimensional ℚ_[p] D :=
    IsCyclotomicExtension.finiteDimensional {m} ℚ_[p] D
  obtain ⟨ζ, hζ⟩ := hDcyclo.exists_isPrimitiveRoot (Set.mem_singleton m) hm.ne'
  have hζa : IsPrimitiveRoot (ζ ^ b) a :=
    hζ.pow (NeZero.pos _) (a := b) (b := a) (by simp [m, mul_comm])
  have hζb : IsPrimitiveRoot (ζ ^ a) b :=
    hζ.pow (NeZero.pos _) (a := a) (b := b) (by simp [m])
  let U : IntermediateField ℚ_[p] D :=
    IntermediateField.adjoin ℚ_[p] {ζ ^ b}
  let C : IntermediateField ℚ_[p] D :=
    IntermediateField.adjoin ℚ_[p] {ζ ^ a}
  let hUcyclo : IsCyclotomicExtension {a} ℚ_[p] U := by
    simpa [U] using hζa.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]
  let hCcyclo : IsCyclotomicExtension {b} ℚ_[p] C := by
    simpa [C] using hζb.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]
  let : FiniteDimensional ℚ_[p] U :=
    IsCyclotomicExtension.finiteDimensional {a} ℚ_[p] U
  let : FiniteDimensional ℚ_[p] C :=
    IsCyclotomicExtension.finiteDimensional {b} ℚ_[p] C
  let algUD : Algebra U D := U.val.toRingHom.toAlgebra
  let : Algebra U D := algUD
  let : SMul U D := algUD.toSMul
  let : Module U D := algUD.toModule
  let : IsScalarTower ℚ_[p] U D := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional U D := FiniteDimensional.right ℚ_[p] U D
  let hTopCyclo : IsCyclotomicExtension {m} ℚ_[p]
      (⊤ : IntermediateField ℚ_[p] D) :=
    IsCyclotomicExtension.equiv {m} ℚ_[p] D IntermediateField.topEquiv.symm
  let hSupCyclo : IsCyclotomicExtension {m} ℚ_[p]
      (U ⊔ C : IntermediateField ℚ_[p] D) := by
    have h := IntermediateField.isCyclotomicExtension_lcm_sup
      ℚ_[p] D a b U C
    simpa [m, hab.lcm_eq_mul] using h
  have hTop : U ⊔ C = (⊤ : IntermediateField ℚ_[p] D) :=
    IntermediateField.isCyclotomicExtension_eq {m} ℚ_[p] D _ _
  let algUSup : Algebra U (U ⊔ C : IntermediateField ℚ_[p] D) :=
    (IntermediateField.inclusion (show U ≤ U ⊔ C from le_sup_left)).toRingHom.toAlgebra
  let : Algebra U (U ⊔ C : IntermediateField ℚ_[p] D) := algUSup
  let : SMul U (U ⊔ C : IntermediateField ℚ_[p] D) := algUSup.toSMul
  let : Module U (U ⊔ C : IntermediateField ℚ_[p] D) := algUSup.toModule
  let : IsScalarTower ℚ_[p] U
      (U ⊔ C : IntermediateField ℚ_[p] D) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional ℚ_[p]
      (U ⊔ C : IntermediateField ℚ_[p] D) :=
    IntermediateField.finiteDimensional_sup U C
  let : FiniteDimensional U
      (U ⊔ C : IntermediateField ℚ_[p] D) :=
    FiniteDimensional.right ℚ_[p] U (U ⊔ C : IntermediateField ℚ_[p] D)
  have hDegreeUD : Module.finrank U D ≤ Module.finrank ℚ_[p] C := by
    let eTop : (U ⊔ C : IntermediateField ℚ_[p] D) ≃+* D :=
      ((IntermediateField.equivOfEq hTop).trans
        IntermediateField.topEquiv).toRingEquiv
    have htransport :
        Module.finrank U (U ⊔ C : IntermediateField ℚ_[p] D) =
          Module.finrank U D := by
      apply Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl U) eTop
      ext x
      rfl
    calc
      Module.finrank U D =
          Module.finrank U (U ⊔ C : IntermediateField ℚ_[p] D) :=
        htransport.symm
      _ ≤ Module.finrank ℚ_[p] C :=
        DiscreteValuationField.FieldCompositum.sup_finrank_over_left_le_right U C
  let eC : C ≃ₐ[ℚ_[p]] CyclotomicField b ℚ_[p] :=
    IsCyclotomicExtension.algEquiv {b} ℚ_[p] C (CyclotomicField b ℚ_[p])
  have hDegreeC : Module.finrank ℚ_[p] C ≤ Nat.totient b := by
    calc
      Module.finrank ℚ_[p] C =
          Module.finrank ℚ_[p] (CyclotomicField b ℚ_[p]) :=
        eC.toLinearEquiv.finrank_eq
      _ ≤ Nat.totient b := cyclotomicField_finrank_le_totient ℚ_[p] b hb
  let v := padicFieldExponentialValuation p
  let u := padicFiniteExtensionExponentialValuation p U
  let w := padicFiniteExtensionExponentialValuation p D
  have hQU : ∀ x : ℚ_[p], u (algebraMap ℚ_[p] U x) = v x :=
    padicFiniteExtensionExponentialValuation_extends p U
  have hUD : ∀ x : U, w (algebraMap U D x) = u x := by
    intro x
    exact padicFiniteExtensionExponentialValuation_algHom p U.val x
  let ζU : U :=
    ⟨ζ ^ b, IntermediateField.subset_adjoin
      (F := ℚ_[p]) (S := {ζ ^ b}) (Set.mem_singleton (ζ ^ b))⟩
  have hζU : IsPrimitiveRoot ζU a :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp hζa
  have hUgen : Algebra.adjoin ℚ_[p] ({ζU} : Set U) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζU
  have hUunramified : FiniteUnramifiedExtension v u hQU := by
    exact padicCyclotomic_finiteUnramified_of_coprime
      p r hpr hζU hUgen
  have hUram : exponentialRamificationIndex v u = 1 :=
    exponentialRamificationIndex_eq_one_of_finiteUnramifiedExtension
      v u hQU hUunramified
  have hTower := exponentialRamificationIndex_mul_in_tower v u w hQU hUD
  have hRamEq : exponentialRamificationIndex v w = exponentialRamificationIndex u w := by
    calc
      exponentialRamificationIndex v w =
          exponentialRamificationIndex v u * exponentialRamificationIndex u w := hTower.symm
      _ = exponentialRamificationIndex u w := by rw [hUram, one_mul]
  have hRamDegree : exponentialRamificationIndex v w ≤ Module.finrank U D := by
    rw [hRamEq]
    exact exponentialRamificationIndex_le_finrank u w hUD
  simpa [a, b, m, D, v, w] using
    hRamDegree.trans (hDegreeUD.trans hDegreeC)

end HilbertRamification

end
