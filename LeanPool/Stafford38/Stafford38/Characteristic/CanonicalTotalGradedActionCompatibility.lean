/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTotalGradedBridge
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTangentialTotalAction
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTangentialRingEquivalence

namespace Stafford38.Characteristic.CanonicalTotalGradedActionCompatibility

open Stafford38.Characteristic
open Stafford38.Characteristic.FilteredTwoTermPages
open Stafford38.Characteristic.CanonicalFilteredTwoTerm
open Stafford38.Characteristic.CanonicalFilteredGradedBridge
open Stafford38.Characteristic.CanonicalTotalGradedBridge
open Stafford38.Characteristic.CanonicalTangentialPageOperators
open Stafford38.Characteristic.CanonicalTangentialTotalAction
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientGraded
open Stafford38.EulerSurjectivity
open Stafford38.WeylFiltration
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylPBW
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylQuotientTransport
open Stafford38.WeylSymplectic
open Stafford38.CanonicalAxisAvoidanceConsumer

noncomputable section

universe u
variable (k : Type u) [Field k] [Algebra ℚ k]

private abbrev CI (n N : ℕ) (d : PresentedWeyl k (n + 1)) :=
  presentedCanonicalRightIdeal (k := k) n N d

private abbrev K (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :=
  canonicalFilteredTwoTerm k n N d hd

def oldGeneratorOrderPiece (n : ℕ) (i : Fin n ⊕ Fin n) :
    orderPiece k (n + 1) (tangentialDegree i) := by
  refine ⟨oldGenerator k n i, ?_⟩
  cases i with
  | inl i =>
      rw [oldGenerator, orderPiece, mem_presentedWeightPiece,
        presentedNormalFormLinearEquiv_generator]
      intro m hm
      simp only [MvPolynomial.coeff_X'] at hm
      split at hm
      · subst m; simp [oldIndex, monomialWeight, orderWeight, fibreWeight,
          tangentialDegree]
      · contradiction
  | inr i =>
      rw [oldGenerator, orderPiece, mem_presentedWeightPiece,
        presentedNormalFormLinearEquiv_generator]
      intro m hm
      simp only [MvPolynomial.coeff_X'] at hm
      split at hm
      · subst m; simp [oldIndex, monomialWeight, orderWeight, fibreWeight,
          tangentialDegree]
      · contradiction

theorem principal_oldGenerator (n : ℕ) (i : Fin n ⊕ Fin n) :
    (principalComponentOnPiece k (@orderWeight (n + 1)) (tangentialDegree i)
      (oldGeneratorOrderPiece k n i) : SymbolRing k (n + 1)) =
      MvPolynomial.X (oldIndex i) := by
  cases i
  · change MvPolynomial.weightedHomogeneousComponent orderWeight 0
        (presentedNormalFormLinearEquiv k (n + 1)
          (Stafford.freeWeylGenerator (standardForm k (n + 1)) (.inl _))) = _
    rw [presentedNormalFormLinearEquiv_generator]
    change MvPolynomial.weightedHomogeneousComponent orderWeight 0
      (MvPolynomial.monomial (Finsupp.single (Sum.inl _) 1) 1) = _
    rw [weightedHomogeneousComponent_monomial]
    simp [monomialWeight, orderWeight, fibreWeight, oldIndex]
    rw [MvPolynomial.monomial_eq]
    simp

  · change MvPolynomial.weightedHomogeneousComponent orderWeight 1
        (presentedNormalFormLinearEquiv k (n + 1)
          (Stafford.freeWeylGenerator (standardForm k (n + 1)) (.inr _))) = _
    rw [presentedNormalFormLinearEquiv_generator]
    change MvPolynomial.weightedHomogeneousComponent orderWeight 1
      (MvPolynomial.monomial (Finsupp.single (Sum.inr _) 1) 1) = _
    rw [weightedHomogeneousComponent_monomial]
    simp [monomialWeight, orderWeight, fibreWeight, oldIndex]
    rw [MvPolynomial.monomial_eq]
    simp

def sourceRepresentative (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (p : ℤ) (m : ℕ) (h : p = -(m : ℤ)) (a : orderPiece k (n + 1) m) :
    (K k n N d hd).SourcePage 0 p :=
  Submodule.Quotient.mk ⟨Submodule.Quotient.mk (a : PresentedWeyl k (n + 1)), by
    rw [h, zeroPage_source_cycles_eq_orderPiece k n N m d hd]
    exact ⟨a, a.property, rfl⟩⟩

def targetRepresentative (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (p : ℤ) (m : ℕ) (h : p = -(m : ℤ)) (a : orderPiece k (n + 1) m) :
    (K k n N d hd).TargetPage 0 p :=
  Submodule.Quotient.mk ⟨Submodule.Quotient.mk (a : PresentedWeyl k (n + 1)), by
    rw [h, G_at_neg k n N m d hd]
    exact ⟨a, a.property, rfl⟩⟩

private theorem sourceRepresentative_cast (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    {p q : ℤ} (m : ℕ) (hp : p = -(m : ℤ)) (hq : q = -(m : ℤ))
    (h : p = q) (a : orderPiece k (n + 1) m) :
    LinearEquiv.cast (R := k) (M := fun p => (K k n N d hd).SourcePage 0 p) h
      (sourceRepresentative k n N d hd p m hp a) =
      sourceRepresentative k n N d hd q m hq a := by
  cases h
  rfl

private theorem targetRepresentative_cast (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    {p q : ℤ} (m : ℕ) (hp : p = -(m : ℤ)) (hq : q = -(m : ℤ))
    (h : p = q) (a : orderPiece k (n + 1) m) :
    LinearEquiv.cast (R := k) (M := fun p => (K k n N d hd).TargetPage 0 p) h
      (targetRepresentative k n N d hd p m hp a) =
      targetRepresentative k n N d hd q m hq a := by
  cases h
  rfl

private theorem sourceRepresentative_lof_eq (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    {p q : ℤ} (m : ℕ) (hp : p = -(m : ℤ)) (hq : q = -(m : ℤ))
    (a : orderPiece k (n + 1) m) :
    DirectSum.lof k ℤ _ p (sourceRepresentative k n N d hd p m hp a) =
      DirectSum.lof k ℤ _ q (sourceRepresentative k n N d hd q m hq a) := by
  have h : p = q := hp.trans hq.symm
  cases h
  rfl

private theorem targetRepresentative_lof_eq (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    {p q : ℤ} (m : ℕ) (hp : p = -(m : ℤ)) (hq : q = -(m : ℤ))
    (a : orderPiece k (n + 1) m) :
    DirectSum.lof k ℤ _ p (targetRepresentative k n N d hd p m hp a) =
      DirectSum.lof k ℤ _ q (targetRepresentative k n N d hd q m hq a) := by
  have h : p = q := hp.trans hq.symm
  cases h
  rfl

theorem sourceEquiv_representative (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (p : ℤ) (m : ℕ) (h : p = -(m : ℤ)) (a : orderPiece k (n + 1) m) :
    sourceTotal0LinearEquivOrderAssociatedGraded k n N d hd
      (DirectSum.lof k ℤ (fun p => (K k n N d hd).SourcePage 0 p) p
        (sourceRepresentative k n N d hd p m h a)) =
      orderAssociatedGradedOf k (CI k n N d) m
        (orderPieceToQuotientGraded k (CI k n N d) m a) := by
  rw [sourceRepresentative_lof_eq k n N d hd m h (negIndex_eq m) a]
  have H := sourceTotal0LinearEquiv_lof_negIndex k n N m d hd
    (sourceRepresentative k n N d hd (negIndex m) m (negIndex_eq m) a)
  rw [H, LinearEquiv.trans_apply, sourceRepresentative_cast]
  congr 1
  simp [zeroPageSourceLinearEquivOrderGradedPiece, sourceRepresentative,
    orderPieceToQuotientGraded, orderPieceToQuotientPiece]

theorem targetEquiv_representative (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (p : ℤ) (m : ℕ) (h : p = -(m : ℤ)) (a : orderPiece k (n + 1) m) :
    targetTotal0LinearEquivOrderAssociatedGraded k n N d hd
      (DirectSum.lof k ℤ (fun p => (K k n N d hd).TargetPage 0 p) p
        (targetRepresentative k n N d hd p m h a)) =
      orderAssociatedGradedOf k (CI k n N d) m
        (orderPieceToQuotientGraded k (CI k n N d) m a) := by
  rw [targetRepresentative_lof_eq k n N d hd m h (negIndex_eq m) a]
  have H := targetTotal0LinearEquiv_lof_negIndex k n N m d hd
    (targetRepresentative k n N d hd (negIndex m) m (negIndex_eq m) a)
  rw [H, LinearEquiv.trans_apply, targetRepresentative_cast]
  congr 1
  simp [zeroPageTargetLinearEquivOrderGradedPiece, targetRepresentative,
    orderPieceToQuotientGraded, orderPieceToQuotientPiece]
theorem sourceRepresentative_surjective (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (p : ℤ) (m : ℕ) (h : p = -(m : ℤ)) :
    Function.Surjective (sourceRepresentative k n N d hd p m h) := by
  subst p
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    have hy := (le_of_eq (zeroPage_source_cycles_eq_orderPiece k n N m d hd)) y.property
    obtain ⟨a, ha, hay⟩ := hy
    refine ⟨⟨a, ha⟩, ?_⟩
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact hay

theorem targetRepresentative_surjective (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (p : ℤ) (m : ℕ) (h : p = -(m : ℤ)) :
    Function.Surjective (targetRepresentative k n N d hd p m h) := by
  subst p
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    have hy := (le_of_eq (G_at_neg k n N m d hd)) y.property
    obtain ⟨a, ha, hay⟩ := hy
    refine ⟨⟨a, ha⟩, ?_⟩
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact hay

theorem sourceRepresentative_map (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (e : ℕ) (a : orderPiece k (n + 1) e)
    (P : (K k n N d hd).PageOperator (e : ℤ))
    (hP : P.g = rightMulLinearMap k (CI k n N d) a)
    (p : ℤ) (m : ℕ) (h : p = -(m : ℤ)) (z : orderPiece k (n + 1) m) :
    P.sourceMap 0 p (sourceRepresentative k n N d hd p m h z) =
      sourceRepresentative k n N d hd (p - e) (m + e) (by omega)
        ⟨(z : PresentedWeyl k (n + 1)) * a,
          mul_mem_orderPiece k z.property a.property⟩ := by
  rw [sourceRepresentative, P.sourceMap_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  change P.g (Submodule.Quotient.mk (z : PresentedWeyl k (n + 1))) = _
  rw [hP, rightMulLinearMap_mk]

theorem targetRepresentative_map (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (e : ℕ) (a : orderPiece k (n + 1) e)
    (P : (K k n N d hd).PageOperator (e : ℤ))
    (hP : P.g = rightMulLinearMap k (CI k n N d) a)
    (p : ℤ) (m : ℕ) (h : p = -(m : ℤ)) (z : orderPiece k (n + 1) m) :
    P.targetMap 0 p (targetRepresentative k n N d hd p m h z) =
      targetRepresentative k n N d hd (p - e) (m + e) (by omega)
        ⟨(z : PresentedWeyl k (n + 1)) * a,
          mul_mem_orderPiece k z.property a.property⟩ := by
  rw [targetRepresentative, P.targetMap_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  change P.g (Submodule.Quotient.mk (z : PresentedWeyl k (n + 1))) = _
  rw [hP, rightMulLinearMap_mk]

theorem sourceEquiv_intertwines_rightMul (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (e : ℕ) (a : orderPiece k (n + 1) e)
    (P : (K k n N d hd).PageOperator (e : ℤ))
    (hP : P.g = rightMulLinearMap k (CI k n N d) a)
    (z : (K k n N d hd).SourceTotal 0) :
    sourceTotal0LinearEquivOrderAssociatedGraded k n N d hd (P.sourceTotalMap 0 z) =
      (principalComponentOnPiece k (@orderWeight (n + 1)) e a : SymbolRing k (n + 1)) •
        sourceTotal0LinearEquivOrderAssociatedGraded k n N d hd z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    by_cases hp : 0 < p
    · have := zeroPage_source_subsingleton_of_pos k n N p d hd hp
      simp [Subsingleton.elim y 0]
    · let m := (-p).toNat
      have hm : p = -(m : ℤ) := by dsimp [m]; omega
      obtain ⟨z, rfl⟩ := sourceRepresentative_surjective k n N d hd p m hm y
      rw [show DirectSum.of ((K k n N d hd).SourcePage 0) p =
        (DirectSum.lof k ℤ (fun p => (K k n N d hd).SourcePage 0 p) p).toAddMonoidHom from rfl]
      simp only [LinearMap.toAddMonoidHom_coe]
      change sourceTotal0LinearEquivOrderAssociatedGraded k n N d hd
        (P.sourceTotalMap 0 (DirectSum.lof k ℤ _ p
          (sourceRepresentative k n N d hd p m hm z))) = _
      rw [P.sourceTotalMap_lof,
        sourceRepresentative_map k n N d hd e a P hP,
        sourceEquiv_representative, sourceEquiv_representative,
        smul_orderAssociatedGradedOf_mk_eq_of_mul]
  | add x y hx hy => simpa [smul_add] using congrArg₂ (· + ·) hx hy

theorem targetEquiv_intertwines_rightMul (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (e : ℕ) (a : orderPiece k (n + 1) e)
    (P : (K k n N d hd).PageOperator (e : ℤ))
    (hP : P.g = rightMulLinearMap k (CI k n N d) a)
    (z : (K k n N d hd).TargetTotal 0) :
    targetTotal0LinearEquivOrderAssociatedGraded k n N d hd (P.targetTotalMap 0 z) =
      (principalComponentOnPiece k (@orderWeight (n + 1)) e a : SymbolRing k (n + 1)) •
        targetTotal0LinearEquivOrderAssociatedGraded k n N d hd z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    by_cases hp : 0 < p
    · have := zeroPage_target_subsingleton_of_pos k n N p d hd hp
      simp [Subsingleton.elim y 0]
    · let m := (-p).toNat
      have hm : p = -(m : ℤ) := by dsimp [m]; omega
      obtain ⟨z, rfl⟩ := targetRepresentative_surjective k n N d hd p m hm y
      rw [show DirectSum.of ((K k n N d hd).TargetPage 0) p =
        (DirectSum.lof k ℤ (fun p => (K k n N d hd).TargetPage 0 p) p).toAddMonoidHom from rfl]
      simp only [LinearMap.toAddMonoidHom_coe]
      change targetTotal0LinearEquivOrderAssociatedGraded k n N d hd
        (P.targetTotalMap 0 (DirectSum.lof k ℤ _ p
          (targetRepresentative k n N d hd p m hm z))) = _
      rw [P.targetTotalMap_lof,
        targetRepresentative_map k n N d hd e a P hP,
        targetEquiv_representative, targetEquiv_representative,
        smul_orderAssociatedGradedOf_mk_eq_of_mul]
  | add x y hx hy => simpa [smul_add] using congrArg₂ (· + ·) hx hy

theorem sourceEquiv_intertwines_generator (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (i : Fin n ⊕ Fin n) (z : (K k n N d hd).SourceTotal 0) :
    sourceTotal0LinearEquivOrderAssociatedGraded k n N d hd
        (sourceGenerator k n N d hd 0 i z) =
      (MvPolynomial.X (oldIndex i) : SymbolRing k (n + 1)) •
        sourceTotal0LinearEquivOrderAssociatedGraded k n N d hd z := by
  have h := sourceEquiv_intertwines_rightMul k n N d hd (tangentialDegree i)
    (oldGeneratorOrderPiece k n i) (generator k n N d hd i) (by cases i <;> rfl) z
  rw [principal_oldGenerator] at h
  exact h

theorem targetEquiv_intertwines_generator (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (i : Fin n ⊕ Fin n) (z : (K k n N d hd).TargetTotal 0) :
    targetTotal0LinearEquivOrderAssociatedGraded k n N d hd
        (targetGenerator k n N d hd 0 i z) =
      (MvPolynomial.X (oldIndex i) : SymbolRing k (n + 1)) •
        targetTotal0LinearEquivOrderAssociatedGraded k n N d hd z := by
  have h := targetEquiv_intertwines_rightMul k n N d hd (tangentialDegree i)
    (oldGeneratorOrderPiece k n i) (generator k n N d hd i) (by cases i <;> rfl) z
  rw [principal_oldGenerator] at h
  exact h

def coordinateOrderPiece (n : ℕ) : orderPiece k (n + 1) 0 :=
  ⟨presentedCoordinate k n, presentedCoordinate_mem_orderPiece_zero k n⟩

theorem principal_coordinate (n : ℕ) :
    (principalComponentOnPiece k (@orderWeight (n + 1)) 0
      (coordinateOrderPiece k n) : SymbolRing k (n + 1)) =
      MvPolynomial.X (.inl (0 : Fin (n + 1))) := by
  change MvPolynomial.weightedHomogeneousComponent orderWeight 0
      (presentedNormalFormLinearEquiv k (n + 1)
        (Stafford.freeWeylGenerator (standardForm k (n + 1)) (.inl 0))) = _
  rw [presentedNormalFormLinearEquiv_generator]
  change MvPolynomial.weightedHomogeneousComponent orderWeight 0
    (MvPolynomial.monomial (Finsupp.single (Sum.inl (0 : Fin (n + 1))) 1) 1) = _
  rw [weightedHomogeneousComponent_monomial]
  simp [monomialWeight, orderWeight, fibreWeight]
  rw [MvPolynomial.monomial_eq]
  simp

theorem sourceRepresentative_drop (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (p : ℤ) (m : ℕ) (h : p = -(m : ℤ)) (z : orderPiece k (n + 1) m) :
    (K k n N d hd).drop 0 p (sourceRepresentative k n N d hd p m h z) =
      targetRepresentative k n N d hd (p + 0) (m + 0) (by omega)
        ⟨(z : PresentedWeyl k (n + 1)) * presentedCoordinate k n,
          mul_mem_orderPiece k z.property (presentedCoordinate_mem_orderPiece_zero k n)⟩ := by
  rw [sourceRepresentative, (K k n N d hd).drop_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  rfl

theorem totalDrop_zero_intertwines_coordinate (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (z : (K k n N d hd).SourceTotal 0) :
    targetTotal0LinearEquivOrderAssociatedGraded k n N d hd
        ((K k n N d hd).totalDrop 0 z) =
      (MvPolynomial.X (.inl (0 : Fin (n + 1))) : SymbolRing k (n + 1)) •
        sourceTotal0LinearEquivOrderAssociatedGraded k n N d hd z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    by_cases hp : 0 < p
    · have := zeroPage_source_subsingleton_of_pos k n N p d hd hp
      simp [Subsingleton.elim y 0]
    · let m := (-p).toNat
      have hm : p = -(m : ℤ) := by dsimp [m]; omega
      obtain ⟨z, rfl⟩ := sourceRepresentative_surjective k n N d hd p m hm y
      rw [show DirectSum.of ((K k n N d hd).SourcePage 0) p =
        (DirectSum.lof k ℤ (fun p => (K k n N d hd).SourcePage 0 p) p).toAddMonoidHom from rfl]
      simp only [LinearMap.toAddMonoidHom_coe]
      change targetTotal0LinearEquivOrderAssociatedGraded k n N d hd
        ((K k n N d hd).totalDrop 0 (DirectSum.lof k ℤ _ p
          (sourceRepresentative k n N d hd p m hm z))) = _
      rw [(K k n N d hd).totalDrop_lof,
        sourceRepresentative_drop]
      trans orderAssociatedGradedOf k (CI k n N d) (m + 0)
        (orderPieceToQuotientGraded k (CI k n N d) (m + 0)
          ⟨(z : PresentedWeyl k (n + 1)) * presentedCoordinate k n,
            mul_mem_orderPiece k z.property (presentedCoordinate_mem_orderPiece_zero k n)⟩)
      · exact targetEquiv_representative k n N d hd (p + 0) (m + 0) (by omega) _
      · rw [sourceEquiv_representative, ← principal_coordinate k n,
          smul_orderAssociatedGradedOf_mk_eq_of_mul]
        rfl
  | add x y hx hy => simpa [smul_add] using congrArg₂ (· + ·) hx hy


end
end Stafford38.Characteristic.CanonicalTotalGradedActionCompatibility
