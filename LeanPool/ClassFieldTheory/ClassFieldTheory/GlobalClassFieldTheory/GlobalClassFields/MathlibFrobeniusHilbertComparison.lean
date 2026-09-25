/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticHilbertClassFieldReciprocity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SUnit.GaloisAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Core
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassFieldOverOriginalBase
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorFrobenius
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldMaximalSubextension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldPrimeSplitting
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldMaximalSubextension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldOverOriginalBase
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealDecompositionLaw
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertPrincipalization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertSplitting
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.NormalClosure
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SUnit.Herbrand
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Frobenius
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.MathlibUnramifiedInterface
/-!
# Frobenius and Hilbert class fields implementation

This module supplies the implementation proofs for the compact public
statements in `ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields`.

The prime element exposed below is the arithmetic-normalized prime Artin
element.  Its residue action identifies it with Mathlib's arithmetic
Frobenius at every unramified finite prime.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace ClassFieldTheory.GlobalClassFieldComparison

open NumberField IsDedekindDomain
open LocalFieldTheory
open scoped ValuativeRel

section PrimeArtin

open scoped Pointwise
open AlgebraicNumberTheory.Valuations

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- Convert Mathlib's ideal-theoretic unramifiedness of a base prime into the
chosen-completion formulation used by the current Artin implementation. -/
private theorem chosenFinitePlaceIsUnramified_of_isUnramifiedIn
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) :
    _root_.ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  let w := _root_.chosenFinitePlaceExtension (L := L) v
  let W :=
    _root_.finitePlaceExtensionCentre
      (K := K) (L := L) v w
  have hW : W.asIdeal.LiesOver v.asIdeal :=
    _root_.finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w
  apply
    _root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v
  exact hunram W.asIdeal inferInstance hW

/-- The arithmetic-normalized prime Artin element is the inverse of the
geometric-normalized prime Artin element.  This fixes the relation between the
two reciprocity conventions. -/
theorem arithmeticPrimeArtin_eq_inverse
    (v : HeightOneSpectrum (𝓞 K)) :
    GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v =
      (GlobalClassFieldTheory.GlobalClassFields.finitePlacePrimeArtin
          (K := K) (L := L) v)⁻¹ :=
  GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_inv
    (K := K) (L := L) v

/-- The arithmetic prime Artin element preserves the chosen prime above the
base prime.  This is the decomposition-group part of its Frobenius property;
the residue-field congruence is a separate comparison. -/
theorem arithmeticPrimeArtin_stabilizes_chosenPrime
    (v : HeightOneSpectrum (𝓞 K)) :
    let w := chosenFinitePlaceExtension (L := L) v
    let W := finitePlaceExtensionCentre (K := K) (L := L) v w
    GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v ∈
      MulAction.stabilizer (L ≃ₐ[K] L) W.asIdeal := by
  let w := chosenFinitePlaceExtension (L := L) v
  let W := finitePlaceExtensionCentre (K := K) (L := L) v w
  let σ := GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
    (K := K) (L := L) v
  have hgeo :
      GlobalClassFieldTheory.GlobalClassFields.finitePlacePrimeArtin
          (K := K) (L := L) v ∈
        finitePlaceDecompositionGroup (K := K) (L := L) v := by
    rw [GlobalClassFieldTheory.GlobalClassFields.finitePlacePrimeArtin_eq_chosenFinitePlaceArtin]
    rw [← GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_range]
    exact ⟨FiniteIdeleGroup.chosenLocalOrderSection v 1, rfl⟩
  have hσ : σ ∈ finitePlaceDecompositionGroup (K := K) (L := L) v := by
    change GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v ∈
      finitePlaceDecompositionGroup (K := K) (L := L) v
    rw [GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_inv]
    exact Subgroup.inv_mem _ hgeo
  have hσinv : σ⁻¹ ∈ finitePlaceDecompositionGroup (K := K) (L := L) v :=
    Subgroup.inv_mem _ hσ
  have hw :
      absoluteValueExtensionConjugate
          (HeightOneSpectrum.adicAbv K v) w σ⁻¹ = w :=
    (mem_finitePlaceDecompositionGroup_iff v σ⁻¹).mp hσinv
  have hW : finitePlaceEquiv K L σ W = W := by
    have hcentre := finitePlaceExtensionCentre_conjugate
      (K := K) (L := L) v w σ⁻¹
    rw [hw] at hcentre
    simpa only [inv_inv] using hcentre.symm
  have hIdeal := congrArg HeightOneSpectrum.asIdeal hW
  have hIdeal' :
      W.asIdeal.map
          (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv = W.asIdeal := by
    simpa only [finitePlaceEquiv_asIdeal] using hIdeal
  change σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) W.asIdeal
  rw [MulAction.mem_stabilizer_iff, Ideal.pointwise_smul_def]
  exact hIdeal'

/-- In an abelian extension, the arithmetic prime Artin element preserves
every prime above the base prime, not only the chosen one. -/
theorem arithmeticPrimeArtin_stabilizes_prime
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal) :
    GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v ∈
      MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
  let W := finitePlaceExtensionCentre (K := K) (L := L) v
    (chosenFinitePlaceExtension (L := L) v)
  have hWover : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver (K := K) (L := L) v
      (chosenFinitePlaceExtension (L := L) v)
  obtain ⟨τ, hτ⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq
      (𝓞 K) (𝓞 L) (L ≃ₐ[K] L)
      W.asIdeal w.asIdeal (hWover.over.symm.trans hw.over)
  have hW := arithmeticPrimeArtin_stabilizes_chosenPrime
    (K := K) (L := L) v
  rw [MulAction.mem_stabilizer_iff] at hW ⊢
  rw [hτ]
  calc
    GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v • (τ • W.asIdeal) =
        τ • (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v • W.asIdeal) := by
      simp only [← mul_smul]
      exact congrArg (fun γ : L ≃ₐ[K] L => γ • W.asIdeal)
        (IsMulCommutative.is_comm.comm
          (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
            (K := K) (L := L) v) τ)
    _ = τ • W.asIdeal := by rw [hW]

open GlobalClassFieldTheory.GlobalClassFields renaming
  orderOf_arithmeticFinitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified →
    orderOf_primeArtin_eq_localDegree_of_unramified in
open GlobalClassFieldTheory.IdealClassFieldTheory renaming
  finitePlaceLocalDegree_eq_inertiaDegree_of_chosenUnramified →
    finitePlaceLocalDegree_eq_inertiaDegree_of_chosenUnramified in
/-- At an ideal-theoretically unramified finite prime, the order of the
arithmetic-normalized prime Artin element is the common inertia degree of the
prime ideals above the base prime. -/
theorem orderOf_arithmeticPrimeArtin_eq_inertiaDegree
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) :
    orderOf
        (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v) =
      Ideal.inertiaDegIn v.asIdeal (𝓞 L) := by
  calc
    orderOf
        (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v) =
        _root_.finitePlaceLocalDegree (K := K) (L := L) v :=
      orderOf_primeArtin_eq_localDegree_of_unramified
        (K := K) (L := L) v
        (chosenFinitePlaceIsUnramified_of_isUnramifiedIn
          (K := K) (L := L) v hunram)
    _ = Ideal.inertiaDegIn v.asIdeal (𝓞 L) :=
      finitePlaceLocalDegree_eq_inertiaDegree_of_chosenUnramified
        (K := K) (L := L) v
        (chosenFinitePlaceIsUnramified_of_isUnramifiedIn
          (K := K) (L := L) v hunram)

open GlobalClassFieldTheory.GlobalClassFields renaming
  arithmeticFinitePlacePrimeArtin_eq_one_iff_splitsCompletely_of_chosenUnramified →
    primeArtin_eq_one_iff_splitsCompletely_of_unramified in
/-- At an ideal-theoretically unramified finite prime, the arithmetic-normalized prime
Artin element is trivial exactly when the finite place actually splits
completely. -/
theorem arithmeticPrimeArtin_eq_one_iff_splitsCompletely
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) :
    GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v =
        1 ↔
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v :=
  primeArtin_eq_one_iff_splitsCompletely_of_unramified
    (K := K) (L := L) v
    (chosenFinitePlaceIsUnramified_of_isUnramifiedIn
      (K := K) (L := L) v hunram)

end PrimeArtin

section ArithmeticFrobenius

open scoped Pointwise

/-- Mathlib's arithmetic Frobenius has order equal to the residue degree
at an unramified prime.  The proof compares its residue action with the
finite-field Frobenius and uses the decomposition-group cardinality. -/
theorem orderOf_arithmeticFrobeniusAt_eq_inertiaDegree
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    orderOf (arithmeticFrobeniusAt (K := K) w) =
      w.asIdeal.inertiaDeg (𝓞 K) := by
  classical
  let P : Ideal (𝓞 K) := v.asIdeal
  let Q : Ideal (𝓞 L) := w.asIdeal
  let G := L ≃ₐ[K] L
  let g : G := arithmeticFrobeniusAt (K := K) w
  let : Q.LiesOver P := hw
  let : Algebra.IsUnramifiedAt (𝓞 K) Q := hunram
  let : Field ((𝓞 K) ⧸ P) := Ideal.Quotient.field P
  let : Field ((𝓞 L) ⧸ Q) := Ideal.Quotient.field Q
  let : Finite ((𝓞 K) ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let : Finite ((𝓞 L) ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  let : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hF : IsArithFrobAt (𝓞 K) g Q := by
    change IsArithFrobAt (𝓞 K) (arithFrobAt (𝓞 K) G Q) Q
    exact IsArithFrobAt.arithFrobAt (𝓞 K) G Q
  let gs : MulAction.stabilizer G Q := ⟨g, hF.mem_stabilizer⟩
  have hImage :
      Ideal.Quotient.stabilizerHom Q P G gs =
        FiniteField.frobeniusAlgEquivOfAlgebraic ((𝓞 K) ⧸ P) ((𝓞 L) ⧸ Q) := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.stabilizerHom_apply]
    simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    have h := hF.mk_apply y
    have hQP : Q.under (𝓞 K) = P := hw.over.symm
    rw [hQP, Nat.card_eq_fintype_card] at h
    exact h
  have hImageOrder :
      orderOf (Ideal.Quotient.stabilizerHom Q P G gs) =
        Q.inertiaDeg (𝓞 K) := by
    rw [hImage, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    exact (Ideal.inertiaDeg_eq_of_isMaximal P Q).symm
  have hCard : Nat.card (MulAction.stabilizer G Q) =
      Q.inertiaDeg (𝓞 K) := by
    rw [Ideal.card_stabilizer_eq (G := G) P Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx P Q G,
      Ideal.inertiaDegIn_eq_inertiaDeg P Q G,
      Ideal.ramificationIdx_eq_one Q (𝓞 K), one_mul]
  have hUpper : orderOf gs ∣ Q.inertiaDeg (𝓞 K) := by
    rw [← hCard]
    exact orderOf_dvd_natCard gs
  have hLower : Q.inertiaDeg (𝓞 K) ∣ orderOf gs := by
    rw [← hImageOrder]
    exact orderOf_map_dvd (Ideal.Quotient.stabilizerHom Q P G) gs
  change orderOf g = Q.inertiaDeg (𝓞 K)
  exact (Subgroup.orderOf_coe gs).trans (Nat.dvd_antisymm hUpper hLower)

end ArithmeticFrobenius

/-- In an abelian extension, Mathlib's chosen arithmetic Frobenius is
independent of the prime above a fixed base prime.  Mathlib chooses
conjugate lifts, and conjugacy is equality in the abelian Galois group. -/
theorem arithmeticFrobeniusAt_eq_of_liesOver
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w w' : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (hw' : w'.asIdeal.LiesOver v.asIdeal) :
    arithmeticFrobeniusAt (K := K) w =
      arithmeticFrobeniusAt (K := K) w' := by
  obtain ⟨τ, hτ⟩ := isConj_iff.mp
    (isConj_arithFrobAt (𝓞 K) (L ≃ₐ[K] L)
      w.asIdeal w'.asIdeal (hw.over.symm.trans hw'.over))
  calc
    arithmeticFrobeniusAt (K := K) w =
        τ * arithmeticFrobeniusAt (K := K) w * τ⁻¹ := by
      rw [IsMulCommutative.is_comm.comm τ
        (arithmeticFrobeniusAt (K := K) w), mul_assoc,
        mul_inv_cancel, mul_one]
    _ = arithmeticFrobeniusAt (K := K) w' := hτ

open GlobalClassFieldTheory.GlobalClassFields renaming
  arithmeticFinitePlacePrimeArtin_eq_chosenFinitePlaceArithmeticFrobenius →
    arithmeticFinitePlacePrimeArtin_eq_chosenFinitePlaceArithmeticFrobenius in
/-- At an unramified finite prime, the arithmetic-normalized prime Artin
element is Mathlib's arithmetic Frobenius, independently of the chosen prime
above the base prime. -/
theorem arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v =
      arithmeticFrobeniusAt (K := K) w := by
  classical
  let w₀ := chosenFinitePlaceExtension (L := L) v
  let W := finitePlaceExtensionCentre (K := K) (L := L) v w₀
  let P : Ideal (𝓞 K) := v.asIdeal
  let Q : Ideal (𝓞 L) := W.asIdeal
  let G := L ≃ₐ[K] L
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let : Algebra C E :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinLocalizedAlgebra v w₀
  have hW : Q.LiesOver P :=
    finitePlaceExtensionCentre_liesOver (K := K) (L := L) v w₀
  let : Q.LiesOver P := hW
  let : w.asIdeal.LiesOver P := hw
  let : Finite G := IsGaloisGroup.finite G K L
  let : IsGaloisGroup G (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing G (𝓞 K) (𝓞 L) K L
  have hEw : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    (Ideal.ramificationIdx_eq_one_iff).mpr hunram
  have hEQ : Q.ramificationIdx (𝓞 K) =
      w.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_eq_of_isGaloisGroup P Q w.asIdeal G
  have hunramQ : Algebra.IsUnramifiedAt (𝓞 K) Q :=
    (Ideal.ramificationIdx_eq_one_iff).mp (hEQ.trans hEw)
  have hChosen : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v :=
    chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v hunramQ
  let : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension C E := hChosen
  let vK := HeightOneSpectrum.adicAbv K v
  let eD : HilbertRamification.absoluteValueDecompositionGroup K w₀.1 ≃*
      (E ≃ₐ[C] E) :=
    HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
      vK (RayClass.adicAbv_isNontrivial v) w₀
  let f : E ≃ₐ[C] E := arithmeticFrobeniusOfUnramifiedValuation C E
  let δ : HilbertRamification.absoluteValueDecompositionGroup K w₀.1 :=
    eD.symm f
  have heDδ : eD δ = f := eD.apply_symm_apply f
  have hδ : (δ : G) =
      GlobalClassFieldTheory.GlobalClassFields.chosenFinitePlaceArithmeticFrobenius
        (K := K) (L := L) v hChosen := by
    change (eD.symm f : G) =
      GlobalClassFieldTheory.Reciprocity.finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w₀ f
    rfl
  let e : (𝓞 L ⧸ Q) ≃+* 𝓀[E] :=
    chosenFinitePlaceLocalizedResidueEquiv (K := K) (L := L) v
  have hCard : Nat.card 𝓀[C] =
      Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
    rw [finitePlaceCompletion_residueField_card (K := K) v,
      hW.over.symm]
  have hResidue (x : 𝓞 L) :
      Ideal.Quotient.mk Q
          (NumberField.RingOfIntegers.mapAlgEquiv (δ : G) x) =
        (Ideal.Quotient.mk Q x) ^
          Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
    apply e.injective
    calc
      e (Ideal.Quotient.mk Q
          (NumberField.RingOfIntegers.mapAlgEquiv (δ : G) x)) =
          LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure C E
            (eD δ) (e (Ideal.Quotient.mk Q x)) :=
        chosenFinitePlaceLocalizedResidueEquiv_equivariant
          (K := K) (L := L) v δ x
      _ = LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure C E
            f (e (Ideal.Quotient.mk Q x)) := by
        simp only [heDδ]
      _ = (e (Ideal.Quotient.mk Q x)) ^ Nat.card 𝓀[C] :=
        galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply
          C E (e (Ideal.Quotient.mk Q x))
      _ = e ((Ideal.Quotient.mk Q x) ^
            Nat.card (𝓞 K ⧸ Q.under (𝓞 K))) := by
        exact (congrArg
          (fun n : ℕ => (e (Ideal.Quotient.mk Q x)) ^ n) hCard).trans
          (map_pow e (Ideal.Quotient.mk Q x) _).symm
  have hArith : IsArithFrobAt (𝓞 K) (δ : G) Q := by
    intro x
    change NumberField.RingOfIntegers.mapAlgEquiv (δ : G) x -
        x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ∈ Q
    rw [← Ideal.Quotient.eq, map_pow]
    exact hResidue x
  have hMath : IsArithFrobAt (𝓞 K)
      (arithmeticFrobeniusAt (K := K) W) Q := by
    change IsArithFrobAt (𝓞 K) (arithFrobAt (𝓞 K) G Q) Q
    exact IsArithFrobAt.arithFrobAt (𝓞 K) G Q
  have hInertiaCard : Nat.card (Q.inertia G) = 1 := by
    calc
      Nat.card (Q.inertia G) = P.ramificationIdxIn (𝓞 L) :=
        Ideal.card_inertia_eq_ramificationIdxIn (G := G) P Q
      _ = Q.ramificationIdx (𝓞 K) :=
        Ideal.ramificationIdxIn_eq_ramificationIdx P Q G
      _ = 1 := hEQ.trans hEw
  have hInertiaBot : Q.inertia G = ⊥ :=
    (Subgroup.eq_bot_iff_card (Q.inertia G)).mpr hInertiaCard
  have hDiff : (δ : G) * (arithmeticFrobeniusAt (K := K) W)⁻¹ ∈
      Q.inertia G := hArith.mul_inv_mem_inertia hMath
  have hDiffEq : (δ : G) * (arithmeticFrobeniusAt (K := K) W)⁻¹ = 1 := by
    simpa only [hInertiaBot, Subgroup.mem_bot] using hDiff
  have hδEq : (δ : G) = arithmeticFrobeniusAt (K := K) W :=
    mul_inv_eq_one.mp hDiffEq
  calc
    GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v =
        GlobalClassFieldTheory.GlobalClassFields.chosenFinitePlaceArithmeticFrobenius
          (K := K) (L := L) v hChosen :=
      arithmeticFinitePlacePrimeArtin_eq_chosenFinitePlaceArithmeticFrobenius
        (K := K) (L := L) v hChosen
    _ = (δ : G) := hδ.symm
    _ = arithmeticFrobeniusAt (K := K) W := hδEq
    _ = arithmeticFrobeniusAt (K := K) w :=
      arithmeticFrobeniusAt_eq_of_liesOver
        (K := K) (L := L) v W w hW hw

/-- Ideal-theoretic complete splitting at every prime above a finite place
agrees with the decomposition-group definition used by the existing library. -/
theorem finitePrimeSplitsCompletely_iff_original
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePrimeSplitsCompletely K L v ↔
      _root_.FinitePlaceSplitsCompletely (K := K) (L := L) v := by
  let : Finite (L ≃ₐ[K] L) := IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  let := _root_.finitePlaceMulAction K L
  have hlocal (W : HeightOneSpectrum (𝓞 L))
      (hW : W.asIdeal.LiesOver v.asIdeal) :
      Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) W) =
        W.asIdeal.ramificationIdx (𝓞 K) *
          W.asIdeal.inertiaDeg (𝓞 K) := by
    let : W.asIdeal.LiesOver v.asIdeal := hW
    calc
      _ = _root_.finiteLogPlaceLocalDegree K L W :=
        _root_.finitePlace_stabilizer_card_eq_localDegree K L W
      _ = v.asIdeal.ramificationIdxIn (𝓞 L) *
          v.asIdeal.inertiaDegIn (𝓞 L) := by
        unfold _root_.finiteLogPlaceLocalDegree
        rw [hW.over.symm]
      _ = _ := by
        rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal W.asIdeal (L ≃ₐ[K] L),
          Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal W.asIdeal (L ≃ₐ[K] L)]
  constructor
  · intro h
    let w := _root_.chosenFinitePlaceExtension (L := L) v
    let W := _root_.finitePlaceExtensionCentre (K := K) (L := L) v w
    have hW : W.asIdeal.LiesOver v.asIdeal :=
      _root_.finitePlaceExtensionCentre_liesOver (K := K) (L := L) v w
    have hb := h W hW
    have hCard : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) W) = 1 := by
      rw [hlocal W hW, hb.1, hb.2]
    have hBot : MulAction.stabilizer (L ≃ₐ[K] L) W = ⊥ :=
      (Subgroup.eq_bot_iff_card _).mpr hCard
    have hBelow : _root_.finitePlaceBelow (K := K) W = v :=
      _root_.finitePlaceBelow_finitePlaceExtensionCentre (K := K) (L := L) v w
    exact (_root_.finitePlaceSplitsCompletely_iff_stabilizer_eq_bot
      (K := K) (L := L) v W hBelow).mpr hBot
  · intro h W hW
    have hBelow : _root_.finitePlaceBelow (K := K) W = v := by
      apply HeightOneSpectrum.ext
      exact hW.over.symm
    have hBot := (_root_.finitePlaceSplitsCompletely_iff_stabilizer_eq_bot
      (K := K) (L := L) v W hBelow).mp h
    have hCard : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) W) = 1 :=
      (Subgroup.eq_bot_iff_card _).mp hBot
    rw [hlocal W hW] at hCard
    have he : W.asIdeal.ramificationIdx (𝓞 K) ∣ 1 :=
      ⟨W.asIdeal.inertiaDeg (𝓞 K), hCard.symm⟩
    have hf : W.asIdeal.inertiaDeg (𝓞 K) ∣ 1 :=
      ⟨W.asIdeal.ramificationIdx (𝓞 K), by
        simpa only [mul_comm] using hCard.symm⟩
    exact ⟨Nat.dvd_one.mp he, Nat.dvd_one.mp hf⟩

section HilbertClassFields

variable (K : Type) [Field K] [NumberField K]

/-- Embed the selected big Hilbert class field in the separable closure of
its original base field. -/
private noncomputable def bigHilbertClassFieldEmbedding :
    GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField K →ₐ[K]
      SeparableClosure K :=
  IsSepClosed.lift

/-- The selected big Hilbert class field, represented in the public type of
finite abelian subextensions of the separable closure. -/
private noncomputable def bigHilbertClassFieldFiniteAbelianExtension :
    FiniteAbelianExtension K := by
  let j := bigHilbertClassFieldEmbedding K
  exact ⟨j.fieldRange,
    j.equivFieldRange.toLinearEquiv.finiteDimensional,
    IsAbelianGalois.of_algHom j.equivFieldRange.symm.toAlgHom⟩

/-- The original selected field and its public separable-closure
realization are equivalent over the base. -/
private noncomputable def bigHilbertClassFieldEquiv :
    GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField K ≃ₐ[K]
      bigHilbertClassFieldFiniteAbelianExtension K :=
  (bigHilbertClassFieldEmbedding K).equivFieldRange

/-- The selected small Hilbert class field in the separable closure. -/
private noncomputable def smallHilbertClassFieldEmbedding :
    GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K →ₐ[K]
      SeparableClosure K :=
  IsSepClosed.lift

private noncomputable def smallHilbertClassFieldFiniteAbelianExtension :
    FiniteAbelianExtension K := by
  let j := smallHilbertClassFieldEmbedding K
  exact ⟨j.fieldRange,
    j.equivFieldRange.toLinearEquiv.finiteDimensional,
    IsAbelianGalois.of_algHom j.equivFieldRange.symm.toAlgHom⟩

private noncomputable def smallHilbertClassFieldEquiv :
    GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K ≃ₐ[K]
      smallHilbertClassFieldFiniteAbelianExtension K :=
  (smallHilbertClassFieldEmbedding K).equivFieldRange

open GlobalClassFieldTheory.GlobalClassFields renaming
  bigHilbertClassField_finrank_over_original_eq_narrowClassGroup_card →
    bigHilbertClassField_finrank_over_original_eq_narrowClassGroup_card in
/-- The selected big Hilbert class field has degree equal to the order of the
narrow class group of the original number field. -/
theorem bigHilbertClassField_degree_eq_narrowClassGroup_card :
    Module.finrank K
        (GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField K) =
      Nat.card (RayClass.NarrowClassGroup K) :=
  bigHilbertClassField_finrank_over_original_eq_narrowClassGroup_card
    K

open GlobalClassFieldTheory.GlobalClassFields renaming
  smallHilbertClassField_finrank_over_original_eq_classNumber →
    smallHilbertClassField_finrank_over_original_eq_classNumber in
/-- The selected small Hilbert class field has degree equal to the ordinary
class number of the original number field. -/
theorem smallHilbertClassField_degree_eq_classNumber :
    Module.finrank K
        (GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K) =
      NumberField.classNumber K :=
  smallHilbertClassField_finrank_over_original_eq_classNumber
    K

/-- The selected big Hilbert class field is unramified at every finite
place. -/
theorem bigHilbertClassField_unramifiedAtFinitePlaces :
    _root_.IsUnramifiedAtFinitePlaces K
      (GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField K) :=
  GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField_isUnramifiedAtFinitePlaces
    K

open GlobalClassFieldTheory.GlobalClassFields renaming
  finiteUnramifiedAbelianExtension_nonempty_algHom_bigHilbertClassField →
    finiteUnramifiedAbelianExtension_nonempty_algHom_bigHilbertClassField in
/-- Every publicly represented finite-prime-unramified abelian extension
embeds into the selected big Hilbert class field. -/
private theorem nonempty_algHom_to_selectedBigHilbertClassField
    (F : FiniteAbelianExtension K)
    (hF : IsUnramifiedAtFinitePlaces K F) :
    Nonempty (F →ₐ[K]
      GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField K) := by
  obtain ⟨f⟩ :=
    finiteUnramifiedAbelianExtension_nonempty_algHom_bigHilbertClassField
      K F ((isUnramifiedAtFinitePlaces_iff_original K F).mp hF)
  exact ⟨f⟩

/-- The intrinsic big Hilbert class field exists inside the chosen
separable closure of the base. -/
theorem exists_bigHilbertClassField :
    ∃ E : FiniteAbelianExtension K, IsBigHilbertClassField E := by
  let E := bigHilbertClassFieldFiniteAbelianExtension K
  let e : GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField K ≃ₐ[K] E :=
    bigHilbertClassFieldEquiv K
  refine ⟨E, ?_, ?_⟩
  · exact
      (isUnramifiedAtFinitePlaces_iff_of_algEquiv K
        (GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField K) E e).mp
        ((isUnramifiedAtFinitePlaces_iff_original K
          (GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField K)).mpr
          (bigHilbertClassField_unramifiedAtFinitePlaces K))
  · intro F hF
    obtain ⟨f⟩ := nonempty_algHom_to_selectedBigHilbertClassField K F hF
    exact ⟨e.toAlgHom.comp f⟩

/-- Every intrinsic big Hilbert class field has the degree of the selected
implementation, hence the narrow class number. -/
theorem bigHilbertClassField_degree_eq_narrowClassGroup_card_of_isBig
    (E : FiniteAbelianExtension K)
    (hE : IsBigHilbertClassField E) :
    Module.finrank K E = Nat.card (RayClass.NarrowClassGroup K) := by
  let H := GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField K
  let F := bigHilbertClassFieldFiniteAbelianExtension K
  let e : H ≃ₐ[K] F := bigHilbertClassFieldEquiv K
  have hF : IsUnramifiedAtFinitePlaces K F :=
    (isUnramifiedAtFinitePlaces_iff_of_algEquiv K H F e).mp
      ((isUnramifiedAtFinitePlaces_iff_original K H).mpr
        (bigHilbertClassField_unramifiedAtFinitePlaces K))
  obtain ⟨f⟩ := nonempty_algHom_to_selectedBigHilbertClassField K E hE.1
  obtain ⟨g⟩ := hE.2 F hF
  have hEH : Module.finrank K E ≤ Module.finrank K H :=
    f.toLinearMap.finrank_le_finrank_of_injective f.injective
  have hHF : Module.finrank K H = Module.finrank K F :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  have hFE : Module.finrank K F ≤ Module.finrank K E :=
    g.toLinearMap.finrank_le_finrank_of_injective g.injective
  have hHE : Module.finrank K H ≤ Module.finrank K E := by
    rw [hHF]
    exact hFE
  exact (Nat.le_antisymm hEH hHE).trans
    (bigHilbertClassField_degree_eq_narrowClassGroup_card K)

/-- The selected small Hilbert class field is unramified at all finite and
infinite places. -/
theorem smallHilbertClassField_everywhereUnramified :
    _root_.IsEverywhereUnramified K
      (GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K) :=
  GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_isEverywhereUnramified
    K

open GlobalClassFieldTheory.GlobalClassFields renaming
  finiteAbelianExtension_nonempty_algHom_to_smallHilbertClassField_of_everywhereUnramified →
    nonempty_algHom_smallHilbertClassField_of_unramified in
/-- Any publicly represented everywhere-unramified abelian extension
embeds into the selected small Hilbert class field. -/
private theorem nonempty_algHom_to_selectedSmallHilbertClassField
    (F : FiniteAbelianExtension K)
    (hF : IsEverywhereUnramified K F) :
    Nonempty (F →ₐ[K]
      GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K) := by
  have hFinite : _root_.IsUnramifiedAtFinitePlaces K F :=
    (isUnramifiedAtFinitePlaces_iff_original K F).mp hF.1
  have hRamifiedEmpty :
      _root_.ramifiedBaseFinitePlaces (K := K) (L := F) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨P, _hP, hP⟩ :=
      (_root_.mem_ramifiedBaseFinitePlaces_iff
        (K := K) (L := F) v).1 hv
    exact hP (hFinite P)
  exact
    @nonempty_algHom_smallHilbertClassField_of_unramified
      K F inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hF.2 hRamifiedEmpty

/-- The intrinsic small Hilbert class field exists inside the chosen
separable closure of the base. -/
theorem exists_smallHilbertClassField :
    ∃ E : FiniteAbelianExtension K, IsSmallHilbertClassField E := by
  let E := smallHilbertClassFieldFiniteAbelianExtension K
  let e : GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K ≃ₐ[K] E :=
    smallHilbertClassFieldEquiv K
  refine ⟨E, ?_, ?_⟩
  · exact
      (isEverywhereUnramified_iff_of_algEquiv K
        (GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K) E e).mp
        ((isEverywhereUnramified_iff_original K
          (GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K)).mpr
          (smallHilbertClassField_everywhereUnramified K))
  · intro F hF
    obtain ⟨f⟩ := nonempty_algHom_to_selectedSmallHilbertClassField K F hF
    exact ⟨e.toAlgHom.comp f⟩

/-- Every intrinsic small Hilbert class field has the degree of the
selected implementation, hence the class number. -/
theorem smallHilbertClassField_degree_eq_classNumber_of_isSmall
    (E : FiniteAbelianExtension K)
    (hE : IsSmallHilbertClassField E) :
    Module.finrank K E = NumberField.classNumber K := by
  let H := GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K
  let F := smallHilbertClassFieldFiniteAbelianExtension K
  let e : H ≃ₐ[K] F := smallHilbertClassFieldEquiv K
  have hF : IsEverywhereUnramified K F :=
    (isEverywhereUnramified_iff_of_algEquiv K H F e).mp
      ((isEverywhereUnramified_iff_original K H).mpr
        (smallHilbertClassField_everywhereUnramified K))
  obtain ⟨f⟩ := nonempty_algHom_to_selectedSmallHilbertClassField K E hE.1
  obtain ⟨g⟩ := hE.2 F hF
  have hEH : Module.finrank K E ≤ Module.finrank K H :=
    f.toLinearMap.finrank_le_finrank_of_injective f.injective
  have hHF : Module.finrank K H = Module.finrank K F :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  have hFE : Module.finrank K F ≤ Module.finrank K E :=
    g.toLinearMap.finrank_le_finrank_of_injective g.injective
  have hHE : Module.finrank K H ≤ Module.finrank K E := by
    rw [hHF]
    exact hFE
  exact (Nat.le_antisymm hEH hHE).trans
    (smallHilbertClassField_degree_eq_classNumber K)

/-- Every intrinsic small Hilbert class field is isomorphic over the base to
the selected implementation. -/
noncomputable def smallHilbertClassFieldEquivOfIsSmall
    (E : FiniteAbelianExtension K)
    (hE : IsSmallHilbertClassField E) :
    E ≃ₐ[K]
      GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K := by
  let H := GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K
  let f := Classical.choice
    (nonempty_algHom_to_selectedSmallHilbertClassField K E hE.1)
  have hdim : Module.finrank K E = Module.finrank K H :=
    (smallHilbertClassField_degree_eq_classNumber_of_isSmall K E hE).trans
      (smallHilbertClassField_degree_eq_classNumber K).symm
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp f.injective
  exact AlgEquiv.ofBijective f ⟨f.injective, hsurj⟩

open GlobalClassFieldTheory.IdealClassFieldTheory renaming
  finitePlaceSplitsCompletelyInSmallHilbertClassField_iff_principal →
    finitePlaceSplitsCompletelyInSmallHilbertClassField_iff_principal in
/-- A finite prime actually splits completely in the selected small Hilbert
class field exactly when its prime fractional ideal is principal. -/
theorem finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal
    (v : HeightOneSpectrum (𝓞 K)) :
    _root_.FinitePlaceSplitsCompletely
          (K := K)
          (L := GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K)
          v ↔
      FractionalIdealGroup.prime v ∈
        (toPrincipalIdeal (𝓞 K) K).range :=
  finitePlaceSplitsCompletelyInSmallHilbertClassField_iff_principal
    (K := K) v

/-- The complete-splitting criterion transfers from the selected small
Hilbert class field to every intrinsic one. -/
theorem finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal_of_isSmall
    (E : FiniteAbelianExtension K)
    (hE : IsSmallHilbertClassField E)
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePrimeSplitsCompletely K E v ↔
      finitePrimeFractionalIdeal v ∈
        (toPrincipalIdeal (𝓞 K) K).range := by
  let H := GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K
  let e : E ≃ₐ[K] H := smallHilbertClassFieldEquivOfIsSmall K E hE
  have hTransport :
      _root_.FinitePlaceSplitsCompletely (K := K) (L := E) v ↔
        _root_.FinitePlaceSplitsCompletely (K := K) (L := H) v :=
    (_root_.finitePlaceSplitsCompletely_iff_inExtension
      (K := K) (E := E) v).trans
      ((_root_.finitePlaceSplitsCompletelyInExtension_algEquiv e v).trans
        (_root_.finitePlaceSplitsCompletely_iff_inExtension
          (K := K) (E := H) v).symm)
  exact (finitePrimeSplitsCompletely_iff_original K E v).trans
    (hTransport.trans
      (finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal K v))

/-- Every integral ideal becomes principal after extension to the selected
small Hilbert class field. -/
theorem ideals_becomePrincipalInSmallHilbertClassField :
    ∀ I : Ideal (𝓞 K),
      (I.map
        (algebraMap
          (𝓞 K)
          (𝓞 (GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K)))).IsPrincipal :=
  GlobalClassFieldTheory.IdealClassFieldTheory.allIdealsBecomePrincipalInSmallHilbertClassField
    (K := K)

/-- Principalization transfers from the selected small Hilbert class field
to every intrinsic one. -/
theorem ideals_becomePrincipalInSmallHilbertClassField_of_isSmall
    (E : FiniteAbelianExtension K)
    (hE : IsSmallHilbertClassField E) :
    ∀ I : Ideal (𝓞 K),
      (I.map (algebraMap (𝓞 K) (𝓞 E))).IsPrincipal := by
  intro I
  let H := GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K
  let e : E ≃ₐ[K] H := smallHilbertClassFieldEquivOfIsSmall K E hE
  let e𝓞 : 𝓞 E ≃ₐ[𝓞 K] 𝓞 H := ringOfIntegersEquivOfAlgEquiv K E H e
  have hSelected :
      (I.map (algebraMap (𝓞 K) (𝓞 H))).IsPrincipal :=
    ideals_becomePrincipalInSmallHilbertClassField K I
  have hBack :
      ((I.map (algebraMap (𝓞 K) (𝓞 H))).map
        e𝓞.symm.toRingHom).IsPrincipal := by
    obtain ⟨x, hx⟩ := hSelected.principal
    refine ⟨e𝓞.symm x, ?_⟩
    change
      (I.map (algebraMap (𝓞 K) (𝓞 H))).map e𝓞.symm.toRingHom =
        Ideal.span {e𝓞.symm x}
    rw [hx, Ideal.map_span, Set.image_singleton]
    rfl
  have hMap :
      (I.map (algebraMap (𝓞 K) (𝓞 H))).map e𝓞.symm.toRingHom =
        I.map (algebraMap (𝓞 K) (𝓞 E)) := by
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro x
    exact e𝓞.symm.commutes x
  rw [← hMap]
  exact hBack

end HilbertClassFields

end ClassFieldTheory.GlobalClassFieldComparison
