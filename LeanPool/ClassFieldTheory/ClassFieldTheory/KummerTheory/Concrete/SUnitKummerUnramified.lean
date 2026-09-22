/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.Core
import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SimpleExtensionLocalBehavior
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.CompositumUnramified
/-!
# Unramifiedness of the full `S`-unit Kummer extension

This file supplies the ramification input in the existence proof for the
global norm topology.  Every defining root of

`K(√[n]{Kˢ}) / K`

is first rescaled to the root of an actual `S`-unit.  Its simple
intermediate field is then identified with the chosen simple Kummer
extension attached to that unit.  The finite set of such simple fields
generating the full extension is used to kill the full inertia group away
from `S`.
-/

open scoped NumberField open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open HilbertRamification.Dedekind

noncomputable section

namespace KummerTheory

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
open scoped Classical in
/-- Adjoining an element internally to an intermediate field gives the
same extension as adjoining its ambient value. -/
noncomputable def adjoinSubtypeEquivAmbientAdjoin
    {Omega : Type} [Field Omega] [Algebra K Omega]
    (E : IntermediateField K Omega) (x : E) :
    IntermediateField.adjoin K {x} ≃ₐ[K]
      IntermediateField.adjoin K {(x : Omega)} := by
  exact
    (IntermediateField.equivMap
        (IntermediateField.adjoin K {x}) E.val).trans
      (IntermediateField.equivOfEq
        (by
          rw [IntermediateField.adjoin_map,
            Set.image_singleton]
          rfl))

omit [NumberField K] in
open scoped Classical in
/-- Equality of singleton adjoins in an ambient field descends to equality
of the corresponding singleton adjoins inside an intermediate field. -/
theorem adjoin_subtype_eq_of_adjoin_ambient_eq
    {Omega : Type} [Field Omega] [Algebra K Omega]
    (E : IntermediateField K Omega) (x y : E)
    (h :
      IntermediateField.adjoin K {(x : Omega)} =
        IntermediateField.adjoin K {(y : Omega)}) :
    IntermediateField.adjoin K {x} =
      IntermediateField.adjoin K {y} := by
  apply IntermediateField.map_injective E.val
  calc
    (IntermediateField.adjoin K {x}).map E.val =
        IntermediateField.adjoin K {E.val x} := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    _ = IntermediateField.adjoin K {E.val y} := h
    _ = (IntermediateField.adjoin K {y}).map E.val := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]

omit [NumberField K] in
open scoped Classical in
/-- An arbitrary nonzero root of `X ^ n - b` in the separable closure
generates the same intermediate field as the chosen simple Kummer root,
provided that the base field contains the `n`-th roots of unity. -/
theorem adjoin_rootUnit_eq_chosenSimpleKummerExtension
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ) (alpha : (SeparableClosure K)ˣ)
    (halpha :
      alpha ^ (n : ℕ) =
        Units.map
          (algebraMap K (SeparableClosure K)).toMonoidHom b) :
    IntermediateField.adjoin K
        {(alpha : SeparableClosure K)} =
      chosenSimpleKummerExtension K n hn b := by
  let E := chosenSimpleKummerExtension K n hn b
  have hbE :
      b ∈
        finiteKummerRadicalSubgroup
          (K := K) (L := E) n := by
    exact
      ⟨chosenSimpleKummerRootUnit K n hn b,
        chosenSimpleKummerRootUnit_pow K n hn b⟩
  have halphaRoot :
      (alpha : SeparableClosure K) ∈
        kummerRootSet
          (K := K) (Omega := SeparableClosure K) n
          (finiteKummerRadicalSubgroup
            (K := K) (L := E) n) := by
    refine ⟨⟨b, hbE⟩, ?_⟩
    simpa using congrArg Units.val halpha
  have halphaE : (alpha : SeparableClosure K) ∈ E :=
    kummerRootSet_finiteKummerRadicalSubgroup_le
      E n hmu halphaRoot
  let R :=
    IntermediateField.adjoin K
      {(alpha : SeparableClosure K)}
  let alphaR : Rˣ :=
    Units.mk0
      ⟨(alpha : SeparableClosure K),
        IntermediateField.subset_adjoin K
          {(alpha : SeparableClosure K)}
          (Set.mem_singleton (alpha : SeparableClosure K))⟩
      (by
        intro hzero
        apply alpha.ne_zero
        exact congrArg Subtype.val hzero)
  have hbR :
      b ∈
        finiteKummerRadicalSubgroup
          (K := K) (L := R) n := by
    refine ⟨alphaR, ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa [alphaR] using congrArg Units.val halpha
  have hchosenRoot :
      chosenSimpleKummerRoot K n hn b ∈
        kummerRootSet
          (K := K) (Omega := SeparableClosure K) n
          (finiteKummerRadicalSubgroup
            (K := K) (L := R) n) := by
    exact
      ⟨⟨b, hbR⟩,
        chosenSimpleKummerRoot_pow K n hn b⟩
  have hchosenRootR :
      chosenSimpleKummerRoot K n hn b ∈ R :=
    kummerRootSet_finiteKummerRadicalSubgroup_le
      R n hmu hchosenRoot
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact halphaE
  · change
      IntermediateField.adjoin K
          {chosenSimpleKummerRoot K n hn b} ≤ R
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hchosenRootR

open scoped Classical in
/-- Each defining root of the full `S`-unit Kummer extension generates
the chosen simple Kummer extension belonging to an actual `S`-unit. -/
theorem exists_sUnit_chosenSimpleKummerExtension_eq_adjoin_of_mem_fullRootSet
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {beta : SeparableClosure K}
    (hbeta :
      beta ∈
        kummerRootSet
          (K := K) (Omega := SeparableClosure K) n
          (fullSUnitKummerSubgroup (K := K) n S).1) :
    ∃ u : SUnitGroup (K := K) S,
      IntermediateField.adjoin K {beta} =
        chosenSimpleKummerExtension K n hn u.1 := by
  obtain ⟨u, alpha, halpha, hadjoin⟩ :=
    exists_sUnitRoot_adjoin_eq_of_mem_fullSUnitKummerRootSet
      (K := K) n S hbeta
  refine ⟨u, ?_⟩
  calc
    IntermediateField.adjoin K {beta} =
        IntermediateField.adjoin K
          {(alpha : SeparableClosure K)} :=
      hadjoin.symm
    _ = chosenSimpleKummerExtension K n hn u.1 :=
      adjoin_rootUnit_eq_chosenSimpleKummerExtension
        n hn hmu u.1 alpha halpha

open scoped Classical in
/-- Internal source data for a defining root of the full `S`-unit Kummer
extension.  Inside the simple field generated by the original root, this
produces an actual root of an `S`-unit which still generates the whole
simple field, together with its concrete simple-Kummer model. -/
theorem exists_sUnitRootUnit_generating_internalAdjoin
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (beta : E)
    (hbeta :
      (beta : Omega) ∈
        kummerRootSet
          (K := K) (Omega := Omega) n
          (fullSUnitKummerSubgroup (K := K) n S).1) :
    let B := IntermediateField.adjoin K {beta}
    ∃ (u : SUnitGroup (K := K) S) (alpha : Bˣ)
        (_ : B ≃ₐ[K] chosenSimpleKummerExtension K n hn u.1),
      alpha ^ (n : ℕ) =
          Units.map (algebraMap K B).toMonoidHom u.1 ∧
        IntermediateField.adjoin K {(alpha : B)} = ⊤ := by
  classical
  dsimp only
  let B := IntermediateField.adjoin K {beta}
  obtain ⟨u, alphaOmega, halphaOmega, hadjoinOmega⟩ :=
    exists_sUnitRoot_adjoin_eq_of_mem_fullSUnitKummerRootSet
      (K := K) n S hbeta
  have hbetaAdjoinE :
      IntermediateField.adjoin K {(beta : Omega)} ≤ E := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact beta.property
  have halphaOmegaMem :
      (alphaOmega : Omega) ∈
        IntermediateField.adjoin K {(beta : Omega)} := by
    rw [← hadjoinOmega]
    exact
      IntermediateField.subset_adjoin K
        {(alphaOmega : Omega)}
        (Set.mem_singleton (alphaOmega : Omega))
  let alphaE : Eˣ :=
    Units.mk0
      ⟨(alphaOmega : Omega),
        hbetaAdjoinE halphaOmegaMem⟩
      (by
        intro hzero
        apply alphaOmega.ne_zero
        exact congrArg Subtype.val hzero)
  have hadjoinE :
      IntermediateField.adjoin K {(alphaE : E)} = B := by
    exact
      adjoin_subtype_eq_of_adjoin_ambient_eq
        E (alphaE : E) beta hadjoinOmega
  let alphaB : Bˣ :=
    Units.mk0
      ⟨(alphaE : E), by
        rw [← hadjoinE]
        exact
          IntermediateField.subset_adjoin K
            {(alphaE : E)}
            (Set.mem_singleton (alphaE : E))⟩
      (by
        intro hzero
        apply alphaE.ne_zero
        exact congrArg Subtype.val hzero)
  have halphaOmegaVal :=
    congrArg Units.val halphaOmega
  simp only [Units.val_pow_eq_pow_val,
    Units.coe_map] at halphaOmegaVal
  have halphaB :
      alphaB ^ (n : ℕ) =
        Units.map (algebraMap K B).toMonoidHom u.1 := by
    apply Units.ext
    apply Subtype.ext
    apply Subtype.ext
    simpa [alphaB, alphaE] using halphaOmegaVal
  have hgenerate :
      IntermediateField.adjoin K {(alphaB : B)} = ⊤ := by
    apply IntermediateField.map_injective B.val
    calc
      (IntermediateField.adjoin K {(alphaB : B)}).map B.val =
          IntermediateField.adjoin K
            {B.val (alphaB : B)} := by
        rw [IntermediateField.adjoin_map,
          Set.image_singleton]
      _ = IntermediateField.adjoin K {(alphaE : E)} := by
        rfl
      _ = B := hadjoinE
      _ = B.val.fieldRange :=
        (IntermediateField.fieldRange_val B).symm
      _ = (⊤ : IntermediateField K B).map B.val :=
        (AlgHom.fieldRange_eq_map B.val)
  let eOmega : Omega ≃ₐ[K] SeparableClosure K :=
    IsSepClosure.equiv K Omega (SeparableClosure K)
  let alphaSep : (SeparableClosure K)ˣ :=
    Units.map eOmega.toMonoidHom alphaOmega
  have halphaSep :
      alphaSep ^ (n : ℕ) =
        Units.map
          (algebraMap K (SeparableClosure K)).toMonoidHom u.1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val,
      alphaSep, Units.coe_map]
    rw [← map_pow, halphaOmegaVal]
    exact eOmega.commutes (u.1 : K)
  have hmap :
      (IntermediateField.adjoin K
          {(alphaOmega : Omega)}).map eOmega.toAlgHom =
        IntermediateField.adjoin K
          {(alphaSep : SeparableClosure K)} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hsimple :
      IntermediateField.adjoin K
          {(alphaSep : SeparableClosure K)} =
        chosenSimpleKummerExtension K n hn u.1 :=
    adjoin_rootUnit_eq_chosenSimpleKummerExtension
      n hn hmu u.1 alphaSep halphaSep
  let eAmbient :
      B ≃ₐ[K]
        IntermediateField.adjoin K {(beta : Omega)} :=
    adjoinSubtypeEquivAmbientAdjoin E beta
  let eSimple : B ≃ₐ[K] chosenSimpleKummerExtension K n hn u.1 :=
    eAmbient.trans
      ((IntermediateField.equivOfEq hadjoinOmega.symm).trans
        ((IntermediateField.equivMap
            (IntermediateField.adjoin K {(alphaOmega : Omega)})
            eOmega.toAlgHom).trans
          ((IntermediateField.equivOfEq hmap).trans
            (IntermediateField.equivOfEq hsimple))))
  exact ⟨u, alphaB, eSimple, halphaB, hgenerate⟩

open scoped Classical in
/-- The simple intermediate field generated by any defining root of the
full `S`-unit Kummer extension is Galois over the base field.  The proof
rescales the defining root to an actual `S`-unit root and transports the
concrete simple-Kummer Galois structure across the resulting algebra
equivalence. -/
theorem fullSUnitKummerRoot_internalAdjoin_isGalois
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (beta : E)
    (hbeta :
      (beta : Omega) ∈
        kummerRootSet
          (K := K) (Omega := Omega) n
          (fullSUnitKummerSubgroup (K := K) n S).1) :
    IsGalois K (IntermediateField.adjoin K {beta}) := by
  obtain ⟨u, _, eSimple, _, _⟩ :=
    exists_sUnitRootUnit_generating_internalAdjoin
      (K := K) E n hn hmu S beta hbeta
  let L := chosenSimpleKummerExtension K n hn u.1
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hn u.1
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hn hmu u.1
  exact IsGalois.of_algEquiv eSimple.symm

open scoped Classical in
/-- Away from `S`, and away from the residue characteristics dividing the
exponent, the full `S`-unit Kummer extension is unramified at the chosen
finite completion.  This is proved on the actual full extension: a finite
set of defining roots generates it, every associated simple field is
unramified by the derivative criterion, and restriction kills the full
inertia group. -/
theorem
    fullSUnitKummerExtension_chosenFinitePlaceIsUnramified_of_not_mem
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K))
    (hvS : v ∉ S)
    (hnv : v.valuation K ((n : ℕ) : K) = 1) :
    let E :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S
    letI : FiniteDimensional K E :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hn hmu S
    letI : IsGalois K E :=
      fullSUnitKummerExtension_isGalois
        (K := K) (Omega := Omega) n S
    letI : NumberField E :=
      NumberField.of_module_finite K E
    ChosenFinitePlaceIsUnramified
      (K := K) (L := E) v := by
  classical
  dsimp only
  let E :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S
  let : FiniteDimensional K E :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hn hmu S
  let : IsGalois K E :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S
  let : NumberField E :=
    NumberField.of_module_finite K E
  let w := chosenFinitePlaceExtension (L := E) v
  let Q :=
    finitePlaceExtensionCentre
      (K := K) (L := E) v w
  obtain ⟨T, hTroot, hTgenerate⟩ :=
    exists_finset_fullSUnitKummerExtensionRoots_adjoin_eq_top
      (K := K) (Omega := Omega) n hn hmu S
  have hnormal :
      ∀ x : E, x ∈ T →
        Normal K (IntermediateField.adjoin K {x}) := by
    intro x hx
    let B := IntermediateField.adjoin K {x}
    let : IsGalois K B :=
      fullSUnitKummerRoot_internalAdjoin_isGalois
        (K := K) E n hn hmu S x (hTroot x hx)
    exact inferInstance
  have hsimpleInertia :
      ∀ (x : E) (hx : x ∈ T),
        inertiaGroup
            (Q.asIdeal.under
              (𝓞 (IntermediateField.adjoin K {x})))
            Gal((IntermediateField.adjoin K {x})/K) =
          ⊥ := by
    intro x hx
    let B := IntermediateField.adjoin K {x}
    let : IsGalois K B :=
      fullSUnitKummerRoot_internalAdjoin_isGalois
        (K := K) E n hn hmu S x (hTroot x hx)
    let : NumberField B :=
      NumberField.of_module_finite K B
    obtain ⟨u, alpha, _, halpha, hgenerate⟩ :=
      exists_sUnitRootUnit_generating_internalAdjoin
        (K := K) E n hn hmu S x (hTroot x hx)
    have huvaluation :
        v.valuation K (u.1 : K) = 1 :=
      (mem_SUnitGroup_iff (K := K) S u.1).mp
        u.2 v hvS
    have hunramifiedB :
        ChosenFinitePlaceIsUnramified
          (K := K) (L := B) v :=
      kummerGeneratedExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
        (K := K) n u.1 alpha halpha hgenerate
        v huvaluation hnv
    let P : HeightOneSpectrum (𝓞 B) :=
      finitePlaceBelow (K := B) Q
    have hPbelow :
        finitePlaceBelow (K := K) P = v := by
      calc
        finitePlaceBelow (K := K) P =
            finitePlaceBelow (K := K) Q := by
          exact
            finitePlaceBelow_finitePlaceBelow
              (K := K) (M := B) (L := E) Q
        _ = v :=
          finitePlaceBelow_finitePlaceExtensionCentre
            (K := K) (L := E) v w
    have hunramifiedP :
        Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal :=
      isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
        (K := K) (L := B) v P hPbelow hunramifiedB
    have hIP :
        inertiaGroup P.asIdeal Gal(B/K) = ⊥ :=
      inertiaGroup_eq_bot_of_isUnramifiedAt
        (K := K) (M := B) P.asIdeal hunramifiedP
    simpa only [P, finitePlaceBelow_asIdeal] using hIP
  have hIQ :
      inertiaGroup Q.asIdeal Gal(E/K) = ⊥ :=
    inertiaGroup_eq_bot_of_finset_adjoin_eq_top
      (K := K) (M := E) T Q.asIdeal
      hnormal hsimpleInertia hTgenerate
  have hunramifiedQ :
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal :=
    isUnramifiedAt_of_inertiaGroup_eq_bot
      (K := K) (M := E) Q.asIdeal hIQ
  exact
    chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := E) v
      (by simpa only [Q] using hunramifiedQ)

open scoped Classical in
/-- Every finite prime of the full `S`-unit Kummer extension above a
place outside `S` is unramified, provided the exponent is a unit at the
base place.  This is the ideal-theoretic form of the preceding chosen
completion theorem. -/
theorem
    fullSUnitKummerExtension_isUnramifiedAt_of_below_not_mem
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let E :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S
    letI : FiniteDimensional K E :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hn hmu S
    letI : IsGalois K E :=
      fullSUnitKummerExtension_isGalois
        (K := K) (Omega := Omega) n S
    letI : NumberField E :=
      NumberField.of_module_finite K E
    ∀ P : HeightOneSpectrum (𝓞 E),
      finitePlaceBelow (K := K) P ∉ S →
        (finitePlaceBelow (K := K) P).valuation K
            ((n : ℕ) : K) =
          1 →
        Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal := by
  dsimp only
  let E :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S
  let _ : FiniteDimensional K E :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hn hmu S
  let _ : IsGalois K E :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S
  let _ : NumberField E :=
    NumberField.of_module_finite K E
  intro P hPS hnP
  let v := finitePlaceBelow (K := K) P
  have hunramified :
      ChosenFinitePlaceIsUnramified
        (K := K) (L := E) v := by
    simpa only [E, v] using
      fullSUnitKummerExtension_chosenFinitePlaceIsUnramified_of_not_mem
        (K := K) (Omega := Omega) n hn hmu S v hPS hnP
  exact
    isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
      (K := K) (L := E) v P rfl hunramified

end KummerTheory
