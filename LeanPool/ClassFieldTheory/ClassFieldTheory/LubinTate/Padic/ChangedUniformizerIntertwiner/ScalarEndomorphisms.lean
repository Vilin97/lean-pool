/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.IntertwinerConstruction
/-!
# Completed scalar endomorphisms

This module constructs the completed multiplicative and changed-standard scalar endomorphisms and proves their linear terms, composition laws, Frobenius invariance, and substitution commutation.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

/-- The multiplicative Lubin--Tate scalar endomorphism with coefficient
`a`, after extending coefficients to the completed unramified Witt ring. -/
noncomputable def padicCompletedMultiplicativeScalarEndomorphism
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries (padicCompletedUnramifiedWittRing p) :=
  PowerSeries.map
    (padicValuationSubringToCompletedUnramifiedWittRing p)
    (recursiveIntertwiner
      (padicMultiplicativeLubinTateSeries_isUniformizer p)
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => a))

private theorem padicMultiplicativeScalarEndomorphism_mul
    (p : ℕ) [Fact p.Prime]
    (a b : (padicLocalField p).valuationSubring) :
    recursiveIntertwiner
        (padicMultiplicativeLubinTateSeries_isUniformizer p)
        (padicMultiplicativeLubinTateSeries p)
        (padicMultiplicativeLubinTateSeries p)
        (fun _ : Unit => a * b) =
      PowerSeries.subst
        (recursiveIntertwiner
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          (padicMultiplicativeLubinTateSeries p)
          (padicMultiplicativeLubinTateSeries p)
          (fun _ : Unit => b))
        (recursiveIntertwiner
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          (padicMultiplicativeLubinTateSeries p)
          (padicMultiplicativeLubinTateSeries p)
          (fun _ : Unit => a)) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let E := padicMultiplicativeLubinTateSeries p
  let A :=
    recursiveIntertwiner hπ E E (fun _ : Unit => a)
  let B :=
    recursiveIntertwiner hπ E E (fun _ : Unit => b)
  have hAlinear :=
    recursiveIntertwiner_hasLinearTerm hπ E E
      (fun _ : Unit => a)
  have hBlinear :=
    recursiveIntertwiner_hasLinearTerm hπ E E
      (fun _ : Unit => b)
  have hcomp :=
    hAlinear.subst
      (G := fun _ : Unit => B)
      (M := fun _ : Unit => fun _ : Unit => b)
      (fun _ => hBlinear)
  have hcomp' :
      HasLinearTerm (PowerSeries.subst B A)
        (fun _ : Unit => a * b) := by
    simpa only [A, B, PowerSeries.subst_def, Finset.univ_unique,
      Finset.sum_singleton] using hcomp
  have hIntertwines :=
    (recursiveIntertwiner_intertwines hπ E E
      (fun _ : Unit => a)).powerSeries_subst
        hAlinear.hasSubst
        (recursiveIntertwiner_intertwines hπ E E
          (fun _ : Unit => b))
        hBlinear.hasSubst
  exact
    eq_of_hasLinearTerm_of_intertwines hπ E E
      (fun _ : Unit => a * b)
      (recursiveIntertwiner_hasLinearTerm hπ E E
        (fun _ : Unit => a * b))
      (recursiveIntertwiner_intertwines hπ E E
        (fun _ : Unit => a * b))
      hcomp' hIntertwines

/-- The standard scalar endomorphism for the changed uniformizer `u p`,
after extending coefficients to the completed unramified Witt ring. -/
noncomputable def padicCompletedChangedStandardScalarEndomorphism
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries (padicCompletedUnramifiedWittRing p) :=
  PowerSeries.map
    (padicValuationSubringToCompletedUnramifiedWittRing p)
    (standardLubinTateEndomorphism
      (standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u)
      a)

/-- A one-variable power series with zero constant coefficient and prescribed
coefficient of `X` has the corresponding `HasLinearTerm` predicate. -/
theorem powerSeries_hasLinearTerm_of_constantCoeff_coeff_one
    {R : Type*} [CommRing R]
    (H : PowerSeries R) (a : R)
    (hconstant : PowerSeries.constantCoeff H = 0)
    (hone : PowerSeries.coeff 1 H = a) :
    SameUniformizer.HasLinearTerm H (fun _ : Unit => a) := by
  rw [SameUniformizer.HasLinearTerm]
  apply MvPowerSeries.nat_le_order
  intro d hd
  have hdegree : d.degree = d () :=
    by simp [Finsupp.degree_eq_sum]
  have hd' : d () < 2 := by
    simpa only [hdegree] using hd
  by_cases hd0 : d () = 0
  · have hdeq : d = 0 := by
      apply Finsupp.ext
      intro i
      cases i
      simp [hd0]
    subst d
    simp only [map_sub,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.constantCoeff_eq, hconstant,
      SameUniformizer.constantCoeff_linearForm,
      sub_self]
  · have hd1 : d () = 1 := by omega
    have hdeq : d = Finsupp.single () 1 := by
      apply Finsupp.ext
      intro i
      cases i
      simp [hd1]
    subst d
    change
      PowerSeries.coeff 1 H -
          MvPowerSeries.coeff (Finsupp.single () 1)
            (SameUniformizer.linearForm (fun _ : Unit => a)) =
        0
    rw [hone]
    classical
    simp [SameUniformizer.linearForm]

theorem
    padicCompletedMultiplicativeScalarEndomorphism_constantCoeff
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.constantCoeff
        (padicCompletedMultiplicativeScalarEndomorphism p a) = 0 := by
  have hconstant :=
    (recursiveIntertwiner_hasLinearTerm
      (padicMultiplicativeLubinTateSeries_isUniformizer p)
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => a)).constantCoeff_eq_zero
  change
    padicValuationSubringToCompletedUnramifiedWittRing p
        (PowerSeries.constantCoeff
          (recursiveIntertwiner
            (padicMultiplicativeLubinTateSeries_isUniformizer p)
            (padicMultiplicativeLubinTateSeries p)
            (padicMultiplicativeLubinTateSeries p)
            (fun _ : Unit => a))) = 0
  rw [PowerSeries.constantCoeff_eq, hconstant, map_zero]

@[simp]
theorem padicCompletedMultiplicativeScalarEndomorphism_coeff_one
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.coeff 1
        (padicCompletedMultiplicativeScalarEndomorphism p a) =
      padicValuationSubringToCompletedUnramifiedWittRing p a := by
  rw [padicCompletedMultiplicativeScalarEndomorphism,
    PowerSeries.coeff_map]
  congr 1
  exact
    (recursiveIntertwiner_hasLinearTerm
      (padicMultiplicativeLubinTateSeries_isUniformizer p)
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => a)).coeff_single ()

theorem
    padicCompletedChangedStandardScalarEndomorphism_constantCoeff
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.constantCoeff
        (padicCompletedChangedStandardScalarEndomorphism p u a) = 0 := by
  have hconstant :=
    (standardLubinTateEndomorphism_hasLinearTerm
      (standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u)
      a).constantCoeff_eq_zero
  change
    padicValuationSubringToCompletedUnramifiedWittRing p
        (PowerSeries.constantCoeff
          (standardLubinTateEndomorphism
            (standardLubinTateChangedUniformizer_isUniformizer
              (padicMultiplicativeLubinTateSeries_isUniformizer p) u)
            a)) = 0
  rw [PowerSeries.constantCoeff_eq, hconstant, map_zero]

@[simp]
theorem
    padicCompletedChangedStandardScalarEndomorphism_coeff_one
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.coeff 1
        (padicCompletedChangedStandardScalarEndomorphism p u a) =
      padicValuationSubringToCompletedUnramifiedWittRing p a := by
  rw [padicCompletedChangedStandardScalarEndomorphism,
    PowerSeries.coeff_map,
    standardLubinTateEndomorphism_coeff_one]

private theorem padicMultiplicativeScalarEndomorphism_commutes
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (recursiveIntertwiner
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          (padicMultiplicativeLubinTateSeries p)
          (padicMultiplicativeLubinTateSeries p)
          (fun _ : Unit => a))
        (padicMultiplicativeLubinTateSeries p).toPowerSeries =
      PowerSeries.subst
        (padicMultiplicativeLubinTateSeries p).toPowerSeries
        (recursiveIntertwiner
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          (padicMultiplicativeLubinTateSeries p)
          (padicMultiplicativeLubinTateSeries p)
          (fun _ : Unit => a)) := by
  have h :=
    recursiveIntertwiner_intertwines
      (padicMultiplicativeLubinTateSeries_isUniformizer p)
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => a)
  calc
    _ =
        MvPowerSeries.subst
          (fun i : Unit =>
            inVariable (padicMultiplicativeLubinTateSeries p) i)
          (recursiveIntertwiner
            (padicMultiplicativeLubinTateSeries_isUniformizer p)
            (padicMultiplicativeLubinTateSeries p)
            (padicMultiplicativeLubinTateSeries p)
            (fun _ : Unit => a)) :=
      h
    _ = _ := by
      rw [PowerSeries.subst_def]
      congr 1
      funext i
      cases i
      exact
        PowerSeries.X_subst
          (padicMultiplicativeLubinTateSeries p).toPowerSeries

private theorem padicChangedStandardScalarEndomorphism_commutes
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (standardLubinTateEndomorphism
          (standardLubinTateChangedUniformizer_isUniformizer
            (padicMultiplicativeLubinTateSeries_isUniformizer p) u)
          a)
        (standardLubinTateSeries
          (standardLubinTateChangedUniformizer_isUniformizer
            (padicMultiplicativeLubinTateSeries_isUniformizer p) u)).toPowerSeries =
      PowerSeries.subst
        (standardLubinTateSeries
          (standardLubinTateChangedUniformizer_isUniformizer
            (padicMultiplicativeLubinTateSeries_isUniformizer p) u)).toPowerSeries
        (standardLubinTateEndomorphism
          (standardLubinTateChangedUniformizer_isUniformizer
            (padicMultiplicativeLubinTateSeries_isUniformizer p) u)
          a) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  have h :=
    standardLubinTateEndomorphism_intertwines hπ a
  calc
    _ =
        MvPowerSeries.subst
          (fun i : Unit => inVariable (standardLubinTateSeries hπ) i)
          (standardLubinTateEndomorphism hπ a) :=
      h
    _ = _ := by
      rw [PowerSeries.subst_def]
      congr 1
      funext i
      cases i
      exact PowerSeries.X_subst (standardLubinTateSeries hπ).toPowerSeries

/-- A completed multiplicative scalar endomorphism commutes with the
completed multiplicative Lubin--Tate series under substitution. -/
theorem padicCompletedMultiplicativeScalarEndomorphism_commutes
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (padicCompletedMultiplicativeScalarEndomorphism p a)
        (padicCompletedMultiplicativeSeries p) =
      PowerSeries.subst
        (padicCompletedMultiplicativeSeries p)
        (padicCompletedMultiplicativeScalarEndomorphism p a) := by
  have hscalar :
      PowerSeries.HasSubst
        (recursiveIntertwiner
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          (padicMultiplicativeLubinTateSeries p)
          (padicMultiplicativeLubinTateSeries p)
          (fun _ : Unit => a)) :=
    (recursiveIntertwiner_hasLinearTerm
      (padicMultiplicativeLubinTateSeries_isUniformizer p)
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => a)).hasSubst
  have hseries :
      PowerSeries.HasSubst
        (padicMultiplicativeLubinTateSeries p).toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (padicMultiplicativeLubinTateSeries p).constantCoeff_eq_zero
  have h :=
    congrArg
      (PowerSeries.map
        (padicValuationSubringToCompletedUnramifiedWittRing p))
      (padicMultiplicativeScalarEndomorphism_commutes p a)
  change MvPowerSeries.map _ _ = MvPowerSeries.map _ _ at h
  rw [PowerSeries.map_subst hscalar,
    PowerSeries.map_subst hseries] at h
  change
    PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) =
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) at h
  simpa only [padicCompletedMultiplicativeScalarEndomorphism,
    padicCompletedMultiplicativeSeries] using h

/-- A completed changed-standard scalar endomorphism commutes with the
completed changed-standard series under substitution. -/
theorem padicCompletedChangedStandardScalarEndomorphism_commutes
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (padicCompletedChangedStandardScalarEndomorphism p u a)
        (padicCompletedChangedStandardSeries p u) =
      PowerSeries.subst
        (padicCompletedChangedStandardSeries p u)
        (padicCompletedChangedStandardScalarEndomorphism p u a) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  have hscalar :
      PowerSeries.HasSubst
        (standardLubinTateEndomorphism hπ a) :=
    (standardLubinTateEndomorphism_hasLinearTerm hπ a).hasSubst
  have hseries :
      PowerSeries.HasSubst
        (standardLubinTateSeries hπ).toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (standardLubinTateSeries hπ).constantCoeff_eq_zero
  have h :=
    congrArg
      (PowerSeries.map
        (padicValuationSubringToCompletedUnramifiedWittRing p))
      (padicChangedStandardScalarEndomorphism_commutes p u a)
  change MvPowerSeries.map _ _ = MvPowerSeries.map _ _ at h
  rw [PowerSeries.map_subst hscalar,
    PowerSeries.map_subst hseries] at h
  change
    PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) =
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) at h
  simpa only [padicCompletedChangedStandardScalarEndomorphism,
    padicCompletedChangedStandardSeries] using h

/-- Completed multiplicative scalar endomorphisms are fixed by coefficientwise
Witt-vector Frobenius. -/
theorem padicCompletedMultiplicativeScalarEndomorphism_frobenius
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.map WittVector.frobenius
        (padicCompletedMultiplicativeScalarEndomorphism p a) =
      padicCompletedMultiplicativeScalarEndomorphism p a := by
  apply PowerSeries.ext
  intro n
  simp [padicCompletedMultiplicativeScalarEndomorphism,
    PowerSeries.coeff_map,
    padicValuationSubringToCompletedUnramifiedWittRing_frobenius]

/-- Completed changed-standard scalar endomorphisms are fixed by
coefficientwise Witt-vector Frobenius. -/
theorem padicCompletedChangedStandardScalarEndomorphism_frobenius
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.map WittVector.frobenius
        (padicCompletedChangedStandardScalarEndomorphism p u a) =
      padicCompletedChangedStandardScalarEndomorphism p u a := by
  apply PowerSeries.ext
  intro n
  simp [padicCompletedChangedStandardScalarEndomorphism,
    PowerSeries.coeff_map,
    padicValuationSubringToCompletedUnramifiedWittRing_frobenius]

/-- The completed multiplicative series is fixed by coefficientwise
Witt-vector Frobenius. -/
theorem padicCompletedMultiplicativeSeries_frobenius
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.map WittVector.frobenius
        (padicCompletedMultiplicativeSeries p) =
      padicCompletedMultiplicativeSeries p := by
  apply PowerSeries.ext
  intro n
  simp [padicCompletedMultiplicativeSeries]

/-- The completed changed-standard series is fixed by coefficientwise
Witt-vector Frobenius. -/
theorem padicCompletedChangedStandardSeries_frobenius
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.map WittVector.frobenius
        (padicCompletedChangedStandardSeries p u) =
      padicCompletedChangedStandardSeries p u := by
  apply PowerSeries.ext
  intro n
  simp [padicCompletedChangedStandardSeries,
    PowerSeries.coeff_map,
    padicValuationSubringToCompletedUnramifiedWittRing_frobenius]

theorem
    padicCompletedMultiplicativeScalarEndomorphism_hasLinearTerm
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    HasLinearTerm
        (padicCompletedMultiplicativeScalarEndomorphism p a)
        (fun _ : Unit =>
          padicValuationSubringToCompletedUnramifiedWittRing p a) :=
  powerSeries_hasLinearTerm_of_constantCoeff_coeff_one
    (padicCompletedMultiplicativeScalarEndomorphism p a)
    (padicValuationSubringToCompletedUnramifiedWittRing p a)
    (padicCompletedMultiplicativeScalarEndomorphism_constantCoeff p a)
    (padicCompletedMultiplicativeScalarEndomorphism_coeff_one p a)

/-- Every completed multiplicative scalar endomorphism admits formal
substitution. -/
theorem padicCompletedMultiplicativeScalarEndomorphism_hasSubst
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.HasSubst
      (padicCompletedMultiplicativeScalarEndomorphism p a) :=
  (padicCompletedMultiplicativeScalarEndomorphism_hasLinearTerm p a).hasSubst

/-- Multiplication of p-adic scalars is composition of their completed
multiplicative Lubin--Tate endomorphisms. -/
theorem padicCompletedMultiplicativeScalarEndomorphism_mul
    (p : ℕ) [Fact p.Prime]
    (a b : (padicLocalField p).valuationSubring) :
    padicCompletedMultiplicativeScalarEndomorphism p (a * b) =
      PowerSeries.subst
        (padicCompletedMultiplicativeScalarEndomorphism p b)
        (padicCompletedMultiplicativeScalarEndomorphism p a) := by
  have h :=
    congrArg
      (PowerSeries.map
        (padicValuationSubringToCompletedUnramifiedWittRing p))
      (padicMultiplicativeScalarEndomorphism_mul p a b)
  change MvPowerSeries.map _ _ = MvPowerSeries.map _ _ at h
  rw [PowerSeries.map_subst
    (recursiveIntertwiner_hasLinearTerm
      (padicMultiplicativeLubinTateSeries_isUniformizer p)
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => b)).hasSubst] at h
  change
    PowerSeries.map _ _ =
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) at h
  simpa only [padicCompletedMultiplicativeScalarEndomorphism] using h

theorem
    padicCompletedChangedStandardScalarEndomorphism_hasLinearTerm
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    HasLinearTerm
        (padicCompletedChangedStandardScalarEndomorphism p u a)
        (fun _ : Unit =>
          padicValuationSubringToCompletedUnramifiedWittRing p a) :=
  powerSeries_hasLinearTerm_of_constantCoeff_coeff_one
    (padicCompletedChangedStandardScalarEndomorphism p u a)
    (padicValuationSubringToCompletedUnramifiedWittRing p a)
    (padicCompletedChangedStandardScalarEndomorphism_constantCoeff p u a)
    (padicCompletedChangedStandardScalarEndomorphism_coeff_one p u a)

/-- Every completed changed-standard scalar endomorphism admits formal
substitution. -/
theorem padicCompletedChangedStandardScalarEndomorphism_hasSubst
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.HasSubst
      (padicCompletedChangedStandardScalarEndomorphism p u a) :=
  (padicCompletedChangedStandardScalarEndomorphism_hasLinearTerm
    p u a).hasSubst

/-- The changed uniformizer itself acts by the defining completed changed
standard Lubin--Tate series. -/
theorem padicCompletedChangedStandardScalarEndomorphism_uniformizer
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedChangedStandardScalarEndomorphism p u
        (standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) =
      padicCompletedChangedStandardSeries p u := by
  rw [padicCompletedChangedStandardScalarEndomorphism,
    padicCompletedChangedStandardSeries,
    SameUniformizer.standardLubinTateEndomorphism_uniformizer]

/-- Multiplication of changed-standard scalars is composition after
completed coefficient extension. -/
theorem padicCompletedChangedStandardScalarEndomorphism_mul
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a b : (padicLocalField p).valuationSubring) :
    padicCompletedChangedStandardScalarEndomorphism p u (a * b) =
      PowerSeries.subst
        (padicCompletedChangedStandardScalarEndomorphism p u b)
        (padicCompletedChangedStandardScalarEndomorphism p u a) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  have h :=
    congrArg
      (PowerSeries.map
        (padicValuationSubringToCompletedUnramifiedWittRing p))
      (standardLubinTateEndomorphism_mul hπ a b)
  change MvPowerSeries.map _ _ = MvPowerSeries.map _ _ at h
  rw [PowerSeries.map_subst
    (standardLubinTateEndomorphism_hasLinearTerm hπ b).hasSubst] at h
  change
    PowerSeries.map _ _ =
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) at h
  simpa only [padicCompletedChangedStandardScalarEndomorphism] using h

/-- The scalar `1` acts by the identity changed-standard series. -/
@[simp]
theorem padicCompletedChangedStandardScalarEndomorphism_one
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedChangedStandardScalarEndomorphism p u 1 =
      PowerSeries.X := by
  rw [padicCompletedChangedStandardScalarEndomorphism,
    standardLubinTateEndomorphism_one, PowerSeries.map_X]

end LubinTate

end
