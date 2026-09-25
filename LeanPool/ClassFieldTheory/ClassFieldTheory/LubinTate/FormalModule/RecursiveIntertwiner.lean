/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection
/-!
# Finite-degree approximations to Lubin--Tate intertwiners

For a fixed total degree there are only finitely many monomials.  This file
orders those monomials, applies the coefficient correction from
`RecursiveCorrection` one at a time, and then iterates the resulting
degreewise correction.

The construction is genuinely recursive: stage `n + 1` corrects every
monomial of total degree `n + 2`.  Corrections in that degree leave all lower
coefficients unchanged.  The stabilized coefficient series and its
intertwining equation are established below after the finite-degree
construction.
-/

@[expose] public section

noncomputable
section

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {pi : F.valuationSubring}
variable {sigma : Type w} [Fintype sigma]

/-- The prescribed linear form itself has the prescribed linear term. -/
theorem linearForm_hasLinearTerm
    (L : sigma → F.valuationSubring) :
    HasLinearTerm (linearForm L) L := by
  simp [HasLinearTerm]

/-- Formal series with the prescribed linear term. -/
abbrev Approximation
    (L : sigma → F.valuationSubring) :=
  {H : MvPowerSeries sigma F.valuationSubring // HasLinearTerm H L}

/-- The finite list of all monomials of a fixed total degree. -/
noncomputable def degreeIndexList (m : ℕ) :
    List {d : sigma →₀ ℕ // d.degree = m} :=
  letI : Fintype {d : sigma →₀ ℕ // d.degree = m} :=
    (Finsupp.finite_of_degree_eq m).fintype
  Finset.univ.toList

private theorem degreeIndexList_nodup (m : ℕ) :
    (degreeIndexList (sigma := sigma) m).Nodup := by
  classical
  simp [degreeIndexList, Finset.nodup_toList]

private theorem mem_degreeIndexList
    (m : ℕ) (d : {d : sigma →₀ ℕ // d.degree = m}) :
    d ∈ degreeIndexList (sigma := sigma) m := by
  classical
  simp [degreeIndexList]

/-- One step in a fixed-degree correction list, bundled with preservation of
the prescribed linear term. -/
noncomputable def correctionStep
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (H : Approximation (F := F) L)
    (d : {d : sigma →₀ ℕ // d.degree = m}) :
    Approximation (F := F) L := by
  have hd : 2 ≤ d.1.degree := by
    simpa only [d.2] using hm
  exact
    ⟨correctedIntertwiner hpi e ebar H.2 d.1 hd,
      correctedIntertwiner_hasLinearTerm hpi e ebar H.2 d.1 hd⟩

/-- Apply a list of fixed-degree monomial corrections from left to right. -/
noncomputable def correctList
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : Approximation (F := F) L) :
    Approximation (F := F) L :=
  ds.foldl (correctionStep hpi e ebar hm) H

private theorem coeff_correctionStep_eq_of_degree_lt
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (H : Approximation (F := F) L)
    (d : {d : sigma →₀ ℕ // d.degree = m})
    (q : sigma →₀ ℕ) (hq : q.degree < m) :
    MvPowerSeries.coeff q (correctionStep hpi e ebar hm H d).1 =
      MvPowerSeries.coeff q H.1 := by
  have hqd : q ≠ d.1 := by
    intro h
    have hdegree : q.degree = d.1.degree :=
      congrArg (fun x : sigma →₀ ℕ => x.degree) h
    rw [d.2] at hdegree
    omega
  simp only [correctionStep, correctedIntertwiner,
    monomialCorrection, map_add,
    MvPowerSeries.coeff_monomial_ne hqd, add_zero]

private theorem coeff_correctList_eq_of_degree_lt
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : Approximation (F := F) L)
    (q : sigma →₀ ℕ) (hq : q.degree < m) :
    MvPowerSeries.coeff q (correctList hpi e ebar hm ds H).1 =
      MvPowerSeries.coeff q H.1 := by
  induction ds generalizing H with
  | nil => rfl
  | cons d ds ih =>
      calc
        MvPowerSeries.coeff q
              (correctList hpi e ebar hm (d :: ds) H).1 =
            MvPowerSeries.coeff q
              (correctList hpi e ebar hm ds
                (correctionStep hpi e ebar hm H d)).1 := by
              rfl
        _ = MvPowerSeries.coeff q
              (correctionStep hpi e ebar hm H d).1 :=
          ih (correctionStep hpi e ebar hm H d)
        _ = MvPowerSeries.coeff q H.1 :=
          coeff_correctionStep_eq_of_degree_lt
            hpi e ebar hm H d q hq

private theorem coeff_defect_correctionStep_eq_of_ne
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (H : Approximation (F := F) L)
    (q d : {d : sigma →₀ ℕ // d.degree = m})
    (hqd : q ≠ d) :
    MvPowerSeries.coeff q.1
        (defect e ebar (correctionStep hpi e ebar hm H d).1) =
      MvPowerSeries.coeff q.1 (defect e ebar H.1) := by
  have hval : q.1 ≠ d.1 := by
    intro h
    exact hqd (Subtype.ext h)
  change
    MvPowerSeries.coeff q.1
        (defect e ebar
          (H.1 + MvPowerSeries.monomial d.1 _)) =
      MvPowerSeries.coeff q.1 (defect e ebar H.1)
  rw [coeff_defect_add_monomial_eq_of_degree_le
    e ebar H.2 q.1 d.1 (by omega) (by omega)]
  simp [hval]

private theorem coeff_defect_correctList_eq_of_not_mem
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : Approximation (F := F) L)
    (q : {d : sigma →₀ ℕ // d.degree = m})
    (hq : q ∉ ds) :
    MvPowerSeries.coeff q.1
        (defect e ebar (correctList hpi e ebar hm ds H).1) =
      MvPowerSeries.coeff q.1 (defect e ebar H.1) := by
  induction ds generalizing H with
  | nil => rfl
  | cons d ds ih =>
      have hqd : q ≠ d := by
        intro h
        apply hq
        simp [h]
      have hqds : q ∉ ds := by
        intro h
        exact hq (List.mem_cons_of_mem d h)
      calc
        MvPowerSeries.coeff q.1
              (defect e ebar
                (correctList hpi e ebar hm (d :: ds) H).1) =
            MvPowerSeries.coeff q.1
              (defect e ebar
                (correctList hpi e ebar hm ds
                  (correctionStep hpi e ebar hm H d)).1) := by
              rfl
        _ = MvPowerSeries.coeff q.1
              (defect e ebar
                (correctionStep hpi e ebar hm H d).1) :=
          ih (correctionStep hpi e ebar hm H d) hqds
        _ = MvPowerSeries.coeff q.1 (defect e ebar H.1) :=
          coeff_defect_correctionStep_eq_of_ne
            hpi e ebar hm H q d hqd

private theorem coeff_defect_correctList_eq_zero_of_mem
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : Approximation (F := F) L)
    (hds : ds.Nodup)
    (q : {d : sigma →₀ ℕ // d.degree = m})
    (hq : q ∈ ds) :
    MvPowerSeries.coeff q.1
        (defect e ebar (correctList hpi e ebar hm ds H).1) = 0 := by
  induction ds generalizing H with
  | nil => simp at hq
  | cons d ds ih =>
      have hdnot : d ∉ ds := (List.nodup_cons.mp hds).1
      have hds' : ds.Nodup := (List.nodup_cons.mp hds).2
      by_cases hqd : q = d
      · subst q
        calc
          MvPowerSeries.coeff d.1
                (defect e ebar
                  (correctList hpi e ebar hm (d :: ds) H).1) =
              MvPowerSeries.coeff d.1
                (defect e ebar
                  (correctList hpi e ebar hm ds
                    (correctionStep hpi e ebar hm H d)).1) := by
                rfl
          _ = MvPowerSeries.coeff d.1
                (defect e ebar
                  (correctionStep hpi e ebar hm H d).1) :=
            coeff_defect_correctList_eq_of_not_mem
              hpi e ebar hm ds
                (correctionStep hpi e ebar hm H d) d hdnot
          _ = 0 := by
            change
              MvPowerSeries.coeff d.1
                (defect e ebar
                  (correctedIntertwiner hpi e ebar H.2 d.1 _)) = 0
            exact
              coeff_defect_correctedIntertwiner_eq_zero
                hpi e ebar H.2 d.1 (by omega)
      · have hqds : q ∈ ds := by
          exact (List.mem_cons.mp hq).resolve_left hqd
        change
          MvPowerSeries.coeff q.1
              (defect e ebar
                (correctList hpi e ebar hm ds
                  (correctionStep hpi e ebar hm H d)).1) = 0
        exact
          ih (correctionStep hpi e ebar hm H d) hds' hqds

/-- Correct every monomial in one fixed total degree. -/
noncomputable def correctDegree
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    (H : Approximation (F := F) L)
    (m : ℕ) (hm : 2 ≤ m) :
    Approximation (F := F) L :=
  correctList hpi e ebar hm (degreeIndexList (sigma := sigma) m) H

private theorem coeff_correctDegree_eq_of_degree_lt
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    (H : Approximation (F := F) L)
    (m : ℕ) (hm : 2 ≤ m)
    (q : sigma →₀ ℕ) (hq : q.degree < m) :
    MvPowerSeries.coeff q (correctDegree hpi e ebar H m hm).1 =
      MvPowerSeries.coeff q H.1 :=
  coeff_correctList_eq_of_degree_lt
    hpi e ebar hm (degreeIndexList (sigma := sigma) m) H q hq

private theorem coeff_defect_correctDegree_eq_zero
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    (H : Approximation (F := F) L)
    (m : ℕ) (hm : 2 ≤ m)
    (q : sigma →₀ ℕ) (hq : q.degree = m) :
    MvPowerSeries.coeff q
        (defect e ebar (correctDegree hpi e ebar H m hm).1) = 0 := by
  let q' : {d : sigma →₀ ℕ // d.degree = m} := ⟨q, hq⟩
  change
    MvPowerSeries.coeff q'.1
        (defect e ebar
          (correctList hpi e ebar hm
            (degreeIndexList (sigma := sigma) m) H).1) = 0
  exact
    coeff_defect_correctList_eq_zero_of_mem
      hpi e ebar hm (degreeIndexList (sigma := sigma) m) H
        (degreeIndexList_nodup (sigma := sigma) m) q'
        (mem_degreeIndexList (sigma := sigma) m q')

/-- The bundled finite-degree approximations.  Stage zero is the prescribed
linear form, and stage `n + 1` corrects total degree `n + 2`. -/
noncomputable def approximation
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) :
    ℕ → Approximation (F := F) L
  | 0 => ⟨linearForm L, linearForm_hasLinearTerm L⟩
  | n + 1 =>
      correctDegree hpi e ebar
        (approximation hpi e ebar L n) (n + 2) (by omega)

/-- The stage-`n` finite-degree approximation to the intertwiner with linear
term `L`. -/
noncomputable def intertwinerApproximation
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) (n : ℕ) :
    MvPowerSeries sigma F.valuationSubring :=
  (approximation hpi e ebar L n).1

/-- Every finite-degree approximation retains the prescribed linear term. -/
theorem intertwinerApproximation_hasLinearTerm
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) (n : ℕ) :
    HasLinearTerm (intertwinerApproximation hpi e ebar L n) L :=
  (approximation hpi e ebar L n).2

/-- Stage zero is exactly the prescribed linear form. -/
@[simp]
theorem intertwinerApproximation_zero
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) :
    intertwinerApproximation hpi e ebar L 0 = linearForm L :=
  rfl

/-- Passing from stage `n` to stage `n + 1` leaves every coefficient below
total degree `n + 2` unchanged. -/
theorem coeff_intertwinerApproximation_succ_eq_of_degree_lt
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring)
    (n : ℕ) (q : sigma →₀ ℕ) (hq : q.degree < n + 2) :
    MvPowerSeries.coeff q
        (intertwinerApproximation hpi e ebar L (n + 1)) =
      MvPowerSeries.coeff q
        (intertwinerApproximation hpi e ebar L n) := by
  exact
    coeff_correctDegree_eq_of_degree_lt
      hpi e ebar (approximation hpi e ebar L n)
        (n + 2) (by omega) q hq

/-- Stage `n + 1` has zero defect in every coordinate of total degree
`n + 2`. -/
theorem coeff_defect_intertwinerApproximation_succ_eq_zero
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring)
    (n : ℕ) (q : sigma →₀ ℕ) (hq : q.degree = n + 2) :
    MvPowerSeries.coeff q
        (defect e ebar
          (intertwinerApproximation hpi e ebar L (n + 1))) = 0 := by
  exact
    coeff_defect_correctDegree_eq_zero
      hpi e ebar (approximation hpi e ebar L n)
        (n + 2) (by omega) q hq

/-- Once a coefficient lies below the next correction degree, it remains
unchanged at every later finite stage. -/
theorem coeff_intertwinerApproximation_eq_of_le
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring)
    (q : sigma →₀ ℕ) {m n : ℕ} (hmn : m ≤ n)
    (hq : q.degree < m + 2) :
    MvPowerSeries.coeff q
        (intertwinerApproximation hpi e ebar L n) =
      MvPowerSeries.coeff q
        (intertwinerApproximation hpi e ebar L m) := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [
        coeff_intertwinerApproximation_succ_eq_of_degree_lt
          hpi e ebar L n q (by omega)]
      exact ih

/-- The full recursive series takes the coefficient of a monomial of degree
`m` from the first stage which has already corrected degree `m`. -/
noncomputable def recursiveIntertwiner
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) :
    MvPowerSeries sigma F.valuationSubring :=
  fun d =>
    MvPowerSeries.coeff d
      (intertwinerApproximation hpi e ebar L (d.degree - 1))

/-- The defining stabilized-coefficient formula. -/
@[simp]
theorem coeff_recursiveIntertwiner
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) (d : sigma →₀ ℕ) :
    MvPowerSeries.coeff d (recursiveIntertwiner hpi e ebar L) =
      MvPowerSeries.coeff d
        (intertwinerApproximation hpi e ebar L (d.degree - 1)) :=
  rfl

/-- Through degree `n + 1`, the stabilized series agrees with the stage-`n`
finite approximation. -/
theorem coeff_recursiveIntertwiner_eq_intertwinerApproximation
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring)
    (n : ℕ) (d : sigma →₀ ℕ) (hd : d.degree ≤ n + 1) :
    MvPowerSeries.coeff d (recursiveIntertwiner hpi e ebar L) =
      MvPowerSeries.coeff d
        (intertwinerApproximation hpi e ebar L n) := by
  rw [coeff_recursiveIntertwiner]
  symm
  exact
    coeff_intertwinerApproximation_eq_of_le
      hpi e ebar L d (by omega) (by omega)

/-- The stabilized recursive series retains the prescribed linear term. -/
theorem recursiveIntertwiner_hasLinearTerm
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) :
    HasLinearTerm (recursiveIntertwiner hpi e ebar L) L := by
  rw [HasLinearTerm]
  apply MvPowerSeries.nat_le_order
  intro d hd
  have hdNat : d.degree < 2 := by
    exact_mod_cast hd
  rw [map_sub,
    coeff_recursiveIntertwiner_eq_intertwinerApproximation
      hpi e ebar L 0 d (by omega),
    intertwinerApproximation_zero,
    sub_self]

/-- Every coefficient of the defect of the stabilized recursive series
vanishes. -/
theorem coeff_defect_recursiveIntertwiner_eq_zero
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring)
    (d : sigma →₀ ℕ) :
    MvPowerSeries.coeff d
        (defect e ebar (recursiveIntertwiner hpi e ebar L)) = 0 := by
  by_cases hd : d.degree < 2
  · have hlt :
        (d.degree : ℕ∞) <
          (defect e ebar (recursiveIntertwiner hpi e ebar L)).order := by
      have hd' : (d.degree : ℕ∞) < (2 : ℕ∞) := by
        exact_mod_cast hd
      exact
        hd'.trans_le
          (two_le_order_defect e ebar
            (recursiveIntertwiner_hasLinearTerm hpi e ebar L))
    exact MvPowerSeries.coeff_of_lt_order hlt
  · let n := d.degree - 2
    have hdegree : d.degree = n + 2 := by
      dsimp only [n]
      omega
    have hcoeff :
        ∀ q : sigma →₀ ℕ, q.degree ≤ d.degree →
          MvPowerSeries.coeff q
              (recursiveIntertwiner hpi e ebar L) =
            MvPowerSeries.coeff q
              (intertwinerApproximation hpi e ebar L (n + 1)) := by
      intro q hq
      apply
        coeff_recursiveIntertwiner_eq_intertwinerApproximation
          hpi e ebar L (n + 1) q
      omega
    have hstable :=
      coeff_defect_eq_of_coeff_eq_degree_le
        e ebar
        (recursiveIntertwiner_hasLinearTerm
          hpi e ebar L).constantCoeff_eq_zero
        (intertwinerApproximation_hasLinearTerm
          hpi e ebar L (n + 1)).constantCoeff_eq_zero
        (m := d.degree) hcoeff (d := d) (by rfl)
    rw [hstable]
    exact
      coeff_defect_intertwinerApproximation_succ_eq_zero
        hpi e ebar L n d hdegree

/-- The stabilized recursive series solves the same-uniformizer
Lubin--Tate intertwining equation. -/
theorem recursiveIntertwiner_intertwines
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) :
    Intertwines e ebar (recursiveIntertwiner hpi e ebar L) := by
  rw [intertwines_iff_defect_eq_zero]
  apply MvPowerSeries.ext
  intro d
  exact coeff_defect_recursiveIntertwiner_eq_zero hpi e ebar L d

private theorem hasLinearTerm_add_monomial
    {H : MvPowerSeries sigma F.valuationSubring}
    {L : sigma → F.valuationSubring}
    (hH : HasLinearTerm H L)
    (d : sigma →₀ ℕ) (hd : 2 ≤ d.degree)
    (c : F.valuationSubring) :
    HasLinearTerm (H + MvPowerSeries.monomial d c) L := by
  rw [HasLinearTerm]
  have hmonomial :
      (2 : ℕ∞) ≤ (MvPowerSeries.monomial d c).order := by
    apply MvPowerSeries.nat_le_order
    intro q hq
    have hqNat : q.degree < 2 := by
      exact_mod_cast hq
    have hqd : q ≠ d := by
      intro h
      have hdegree :=
        congrArg (fun x : sigma →₀ ℕ => x.degree) h
      omega
    rw [MvPowerSeries.coeff_monomial_ne hqd]
  rw [show
    H + MvPowerSeries.monomial d c - linearForm L =
      (H - linearForm L) + MvPowerSeries.monomial d c by ring]
  exact
    (le_min hH hmonomial).trans
      MvPowerSeries.min_order_le_add

/-- Replace one coefficient in a fixed total degree by the corresponding
coefficient of a target series. -/
private noncomputable def replacementStep
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : Approximation (F := F) L)
    (d : {d : sigma →₀ ℕ // d.degree = m}) :
    Approximation (F := F) L :=
  ⟨H.1 + MvPowerSeries.monomial d.1
      (MvPowerSeries.coeff d.1 target -
        MvPowerSeries.coeff d.1 H.1),
    hasLinearTerm_add_monomial H.2 d.1 (by omega)
      (MvPowerSeries.coeff d.1 target -
        MvPowerSeries.coeff d.1 H.1)⟩

/-- Replace the coefficients indexed by a list in a fixed total degree. -/
private noncomputable def replaceList
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : Approximation (F := F) L) :
    Approximation (F := F) L :=
  ds.foldl (replacementStep hm target) H

private theorem coeff_replacementStep_self
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : Approximation (F := F) L)
    (d : {d : sigma →₀ ℕ // d.degree = m}) :
    MvPowerSeries.coeff d.1 (replacementStep hm target H d).1 =
      MvPowerSeries.coeff d.1 target := by
  simp [replacementStep, MvPowerSeries.coeff_monomial_same]

private theorem coeff_replacementStep_eq_of_ne
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : Approximation (F := F) L)
    (q d : {d : sigma →₀ ℕ // d.degree = m})
    (hqd : q ≠ d) :
    MvPowerSeries.coeff q.1 (replacementStep hm target H d).1 =
      MvPowerSeries.coeff q.1 H.1 := by
  have hval : q.1 ≠ d.1 := by
    intro h
    exact hqd (Subtype.ext h)
  simp [replacementStep, MvPowerSeries.coeff_monomial_ne hval]

private theorem coeff_replaceList_eq_of_degree_lt
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : Approximation (F := F) L)
    (q : sigma →₀ ℕ) (hq : q.degree < m) :
    MvPowerSeries.coeff q (replaceList hm target ds H).1 =
      MvPowerSeries.coeff q H.1 := by
  induction ds generalizing H with
  | nil => rfl
  | cons d ds ih =>
      have hqd : q ≠ d.1 := by
        intro h
        have hdegree :=
          congrArg (fun x : sigma →₀ ℕ => x.degree) h
        omega
      calc
        MvPowerSeries.coeff q
              (replaceList hm target (d :: ds) H).1 =
            MvPowerSeries.coeff q
              (replaceList hm target ds
                (replacementStep hm target H d)).1 := by
              rfl
        _ = MvPowerSeries.coeff q
              (replacementStep hm target H d).1 :=
          ih (replacementStep hm target H d)
        _ = MvPowerSeries.coeff q H.1 := by
          simp [replacementStep,
            MvPowerSeries.coeff_monomial_ne hqd]

private theorem coeff_replaceList_eq_of_not_mem
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : Approximation (F := F) L)
    (q : {d : sigma →₀ ℕ // d.degree = m})
    (hq : q ∉ ds) :
    MvPowerSeries.coeff q.1 (replaceList hm target ds H).1 =
      MvPowerSeries.coeff q.1 H.1 := by
  induction ds generalizing H with
  | nil => rfl
  | cons d ds ih =>
      have hqd : q ≠ d := by
        intro h
        apply hq
        simp [h]
      have hqds : q ∉ ds := by
        intro h
        exact hq (List.mem_cons_of_mem d h)
      calc
        MvPowerSeries.coeff q.1
              (replaceList hm target (d :: ds) H).1 =
            MvPowerSeries.coeff q.1
              (replaceList hm target ds
                (replacementStep hm target H d)).1 := by
              rfl
        _ = MvPowerSeries.coeff q.1
              (replacementStep hm target H d).1 :=
          ih (replacementStep hm target H d) hqds
        _ = MvPowerSeries.coeff q.1 H.1 :=
          coeff_replacementStep_eq_of_ne
            hm target H q d hqd

private theorem coeff_replaceList_eq_target_of_mem
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : Approximation (F := F) L)
    (hds : ds.Nodup)
    (q : {d : sigma →₀ ℕ // d.degree = m})
    (hq : q ∈ ds) :
    MvPowerSeries.coeff q.1 (replaceList hm target ds H).1 =
      MvPowerSeries.coeff q.1 target := by
  induction ds generalizing H with
  | nil => simp at hq
  | cons d ds ih =>
      have hdnot : d ∉ ds := (List.nodup_cons.mp hds).1
      have hds' : ds.Nodup := (List.nodup_cons.mp hds).2
      by_cases hqd : q = d
      · subst q
        calc
          MvPowerSeries.coeff d.1
                (replaceList hm target (d :: ds) H).1 =
              MvPowerSeries.coeff d.1
                (replaceList hm target ds
                  (replacementStep hm target H d)).1 := by
                rfl
          _ = MvPowerSeries.coeff d.1
                (replacementStep hm target H d).1 :=
            coeff_replaceList_eq_of_not_mem
              hm target ds (replacementStep hm target H d) d hdnot
          _ = MvPowerSeries.coeff d.1 target :=
            coeff_replacementStep_self hm target H d
      · have hqds : q ∈ ds :=
          (List.mem_cons.mp hq).resolve_left hqd
        change
          MvPowerSeries.coeff q.1
              (replaceList hm target ds
                (replacementStep hm target H d)).1 =
            MvPowerSeries.coeff q.1 target
        exact
          ih (replacementStep hm target H d) hds' hqds

private theorem coeff_defect_replacementStep_eq_of_ne
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : Approximation (F := F) L)
    (q d : {d : sigma →₀ ℕ // d.degree = m})
    (hqd : q ≠ d) :
    MvPowerSeries.coeff q.1
        (defect e ebar (replacementStep hm target H d).1) =
      MvPowerSeries.coeff q.1 (defect e ebar H.1) := by
  have hval : q.1 ≠ d.1 := by
    intro h
    exact hqd (Subtype.ext h)
  change
    MvPowerSeries.coeff q.1
        (defect e ebar
          (H.1 + MvPowerSeries.monomial d.1 _)) =
      MvPowerSeries.coeff q.1 (defect e ebar H.1)
  rw [coeff_defect_add_monomial_eq_of_degree_le
    e ebar H.2 q.1 d.1 (by omega) (by omega)]
  simp [hval]

private theorem coeff_defect_replaceList_eq_of_not_mem
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : Approximation (F := F) L)
    (q : {d : sigma →₀ ℕ // d.degree = m})
    (hq : q ∉ ds) :
    MvPowerSeries.coeff q.1
        (defect e ebar (replaceList hm target ds H).1) =
      MvPowerSeries.coeff q.1 (defect e ebar H.1) := by
  induction ds generalizing H with
  | nil => rfl
  | cons d ds ih =>
      have hqd : q ≠ d := by
        intro h
        apply hq
        simp [h]
      have hqds : q ∉ ds := by
        intro h
        exact hq (List.mem_cons_of_mem d h)
      calc
        MvPowerSeries.coeff q.1
              (defect e ebar
                (replaceList hm target (d :: ds) H).1) =
            MvPowerSeries.coeff q.1
              (defect e ebar
                (replaceList hm target ds
                  (replacementStep hm target H d)).1) := by
              rfl
        _ = MvPowerSeries.coeff q.1
              (defect e ebar
                (replacementStep hm target H d).1) :=
          ih (replacementStep hm target H d) hqds
        _ = MvPowerSeries.coeff q.1
              (defect e ebar H.1) :=
          coeff_defect_replacementStep_eq_of_ne
            e ebar hm target H q d hqd

private theorem coeff_defect_replaceList_of_mem
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : Approximation (F := F) L)
    (hds : ds.Nodup)
    (q : {d : sigma →₀ ℕ // d.degree = m})
    (hq : q ∈ ds) :
    MvPowerSeries.coeff q.1
        (defect e ebar (replaceList hm target ds H).1) =
      MvPowerSeries.coeff q.1 (defect e ebar H.1) +
        pi * ((1 - pi ^ (m - 1)) *
          (MvPowerSeries.coeff q.1 target -
            MvPowerSeries.coeff q.1 H.1)) := by
  induction ds generalizing H with
  | nil => simp at hq
  | cons d ds ih =>
      have hdnot : d ∉ ds := (List.nodup_cons.mp hds).1
      have hds' : ds.Nodup := (List.nodup_cons.mp hds).2
      by_cases hqd : q = d
      · subst q
        have htail :
            MvPowerSeries.coeff d.1
                (defect e ebar
                  (replaceList hm target ds
                    (replacementStep hm target H d)).1) =
              MvPowerSeries.coeff d.1
                (defect e ebar
                  (replacementStep hm target H d).1) := by
          exact
            coeff_defect_replaceList_eq_of_not_mem
              e ebar hm target ds
                (replacementStep hm target H d) d hdnot
        calc
          MvPowerSeries.coeff d.1
                (defect e ebar
                  (replaceList hm target (d :: ds) H).1) =
              MvPowerSeries.coeff d.1
                (defect e ebar
                  (replacementStep hm target H d).1) := by
                rw [show
                  replaceList hm target (d :: ds) H =
                    replaceList hm target ds
                      (replacementStep hm target H d) by rfl]
                exact htail
          _ = MvPowerSeries.coeff d.1 (defect e ebar H.1) +
                pi * ((1 - pi ^ (m - 1)) *
                  (MvPowerSeries.coeff d.1 target -
                    MvPowerSeries.coeff d.1 H.1)) := by
            change
              MvPowerSeries.coeff d.1
                  (defect e ebar
                    (H.1 + MvPowerSeries.monomial d.1 _)) =
                _
            rw [coeff_defect_add_monomial_eq_of_degree_le
              e ebar H.2 d.1 d.1 (by rfl) (by omega)]
            simp [d.2]
      · have hqds : q ∈ ds :=
          (List.mem_cons.mp hq).resolve_left hqd
        calc
          MvPowerSeries.coeff q.1
                (defect e ebar
                  (replaceList hm target (d :: ds) H).1) =
              MvPowerSeries.coeff q.1
                (defect e ebar
                  (replaceList hm target ds
                    (replacementStep hm target H d)).1) := by
                rfl
          _ = MvPowerSeries.coeff q.1
                (defect e ebar
                  (replacementStep hm target H d).1) +
              pi * ((1 - pi ^ (m - 1)) *
                (MvPowerSeries.coeff q.1 target -
                  MvPowerSeries.coeff q.1
                    (replacementStep hm target H d).1)) :=
            ih (replacementStep hm target H d) hds' hqds
          _ = MvPowerSeries.coeff q.1 (defect e ebar H.1) +
              pi * ((1 - pi ^ (m - 1)) *
                (MvPowerSeries.coeff q.1 target -
                  MvPowerSeries.coeff q.1 H.1)) := by
            rw [
              coeff_defect_replacementStep_eq_of_ne
                e ebar hm target H q d hqd,
              coeff_replacementStep_eq_of_ne
                hm target H q d hqd]

/-- Replace every coefficient of one total degree by the corresponding
coefficient of a target series. -/
private noncomputable def replaceDegree
    {L : sigma → F.valuationSubring}
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : Approximation (F := F) L)
    (m : ℕ) (hm : 2 ≤ m) :
    Approximation (F := F) L :=
  replaceList hm target (degreeIndexList (sigma := sigma) m) H

private theorem coeff_replaceDegree_eq_target_of_degree_le
    {L : sigma → F.valuationSubring}
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : Approximation (F := F) L)
    (m : ℕ) (hm : 2 ≤ m)
    (hlower : ∀ q : sigma →₀ ℕ, q.degree < m →
      MvPowerSeries.coeff q H.1 =
        MvPowerSeries.coeff q target)
    (q : sigma →₀ ℕ) (hq : q.degree ≤ m) :
    MvPowerSeries.coeff q (replaceDegree target H m hm).1 =
      MvPowerSeries.coeff q target := by
  by_cases hlt : q.degree < m
  · calc
      MvPowerSeries.coeff q (replaceDegree target H m hm).1 =
          MvPowerSeries.coeff q H.1 :=
        coeff_replaceList_eq_of_degree_lt
          hm target (degreeIndexList (sigma := sigma) m) H q hlt
      _ = MvPowerSeries.coeff q target := hlower q hlt
  · have heq : q.degree = m := by omega
    let q' : {d : sigma →₀ ℕ // d.degree = m} := ⟨q, heq⟩
    exact
      coeff_replaceList_eq_target_of_mem
        hm target (degreeIndexList (sigma := sigma) m) H
          (degreeIndexList_nodup m) q'
          (mem_degreeIndexList m q')

private theorem coeff_defect_replaceDegree
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : Approximation (F := F) L)
    (m : ℕ) (hm : 2 ≤ m)
    (q : sigma →₀ ℕ) (hq : q.degree = m) :
    MvPowerSeries.coeff q
        (defect e ebar (replaceDegree target H m hm).1) =
      MvPowerSeries.coeff q (defect e ebar H.1) +
        pi * ((1 - pi ^ (m - 1)) *
          (MvPowerSeries.coeff q target -
            MvPowerSeries.coeff q H.1)) := by
  let q' : {d : sigma →₀ ℕ // d.degree = m} := ⟨q, hq⟩
  exact
    coeff_defect_replaceList_of_mem
      e ebar hm target (degreeIndexList (sigma := sigma) m) H
        (degreeIndexList_nodup m) q'
        (mem_degreeIndexList m q')

private theorem coeff_eq_linearForm_of_hasLinearTerm
    {H : MvPowerSeries sigma F.valuationSubring}
    {L : sigma → F.valuationSubring}
    (hH : HasLinearTerm H L)
    (d : sigma →₀ ℕ) (hd : d.degree < 2) :
    MvPowerSeries.coeff d H =
      MvPowerSeries.coeff d (linearForm L) := by
  have hd' : (d.degree : ℕ∞) < (2 : ℕ∞) := by
    exact_mod_cast hd
  have hzero :=
    MvPowerSeries.coeff_of_lt_order (hd'.trans_le hH)
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- Any intertwiner with a prescribed linear term is the recursively
constructed intertwiner. -/
theorem eq_recursiveIntertwiner_of_hasLinearTerm_of_intertwines
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring)
    {H : MvPowerSeries sigma F.valuationSubring}
    (hH : HasLinearTerm H L)
    (hI : Intertwines e ebar H) :
    H = recursiveIntertwiner hpi e ebar L := by
  let R := recursiveIntertwiner hpi e ebar L
  have hRlin : HasLinearTerm R L :=
    recursiveIntertwiner_hasLinearTerm hpi e ebar L
  have hHdef : defect e ebar H = 0 :=
    (intertwines_iff_defect_eq_zero e ebar H).mp hI
  have hRdef : defect e ebar R = 0 :=
    (intertwines_iff_defect_eq_zero e ebar R).mp
      (recursiveIntertwiner_intertwines hpi e ebar L)
  apply MvPowerSeries.ext
  intro d
  have hall :
      ∀ m : ℕ, ∀ q : sigma →₀ ℕ, q.degree = m →
        MvPowerSeries.coeff q H =
          MvPowerSeries.coeff q R := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro q hq
        by_cases hm : m < 2
        · have hq2 : q.degree < 2 := by omega
          calc
            MvPowerSeries.coeff q H =
                MvPowerSeries.coeff q (linearForm L) :=
              coeff_eq_linearForm_of_hasLinearTerm hH q hq2
            _ = MvPowerSeries.coeff q R :=
              (coeff_eq_linearForm_of_hasLinearTerm
                hRlin q hq2).symm
        · have hm2 : 2 ≤ m := by omega
          let HA : Approximation (F := F) L := ⟨H, hH⟩
          let J := replaceDegree R HA m hm2
          have hlower :
              ∀ r : sigma →₀ ℕ, r.degree < m →
                MvPowerSeries.coeff r H =
                  MvPowerSeries.coeff r R := by
            intro r hr
            exact ih r.degree hr r rfl
          have hthrough :
              ∀ r : sigma →₀ ℕ, r.degree ≤ m →
                MvPowerSeries.coeff r J.1 =
                  MvPowerSeries.coeff r R := by
            intro r hr
            exact
              coeff_replaceDegree_eq_target_of_degree_le
                R HA m hm2 hlower r hr
          have hdefeq :
              MvPowerSeries.coeff q (defect e ebar J.1) =
                MvPowerSeries.coeff q (defect e ebar R) :=
            coeff_defect_eq_of_coeff_eq_degree_le
              e ebar J.2.constantCoeff_eq_zero
                hRlin.constantCoeff_eq_zero
                (m := m) hthrough (d := q) (by omega)
          have hJzero :
              MvPowerSeries.coeff q (defect e ebar J.1) = 0 := by
            rw [hdefeq, hRdef, MvPowerSeries.coeff_zero]
          have hformula :=
            coeff_defect_replaceDegree
              e ebar R HA m hm2 q hq
          have hproduct :
              pi * ((1 - pi ^ (m - 1)) *
                (MvPowerSeries.coeff q R -
                  MvPowerSeries.coeff q H)) = 0 := by
            rw [show J = replaceDegree R HA m hm2 by rfl] at hJzero
            rw [hJzero, hHdef, MvPowerSeries.coeff_zero,
              zero_add] at hformula
            exact hformula.symm
          have hpine : pi ≠ (0 : F.valuationSubring) := by
            intro hp
            apply hpi.ne_zero
            simpa using congrArg
              (fun x : F.valuationSubring => (x : K)) hp
          have hunit :
              IsUnit (1 - pi ^ (m - 1)) :=
            isUnit_one_sub_uniformizer_pow hpi (by omega)
          have hrest :
              (1 - pi ^ (m - 1)) *
                (MvPowerSeries.coeff q R -
                  MvPowerSeries.coeff q H) = 0 :=
            (mul_eq_zero.mp hproduct).resolve_left hpine
          have hdiff :
              MvPowerSeries.coeff q R -
                MvPowerSeries.coeff q H = 0 :=
            (mul_eq_zero.mp hrest).resolve_left hunit.ne_zero
          exact (sub_eq_zero.mp hdiff).symm
  exact hall d.degree d rfl

/-- Two same-uniformizer intertwiners with the same prescribed linear term
are equal. -/
theorem eq_of_hasLinearTerm_of_intertwines
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring)
    {H H' : MvPowerSeries sigma F.valuationSubring}
    (hH : HasLinearTerm H L) (hI : Intertwines e ebar H)
    (hH' : HasLinearTerm H' L) (hI' : Intertwines e ebar H') :
    H = H' :=
  (eq_recursiveIntertwiner_of_hasLinearTerm_of_intertwines
      hpi e ebar L hH hI).trans
    (eq_recursiveIntertwiner_of_hasLinearTerm_of_intertwines
      hpi e ebar L hH' hI').symm

/-- There is a unique same-uniformizer intertwiner with any prescribed
linear term. -/
theorem existsUnique_intertwiner
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) :
    ∃! H : MvPowerSeries sigma F.valuationSubring,
      HasLinearTerm H L ∧ Intertwines e ebar H := by
  refine
    ⟨recursiveIntertwiner hpi e ebar L,
      ⟨recursiveIntertwiner_hasLinearTerm hpi e ebar L,
        recursiveIntertwiner_intertwines hpi e ebar L⟩, ?_⟩
  intro H hH
  exact
    eq_recursiveIntertwiner_of_hasLinearTerm_of_intertwines
      hpi e ebar L hH.1 hH.2

end SameUniformizer
end LubinTate

end
