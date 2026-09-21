/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.Basic
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.Basic
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.RHS
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.DiscountBounds
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.Definitions

/-! # Additivity Defects -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory
open scoped BigOperators

/-!
# Response-defect expectation conversion

This file contains the proof-internal expectation conversion for the
response-defect baseline sums in the third Section 5.3 lemma.
-/

noncomputable section

/-- The weak-norm maximizer response-defect observable is the same
parent/descendant response defect used in the first Section 5.3 lemma. -/
private theorem responseDefectAverageAtScale_eq_responseJAdditivityDefectAtScale
    {d : ℕ} [NeZero d] (m n : ℤ) (p q : Vec d) (a : RegCoeffField d) :
    WeakNormsMaximizer.responseDefectAverageAtScale m n p q a =
      JUpperBoundWeakNorms.responseJAdditivityDefectAtScale m n p q a := by
  rfl

/-- Integrability of the response defect in the notation of the weak-norm
maximizer RHS. -/
private theorem integrable_responseDefectAverageAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {n m : ℤ} (hnm : n ≤ m) (p q : Vec d)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDesc : ∀ R, R ∈ descendantsAtScale (originCube d m) n →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    Integrable (WeakNormsMaximizer.responseDefectAverageAtScale m n p q) P := by
  exact JUpperBoundWeakNorms.integrable_responseJAdditivityDefectAtScale
      hnm p q hParent hDesc

/-- A.e. nonnegativity of the response defect in the notation of the
weak-norm maximizer RHS. -/
private theorem responseDefectAverageAtScale_nonneg_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) {n m : ℤ} (hnm : n ≤ m) (p q : Vec d) :
    0 ≤ᵐ[P] WeakNormsMaximizer.responseDefectAverageAtScale m n p q := by
  exact JUpperBoundWeakNorms.responseJAdditivityDefectAtScale_nonneg_ae
      hP hnm p q

/-- Law-facing tau conversion for the response defect as it appears in the
weak-norm maximizer RHS. -/
private theorem integral_responseDefectAverageAtScale_eq_tauAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {n m : ℤ} (hn_nonneg : 0 ≤ n) (hnm : n ≤ m) (p q : Vec d)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDesc : ∀ R, R ∈ descendantsAtScale (originCube d m) n →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    ∫ a, WeakNormsMaximizer.responseDefectAverageAtScale m n p q a ∂P =
      tauAtScale P m n p q := by
  simpa [responseDefectAverageAtScale_eq_responseJAdditivityDefectAtScale] using
    JUpperBoundWeakNorms.integral_responseJAdditivityDefectAtScale_eq_tauAtScale
      hP hstat hn_nonneg hnm p q hParent hDesc

private theorem int_mem_Icc_succ_right_nonneg_and_le
    {k m n : ℤ} (hk : 0 ≤ k) (hn : n ∈ Finset.Icc (k + 1) m) :
    0 ≤ n ∧ n ≤ m := by
  have hn_low : k + 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn_high : n ≤ m := (Finset.mem_Icc.mp hn).2
  constructor
  · linarith
  · exact hn_high

private theorem sum_range_to_Icc_descending {k m : ℤ} (hkm : k ≤ m)
    (F : ℕ → ℝ) :
    (∑ j ∈ Finset.range (Int.toNat (m - k)), F j) =
      ∑ n ∈ Finset.Icc (k + 1) m, F (Int.toNat (m - n)) := by
  classical
  refine Finset.sum_bij (fun j _hj => m - (j : ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    have hL : ((Int.toNat (m - k) : ℕ) : ℤ) = m - k :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
    have hj_lt_nat : j < Int.toNat (m - k) := Finset.mem_range.mp hj
    have hj_lt : (j : ℤ) < m - k := by
      have hj_lt' : (j : ℤ) < ((Int.toNat (m - k) : ℕ) : ℤ) := by
        exact_mod_cast hj_lt_nat
      simpa [hL] using hj_lt'
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · intro j₁ _hj₁ j₂ _hj₂ h
    have h' : m - (j₁ : ℤ) = m - (j₂ : ℤ) := by simpa using h
    have hcast : (j₁ : ℤ) = (j₂ : ℤ) := by omega
    exact_mod_cast hcast
  · intro n hn
    have hn_low : k + 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn_high : n ≤ m := (Finset.mem_Icc.mp hn).2
    refine ⟨Int.toNat (m - n), ?_, ?_⟩
    · have hL : ((Int.toNat (m - k) : ℕ) : ℤ) = m - k :=
        Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
      have hmn_nonneg : 0 ≤ m - n := sub_nonneg.mpr hn_high
      have hmn_lt : m - n < m - k := by omega
      have hto : ((Int.toNat (m - n) : ℕ) : ℤ) = m - n :=
        Int.toNat_of_nonneg hmn_nonneg
      apply Finset.mem_range.mpr
      have hcast : ((Int.toNat (m - n) : ℕ) : ℤ) <
          ((Int.toNat (m - k) : ℕ) : ℤ) := by
        simpa [hto, hL] using hmn_lt
      exact_mod_cast hcast
    · have hmn_nonneg : 0 ≤ m - n := sub_nonneg.mpr hn_high
      have hto : ((Int.toNat (m - n) : ℕ) : ℤ) = m - n :=
        Int.toNat_of_nonneg hmn_nonneg
      change m - ((Int.toNat (m - n) : ℕ) : ℤ) = n
      rw [hto]
      omega
  · intro j _hj
    have harg : Int.toNat (m - (m - (j : ℤ))) = j := by
      have hsub : m - (m - (j : ℤ)) = (j : ℤ) := by ring
      simp [hsub]
    exact congrArg F harg.symm

private theorem sum_Icc_betaWeight_le_geometric_inv
    {k m : ℤ} (hkm : k ≤ m) {β : ℝ} (hβ : 0 < β) :
    (∑ n ∈ Finset.Icc (k + 1) m,
        Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ))) ≤
      (1 - Real.rpow (3 : ℝ) (-β))⁻¹ := by
  let L : ℕ := Int.toNat (m - k)
  have hsum_eq :
      (∑ n ∈ Finset.Icc (k + 1) m,
          Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ))) =
        ∑ j ∈ Finset.range L, Real.rpow (3 : ℝ) (-β * (j : ℝ)) := by
    simpa [L] using
      (sum_range_to_Icc_descending (k := k) (m := m) hkm
        (fun j => Real.rpow (3 : ℝ) (-β * (j : ℝ)))).symm
  have hrange_le :
      (∑ j ∈ Finset.range L, Real.rpow (3 : ℝ) (-β * (j : ℝ))) ≤
        ∑ j ∈ (Finset.range (L + 1)).filter (fun _j => True),
          Real.rpow (3 : ℝ) (-β * (j : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      simpa only [Finset.mem_filter, and_true] using
        Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))
    · intro j _hj _hj_not
      exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hgeom :=
    Homogenization.sum_filter_triadicDepthWeight_le_geometric_inv
      β L (fun _j => True) hβ
  calc
    (∑ n ∈ Finset.Icc (k + 1) m,
        Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ)))
        =
      ∑ j ∈ Finset.range L, Real.rpow (3 : ℝ) (-β * (j : ℝ)) := hsum_eq
    _ ≤
      ∑ j ∈ (Finset.range (L + 1)).filter (fun _j => True),
        Real.rpow (3 : ℝ) (-β * (j : ℝ)) := hrange_le
    _ ≤ (1 - Real.rpow (3 : ℝ) (-β))⁻¹ := hgeom

/-- Integrability of the square of a finite weighted response-defect
square-root sum.  This is the integrability part of the Cauchy/tau estimate
below, exposed proof-internally for the final paired-square assembly. -/
theorem integrable_sq_weighted_sqrt_responseDefectAverageAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k)
    (w : ℤ → ℝ) (p q : Vec d)
    (hw : ∀ n ∈ Finset.Icc (k + 1) m, 0 ≤ w n)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDesc :
      ∀ n ∈ Finset.Icc (k + 1) m,
        ∀ R, R ∈ descendantsAtScale (originCube d m) n →
          Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    Integrable
      (fun a : RegCoeffField d =>
        (∑ n ∈ Finset.Icc (k + 1) m,
          w n * Real.sqrt
            (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) ^ 2) P := by
  let S : Finset ℤ := Finset.Icc (k + 1) m
  let D : ℤ → RegCoeffField d → ℝ :=
    fun n a => WeakNormsMaximizer.responseDefectAverageAtScale m n p q a
  let X : RegCoeffField d → ℝ :=
    fun a => (∑ n ∈ S, w n * Real.sqrt (D n a)) ^ 2
  let Y : RegCoeffField d → ℝ :=
    fun a => (∑ n ∈ S, w n) * ∑ n ∈ S, w n * D n a
  have hIndex : ∀ n ∈ S, 0 ≤ n ∧ n ≤ m := by
    intro n hn
    exact int_mem_Icc_succ_right_nonneg_and_le hk_nonneg (by simpa [S] using hn)
  have hDInt : ∀ n ∈ S, Integrable (D n) P := by
    intro n hn
    have hnm : n ≤ m := (hIndex n hn).2
    exact integrable_responseDefectAverageAtScale hnm p q hParent
      (hDesc n (by simpa [S] using hn))
  have hDNonneg : ∀ n ∈ S, 0 ≤ᵐ[P] D n := by
    intro n hn
    exact responseDefectAverageAtScale_nonneg_ae hP (hIndex n hn).2 p q
  have hDNonneg_all : ∀ᵐ a ∂P, ∀ n ∈ S, 0 ≤ D n a := by
    exact (Finset.eventually_all (I := S)
      (l := ae P) (p := fun n a => 0 ≤ D n a)).2 hDNonneg
  have hYInt : Integrable Y P := by
    have hsum :
        Integrable (fun a : RegCoeffField d => ∑ n ∈ S, w n * D n a) P :=
      integrable_finsetSum S
        (fun n hn => (hDInt n hn).const_mul (w n))
    exact hsum.const_mul (∑ n ∈ S, w n)
  have hsumAEMeas :
      AEStronglyMeasurable
        (fun a : RegCoeffField d => ∑ n ∈ S, w n * Real.sqrt (D n a)) P := by
    have hfun :
        AEStronglyMeasurable
          (∑ n ∈ S, fun a : RegCoeffField d => w n * Real.sqrt (D n a)) P :=
      Finset.aestronglyMeasurable_sum S
        (f := fun n a => w n * Real.sqrt (D n a))
        (by
          intro n hn
          have hsqrt :
              AEStronglyMeasurable (fun a : RegCoeffField d => Real.sqrt (D n a)) P :=
            (hDInt n hn).aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
          exact hsqrt.const_mul (w n))
    refine hfun.congr ?_
    filter_upwards with a
    simp [Finset.sum_apply]
  have hXAEMeas : AEStronglyMeasurable X P := by
    simpa [X] using! hsumAEMeas.pow 2
  have hPoint : ∀ᵐ a ∂P, X a ≤ Y a := by
    filter_upwards [hDNonneg_all] with a hnonneg
    have hCauchy :=
      sq_sum_mul_sqrt_le_sum_mul_sum_mul S w (fun n => D n a)
        (by intro n hn; exact hw n (by simpa [S] using hn))
        (by intro n hn; exact hnonneg n hn)
    simpa [X, Y, S, D] using hCauchy
  have hXNonneg : ∀ᵐ a ∂P, 0 ≤ X a := by
    filter_upwards with a
    exact sq_nonneg _
  have hXInt : Integrable X P := by
    refine Integrable.mono' hYInt hXAEMeas ?_
    filter_upwards [hPoint, hXNonneg] with a hle hnonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  simpa [X, D, S] using hXInt

/-- Finite weighted Cauchy plus stationarity converts the square of a weighted
sum of response-defect square roots into the corresponding weighted tau sum. -/
theorem integral_sq_weighted_sqrt_responseDefectAverageAtScale_le_sum_weights_mul_tauAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k)
    (w : ℤ → ℝ) (p q : Vec d)
    (hw : ∀ n ∈ Finset.Icc (k + 1) m, 0 ≤ w n)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDesc :
      ∀ n ∈ Finset.Icc (k + 1) m,
        ∀ R, R ∈ descendantsAtScale (originCube d m) n →
          Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    ∫ a,
        (∑ n ∈ Finset.Icc (k + 1) m,
          w n * Real.sqrt
            (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) ^ 2 ∂P
      ≤
        (∑ n ∈ Finset.Icc (k + 1) m, w n) *
          ∑ n ∈ Finset.Icc (k + 1) m, w n * tauAtScale P m n p q := by
  let S : Finset ℤ := Finset.Icc (k + 1) m
  let D : ℤ → RegCoeffField d → ℝ :=
    fun n a => WeakNormsMaximizer.responseDefectAverageAtScale m n p q a
  let X : RegCoeffField d → ℝ :=
    fun a => (∑ n ∈ S, w n * Real.sqrt (D n a)) ^ 2
  let Y : RegCoeffField d → ℝ :=
    fun a => (∑ n ∈ S, w n) * ∑ n ∈ S, w n * D n a
  have hIndex : ∀ n ∈ S, 0 ≤ n ∧ n ≤ m := by
    intro n hn
    exact int_mem_Icc_succ_right_nonneg_and_le hk_nonneg (by simpa [S] using hn)
  have hDInt : ∀ n ∈ S, Integrable (D n) P := by
    intro n hn
    have hnm : n ≤ m := (hIndex n hn).2
    exact integrable_responseDefectAverageAtScale hnm p q hParent
      (hDesc n (by simpa [S] using hn))
  have hDNonneg : ∀ n ∈ S, 0 ≤ᵐ[P] D n := by
    intro n hn
    exact responseDefectAverageAtScale_nonneg_ae hP (hIndex n hn).2 p q
  have hDNonneg_all : ∀ᵐ a ∂P, ∀ n ∈ S, 0 ≤ D n a := by
    exact (Finset.eventually_all (I := S)
      (l := ae P) (p := fun n a => 0 ≤ D n a)).2 hDNonneg
  have hYInt : Integrable Y P := by
    have hsum :
        Integrable (fun a : RegCoeffField d => ∑ n ∈ S, w n * D n a) P :=
      integrable_finsetSum S
        (fun n hn => (hDInt n hn).const_mul (w n))
    exact hsum.const_mul (∑ n ∈ S, w n)
  have hsumAEMeas :
      AEStronglyMeasurable
        (fun a : RegCoeffField d => ∑ n ∈ S, w n * Real.sqrt (D n a)) P := by
    have hfun :
        AEStronglyMeasurable
          (∑ n ∈ S, fun a : RegCoeffField d => w n * Real.sqrt (D n a)) P :=
      Finset.aestronglyMeasurable_sum S
        (f := fun n a => w n * Real.sqrt (D n a))
        (by
          intro n hn
          have hsqrt :
              AEStronglyMeasurable (fun a : RegCoeffField d => Real.sqrt (D n a)) P :=
            (hDInt n hn).aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
          exact hsqrt.const_mul (w n))
    refine hfun.congr ?_
    filter_upwards with a
    simp [Finset.sum_apply]
  have hXAEMeas : AEStronglyMeasurable X P := by
    simpa [X] using! hsumAEMeas.pow 2
  have hPoint : ∀ᵐ a ∂P, X a ≤ Y a := by
    filter_upwards [hDNonneg_all] with a hnonneg
    have hCauchy :=
      sq_sum_mul_sqrt_le_sum_mul_sum_mul S w (fun n => D n a)
        (by intro n hn; exact hw n (by simpa [S] using hn))
        (by intro n hn; exact hnonneg n hn)
    simpa [X, Y, S, D] using hCauchy
  have hXNonneg : ∀ᵐ a ∂P, 0 ≤ X a := by
    filter_upwards with a
    exact sq_nonneg _
  have hXInt : Integrable X P := by
    refine Integrable.mono' hYInt hXAEMeas ?_
    filter_upwards [hPoint, hXNonneg] with a hle hnonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hIntegralY :
      ∫ a, Y a ∂P =
        (∑ n ∈ S, w n) * ∑ n ∈ S, w n * tauAtScale P m n p q := by
    calc
      ∫ a, Y a ∂P =
          (∑ n ∈ S, w n) *
            ∫ a, (∑ n ∈ S, w n * D n a) ∂P := by
          simp [Y, integral_const_mul]
      _ =
          (∑ n ∈ S, w n) *
            ∑ n ∈ S, ∫ a, w n * D n a ∂P := by
          rw [integral_finsetSum S
            (fun n hn => (hDInt n hn).const_mul (w n))]
      _ =
          (∑ n ∈ S, w n) *
            ∑ n ∈ S, w n * tauAtScale P m n p q := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro n hn
          have hn_nonneg : 0 ≤ n := (hIndex n hn).1
          have hnm : n ≤ m := (hIndex n hn).2
          rw [integral_const_mul]
          rw [integral_responseDefectAverageAtScale_eq_tauAtScale
            hP hstat hn_nonneg hnm p q hParent
            (hDesc n (by simpa [S] using hn))]
  calc
    ∫ a, (∑ n ∈ Finset.Icc (k + 1) m,
          w n * Real.sqrt
            (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) ^ 2 ∂P
        =
      ∫ a, X a ∂P := by simp [X, D, S]
    _ ≤ ∫ a, Y a ∂P := integral_mono_ae hXInt hYInt hPoint
    _ =
        (∑ n ∈ Finset.Icc (k + 1) m, w n) *
          ∑ n ∈ Finset.Icc (k + 1) m, w n * tauAtScale P m n p q := by
        simpa [S] using hIntegralY

/-- The beta-weighted response-defect baseline term is bounded by the geometric
series factor times the beta-weighted tau sum. -/
theorem integral_sq_beta_weighted_sqrt_responseDefectAverageAtScale_le_geometric_tauSum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    {β : ℝ} (hβ : 0 < β) (p q : Vec d)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDesc :
      ∀ n ∈ Finset.Icc (k + 1) m,
        ∀ R, R ∈ descendantsAtScale (originCube d m) n →
          Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    ∫ a,
        (∑ n ∈ Finset.Icc (k + 1) m,
          Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ)) *
            Real.sqrt
              (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) ^ 2 ∂P
      ≤
        (1 - Real.rpow (3 : ℝ) (-β))⁻¹ *
          ∑ n ∈ Finset.Icc (k + 1) m,
            Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ)) *
              tauAtScale P m n p q := by
  let S : Finset ℤ := Finset.Icc (k + 1) m
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ))
  have hw : ∀ n ∈ S, 0 ≤ w n := by
    intro n _hn
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hbase :=
    integral_sq_weighted_sqrt_responseDefectAverageAtScale_le_sum_weights_mul_tauAtScale
      hP hstat hk_nonneg w p q
      (by intro n hn; exact hw n (by simpa [S] using hn))
      hParent hDesc
  have hTauNonneg : ∀ n ∈ S, 0 ≤ tauAtScale P m n p q := by
    intro n hn
    have hIndex := int_mem_Icc_succ_right_nonneg_and_le hk_nonneg (by simpa [S] using hn)
    have hint :=
      integral_responseDefectAverageAtScale_eq_tauAtScale
        hP hstat hIndex.1 hIndex.2 p q hParent
        (hDesc n (by simpa [S] using hn))
    rw [← hint]
    exact integral_nonneg_of_ae
      (responseDefectAverageAtScale_nonneg_ae hP hIndex.2 p q)
  have hTauSumNonneg :
      0 ≤ ∑ n ∈ S, w n * tauAtScale P m n p q := by
    exact Finset.sum_nonneg fun n hn => mul_nonneg (hw n hn) (hTauNonneg n hn)
  have hWeight :
      (∑ n ∈ S, w n) ≤ (1 - Real.rpow (3 : ℝ) (-β))⁻¹ := by
    simpa [S, w] using
      sum_Icc_betaWeight_le_geometric_inv (k := k) (m := m) hkm hβ
  have hfactor :
      (∑ n ∈ S, w n) *
          ∑ n ∈ S, w n * tauAtScale P m n p q
        ≤
        (1 - Real.rpow (3 : ℝ) (-β))⁻¹ *
          ∑ n ∈ S, w n * tauAtScale P m n p q :=
    mul_le_mul_of_nonneg_right hWeight hTauSumNonneg
  exact hbase.trans (by simpa [S, w] using hfactor)

/-- The beta-weighted response-defect baseline term with the geometric factor
absorbed into the standard `5 * beta^{-1}` loss. -/
theorem integral_sq_beta_weighted_sqrt_responseDefectAverageAtScale_le_beta_inv_tauSum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    {β : ℝ} (hβ : 0 < β) (hβ_le : β ≤ 1) (p q : Vec d)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDesc :
      ∀ n ∈ Finset.Icc (k + 1) m,
        ∀ R, R ∈ descendantsAtScale (originCube d m) n →
          Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    ∫ a,
        (∑ n ∈ Finset.Icc (k + 1) m,
          Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ)) *
            Real.sqrt
              (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) ^ 2 ∂P
      ≤
        (5 * β⁻¹) *
          ∑ n ∈ Finset.Icc (k + 1) m,
            Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ)) *
              tauAtScale P m n p q := by
  let S : Finset ℤ := Finset.Icc (k + 1) m
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ))
  have hgeom :=
    integral_sq_beta_weighted_sqrt_responseDefectAverageAtScale_le_geometric_tauSum
      hP hstat hk_nonneg hkm hβ p q hParent hDesc
  have hw : ∀ n ∈ S, 0 ≤ w n := by
    intro n _hn
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hTauNonneg : ∀ n ∈ S, 0 ≤ tauAtScale P m n p q := by
    intro n hn
    have hIndex := int_mem_Icc_succ_right_nonneg_and_le hk_nonneg (by simpa [S] using hn)
    have hint :=
      integral_responseDefectAverageAtScale_eq_tauAtScale
        hP hstat hIndex.1 hIndex.2 p q hParent
        (hDesc n (by simpa [S] using hn))
    rw [← hint]
    exact integral_nonneg_of_ae
      (responseDefectAverageAtScale_nonneg_ae hP hIndex.2 p q)
  have hTauSumNonneg :
      0 ≤ ∑ n ∈ S, w n * tauAtScale P m n p q := by
    exact Finset.sum_nonneg fun n hn => mul_nonneg (hw n hn) (hTauNonneg n hn)
  have hfactor :
      (1 - Real.rpow (3 : ℝ) (-β))⁻¹ *
          ∑ n ∈ S, w n * tauAtScale P m n p q
        ≤
        (5 * β⁻¹) *
          ∑ n ∈ S, w n * tauAtScale P m n p q :=
    mul_le_mul_of_nonneg_right
      (Homogenization.Book.Ch02.inv_one_sub_rpow_three_neg_le_five_inv hβ hβ_le)
      hTauSumNonneg
  exact hgeom.trans (by simpa [S, w] using hfactor)

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
