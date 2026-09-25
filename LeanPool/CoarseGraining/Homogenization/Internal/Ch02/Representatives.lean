/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Definitions
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
public import Mathlib.MeasureTheory.OuterMeasure.AE

/-! # Representatives -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

theorem matVecMul_smul_one {d : ℕ} (c : ℝ) (x : Vec d) :
    matVecMul (c • (1 : Mat d)) x = c • x := by
  ext i
  simp [matVecMul, Matrix.one_apply]

theorem isEllipticMatrix_smul_one {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hLe : lam ≤ Lam) :
    IsEllipticMatrix lam Lam (lam • (1 : Mat d)) := by
  refine ⟨hlam, hLe, ?_, ?_⟩
  · intro ξ
    rw [matVecMul_smul_one, vecDot_smul_right]
    rfl
  · intro ξ
    have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam hLe
    have hInv_le : Lam⁻¹ ≤ lam⁻¹ :=
      (inv_le_inv₀ hLam_pos hlam).2 hLe
    have hinv :
        ((lam • (1 : Mat d))⁻¹ : Mat d) = lam⁻¹ • (1 : Mat d) := by
      rw [nonsing_inv_smul lam hlam.ne' (by simp)]
      simp
    rw [hinv, matVecMul_smul_one, vecDot_smul_right]
    exact mul_le_mul_of_nonneg_right hInv_le (vecNormSq_nonneg ξ)

theorem isSymm_smul_one {d : ℕ} (c : ℝ) :
    (c • (1 : Mat d)).IsSymm := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := by
      intro hji
      exact hij hji.symm
    simp [hij, hji]

/-- A measurable representative of the public coefficient field, assembled
entrywise from the `AEStronglyMeasurable` data. -/
noncomputable def measurableCoeffField {d : ℕ} (U : Domain d)
    (a : CoeffOn U) : CoeffField d :=
  fun x i j =>
    (a.aeStronglyMeasurable i j).mk
      (fun x : Vec d => restrictCoeffField (U : Set (Vec d)) a.toCoeffField x i j) x

theorem measurableCoeffField_measurable {d : ℕ} (U : Domain d)
    (a : CoeffOn U) :
    Measurable (fun x i j => measurableCoeffField U a x i j) := by
  refine measurable_pi_iff.2 ?_
  intro i
  refine measurable_pi_iff.2 ?_
  intro j
  exact (a.aeStronglyMeasurable i j).measurable_mk

theorem measurableCoeffField_entry_ae_eq {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (i j : Fin d) :
    (fun x : Vec d => restrictCoeffField (U : Set (Vec d)) a.toCoeffField x i j)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x : Vec d => measurableCoeffField U a x i j :=
  (a.aeStronglyMeasurable i j).ae_eq_mk

theorem measurableCoeffField_ae_eq {d : ℕ} (U : Domain d)
    (a : CoeffOn U) :
    measurableCoeffField U a =ᵐ[volumeMeasureOn (U : Set (Vec d))] a.toCoeffField := by
  have hmem :
      ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), x ∈ (U : Set (Vec d)) :=
    MeasureTheory.ae_restrict_mem U.measurableSet
  have hentries :
      ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), ∀ i j : Fin d,
        restrictCoeffField (U : Set (Vec d)) a.toCoeffField x i j =
          measurableCoeffField U a x i j := by
    exact MeasureTheory.ae_all_iff.2 fun i =>
      MeasureTheory.ae_all_iff.2 fun j => measurableCoeffField_entry_ae_eq U a i j
  filter_upwards [hmem, hentries] with x hxU hxentry
  ext i j
  simpa [restrictCoeffField, hxU] using (hxentry i j).symm

theorem measurableCoeffField_aeElliptic {d : ℕ} (U : Domain d)
    (a : CoeffOn U) :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      IsEllipticMatrix a.lam a.Lam (measurableCoeffField U a x) := by
  filter_upwards [measurableCoeffField_ae_eq U a, a.aeElliptic] with x hx hEll
  simpa [hx] using hEll

theorem measurableCoeffField_aeSymmetric {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      (measurableCoeffField U a x).IsSymm := by
  filter_upwards [measurableCoeffField_ae_eq U a, hsym] with x hx hsymx
  simpa [hx] using hsymx

structure GoodSetData {d : ℕ} (U : Domain d) (a : CoeffOn U) where
  set : Set (Vec d)
  ae_mem : set ∈ MeasureTheory.ae (volumeMeasureOn (U : Set (Vec d)))
  measurableSet : MeasurableSet set
  elliptic : ∀ x ∈ set, IsEllipticMatrix a.lam a.Lam (measurableCoeffField U a x)

theorem exists_goodSetData {d : ℕ} (U : Domain d)
    (a : CoeffOn U) : Nonempty (GoodSetData U a) := by
  rcases (measurableCoeffField_aeElliptic U a).exists_measurable_mem with
    ⟨E, hEae, hEmeas, hEell⟩
  exact ⟨⟨E, hEae, hEmeas, hEell⟩⟩

noncomputable def goodSetData {d : ℕ} (U : Domain d)
    (a : CoeffOn U) : GoodSetData U a :=
  Classical.choice (exists_goodSetData U a)

structure GoodSymmetricSetData {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (hsym : CoeffOn.IsSymmetric a) where
  set : Set (Vec d)
  ae_mem : set ∈ MeasureTheory.ae (volumeMeasureOn (U : Set (Vec d)))
  measurableSet : MeasurableSet set
  elliptic : ∀ x ∈ set, IsEllipticMatrix a.lam a.Lam (measurableCoeffField U a x)
  symmetric : ∀ x ∈ set, (measurableCoeffField U a x).IsSymm

theorem exists_goodSymmetricSetData {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    Nonempty (GoodSymmetricSetData U a hsym) := by
  have hboth :
      ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
        IsEllipticMatrix a.lam a.Lam (measurableCoeffField U a x) ∧
          (measurableCoeffField U a x).IsSymm :=
    (measurableCoeffField_aeElliptic U a).and
      (measurableCoeffField_aeSymmetric U a hsym)
  rcases hboth.exists_measurable_mem with ⟨E, hEae, hEmeas, hEboth⟩
  exact ⟨⟨E, hEae, hEmeas, fun x hx => (hEboth x hx).1,
    fun x hx => (hEboth x hx).2⟩⟩

noncomputable def goodSymmetricSetData {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    GoodSymmetricSetData U a hsym :=
  Classical.choice (exists_goodSymmetricSetData U a hsym)

/-- Internal pointwise-good representative of the public a.e. coefficient field.
Outside a measurable full-measure good set we insert the scalar matrix
`a.lam • I`, which is uniformly elliptic with the same constants. -/
noncomputable def pointwiseCoeffField {d : ℕ} (U : Domain d)
    (a : CoeffOn U) : CoeffField d := by
  classical
  exact fun x =>
    if x ∈ (goodSetData U a).set then
      measurableCoeffField U a x
    else
      a.lam • (1 : Mat d)

theorem pointwiseCoeffField_ae_eq {d : ℕ} (U : Domain d)
    (a : CoeffOn U) :
    pointwiseCoeffField U a =ᵐ[volumeMeasureOn (U : Set (Vec d))] a.toCoeffField := by
  filter_upwards [(goodSetData U a).ae_mem, measurableCoeffField_ae_eq U a]
    with x hxGood hxCoeff
  simp [pointwiseCoeffField, hxGood, hxCoeff]

theorem pointwiseCoeffField_measurable {d : ℕ} (U : Domain d)
    (a : CoeffOn U) :
    Measurable (fun x i j => pointwiseCoeffField U a x i j) := by
  classical
  refine measurable_pi_iff.2 ?_
  intro i
  refine measurable_pi_iff.2 ?_
  intro j
  have hrep : Measurable fun x : Vec d => measurableCoeffField U a x i j :=
    (measurable_pi_iff.1 (measurable_pi_iff.1
      (measurableCoeffField_measurable U a) i) j)
  have hite :
      Measurable fun x : Vec d =>
        if x ∈ (goodSetData U a).set then
          measurableCoeffField U a x i j
        else
          (a.lam • (1 : Mat d)) i j :=
    Measurable.ite (by simpa using (goodSetData U a).measurableSet)
      hrep measurable_const
  convert hite using 1
  funext x
  by_cases hxGood : x ∈ (goodSetData U a).set <;>
    simp [pointwiseCoeffField, hxGood]

theorem pointwiseCoeffField_restrict_measurable {d : ℕ} (U : Domain d)
    (a : CoeffOn U) :
    Measurable
      (fun x i j =>
        restrictCoeffField (U : Set (Vec d)) (pointwiseCoeffField U a) x i j) := by
  classical
  refine measurable_pi_iff.2 ?_
  intro i
  refine measurable_pi_iff.2 ?_
  intro j
  have hcoeff : Measurable fun x : Vec d => pointwiseCoeffField U a x i j :=
    (measurable_pi_iff.1 (measurable_pi_iff.1
      (pointwiseCoeffField_measurable U a) i) j)
  have hite :
      Measurable fun x : Vec d =>
        if x ∈ (U : Set (Vec d)) then pointwiseCoeffField U a x i j else 0 :=
    Measurable.ite (by simpa using U.measurableSet) hcoeff measurable_const
  convert hite using 1
  funext x
  by_cases hxU : x ∈ (U : Set (Vec d)) <;> simp [restrictCoeffField, hxU]

theorem pointwiseCoeffField_isEllipticFieldOn {d : ℕ} (U : Domain d)
    (a : CoeffOn U) :
    IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) (pointwiseCoeffField U a) := by
  classical
  have hmeas :
      Measurable
        (fun x i j =>
          if x ∈ (U : Set (Vec d)) then pointwiseCoeffField U a x i j else 0) := by
    convert pointwiseCoeffField_restrict_measurable U a using 1
    funext x i j
    by_cases hxU : x ∈ (U : Set (Vec d)) <;> simp [restrictCoeffField, hxU]
  refine ⟨hmeas, ?_⟩
  intro x _hxU
  by_cases hxGood : x ∈ (goodSetData U a).set
  · simpa [pointwiseCoeffField, hxGood] using
      (goodSetData U a).elliptic x hxGood
  · simpa [pointwiseCoeffField, hxGood] using
      isEllipticMatrix_smul_one (d := d) a.lam_pos a.lam_le_Lam

/-- The pointwise-good representative attached to the public open-cube
coefficient field is pointwise elliptic on the corresponding closed cube.

The public `CoeffOn` data are a.e.-elliptic on the open cube.  The representative
fills the exceptional set by `a.lam • I`, so the same pointwise ellipticity
extends across the half-open/closed cube realization used by the deterministic
proof engines. -/
theorem pointwiseCoeffField_isEllipticFieldOn_cubeSet {d : ℕ}
    (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q)) :
    IsEllipticFieldOn a.lam a.Lam (cubeSet Q)
      (pointwiseCoeffField (cubeDomain Q) a) := by
  classical
  have hmeas :
      Measurable
        (fun x i j =>
          if x ∈ cubeSet Q then
            pointwiseCoeffField (cubeDomain Q) a x i j
          else 0) := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    have hcoeff :
        Measurable fun x : Vec d =>
          pointwiseCoeffField (cubeDomain Q) a x i j := by
      exact (measurable_pi_iff.1 (measurable_pi_iff.1
        (pointwiseCoeffField_measurable (cubeDomain Q) a) i) j)
    exact Measurable.ite (measurableSet_cubeSet Q) hcoeff measurable_const
  refine ⟨hmeas, ?_⟩
  intro x _hxQ
  by_cases hxGood : x ∈ (goodSetData (cubeDomain Q) a).set
  · simpa [pointwiseCoeffField, hxGood] using
      (goodSetData (cubeDomain Q) a).elliptic x hxGood
  · simpa [pointwiseCoeffField, hxGood] using
      isEllipticMatrix_smul_one (d := d) a.lam_pos a.lam_le_Lam

noncomputable def pointwiseCoeffOn {d : ℕ} (U : Domain d)
    (a : CoeffOn U) : CoeffOn U where
  toCoeffField := pointwiseCoeffField U a
  lam := a.lam
  Lam := a.Lam
  lam_pos := a.lam_pos
  lam_le_Lam := a.lam_le_Lam
  aeStronglyMeasurable := by
    intro i j
    have hentry :
        Measurable fun x : Vec d =>
          restrictCoeffField (U : Set (Vec d)) (pointwiseCoeffField U a) x i j := by
      exact (measurable_pi_iff.1 (measurable_pi_iff.1
        (pointwiseCoeffField_restrict_measurable U a) i) j)
    exact hentry.aestronglyMeasurable
  aeElliptic := by
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hxU
    exact (pointwiseCoeffField_isEllipticFieldOn U a).2 x hxU

theorem pointwiseCoeffOn_isEllipticFieldOn {d : ℕ} (U : Domain d)
    (a : CoeffOn U) :
    IsEllipticFieldOn (pointwiseCoeffOn U a).lam (pointwiseCoeffOn U a).Lam
      (U : Set (Vec d)) (pointwiseCoeffOn U a).toCoeffField := by
  simpa [pointwiseCoeffOn] using pointwiseCoeffField_isEllipticFieldOn U a

theorem pointwiseCoeffOn_ae_eq {d : ℕ} (U : Domain d)
    (a : CoeffOn U) :
    CoeffOn.AEEq (pointwiseCoeffOn U a) a :=
  pointwiseCoeffField_ae_eq U a

/-- Pointwise elliptic and pointwise symmetric representative used to consume
old symmetric proof engines while preserving the public a.e. symmetry surface. -/
noncomputable def pointwiseSymmetricCoeffField {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) : CoeffField d := by
  classical
  exact fun x =>
    if x ∈ (goodSymmetricSetData U a hsym).set then
      measurableCoeffField U a x
    else
      a.lam • (1 : Mat d)

theorem pointwiseSymmetricCoeffField_ae_eq {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    pointwiseSymmetricCoeffField U a hsym
      =ᵐ[volumeMeasureOn (U : Set (Vec d))] a.toCoeffField := by
  filter_upwards [(goodSymmetricSetData U a hsym).ae_mem,
      measurableCoeffField_ae_eq U a] with x hxGood hxCoeff
  simp [pointwiseSymmetricCoeffField, hxGood, hxCoeff]

theorem pointwiseSymmetricCoeffField_measurable {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    Measurable (fun x i j => pointwiseSymmetricCoeffField U a hsym x i j) := by
  classical
  refine measurable_pi_iff.2 ?_
  intro i
  refine measurable_pi_iff.2 ?_
  intro j
  have hrep : Measurable fun x : Vec d => measurableCoeffField U a x i j :=
    (measurable_pi_iff.1 (measurable_pi_iff.1
      (measurableCoeffField_measurable U a) i) j)
  have hite :
      Measurable fun x : Vec d =>
        if x ∈ (goodSymmetricSetData U a hsym).set then
          measurableCoeffField U a x i j
        else
          (a.lam • (1 : Mat d)) i j :=
    Measurable.ite (by simpa using (goodSymmetricSetData U a hsym).measurableSet)
      hrep measurable_const
  convert hite using 1
  funext x
  by_cases hxGood : x ∈ (goodSymmetricSetData U a hsym).set <;>
    simp [pointwiseSymmetricCoeffField, hxGood]

theorem pointwiseSymmetricCoeffField_restrict_measurable {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    Measurable
      (fun x i j =>
        restrictCoeffField (U : Set (Vec d))
          (pointwiseSymmetricCoeffField U a hsym) x i j) := by
  classical
  refine measurable_pi_iff.2 ?_
  intro i
  refine measurable_pi_iff.2 ?_
  intro j
  have hcoeff :
      Measurable fun x : Vec d => pointwiseSymmetricCoeffField U a hsym x i j :=
    (measurable_pi_iff.1 (measurable_pi_iff.1
      (pointwiseSymmetricCoeffField_measurable U a hsym) i) j)
  have hite :
      Measurable fun x : Vec d =>
        if x ∈ (U : Set (Vec d)) then
          pointwiseSymmetricCoeffField U a hsym x i j
        else 0 :=
    Measurable.ite (by simpa using U.measurableSet) hcoeff measurable_const
  convert hite using 1
  funext x
  by_cases hxU : x ∈ (U : Set (Vec d)) <;> simp [restrictCoeffField, hxU]

theorem pointwiseSymmetricCoeffField_isEllipticFieldOn {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d))
      (pointwiseSymmetricCoeffField U a hsym) := by
  classical
  have hmeas :
      Measurable
        (fun x i j =>
          if x ∈ (U : Set (Vec d)) then
            pointwiseSymmetricCoeffField U a hsym x i j
          else 0) := by
    convert pointwiseSymmetricCoeffField_restrict_measurable U a hsym using 1
    funext x i j
    by_cases hxU : x ∈ (U : Set (Vec d)) <;> simp [restrictCoeffField, hxU]
  refine ⟨hmeas, ?_⟩
  intro x _hxU
  by_cases hxGood : x ∈ (goodSymmetricSetData U a hsym).set
  · simpa [pointwiseSymmetricCoeffField, hxGood] using
      (goodSymmetricSetData U a hsym).elliptic x hxGood
  · simpa [pointwiseSymmetricCoeffField, hxGood] using
      isEllipticMatrix_smul_one (d := d) a.lam_pos a.lam_le_Lam

theorem pointwiseSymmetricCoeffField_isSymmetricCoeffField {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    IsSymmetricCoeffField (pointwiseSymmetricCoeffField U a hsym) := by
  intro x
  by_cases hxGood : x ∈ (goodSymmetricSetData U a hsym).set
  · simpa [pointwiseSymmetricCoeffField, hxGood] using
      (goodSymmetricSetData U a hsym).symmetric x hxGood
  · simp [pointwiseSymmetricCoeffField, hxGood]

noncomputable def pointwiseSymmetricCoeffOn {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) : CoeffOn U where
  toCoeffField := pointwiseSymmetricCoeffField U a hsym
  lam := a.lam
  Lam := a.Lam
  lam_pos := a.lam_pos
  lam_le_Lam := a.lam_le_Lam
  aeStronglyMeasurable := by
    intro i j
    have hentry :
        Measurable fun x : Vec d =>
          restrictCoeffField (U : Set (Vec d))
            (pointwiseSymmetricCoeffField U a hsym) x i j := by
      exact (measurable_pi_iff.1 (measurable_pi_iff.1
        (pointwiseSymmetricCoeffField_restrict_measurable U a hsym) i) j)
    exact hentry.aestronglyMeasurable
  aeElliptic := by
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hxU
    exact (pointwiseSymmetricCoeffField_isEllipticFieldOn U a hsym).2 x hxU

theorem pointwiseSymmetricCoeffOn_isEllipticFieldOn {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    IsEllipticFieldOn (pointwiseSymmetricCoeffOn U a hsym).lam
      (pointwiseSymmetricCoeffOn U a hsym).Lam
      (U : Set (Vec d)) (pointwiseSymmetricCoeffOn U a hsym).toCoeffField := by
  simpa [pointwiseSymmetricCoeffOn] using
    pointwiseSymmetricCoeffField_isEllipticFieldOn U a hsym

theorem pointwiseSymmetricCoeffOn_isSymmetricCoeffField {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    IsSymmetricCoeffField (pointwiseSymmetricCoeffOn U a hsym).toCoeffField := by
  simpa [pointwiseSymmetricCoeffOn] using
    pointwiseSymmetricCoeffField_isSymmetricCoeffField U a hsym

theorem pointwiseSymmetricCoeffOn_ae_eq {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    CoeffOn.AEEq (pointwiseSymmetricCoeffOn U a hsym) a :=
  pointwiseSymmetricCoeffField_ae_eq U a hsym

end BookCh02

end

end Ch02
end Internal
end Homogenization
