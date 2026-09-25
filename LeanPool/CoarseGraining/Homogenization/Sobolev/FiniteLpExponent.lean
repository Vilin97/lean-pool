/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.UnitCubeEuclideanL2

/-!
# Finite `L^p` exponents and Euclidean cube fields

This module provides the exact finite-exponent carrier used by the Chapter 3
analytic kernels, together with restriction of a Euclidean `L^p` field to a
subcube while retaining its same pointwise representative.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

structure FiniteLpExponent where
  exponent : ℝ≥0∞
  one_lt : 1 < exponent
  lt_top : exponent < ∞

namespace FiniteLpExponent

private theorem eq_of_exponent_eq (p q : FiniteLpExponent)
    (h : p.exponent = q.exponent) : p = q := by
  cases p
  cases q
  simp_all

noncomputable def conjugate (p : FiniteLpExponent) : FiniteLpExponent where
  exponent := ENNReal.conjExponent p.exponent
  one_lt := by
    have hpq : ENNReal.HolderConjugate p.exponent
        (ENNReal.conjExponent p.exponent) :=
      ENNReal.HolderConjugate.conjExponent p.one_lt.le
    exact hpq.lt_top_iff_one_lt.mp p.lt_top
  lt_top := by
    have hpq : ENNReal.HolderConjugate p.exponent
        (ENNReal.conjExponent p.exponent) :=
      ENNReal.HolderConjugate.conjExponent p.one_lt.le
    exact hpq.symm.lt_top_iff_one_lt.mpr p.one_lt

theorem holderConjugate (p : FiniteLpExponent) :
    ENNReal.HolderConjugate p.exponent p.conjugate.exponent :=
  ENNReal.HolderConjugate.conjExponent p.one_lt.le

@[simp] theorem conjugate_conjugate (p : FiniteLpExponent) :
    p.conjugate.conjugate = p := by
  apply eq_of_exponent_eq
  change ENNReal.conjExponent (ENNReal.conjExponent p.exponent) = p.exponent
  let : ENNReal.HolderConjugate p.exponent
      (ENNReal.conjExponent p.exponent) := holderConjugate p
  let : ENNReal.HolderConjugate (ENNReal.conjExponent p.exponent)
      p.exponent := (holderConjugate p).symm
  exact ENNReal.HolderConjugate.conjExponent_eq

noncomputable def two : FiniteLpExponent where
  exponent := 2
  one_lt := by norm_num
  lt_top := by norm_num

@[simp] theorem two_exponent : two.exponent = 2 := rfl

@[simp] theorem conjugate_two : two.conjugate = two := by
  apply eq_of_exponent_eq
  change ENNReal.conjExponent 2 = 2
  exact ENNReal.HolderConjugate.conjExponent_eq
    (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))

end FiniteLpExponent

/-- Halving preserves the open interval of fractional orders. -/
noncomputable def fractionalOrderHalf
    (s : FractionalOrder) : FractionalOrder :=
  ⟨s.1 / 2, by constructor <;> nlinarith [s.2.1, s.2.2]⟩

@[simp] theorem fractionalOrderHalf_value (s : FractionalOrder) :
    (fractionalOrderHalf s).1 = s.1 / 2 := rfl

structure CubeEuclideanLpField {d : ℕ} (Q : TriadicCube d)
    (p : FiniteLpExponent) where
  toField : Vec d → Vec d
  euclideanMemLp :
    MeasureTheory.MemLp (fun x => HilbertVec.ofVec (toField x)) p.exponent
      (normalizedCubeMeasure Q)

namespace CubeEuclideanLpField

instance {d : ℕ} {Q : TriadicCube d} {p : FiniteLpExponent} :
    CoeFun (CubeEuclideanLpField Q p) (fun _ => Vec d → Vec d) where
  coe F := F.toField

noncomputable def restrictToSubcube {d : ℕ} {Q R : TriadicCube d}
    {p : FiniteLpExponent} (F : CubeEuclideanLpField Q p)
    (hRQ : openCubeSet R ⊆ openCubeSet Q) : CubeEuclideanLpField R p where
  toField := F.toField
  euclideanMemLp := by
    have hQnormalized :
        MeasureTheory.MemLp (fun x => HilbertVec.ofVec (F.toField x)) p.exponent
          (cubeBoundedMeasurableDomain Q).normalizedVolume := by
      simpa only [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using F.euclideanMemLp
    have hQrestricted :
        MeasureTheory.MemLp (fun x => HilbertVec.ofVec (F.toField x)) p.exponent
          (cubeBoundedMeasurableDomain Q).restrictedVolume :=
      ((cubeBoundedMeasurableDomain Q).memLp_normalizedVolume_iff
        p.exponent _).mp hQnormalized
    have hOpenQ :
        MeasureTheory.MemLp (fun x => HilbertVec.ofVec (F.toField x)) p.exponent
          (MeasureTheory.volume.restrict (openCubeSet Q)) := by
      simpa only [cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet]
        using hQrestricted
    have hOpenR :
        MeasureTheory.MemLp (fun x => HilbertVec.ofVec (F.toField x)) p.exponent
          (MeasureTheory.volume.restrict (openCubeSet R)) :=
      hOpenQ.mono_measure (MeasureTheory.Measure.restrict_mono hRQ le_rfl)
    have hRrestricted :
        MeasureTheory.MemLp (fun x => HilbertVec.ofVec (F.toField x)) p.exponent
          (cubeBoundedMeasurableDomain R).restrictedVolume := by
      simpa only [cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet]
        using hOpenR
    have hRnormalized :
        MeasureTheory.MemLp (fun x => HilbertVec.ofVec (F.toField x)) p.exponent
          (cubeBoundedMeasurableDomain R).normalizedVolume :=
      ((cubeBoundedMeasurableDomain R).memLp_normalizedVolume_iff
        p.exponent _).mpr hRrestricted
    simpa only [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      using hRnormalized

@[simp] theorem restrictToSubcube_toField {d : ℕ}
    {Q R : TriadicCube d} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q p)
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    (F.restrictToSubcube hRQ).toField = F.toField := rfl

end CubeEuclideanLpField

end

end Homogenization
