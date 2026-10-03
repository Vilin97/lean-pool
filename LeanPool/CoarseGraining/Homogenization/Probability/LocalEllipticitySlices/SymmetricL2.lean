/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.LocalEllipticitySlices

/-! # Symmetric L2 -/

@[expose] public section

namespace Homogenization

noncomputable section

namespace IsAEEllipticFieldOn

/--
Spatial a.e. ellipticity sends `L²` vector fields to `L²` vector fields after
multiplication by the symmetric part of the coefficient matrix.
-/
theorem memVectorL2_matVecMul_symmPart {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (h : IsAEEllipticFieldOn lam Lam U a)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 U (fun x => matVecMul (symmPart (a x)) (f x)) := by
  classical
  rw [MemVectorL2] at hf ⊢
  refine (MeasureTheory.memLp_pi_iff).2 ?_
  intro i
  refine MeasureTheory.memLp_finsetSum
    (s := Finset.univ)
    (f := fun j : Fin d => fun x : Vec d => symmPart (a x) i j * f x j) ?_
  intro j _hj
  have hfj : MeasureTheory.MemLp (fun x => f x j) 2 (volumeMeasureOn U) :=
    (MeasureTheory.memLp_pi_iff.mp hf) j
  have hcoeff_i :
      MeasureTheory.AEStronglyMeasurable (fun x : Vec d => a x i j)
        (volumeMeasureOn U) := by
    refine (h.aestronglyMeasurable_restrictCoeffField_apply i j).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem h.measurableSet] with x hx
    simp [restrictCoeffField, hx]
  have hcoeff_j :
      MeasureTheory.AEStronglyMeasurable (fun x : Vec d => a x j i)
        (volumeMeasureOn U) := by
    refine (h.aestronglyMeasurable_restrictCoeffField_apply j i).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem h.measurableSet] with x hx
    simp [restrictCoeffField, hx]
  have hcoeff_symm :
      MeasureTheory.AEStronglyMeasurable (fun x : Vec d => symmPart (a x) i j)
        (volumeMeasureOn U) := by
    have hsum :
        MeasureTheory.AEStronglyMeasurable
          (fun x : Vec d => a x i j + a x j i) (volumeMeasureOn U) := by
      simpa using! hcoeff_i.add hcoeff_j
    simpa [symmPart, div_eq_mul_inv] using hsum.mul_const ((2 : ℝ)⁻¹)
  have hterm_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun x => symmPart (a x) i j * f x j) (volumeMeasureOn U) :=
    hcoeff_symm.mul hfj.aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂ volumeMeasureOn U,
        ‖symmPart (a x) i j * f x j‖ ≤ Lam * ‖f x j‖ := by
    filter_upwards [h.ae_isEllipticMatrix] with x hxEll
    have hcoeff_ij : |a x i j| ≤ Lam := abs_apply_le_of_isEllipticMatrix hxEll i j
    have hcoeff_ji : |a x j i| ≤ Lam := abs_apply_le_of_isEllipticMatrix hxEll j i
    have hsymm : |symmPart (a x) i j| ≤ Lam := by
      calc
        |symmPart (a x) i j|
            = |a x i j + a x j i| * (1 / 2 : ℝ) := by
                simp [symmPart, div_eq_mul_inv, abs_mul]
        _ = (1 / 2 : ℝ) * |a x i j + a x j i| := by ring
        _ ≤ (1 / 2 : ℝ) * (|a x i j| + |a x j i|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ Lam := by
              nlinarith
    calc
      ‖symmPart (a x) i j * f x j‖ =
          |symmPart (a x) i j| * ‖f x j‖ := by
        rw [norm_mul, Real.norm_eq_abs]
      _ ≤ Lam * ‖f x j‖ := mul_le_mul_of_nonneg_right hsymm (norm_nonneg _)
  simpa using MeasureTheory.MemLp.of_le_mul hfj hterm_meas hbound

end IsAEEllipticFieldOn

end

end Homogenization
