/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Smooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.CoordDeriv

/-!
# Space Second Deriv

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators Topology

open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Foundation.Heat

/-- The spatial derivative of the heat kernel's first derivative in direction `i` equals the
second spatial derivative of the heat kernel in direction `i`. -/
theorem heatKernelSpaceDerivative_fderiv_apply_basisVec {x : Vec3} {t : ℝ}
    (ht : 0 < t) (i : Fin 3) :
    (fderiv ℝ (fun z : Vec3 => heatKernelSpaceDerivative z t i) x)
        (CKN.basisVec i) = heatKernelSpaceSecondDerivative x t i := by
  have hdiff : DifferentiableAt ℝ
      (fun z : Vec3 => heatKernelSpaceDerivative z t i) x := by
    rw [show (fun z : Vec3 => heatKernelSpaceDerivative z t i) = fun z : Vec3 =>
        -(z i) / (2 * t) *
          ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, z j ^ 2) / (4 * t))) by
      funext z
      rw [heatKernelSpaceDerivative, ite_eq_left ht,
        heatKernel_eq_formula_sum ht]]
    fun_prop (disch := positivity)
  rw [CKN.coordFDeriv_eq_deriv_update hdiff i]
  have quadratic_update (x : Vec3) (i : Fin 3) (s : ℝ) :
      ∑ j, (Function.update x i s j) ^ 2 =
        s ^ 2 + ∑ j ∈ Finset.univ.erase i, x j ^ 2 := by
    classical
    have hfun : (fun j => (Function.update x i s j) ^ 2) =
        Function.update (fun j => x j ^ 2) i (s ^ 2) := by
      funext j
      by_cases hji : j = i <;> simp [hji]
    rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i)]
    simp
  have hline : DifferentiableAt ℝ
      (fun s : ℝ => heatKernel (Function.update x i s) t) (x i) := by
    rw [show (fun s : ℝ => heatKernel (Function.update x i s) t) = fun s : ℝ =>
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(s ^ 2 + ∑ j ∈ Finset.univ.erase i, x j ^ 2) / (4 * t)) by
      funext s
      rw [heatKernel_eq_formula_sum ht, quadratic_update x i s]]
    fun_prop (disch := positivity)
  have hline' := hline.hasDerivAt
  rw [heatKernel_space_deriv ht i] at hline'
  have hlin : HasDerivAt (fun s : ℝ => -(s) / (2 * t))
      (-(1 : ℝ) / (2 * t)) (x i) := by
    convert (hasDerivAt_id (x i)).neg.div_const (2 * t) using 1
    · funext s
      simp
  have hprod := hlin.mul hline'
  have heq : (fun s : ℝ => heatKernelSpaceDerivative (Function.update x i s) t i) =
      fun s : ℝ => -(s) / (2 * t) * heatKernel (Function.update x i s) t := by
    funext s
    rw [heatKernelSpaceDerivative, ite_eq_left ht]
    simp
  rw [heq]
  have hprod' : HasDerivAt
      (fun s : ℝ => -(s) / (2 * t) * heatKernel (Function.update x i s) t)
      (-1 / (2 * t) * heatKernel (Function.update x i (x i)) t +
        -x i / (2 * t) * heatKernelSpaceDerivative x t i) (x i) := by
    convert hprod using 1
  rw [hprod'.deriv, Function.update_eq_self]
  rw [heatKernelSpaceSecondDerivative, ite_eq_left ht,
    heatKernelSpaceDerivative, ite_eq_left ht, heatKernel_eq_formula_sum ht]
  ring_nf

end CKN.Foundation.Heat
