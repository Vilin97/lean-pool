/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Admissibility
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Derivatives

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat


noncomputable section

namespace CKN

private lemma coord_fderiv_eq_deriv_update {f : Vec3 → ℝ} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    (fderiv ℝ f x) (basisVec i) =
      deriv (fun s => f (Function.update x i s)) (x i) := by
  have hcomp := HasFDerivAt.comp (x i)
    (by simpa only [Function.update_eq_self] using hf.hasFDerivAt)
    (hasFDerivAt_update (𝕜 := ℝ) (i := i) x (x i))
  have hderiv := hcomp.hasDerivAt
  have hderiv' : HasDerivAt (fun s : ℝ => f (Function.update x i s))
      ((fderiv ℝ f x ∘SL ContinuousLinearMap.pi
        (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1) (x i) := by
    simpa only [Function.comp_def] using hderiv
  rw [hderiv'.deriv]
  have hb : ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1 =
      basisVec i := by
    ext j
    by_cases hji : j = i <;> simp [basisVec, hji]
  rw [show (fderiv ℝ f x ∘SL
      ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1 =
      (fderiv ℝ f x) (ContinuousLinearMap.pi
        (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1) by rfl, hb]

private lemma heatKernel_fderiv_apply_basisVec_local {x : Vec3} {t : ℝ}
    (ht : 0 < t) (i : Fin 3) :
    (fderiv ℝ (fun y : Vec3 => heatKernel y t) x) (basisVec i) =
      heatKernelSpaceDerivative x t i := by
  have hdiff : DifferentiableAt ℝ (fun y : Vec3 => heatKernel y t) x := by
    rw [show (fun y : Vec3 => heatKernel y t) = fun y : Vec3 =>
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ j, y j ^ 2) / (4 * t)) by
      funext y
      exact heatKernel_eq_formula_sum ht]
    fun_prop (disch := positivity)
  rw [coord_fderiv_eq_deriv_update hdiff i]
  exact heatKernel_space_deriv ht i

private lemma heatKernelSpaceDerivative_fderiv_apply_basisVec
    {x : Vec3} {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    (fderiv ℝ (fun y : Vec3 => heatKernelSpaceDerivative y t i) x)
        (basisVec i) = heatKernelSpaceSecondDerivative x t i := by
  have hdiff : DifferentiableAt ℝ
      (fun y : Vec3 => heatKernelSpaceDerivative y t i) x := by
    rw [show (fun y : Vec3 => heatKernelSpaceDerivative y t i) = fun y : Vec3 =>
        -(y i) / (2 * t) *
          ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, y j ^ 2) / (4 * t))) by
      funext y
      rw [heatKernelSpaceDerivative, ite_eq_left ht,
        heatKernel_eq_formula_sum ht]]
    fun_prop (disch := positivity)
  rw [coord_fderiv_eq_deriv_update hdiff i]
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

theorem caccioppoli_heat_spatialPartial
    {x₀ : Vec3} {t₀ r : ℝ} {z : ParabolicPoint} (ht : z.2 - t₀ < r ^ 2)
    (i : Fin 3) :
    spatialPartial (fun w : ParabolicPoint =>
      backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀)) i z =
      r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) i := by
  have hτ : 0 < r ^ 2 - (z.2 - t₀) := sub_pos.mpr ht
  unfold spatialPartial
  have hinner : HasFDerivAt (fun x : Vec3 => x - x₀)
      (ContinuousLinearMap.id ℝ Vec3) z.1 := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) z.1).sub_const x₀
  have houter : HasFDerivAt (fun x : Vec3 =>
      backwardHeatTestFunction r x (z.2 - t₀))
      (r ^ 2 • fderiv ℝ (fun y : Vec3 => heatKernel y
        (r ^ 2 - (z.2 - t₀))) (z.1 - x₀)) (z.1 - x₀) := by
    have hheat : DifferentiableAt ℝ (fun y : Vec3 => heatKernel y
        (r ^ 2 - (z.2 - t₀))) (z.1 - x₀) := by
      rw [show (fun y : Vec3 => heatKernel y (r ^ 2 - (z.2 - t₀))) = fun y : Vec3 =>
          (4 * Real.pi * (r ^ 2 - (z.2 - t₀))) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, y j ^ 2) / (4 * (r ^ 2 - (z.2 - t₀)))) by
        funext y
        exact heatKernel_eq_formula_sum hτ]
      fun_prop (disch := positivity)
    change HasFDerivAt (fun x : Vec3 => r ^ 2 * heatKernel x
      (r ^ 2 - (z.2 - t₀))) _ _
    simpa [smul_eq_mul] using hheat.hasFDerivAt.const_mul (r ^ 2)
  have hcomp := houter.comp z.1 hinner
  have hvalue := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hcomp.fderiv
  dsimp at hvalue
  change (fderiv ℝ (fun x : Vec3 =>
    backwardHeatTestFunction r (x - x₀) (z.2 - t₀)) z.1) (basisVec i) = _
  have hvalue' :
      (fderiv ℝ (fun x : Vec3 => backwardHeatTestFunction r
        (x - x₀) (z.2 - t₀)) z.1) (basisVec i) =
        (r ^ 2 • fderiv ℝ (fun y : Vec3 => heatKernel y
          (r ^ 2 - (z.2 - t₀))) (z.1 - x₀) ∘SL
          ContinuousLinearMap.id ℝ Vec3) (basisVec i) := by
    simpa only [Function.comp_def] using hvalue
  calc
    (fderiv ℝ (fun x : Vec3 => backwardHeatTestFunction r
        (x - x₀) (z.2 - t₀)) z.1) (basisVec i) =
        (r ^ 2 • fderiv ℝ (fun y : Vec3 => heatKernel y
          (r ^ 2 - (z.2 - t₀))) (z.1 - x₀) ∘SL
          ContinuousLinearMap.id ℝ Vec3) (basisVec i) := hvalue'
    _ = r ^ 2 * (fderiv ℝ (fun y : Vec3 => heatKernel y
          (r ^ 2 - (z.2 - t₀))) (z.1 - x₀)) (basisVec i) := by
      simp [smul_eq_mul]
    _ = r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) i := by
      rw [heatKernel_fderiv_apply_basisVec_local hτ i]

theorem caccioppoli_heat_timePartial
    {x₀ : Vec3} {t₀ r : ℝ} {z : ParabolicPoint} (ht : z.2 - t₀ < r ^ 2) :
    timePartial (fun w : ParabolicPoint =>
      backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀)) z =
      -r ^ 2 * heatKernelTimeDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) := by
  have hτ : 0 < r ^ 2 - (z.2 - t₀) := sub_pos.mpr ht
  unfold timePartial
  have houter := (heatKernel_time_differentiableAt
    (x := z.1 - x₀) hτ).hasDerivAt
  rw [heatKernel_time_deriv hτ] at houter
  have hinner : HasDerivAt (fun s : ℝ => r ^ 2 - (s - t₀)) (-1) z.2 := by
    convert (hasDerivAt_const z.2 (r ^ 2)).sub
      ((hasDerivAt_id z.2).sub_const t₀) using 1
    · funext s
      dsimp
    · simp
  have hcomp := houter.comp z.2 hinner
  have hscaled := (hasDerivAt_const z.2 (r ^ 2)).mul hcomp
  have hderiv : HasDerivAt (fun s : ℝ =>
      backwardHeatTestFunction r (z.1 - x₀) (s - t₀))
      (-r ^ 2 * heatKernelTimeDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀))) z.2 := by
    convert hscaled using 1
    · funext s
      rfl
    · simp
  change (fderiv ℝ (fun s : ℝ =>
    backwardHeatTestFunction r (z.1 - x₀) (s - t₀)) z.2) 1 = _
  have hfderiv := hderiv.hasFDerivAt.fderiv
  have hvalue := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hfderiv
  simpa [smul_eq_mul] using hvalue

theorem caccioppoli_heat_secondSpatialPartial
    {x₀ : Vec3} {t₀ r : ℝ} {z : ParabolicPoint} (ht : z.2 - t₀ < r ^ 2)
    (i : Fin 3) :
    spatialSecondPartial (fun w : ParabolicPoint =>
      backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀)) i i z =
      r ^ 2 * heatKernelSpaceSecondDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) i := by
  have hτ : 0 < r ^ 2 - (z.2 - t₀) := sub_pos.mpr ht
  unfold spatialSecondPartial
  change (fderiv ℝ (fun x : Vec3 => spatialPartial (fun w : ParabolicPoint =>
      backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀)) i (x, z.2)) z.1)
      (basisVec i) = _
  have hfirst : ∀ x : Vec3,
      (fderiv ℝ (fun y : Vec3 =>
        backwardHeatTestFunction r (y - x₀) (z.2 - t₀)) x) (basisVec i) =
        r ^ 2 * heatKernelSpaceDerivative (x - x₀)
          (r ^ 2 - (z.2 - t₀)) i := by
    intro x
    exact caccioppoli_heat_spatialPartial (z := (x, z.2)) (by simpa using ht) i
  have hformula : (fun x : Vec3 => spatialPartial (fun w : ParabolicPoint =>
      backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀)) i (x, z.2)) =
      (fun x : Vec3 => r ^ 2 * heatKernelSpaceDerivative (x - x₀)
        (r ^ 2 - (z.2 - t₀)) i) := by
    funext x
    exact hfirst x
  have hformula' : (fun x : Vec3 => spatialPartial (fun w : ParabolicPoint =>
      backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀)) i (x, z.2)) =
      (fun x : Vec3 => r ^ 2 * heatKernelSpaceDerivative (x - x₀)
        (r ^ 2 - (z.2 - t₀)) i) := hformula
  rw [hformula']
  have hinner : HasFDerivAt (fun x : Vec3 => x - x₀)
      (ContinuousLinearMap.id ℝ Vec3) z.1 := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) z.1).sub_const x₀
  have houter : HasFDerivAt (fun x : Vec3 =>
      r ^ 2 * heatKernelSpaceDerivative x
        (r ^ 2 - (z.2 - t₀)) i)
      (r ^ 2 • fderiv ℝ (fun y : Vec3 =>
        heatKernelSpaceDerivative y (r ^ 2 - (z.2 - t₀)) i) (z.1 - x₀))
      (z.1 - x₀) := by
    have hdiff : DifferentiableAt ℝ (fun y : Vec3 =>
        heatKernelSpaceDerivative y (r ^ 2 - (z.2 - t₀)) i) (z.1 - x₀) := by
      rw [show (fun y : Vec3 => heatKernelSpaceDerivative y
          (r ^ 2 - (z.2 - t₀)) i) = fun y : Vec3 =>
          -(y i) / (2 * (r ^ 2 - (z.2 - t₀))) *
            ((4 * Real.pi * (r ^ 2 - (z.2 - t₀))) ^ (-(3 : ℝ) / 2) *
              Real.exp (-(∑ j, y j ^ 2) /
                (4 * (r ^ 2 - (z.2 - t₀))))) by
        funext y
        rw [heatKernelSpaceDerivative, ite_eq_left hτ,
          heatKernel_eq_formula_sum hτ]]
      fun_prop (disch := positivity)
    simpa [smul_eq_mul] using hdiff.hasFDerivAt.const_mul (r ^ 2)
  have hcomp := houter.comp z.1 hinner
  have hvalue := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hcomp.fderiv
  dsimp at hvalue
  have hvalue' :
      (fderiv ℝ (fun x : Vec3 => r ^ 2 * heatKernelSpaceDerivative
        (x - x₀) (r ^ 2 - (z.2 - t₀)) i) z.1) (basisVec i) =
        (r ^ 2 • fderiv ℝ (fun y : Vec3 =>
          heatKernelSpaceDerivative y (r ^ 2 - (z.2 - t₀)) i) (z.1 - x₀) ∘SL
          ContinuousLinearMap.id ℝ Vec3) (basisVec i) := by
    simpa only [Function.comp_def] using hvalue
  calc
    (fderiv ℝ (fun x : Vec3 => r ^ 2 * heatKernelSpaceDerivative
        (x - x₀) (r ^ 2 - (z.2 - t₀)) i) z.1) (basisVec i) =
        (r ^ 2 • fderiv ℝ (fun y : Vec3 =>
          heatKernelSpaceDerivative y (r ^ 2 - (z.2 - t₀)) i) (z.1 - x₀) ∘SL
          ContinuousLinearMap.id ℝ Vec3) (basisVec i) := hvalue'
    _ = r ^ 2 * (fderiv ℝ (fun y : Vec3 =>
          heatKernelSpaceDerivative y (r ^ 2 - (z.2 - t₀)) i) (z.1 - x₀))
          (basisVec i) := by simp [smul_eq_mul]
    _ = r ^ 2 * heatKernelSpaceSecondDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) i := by
      rw [heatKernelSpaceDerivative_fderiv_apply_basisVec hτ i]

end CKN
