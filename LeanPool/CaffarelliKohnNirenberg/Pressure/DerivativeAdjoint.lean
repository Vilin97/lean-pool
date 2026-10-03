/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HeatKernelIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.IntegralBounds
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Derivative Adjoint

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

lemma pressure_coord_fderiv_eq_deriv_update {f : Vec3 → ℝ} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    (fderiv ℝ f x) (basisVec i) =
      deriv (fun s => f (Function.update x i s)) (x i) := by
  have hcomp := HasFDerivAt.comp (x i)
    (by simpa only [Function.update_eq_self] using hf.hasFDerivAt)
    (hasFDerivAt_update (𝕜 := ℝ) (i := i) x (x i))
  have hderiv := hcomp.hasDerivAt
  have hderiv' : HasDerivAt (fun s => f (Function.update x i s))
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

private lemma pressure_heatKernel_fderiv_apply {x : Vec3} {t : ℝ}
    (ht : 0 < t) (i : Fin 3) :
    (fderiv ℝ (fun z : Vec3 => heatKernel z t) x) (basisVec i) =
      heatKernelSpaceDerivative x t i := by
  have hdiff : DifferentiableAt ℝ (fun z : Vec3 => heatKernel z t) x := by
    rw [show (fun z : Vec3 => heatKernel z t) = fun z : Vec3 =>
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ j, z j ^ 2) / (4 * t)) by
      funext z
      exact heatKernel_eq_formula_sum ht]
    fun_prop (disch := positivity)
  rw [pressure_coord_fderiv_eq_deriv_update hdiff i]
  exact heatKernel_space_deriv ht i

private lemma pressure_heatKernel_shift_fderiv_apply {x y : Vec3} {t : ℝ}
    (ht : 0 < t) (i : Fin 3) :
    (fderiv ℝ (fun z : Vec3 => heatKernel (z-y) t) x) (basisVec i) =
      heatKernelSpaceDerivative (x-y) t i := by
  have houter : HasFDerivAt (fun z : Vec3 => heatKernel z t)
      (fderiv ℝ (fun z : Vec3 => heatKernel z t) (x-y)) (x-y) := by
    exact (by
      have hdiff : DifferentiableAt ℝ (fun z : Vec3 => heatKernel z t) (x-y) := by
        rw [show (fun z : Vec3 => heatKernel z t) = fun z : Vec3 =>
            (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
              Real.exp (-(∑ j, z j ^ 2) / (4 * t)) by
          funext z
          exact heatKernel_eq_formula_sum ht]
        fun_prop (disch := positivity)
      exact hdiff.hasFDerivAt)
  have hinner : HasFDerivAt (fun z : Vec3 => z-y)
      (ContinuousLinearMap.id ℝ Vec3) x := by
    convert (hasFDerivAt_id (𝕜 := ℝ) x).sub
      (hasFDerivAt_const (𝕜 := ℝ) y x) using 1
    · funext z
      rfl
    · ext z
      simp
  have hcomp := houter.comp x hinner
  have hval := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hcomp.fderiv
  dsimp at hval
  have hval' : (fderiv ℝ (fun z : Vec3 => heatKernel (z-y) t) x)
      (basisVec i) = (fderiv ℝ (fun z : Vec3 => heatKernel z t) (x-y))
        (basisVec i) := by
    change (fderiv ℝ (fun z : Vec3 => heatKernel (z-y) t) x)
      (basisVec i) = _ at hval
    exact hval
  rw [hval', pressure_heatKernel_fderiv_apply ht i]

private lemma pressure_heatKernel_derivative_continuous {t : ℝ} (ht : 0 < t)
    (i : Fin 3) : Continuous (fun z : Vec3 => heatKernelSpaceDerivative z t i) := by
  rw [show (fun z : Vec3 => heatKernelSpaceDerivative z t i) = fun z : Vec3 =>
      -(z i) / (2 * t) *
        ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ j, z j ^ 2) / (4 * t))) by
    funext z
    rw [heatKernelSpaceDerivative, ite_eq_left ht, heatKernel_eq_formula_sum ht]]
  fun_prop (disch := positivity)

private lemma pressure_heat_fixed_time_adjoint {ψ : Vec3 → ℝ} {y : Vec3}
    {t : ℝ} (ht : 0 < t) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (i : Fin 3) :
    ∫ x : Vec3, heatKernelSpaceDerivative (x-y) t i *
        spatialLaplacian ψ x =
      -∫ x : Vec3, heatKernel (x-y) t *
        spatialDeriv (spatialLaplacian ψ) i x := by
  let f : Vec3 → ℝ := fun x => heatKernel (x-y) t
  let g : Vec3 → ℝ := spatialLaplacian ψ
  have hf : Continuous f := by
    dsimp [f]
    have hc : Continuous (fun z : Vec3 => heatKernel z t) := by
      rw [show (fun z : Vec3 => heatKernel z t) = fun z : Vec3 =>
          (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, z j ^ 2) / (4 * t)) by
        funext z
        exact heatKernel_eq_formula_sum ht]
      fun_prop (disch := positivity)
    exact hc.comp (continuous_id.sub continuous_const)
  have hfd : Continuous (fun x : Vec3 =>
      (fderiv ℝ f x) (basisVec i)) := by
    rw [show (fun x : Vec3 => (fderiv ℝ f x) (basisVec i)) =
        fun x : Vec3 => heatKernelSpaceDerivative (x-y) t i by
      funext x
      dsimp [f]
      exact pressure_heatKernel_shift_fderiv_apply ht i]
    exact (pressure_heatKernel_derivative_continuous ht i).comp
      (continuous_id.sub continuous_const)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_spatialLaplacian_smooth hψ
  have hgc : HasCompactSupport g := by
    have hdiag (j : Fin 3) : HasCompactSupport
        (spatialDeriv (spatialDeriv ψ j) j) :=
      (hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply
        (𝕜 := ℝ) (basisVec j)
    have h01 : HasCompactSupport (fun z : Vec3 =>
        spatialDeriv (spatialDeriv ψ (0 : Fin 3)) 0 z +
          spatialDeriv (spatialDeriv ψ (1 : Fin 3)) 1 z) := by
      convert (hdiag 0).add (hdiag 1) using 1
    have hsum : HasCompactSupport (fun z : Vec3 =>
        spatialDeriv (spatialDeriv ψ (0 : Fin 3)) 0 z +
        spatialDeriv (spatialDeriv ψ (1 : Fin 3)) 1 z +
          spatialDeriv (spatialDeriv ψ (2 : Fin 3)) 2 z) := by
      convert h01.add (hdiag 2) using 1
    change HasCompactSupport (fun z : Vec3 =>
      ∑ j : Fin 3, spatialDeriv (spatialDeriv ψ j) j z)
    simpa only [Fin.sum_univ_three] using hsum
  have hgd : Continuous (fun x : Vec3 =>
      (fderiv ℝ g x) (basisVec i)) := by
    change Continuous (spatialDeriv (spatialLaplacian ψ) i)
    exact (contDiff_spatialDeriv_smooth hg i).continuous
  have hgdc : HasCompactSupport (fun x : Vec3 =>
      (fderiv ℝ g x) (basisVec i)) := by
    change HasCompactSupport (spatialDeriv (spatialLaplacian ψ) i)
    exact hgc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hfg : Integrable (fun x : Vec3 => f x * g x) volume :=
    (hf.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hfdg : Integrable (fun x : Vec3 =>
      (fderiv ℝ f x) (basisVec i) * g x) volume :=
    (hfd.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hfgd : Integrable (fun x : Vec3 =>
      f x * (fderiv ℝ g x) (basisVec i)) volume :=
    (hf.mul hgd).integrable_of_hasCompactSupport hgdc.mul_left
  have hdiff_f : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x := by
    intro x hx
    dsimp [f]
    have hdiff : DifferentiableAt ℝ (fun z : Vec3 => heatKernel z t) (x-y) := by
      rw [show (fun z : Vec3 => heatKernel z t) = fun z : Vec3 =>
          (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, z j ^ 2) / (4 * t)) by
        funext z
        exact heatKernel_eq_formula_sum ht]
      fun_prop (disch := positivity)
    have hcomp := DifferentiableAt.comp x hdiff
      (differentiableAt_id.sub (differentiableAt_const y))
    convert hcomp using 1
    funext z
    rfl
  have hdiff_g : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x := by
    intro x hx
    exact hg.differentiable (by simp) x
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := f) (g := g) (v := basisVec i) hfdg hfgd hfg hdiff_f hdiff_g
  have hrewrite : (fun x : Vec3 => (fderiv ℝ f x) (basisVec i) * g x) =
      (fun x : Vec3 => heatKernelSpaceDerivative (x-y) t i *
        spatialLaplacian ψ x) := by
    funext x
    dsimp [f, g]
    rw [pressure_heatKernel_shift_fderiv_apply ht i]
  have hrewrite' : (fun x : Vec3 => f x * (fderiv ℝ g x) (basisVec i)) =
      (fun x : Vec3 => heatKernel (x-y) t *
        spatialDeriv (spatialLaplacian ψ) i x) := by
    funext x
    dsimp [f, g, spatialDeriv]
  have hibp' := hibp
  rw [hrewrite'] at hibp'
  rw [hrewrite] at hibp'
  linarith only [hibp']

private lemma pressure_heat_derivative_integral {z : Vec3} (hz : z ≠ 0)
    (i : Fin 3) :
    ∫ t : ℝ in Ioi 0, heatKernelSpaceDerivative z t i =
      CKN.spatialDeriv newtonianKernel i z := by
  have hr : 0 < vec3EuclideanNorm z := by
    rw [vec3EuclideanNorm_eq_l2]
    apply norm_pos_iff.mpr
    intro hzero
    apply hz
    exact (WithLp.toLp_injective 2) hzero
  have hb : 0 < (vec3EuclideanNorm z) ^ 2 / 4 := by positivity
  have hform : (fun t : ℝ => heatKernelSpaceDerivative z t i) =ᵐ[
      volume.restrict (Ioi 0)] (fun t : ℝ =>
        -(z i) / 2 * (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
          (t ^ (-(5 : ℝ) / 2) *
            Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * t⁻¹))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    rw [heatKernelSpaceDerivative, ite_eq_left htpos]
    rw [heatKernel_eq_formula ht]
    rw [show 4 * Real.pi * t = (4 * Real.pi) * t by ring_nf,
      Real.mul_rpow (by positivity) ht.le]
    have ht0 : 0 < t := ht
    have hpow : t ^ (-(3 : ℝ) / 2) / t = t ^ (-(5 : ℝ) / 2) := by
      have htinv : t⁻¹ = t ^ (-1 : ℝ) := by
        rw [Real.rpow_neg ht0.le, Real.rpow_one]
      rw [div_eq_mul_inv, htinv, ← Real.rpow_add ht0]
      congr 1
      ring
    have hexp : -(vec3EuclideanNorm z) ^ 2 / (4 * t) =
        -((vec3EuclideanNorm z) ^ 2 / 4) * t⁻¹ := by
      field_simp
    rw [hexp]
    rw [show -(z i) / (2 * t) *
        ((4 * Real.pi) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) *
          Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * t⁻¹)) =
        -(z i) / 2 * (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
          (t ^ (-(3 : ℝ) / 2) / t *
            Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * t⁻¹)) by ring]
    rw [hpow]
  rw [integral_congr_ae hform]
  rw [show (fun t : ℝ =>
      -(z i) / 2 * (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
        (t ^ (-(5 : ℝ) / 2) *
          Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * t⁻¹))) =
      (fun t : ℝ => -(z i) / 2 * (4 * Real.pi) ^ (-(3 : ℝ) / 2)) *
        (fun t : ℝ => t ^ (-(5 : ℝ) / 2) *
          Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * t⁻¹)) by
    funext t
    dsimp]
  change (∫ t : ℝ in Ioi 0,
      (-(z i) / 2 * (4 * Real.pi) ^ (-(3 : ℝ) / 2)) *
        (t ^ (-(5 : ℝ) / 2) *
          Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * t⁻¹))) = _
  have hsub := integral_comp_rpow_Ioi
    (fun y : ℝ => y ^ ((1 : ℝ) / 2) *
      Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * y))
    (p := -(1 : ℝ)) (by norm_num)
  have hsub' :
      (∫ t : ℝ in Ioi 0, t ^ (-(5 : ℝ) / 2) *
        Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * t⁻¹)) =
      ∫ y : ℝ in Ioi 0, y ^ ((1 : ℝ) / 2) *
        Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * y) := by
    rw [← hsub]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have htpos : 0 < t := ht
    rw [smul_eq_mul]
    simp only [abs_neg, abs_one, one_mul]
    rw [← Real.rpow_mul htpos.le]
    have hpow : t ^ (-(1 : ℝ) - 1) *
        t ^ (-(1 : ℝ) * ((1 : ℝ) / 2)) = t ^ (-(5 : ℝ) / 2) := by
      calc
        t ^ (-(1 : ℝ) - 1) * t ^ (-(1 : ℝ) * ((1 : ℝ) / 2)) =
            t ^ ((-(1 : ℝ) - 1) + (-(1 : ℝ) * ((1 : ℝ) / 2))) :=
          (Real.rpow_add htpos _ _).symm
        _ = t ^ (-(5 : ℝ) / 2) := by
          congr 1
          ring_nf
    calc
      t ^ (-(5 : ℝ) / 2) *
          Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * t⁻¹) =
          (t ^ (-(1 : ℝ) - 1) *
            t ^ (-(1 : ℝ) * ((1 : ℝ) / 2))) *
            Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * t⁻¹) := by
        rw [hpow]
      _ = t ^ (-(1 : ℝ) - 1) *
          (t ^ (-(1 : ℝ) * ((1 : ℝ) / 2)) *
            Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * t⁻¹)) := by ring
      _ = t ^ (-(1 : ℝ) - 1) *
          (t ^ (-(1 : ℝ) * ((1 : ℝ) / 2)) *
            Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) *
              t ^ (-(1 : ℝ)))) := by
        rw [Real.rpow_neg htpos.le, Real.rpow_one]
  rw [integral_const_mul, hsub']
  have hgamma := integral_rpow_mul_exp_neg_mul_rpow
    (p := 1) (q := (1 : ℝ) / 2)
    (b := (vec3EuclideanNorm z) ^ 2 / 4) (by norm_num) (by norm_num) hb
  have hgamma' :
      (∫ y : ℝ in Ioi 0, y ^ ((1 : ℝ) / 2) *
        Real.exp (-((vec3EuclideanNorm z) ^ 2 / 4) * y)) =
      ((vec3EuclideanNorm z) ^ 2 / 4) ^ (-((1 : ℝ) / 2 + 1)) *
        (1 / 1) * Real.Gamma (((1 : ℝ) / 2 + 1) / 1) := by
    simpa only [Real.rpow_one, div_one] using hgamma
  rw [hgamma']
  norm_num only [one_div, div_one]
  have hgamma32 : Real.Gamma (3 / 2 : ℝ) =
      (1 / 2 : ℝ) * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num]
    rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
      Real.Gamma_one_half_eq]
  rw [hgamma32]
  have hrpow : ((vec3EuclideanNorm z) ^ 2 / 4) ^ (-(3 : ℝ) / 2) =
      8 / (vec3EuclideanNorm z) ^ 3 := by
    rw [Real.div_rpow (sq_nonneg _) (by norm_num)]
    have hn2 : (vec3EuclideanNorm z ^ 2) ^ (-(3 : ℝ) / 2) =
        vec3EuclideanNorm z ^ (-3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      norm_num
    rw [hn2, Real.rpow_neg hr.le]
    have h4 : (4 : ℝ) ^ (-(3 : ℝ) / 2) = 1 / 8 := by
      have h4pos : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
        norm_num
      rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
        Real.rpow_neg (by norm_num : 0 ≤ (4 : ℝ)), h4pos]
      norm_num
    rw [h4]
    field_simp
    rw [← Real.rpow_natCast]
    rw [Real.rpow_natCast]
    exact (Real.rpow_natCast (vec3EuclideanNorm z) 3).symm
  have hrpow' : ((vec3EuclideanNorm z) ^ 2 / 4) ^ (-(3 / 2 : ℝ)) =
      8 / (vec3EuclideanNorm z) ^ 3 := by
    convert hrpow using 1
    all_goals ring_nf
  rw [hrpow']
  rw [newtonianKernel_spatialDeriv_formula hz i]
  simp only [vec3EuclideanNorm, mul_one, one_div, mul_inv_rev, neg_mul]
  change -z i / 2 * (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
      (8 / vec3EuclideanNorm z ^ 3 * (2⁻¹ * Real.sqrt Real.pi)) =
    -(Real.pi⁻¹ * 4⁻¹ * z i * (∑ j, z j ^ 2) ^ (-(3 : ℝ) / 2))
  rw [← vec3EuclideanNorm_sq]
  have hnormpow : (vec3EuclideanNorm z ^ 2) ^ (-(3 : ℝ) / 2) =
      (vec3EuclideanNorm z) ^ (-3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  rw [hnormpow, Real.rpow_neg hr.le]
  field_simp
  have hbase : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) =
      (8 * Real.pi * Real.sqrt Real.pi)⁻¹ := by
    rw [show -(3 / 2 : ℝ) = -((3 : ℝ) / 2) by ring_nf,
      Real.rpow_neg (by positivity)]
    have hpow : (4 * Real.pi) ^ ((3 : ℝ) / 2) =
        8 * Real.pi * Real.sqrt Real.pi := by
      rw [show (3 : ℝ) / 2 = 1 + (1 / 2 : ℝ) by ring_nf,
        Real.rpow_add (by positivity), Real.rpow_one, Real.sqrt_eq_rpow,
        Real.mul_rpow (by norm_num) (by positivity)]
      have hfour : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
        rw [← Real.sqrt_eq_rpow]
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (by norm_num)]
      rw [hfour]
      ring_nf
    rw [hpow]
  rw [hbase]
  field_simp
  ring_nf
  exact congrArg (fun q : ℝ => -(z i * q * 4))
    (Real.rpow_natCast (vec3EuclideanNorm z) 3)

private lemma pressure_heat_derivative_integrable {ψ : Vec3 → ℝ} {y : Vec3}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (i : Fin 3) :
    Integrable (fun p : ℝ × Vec3 =>
      heatKernelSpaceDerivative (p.2-y) p.1 i * spatialLaplacian ψ p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  let g : Vec3 → ℝ := spatialLaplacian ψ
  let K : Set Vec3 := tsupport g
  let F : ℝ × Vec3 → ℝ := fun p =>
    heatKernelSpaceDerivative (p.2-y) p.1 i * g p.2
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_spatialLaplacian_smooth hψ
  have hgc : HasCompactSupport g := laplacian_compact_support_global hψc
  have hK : IsCompact K := hgc.isCompact
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hCbound : ∃ C, 0 ≤ C ∧ ∀ x, ‖g x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg.continuous
    have hC0 : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hC 0)
    exact ⟨C, hC0, hC⟩
  obtain ⟨C, hC0, hC⟩ := hCbound
  have hFmeas : AEStronglyMeasurable F
      ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    have hheat : Measurable (fun p : ℝ × Vec3 =>
        heatKernel (p.2-y) p.1) := by
      unfold heatKernel
      apply Measurable.ite (measurableSet_Ioi.preimage measurable_fst)
      · fun_prop
      · exact measurable_const
    have hderiv : Measurable (fun p : ℝ × Vec3 =>
        heatKernelSpaceDerivative (p.2-y) p.1 i) := by
      unfold heatKernelSpaceDerivative
      apply Measurable.ite (measurableSet_Ioi.preimage measurable_fst)
      · have hcoord : Measurable (fun p : ℝ × Vec3 => (p.2-y) i) :=
          (measurable_pi_apply i).comp (measurable_snd.sub measurable_const)
        have hden : Measurable (fun p : ℝ × Vec3 => (2 : ℝ) * p.1) :=
          measurable_const.mul measurable_fst
        have hm := hcoord.div hden |>.neg.mul hheat
        convert hm using 1
        funext p
        dsimp
        ring
      · exact measurable_const
    have hgmeas : Measurable (fun p : ℝ × Vec3 => g p.2) :=
      hg.continuous.measurable.comp measurable_snd
    exact (hderiv.mul hgmeas).aestronglyMeasurable
  have hnearBase : Integrable (fun p : ℝ × Vec3 =>
      heatKernelGradientNorm (p.2-y) p.1)
      ((volume.restrict (Ioc 0 1)).prod volume) := by
    have hgrad := (heatKernelGradientNorm_integrable_prod (T := 1)
      (by norm_num : (0 : ℝ) < 1)).swap
    have hgrad' : Integrable (fun p : ℝ × Vec3 =>
        heatKernelGradientNorm p.2 p.1)
        ((volume.restrict (Ioc 0 1)).prod volume) := by
      convert hgrad using 1
      funext p
      rfl
    let S : ℝ × Vec3 → ℝ × Vec3 := Prod.map id (fun x : Vec3 => x-y)
    have hS : MeasurePreserving S
        ((volume.restrict (Ioc 0 1)).prod volume)
        ((volume.restrict (Ioc 0 1)).prod volume) := by
      exact MeasurePreserving.prod
        (MeasurePreserving.id (volume.restrict (Ioc 0 1)))
        (measurePreserving_sub_right volume y)
    have hshift := (hS.integrable_comp hgrad'.aestronglyMeasurable).2 hgrad'
    change Integrable (fun p : ℝ × Vec3 =>
      heatKernelGradientNorm (p.2-y) p.1)
      ((volume.restrict (Ioc 0 1)).prod volume) at hshift
    exact hshift
  have hnearMajor : Integrable (fun p : ℝ × Vec3 => C *
      heatKernelGradientNorm (p.2-y) p.1)
      ((volume.restrict (Ioc 0 1)).prod volume) :=
    hnearBase.const_mul C
  have hnear : IntegrableOn F (Ioc 0 1 ×ˢ (Set.univ : Set Vec3))
      ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    change Integrable F ((volume.prod volume).restrict
      (Ioc 0 1 ×ˢ (Set.univ : Set Vec3)))
    rw [← Measure.prod_restrict]
    have hFmeasNear : AEStronglyMeasurable F
        ((volume.restrict (Ioc 0 1)).prod volume) := by
      have h := hFmeas.restrict (s := Ioc 0 1 ×ˢ (Set.univ : Set Vec3))
      rw [← Measure.prod_restrict] at h
      simpa only [Measure.restrict_univ] using h
    have hnear0 : Integrable F ((volume.restrict (Ioc 0 1)).prod volume) := by
      apply hnearMajor.mono' hFmeasNear
      filter_upwards [] with p
      by_cases hp : p.2 ∈ K
      · have hderiv : |heatKernelSpaceDerivative (p.2-y) p.1 i| ≤
            heatKernelGradientNorm (p.2-y) p.1 := by
          unfold heatKernelGradientNorm
          exact Finset.single_le_sum
            (fun j _hj => abs_nonneg (heatKernelSpaceDerivative (p.2-y) p.1 j))
            (Finset.mem_univ i)
        have hg' : ‖g p.2‖ ≤ C := hC p.2
        dsimp [F]
        rw [abs_mul]
        calc
          |heatKernelSpaceDerivative (p.2 - y) p.1 i| * |g p.2| ≤
              heatKernelGradientNorm (p.2-y) p.1 * C :=
            mul_le_mul hderiv hg' (abs_nonneg _)
              (by unfold heatKernelGradientNorm; positivity)
          _ = C * heatKernelGradientNorm (p.2-y) p.1 := by ring
      · have hz : g p.2 = 0 := image_eq_zero_of_notMem_tsupport hp
        simp only [hz, mul_zero, norm_zero, ge_iff_le, F]
        exact mul_nonneg hC0 (by unfold heatKernelGradientNorm; positivity)
    simpa only [Measure.restrict_univ] using hnear0
  have ht2 : Integrable (fun t : ℝ => t ^ (-2 : ℝ))
      (volume.restrict (Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).integrable
  have hKone : Integrable (K.indicator (fun _ : Vec3 => (1 : ℝ))) volume := by
    apply (integrable_indicator_iff hKmeas).2
    exact integrableOn_const hK.measure_lt_top.ne
  have htailBase : Integrable (fun p : ℝ × Vec3 =>
      p.1 ^ (-2 : ℝ) * K.indicator (fun _ : Vec3 => (1 : ℝ)) p.2)
      ((volume.restrict (Ioi 1)).prod volume) := by
    simpa only using ht2.mul_prod hKone
  have htailMajor : Integrable (fun p : ℝ × Vec3 =>
      300000 * C * (p.1 ^ (-2 : ℝ) *
        K.indicator (fun _ : Vec3 => (1 : ℝ)) p.2))
      ((volume.restrict (Ioi 1)).prod volume) :=
    htailBase.const_mul (300000 * C)
  have htail : IntegrableOn F (Ioi 1 ×ˢ (Set.univ : Set Vec3))
      ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    change Integrable F ((volume.prod volume).restrict
      (Ioi 1 ×ˢ (Set.univ : Set Vec3)))
    have htailMajor' : Integrable (fun p : ℝ × Vec3 =>
        300000 * C * (p.1 ^ (-2 : ℝ) *
          K.indicator (fun _ : Vec3 => (1 : ℝ)) p.2))
        ((volume.prod volume).restrict (Ioi 1 ×ˢ (Set.univ : Set Vec3))) := by
      rw [← Measure.prod_restrict]
      simpa only [Measure.restrict_univ] using htailMajor
    have hFmeasTail : AEStronglyMeasurable F
        ((volume.prod volume).restrict (Ioi 1 ×ˢ (Set.univ : Set Vec3))) :=
      hFmeas.restrict
    have htail0 : Integrable F ((volume.prod volume).restrict
        (Ioi 1 ×ˢ (Set.univ : Set Vec3))) := by
      apply htailMajor'.mono' hFmeasTail
      filter_upwards [ae_restrict_mem
        (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp_time
      by_cases hp : p.2 ∈ K
      · have ht : 1 < p.1 := hp_time.1
        have ht0 : 0 < p.1 := lt_trans zero_lt_one ht
        have hrho : Real.sqrt p.1 ≤ rhoTwo (p.2-y) p.1 := by
          unfold rhoTwo
          exact le_add_of_nonneg_left (vec3EuclideanNorm_nonneg (p.2-y))
        have hpow : p.1 ^ (2 : ℕ) ≤ rhoTwo (p.2-y) p.1 ^ 4 := by
          have hs : (Real.sqrt p.1) ^ 4 ≤ rhoTwo (p.2-y) p.1 ^ 4 := by
            gcongr
          have hsquare : p.1 ^ (2 : ℕ) = (Real.sqrt p.1) ^ 4 := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
              Real.sq_sqrt ht0.le]
          rw [hsquare]
          exact hs
        have hrhopos : 0 < rhoTwo (p.2-y) p.1 ^ 4 := by
          have : 0 < rhoTwo (p.2-y) p.1 := lt_of_lt_of_le
            (Real.sqrt_pos.2 ht0) hrho
          positivity
        have htpowpos : 0 < p.1 ^ (2 : ℕ) := by positivity
        have hinv : (rhoTwo (p.2-y) p.1 ^ 4)⁻¹ ≤
            (p.1 ^ (2 : ℕ))⁻¹ := (inv_le_inv₀ hrhopos htpowpos).2 hpow
        have hkernel : |heatKernelSpaceDerivative (p.2-y) p.1 i| ≤
            300000 * p.1 ^ (-2 : ℝ) := by
          have hraw := heatKernelSpaceDerivative_abs_le_rho_inv_four
            (x := p.2-y) (t := p.1) ht0 i
          calc
            |heatKernelSpaceDerivative (p.2-y) p.1 i| ≤
                300000 / rhoTwo (p.2-y) p.1 ^ 4 := hraw
            _ = 300000 * (rhoTwo (p.2-y) p.1 ^ 4)⁻¹ := by ring
            _ ≤ 300000 * (p.1 ^ (2 : ℕ))⁻¹ := by gcongr
            _ = 300000 * p.1 ^ (-2 : ℝ) := by
              rw [Real.rpow_neg ht0.le]
              rw [← Real.rpow_natCast, Real.rpow_natCast]
              exact congrArg (fun q : ℝ => 300000 * q⁻¹)
                (Real.rpow_natCast p.1 2).symm
        have hg' : |g p.2| ≤ C := by
          simpa only [Real.norm_eq_abs] using hC p.2
        have hmain : ‖F p‖ ≤ 300000 * C *
            (p.1 ^ (-2 : ℝ) * K.indicator (fun _ : Vec3 => (1 : ℝ)) p.2) := by
          rw [Real.norm_eq_abs, abs_mul, Set.indicator_of_mem hp]
          calc
            |heatKernelSpaceDerivative (p.2-y) p.1 i| * |g p.2| ≤
                (300000 * p.1 ^ (-2 : ℝ)) * C := by
              exact mul_le_mul hkernel hg' (abs_nonneg _) (by positivity)
            _ = 300000 * C * (p.1 ^ (-2 : ℝ) * 1) := by ring
        exact hmain
      · have hz : g p.2 = 0 := image_eq_zero_of_notMem_tsupport hp
        simp [F, hz, Set.indicator_of_notMem hp]
    exact htail0
  have hall : IntegrableOn F (Ioi 0 ×ˢ (Set.univ : Set Vec3))
      ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
      Set.union_prod, integrableOn_union]
    exact ⟨hnear, htail⟩
  have hall' : Integrable F ((volume.prod volume).restrict
      (Ioi 0 ×ˢ (Set.univ : Set Vec3))) := hall
  rw [← Measure.prod_restrict] at hall'
  simpa only [Measure.restrict_univ] using hall'

private lemma pressure_newtonian_derivative_adjoint_aux {ψ : Vec3 → ℝ} {y : Vec3}
    {i : Fin 3} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hF : Integrable (fun p : ℝ × Vec3 =>
      heatKernelSpaceDerivative (p.2-y) p.1 i * spatialLaplacian ψ p.2)
      ((volume.restrict (Ioi 0)).prod volume))
    (hG : Integrable (fun p : ℝ × Vec3 =>
      heatKernel (p.2-y) p.1 * spatialDeriv (spatialLaplacian ψ) i p.2)
      ((volume.restrict (Ioi 0)).prod volume)) :
    ∫ x : Vec3, spatialDeriv newtonianKernel i (x-y) * spatialLaplacian ψ x =
      spatialDeriv ψ i y := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ × Vec3 → ℝ := fun p =>
    heatKernelSpaceDerivative (p.2-y) p.1 i * spatialLaplacian ψ p.2
  let G : ℝ × Vec3 → ℝ := fun p =>
    heatKernel (p.2-y) p.1 * spatialDeriv (spatialLaplacian ψ) i p.2
  have hswapF := MeasureTheory.integral_integral_swap (f := fun t x => F (t,x)) hF
  have hswapG := MeasureTheory.integral_integral_swap (f := fun t x => G (t,x)) hG
  have hleft : ∫ x : Vec3, ∫ t : ℝ, F (t,x) ∂μ =
      ∫ x : Vec3, spatialDeriv newtonianKernel i (x-y) *
        spatialLaplacian ψ x := by
    apply integral_congr_ae
    filter_upwards [ae_ne volume y] with x hxy
    have hz : x-y ≠ 0 := sub_ne_zero.mpr hxy
    rw [show (fun t : ℝ => F (t,x)) = fun t =>
        heatKernelSpaceDerivative (x-y) t i * spatialLaplacian ψ x by rfl]
    rw [integral_mul_const]
    rw [pressure_heat_derivative_integral hz i]
  have htime : ∫ t : ℝ, ∫ x : Vec3, F (t,x) ∂volume ∂μ =
      ∫ t : ℝ, -∫ x : Vec3, G (t,x) ∂volume ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (∫ x : Vec3, heatKernelSpaceDerivative (x-y) t i *
        spatialLaplacian ψ x) =
      -∫ x : Vec3, heatKernel (x-y) t *
        spatialDeriv (spatialLaplacian ψ) i x
    exact pressure_heat_fixed_time_adjoint ht hψ hψc i
  have hright : ∫ x : Vec3, ∫ t : ℝ, F (t,x) ∂μ =
      spatialDeriv ψ i y := by
    rw [← hswapF, htime]
    have hrepr := newtonian_representation_smooth
      (contDiff_spatialDeriv_smooth hψ i)
      (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)) y
    have hswapG' : ∫ t : ℝ, ∫ x : Vec3, G (t,x) ∂volume ∂μ =
        ∫ x : Vec3, ∫ t : ℝ, G (t,x) ∂μ ∂volume := hswapG
    have htimeG : (∫ t : ℝ, -∫ x : Vec3, G (t,x) ∂volume ∂μ) =
        -∫ x : Vec3, ∫ t : ℝ, G (t,x) ∂μ ∂volume := by
      calc
        (∫ t : ℝ, -∫ x : Vec3, G (t,x) ∂volume ∂μ) =
            -∫ t : ℝ, ∫ x : Vec3, G (t,x) ∂volume ∂μ := by
              simpa only using (integral_neg (μ := μ)
                (f := fun t : ℝ => ∫ x : Vec3, G (t,x) ∂volume))
        _ = -∫ x : Vec3, ∫ t : ℝ, G (t,x) ∂μ ∂volume :=
          congrArg Neg.neg hswapG'
    rw [htimeG]
    have hcommute : spatialLaplacian (spatialDeriv ψ i) =
        spatialDeriv (spatialLaplacian ψ) i := by
      funext x
      unfold spatialLaplacian spatialDeriv
      rw [show (fun x : Vec3 => ∑ j : Fin 3,
          (fderiv ℝ (fun z => (fderiv ℝ ψ z) (basisVec j)) x)
            (basisVec j)) =
        ∑ j : Fin 3, (fun x : Vec3 =>
          (fderiv ℝ (fun z => (fderiv ℝ ψ z) (basisVec j)) x)
            (basisVec j)) by
          funext z
          rfl]
      rw [fderiv_sum]
      · change (∑ j : Fin 3, (fderiv ℝ (fun x =>
          (fderiv ℝ (fun z => (fderiv ℝ ψ z) (basisVec i)) x)
            (basisVec j)) x) (basisVec j)) =
          ∑ j : Fin 3, (fderiv ℝ (fun x =>
            (fderiv ℝ (fun z => (fderiv ℝ ψ z) (basisVec j)) x)
              (basisVec j)) x) (basisVec i)
        apply Finset.sum_congr rfl
        intro j hj
        change spatialDeriv (mixedSecond ψ j i) j x =
          spatialDeriv (mixedSecond ψ j j) i x
        exact thirdDerivative_identity hψ i j x
      · intro j hj
        exact (contDiff_spatialDeriv_smooth
          (contDiff_spatialDeriv_smooth hψ j) j).differentiable (by simp) x
    rw [hrepr]
    apply congrArg Neg.neg
    apply integral_congr_ae
    filter_upwards [ae_ne volume y] with x hxy
    have hz : x-y ≠ 0 := sub_ne_zero.mpr hxy
    rw [show (fun t : ℝ => G (t,x)) = fun t =>
        heatKernel (x-y) t * spatialDeriv (spatialLaplacian ψ) i x by rfl]
    rw [integral_mul_const, heatKernel_integral_Ioi hz]
    rw [← hcommute]
    rw [newtonianKernel]
    rw [show y - x = -(x-y) by ring]
    have hnorm : vec3EuclideanNorm (-(x-y)) = vec3EuclideanNorm (x-y) := by
      unfold vec3EuclideanNorm
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Pi.neg_apply]
      ring
    rw [hnorm]
  exact hleft.symm.trans hright

theorem pressure_newtonian_derivative_adjoint {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (i : Fin 3) (y : Vec3) :
    ∫ x : Vec3, spatialDeriv newtonianKernel i (x-y) * spatialLaplacian ψ x =
      spatialDeriv ψ i y := by
  exact pressure_newtonian_derivative_adjoint_aux hψ hψc
    (pressure_heat_derivative_integrable hψ hψc i)
    (pressure_heat_kernel_integrable hψ hψc i)

theorem pressureNewtonianDerivativePotential_distributional_pairing_smooth
    {i : Fin 3} {g ψ : Vec3 → ℝ} (hg : Integrable g volume)
    (hgc : HasCompactSupport g) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, pressureNewtonianDerivativePotential i g x * spatialLaplacian ψ x =
      ∫ y, g y * spatialDeriv ψ i y := by
  exact pressureNewtonianDerivativePotential_distributional_pairing
    hg hgc hψ hψc (fun y => pressure_newtonian_derivative_adjoint hψ hψc i y)

end CKN
