/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairingHeat
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.HessianL2
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DerivativeAdjoint
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.IntegralBounds
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # The first-order Newtonian adjoint and the smooth pairing

The singular identity `∫ ∂ᵢN(x - y) ∂ⱼψ(x) dx = -∫ N(x - y) ∂ᵢ∂ⱼψ(x) dx` is
obtained by heat subordination: at each positive time the Gaussian kernel is
smooth, so the identity is the ordinary compactly supported integration by
parts, and the time integral of the Gaussian family reproduces the Newtonian
kernel and its first derivative.  Fubini in the time variable is legitimate
because the test function has compact support.

Combining this with the Fubini pairing for potentials and with two classical
integrations by parts gives, for smooth compactly supported data `G`,

`∫ Pᵢ(G) ∂ⱼψ = ∫ ∂ᵢ∂ⱼ(N * G) ψ`,

which is the smooth case of the distributional adjointness used for the
`L^(6/5)` Calderón--Zygmund endpoint.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

private lemma coord_fderiv_eq_deriv_update {f : Vec3 → ℝ} {x : Vec3}
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

private lemma heatKernel_fderiv_apply {x : Vec3} {t : ℝ}
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
  rw [coord_fderiv_eq_deriv_update hdiff i]
  exact heatKernel_space_deriv ht i

private lemma heatKernel_shift_fderiv_apply {x y : Vec3} {t : ℝ}
    (ht : 0 < t) (i : Fin 3) :
    (fderiv ℝ (fun z : Vec3 => heatKernel (z-y) t) x) (basisVec i) =
      heatKernelSpaceDerivative (x-y) t i := by
  have houter : HasFDerivAt (fun z : Vec3 => heatKernel z t)
      (fderiv ℝ (fun z : Vec3 => heatKernel z t) (x-y)) (x-y) := by
    have hdiff : DifferentiableAt ℝ (fun z : Vec3 => heatKernel z t) (x-y) := by
      rw [show (fun z : Vec3 => heatKernel z t) = fun z : Vec3 =>
          (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, z j ^ 2) / (4 * t)) by
        funext z
        exact heatKernel_eq_formula_sum ht]
      fun_prop (disch := positivity)
    exact hdiff.hasFDerivAt
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
  have hval' : (fderiv ℝ (fun z : Vec3 => heatKernel (z-y) t)
      x) (basisVec i) = (fderiv ℝ (fun z : Vec3 => heatKernel z t) (x-y))
        (basisVec i) := by
    change (fderiv ℝ (fun z : Vec3 => heatKernel (z-y) t) x)
      (basisVec i) = _ at hval
    exact hval
  rw [hval', heatKernel_fderiv_apply ht i]

private lemma heatKernel_derivative_continuous {t : ℝ} (ht : 0 < t)
    (i : Fin 3) : Continuous (fun z : Vec3 => heatKernelSpaceDerivative z t i) := by
  rw [show (fun z : Vec3 => heatKernelSpaceDerivative z t i) = fun z : Vec3 =>
      -(z i) / (2 * t) *
        ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ j, z j ^ 2) / (4 * t))) by
    funext z
    rw [heatKernelSpaceDerivative, ite_eq_left ht, heatKernel_eq_formula_sum ht]]
  fun_prop (disch := positivity)

private lemma heat_fixed_time_derivative_adjoint {g : Vec3 → ℝ} {y : Vec3}
    {t : ℝ} (ht : 0 < t) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (i : Fin 3) :
    ∫ x : Vec3, heatKernelSpaceDerivative (x-y) t i * g x =
      -∫ x : Vec3, heatKernel (x-y) t * spatialDeriv g i x := by
  let f : Vec3 → ℝ := fun x => heatKernel (x-y) t
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
      exact heatKernel_shift_fderiv_apply ht i]
    exact (heatKernel_derivative_continuous ht i).comp
      (continuous_id.sub continuous_const)
  have hgd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g i) :=
    contDiff_spatialDeriv_smooth hg i
  have hgc' : HasCompactSupport (spatialDeriv g i) := by
    change HasCompactSupport (fun x => (fderiv ℝ g x) (basisVec i))
    exact hgc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hfg : Integrable (fun x : Vec3 => f x * g x) volume :=
    (hf.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hfdg : Integrable (fun x : Vec3 =>
      (fderiv ℝ f x) (basisVec i) * g x) volume :=
    (hfd.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hfgd : Integrable (fun x : Vec3 =>
      f x * (fderiv ℝ g x) (basisVec i)) volume :=
    (hf.mul hgd.continuous).integrable_of_hasCompactSupport
      (hgc'.mul_left (f := f))
  have hfdiff : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x := by
    intro x _
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
  have hgdiff : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x := by
    intro x _
    exact hg.differentiable (by simp) x
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := f) (g := g) (v := basisVec i) hfdg hfgd hfg hfdiff hgdiff
  have hrewrite : (fun x : Vec3 =>
      (fderiv ℝ f x) (basisVec i) * g x) =
      (fun x : Vec3 => heatKernelSpaceDerivative (x-y) t i * g x) := by
    funext x
    dsimp [f]
    rw [heatKernel_shift_fderiv_apply ht i]
  have hrewrite' : (fun x : Vec3 =>
      f x * (fderiv ℝ g x) (basisVec i)) =
      (fun x : Vec3 => heatKernel (x-y) t * spatialDeriv g i x) := by
    funext x
    dsimp [f, spatialDeriv]
  have hibp' := hibp
  rw [hrewrite'] at hibp'
  rw [hrewrite] at hibp'
  linarith only [hibp']

private lemma heat_derivative_integral {z : Vec3} (hz : z ≠ 0)
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
    have hpow : t ^ (-(3 : ℝ) / 2) / t = t ^ (-(5 : ℝ) / 2) := by
      have htinv : t⁻¹ = t ^ (-1 : ℝ) := by
        rw [Real.rpow_neg htpos.le, Real.rpow_one]
      rw [div_eq_mul_inv, htinv, ← Real.rpow_add htpos]
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
        t ^ (-(1 : ℝ) * ((1 : ℝ) / 2)) =
        t ^ (-(5 : ℝ) / 2) := by
      calc
        t ^ (-(1 : ℝ) - 1) *
            t ^ (-(1 : ℝ) * ((1 : ℝ) / 2)) =
            t ^ ((-(1 : ℝ) - 1) + (-(1 : ℝ) * ((1 : ℝ) / 2))) :=
          (Real.rpow_add htpos _ _).symm
        _ = t ^ (-(5 : ℝ) / 2) := by congr 1; ring_nf
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
    rw [← Real.rpow_natCast, Real.rpow_natCast]
    exact (Real.rpow_natCast (vec3EuclideanNorm z) 3).symm
  have hrpow' : ((vec3EuclideanNorm z) ^ 2 / 4) ^ (-(3 / 2 : ℝ)) =
      8 / (vec3EuclideanNorm z) ^ 3 := by
    convert hrpow using 1
    all_goals ring_nf
  rw [hrpow']
  rw [newtonianKernel_spatialDeriv_formula hz i]
  simp [vec3EuclideanNorm]
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
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
      rw [hfour]
      ring_nf
    rw [hpow]
  rw [hbase]
  field_simp
  ring_nf
  exact congrArg (fun q : ℝ => -(z i * q * 4))
    (Real.rpow_natCast (vec3EuclideanNorm z) 3)

/-- The first-order Newtonian kernel adjoint.  Heat subordination reduces the
singular identity to the ordinary compactly supported integration-by-parts
identity at each positive time. -/
theorem newtonian_derivative_kernel_adjoint {ψ : Vec3 → ℝ} {y : Vec3}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin 3) :
    ∫ x : Vec3, spatialDeriv newtonianKernel i (x-y) * spatialDeriv ψ j x =
      -∫ x : Vec3, newtonianKernel (x-y) * mixedSecond ψ i j x := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ × Vec3 → ℝ := fun p =>
    heatKernelSpaceDerivative (p.2-y) p.1 i * spatialDeriv ψ j p.2
  let G : ℝ × Vec3 → ℝ := fun p =>
    heatKernel (p.2-y) p.1 * mixedSecond ψ i j p.2
  have hF : Integrable F (μ.prod volume) := by
    change Integrable (fun p : ℝ × Vec3 =>
      heatKernelSpaceDerivative (p.2-y) p.1 i * spatialDeriv ψ j p.2)
      ((volume.restrict (Ioi 0)).prod volume)
    exact heat_derivative_mul_compact_integrable
      (contDiff_spatialDeriv_smooth hψ j)
      (hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)) i
  have hG : Integrable G (μ.prod volume) := by
    change Integrable (fun p : ℝ × Vec3 =>
      heatKernel (p.2-y) p.1 * mixedSecond ψ i j p.2)
      ((volume.restrict (Ioi 0)).prod volume)
    exact heat_kernel_mul_compact_integrable
      (contDiff_mixedSecond_smooth hψ i j)
      ((hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply
        (𝕜 := ℝ) (basisVec i))
  have hswapF := MeasureTheory.integral_integral_swap
    (f := fun t x => F (t,x)) hF
  have hswapG := MeasureTheory.integral_integral_swap
    (f := fun t x => G (t,x)) hG
  have hleft : ∫ x : Vec3, ∫ t : ℝ, F (t,x) ∂μ =
      ∫ x : Vec3, spatialDeriv newtonianKernel i (x-y) *
        spatialDeriv ψ j x := by
    apply integral_congr_ae
    filter_upwards [ae_ne volume y] with x hxy
    have hz : x-y ≠ 0 := sub_ne_zero.mpr hxy
    rw [show (fun t : ℝ => F (t,x)) = fun t =>
        heatKernelSpaceDerivative (x-y) t i * spatialDeriv ψ j x by rfl]
    rw [integral_mul_const, heat_derivative_integral hz i]
  have htime : ∫ t : ℝ, ∫ x : Vec3, F (t,x) ∂volume ∂μ =
      ∫ t : ℝ, -∫ x : Vec3, G (t,x) ∂volume ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (∫ x : Vec3, heatKernelSpaceDerivative (x-y) t i *
        spatialDeriv ψ j x) =
      -∫ x : Vec3, heatKernel (x-y) t * mixedSecond ψ i j x
    exact heat_fixed_time_derivative_adjoint (g := spatialDeriv ψ j) ht
      (contDiff_spatialDeriv_smooth hψ j)
      (hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)) i
  have hright : ∫ x : Vec3, ∫ t : ℝ, F (t,x) ∂μ =
      -∫ x : Vec3, newtonianKernel (x-y) * mixedSecond ψ i j x := by
    rw [← hswapF, htime]
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
    apply congrArg Neg.neg
    apply integral_congr_ae
    filter_upwards [ae_ne volume y] with x hxy
    have hz : x-y ≠ 0 := sub_ne_zero.mpr hxy
    rw [show (fun t : ℝ => G (t,x)) = fun t =>
        heatKernel (x-y) t * mixedSecond ψ i j x by rfl]
    rw [integral_mul_const, heatKernel_integral_Ioi hz]
    rw [newtonianKernel]
  exact hleft.symm.trans hright

private lemma smooth_ibp {u φ : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (i : Fin 3) :
    ∫ x, u x * spatialDeriv φ i x =
      -∫ x, spatialDeriv u i x * φ x := by
  have hφd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv φ i) :=
    contDiff_spatialDeriv_smooth hφ i
  have hud : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv u i) :=
    contDiff_spatialDeriv_smooth hu i
  have hφdc : HasCompactSupport (spatialDeriv φ i) := by
    change HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec i))
    exact hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hleft : Integrable (fun x => u x * spatialDeriv φ i x) volume :=
    (hu.continuous.mul hφd.continuous).integrable_of_hasCompactSupport
      (hφdc.mul_left (f := u))
  have hright : Integrable (fun x => spatialDeriv u i x * φ x) volume :=
    (hud.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      (hφc.mul_left (f := spatialDeriv u i))
  have hprod : Integrable (fun x => u x * φ x) volume :=
    (hu.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      (hφc.mul_left (f := u))
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Vec3)) (v := basisVec i) hright hleft hprod
    (fun x _ => hu.differentiable (by norm_num) x)
    (fun x _ => hφ.differentiable (by norm_num) x)
  simpa only [spatialDeriv] using h

private lemma smooth_mixed_pairing {u ψ : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin 3) :
    ∫ x, u x * mixedSecond ψ i j x =
      ∫ x, mixedSecond u i j x * ψ x := by
  have hfirst := smooth_ibp hu
    (contDiff_spatialDeriv_smooth hψ j)
    (hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)) i
  have hsecond := smooth_ibp (contDiff_spatialDeriv_smooth hu i)
    hψ hψc j
  have hswap : ∀ x, mixedSecond u i j x = mixedSecond u j i x :=
    mixedSecond_swap hu i j
  calc
    ∫ x, u x * mixedSecond ψ i j x =
        -∫ x, spatialDeriv u i x * spatialDeriv ψ j x := by
      simpa only [mixedSecond] using hfirst
    _ = ∫ x, mixedSecond u j i x * ψ x := by
      have hsecond' :
          ∫ x, spatialDeriv u i x * spatialDeriv ψ j x =
            -∫ x, mixedSecond u j i x * ψ x := by
        simpa only [mixedSecond] using hsecond
      rw [hsecond']
      simp only [neg_neg]
    _ = ∫ x, mixedSecond u i j x * ψ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hswap x]

/-- For smooth compactly supported data the first derivative potential is
adjoint to the classical Hessian of the Newtonian potential. -/
theorem pressure_newtonian_derivative_potential_smooth_pairing
    {i j : Fin 3} {G ψ : Vec3 → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x =
      ∫ x, mixedSecond (pressureNewtonianPotential G) i j x * ψ x := by
  have hGi : Integrable G volume :=
    hG.continuous.integrable_of_hasCompactSupport hGc
  have hinner : ∀ y, ∫ x, spatialDeriv newtonianKernel i (x-y) *
      spatialDeriv ψ j x =
        -∫ x, newtonianKernel (x-y) * mixedSecond ψ i j x := by
    intro y
    exact newtonian_derivative_kernel_adjoint hψ hψc i j
  have hderiv := pressureNewtonianDerivativePotential_pairing hGi hGc
    (contDiff_spatialDeriv_smooth hψ j)
    (hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)) hinner
  have hpot := pressureNewtonianPotential_pairing hGi hGc
    (contDiff_mixedSecond_smooth hψ i j)
    ((hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply
      (𝕜 := ℝ) (basisVec i))
  have hrewrite :
      (∫ y, G y * (-∫ x, newtonianKernel (x-y) * mixedSecond ψ i j x)) =
        ∫ y, G y * (∫ x, (-newtonianKernel (x-y)) *
          mixedSecond ψ i j x) := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [← integral_neg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  calc
    ∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x =
        ∫ y, G y * (-∫ x, newtonianKernel (x-y) * mixedSecond ψ i j x) := by
      rw [hderiv]
    _ = ∫ y, G y * (∫ x, (-newtonianKernel (x-y)) *
          mixedSecond ψ i j x) := hrewrite
    _ = ∫ x, pressureNewtonianPotential G x * mixedSecond ψ i j x := by
      rw [hpot]
    _ = ∫ x, mixedSecond (pressureNewtonianPotential G) i j x * ψ x := by
      exact smooth_mixed_pairing
        (pressureNewtonianPotential_smooth hG hGc) hψ hψc i j

end CKN.Foundation.Euclidean
