/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Interior
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Hessian L2

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

lemma pressure_neg_kernel_locallyIntegrable :
    LocallyIntegrable (fun z : Vec3 => -Foundation.Heat.newtonianKernel z) volume := by
  have hbound : ∀ᵐ z : Vec3, ‖-Foundation.Heat.newtonianKernel z‖ ≤
      (4 * Real.pi)⁻¹ * ‖z‖ ^ (-1 : ℝ) := by
    filter_upwards [Measure.ae_ne volume (0 : Vec3)] with z hz
    have hb := Foundation.Heat.newtonianKernel_size_bound hz
    rw [norm_neg, Real.rpow_neg (norm_nonneg _), Real.rpow_one]
    simpa only [Real.norm_eq_abs] using hb
  have hmeas : Measurable (fun z : Vec3 => -Foundation.Heat.newtonianKernel z) := by
    have hnorm : Measurable (fun z : Vec3 => vec3EuclideanNorm z) := by
      unfold vec3EuclideanNorm
      fun_prop
    have hk : Measurable (Foundation.Heat.newtonianKernel : Vec3 → ℝ) := by
      unfold Foundation.Heat.newtonianKernel
      exact measurable_const.div (measurable_const.mul hnorm)
    exact hk.neg
  refine locallyIntegrable_of_norm_le_rpow (E := Vec3) (F := ℝ)
    (by change 1 ≤ Module.finrank ℝ (Fin 3 → ℝ); rw [Module.finrank_fin_fun]; norm_num)
    (by norm_num) hbound hmeas.aestronglyMeasurable

lemma smooth_integration_by_parts {u φ : Vec3 → ℝ}
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

private lemma potential_laplacian_pairing {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, u x * spatialLaplacian ψ x =
        ∫ x, spatialLaplacian u x * ψ x := by
  intro ψ hψ hψc
  have hψd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ i) :=
    contDiff_spatialDeriv_smooth hψ i
  have hψdc (i : Fin 3) : HasCompactSupport (spatialDeriv ψ i) := by
    change HasCompactSupport (fun x => (fderiv ℝ ψ x) (basisVec i))
    exact hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hleft (i : Fin 3) : Integrable
      (fun x => u x * spatialDeriv (spatialDeriv ψ i) i x) volume := by
    exact (hu.continuous.mul
      (contDiff_spatialDeriv_smooth (hψd i) i).continuous).integrable_of_hasCompactSupport
      ((hψdc i).fderiv_apply (𝕜 := ℝ) (basisVec i) |>.mul_left (f := u))
  have hright (i : Fin 3) : Integrable
      (fun x => spatialDeriv (spatialDeriv u i) i x * ψ x) volume := by
    exact (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hu i) i).continuous.mul
      hψ.continuous |>.integrable_of_hasCompactSupport
        (hψc.mul_left (f := spatialDeriv (spatialDeriv u i) i))
  have hfirst (i : Fin 3) := smooth_integration_by_parts hu (hψd i) (hψdc i) i
  have hsecond (i : Fin 3) := smooth_integration_by_parts
    (contDiff_spatialDeriv_smooth hu i) hψ hψc i
  have hsumleft : ∫ x, u x * spatialLaplacian ψ x =
      ∑ i : Fin 3, ∫ x, u x * spatialDeriv (spatialDeriv ψ i) i x := by
    unfold spatialLaplacian
    rw [show (fun x => u x * ∑ i : Fin 3,
        spatialDeriv (spatialDeriv ψ i) i x) =
        (fun x => ∑ i : Fin 3, u x * spatialDeriv (spatialDeriv ψ i) i x) by
          funext x; rw [Finset.mul_sum]]
    symm
    rw [integral_finsetSum]
    intro i hi
    exact hleft i
  have hsumright : ∫ x, spatialLaplacian u x * ψ x =
      ∑ i : Fin 3, ∫ x, spatialDeriv (spatialDeriv u i) i x * ψ x := by
    unfold spatialLaplacian
    rw [show (fun x => (∑ i : Fin 3,
        spatialDeriv (spatialDeriv u i) i x) * ψ x) =
        (fun x => ∑ i : Fin 3, spatialDeriv (spatialDeriv u i) i x * ψ x) by
          funext x; rw [Finset.sum_mul]]
    symm
    rw [integral_finsetSum]
    intro i hi
    exact hright i
  rw [hsumleft, hsumright]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfirst i, hsecond i]
  ring

/- The Newtonian potential is smooth because the compactly supported datum is
   the left convolution factor, while the Newtonian kernel is locally integrable. -/
theorem pressureNewtonianPotential_smooth {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    ContDiff ℝ (⊤ : ℕ∞) (pressureNewtonianPotential F) := by
  have hfun : pressureNewtonianPotential F =
      MeasureTheory.convolution F
        (fun z : Vec3 => -Foundation.Heat.newtonianKernel z)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    rw [pressureNewtonianPotential, MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards [] with y
    simp [ContinuousLinearMap.lsmul_apply, mul_comm]
  rw [hfun]
  exact hFc.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    hF pressure_neg_kernel_locallyIntegrable

/- The first derivative may be computed on the compactly supported datum.
   This is the decay input needed on the large cutoff annuli. -/
theorem pressureNewtonianPotential_spatialDeriv_convolution
    {F : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (i : Fin 3) (x : Vec3) :
    spatialDeriv (pressureNewtonianPotential F) i x =
      ∫ y, spatialDeriv F i y * (-Foundation.Heat.newtonianKernel (x-y)) := by
  have hD := hFc.hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (hF.of_le (by simp))
      pressure_neg_kernel_locallyIntegrable x
  have hDcompact : HasCompactSupport (fderiv ℝ F) := hFc.fderiv (𝕜 := ℝ)
  have hDf : ContDiff ℝ (1 : ℕ∞) (fderiv ℝ F) :=
    hF.fderiv_right (by simp)
  have hconvD := hDcompact.convolutionExists_left
    (L := (ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec3))
    hDf.continuous pressure_neg_kernel_locallyIntegrable x
  have hi := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hD.fderiv
  rw [show pressureNewtonianPotential F =
      MeasureTheory.convolution F
        (fun z : Vec3 => -Foundation.Heat.newtonianKernel z)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume by
    funext z
    rw [pressureNewtonianPotential, MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards [] with y
    simp [ContinuousLinearMap.lsmul_apply, mul_comm]]
  rw [spatialDeriv]
  rw [MeasureTheory.convolution_def] at hi
  rw [ContinuousLinearMap.integral_apply (hconvD)] at hi
  simpa [ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul, spatialDeriv] using hi

private lemma neg_newtonian_convolution_tail_bound
    {G : Vec3 → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) {R : ℝ} (hR : 0 < R)
    (hSupp : tsupport G ⊆ Metric.closedBall (0 : Vec3) R)
    {x : Vec3} (hx : 2 * R ≤ ‖x‖) :
    |∫ y, G y * (-Foundation.Heat.newtonianKernel (x-y))| ≤
      (2 * (4 * Real.pi)⁻¹ / ‖x‖) * ∫ y, |G y| := by
  have hconv := hGc.convolutionExists_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hG.continuous
      pressure_neg_kernel_locallyIntegrable x
  have hprod : Integrable
      (fun y : Vec3 => G y * (-Foundation.Heat.newtonianKernel (x-y))) volume := by
    exact hconv.integrable
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hx
    linarith only [hx, hR]
  have hpoint : ∀ y,
      |G y * (-Foundation.Heat.newtonianKernel (x-y))| ≤
        (2 * (4 * Real.pi)⁻¹ / ‖x‖) * |G y| := by
    intro y
    by_cases hy : y ∈ tsupport G
    · have hy' := hSupp hy
      rw [Metric.mem_closedBall, dist_zero_right] at hy'
      have hxy : x-y ≠ 0 := by
        intro hzero
        have heq : x = y := sub_eq_zero.mp hzero
        rw [heq] at hx
        linarith only [hx, hy', hR]
      have hdist : ‖x‖ / 2 ≤ ‖x-y‖ := by
        have htri : ‖x‖ ≤ ‖x-y‖ + ‖y‖ := by
          calc
            ‖x‖ = ‖(x-y) + y‖ := by congr 1; abel
            _ ≤ ‖x-y‖ + ‖y‖ := norm_add_le _ _
        linarith only [htri, hy', hx]
      have hinv : ‖x-y‖⁻¹ ≤ (‖x‖ / 2)⁻¹ := by
        exact (inv_le_inv₀ (by positivity) (by positivity)).2 hdist
      have hkernel' : |Foundation.Heat.newtonianKernel (x-y)| ≤
          (4 * Real.pi)⁻¹ * (‖x‖ / 2)⁻¹ := by
        have hb := Foundation.Heat.newtonianKernel_size_bound hxy
        exact hb.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
      rw [abs_mul, abs_neg]
      calc
        |G y| * |Foundation.Heat.newtonianKernel (x-y)| ≤
            |G y| * ((4 * Real.pi)⁻¹ * (‖x‖ / 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hkernel' (abs_nonneg _)
        _ = (2 * (4 * Real.pi)⁻¹ / ‖x‖) * |G y| := by
          have hnormx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
          field_simp [hnormx, ne_of_gt Real.pi_pos]
    · have hGzero : G y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hGzero]
  have hright : Integrable
      (fun y => (2 * (4 * Real.pi)⁻¹ / ‖x‖) * |G y|) volume := by
    exact (hG.continuous.norm.integrable_of_hasCompactSupport hGc.norm).const_mul _
  have hpoint' : ∀ y,
      ‖G y * (-Foundation.Heat.newtonianKernel (x-y))‖ ≤
        (2 * (4 * Real.pi)⁻¹ / ‖x‖) * |G y| := by
    intro y
    simpa only [Real.norm_eq_abs] using hpoint y
  have hmono := integral_mono hprod.norm hright hpoint'
  calc
    |∫ y, G y * (-Foundation.Heat.newtonianKernel (x-y))| ≤
        ∫ y, |G y * (-Foundation.Heat.newtonianKernel (x-y))| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (fun y => G y * (-Foundation.Heat.newtonianKernel (x-y))))
    _ ≤ ∫ y, (2 * (4 * Real.pi)⁻¹ / ‖x‖) * |G y| := hmono
    _ = (2 * (4 * Real.pi)⁻¹ / ‖x‖) * ∫ y, |G y| := by
      rw [integral_const_mul]

theorem pressureNewtonianPotential_laplacian_eq {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    ∀ x, spatialLaplacian (pressureNewtonianPotential F) x = F x := by
  let u : Vec3 → ℝ := pressureNewtonianPotential F
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := pressureNewtonianPotential_smooth hF hFc
  have hFi : Integrable F volume := hF.continuous.integrable_of_hasCompactSupport hFc
  have hrep : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → ∫ x, u x * spatialLaplacian ψ x = ∫ x, F x * ψ x := by
    intro ψ hψ hψc
    exact pressureNewtonianPotential_distributional_pairing hFi hFc hψ hψc
  have hpair := potential_laplacian_pairing hu
  have hzero : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → ∫ x, ψ x * (spatialLaplacian u x - F x) = 0 := by
    intro ψ hψ hψc
    have h := hpair ψ hψ hψc
    have hr := hrep ψ hψ hψc
    have hA : Integrable (fun x => spatialLaplacian u x * ψ x) volume := by
      exact (contDiff_spatialLaplacian_smooth hu).continuous.mul hψ.continuous
        |>.integrable_of_hasCompactSupport (hψc.mul_left
          (f := spatialLaplacian u))
    have hB : Integrable (fun x => F x * ψ x) volume :=
      (hF.continuous.mul hψ.continuous).integrable_of_hasCompactSupport
        (hψc.mul_left (f := F))
    calc
      ∫ x, ψ x * (spatialLaplacian u x - F x) =
          (∫ x, spatialLaplacian u x * ψ x) - ∫ x, F x * ψ x := by
        rw [show (fun x => ψ x * (spatialLaplacian u x - F x)) =
            (fun x => spatialLaplacian u x * ψ x - F x * ψ x) by
              funext x; ring]
        rw [integral_sub hA hB]
      _ = 0 := by rw [← h, ← hr, sub_self]
  have hloc : LocallyIntegrable (fun x => spatialLaplacian u x - F x) volume :=
    (contDiff_spatialLaplacian_smooth hu).continuous.sub hF.continuous |>.locallyIntegrable
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro ψ hψ hψc
    simpa [smul_eq_mul, mul_comm] using hzero ψ hψ hψc)
  have hcont : Continuous (fun x => spatialLaplacian u x - F x) :=
    (contDiff_spatialLaplacian_smooth hu).continuous.sub hF.continuous
  have heq := (hcont.ae_eq_iff_eq volume continuous_zero).mp hae
  intro x
  exact sub_eq_zero.mp (congrFun heq x)

private lemma compact_ibp {f g : Vec3 → ℝ} {i : Fin 3}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∫ x, f x * spatialDeriv g i x =
      -∫ x, spatialDeriv f i x * g x := by
  have hfdc : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f i) :=
    contDiff_spatialDeriv_smooth hf i
  have hgdc : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g i) :=
    contDiff_spatialDeriv_smooth hg i
  have hfdi : HasCompactSupport (spatialDeriv f i) := by
    change HasCompactSupport (fun x => (fderiv ℝ f x) (basisVec i))
    exact hfc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hgdi : HasCompactSupport (spatialDeriv g i) := by
    change HasCompactSupport (fun x => (fderiv ℝ g x) (basisVec i))
    exact hgc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hff : Integrable (fun x => spatialDeriv f i x * g x) volume :=
    (hfdc.continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (hfdi.mul_right (f' := g))
  have hgg : Integrable (fun x => f x * spatialDeriv g i x) volume :=
    (hf.continuous.mul hgdc.continuous).integrable_of_hasCompactSupport
      (hgdi.mul_left (f := f))
  have hfg : Integrable (fun x => f x * g x) volume :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (hfc.mul_right (f' := g))
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Vec3)) (v := basisVec i) hff hgg hfg
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => hg.differentiable (by norm_num) x)
  simpa only [spatialDeriv] using h

private lemma mixed_third_swap {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin 3) (x : Vec3) :
    spatialDeriv (mixedSecond u i j) j x =
      spatialDeriv (mixedSecond u j j) i x := by
  have h := mixedSecond_swap (contDiff_spatialDeriv_smooth hu j) i j x
  unfold mixedSecond at ⊢
  exact h.symm

private lemma mixed_hessian_pair {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huc : HasCompactSupport u)
    (i j : Fin 3) :
    ∫ x, (mixedSecond u i j x) ^ (2 : ℕ) =
      ∫ x, mixedSecond u i i x * mixedSecond u j j x := by
  let a : Vec3 → ℝ := mixedSecond u i j
  let b : Vec3 → ℝ := spatialDeriv u i
  let c : Vec3 → ℝ := mixedSecond u j j
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := by
    dsimp [a]
    exact contDiff_mixedSecond_smooth hu i j
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    dsimp [b]
    exact contDiff_spatialDeriv_smooth hu i
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := by
    dsimp [c]
    exact contDiff_mixedSecond_smooth hu j j
  have hac : HasCompactSupport a := by
    dsimp [a, mixedSecond, spatialDeriv]
    exact (huc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply
      (𝕜 := ℝ) (basisVec i)
  have hbc : HasCompactSupport b := by
    dsimp [b, spatialDeriv]
    exact huc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hcc : HasCompactSupport c := by
    dsimp [c, mixedSecond, spatialDeriv]
    exact (huc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply
      (𝕜 := ℝ) (basisVec j)
  have hfirst := compact_ibp ha hac hb hbc (i := j)
  have hsecond := compact_ibp hc hcc hb hbc (i := i)
  have hswap := mixedSecond_swap hu i j
  have hthird : (fun x => spatialDeriv a j x) =
      (fun x => spatialDeriv c i x) := by
    funext x
    exact mixed_third_swap hu i j x
  have hfirst' : ∫ x, a x * a x =
      -∫ x, spatialDeriv a j x * b x := by
    calc
      ∫ x, a x * a x = ∫ x, a x * spatialDeriv b j x := by
        apply integral_congr_ae
        filter_upwards [] with x
        simpa only [a, b, mixedSecond] using
          congrArg (fun z => mixedSecond u i j x * z)
            (mixedSecond_swap hu i j x)
      _ = -∫ x, spatialDeriv a j x * b x := hfirst
  have hsecond' : ∫ x, c x * mixedSecond u i i x =
      -∫ x, spatialDeriv c i x * b x := by
    calc
      ∫ x, c x * mixedSecond u i i x = ∫ x, c x * spatialDeriv b i x := by
        apply integral_congr_ae
        filter_upwards [] with x
        rfl
      _ = -∫ x, spatialDeriv c i x * b x := hsecond
  rw [show (fun x => (mixedSecond u i j x) ^ (2 : ℕ)) =
      (fun x => a x * a x) by funext x; simp [a, pow_two]]
  rw [hfirst']
  calc
    -∫ x, spatialDeriv a j x * b x =
        -∫ x, spatialDeriv c i x * b x := by
          apply congrArg Neg.neg
          apply integral_congr_ae
          filter_upwards [] with x
          exact congrArg (fun z => z * b x) (congrFun hthird x)
    _ =
        ∫ x, c x * mixedSecond u i i x := hsecond'.symm
    _ = ∫ x, mixedSecond u i i x * c x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = ∫ x, mixedSecond u i i x * mixedSecond u j j x := by
      rfl

/-- The squared `L²` Hessian norm equals the squared `L²` Laplacian norm for a
smooth compactly supported scalar function on `Vec3`. -/
theorem hessian_l2_eq_laplacian_l2 {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huc : HasCompactSupport u) :
    ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (mixedSecond u i j x) ^ (2 : ℕ) =
      ∫ x, (spatialLaplacian u x) ^ (2 : ℕ) := by
  have hpairs : ∀ i j : Fin 3,
      ∫ x, (mixedSecond u i j x) ^ (2 : ℕ) =
        ∫ x, mixedSecond u i i x * mixedSecond u j j x :=
    fun i j => mixed_hessian_pair hu huc i j
  calc
    ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (mixedSecond u i j x) ^ (2 : ℕ) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x, mixedSecond u i i x * mixedSecond u j j x := by
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpairs i j))
    _ = ∫ x, (∑ i : Fin 3, mixedSecond u i i x) ^ (2 : ℕ) := by
      have hci (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond u i i) :=
        contDiff_mixedSecond_smooth hu i i
      have hcci (i : Fin 3) : HasCompactSupport (mixedSecond u i i) := by
        exact (huc.fderiv_apply (𝕜 := ℝ) (basisVec i)).fderiv_apply
          (𝕜 := ℝ) (basisVec i)
      have hprod (i j : Fin 3) : Integrable
          (fun x => mixedSecond u i i x * mixedSecond u j j x) volume := by
        exact ((hci i).continuous.mul (hci j).continuous).integrable_of_hasCompactSupport
          ((hcci i).mul_right (f' := mixedSecond u j j))
      have hsumj : ∀ i : Fin 3,
          ∑ j : Fin 3, ∫ x, mixedSecond u i i x * mixedSecond u j j x =
            ∫ x, ∑ j : Fin 3, mixedSecond u i i x * mixedSecond u j j x := by
        intro i
        rw [integral_finsetSum]
        intro j hj
        exact hprod i j
      calc
        ∑ i : Fin 3, ∑ j : Fin 3,
            ∫ x, mixedSecond u i i x * mixedSecond u j j x =
            ∑ i : Fin 3, ∫ x, ∑ j : Fin 3,
              mixedSecond u i i x * mixedSecond u j j x := by
          exact Finset.sum_congr rfl (fun i _ => hsumj i)
        _ = ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
              mixedSecond u i i x * mixedSecond u j j x := by
          rw [integral_finsetSum]
          intro i hi
          exact integrable_finsetSum _ (fun j hj => hprod i j)
        _ = ∫ x, (∑ i : Fin 3, mixedSecond u i i x) ^ (2 : ℕ) := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [pow_two, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])
    _ = ∫ x, (spatialLaplacian u x) ^ (2 : ℕ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      change (∑ i : Fin 3, mixedSecond u i i x) ^ (2 : ℕ) =
        (∑ i : Fin 3, mixedSecond u i i x) ^ (2 : ℕ)
      rfl

/- The component estimate is the form used by the singular-integral
   construction: each Hessian coordinate is controlled by the common
   Laplacian energy. -/
theorem riesz_second_l2_bound {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huc : HasCompactSupport u)
    (i j : Fin 3) :
    ∫ x, (mixedSecond u i j x) ^ (2 : ℕ) ≤
      ∫ x, (spatialLaplacian u x) ^ (2 : ℕ) := by
  have hterm : ∀ k l : Fin 3,
      0 ≤ ∫ x, (mixedSecond u k l x) ^ (2 : ℕ) := by
    intro k l
    exact integral_nonneg (fun x => sq_nonneg (mixedSecond u k l x))
  have hsingle :
      ∫ x, (mixedSecond u i j x) ^ (2 : ℕ) ≤
        ∑ k : Fin 3, ∑ l : Fin 3,
          ∫ x, (mixedSecond u k l x) ^ (2 : ℕ) := by
    have hrow :
        ∫ x, (mixedSecond u i j x) ^ (2 : ℕ) ≤
          ∑ l : Fin 3, ∫ x, (mixedSecond u i l x) ^ (2 : ℕ) := by
      have hrow' := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (f := fun l : Fin 3 => ∫ x, (mixedSecond u i l x) ^ (2 : ℕ))
        (fun l hl => hterm i l) (Finset.mem_univ j)
      simpa using hrow'
    have houter := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun k : Fin 3 => ∑ l : Fin 3,
        ∫ x, (mixedSecond u k l x) ^ (2 : ℕ))
      (fun k hk => Finset.sum_nonneg (fun l hl => hterm k l))
      (Finset.mem_univ i)
    exact hrow.trans (by simpa using houter)
  exact hsingle.trans_eq (hessian_l2_eq_laplacian_l2 hu huc)

end CKN
