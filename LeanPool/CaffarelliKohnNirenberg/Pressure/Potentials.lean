/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Interior
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.NewtonianKernelIntegrability
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Potentials

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

private lemma pressure_kernel_meas : Measurable (newtonianKernel : Vec3 → ℝ) := by
  have hnorm : Measurable (fun z : Vec3 => vec3EuclideanNorm z) := by
    unfold vec3EuclideanNorm
    fun_prop
  unfold newtonianKernel
  exact measurable_const.div (measurable_const.mul hnorm)

private lemma pressure_kernel_deriv_meas (i : Fin 3) : Measurable
    (fun z : Vec3 => CKN.spatialDeriv newtonianKernel i z) := by
  unfold CKN.spatialDeriv
  exact measurable_fderiv_apply_const ℝ newtonianKernel (CKN.basisVec i)

private lemma pressure_kernel_deriv_locallyIntegrable (i : Fin 3) :
    LocallyIntegrable (fun z : Vec3 => CKN.spatialDeriv newtonianKernel i z) volume := by
  have hbound : ∀ᵐ z : Vec3, ‖CKN.spatialDeriv newtonianKernel i z‖ ≤
      (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) := by
    filter_upwards [Measure.ae_ne volume (0 : Vec3)] with z hz
    have hb := newtonianKernel_spatialDeriv_size_bound hz i
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two]
    exact hb
  refine locallyIntegrable_of_norm_le_rpow (E := Vec3) (F := ℝ)
    (by change 1 ≤ Module.finrank ℝ (Fin 3 → ℝ); rw [Module.finrank_fin_fun]; norm_num)
    (by norm_num) hbound (pressure_kernel_deriv_meas i).aestronglyMeasurable

private lemma pressure_neg_kernel_meas : Measurable (fun z : Vec3 => -newtonianKernel z) :=
  pressure_kernel_meas.neg

private lemma pressure_neg_kernel_locallyIntegrable :
    LocallyIntegrable (fun z : Vec3 => -newtonianKernel z) volume :=
  CKN.Foundation.Heat.locallyIntegrable_newtonianKernel.neg

private lemma pressure_integrableOn_shift_of_locallyIntegrable
    {k : Vec3 → ℝ} (hk : LocallyIntegrable k volume)
    {K : Set Vec3} (hK : IsCompact K) (y : Vec3) :
    IntegrableOn (fun x : Vec3 => k (x-y)) K volume := by
  let S : Set Vec3 := (fun x : Vec3 => x + -y) '' K
  have hS : IsCompact S := hK.image (by fun_prop)
  have hkS : IntegrableOn k S volume := hk.integrableOn_isCompact hS
  have hInd := hkS.integrable_indicator hS.measurableSet
  have hcomp := (measurePreserving_add_right (volume : Measure Vec3) (-y)).integrable_comp
    hInd.aestronglyMeasurable |>.mpr hInd
  have heq : (fun x : Vec3 => S.indicator k (x + -y)) =
      (fun x : Vec3 => K.indicator (fun z : Vec3 => k (z-y)) x) := by
    funext x
    by_cases hx : x ∈ K
    · have hxy : x + -y ∈ S := ⟨x, hx, rfl⟩
      simp only [Set.indicator_of_mem hxy, Set.indicator_of_mem hx]
      simp only [sub_eq_add_neg]
    · have hxy : x + -y ∉ S := by
        rintro ⟨z, hz, hzx⟩
        have hzx' : z = x := sub_left_injective (by simpa only [sub_eq_add_neg] using hzx)
        exact hx (by simpa only [hzx'] using hz)
      simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxy]
  have hcomp' : Integrable (fun x : Vec3 => S.indicator k (x + -y)) volume := by
    change Integrable (fun x : Vec3 => S.indicator k (x + -y)) volume at hcomp
    exact hcomp
  rw [heq] at hcomp'
  exact (integrable_indicator_iff hK.measurableSet).mp hcomp'

private lemma pressure_setIntegral_norm_shift_le
    {k : Vec3 → ℝ} (hk : LocallyIntegrable k volume)
    {K L : Set Vec3} (hK : IsCompact K) (hL : IsCompact L)
    (y : Vec3) (hsub : (fun x : Vec3 => x-y) '' K ⊆ L) :
    (∫ x in K, ‖k (x-y)‖) ≤ ∫ z in L, ‖k z‖ := by
  have hkn : LocallyIntegrable (fun z : Vec3 => ‖k z‖) volume := by
    have hkOn : LocallyIntegrableOn k univ := locallyIntegrableOn_univ.mpr hk
    exact locallyIntegrableOn_univ.mp hkOn.norm
  have hshift : IntegrableOn (fun x : Vec3 => ‖k (x-y)‖) K volume :=
    pressure_integrableOn_shift_of_locallyIntegrable hkn hK y
  have hleft := hshift.integrable_indicator hK.measurableSet
  have hright0 := hkn.integrableOn_isCompact hL
  have hright := hright0.integrable_indicator hL.measurableSet
  have hcomp := (measurePreserving_add_right (volume : Measure Vec3) (-y)).integrable_comp
    hright.aestronglyMeasurable |>.mpr hright
  have hcomp' : Integrable (fun x : Vec3 => L.indicator (fun z : Vec3 => ‖k z‖) (x + -y)) volume
    := by
    change Integrable (fun x : Vec3 => L.indicator (fun z : Vec3 => ‖k z‖) (x + -y)) volume at hcomp
    exact hcomp
  have hle : ∀ᵐ x : Vec3, K.indicator (fun z : Vec3 => ‖k (z-y)‖) x ≤
      L.indicator (fun z : Vec3 => ‖k z‖) (x + -y) := by
    filter_upwards [] with x
    by_cases hx : x ∈ K
    · have hxy : x-y ∈ L := hsub ⟨x, hx, rfl⟩
      have hxy' : x + -y ∈ L := by simpa only [sub_eq_add_neg] using hxy
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxy']
      simp only [sub_eq_add_neg]
      exact le_rfl
    · rw [Set.indicator_of_notMem hx]
      by_cases hLxy : x + -y ∈ L
      · rw [Set.indicator_of_mem hLxy]
        exact norm_nonneg _
      · rw [Set.indicator_of_notMem hLxy]
  have hint := integral_mono_ae hleft hcomp' hle
  rw [integral_indicator hK.measurableSet] at hint
  have htrans := (measurePreserving_add_right (volume : Measure Vec3) (-y)).integral_comp
    (Homeomorph.subRight y).measurableEmbedding (L.indicator (fun z : Vec3 => ‖k z‖))
  have htrans' : (∫ x : Vec3, L.indicator (fun z : Vec3 => ‖k z‖) (x + -y)) =
      ∫ z : Vec3, L.indicator (fun z : Vec3 => ‖k z‖) z := by
    simpa only [Function.comp_apply, sub_eq_add_neg] using htrans
  rw [htrans', integral_indicator hL.measurableSet] at hint
  exact hint

private lemma pressure_potential_locallyIntegrable_of_compact_integrable
    {k g : Vec3 → ℝ} (hk : LocallyIntegrable k volume)
    (hkm : Measurable k) (hg : Integrable g volume) (hgc : HasCompactSupport g) :
    LocallyIntegrable (fun x : Vec3 => ∫ y, k (x-y) * g y) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let S : Set Vec3 := tsupport g
  have hS : IsCompact S := hgc.isCompact
  let L : Set Vec3 := (fun z : Vec3 × Vec3 => z.1-z.2) '' (K ×ˢ S)
  have hL : IsCompact L := (hK.prod hS).image (by fun_prop)
  have hLInt : IntegrableOn (fun z : Vec3 => ‖k z‖) L volume := by
    have hkn : LocallyIntegrable (fun z : Vec3 => ‖k z‖) volume := by
      have hkOn : LocallyIntegrableOn k univ := locallyIntegrableOn_univ.mpr hk
      exact locallyIntegrableOn_univ.mp hkOn.norm
    exact hkn.integrableOn_isCompact hL
  let μ : Measure Vec3 := volume.restrict K
  let F : Vec3 × Vec3 → ℝ := fun z => k (z.1-z.2) * g z.2
  have hFmeas : AEStronglyMeasurable F (μ.prod volume) := by
    have hk' : Measurable (fun z : Vec3 × Vec3 => k (z.1-z.2)) :=
      hkm.comp (measurable_fst.sub measurable_snd)
    exact (hk'.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd)
  have hprod : Integrable F (μ.prod volume) := by
    apply (integrable_prod_iff' hFmeas).2
    constructor
    · filter_upwards [] with y
      have hshift := pressure_integrableOn_shift_of_locallyIntegrable hk hK y
      have hmul := hshift.integrable.const_mul (g y)
      simpa only [F, Function.comp_apply, mul_comm] using hmul
    · have hmeas : AEStronglyMeasurable
          (fun y : Vec3 => ∫ x, ‖F (x,y)‖ ∂μ) volume :=
        hFmeas.prod_swap.norm.integral_prod_right'
      have hmajor : Integrable (fun y : Vec3 =>
          (∫ z in L, ‖k z‖) * ‖g y‖) volume := hg.norm.const_mul _
      apply hmajor.mono hmeas
      filter_upwards [] with y
      by_cases hy : y ∈ S
      · have hsub : (fun x : Vec3 => x-y) '' K ⊆ L := by
          rintro z ⟨x, hx, rfl⟩
          exact ⟨⟨x,y⟩, ⟨hx, hy⟩, rfl⟩
        have hbound := pressure_setIntegral_norm_shift_le hk hK hL y hsub
        dsimp [F, μ]
        rw [abs_of_nonneg (integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun _ => abs_nonneg _))]
        rw [abs_of_nonneg (mul_nonneg (integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)) (abs_nonneg _))]
        simp_rw [abs_mul, mul_comm]
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
      · have hgy : g y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [F, hgy]
  have hpot := hprod.integral_prod_left
  change Integrable (fun x : Vec3 => ∫ y, k (x-y) * g y) (volume.restrict K)
  exact hpot

private lemma pressure_kernel_reflection (x y : Vec3) :
    newtonianKernel (y-x) = newtonianKernel (x-y) := by
  unfold newtonianKernel vec3EuclideanNorm
  congr 3
  apply Finset.sum_congr rfl
  intro i hi
  have hcoord : (y - x) i = -((x - y) i) := by
    change y i - x i = -(x i - y i)
    ring
  rw [hcoord]
  ring

lemma pressure_laplacian_hasCompactSupport {ψ : Vec3 → ℝ}
    (hψc : HasCompactSupport ψ) : HasCompactSupport (spatialLaplacian ψ) := by
  have hdiag (i : Fin 3) : HasCompactSupport
      (spatialDeriv (spatialDeriv ψ i) i) :=
    (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)).fderiv_apply
      (𝕜 := ℝ) (basisVec i)
  have h01 : HasCompactSupport (fun y : Vec3 =>
      spatialDeriv (spatialDeriv ψ (0 : Fin 3)) 0 y +
        spatialDeriv (spatialDeriv ψ (1 : Fin 3)) 1 y) := by
    convert (hdiag (0 : Fin 3)).add (hdiag (1 : Fin 3)) using 1
  have hsum : HasCompactSupport (fun y : Vec3 =>
      spatialDeriv (spatialDeriv ψ (0 : Fin 3)) 0 y +
        spatialDeriv (spatialDeriv ψ (1 : Fin 3)) 1 y +
          spatialDeriv (spatialDeriv ψ (2 : Fin 3)) 2 y) := by
    convert h01.add (hdiag (2 : Fin 3)) using 1
  change HasCompactSupport (fun y : Vec3 =>
    ∑ i : Fin 3, spatialDeriv (spatialDeriv ψ i) i y)
  simpa only [Fin.sum_univ_three] using hsum

private lemma pressure_potential_pairing_of_compact
    {k g φ H : Vec3 → ℝ} (hk : LocallyIntegrable k volume)
    (hkm : Measurable k) (hg : Integrable g volume) (hgc : HasCompactSupport g)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hinner : ∀ y, ∫ x, k (x - y) * φ x = H y) :
    ∫ x, (∫ y, k (x-y) * g y) * φ x = ∫ y, g y * H y := by
  let K : Set Vec3 := tsupport φ
  have hK : IsCompact K := hφc.isCompact
  let μ : Measure Vec3 := volume.restrict K
  let F : Vec3 × Vec3 → ℝ := fun z => k (z.1-z.2) * g z.2 * φ z.1
  have hFbase : Integrable (fun z : Vec3 × Vec3 => k (z.1-z.2) * g z.2)
      (μ.prod volume) := by
    have hFmeas : AEStronglyMeasurable
        (fun z : Vec3 × Vec3 => k (z.1-z.2) * g z.2) (μ.prod volume) := by
      have hk' : Measurable (fun z : Vec3 × Vec3 => k (z.1-z.2)) :=
        hkm.comp (measurable_fst.sub measurable_snd)
      exact (hk'.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd)
    let L : Set Vec3 := (fun z : Vec3 × Vec3 => z.1-z.2) '' (K ×ˢ tsupport g)
    have hL : IsCompact L := (hK.prod hgc.isCompact).image (by fun_prop)
    have hLInt : IntegrableOn (fun z : Vec3 => ‖k z‖) L volume := by
      have hkn : LocallyIntegrable (fun z : Vec3 => ‖k z‖) volume := by
        have hkOn : LocallyIntegrableOn k univ := locallyIntegrableOn_univ.mpr hk
        exact locallyIntegrableOn_univ.mp hkOn.norm
      exact hkn.integrableOn_isCompact hL
    apply (integrable_prod_iff' hFmeas).2
    constructor
    · filter_upwards [] with y
      have hshift := pressure_integrableOn_shift_of_locallyIntegrable hk hK y
      have hmul := hshift.integrable.const_mul (g y)
      simpa only [mul_comm] using hmul
    · have hmeas : AEStronglyMeasurable
          (fun y : Vec3 => ∫ x, ‖k (x-y) * g y‖ ∂μ) volume :=
        hFmeas.prod_swap.norm.integral_prod_right'
      have hmajor : Integrable (fun y : Vec3 =>
          (∫ z in L, ‖k z‖) * ‖g y‖) volume := hg.norm.const_mul _
      apply hmajor.mono hmeas
      filter_upwards [] with y
      by_cases hy : y ∈ tsupport g
      · have hsub : (fun x : Vec3 => x-y) '' K ⊆ L := by
          rintro z ⟨x, hx, rfl⟩
          exact ⟨⟨x,y⟩, ⟨hx, hy⟩, rfl⟩
        have hbound := pressure_setIntegral_norm_shift_le hk hK hL y hsub
        dsimp [F, μ]
        rw [abs_of_nonneg (integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun _ => abs_nonneg _))]
        rw [abs_of_nonneg (mul_nonneg (integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)) (abs_nonneg _))]
        simp_rw [abs_mul, mul_comm]
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
      · have hgy : g y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [hgy]
  have hφbound : ∃ C, ∀ x, ‖φ x‖ ≤ C := hφc.exists_bound_of_continuous hφ
  obtain ⟨C, hC⟩ := hφbound
  have hF : Integrable F (μ.prod volume) := by
    exact hFbase.mul_bdd ((hφ.measurable.comp measurable_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun z => by simpa [F] using hC z.1))
  have hswap := MeasureTheory.integral_integral_swap (f := fun x y => F (x,y)) hF
  have hleft : ∫ x, (∫ y, k (x-y) * g y) * φ x =
      ∫ x in K, (∫ y, k (x-y) * g y) * φ x := by
    have hpot := pressure_potential_locallyIntegrable_of_compact_integrable hk hkm hg hgc
    have hprod : Integrable (fun x => (∫ y, k (x-y) * g y) * φ x) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hpot.integrable_smul_right_of_hasCompactSupport hφ hφc
    have heq : (fun x => (∫ y, k (x-y) * g y) * φ x) =
        K.indicator (fun x => (∫ y, k (x-y) * g y) * φ x) := by
      funext x
      by_cases hx : x ∈ K
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, mul_zero]
    calc
      ∫ x, (∫ y, k (x-y) * g y) * φ x =
          ∫ x, K.indicator (fun x => (∫ y, k (x-y) * g y) * φ x) x :=
            congrArg (fun f => ∫ x, f x) heq
      _ = ∫ x in K, (∫ y, k (x-y) * g y) * φ x :=
            integral_indicator hK.measurableSet
  rw [hleft]
  change (∫ x : Vec3, (∫ y, k (x-y) * g y) * φ x ∂μ) = _
  calc
    (∫ x : Vec3, (∫ y, k (x-y) * g y) * φ x ∂μ) =
        ∫ x : Vec3, ∫ y : Vec3, F (x,y) ∂volume ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [F]
      rw [integral_mul_const]
    _ = ∫ y : Vec3, ∫ x : Vec3, F (x,y) ∂μ ∂volume := hswap
    _ = ∫ y : Vec3, g y * H y := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hset : ∫ x in K, k (x-y) * φ x = ∫ x, k (x-y) * φ x := by
        symm
        rw [← integral_indicator hK.measurableSet]
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ K
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx,
            image_eq_zero_of_notMem_tsupport hx, mul_zero]
      rw [show (∫ x : Vec3, F (x,y) ∂μ) =
          (∫ x in K, k (x-y) * φ x) * g y by
            calc
              (∫ x : Vec3, F (x,y) ∂μ) =
                  ∫ x : Vec3, g y * (k (x-y) * φ x) ∂μ := by
                    apply integral_congr_ae
                    filter_upwards [] with x
                    simp only [F]
                    ring
              _ = g y * (∫ x : Vec3, k (x-y) * φ x ∂μ) := by
                    rw [integral_const_mul]
              _ = (∫ x in K, k (x-y) * φ x) * g y := by
                    rw [hset]
                    ring]
      rw [hset, hinner y]
      ring

/-- The Newtonian potential with the paper's sign convention `N = -newtonianKernel`. -/
@[expose]
def pressureNewtonianPotential (g : Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∫ y, (-newtonianKernel (x-y)) * g y

/-- The first derivative potential, written as `-∂ⱼN * g = ∂ⱼ(newtonianKernel) * g`. -/
@[expose]
def pressureNewtonianDerivativePotential (i : Fin 3) (g : Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∫ y, CKN.spatialDeriv newtonianKernel i (x-y) * g y

theorem pressureNewtonianPotential_locallyIntegrable {g : Vec3 → ℝ}
    (hg : Integrable g volume) (hgc : HasCompactSupport g) :
    LocallyIntegrable (pressureNewtonianPotential g) volume := by
  change LocallyIntegrable (fun x => ∫ y, (-newtonianKernel (x-y)) * g y) volume
  exact pressure_potential_locallyIntegrable_of_compact_integrable
    pressure_neg_kernel_locallyIntegrable pressure_neg_kernel_meas hg hgc

theorem pressureNewtonianDerivativePotential_locallyIntegrable {g : Vec3 → ℝ}
    (i : Fin 3) (hg : Integrable g volume) (hgc : HasCompactSupport g) :
    LocallyIntegrable (pressureNewtonianDerivativePotential i g) volume := by
  exact pressure_potential_locallyIntegrable_of_compact_integrable
    (pressure_kernel_deriv_locallyIntegrable i) (pressure_kernel_deriv_meas i) hg hgc

theorem pressureNewtonianPotential_mul_smooth_integrable {g φ : Vec3 → ℝ}
    (hg : Integrable g volume) (hgc : HasCompactSupport g)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => pressureNewtonianPotential g x * φ x) volume := by
  simpa only [smul_eq_mul, mul_comm] using
    (pressureNewtonianPotential_locallyIntegrable hg hgc).integrable_smul_right_of_hasCompactSupport
      hφ.continuous hφc

theorem pressureNewtonianDerivativePotential_mul_smooth_integrable {i : Fin 3}
    {g φ : Vec3 → ℝ} (hg : Integrable g volume) (hgc : HasCompactSupport g)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => pressureNewtonianDerivativePotential i g x * φ x) volume := by
  simpa only [smul_eq_mul, mul_comm] using
    (pressureNewtonianDerivativePotential_locallyIntegrable i hg
      hgc).integrable_smul_right_of_hasCompactSupport
      hφ.continuous hφc

theorem pressureNewtonianPotential_pairing {g φ : Vec3 → ℝ}
    (hg : Integrable g volume) (hgc : HasCompactSupport g)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, pressureNewtonianPotential g x * φ x = ∫ y, g y *
      (∫ x, (-newtonianKernel (x-y)) * φ x) := by
  apply pressure_potential_pairing_of_compact (k := fun z => -newtonianKernel z)
    (H := fun y => ∫ x, (-newtonianKernel (x-y)) * φ x)
    pressure_neg_kernel_locallyIntegrable pressure_neg_kernel_meas hg hgc hφ.continuous hφc
  · intro y
    rfl

theorem pressureNewtonianPotential_adjoint {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (y : Vec3) :
    ∫ x, (-newtonianKernel (x-y)) * CKN.spatialLaplacian ψ x = ψ y := by
  have hrep := newtonian_representation_smooth hψ hψc y
  rw [hrep]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [pressure_kernel_reflection]
  ring

theorem pressureNewtonianPotential_distributional_pairing {g ψ : Vec3 → ℝ}
    (hg : Integrable g volume) (hgc : HasCompactSupport g)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, pressureNewtonianPotential g x * spatialLaplacian ψ x =
      ∫ y, g y * ψ y := by
  have hpair := pressureNewtonianPotential_pairing hg hgc
    (contDiff_spatialLaplacian_smooth hψ) (pressure_laplacian_hasCompactSupport hψc)
  rw [hpair]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [pressureNewtonianPotential_adjoint hψ hψc y]

theorem pressureNewtonianDerivativePotential_pairing {i : Fin 3} {g φ H : Vec3 → ℝ}
    (hg : Integrable g volume) (hgc : HasCompactSupport g)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hinner : ∀ y, ∫ x, CKN.spatialDeriv newtonianKernel i (x - y) * φ x = H y) :
    ∫ x, pressureNewtonianDerivativePotential i g x * φ x = ∫ y,
      g y * H y := by
  exact pressure_potential_pairing_of_compact (k := fun z => CKN.spatialDeriv newtonianKernel i z)
    (H := H)
    (pressure_kernel_deriv_locallyIntegrable i) (pressure_kernel_deriv_meas i)
    hg hgc hφ.continuous hφc hinner

theorem pressureNewtonianDerivativePotential_distributional_pairing {i : Fin 3}
    {g ψ : Vec3 → ℝ} (hg : Integrable g volume) (hgc : HasCompactSupport g)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hinner : ∀ y, ∫ x, CKN.spatialDeriv newtonianKernel i (x - y) *
      CKN.spatialLaplacian ψ x = CKN.spatialDeriv ψ i y) :
    ∫ x, pressureNewtonianDerivativePotential i g x * CKN.spatialLaplacian ψ x =
      ∫ y, g y * CKN.spatialDeriv ψ i y := by
  exact pressureNewtonianDerivativePotential_pairing hg hgc
    (contDiff_spatialLaplacian_smooth hψ)
    (pressure_laplacian_hasCompactSupport hψc) hinner

end CKN
