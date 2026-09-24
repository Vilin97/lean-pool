/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.BackwardPotentialIdentity
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Integrability
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Backward Potential Kernel Bridge

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology Convolution

open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

private lemma hcompact_integrable (f g : Vec3 → ℝ) (hf : Continuous f)
    (hg : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun y : Vec3 => f y * g y) volume := by
  exact hf.mul hg |>.integrable_of_hasCompactSupport hgs.mul_left

lemma heatConv_spatial_kernel_transfer
    {u : Vec3 → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (huSupport : HasCompactSupport u) {t : ℝ} (ht : 0 < t)
    (i : Fin 3) (x : Vec3) :
    heatConv t (fun y => (fderiv ℝ u y) (CKN.basisVec i)) x =
      ∫ y : Vec3, heatKernelSpaceDerivative y t i * u (x - y) := by
  have hk : Continuous (fun y : Vec3 => heatKernel y t) := by
    rw [show (fun y : Vec3 => heatKernel y t) = fun y : Vec3 =>
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ j, y j ^ 2) / (4 * t)) by
      funext y
      exact heatKernel_eq_formula_sum ht]
    fun_prop (disch := positivity)
  have hkd : Continuous
      (fun y : Vec3 => heatKernelSpaceDerivative y t i) := by
    rw [show (fun y : Vec3 => heatKernelSpaceDerivative y t i) = fun y : Vec3 =>
        -(y i) / (2 * t) *
          ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, y j ^ 2) / (4 * t))) by
      funext y
      rw [heatKernelSpaceDerivative, ite_eq_left ht,
        heatKernel_eq_formula_sum ht]]
    fun_prop (disch := positivity)
  let g : Vec3 → ℝ := fun y => u (x - y)
  have hgc : Continuous g := by
    dsimp [g]
    exact hu.continuous.comp (by fun_prop)
  have hgs : HasCompactSupport g := by
    dsimp [g]
    exact huSupport.comp_homeomorph (Homeomorph.subLeft x)
  have hgdiff (y : Vec3) : DifferentiableAt ℝ g y := by
    dsimp [g]
    have houter : HasFDerivAt u (fderiv ℝ u (x - y)) (x - y) :=
      ((hu.differentiable (by simp)) (x - y)).hasFDerivAt
    have hinner : HasFDerivAt (fun z : Vec3 => x - z)
        (-ContinuousLinearMap.id ℝ Vec3) y := by
      convert (hasFDerivAt_const x y).sub (hasFDerivAt_id y) using 1
      · funext z
        rfl
      · ext z
        simp
    exact (houter.comp y hinner).differentiableAt
  have hgd : Continuous (fun y : Vec3 =>
      (fderiv ℝ g y) (CKN.basisVec i)) := by
    rw [show (fun y : Vec3 => (fderiv ℝ g y) (CKN.basisVec i)) =
        fun y => -CKN.spatialDeriv u i (x - y) by
      funext y
      exact shift_fderiv_apply_basisVec hu x y i]
    exact (CKN.contDiff_spatialDeriv_smooth hu i).continuous.comp
      (by fun_prop) |>.neg
  have hgds : HasCompactSupport (fun y : Vec3 =>
      (fderiv ℝ g y) (CKN.basisVec i)) := by
    rw [show (fun y : Vec3 => (fderiv ℝ g y) (CKN.basisVec i)) =
        fun y => -CKN.spatialDeriv u i (x - y) by
      funext y
      exact shift_fderiv_apply_basisVec hu x y i]
    exact (huSupport.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)).comp_homeomorph
      (Homeomorph.subLeft x) |>.neg
  have hkernel_diff (y : Vec3) : DifferentiableAt ℝ
      (fun z : Vec3 => heatKernel z t) y := by
    rw [show (fun z : Vec3 => heatKernel z t) = fun z : Vec3 =>
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ j, z j ^ 2) / (4 * t)) by
      funext z
      exact heatKernel_eq_formula_sum ht]
    fun_prop (disch := positivity)
  have hfirst := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun y : Vec3 => heatKernel y t) (g := g)
    (v := CKN.basisVec i)
    (hcompact_integrable
      (fun y : Vec3 => (fderiv ℝ (fun z : Vec3 => heatKernel z t) y)
        (CKN.basisVec i)) g
      (by simpa only [heatKernel_fderiv_apply_basisVec ht i] using hkd) hgc hgs)
    (hcompact_integrable (fun y : Vec3 => heatKernel y t)
      (fun y : Vec3 => (fderiv ℝ g y) (CKN.basisVec i)) hk hgd hgds)
    (hcompact_integrable (fun y : Vec3 => heatKernel y t) g hk hgc hgs)
    (fun y _ => hkernel_diff y) (fun y _ => hgdiff y)
  rw [heatConv_eq_integral]
  have hright : (fun y : Vec3 =>
      (fderiv ℝ (fun z : Vec3 => heatKernel z t) y) (CKN.basisVec i) * g y) =
      (fun y : Vec3 => heatKernelSpaceDerivative y t i * u (x - y)) := by
    funext y
    rw [heatKernel_fderiv_apply_basisVec ht i]
  calc
    (∫ y : Vec3, heatKernel y t *
        (fderiv ℝ u (x - y)) (CKN.basisVec i)) =
        -∫ y : Vec3, heatKernel y t * (fderiv ℝ g y)
          (CKN.basisVec i) := by
      rw [show (fun y : Vec3 => heatKernel y t *
          (fderiv ℝ u (x - y)) (CKN.basisVec i)) =
          fun y => -(heatKernel y t * (fderiv ℝ g y)
            (CKN.basisVec i)) by
        funext y
        rw [shift_fderiv_apply_basisVec hu x y i]
        change heatKernel y t * CKN.spatialDeriv u i (x - y) =
          -(heatKernel y t * -CKN.spatialDeriv u i (x - y))
        ring_nf]
      rw [integral_neg]
    _ = ∫ y : Vec3, (fderiv ℝ (fun z : Vec3 => heatKernel z t) y)
          (CKN.basisVec i) * g y := by
      linarith only [hfirst]
    _ = ∫ y : Vec3, heatKernelSpaceDerivative y t i * u (x - y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [congrFun hright y]

private lemma heatKernel_space_derivative_measurable (i : Fin 3) :
    Measurable (fun p : ParabolicPoint =>
      heatKernelSpaceDerivative p.1 p.2 i) := by
  unfold heatKernelSpaceDerivative
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · have hheat : Measurable (fun p : ParabolicPoint =>
        heatKernel p.1 p.2) := by
      unfold heatKernel
      apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
      · fun_prop
      · exact measurable_const
    have hcoord : Measurable (fun p : ParabolicPoint => p.1 i) :=
      measurable_pi_apply i |>.comp measurable_fst
    exact (hcoord.neg.div (measurable_const.mul measurable_snd)).mul hheat
  · exact measurable_const

private lemma shifted_gradient_integrable
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (i : Fin 3) (x : Vec3) (t : ℝ) :
    Integrable (fun q : Vec3 × ℝ =>
      heatKernelSpaceDerivative q.1 q.2 i * ζ (x - q.1, t + q.2)) volume := by
  let Kt : Set ℝ := (fun z : Vec3 × ℝ => z.2) '' tsupport ζ
  rcases hζc.isCompact.image continuous_snd |>.bddAbove with ⟨C, hC⟩
  let T : ℝ := max 1 (C - t) + 1
  have hT : 0 < T := by
    dsimp [T]
    positivity
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioc 0 T
  let F : Vec3 × ℝ → ℝ := fun q =>
    heatKernelSpaceDerivative q.1 q.2 i * ζ (x - q.1, t + q.2)
  let G : Vec3 × ℝ → ℝ := fun q =>
    heatKernelGradientNorm q.1 q.2 * |ζ (x - q.1, t + q.2)|
  have hζbound : BddAbove (Set.range (fun z : Vec3 × ℝ => ‖ζ z‖)) :=
    hζ.continuous.norm.bddAbove_range_of_hasCompactSupport hζc.norm
  rcases hζbound with ⟨B, hB⟩
  have hG_S : IntegrableOn G S volume := by
    unfold IntegrableOn
    have hmap : Continuous (fun q : Vec3 × ℝ =>
        (x - q.1, t + q.2)) := by
      exact (continuous_const.sub continuous_fst).prodMk
        (continuous_const.add continuous_snd)
    have hcont : Continuous (fun q : Vec3 × ℝ =>
        |ζ (x - q.1, t + q.2)|) :=
      (hζ.continuous.comp hmap).abs
    have hmeas : AEStronglyMeasurable
        (fun q : Vec3 × ℝ => |ζ (x - q.1, t + q.2)|)
        (volume : Measure (Vec3 × ℝ)) := hcont.aestronglyMeasurable
    apply (heatKernelGradientNorm_integrableOn_time hT).mul_bdd
      (show AEStronglyMeasurable
          (fun q : Vec3 × ℝ => |ζ (x - q.1, t + q.2)|)
          ((volume : Measure (Vec3 × ℝ)).restrict S) from
        hmeas.restrict)
    · filter_upwards [ae_restrict_mem
        (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc)] with q hq
      simpa only [Real.norm_eq_abs, abs_abs] using
        hB ⟨(x - q.1, t + q.2), rfl⟩
  have hG : Integrable G volume := by
    apply hG_S.integrable_of_forall_notMem_eq_zero
    intro q hq
    have hqtime : q.2 ∉ Ioc (0 : ℝ) T := by
      intro hqt
      exact hq ⟨Set.mem_univ _, hqt⟩
    by_cases hq0 : q.2 ≤ 0
    · change heatKernelGradientNorm q.1 q.2 *
        |ζ (x - q.1, t + q.2)| = 0
      rw [heatKernelGradientNorm_eq_zero_of_nonpos hq0]
      simp
    · have hqpos : 0 < q.2 := lt_of_not_ge hq0
      have hqT : T < q.2 := lt_of_not_ge (fun hqle => hqtime ⟨hqpos, hqle⟩)
      have hz : (x - q.1, t + q.2) ∉ tsupport ζ := by
        intro hz
        have htime := hC ⟨(x - q.1, t + q.2), hz, rfl⟩
        change t + q.2 ≤ C at htime
        dsimp [T] at hqT
        linarith only [htime, hqT, le_max_right (1 : ℝ) (C - t)]
      change heatKernelGradientNorm q.1 q.2 *
        |ζ (x - q.1, t + q.2)| = 0
      rw [image_eq_zero_of_notMem_tsupport hz]
      simp
  have hFmeas : AEStronglyMeasurable F (volume : Measure (Vec3 × ℝ)) := by
    have hkmeas : Measurable (fun q : Vec3 × ℝ =>
        heatKernelSpaceDerivative q.1 q.2 i) :=
      heatKernel_space_derivative_measurable i
    have hzmeas : Measurable (fun q : Vec3 × ℝ =>
        ζ (x - q.1, t + q.2)) :=
      hζ.continuous.comp (by fun_prop) |>.measurable
    exact (hkmeas.mul hzmeas).aestronglyMeasurable
  apply hG.mono' hFmeas
  filter_upwards [] with q
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => abs_nonneg
      (heatKernelSpaceDerivative q.1 q.2 j)) (Finset.mem_univ i))
    (abs_nonneg _)

private lemma heatKernelSpaceDerivative_neg (y : Vec3) (s : ℝ) (i : Fin 3) :
    heatKernelSpaceDerivative (-y) s i =
      -heatKernelSpaceDerivative y s i := by
  by_cases hs : 0 < s
  · rw [heatKernelSpaceDerivative, ite_eq_left hs,
      heatKernelSpaceDerivative, ite_eq_left hs]
    rw [heatKernel_eq_formula_sum hs, heatKernel_eq_formula_sum hs]
    simp only [Pi.neg_apply, neg_sq]
    ring_nf
  · rw [heatKernelSpaceDerivative, ite_eq_right (not_lt.mpr (le_of_not_gt hs)),
      heatKernelSpaceDerivative, ite_eq_right (not_lt.mpr (le_of_not_gt hs))]
    simp

private lemma backwardPotential_derivative_hconv_1 :
    ∀ {ζ : Vec3 × ℝ → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ζ →
        HasCompactSupport ζ →
          ∀ (i : Fin (3 : ℕ)) (x : Vec3) (t : ℝ),
            let η : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
              spatialPartial
                (have this : ParabolicPoint → ℝ := ζ;
                this)
                i z;
            ∀ (s : ℝ),
              (0 : ℝ) < s →
                heatConv s (fun (y : Vec3) => η (y, t + s)) x =
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                    heatKernelSpaceDerivative y s i * ζ (x - y, t + s)
    := by
  intro ζ hζ hζc i x t η s hs
  let us : Vec3 → ℝ := fun y => ζ (y, t + s)
  have hus : ContDiff ℝ (⊤ : ℕ∞) us := by
    exact test_slice_contDiff hζ (t + s)
  have husc : HasCompactSupport us := by
    exact test_slice_hasCompactSupport hζc (t + s)
  have heq : (fun y : Vec3 => η (y, t + s)) =
      (fun y => (fderiv ℝ us y) (CKN.basisVec i)) := by
    funext y
    change CKN.spatialPartial (show ParabolicPoint → ℝ from ζ) i
        (y, t + s) = (fderiv ℝ us y) (CKN.basisVec i)
    rw [spatialPartial_eq_fderiv_apply hζ i y (t + s)]
    have hinner : HasFDerivAt (fun z : Vec3 => (z, t + s))
        (ContinuousLinearMap.inl ℝ Vec3 ℝ) y := by
      have hinl : ContinuousLinearMap.inl ℝ Vec3 ℝ =
          (ContinuousLinearMap.id ℝ Vec3).prod (0 : Vec3 →L[ℝ] ℝ) := by
        ext z <;> rfl
      convert (hasFDerivAt_id y).prodMk
        (hasFDerivAt_const (x := y) (c := t + s)) using 1
      · ext z <;> simp
    have houter : HasFDerivAt ζ (fderiv ℝ ζ (y, t + s))
        (y, t + s) :=
      (hζ.differentiable (by simp) (y, t + s)).hasFDerivAt
    have hcomp := houter.comp y hinner
    have hcf := hcomp.fderiv
    have hcf' : (fderiv ℝ us y) (CKN.basisVec i) =
        (fderiv ℝ ζ (y, t + s)) (CKN.basisVec i, 0) := by
      change (fderiv ℝ (ζ ∘ fun z : Vec3 => (z, t + s)) y)
          (CKN.basisVec i) = _
      rw [hcf]
      rfl
    exact hcf'.symm
  rw [heq, heatConv_spatial_kernel_transfer hus husc hs i x]

private lemma backwardPotential_derivative_hfuture'_2 :
    ∀ {ζ : Vec3 × ℝ → ℝ} (i : Fin (3 : ℕ)) (x : Vec3) (t : ℝ),
      let F : Vec3 × ℝ → ℝ := fun (q : Vec3 × ℝ) =>
        heatKernelSpaceDerivative q.1 q.2 i * ζ (x - q.1, t + q.2);
      Measure.prod volume (Measure.restrict volume (Ioi (0 : ℝ))) =
          Measure.restrict volume (SProd.sprod (α := Set Vec3) univ (Ioi (0 : ℝ))) →
        Eq (α := ℝ)
            (@integral _ _ _ _ Prod.instMeasurableSpace
              (Measure.prod volume (Measure.restrict volume (Ioi (0 : ℝ)))) fun (q : Vec3 × ℝ) =>
              F q)
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
              (Measure.restrict volume (Ioi (0 : ℝ))) fun (s : ℝ) =>
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) => F (y, s)) →
          Eq (α := ℝ)
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
              (Measure.restrict volume (Ioi (0 : ℝ))) fun (s : ℝ) =>
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) => F (y, s))
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (q : Vec3 × ℝ) => F q)
    := by
  intro ζ i x t F hmeasure hswap
  rw [← hswap]
  calc
    (∫ q : Vec3 × ℝ, F q ∂
        ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))))) =
        ∫ q : Vec3 × ℝ, F q ∂
          ((volume : Measure (Vec3 × ℝ)).restrict
            ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ))) := by
      rw [hmeasure]
    _ = ∫ q : Vec3 × ℝ, F q := by
      have hset : MeasurableSet ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) :=
        MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
      have hzero : ∀ᵐ q : Vec3 × ℝ ∂(volume : Measure (Vec3 × ℝ)),
          F q = ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)).indicator F q := by
        filter_upwards [] with q
        by_cases hq : 0 < q.2
        · have hmem : q ∈ (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) :=
            ⟨Set.mem_univ _, hq⟩
          rw [Set.indicator_of_mem hmem]
        · have hFzero : F q = 0 := by
            dsimp [F]
            rw [heatKernelSpaceDerivative]
            simp [not_lt.mpr (le_of_not_gt hq)]
          simp [hFzero, hq]
      rw [← integral_indicator hset]
      apply integral_congr_ae
      filter_upwards [hzero] with q hq
      exact hq.symm

private lemma backwardPotential_derivative_hspatial_3 :
    ∀ {ζ : Vec3 × ℝ → ℝ} (i : Fin (3 : ℕ)) (x : Vec3) (t : ℝ),
      let F : Vec3 × ℝ → ℝ := fun (q : Vec3 × ℝ) =>
        heatKernelSpaceDerivative q.1 q.2 i * ζ (x - q.1, t + q.2);
      let e : Vec3 × ℝ ≃ᵐ Vec3 × ℝ :=
        MeasurableEquiv.prodCongr (MeasurableEquiv.neg Vec3) (MeasurableEquiv.refl ℝ);
      MeasurePreserving (α := Vec3 × ℝ) (β := Vec3 × ℝ) (⇑e : Vec3 × ℝ → Vec3 × ℝ) volume volume →
        let _ : Vec3 × ℝ → ℝ := fun (q : Vec3 × ℝ) =>
          heatKernelSpaceDerivative q.1 q.2 i * ζ (x + q.1, t + q.2);
        let v : Vec3 × ℝ := (x, t);
        let _ : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
          heatKernelSpaceDerivative (z.1 - v.1) (z.2 - v.2) i * ζ z;
        backwardHeatPotentialSpatial i
            (have this : ParabolicPoint → ℝ := ζ;
            this)
            (x, t) =
          @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (q : Vec3 × ℝ) => F q
    := by
  intro ζ i x t F e he H v G
  unfold backwardHeatPotentialSpatial backwardHeatSpatialKernel
  change -∫ z : Vec3 × ℝ,
    heatKernelSpaceDerivative (z.1 - x) (z.2 - t) i * ζ z = _
  change -∫ z : Vec3 × ℝ,
      heatKernelSpaceDerivative (z.1 - x) (z.2 - t) i * ζ z
      ∂backwardProductVolume =
    ∫ q : Vec3 × ℝ, F q ∂backwardProductVolume
  let _ : backwardProductVolume.IsAddLeftInvariant := by
    dsimp [backwardProductVolume]
    infer_instance
  have hadd0 := measurePreserving_add_left
    backwardProductVolume v
  let hadd : MeasurePreserving (MeasurableEquiv.addLeft v :
      Vec3 × ℝ → Vec3 × ℝ) backwardProductVolume backwardProductVolume := by
    convert hadd0 using 1
    funext q
    rfl
  have haddint := hadd.integral_comp' G
  have hGtoH : (fun q : Vec3 × ℝ => G (v + q)) = H := by
    funext q
    dsimp [G, H, v]
    congr 2 <;> simp [sub_eq_add_neg]
  calc
    -∫ z : Vec3 × ℝ,
        heatKernelSpaceDerivative (z.1 - x) (z.2 - t) i * ζ z
        ∂backwardProductVolume =
        -∫ z : Vec3 × ℝ, G z ∂backwardProductVolume := by
          congr 1
    _ = -∫ q : Vec3 × ℝ, H q ∂backwardProductVolume := by
      rw [← haddint]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with q
      exact congrFun hGtoH q
    _ = ∫ q : Vec3 × ℝ, F q := by
      have heint := he.integral_comp' H
      have heint' :
          (∫ q : Vec3 × ℝ, H (e q) ∂backwardProductVolume) =
            ∫ q : Vec3 × ℝ, H q ∂backwardProductVolume := by
        change (∫ q : Vec3 × ℝ, H (e q) ∂backwardProductVolume) =
          ∫ q : Vec3 × ℝ, H q ∂backwardProductVolume at heint
        exact heint
      calc
        -∫ q : Vec3 × ℝ, H q ∂backwardProductVolume =
            -∫ q : Vec3 × ℝ, H (e q) ∂backwardProductVolume := by rw [heint']
        _ = -∫ q : Vec3 × ℝ, -F q := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with q
          change heatKernelSpaceDerivative (-q.1) q.2 i *
              ζ (x + -q.1, t + q.2) =
            -(heatKernelSpaceDerivative q.1 q.2 i *
              ζ (x - q.1, t + q.2))
          rw [heatKernelSpaceDerivative_neg]
          ring_nf
        _ = ∫ q : Vec3 × ℝ, F q := by rw [integral_neg]; simp

theorem backwardTestPotential_spatialPartial_eq_backwardHeatPotentialSpatial
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (i : Fin 3) (x : Vec3) (t : ℝ) :
    CKN.spatialPartial (show ParabolicPoint → ℝ from
      fun z => backwardTestPotential ζ z) i (x, t) =
      backwardHeatPotentialSpatial i
        (show ParabolicPoint → ℝ from ζ) (x, t) := by
  let η : Vec3 × ℝ → ℝ := fun z => CKN.spatialPartial
    (show ParabolicPoint → ℝ from ζ) i z
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := by
    exact spatialPartial_contDiff hζ i
  have hηc : HasCompactSupport η := by
    have hfull := hζc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i, 0)
    have heq : (fun z : Vec3 × ℝ => (fderiv ℝ ζ z)
        (CKN.basisVec i, 0)) = η := by
      funext z
      exact (spatialPartial_eq_fderiv_apply hζ i z.1 z.2).symm
    rw [← heq]
    exact hfull
  let F : Vec3 × ℝ → ℝ := fun q =>
    heatKernelSpaceDerivative q.1 q.2 i * ζ (x - q.1, t + q.2)
  have hF : Integrable F (volume : Measure (Vec3 × ℝ)) := by
    exact shifted_gradient_integrable hζ hζc i x t
  have hFmeas : AEStronglyMeasurable F (volume : Measure (Vec3 × ℝ)) := by
    have hkmeas : Measurable (fun q : Vec3 × ℝ =>
        heatKernelSpaceDerivative q.1 q.2 i) :=
      heatKernel_space_derivative_measurable i
    have hmap : Continuous (fun q : Vec3 × ℝ =>
        (x - q.1, t + q.2)) := by
      exact (continuous_const.sub continuous_fst).prodMk
        (continuous_const.add continuous_snd)
    have hzmeas : Measurable (fun q : Vec3 × ℝ =>
        ζ (x - q.1, t + q.2)) :=
      hζ.continuous.comp hmap |>.measurable
    exact (hkmeas.mul hzmeas).aestronglyMeasurable
  have hconv (s : ℝ) (hs : 0 < s) := @backwardPotential_derivative_hconv_1 ζ hζ hζc i x t s hs
  have hfuture :
      CKN.spatialPartial (show ParabolicPoint → ℝ from
          fun z => backwardTestPotential ζ z) i (x, t) =
      ∫ s : ℝ in Ioi 0, ∫ y : Vec3, F (y, s) := by
    rw [backwardTestPotential_spatialPartial hζ hζc i x t,
      backwardTestPotential_future_integral hη hηc x t]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hconv s hs
  have hmeasure :
      (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))) =
        (volume : Measure (Vec3 × ℝ)).restrict
          ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) := by
    change (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))) =
      ((volume : Measure Vec3).prod volume).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ))
    rw [← Measure.prod_restrict]
    simp
  have hprod : Integrable F
      ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [hmeasure]
    exact hF.restrict
  have hswap :
      ∫ q : Vec3 × ℝ, F q ∂
          ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) =
        ∫ s : ℝ in Ioi 0, ∫ y : Vec3, F (y, s) := by
    have hs := integral_prod_swap
      (μ := (volume : Measure Vec3))
      (ν := volume.restrict (Ioi (0 : ℝ))) F
    have hp := integral_prod
      (fun q : ℝ × Vec3 => F q.swap) hprod.swap
    calc
      ∫ q : Vec3 × ℝ, F q ∂
          ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) =
          ∫ q : ℝ × Vec3, F q.swap ∂
            ((volume.restrict (Ioi (0 : ℝ))).prod volume) := hs.symm
      _ = ∫ s : ℝ in Ioi 0, ∫ y : Vec3, F (y, s) := by
        simpa only [Prod.swap_prod_mk] using hp
  have hfuture' := @backwardPotential_derivative_hfuture'_2 ζ i x t hmeasure hswap
  let e : (Vec3 × ℝ) ≃ᵐ (Vec3 × ℝ) :=
    (MeasurableEquiv.neg Vec3).prodCongr (MeasurableEquiv.refl ℝ)
  have he : MeasurePreserving e
      (volume : Measure (Vec3 × ℝ)) volume := by
    dsimp [e]
    exact (Measure.measurePreserving_neg (volume : Measure Vec3)).prod
      (MeasurePreserving.id volume)
  let H : Vec3 × ℝ → ℝ := fun q =>
    heatKernelSpaceDerivative q.1 q.2 i * ζ (x + q.1, t + q.2)
  have hH : Integrable H (volume : Measure (Vec3 × ℝ)) := by
    have hcomp : Integrable (H ∘ e) (volume : Measure (Vec3 × ℝ)) := by
      apply (show Integrable (fun q => -F q) volume from hF.neg).congr
      filter_upwards [] with q
      dsimp [Function.comp, e]
      change -(heatKernelSpaceDerivative q.1 q.2 i *
          ζ (x - q.1, t + q.2)) =
        heatKernelSpaceDerivative (-q.1) q.2 i *
          ζ (x + -q.1, t + q.2)
      rw [heatKernelSpaceDerivative_neg]
      ring_nf
    have hhmeas : AEStronglyMeasurable H (volume : Measure (Vec3 × ℝ)) := by
      have hkmeas : Measurable (fun q : Vec3 × ℝ =>
          heatKernelSpaceDerivative q.1 q.2 i) :=
        heatKernel_space_derivative_measurable i
      have hmap : Continuous (fun q : Vec3 × ℝ =>
          (x + q.1, t + q.2)) := by
        exact (continuous_const.add continuous_fst).prodMk
          (continuous_const.add continuous_snd)
      have hzmeas : Measurable (fun q : Vec3 × ℝ =>
          ζ (x + q.1, t + q.2)) :=
        hζ.continuous.comp hmap |>.measurable
      exact (hkmeas.mul hzmeas).aestronglyMeasurable
    exact (he.integrable_comp hhmeas).mp hcomp
  let v : Vec3 × ℝ := (x, t)
  let G : Vec3 × ℝ → ℝ := fun z =>
    heatKernelSpaceDerivative (z.1 - v.1) (z.2 - v.2) i * ζ z
  have hG : Integrable G (volume : Measure (Vec3 × ℝ)) := by
    change Integrable G backwardProductVolume
    let _ : backwardProductVolume.IsAddLeftInvariant := by
      dsimp [backwardProductVolume]
      infer_instance
    let hadd0 := measurePreserving_add_left
      backwardProductVolume v
    let hadd : MeasurePreserving (MeasurableEquiv.addLeft v :
        Vec3 × ℝ → Vec3 × ℝ) backwardProductVolume backwardProductVolume := by
      convert hadd0 using 1
      funext q
      rfl
    have hGmeas : AEStronglyMeasurable G backwardProductVolume := by
      have hkmeas : Measurable (fun z : Vec3 × ℝ =>
          heatKernelSpaceDerivative (z.1 - v.1) (z.2 - v.2) i) := by
        exact (heatKernel_space_derivative_measurable i).comp
          ((measurable_fst.sub measurable_const).prodMk
            (measurable_snd.sub measurable_const))
      exact (hkmeas.mul hζ.continuous.measurable).aestronglyMeasurable
    apply (hadd.integrable_comp hGmeas).mp
    have hH' : Integrable H backwardProductVolume := by
      exact hH
    convert hH' using 1
    funext q
    dsimp [H, G, v]
    congr 2 <;> simp
  have hspatial := @backwardPotential_derivative_hspatial_3 ζ i x t he
  calc
    CKN.spatialPartial (show ParabolicPoint → ℝ from
        fun z => backwardTestPotential ζ z) i (x, t) =
        ∫ s : ℝ in Ioi 0, ∫ y : Vec3, F (y, s) := hfuture
    _ = ∫ q : Vec3 × ℝ, F q := hfuture'
    _ = backwardHeatPotentialSpatial i
        (show ParabolicPoint → ℝ from ζ) (x, t) := hspatial.symm

end CKN.Foundation.Heat
