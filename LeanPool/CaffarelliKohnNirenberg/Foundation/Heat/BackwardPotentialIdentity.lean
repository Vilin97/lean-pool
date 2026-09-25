/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.BackwardPotentialSmooth

/-!
# Backward Potential Identity

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology Convolution

open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

private lemma slice_laplacian_eq_second
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (y : Vec3) (t : ℝ) :
    CKN.spatialLaplacian (fun x : Vec3 => ζ (x, t)) y =
      ∑ i : Fin 3, CKN.spatialSecondPartial
        (show ParabolicPoint → ℝ from ζ) i i (y, t) := by
  let u : Vec3 → ℝ := fun x => ζ (x, t)
  have hinner (x : Vec3) : HasFDerivAt (fun x : Vec3 => (x, t))
      (ContinuousLinearMap.inl ℝ Vec3 ℝ) x := by
    have hinl : ContinuousLinearMap.inl ℝ Vec3 ℝ =
        (ContinuousLinearMap.id ℝ Vec3).prod (0 : Vec3 →L[ℝ] ℝ) := by
      ext z <;> rfl
    convert (hasFDerivAt_id x).prodMk
      (hasFDerivAt_const (x := x) (c := t)) using 1
    ext z <;> simp
  have hfirst (i : Fin 3) :
      CKN.spatialDeriv u i =
        (fun x : Vec3 => CKN.spatialPartial
          (show ParabolicPoint → ℝ from ζ) i (x, t)) := by
    funext x
    have houter : HasFDerivAt ζ (fderiv ℝ ζ (x, t)) (x, t) :=
      (hζ.differentiable (by simp) (x, t)).hasFDerivAt
    have hc := houter.comp x (hinner x)
    have hcoord := spatialPartial_eq_fderiv_apply hζ i x t
    have hfd := hc.fderiv
    change (fderiv ℝ u x) (CKN.basisVec i) = _
    change (fderiv ℝ (ζ ∘ (fun z : Vec3 => (z, t))) x)
        (CKN.basisVec i) = _
    rw [hfd]
    change (fderiv ℝ ζ (x, t)) (CKN.basisVec i, 0) = _
    exact hcoord.symm
  unfold CKN.spatialLaplacian
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfirst i]
  rfl

private lemma backward_green_truncated_hW_1 :
    ∀ {ζ : Vec3 × ℝ → ℝ} (x : Vec3) (t ε : ℝ),
      (0 : ℝ) < ε →
        let K : Set (Vec3 × ℝ) := (fun (z : Vec3 × ℝ) => (x - z.1, z.2 - t)) '' tsupport ζ;
        ∀ (C : ℝ),
          let B : ℝ := C - t;
          let B' : ℝ := max B ε + (1 : ℝ);
          let S : Set (Vec3 × ℝ) := K ∩ SProd.sprod (α := Set Vec3) univ (Icc ε B');
          ContinuousOn (Y := ℝ) (fun (p : Vec3 × ℝ) => heatKernel p.1 p.2) S
    := by
  intro ζ x t ε hε K C B B' S p hp
  have hp0 : 0 < p.2 := lt_of_lt_of_le hε hp.2.2.1
  let F : Vec3 × ℝ → ℝ := fun q => (4 * Real.pi * q.2) ^ (-(3 : ℝ) / 2) *
    Real.exp (-(∑ i, q.1 i ^ 2) / (4 * q.2))
  have hF : ContinuousAt F p := by
    have hbase : 4 * Real.pi * p.2 ≠ 0 := by positivity
    have hpow : ContinuousAt (fun s : ℝ =>
        (4 * Real.pi * s) ^ (-(3 : ℝ) / 2)) p.2 := by
      exact (Real.continuousAt_rpow_const (4 * Real.pi * p.2)
        (-(3 : ℝ) / 2) (Or.inl hbase)).comp (by fun_prop)
    have hpow' : ContinuousAt (fun q : Vec3 × ℝ =>
        (4 * Real.pi * q.2) ^ (-(3 : ℝ) / 2)) p :=
      hpow.comp continuous_snd.continuousAt
    have hexp : ContinuousAt (fun q : Vec3 × ℝ =>
        Real.exp (-(∑ i, q.1 i ^ 2) / (4 * q.2))) p := by
      apply (Real.continuous_exp.continuousAt).comp
      fun_prop (disch := positivity)
    change ContinuousAt ((fun q : Vec3 × ℝ =>
      (4 * Real.pi * q.2) ^ (-(3 : ℝ) / 2)) *
      (fun q : Vec3 × ℝ => Real.exp (-(∑ i, q.1 i ^ 2) / (4 * q.2)))) p
    simpa [F] using hpow'.mul hexp
  have hEq : (fun q : Vec3 × ℝ => heatKernel q.1 q.2) =ᶠ[𝓝 p] F := by
    have hnh : {q : Vec3 × ℝ | 0 < q.2} ∈ 𝓝 p := by
      exact (isOpen_lt continuous_const continuous_snd).mem_nhds hp0
    filter_upwards [hnh] with q hq
    exact heatKernel_eq_formula_sum hq
  exact hF.congr_of_eventuallyEq hEq |>.continuousWithinAt

private lemma backward_green_truncated_hWt_2 :
    ∀ {ζ : Vec3 × ℝ → ℝ} (x : Vec3) (t ε : ℝ),
      (0 : ℝ) < ε →
        let K : Set (Vec3 × ℝ) := (fun (z : Vec3 × ℝ) => (x - z.1, z.2 - t)) '' tsupport ζ;
        ∀ (C : ℝ),
          let B : ℝ := C - t;
          let B' : ℝ := max B ε + (1 : ℝ);
          let S : Set (Vec3 × ℝ) := K ∩ SProd.sprod (α := Set Vec3) univ (Icc ε B');
          ContinuousOn (Y := ℝ) (fun (p : Vec3 × ℝ) => heatKernelTimeDerivative p.1 p.2) S
    := by
  intro ζ x t ε hε K C B B' S p hp
  have hp0 : 0 < p.2 := lt_of_lt_of_le hε hp.2.2.1
  let F : Vec3 × ℝ → ℝ := fun q =>
    ((4 * Real.pi * q.2) ^ (-(3 : ℝ) / 2) *
      Real.exp (-(∑ i, q.1 i ^ 2) / (4 * q.2))) *
      ((∑ i, q.1 i ^ 2) / (4 * q.2 ^ 2) - (3 : ℝ) / (2 * q.2))
  have hF : ContinuousAt F p := by
    have hbase : 4 * Real.pi * p.2 ≠ 0 := by positivity
    have hpow : ContinuousAt (fun s : ℝ =>
        (4 * Real.pi * s) ^ (-(3 : ℝ) / 2)) p.2 := by
      exact (Real.continuousAt_rpow_const (4 * Real.pi * p.2)
        (-(3 : ℝ) / 2) (Or.inl hbase)).comp (by fun_prop)
    have hpow' : ContinuousAt (fun q : Vec3 × ℝ =>
        (4 * Real.pi * q.2) ^ (-(3 : ℝ) / 2)) p :=
      hpow.comp continuous_snd.continuousAt
    have hexp : ContinuousAt (fun q : Vec3 × ℝ =>
        Real.exp (-(∑ i, q.1 i ^ 2) / (4 * q.2))) p := by
      apply (Real.continuous_exp.continuousAt).comp
      fun_prop (disch := positivity)
    have hfrac : ContinuousAt (fun q : Vec3 × ℝ =>
        (∑ i, q.1 i ^ 2) / (4 * q.2 ^ 2) - (3 : ℝ) / (2 * q.2)) p := by
      fun_prop (disch := positivity)
    let G : Vec3 × ℝ → ℝ := fun q =>
      ((4 * Real.pi * q.2) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, q.1 i ^ 2) / (4 * q.2))) *
        ((∑ i, q.1 i ^ 2) / (4 * q.2 ^ 2) - (3 : ℝ) / (2 * q.2))
    have hG : ContinuousAt G p := by
      dsimp [G]
      exact (hpow'.mul hexp).mul hfrac
    simpa [F, G] using hG
  have hEq : (fun q : Vec3 × ℝ => heatKernelTimeDerivative q.1 q.2) =ᶠ[𝓝 p] F := by
    have hnh : {q : Vec3 × ℝ | 0 < q.2} ∈ 𝓝 p := by
      exact (isOpen_lt continuous_const continuous_snd).mem_nhds hp0
    filter_upwards [hnh] with q hq
    rw [heatKernelTimeDerivative, ite_eq_left hq,
      heatKernel_eq_formula_sum hq]
  exact hF.congr_of_eventuallyEq hEq |>.continuousWithinAt

private lemma backward_green_truncated_hslice_3 :
    ∀ {ζ : Vec3 × ℝ → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ζ →
        HasCompactSupport ζ →
          ∀ (x : Vec3) (t ε : ℝ),
            (0 : ℝ) < ε →
              let A : Vec3 × ℝ → ℝ := fun (p : Vec3 × ℝ) =>
                heatKernelTimeDerivative p.1 p.2 * ζ (x - p.1, t + p.2) +
                  heatKernel p.1 p.2 *
                    timePartial
                      (have this : ParabolicPoint → ℝ := ζ;
                      this)
                      (x - p.1, t + p.2);
              (Continuous (Y := ℝ) fun (z : Vec3 × ℝ) =>
                  timePartial
                    (have this : ParabolicPoint → ℝ := ζ;
                    this)
                    z) →
                ∀ (s : ℝ),
                  ε < s →
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                        A (y, s)) =
                      heatConv s
                        (fun (y : Vec3) =>
                          timePartial
                              (have this : ParabolicPoint → ℝ := ζ;
                              this)
                              (y, t + s) +
                            spatialLaplacian (fun (w : Vec3) => ζ (w, t + s)) y)
                        x
    := by
  intro ζ hζ hζc x t ε hε A htimecont s hs
  have hs0 : 0 < s := lt_trans hε hs
  let u : Vec3 → ℝ := fun y => ζ (y, t + s)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := test_slice_contDiff hζ (t + s)
  have huc : HasCompactSupport u := test_slice_hasCompactSupport hζc (t + s)
  have hWlap := heatKernel_laplacian_integral_eq_smooth hu huc hs0 x
  have hkernel : Continuous (fun y : Vec3 => heatKernel y s) := by
    rw [show (fun y : Vec3 => heatKernel y s) = fun y : Vec3 =>
        (4 * Real.pi * s) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ i, y i ^ 2) / (4 * s)) by
      funext y
      exact heatKernel_eq_formula_sum hs0]
    fun_prop (disch := positivity)
  have hlap : Continuous (fun y : Vec3 => heatKernelLaplacian y s) := by
    unfold heatKernelLaplacian
    apply continuous_finsetSum
    intro i hi
    rw [show (fun y : Vec3 => heatKernelSpaceSecondDerivative y s i) =
        fun y : Vec3 =>
          ((y i) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) *
            ((4 * Real.pi * s) ^ (-(3 : ℝ) / 2) *
              Real.exp (-(∑ j, y j ^ 2) / (4 * s))) by
      funext y
      rw [heatKernelSpaceSecondDerivative, ite_eq_left hs0,
        heatKernel_eq_formula_sum hs0]]
    fun_prop (disch := positivity)
  have hsp : Integrable (fun y : Vec3 =>
      heatKernelLaplacian y s * u (x - y)) volume := by
    have hcomp : HasCompactSupport (fun y : Vec3 => u (x - y)) :=
      huc.comp_homeomorph (Homeomorph.subLeft x)
    have hux : Continuous (fun y : Vec3 => u (x - y)) :=
      hu.continuous.comp (Homeomorph.subLeft x).continuous
    exact (hlap.mul hux).integrable_of_hasCompactSupport hcomp.mul_left
  have hpartc : HasCompactSupport (fun y : Vec3 =>
      CKN.timePartial (show ParabolicPoint → ℝ from ζ) (y, t + s)) := by
    let Kslice : Set Vec3 := (fun z : Vec3 × ℝ => z.1) '' tsupport ζ
    have hKslice : IsCompact Kslice := hζc.isCompact.image continuous_fst
    apply HasCompactSupport.intro hKslice
    intro y hy
    by_contra hne
    have hz : (y, t + s) ∉ tsupport ζ := by
      intro hz
      apply hy
      exact ⟨(y, t + s), hz, rfl⟩
    apply hne
    rw [timePartial_eq_fderiv_apply hζ y (t + s)]
    rw [fderiv_of_notMem_tsupport ℝ hz]
    simp
  have htime : Integrable (fun y : Vec3 =>
      heatKernel y s * CKN.timePartial
        (show ParabolicPoint → ℝ from ζ) (x - y, t + s)) volume := by
    have hcomp : HasCompactSupport (fun y : Vec3 =>
        CKN.timePartial (show ParabolicPoint → ℝ from ζ) (x - y, t + s)) :=
      hpartc.comp_homeomorph (Homeomorph.subLeft x)
    have htc : Continuous (fun y : Vec3 =>
        CKN.timePartial (show ParabolicPoint → ℝ from ζ) (x - y, t + s)) := by
      exact htimecont.comp (by fun_prop)
    exact (hkernel.mul htc).integrable_of_hasCompactSupport hcomp.mul_left
  have hdeltaC : HasCompactSupport (CKN.spatialLaplacian u) := by
    change HasCompactSupport (fun y : Vec3 =>
      ∑ i, CKN.spatialDeriv (CKN.spatialDeriv u i) i y)
    have hterm : ∀ i : Fin 3, HasCompactSupport
        (fun y : Vec3 => CKN.spatialDeriv (CKN.spatialDeriv u i) i y) := by
      intro i
      change HasCompactSupport (fun y : Vec3 =>
        (fderiv ℝ (CKN.spatialDeriv u i) y) (CKN.basisVec i))
      exact (huc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)).fderiv_apply
        (𝕜 := ℝ) (CKN.basisVec i)
    have hsum := HasCompactSupport.finset_sum
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i : Fin 3 => CKN.spatialDeriv (CKN.spatialDeriv u i) i)
      (fun i hi => hterm i)
    convert hsum using 1
    funext y
    simp only [Finset.sum_apply]
  have hdeltaCont : Continuous (CKN.spatialLaplacian u) :=
    (contDiff_spatialLaplacian_smooth hu).continuous
  have hdelta : Integrable (fun y : Vec3 =>
      heatKernel y s * CKN.spatialLaplacian u (x - y)) volume := by
    have hcomp : HasCompactSupport (fun y : Vec3 =>
        CKN.spatialLaplacian u (x - y)) :=
      hdeltaC.comp_homeomorph (Homeomorph.subLeft x)
    exact (hkernel.mul (hdeltaCont.comp (by fun_prop))).integrable_of_hasCompactSupport
      hcomp.mul_left
  have hkernelLap : ∫ y : Vec3, heatKernelTimeDerivative y s * u (x - y) =
      heatConv s (CKN.spatialLaplacian u) x := by
    rw [show (∫ y : Vec3, heatKernelTimeDerivative y s * u (x - y)) =
        ∫ y : Vec3, heatKernelLaplacian y s * u (x - y) by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [heatKernel_heat_equation hs0]]
    exact hWlap
  have hwtInt : Integrable (fun y : Vec3 =>
      heatKernelTimeDerivative y s * u (x - y)) volume := by
    apply hsp.congr
    filter_upwards [] with y
    rw [heatKernel_heat_equation hs0]
  calc
    ∫ y : Vec3, A (y, s) =
        (∫ y : Vec3, heatKernelTimeDerivative y s * u (x - y)) +
          ∫ y : Vec3, heatKernel y s *
            CKN.timePartial (show ParabolicPoint → ℝ from ζ) (x - y, t + s) := by
      rw [← integral_add hwtInt htime]
    _ = heatConv s (CKN.spatialLaplacian u) x +
        heatConv s (fun y : Vec3 =>
          CKN.timePartial (show ParabolicPoint → ℝ from ζ) (y, t + s)) x := by
      rw [hkernelLap, heatConv_eq_integral, heatConv_eq_integral]
    _ = heatConv s (fun y : Vec3 =>
        CKN.timePartial (show ParabolicPoint → ℝ from ζ) (y, t + s) +
          CKN.spatialLaplacian (fun w : Vec3 => ζ (w, t + s)) y) x := by
      calc
        heatConv s (CKN.spatialLaplacian u) x +
            heatConv s (fun y : Vec3 =>
              CKN.timePartial (show ParabolicPoint → ℝ from ζ) (y, t + s)) x =
            (∫ y : Vec3, heatKernel y s * CKN.spatialLaplacian u (x - y)) +
              ∫ y : Vec3, heatKernel y s *
                CKN.timePartial (show ParabolicPoint → ℝ from ζ) (x - y, t + s) := by
          rw [heatConv_eq_integral, heatConv_eq_integral]
        _ = ∫ y : Vec3, (heatKernel y s * CKN.spatialLaplacian u (x - y) +
              heatKernel y s * CKN.timePartial
                (show ParabolicPoint → ℝ from ζ) (x - y, t + s)) :=
          (integral_add hdelta htime).symm
        _ = heatConv s (fun y : Vec3 =>
            CKN.timePartial (show ParabolicPoint → ℝ from ζ) (y, t + s) +
              CKN.spatialLaplacian (fun w : Vec3 => ζ (w, t + s)) y) x := by
          rw [heatConv_eq_integral]
          apply integral_congr_ae
          filter_upwards [] with y
          simp only [u]
          ring

private lemma backward_green_truncated
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (x : Vec3) (t ε : ℝ) (hε : 0 < ε) :
    ∫ s : ℝ in Ioi ε,
        heatConv s (fun y : Vec3 =>
          CKN.timePartial (show ParabolicPoint → ℝ from ζ) (y, t + s) +
            CKN.spatialLaplacian (fun w : Vec3 => ζ (w, t + s)) y) x =
      -heatConv ε (fun y : Vec3 => ζ (y, t + ε)) x := by
  let A : Vec3 × ℝ → ℝ := fun p =>
    heatKernelTimeDerivative p.1 p.2 * ζ (x - p.1, t + p.2) +
      heatKernel p.1 p.2 * CKN.timePartial
        (show ParabolicPoint → ℝ from ζ) (x - p.1, t + p.2)
  let K : Set (Vec3 × ℝ) :=
    (fun z : Vec3 × ℝ => (x - z.1, z.2 - t)) '' tsupport ζ
  have hK : IsCompact K := by
    apply hζc.isCompact.image
    fun_prop
  let Kt : Set ℝ := (fun z : Vec3 × ℝ => z.2) '' tsupport ζ
  rcases hζc.isCompact.image continuous_snd |>.bddAbove with ⟨C, hC⟩
  let B : ℝ := C - t
  let B' : ℝ := max B ε + 1
  have hB : B < B' := by
    dsimp [B']
    linarith only [le_max_left B ε]
  let S : Set (Vec3 × ℝ) :=
    K ∩ ((Set.univ : Set Vec3) ×ˢ Icc ε B')
  have hS : IsCompact S := by
    apply hK.inter_right
    exact isClosed_univ.prod isClosed_Icc
  have htimecont : Continuous (fun z : Vec3 × ℝ =>
      CKN.timePartial (show ParabolicPoint → ℝ from ζ) z) := by
    rw [show (fun z : Vec3 × ℝ => CKN.timePartial
        (show ParabolicPoint → ℝ from ζ) z) =
        (fun z => (fderiv ℝ ζ z) (0, 1)) by
      funext z
      simpa using timePartial_eq_fderiv_apply hζ z.1 z.2]
    exact (hζ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hW := @backward_green_truncated_hW_1 ζ x t ε hε C
  have hWt := @backward_green_truncated_hWt_2 ζ x t ε hε C
  have hsource : Continuous (fun p : Vec3 × ℝ =>
      ζ (x - p.1, t + p.2)) := by
    fun_prop
  have hsourceTime : Continuous (fun p : Vec3 × ℝ =>
      CKN.timePartial (show ParabolicPoint → ℝ from ζ) (x - p.1, t + p.2)) := by
    exact htimecont.comp (by fun_prop)
  have hAcont : ContinuousOn A S := by
    dsimp [A]
    exact ((hWt.mul hsource.continuousOn).add
      (hW.mul hsourceTime.continuousOn))
  have hAcompact : IntegrableOn A S backwardProductVolume :=
    let _ : IsFiniteMeasureOnCompacts backwardProductVolume := by
      dsimp [backwardProductVolume]
      infer_instance
    hAcont.integrableOn_compact hS
  have hAsupport :
      (Set.univ ×ˢ Ioi ε) ∩ Function.support A ⊆ S := by
    intro p hp
    have hpε : ε < p.2 := hp.1.2
    have hpK : p ∈ K := by
      by_contra hnot
      have hz : (x - p.1, t + p.2) ∉ tsupport ζ := by
        intro hz
        refine hnot ⟨(x - p.1, t + p.2), hz, ?_⟩
        ext <;> simp
      have hz0 : ζ (x - p.1, t + p.2) = 0 :=
        image_eq_zero_of_notMem_tsupport hz
      have hdz : CKN.timePartial (show ParabolicPoint → ℝ from ζ)
          (x - p.1, t + p.2) = 0 := by
        rw [timePartial_eq_fderiv_apply hζ (x - p.1) (t + p.2)]
        rw [fderiv_of_notMem_tsupport ℝ hz]
        simp
      exact (Function.mem_support.mp hp.2) (by
        dsimp [A]
        rw [hz0, hdz]
        ring)
    have hpB : p.2 ≤ B' := by
      rcases hpK with ⟨z, hz, rfl⟩
      have htime := hC ⟨z, hz, rfl⟩
      dsimp [B, B']
      linarith only [htime, le_max_left (C - t) ε]
    exact ⟨hpK, ⟨Set.mem_univ _, hpε.le, hpB⟩⟩
  have hAset : IntegrableOn A (Set.univ ×ˢ Ioi ε) backwardProductVolume := by
    apply (hAcompact.mono_set hAsupport).of_inter_support
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hAprod : Integrable A
      ((volume : Measure Vec3).prod (volume.restrict (Ioi ε))) := by
    have hmeasure :
        (volume : Measure Vec3).prod (volume.restrict (Ioi ε)) =
          backwardProductVolume.restrict (Set.univ ×ˢ Ioi ε) := by
      rw [backwardProductVolume, ← Measure.prod_restrict]
      simp
    rw [hmeasure]
    change Integrable A (backwardProductVolume.restrict (Set.univ ×ˢ Ioi ε))
    exact hAset
  have hBint : Integrable (fun y : Vec3 =>
      heatKernel y ε * ζ (x - y, t + ε)) volume := by
    have hcont : Continuous (fun y : Vec3 =>
        heatKernel y ε * ζ (x - y, t + ε)) := by
      have hkernel : Continuous (fun y : Vec3 => heatKernel y ε) := by
        rw [show (fun y : Vec3 => heatKernel y ε) = fun y : Vec3 =>
            (4 * Real.pi * ε) ^ (-(3 : ℝ) / 2) *
              Real.exp (-(∑ i, y i ^ 2) / (4 * ε)) by
          funext y
          exact heatKernel_eq_formula_sum hε]
        fun_prop (disch := positivity)
      exact hkernel.mul (by fun_prop)
    have hsupp : HasCompactSupport (fun y : Vec3 =>
        heatKernel y ε * ζ (x - y, t + ε)) := by
      have hslice := test_slice_hasCompactSupport hζc (t + ε)
      exact (hslice.comp_homeomorph (Homeomorph.subLeft x)).mul_left
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hpoint : ∀ y : Vec3,
      ∫ s : ℝ in Ioi ε, A (y, s) =
        -(heatKernel y ε * ζ (x - y, t + ε)) := by
    intro y
    exact shifted_time_green hζ hζc x y t ε hε
  have hswap : ∫ s : ℝ in Ioi ε, ∫ y : Vec3, A (y, s) =
      ∫ y : Vec3, ∫ s : ℝ in Ioi ε, A (y, s) := by
    have hs := integral_prod_swap A
      (μ := (volume : Measure Vec3)) (ν := volume.restrict (Ioi ε))
    have hp := integral_prod (fun q : ℝ × Vec3 => A q.swap) hAprod.swap
    calc
      ∫ s : ℝ in Ioi ε, ∫ y : Vec3, A (y, s) =
          ∫ q : ℝ × Vec3, A q.swap ∂
            ((volume.restrict (Ioi ε)).prod volume) := by
        simpa only [Prod.swap_prod_mk] using hp.symm
      _ = ∫ q : Vec3 × ℝ, A q ∂
          ((volume : Measure Vec3).prod (volume.restrict (Ioi ε))) := hs
      _ = ∫ y : Vec3, ∫ s : ℝ in Ioi ε, A (y, s) :=
        integral_prod A hAprod
  have hgreen : ∫ s : ℝ in Ioi ε, ∫ y : Vec3, A (y, s) =
      -∫ y : Vec3, heatKernel y ε * ζ (x - y, t + ε) := by
    rw [hswap]
    rw [show (fun y : Vec3 => ∫ s : ℝ in Ioi ε, A (y, s)) =
        (fun y : Vec3 => -(heatKernel y ε * ζ (x - y, t + ε))) by
      funext y
      exact hpoint y]
    rw [integral_neg]
  have hslice := @backward_green_truncated_hslice_3 ζ hζ hζc x t ε hε htimecont
  calc
    ∫ s : ℝ in Ioi ε, heatConv s (fun y : Vec3 =>
        CKN.timePartial (show ParabolicPoint → ℝ from ζ) (y, t + s) +
          CKN.spatialLaplacian (fun w : Vec3 => ζ (w, t + s)) y) x =
        ∫ s : ℝ in Ioi ε, ∫ y : Vec3, A (y, s) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [hslice s hs]
    _ = -∫ y : Vec3, heatKernel y ε * ζ (x - y, t + ε) := hgreen
    _ = -heatConv ε (fun y : Vec3 => ζ (y, t + ε)) x := by
      rw [heatConv_eq_integral]

theorem backwardTestPotential_heat_equation
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (x : Vec3) (t : ℝ) :
    -CKN.timePartial (show ParabolicPoint → ℝ from
        fun z => backwardTestPotential ζ z) (x, t) -
        ∑ i : Fin 3, CKN.spatialSecondPartial (show ParabolicPoint → ℝ from
          fun z => backwardTestPotential ζ z) i i (x, t) = ζ (x, t) := by
  have htimeSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ =>
      CKN.timePartial (show ParabolicPoint → ℝ from ζ) z) := by
    let F : (Vec3 × ℝ) → ℝ → ℝ := fun z s => ζ (z.1, s)
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : (Vec3 × ℝ) × ℝ => (q.1.1, q.2)) := by
      fun_prop
    have hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) := by
      convert hζ.comp hmap using 1
      funext q
      rfl
    have hderiv := hF.fderiv_apply
      (contDiff_snd (𝕜 := ℝ) (n := (⊤ : ℕ∞)))
      (contDiff_const (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (c := (1 : ℝ)))
      (by simp)
    simpa only [F, CKN.timePartial, Function.uncurry] using hderiv
  have htimeCompact : HasCompactSupport (fun z : Vec3 × ℝ =>
      CKN.timePartial (show ParabolicPoint → ℝ from ζ) z) := by
    rw [show (fun z : Vec3 × ℝ => CKN.timePartial
        (show ParabolicPoint → ℝ from ζ) z) =
        (fun z => (fderiv ℝ ζ z) (0, 1)) by
      funext z
      simpa using timePartial_eq_fderiv_apply hζ z.1 z.2]
    exact hζc.fderiv_apply (𝕜 := ℝ) (0, 1)
  have hsecondSmooth : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ =>
      CKN.spatialSecondPartial (show ParabolicPoint → ℝ from ζ) i i z) := by
    intro i
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ =>
      CKN.spatialPartial (fun w => CKN.spatialPartial
        (show ParabolicPoint → ℝ from ζ) i w) i z)
    exact spatialPartial_contDiff (spatialPartial_contDiff hζ i) i
  have hsecondCompact : ∀ i : Fin 3, HasCompactSupport (fun z : Vec3 × ℝ =>
      CKN.spatialSecondPartial (show ParabolicPoint → ℝ from ζ) i i z) := by
    intro i
    let η : Vec3 × ℝ → ℝ := fun z => CKN.spatialPartial
      (show ParabolicPoint → ℝ from ζ) i z
    have hηc : HasCompactSupport η := by
      rw [show η = (fun z : Vec3 × ℝ => (fderiv ℝ ζ z)
          (CKN.basisVec i, 0)) by
        funext z
        dsimp [η]
        exact spatialPartial_eq_fderiv_apply hζ i z.1 z.2]
      exact hζc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i, 0)
    rw [show (fun z : Vec3 × ℝ => CKN.spatialSecondPartial
        (show ParabolicPoint → ℝ from ζ) i i z) =
        (fun z => (fderiv ℝ η z) (CKN.basisVec i, 0)) by
      funext z
      dsimp [η]
      exact spatialPartial_eq_fderiv_apply
        (spatialPartial_contDiff hζ i) i z.1 z.2]
    exact hηc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i, 0)
  let D : Vec3 × ℝ → ℝ := fun z =>
    CKN.timePartial (show ParabolicPoint → ℝ from ζ) z +
      ∑ i : Fin 3, CKN.spatialSecondPartial
        (show ParabolicPoint → ℝ from ζ) i i z
  have hsecondSumSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, CKN.spatialSecondPartial
        (show ParabolicPoint → ℝ from ζ) i i z) := by
    have hsum := ContDiff.sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i : Fin 3 => fun z : Vec3 × ℝ =>
        CKN.spatialSecondPartial (show ParabolicPoint → ℝ from ζ) i i z)
      (fun i hi => hsecondSmooth i)
    simpa only [Finset.sum_apply] using hsum
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := by
    dsimp [D]
    exact htimeSmooth.add hsecondSumSmooth
  have hsecondSumCompact : HasCompactSupport (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, CKN.spatialSecondPartial
        (show ParabolicPoint → ℝ from ζ) i i z) := by
    have hsum := HasCompactSupport.finset_sum
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i : Fin 3 => fun z : Vec3 × ℝ =>
        CKN.spatialSecondPartial (show ParabolicPoint → ℝ from ζ) i i z)
      (fun i hi => hsecondCompact i)
    convert hsum using 1
    funext z
    simp only [Finset.sum_apply]
  have hDc : HasCompactSupport D := by
    dsimp [D]
    exact htimeCompact.add hsecondSumCompact
  have hDlim := backwardTestPotential_future_truncated_tendsto hD hDc x t
  have hgreenlim : Tendsto (fun ε : ℝ =>
      ∫ s : ℝ in Ioi ε, heatConv s (fun y : Vec3 => D (y, t + s)) x)
      (𝓝[>] 0) (𝓝 (-ζ (x, t))) := by
    have hboundary := (heatConv_time_shift_tendsto hζ hζc x t).neg
    apply hboundary.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← backward_green_truncated hζ hζc x t ε hε]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    congr 2
  have hDvalue : backwardTestPotential D (x, t) = -ζ (x, t) := by
    have hEq := tendsto_nhds_unique hDlim hgreenlim
    exact hEq
  let ηt : Vec3 × ℝ → ℝ := fun z =>
    CKN.timePartial (show ParabolicPoint → ℝ from ζ) z
  let ηi : Fin 3 → Vec3 × ℝ → ℝ := fun i z =>
    CKN.spatialSecondPartial (show ParabolicPoint → ℝ from ζ) i i z
  have hD_eq : D = ηt + ∑ i : Fin 3, ηi i := by
    funext z
    rfl
  have hconvT := htimeCompact.convolutionExists_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) backwardTestKernel_locallyIntegrable
    htimeSmooth.continuous
  have hconvI : ∀ i : Fin 3,
      ConvolutionExists backwardTestKernel (ηi i)
        (ContinuousLinearMap.lsmul ℝ ℝ) backwardProductVolume := by
    intro i
    exact (hsecondCompact i).convolutionExists_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) backwardTestKernel_locallyIntegrable
      (hsecondSmooth i).continuous
  have hsumSmooth : ContDiff ℝ (⊤ : ℕ∞) (∑ i : Fin 3, ηi i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, CKN.spatialSecondPartial
        (show ParabolicPoint → ℝ from ζ) i i z)
    exact hsecondSumSmooth
  have hconvSum := hsecondSumCompact.convolutionExists_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) backwardTestKernel_locallyIntegrable
    hsumSmooth.continuous
  have hsumConv :
      MeasureTheory.convolution backwardTestKernel (∑ i : Fin 3, ηi i)
          (ContinuousLinearMap.lsmul ℝ ℝ) backwardProductVolume (x, t) =
        ∑ i : Fin 3, MeasureTheory.convolution backwardTestKernel (ηi i)
          (ContinuousLinearMap.lsmul ℝ ℝ) backwardProductVolume (x, t) := by
    simp only [MeasureTheory.convolution_lsmul, smul_eq_mul]
    have hIi : ∀ i : Fin 3, Integrable (fun p : Vec3 × ℝ =>
        backwardTestKernel p * ηi i ((x, t) - p)) backwardProductVolume := by
      intro i
      change Integrable (fun p : Vec3 × ℝ =>
        ContinuousLinearMap.lsmul ℝ ℝ (backwardTestKernel p)
          (ηi i ((x, t) - p))) backwardProductVolume
      exact (hconvI i (x, t)).integrable
    rw [← integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun i hi => hIi i)]
    apply integral_congr_ae
    filter_upwards [] with p
    simp only [Finset.sum_apply, Finset.mul_sum]
  have htotalConv :
      MeasureTheory.convolution backwardTestKernel D
          (ContinuousLinearMap.lsmul ℝ ℝ) backwardProductVolume (x, t) =
        MeasureTheory.convolution backwardTestKernel ηt
          (ContinuousLinearMap.lsmul ℝ ℝ) backwardProductVolume (x, t) +
          MeasureTheory.convolution backwardTestKernel (∑ i : Fin 3, ηi i)
          (ContinuousLinearMap.lsmul ℝ ℝ) backwardProductVolume (x, t) := by
    rw [hD_eq]
    exact congrFun (ConvolutionExists.distrib_add hconvT hconvSum) (x, t)
  have hP : backwardTestPotential D (x, t) =
      backwardTestPotential ηt (x, t) +
        ∑ i : Fin 3, backwardTestPotential (ηi i) (x, t) := by
    unfold backwardTestPotential
    rw [htotalConv, hsumConv]
  have htimeP := backwardTestPotential_timePartial hζ hζc x t
  have htimeP' : CKN.timePartial (show ParabolicPoint → ℝ from
      fun z => backwardTestPotential ζ z) (x, t) =
      backwardTestPotential ηt (x, t) := by
    simpa only [ηt] using htimeP
  have hsecondP : ∀ i : Fin 3,
      CKN.spatialSecondPartial (show ParabolicPoint → ℝ from
        fun z => backwardTestPotential ζ z) i i (x, t) =
        backwardTestPotential (ηi i) (x, t) := by
    intro i
    simpa only [ηi] using
      (backwardTestPotential_spatialSecondPartial hζ hζc i i x t)
  calc
    -CKN.timePartial (show ParabolicPoint → ℝ from
        fun z => backwardTestPotential ζ z) (x, t) -
        ∑ i : Fin 3, CKN.spatialSecondPartial (show ParabolicPoint → ℝ from
          fun z => backwardTestPotential ζ z) i i (x, t) =
        -backwardTestPotential ηt (x, t) -
          ∑ i : Fin 3, backwardTestPotential (ηi i) (x, t) := by
      rw [htimeP']
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact hsecondP i
    _ = -backwardTestPotential D (x, t) := by
      rw [hP]
      ring
    _ = ζ (x, t) := by
      rw [hDvalue]
      ring


end CKN.Foundation.Heat
