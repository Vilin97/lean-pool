/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP7SolutionBound
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalP8

/-!
# Lin34 Slice Force Cylinder

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-! The two cylinder bounds for the force terms `p₇` and `p₈` are added into a
single `L^{3/2}` bound on the parabolic cylinder.  This is the estimate
`r^{-2} ∬_{Q_r} |p₇ + p₈|^{3/2} ≤ (C₁₃(q) κ λ(z₀,ρ))^{3/2}` appearing in the
proof of `prop:lin34`(ii-b) of `paper/ckn.tex`. -/

/-- The force term `p₈` is a.e. strongly measurable on the parabolic cylinder
`Q_ρ`, so that it can be added to `p₇` in `L^{3/2}`. -/
private theorem pressureP8_aestronglyMeasurable_on_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    AEStronglyMeasurable
      (fun w : ParabolicPoint =>
        pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
  let B : Set Vec3 := vec3Ball z.1 ρ
  let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hfglobal : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.2.1
  let fm : ParabolicPoint → Vec3 := hfglobal.mk f
  have hfm : Measurable fm := hfglobal.measurable_mk
  have hfmj (j : Fin 3) : Measurable (fun w : ParabolicPoint => fm w j) :=
    (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).measurable.comp hfm
  have hdηj (j : Fin 3) : Measurable (fun y : Vec3 =>
      CKN.spatialDeriv (mollifiedBallCutoff z.1 hρ) j y) := by
    simpa only [CKN.spatialDeriv] using
      measurable_fderiv_apply_const ℝ (mollifiedBallCutoff z.1 hρ)
        (CKN.basisVec j)
  have hkernel : Measurable (fun w : ParabolicPoint × Vec3 =>
      -CKN.Foundation.Heat.newtonianKernel (w.1.1 - w.2)) := by
    have hnorm : Measurable (fun w : ParabolicPoint × Vec3 =>
        vec3EuclideanNorm (w.1.1 - w.2)) := by
      unfold vec3EuclideanNorm
      fun_prop
    unfold CKN.Foundation.Heat.newtonianKernel
    exact (measurable_const.div (measurable_const.mul hnorm)).neg
  let P : Fin 3 → ParabolicPoint → ℝ := fun j w =>
    ∫ y : Vec3, (-CKN.Foundation.Heat.newtonianKernel (w.1 - y)) *
      (CKN.spatialDeriv (mollifiedBallCutoff z.1 hρ) j y * fm (y, w.2) j)
  have hPmeas (j : Fin 3) : AEMeasurable (P j) volume := by
    have hmap : Measurable (fun w : ParabolicPoint × Vec3 =>
        (w.2, w.1.2)) :=
      measurable_snd.prodMk (measurable_snd.comp measurable_fst)
    have hsource' : Measurable (fun w : ParabolicPoint × Vec3 =>
        CKN.spatialDeriv (mollifiedBallCutoff z.1 hρ) j w.2 *
          fm (w.2, w.1.2) j) :=
      ((hdηj j).comp measurable_snd).mul ((hfmj j).comp hmap)
    have hF : Measurable (fun w : ParabolicPoint × Vec3 =>
        (-CKN.Foundation.Heat.newtonianKernel (w.1.1 - w.2)) *
          (CKN.spatialDeriv (mollifiedBallCutoff z.1 hρ) j w.2 *
            fm (w.2, w.1.2) j)) :=
      hkernel.mul hsource'
    have hF' : AEStronglyMeasurable (fun w : ParabolicPoint × Vec3 =>
        (-CKN.Foundation.Heat.newtonianKernel (w.1.1 - w.2)) *
          (CKN.spatialDeriv (mollifiedBallCutoff z.1 hρ) j w.2 *
            fm (w.2, w.1.2) j))
        (volume.prod volume) := by
      simpa only [Function.comp_apply] using hF.aestronglyMeasurable
    have hI := hF'.integral_prod_right'
    simpa only [P] using hI.aemeasurable
  let Psum : ParabolicPoint → ℝ := fun w => -∑ j, P j w
  have hPsum : AEMeasurable Psum volume := by
    exact (Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
      (fun j _ => hPmeas j)).neg
  have hfg : f =ᵐ[volume.restrict (spaceTimeSet Ω' J)] fm := hfglobal.ae_eq_mk
  have hBT : B ×ˢ T ⊆ spaceTimeSet Ω' J := by
    intro w hw
    exact ⟨hball hw.1, htime hw.2⟩
  have hfgBT : f =ᵐ[volume.restrict (B ×ˢ T)] fm :=
    ae_restrict_of_ae_restrict_of_subset hBT hfg
  have hfgBT' : f =ᵐ[(volume.restrict B).prod (volume.restrict T)] fm := by
    rw [show volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]] at hfgBT
    exact hfgBT
  have hfgSwap : (fun w : ℝ × Vec3 => f (w.2, w.1)) =ᵐ[
      (volume.restrict T).prod (volume.restrict B)]
      (fun w => fm (w.2, w.1)) := by
    exact MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
      hfgBT'
  have hfgSlices : ∀ᵐ s ∂volume.restrict T, ∀ᵐ y ∂volume.restrict B,
      f (y, s) = fm (y, s) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hfgSwap
  have hpot : ∀ᵐ s ∂volume.restrict T, ∀ x : Vec3, ∀ j : Fin 3,
      pressureNewtonianPotential
          (fun y => CKN.spatialDeriv (mollifiedBallCutoff z.1 hρ) j y *
            f (y, s) j) x =
        P j (x, s) := by
    filter_upwards [hfgSlices] with s hs
    have hsourceEq (j : Fin 3) :
        (fun y : Vec3 => CKN.spatialDeriv (mollifiedBallCutoff z.1 hρ) j y *
            f (y, s) j) =ᵐ[volume]
          (fun y => CKN.spatialDeriv (mollifiedBallCutoff z.1 hρ) j y *
            fm (y, s) j) := by
      apply ae_of_ae_restrict_of_ae_restrict_compl B
      · filter_upwards [hs] with y hy
        exact congrArg (fun a : ℝ =>
          CKN.spatialDeriv (mollifiedBallCutoff z.1 hρ) j y * a)
          (congrArg (fun v : Vec3 => v j) hy)
      · filter_upwards [ae_restrict_mem (show MeasurableSet Bᶜ from
          (vec3Ball_measurable z.1 ρ).compl)] with y hy
        have hy' : y ∉ tsupport (mollifiedBallCutoff z.1 hρ) := by
          intro hyt
          exact hy (pressure_cutoff_support_subset_ball z.1 hρ hyt)
        have hzero : CKN.spatialDeriv (mollifiedBallCutoff z.1 hρ) j y = 0 := by
          simp only [CKN.spatialDeriv]
          rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hy']
          simp
        rw [hzero]
        simp
    intro x j
    unfold pressureNewtonianPotential P
    apply integral_congr_ae
    filter_upwards [hsourceEq j] with y hy
    simp only [hy]
  have hPae : (fun w : Vec3 × ℝ =>
      pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) =ᵐ[
        volume.restrict (B ×ˢ T)] Psum := by
    have hpot' : ∀ᵐ s ∂volume.restrict T, ∀ x : Vec3,
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s x = Psum (x, s) := by
      filter_upwards [hpot] with s hs
      intro x
      change -∑ j, pressureNewtonianPotential
          (fun y => CKN.spatialDeriv (mollifiedBallCutoff z.1 hρ) j y *
            f (y, s) j) x =
        -∑ j, P j (x, s)
      apply congrArg Neg.neg
      exact Finset.sum_congr rfl (fun j _ => hs x j)
    have hprod : ∀ᵐ w ∂(volume.restrict B).prod (volume.restrict T),
        pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 = Psum (w.1, w.2) := by
      have hsnd := (Measure.quasiMeasurePreserving_snd
        (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot'
      filter_upwards [hsnd] with w hw
      exact hw w.1
    rw [show volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]]
    exact hprod
  have hPsumR : AEMeasurable Psum
      (volume.restrict (B ×ˢ T)) := hPsum.mono_measure
        (Measure.restrict_le_self)
  have hPae' : (fun w : ParabolicPoint =>
      pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) =ᵐ[
        volume.restrict (parabolicCylinder z.1 z.2 ρ)] Psum := by
    change (fun w : Vec3 × ℝ =>
      pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) =ᵐ[
        volume.restrict (parabolicCylinder z.1 z.2 ρ)] Psum
    have hset : parabolicCylinder z.1 z.2 ρ = B ×ˢ T := by
      ext w
      rfl
    rw [hset]
    exact hPae
  have hPsumC : AEMeasurable Psum
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    simpa [ParabolicPoint, parabolicCylinder, B, T] using hPsumR
  exact hPsumC.aestronglyMeasurable.congr hPae'.symm

/-- The constant `C₁₃(q)` of `lem:pk-bounds`(d)--(e) in `paper/ckn.tex`. -/
noncomputable def lin34ForceCylinderConstant (q : ℝ) : ℝ :=
  (pressureP7SolutionConstant q).toReal + pressureP13Constant q

/-- The constant `C₁₃(q)` of `lem:pk-bounds`(d)--(e) in `paper/ckn.tex` is
nonnegative for `q > 5/2`. -/
theorem lin34ForceCylinderConstant_nonneg (q : ℝ) (hq : 5 / 2 < q) :
    0 ≤ lin34ForceCylinderConstant q := by
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  unfold lin34ForceCylinderConstant
  have h13 : 0 ≤ pressureP13Constant q :=
    pressureP13Constant_nonneg (x₀ := (0 : Vec3)) (ρ := q) (q := q) hqpos
  exact add_nonneg ENNReal.toReal_nonneg h13

/-- The real-valued cylinder bound for the summed force terms in the proof of
`prop:lin34`(ii-b) of `paper/ckn.tex`: integrating `|p₇ + p₈|^{3/2}` over
`Q_r` is bounded by `r^2 (C₁₃(q) κ λ(z₀,ρ))^{3/2}`, the `L^{3/2}` form of
`lem:pk-bounds`(d)--(e). -/
theorem lin34_force_cylinder_lintegral_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (|pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1| ^ (3 / 2 : ℝ))) ≤
      ENNReal.ofReal (r ^ 2 *
        (lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ)) ^ (3 / 2 : ℝ)) := by
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hlam : 0 ≤ lambda q f z ρ := by unfold lambda; positivity
  have hkappa : 0 ≤ r / ρ := by positivity
  have hkl : 0 ≤ (r / ρ) * lambda q f z ρ := mul_nonneg hkappa hlam
  have hC : 0 ≤ lin34ForceCylinderConstant q := lin34ForceCylinderConstant_nonneg q hq
  have hCkl : 0 ≤ lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ) :=
    mul_nonneg hC hkl
  have hQr : parabolicCylinder z.1 z.2 r ⊆ parabolicCylinder z.1 z.2 ρ := by
    intro w hw
    change w.1 ∈ vec3Ball z.1 r ∧ w.2 ∈ Ioc (z.2 - r ^ 2) z.2 at hw
    change w.1 ∈ vec3Ball z.1 ρ ∧ w.2 ∈ Ioc (z.2 - ρ ^ 2) z.2
    rcases hw with ⟨hwx, hwt⟩
    refine ⟨?_, ?_⟩
    · rw [mem_vec3Ball] at hwx ⊢
      have hrho : r ≤ ρ := hhalf.trans (by linarith only [hρ])
      exact lt_of_lt_of_le hwx hrho
    · have hρ0 : 0 ≤ ρ := by linarith only [hhalf, hr]
      have hsq : r ^ 2 ≤ ρ ^ 2 :=
        (sq_le_sq₀ hr.le hρ0).2 (by linarith only [hhalf, hρ0])
      exact ⟨by linarith only [hwt.1, hsq], hwt.2⟩
  have hp7m : AEStronglyMeasurable
      (fun w : ParabolicPoint =>
        pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
    (pressureP7_aestronglyMeasurable_on_cylinder hsol hρ hsub).mono_measure
      (Measure.restrict_mono_set volume hQr)
  have hp8m : AEStronglyMeasurable
      (fun w : ParabolicPoint =>
        pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
    (pressureP8_aestronglyMeasurable_on_cylinder hsol hρ hsub).mono_measure
      (Measure.restrict_mono_set volume hQr)
  have htri :
      eLpNorm' (fun w : ParabolicPoint =>
          pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
            pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
        eLpNorm' (fun w : ParabolicPoint =>
            pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
            (volume.restrict (parabolicCylinder z.1 z.2 r)) +
          eLpNorm' (fun w : ParabolicPoint =>
            pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
            (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
    eLpNorm'_add_le hp7m hp8m (by norm_num)
  have h7 := pressureP7_bound hsol hρ hr hhalf hsub
  have h8 := pressureP8_bound hsol hρ hr hhalf hsub
  have hP7cast :
      pressureP7SolutionConstant q *
          ENNReal.ofReal ((r / ρ) * lambda q f z ρ) =
        ENNReal.ofReal
          ((pressureP7SolutionConstant q).toReal * ((r / ρ) * lambda q f z ρ)) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    rw [ENNReal.ofReal_toReal (pressureP7SolutionConstant_ne_top hq)]
  have hP8cast :
      ENNReal.ofReal (pressureP13Constant q * (r / ρ) * lambda q f z ρ) =
        ENNReal.ofReal (pressureP13Constant q * ((r / ρ) * lambda q f z ρ)) := by
    congr 1
    ring
  have h13 : 0 ≤ pressureP13Constant q :=
    pressureP13Constant_nonneg (x₀ := (0 : Vec3)) (ρ := 1) (q := q) (by norm_num)
  have hsumcast :
      ENNReal.ofReal
            ((pressureP7SolutionConstant q).toReal * ((r / ρ) * lambda q f z ρ)) +
          ENNReal.ofReal (pressureP13Constant q * ((r / ρ) * lambda q f z ρ)) =
        ENNReal.ofReal (lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ)) := by
    rw [← ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hkl)
      (mul_nonneg h13 hkl)]
    congr 1
    unfold lin34ForceCylinderConstant
    ring
  have hmain :
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          eLpNorm' (fun w : ParabolicPoint =>
            pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
              pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
            (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
        ENNReal.ofReal (lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ)) := by
    calc
      _ ≤ ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          (eLpNorm' (fun w : ParabolicPoint =>
              pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
              (volume.restrict (parabolicCylinder z.1 z.2 r)) +
            eLpNorm' (fun w : ParabolicPoint =>
              pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
              (volume.restrict (parabolicCylinder z.1 z.2 r))) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
      _ = ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
            eLpNorm' (fun w : ParabolicPoint =>
              pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
              (volume.restrict (parabolicCylinder z.1 z.2 r)) +
          ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
            eLpNorm' (fun w : ParabolicPoint =>
              pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
              (volume.restrict (parabolicCylinder z.1 z.2 r)) := by ring
      _ ≤ ENNReal.ofReal
            ((pressureP7SolutionConstant q).toReal * ((r / ρ) * lambda q f z ρ)) +
          ENNReal.ofReal (pressureP13Constant q * ((r / ρ) * lambda q f z ρ)) :=
        add_le_add (h7.trans hP7cast.le) (h8.trans hP8cast.le)
      _ = ENNReal.ofReal
          (lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ)) := hsumcast
  have hB : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ‖pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1‖ₑ ^ (3 / 2 : ℝ)) ≤
      ENNReal.ofReal (r ^ 2 *
        (lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ)) ^ (3 / 2 : ℝ)) := by
    set B : ℝ≥0∞ := ∫⁻ w in parabolicCylinder z.1 z.2 r,
        ‖pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1‖ₑ ^ (3 / 2 : ℝ) with hBdef
    have hH : ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) * B ^ (2 / 3 : ℝ) ≤
        ENNReal.ofReal (lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ)) := by
      have h := hmain
      rw [eLpNorm'_eq_lintegral_enorm] at h
      rw [show (1 : ℝ) / (3 / 2) = 2 / 3 by norm_num] at h
      exact h
    have hXpow : (ENNReal.ofReal (r ^ (-4 / 3 : ℝ))) ^ (3 / 2 : ℝ) =
        ENNReal.ofReal (r ^ (-2 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hr _)]
      congr 1
      rw [← Real.rpow_mul hr.le]
      norm_num
    have hBpow : (B ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = B := by
      rw [← ENNReal.rpow_mul, show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num,
        ENNReal.rpow_one]
    have hZpow : (ENNReal.ofReal
          (lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ))) ^ (3 / 2 : ℝ) =
        ENNReal.ofReal
          ((lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ)) ^
            (3 / 2 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg hCkl (by norm_num)
    have hpow' : ENNReal.ofReal (r ^ (-2 : ℝ)) * B ≤
        ENNReal.ofReal
          ((lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ)) ^
            (3 / 2 : ℝ)) := by
      have h := ENNReal.rpow_le_rpow hH (by norm_num : (0 : ℝ) ≤ 3 / 2)
      rwa [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2),
        hXpow, hBpow, hZpow] at h
    have hrr : r ^ 2 * r ^ (-2 : ℝ) = 1 := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
      norm_num
    have hleft : ENNReal.ofReal (r ^ 2) *
        (ENNReal.ofReal (r ^ (-2 : ℝ)) * B) = B := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ r ^ 2),
        hrr, ENNReal.ofReal_one, one_mul]
    have hright : ENNReal.ofReal (r ^ 2) * ENNReal.ofReal
          ((lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ)) ^
            (3 / 2 : ℝ)) =
        ENNReal.ofReal (r ^ 2 *
          (lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ)) ^
            (3 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ r ^ 2)]
    have hfin := mul_le_mul_of_nonneg_left hpow'
      (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ 2))
    rwa [hleft, hright] at hfin
  calc
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (|pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1| ^ (3 / 2 : ℝ)))
        = (∫⁻ w in parabolicCylinder z.1 z.2 r,
            ‖pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
              pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1‖ₑ ^
                (3 / 2 : ℝ)) := by
          apply lintegral_congr
          intro w
          rw [Real.enorm_eq_ofReal_abs,
            ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    _ ≤ _ := hB

/-- The force group `p₇ + p₈` is `L^{3/2}` on the parabolic cylinder `Q_r`. -/
theorem lin34_force_integrableOn_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    IntegrableOn (fun w : ParabolicPoint =>
        |pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1| ^ (3 / 2 : ℝ))
      (parabolicCylinder z.1 z.2 r) volume := by
  have hQr : parabolicCylinder z.1 z.2 r ⊆ parabolicCylinder z.1 z.2 ρ := by
    apply parabolicCylinder_mono
    · exact hr.le
    · linarith only [hhalf, hρ]
  have h7 := (pressureP7_aestronglyMeasurable_on_cylinder hsol hρ hsub).mono_measure
    (Measure.restrict_mono_set volume hQr)
  have h8 := (pressureP8_aestronglyMeasurable_on_cylinder hsol hρ hsub).mono_measure
    (Measure.restrict_mono_set volume hQr)
  have hcont : Continuous (fun a : ℝ => |a| ^ (3 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num)).comp continuous_abs
  have hmeas : AEStronglyMeasurable (fun w : ParabolicPoint =>
      |pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1| ^ (3 / 2 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
    hcont.comp_aestronglyMeasurable (h7.add h8)
  have hbound := lin34_force_cylinder_lintegral_bound hsol hρ hr hhalf hsub
  have hfin : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (|pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1| ^ (3 / 2 : ℝ))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  exact (lintegral_ofReal_ne_top_iff_integrable hmeas
    (Filter.Eventually.of_forall (fun w => Real.rpow_nonneg (abs_nonneg _) _))).mp
    hfin

/-- The real-valued form of the force cylinder bound in the proof of
`prop:lin34`(ii-b) of `paper/ckn.tex`. -/
theorem lin34_force_cylinder_integral_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    (∫ w in parabolicCylinder z.1 z.2 r,
        |pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1| ^ (3 / 2 : ℝ)) ≤
      r ^ 2 * (lin34ForceCylinderConstant q *
        ((r / ρ) * lambda q f z ρ)) ^ (3 / 2 : ℝ) := by
  have hint := lin34_force_integrableOn_cylinder hsol hρ hr hhalf hsub
  have hbound := lin34_force_cylinder_lintegral_bound hsol hρ hr hhalf hsub
  have hnonneg : 0 ≤ᵐ[volume.restrict (parabolicCylinder z.1 z.2 r)]
      fun w : ParabolicPoint =>
        |pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1| ^ (3 / 2 : ℝ) :=
    Filter.Eventually.of_forall
      (fun w => Real.rpow_nonneg (abs_nonneg _) _)
  have heq := integral_eq_lintegral_of_nonneg_ae hnonneg
    hint.aestronglyMeasurable
  rw [heq]
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  refine hle.trans_eq ?_
  refine ENNReal.toReal_ofReal ?_
  have hlam : 0 ≤ lambda q f z ρ := by
    unfold lambda
    positivity
  have hC : 0 ≤ lin34ForceCylinderConstant q * ((r / ρ) * lambda q f z ρ) := by
    have hCq : 0 ≤ lin34ForceCylinderConstant q :=
      lin34ForceCylinderConstant_nonneg q hsol.2.2.2.1
    have hq : 0 ≤ (r / ρ) * lambda q f z ρ := by
      have : (0 : ℝ) ≤ r / ρ := by positivity
      exact mul_nonneg this hlam
    exact mul_nonneg hCq hq
  have := Real.rpow_nonneg hC (3 / 2 : ℝ)
  positivity

end CKN
