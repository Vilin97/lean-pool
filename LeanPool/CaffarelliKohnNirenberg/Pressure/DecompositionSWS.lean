/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionIdentity
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWSBasic

/-!
# Decomposition SWS

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

theorem pressureP1_distributional_identity_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω) :
    ∀ᵐ s ∂volume.restrict I,
      ∫ x, pressureP1 η u c p f s x * spatialLaplacian ψ x =
        ∫ x, ∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
          mixedSecond ψ i j x := by
  obtain ⟨Ω', hΩ'open, hηΩ', hψΩ', hΩ'compact, hΩ'Ω, hLp⟩ :=
    decomposition_slice_integrability hsol hηc hηΩ hψc hψΩ
  haveI : IsFiniteMeasure (volume.restrict Ω') := by
    apply isFiniteMeasure_restrict.mpr
    exact (lt_of_le_of_lt (measure_mono (μ := volume) subset_closure)
      hΩ'compact.measure_lt_top).ne
  have hcut := pressure_laplace_cutoff_identity_ae hsol hη hηc hηΩ (c := c) hψ hψc hψΩ
  filter_upwards [hcut, hLp] with s hcut_s hLp_s
  have hΩ'sub : Ω' ⊆ Ω := subset_closure.trans hΩ'Ω
  have huComp (i : Fin 3) : MemLp (fun x : Vec3 => u (x, s) i) 2
      (volume.restrict Ω') :=
    hLp_s.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have huInt (i : Fin 3) : Integrable (fun x : Vec3 => u (x, s) i)
      (volume.restrict Ω') := huComp i |>.integrable (by norm_num)
  have hfInt (i : Fin 3) : Integrable (fun x : Vec3 => f (x, s) i)
      (volume.restrict Ω') := by
    apply hLp_s.2.2.mono
      ((ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
        hLp_s.2.2.aestronglyMeasurable)
    filter_upwards [] with x
    change ‖f (x, s) i‖ ≤ ‖f (x, s)‖
    rw [Pi.norm_def]
    simpa only [coe_nnnorm] using
      (NNReal.coe_le_coe.mpr
        (Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
          (f := fun b => ‖f (x, s) b‖₊) (Finset.mem_univ i)))
  have hpScalar {g : Vec3 → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
      (hgΩ : tsupport g ⊆ Ω') : IntegrableOn
      (fun x => p (x, s) * g x) Ω volume := by
    obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
    have h' := hLp_s.2.1.mul_bdd hg.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
    have h'int : Integrable (fun x => p (x, s) * g x) (volume.restrict Ω') :=
      ⟨h'.1, h'.2⟩
    have h'On : IntegrableOn (fun x => p (x, s) * g x) Ω' volume := h'int
    exact (h'On.integrable_of_forall_notMem_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (f := g) (fun hxt => hx (hgΩ hxt)), mul_zero])).integrableOn
  have huScalar {i : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') : IntegrableOn
      (fun x => u (x, s) i * g x) Ω volume := by
    obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
    have h' := (huInt i).mul_bdd hg.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
    have h'int : Integrable (fun x => u (x, s) i * g x) (volume.restrict Ω') :=
      ⟨h'.1, h'.2⟩
    have h'On : IntegrableOn (fun x => u (x, s) i * g x) Ω' volume := h'int
    exact (h'On.integrable_of_forall_notMem_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (f := g) (fun hxt => hx (hgΩ hxt)), mul_zero])).integrableOn
  have huuScalar {i j : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') : IntegrableOn
      (fun x => u (x, s) i * u (x, s) j * g x) Ω volume := by
    obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
    have h' := ((huComp i).integrable_mul (huComp j)).mul_bdd
      hg.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
    have h'int : Integrable (fun x => u (x, s) i * u (x, s) j * g x)
        (volume.restrict Ω') := ⟨h'.1, h'.2⟩
    have h'On : IntegrableOn (fun x => u (x, s) i * u (x, s) j * g x)
        Ω' volume := h'int
    exact (h'On.integrable_of_forall_notMem_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (f := g) (fun hxt => hx (hgΩ hxt)), mul_zero])).integrableOn
  have hfScalar {i : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') : IntegrableOn
      (fun x => f (x, s) i * g x) Ω volume := by
    obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
    have h' := (hfInt i).mul_bdd hg.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
    have h'int : Integrable (fun x => f (x, s) i * g x) (volume.restrict Ω') :=
      ⟨h'.1, h'.2⟩
    have h'On : IntegrableOn (fun x => f (x, s) i * g x) Ω' volume := h'int
    exact (h'On.integrable_of_forall_notMem_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (f := g) (fun hxt => hx (hgΩ hxt)), mul_zero])).integrableOn
  have hUScalar {i j : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') : IntegrableOn
      (fun x => pressureUTensor u c (x, s) i j * g x) Ω volume := by
    have hu := huuScalar (i := i) (j := j) hg hgc hgΩ
    have huc := huScalar (i := i) hg hgc hgΩ
    have hs : IntegrableOn (fun x => -(u (x, s) i * u (x, s) j * g x) +
        c s j * (u (x, s) i * g x)) Ω volume := hu.neg.add (huc.const_mul (c s j))
    exact hs.congr (Filter.Eventually.of_forall fun x => by
      simp only [pressureUTensor]
      ring)
  have hfinite {g : Fin 3 → Vec3 → ℝ} (hg : ∀ i, IntegrableOn (g i) Ω volume) :
      IntegrableOn (fun x => ∑ i, g i x) Ω volume := by
    change Integrable (∑ i, (fun x => g i x)) (volume.restrict Ω)
    exact integrable_finsetSum' (Finset.univ : Finset (Fin 3)) (fun i _ => hg i)
  have hηd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i) :=
    contDiff_spatialDeriv_smooth hη i
  have hψd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ i) :=
    contDiff_spatialDeriv_smooth hψ i
  have hηm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j) :=
    contDiff_mixedSecond_smooth hη i j
  have hψm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j) :=
    contDiff_mixedSecond_smooth hψ i j
  have hηdc (i : Fin 3) : HasCompactSupport (spatialDeriv η i) :=
    (hηc.fderiv_apply (𝕜 := ℝ) (basisVec i))
  have hψdc (i : Fin 3) : HasCompactSupport (spatialDeriv ψ i) :=
    (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i))
  have hηmc (i j : Fin 3) : HasCompactSupport (mixedSecond η i j) := by
    exact (hηdc j).fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hηmΩ (i j : Fin 3) : tsupport (mixedSecond η i j) ⊆ Ω' := by
    exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')
  have hηLapΩ : tsupport (spatialLaplacian η) ⊆ Ω' := by
    change tsupport (fun x => ∑ i : Fin 3,
      spatialDeriv (spatialDeriv η i) i x) ⊆ Ω'
    apply decomposition_ts_support_sum₃_sws
    intro i
    exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ')
  have hψLapc : HasCompactSupport (spatialLaplacian ψ) :=
    decomposition_laplacian_hasCompactSupport_sws hψc
  have hηLapc : HasCompactSupport (spatialLaplacian η) :=
    decomposition_laplacian_hasCompactSupport_sws hηc
  have hsuppMul {a b : Vec3 → ℝ} (ha : HasCompactSupport a)
      (hb : HasCompactSupport b) (haΩ : tsupport a ⊆ Ω') :
      HasCompactSupport (fun x => a x * b x) ∧
        tsupport (fun x => a x * b x) ⊆ Ω' := by
    refine ⟨ha.mul_right (f' := b), (tsupport_mul_subset_left (f := a) (g := b)).trans haΩ⟩
  have hAon : IntegrableOn (fun x => η x * p (x, s) * spatialLaplacian ψ x) Ω volume := by
    convert hpScalar (hη.mul (contDiff_spatialLaplacian_smooth hψ)).continuous
      (hηc.mul_right (f' := spatialLaplacian ψ))
      ((tsupport_mul_subset_left (f := η) (g := spatialLaplacian ψ)).trans hηΩ') using 1
    funext x
    ring
  have hAΩ : tsupport (fun x => η x * p (x, s) * spatialLaplacian ψ x) ⊆ Ω := by
    rw [show (fun x => η x * p (x, s) * spatialLaplacian ψ x) =
      (fun x => η x * (p (x, s) * spatialLaplacian ψ x)) by funext x; ring]
    exact (tsupport_mul_subset_left (f := η) (g := fun x =>
      p (x, s) * spatialLaplacian ψ x)).trans hηΩ
  have hA : Integrable (fun x => η x * p (x, s) * spatialLaplacian ψ x) volume :=
    decomposition_full_of_on_sws hAon hAΩ
  have hB : Integrable (fun x => ∑ i, ∑ j,
      η x * pressureUTensor u c (x, s) i j * mixedSecond ψ i j x) volume := by
    have hBij (i j : Fin 3) : IntegrableOn
        (fun x => η x * pressureUTensor u c (x, s) i j * mixedSecond ψ i j x) Ω volume := by
      convert hUScalar (i := i) (j := j) (hη.mul (hψm i j)).continuous
        (hηc.mul_right (f' := mixedSecond ψ i j))
        ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηΩ') using 1
      funext x
      ring
    have hBΩ : tsupport (fun x => ∑ i, ∑ j,
        η x * pressureUTensor u c (x, s) i j * mixedSecond ψ i j x) ⊆ Ω := by
      apply decomposition_ts_support_sum₂_sws
      intro i j
      rw [show (fun x => η x * pressureUTensor u c (x, s) i j * mixedSecond ψ i j x) =
        (fun x => η x * (pressureUTensor u c (x, s) i j * mixedSecond ψ i j x)) by
          funext x; ring]
      exact ((tsupport_mul_subset_left (f := η) (g :=
        fun x => pressureUTensor u c (x, s) i j * mixedSecond ψ i j x)).trans hηΩ').trans hΩ'sub
    exact decomposition_full_of_on_sws (hfinite fun i => hfinite fun j => hBij i j) hBΩ
  have hSource (g : Vec3 → ℝ) (hg : IntegrableOn g Ω volume)
      (hgΩ : tsupport g ⊆ Ω) :
      Integrable g volume := decomposition_full_of_on_sws hg
        hgΩ
  have hU0 (i j : Fin 3) : Integrable
      (fun x => pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) volume :=
    by
      have hU0Ω : tsupport (fun x => pressureUTensor u c (x, s) i j *
        (η x * mixedSecond ψ i j x)) ⊆ Ω := by
        exact ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
          (g := fun x => η x * mixedSecond ψ i j x)).trans
          ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηΩ')).trans hΩ'sub
      exact hSource _ (hUScalar (i := i) (j := j) (hη.mul (hψm i j)).continuous
        (hηc.mul_right (f' := mixedSecond ψ i j))
        ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηΩ')) hU0Ω
  have hU1 (i j : Fin 3) : Integrable
      (fun x => pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) volume :=
    by
      have hU1Ω : tsupport (fun x => pressureUTensor u c (x, s) i j *
          (mixedSecond η i j x * ψ x)) ⊆ Ω := by
        exact ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
          (g := fun x => mixedSecond η i j x * ψ x)).trans
          ((tsupport_mul_subset_right (f := mixedSecond η i j) (g := ψ)).trans hψΩ')).trans hΩ'sub
      exact hSource _ (hUScalar (i := i) (j := j) ((hηm i j).mul hψ).continuous
        (hψc.mul_left (f := mixedSecond η i j))
        ((tsupport_mul_subset_right (f := mixedSecond η i j) (g := ψ)).trans hψΩ')) hU1Ω
  have hU2 (i j : Fin 3) : Integrable
      (fun x => pressureUTensor u c (x, s) i j * (spatialDeriv η i x * spatialDeriv ψ j x)) volume :=
    hSource _ (hUScalar (i := i) (j := j) ((hηd i).mul (hψd j)).continuous
      ((hηdc i).mul_right (f' := spatialDeriv ψ j))
      ((tsupport_mul_subset_left (f := spatialDeriv η i) (g := spatialDeriv ψ j)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ')))
      ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
        (g := fun x => spatialDeriv η i x * spatialDeriv ψ j x)).trans
        ((tsupport_mul_subset_left (f := spatialDeriv η i) (g := spatialDeriv ψ j)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ)))
  have hU3 (i j : Fin 3) : Integrable
      (fun x => pressureUTensor u c (x, s) i j * (spatialDeriv η j x * spatialDeriv ψ i x)) volume := by
    exact hSource _ (hUScalar (i := i) (j := j) ((hηd j).mul (hψd i)).continuous
      ((hηdc j).mul_right (f' := spatialDeriv ψ i))
      ((tsupport_mul_subset_left (f := spatialDeriv η j) (g := spatialDeriv ψ i)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')))
      ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
        (g := fun x => spatialDeriv η j x * spatialDeriv ψ i x)).trans
        ((tsupport_mul_subset_left (f := spatialDeriv η j) (g := spatialDeriv ψ i)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ)))
  have hC5 : Integrable (fun x => p (x, s) * (ψ x * spatialLaplacian η x)) volume := by
    have hψLapηc : HasCompactSupport (spatialLaplacian η) :=
      decomposition_laplacian_hasCompactSupport_sws hηc
    exact decomposition_full_of_on_sws
      (hpScalar (hψ.mul (contDiff_spatialLaplacian_smooth hη)).continuous
        (hψc.mul_right (f' := spatialLaplacian η))
        ((tsupport_mul_subset_left (f := ψ) (g := spatialLaplacian η)).trans hψΩ'))
      ((tsupport_mul_subset_right (f := fun x => p (x, s))
        (g := fun x => ψ x * spatialLaplacian η x)).trans
        ((tsupport_mul_subset_left (f := ψ) (g := spatialLaplacian η)).trans hψΩ))
  have hC6 : Integrable (fun x => spatialGradDot η ψ x * p (x, s)) volume := by
    have hsum : Integrable (fun x => ∑ j, p (x, s) *
        (spatialDeriv η j x * spatialDeriv ψ j x)) volume := by
      exact decomposition_full_of_on_sws (hfinite fun j =>
        hpScalar ((hηd j).mul (hψd j)).continuous
          ((hηdc j).mul_right (f' := spatialDeriv ψ j))
          ((tsupport_mul_subset_left (f := spatialDeriv η j) (g := spatialDeriv ψ j)).trans
            ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')))
        (by
          apply decomposition_ts_support_sum₃_sws
          intro j
          exact (tsupport_mul_subset_right (f := fun x => p (x, s))
            (g := fun x => spatialDeriv η j x * spatialDeriv ψ j x)).trans
            ((tsupport_mul_subset_left (f := spatialDeriv η j)
              (g := spatialDeriv ψ j)).trans
              ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ)))
    exact hsum.congr (Filter.Eventually.of_forall fun x => by
      simp only [spatialGradDot]
      calc
        _ = p (x, s) * ∑ j, spatialDeriv η j x * spatialDeriv ψ j x := by
          rw [Finset.mul_sum]
        _ = _ := by ring)
  have hF7 : Integrable (fun x => ∑ i, f (x, s) i *
      (η x * spatialDeriv ψ i x)) volume := by
    exact decomposition_full_of_on_sws (hfinite fun i =>
      hfScalar ((hη.mul (hψd i)).continuous)
        (hηc.mul_right (f' := spatialDeriv ψ i))
        ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ i)).trans hηΩ'))
      (by
        apply decomposition_ts_support_sum₃_sws
        intro i
        exact (tsupport_mul_subset_right (f := fun x => f (x, s) i)
          (g := fun x => η x * spatialDeriv ψ i x)).trans
          ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ i)).trans hηΩ))
  have hF8 : Integrable (fun x => ∑ i, f (x, s) i *
      (ψ x * spatialDeriv η i x)) volume := by
    exact decomposition_full_of_on_sws (hfinite fun i =>
      hfScalar ((hψ.mul (hηd i)).continuous)
        (hψc.mul_right (f' := spatialDeriv η i))
        ((tsupport_mul_subset_left (f := ψ) (g := spatialDeriv η i)).trans hψΩ'))
      (by
        apply decomposition_ts_support_sum₃_sws
        intro i
        exact (tsupport_mul_subset_right (f := fun x => f (x, s) i)
          (g := fun x => ψ x * spatialDeriv η i x)).trans
          ((tsupport_mul_subset_left (f := ψ) (g := spatialDeriv η i)).trans hψΩ))
  let A : Vec3 → ℝ := fun x => η x * p (x, s) * spatialLaplacian ψ x
  let B : Vec3 → ℝ := fun x => ∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j * mixedSecond ψ i j x
  let Q : Vec3 → ℝ := fun x => (pressureP2 η u c s x + pressureP3 η u c s x +
    pressureP4 η u c s x + pressureP5 η p s x + pressureP6 η p s x +
    pressureP7 η f s x + pressureP8 η f s x) * spatialLaplacian ψ x
  have hηLapΩ : tsupport (spatialLaplacian η) ⊆ Ω' := by
    change tsupport (fun x => ∑ i : Fin 3,
      spatialDeriv (spatialDeriv η i) i x) ⊆ Ω'
    apply decomposition_ts_support_sum₃_sws
    intro i
    exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ')
  have hP2term (i j : Fin 3) : Integrable
      (fun x => pressureNewtonianPotential
        (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x *
          spatialLaplacian ψ x) volume := by
    have hon := hUScalar (i := i) (j := j) (hηm i j).continuous
      (hηmc i j) (hηmΩ i j)
    have hon' : IntegrableOn
        (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) Ω volume :=
      hon.congr (Filter.Eventually.of_forall fun y => by ring)
    have hs := hSource _ hon'
      ((tsupport_mul_subset_left (f := mixedSecond η i j)
        (g := fun y => pressureUTensor u c (y, s) i j)).trans
        ((hηmΩ i j).trans hΩ'sub))
    exact pressureNewtonianPotential_mul_smooth_integrable hs
      ((hηmc i j).mul_right (f' := fun y => pressureUTensor u c (y, s) i j))
      (contDiff_spatialLaplacian_smooth hψ) hψLapc
  have hP2 : Integrable
      (fun x => pressureP2 η u c s x * spatialLaplacian ψ x) volume := by
    have hs := integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hP2term i j))
    simpa only [pressureP2, Finset.sum_mul] using hs
  have hP3term (i j : Fin 3) : Integrable
      (fun x => pressureNewtonianDerivativePotential j
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x *
          spatialLaplacian ψ x) volume :=
    pressureNewtonianDerivativePotential_mul_smooth_integrable
      (hSource _ (hUScalar (i := i) (j := j) (hηd i).continuous (hηdc i)
        ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ'))
        (((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
          (g := spatialDeriv η i)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ')).trans hΩ'sub))
      ((hηdc i).mul_left (f := fun y => pressureUTensor u c (y, s) i j))
        (contDiff_spatialLaplacian_smooth hψ) hψLapc
  have hP3 : Integrable
      (fun x => pressureP3 η u c s x * spatialLaplacian ψ x) volume := by
    have hs := integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hP3term i j))
    simpa only [pressureP3, Finset.sum_mul] using hs
  have hP4term (i j : Fin 3) : Integrable
      (fun x => pressureNewtonianDerivativePotential i
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x *
          spatialLaplacian ψ x) volume :=
    pressureNewtonianDerivativePotential_mul_smooth_integrable
      (hSource _ (hUScalar (i := i) (j := j) (hηd j).continuous (hηdc j)
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ'))
        (((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
          (g := spatialDeriv η j)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')).trans hΩ'sub))
      ((hηdc j).mul_left (f := fun y => pressureUTensor u c (y, s) i j))
        (contDiff_spatialLaplacian_smooth hψ) hψLapc
  have hP4 : Integrable
      (fun x => pressureP4 η u c s x * spatialLaplacian ψ x) volume := by
    have hs := integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hP4term i j))
    simpa only [pressureP4, Finset.sum_mul] using hs
  have hP5 : Integrable (fun x => pressureP5 η p s x * spatialLaplacian ψ x) volume := by
    change Integrable (fun x => -pressureNewtonianPotential
      (fun y => p (y, s) * spatialLaplacian η y) x * spatialLaplacian ψ x) volume
    have hon := hpScalar (contDiff_spatialLaplacian_smooth hη).continuous
      hηLapc hηLapΩ
    convert (pressureNewtonianPotential_mul_smooth_integrable
      (hSource _ hon (((tsupport_mul_subset_right (f := fun y => p (y, s))
        (g := spatialLaplacian η)).trans hηLapΩ).trans hΩ'sub))
      ((hηLapc).mul_left (f := fun y => p (y, s)))
      (contDiff_spatialLaplacian_smooth hψ) hψLapc).neg using 1
    funext x
    simp only [Pi.neg_apply]
    ring
  have hP6term (j : Fin 3) : Integrable
      (fun x => pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s)) x * spatialLaplacian ψ x) volume := by
    have hon := hpScalar (hηd j).continuous (hηdc j)
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')
    have hon' : IntegrableOn (fun y => spatialDeriv η j y * p (y, s)) Ω volume :=
      hon.congr (Filter.Eventually.of_forall fun y => by ring)
    exact pressureNewtonianDerivativePotential_mul_smooth_integrable
      (hSource _ hon' (((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := fun y => p (y, s))).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')).trans hΩ'sub))
      ((hηdc j).mul_right (f' := fun y => p (y, s)))
      (contDiff_spatialLaplacian_smooth hψ) hψLapc
  have hP6 : Integrable (fun x => pressureP6 η p s x * spatialLaplacian ψ x) volume := by
    change Integrable (fun x => (-2 : ℝ) *
      (∑ j, pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s)) x) * spatialLaplacian ψ x) volume
    have hs : Integrable (fun x => ∑ j, pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s)) x * spatialLaplacian ψ x) volume :=
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hP6term j)
    convert hs.const_mul (-2) using 1
    funext x
    calc
      (-2 * ∑ j, pressureNewtonianDerivativePotential j
          (fun y => spatialDeriv η j y * p (y, s)) x) * spatialLaplacian ψ x =
          -2 * ((∑ j, pressureNewtonianDerivativePotential j
            (fun y => spatialDeriv η j y * p (y, s)) x) * spatialLaplacian ψ x) := by ring
      _ = -2 * ∑ j, pressureNewtonianDerivativePotential j
          (fun y => spatialDeriv η j y * p (y, s)) x * spatialLaplacian ψ x := by
            rw [Finset.sum_mul]
  have hP7term (j : Fin 3) : Integrable
      (fun x => pressureNewtonianDerivativePotential j
        (fun y => η y * f (y, s) j) x * spatialLaplacian ψ x) volume := by
    have hon := hfScalar (i := j) hη.continuous hηc hηΩ'
    have hon' : IntegrableOn (fun y => η y * f (y, s) j) Ω volume :=
      hon.congr (Filter.Eventually.of_forall fun y => by ring)
    exact pressureNewtonianDerivativePotential_mul_smooth_integrable
      (hSource _ hon' (((tsupport_mul_subset_left (f := η)
        (g := fun y => f (y, s) j)).trans hηΩ').trans hΩ'sub))
      (hηc.mul_right (f' := fun y => f (y, s) j))
      (contDiff_spatialLaplacian_smooth hψ) hψLapc
  have hP7 : Integrable (fun x => pressureP7 η f s x * spatialLaplacian ψ x) volume := by
    change Integrable (fun x => -(∑ j, pressureNewtonianDerivativePotential j
      (fun y => η y * f (y, s) j) x) * spatialLaplacian ψ x) volume
    have hs : Integrable (fun x => ∑ j, pressureNewtonianDerivativePotential j
        (fun y => η y * f (y, s) j) x * spatialLaplacian ψ x) volume :=
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hP7term j)
    convert hs.neg using 1
    funext x
    calc
      (-∑ j, pressureNewtonianDerivativePotential j
          (fun y => η y * f (y, s) j) x) * spatialLaplacian ψ x =
          -((∑ j, pressureNewtonianDerivativePotential j
            (fun y => η y * f (y, s) j) x) * spatialLaplacian ψ x) := by ring
      _ = -∑ j, pressureNewtonianDerivativePotential j
          (fun y => η y * f (y, s) j) x * spatialLaplacian ψ x := by
            rw [Finset.sum_mul]
  have hP8term (j : Fin 3) : Integrable
      (fun x => pressureNewtonianPotential
        (fun y => spatialDeriv η j y * f (y, s) j) x * spatialLaplacian ψ x) volume := by
    have hon := hfScalar (i := j) (hηd j).continuous (hηdc j)
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')
    have hon' : IntegrableOn (fun y => spatialDeriv η j y * f (y, s) j) Ω volume :=
      hon.congr (Filter.Eventually.of_forall fun y => by ring)
    exact pressureNewtonianPotential_mul_smooth_integrable
      (hSource _ hon' (((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := fun y => f (y, s) j)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')).trans hΩ'sub))
      ((hηdc j).mul_right (f' := fun y => f (y, s) j))
      (contDiff_spatialLaplacian_smooth hψ) hψLapc
  have hP8 : Integrable (fun x => pressureP8 η f s x * spatialLaplacian ψ x) volume := by
    change Integrable (fun x => -(∑ j, pressureNewtonianPotential
      (fun y => spatialDeriv η j y * f (y, s) j) x) * spatialLaplacian ψ x) volume
    have hs : Integrable (fun x => ∑ j, pressureNewtonianPotential
        (fun y => spatialDeriv η j y * f (y, s) j) x * spatialLaplacian ψ x) volume :=
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hP8term j)
    convert hs.neg using 1
    funext x
    calc
      (-∑ j, pressureNewtonianPotential
          (fun y => spatialDeriv η j y * f (y, s) j) x) * spatialLaplacian ψ x =
          -((∑ j, pressureNewtonianPotential
            (fun y => spatialDeriv η j y * f (y, s) j) x) * spatialLaplacian ψ x) := by ring
      _ = -∑ j, pressureNewtonianPotential
          (fun y => spatialDeriv η j y * f (y, s) j) x * spatialLaplacian ψ x := by
            rw [Finset.sum_mul]
  have hB0 : Integrable (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) volume := by
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hU0 i j))
  have hB1 : Integrable (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) volume := by
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hU1 i j))
  have hB2 : Integrable (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j *
        (spatialDeriv η i x * spatialDeriv ψ j x)) volume := by
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hU2 i j))
  have hB3 : Integrable (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j *
        (spatialDeriv η j x * spatialDeriv ψ i x)) volume := by
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hU3 i j))
  have hB0Ω : tsupport (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) ⊆ Ω := by
    apply decomposition_ts_support_sum₂_sws
    intro i j
    exact ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
      (g := fun x => η x * mixedSecond ψ i j x)).trans
      ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηΩ')).trans hΩ'sub
  have hB1Ω : tsupport (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) ⊆ Ω := by
    apply decomposition_ts_support_sum₂_sws
    intro i j
    exact ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
      (g := fun x => mixedSecond η i j x * ψ x)).trans
      ((tsupport_mul_subset_right (f := mixedSecond η i j) (g := ψ)).trans hψΩ')).trans hΩ'sub
  have hB2Ω : tsupport (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j *
        (spatialDeriv η i x * spatialDeriv ψ j x)) ⊆ Ω := by
    apply decomposition_ts_support_sum₂_sws
    intro i j
    exact ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
      (g := fun x => spatialDeriv η i x * spatialDeriv ψ j x)).trans
      ((tsupport_mul_subset_left (f := spatialDeriv η i)
        (g := spatialDeriv ψ j)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ'))).trans hΩ'sub
  have hB3Ω : tsupport (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j *
        (spatialDeriv η j x * spatialDeriv ψ i x)) ⊆ Ω := by
    apply decomposition_ts_support_sum₂_sws
    intro i j
    exact ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
      (g := fun x => spatialDeriv η j x * spatialDeriv ψ i x)).trans
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := spatialDeriv ψ i)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ'))).trans hΩ'sub
  have hC5Ω : tsupport (fun x => p (x, s) *
      (ψ x * spatialLaplacian η x)) ⊆ Ω := by
    exact (tsupport_mul_subset_right (f := fun x => p (x, s))
      (g := fun x => ψ x * spatialLaplacian η x)).trans
      ((tsupport_mul_subset_left (f := ψ) (g := spatialLaplacian η)).trans hψΩ)
  have hC6Ω : tsupport (fun x => spatialGradDot η ψ x * p (x, s)) ⊆ Ω := by
    rw [show (fun x => spatialGradDot η ψ x * p (x, s)) =
      (fun x => ∑ j, p (x, s) * (spatialDeriv η j x * spatialDeriv ψ j x)) by
        funext x
        simp only [spatialGradDot]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring]
    apply decomposition_ts_support_sum₃_sws
    intro j
    exact (((tsupport_mul_subset_right
      (f := fun x => p (x, s))
      (g := fun x => spatialDeriv η j x * spatialDeriv ψ j x)).trans
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := spatialDeriv ψ j)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ'))).trans hΩ'sub)
  have hF7Ω : tsupport (fun x => ∑ i,
      f (x, s) i * (η x * spatialDeriv ψ i x)) ⊆ Ω := by
    apply decomposition_ts_support_sum₃_sws
    intro i
    exact (tsupport_mul_subset_right (f := fun x => f (x, s) i)
      (g := fun x => η x * spatialDeriv ψ i x)).trans
      ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ i)).trans hηΩ)
  have hF8Ω : tsupport (fun x => ∑ i,
      f (x, s) i * (ψ x * spatialDeriv η i x)) ⊆ Ω := by
    apply decomposition_ts_support_sum₃_sws
    intro i
    exact (tsupport_mul_subset_right (f := fun x => f (x, s) i)
      (g := fun x => ψ x * spatialDeriv η i x)).trans
      ((tsupport_mul_subset_left (f := ψ) (g := spatialDeriv η i)).trans hψΩ)
  have hQ : Integrable (fun x => (pressureP2 η u c s x + pressureP3 η u c s x +
      pressureP4 η u c s x + pressureP5 η p s x + pressureP6 η p s x +
      pressureP7 η f s x + pressureP8 η f s x) * spatialLaplacian ψ x) volume := by
    have hs := hP2.add (hP3.add (hP4.add (hP5.add (hP6.add (hP7.add hP8)))))
    convert hs using 1
    funext x
    simp only [Pi.add_apply]
    ring
  have integral_sum₁ {G : Fin 3 → Vec3 → ℝ}
      (hG : ∀ j, Integrable (G j) volume) :
      ∫ x, ∑ j, G j x = ∑ j, ∫ x, G j x := by
    rw [integral_finsetSum (s := Finset.univ)]
    intro j hj
    exact hG j
  have integral_sum₂ {G : Fin 3 → Fin 3 → Vec3 → ℝ}
      (hG : ∀ i j, Integrable (G i j) volume) :
      ∫ x, ∑ i, ∑ j, G i j x = ∑ i, ∑ j, ∫ x, G i j x := by
    rw [integral_finsetSum (s := Finset.univ)]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum (s := Finset.univ)]
      intro j hj
      exact hG i j
    · intro i hi
      exact integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j hj => hG i j)
  have hP2Int (i j : Fin 3) : Integrable
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) volume := by
    have hon := hUScalar (i := i) (j := j) (hηm i j).continuous
      (hηmc i j) (hηmΩ i j)
    exact hSource _ (hon.congr (Filter.Eventually.of_forall fun y => by ring))
      (((tsupport_mul_subset_left (f := mixedSecond η i j)
        (g := fun y => pressureUTensor u c (y, s) i j)).trans (hηmΩ i j)).trans hΩ'sub)
  have hP2Supp (i j : Fin 3) : HasCompactSupport
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) :=
    (hηmc i j).mul_right (f' := fun y => pressureUTensor u c (y, s) i j)
  have hP3Int (i j : Fin 3) : Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) volume := by
    exact hSource _ (hUScalar (i := i) (j := j) (hηd i).continuous (hηdc i)
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ'))
      (((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
        (g := spatialDeriv η i)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ')).trans hΩ'sub)
  have hP3Supp (i j : Fin 3) : HasCompactSupport
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) :=
    (hηdc i).mul_left (f := fun y => pressureUTensor u c (y, s) i j)
  have hP4Int (i j : Fin 3) : Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) volume := by
    exact hSource _ (hUScalar (i := i) (j := j) (hηd j).continuous (hηdc j)
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ'))
      (((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
        (g := spatialDeriv η j)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')).trans hΩ'sub)
  have hP4Supp (i j : Fin 3) : HasCompactSupport
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) :=
    (hηdc j).mul_left (f := fun y => pressureUTensor u c (y, s) i j)
  have hP5Int : Integrable
      (fun y => p (y, s) * spatialLaplacian η y) volume := by
    exact hSource _ (hpScalar (contDiff_spatialLaplacian_smooth hη).continuous
      hηLapc hηLapΩ)
      (((tsupport_mul_subset_right (f := fun y => p (y, s))
        (g := spatialLaplacian η)).trans hηLapΩ).trans hΩ'sub)
  have hP5Supp : HasCompactSupport
      (fun y => p (y, s) * spatialLaplacian η y) :=
    hηLapc.mul_left (f := fun y => p (y, s))
  have hP6Int (j : Fin 3) : Integrable
      (fun y => spatialDeriv η j y * p (y, s)) volume := by
    have hon := hpScalar (hηd j).continuous (hηdc j)
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')
    exact hSource _ (hon.congr (Filter.Eventually.of_forall fun y => by ring))
      (((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := fun y => p (y, s))).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')).trans hΩ'sub)
  have hP6Supp (j : Fin 3) : HasCompactSupport
      (fun y => spatialDeriv η j y * p (y, s)) :=
    (hηdc j).mul_right (f' := fun y => p (y, s))
  have hP7Int (j : Fin 3) : Integrable
      (fun y => η y * f (y, s) j) volume := by
    have hon := hfScalar (i := j) hη.continuous hηc hηΩ'
    exact hSource _ (hon.congr (Filter.Eventually.of_forall fun y => by ring))
      (((tsupport_mul_subset_left (f := η) (g := fun y => f (y, s) j)).trans
        hηΩ').trans hΩ'sub)
  have hP7Supp (j : Fin 3) : HasCompactSupport
      (fun y => η y * f (y, s) j) :=
    hηc.mul_right (f' := fun y => f (y, s) j)
  have hP8Int (j : Fin 3) : Integrable
      (fun y => spatialDeriv η j y * f (y, s) j) volume := by
    have hon := hfScalar (i := j) (hηd j).continuous (hηdc j)
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')
    exact hSource _ (hon.congr (Filter.Eventually.of_forall fun y => by ring))
      (((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := fun y => f (y, s) j)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')).trans hΩ'sub)
  have hP8Supp (j : Fin 3) : HasCompactSupport
      (fun y => spatialDeriv η j y * f (y, s) j) :=
    (hηdc j).mul_right (f' := fun y => f (y, s) j)
  have hC6Int (j : Fin 3) : Integrable
      (fun y => p (y, s) * (spatialDeriv η j y * spatialDeriv ψ j y)) volume := by
    have hon := hpScalar ((hηd j).mul (hψd j)).continuous
      ((hηdc j).mul_right (f' := spatialDeriv ψ j))
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := spatialDeriv ψ j)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ'))
    exact hSource _ hon
      ((((tsupport_mul_subset_right (f := fun y => p (y, s))
        (g := fun y => spatialDeriv η j y * spatialDeriv ψ j y)).trans
        ((tsupport_mul_subset_left (f := spatialDeriv η j)
          (g := spatialDeriv ψ j)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ'))).trans hΩ'sub))
  have hF7PairInt (j : Fin 3) : Integrable
      (fun y => f (y, s) j * (η y * spatialDeriv ψ j y)) volume := by
    exact hSource _ (hfScalar (i := j) (hη.mul (hψd j)).continuous
      (hηc.mul_right (f' := spatialDeriv ψ j))
      ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ j)).trans hηΩ'))
      ((((tsupport_mul_subset_right (f := fun y => f (y, s) j)
        (g := fun y => η y * spatialDeriv ψ j y)).trans
        ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ j)).trans hηΩ')).trans
        hΩ'sub))
  have hF8PairInt (j : Fin 3) : Integrable
      (fun y => f (y, s) j * (ψ y * spatialDeriv η j y)) volume := by
    exact hSource _ (hfScalar (i := j) (hψ.mul (hηd j)).continuous
      (hψc.mul_right (f' := spatialDeriv η j))
      ((tsupport_mul_subset_left (f := ψ) (g := spatialDeriv η j)).trans hψΩ'))
      ((((tsupport_mul_subset_right (f := fun y => f (y, s) j)
        (g := fun y => ψ y * spatialDeriv η j y)).trans
        ((tsupport_mul_subset_left (f := ψ) (g := spatialDeriv η j)).trans hψΩ')).trans
        hΩ'sub))
  have hPair2 : ∫ x, pressureP2 η u c s x * spatialLaplacian ψ x =
      ∫ x, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
        (mixedSecond η i j x * ψ x) := by
    calc
      _ = ∑ i, ∑ j, ∫ y, mixedSecond η i j y *
          pressureUTensor u c (y, s) i j * ψ y :=
        pressureP2_distributional_pairing hP2Int hP2Supp hψ hψc
      _ = ∑ i, ∑ j, ∫ y, pressureUTensor u c (y, s) i j *
          (mixedSecond η i j y * ψ y) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = _ := (integral_sum₂ (fun i j => hU1 i j)).symm
  have hPair3 : ∫ x, pressureP3 η u c s x * spatialLaplacian ψ x =
      ∫ x, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
        (spatialDeriv η i x * spatialDeriv ψ j x) := by
    calc
      _ = ∑ i, ∑ j, ∫ y, pressureUTensor u c (y, s) i j *
          spatialDeriv η i y * CKN.spatialDeriv ψ j y :=
        pressureP3_distributional_pairing hP3Int hP3Supp hψ hψc
      _ = ∑ i, ∑ j, ∫ y, pressureUTensor u c (y, s) i j *
          (spatialDeriv η i y * spatialDeriv ψ j y) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = _ := (integral_sum₂ (fun i j => hU2 i j)).symm
  have hPair4 : ∫ x, pressureP4 η u c s x * spatialLaplacian ψ x =
      ∫ x, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
        (spatialDeriv η j x * spatialDeriv ψ i x) := by
    calc
      _ = ∑ i, ∑ j, ∫ y, pressureUTensor u c (y, s) i j *
          spatialDeriv η j y * CKN.spatialDeriv ψ i y :=
        pressureP4_distributional_pairing hP4Int hP4Supp hψ hψc
      _ = ∑ i, ∑ j, ∫ y, pressureUTensor u c (y, s) i j *
          (spatialDeriv η j y * spatialDeriv ψ i y) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = _ := (integral_sum₂ (fun i j => hU3 i j)).symm
  have hPair5 : ∫ x, pressureP5 η p s x * spatialLaplacian ψ x =
      -∫ x, p (x, s) * (ψ x * spatialLaplacian η x) := by
    calc
      _ = -∫ y, p (y, s) * spatialLaplacian η y * ψ y :=
        pressureP5_distributional_pairing hP5Int hP5Supp hψ hψc
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with y
        ring
  have hPair6 : ∫ x, pressureP6 η p s x * spatialLaplacian ψ x =
      -2 * ∫ x, spatialGradDot η ψ x * p (x, s) := by
    calc
      _ = -2 * ∑ j, ∫ y, spatialDeriv η j y * p (y, s) *
          CKN.spatialDeriv ψ j y :=
        pressureP6_distributional_pairing hP6Int hP6Supp hψ hψc
      _ = -2 * ∫ y, ∑ j, p (y, s) *
          (spatialDeriv η j y * spatialDeriv ψ j y) := by
        congr 1
        rw [integral_sum₁ (G := fun j y =>
          p (y, s) * (spatialDeriv η j y * spatialDeriv ψ j y))
          (fun j => hC6Int j)]
        apply Finset.sum_congr rfl
        intro j hj
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with y
        simp only [spatialGradDot]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hPair7 : ∫ x, pressureP7 η f s x * spatialLaplacian ψ x =
      -∫ x, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x) := by
    calc
      _ = -∑ j, ∫ y, η y * f (y, s) j * CKN.spatialDeriv ψ j y :=
        pressureP7_distributional_pairing hP7Int hP7Supp hψ hψc
      _ = -∫ y, ∑ j, f (y, s) j * (η y * spatialDeriv ψ j y) := by
        rw [integral_sum₁ (G := fun j y =>
          f (y, s) j * (η y * spatialDeriv ψ j y))
          (fun j => hF7PairInt j)]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        apply integral_congr_ae
        filter_upwards [] with y
        ring
  have hPair8 : ∫ x, pressureP8 η f s x * spatialLaplacian ψ x =
      -∫ x, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x) := by
    calc
      _ = -∑ j, ∫ y, spatialDeriv η j y * f (y, s) j * ψ y :=
        pressureP8_distributional_pairing hP8Int hP8Supp hψ hψc
      _ = -∫ y, ∑ j, f (y, s) j * (ψ y * spatialDeriv η j y) := by
        rw [integral_sum₁ (G := fun j y =>
          f (y, s) j * (ψ y * spatialDeriv η j y))
          (fun j => hF8PairInt j)]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        apply integral_congr_ae
        filter_upwards [] with y
        ring
  have hs : PressureP1DistributionalData (Ω := Ω) (u := u) (c := c) (p := p)
      (f := f) (η := η) (ψ := ψ) s := {
    hcut := by
      simpa only [A, B] using hcut_s
    hA := hA
    hAΩ := hAΩ
    hB0 := hB0
    hB0Ω := hB0Ω
    hB1 := hB1
    hB1Ω := hB1Ω
    hB2 := hB2
    hB2Ω := hB2Ω
    hB3 := hB3
    hB3Ω := hB3Ω
    hC5 := hC5
    hC5Ω := hC5Ω
    hC6 := hC6
    hC6Ω := hC6Ω
    hF7 := hF7
    hF7Ω := hF7Ω
    hF8 := hF8
    hF8Ω := hF8Ω
    hQ := hQ
    hP2 := hP2
    hP3 := hP3
    hP4 := hP4
    hP5 := hP5
    hP6 := hP6
    hP7 := hP7
    hP8 := hP8
    hPair2 := hPair2
    hPair3 := hPair3
    hPair4 := hPair4
    hPair5 := hPair5
    hPair6 := hPair6
    hPair7 := hPair7
    hPair8 := hPair8 }
  exact pressureP1_distributional_identity_of_cutoff
    hs.hcut hs.hA hs.hAΩ hs.hB0 hs.hB0Ω hs.hB1 hs.hB1Ω hs.hB2 hs.hB2Ω
    hs.hB3 hs.hB3Ω hs.hC5 hs.hC5Ω hs.hC6 hs.hC6Ω hs.hF7 hs.hF7Ω hs.hF8 hs.hF8Ω
    hs.hQ hs.hP2 hs.hP3 hs.hP4 hs.hP5 hs.hP6 hs.hP7 hs.hP8 hs.hPair2 hs.hPair3
    hs.hPair4 hs.hPair5 hs.hPair6 hs.hPair7 hs.hPair8

end CKN
