/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.IntegralBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Convolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Smooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Newtonian
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Backward Potential

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology Convolution

open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-! The backward heat potential used to test a causal weak equation. -/

/-- Product of spatial volume and time volume for backward heat integration. -/
@[expose]
def backwardProductVolume : Measure (Vec3 × ℝ) :=
  (volume : Measure Vec3).prod (volume : Measure ℝ)

/-- Reflected causal heat kernel used in the backward test-function convolution. -/
@[expose]
def backwardTestKernel (p : Vec3 × ℝ) : ℝ :=
  heatKernelPlus (show ParabolicPoint from -p)

/-- Backward heat potential of a test function, written as a product-space convolution. -/
@[expose]
def backwardTestPotential (ζ : Vec3 × ℝ → ℝ) (v : Vec3 × ℝ) : ℝ :=
  MeasureTheory.convolution backwardTestKernel ζ
    (ContinuousLinearMap.lsmul ℝ ℝ) backwardProductVolume v

lemma heatKernelPlus_locallyIntegrable_prod :
    LocallyIntegrable (fun p : Vec3 × ℝ =>
      heatKernelPlus (show ParabolicPoint from p)) backwardProductVolume := by
  intro p
  let T : ℝ := max 1 (p.2 + 1)
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hstrip := heatKernelPlus_integrableOn_time (T := T)
  have hstrip' : IntegrableOn (fun q : Vec3 × ℝ =>
      heatKernelPlus (show ParabolicPoint from q))
      ((Set.univ : Set Vec3) ×ˢ Ioc 0 T) backwardProductVolume := by
    exact hstrip
  have hneg : IntegrableOn (fun q : Vec3 × ℝ =>
      heatKernelPlus (show ParabolicPoint from q))
      ((Set.univ : Set Vec3) ×ˢ Iic 0) backwardProductVolume := by
    apply (integrableOn_zero
      (s := (Set.univ : Set Vec3) ×ˢ Iic 0)).congr_fun
    · intro q hq
      exact (heatKernelPlus_eq_zero_of_nonpos hq.2).symm
    · exact MeasurableSet.prod MeasurableSet.univ measurableSet_Iic
  have hU : IntegrableOn (fun q : Vec3 × ℝ =>
      heatKernelPlus (show ParabolicPoint from q))
      ((Set.univ : Set Vec3) ×ˢ Iio T) backwardProductVolume := by
    have hunion := hneg.union hstrip'
    apply hunion.mono_set
    intro q hq
    rcases hq with ⟨_, hqt⟩
    by_cases hq0 : q.2 ≤ 0
    · exact Or.inl ⟨Set.mem_univ _, hq0⟩
    · exact Or.inr ⟨Set.mem_univ _, lt_of_not_ge hq0, hqt.le⟩
  refine ⟨(Set.univ : Set Vec3) ×ˢ Iio T, ?_, hU⟩
  apply isOpen_univ.prod isOpen_Iio |>.mem_nhds
  exact ⟨Set.mem_univ _, (lt_add_one p.2).trans_le (le_max_right _ _)⟩

lemma backwardTestKernel_locallyIntegrable :
    LocallyIntegrable backwardTestKernel backwardProductVolume := by
  intro p
  rcases heatKernelPlus_locallyIntegrable_prod (-p) with ⟨s, hs, hi⟩
  let e := (Homeomorph.neg Vec3).prodCongr (Homeomorph.neg ℝ)
  have hs' : e '' s ∈ 𝓝 p := by
    have h := e.isOpenMap.image_mem_nhds hs
    rw [show e (-p) = p by ext <;> simp [e]] at h
    exact h
  refine ⟨e '' s, hs', ?_⟩
  have hneg : MeasurePreserving (Prod.map Neg.neg Neg.neg)
      backwardProductVolume backwardProductVolume := by
    dsimp [backwardProductVolume]
    exact (Measure.measurePreserving_neg (volume : Measure Vec3)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hc := hneg.integrableOn_comp_preimage
      e.measurableEmbedding
      (f := fun q : Vec3 × ℝ => heatKernelPlus (show ParabolicPoint from q)) (s := s)
  have hc' := hc.mpr hi
  have hset : (Prod.map Neg.neg Neg.neg) ⁻¹' s = e '' s := by
    ext x
    constructor
    · intro hx
      refine ⟨-x, hx, ?_⟩
      ext <;> simp [e]
    · rintro ⟨y, hy, rfl⟩
      have he : Prod.map Neg.neg Neg.neg (e y) = y := by
        ext <;> simp [e]
      simpa [he] using hy
  rw [hset] at hc'
  have hfun : (fun q : Vec3 × ℝ =>
      heatKernelPlus (show ParabolicPoint from q)) ∘
      Prod.map Neg.neg Neg.neg = backwardTestKernel := by
    funext x
    change heatKernelPlus (show ParabolicPoint from Prod.map Neg.neg Neg.neg x) =
      heatKernelPlus (show ParabolicPoint from -x)
    rfl
  simpa only [hfun] using hc'

theorem backwardTestPotential_smooth
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v => backwardTestPotential ζ v) := by
  unfold backwardTestPotential
  exact hζc.contDiff_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) backwardTestKernel_locallyIntegrable hζ

theorem backwardTestPotential_hasFDerivAt
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (v : Vec3 × ℝ) :
    HasFDerivAt (fun w => backwardTestPotential ζ w)
      (MeasureTheory.convolution backwardTestKernel
        (fderiv ℝ ζ) ((ContinuousLinearMap.precompR (Vec3 × ℝ)
          (ContinuousLinearMap.lsmul ℝ ℝ))) backwardProductVolume v) v := by
  let _ : backwardProductVolume.IsAddLeftInvariant := by
    dsimp [backwardProductVolume]
    infer_instance
  let _ : SFinite backwardProductVolume := by
    dsimp [backwardProductVolume]
    exact Measure.prod.instSFinite
  unfold backwardTestPotential
  exact hζc.hasFDerivAt_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    backwardTestKernel_locallyIntegrable (hζ.of_le (by norm_num)) v

lemma test_slice_contDiff {ζ : Vec3 × ℝ → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => ζ (y, t)) := by
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => (y, t)) := by
    exact contDiff_id.prodMk contDiff_const
  simpa [Function.comp_def] using hζ.comp hm

lemma test_slice_hasCompactSupport {ζ : Vec3 × ℝ → ℝ}
    (hζc : HasCompactSupport ζ) (t : ℝ) :
    HasCompactSupport (fun y : Vec3 => ζ (y, t)) := by
  let K : Set Vec3 := (fun z : Vec3 × ℝ => z.1) '' tsupport ζ
  have hK : IsCompact K := hζc.isCompact.image continuous_fst
  apply HasCompactSupport.intro hK
  intro y hy
  by_contra hne
  have hmem : (y, t) ∈ tsupport ζ := by
    apply subset_tsupport
    exact hne
  exact hy ⟨(y, t), hmem, rfl⟩

theorem heatConv_time_shift_tendsto
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (x : Vec3) (t : ℝ) :
    Tendsto (fun s : ℝ =>
      heatConv s (fun y : Vec3 => ζ (y, t + s)) x)
      (𝓝[>] 0) (𝓝 (ζ (x, t))) := by
  let u₀ : Vec3 → ℝ := fun y => ζ (y, t)
  have hu₀ : ContDiff ℝ (⊤ : ℕ∞) u₀ := test_slice_contDiff hζ t
  have hu₀c : HasCompactSupport u₀ := test_slice_hasCompactSupport hζc t
  have hfixed := heatConv_tendsto_self_nhdsWithin_zero_smooth hu₀ hu₀c x
  have hunif : UniformContinuous ζ :=
    hζc.uniformContinuous_of_continuous hζ.continuous
  have hdiff_tendsto : Tendsto (fun s : ℝ =>
      heatConv s (fun y : Vec3 => ζ (y, t + s)) x - heatConv s u₀ x)
      (𝓝[>] 0) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    have hη2 : 0 < η / 2 := by positivity
    obtain ⟨δ, hδ, hδζ⟩ :=
      (Metric.uniformContinuous_iff.mp hunif) (η / 2) hη2
    have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, |s| < δ := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.mem_nhds_iff.mpr ⟨δ, hδ, by
        intro s hs
        exact hs⟩] with s hs hspos
      simpa [Metric.mem_ball, Real.dist_eq] using hs
    filter_upwards [hsmall, self_mem_nhdsWithin] with s hs hspos
    let us : Vec3 → ℝ := fun y => ζ (y, t + s)
    let ds : Vec3 → ℝ := fun y => us y - u₀ y
    have husc : HasCompactSupport us :=
      test_slice_hasCompactSupport hζc (t + s)
    have hdsc : HasCompactSupport ds := husc.sub hu₀c
    have hds : Continuous ds := by
      dsimp [ds, us, u₀]
      exact (hζ.continuous.comp
        (continuous_id.prodMk continuous_const)).sub
        (hζ.continuous.comp (continuous_id.prodMk continuous_const))
    have hcontkernel : Continuous (fun y : Vec3 => heatKernel y s) := by
      rw [show (fun y : Vec3 => heatKernel y s) = fun y : Vec3 =>
          (4 * Real.pi * s) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(vec3EuclideanNorm y) ^ 2 / (4 * s)) by
        funext y
        exact heatKernel_eq_formula hspos]
      simp only [vec3EuclideanNorm]
      fun_prop (disch := positivity)
    let usx : Vec3 → ℝ := fun y => us (x - y)
    let u₀x : Vec3 → ℝ := fun y => u₀ (x - y)
    let dsx : Vec3 → ℝ := fun y => ds (x - y)
    have husxc : HasCompactSupport usx :=
      husc.comp_homeomorph (Homeomorph.subLeft x)
    have hu₀xc : HasCompactSupport u₀x :=
      hu₀c.comp_homeomorph (Homeomorph.subLeft x)
    have hdsxc : HasCompactSupport dsx :=
      hdsc.comp_homeomorph (Homeomorph.subLeft x)
    have husx : Continuous usx := by
      dsimp [usx, us]
      fun_prop
    have hu₀x : Continuous u₀x := by
      dsimp [u₀x, u₀]
      fun_prop
    have hdsx : Continuous dsx := husx.sub hu₀x
    have hleft : Integrable (fun y : Vec3 => heatKernel y s * usx y) volume := by
      exact (hcontkernel.mul husx).integrable_of_hasCompactSupport husxc.mul_left
    have hright : Integrable (fun y : Vec3 => heatKernel y s * u₀x y) volume := by
      exact (hcontkernel.mul hu₀x).integrable_of_hasCompactSupport hu₀xc.mul_left
    have hprodx : Integrable (fun y : Vec3 => heatKernel y s * dsx y) volume := by
      exact (hcontkernel.mul hdsx).integrable_of_hasCompactSupport hdsxc.mul_left
    have hdiff_integral :
        heatConv s us x - heatConv s u₀ x =
          ∫ y : Vec3, heatKernel y s * dsx y := by
      rw [heatConv_eq_integral, heatConv_eq_integral,
        ← integral_sub hleft hright]
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp [dsx, ds, usx, us, u₀x, u₀]
      ring
    have hbound_point : ∀ y : Vec3, ‖ds y‖ ≤ η / 2 := by
      intro y
      have hdist : dist (y, t + s) (y, t) < δ := by
        simp only [Prod.dist_eq, dist_self, Real.dist_eq]
        rw [max_eq_right (abs_nonneg _)]
        have hspos' : 0 < s := hspos
        ring_nf
        rw [abs_of_pos hspos']
        exact lt_of_le_of_lt (le_abs_self s) hs
      have hval := hδζ hdist
      simpa [ds, us, u₀, Real.dist_eq, dist_eq_norm] using hval.le
    have hprod_norm : Integrable (fun y : Vec3 =>
        ‖heatKernel y s * dsx y‖) volume := hprodx.norm
    have hkernel : Integrable (fun y : Vec3 => heatKernel y s) volume :=
      heatKernel_integrable hspos
    have hmajor : Integrable (fun y : Vec3 =>
        (η / 2) * heatKernel y s) volume := hkernel.const_mul _
    have hpoint : ∀ y : Vec3,
        ‖heatKernel y s * dsx y‖ ≤ (η / 2) * heatKernel y s := by
      intro y
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg y s)]
      have hdiff' := hbound_point (x - y)
      calc
        heatKernel y s * ‖dsx y‖ ≤ heatKernel y s * (η / 2) :=
          mul_le_mul_of_nonneg_left hdiff' (heatKernel_nonneg y s)
        _ = (η / 2) * heatKernel y s := by ring
    rw [hdiff_integral]
    calc
      dist (∫ y : Vec3, heatKernel y s * dsx y) 0 =
          ‖∫ y : Vec3, heatKernel y s * dsx y‖ := by
            rw [dist_zero_right]
      _ ≤ ∫ y : Vec3, ‖heatKernel y s * dsx y‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ y : Vec3, (η / 2) * heatKernel y s :=
        integral_mono hprod_norm hmajor hpoint
      _ = η / 2 := by
        rw [integral_const_mul, heatKernel_integral s hspos]
        ring_nf
      _ < η := by linarith only [hη]
  have hsum := hdiff_tendsto.add hfixed
  simpa [u₀, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

lemma timePartial_eq_fderiv_apply
    {F : Vec3 × ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (x : Vec3) (t : ℝ) :
    CKN.timePartial (show ParabolicPoint → ℝ from F) (x, t) =
      (fderiv ℝ F (x, t)) (0, 1) := by
  let inner : ℝ → Vec3 × ℝ := fun s => (x, s)
  have hinr : ContinuousLinearMap.inr ℝ Vec3 ℝ =
      (0 : ℝ →L[ℝ] Vec3).prod (ContinuousLinearMap.id ℝ ℝ) := by
    ext s <;> rfl
  have hinner : HasFDerivAt inner (ContinuousLinearMap.inr ℝ Vec3 ℝ) t := by
    convert (hasFDerivAt_const (x := t) (c := x)).prodMk
      (hasFDerivAt_id t) using 1
    ext s <;> simp [inner]
  have houter : HasFDerivAt F (fderiv ℝ F (x, t)) (x, t) :=
    (hF.differentiable (by simp) (x, t)).hasFDerivAt
  have hc := houter.comp t hinner
  have hcf := hc.fderiv
  change (fderiv ℝ (F ∘ inner) t) 1 = _
  rw [hcf]
  rfl

lemma spatialPartial_eq_fderiv_apply
    {F : Vec3 × ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (i : Fin 3) (x : Vec3) (t : ℝ) :
    CKN.spatialPartial (show ParabolicPoint → ℝ from F) i (x, t) =
      (fderiv ℝ F (x, t)) (CKN.basisVec i, 0) := by
  let inner : Vec3 → Vec3 × ℝ := fun y => (y, t)
  have hinl : ContinuousLinearMap.inl ℝ Vec3 ℝ =
      (ContinuousLinearMap.id ℝ Vec3).prod (0 : Vec3 →L[ℝ] ℝ) := by
    ext y <;> rfl
  have hinner : HasFDerivAt inner (ContinuousLinearMap.inl ℝ Vec3 ℝ) x := by
    convert (hasFDerivAt_id x).prodMk
      (hasFDerivAt_const (x := x) (c := t)) using 1
    ext y <;> simp [inner]
  have houter : HasFDerivAt F (fderiv ℝ F (x, t)) (x, t) :=
    (hF.differentiable (by simp) (x, t)).hasFDerivAt
  have hc := houter.comp x hinner
  have hcf := hc.fderiv
  change (fderiv ℝ (F ∘ inner) x) (CKN.basisVec i) = _
  rw [hcf]
  rfl

lemma backwardTestPotential_timePartial
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (x : Vec3) (t : ℝ) :
    CKN.timePartial (show ParabolicPoint → ℝ from
      fun z => backwardTestPotential ζ z) (x, t) =
      backwardTestPotential (fun z => CKN.timePartial
        (show ParabolicPoint → ℝ from ζ) z) (x, t) := by
  have hfd := backwardTestPotential_hasFDerivAt hζ hζc (x, t)
  have htime := timePartial_eq_fderiv_apply
    (backwardTestPotential_smooth hζ hζc) x t
  calc
    CKN.timePartial (show ParabolicPoint → ℝ from
        fun z => backwardTestPotential ζ z) (x, t) =
        (fderiv ℝ (fun v => backwardTestPotential ζ v) (x, t)) (0, 1) := htime
    _ = ((MeasureTheory.convolution backwardTestKernel
        (fderiv ℝ ζ)
        ((ContinuousLinearMap.precompR (Vec3 × ℝ)
          (ContinuousLinearMap.lsmul ℝ ℝ))) backwardProductVolume (x, t))) (0, 1) := by
      rw [hfd.fderiv]
    _ = backwardTestPotential (fun z => CKN.timePartial
        (show ParabolicPoint → ℝ from ζ) z) (x, t) := by
      rw [MeasureTheory.convolution_precompR_apply
        (L := ContinuousLinearMap.lsmul ℝ ℝ) backwardTestKernel_locallyIntegrable
        (hζc.fderiv (𝕜 := ℝ)) (hζ.continuous_fderiv (by simp))]
      apply integral_congr_ae
      filter_upwards [] with p
      congr 1
      have hcoord := timePartial_eq_fderiv_apply hζ (x - p.1) (t - p.2)
      change (fderiv ℝ ζ (x - p.1, t - p.2)) (0, 1) =
        CKN.timePartial (show ParabolicPoint → ℝ from ζ) (x - p.1, t - p.2)
      exact hcoord.symm

lemma backwardTestPotential_spatialPartial
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (i : Fin 3) (x : Vec3) (t : ℝ) :
    CKN.spatialPartial (show ParabolicPoint → ℝ from
      fun z => backwardTestPotential ζ z) i (x, t) =
      backwardTestPotential (fun z => CKN.spatialPartial
        (show ParabolicPoint → ℝ from ζ) i z) (x, t) := by
  have hfd := backwardTestPotential_hasFDerivAt hζ hζc (x, t)
  have hspace := spatialPartial_eq_fderiv_apply
    (backwardTestPotential_smooth hζ hζc) i x t
  calc
    CKN.spatialPartial (show ParabolicPoint → ℝ from
        fun z => backwardTestPotential ζ z) i (x, t) =
        (fderiv ℝ (fun v => backwardTestPotential ζ v) (x, t))
          (CKN.basisVec i, 0) := hspace
    _ = ((MeasureTheory.convolution backwardTestKernel
        (fderiv ℝ ζ)
        ((ContinuousLinearMap.precompR (Vec3 × ℝ)
          (ContinuousLinearMap.lsmul ℝ ℝ))) backwardProductVolume (x, t)))
          (CKN.basisVec i, 0) := by
      rw [hfd.fderiv]
    _ = backwardTestPotential (fun z => CKN.spatialPartial
        (show ParabolicPoint → ℝ from ζ) i z) (x, t) := by
      rw [MeasureTheory.convolution_precompR_apply
        (L := ContinuousLinearMap.lsmul ℝ ℝ) backwardTestKernel_locallyIntegrable
        (hζc.fderiv (𝕜 := ℝ)) (hζ.continuous_fderiv (by simp))]
      apply integral_congr_ae
      filter_upwards [] with p
      congr 1
      have hcoord := spatialPartial_eq_fderiv_apply hζ i (x - p.1) (t - p.2)
      change (fderiv ℝ ζ (x - p.1, t - p.2)) (CKN.basisVec i, 0) =
        CKN.spatialPartial (show ParabolicPoint → ℝ from ζ) i
          (x - p.1, t - p.2)
      exact hcoord.symm

lemma backwardTestPotential_spatialSecondPartial
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (i j : Fin 3) (x : Vec3) (t : ℝ) :
    CKN.spatialSecondPartial (show ParabolicPoint → ℝ from
      fun z => backwardTestPotential ζ z) i j (x, t) =
      backwardTestPotential (fun z => CKN.spatialSecondPartial
        (show ParabolicPoint → ℝ from ζ) i j z) (x, t) := by
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
  have hfirst : ∀ z : Vec3 × ℝ,
      CKN.spatialPartial (show ParabolicPoint → ℝ from
        fun w => backwardTestPotential ζ w) i z =
        backwardTestPotential η z := by
    intro z
    exact backwardTestPotential_spatialPartial hζ hζc i z.1 z.2
  change CKN.spatialPartial (show ParabolicPoint → ℝ from
      fun w => CKN.spatialPartial (show ParabolicPoint → ℝ from
        fun v => backwardTestPotential ζ v) i w) j (x, t) = _
  have hfun : (fun w : Vec3 × ℝ => CKN.spatialPartial
      (show ParabolicPoint → ℝ from fun v => backwardTestPotential ζ v) i w) =
      (fun w => backwardTestPotential η w) := by
    funext w
    exact hfirst w
  have hsp : CKN.spatialPartial (show ParabolicPoint → ℝ from
      fun w => CKN.spatialPartial (show ParabolicPoint → ℝ from
        fun v => backwardTestPotential ζ v) i w) j (x, t) =
      CKN.spatialPartial (show ParabolicPoint → ℝ from
        fun w => backwardTestPotential η w) j (x, t) := by
    congr 1
  rw [hsp]
  exact backwardTestPotential_spatialPartial hη hηc j x t

private lemma time_derivative_integrable_on
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (x y : Vec3) (t ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun r : ℝ =>
      heatKernelTimeDerivative y r * ζ (x - y, t + r) +
        heatKernel y r * CKN.timePartial
          (show ParabolicPoint → ℝ from ζ) (x - y, t + r)) (Ioi ε) volume := by
  let Kt : Set ℝ := (fun z : Vec3 × ℝ => z.2) '' tsupport ζ
  have hKt : IsCompact Kt := hζc.isCompact.image continuous_snd
  rcases hKt.bddAbove with ⟨C, hC⟩
  let B : ℝ := C - t
  let B' : ℝ := max B ε + 1
  have hεB : ε < B' := by
    dsimp [B']
    linarith only [le_max_right B ε]
  have hB' : B < B' := by
    dsimp [B']
    linarith only [le_max_left B ε]
  let g : ℝ → ℝ := fun r =>
    heatKernelTimeDerivative y r * ζ (x - y, t + r) +
      heatKernel y r * CKN.timePartial
        (show ParabolicPoint → ℝ from ζ) (x - y, t + r)
  have htimecont : Continuous (fun z : Vec3 × ℝ =>
      CKN.timePartial (show ParabolicPoint → ℝ from ζ) z) := by
    rw [show (fun z : Vec3 × ℝ => CKN.timePartial
        (show ParabolicPoint → ℝ from ζ) z) =
        (fun z => (fderiv ℝ ζ z) (0, 1)) by
      funext z
      simpa using timePartial_eq_fderiv_apply hζ z.1 z.2]
    exact (hζ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hW : ContinuousOn (fun r : ℝ => heatKernel y r) (Ioi 0) := by
    intro r hr
    change 0 < r at hr
    let F : ℝ → ℝ := fun s => (4 * Real.pi * s) ^ (-(3 : ℝ) / 2) *
      Real.exp (-(∑ i, y i ^ 2) / (4 * s))
    have hF : ContinuousAt F r := by
      have hbase : 4 * Real.pi * r ≠ 0 := by positivity
      have hpow : ContinuousAt (fun s : ℝ =>
          (4 * Real.pi * s) ^ (-(3 : ℝ) / 2)) r := by
        exact (Real.continuousAt_rpow_const (4 * Real.pi * r)
          (-(3 : ℝ) / 2) (Or.inl hbase)).comp (by fun_prop)
      have hexp : ContinuousAt (fun s : ℝ =>
          Real.exp (-(∑ i, y i ^ 2) / (4 * s))) r := by
        apply (Real.continuous_exp.continuousAt).comp
        fun_prop (disch := positivity)
      exact hpow.mul hexp
    have hEq : (fun s : ℝ => heatKernel y s) =ᶠ[𝓝 r] F := by
      filter_upwards [eventually_gt_nhds hr] with s hs
      exact heatKernel_eq_formula_sum hs
    exact hF.congr_of_eventuallyEq hEq |>.continuousWithinAt
  have hWt : ContinuousOn (fun r : ℝ => heatKernelTimeDerivative y r) (Ioi 0) := by
    intro r hr
    change 0 < r at hr
    let F : ℝ → ℝ := fun s =>
      ((4 * Real.pi * s) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, y i ^ 2) / (4 * s))) *
        ((∑ i, y i ^ 2) / (4 * s ^ 2) - (3 : ℝ) / (2 * s))
    have hF : ContinuousAt F r := by
      have hbase : 4 * Real.pi * r ≠ 0 := by positivity
      have hpow : ContinuousAt (fun s : ℝ =>
          (4 * Real.pi * s) ^ (-(3 : ℝ) / 2)) r := by
        exact (Real.continuousAt_rpow_const (4 * Real.pi * r)
          (-(3 : ℝ) / 2) (Or.inl hbase)).comp (by fun_prop)
      have hexp : ContinuousAt (fun s : ℝ =>
          Real.exp (-(∑ i, y i ^ 2) / (4 * s))) r := by
        apply (Real.continuous_exp.continuousAt).comp
        fun_prop (disch := positivity)
      have hfrac : ContinuousAt (fun s : ℝ =>
          (∑ i, y i ^ 2) / (4 * s ^ 2) - (3 : ℝ) / (2 * s)) r := by
        fun_prop (disch := positivity)
      exact (hpow.mul hexp).mul hfrac
    have hEq : (fun s : ℝ => heatKernelTimeDerivative y s) =ᶠ[𝓝 r] F := by
      filter_upwards [eventually_gt_nhds hr] with s hs
      rw [heatKernelTimeDerivative, ite_eq_left hs,
        heatKernel_eq_formula_sum hs]
    exact hF.congr_of_eventuallyEq hEq |>.continuousWithinAt
  have hcont : ContinuousOn g (Icc ε B') := by
    have hI : Icc ε B' ⊆ Ioi 0 := by
      intro r hr
      exact lt_of_lt_of_le hε hr.1
    have hs : Continuous (fun r : ℝ => ζ (x - y, t + r)) := by
      exact hζ.continuous.comp
        (continuous_const.prodMk (continuous_const.add continuous_id))
    have hds : Continuous (fun r : ℝ =>
        CKN.timePartial (show ParabolicPoint → ℝ from ζ) (x - y, t + r)) := by
      exact htimecont.comp
        (continuous_const.prodMk (continuous_const.add continuous_id))
    dsimp [g]
    exact ((hWt.mono hI).mul hs.continuousOn).add
      ((hW.mono hI).mul hds.continuousOn)
  have hcompact : IntegrableOn g (Icc ε B') volume := by
    exact hcont.integrableOn_compact isCompact_Icc
  have hleft : IntegrableOn g (Ioo ε B') volume :=
    hcompact.mono_set Ioo_subset_Icc_self
  have htail : IntegrableOn g (Ici B') volume := by
    apply (integrableOn_zero (s := Ici B')).congr_fun
    · intro r hr
      dsimp [g]
      have hrB : B < r := lt_of_lt_of_le hB' hr
      have hz : (x - y, t + r) ∉ tsupport ζ := by
        intro hz
        have htime := hC ⟨(x - y, t + r), hz, rfl⟩
        change t + r ≤ C at htime
        dsimp [B] at hrB
        linarith only [htime, hrB]
      have hz0 : ζ (x - y, t + r) = 0 :=
        image_eq_zero_of_notMem_tsupport hz
      have hdz : CKN.timePartial (show ParabolicPoint → ℝ from ζ)
          (x - y, t + r) = 0 := by
        rw [timePartial_eq_fderiv_apply hζ (x - y) (t + r)]
        rw [fderiv_of_notMem_tsupport ℝ hz]
        simp
      rw [hz0, hdz]
      ring
    · exact measurableSet_Ici
  have hunion : Ioi ε = Ioo ε B' ∪ Ici B' := by
    ext r
    constructor
    · intro hr
      by_cases hlt : r < B'
      · exact Or.inl ⟨hr, hlt⟩
      · exact Or.inr (le_of_not_gt hlt)
    · intro hr
      rcases hr with hr | hr
      · exact hr.1
      · have hB'e : ε < B' := hεB
        exact lt_of_lt_of_le hB'e hr
  rw [hunion, integrableOn_union]
  exact ⟨hleft, htail⟩

lemma shifted_time_hasDerivAt
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (x y : Vec3) (t r : ℝ) :
    HasDerivAt (fun s : ℝ => ζ (x - y, t + s))
      (CKN.timePartial (show ParabolicPoint → ℝ from ζ) (x - y, t + r)) r := by
  let inner : ℝ → Vec3 × ℝ := fun s => (x - y, t + s)
  have hinner : HasFDerivAt inner
      (ContinuousLinearMap.inr ℝ Vec3 ℝ) r := by
    have hinr : ContinuousLinearMap.inr ℝ Vec3 ℝ =
        (0 : ℝ →L[ℝ] Vec3).prod (ContinuousLinearMap.id ℝ ℝ) := by
      ext s <;> rfl
    convert (hasFDerivAt_const (x := r) (c := x - y)).prodMk
      ((hasFDerivAt_const (x := r) (c := t)).add (hasFDerivAt_id r)) using 1
    · ext s <;> simp [inner]
    · simpa only [zero_add] using hinr
  have houter : HasFDerivAt ζ (fderiv ℝ ζ (x - y, t + r))
      (x - y, t + r) :=
    (hζ.differentiable (by simp) (x - y, t + r)).hasFDerivAt
  have hc := houter.comp r hinner
  have hcoord := timePartial_eq_fderiv_apply hζ (x - y) (t + r)
  have hs := hc.hasDerivAt
  simpa [inner, Function.comp_def, hcoord] using hs

private lemma shifted_heat_hasDerivAt
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (x y : Vec3) (t r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => heatKernel y s * ζ (x - y, t + s))
      (heatKernelTimeDerivative y r * ζ (x - y, t + r) +
        heatKernel y r * CKN.timePartial
          (show ParabolicPoint → ℝ from ζ) (x - y, t + r)) r := by
  have hW := (heatKernel_time_differentiableAt (x := y) hr).hasDerivAt
  rw [heatKernel_time_deriv hr] at hW
  have hZ := shifted_time_hasDerivAt hζ x y t r
  convert hW.mul hZ using 1

lemma shifted_time_green
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (x y : Vec3) (t ε : ℝ) (hε : 0 < ε) :
    ∫ r : ℝ in Ioi ε,
        heatKernelTimeDerivative y r * ζ (x - y, t + r) +
          heatKernel y r * CKN.timePartial
            (show ParabolicPoint → ℝ from ζ) (x - y, t + r) =
      -(heatKernel y ε * ζ (x - y, t + ε)) := by
  have hu : ∀ r ∈ Ioi ε,
      HasDerivAt (fun s : ℝ => heatKernel y s)
        (heatKernelTimeDerivative y r) r := by
    intro r hr
    have hpos : 0 < r := lt_trans hε hr
    have hderiv := (heatKernel_time_differentiableAt (x := y) hpos).hasDerivAt
    rw [heatKernel_time_deriv hpos] at hderiv
    exact hderiv
  have hv : ∀ r ∈ Ioi ε,
      HasDerivAt (fun s : ℝ => ζ (x - y, t + s))
        (CKN.timePartial (show ParabolicPoint → ℝ from ζ) (x - y, t + r)) r := by
    intro r hr
    exact shifted_time_hasDerivAt hζ x y t r
  have hprod := time_derivative_integrable_on hζ hζc x y t ε hε
  have hzero : Tendsto (fun r : ℝ => heatKernel y r *
      ζ (x - y, t + r)) (𝓝[>] ε)
      (𝓝 (heatKernel y ε * ζ (x - y, t + ε))) := by
    have hcontW := (heatKernel_time_differentiableAt (x := y) hε).continuousAt
    have hcontZ := (shifted_time_hasDerivAt hζ x y t ε).continuousAt
    exact (hcontW.mul hcontZ).continuousWithinAt.tendsto
  let Kt : Set ℝ := (fun z : Vec3 × ℝ => z.2) '' tsupport ζ
  rcases hζc.isCompact.image continuous_snd |>.bddAbove with ⟨C, hC⟩
  let B : ℝ := C - t
  let B' : ℝ := max B ε + 1
  have hB' : B < B' := by
    dsimp [B']
    linarith only [le_max_left B ε]
  have hzeroTop : Tendsto (fun r : ℝ => heatKernel y r *
      ζ (x - y, t + r)) atTop (𝓝 0) := by
    apply (tendsto_congr' ?_).2
    on_goal 1 => exact tendsto_const_nhds
    filter_upwards [eventually_gt_atTop B'] with r hr
    have hrB : B < r := lt_trans hB' hr
    have hz : (x - y, t + r) ∉ tsupport ζ := by
      intro hz
      have htime := hC ⟨(x - y, t + r), hz, rfl⟩
      change t + r ≤ C at htime
      dsimp [B] at hrB
      linarith only [htime, hrB]
    rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  simpa only [zero_sub] using
    (integral_Ioi_deriv_mul_eq_sub hu hv hprod hzero hzeroTop)

/-- Causal heat kernel pairing a later test point with an earlier source point. -/
@[expose]
def backwardHeatKernel (z v : ParabolicPoint) : ℝ :=
  heatKernelPlus (z.1 - v.1, z.2 - v.2)

/-- Spatial derivative kernel in the backward heat-potential pairing. -/
@[expose]
def backwardHeatSpatialKernel (i : Fin 3) (z v : ParabolicPoint) : ℝ :=
  heatKernelSpaceDerivative (z.1 - v.1) (z.2 - v.2) i

/-- Backward heat potential obtained by integrating against the test variable. -/
@[expose]
def backwardHeatPotential (ζ : ParabolicPoint → ℝ) (v : ParabolicPoint) : ℝ :=
  ∫ z, backwardHeatKernel z v * ζ z

/-- Spatial derivative of the backward heat potential, including the differentiation sign. -/
@[expose]
def backwardHeatPotentialSpatial (i : Fin 3) (ζ : ParabolicPoint → ℝ)
    (v : ParabolicPoint) : ℝ :=
  -(∫ z, backwardHeatSpatialKernel i z v * ζ z)

theorem backwardTestPotential_eq_backwardHeatPotential
    (ζ : Vec3 × ℝ → ℝ) (v : Vec3 × ℝ) :
    backwardTestPotential ζ v =
      backwardHeatPotential (show ParabolicPoint → ℝ from ζ)
        (show ParabolicPoint from v) := by
  let hneg0 : MeasurePreserving (Prod.map Neg.neg Neg.neg)
      backwardProductVolume backwardProductVolume := by
    dsimp [backwardProductVolume]
    exact (Measure.measurePreserving_neg (volume : Measure Vec3)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  let hneg : MeasurePreserving (MeasurableEquiv.neg (Vec3 × ℝ) :
      Vec3 × ℝ → Vec3 × ℝ) backwardProductVolume backwardProductVolume := by
    convert hneg0 using 1
    funext x
    rfl
  let _ : backwardProductVolume.IsAddLeftInvariant := by
    dsimp [backwardProductVolume]
    infer_instance
  let hadd0 := measurePreserving_add_left backwardProductVolume v
  let hadd : MeasurePreserving (MeasurableEquiv.addLeft v :
      Vec3 × ℝ → Vec3 × ℝ) backwardProductVolume backwardProductVolume := by
    convert hadd0 using 1
    funext x
    rfl
  unfold backwardTestPotential
  change (∫ t : Vec3 × ℝ,
      heatKernelPlus (show ParabolicPoint from -t) * ζ (v - t)
        ∂backwardProductVolume) = _
  unfold backwardHeatPotential backwardHeatKernel
  have h₁ := hneg.integral_comp'
    (fun t : Vec3 × ℝ =>
      heatKernelPlus (show ParabolicPoint from -t) * ζ (v - t))
  have h₂ := hadd.integral_comp'
    (fun z : Vec3 × ℝ =>
      heatKernelPlus (show ParabolicPoint from (z - v)) * ζ z)
  calc
    (∫ t : Vec3 × ℝ,
        heatKernelPlus (show ParabolicPoint from -t) * ζ (v - t)
          ∂backwardProductVolume) =
        ∫ t : Vec3 × ℝ,
          heatKernelPlus (show ParabolicPoint from t) * ζ (v + t)
            ∂backwardProductVolume := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h₁.symm
    _ = ∫ z : Vec3 × ℝ,
        heatKernelPlus (show ParabolicPoint from (z - v)) * ζ z
          ∂backwardProductVolume := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h₂

lemma backwardHeatKernel_eq_zero_of_nonpos {z v : ParabolicPoint}
    (h : z.2 - v.2 ≤ 0) : backwardHeatKernel z v = 0 := by
  unfold backwardHeatKernel
  exact heatKernelPlus_eq_zero_of_nonpos h

lemma backwardHeatSpatialKernel_eq_zero_of_nonpos {i : Fin 3}
    {z v : ParabolicPoint} (h : z.2 - v.2 ≤ 0) :
    backwardHeatSpatialKernel i z v = 0 := by
  unfold backwardHeatSpatialKernel
  rw [heatKernelSpaceDerivative, ite_eq_right (not_lt.mpr h)]

lemma backwardHeatPotential_eq_zero_of_future
    {ζ : ParabolicPoint → ℝ} {T : ℝ} {v : ParabolicPoint}
    (hv : T ≤ v.2) (hζ : ∀ z, T ≤ z.2 → ζ z = 0) :
    backwardHeatPotential ζ v = 0 := by
  unfold backwardHeatPotential
  rw [← integral_zero]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases htime : z.2 ≤ v.2
  · rw [backwardHeatKernel_eq_zero_of_nonpos (sub_nonpos.mpr htime)]
    simp
  · have htime' : T ≤ z.2 := by
      exact hv.trans (le_of_not_ge htime)
    rw [hζ z htime']
    simp

lemma backwardHeatPotentialSpatial_eq_zero_of_future
    {i : Fin 3} {ζ : ParabolicPoint → ℝ} {T : ℝ} {v : ParabolicPoint}
    (hv : T ≤ v.2) (hζ : ∀ z, T ≤ z.2 → ζ z = 0) :
    backwardHeatPotentialSpatial i ζ v = 0 := by
  unfold backwardHeatPotentialSpatial
  rw [show (∫ z, backwardHeatSpatialKernel i z v * ζ z) =
      ∫ z, (0 : ℝ) by
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases htime : z.2 ≤ v.2
    · rw [backwardHeatSpatialKernel_eq_zero_of_nonpos (sub_nonpos.mpr htime)]
      simp
    · have htime' : T ≤ z.2 := by
        exact hv.trans (le_of_not_ge htime)
      rw [hζ z htime']
      simp]
  simp


end CKN.Foundation.Heat
