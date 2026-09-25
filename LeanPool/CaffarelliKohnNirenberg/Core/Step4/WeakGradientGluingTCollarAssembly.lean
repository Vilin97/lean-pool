/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFixedPairing
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTDecompositionMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedRemainderBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSlice
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCorrectedSWS
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.VecMem
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CompactBall

/-! # Fixed-collar assembly of the pressure slice majorant

Local signed pressure decompositions give Morrey control on a finite cover
of the enlarged cell carrier. Weak-derivative uniqueness transfers those
bounds to one measurable field. The only external analytic input is the
fixed harmonic and far-force remainder's temporal majorant.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4

private theorem supported_riesz_finite
    (j i : Fin 3) {κ : ℝ} (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9)
    {X T : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hX : AEMeasurable X volume)
    (hzero : ∀ w ∉ parabolicCylinder z.1 z.2 r, X w = 0)
    (hXN : morreyNorm (6 / 5 : ℝ) κ X < ⊤)
    (hT : AEMeasurable T volume)
    (hid : ∀ᵐ s ∂volume, (fun y => T (y, s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i) (fun y => X (y, s))) :
    morreyNorm (6 / 5 : ℝ) κ T < ⊤ := by
  obtain ⟨L, hL⟩ := (CKN.Foundation.Parabolic.isCompact_closure_vec3Ball
    hr).isBounded.exists_norm_le
  have hsupport (y : Vec3) (s : ℝ) (hy : L < ‖y‖) : X (y,s) = 0 :=
    hzero (y,s) (fun h => (not_le.mpr hy) (hL y (subset_closure h.1)))
  have hbound := pressure_riesz_restricted_morreyNorm_bound j i hκ hκhi hX
    (glued_supported_source_slice_memLp hX hXN hr hzero) hsupport
    (B := Set.univ) MeasurableSet.univ hT (fun _ _ hn => (hn (mem_univ _)).elim)
    (by simpa only [Measure.restrict_univ] using hid)
  exact hbound.trans_lt (ENNReal.mul_lt_top (pressureRieszMorreyConstant_lt_top κ) hXN)

private theorem local_field_of_remainder_majorant
    {q τ : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτhi : τ ≤ 25)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hrem : ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      ∃ M : ℝ → ℝ≥0∞, AEMeasurable M volume ∧
        (∫⁻ s, M s ^ (3 / 2 : ℝ)) < ⊤ ∧
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
            ‖classicalGradient
              (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                (sourceSliceCentredMean z.1 ρ u) p s +
                pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤ M s)
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R)
    (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I)
    (hu : morreyVecMem 3 τ (Metric.ball z₀ R) u)
    (hDu : ∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
      (Metric.ball z₀ R) (fun z => Du z i)) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      (∀ᵐ s ∂volume.restrict (Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4)),
        ∀ i : Fin 3,
          LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball z₀.1 (R / 2)) volume ∧
          HasWeakPartialDerivOn (vec3Ball z₀.1 (R / 2)) i
            (fun y => p (y,s)) (fun y => Dp (y,s) i)) ∧
      morreyVecMem (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
        (Metric.ball z₀ (R / 2)) Dp := by
  let κ := min ((1 / τ + 8 / 25)⁻¹) q
  let B := vec3Ball z₀.1 (R / 2)
  let J := Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4)
  let S := Metric.ball z₀ (R / 2)
  have hκlo : 25 / 11 ≤ κ := endgame_kappa_ge hτ hq
  have hκhi : κ ≤ 25 / 9 := endgame_kappa_le (by linarith only [hτ]) hτhi
  have hκP : 6 / 5 ≤ κ := le_trans (by norm_num) hκlo
  have hκH : 3 / 2 ≤ κ := le_trans (by norm_num) hκlo
  have hS : MeasurableSet S := Metric.isOpen_ball.measurableSet
  have hSJ : S = B ×ˢ J := inner_pressure_ball_eq_product z₀ R
  have hsub := (closure_fixed_pressure_cylinder_subset_doubled_ball z₀ hR).trans hdom
  have hJsub : J ⊆ Ioc (z₀.2 + R ^ 2 / 4 - R ^ 2) (z₀.2 + R ^ 2 / 4) := by
    intro s hs
    have hsq : 0 ≤ R ^ 2 := sq_nonneg R
    exact ⟨by dsimp [J] at hs; linarith only [hs.1, hsq], hs.2.le⟩
  obtain ⟨Dp, T, F, H, hm, ht, hf, hh, hd, hti, hfi, hid, hhs⟩ :=
    exists_measurable_fixed_pressure_decomposition_of_sws hsol z₀ hR hdom
  have hsource := fixed_pressure_sources_aemeasurable_of_sws
    (z := (z₀.1, z₀.2 + R ^ 2 / 4)) hsol hR hsub
  have htN (j i : Fin 3) : morreyNorm (6 / 5 : ℝ) κ (T j i) < ⊤ :=
    supported_riesz_finite j i (lt_of_lt_of_le (by norm_num) hκlo) hκhi
      (z := (z₀.1, z₀.2 + R ^ 2 / 4)) hR (hsource j).1
      (fun w hw => indicator_of_notMem hw _)
      (fixed_centred_source_morrey_lt_top_of_sws hq hτ hτhi hsol z₀ hR hdom hu hDu j)
      (ht j i).aemeasurable (hti j i)
  have hfN (j i : Fin 3) : morreyNorm (6 / 5 : ℝ) κ (F j i) < ⊤ :=
    supported_riesz_finite j i (lt_of_lt_of_le (by norm_num) hκlo) hκhi
      (z := (z₀.1, z₀.2 + R ^ 2 / 4)) hR (hsource j).2
      (fun w hw => indicator_of_notMem hw _)
      (fixed_near_force_source_morrey_lt_top_of_sws hκP (min_le_right _ _) hsol z₀ hR hdom j)
      (hf j i).aemeasurable (hfi j i)
  obtain ⟨M, hM, hMn, hMb⟩ := hrem (z := (z₀.1, z₀.2 + R ^ 2 / 4)) hR hsub
  have hHN (i : Fin 3) : morreyNorm (6 / 5 : ℝ) κ (S.indicator (H i)) < ⊤ := by
    have hb : ∀ᵐ s ∂volume.restrict J, ∀ᵐ x ∂volume.restrict B, ‖H i (x, s)‖ₑ ≤ M s := by
      filter_upwards [hhs, ae_restrict_of_ae_restrict_of_subset hJsub hMb] with s hs hb
      filter_upwards [hs i, ae_restrict_mem (isOpen_vec3Ball _ _).measurableSet] with x hx hxB
      rw [hx]
      exact hb i x hxB
    apply pressure_remainder_indicator_morrey_lt_top_of_ae_slice_bound hκH hκhi (hh i) hM hS
      (fun w hw => by rw [hSJ] at hw; exact hw.1)
      (isOpen_vec3Ball _ _).measurableSet Integration.volume_vec3Ball_lt_top ?_ hMn
    rw [hSJ]
    exact ae_spatial_bound_on_product_of_restricted_slices
      (isOpen_vec3Ball _ _).measurableSet measurableSet_Ioo hb
  have hN : morreyVecMem (6 / 5 : ℝ) κ S Dp :=
    morreyVecMem_of_signed_pressure_decomposition hκP hS ht hf hh htN hfN hHN
      (fun i => Eventually.of_forall (fun w => hid i w))
  exact ⟨Dp, hm, hd, hN⟩

private theorem collar_measurable_pressure_gradient_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R)
    (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      ∀ᵐ s ∂volume.restrict (Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2)), ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball z₀.1 (3 * R / 4)) volume ∧
        HasWeakPartialDerivOn (vec3Ball z₀.1 (3 * R / 4)) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i) := by
  let J := Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2)
  have hbox := Core.Endgame.localBox_of_parabolic_ball hR hdom
  have hp := Core.Step4.pressure_integrable_on_of_suitable_local_box hsol hbox (Subset.refl _)
  have hpProd : Integrable (fun z : Vec3 × ℝ => p z)
      ((volume.restrict (vec3Ball z₀.1 R)).prod (volume.restrict J)) := by
    change Integrable (fun z : Vec3 × ℝ => p z) (volume.restrict (vec3Ball z₀.1 R ×ˢ J)) at hp
    rwa [Measure.volume_eq_prod, ← Measure.prod_restrict] at hp
  have hploc : ∀ᵐ s ∂volume.restrict J,
      LocallyIntegrableOn (fun x => p (x, s)) (vec3Ball z₀.1 R) volume :=
    hpProd.prod_left_ae.mono (fun _ hs => IntegrableOn.locallyIntegrableOn hs)
  have hJI : J ⊆ I := subset_closure.trans hbox.2.2.2.2.2
  have hslices (i : Fin 3) : ∀ᵐ s ∂volume.restrict J, ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball z₀.1 R) volume ∧
      HasWeakPartialDerivOn (vec3Ball z₀.1 R) i (fun x => p (x, s)) g := by
    apply Core.Step4.ae_exists_weakPartialDerivOn_ball_of_small_euclidean_cylinders
      isOpen_Ioo (subset_closure.trans hbox.2.2.1) hploc
    intro c t ρ hρ hsub
    have hsub' : closure (parabolicCylinder c t ρ) ⊆ spaceTimeSet Ω I :=
      hsub.trans (Set.prod_mono Subset.rfl hJI)
    have hs := Core.Step4.slice_selected_gradient_corrected_ae_of_sws_data
      (1000 * harmonicInteriorDisplayConstant) czP1OperatorConstant
      sliceForceGradientConstant le_rfl le_rfl le_rfl hsol (z := (c, t)) hρ hsub'
    filter_upwards [hs] with s h
    obtain ⟨D, hloc, _hmem, hweak, _hbound⟩ := h
    exact ⟨fun x => D x i, hloc i, hweak i⟩
  have hUB : closure (vec3Ball z₀.1 (3 * R / 4)) ⊆ vec3Ball z₀.1 R :=
    Core.Step4.closure_vec3Ball_subset_vec3Ball (by positivity) (by linarith only [hR])
  obtain ⟨Dp, hDp, hw⟩ := exists_measurable_weakGradient_on_time_union
    (isOpen_vec3Ball _ _) (isOpen_vec3Ball _ _)
    (CKN.Foundation.Parabolic.isCompact_closure_vec3Ball (by positivity)) hUB
    (I := J) (J := fun _ : ℕ => J) (fun _ => measurableSet_Ioo) (iUnion_const J)
    (fun _ => hp) hslices
  exact ⟨Dp, hDp, hw.mono (fun _ h i => ⟨(h i).1, (h i).2.1⟩)⟩

private theorem finite_cover_morrey
    {κ : ℝ} {K : Set ParabolicPoint} {D : ParabolicPoint → ℝ}
    (hD : Measurable D) {ι : Type*} (s : Finset ι) (U : ι → Set ParabolicPoint)
    (hU : ∀ a ∈ s, MeasurableSet (U a)) (hcover : K ⊆ ⋃ a ∈ s, U a)
    (hN : ∀ a ∈ s, morreyNorm (6 / 5 : ℝ) κ ((U a).indicator D) < ⊤) :
    morreyNorm (6 / 5 : ℝ) κ (K.indicator D) < ⊤ := by
  classical
  have hsum : morreyNorm (6 / 5 : ℝ) κ
      (fun w => ∑ a ∈ s, |(U a).indicator D w|) < ⊤ := by
    apply finite_sum_morreyNorm_lt_top (by norm_num)
      s (F := fun a w => |(U a).indicator D w|) (fun a ha => by
        simpa only [Real.norm_eq_abs] using (hD.indicator (hU a ha)).norm)
    intro a ha
    rw [morreyNorm_abs]
    exact hN a ha
  apply (routeA_morreyNorm_mono_ae (by norm_num : (0 : ℝ) ≤ 6 / 5)
    (Eventually.of_forall ?_)).trans_lt hsum
  intro w
  rw [show abs (∑ a ∈ s, |(U a).indicator D w|) = ∑ a ∈ s, |(U a).indicator D w| from
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))]
  by_cases hw : w ∈ K
  · obtain ⟨a, ha, haw⟩ := mem_iUnion₂.mp (hcover hw)
    rw [indicator_of_mem hw]
    calc
      |D w| = |(U a).indicator D w| := by rw [indicator_of_mem haw]
      _ ≤ ∑ b ∈ s, |(U b).indicator D w| := Finset.single_le_sum (f := fun b => |(U b).indicator D
        w|) (fun _ _ => abs_nonneg _) ha
  · rw [indicator_of_notMem hw, abs_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

private theorem product_ae_eq_of_slices
    {B : Set Vec3} {J : Set ℝ} {D E : ParabolicPoint → ℝ}
    (hD : Measurable D) (hE : Measurable E)
    (h : ∀ᵐ t ∂volume.restrict J, (fun x => D (x, t)) =ᵐ[volume.restrict B]
      (fun x => E (x, t))) :
    D =ᵐ[volume.restrict (B ×ˢ J)] E := by
  have hm : MeasurableSet {w : Vec3 × ℝ | D w = E w} := measurableSet_eq_fun hD hE
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact (Measure.ae_prod_iff_ae_ae hm).mpr ((Measure.ae_ae_comm hm).mpr h)

private theorem collar_morrey_of_local_fields
    {κ : ℝ} (hκ : 6 / 5 ≤ κ) {p : ParabolicPoint → ℝ}
    {D : ParabolicPoint → Vec3} (hD : Measurable D)
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R)
    (hweak : ∀ᵐ t ∂volume.restrict (Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2)),
      ∀ i : Fin 3,
        LocallyIntegrableOn (fun x => D (x,t) i) (vec3Ball z₀.1 (3 * R / 4)) volume ∧
        HasWeakPartialDerivOn (vec3Ball z₀.1 (3 * R / 4)) i
          (fun x => p (x,t)) (fun x => D (x,t) i))
    (hlocal : ∀ y ∈ Metric.closedBall z₀ (2 * R / 3),
      ∃ E : ParabolicPoint → Vec3, Measurable E ∧
        (∀ᵐ t ∂volume.restrict (Ioo (y.2 - (R / 8) ^ 2 / 4) (y.2 + (R / 8) ^ 2 / 4)),
          ∀ i : Fin 3,
            LocallyIntegrableOn (fun x => E (x,t) i) (vec3Ball y.1 (R / 8 / 2)) volume ∧
            HasWeakPartialDerivOn (vec3Ball y.1 (R / 8 / 2)) i
              (fun x => p (x,t)) (fun x => E (x,t) i)) ∧
        morreyVecMem (6 / 5 : ℝ) κ (Metric.ball y (R / 8 / 2)) E) :
    ∀ i, morreyNorm (6 / 5 : ℝ) κ
      ((Metric.closedBall z₀ (2 * R / 3)).indicator (fun w => D w i)) < ⊤ := by
  classical
  let K := Metric.closedBall z₀ (2 * R / 3)
  let U (y : K) := Metric.ball y.1 (R / 8 / 2)
  have hrad : 0 < R / 8 / 2 := by positivity
  have hcover : K ⊆ ⋃ y : K, U y := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self hrad⟩
  obtain ⟨s, hs⟩ := (Core.Endgame.isCompact_parabolic_closedBall z₀ (2 * R /
    3)).elim_finite_subcover
    U (fun _ => Metric.isOpen_ball) hcover
  intro i
  apply finite_cover_morrey ((measurable_pi_apply i).comp hD) s U
    (fun _ _ => Metric.isOpen_ball.measurableSet) hs
  intro y _hy
  obtain ⟨E, hE, hEs, hEN⟩ := hlocal y.1 y.2
  have hUsmall : U y ⊆ Metric.ball z₀ (3 * R / 4) := by
    intro w hw
    have hw' : dist w y.1 < R / 8 / 2 := hw
    have hy' : dist y.1 z₀ ≤ 2 * R / 3 := y.2
    have ht := dist_triangle w y.1 z₀
    change dist w z₀ < 3 * R / 4
    linarith only [hw', hy', ht, hR]
  have hB : vec3Ball y.1.1 (R / 8 / 2) ⊆ vec3Ball z₀.1 (3 * R / 4) := by
    intro x hx
    have hm : (show ParabolicPoint from (x, y.1.2)) ∈ U y := by
      change (show ParabolicPoint from (x, y.1.2)) ∈ Metric.ball y.1 (R / 8 / 2)
      rw [metricBall_eq_parabolicBall]
      exact ⟨hx, sub_lt_self _ (sq_pos_of_pos hrad), lt_add_of_pos_right _ (sq_pos_of_pos hrad)⟩
    exact ((metricBall_eq_parabolicBall z₀ (3 * R / 4)) ▸ hUsmall hm).1
  have hJ : Ioo (y.1.2 - (R / 8) ^ 2 / 4) (y.1.2 + (R / 8) ^ 2 / 4) ⊆
      Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2) := by
    intro t ht
    have hm : (show ParabolicPoint from (y.1.1, t)) ∈ U y := by
      change (show ParabolicPoint from (y.1.1, t)) ∈ Metric.ball y.1 (R / 8 / 2)
      rw [metricBall_eq_parabolicBall]
      refine ⟨?_, ?_, ?_⟩
      · change vec3EuclideanNorm (y.1.1 - y.1.1) < R / 8 / 2
        simpa only [sub_self, vec3EuclideanNorm_zero] using hrad
      · nlinarith only [ht.1]
      · nlinarith only [ht.2]
    have hb := ((metricBall_eq_parabolicBall z₀ (3 * R / 4)) ▸ hUsmall hm).2
    constructor <;> nlinarith only [hb.1, hb.2, sq_nonneg R]
  have heq : (fun w => D w i) =ᵐ[volume.restrict (U y)] (fun w => E w i) := by
    rw [show U y = vec3Ball y.1.1 (R / 8 / 2) ×ˢ
      Ioo (y.1.2 - (R / 8) ^ 2 / 4) (y.1.2 + (R / 8) ^ 2 / 4) from
      inner_pressure_ball_eq_product y.1 (R / 8)]
    apply product_ae_eq_of_slices ((measurable_pi_apply i).comp hD)
      ((measurable_pi_apply i).comp hE)
    filter_upwards [hEs, ae_restrict_of_ae_restrict_of_subset hJ hweak] with t he hd
    exact ((hd i).2.restrict (isOpen_vec3Ball _ _) hB).ae_eq
      (isOpen_vec3Ball _ _) ((hd i).1.mono_set hB) (he i).1 (he i).2
  have hN := (morreyNorm_le_morreyBallNorm (by norm_num : (0 : ℝ) ≤ 6 / 5) hκ _).trans_lt (hEN i)
  apply (routeA_morreyNorm_mono_ae (by norm_num : (0 : ℝ) ≤ 6 / 5) ?_).trans_lt hN
  filter_upwards [(ae_eq_restrict_iff_indicator_ae_eq Metric.isOpen_ball.measurableSet).mp heq]
    with w hw
  exact le_of_eq (congrArg abs hw)

private theorem shared_majorant_of_collar_field
    {Ω : Set Vec3} {I : Set ℝ} {q κ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {D : ParabolicPoint → Vec3} (hD : Measurable D)
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R)
    (hweak : ∀ᵐ t ∂volume.restrict (Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2)),
      ∀ i : Fin 3,
        LocallyIntegrableOn (fun x => D (x,t) i) (vec3Ball z₀.1 (3 * R / 4)) volume ∧
        HasWeakPartialDerivOn (vec3Ball z₀.1 (3 * R / 4)) i
          (fun x => p (x,t)) (fun x => D (x,t) i))
    (hN : ∀ i, morreyNorm (6 / 5 : ℝ) κ
      ((Metric.closedBall z₀ (2 * R / 3)).indicator (fun w => D w i)) < ⊤) :
    ∃ (A : ℝ≥0∞) (N : Fin 3 → Vec3 → ℝ → ℝ → ℝ → ℝ≥0∞), A < ⊤ ∧
      (∀ (i : Fin 3) (c : Vec3) (t ρ : ℝ), 0 < ρ →
        closure (parabolicCylinder c t ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (t - ρ ^ 2) t), ∃ g : Vec3 → ℝ,
          LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
          HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) i (fun y => p (y, s)) g ∧
          eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (euclideanBall c (ρ / 2))) ≤ N i c t ρ s) ∧
      (∀ (i : Fin 3) (z : ParabolicPoint) (r : ℝ), 0 < r → r ≤ R / 16 →
        (parabolicCylinder z.1 z.2 r ∩ Metric.ball z₀ (R / 2)).Nonempty →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2, N i z.1 z.2 (2 * r) s ^ (6 / 5 : ℝ)) ≤
          A * ENNReal.ofReal (r ^ (5 * (1 - (6 / 5 : ℝ) / κ)))) := by
  classical
  let K := Metric.closedBall z₀ (2 * R / 3)
  let G (i : Fin 3) := K.indicator (fun w => D w i)
  let N (i : Fin 3) (c : Vec3) (t ρ s : ℝ) : ℝ≥0∞ :=
    if parabolicCylinder c t (ρ / 2) ⊆ K ∧ s ∈ Ioc (t - (ρ / 2) ^ 2) t then
      eLpNorm (fun y => G i (y,s)) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall c (ρ / 2))) else ⊤
  let A : ℝ≥0∞ := ∑ i, morreyNorm (6 / 5 : ℝ) κ (G i) ^ (6 / 5 : ℝ)
  have hG (i : Fin 3) : Measurable (G i) :=
    ((measurable_pi_apply i).comp hD).indicator Metric.isClosed_closedBall.measurableSet
  have hK : K ⊆ vec3Ball z₀.1 (3 * R / 4) ×ˢ
      Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2) := by
    intro w hw
    have hm : w ∈ Metric.ball z₀ (3 * R / 4) := by
      change dist w z₀ < 3 * R / 4
      have hd : dist w z₀ ≤ 2 * R / 3 := hw
      linarith only [hd, hR]
    rw [metricBall_eq_parabolicBall] at hm
    refine ⟨hm.1, ?_, ?_⟩ <;> nlinarith only [hm.2.1, hm.2.2, sq_nonneg R]
  refine ⟨A, N, ENNReal.sum_lt_top.mpr (fun i _ =>
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hN i).ne), ?_, ?_⟩
  · intro i c t ρ hρ hsub
    have hex := slice_selected_gradient_corrected_ae_of_sws_data
      (1000 * harmonicInteriorDisplayConstant) czP1OperatorConstant
      sliceForceGradientConstant le_rfl le_rfl le_rfl hsol (z := (c,t)) hρ hsub
    filter_upwards [hex, ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp hweak)] with s
      hs hd
    by_cases hc : parabolicCylinder c t (ρ / 2) ⊆ K ∧ s ∈ Ioc (t - (ρ / 2) ^ 2) t
    · have heuc := CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
        (x₀ := c) (by positivity : 0 < ρ / 2)
      have hB : euclideanBall c (ρ / 2) ⊆ vec3Ball z₀.1 (3 * R / 4) := by
        rw [heuc]
        intro x hx
        have hxK : (show ParabolicPoint from (x,s)) ∈ K := hc.1 ⟨hx, hc.2⟩
        exact (hK hxK).1
      have hself : c ∈ vec3Ball c (ρ / 2) := by
        change vec3EuclideanNorm (c - c) < ρ / 2
        simp only [sub_self, vec3EuclideanNorm_zero]
        positivity
      have hcK : (show ParabolicPoint from (c,s)) ∈ K := hc.1 ⟨hself, hc.2⟩
      have hd' := hd (hK hcK).2 i
      refine ⟨fun x => D (x,s) i, hd'.1.mono_set hB,
        hd'.2.restrict (by rw [heuc]; exact isOpen_vec3Ball _ _) hB, ?_⟩
      simp only [N, ite_eq_left hc]
      apply le_of_eq
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem (by rw [heuc]; exact (isOpen_vec3Ball _ _).measurableSet)]
        with x hx
      have hx' : x ∈ vec3Ball c (ρ / 2) := heuc ▸ hx
      have hxK : (show ParabolicPoint from (x,s)) ∈ K := hc.1 ⟨hx', hc.2⟩
      exact (indicator_of_mem hxK (fun w => D w i)).symm
    · obtain ⟨E, hEl, _hEm, hEw, _hEb⟩ := hs
      exact ⟨fun x => E x i, hEl i, hEw i, by simp only [N, ite_eq_right hc, le_top]⟩
  · intro i z r hr hrR hmeet
    have hcell : parabolicCylinder z.1 z.2 r ⊆ K := by
      obtain ⟨w, hwQ, hwB⟩ := hmeet
      have hwz := parabolicCylinder_subset_metricBall_sameCenter z hr hwQ
      intro v hv
      have hvz := parabolicCylinder_subset_metricBall_sameCenter z hr hv
      have htri := dist_triangle v z z₀
      have htri' := dist_triangle z w z₀
      have hwz' : dist z w < r := by simpa only [dist_comm] using (Metric.mem_ball.mp hwz)
      have hwB' : dist w z₀ < R / 2 := hwB
      have hvz' : dist v z < r := hvz
      change dist v z₀ ≤ 2 * R / 3
      linarith only [htri, htri', hwz', hwB', hvz', hrR, hR]
    have hhalf : 2 * r / 2 = r := by ring
    have hn : (∫⁻ s in Ioc (z.2 - r ^ 2) z.2, N i z.1 z.2 (2 * r) s ^ (6 / 5 : ℝ)) =
        ∫⁻ s in Ioc (z.2 - r ^ 2) z.2,
          eLpNorm (fun x => G i (x,s)) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r)) ^ (6 / 5 : ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [N, hhalf, ite_eq_left (And.intro hcell ht),
        CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr]
    rw [hn]
    have hb := (glued_clipped_slice_time_bound (κ := κ) (hG i).aemeasurable
      Set.univ Set.univ z hr).2
    simp only [inter_univ] at hb
    apply hb.trans
    have hAi : morreyNorm (6 / 5 : ℝ) κ (G i) ^ (6 / 5 : ℝ) ≤ A :=
      Finset.single_le_sum (f := fun j => morreyNorm (6 / 5 : ℝ) κ (G j) ^ (6 / 5 : ℝ))
        (fun _ _ => bot_le) (Finset.mem_univ i)
    calc
      _ ≤ ENNReal.ofReal r ^ (5 * (1 - (6 / 5 : ℝ) / κ)) * A := mul_le_mul' le_rfl hAi
      _ = _ := by rw [← ENNReal.ofReal_rpow_of_pos hr]; exact mul_comm _ _

/-- A finite `3/2` temporal majorant for the fixed harmonic and far-force
remainder supplies the shared small-cell pressure-gradient bound, uniformly
in the full admissible range of Morrey exponents. -/
theorem shared_binder_of_remainder_majorant
    (hRemainderMajorant :
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}, 5 / 2 < q →
        ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
            closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
            ∃ M : ℝ → ℝ≥0∞,
              AEMeasurable M (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) ∧
              (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, M s ^ (3 / 2 : ℝ)) < ⊤ ∧
              ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
                ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
                  ‖classicalGradient
                    (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                      (sourceSliceCentredMean z.1 ρ u) p s +
                      pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤ M s) :
    ∀ q τ : ℝ, 5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
          Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
          morreyVecMem 3 τ (Metric.ball z₀ R) u →
          (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
            (Metric.ball z₀ R) (fun z => Du z i)) →
    ∃ (A : ℝ≥0∞) (N : Fin 3 → Vec3 → ℝ → ℝ → ℝ → ℝ≥0∞), A < ⊤ ∧
      (∀ (i : Fin 3) (c : Vec3) (t ρ : ℝ), 0 < ρ →
        closure (parabolicCylinder c t ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (t - ρ ^ 2) t), ∃ g : Vec3 → ℝ,
          LocallyIntegrableOn g (euclideanBall c (ρ / 2)) volume ∧
          HasWeakPartialDerivOn (euclideanBall c (ρ / 2)) i (fun y => p (y, s)) g ∧
          eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (euclideanBall c (ρ / 2))) ≤ N i c t ρ s) ∧
      (∀ (i : Fin 3) (z : ParabolicPoint) (r : ℝ), 0 < r → r ≤ R / 16 →
        (parabolicCylinder z.1 z.2 r ∩ Metric.ball z₀ (R / 2)).Nonempty →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2, N i z.1 z.2 (2 * r) s ^ (6 / 5 : ℝ)) ≤
          A * ENNReal.ofReal (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) := by
  intro q τ hq hτ hτhi Ω I u Du p f hsol z₀ R hR hdom hu hDu
  have hrem {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
      (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
      ∃ M : ℝ → ℝ≥0∞, AEMeasurable M volume ∧
        (∫⁻ s, M s ^ (3 / 2 : ℝ)) < ⊤ ∧
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
            ‖classicalGradient
              (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                (sourceSliceCentredMean z.1 ρ u) p s +
                pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤ M s := by
    obtain ⟨M, hm, hn, hb⟩ := hRemainderMajorant hq hsol hρ hsub
    obtain ⟨hm', hn'⟩ := glued_time_indicator_power measurableSet_Ioc hm hn
    refine ⟨(Ioc (z.2 - ρ ^ 2) z.2).indicator M, hm', hn', ?_⟩
    filter_upwards [hb, ae_restrict_mem measurableSet_Ioc] with s hs hsJ
    simpa only [indicator_of_mem hsJ] using hs
  obtain ⟨D, hD, hweak⟩ := collar_measurable_pressure_gradient_of_sws hsol z₀ hR hdom
  apply shared_majorant_of_collar_field hsol hD z₀ hR hweak
  apply collar_morrey_of_local_fields
    (le_trans (by norm_num : (6 / 5 : ℝ) ≤ 25 / 11) (endgame_kappa_ge hτ hq)) hD z₀ hR hweak
  intro y hy
  have hinner : Metric.ball y (R / 8) ⊆ Metric.ball z₀ R := by
    intro w hw
    have hw' : dist w y < R / 8 := hw
    have hy' : dist y z₀ ≤ 2 * R / 3 := hy
    have ht := dist_triangle w y z₀
    change dist w z₀ < R
    linarith only [hw', hy', ht, hR]
  have houter : Metric.ball y (2 * (R / 8)) ⊆ spaceTimeSet Ω I := by
    intro w hw
    apply hdom
    have hw' : dist w y < 2 * (R / 8) := hw
    have hy' : dist y z₀ ≤ 2 * R / 3 := hy
    have ht := dist_triangle w y z₀
    change dist w z₀ < 2 * R
    linarith only [hw', hy', ht, hR]
  exact local_field_of_remainder_majorant hq hτ hτhi hsol hrem y (by positivity) houter
    (morreyVecMem_mono (by norm_num) hinner hu)
    (fun i => morreyVecMem_mono (by norm_num) hinner (hDu i))

end CKN.Core.Step4
