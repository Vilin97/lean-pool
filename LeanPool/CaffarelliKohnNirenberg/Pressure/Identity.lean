/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation
public import LeanPool.CaffarelliKohnNirenberg.Pressure.ParamExtension
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.SpaceTime
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.TsupportSpatialBox
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Identity

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- The spatial pressure residual at a fixed time for a compactly supported test. -/
def pressureSliceResidual {Ω : Set Vec3} {u : ParabolicPoint → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (ψ : Vec3 → ℝ) (s : ℝ) : ℝ :=
  (∫ x in Ω, p (x, s) * spatialLaplacian ψ x) +
    (∫ x in Ω, ∑ i, ∑ j, u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
    ∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv ψ i x

private theorem support_spatialDeriv_subset {ψ : Vec3 → ℝ} (i : Fin 3) :
    Function.support (spatialDeriv ψ i) ⊆ tsupport ψ := by
  intro x hx
  by_contra hxt
  exact hx (by simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt])

private theorem tsupport_spatialDeriv_subset {ψ : Vec3 → ℝ} (i : Fin 3) :
    tsupport (spatialDeriv ψ i) ⊆ tsupport ψ :=
  closure_minimal (support_spatialDeriv_subset i) (isClosed_tsupport ψ)

private theorem support_mixedSecond_subset {ψ : Vec3 → ℝ} (i j : Fin 3) :
    Function.support (mixedSecond ψ i j) ⊆ tsupport ψ :=
  (support_spatialDeriv_subset (ψ := spatialDeriv ψ j) i).trans
    (tsupport_spatialDeriv_subset j)

private theorem tsupport_mixedSecond_subset {ψ : Vec3 → ℝ} (i j : Fin 3) :
    tsupport (mixedSecond ψ i j) ⊆ tsupport ψ :=
  closure_minimal (support_mixedSecond_subset i j) (isClosed_tsupport ψ)

private theorem support_spatialLaplacian_subset {ψ : Vec3 → ℝ} :
    Function.support (spatialLaplacian ψ) ⊆ tsupport ψ := by
  intro x hx
  by_contra hxt
  apply hx
  simp only [spatialLaplacian]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hxi : x ∉ tsupport (spatialDeriv ψ i) :=
    fun hi => hxt (tsupport_spatialDeriv_subset i hi)
  simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxi]

private theorem tsupport_spatialLaplacian_subset {ψ : Vec3 → ℝ} :
    tsupport (spatialLaplacian ψ) ⊆ tsupport ψ :=
  closure_minimal support_spatialLaplacian_subset (isClosed_tsupport ψ)

private theorem hasCompactSupport_spatialDeriv {ψ : Vec3 → ℝ}
    (hψc : HasCompactSupport ψ) (i : Fin 3) : HasCompactSupport (spatialDeriv ψ i) :=
  HasCompactSupport.of_support_subset_isCompact hψc.isCompact
    (support_spatialDeriv_subset i)

private theorem hasCompactSupport_mixedSecond {ψ : Vec3 → ℝ}
    (hψc : HasCompactSupport ψ) (i j : Fin 3) :
    HasCompactSupport (mixedSecond ψ i j) :=
  HasCompactSupport.of_support_subset_isCompact hψc.isCompact
    (support_mixedSecond_subset i j)

private theorem pressure_convection_pointwise
    {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {u : ParabolicPoint → Vec3} (z : ParabolicPoint) :
    (∑ i, ∑ j, u z i * u z j *
      spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z) =
      θ z.2 * ∑ i, ∑ j, u z i * u z j * mixedSecond ψ i j z.1 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pressureTest_spatialPartial hψ i j z, mixedSecond_swap hψ j i z.1]
  ring

private theorem pressure_laplacian_pointwise
    {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : ParabolicPoint) :
    ∑ i, spatialPartial (fun w => pressureTestParabolic ψ θ w i) i z =
      θ z.2 * spatialLaplacian ψ z.1 := by
  unfold spatialLaplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pressureTest_spatialPartial hψ i i z]
  rfl

private theorem pressure_force_pointwise
    {ψ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (z : ParabolicPoint) {f : ParabolicPoint → Vec3} :
    (∑ i, f z i * pressureTestParabolic ψ θ z i) =
      θ z.2 * ∑ i, f z i * spatialDeriv ψ i z.1 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change f z i * (θ z.2 * spatialDeriv ψ i z.1) = _
  ring

private theorem pressure_slice_integral_eq_full
    {Ω : Set Vec3} {g : Vec3 → ℝ}
    (hzero : ∀ x ∉ Ω, g x = 0) :
    ∫ x in Ω, g x = ∫ x, g x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

private theorem pressureSliceResidual_locallyIntegrable_aux
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω) :
    LocallyIntegrableOn
      (pressureSliceResidual (Ω := Ω) (u := u) (p := p) (f := f) ψ) I volume := by
  have hΩ : IsOpen Ω := h.1
  have hI : IsOpen I := h.2.1
  intro s hs
  obtain ⟨ε, hεpos, hεI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hs)
  let c : ContDiffBump s :=
    ⟨ε / 4, ε / 2, by linarith only [hεpos], by linarith only [hεpos]⟩
  let θ : ℝ → ℝ := ⇑c
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := c.contDiff
  have hθc : HasCompactSupport θ := c.hasCompactSupport
  have hθI : tsupport θ ⊆ I := by
    rw [show tsupport θ = closedBall s (ε / 2) from c.tsupport_eq]
    exact (closedBall_subset_ball (by linarith only [hεpos])).trans hεI
  obtain ⟨hconv, _hvisc, hpress, hforce⟩ :=
    pressure_test_terms_integrable h hψ hψc hψΩ hθ hθc hθI
  have hconv_time : Integrable (fun t => ∫ x,
      θ t * ∑ i, ∑ j, u (x, t) i * u (x, t) j * mixedSecond ψ i j x) volume := by
    have htime := hconv.integral_prod_right
    refine htime.congr (Filter.Eventually.of_forall (fun t => ?_))
    apply integral_congr_ae
    filter_upwards [] with x
    rw [pressure_convection_pointwise hψ (x, t)]
  have hpress_time : Integrable (fun t => ∫ x,
      θ t * (p (x, t) * spatialLaplacian ψ x)) volume := by
    have htime := hpress.integral_prod_right
    refine htime.congr (Filter.Eventually.of_forall (fun t => ?_))
    apply integral_congr_ae
    filter_upwards [] with x
    rw [pressure_laplacian_pointwise hψ (x, t)]
    ring
  have hforce_time : Integrable (fun t => ∫ x,
      θ t * ∑ i, f (x, t) i * spatialDeriv ψ i x) volume := by
    have htime := hforce.integral_prod_right
    refine htime.congr (Filter.Eventually.of_forall (fun t => ?_))
    apply integral_congr_ae
    filter_upwards [] with x
    rw [pressure_force_pointwise (x, t)]
  have hconv_local : IntegrableOn (fun t => ∫ x,
      ∑ i, ∑ j, u (x, t) i * u (x, t) j * mixedSecond ψ i j x)
      (ball s (ε / 4)) volume := by
    have htime : Integrable (fun t => ∫ x,
        θ t * ∑ i, ∑ j, u (x, t) i * u (x, t) j * mixedSecond ψ i j x)
        (volume.restrict (ball s (ε / 4))) := hconv_time.integrableOn
    refine htime.congr ?_
    filter_upwards [self_mem_ae_restrict isOpen_ball.measurableSet] with t ht
    have hct := c.one_of_mem_closedBall (ball_subset_closedBall ht)
    simp only [θ, hct, one_mul]
  have hpress_local : IntegrableOn (fun t => ∫ x,
      p (x, t) * spatialLaplacian ψ x) (ball s (ε / 4)) volume := by
    have htime : Integrable (fun t => ∫ x,
        θ t * (p (x, t) * spatialLaplacian ψ x))
        (volume.restrict (ball s (ε / 4))) := hpress_time.integrableOn
    refine htime.congr ?_
    filter_upwards [self_mem_ae_restrict isOpen_ball.measurableSet] with t ht
    have hct := c.one_of_mem_closedBall (ball_subset_closedBall ht)
    simp only [θ, hct, one_mul]
  have hforce_local : IntegrableOn (fun t => ∫ x,
      ∑ i, f (x, t) i * spatialDeriv ψ i x) (ball s (ε / 4)) volume := by
    have htime : Integrable (fun t => ∫ x,
        θ t * ∑ i, f (x, t) i * spatialDeriv ψ i x)
        (volume.restrict (ball s (ε / 4))) := hforce_time.integrableOn
    refine htime.congr ?_
    filter_upwards [self_mem_ae_restrict isOpen_ball.measurableSet] with t ht
    have hct := c.one_of_mem_closedBall (ball_subset_closedBall ht)
    simp only [θ, hct, one_mul]
  have hsum : IntegrableOn
      (fun t =>
        (∫ x, p (x, t) * spatialLaplacian ψ x) +
          (∫ x, ∑ i, ∑ j, u (x, t) i * u (x, t) j * mixedSecond ψ i j x) +
          ∫ x, ∑ i, f (x, t) i * spatialDeriv ψ i x)
      (ball s (ε / 4)) volume :=
    (hpress_local.add hconv_local).add hforce_local
  refine ⟨ball s (ε / 4), ?_, ?_⟩
  · exact mem_nhdsWithin.mpr
      ⟨ball s (ε / 4), isOpen_ball, mem_ball_self (by linarith only [hεpos]),
        fun t ht => ht.1⟩
  · refine hsum.congr (Filter.Eventually.of_forall (fun t => ?_))
    simp only [pressureSliceResidual]
    have hpress_zero : ∀ x ∉ Ω, p (x, t) * spatialLaplacian ψ x = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport
        (fun hm => hx (hψΩ (tsupport_spatialLaplacian_subset hm))), mul_zero]
    have hconv_zero : ∀ x ∉ Ω,
        ∑ i, ∑ j, u (x, t) i * u (x, t) j * mixedSecond ψ i j x = 0 := by
      intro x hx
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      rw [image_eq_zero_of_notMem_tsupport
        (fun hm => hx (hψΩ (tsupport_mixedSecond_subset i j hm))), mul_zero]
    have hforce_zero : ∀ x ∉ Ω,
        ∑ i, f (x, t) i * spatialDeriv ψ i x = 0 := by
      intro x hx
      apply Finset.sum_eq_zero
      intro i hi
      rw [image_eq_zero_of_notMem_tsupport
        (fun hm => hx (hψΩ (tsupport_spatialDeriv_subset i hm))), mul_zero]
    calc
      (∫ x, p (x, t) * spatialLaplacian ψ x) +
          (∫ x, ∑ i, ∑ j, u (x, t) i * u (x, t) j * mixedSecond ψ i j x) +
          ∫ x, ∑ i, f (x, t) i * spatialDeriv ψ i x =
        (∫ x in Ω, p (x, t) * spatialLaplacian ψ x) +
          (∫ x, ∑ i, ∑ j, u (x, t) i * u (x, t) j * mixedSecond ψ i j x) +
          ∫ x, ∑ i, f (x, t) i * spatialDeriv ψ i x := by
            rw [(pressure_slice_integral_eq_full hpress_zero).symm]
      _ = (∫ x in Ω, p (x, t) * spatialLaplacian ψ x) +
          (∫ x in Ω, ∑ i, ∑ j, u (x, t) i * u (x, t) j * mixedSecond ψ i j x) +
          ∫ x, ∑ i, f (x, t) i * spatialDeriv ψ i x := by
            rw [(pressure_slice_integral_eq_full hconv_zero).symm]
      _ = (∫ x in Ω, p (x, t) * spatialLaplacian ψ x) +
          (∫ x in Ω, ∑ i, ∑ j, u (x, t) i * u (x, t) j * mixedSecond ψ i j x) +
          ∫ x in Ω, ∑ i, f (x, t) i * spatialDeriv ψ i x := by
            rw [(pressure_slice_integral_eq_full hforce_zero).symm]

private theorem exists_identity_time_radius {I : Set ℝ} (hI : IsOpen I) {s : ℝ}
    (hs : s ∈ I) : ∃ r : ℝ, 0 < r ∧ closedBall s r ⊆ I := by
  obtain ⟨ε, hε, hεI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hs)
  refine ⟨ε / 2, by linarith only [hε], ?_⟩
  exact (closedBall_subset_ball (by linarith only [hε])).trans hεI

private theorem slice_memLp_on_support_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 → ℝ} (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω) :
    ∃ Ω' : Set Vec3, IsOpen Ω' ∧ tsupport ψ ⊆ Ω' ∧
      IsCompact (closure Ω') ∧ closure Ω' ⊆ Ω ∧
      ∀ᵐ s ∂volume.restrict I,
        MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
        MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω') := by
  classical
  have hΩ : IsOpen Ω := h.1
  have hI : IsOpen I := h.2.1
  obtain ⟨Ω', hΩ'open, hψΩ', hΩ'compact, hΩ'Ω⟩ :=
    exists_spatial_box_of_tsupport_subset hΩ hψΩ hψc
  let r : ℝ → ℝ := fun s => if hs : s ∈ I then
    Classical.choose (exists_identity_time_radius hI hs) else 1
  have hr_pos : ∀ s ∈ I, 0 < r s := by
    intro s hs
    simp only [r, dite_eq_left hs]
    exact (Classical.choose_spec (exists_identity_time_radius hI hs)).1
  have hr_sub : ∀ s ∈ I, closedBall s (r s) ⊆ I := by
    intro s hs
    simp only [r, dite_eq_left hs]
    exact (Classical.choose_spec (exists_identity_time_radius hI hs)).2
  let V : ℝ → Set ℝ := fun s => ball s (r s)
  obtain ⟨T, hTsub, hTcount, hcover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin
      (s := I) (f := V) (by
        intro s hs
        refine mem_nhdsWithin.mpr ⟨V s, isOpen_ball, mem_ball_self (hr_pos s hs), ?_⟩
        exact inter_subset_left)
  have hlocal : ∀ s ∈ T, ∀ᵐ t ∂volume.restrict (closedBall s (r s)),
      MemLp (fun x : Vec3 => u (x, t)) 2 (volume.restrict Ω') ∧
      MemLp (fun x : Vec3 => Du (x, t)) 2 (volume.restrict Ω') := by
    intro s hs
    have hsI : s ∈ I := hTsub hs
    let J : Set ℝ := closedBall s (r s)
    have hJsub : J ⊆ I := hr_sub s hsI
    have hJcompact : IsCompact (closure J) := by
      rw [Metric.closure_closedBall]
      exact ProperSpace.isCompact_closedBall s (r s)
    have hJord : J.OrdConnected := by
      rw [show J = Icc (s - r s) (s + r s) by
        ext t
        simp only [J, mem_closedBall, Real.dist_eq, mem_Icc, abs_le]
        constructor
        · rintro ⟨h₁, h₂⟩
          constructor <;> linarith only [h₁, h₂]
        · rintro ⟨h₁, h₂⟩
          constructor <;> linarith only [h₁, h₂]]
      exact ordConnected_Icc
    have hJsub' : closure J ⊆ I := by
      simpa only [J, Metric.closure_closedBall] using hJsub
    have hbox : localBox Ω I Ω' J :=
      ⟨hΩ'open, hΩ'compact, hΩ'Ω, hJord, hJcompact, hJsub'⟩
    simpa only [J] using (slice_memLp_ae_of_sws h hbox)
  have hlocal_ball : ∀ s ∈ T, ∀ᵐ t ∂volume.restrict (V s),
      MemLp (fun x : Vec3 => u (x, t)) 2 (volume.restrict Ω') ∧
      MemLp (fun x : Vec3 => Du (x, t)) 2 (volume.restrict Ω') := by
    intro s hs
    exact ae_restrict_of_ae_restrict_of_subset
      (by simpa only [V] using (Metric.ball_subset_closedBall :
        ball s (r s) ⊆ closedBall s (r s))) (hlocal s hs)
  have hunion : ∀ᵐ t ∂volume.restrict (⋃ s ∈ T, V s),
      MemLp (fun x : Vec3 => u (x, t)) 2 (volume.restrict Ω') ∧
      MemLp (fun x : Vec3 => Du (x, t)) 2 (volume.restrict Ω') :=
    (ae_restrict_biUnion_iff V hTcount _).2 hlocal_ball
  refine ⟨Ω', hΩ'open, hψΩ', hΩ'compact, hΩ'Ω, ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset hcover hunion

private theorem identity_restrict_isFiniteMeasure {K : Set Vec3}
    (hK : IsCompact (closure K)) : IsFiniteMeasure (volume.restrict K) := by
  apply isFiniteMeasure_restrict.mpr
  exact (lt_of_le_of_lt (measure_mono (μ := volume) subset_closure)
    hK.measure_lt_top).ne

private theorem pressure_viscous_slice_zero
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθI : tsupport θ ⊆ I) :
    ∫ z in spaceTimeSet Ω I, ∑ i, ∑ j,
        Du z i j * spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z = 0 := by
  have hΩ : IsOpen Ω := h.1
  have hI : IsOpen I := h.2.1
  have hgrad_all : ∀ᵐ s ∂volume.restrict I, ∀ i j : Fin 3,
      ∫ x in Ω, u (x, s) i * spatialDeriv (mixedSecond ψ j i) j x =
        -∫ x in Ω, Du (x, s) i j * mixedSecond ψ j i x := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    have hm : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ j i) :=
      (contDiff_mixedSecond_smooth hψ j i).of_le (by simp)
    have hg := weakGradient_slice_ae_of_sws h hm
      (hasCompactSupport_mixedSecond hψc j i)
      ((tsupport_mixedSecond_subset j i).trans hψΩ)
    filter_upwards [hg] with s hs
    simpa only [spatialDeriv] using hs i j
  have hdiv_all : ∀ᵐ s ∂volume.restrict I, ∀ j : Fin 3,
      ∫ x in Ω, ∑ i, u (x, s) i * spatialDeriv (mixedSecond ψ j j) i x = 0 := by
    rw [ae_all_iff]
    intro j
    have hm : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ j j) :=
      (contDiff_mixedSecond_smooth hψ j j).of_le (by simp)
    have hd := divfree_slice_weak_of_suitable h (mixedSecond ψ j j) hm
      (hasCompactSupport_mixedSecond hψc j j)
      ((tsupport_mixedSecond_subset j j).trans hψΩ)
    filter_upwards [hd] with s hs
    simpa only [spatialDeriv] using hs
  obtain ⟨Ω', hΩ'open, hψΩ', hΩ'compact, hΩ'Ω, hLp⟩ :=
    slice_memLp_on_support_ae h hψc hψΩ
  haveI : IsFiniteMeasure (volume.restrict Ω') :=
    identity_restrict_isFiniteMeasure hΩ'compact
  have hgood : ∀ᵐ s ∂volume.restrict I,
      (MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
        MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω')) ∧
      (∀ i j : Fin 3,
        ∫ x in Ω, u (x, s) i * spatialDeriv (mixedSecond ψ j i) j x =
          -∫ x in Ω, Du (x, s) i j * mixedSecond ψ j i x) ∧
      (∀ j : Fin 3,
        ∫ x in Ω, ∑ i, u (x, s) i * spatialDeriv (mixedSecond ψ j j) i x = 0) := by
    filter_upwards [hLp, hgrad_all, hdiv_all]
      with s hLp_s hgrad_s hdiv_s
    exact ⟨hLp_s, hgrad_s, hdiv_s⟩
  have hvisc_full : Integrable
      (fun z => ∑ i, ∑ j,
        Du z i j * spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z) volume :=
    (pressure_test_terms_integrable h hψ hψc hψΩ hθ hθc hθI).2.1
  have hvisc_zero_out : ∀ z ∉ spaceTimeSet Ω I,
      (∑ i, ∑ j,
        Du z i j * spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z) = 0 := by
    intro z hz
    by_cases hx : z.1 ∈ Ω
    · have ht : z.2 ∉ I := fun ht => hz ⟨hx, ht⟩
      have htθ : z.2 ∉ tsupport θ := fun htθ => ht (hθI htθ)
      have hsp : ∀ i j : Fin 3,
          spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z = 0 := by
        intro i j
        rw [pressureTest_spatialPartial hψ i j z]
        rw [image_eq_zero_of_notMem_tsupport htθ, zero_mul]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [hsp i j, mul_zero]
    · have hxψ : z.1 ∉ tsupport ψ := fun hxψ => hx (hψΩ hxψ)
      have hsp : ∀ i j : Fin 3,
          spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z = 0 := by
        intro i j
        rw [pressureTest_spatialPartial hψ i j z]
        rw [image_eq_zero_of_notMem_tsupport
          (fun hm => hxψ (tsupport_mixedSecond_subset j i hm)), mul_zero]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [hsp i j, mul_zero]
  have hvisc_set : ∫ z in spaceTimeSet Ω I,
      ∑ i, ∑ j, Du z i j *
        spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z =
      ∫ z, ∑ i, ∑ j, Du z i j *
        spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvisc_zero_out]
  have hvisc_full' : Integrable
      (fun z => ∑ i, ∑ j,
        Du z i j * spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z)
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := hvisc_full
  have hFubini : (∫ z, ∑ i, ∑ j,
        Du z i j * spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z) =
      ∫ s, ∫ x, ∑ i, ∑ j,
        Du (x, s) i j * spatialPartial (fun w => pressureTestParabolic ψ θ w i) j (x, s) :=
    integral_prod_symm _ hvisc_full'
  rw [hvisc_set, hFubini]
  apply integral_eq_zero_of_ae
  rw [ae_restrict_iff' hI.measurableSet] at hgood
  filter_upwards [hgood] with s hs
  by_cases hsI : s ∈ I
  · rcases hs hsI with ⟨hLp_s, hgrad_s, hdiv_s⟩
    have huInt (i : Fin 3) : Integrable (fun x : Vec3 => u (x, s) i)
        (volume.restrict Ω') := by
      exact (hLp_s.1.continuousLinearMap_comp
        (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)).integrable (by norm_num)
    have hDuInt (i j : Fin 3) : Integrable (fun x : Vec3 => Du (x, s) i j)
        (volume.restrict Ω') := by
      exact ((hLp_s.2.continuousLinearMap_comp
        (ContinuousLinearMap.proj i : (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
        (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)).integrable (by norm_num)
    have huTerm (i j : Fin 3) : Integrable (fun x : Vec3 =>
        u (x, s) i * spatialDeriv (mixedSecond ψ j i) j x) volume := by
      obtain ⟨C, hC⟩ :=
        (hasCompactSupport_spatialDeriv (hasCompactSupport_mixedSecond hψc j i) j).exists_bound_of_continuous
          (contDiff_spatialDeriv_smooth (contDiff_mixedSecond_smooth hψ j i) j).continuous
      have hfac : AEStronglyMeasurable
          (fun x : Vec3 => spatialDeriv (mixedSecond ψ j i) j x)
          (volume.restrict Ω') :=
        ((contDiff_spatialDeriv_smooth (contDiff_mixedSecond_smooth hψ j i) j).continuous).measurable.aestronglyMeasurable
      have hmul := (huInt i).mul_bdd hfac
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
      have hmulOn : IntegrableOn (fun x : Vec3 =>
          u (x, s) i * spatialDeriv (mixedSecond ψ j i) j x) Ω' volume := hmul
      exact hmulOn.integrable_of_forall_notMem_eq_zero (by
          intro x hx
          rw [image_eq_zero_of_notMem_tsupport
            (fun hm => hx (hψΩ' (tsupport_mixedSecond_subset j i
              (tsupport_spatialDeriv_subset j hm)))), mul_zero])
    have hDuTerm (i j : Fin 3) : Integrable (fun x : Vec3 =>
        Du (x, s) i j * mixedSecond ψ j i x) volume := by
      obtain ⟨C, hC⟩ := (hasCompactSupport_mixedSecond hψc j i).exists_bound_of_continuous
        (contDiff_mixedSecond_smooth hψ j i).continuous
      have hfac : AEStronglyMeasurable (fun x : Vec3 => mixedSecond ψ j i x)
          (volume.restrict Ω') :=
        (contDiff_mixedSecond_smooth hψ j i).continuous.measurable.aestronglyMeasurable
      have hmul := (hDuInt i j).mul_bdd hfac
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
      have hmulOn : IntegrableOn (fun x : Vec3 =>
          Du (x, s) i j * mixedSecond ψ j i x) Ω' volume := hmul
      exact hmulOn.integrable_of_forall_notMem_eq_zero (by
          intro x hx
          rw [image_eq_zero_of_notMem_tsupport
            (fun hm => hx (hψΩ' (tsupport_mixedSecond_subset j i hm))), mul_zero])
    have hgrad_sum (j : Fin 3) :
        ∫ x in Ω, ∑ i, u (x, s) i * spatialDeriv (mixedSecond ψ j i) j x =
          -∑ i, ∫ x in Ω, Du (x, s) i j * mixedSecond ψ j i x := by
      rw [integral_finsetSum (Finset.univ : Finset (Fin 3))
        (fun i _ => (huTerm i j).integrableOn)]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hgrad_s i j]
    have hdiv_eq (j : Fin 3) :
        ∫ x in Ω, ∑ i, u (x, s) i * spatialDeriv (mixedSecond ψ j i) j x = 0 := by
      calc
        ∫ x in Ω, ∑ i, u (x, s) i * spatialDeriv (mixedSecond ψ j i) j x =
            ∫ x in Ω, ∑ i, u (x, s) i * spatialDeriv (mixedSecond ψ j j) i x := by
              apply integral_congr_ae
              filter_upwards [] with x
              apply Finset.sum_congr rfl
              intro i hi
              rw [thirdDerivative_identity hψ i j x]
        _ = 0 := hdiv_s j
    have hDu_sum (j : Fin 3) :
        ∑ i, ∫ x in Ω, Du (x, s) i j * mixedSecond ψ j i x = 0 := by
      linarith only [hgrad_sum j, hdiv_eq j]
    have hsumDu_zero (j : Fin 3) :
        ∫ x in Ω, ∑ i, Du (x, s) i j * mixedSecond ψ j i x = 0 := by
      calc
        ∫ x in Ω, ∑ i, Du (x, s) i j * mixedSecond ψ j i x =
            ∑ i, ∫ x in Ω, Du (x, s) i j * mixedSecond ψ j i x := by
              simpa using integral_finsetSum (μ := volume.restrict Ω)
                (Finset.univ : Finset (Fin 3))
                (fun i _ => (hDuTerm i j).integrableOn)
        _ = 0 := hDu_sum j
    have hsumDu (j : Fin 3) : IntegrableOn
        (fun x => ∑ i, Du (x, s) i j * mixedSecond ψ j i x) Ω volume :=
      integrable_finsetSum' (Finset.univ : Finset (Fin 3))
        (fun i _ => (hDuTerm i j).integrableOn)
    have hbase_zero : ∫ x in Ω, ∑ j, ∑ i,
        Du (x, s) i j * mixedSecond ψ j i x = 0 := by
      have hfin := integral_finsetSum (μ := volume.restrict Ω)
        (Finset.univ : Finset (Fin 3))
        (fun j _ => hsumDu j)
      calc
        ∫ x in Ω, ∑ j, ∑ i, Du (x, s) i j * mixedSecond ψ j i x =
            ∑ j, ∫ x in Ω, ∑ i, Du (x, s) i j * mixedSecond ψ j i x := by
              simpa using hfin
        _ = 0 := by
          exact Finset.sum_eq_zero (fun j _ => hsumDu_zero j)
    have hvzero : ∀ x ∉ Ω, ∑ i, ∑ j, Du (x, s) i j *
        spatialPartial (fun w => pressureTestParabolic ψ θ w i) j (x, s) = 0 := by
      intro x hx
      refine Finset.sum_eq_zero (fun i _ => ?_)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have hpartial := pressureTest_spatialPartial (ψ := ψ) (θ := θ) hψ i j
        ((x, s) : ParabolicPoint)
      rw [hpartial]
      simp [image_eq_zero_of_notMem_tsupport
        (fun hm => hx (hψΩ (tsupport_mixedSecond_subset j i hm)))]
    calc
      ∫ x, ∑ i, ∑ j, Du (x, s) i j *
          spatialPartial (fun w => pressureTestParabolic ψ θ w i) j (x, s) =
          ∫ x in Ω, ∑ i, ∑ j, Du (x, s) i j *
          spatialPartial (fun w => pressureTestParabolic ψ θ w i) j (x, s) :=
            (pressure_slice_integral_eq_full hvzero).symm
      _ =
          ∫ x in Ω, θ s * ∑ j, ∑ i,
            Du (x, s) i j * mixedSecond ψ j i x := by
              apply integral_congr_ae
              filter_upwards [] with x
              have hpartial (i j : Fin 3) :=
                pressureTest_spatialPartial (ψ := ψ) (θ := θ) hψ i j
                  ((x, s) : ParabolicPoint)
              simp_rw [hpartial]
              calc
                ∑ i, ∑ j, Du (x, s) i j *
                      (θ s * mixedSecond ψ j i x) =
                    ∑ i, ∑ j, θ s *
                      (Du (x, s) i j * mixedSecond ψ j i x) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        apply Finset.sum_congr rfl
                        intro j hj
                        ring
                _ = ∑ j, ∑ i, θ s *
                      (Du (x, s) i j * mixedSecond ψ j i x) := by
                        rw [Finset.sum_comm]
                _ = θ s * ∑ j, ∑ i,
                      Du (x, s) i j * mixedSecond ψ j i x := by
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro j hj
                        rw [Finset.mul_sum]
      _ = θ s * (∫ x in Ω, ∑ j, ∑ i,
            Du (x, s) i j * mixedSecond ψ j i x) := by
              rw [integral_const_mul]
      _ = 0 := by rw [hbase_zero, mul_zero]
  · have htθ : s ∉ tsupport θ := fun htθ => hsI (hθI htθ)
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    refine Finset.sum_eq_zero (fun i _ => ?_)
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have hpartial := pressureTest_spatialPartial (ψ := ψ) (θ := θ) hψ i j
      ((x, s) : ParabolicPoint)
    rw [hpartial]
    simp [image_eq_zero_of_notMem_tsupport htθ]

/- The following two interfaces expose the integrability reductions used by the
   slice identity without exposing their auxiliary covering constructions. -/
/-- The pressure residual is locally integrable on the time interval. -/
theorem pressureSliceResidual_locallyIntegrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω) :
    LocallyIntegrableOn
      (pressureSliceResidual (Ω := Ω) (u := u) (p := p) (f := f) ψ) I volume :=
  pressureSliceResidual_locallyIntegrable_aux h hψ hψc hψΩ

/-- The viscous term of a separated pressure test has zero space-time integral. -/
theorem pressure_viscous_test_integral_zero
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθI : tsupport θ ⊆ I) :
    ∫ z in spaceTimeSet Ω I, ∑ i, ∑ j,
        Du z i j * spatialPartial (fun w => pressureTestParabolic ψ θ w i) j z = 0 := by
  exact pressure_viscous_slice_zero h hψ hψc hψΩ hθ hθc hθI


end CKN
