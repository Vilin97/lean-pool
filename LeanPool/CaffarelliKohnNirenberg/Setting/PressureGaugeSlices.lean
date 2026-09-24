/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.LocalBox
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Slice identities behind the pressure gauge invariance

This file collects the measure-theoretic slice identities used in the proof of
the pressure gauge invariance of `rem:two-means` in `paper/ckn.tex`: a suitable
weak solution stays one when an arbitrary function of time is added to the
pressure.

The two facts that carry the analytic content are

* `gauge_divergence_pairing`: the gauge pairs integrably with the divergence of
  a space-time test field and the pairing vanishes, because the spatial
  integral of a divergence vanishes on every time slice;
* `gauge_velocity_pairing`: the gauge pairs integrably with `u · ∇ψ` and the
  pairing vanishes, because the divergence-free clause (S2) of `def:sws`,
  tested against `θ(t)ψ(x,t)`, forces the spatial pairing of the slice
  `u(·,t)` with `∇ψ(·,t)` to vanish for almost every time.

The uniform time-slice bound of the velocity comes from the essential
supremum of the slice energies in `def:sws` together with `x ≤ 1 + x²`; no
Gagliardo-Nirenberg input is needed.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- A local spatial box has finite volume. -/
private theorem localBox_volume_lt_top {Ω : Set Vec3} {I : Set ℝ} {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) : volume Ω' < ∞ :=
  lt_of_le_of_lt (measure_mono subset_closure) hbox.2.1.measure_lt_top

private theorem localBox_time_volume_lt_top {Ω : Set Vec3} {I : Set ℝ} {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) : volume J < ∞ :=
  lt_of_le_of_lt (measure_mono subset_closure) hbox.2.2.2.2.1.measure_lt_top

/-- A time-dependent gauge in `L^{3/2}(J)` lies in `L^{3/2}` of the space-time box. -/
theorem memLp_gauge_on_box {Ω : Set Vec3} {I : Set ℝ} {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) {c : ℝ → ℝ}
    (hc : MemLp c (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict J)) :
    MemLp (fun z : ParabolicPoint => c z.2) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have hfin : IsFiniteMeasure (volume.restrict Ω') := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact localBox_volume_lt_top hbox
  have h := hc.comp_snd (volume.restrict Ω')
  rw [Measure.prod_restrict] at h
  rw [spaceTimeSet]
  exact h

/-- A spatial partial derivative vanishes off the topological support. -/
theorem spatialPartial_eq_zero_off_tsupport {ψ : Vec3 × ℝ → ℝ}
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) (i : Fin 3) :
    spatialPartial ψ i z = 0 := by
  change (fderiv ℝ (fun x : Vec3 => ψ (x, z.2)) z.1) (basisVec i) = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hmap : Continuous (fun x : Vec3 => (x, z.2)) :=
    Continuous.prodMk continuous_id continuous_const
  have hev : (fun x : Vec3 => ψ (x, z.2)) =ᶠ[𝓝 z.1] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hopen] with x hx
    by_contra hne
    exact hx (subset_tsupport (f := ψ) (Function.mem_support.mpr hne))
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp


/-- The parabolic topology and the product topology have the same closed
supports: the identity is a homeomorphism between them. -/
theorem tsupport_parabolic_eq {V : Type} [Zero V] (f : Vec3 × ℝ → V) :
    tsupport (show ParabolicPoint → V from f) = tsupport f := by
  have hsupp : Function.support (show ParabolicPoint → V from f)
      = parabolicHomeomorph ⁻¹' (Function.support f) := rfl
  rw [tsupport, hsupp, ← parabolicHomeomorph.preimage_closure,
    parabolicHomeomorph_preimage, tsupport]

/-- Multiplying a space-time test function by a smooth time cutoff supported in
the time interval again gives a space-time test function. -/
private theorem timeMul_mem_spaceTimeTestFunction {Ω : Set Vec3} {I : Set ℝ}
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) :
    (fun z : Vec3 × ℝ => θ z.2 * ψ z) ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
  obtain ⟨hψd, hψc, hψΩ⟩ := hψ
  refine ⟨?_, ?_, ?_⟩
  · exact (hθ.comp (contDiff_snd (𝕜 := ℝ) (E := Vec3) (F := ℝ))).mul hψd
  · exact hψc.mul_left
  · exact (closure_mono (Function.support_mul_subset_right _ _)).trans hψΩ

/-- The spatial derivative of `θ(t)ψ(x,t)` splits off the time factor. -/
private theorem spatialPartial_timeMul (ψ : Vec3 × ℝ → ℝ) (θ : ℝ → ℝ)
    (i : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (fun w : Vec3 × ℝ => θ w.2 * ψ w) i z = θ z.2 * spatialPartial ψ i z := by
  change (fderiv ℝ (fun x : Vec3 => θ z.2 * ψ (x, z.2)) z.1) (basisVec i)
      = θ z.2 * (fderiv ℝ (fun x : Vec3 => ψ (x, z.2)) z.1) (basisVec i)
  by_cases hd : DifferentiableAt ℝ (fun x : Vec3 => ψ (x, z.2)) z.1
  · rw [fderiv_const_mul hd]
    simp
  · rw [fderiv_zero_of_not_differentiableAt hd]
    by_cases hθ0 : θ z.2 = 0
    · simp [hθ0]
    · rw [fderiv_zero_of_not_differentiableAt (fun hcon => hd ?_)]
      · simp
      · have := hcon.const_mul (θ z.2)⁻¹
        simpa [hθ0, inv_mul_cancel_left₀] using this



/-- The slice form of the divergence-free clause (S2) for a space-time test
function: for almost every time the spatial pairing of the slice `u(·,t)` with
`∇ψ(·,t)` vanishes. -/
private theorem slice_divfree_ae
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3} (hI : IsOpen I)
    (hS2 : ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun z => ∑ i, u z i * spatialPartial ψ i z) (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet Ω I, ∑ i, u z i * spatialPartial ψ i z = 0)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    ∀ᵐ t ∂volume.restrict I,
      ∫ x : Vec3, (∑ i, u (x, t) i * spatialPartial ψ i (x, t)) = 0 := by
  set h : Vec3 × ℝ → ℝ := fun z => ∑ i, u z i * spatialPartial ψ i z with hhdef
  set H : ℝ → ℝ := fun t => ∫ x : Vec3, h (x, t) with hHdef
  have hoff : ∀ z : Vec3 × ℝ, z ∉ spaceTimeSet Ω I → h z = 0 := by
    intro z hz
    have hz' : z ∉ tsupport ψ := fun hmem => hz (hψ.2.2 hmem)
    simp only [hhdef]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [spatialPartial_eq_zero_off_tsupport hz' i, mul_zero]
  have main : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
      Integrable (fun z : Vec3 × ℝ => θ z.2 * h z) volume ∧
        ∫ t : ℝ, θ t * H t = 0 := by
    intro θ hθ
    have hmem := timeMul_mem_spaceTimeTestFunction hψ hθ
    obtain ⟨hint, hzero⟩ := hS2 _ hmem
    have hgeq : (fun z : Vec3 × ℝ =>
        ∑ i, u z i * spatialPartial (fun w : Vec3 × ℝ => θ w.2 * ψ w) i z)
          = fun z : Vec3 × ℝ => θ z.2 * h z := by
      funext z
      simp only [hhdef, spatialPartial_timeMul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsupp : Function.support
        (fun z : ParabolicPoint =>
          ∑ i, u z i * spatialPartial (fun w : Vec3 × ℝ => θ w.2 * ψ w) i z)
        ⊆ tsupport (show ParabolicPoint → ℝ from fun w : Vec3 × ℝ => θ w.2 * ψ w) := by
      rw [tsupport_parabolic_eq]
      intro z hz
      by_contra hcon
      refine hz ?_
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [spatialPartial_eq_zero_off_tsupport hcon i, mul_zero]
    have hInt : Integrable (fun z : Vec3 × ℝ => θ z.2 * h z) volume := by
      rw [← hgeq]
      exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hint
    have hoff' : ∀ z : Vec3 × ℝ, z ∉ spaceTimeSet Ω I → θ z.2 * h z = 0 := by
      intro z hz
      rw [hoff z hz, mul_zero]
    have hcongr : ∫ z in spaceTimeSet Ω I, θ z.2 * h z
        = ∫ z in spaceTimeSet Ω I,
            ∑ i, u z i * spatialPartial (fun w : Vec3 × ℝ => θ w.2 * ψ w) i z :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => (congrFun hgeq z).symm))
    have hfull : ∫ z : Vec3 × ℝ, θ z.2 * h z = 0 := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hoff']
      exact hcongr.trans hzero
    have hInt' : Integrable (fun z : Vec3 × ℝ => θ z.2 * h z)
        ((volume : Measure Vec3).prod (volume : Measure ℝ)) := hInt
    have hFub : ∫ z : Vec3 × ℝ, θ z.2 * h z
        = ∫ t : ℝ, ∫ x : Vec3, θ t * h (x, t) :=
      integral_prod_symm (fun z : Vec3 × ℝ => θ z.2 * h z) hInt'
    have hinner : ∀ t : ℝ, ∫ x : Vec3, θ t * h (x, t) = θ t * H t := by
      intro t
      simp only [hHdef]
      exact integral_const_mul (θ t) (fun x : Vec3 => h (x, t))
    refine ⟨hInt, ?_⟩
    rw [← hfull, hFub]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun t => (hinner t).symm))
  have hHloc : LocallyIntegrableOn H I volume := by
    intro t₀ ht₀
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds ht₀)
    let cb : ContDiffBump t₀ :=
      ⟨ε / 4, ε / 2, by linarith only [hεpos], by linarith only [hεpos]⟩
    have hcbdiff : ContDiff ℝ (⊤ : ℕ∞) (⇑cb) := cb.contDiff
    obtain ⟨hcbInt, -⟩ := main (⇑cb) hcbdiff
    have hcbInt' : Integrable (fun z : Vec3 × ℝ => cb z.2 * h z)
        ((volume : Measure Vec3).prod (volume : Measure ℝ)) := hcbInt
    have hslice : Integrable (fun t : ℝ => ∫ x : Vec3, cb t * h (x, t)) volume :=
      hcbInt'.integral_prod_right
    refine ⟨ball t₀ (ε / 4), mem_nhdsWithin.mpr
      ⟨ball t₀ (ε / 4), isOpen_ball, mem_ball_self (by linarith only [hεpos]),
        fun y hy => hy.1⟩, ?_⟩
    refine (hslice.integrableOn (s := ball t₀ (ε / 4))).congr ?_
    filter_upwards [self_mem_ae_restrict (isOpen_ball (x := t₀) (ε := ε / 4)).measurableSet]
      with t ht
    have hone : cb t = 1 := cb.one_of_mem_closedBall (ball_subset_closedBall ht)
    rw [integral_const_mul, hone, one_mul]
  have hae := hI.ae_eq_zero_of_integral_contDiff_smul_eq_zero hHloc
    (fun θ hθ _ _ => by
      simpa only [smul_eq_mul] using (main θ hθ).2)
  exact (ae_restrict_iff' hI.measurableSet).mpr hae



/-- The spatial integral of a spatial partial derivative of a smooth compactly
supported space-time function vanishes at every fixed time. -/
private theorem integral_slice_spatialPartial_eq_zero {G : Vec3 × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) (i : Fin 3) (t : ℝ) :
    ∫ x : Vec3, spatialPartial G i (x, t) = 0 := by
  classical
  set g : Vec3 → ℝ := fun x => G (x, t) with hgdef
  have hgdiff : ContDiff ℝ (⊤ : ℕ∞) g :=
    hG.comp ((contDiff_id (𝕜 := ℝ) (E := Vec3)).prodMk contDiff_const)
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (hGc.isCompact.image continuous_fst) ?_
    intro x hx
    have hx' : (x, t) ∉ tsupport G := by
      intro hmem
      exact hx ⟨(x, t), hmem, rfl⟩
    show G (x, t) = 0
    exact image_eq_zero_of_notMem_tsupport hx'
  have hgD : Differentiable ℝ g := hgdiff.differentiable (by simp)
  have hcont : Continuous (fun x : Vec3 => (fderiv ℝ g x) (basisVec i)) :=
    (hgdiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun x : Vec3 => (fderiv ℝ g x) (basisVec i)) :=
    hgcs.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hint : Integrable (fun x : Vec3 => (fderiv ℝ g x) (basisVec i)) :=
    hcont.integrable_of_hasCompactSupport hcs
  have hgint : Integrable g := hgdiff.continuous.integrable_of_hasCompactSupport hgcs
  have hf'g : Integrable
      (fun x : Vec3 => fderiv ℝ (fun _ : Vec3 => (1 : ℝ)) x (basisVec i) * g x) := by
    simp
  have hfg' : Integrable
      (fun x : Vec3 => (1 : ℝ) * fderiv ℝ g x (basisVec i)) := by
    simpa using hint
  have hfg : Integrable (fun x : Vec3 => (1 : ℝ) * g x) := by simpa using hgint
  have hf : ∀ x ∈ tsupport g, DifferentiableAt ℝ (fun _ : Vec3 => (1 : ℝ)) x :=
    fun _ _ => differentiableAt_const (1 : ℝ)
  have hg : ∀ x ∈ tsupport (fun _ : Vec3 => (1 : ℝ)), DifferentiableAt ℝ g x :=
    fun x _ => hgD x
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Vec3)) (f := fun _ : Vec3 => (1 : ℝ)) (g := g)
    (v := basisVec i) hf'g hfg' hfg hf hg
  have hRHS : (∫ x : Vec3,
      fderiv ℝ (fun _ : Vec3 => (1 : ℝ)) x (basisVec i) * g x) = 0 := by simp
  have hLHS : (∫ x : Vec3, (1 : ℝ) * fderiv ℝ g x (basisVec i)) = 0 := by
    rw [hIBP, hRHS, neg_zero]
  simpa only [one_mul, spatialPartial, hgdef] using hLHS

/-- The elementary bound `x ≤ 1 + x²` in `ℝ≥0∞`. -/
private theorem enorm_le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ (2 : ℝ) := by
  rcases le_total x 1 with hx | hx
  · exact le_trans hx le_self_add
  · refine le_trans ?_ le_add_self
    calc x = x ^ (1 : ℝ) := (ENNReal.rpow_one x).symm
      _ ≤ x ^ (2 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hx (by norm_num)

/-- On a local box the velocity has a uniform `L¹` bound on almost every time
slice: the energy clause bounds the slice `L²` norms uniformly, and `x ≤ 1 + x²`
converts this into an `L¹` bound. -/
private theorem slice_velocity_lintegral_le
    {Ω' : Set Vec3} {J : Set ℝ} {u : ParabolicPoint → Vec3} :
    ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in Ω', ‖u (x, t)‖ₑ) ≤ volume Ω' +
        essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict J) := by
  filter_upwards [ENNReal.ae_le_essSup
    (μ := volume.restrict J) (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))] with t ht
  calc (∫⁻ x in Ω', ‖u (x, t)‖ₑ)
      ≤ ∫⁻ x in Ω', (1 + ‖u (x, t)‖ₑ ^ (2 : ℝ)) :=
        lintegral_mono fun x => enorm_le_one_add_sq _
    _ = volume Ω' + ∫⁻ x in Ω', ‖u (x, t)‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_add_left measurable_const, setLIntegral_one]
    _ ≤ volume Ω' + essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
          (volume.restrict J) := by
        exact add_le_add le_rfl ht

/-- Tonelli on a local space-time box, in the time-outer order. -/
private theorem lintegral_box_eq {Ω' : Set Vec3} {J : Set ℝ} {F : Vec3 × ℝ → ℝ≥0∞}
    (hF : AEMeasurable F (((volume : Measure Vec3).restrict Ω').prod
      (volume.restrict J))) :
    ∫⁻ z in spaceTimeSet Ω' J, F z = ∫⁻ t in J, ∫⁻ x in Ω', F (x, t) := by
  have hmeq : (volume : Measure ParabolicPoint).restrict (spaceTimeSet Ω' J)
      = ((volume : Measure Vec3).restrict Ω').prod (volume.restrict J) := by
    rw [spaceTimeSet, Measure.prod_restrict]
    rfl
  rw [show (∫⁻ z in spaceTimeSet Ω' J, F z)
      = ∫⁻ z, F z ∂((((volume : Measure Vec3).restrict Ω')).prod
        (volume.restrict J)) from by rw [← hmeq]; rfl]
  exact lintegral_prod_symm _ hF

/-- A field dominated by the velocity pairs integrably with the time gauge on a
local box: Tonelli, the uniform slice bound of `slice_velocity_lintegral_le`
and `c ∈ L¹(J)`. -/
private theorem integrableOn_gauge_mul_of_velocity_bound
    {Ω' : Set Vec3} {J : Set ℝ} {c : ℝ → ℝ} {u : ParabolicPoint → Vec3}
    {g : Vec3 × ℝ → ℝ} {K : ℝ}
    (hΩ'fin : volume Ω' < ∞)
    (hcint : (∫⁻ t in J, ‖c t‖ₑ) < ∞)
    (hE : essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict J) < ∞)
    (hbound : ∀ z : Vec3 × ℝ, ‖g z‖ₑ ≤ ENNReal.ofReal K * ‖u z‖ₑ)
    (hcmeas : AEMeasurable (fun z : Vec3 × ℝ => ‖c z.2‖ₑ)
      (volume.restrict (spaceTimeSet Ω' J)))
    (humeas : AEMeasurable (fun z : Vec3 × ℝ => ‖u z‖ₑ)
      (volume.restrict (spaceTimeSet Ω' J)))
    (hmeasCG : AEStronglyMeasurable (fun z : Vec3 × ℝ => c z.2 * g z)
      (volume.restrict (spaceTimeSet Ω' J))) :
    IntegrableOn (fun z : Vec3 × ℝ => c z.2 * g z) (spaceTimeSet Ω' J) volume := by
  refine ⟨hmeasCG, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  set B : ℝ≥0∞ := volume Ω' +
    essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict J) with hB
  have hBtop : B ≠ ∞ := by
    rw [hB]
    exact (ENNReal.add_lt_top.mpr ⟨hΩ'fin, hE⟩).ne
  have hprodmeas : AEMeasurable
      (fun z : Vec3 × ℝ => ‖c z.2‖ₑ * (ENNReal.ofReal K * ‖u z‖ₑ))
      (volume.restrict (spaceTimeSet Ω' J)) :=
    hcmeas.mul (humeas.const_mul _)
  have hprodmeas' : AEMeasurable
      (fun z : Vec3 × ℝ => ‖c z.2‖ₑ * (ENNReal.ofReal K * ‖u z‖ₑ))
      (((volume : Measure Vec3).restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact hprodmeas
  have hslice := slice_velocity_lintegral_le (Ω' := Ω') (J := J) (u := u)
  calc (∫⁻ z in spaceTimeSet Ω' J, ‖c z.2 * g z‖ₑ)
      = ∫⁻ z in spaceTimeSet Ω' J, ‖c z.2‖ₑ * ‖g z‖ₑ := by
        refine lintegral_congr fun z => ?_
        rw [enorm_mul]
    _ ≤ ∫⁻ z in spaceTimeSet Ω' J, ‖c z.2‖ₑ * (ENNReal.ofReal K * ‖u z‖ₑ) := by
        refine lintegral_mono fun z => ?_
        exact mul_le_mul' le_rfl (hbound z)
    _ = ∫⁻ t in J, ∫⁻ x in Ω', ‖c t‖ₑ * (ENNReal.ofReal K * ‖u (x, t)‖ₑ) := by
        exact lintegral_box_eq hprodmeas'
    _ = ∫⁻ t in J, (‖c t‖ₑ * ENNReal.ofReal K) * ∫⁻ x in Ω', ‖u (x, t)‖ₑ := by
        refine lintegral_congr fun t => ?_
        rw [← lintegral_const_mul' _ _ (by finiteness)]
        refine lintegral_congr fun x => ?_
        ring
    _ ≤ ∫⁻ t in J, (‖c t‖ₑ * ENNReal.ofReal K) * B := by
        refine lintegral_mono_ae ?_
        filter_upwards [hslice] with t ht
        exact mul_le_mul' le_rfl ht
    _ = ∫⁻ t in J, (ENNReal.ofReal K * B) * ‖c t‖ₑ := by
        refine lintegral_congr fun t => ?_
        ring
    _ = (ENNReal.ofReal K * B) * ∫⁻ t in J, ‖c t‖ₑ :=
        lintegral_const_mul' _ _ (by finiteness)
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBtop.lt_top) hcint

/-- The support of a spatial partial derivative lies in the support of the
function. -/
theorem tsupport_spatialPartial_subset {ψ : Vec3 × ℝ → ℝ} (i : Fin 3) :
    tsupport (fun z : Vec3 × ℝ => spatialPartial ψ i z) ⊆ tsupport ψ := by
  refine closure_minimal ?_ (isClosed_tsupport ψ)
  intro z hz
  by_contra hcon
  exact hz (spatialPartial_eq_zero_off_tsupport hcon i)

/-- A time partial derivative vanishes off the topological support. -/
theorem timePartial_eq_zero_off_tsupport {ψ : Vec3 × ℝ → ℝ}
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) :
    timePartial ψ z = 0 := by
  change (fderiv ℝ (fun s : ℝ => ψ (z.1, s)) z.2) 1 = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hmap : Continuous (fun s : ℝ => (z.1, s)) :=
    Continuous.prodMk continuous_const continuous_id
  have hev : (fun s : ℝ => ψ (z.1, s)) =ᶠ[𝓝 z.2] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hopen] with s hs
    by_contra hne
    exact hs (subset_tsupport (f := ψ) (Function.mem_support.mpr hne))
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

/-- A component of a vector-valued test function has support inside the support
of the test function. -/
theorem tsupport_component_subset {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {ι : Type} (φ : Vec3 × ℝ → ι → ℝ) (i : ι)
    (hzero : ∀ z, φ z = 0 → φ z i = 0) :
    tsupport (fun w => φ w i) ⊆ tsupport φ := by
  refine closure_mono ?_
  intro z hz
  by_contra hcon
  rw [Function.mem_support] at hz
  exact hz (hzero z (not_not.mp hcon))

/-- The pairing of the time gauge with a field whose spatial slices integrate to
zero vanishes. -/
private theorem gauge_pairing_eq_zero {c : ℝ → ℝ} {h : Vec3 × ℝ → ℝ}
    (hInt : Integrable (fun z : Vec3 × ℝ => c z.2 * h z) volume)
    (hslice : ∀ᵐ t : ℝ, ∫ x : Vec3, h (x, t) = 0) :
    ∫ z : Vec3 × ℝ, c z.2 * h z = 0 := by
  have hInt' : Integrable (fun z : Vec3 × ℝ => c z.2 * h z)
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := hInt
  have hzero : (fun t : ℝ => ∫ x : Vec3, c t * h (x, t)) =ᵐ[volume] fun _ => (0 : ℝ) := by
    filter_upwards [hslice] with t ht
    rw [integral_const_mul, ht, mul_zero]
  calc ∫ z : Vec3 × ℝ, c z.2 * h z
      = ∫ t : ℝ, ∫ x : Vec3, c t * h (x, t) :=
        integral_prod_symm (fun z : Vec3 × ℝ => c z.2 * h z) hInt'
    _ = 0 := by rw [integral_congr_ae hzero, integral_zero]

/-- The spatial partial derivative is the full space-time derivative in a
spatial direction. -/
private theorem fderiv_inl_eq_spatialPartial {G : Vec3 × ℝ → ℝ}
    (hG : Differentiable ℝ G) (i : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial G i z = (fderiv ℝ G z) (basisVec i, 0) := by
  change (fderiv ℝ (fun x : Vec3 => G (x, z.2)) z.1) (basisVec i) = _
  have hGd : HasFDerivAt G (fderiv ℝ G z) z := (hG z).hasFDerivAt
  have hlin : HasFDerivAt (fun x : Vec3 => (x, z.2))
      (ContinuousLinearMap.inl ℝ Vec3 ℝ) z.1 := hasFDerivAt_prodMk_left z.1 z.2
  have hcomp := hGd.comp z.1 hlin
  have hfd : fderiv ℝ (fun x : Vec3 => G (x, z.2)) z.1 =
      (fderiv ℝ G z).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ) := hcomp.fderiv
  rw [hfd]
  simp

/-- A spatial partial derivative of a smooth function is continuous. -/
private theorem continuous_spatialPartial {G : Vec3 × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (i : Fin 3) :
    Continuous (fun z : Vec3 × ℝ => spatialPartial G i z) := by
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hcont : Continuous (fun z : Vec3 × ℝ => (fderiv ℝ G z) (basisVec i, 0)) :=
    (hG.continuous_fderiv (by simp)).clm_apply continuous_const
  exact hcont.congr (fun z => (fderiv_inl_eq_spatialPartial hGd i z).symm)

/-- Compactness transfers from the product topology to the parabolic topology. -/
private theorem isCompact_parabolic_of_prod {K : Set (Vec3 × ℝ)} (hK : IsCompact K) :
    IsCompact (show Set ParabolicPoint from K) := by
  rw [← parabolicHomeomorph_preimage K]
  exact parabolicHomeomorph.isCompact_preimage.mpr hK

/-- A bounded field pairs integrably with the time gauge on a local box. -/
private theorem integrableOn_gauge_mul_of_bounded
    {Ω' : Set Vec3} {J : Set ℝ} {c : ℝ → ℝ} {g : Vec3 × ℝ → ℝ} {K : ℝ}
    (hΩ'fin : volume Ω' < ∞)
    (hcint : (∫⁻ t in J, ‖c t‖ₑ) < ∞)
    (hbound : ∀ z : Vec3 × ℝ, ‖g z‖ₑ ≤ ENNReal.ofReal K)
    (hcmeas : AEMeasurable (fun z : Vec3 × ℝ => ‖c z.2‖ₑ)
      (volume.restrict (spaceTimeSet Ω' J)))
    (hmeasCG : AEStronglyMeasurable (fun z : Vec3 × ℝ => c z.2 * g z)
      (volume.restrict (spaceTimeSet Ω' J))) :
    IntegrableOn (fun z : Vec3 × ℝ => c z.2 * g z) (spaceTimeSet Ω' J) volume := by
  refine ⟨hmeasCG, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hprodmeas' : AEMeasurable
      (fun z : Vec3 × ℝ => ‖c z.2‖ₑ * ENNReal.ofReal K)
      (((volume : Measure Vec3).restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact hcmeas.mul_const _
  calc (∫⁻ z in spaceTimeSet Ω' J, ‖c z.2 * g z‖ₑ)
      = ∫⁻ z in spaceTimeSet Ω' J, ‖c z.2‖ₑ * ‖g z‖ₑ := by
        refine lintegral_congr fun z => ?_
        rw [enorm_mul]
    _ ≤ ∫⁻ z in spaceTimeSet Ω' J, ‖c z.2‖ₑ * ENNReal.ofReal K := by
        refine lintegral_mono fun z => ?_
        exact mul_le_mul' le_rfl (hbound z)
    _ = ∫⁻ t in J, ∫⁻ _x in Ω', ‖c t‖ₑ * ENNReal.ofReal K :=
        lintegral_box_eq hprodmeas'
    _ = ∫⁻ t in J, (ENNReal.ofReal K * volume Ω') * ‖c t‖ₑ := by
        refine lintegral_congr fun t => ?_
        rw [setLIntegral_const]
        ring
    _ = (ENNReal.ofReal K * volume Ω') * ∫⁻ t in J, ‖c t‖ₑ :=
        lintegral_const_mul' _ _ (by finiteness)
    _ < ∞ := ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΩ'fin) hcint



/-- The elementary bound `x ≤ 1 + x^r` for `r ≥ 1` in `ℝ≥0∞`. -/
private theorem enorm_le_one_add_rpow {r : ℝ} (hr : 1 ≤ r) (x : ℝ≥0∞) :
    x ≤ 1 + x ^ r := by
  rcases le_total x 1 with hx | hx
  · exact le_trans hx le_self_add
  · refine le_trans ?_ le_add_self
    calc x = x ^ (1 : ℝ) := (ENNReal.rpow_one x).symm
      _ ≤ x ^ r := ENNReal.rpow_le_rpow_of_exponent_le hx hr

/-- An `L^{3/2}` gauge on a bounded time interval is integrable there. -/
private theorem lintegral_enorm_gauge_lt_top {J : Set ℝ} {c : ℝ → ℝ}
    (hJ : volume J < ∞)
    (hc : MemLp c (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict J)) :
    (∫⁻ t in J, ‖c t‖ₑ) < ∞ := by
  have hpow : (∫⁻ t in J, ‖c t‖ₑ ^ ((ENNReal.ofReal (3 / 2 : ℝ)).toReal)) < ∞ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      norm_num) (by finiteness) hc
  have htoReal : (ENNReal.ofReal (3 / 2 : ℝ)).toReal = (3 / 2 : ℝ) := by
    rw [ENNReal.toReal_ofReal (by norm_num)]
  rw [htoReal] at hpow
  calc (∫⁻ t in J, ‖c t‖ₑ)
      ≤ ∫⁻ t in J, (1 + ‖c t‖ₑ ^ (3 / 2 : ℝ)) :=
        lintegral_mono fun t => enorm_le_one_add_rpow (by norm_num) _
    _ = volume J + ∫⁻ t in J, ‖c t‖ₑ ^ (3 / 2 : ℝ) := by
        rw [lintegral_add_left measurable_const, setLIntegral_one]
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hJ, hpow⟩

/-- The gauge pairs integrably with the divergence of a vector test function,
and the pairing vanishes. -/
theorem gauge_divergence_pairing
    {Ω : Set Vec3} {I : Set ℝ} {c : ℝ → ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hIord : I.OrdConnected)
    (hc : ∀ Ω' J, localBox Ω I Ω' J →
      MemLp c (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict J))
    {φ : Vec3 × ℝ → Vec3} (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I) :
    Integrable
        (fun z : Vec3 × ℝ => c z.2 * ∑ i, spatialPartial (fun w => φ w i) i z) volume ∧
      ∫ z : Vec3 × ℝ, c z.2 * ∑ i, spatialPartial (fun w => φ w i) i z = 0 := by
  classical
  obtain ⟨hφd, hφc, hφΩ⟩ := hφ
  have hcomp : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => φ w i) := fun i =>
    (contDiff_apply ℝ ℝ i).comp hφd
  have hcompsupp : ∀ i : Fin 3, tsupport (fun w : Vec3 × ℝ => φ w i) ⊆ tsupport φ := by
    intro i
    refine tsupport_component_subset (V := Vec3) (ι := Fin 3) φ i ?_
    intro z hz
    rw [hz]
    rfl
  have hcompc : ∀ i : Fin 3, HasCompactSupport (fun w : Vec3 × ℝ => φ w i) := fun i =>
    hφc.isCompact.of_isClosed_subset (isClosed_tsupport _) (hcompsupp i)
  set D : Vec3 × ℝ → ℝ := fun z => ∑ i, spatialPartial (fun w => φ w i) i z with hD
  have hDcont : Continuous D :=
    continuous_finsetSum _ fun i _ => continuous_spatialPartial (hcomp i) i
  have hDzero : ∀ z ∉ tsupport φ, D z = 0 := by
    intro z hz
    refine Finset.sum_eq_zero fun i _ => ?_
    exact spatialPartial_eq_zero_off_tsupport (fun hmem => hz (hcompsupp i hmem)) i
  obtain ⟨K, hK⟩ := hφc.isCompact.exists_bound_of_continuousOn hDcont.continuousOn
  have hDbdd : ∀ z : Vec3 × ℝ, ‖D z‖ₑ ≤ ENNReal.ofReal (max K 0) := by
    intro z
    by_cases hz : z ∈ tsupport φ
    · rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal ((hK z hz).trans (le_max_left _ _))
    · rw [hDzero z hz]
      simp
  obtain ⟨Ω', J, hbox, hsub⟩ := caccioppoli_localBox_of_compact_subset hΩ hI hIord
    (isCompact_parabolic_of_prod hφc.isCompact) hφΩ
  have hcbox := memLp_gauge_on_box hbox (hc Ω' J hbox)
  have hcJ : (∫⁻ t in J, ‖c t‖ₑ) < ∞ :=
    lintegral_enorm_gauge_lt_top (localBox_time_volume_lt_top hbox) (hc Ω' J hbox)
  have hmeasCG : AEStronglyMeasurable (fun z : Vec3 × ℝ => c z.2 * D z)
      (volume.restrict (spaceTimeSet Ω' J)) :=
    hcbox.aestronglyMeasurable.mul hDcont.aestronglyMeasurable
  have hIntBox : IntegrableOn (fun z : Vec3 × ℝ => c z.2 * D z)
      (spaceTimeSet Ω' J) volume :=
    integrableOn_gauge_mul_of_bounded (localBox_volume_lt_top hbox) hcJ hDbdd
      hcbox.aestronglyMeasurable.enorm hmeasCG
  have hsupp : Function.support (fun z : Vec3 × ℝ => c z.2 * D z) ⊆
      spaceTimeSet Ω' J := by
    intro z hz
    by_contra hcon
    refine hz ?_
    have hz' : z ∉ tsupport φ := fun hmem => hcon (hsub hmem)
    show c z.2 * D z = 0
    rw [hDzero z hz', mul_zero]
  have hInt : Integrable (fun z : Vec3 × ℝ => c z.2 * D z) volume :=
    (integrableOn_iff_integrable_of_support_subset hsupp).mp hIntBox
  have hslice : ∀ t : ℝ, ∫ x : Vec3, D (x, t) = 0 := by
    intro t
    have hintegrable : ∀ i : Fin 3,
        Integrable (fun x : Vec3 => spatialPartial (fun w => φ w i) i (x, t)) := by
      intro i
      have hcontx : Continuous
          (fun x : Vec3 => spatialPartial (fun w : Vec3 × ℝ => φ w i) i (x, t)) :=
        (continuous_spatialPartial (hcomp i) i).comp
          (Continuous.prodMk continuous_id continuous_const)
      refine hcontx.integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.intro ((hφc.isCompact.image continuous_fst)) ?_
      intro x hx
      have hx' : (x, t) ∉ tsupport φ := fun hmem => hx ⟨(x, t), hmem, rfl⟩
      exact spatialPartial_eq_zero_off_tsupport
        (fun hmem => hx' (hcompsupp i hmem)) i
    rw [hD]
    rw [integral_finsetSum _ (fun i _ => hintegrable i)]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact integral_slice_spatialPartial_eq_zero (hcomp i) (hcompc i) i t
  exact ⟨hInt, gauge_pairing_eq_zero hInt (Filter.Eventually.of_forall hslice)⟩

/-- The gauge pairs integrably with the velocity paired against a spatial
gradient, and the pairing vanishes. -/
theorem gauge_velocity_pairing
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (hIord : I.OrdConnected)
    (hc : ∀ Ω' J, localBox Ω I Ω' J →
      MemLp c (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict J))
    (humeas : ∀ Ω' J, localBox Ω I Ω' J →
      AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J)))
    (hessSup : ∀ Ω' J, localBox Ω I Ω' J →
      essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict J) < ∞)
    (hS2 : ∀ χ : Vec3 × ℝ → ℝ, χ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun z => ∑ i, u z i * spatialPartial χ i z) (tsupport χ) volume ∧
      ∫ z in spaceTimeSet Ω I, ∑ i, u z i * spatialPartial χ i z = 0)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    Integrable (fun z : Vec3 × ℝ => c z.2 * ∑ i, u z i * spatialPartial ψ i z) volume ∧
      ∫ z : Vec3 × ℝ, c z.2 * ∑ i, u z i * spatialPartial ψ i z = 0 := by
  classical
  obtain ⟨hψd, hψc, hψΩ⟩ := hψ
  set g : Vec3 × ℝ → ℝ := fun z => ∑ i, u z i * spatialPartial ψ i z with hg
  have hgzero : ∀ z ∉ tsupport ψ, g z = 0 := by
    intro z hz
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [spatialPartial_eq_zero_off_tsupport hz i, mul_zero]
  choose Ki hKi using fun i : Fin 3 =>
    hψc.isCompact.exists_bound_of_continuousOn
      (continuous_spatialPartial hψd i).continuousOn
  set K : ℝ := max 0 (Finset.univ.sup' ⟨0, Finset.mem_univ 0⟩ Ki) with hK
  have hK0 : 0 ≤ K := le_max_left _ _
  have hKi' : ∀ i : Fin 3, ∀ z ∈ tsupport ψ, ‖spatialPartial ψ i z‖ ≤ K :=
    fun i z hz => (hKi i z hz).trans
      ((Finset.le_sup' Ki (Finset.mem_univ i)).trans (le_max_right _ _))
  have hgbdd : ∀ z : Vec3 × ℝ, ‖g z‖ₑ ≤ ENNReal.ofReal (3 * K) * ‖u z‖ₑ := by
    intro z
    by_cases hz : z ∈ tsupport ψ
    · have habs : |g z| ≤ 3 * K * ‖u z‖ := by
        have hterm : ∀ i : Fin 3, |u z i * spatialPartial ψ i z| ≤ K * ‖u z‖ := by
          intro i
          rw [abs_mul]
          have h1 : |u z i| ≤ ‖u z‖ := by
            simpa [Real.norm_eq_abs] using norm_le_pi_norm (u z) i
          have h2 : |spatialPartial ψ i z| ≤ K := by
            simpa [Real.norm_eq_abs] using hKi' i z hz
          calc |u z i| * |spatialPartial ψ i z| ≤ ‖u z‖ * K :=
                mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
            _ = K * ‖u z‖ := by ring
        calc |g z| ≤ ∑ i, |u z i * spatialPartial ψ i z| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin 3, K * ‖u z‖ := Finset.sum_le_sum fun i _ => hterm i
          _ = 3 * K * ‖u z‖ := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              simp only [nsmul_eq_mul, Nat.cast_ofNat]
              ring
      calc ‖g z‖ₑ = ENNReal.ofReal |g z| := Real.enorm_eq_ofReal_abs _
        _ ≤ ENNReal.ofReal (3 * K * ‖u z‖) := ENNReal.ofReal_le_ofReal habs
        _ = ENNReal.ofReal (3 * K) * ENNReal.ofReal ‖u z‖ := by
            rw [← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal (3 * K) * ‖u z‖ₑ := by
            rw [← Real.enorm_eq_ofReal (norm_nonneg _), enorm_norm]
    · rw [hgzero z hz]
      simp
  obtain ⟨Ω', J, hbox, hsub⟩ := caccioppoli_localBox_of_compact_subset hΩ hI hIord
    (isCompact_parabolic_of_prod hψc.isCompact) hψΩ
  have hcbox := memLp_gauge_on_box hbox (hc Ω' J hbox)
  have hcJ : (∫⁻ t in J, ‖c t‖ₑ) < ∞ :=
    lintegral_enorm_gauge_lt_top (localBox_time_volume_lt_top hbox) (hc Ω' J hbox)
  have hu := humeas Ω' J hbox
  have hgterm : ∀ i : Fin 3, AEStronglyMeasurable
      (fun z : Vec3 × ℝ => u z i * spatialPartial ψ i z)
      (volume.restrict (spaceTimeSet Ω' J)) := fun i =>
    ((continuous_apply i).comp_aestronglyMeasurable hu).mul
      (continuous_spatialPartial hψd i).aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable g (volume.restrict (spaceTimeSet Ω' J)) := by
    simp only [hg, Fin.sum_univ_three]
    exact ((hgterm 0).add (hgterm 1)).add (hgterm 2)
  have hmeasCG : AEStronglyMeasurable (fun z : Vec3 × ℝ => c z.2 * g z)
      (volume.restrict (spaceTimeSet Ω' J)) :=
    hcbox.aestronglyMeasurable.mul hgmeas
  have hIntBox : IntegrableOn (fun z : Vec3 × ℝ => c z.2 * g z)
      (spaceTimeSet Ω' J) volume :=
    integrableOn_gauge_mul_of_velocity_bound (localBox_volume_lt_top hbox) hcJ
      (hessSup Ω' J hbox) hgbdd hcbox.aestronglyMeasurable.enorm hu.enorm hmeasCG
  have hsupp : Function.support (fun z : Vec3 × ℝ => c z.2 * g z) ⊆
      spaceTimeSet Ω' J := by
    intro z hz
    by_contra hcon
    refine hz ?_
    have hz' : z ∉ tsupport ψ := fun hmem => hcon (hsub hmem)
    show c z.2 * g z = 0
    rw [hgzero z hz', mul_zero]
  have hInt : Integrable (fun z : Vec3 × ℝ => c z.2 * g z) volume :=
    (integrableOn_iff_integrable_of_support_subset hsupp).mp hIntBox
  have hslice : ∀ᵐ t : ℝ, ∫ x : Vec3, g (x, t) = 0 := by
    have h1 := (ae_restrict_iff' hI.measurableSet).1
      (slice_divfree_ae hI hS2 ⟨hψd, hψc, hψΩ⟩)
    filter_upwards [h1] with t ht
    by_cases htI : t ∈ I
    · exact ht htI
    · have hzero : ∀ x : Vec3, g (x, t) = 0 := by
        intro x
        refine hgzero (x, t) fun hmem => ?_
        exact htI (hψΩ hmem).2
      simp only [hzero, integral_zero]
  exact ⟨hInt, gauge_pairing_eq_zero hInt hslice⟩

end CKN
