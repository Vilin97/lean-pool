/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.LocalizedWeakJetFourier
public import LeanPool.PoincareGeometry.AlmostSchur.LocalizedWeakJetIdentities
public import LeanPool.PoincareGeometry.AlmostSchur.WeakJetRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.CutoffPlateau
public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Approximation
public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Kernels
public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.TranslationIntegral
public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # Strong graph approximation for localized weak jets

This file is the analytic bridge from a localized weak first-order identity to
the closure of the genuine compactly supported `C¹` graph.  The target is the
ambient graph (`Set.univ`); this is the form used by the local quotient
estimate, whose support control is supplied separately by the cutoff.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff Convolution Pointwise
namespace AlmostSchur

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

-- The Euclidean translation API is specialized to the canonical Borel
-- measurable structure.  Use the same local instance here so that its `L²`
-- type and the ambient `volume` in this file are definitionally aligned.
local instance weakH1GraphClosureMeasurableSpace : MeasurableSpace E := borel E
local instance weakH1GraphClosureBorelSpace : BorelSpace E := ⟨rfl⟩
local instance weakH1GraphClosureOpensMeasurableSpace : OpensMeasurableSpace E := by
  infer_instance
local instance weakH1GraphClosureMeasurableAdd : MeasurableAdd E := by
  infer_instance

private lemma tendsto_translateL2_zero
    (F : E →₂[(volume : Measure E)] ℝ) :
    Tendsto (fun t : E =>
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.translateL2
        (μ := (volume : Measure E)) t F) (𝓝 (0 : E)) (𝓝 F) := by
  let g : E → C(E, E) := fun t => ContinuousMap.addRight t
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : E × E => p.2 + p.1)
    exact continuous_snd.add continuous_fst
  have hmp : ∀ t : E,
      MeasurePreserving (g t) (volume : Measure E) (volume : Measure E) := by
    intro t
    exact MeasureTheory.measurePreserving_add_right (μ := (volume : Measure E)) t
  have hcomp : Continuous (fun t : E =>
      MeasureTheory.Lp.compMeasurePreserving (g t) (hmp t) F) :=
    (continuous_const : Continuous (fun _ : E => F)).compMeasurePreservingLp
      hg hmp (by norm_num)
  have hcomp0 :
      MeasureTheory.Lp.compMeasurePreserving (g 0) (hmp 0) F = F := by
    apply MeasureTheory.Lp.ext
    filter_upwards [MeasureTheory.Lp.coeFn_compMeasurePreserving F (hmp 0)] with x hx
    simpa [g, Function.comp_def] using hx
  have htrans (t : E) :
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.translateL2
          (μ := (volume : Measure E)) t F =
        MeasureTheory.Lp.compMeasurePreserving (g t) (hmp t) F := by
    apply MeasureTheory.Lp.ext
    filter_upwards [
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.translateL2_ae_eq
        (μ := (volume : Measure E)) t F,
      MeasureTheory.Lp.coeFn_compMeasurePreserving F (hmp t)] with x hx ht
    have ht' :
        (MeasureTheory.Lp.compMeasurePreserving (g t) (hmp t) F : E → ℝ) x =
          (F : E → ℝ) (x + t) := by
      simpa [g, Function.comp_def] using ht
    exact hx.trans ht'.symm
  have htransfun :
      (fun t : E =>
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.translateL2
          (μ := (volume : Measure E)) t F) =
      (fun t : E => MeasureTheory.Lp.compMeasurePreserving (g t) (hmp t) F) :=
    funext htrans
  have hlim : Tendsto (fun t : E =>
      MeasureTheory.Lp.compMeasurePreserving (g t) (hmp t) F) (𝓝 (0 : E))
        (𝓝 (MeasureTheory.Lp.compMeasurePreserving (g 0) (hmp 0) F)) :=
    hcomp.continuousAt
  rw [hcomp0] at hlim
  rw [htransfun]
  exact hlim

private lemma extendByZeroL2_eq_toLp_of_support
    {S : Set E} (hS : IsCompact S) (f : E → ℝ)
    (hf : MemLp f 2 (volume : Measure E)) (hsupp : Function.support f ⊆ S) :
    extendByZeroL2 (E := E) (K := S) hS.measurableSet ((hf.restrict S).toLp f) = hf.toLp f := by
  apply MeasureTheory.Lp.ext
  have hrestrict :
      ((hf.restrict S).toLp f : E → ℝ) =ᵐ[(volume : Measure E).restrict S] f :=
    (hf.restrict S).coeFn_toLp
  have hext :
      (extendByZeroL2 (E := E) (K := S) hS.measurableSet ((hf.restrict S).toLp f) : E → ℝ) =ᵐ[volume]
        extendByZeroFun (E := E) (K := S) ((hf.restrict S).toLp f) :=
    extendByZeroL2_ae_eq (E := E) (K := S) hS.measurableSet ((hf.restrict S).toLp f)
  have hSmeas : MeasurableSet S := hS.measurableSet
  have hrestrict' : ∀ᵐ x : E ∂(volume : Measure E),
      x ∈ S → ((hf.restrict S).toLp f : E → ℝ) x = f x :=
    (MeasureTheory.ae_restrict_iff' hSmeas).1 hrestrict
  have hfull : ∀ᵐ x : E ∂(volume : Measure E),
      (hf.toLp f : E → ℝ) x = f x := hf.coeFn_toLp
  filter_upwards [hext, hrestrict', hfull] with x hx hfx hff
  by_cases hxs : x ∈ S
  · rw [hx]
    simp only [extendByZeroFun, Set.indicator_of_mem hxs]
    exact (hfx hxs).trans hff.symm
  · rw [hx]
    simp only [extendByZeroFun, Set.indicator, hxs, ↓reduceIte]
    by_contra hne
    apply hxs
    apply hsupp
    intro hzero
    apply hne
    rw [hff, hzero]

private theorem exists_contDiff_kernel_tsupport_subset_ball_integral_eq_one
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
        tsupport ψ ⊆ Metric.ball (0 : E) δ := by
  classical
  have hs : (Metric.ball (0 : E) δ) ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hδ
  rcases exists_contDiff_tsupport_subset (n := ⊤)
    (E := E) (s := Metric.ball (0 : E) δ) (x := (0 : E)) hs with
    ⟨f, hf_tsupp, hf_cs, hf_smooth, hf_range, hf0⟩
  have hf_cont : Continuous f := hf_smooth.continuous
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact (hf_range ⟨x, rfl⟩).1
  have hf0_ne : f (0 : E) ≠ 0 := by simp [hf0]
  have hIpos : 0 < ∫ x, f x ∂(volume : Measure E) := by
    simpa using!
      (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure E))
        hf_cont hf_cs hf_nonneg hf0_ne)
  set I : ℝ := ∫ x, f x ∂(volume : Measure E)
  have hI0 : I ≠ 0 := ne_of_gt hIpos
  have hIpos' : 0 < I := by simpa [I] using hIpos
  let ψ : E → ℝ := fun x => I⁻¹ * f x
  have hψsmooth : ContDiff ℝ ∞ ψ := by
    simpa [ψ] using (contDiff_const.mul hf_smooth)
  have hψcs : HasCompactSupport ψ := by
    rw [show ψ = (fun _x : E => I⁻¹) * f by
      funext x; rfl]
    exact HasCompactSupport.smul_left
      (f := fun _x : E => I⁻¹) (f' := f) hf_cs
  have hψ0 : ∀ x, 0 ≤ ψ x := by
    intro x
    have hInv : 0 ≤ I⁻¹ := inv_nonneg.mpr (le_of_lt hIpos')
    exact mul_nonneg hInv (hf_nonneg x)
  have hψint : ∫ x, ψ x ∂(volume : Measure E) = 1 := by
    have hmul : (∫ x, ψ x ∂(volume : Measure E)) = I⁻¹ * I := by
      simpa [ψ, I] using
        (MeasureTheory.integral_const_mul (μ := (volume : Measure E)) (r := I⁻¹) (f := f))
    rw [hmul]
    exact inv_mul_cancel₀ hI0
  have hψ_tsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ := by
    have hsub : tsupport ψ ⊆ tsupport f := by
      simpa [ψ, smul_eq_mul] using
        (tsupport_smul_subset_right (f := fun _x : E => I⁻¹) (g := f))
    exact hsub.trans hf_tsupp
  exact ⟨ψ, hψsmooth, hψcs, hψ0, hψint, hψ_tsupp⟩

private lemma smoothL2_kernel_tendsto
    {S : Set E} (hS : IsCompact S) (f : E → ℝ)
    (hf : MemLp f 2 (volume : Measure E)) (hsupp : Function.support f ⊆ S)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrt : Tendsto r atTop (𝓝 0))
    (ψ : ℕ → E → ℝ)
    (hψ : ∀ n, Continuous (ψ n) ∧ HasCompactSupport (ψ n) ∧
      (∀ x, 0 ≤ ψ n x) ∧ (∫ x, ψ n x ∂(volume : Measure E) = 1) ∧
      tsupport (ψ n) ⊆ Metric.ball (0 : E) (r n)) :
    Tendsto (fun n => smoothL2 (E := E) (K := S) (ψ n) hS hS.measurableSet
      (hψ n).1 (hψ n).2.1 ((hf.restrict S).toLp f)) atTop
      (𝓝 (hf.toLp f)) := by
  let uS : Lp ℝ 2 (volume.restrict S) := (hf.restrict S).toLp f
  have hExt : extendByZeroL2 (E := E) (K := S) hS.measurableSet uS = hf.toLp f := by
    exact extendByZeroL2_eq_toLp_of_support hS f hf hsupp
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htrans : Tendsto (fun t : E =>
      translateL2 (μ := (volume : Measure E)) (-t) (hf.toLp f)) (𝓝 (0 : E))
      (𝓝 (hf.toLp f)) := by
    have hneg : Tendsto (fun t : E => -t) (𝓝 (0 : E)) (𝓝 (0 : E)) := by
      have h : Tendsto (fun t : E => -t) (𝓝 (0 : E)) (𝓝 (-(0 : E))) :=
        continuous_neg.continuousAt
      simpa using h
    simpa [Function.comp_def] using
      (tendsto_translateL2_zero (F := hf.toLp f)).comp hneg
  have hev : ∀ᶠ t : E in 𝓝 (0 : E),
      dist (translateL2 (μ := (volume : Measure E)) (-t) (hf.toLp f))
        (hf.toLp f) < ε / 2 :=
    htrans.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  obtain ⟨δ, hδ, hδmod⟩ := (Metric.eventually_nhds_iff.mp hev)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hrt) δ hδ
  refine ⟨N, ?_⟩
  intro n hn
  have hrδ : r n < δ := by
    have h := hN n hn
    simpa [dist_zero_right, abs_of_pos (hr n)] using h
  have hmod : ∀ t : E, t ∈ Metric.ball (0 : E) δ →
      ‖translateL2 (μ := (volume : Measure E)) (-t) (hf.toLp f) - hf.toLp f‖ ≤ ε / 2 := by
    intro t ht
    have hlt := hδmod (by simpa [Metric.mem_ball] using ht)
    exact le_of_lt (by simpa [dist_eq_norm] using hlt)
  have hψn := hψ n
  have hψsupp : tsupport (ψ n) ⊆ Metric.ball (0 : E) δ :=
    hψn.2.2.2.2.trans (Metric.ball_subset_ball (le_of_lt hrδ))
  have hint := integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
    (E := E) hψn.1 hψn.2.1 hψn.2.2.1 hψn.2.2.2.1
    (hη := by positivity) hψsupp (hf.toLp f) hmod
  have hint' : ∫ t,
        ‖translateL2 (μ := (volume : Measure E)) (-t) (extendByZeroL2
          (E := E) (K := S) hS.measurableSet uS) - extendByZeroL2
          (E := E) (K := S) hS.measurableSet uS‖ ^ 2
      ∂kernelMeasure (E := E) (ψ n) ≤ (ε / 2) ^ 2 := by
    simpa only [hExt] using hint
  have hsq := norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
    (E := E) (K := S) hS hS.measurableSet (ψ := ψ n) hψn.1 hψn.2.1
    hψn.2.2.1 hψn.2.2.2.1 uS
  have hsq' : ‖smoothL2 (E := E) (K := S) (ψ n) hS hS.measurableSet
      hψn.1 hψn.2.1 uS - hf.toLp f‖ ^ 2 ≤ (ε / 2) ^ 2 := by
    rw [← hExt]
    exact hsq.trans hint'
  have hle : ‖smoothL2 (E := E) (K := S) (ψ n) hS hS.measurableSet
      hψn.1 hψn.2.1 uS - hf.toLp f‖ ≤ ε / 2 := by
    nlinarith [sq_nonneg (‖smoothL2 (E := E) (K := S) (ψ n) hS hS.measurableSet
      hψn.1 hψn.2.1 uS - hf.toLp f‖)]
  simpa [dist_eq_norm] using lt_of_le_of_lt hle (by linarith)

/-! ## Weak first-order identities are closed under compactly supported smoothing -/

theorem localizedWeakJet_mem_c1SupportedTestGraph_of_weak
    {ι : Type*} [Fintype ι] {b : OrthonormalBasis ι ℝ E}
    {K₀ K : Set E} {n : ℕ} (J : LocalL2DerivativeJet b K₀ n)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ₀ : tsupport χ ⊆ K₀) (hK : IsCompact K)
    (hsχK : tsupport χ ⊆ interior K) (hn : 1 ≤ n) :
    (((localizedWeakJet_properties J hχ hcχ []).1.toLp (localizedWeakJet J χ []),
        fun i => (localizedWeakJet_properties J hχ hcχ [i]).1.toLp
          (localizedWeakJet J χ [i])) :
      Lp ℝ 2 (volume : Measure E) ×
        (ι → Lp ℝ 2 (volume : Measure E))) ∈
      closure (c1SupportedTestGraph (fun i => b i) K) := by
  let S : Set E := tsupport χ
  have hS : IsCompact S := by
    simpa [S] using hcχ.isCompact
  have hSm : MeasurableSet S := hS.measurableSet
  obtain ⟨ε₀, hε₀, hmargin⟩ := exists_uniform_translation_margin hS
    isOpen_interior hsχK
  let r : ℕ → ℝ := fun m => min (ε₀ / 2) (((m : ℝ) + 1)⁻¹)
  have hr (m : ℕ) : 0 < r m := by
    exact lt_min (by linarith) (inv_pos.mpr (by positivity))
  have hrt : Tendsto r atTop (𝓝 0) := by
    have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hplus : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop 1 hnat
    have hinv : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hplus
    have hmin := Filter.Tendsto.min
      (f := fun _ : ℕ => ε₀ / 2)
      (g := fun m : ℕ => ((m : ℝ) + 1)⁻¹)
      tendsto_const_nhds hinv
    simpa [r, min_eq_right (le_of_lt (by linarith : 0 < ε₀ / 2))] using hmin
  choose ψ hψ using fun m =>
    exists_contDiff_kernel_tsupport_subset_ball_integral_eq_one (E := E) (hr m)
  let f₀ : E → ℝ := localizedWeakJet J χ []
  let d : ι → E → ℝ := fun i => localizedWeakJet J χ [i]
  have hf₀ : MemLp f₀ 2 (volume : Measure E) := by
    simpa [f₀] using (localizedWeakJet_properties J hχ hcχ []).1
  have hd (i : ι) : MemLp (d i) 2 (volume : Measure E) := by
    simpa [d] using (localizedWeakJet_properties J hχ hcχ [i]).1
  have hsupp₀ : Function.support f₀ ⊆ S := by
    have hst : Function.support f₀ ⊆ tsupport f₀ :=
      (subset_closure : Function.support f₀ ⊆ closure (Function.support f₀))
    exact hst.trans ((localizedWeakJet_properties J hχ hcχ []).2.2.trans (by rfl))
  have hsuppd (i : ι) : Function.support (d i) ⊆ S := by
    have hst : Function.support (d i) ⊆ tsupport (d i) :=
      (subset_closure : Function.support (d i) ⊆ closure (Function.support (d i)))
    exact hst.trans ((localizedWeakJet_properties J hχ hcχ [i]).2.2.trans (by rfl))
  let u₀ : Lp ℝ 2 (volume : Measure E) := hf₀.toLp f₀
  let du : ι → Lp ℝ 2 (volume : Measure E) := fun i => (hd i).toLp (d i)
  have hu₀ : (u₀ : E → ℝ) =ᵐ[(volume : Measure E)] f₀ := by
    simpa [u₀] using hf₀.coeFn_toLp
  have hdu (i : ι) : (du i : E → ℝ) =ᵐ[(volume : Measure E)] d i := by
    simpa [du] using (hd i).coeFn_toLp
  have hweak (i : ι) : HasWeakDirectionalDerivativeOn Set.univ
      (b i) (u₀ : E → ℝ) (du i : E → ℝ) := by
    apply hasWeakDirectionalDerivativeOn_of_global_test_identity Set.univ
      (b i) (u₀ : E → ℝ) (du i : E → ℝ)
    intro φ hφ hcφ _
    have hn0 : 0 < n := by omega
    have hroot := localizedWeakJet_weak_derivative J hχ hcχ hsχ₀ []
      (by simpa using hn0) i φ hφ
    calc
      (∫ z, u₀ z * fderiv ℝ φ z (b i)) =
          ∫ z, f₀ z * fderiv ℝ φ z (b i) := by
        apply integral_congr_ae
        filter_upwards [hu₀] with z hz
        rw [hz]
      _ = -(∫ z, d i z * φ z) := by simpa [f₀, d] using hroot
      _ = -(∫ z, du i z * φ z) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hdu i] with z hz
        rw [hz]
  have hmul : ContinuousLinearMap.lsmul ℝ ℝ = ContinuousLinearMap.mul ℝ ℝ := by
    ext x y
    simp [smul_eq_mul]
  have hconv (f : E → ℝ) (hf : MemLp f 2 (volume : Measure E))
      (hsupp : Function.support f ⊆ S) (m : ℕ) :
      smoothFun (E := E) (K := S) (ψ m)
          ((hf.restrict S).toLp f) =
        ((hf.toLp f : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (ψ m)) := by
    have hExt : extendByZeroL2 (E := E) (K := S) hSm
        ((hf.restrict S).toLp f) = hf.toLp f := by
      exact extendByZeroL2_eq_toLp_of_support hS f hf hsupp
    have hzero :
        (extendByZeroFun (E := E) (K := S) ((hf.restrict S).toLp f) : E → ℝ) =ᵐ[volume]
          (hf.toLp f : E → ℝ) := by
      have h1 := extendByZeroL2_ae_eq (E := E) (K := S) hSm
        ((hf.restrict S).toLp f)
      have h2 :
          (extendByZeroL2 (E := E) (K := S) hSm
            ((hf.restrict S).toLp f) : E → ℝ) =ᵐ[volume]
            (hf.toLp f : E → ℝ) := by
        rw [hExt]
      exact h1.symm.trans h2
    rw [smoothFun, hmul]
    exact MeasureTheory.convolution_congr (ContinuousLinearMap.mul ℝ ℝ)
      hzero EventuallyEq.rfl
  have hφsmooth (m : ℕ) : ContDiff ℝ ∞
      (smoothFun (E := E) (K := S) (ψ m)
        ((hf₀.restrict S).toLp f₀)) := by
    rw [hconv f₀ hf₀ hsupp₀ m]
    exact contDiff_L2_convolution u₀ (hψ m).1 (hψ m).2.1
  have hφcompact (m : ℕ) : HasCompactSupport
      (smoothFun (E := E) (K := S) (ψ m)
        ((hf₀.restrict S).toLp f₀)) := by
    exact hasCompactSupport_smoothFun (E := E) (K := S) (ψ m) hS
      (hψ m).2.1 ((hf₀.restrict S).toLp f₀)
  have hsumK (m : ℕ) : S + tsupport (ψ m) ⊆ K := by
    intro z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    have hyr : ‖y‖ < r m := by
      have := (hψ m).2.2.2.2 hy
      simpa [Metric.mem_ball, dist_eq_norm] using this
    have hry : r m < ε₀ := by
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hxy : |(1 : ℝ)| * ‖y‖ < ε₀ := by
      simpa using hyr.trans hry
    exact interior_subset (by simpa using (hmargin y 1 hxy).1 x hx |>.1)
  have hφsupport (m : ℕ) : Function.support
      (smoothFun (E := E) (K := S) (ψ m)
        ((hf₀.restrict S).toLp f₀)) ⊆ K := by
    exact (support_smoothFun_subset_add_tsupport (E := E) (K := S) (ψ := ψ m)
      ((hf₀.restrict S).toLp f₀)).trans (hsumK m)
  let q₀ : ℕ → Lp ℝ 2 (volume : Measure E) := fun m =>
    smoothL2 (E := E) (K := S) (ψ m) hS hSm (hψ m).1.continuous (hψ m).2.1
      ((hf₀.restrict S).toLp f₀)
  let q : ℕ → ι → Lp ℝ 2 (volume : Measure E) := fun m i =>
    smoothL2 (E := E) (K := S) (ψ m) hS hSm (hψ m).1.continuous (hψ m).2.1
      (((hd i).restrict S).toLp (d i))
  have hfd (m : ℕ) (i : ι) (x : E) :
      fderiv ℝ (smoothFun (E := E) (K := S) (ψ m)
        ((hf₀.restrict S).toLp f₀)) x (b i) =
        ((du i : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (ψ m)) x := by
    rw [hconv f₀ hf₀ hsupp₀ m]
    exact fderiv_convolution_eq_weakDerivative_convolution u₀ (du i) (b i)
      (hweak i) (hψ m).1 (hψ m).2.1 x (subset_univ _)
  have hqderiv (m : ℕ) (i : ι) :
      q m i = (let hm := (hφsmooth m).continuous_fderiv (by norm_num)
        let hc := hφcompact m
        let hmem : MemLp (fun x => fderiv ℝ
          (smoothFun (E := E) (K := S) (ψ m)
            ((hf₀.restrict S).toLp f₀)) x (b i)) 2 volume :=
          (hm.clm_apply continuous_const).memLp_of_hasCompactSupport
            (hc.fderiv_apply ℝ (b i))
        hmem.toLp (fun x => fderiv ℝ
          (smoothFun (E := E) (K := S) (ψ m)
            ((hf₀.restrict S).toLp f₀)) x (b i))) := by
    let hm := (hφsmooth m).continuous_fderiv (by norm_num)
    let hc := hφcompact m
    let hmem : MemLp (fun x => fderiv ℝ
        (smoothFun (E := E) (K := S) (ψ m)
          ((hf₀.restrict S).toLp f₀)) x (b i)) 2 volume :=
      (hm.clm_apply continuous_const).memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ (b i))
    apply MeasureTheory.Lp.ext
    have hqae := smoothL2_ae_eq (E := E) (K := S) (ψ := ψ m) hS hSm
      (hψ m).1.continuous (hψ m).2.1 (((hd i).restrict S).toLp (d i))
    have hdiConv := hconv (d i) (hd i) (hsuppd i) m
    have hmemae := hmem.coeFn_toLp
    filter_upwards [hqae, hmemae] with x hqx hmx
    calc
      q m i x = smoothFun (E := E) (K := S) (ψ m)
          (((hd i).restrict S).toLp (d i)) x := by
            exact hqx
      _ = ((du i : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
          (ψ m)) x := by
            rw [hdiConv]
      _ = fderiv ℝ (smoothFun (E := E) (K := S) (ψ m)
          ((hf₀.restrict S).toLp f₀)) x (b i) := (hfd m i x).symm
      _ = hmem.toLp (fun x => fderiv ℝ (smoothFun (E := E) (K := S) (ψ m)
          ((hf₀.restrict S).toLp f₀)) x (b i)) x := hmx.symm
  have hgraph (m : ℕ) :
      (q₀ m, fun i => q m i) ∈ c1SupportedTestGraph (fun i => b i) K := by
    have hφtsupport : tsupport (smoothFun (E := E) (K := S) (ψ m)
        ((hf₀.restrict S).toLp f₀)) ⊆ K := by
      exact closure_minimal (hφsupport m) hK.isClosed
    refine ⟨smoothFun (E := E) (K := S) (ψ m)
      ((hf₀.restrict S).toLp f₀), (hφsmooth m).of_le (by norm_num),
      hφcompact m, hφtsupport, ?_, ?_⟩
    · exact smoothL2_ae_eq (E := E) (K := S) (ψ := ψ m) hS hSm
        (hψ m).1.continuous (hψ m).2.1 ((hf₀.restrict S).toLp f₀)
    · intro i
      change (q m i : E → ℝ) =ᵐ[(volume : Measure E)]
        (fun z => fderiv ℝ (smoothFun (E := E) (K := S) (ψ m)
          ((hf₀.restrict S).toLp f₀)) z (b i))
      let hm := (hφsmooth m).continuous_fderiv (by norm_num)
      let hc := hφcompact m
      let hmem : MemLp (fun x => fderiv ℝ
          (smoothFun (E := E) (K := S) (ψ m)
            ((hf₀.restrict S).toLp f₀)) x (b i)) 2 volume :=
        (hm.clm_apply continuous_const).memLp_of_hasCompactSupport
          (hc.fderiv_apply ℝ (b i))
      have heq := hqderiv m i
      have hae := hmem.coeFn_toLp
      change (q m i : E → ℝ) =ᵐ[(volume : Measure E)] _
      rw [heq]
      exact hae
  have hq₀t : Tendsto q₀ atTop (𝓝 u₀) := by
    simpa [q₀, u₀] using smoothL2_kernel_tendsto hS f₀ hf₀ hsupp₀ r hr hrt ψ
      (fun m => ⟨(hψ m).1.continuous, (hψ m).2.1, (hψ m).2.2.1,
        (hψ m).2.2.2.1, (hψ m).2.2.2.2⟩)
  have hqt : ∀ i, Tendsto (fun m => q m i) atTop (𝓝 (du i)) := by
    intro i
    simpa [q, du] using smoothL2_kernel_tendsto hS (d i) (hd i) (hsuppd i)
      r hr hrt ψ (fun m => ⟨(hψ m).1.continuous, (hψ m).2.1, (hψ m).2.2.1,
        (hψ m).2.2.2.1, (hψ m).2.2.2.2⟩)
  have hqfamily : Tendsto (fun m => fun i => q m i) atTop
      (𝓝 (fun i => du i)) := (tendsto_pi_nhds).2 hqt
  have hpt : Tendsto (fun m => (q₀ m, fun i => q m i)) atTop
      (𝓝 (u₀, fun i => du i)) := by
    simpa only [nhds_prod_eq] using hq₀t.prodMk hqfamily
  have hcl : (u₀, fun i => du i) ∈
      closure (c1SupportedTestGraph (fun i => b i) K) := by
    apply isClosed_closure.mem_of_tendsto hpt
    exact Filter.Eventually.of_forall (fun m => subset_closure (hgraph m))
  simpa [u₀, du, f₀, d] using hcl

end AlmostSchur
