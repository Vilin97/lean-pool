/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.LocalizedWeakJetIdentities
public import LeanPool.PoincareGeometry.AlmostSchur.OpenDomainIntegration
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyCutoffGraph

/-! # Smooth representatives give genuine localized weak-jet graphs

This file isolates a useful endpoint of the local weak-jet analysis.  If the
localized zeroth field already has a smooth representative, its weak first
derivatives are identified almost everywhere with the corresponding classical
derivatives by test-function uniqueness.  The resulting pair is therefore a
genuine compactly supported `C¹` test graph, not merely an element supplied by
an abstract density assumption.

No elliptic regularity is proved here: the smooth representative remains an
input to the bridge.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators FourierTransform
namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## Identification of the first weak derivatives -/

theorem localizedWeakJet_first_derivative_ae_eq_fderiv
    {ι : Type*} {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) {χ g : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ K) (hn : 1 ≤ n)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hge : g =ᵐ[volume] localizedWeakJet J χ []) (i : ι) :
    (fun x => fderiv ℝ g x (b i)) =ᵐ[volume] localizedWeakJet J χ [i] := by
  have hu := localizedWeakJet_properties J hχ hcχ []
  have hdu := localizedWeakJet_properties J hχ hcχ [i]
  apply ae_eq_of_integral_contDiff_smul_eq
  · have hcg : HasCompactSupport (fun x => fderiv ℝ g x (b i)) :=
      hgc.fderiv_apply ℝ (b i)
    exact ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport hcg
      |>.locallyIntegrable
  · exact hdu.1.locallyIntegrable (by norm_num)
  · intro φ hφ hcφ
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
    have hIBP := integral_mul_fderiv_openDomain (μ := (volume : Measure E))
      (U := Set.univ) isOpen_univ g φ (hg.of_le (by norm_num)).contDiffOn hφ1 hcφ
      (subset_univ _) (b i)
    have hn0 : 0 < n := by omega
    have hweak := localizedWeakJet_weak_derivative J hχ hcχ hsχ [] (by simpa using hn0) i φ hφ
    have hroot : (∫ x, localizedWeakJet J χ [] x * fderiv ℝ φ x (b i)) =
        ∫ x, g x * fderiv ℝ φ x (b i) := by
      apply integral_congr_ae
      exact hge.symm.mul EventuallyEq.rfl
    calc
      (∫ x, φ x • fderiv ℝ g x (b i)) =
          ∫ x, fderiv ℝ g x (b i) * φ x := by
        congr 1
        funext x
        simp [smul_eq_mul, mul_comm]
      _ = -(∫ x, g x * fderiv ℝ φ x (b i)) := by
        linarith [hIBP]
      _ = -(∫ x, localizedWeakJet J χ [] x * fderiv ℝ φ x (b i)) := by
        rw [hroot]
      _ = ∫ x, localizedWeakJet J χ [i] x * φ x := by
        linarith [hweak]
      _ = ∫ x, φ x • localizedWeakJet J χ [i] x := by
        congr 1
        funext x
        simp [smul_eq_mul, mul_comm]

/-! ## Graph membership -/

theorem localizedWeakJet_mem_c1SupportedTestGraph
    {ι : Type*} {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) {χ g : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ K) (hn : 1 ≤ n)
    (hg : ContDiff ℝ ∞ g)
    (hge : g =ᵐ[volume] localizedWeakJet J χ []) :
    (((localizedWeakJet_properties J hχ hcχ []).1.toLp (localizedWeakJet J χ []),
        fun i => (localizedWeakJet_properties J hχ hcχ [i]).1.toLp (localizedWeakJet J χ [i])) :
      Lp ℝ 2 (volume : Measure E) ×
        (ι → Lp ℝ 2 (volume : Measure E))) ∈
      closure (c1SupportedTestGraph b (tsupport χ)) := by
  let u : E → ℝ := localizedWeakJet J χ []
  let d : ι → E → ℝ := fun i => localizedWeakJet J χ [i]
  have hu : MemLp u 2 (volume : Measure E) := by
    simpa [u] using (localizedWeakJet_properties J hχ hcχ []).1
  have hd (i : ι) : MemLp (d i) 2 (volume : Measure E) := by
    simpa [d] using (localizedWeakJet_properties J hχ hcχ [i]).1
  have hsupp : Function.support g ⊆ tsupport χ := by
    intro x hx
    by_contra hnot
    have hzero : u =ᵐ[(volume : Measure E).restrict (tsupport χ)ᶜ] 0 := by
      filter_upwards [ae_restrict_mem (isClosed_tsupport χ).isOpen_compl.measurableSet] with y hy
      have hy' : y ∉ tsupport u := fun hyu => hy ((localizedWeakJet_properties J hχ hcχ []).2.2
        (by simpa [u] using hyu))
      simp [u, image_eq_zero_of_notMem_tsupport hy']
    have hge' : g =ᵐ[(volume : Measure E).restrict (tsupport χ)ᶜ] 0 := by
      filter_upwards [ae_restrict_of_ae hge, hzero] with y hy hy0
      exact hy.trans hy0
    have heq : g x = 0 :=
      Measure.eqOn_open_of_ae_eq hge' (isClosed_tsupport χ).isOpen_compl
        hg.continuous.continuousOn continuousOn_const hnot
    exact hx heq
  have hgc : HasCompactSupport g := hcχ.mono' hsupp
  let p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E)) :=
    (hu.toLp u, fun i => (hd i).toLp (d i))
  apply subset_closure
  refine ⟨g, hg.of_le (by norm_num), hgc,
    closure_minimal hsupp (isClosed_tsupport χ), ?_, ?_⟩
  · exact (hu.coeFn_toLp).trans hge.symm
  · intro i
    exact ((hd i).coeFn_toLp).trans (localizedWeakJet_first_derivative_ae_eq_fderiv
      J hχ hcχ hsχ hn hg hgc hge i).symm

/-! ## Fourier-to-graph packaging -/

theorem localizedWeakJet_mem_c1SupportedTestGraph_of_all_weighted_fourier
    {ι : Type*} [Fintype ι] {b : OrthonormalBasis ι ℝ E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) {χ : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ K) (hn : 1 ≤ n)
    (hweighted : ∀ k : ℕ, ∃ s : ℝ, (Module.finrank ℝ E : ℝ) < 2 * (s - k) ∧
      MemLp (fun ξ => (1 + ‖ξ‖) ^ s *
        ‖𝓕 (fun x => ((localizedWeakJet J χ [] x : ℝ) : ℂ)) ξ‖) 2 volume) :
    (((localizedWeakJet_properties J hχ hcχ []).1.toLp (localizedWeakJet J χ []),
        fun i => (localizedWeakJet_properties J hχ hcχ [i]).1.toLp (localizedWeakJet J χ [i])) :
      Lp ℝ 2 (volume : Measure E) ×
        (ι → Lp ℝ 2 (volume : Measure E))) ∈
      closure (c1SupportedTestGraph (fun i => b i) (tsupport χ)) := by
  have hi : Integrable (localizedWeakJet J χ []) volume :=
    (localizedWeakJet_properties J hχ hcχ []).2.1
  obtain ⟨g, hg, hge⟩ := exists_smooth_representative_of_all_weighted_fourier
    hi.ofReal hweighted
  let gr : E → ℝ := fun x => (g x).re
  have hgr : ContDiff ℝ ∞ gr := Complex.reCLM.contDiff.comp hg
  have hgre : gr =ᵐ[volume] localizedWeakJet J χ [] := by
    filter_upwards [hge] with x hx
    exact congrArg Complex.re hx
  exact localizedWeakJet_mem_c1SupportedTestGraph J hχ hcχ hsχ hn hgr hgre

theorem localizedWeakJet_mem_c1SupportedTestGraph_of_all_order_jets
    {ι : Type*} [Fintype ι] {b : OrthonormalBasis ι ℝ E} {K : Set E}
    (J : ∀ n : ℕ, LocalL2DerivativeJet b K n)
    (u : Lp ℝ 2 (volume : Measure E))
    (hroot : ∀ n, (J n).value [] = u) {χ : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ K) :
    (((localizedWeakJet_properties (J 1) hχ hcχ []).1.toLp (localizedWeakJet (J 1) χ []),
        fun i => (localizedWeakJet_properties (J 1) hχ hcχ [i]).1.toLp
          (localizedWeakJet (J 1) χ [i])) :
      Lp ℝ 2 (volume : Measure E) ×
        (ι → Lp ℝ 2 (volume : Measure E))) ∈
      closure (c1SupportedTestGraph (fun i => b i) (tsupport χ)) := by
  apply localizedWeakJet_mem_c1SupportedTestGraph_of_all_weighted_fourier
    (J := J 1) hχ hcχ hsχ (by simp)
  intro k
  let m : ℕ := Module.finrank ℝ E + k + 1
  refine ⟨(m : ℝ), ?_, ?_⟩
  · have hd : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
    dsimp [m]
    push_cast
    linarith
  · have hm := localizedWeakJet_weighted_fourier b (J m) hχ hcχ
      hsχ
    have hLp : (J m).value [] = (J 1).value [] := (hroot m).trans (hroot 1).symm
    have hLp' : ((J m).value [] : E → ℝ) = (J 1).value [] :=
      congrArg (fun z : Lp ℝ 2 (volume : Measure E) => (z : E → ℝ)) hLp
    have hval (x : E) : ((J m).value [] : E → ℝ) x = ((J 1).value [] : E → ℝ) x :=
      congrFun hLp' x
    have hloc : localizedWeakJet (J m) χ [] = localizedWeakJet (J 1) χ [] := by
      funext x
      simp [localizedWeakJet, cutoffJetTerms, cutoffJetTerm, localDirectionalIterate, hval x]
    have hcomplex :
        (fun x => ((localizedWeakJet (J m) χ [] x : ℝ) : ℂ)) =
          (fun x => ((localizedWeakJet (J 1) χ [] x : ℝ) : ℂ)) := by
      simpa [hloc]
    rw [hcomplex] at hm
    simpa only [Real.rpow_natCast] using hm

end AlmostSchur
