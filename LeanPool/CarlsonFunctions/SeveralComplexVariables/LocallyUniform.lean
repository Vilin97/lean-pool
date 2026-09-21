/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Basic
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Derivatives
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.CauchyEstimates
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Locally uniform limits of analytic maps in several variables

This file proves the Weierstrass convergence theorem for finite-dimensional complex domains,
its normally summable series consequences, and locally uniform convergence of all mixed
coordinate and iterated Fréchet derivatives. The topological notion
`TendstoLocallyUniformlyOn` is Mathlib's.

This is a temporary project home for material ultimately intended for a Mathlib location such as
`Mathlib.Analysis.Complex.SeveralVariables.LocallyUniform`.

## Main results

* `TendstoLocallyUniformlyOn.analyticOnNhd_pi` is the several-variable Weierstrass convergence
  theorem for finite complex coordinate spaces.
* `HasSumLocallyUniformlyOn.analyticOnNhd_pi` is its series form.
* `TendstoLocallyUniformlyOn.partialDeriv` and
  `TendstoLocallyUniformlyOn.iteratedPartialDeriv` give convergence of coordinate derivatives.
* `HasSumLocallyUniformlyOn.iteratedPartialDeriv` gives termwise differentiation of series.
* `TendstoLocallyUniformlyOn.analyticOnNhd_finiteDimensional` and
  `TendstoLocallyUniformlyOn.iteratedFDeriv_finiteDimensional` are the coordinate-independent
  formulations, with multilinear operator norm for the latter.

Derivative convergence uses a one-variable Cauchy estimate on compact thickenings, followed
by finite sums, currying, and transport along a continuous linear choice of coordinates.
-/

public section

open Filter Set
open scoped Classical

variable {ι κ F : Type*} [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Weierstrass convergence theorem, finite-coordinate form.** A locally uniform limit of
analytic maps on an open subset of a finite complex coordinate space is analytic. -/
theorem TendstoLocallyUniformlyOn.analyticOnNhd_pi
    {U : Set (ι → ℂ)} {l : Filter κ} [l.NeBot]
    {f : κ → (ι → ℂ) → F} {g : (ι → ℂ) → F}
    (hlim : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ n in l, AnalyticOnNhd ℂ (f n) U) (hU : IsOpen U) :
    AnalyticOnNhd ℂ g U := by
  have hg : ContinuousOn g U :=
    hlim.continuousOn (hf.frequently.mono fun _ hn => hn.continuousOn)
  apply SeveralComplexVariables.analyticOnNhd_pi_of_analyticOnNhd_update hU hg
  intro z hz i
  let update : ℂ → (ι → ℂ) := fun w ↦ Function.update z i w
  let V : Set ℂ := update ⁻¹' U
  have hupdate : Continuous update := by
    dsimp only [update]
    fun_prop
  have hupdate_diff : Differentiable ℂ update :=
    fun w => (hasDerivAt_update z i w).differentiableAt
  have hV : IsOpen V := hU.preimage hupdate
  have hmap : Set.MapsTo update V U := fun _ hw ↦ hw
  have hlim' : TendstoLocallyUniformlyOn
      (fun n ↦ f n ∘ update) (g ∘ update) l V :=
    hlim.comp update hmap hupdate.continuousOn
  have hfdiff : ∀ᶠ n in l, DifferentiableOn ℂ (f n ∘ update) V := by
    filter_upwards [hf] with n hn
    intro w hw
    exact (((hn.differentiableOn _ hw).differentiableAt
      (hU.mem_nhds (hmap hw))).comp w hupdate_diff.differentiableAt).differentiableWithinAt
  exact (hlim'.differentiableOn hfdiff hV).analyticAt
    (hV.mem_nhds (show update (z i) ∈ U by simpa [update] using hz))

/-- A locally uniformly convergent sum of analytic maps on an open finite complex coordinate
space is analytic. -/
theorem HasSumLocallyUniformlyOn.analyticOnNhd_pi
    {U : Set (ι → ℂ)} {f : κ → (ι → ℂ) → F} {g : (ι → ℂ) → F}
    (hsum : HasSumLocallyUniformlyOn f g U)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hU : IsOpen U) :
    AnalyticOnNhd ℂ g U := by
  apply TendstoLocallyUniformlyOn.analyticOnNhd_pi hsum _ hU
  filter_upwards with s
  exact Finset.analyticOnNhd_fun_sum s fun n _ ↦ hf n

/-- A series of analytic maps is analytic when its terms admit a summable uniform majorant on
every compact subset of the domain. -/
theorem analyticOnNhd_tsum_of_summable_norm_on_compacts
    {U : Set (ι → ℂ)} {f : κ → (ι → ℂ) → F}
    (hU : IsOpen U) (hf : ∀ n, AnalyticOnNhd ℂ (f n) U)
    (hmajorant : ∀ K ⊆ U, IsCompact K → ∃ M : κ → ℝ,
      Summable M ∧ ∀ n x, x ∈ K → ‖f n x‖ ≤ M n) :
    AnalyticOnNhd ℂ (fun x ↦ ∑' n, f n x) U := by
  have hs : SummableLocallyUniformlyOn f U :=
    SummableLocallyUniformlyOn_of_locally_bounded hU hmajorant
  exact hs.hasSumLocallyUniformlyOn.analyticOnNhd_pi hf hU

/-- Locally uniform convergence of holomorphic maps implies locally uniform convergence
of each coordinate derivative. The Cauchy estimate is applied on a compact thickening. -/
theorem TendstoLocallyUniformlyOn.partialDeriv
    {U : Set (ι → ℂ)} {l : Filter κ} [l.NeBot]
    {f : κ → (ι → ℂ) → F} {g : (ι → ℂ) → F}
    (hlim : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ n in l, AnalyticOnNhd ℂ (f n) U) (hU : IsOpen U) (i : ι) :
    TendstoLocallyUniformlyOn (fun n => SeveralComplexVariables.partialDeriv i (f n))
      (SeveralComplexVariables.partialDeriv i g) l U := by
  have hg := hlim.analyticOnNhd_pi hf hU
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hU hKU
  have hc := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim
    (Metric.cthickening δ K) hKδ hK.cthickening
  rw [Metric.tendstoUniformlyOn_iff] at hc ⊢
  intro ε hε
  filter_upwards [hf, hc (ε * δ / 2) (by positivity)] with n hn hbound z hz
  have hball : Metric.closedBall z δ ⊆ Metric.cthickening δ K :=
    Metric.closedBall_subset_cthickening hz δ
  have hnorm := SeveralComplexVariables.norm_partialDeriv_le (hg.sub hn) i hδ
    (hball.trans hKδ) (M := ε * δ / 2) (fun w hw => by
      exact le_of_lt (by simpa [dist_eq_norm] using hbound w (hball hw)))
  rw [SeveralComplexVariables.partialDeriv_sub (hg z (hKU hz)).differentiableAt
    (hn z (hKU hz)).differentiableAt i] at hnorm
  rw [dist_eq_norm]
  exact hnorm.trans_lt ((div_lt_iff₀ hδ).mpr (by nlinarith [mul_pos hε hδ]))

/-- All mixed coordinate derivatives converge locally uniformly on the original domain. -/
theorem TendstoLocallyUniformlyOn.iteratedPartialDeriv
    {U : Set (ι → ℂ)} {l : Filter κ} [l.NeBot]
    {f : κ → (ι → ℂ) → F} {g : (ι → ℂ) → F}
    (hlim : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ n in l, AnalyticOnNhd ℂ (f n) U) (hU : IsOpen U) (is : List ι) :
    TendstoLocallyUniformlyOn (fun n => SeveralComplexVariables.iteratedPartialDeriv is (f n))
      (SeveralComplexVariables.iteratedPartialDeriv is g) l U := by
  induction is with
  | nil => exact hlim
  | cons i is ih =>
      exact ih.partialDeriv (hf.mono fun n hn => hn.iteratedPartialDeriv hU is) hU i

/-- Locally uniform convergence of holomorphic maps gives locally uniform convergence
of their Fréchet derivatives in operator norm. -/
theorem TendstoLocallyUniformlyOn.fderiv_pi
    {U : Set (ι → ℂ)} {l : Filter κ} [l.NeBot]
    {f : κ → (ι → ℂ) → F} {g : (ι → ℂ) → F}
    (hlim : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ n in l, AnalyticOnNhd ℂ (f n) U) (hU : IsOpen U) :
    TendstoLocallyUniformlyOn (fun n => fderiv ℂ (f n)) (fderiv ℂ g) l U := by
  let L (i : ι) : F →L[ℂ] ((ι → ℂ) →L[ℂ] F) :=
    ContinuousLinearMap.smulRightL ℂ (ι → ℂ) F (ContinuousLinearMap.proj i)
  have hi (i : ι) := (L i).uniformContinuous.comp_tendstoLocallyUniformlyOn
    (hlim.partialDeriv hf hU i)
  have hs (s : Finset ι) : TendstoLocallyUniformlyOn
      (fun n z => ∑ i ∈ s, L i (SeveralComplexVariables.partialDeriv i (f n) z))
      (fun z => ∑ i ∈ s, L i (SeveralComplexVariables.partialDeriv i g z)) l U := by
    induction s using Finset.induction_on with
    | empty =>
      simpa using (tendsto_const_nhds.tendstoUniformlyOn_const U).tendstoLocallyUniformlyOn
    | @insert i s his ih =>
      simpa only [Finset.sum_insert his, Function.comp_def] using (hi i).fun_add ih
  have heq {a : (ι → ℂ) → F} {z : ι → ℂ} (ha : DifferentiableAt ℂ a z) :
      (∑ i, L i (SeveralComplexVariables.partialDeriv i a z)) = fderiv ℂ a z := by
    ext v
    simpa [L] using (SeveralComplexVariables.fderiv_eq_sum_partialDeriv ha v).symm
  have h := (hs Finset.univ).congr_inseparable (hf.mono fun n hn z hz =>
    Inseparable.of_eq (heq (hn z hz).differentiableAt))
  exact h.congr_right fun z hz => heq ((hlim.analyticOnNhd_pi hf hU) z hz).differentiableAt

/-- All iterated Fréchet derivatives converge locally uniformly in multilinear operator norm. -/
theorem TendstoLocallyUniformlyOn.iteratedFDeriv_pi
    {U : Set (ι → ℂ)} {l : Filter κ} [l.NeBot]
    {f : κ → (ι → ℂ) → F} {g : (ι → ℂ) → F}
    (hlim : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ n in l, AnalyticOnNhd ℂ (f n) U) (hU : IsOpen U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℂ k (f n))
      (iteratedFDeriv ℂ k g) l U := by
  induction k with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp] using
      (continuousMultilinearCurryFin0 ℂ (ι → ℂ) F).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn hlim
  | succ k ih =>
    have hd := ih.fderiv_pi (hf.mono fun n hn => hn.iteratedFDeriv_of_isOpen hU k) hU
    simpa only [iteratedFDeriv_succ_eq_comp_left] using
      (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (k + 1) => ι → ℂ) F).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn hd

/-- A locally uniformly convergent holomorphic series may be differentiated term by term
any finite number of times, with locally uniform convergence of the differentiated series. -/
theorem HasSumLocallyUniformlyOn.iteratedPartialDeriv
    {U : Set (ι → ℂ)} {f : κ → (ι → ℂ) → F} {g : (ι → ℂ) → F}
    (hsum : HasSumLocallyUniformlyOn f g U)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hU : IsOpen U) (is : List ι) :
    HasSumLocallyUniformlyOn (fun n => SeveralComplexVariables.iteratedPartialDeriv is (f n))
      (SeveralComplexVariables.iteratedPartialDeriv is g) U := by
  have h := TendstoLocallyUniformlyOn.iteratedPartialDeriv hsum
    (Eventually.of_forall fun t => Finset.analyticOnNhd_fun_sum t fun n _ => hf n) hU is
  exact h.congr_inseparable (Eventually.of_forall fun t z hz => Inseparable.of_eq
    (SeveralComplexVariables.iteratedPartialDeriv_finset_sum t (fun n _ => hf n) hU is hz))

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The Weierstrass convergence theorem on any finite-dimensional complex normed domain. -/
theorem TendstoLocallyUniformlyOn.analyticOnNhd_finiteDimensional
    {U : Set E} {l : Filter κ} [l.NeBot] {f : κ → E → F} {g : E → F}
    (hlim : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ n in l, AnalyticOnNhd ℂ (f n) U) (hU : IsOpen U) :
    AnalyticOnNhd ℂ g U := by
  let e := (Module.finBasis ℂ E).equivFunL
  have hc := hlim.comp e.symm (fun _ hx => hx) e.symm.continuous.continuousOn
  have ha := hc.analyticOnNhd_pi (hf.mono fun n hn =>
    hn.comp (e.symm.toContinuousLinearMap.analyticOnNhd _) (fun _ hx => hx))
    (hU.preimage e.symm.continuous)
  intro x hx
  have hmem : e x ∈ e.symm ⁻¹' U := by simpa using hx
  simpa [Function.comp_def] using
    (ha (e x) hmem).comp_of_eq (e.toContinuousLinearMap.analyticAt x) rfl

/-- Locally uniform convergence of the Fréchet derivatives, without a choice of coordinates
in the statement. The target carries the operator norm. -/
theorem TendstoLocallyUniformlyOn.fderiv_finiteDimensional
    {U : Set E} {l : Filter κ} [l.NeBot] {f : κ → E → F} {g : E → F}
    (hlim : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ n in l, AnalyticOnNhd ℂ (f n) U) (hU : IsOpen U) :
    TendstoLocallyUniformlyOn (fun n => fderiv ℂ (f n)) (fderiv ℂ g) l U := by
  let e := (Module.finBasis ℂ E).equivFunL
  have hc := hlim.comp e.symm (fun _ hx => hx) e.symm.continuous.continuousOn
  have hd := hc.fderiv_pi (hf.mono fun n hn =>
    hn.comp (e.symm.toContinuousLinearMap.analyticOnNhd _) (fun _ hx => hx))
    (hU.preimage e.symm.continuous)
  let L := (ContinuousLinearMap.compL ℂ E (Fin (Module.finrank ℂ E) → ℂ) F).flip
    e.toContinuousLinearMap
  have H := (L.uniformContinuous.comp_tendstoLocallyUniformlyOn hd).comp e
    (fun x hx => show e x ∈ e.symm ⁻¹' U by simpa using hx) e.continuous.continuousOn
  have heq {a : E → F} {x : E} (ha : DifferentiableAt ℂ a x) :
      L (fderiv ℂ (a ∘ e.symm) (e x)) = fderiv ℂ a x := by
    have ha' : DifferentiableAt ℂ a (e.symm (e x)) := by simpa using ha
    rw [fderiv_comp _ ha' e.symm.differentiableAt, e.symm.fderiv]
    ext v
    simp [L]
  have H' := H.congr_inseparable (hf.mono fun n hn x hx =>
    Inseparable.of_eq (heq (hn x hx).differentiableAt))
  exact H'.congr_right fun x hx => heq
    ((hlim.analyticOnNhd_finiteDimensional hf hU) x hx).differentiableAt

/-- All iterated Fréchet derivatives converge locally uniformly on a finite-dimensional
complex domain, in multilinear operator norm. -/
theorem TendstoLocallyUniformlyOn.iteratedFDeriv_finiteDimensional
    {U : Set E} {l : Filter κ} [l.NeBot] {f : κ → E → F} {g : E → F}
    (hlim : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ n in l, AnalyticOnNhd ℂ (f n) U) (hU : IsOpen U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℂ k (f n))
      (iteratedFDeriv ℂ k g) l U := by
  induction k with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp] using
      (continuousMultilinearCurryFin0 ℂ E F).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn hlim
  | succ k ih =>
    have hd := ih.fderiv_finiteDimensional
      (hf.mono fun n hn => hn.iteratedFDeriv_of_isOpen hU k) hU
    simpa only [iteratedFDeriv_succ_eq_comp_left] using
      (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (k + 1) => E) F).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn hd

end FiniteDimensional

end
