/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Smooth parameter integrals with local integrable majorants

The Taylor coefficients below are integrals of the actual `iteratedFDeriv` of
the integrand. Their successive derivative relation is proved using dominated
differentiation and the currying identity for `iteratedFDeriv`; it is not an
assumption on a separately supplied family of jets.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped Topology ContDiff

namespace NavierStokes.SmoothParameterIntegral

variable {α H E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine derivative in the parameter, with the integration variable last. -/
def jet (F : H → α → E) (k : ℕ) (x : H) (t : α) : H [×k]→L[ℝ] E :=
  iteratedFDeriv ℝ k (fun y => F y t) x

/-- Each order has an integrable majorant on a neighborhood of each parameter.
The neighborhood is uniform in the integration variable; it may depend on the
order and the center. -/
def LocallyDominated (F : H → α → E) (μ : Measure α) : Prop :=
  ∀ (k : ℕ) (x : H), ∃ ε : ℝ, 0 < ε ∧ ∃ bound : α → ℝ,
    Integrable bound μ ∧
      ∀ᵐ t ∂μ, ∀ y ∈ ball x ε, ‖jet F k y t‖ ≤ bound t

variable {F : H → α → E} {μ : Measure α}

theorem integrable_jet
    (h_meas : ∀ k x, AEStronglyMeasurable (jet F k x) μ)
    (h_dom : LocallyDominated F μ) (k : ℕ) (x : H) :
    Integrable (jet F k x) μ := by
  obtain ⟨ε, hε, bound, hb, hbound⟩ := h_dom k x
  exact hb.mono' (h_meas k x)
    (hbound.mono fun t ht => ht x (mem_ball_self hε))

/-- Differentiation of every integrated genuine jet, with the correct curry map. -/
theorem hasFDerivAt_integral_jet
    (h_smooth : ∀ᵐ t ∂μ, ContDiff ℝ ∞ (fun x => F x t))
    (h_meas : ∀ k x, AEStronglyMeasurable (jet F k x) μ)
    (h_dom : LocallyDominated F μ) (k : ℕ) (x : H) :
    HasFDerivAt (fun y => ∫ t, jet F k y t ∂μ)
      (∫ t, jet F (k + 1) x t ∂μ).curryLeft x := by
  let curry : (H [×(k + 1)]→L[ℝ] E) ≃ₗᵢ[ℝ] (H →L[ℝ] H [×k]→L[ℝ] E) :=
    continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => H) E
  obtain ⟨ε, hε, bound, hb, hbound⟩ := h_dom (k + 1) x
  have hm : AEStronglyMeasurable (fun t => curry (jet F (k + 1) x t)) μ :=
    curry.continuous.comp_aestronglyMeasurable (h_meas (k + 1) x)
  have hd : ∀ᵐ t ∂μ, ∀ y ∈ ball x ε,
      HasFDerivAt (fun z => jet F k z t) (curry (jet F (k + 1) y t)) y := by
    filter_upwards [h_smooth] with t ht
    intro y _
    simpa only [jet, fderiv_iteratedFDeriv, Function.comp_apply] using
      (ht.differentiable_iteratedFDeriv (m := k)
        (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)) y).hasFDerivAt
  have hnorm : ∀ᵐ t ∂μ, ∀ y ∈ ball x ε,
      ‖curry (jet F (k + 1) y t)‖ ≤ bound t := by
    filter_upwards [hbound] with t ht
    intro y hy
    simpa only [LinearIsometryEquiv.norm_map] using ht y hy
  have hi := hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds _ hε)
    (Filter.Eventually.of_forall (h_meas k)) (integrable_jet h_meas h_dom k x)
    hm hnorm hb hd
  have hc : (∫ t, curry (jet F (k + 1) x t) ∂μ) =
      curry (∫ t, jet F (k + 1) x t ∂μ) := by
    simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := μ)
        (E := H [×(k + 1)]→L[ℝ] E) (F := H →L[ℝ] H [×k]→L[ℝ] E)
        (curry.toContinuousLinearEquiv) (fun t => jet F (k + 1) x t))
  rw [hc] at hi
  exact hi

/-- The Taylor series consists of the integrated genuine derivatives. -/
theorem hasFTaylorSeriesUpTo_integral
    (h_smooth : ∀ᵐ t ∂μ, ContDiff ℝ ∞ (fun x => F x t))
    (h_meas : ∀ k x, AEStronglyMeasurable (jet F k x) μ)
    (h_dom : LocallyDominated F μ) :
    HasFTaylorSeriesUpTo ∞ (fun x => ∫ t, F x t ∂μ)
      (fun x k => ∫ t, jet F k x t ∂μ) := by
  constructor
  · intro x
    calc
      (∫ t, jet F 0 x t ∂μ).curry0 = ∫ t, (jet F 0 x t).curry0 ∂μ :=
        ((continuousMultilinearCurryFin0 ℝ H E).toContinuousLinearEquiv.integral_comp_comm
          (fun t => jet F 0 x t)).symm
      _ = ∫ t, F x t ∂μ := rfl
  · intro k _ x
    exact hasFDerivAt_integral_jet h_smooth h_meas h_dom k x
  · intro k _
    have hd : Differentiable ℝ (fun x => ∫ t, jet F k x t ∂μ) :=
      fun x => (hasFDerivAt_integral_jet h_smooth h_meas h_dom k x).differentiableAt
    exact hd.continuous

theorem contDiff_integral
    (h_smooth : ∀ᵐ t ∂μ, ContDiff ℝ ∞ (fun x => F x t))
    (h_meas : ∀ k x, AEStronglyMeasurable (jet F k x) μ)
    (h_dom : LocallyDominated F μ) :
    ContDiff ℝ ∞ (fun x => ∫ t, F x t ∂μ) :=
  (hasFTaylorSeriesUpTo_integral h_smooth h_meas h_dom).contDiff

theorem iteratedFDeriv_integral
    (h_smooth : ∀ᵐ t ∂μ, ContDiff ℝ ∞ (fun x => F x t))
    (h_meas : ∀ k x, AEStronglyMeasurable (jet F k x) μ)
    (h_dom : LocallyDominated F μ) (k : ℕ) (x : H) :
    iteratedFDeriv ℝ k (fun y => ∫ t, F y t ∂μ) x =
      ∫ t, iteratedFDeriv ℝ k (fun y => F y t) x ∂μ :=
  ((hasFTaylorSeriesUpTo_integral h_smooth h_meas h_dom).eq_iteratedFDeriv
    (m := k) (WithTop.coe_le_coe.mpr le_top) x).symm

section OpenDomain

variable {s : Set H}

/-- Local domination on an open parameter domain. The dominating ball is
explicitly contained in that domain; no behavior outside it is prescribed. -/
def LocallyDominatedOn (F : H → α → E) (μ : Measure α) (s : Set H) : Prop :=
  ∀ (k : ℕ) (x : H), x ∈ s → ∃ ε : ℝ, 0 < ε ∧ ball x ε ⊆ s ∧
    ∃ bound : α → ℝ, Integrable bound μ ∧
      ∀ᵐ t ∂μ, ∀ y ∈ ball x ε, ‖jet F k y t‖ ≤ bound t

theorem integrable_jetOn
    (h_meas : ∀ k x, x ∈ s → AEStronglyMeasurable (jet F k x) μ)
    (h_dom : LocallyDominatedOn F μ s) (k : ℕ) {x : H} (hx : x ∈ s) :
    Integrable (jet F k x) μ := by
  obtain ⟨ε, hε, _, bound, hb, hbound⟩ := h_dom k x hx
  exact hb.mono' (h_meas k x hx)
    (hbound.mono fun t ht => ht x (mem_ball_self hε))

theorem hasFDerivAt_integral_jetOn (hs : IsOpen s)
    (h_smooth : ∀ᵐ t ∂μ, ContDiffOn ℝ ∞ (fun x => F x t) s)
    (h_meas : ∀ k x, x ∈ s → AEStronglyMeasurable (jet F k x) μ)
    (h_dom : LocallyDominatedOn F μ s) (k : ℕ) {x : H} (hx : x ∈ s) :
    HasFDerivAt (fun y => ∫ t, jet F k y t ∂μ)
      (∫ t, jet F (k + 1) x t ∂μ).curryLeft x := by
  let curry : (H [×(k + 1)]→L[ℝ] E) ≃ₗᵢ[ℝ] (H →L[ℝ] H [×k]→L[ℝ] E) :=
    continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => H) E
  obtain ⟨ε, hε, hεs, bound, hb, hbound⟩ := h_dom (k + 1) x hx
  have hm : AEStronglyMeasurable (fun t => curry (jet F (k + 1) x t)) μ :=
    curry.continuous.comp_aestronglyMeasurable (h_meas (k + 1) x hx)
  have hd : ∀ᵐ t ∂μ, ∀ y ∈ ball x ε,
      HasFDerivAt (fun z => jet F k z t) (curry (jet F (k + 1) y t)) y := by
    filter_upwards [h_smooth] with t ht
    intro y hy
    have hc : ContDiffAt ℝ ∞ (fun z => F z t) y :=
      ht.contDiffAt (hs.mem_nhds (hεs hy))
    have horder : (1 : WithTop ℕ∞) + (k : WithTop ℕ∞) ≤ ∞ := by
      change (((1 : ℕ∞) + (k : ℕ∞)) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top
    have hj : DifferentiableAt ℝ (iteratedFDeriv ℝ k (fun z => F z t)) y :=
      (hc.iteratedFDeriv_right (m := 1) horder).differentiableAt (by norm_num)
    simpa only [jet, fderiv_iteratedFDeriv, Function.comp_apply] using hj.hasFDerivAt
  have hnorm : ∀ᵐ t ∂μ, ∀ y ∈ ball x ε,
      ‖curry (jet F (k + 1) y t)‖ ≤ bound t := by
    filter_upwards [hbound] with t ht
    intro y hy
    simpa only [LinearIsometryEquiv.norm_map] using ht y hy
  have hm_near : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (jet F k y) μ := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact h_meas k y hy
  have hi := hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds _ hε) hm_near
    (integrable_jetOn h_meas h_dom k hx) hm hnorm hb hd
  have hcomm : (∫ t, curry (jet F (k + 1) x t) ∂μ) =
      curry (∫ t, jet F (k + 1) x t ∂μ) := by
    simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := μ)
        (E := H [×(k + 1)]→L[ℝ] E) (F := H →L[ℝ] H [×k]→L[ℝ] E)
        (curry.toContinuousLinearEquiv) (fun t => jet F (k + 1) x t))
  rw [hcomm] at hi
  exact hi

theorem hasFTaylorSeriesUpToOn_integral (hs : IsOpen s)
    (h_smooth : ∀ᵐ t ∂μ, ContDiffOn ℝ ∞ (fun x => F x t) s)
    (h_meas : ∀ k x, x ∈ s → AEStronglyMeasurable (jet F k x) μ)
    (h_dom : LocallyDominatedOn F μ s) :
    HasFTaylorSeriesUpToOn ∞ (fun x => ∫ t, F x t ∂μ)
      (fun x k => ∫ t, jet F k x t ∂μ) s := by
  constructor
  · intro x _
    calc
      (∫ t, jet F 0 x t ∂μ).curry0 = ∫ t, (jet F 0 x t).curry0 ∂μ :=
        ((continuousMultilinearCurryFin0 ℝ H E).toContinuousLinearEquiv.integral_comp_comm
          (fun t => jet F 0 x t)).symm
      _ = ∫ t, F x t ∂μ := rfl
  · intro k _ x hx
    exact (hasFDerivAt_integral_jetOn hs h_smooth h_meas h_dom k hx).hasFDerivWithinAt
  · intro k _ x hx
    exact (hasFDerivAt_integral_jetOn hs h_smooth h_meas h_dom k hx).continuousAt.continuousWithinAt

theorem contDiffOn_integral (hs : IsOpen s)
    (h_smooth : ∀ᵐ t ∂μ, ContDiffOn ℝ ∞ (fun x => F x t) s)
    (h_meas : ∀ k x, x ∈ s → AEStronglyMeasurable (jet F k x) μ)
    (h_dom : LocallyDominatedOn F μ s) :
    ContDiffOn ℝ ∞ (fun x => ∫ t, F x t ∂μ) s :=
  (hasFTaylorSeriesUpToOn_integral hs h_smooth h_meas h_dom).contDiffOn

theorem iteratedFDeriv_integralOn (hs : IsOpen s)
    (h_smooth : ∀ᵐ t ∂μ, ContDiffOn ℝ ∞ (fun x => F x t) s)
    (h_meas : ∀ k x, x ∈ s → AEStronglyMeasurable (jet F k x) μ)
    (h_dom : LocallyDominatedOn F μ s) (k : ℕ) {x : H} (hx : x ∈ s) :
    iteratedFDeriv ℝ k (fun y => ∫ t, F y t ∂μ) x =
      ∫ t, iteratedFDeriv ℝ k (fun y => F y t) x ∂μ := by
  rw [← iteratedFDerivWithin_of_isOpen k hs hx]
  have hp := hasFTaylorSeriesUpToOn_integral hs h_smooth h_meas h_dom
  exact (hp.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (m := k) (WithTop.coe_le_coe.mpr le_top) hs.uniqueDiffOn hx).symm

end OpenDomain

section CompactInterval

variable [ProperSpace H] {F : H → ℝ → E} {s : Set H} {a b : ℝ}

/-- On a compact integration interval, joint continuity of the actual parameter
jets supplies all local majorants. Properness is automatic for finite-dimensional
real normed parameter spaces. -/
theorem contDiffOn_integral_Ioc_of_continuous_jet (hs : IsOpen s)
    (h_smooth : ∀ t ∈ Icc a b, ContDiffOn ℝ ∞ (fun x => F x t) s)
    (h_jet : ∀ k, ContinuousOn (fun z : H × ℝ => jet F k z.1 z.2) (s ×ˢ Icc a b)) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in Ioc a b, F x t) s := by
  apply contDiffOn_integral hs
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact h_smooth t ⟨ht.1.le, ht.2⟩
  · intro k x hx
    have hc : ContinuousOn (jet F k x) (Icc a b) :=
      (h_jet k).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hx, ht⟩)
    exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · intro k x hx
    obtain ⟨ε, hε, hεs⟩ := nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hx)
    have hcompact : IsCompact (closedBall x ε ×ˢ Icc a b) :=
      (isCompact_closedBall x ε).prod isCompact_Icc
    have hc : ContinuousOn (fun z : H × ℝ => jet F k z.1 z.2)
        (closedBall x ε ×ˢ Icc a b) :=
      (h_jet k).mono (Set.prod_mono hεs Subset.rfl)
    obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hc
    refine ⟨ε, hε, ball_subset_closedBall.trans hεs, fun _ => C, integrable_const C, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro y hy
    exact hC (y, t) ⟨ball_subset_closedBall hy, ht.1.le, ht.2⟩

theorem contDiffOn_intervalIntegral_of_continuous_jet (hs : IsOpen s) (hab : a ≤ b)
    (h_smooth : ∀ t ∈ Icc a b, ContDiffOn ℝ ∞ (fun x => F x t) s)
    (h_jet : ∀ k, ContinuousOn (fun z : H × ℝ => jet F k z.1 z.2) (s ×ˢ Icc a b)) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in a..b, F x t) s := by
  simpa only [intervalIntegral.integral_of_le hab] using
    contDiffOn_integral_Ioc_of_continuous_jet hs h_smooth h_jet

end CompactInterval

section ScalarParameter

variable {F : ℝ → α → E}

/-- One-dimensional form of the same local domination condition, using actual
scalar iterated derivatives rather than multilinear maps. -/
def LocallyDominatedDeriv (F : ℝ → α → E) (μ : Measure α) : Prop :=
  ∀ (k : ℕ) (x : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∃ bound : α → ℝ,
    Integrable bound μ ∧ ∀ᵐ t ∂μ, ∀ y ∈ ball x ε,
      ‖iteratedDeriv k (fun z => F z t) y‖ ≤ bound t

theorem LocallyDominatedDeriv.toLocallyDominated
    (h : LocallyDominatedDeriv F μ) : LocallyDominated F μ := by
  intro k x
  obtain ⟨ε, hε, bound, hb, hbound⟩ := h k x
  refine ⟨ε, hε, bound, hb, ?_⟩
  simpa only [jet, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hbound

theorem aestronglyMeasurable_jet_of_iteratedDeriv
    (h : ∀ k x, AEStronglyMeasurable
      (fun t => iteratedDeriv k (fun y => F y t) x) μ) :
    ∀ k x, AEStronglyMeasurable (jet F k x) μ := by
  intro k x
  change AEStronglyMeasurable (fun t => iteratedFDeriv ℝ k (fun y => F y t) x) μ
  simp_rw [iteratedFDeriv_eq_equiv_comp, Function.comp_apply]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) E).continuous.comp_aestronglyMeasurable
    (h k x)

/-- The scalar-parameter interface can be applied directly to a restricted
Lebesgue measure, including `volume.restrict (Ioi 0)`. -/
theorem contDiff_integral_of_iteratedDeriv
    (h_smooth : ∀ᵐ t ∂μ, ContDiff ℝ ∞ (fun x => F x t))
    (h_meas : ∀ k x, AEStronglyMeasurable
      (fun t => iteratedDeriv k (fun y => F y t) x) μ)
    (h_dom : LocallyDominatedDeriv F μ) :
    ContDiff ℝ ∞ (fun x => ∫ t, F x t ∂μ) :=
  contDiff_integral h_smooth (aestronglyMeasurable_jet_of_iteratedDeriv h_meas)
    h_dom.toLocallyDominated

theorem iteratedDeriv_integral
    (h_smooth : ∀ᵐ t ∂μ, ContDiff ℝ ∞ (fun x => F x t))
    (h_meas : ∀ k x, AEStronglyMeasurable
      (fun t => iteratedDeriv k (fun y => F y t) x) μ)
    (h_dom : LocallyDominatedDeriv F μ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y => ∫ t, F y t ∂μ) x =
      ∫ t, iteratedDeriv k (fun y => F y t) x ∂μ := by
  have hm := aestronglyMeasurable_jet_of_iteratedDeriv h_meas
  have hd := h_dom.toLocallyDominated
  rw [iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDeriv_integral h_smooth hm hd k x]
  exact ContinuousMultilinearMap.integral_apply (integrable_jet hm hd k x) _

end ScalarParameter

end NavierStokes.SmoothParameterIntegral
