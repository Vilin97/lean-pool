/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Actual shifted transport primitives

The source is integrated along a fixed translation direction. All integrals are
Bochner integrals. Compact radial support is used to justify local fixed finite
integration intervals, so ordinary derivatives pass under the integral without
differentiating the translation parameter.
-/

section

/-!
# The translated radial integral and repeated integration by parts

The integrals and derivatives in this file are actual Bochner integrals and
Fréchet derivatives. The auxiliary variable may be the universal cover of a
torus. A separately constructed directional primitive supplies the inverse
identity; no decay estimate for the integral is assumed.
-/

@[expose] public section

noncomputable section

open Set Function MeasureTheory
open scoped ContDiff Interval

namespace NavierStokes.RadialAlias

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual line along which the auxiliary variable is translated. -/
def shift (M : ℝ) (v Y : E) (u : ℝ) : ℝ × E := (u, Y + (M * u) • v)

/-- The translated integral over the radial support interval. -/
def aliasIntegral (a b M : ℝ) (v Y : E) (f : ℝ × E → F) : F :=
  ∫ u in a..b, f (shift M v Y u)

/-- The same integral over the whole radial line. -/
def wholeAlias (M : ℝ) (v Y : E) (f : ℝ × E → F) : F :=
  ∫ u : ℝ, f (shift M v Y u)

/-- Support in a fixed radial interval, uniformly in the auxiliary variable. -/
def RadiallySupported (a b : ℝ) (f : ℝ × E → F) : Prop :=
  support f ⊆ Prod.fst ⁻¹' Icc a b

/-- The derivative in the slow radial coordinate, holding the auxiliary variable fixed. -/
def slowDeriv (f : ℝ × E → F) (z : ℝ × E) : F :=
  fderiv ℝ f z (1, 0)

/-- The actual auxiliary directional derivative. -/
def directionalDeriv (v : E) (f : ℝ × E → F) (z : ℝ × E) : F :=
  fderiv ℝ f z (0, v)

theorem shift_hasDerivAt (M : ℝ) (v Y : E) (u : ℝ) :
    HasDerivAt (shift M v Y) (1, M • v) u := by
  unfold shift
  have h := (hasDerivAt_id u).prodMk
    ((hasDerivAt_const u Y).add (((hasDerivAt_id u).const_mul M).smul_const v))
  simpa only [shift, Pi.add_apply, id_eq, mul_one, zero_add] using h

theorem shift_continuous (M : ℝ) (v Y : E) : Continuous (shift M v Y) :=
  continuous_iff_continuousAt.mpr fun u => (shift_hasDerivAt M v Y u).continuousAt

/-- This is the chain rule `d/du = ∂u + M L_v` on the translated source. -/
theorem shifted_hasDerivAt {g : ℝ × E → F} {M u : ℝ} {v Y : E}
    (hg : DifferentiableAt ℝ g (shift M v Y u)) :
    HasDerivAt (fun s => g (shift M v Y s))
      (slowDeriv g (shift M v Y u) + M • directionalDeriv v g (shift M v Y u)) u := by
  have h : HasDerivAt (g ∘ shift M v Y)
      (fderiv ℝ g (shift M v Y u) (1, M • v)) u :=
    hg.hasFDerivAt.comp_hasDerivAt u (shift_hasDerivAt M v Y u)
  have hv : ((1 : ℝ), M • v) = (1, (0 : E)) + M • ((0 : ℝ), v) := by
    ext <;> simp
  rw [hv, map_add, map_smul] at h
  exact h

theorem slowDeriv_continuous {g : ℝ × E → F} (hg : ContDiff ℝ 1 g) :
    Continuous (slowDeriv g) :=
  (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem directionalDeriv_continuous {g : ℝ × E → F} (hg : ContDiff ℝ 1 g) (v : E) :
    Continuous (directionalDeriv v g) :=
  (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const

omit [NormedSpace ℝ F] in
theorem shifted_support_subset {a b : ℝ} {g : ℝ × E → F}
    (hg : RadiallySupported a b g) (M : ℝ) (v Y : E) :
    support (fun u => g (shift M v Y u)) ⊆ Icc a b := by
  intro u hu
  exact hg hu

theorem radialSupport_fderiv_apply {a b : ℝ} {g : ℝ × E → F}
    (hg : RadiallySupported a b g) (w : ℝ × E) :
    RadiallySupported a b (fun z => fderiv ℝ g z w) := by
  have hts : tsupport g ⊆ Prod.fst ⁻¹' Icc a b :=
    closure_minimal hg (isClosed_Icc.preimage continuous_fst)
  intro z hz
  by_contra hn
  have hnot : z ∉ tsupport g := fun h => hn (hts h)
  have hzero := fderiv_of_notMem_tsupport ℝ hnot
  change fderiv ℝ g z w ≠ 0 at hz
  exact hz (by rw [hzero]; rfl)

theorem radialSupport_slowDeriv {a b : ℝ} {g : ℝ × E → F}
    (hg : RadiallySupported a b g) : RadiallySupported a b (slowDeriv g) :=
  radialSupport_fderiv_apply hg (1, 0)

theorem radialSupport_directionalDeriv {a b : ℝ} {g : ℝ × E → F}
    (hg : RadiallySupported a b g) (v : E) :
    RadiallySupported a b (directionalDeriv v g) :=
  radialSupport_fderiv_apply hg (0, v)

omit [NormedSpace ℝ F] in
theorem endpoint_zero_of_support {a b : ℝ} {g : ℝ → F}
    (hc : Continuous g) (hs : support g ⊆ Icc a b) : g a = 0 ∧ g b = 0 := by
  have hopen : support g ⊆ Ioo a b := by
    simpa only [Function.comp_def, interior_Icc] using hc.isOpen_support.subset_interior_iff.mpr hs
  constructor
  · by_contra h
    exact (lt_irrefl a) (hopen h).1
  · by_contra h
    exact (lt_irrefl b) (hopen h).2

/-- Compact radial support makes the finite interval integral the whole-line integral. -/
theorem aliasIntegral_eq_wholeAlias {a b M : ℝ} {v Y : E} {g : ℝ × E → F}
    (hc : Continuous g) (hs : RadiallySupported a b g) :
    aliasIntegral a b M v Y g = wholeAlias M v Y g := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  have hopen : support (fun u => g (shift M v Y u)) ⊆ Ioo a b := by
    simpa only [Function.comp_def, interior_Icc] using
      (hc.comp (shift_continuous M v Y)).isOpen_support.subset_interior_iff.mpr
        (shifted_support_subset hs M v Y)
  exact hopen.trans Ioo_subset_Ioc_self

/-- One integration by parts, including the minus sign and the inverse factor. -/
theorem aliasIntegral_directionalDeriv [CompleteSpace F]
    {a b M : ℝ} {v Y : E} {g : ℝ × E → F}
    (hM : M ≠ 0) (hg : ContDiff ℝ 1 g) (hs : RadiallySupported a b g) :
    aliasIntegral a b M v Y (directionalDeriv v g) =
      (-M⁻¹) • aliasIntegral a b M v Y (slowDeriv g) := by
  have hslow : Continuous (fun u => slowDeriv g (shift M v Y u)) :=
    (slowDeriv_continuous hg).comp (shift_continuous M v Y)
  have hdir : Continuous (fun u => directionalDeriv v g (shift M v Y u)) :=
    (directionalDeriv_continuous hg v).comp (shift_continuous M v Y)
  have hscaled : Continuous (fun u => M • directionalDeriv v g (shift M v Y u)) :=
    continuous_const.smul hdir
  have hboundary := endpoint_zero_of_support (hg.continuous.comp (shift_continuous M v Y))
    (shifted_support_subset hs M v Y)
  dsimp only [Function.comp_apply] at hboundary
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => shifted_hasDerivAt ((hg.differentiable (by norm_num)) (shift M v Y u)))
    ((hslow.add hscaled).intervalIntegrable a b)
  rw [hboundary.1, hboundary.2, sub_self,
    intervalIntegral.integral_add (hslow.intervalIntegrable a b)
      (hscaled.intervalIntegrable a b), intervalIntegral.integral_smul] at hFTC
  have hsum : aliasIntegral a b M v Y (slowDeriv g) +
      M • aliasIntegral a b M v Y (directionalDeriv v g) = 0 := hFTC
  have hscaledEq : M • aliasIntegral a b M v Y (directionalDeriv v g) =
      -aliasIntegral a b M v Y (slowDeriv g) := by
    simpa only [add_sub_cancel_left, zero_sub] using
      congrArg (fun z => z - aliasIntegral a b M v Y (slowDeriv g)) hsum
  have h := congrArg (fun z => M⁻¹ • z) hscaledEq
  simpa only [smul_smul, inv_mul_cancel₀ hM, one_smul, smul_neg, neg_smul] using h

theorem wholeAlias_directionalDeriv [CompleteSpace F]
    {a b M : ℝ} {v Y : E} {g : ℝ × E → F}
    (hM : M ≠ 0) (hg : ContDiff ℝ 1 g) (hs : RadiallySupported a b g) :
    wholeAlias M v Y (directionalDeriv v g) =
      (-M⁻¹) • wholeAlias M v Y (slowDeriv g) := by
  rw [← aliasIntegral_eq_wholeAlias (directionalDeriv_continuous hg v)
      (radialSupport_directionalDeriv hs v),
    ← aliasIntegral_eq_wholeAlias (slowDeriv_continuous hg) (radialSupport_slowDeriv hs)]
  exact aliasIntegral_directionalDeriv hM hg hs

/-- Successive actual slow derivatives of directional primitives. -/
def sourceJet (J : (ℝ × E → F) → (ℝ × E → F)) (f : ℝ × E → F) (p : ℕ) :
    ℝ × E → F := (slowDeriv ∘ J)^[p] f

@[simp] theorem sourceJet_zero (J : (ℝ × E → F) → (ℝ × E → F)) (f : ℝ × E → F) :
    sourceJet J f 0 = f := rfl

theorem sourceJet_succ (J : (ℝ × E → F) → (ℝ × E → F)) (f : ℝ × E → F) (p : ℕ) :
    sourceJet J f (p + 1) = slowDeriv (J (sourceJet J f p)) := by
  simp only [sourceJet, Function.iterate_succ_apply', Function.comp_apply]

/-- When the inverse commutes with slow differentiation, these are literally
`∂u^p (J^p f)`, as in the manuscript. -/
theorem sourceJet_eq_deriv_inverse_iterate
    (J : (ℝ × E → F) → (ℝ × E → F)) (f : ℝ × E → F) (p : ℕ)
    (hcomm : Function.Commute slowDeriv J) :
    sourceJet J f p = slowDeriv^[p] (J^[p] f) := by
  rw [sourceJet, hcomm.comp_iterate]
  rfl

/-- Arbitrarily many integrations by parts. The hypotheses concern actual
directional derivatives, smoothness and support; no integral estimate is assumed. -/
theorem wholeAlias_sourceJet [CompleteSpace F] {a b M : ℝ} {v Y : E}
    (J : (ℝ × E → F) → (ℝ × E → F)) (f : ℝ × E → F) (p : ℕ) (hM : M ≠ 0)
    (hJ : ∀ n < p, ContDiff ℝ 1 (J (sourceJet J f n)))
    (hs : ∀ n < p, RadiallySupported a b (J (sourceJet J f n)))
    (hr : ∀ n < p, directionalDeriv v (J (sourceJet J f n)) = sourceJet J f n) :
    wholeAlias M v Y f = (-M⁻¹) ^ p • wholeAlias M v Y (sourceJet J f p) := by
  revert hJ hs hr
  induction p with
  | zero =>
      intro hJ hs hr
      simp only [sourceJet_zero, pow_zero, one_smul]
  | succ p ih =>
      intro hJ hs hr
      have hp := ih (fun n hn => hJ n (Nat.lt_trans hn (Nat.lt_succ_self p)))
        (fun n hn => hs n (Nat.lt_trans hn (Nat.lt_succ_self p)))
        (fun n hn => hr n (Nat.lt_trans hn (Nat.lt_succ_self p)))
      have hstep := wholeAlias_directionalDeriv hM (hJ p (Nat.lt_succ_self p))
        (hs p (Nat.lt_succ_self p)) (v := v) (Y := Y)
      rw [hr p (Nat.lt_succ_self p), ← sourceJet_succ] at hstep
      rw [hp, hstep, smul_smul, ← pow_succ]

/-- The manuscript's literal `∂u^p J^p` form, with the sign displayed. -/
theorem wholeAlias_inverse_iterate [CompleteSpace F] {a b M : ℝ} {v Y : E}
    (J : (ℝ × E → F) → (ℝ × E → F)) (f : ℝ × E → F) (p : ℕ) (hM : M ≠ 0)
    (hcomm : Function.Commute slowDeriv J)
    (hJ : ∀ n < p, ContDiff ℝ 1 (J (sourceJet J f n)))
    (hs : ∀ n < p, RadiallySupported a b (J (sourceJet J f n)))
    (hr : ∀ n < p, directionalDeriv v (J (sourceJet J f n)) = sourceJet J f n) :
    wholeAlias M v Y f = (-M⁻¹) ^ p •
      wholeAlias M v Y (slowDeriv^[p] (J^[p] f)) := by
  rw [← sourceJet_eq_deriv_inverse_iterate J f p hcomm]
  exact wholeAlias_sourceJet J f p hM hJ hs hr

theorem sourceJet_continuous
    (J : (ℝ × E → F) → (ℝ × E → F)) (f : ℝ × E → F) (p : ℕ)
    (hf : Continuous f) (hJ : ∀ n < p, ContDiff ℝ 1 (J (sourceJet J f n))) :
    Continuous (sourceJet J f p) := by
  cases p with
  | zero => exact hf
  | succ p =>
      rw [sourceJet_succ]
      exact slowDeriv_continuous (hJ p (Nat.lt_succ_self p))

theorem sourceJet_radiallySupported {a b : ℝ}
    (J : (ℝ × E → F) → (ℝ × E → F)) (f : ℝ × E → F) (p : ℕ)
    (hf : RadiallySupported a b f)
    (hs : ∀ n < p, RadiallySupported a b (J (sourceJet J f n))) :
    RadiallySupported a b (sourceJet J f p) := by
  cases p with
  | zero => exact hf
  | succ p =>
      rw [sourceJet_succ]
      exact radialSupport_slowDeriv (hs p (Nat.lt_succ_self p))

theorem wholeAlias_norm_le {a b M C : ℝ} {v Y : E} {f : ℝ × E → F}
    (hab : a ≤ b) (hf : Continuous f) (hs : RadiallySupported a b f)
    (hbound : ∀ u ∈ Icc a b, ∀ Z : E, ‖f (u, Z)‖ ≤ C) :
    ‖wholeAlias M v Y f‖ ≤ C * |b - a| := by
  rw [← aliasIntegral_eq_wholeAlias hf hs]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro u hu
  have hu' : u ∈ Icc a b := by
    simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hu
  exact hbound u hu' _

/-- The all-order gain has a constant uniform in the translation parameter Y
and in M whenever the last source-jet bound is uniform. -/
theorem wholeAlias_sourceJet_norm_le [CompleteSpace F] {a b M C : ℝ} {v Y : E}
    (J : (ℝ × E → F) → (ℝ × E → F)) (f : ℝ × E → F) (p : ℕ)
    (hab : a ≤ b) (hM : M ≠ 0) (hf : Continuous f) (hfs : RadiallySupported a b f)
    (hJ : ∀ n < p, ContDiff ℝ 1 (J (sourceJet J f n)))
    (hs : ∀ n < p, RadiallySupported a b (J (sourceJet J f n)))
    (hr : ∀ n < p, directionalDeriv v (J (sourceJet J f n)) = sourceJet J f n)
    (hbound : ∀ u ∈ Icc a b, ∀ Z : E, ‖sourceJet J f p (u, Z)‖ ≤ C) :
    ‖wholeAlias M v Y f‖ ≤ (|M|⁻¹) ^ p * (C * |b - a|) := by
  rw [wholeAlias_sourceJet J f p hM hJ hs hr, norm_smul, Real.norm_eq_abs,
    abs_pow, abs_neg, abs_inv]
  exact mul_le_mul_of_nonneg_left
    (wholeAlias_norm_le hab (sourceJet_continuous J f p hf hJ)
      (sourceJet_radiallySupported J f p hfs hs) hbound)
    (pow_nonneg (inv_nonneg.mpr (abs_nonneg M)) p)

end NavierStokes.RadialAlias

end
end

end

@[expose] public section

noncomputable section

open Set Function MeasureTheory Filter
open scoped ContDiff Interval Topology

namespace NavierStokes.TransportPrimitive

universe u

section ParameterIntegral

variable {H G : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ H] [NormedSpace ℝ G] in
/-- Continuity gives a uniform bound near a parameter value on a compact interval.
The parameter space need not be finite dimensional. -/
theorem uniform_local_bound {g : H × ℝ → G} (hg : Continuous g) (x : H) (a b : ℝ) :
    ∃ ε > 0, ∃ C : ℝ, ∀ y ∈ Metric.ball x ε, ∀ u ∈ uIcc a b, ‖g (y, u)‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    (hg.comp (continuous_const.prodMk continuous_id)).continuousOn
  let S : Set (H × ℝ) := {z | ‖g z‖ < C + 1}
  have hS : IsOpen S := isOpen_lt hg.norm continuous_const
  have hsub : ({x} : Set H) ×ˢ uIcc a b ⊆ S := by
    rintro ⟨y, u⟩ ⟨hy, hu⟩
    simp only [mem_singleton_iff] at hy
    subst y
    exact lt_of_le_of_lt (hC u hu) (lt_add_one C)
  obtain ⟨V, W, hV, _, hxV, hW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hS hsub
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (hxV (mem_singleton x)))
  exact ⟨ε, hε, C + 1, fun y hy u hu => (hVW ⟨hball hy, hW hu⟩).le⟩

/-- The parameter derivative of a jointly smooth integrand. -/
noncomputable def parameterDerivative (g : H × ℝ → G) (z : H × ℝ) : H →L[ℝ] G :=
  (fderiv ℝ g z).comp (ContinuousLinearMap.inl ℝ H ℝ)

theorem parameterDerivative_contDiff {g : H × ℝ → G} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (parameterDerivative g) := by
  exact (hg.fderiv_right (by simp)).clm_comp contDiff_const

theorem parameter_hasFDerivAt {g : H × ℝ → G} (hg : ContDiff ℝ ∞ g)
    (x : H) (u : ℝ) :
    HasFDerivAt (fun y => g (y, u)) (parameterDerivative g (x, u)) x := by
  simpa only [Function.comp_def, parameterDerivative] using
    ((hg.differentiable (by simp)) (x, u)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const u x))

theorem parameterIntegral_hasFDerivAt {g : H × ℝ → G} (hg : ContDiff ℝ ∞ g)
    (a b : ℝ) (x : H) :
    HasFDerivAt (fun y => ∫ u in a..b, g (y, u))
      (∫ u in a..b, parameterDerivative g (x, u)) x := by
  obtain ⟨ε, hε, C, hC⟩ := uniform_local_bound
    (parameterDerivative_contDiff hg).continuous x a b
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y u => parameterDerivative g (y, u)) (bound := fun _ => C) (Metric.ball_mem_nhds _
        hε)
  · exact Eventually.of_forall fun y =>
      (hg.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hg.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact ((parameterDerivative_contDiff hg).continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun u hu y hy => hC y hy u (uIoc_subset_uIcc hu)
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun u _ y _ => parameter_hasFDerivAt hg y u

/-- Smoothness of a genuine integral over a fixed finite interval, with arbitrary
normed parameter space and Banach-valued output. -/
theorem parameterIntegral_contDiff_nat (n : ℕ) :
    ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {g : H × ℝ → G}, ContDiff ℝ ∞ g → ∀ a b : ℝ,
        ContDiff ℝ (n : ℕ∞) (fun y => ∫ u in a..b, g (y, u)) := by
  induction n with
  | zero =>
    intro G _ _ _ g hg a b
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun x =>
      (parameterIntegral_hasFDerivAt hg a b x).continuousAt)
  | succ n ih =>
    intro G _ _ _ g hg a b
    rw [show ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 by simp]
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨fun x => ∫ u in a..b, parameterDerivative g (x, u),
      ih (parameterDerivative_contDiff hg) a b, parameterIntegral_hasFDerivAt hg a b⟩

theorem parameterIntegral_contDiff [CompleteSpace G] {g : H × ℝ → G}
    (hg : ContDiff ℝ ∞ g) (a b : ℝ) :
    ContDiff ℝ ∞ (fun y => ∫ u in a..b, g (y, u)) :=
  contDiff_infty.mpr fun n => parameterIntegral_contDiff_nat n hg a b

end ParameterIntegral

section Shifted

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A fixed translation along the transport direction. -/
noncomputable def shift (M : ℝ) (v : E) (z : ℝ × E) (u : ℝ) : ℝ × E :=
  z + (u, (M * u) • v)

/-- The past half-line primitive, in fixed integration coordinates. -/
noncomputable def pastIntegral (M : ℝ) (v : E) (f : ℝ × E → F) (z : ℝ × E) : F :=
  ∫ u in Iic (0 : ℝ), f (shift M v z u)

/-- The complete translated radial integral. -/
noncomputable def totalIntegral (M : ℝ) (v : E) (f : ℝ × E → F) (z : ℝ × E) : F :=
  ∫ u : ℝ, f (shift M v z u)

/-- Compactification with a fixed radial cutoff. -/
noncomputable def compactIntegral (χ : ℝ → ℝ) (M : ℝ) (v : E)
    (f : ℝ × E → F) (z : ℝ × E) : F :=
  pastIntegral M v f z - χ z.1 • totalIntegral M v f z

@[simp] theorem shift_fst (M : ℝ) (v : E) (z : ℝ × E) (u : ℝ) :
    (shift M v z u).1 = z.1 + u := rfl

@[simp] theorem shift_snd (M : ℝ) (v : E) (z : ℝ × E) (u : ℝ) :
    (shift M v z u).2 = z.2 + (M * u) • v := rfl

@[simp] theorem shift_zero (M : ℝ) (v : E) (z : ℝ × E) : shift M v z 0 = z := by
  simp [shift]

theorem shift_contDiff (M : ℝ) (v : E) :
    ContDiff ℝ ∞ (fun p : (ℝ × E) × ℝ => shift M v p.1 p.2) := by
  dsimp only [shift]
  exact contDiff_fst.add (contDiff_snd.prodMk
    ((contDiff_const.mul contDiff_snd).smul contDiff_const))

omit [NormedSpace ℝ F] in
theorem shifted_continuous {f : ℝ × E → F} (hf : Continuous f)
    (M : ℝ) (v : E) (z : ℝ × E) : Continuous (fun u => f (shift M v z u)) := by
  exact hf.comp ((shift_contDiff M v).continuous.comp (continuous_const.prodMk continuous_id))

omit [NormedSpace ℝ F] in
theorem shifted_support_subset {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    support (fun u => f (shift M v z u)) ⊆ Icc (a - z.1) (b - z.1) := by
  intro u hu
  have h := hs hu
  change a ≤ z.1 + u ∧ z.1 + u ≤ b at h
  constructor <;> linarith [h.1, h.2]

omit [NormedSpace ℝ F] in
theorem shifted_integrable {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    Integrable (fun u => f (shift M v z u)) := by
  exact (shifted_continuous hf M v z).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (shifted_support_subset hs z))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem radial_zero_of_lt {a b : ℝ} {f : ℝ × E → F}
    (hs : RadialAlias.RadiallySupported a b f) {z : ℝ × E} (hz : z.1 < a) : f z = 0 := by
  by_contra hn
  exact (not_le_of_gt hz) (hs hn).1

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem radial_zero_of_gt {a b : ℝ} {f : ℝ × E → F}
    (hs : RadialAlias.RadiallySupported a b f) {z : ℝ × E} (hz : b < z.1) : f z = 0 := by
  by_contra hn
  exact (not_le_of_gt hz) (hs hn).2

/-- The past integral is locally a finite interval integral with fixed endpoints. -/
theorem pastIntegral_eq_interval {a b M c : ℝ} {v : E} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f)
    (z : ℝ × E) (hc : z.1 + c < a) :
    pastIntegral M v f z = ∫ u in c..0, f (shift M v z u) := by
  have hi := shifted_integrable (M := M) (v := v) hf hs z
  have hz : (∫ u in Iic c, f (shift M v z u)) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu =>
      radial_zero_of_lt hs (by change u ≤ c at hu; simp only [shift_fst]; linarith)
  simpa only [hz, sub_zero, pastIntegral] using
    intervalIntegral.integral_Iic_sub_Iic (hi.integrableOn (s := Iic c))
      (hi.integrableOn (s := Iic 0))

theorem totalIntegral_eq_interval {a b M c d : ℝ} {v : E} {f : ℝ × E → F}
    (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E)
    (hc : z.1 + c < a) (hd : b ≤ z.1 + d) :
    totalIntegral M v f z = ∫ u in c..d, f (shift M v z u) := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro u hu
  have h := hs hu
  change a ≤ z.1 + u ∧ z.1 + u ≤ b at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem pastIntegral_eventually_eq_interval {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    pastIntegral M v f =ᶠ[𝓝 z]
      (fun y => ∫ u in (a - z.1 - 1)..0, f (shift M v y u)) := by
  have hn : {y : ℝ × E | y.1 < z.1 + 1} ∈ 𝓝 z :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds (by dsimp; linarith)
  filter_upwards [hn] with y hy
  exact pastIntegral_eq_interval hf hs y (by change y.1 < z.1 + 1 at hy; linarith)

theorem totalIntegral_eventually_eq_interval {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    totalIntegral M v f =ᶠ[𝓝 z]
      (fun y => ∫ u in (a - z.1 - 1)..(b - z.1 + 1), f (shift M v y u)) := by
  have hn : {y : ℝ × E | z.1 - 1 < y.1 ∧ y.1 < z.1 + 1} ∈ 𝓝 z :=
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)).mem_nhds (by constructor <;> dsimp <;> linarith)
  filter_upwards [hn] with y hy
  change z.1 - 1 < y.1 ∧ y.1 < z.1 + 1 at hy
  exact totalIntegral_eq_interval hs y (by linarith [hy.2]) (by linarith [hy.1])

theorem pastIntegral_contDiff [CompleteSpace F] {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) :
    ContDiff ℝ ∞ (pastIntegral M v f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (parameterIntegral_contDiff (hf.comp (shift_contDiff M v))
    (a - z.1 - 1) 0).contDiffAt.congr_of_eventuallyEq
      (pastIntegral_eventually_eq_interval hf.continuous hs z)

theorem totalIntegral_contDiff [CompleteSpace F] {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) :
    ContDiff ℝ ∞ (totalIntegral M v f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (parameterIntegral_contDiff (hf.comp (shift_contDiff M v))
    (a - z.1 - 1) (b - z.1 + 1)).contDiffAt.congr_of_eventuallyEq
      (totalIntegral_eventually_eq_interval hs z)

theorem compactIntegral_contDiff [CompleteSpace F] {a b M : ℝ} {v : E}
    {f : ℝ × E → F} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) :
    ContDiff ℝ ∞ (compactIntegral χ M v f) :=
  (pastIntegral_contDiff hf hs).sub ((hχ.comp contDiff_fst).smul (totalIntegral_contDiff hf hs))

/-- All actual Fréchet derivatives retain radial support. -/
theorem radialSupport_fderiv {a b : ℝ} {f : ℝ × E → F}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (fderiv ℝ f) := by
  have hts : tsupport f ⊆ Prod.fst ⁻¹' Icc a b :=
    closure_minimal hs (isClosed_Icc.preimage continuous_fst)
  intro z hz
  by_contra hn
  exact hz (fderiv_of_notMem_tsupport ℝ (fun h => hn (hts h)))

theorem parameterDerivative_shifted {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f)
    (M : ℝ) (v : E) (z : ℝ × E) (u : ℝ) :
    parameterDerivative (fun p : (ℝ × E) × ℝ => f (shift M v p.1 p.2)) (z, u) =
      fderiv ℝ f (shift M v z u) := by
  apply (parameter_hasFDerivAt (hf.comp (shift_contDiff M v)) z u).unique
  simpa only [id_eq, shift, ContinuousLinearMap.comp_id, Function.comp_def] using
    ((hf.differentiable (by simp)) (shift M v z u)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).add_const (u, (M * u) • v))

/-- The entire Fréchet derivative commutes with the fixed-u past integral. -/
theorem pastIntegral_hasFDerivAt {a b M : ℝ} {v : E}
    {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (z : ℝ × E) :
    HasFDerivAt (pastIntegral M v f) (pastIntegral M v (fderiv ℝ f) z) z := by
  have h := parameterIntegral_hasFDerivAt (hf.comp (shift_contDiff M v)) (a - z.1 - 1) 0 z
  dsimp only [Function.comp_def] at h
  simp_rw [parameterDerivative_shifted hf] at h
  rw [← pastIntegral_eq_interval (hf.fderiv_right (m := ∞) (by simp)).continuous
    (radialSupport_fderiv hs) z (by linarith : z.1 + (a - z.1 - 1) < a)] at h
  exact h.congr_of_eventuallyEq (pastIntegral_eventually_eq_interval hf.continuous hs z)

theorem totalIntegral_hasFDerivAt {a b M : ℝ} {v : E}
    {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (z : ℝ × E) :
    HasFDerivAt (totalIntegral M v f) (totalIntegral M v (fderiv ℝ f) z) z := by
  have h := parameterIntegral_hasFDerivAt (hf.comp (shift_contDiff M v))
    (a - z.1 - 1) (b - z.1 + 1) z
  dsimp only [Function.comp_def] at h
  simp_rw [parameterDerivative_shifted hf] at h
  rw [← totalIntegral_eq_interval (radialSupport_fderiv hs) z
    (by linarith : z.1 + (a - z.1 - 1) < a)
    (by linarith : b ≤ z.1 + (b - z.1 + 1))] at h
  exact h.congr_of_eventuallyEq (totalIntegral_eventually_eq_interval hs z)

/-- An ordinary derivative in any fixed direction, including a slow parameter. -/
noncomputable def fixedDeriv (w : ℝ × E) (f : ℝ × E → F) (z : ℝ × E) : F :=
  fderiv ℝ f z w

theorem fixedDeriv_contDiff {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) (w : ℝ × E) :
    ContDiff ℝ ∞ (fixedDeriv w f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem fixedDeriv_supported {a b : ℝ} {f : ℝ × E → F}
    (hs : RadialAlias.RadiallySupported a b f) (w : ℝ × E) :
    RadialAlias.RadiallySupported a b (fixedDeriv w f) :=
  RadialAlias.radialSupport_fderiv_apply hs w

theorem fixedDeriv_pastIntegral {a b M : ℝ} {v : E}
    {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (w z : ℝ × E) :
    fixedDeriv w (pastIntegral M v f) z = pastIntegral M v (fixedDeriv w f) z := by
  rw [fixedDeriv, (pastIntegral_hasFDerivAt hf hs z).fderiv]
  exact ContinuousLinearMap.integral_apply
    ((shifted_integrable (M := M) (v := v) (hf.fderiv_right (m := ∞) (by simp)).continuous
      (radialSupport_fderiv hs) z).integrableOn) w

theorem fixedDeriv_totalIntegral {a b M : ℝ} {v : E}
    {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (w z : ℝ × E) :
    fixedDeriv w (totalIntegral M v f) z = totalIntegral M v (fixedDeriv w f) z := by
  rw [fixedDeriv, (totalIntegral_hasFDerivAt hf hs z).fderiv]
  exact ContinuousLinearMap.integral_apply
    (shifted_integrable (M := M) (v := v) (hf.fderiv_right (m := ∞) (by simp)).continuous
      (radialSupport_fderiv hs) z) w

theorem shift_hasDerivAt (M : ℝ) (v : E) (z : ℝ × E) (u : ℝ) :
    HasDerivAt (shift M v z) (1, M • v) u := by
  unfold shift
  have h := ((hasDerivAt_const u z.1).add (hasDerivAt_id u)).prodMk
    ((hasDerivAt_const u z.2).add (((hasDerivAt_id u).const_mul M).smul_const v))
  simpa only [id_eq, Pi.add_apply, shift, zero_add, mul_one, Prod.add_def] using h

theorem shifted_hasDerivAt {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f)
    (M : ℝ) (v : E) (z : ℝ × E) (u : ℝ) :
    HasDerivAt (fun t => f (shift M v z t))
      (fixedDeriv (1, M • v) f (shift M v z u)) u :=
  ((hf.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt u (shift_hasDerivAt M v z u)

/-- The exact transport identity, proved by the fundamental theorem of calculus. -/
theorem transport_pastIntegral [CompleteSpace F] {a b M : ℝ} {v : E}
    {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (z : ℝ × E) : fixedDeriv (1, M • v) (pastIntegral M v f) z = f z := by
  rw [fixedDeriv_pastIntegral hf hs]
  rw [pastIntegral_eq_interval (fixedDeriv_contDiff hf _).continuous
    (fixedDeriv_supported hs _) z (c := a - z.1 - 1) (by linarith)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => shifted_hasDerivAt hf M v z u)
    ((shifted_continuous (fixedDeriv_contDiff hf _).continuous M v z).intervalIntegrable _ _)]
  rw [shift_zero, radial_zero_of_lt (z := shift M v z (a - z.1 - 1)) hs
    (by simp only [shift_fst]; linarith), sub_zero]

/-- The complete translated integral is constant along each transport line. -/
theorem transport_totalIntegral [CompleteSpace F] {a b M : ℝ} {v : E}
    {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (z : ℝ × E) : fixedDeriv (1, M • v) (totalIntegral M v f) z = 0 := by
  rw [fixedDeriv_totalIntegral hf hs]
  rw [totalIntegral_eq_interval (fixedDeriv_supported hs _) z
    (c := a - z.1 - 1) (d := b - z.1 + 1) (by linarith) (by linarith)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => shifted_hasDerivAt hf M v z u)
    ((shifted_continuous (fixedDeriv_contDiff hf _).continuous M v z).intervalIntegrable _ _)]
  rw [radial_zero_of_gt (z := shift M v z (b - z.1 + 1)) hs
      (by simp only [shift_fst]; linarith),
    radial_zero_of_lt (z := shift M v z (a - z.1 - 1)) hs
      (by simp only [shift_fst]; linarith), sub_self]

/-- This derivative is exactly `∂U + M v·∂Y`. -/
theorem transport_eq_partials (M : ℝ) (v : E) (f : ℝ × E → F) (z : ℝ × E) :
    fixedDeriv (1, M • v) f z = fixedDeriv (1, 0) f z + M • fixedDeriv (0, v) f z := by
  have hv : ((1 : ℝ), M • v) = (1, (0 : E)) + M • ((0 : ℝ), v) := by
    ext <;> simp
  simp only [fixedDeriv, hv, map_add, map_smul]

/-- The cutoff product rule retains the actual ordinary radial derivative. -/
theorem fixedDeriv_compactIntegral {a b M : ℝ} {v : E}
    {f : ℝ × E → F} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (w z : ℝ × E) :
    fixedDeriv w (compactIntegral χ M v f) z =
      compactIntegral χ M v (fixedDeriv w f) z -
        (deriv χ z.1 * w.1) • totalIntegral M v f z := by
  have hχd := ((hχ.differentiable (by simp)) z.1).hasFDerivAt.comp z
    hasFDerivAt_fst
  have h := (pastIntegral_hasFDerivAt (M := M) (v := v) hf hs z).sub
    (hχd.smul (totalIntegral_hasFDerivAt (M := M) (v := v) hf hs z))
  change HasFDerivAt (compactIntegral χ M v f) _ z at h
  have hi := fixedDeriv_pastIntegral (M := M) (v := v) hf hs w z
  have hj := fixedDeriv_totalIntegral (M := M) (v := v) hf hs w z
  change (fderiv ℝ (pastIntegral M v f) z) w = _ at hi
  change (fderiv ℝ (totalIntegral M v f) z) w = _ at hj
  rw [(pastIntegral_hasFDerivAt hf hs z).fderiv] at hi
  rw [(totalIntegral_hasFDerivAt hf hs z).fderiv] at hj
  change (fderiv ℝ (compactIntegral χ M v f) z) w = _
  rw [h.fderiv]
  simp only [_root_.sub_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', fderiv_eq_deriv_mul,
    Function.comp_apply, hi, hj, compactIntegral]
  abel

theorem transport_compactIntegral [CompleteSpace F] {a b M : ℝ} {v : E}
    {f : ℝ × E → F} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (z : ℝ × E) :
    fixedDeriv (1, M • v) (compactIntegral χ M v f) z =
      f z - deriv χ z.1 • totalIntegral M v f z := by
  rw [fixedDeriv_compactIntegral hχ hf hs]
  unfold compactIntegral
  rw [← fixedDeriv_pastIntegral hf hs, ← fixedDeriv_totalIntegral hf hs,
    transport_pastIntegral hf hs, transport_totalIntegral hf hs]
  simp

theorem auxiliaryDeriv_compactIntegral {a b M : ℝ} {v : E}
    {f : ℝ × E → F} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (w : E) (z : ℝ × E) :
    fixedDeriv (0, w) (compactIntegral χ M v f) z =
      compactIntegral χ M v (fixedDeriv (0, w) f) z := by
  simpa only [mul_zero, zero_smul, sub_zero] using fixedDeriv_compactIntegral hχ hf hs (0, w) z

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem radial_zero_of_le {a b : ℝ} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f)
    {z : ℝ × E} (hz : z.1 ≤ a) : f z = 0 := by
  have hc : Continuous (fun u : ℝ => f (u, z.2)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hsupport : support (fun u : ℝ => f (u, z.2)) ⊆ Ioo a b := by
    simpa only [interior_Icc] using hc.isOpen_support.subset_interior_iff.mpr
      (show support (fun u : ℝ => f (u, z.2)) ⊆ Icc a b from fun u hu => hs hu)
  by_contra hn
  exact (not_lt_of_ge hz) (hsupport hn).1

theorem pastIntegral_eq_zero_of_le {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f)
    (z : ℝ × E) (hz : z.1 ≤ a) : pastIntegral M v f z = 0 := by
  exact setIntegral_eq_zero_of_forall_eq_zero fun u hu =>
    radial_zero_of_le hf hs (by change u ≤ 0 at hu; simp only [shift_fst]; linarith)

theorem pastIntegral_eq_total_of_ge {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hs : RadialAlias.RadiallySupported a b f)
    (z : ℝ × E) (hz : b ≤ z.1) : pastIntegral M v f z = totalIntegral M v f z := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  have hu' : 0 < u := not_le.mp hu
  exact radial_zero_of_gt hs (by simp only [shift_fst]; linarith)

theorem compactIntegral_supported {a b M : ℝ} {v : E} {f : ℝ × E → F} {χ : ℝ → ℝ}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1) :
    RadialAlias.RadiallySupported a b (compactIntegral χ M v f) := by
  intro z hz
  change compactIntegral χ M v f z ≠ 0 at hz
  constructor
  · by_contra hn
    have hza : z.1 ≤ a := le_of_not_ge hn
    exact hz (by simp [compactIntegral, pastIntegral_eq_zero_of_le hf hs z hza, hleft _ hza])
  · by_contra hn
    have hzb : b ≤ z.1 := le_of_not_ge hn
    exact hz (by simp [compactIntegral, pastIntegral_eq_total_of_ge hs z hzb, hright _ hzb])

/-- An explicit smooth transition with specified plateau thresholds. -/
noncomputable def cutoff (c d : ℝ) (u : ℝ) : ℝ :=
  Real.smoothTransition ((u - c) / (d - c))

theorem cutoff_contDiff (c d : ℝ) : ContDiff ℝ ∞ (cutoff c d) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem cutoff_zero {c d u : ℝ} (hcd : c < d) (hu : u ≤ c) : cutoff c d u = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu)
    (sub_nonneg.mpr hcd.le))

theorem cutoff_one {c d u : ℝ} (hcd : c < d) (hu : d ≤ u) : cutoff c d u = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hcd)).mpr (by linarith))

theorem cutoff_mem_Icc (c d u : ℝ) : cutoff c d u ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The canonical cutoff has both plateaus strictly inside the support interval. -/
noncomputable def interiorCutoff (a b : ℝ) : ℝ → ℝ :=
  cutoff ((2 * a + b) / 3) ((a + 2 * b) / 3)

theorem interiorCutoff_contDiff (a b : ℝ) : ContDiff ℝ ∞ (interiorCutoff a b) :=
  cutoff_contDiff _ _

theorem interiorCutoff_zero {a b u : ℝ} (hab : a < b) (hu : u ≤ (2 * a + b) / 3) :
    interiorCutoff a b u = 0 := cutoff_zero (by linarith) hu

theorem interiorCutoff_one {a b u : ℝ} (hab : a < b) (hu : (a + 2 * b) / 3 ≤ u) :
    interiorCutoff a b u = 1 := cutoff_one (by linarith) hu

theorem canonicalCompact_supported {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hab : a < b) (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (compactIntegral (interiorCutoff a b) M v f) :=
  compactIntegral_supported hf hs
    (fun u hu => interiorCutoff_zero hab (by linarith))
    (fun u hu => interiorCutoff_one hab (by linarith))

/-- The complementary future integral used at the right support edge. -/
noncomputable def futureIntegral (M : ℝ) (v : E) (f : ℝ × E → F) (z : ℝ × E) : F :=
  ∫ u in Ioi (0 : ℝ), f (shift M v z u)

theorem past_add_future {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    pastIntegral M v f z + futureIntegral M v f z = totalIntegral M v f z :=
  intervalIntegral.integral_Iic_add_Ioi (shifted_integrable hf hs z).integrableOn
    (shifted_integrable hf hs z).integrableOn

theorem compactIntegral_eq_neg_future {a b M : ℝ} {v : E}
    {f : ℝ × E → F} {χ : ℝ → ℝ} (hf : Continuous f)
    (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) (hχ : χ z.1 = 1) :
    compactIntegral χ M v f z = -futureIntegral M v f z := by
  rw [compactIntegral, hχ, one_smul, ← past_add_future hf hs]
  abel

theorem pastIntegral_eq_supportInterval {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    pastIntegral M v f z = ∫ u in (a - z.1)..0, f (shift M v z u) := by
  have hi := shifted_integrable (M := M) (v := v) hf hs z
  have hz : (∫ u in Iic (a - z.1), f (shift M v z u)) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu =>
      radial_zero_of_le hf hs
        (by change u ≤ a - z.1 at hu; simp only [shift_fst]; linarith)
  simpa only [hz, sub_zero, pastIntegral] using
    intervalIntegral.integral_Iic_sub_Iic (hi.integrableOn (s := Iic (a - z.1)))
      (hi.integrableOn (s := Iic 0))

theorem totalIntegral_eq_supportInterval {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    totalIntegral M v f z = ∫ u in (a - z.1)..(b - z.1), f (shift M v z u) := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  have ho : support (fun u => f (shift M v z u)) ⊆ Ioo (a - z.1) (b - z.1) := by
    simpa only [interior_Icc] using
      (shifted_continuous hf M v z).isOpen_support.subset_interior_iff.mpr
        (shifted_support_subset hs z)
  exact ho.trans Ioo_subset_Ioc_self

/-- The alternative radial-coordinate formula is derived by translation. -/
theorem pastIntegral_eq_radialInterval {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    pastIntegral M v f z = ∫ s in a..z.1, f (s, z.2 + (M * (s - z.1)) • v) := by
  rw [pastIntegral_eq_supportInterval hf hs]
  have heq : (fun u => f (shift M v z u)) =
      (fun u => f (u + z.1, z.2 + (M * ((u + z.1) - z.1)) • v)) := by
    funext u
    congr 1
    ext <;> simp [shift, add_comm]
  rw [heq]
  simpa only [sub_add_cancel, zero_add] using
    (intervalIntegral.integral_comp_add_right
      (fun s => f (s, z.2 + (M * (s - z.1)) • v)) z.1 (a := a - z.1) (b := 0))

theorem totalIntegral_eq_radialInterval {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    totalIntegral M v f z = ∫ s in a..b, f (s, z.2 + (M * (s - z.1)) • v) := by
  rw [totalIntegral_eq_supportInterval hf hs]
  have heq : (fun u => f (shift M v z u)) =
      (fun u => f (u + z.1, z.2 + (M * ((u + z.1) - z.1)) • v)) := by
    funext u
    congr 1
    ext <;> simp [shift, add_comm]
  rw [heq]
  simpa only [sub_add_cancel] using
    (intervalIntegral.integral_comp_add_right
      (fun s => f (s, z.2 + (M * (s - z.1)) • v)) z.1 (a := a - z.1) (b := b - z.1))

theorem futureIntegral_eq_radialInterval {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    futureIntegral M v f z = ∫ s in z.1..b, f (s, z.2 + (M * (s - z.1)) • v) := by
  have hc : Continuous (fun s : ℝ => f (s, z.2 + (M * (s - z.1)) • v)) := by
    exact hf.comp (continuous_id.prodMk
      (continuous_const.add ((continuous_const.mul (continuous_id.sub continuous_const)).smul
        continuous_const)))
  have h := past_add_future (M := M) (v := v) hf hs z
  rw [pastIntegral_eq_radialInterval hf hs, totalIntegral_eq_radialInterval hf hs] at h
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a z.1)
    (hc.intervalIntegrable z.1 b)] at h
  exact add_left_cancel h

theorem totalIntegral_norm_le {a b M C : ℝ} {v : E} {f : ℝ × E → F}
    (hab : a ≤ b) (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f)
    (hbound : ∀ s ∈ Icc a b, ∀ Y : E, ‖f (s, Y)‖ ≤ C) (z : ℝ × E) :
    ‖totalIntegral M v f z‖ ≤ C * (b - a) := by
  rw [totalIntegral_eq_radialInterval hf hs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := C)
    (f := fun s => f (s, z.2 + (M * (s - z.1)) • v)) (a := a) (b := b)
    (fun s hs => hbound s (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hs) _)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h

/-- Only the radial support length enters; there is no power of M in this bound. -/
theorem pastIntegral_norm_le {a b M C : ℝ} {v : E} {f : ℝ × E → F}
    (hab : a ≤ b) (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f)
    (hbound : ∀ s ∈ Icc a b, ∀ Y : E, ‖f (s, Y)‖ ≤ C) (z : ℝ × E) :
    ‖pastIntegral M v f z‖ ≤ C * (b - a) := by
  have hnorm : RadialAlias.RadiallySupported a b (fun x => ‖f x‖) := by
    intro x hx
    exact hs (norm_ne_zero_iff.mp hx)
  calc
    ‖pastIntegral M v f z‖ ≤ ∫ u in Iic (0 : ℝ), ‖f (shift M v z u)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, ‖f (shift M v z u)‖ :=
      setIntegral_le_integral (shifted_integrable hf hs z).norm
        (Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ‖totalIntegral M v (fun x => ‖f x‖) z‖ := Real.le_norm_self _
    _ ≤ C * (b - a) := totalIntegral_norm_le (f := fun x => ‖f x‖) hab hf.norm hnorm
      (fun s hs Y => by simpa only [norm_norm] using hbound s hs Y) z

theorem compactIntegral_norm_le {a b M C K : ℝ} {v : E} {f : ℝ × E → F} {χ : ℝ → ℝ}
    (hab : a ≤ b) (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f)
    (hbound : ∀ s ∈ Icc a b, ∀ Y : E, ‖f (s, Y)‖ ≤ C)
    (hK : 0 ≤ K) (hχ : ∀ u, |χ u| ≤ K) (z : ℝ × E) :
    ‖compactIntegral χ M v f z‖ ≤ (1 + K) * C * (b - a) := by
  have hC : 0 ≤ C := (norm_nonneg (f (a, 0))).trans (hbound a ⟨le_rfl, hab⟩ 0)
  calc
    ‖compactIntegral χ M v f z‖ ≤ ‖pastIntegral M v f z‖ +
        |χ z.1| * ‖totalIntegral M v f z‖ := by
      simpa only [compactIntegral, norm_smul, Real.norm_eq_abs] using
        norm_sub_le (pastIntegral M v f z) (χ z.1 • totalIntegral M v f z)
    _ ≤ C * (b - a) + K * (C * (b - a)) := by
      exact add_le_add (pastIntegral_norm_le hab hf hs hbound z)
        (mul_le_mul (hχ _) (totalIntegral_norm_le hab hf hs hbound z) (norm_nonneg _) hK)
    _ = (1 + K) * C * (b - a) := by ring

theorem pastIntegral_add {a b M : ℝ} {v : E} {f g : ℝ × E → F}
    (hf : Continuous f) (hg : Continuous g)
    (hsf : RadialAlias.RadiallySupported a b f) (hsg : RadialAlias.RadiallySupported a b g)
    (z : ℝ × E) :
    pastIntegral M v (fun x => f x + g x) z = pastIntegral M v f z + pastIntegral M v g z :=
  integral_add (shifted_integrable hf hsf z).integrableOn (shifted_integrable hg hsg z).integrableOn

theorem totalIntegral_add {a b M : ℝ} {v : E} {f g : ℝ × E → F}
    (hf : Continuous f) (hg : Continuous g)
    (hsf : RadialAlias.RadiallySupported a b f) (hsg : RadialAlias.RadiallySupported a b g)
    (z : ℝ × E) :
    totalIntegral M v (fun x => f x + g x) z = totalIntegral M v f z + totalIntegral M v g z :=
  integral_add (shifted_integrable hf hsf z) (shifted_integrable hg hsg z)

theorem compactIntegral_add {a b M : ℝ} {v : E} {f g : ℝ × E → F}
    (hf : Continuous f) (hg : Continuous g)
    (hsf : RadialAlias.RadiallySupported a b f) (hsg : RadialAlias.RadiallySupported a b g)
    (χ : ℝ → ℝ) (z : ℝ × E) :
    compactIntegral χ M v (fun x => f x + g x) z =
      compactIntegral χ M v f z + compactIntegral χ M v g z := by
  simp only [compactIntegral, pastIntegral_add hf hg hsf hsg,
    totalIntegral_add hf hg hsf hsg, smul_add]
  abel

theorem pastIntegral_smul (M c : ℝ) (v : E) (f : ℝ × E → F) (z : ℝ × E) :
    pastIntegral M v (fun x => c • f x) z = c • pastIntegral M v f z := integral_smul c _

theorem totalIntegral_smul (M c : ℝ) (v : E) (f : ℝ × E → F) (z : ℝ × E) :
    totalIntegral M v (fun x => c • f x) z = c • totalIntegral M v f z := integral_smul c _

theorem compactIntegral_smul (χ : ℝ → ℝ) (M c : ℝ) (v : E) (f : ℝ × E → F) (z : ℝ × E) :
    compactIntegral χ M v (fun x => c • f x) z = c • compactIntegral χ M v f z := by
  simp only [compactIntegral, pastIntegral_smul, totalIntegral_smul, smul_sub]
  rw [smul_comm]

theorem iteratedFDeriv_supported {a b : ℝ} {f : ℝ × E → F}
    (hs : RadialAlias.RadiallySupported a b f) (n : ℕ) :
    RadialAlias.RadiallySupported a b (iteratedFDeriv ℝ n f) :=
  (support_iteratedFDeriv_subset n).trans
    (closure_minimal hs (isClosed_Icc.preimage continuous_fst))

theorem iteratedFDeriv_contDiff {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) :=
  hf.iteratedFDeriv_right (by exact_mod_cast (le_top : (⊤ : ℕ∞) + (n : ℕ∞) ≤ ⊤))

/-- Every order of the actual multilinear Fréchet derivative commutes with I. -/
theorem iteratedFDeriv_pastIntegral {a b M : ℝ} {v : E}
    {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (n : ℕ) (z : ℝ × E) :
    iteratedFDeriv ℝ n (pastIntegral M v f) z = pastIntegral M v (iteratedFDeriv ℝ n f) z := by
  induction n generalizing z with
  | zero =>
    let L := (continuousMultilinearCurryFin0 ℝ (ℝ × E) F).symm
    change L (∫ u in Iic (0 : ℝ), f (shift M v z u)) =
      ∫ u in Iic (0 : ℝ), L (f (shift M v z u))
    exact (L.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ n ih =>
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => ℝ × E) F).symm
    have heq : iteratedFDeriv ℝ n (pastIntegral M v f) =
        pastIntegral M v (iteratedFDeriv ℝ n f) := funext ih
    change L (fderiv ℝ (iteratedFDeriv ℝ n (pastIntegral M v f)) z) =
      ∫ u in Iic (0 : ℝ), L (fderiv ℝ (iteratedFDeriv ℝ n f) (shift M v z u))
    rw [heq, (pastIntegral_hasFDerivAt (iteratedFDeriv_contDiff hf n)
      (iteratedFDeriv_supported hs n) z).fderiv]
    exact (L.toContinuousLinearEquiv.integral_comp_comm
      (E := (ℝ × E) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × E) F)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => ℝ × E) F) (𝕜 := ℝ)
      (μ := volume.restrict (Iic (0 : ℝ)))
      (fun u : ℝ => fderiv ℝ (iteratedFDeriv ℝ n f) (shift M v z u))).symm

/-- Every order of the actual multilinear Fréchet derivative commutes with J. -/
theorem iteratedFDeriv_totalIntegral {a b M : ℝ} {v : E}
    {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (n : ℕ) (z : ℝ × E) :
    iteratedFDeriv ℝ n (totalIntegral M v f) z = totalIntegral M v (iteratedFDeriv ℝ n f) z := by
  induction n generalizing z with
  | zero =>
    let L := (continuousMultilinearCurryFin0 ℝ (ℝ × E) F).symm
    change L (∫ u : ℝ, f (shift M v z u)) = ∫ u : ℝ, L (f (shift M v z u))
    exact (L.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ n ih =>
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => ℝ × E) F).symm
    have heq : iteratedFDeriv ℝ n (totalIntegral M v f) =
        totalIntegral M v (iteratedFDeriv ℝ n f) := funext ih
    change L (fderiv ℝ (iteratedFDeriv ℝ n (totalIntegral M v f)) z) =
      ∫ u : ℝ, L (fderiv ℝ (iteratedFDeriv ℝ n f) (shift M v z u))
    rw [heq, (totalIntegral_hasFDerivAt (iteratedFDeriv_contDiff hf n)
      (iteratedFDeriv_supported hs n) z).fderiv]
    exact (L.toContinuousLinearEquiv.integral_comp_comm
      (E := (ℝ × E) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × E) F)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => ℝ × E) F) (𝕜 := ℝ) (μ := volume)
      (fun u : ℝ => fderiv ℝ (iteratedFDeriv ℝ n f) (shift M v z u))).symm

theorem iteratedFDeriv_pastIntegral_norm_le {a b M C : ℝ} {v : E}
    {f : ℝ × E → F} (hab : a ≤ b) (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (n : ℕ)
    (hbound : ∀ s ∈ Icc a b, ∀ Y : E, ‖iteratedFDeriv ℝ n f (s, Y)‖ ≤ C) (z : ℝ × E) :
    ‖iteratedFDeriv ℝ n (pastIntegral M v f) z‖ ≤ C * (b - a) := by
  rw [iteratedFDeriv_pastIntegral hf hs]
  exact pastIntegral_norm_le hab (iteratedFDeriv_contDiff hf n).continuous
    (iteratedFDeriv_supported hs n) hbound z

theorem iteratedFDeriv_totalIntegral_norm_le {a b M C : ℝ} {v : E}
    {f : ℝ × E → F} (hab : a ≤ b) (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (n : ℕ)
    (hbound : ∀ s ∈ Icc a b, ∀ Y : E, ‖iteratedFDeriv ℝ n f (s, Y)‖ ≤ C) (z : ℝ × E) :
    ‖iteratedFDeriv ℝ n (totalIntegral M v f) z‖ ≤ C * (b - a) := by
  rw [iteratedFDeriv_totalIntegral hf hs]
  exact totalIntegral_norm_le hab (iteratedFDeriv_contDiff hf n).continuous
    (iteratedFDeriv_supported hs n) hbound z

theorem iteratedFDeriv_compactIntegral_eq [CompleteSpace F] {a b M : ℝ} {v : E}
    {f : ℝ × E → F} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) (n : ℕ) (z : ℝ × E) :
    iteratedFDeriv ℝ n (compactIntegral χ M v f) z =
      iteratedFDeriv ℝ n (pastIntegral M v f) z -
        iteratedFDeriv ℝ n (fun y => χ y.1 • totalIntegral M v f y) z := by
  have heq : compactIntegral χ M v f =
      pastIntegral M v f + -(fun y => χ y.1 • totalIntegral M v f y) := by
    funext y
    exact sub_eq_add_neg _ _
  have hi : ContDiff ℝ n (pastIntegral M v f) :=
    (pastIntegral_contDiff hf hs).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hg : ContDiff ℝ n (fun y => χ y.1 • totalIntegral M v f y) :=
    ((hχ.comp contDiff_fst).smul (totalIntegral_contDiff hf hs)).of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  rw [heq]
  have hadd := iteratedFDeriv_add_apply (i := n) (x := z)
    (f := pastIntegral M v f) (g := -(fun y => χ y.1 • totalIntegral M v f y))
    hi.contDiffAt hg.neg.contDiffAt
  rw [hadd, iteratedFDeriv_neg_apply]
  exact (sub_eq_add_neg _ _).symm

/-- Full binomial Leibniz bound. Every derivative of the cutoff is retained. -/
theorem iteratedFDeriv_compactIntegral_norm_le [CompleteSpace F] {a b M : ℝ} {v : E}
    {f : ℝ × E → F} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) (n : ℕ) (z : ℝ × E) :
    ‖iteratedFDeriv ℝ n (compactIntegral χ M v f) z‖ ≤
      ‖pastIntegral M v (iteratedFDeriv ℝ n f) z‖ +
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y : ℝ × E => χ y.1) z‖ *
            ‖totalIntegral M v (iteratedFDeriv ℝ (n - i) f) z‖ := by
  have hb := norm_iteratedFDeriv_smul_le (𝕜 := ℝ)
    (hχ.comp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ℝ × E → ℝ)))
    (totalIntegral_contDiff (M := M) (v := v) hf hs) z
    (n := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  simp_rw [iteratedFDeriv_totalIntegral hf hs] at hb
  rw [iteratedFDeriv_compactIntegral_eq hχ hf hs, iteratedFDeriv_pastIntegral hf hs]
  exact (norm_sub_le _ _).trans (add_le_add_right hb _)

/-- Uniform all-order operator-norm estimate from a finite list of genuine source
and cutoff derivative bounds. The constant contains no translation parameter. -/
theorem iteratedFDeriv_compactIntegral_uniform [CompleteSpace F] {a b M : ℝ} {v : E}
    {f : ℝ × E → F} {χ : ℝ → ℝ} (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) (n : ℕ)
    (A B : ℕ → ℝ) (hB : ∀ i ≤ n, 0 ≤ B i)
    (hsource : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ Y : E, ‖iteratedFDeriv ℝ j f (s, Y)‖ ≤ A j)
    (hcutoff : ∀ i ≤ n, ∀ z : ℝ × E, ‖iteratedFDeriv ℝ i (fun y : ℝ × E => χ y.1) z‖ ≤ B i)
    (z : ℝ × E) :
    ‖iteratedFDeriv ℝ n (compactIntegral χ M v f) z‖ ≤
      (A n + ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i * A (n - i)) * (b - a) := by
  have hp : ‖pastIntegral M v (iteratedFDeriv ℝ n f) z‖ ≤ A n * (b - a) :=
    pastIntegral_norm_le hab (iteratedFDeriv_contDiff hf n).continuous
      (iteratedFDeriv_supported hs n) (hsource n le_rfl) z
  have ht : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : ℝ × E => χ y.1) z‖ *
        ‖totalIntegral M v (iteratedFDeriv ℝ (n - i) f) z‖ ≤
      ((n.choose i : ℝ) * B i * A (n - i)) * (b - a) := by
    intro i hi
    have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hj := totalIntegral_norm_le (M := M) (v := v) hab
      (iteratedFDeriv_contDiff hf (n - i)).continuous
      (iteratedFDeriv_supported hs (n - i)) (hsource (n - i) (Nat.sub_le _ _)) z
    calc
      _ ≤ ((n.choose i : ℝ) * B i) * (A (n - i) * (b - a)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hcutoff i hin z) (Nat.cast_nonneg _)) hj
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB i hin))
      _ = _ := by ring
  calc
    _ ≤ ‖pastIntegral M v (iteratedFDeriv ℝ n f) z‖ +
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y : ℝ × E => χ y.1) z‖ *
            ‖totalIntegral M v (iteratedFDeriv ℝ (n - i) f) z‖ :=
      iteratedFDeriv_compactIntegral_norm_le hχ hf hs n z
    _ ≤ A n * (b - a) + ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) * B i * A (n - i)) * (b - a) :=
      add_le_add hp (Finset.sum_le_sum ht)
    _ = _ := by rw [add_mul, Finset.sum_mul]

theorem futureIntegral_eq_total_sub_past {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    futureIntegral M v f z = totalIntegral M v f z - pastIntegral M v f z := by
  have h := past_add_future (M := M) (v := v) hf hs z
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)

theorem futureIntegral_contDiff [CompleteSpace F] {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) :
    ContDiff ℝ ∞ (futureIntegral M v f) := by
  have heq : futureIntegral M v f = fun z => totalIntegral M v f z - pastIntegral M v f z :=
    funext (futureIntegral_eq_total_sub_past hf.continuous hs)
  rw [heq]
  exact (totalIntegral_contDiff hf hs).sub (pastIntegral_contDiff hf hs)

theorem iteratedFDeriv_sub_of_smooth {f g : ℝ × E → F}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (z : ℝ × E) :
    iteratedFDeriv ℝ n (fun y => f y - g y) z =
      iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n g z := by
  have hf' : ContDiff ℝ n f := hf.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hg' : ContDiff ℝ n g := hg.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have heq : (fun y => f y - g y) = f + -g := by
    funext y
    exact sub_eq_add_neg _ _
  rw [heq]
  have hadd := iteratedFDeriv_add_apply (i := n) (x := z) (f := f) (g := -g)
    hf'.contDiffAt hg'.neg.contDiffAt
  rw [hadd, iteratedFDeriv_neg_apply]
  exact (sub_eq_add_neg _ _).symm

/-- The future primitive has the same derivative commutation as the past primitive. -/
theorem iteratedFDeriv_futureIntegral [CompleteSpace F] {a b M : ℝ} {v : E}
    {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (n : ℕ) (z : ℝ × E) :
    iteratedFDeriv ℝ n (futureIntegral M v f) z =
      futureIntegral M v (iteratedFDeriv ℝ n f) z := by
  have heq : futureIntegral M v f = fun z => totalIntegral M v f z - pastIntegral M v f z :=
    funext (futureIntegral_eq_total_sub_past hf.continuous hs)
  rw [heq, iteratedFDeriv_sub_of_smooth (totalIntegral_contDiff hf hs)
    (pastIntegral_contDiff hf hs), iteratedFDeriv_totalIntegral hf hs,
    iteratedFDeriv_pastIntegral hf hs]
  exact (futureIntegral_eq_total_sub_past (iteratedFDeriv_contDiff hf n).continuous
    (iteratedFDeriv_supported hs n) z).symm

theorem futureIntegral_norm_le {a b M C : ℝ} {v : E} {f : ℝ × E → F}
    (hab : a ≤ b) (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f)
    (hbound : ∀ s ∈ Icc a b, ∀ Y : E, ‖f (s, Y)‖ ≤ C) (z : ℝ × E) :
    ‖futureIntegral M v f z‖ ≤ C * (b - a) := by
  have hnorm : RadialAlias.RadiallySupported a b (fun x => ‖f x‖) := by
    intro x hx
    exact hs (norm_ne_zero_iff.mp hx)
  calc
    ‖futureIntegral M v f z‖ ≤ ∫ u in Ioi (0 : ℝ), ‖f (shift M v z u)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, ‖f (shift M v z u)‖ :=
      setIntegral_le_integral (shifted_integrable hf hs z).norm
        (Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ‖totalIntegral M v (fun x => ‖f x‖) z‖ := Real.le_norm_self _
    _ ≤ C * (b - a) := totalIntegral_norm_le (f := fun x => ‖f x‖) hab hf.norm hnorm
      (fun s hs Y => by simpa only [norm_norm] using hbound s hs Y) z

theorem iteratedFDeriv_futureIntegral_norm_le [CompleteSpace F] {a b M C : ℝ} {v : E}
    {f : ℝ × E → F} (hab : a ≤ b) (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (n : ℕ)
    (hbound : ∀ s ∈ Icc a b, ∀ Y : E, ‖iteratedFDeriv ℝ n f (s, Y)‖ ≤ C) (z : ℝ × E) :
    ‖iteratedFDeriv ℝ n (futureIntegral M v f) z‖ ≤ C * (b - a) := by
  rw [iteratedFDeriv_futureIntegral hf hs]
  exact futureIntegral_norm_le hab (iteratedFDeriv_contDiff hf n).continuous
    (iteratedFDeriv_supported hs n) hbound z

/-- The total integral agrees with the separately formalized radial alias. -/
theorem totalIntegral_eq_wholeAlias {a b M : ℝ} {v : E} {f : ℝ × E → F}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    totalIntegral M v f z = RadialAlias.wholeAlias M v (z.2 - (M * z.1) • v) f := by
  rw [totalIntegral_eq_radialInterval hf hs,
    ← RadialAlias.aliasIntegral_eq_wholeAlias hf hs]
  apply intervalIntegral.integral_congr
  intro s _
  apply congrArg f
  change (s, z.2 + (M * (s - z.1)) • v) =
    (s, z.2 - (M * z.1) • v + (M * s) • v)
  apply congrArg (fun y : E => (s, y))
  rw [mul_sub, sub_smul]
  abel

end Shifted

end NavierStokes.TransportPrimitive
