/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Logic.Function.Iterate

@[expose] public section

/-!
# The translated radial integral and repeated integration by parts

The integrals and derivatives in this file are actual Bochner integrals and
Fréchet derivatives. The auxiliary variable may be the universal cover of a
torus. A separately constructed directional primitive supplies the inverse
identity; no decay estimate for the integral is assumed.
-/

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
