/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingPotential

/-!
# The resolvent equation for a kernel resolvent

The kernel resolvent of a sub-Markov kernel semigroup satisfies the resolvent equation

  `R_lam f = R_mu f + (mu - lam) R_lam (R_mu f)`   for `0 < lam < mu`

(`SubMarkovKernelSemigroup.kernelResolvent_resolventEquation`), as an identity of
extended-nonnegative-real valued observables, so no integrability hypothesis is needed.  The proof
is the convolution identity for exponential weights

  `e^{-mu u} + (mu - lam) ∫_0^u e^{-lam s} e^{-mu (u - s)} ds = e^{-lam u}`

(`expWeight_convolution`) together with the Chapman--Kolmogorov law, which turns the composition
of the two resolvents into a convolution in time.

Main definitions: `expWeight`.

The same double-integral form is symmetric in the two shifts, so the two resolvents commute
(`SubMarkovKernelSemigroup.kernelResolvent_comm`).

Main results: `expWeight_convolution`,
`SubMarkovKernelSemigroup.kernelResolvent_eq_lintegral_expWeight`,
`SubMarkovKernelSemigroup.kernelResolvent_comp_eq_lintegral`,
`SubMarkovKernelSemigroup.kernelResolvent_comm`,
`SubMarkovKernelSemigroup.kernelResolvent_resolventEquation`.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

section

namespace MarkovProcess

/-- The exponential weight at the shift `c`, extended by zero to nonpositive times. -/
noncomputable def expWeight (c : ℝ) (t : ℝ) : ℝ≥0∞ :=
  (Set.Ioi (0 : ℝ)).indicator (fun t ↦ ENNReal.ofReal (Real.exp (-c * t))) t

/-- The exponential weight is measurable. -/
theorem measurable_expWeight (c : ℝ) : Measurable (expWeight c) :=
  (measurable_laplaceDensity c).indicator measurableSet_Ioi

/-- At a positive time the exponential weight is the exponential density. -/
@[simp] theorem expWeight_of_pos {c t : ℝ} (ht : 0 < t) :
    expWeight c t = ENNReal.ofReal (Real.exp (-c * t)) :=
  Set.indicator_of_mem (Set.mem_Ioi.mpr ht) _

/-- At a nonpositive time the exponential weight vanishes. -/
@[simp] theorem expWeight_of_nonpos {c t : ℝ} (ht : t ≤ 0) : expWeight c t = 0 :=
  Set.indicator_of_notMem (by simpa using ht) _

/-- Integration against the exponential weight is integration over positive times. -/
theorem lintegral_expWeight_mul (c : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ t, expWeight c t * F t = ∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-c * t)) * F t := by
  rw [← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun t ↦ ?_
  by_cases ht : (0 : ℝ) < t
  · rw [expWeight_of_pos ht, Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
  · rw [expWeight_of_nonpos (le_of_not_gt ht),
      Set.indicator_of_notMem (by simpa using ht), zero_mul]

/-- **The convolution identity for exponential weights.**  At two different shifts the difference
of the weights is the convolution of the weights, scaled by the difference of the shifts. -/
theorem expWeight_convolution {lam mu : ℝ} (hlt : lam < mu) (u : ℝ) :
    expWeight mu u + ENNReal.ofReal (mu - lam) *
        ∫⁻ s, expWeight lam s * expWeight mu (u - s) = expWeight lam u := by
  have hc : (0 : ℝ) < mu - lam := sub_pos.mpr hlt
  have hind : (fun s ↦ expWeight lam s * expWeight mu (u - s)) =
      (Set.Ioo (0 : ℝ) u).indicator
        (fun s ↦ ENNReal.ofReal (Real.exp (-mu * u + (mu - lam) * s))) := by
    funext s
    by_cases hs : s ∈ Set.Ioo (0 : ℝ) u
    · rw [Set.indicator_of_mem hs, expWeight_of_pos hs.1,
        expWeight_of_pos (sub_pos.mpr hs.2), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]
      congr 2
      ring
    · rw [Set.indicator_of_notMem hs]
      rcases le_or_gt s 0 with h | h
      · rw [expWeight_of_nonpos h, zero_mul]
      · have h2 : u ≤ s := by
          by_contra hcon
          exact hs ⟨h, lt_of_not_ge hcon⟩
        rw [expWeight_of_nonpos (sub_nonpos.mpr h2), mul_zero]
  rw [hind, lintegral_indicator measurableSet_Ioo]
  rcases le_or_gt u 0 with hu | hu
  · rw [expWeight_of_nonpos hu, expWeight_of_nonpos hu,
      Set.Ioo_eq_empty (not_lt.mpr hu)]
    simp only [Measure.restrict_empty, neg_mul, lintegral_zero_measure, mul_zero, add_zero]
  · have hcont : Continuous fun s : ℝ ↦ Real.exp (-mu * u + (mu - lam) * s) := by fun_prop
    have hint : IntegrableOn (fun s : ℝ ↦ Real.exp (-mu * u + (mu - lam) * s))
        (Set.Ioo (0 : ℝ) u) :=
      ((hcont.intervalIntegrable 0 u).1).mono_set Set.Ioo_subset_Ioc_self
    have hval : ∫ s in Set.Ioo (0 : ℝ) u, Real.exp (-mu * u + (mu - lam) * s) =
        (Real.exp (-lam * u) - Real.exp (-mu * u)) / (mu - lam) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu.le]
      have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) u, HasDerivAt
          (fun s : ℝ ↦ Real.exp (-mu * u + (mu - lam) * s) / (mu - lam))
          (Real.exp (-mu * u + (mu - lam) * s)) s := by
        intro s _
        have h1 : HasDerivAt (fun s : ℝ ↦ -mu * u + (mu - lam) * s) (mu - lam) s := by
          simpa using ((hasDerivAt_id s).const_mul (mu - lam)).const_add (-mu * u)
        have h2 := (h1.exp).div_const (mu - lam)
        simpa only [neg_mul, mul_div_cancel_right₀ _ hc.ne'] using h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 u)]
      have hexp : Real.exp (-mu * u + (mu - lam) * u) = Real.exp (-lam * u) := by
        congr 1
        ring
      rw [hexp]
      simp only [mul_zero, add_zero]
      ring
    have hmul : (mu - lam) * ((Real.exp (-lam * u) - Real.exp (-mu * u)) / (mu - lam)) =
        Real.exp (-lam * u) - Real.exp (-mu * u) := by
      field_simp
    have hnn : 0 ≤ Real.exp (-lam * u) - Real.exp (-mu * u) := by
      have hle : -mu * u ≤ -lam * u := by nlinarith only [hlt, hu]
      exact sub_nonneg.mpr (Real.exp_le_exp.mpr hle)
    rw [expWeight_of_pos hu, expWeight_of_pos hu,
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun s ↦ (Real.exp_pos _).le),
      hval, ← ENNReal.ofReal_mul hc.le, hmul,
      ← ENNReal.ofReal_add (Real.exp_pos _).le hnn]
    congr 1
    ring

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MeasurableSpace alpha] (P : SubMarkovKernelSemigroup alpha)

/-- Every transition measure of a sub-Markov kernel semigroup is finite. -/
theorem isFiniteMeasure_apply (t : NNReal) (x : alpha) : IsFiniteMeasure (P t x) :=
  ⟨lt_of_le_of_lt (P.measure_univ_le_one t x) ENNReal.one_lt_top⟩

/-- The time profile of an observable from a starting point: its transition integral at each
time, read on the whole time line through the nonnegative part. -/
noncomputable def transitionProfile (f : alpha → ℝ≥0∞) (x : alpha) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, f y ∂P (Real.toNNReal u) x

/-- The time profile is measurable in time. -/
theorem measurable_transitionProfile {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    Measurable (P.transitionProfile f x) :=
  (Measure.measurable_lintegral hf).comp (P.measurable_toMeasure_toNNReal x)

/-- The kernel resolvent, written as an integral over the whole time line against the exponential
weight. -/
theorem kernelResolvent_eq_lintegral_expWeight (lam : ℝ) (f : alpha → ℝ≥0∞) (x : alpha) :
    P.kernelResolvent lam f x = ∫⁻ t, expWeight lam t * P.transitionProfile f x t :=
  (lintegral_expWeight_mul lam _).symm

/-- The composition of two kernel resolvents is a convolution in time. -/
theorem lintegral_kernelResolvent_eq (mu : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) {s : ℝ} (hs : 0 < s) :
    ∫⁻ y, P.kernelResolvent mu f y ∂P (Real.toNNReal s) x =
      ∫⁻ t, expWeight mu t * P.transitionProfile f x (s + t) := by
  have := P.isFiniteMeasure_apply (Real.toNNReal s) x
  have hjoint : Measurable fun q : alpha × ℝ ↦
      expWeight mu q.2 * ∫⁻ z, f z ∂P (Real.toNNReal q.2) q.1 :=
    ((measurable_expWeight mu).comp measurable_snd).mul
      ((Measure.measurable_lintegral hf).comp
        (P.measurable_toMeasure.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk
          measurable_fst)))
  calc ∫⁻ y, P.kernelResolvent mu f y ∂P (Real.toNNReal s) x
      = ∫⁻ y, (∫⁻ t, expWeight mu t * ∫⁻ z, f z ∂P (Real.toNNReal t) y)
          ∂P (Real.toNNReal s) x :=
        lintegral_congr fun y ↦ P.kernelResolvent_eq_lintegral_expWeight mu f y
    _ = ∫⁻ t, ∫⁻ y, expWeight mu t * (∫⁻ z, f z ∂P (Real.toNNReal t) y)
          ∂P (Real.toNNReal s) x := lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ t, expWeight mu t * ∫⁻ y, (∫⁻ z, f z ∂P (Real.toNNReal t) y)
          ∂P (Real.toNNReal s) x :=
        lintegral_congr fun t ↦ lintegral_const_mul _
          ((Measure.measurable_lintegral hf).comp
            (P.measurable_toMeasure.comp (measurable_const.prodMk measurable_id)))
    _ = ∫⁻ t, expWeight mu t * P.transitionProfile f x (s + t) := by
        refine lintegral_congr fun t ↦ ?_
        rcases le_or_gt t 0 with ht | ht
        · rw [expWeight_of_nonpos ht, zero_mul, zero_mul]
        · rw [transitionProfile, Real.toNNReal_add hs.le ht.le, P.lintegral_add _ _ x hf]

/-- **The composition of two kernel resolvents is a double integral in time**, against the
product of the two exponential weights. -/
theorem kernelResolvent_comp_eq_lintegral (lam mu : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    P.kernelResolvent lam (P.kernelResolvent mu f) x =
      ∫⁻ s, ∫⁻ t, (expWeight lam s * expWeight mu t) * P.transitionProfile f x (s + t) := by
  have hFmeas : Measurable (P.transitionProfile f x) := P.measurable_transitionProfile hf x
  rw [P.kernelResolvent_eq_lintegral_expWeight lam _ x]
  refine lintegral_congr fun s ↦ ?_
  rcases le_or_gt s 0 with hs | hs
  · rw [expWeight_of_nonpos hs, zero_mul]
    symm
    simp only [zero_mul, lintegral_const, measure_univ_of_isAddLeftInvariant]
  · have hgmeas : Measurable fun t : ℝ ↦
        expWeight mu t * P.transitionProfile f x (s + t) :=
      (measurable_expWeight mu).mul (hFmeas.comp (measurable_const_add s))
    rw [transitionProfile, P.lintegral_kernelResolvent_eq mu hf x hs,
      ← lintegral_const_mul _ hgmeas]
    exact lintegral_congr fun t ↦ (mul_assoc _ _ _).symm

/-- **The kernel resolvents at two shifts commute**: their composition is a double integral
which is symmetric in the two shifts. -/
theorem kernelResolvent_comm (lam mu : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    P.kernelResolvent lam (P.kernelResolvent mu f) x =
      P.kernelResolvent mu (P.kernelResolvent lam f) x := by
  have hFmeas : Measurable (P.transitionProfile f x) := P.measurable_transitionProfile hf x
  have hjoint : Measurable fun q : ℝ × ℝ ↦
      (expWeight lam q.1 * expWeight mu q.2) * P.transitionProfile f x (q.1 + q.2) :=
    (((measurable_expWeight lam).comp measurable_fst).mul
      ((measurable_expWeight mu).comp measurable_snd)).mul
      (hFmeas.comp (measurable_fst.add measurable_snd))
  rw [P.kernelResolvent_comp_eq_lintegral lam mu hf x,
    P.kernelResolvent_comp_eq_lintegral mu lam hf x,
    lintegral_lintegral_swap hjoint.aemeasurable]
  refine lintegral_congr fun t ↦ lintegral_congr fun s ↦ ?_
  rw [mul_comm (expWeight lam s) (expWeight mu t), add_comm s t]

/-- **The resolvent equation.**  At two different positive shifts the kernel resolvents differ by
their composition, scaled by the difference of the shifts. -/
theorem kernelResolvent_resolventEquation {lam mu : ℝ} (hlt : lam < mu)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    P.kernelResolvent lam f x =
      P.kernelResolvent mu f x +
        ENNReal.ofReal (mu - lam) * P.kernelResolvent lam (P.kernelResolvent mu f) x := by
  have hFmeas : Measurable (P.transitionProfile f x) := P.measurable_transitionProfile hf x
  have hprodmeas : Measurable fun q : ℝ × ℝ ↦
      (expWeight lam q.1 * expWeight mu (q.2 - q.1)) * P.transitionProfile f x q.2 :=
    (((measurable_expWeight lam).comp measurable_fst).mul
      ((measurable_expWeight mu).comp (measurable_snd.sub measurable_fst))).mul
      (hFmeas.comp measurable_snd)
  have hconvmeas : Measurable fun u : ℝ ↦ ∫⁻ s, expWeight lam s * expWeight mu (u - s) := by
    have hj : Measurable fun q : ℝ × ℝ ↦ expWeight lam q.2 * expWeight mu (q.1 - q.2) :=
      ((measurable_expWeight lam).comp measurable_snd).mul
        ((measurable_expWeight mu).comp (measurable_fst.sub measurable_snd))
    exact hj.lintegral_prod_right'
  have hdouble := P.kernelResolvent_comp_eq_lintegral lam mu hf x
  have hshift : ∀ s : ℝ,
      (∫⁻ t, (expWeight lam s * expWeight mu t) * P.transitionProfile f x (s + t)) =
        ∫⁻ v, (expWeight lam s * expWeight mu (v - s)) * P.transitionProfile f x v := by
    intro s
    rw [← lintegral_add_right_eq_self
      (fun v ↦ (expWeight lam s * expWeight mu (v - s)) * P.transitionProfile f x v) s]
    refine lintegral_congr fun t ↦ ?_
    rw [add_sub_cancel_right, add_comm t s]
  have hswap :
      (∫⁻ s, ∫⁻ t, (expWeight lam s * expWeight mu t) * P.transitionProfile f x (s + t)) =
        ∫⁻ u, (∫⁻ s, expWeight lam s * expWeight mu (u - s)) *
          P.transitionProfile f x u := by
    simp_rw [hshift]
    rw [lintegral_lintegral_swap hprodmeas.aemeasurable]
    refine lintegral_congr fun v ↦ ?_
    exact lintegral_mul_const _ ((measurable_expWeight lam).mul
      ((measurable_expWeight mu).comp (measurable_const.sub measurable_id)))
  have hconst : ENNReal.ofReal (mu - lam) *
      ∫⁻ u, (∫⁻ s, expWeight lam s * expWeight mu (u - s)) * P.transitionProfile f x u =
      ∫⁻ u, ENNReal.ofReal (mu - lam) *
        ((∫⁻ s, expWeight lam s * expWeight mu (u - s)) * P.transitionProfile f x u) :=
    (lintegral_const_mul _ (hconvmeas.mul hFmeas)).symm
  have hadd : (∫⁻ u, expWeight mu u * P.transitionProfile f x u) +
      ∫⁻ u, ENNReal.ofReal (mu - lam) *
        ((∫⁻ s, expWeight lam s * expWeight mu (u - s)) * P.transitionProfile f x u) =
      ∫⁻ u, expWeight mu u * P.transitionProfile f x u +
        ENNReal.ofReal (mu - lam) *
          ((∫⁻ s, expWeight lam s * expWeight mu (u - s)) * P.transitionProfile f x u) :=
    (lintegral_add_left ((measurable_expWeight mu).mul hFmeas) _).symm
  rw [hdouble, hswap, P.kernelResolvent_eq_lintegral_expWeight lam f x,
    P.kernelResolvent_eq_lintegral_expWeight mu f x, hconst, hadd]
  refine lintegral_congr fun u ↦ ?_
  rw [← mul_assoc, ← add_mul, expWeight_convolution hlt u]

end SubMarkovKernelSemigroup

end MarkovProcess

end

end PortComputability
