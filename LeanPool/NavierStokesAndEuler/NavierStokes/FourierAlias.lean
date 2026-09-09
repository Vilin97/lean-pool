/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TransportPrimitive
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothFourierData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricTorusInverse
public import LeanPool.NavierStokesAndEuler.NavierStokes.ChartScales
public import LeanPool.NavierStokesAndEuler.NavierStokes.Flatness
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

/-!
# Exact radial aliases and Fourier suppression

The compactification defect is retained as an actual function. Its averaging
and integration-by-parts identities concern genuine Bochner integrals.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Interval Topology BigOperators

namespace NavierStokes.FourierAlias

open TorusInverse

abbrev State := ℝ × Plane

section Averages

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integer translation invariance of an actual function on the universal cover. -/
noncomputable def TorusPeriodic (f : Plane → F) : Prop :=
  ∀ Y : Plane, ∀ k : Frequency, f (Y + ((k.1 : ℝ), (k.2 : ℝ))) = f Y

/-- The actual normalized unit-square average. -/
noncomputable def torusMean (f : Plane → F) : F :=
  ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y)

noncomputable def sliceMean (f : State → F) (U : ℝ) : F := torusMean (fun Y => f (U, Y))

/-- The exact defect in `D Ic = f - cutoffAlias`. -/
noncomputable def cutoffAlias (χ : ℝ → ℝ) (M : ℝ) (v : Plane) (f : State → F) (z : State) : F :=
  deriv χ z.1 • TransportPrimitive.totalIntegral M v f z

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem torusPeriodic_first {f : Plane → F} (hp : TorusPeriodic f) (y : ℝ) :
    Periodic (fun x => f (x, y)) 1 := by
  intro x
  simpa using hp (x, y) (1, 0)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem torusPeriodic_second {f : Plane → F} (hp : TorusPeriodic f) (x : ℝ) :
    Periodic (fun y => f (x, y)) 1 := by
  intro y
  simpa using hp (x, y) (0, 1)

theorem periodic_integral_translate {g : ℝ → F} (hg : Periodic g 1) (c : ℝ) :
    (∫ x in (0 : ℝ)..1, g (x + c)) = ∫ x in (0 : ℝ)..1, g x := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_zero, add_comm] using hg.intervalIntegral_add_eq c 0

/-- Averaging is invariant under any real torus translation. -/
theorem torusMean_translate {f : Plane → F} (hp : TorusPeriodic f) (Y : Plane) :
    torusMean (fun Z => f (Z + Y)) = torusMean f := by
  have hx (y : ℝ) : (∫ x in (0 : ℝ)..1, f (x + Y.1, y + Y.2)) =
      ∫ x in (0 : ℝ)..1, f (x, y + Y.2) :=
    periodic_integral_translate (torusPeriodic_first hp (y + Y.2)) Y.1
  have hy : Periodic (fun y => ∫ x in (0 : ℝ)..1, f (x, y)) 1 := by
    intro y
    apply intervalIntegral.integral_congr
    intro x _
    exact torusPeriodic_second hp x y
  change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x + Y.1, y + Y.2)) = _
  simp_rw [hx]
  exact periodic_integral_translate hy Y.2

theorem torusMean_smul (c : ℝ) (f : Plane → F) :
    torusMean (fun Y => c • f Y) = c • torusMean f := by
  simp only [torusMean, intervalIntegral.integral_smul]

/-- Fubini on two compact real intervals. -/
theorem intervalIntegral_comm {g : Plane → F} (hg : Continuous g)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ y in c..d, ∫ x in a..b, g (x, y)) = ∫ x in a..b, ∫ y in c..d, g (x, y) := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply (integral_integral_swap ?_).symm
  change Integrable g ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d)))
  rw [Measure.prod_restrict]
  exact (hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem continuous_parameter_interval {H : Type} [TopologicalSpace H]
    [FirstCountableTopology H] [LocallyCompactSpace H] {g : H × ℝ → F}
    (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun x => ∫ u in a..b, g (x, u)) := by
  have heq : (fun x => ∫ u in a..b, g (x, u)) =
      (fun x => ∫ u in Icc a b, g (x, u)) := by
    funext x
    rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact continuous_parametric_integral_of_continuous (f := fun x u => g (x, u)) hg isCompact_Icc

theorem torusMean_const [CompleteSpace F] (c : F) : torusMean (fun _ => c) = c := by
  simp [torusMean]

theorem torusMean_neg (f : Plane → F) : torusMean (fun Y => -f Y) = -torusMean f := by
  simp only [torusMean, intervalIntegral.integral_neg]

theorem torusMean_add {f g : Plane → F} (hf : Continuous f) (hg : Continuous g) :
    torusMean (fun Y => f Y + g Y) = torusMean f + torusMean g := by
  have hcf : Continuous (fun y => ∫ x in (0 : ℝ)..1, f (x, y)) :=
    continuous_parameter_interval (g := fun p : ℝ × ℝ => f (p.2, p.1))
      (hf.comp (continuous_snd.prodMk continuous_fst)) (by norm_num)
  have hcg : Continuous (fun y => ∫ x in (0 : ℝ)..1, g (x, y)) :=
    continuous_parameter_interval (g := fun p : ℝ × ℝ => g (p.2, p.1))
      (hg.comp (continuous_snd.prodMk continuous_fst)) (by norm_num)
  have hx (y : ℝ) : (∫ x in (0 : ℝ)..1, f (x, y) + g (x, y)) =
      (∫ x in (0 : ℝ)..1, f (x, y)) + ∫ x in (0 : ℝ)..1, g (x, y) :=
    intervalIntegral.integral_add
      ((hf.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
      ((hg.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
  unfold torusMean
  simp_rw [hx]
  exact intervalIntegral.integral_add (hcf.intervalIntegrable _ _) (hcg.intervalIntegrable _ _)

theorem torusMean_sub {f g : Plane → F} (hf : Continuous f) (hg : Continuous g) :
    torusMean (fun Y => f Y - g Y) = torusMean f - torusMean g := by
  simp only [sub_eq_add_neg]
  rw [torusMean_add hf hg.fun_neg, torusMean_neg]

/-- The torus and radial averages commute as actual iterated integrals. -/
theorem torusMean_intervalIntegral {g : State → F} (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) :
    torusMean (fun Y => ∫ s in a..b, g (s, Y)) = ∫ s in a..b, sliceMean g s := by
  have hx (y : ℝ) : (∫ x in (0 : ℝ)..1, ∫ s in a..b, g (s, (x, y))) =
      ∫ s in a..b, ∫ x in (0 : ℝ)..1, g (s, (x, y)) := by
    exact intervalIntegral_comm (g := fun p : Plane => g (p.1, (p.2, y)))
      (hg.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))) hab (by norm_num)
  have hc : Continuous (fun p : Plane => ∫ x in (0 : ℝ)..1, g (p.1, (x, p.2))) := by
    exact continuous_parameter_interval (g := fun p : Plane × ℝ => g (p.1.1, (p.2, p.1.2)))
      (hg.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd)))
      (by norm_num : (0 : ℝ) ≤ 1)
  change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ∫ s in a..b, g (s, (x, y))) = _
  simp_rw [hx]
  exact intervalIntegral_comm hc hab (by norm_num)

/-- The shifted total integral has exactly the radially integrated source mean. -/
theorem torusMean_totalIntegral {a b M : ℝ} {v : Plane} {f : State → F}
    (hab : a ≤ b) (hf : Continuous f) (hp : ∀ U, TorusPeriodic (fun Y => f (U, Y)))
    (hs : RadialAlias.RadiallySupported a b f) (U : ℝ) :
    sliceMean (TransportPrimitive.totalIntegral M v f) U = ∫ s in a..b, sliceMean f s := by
  have heq : (fun Y => TransportPrimitive.totalIntegral M v f (U, Y)) =
      (fun Y => ∫ s in a..b, f (s, Y + (M * (s - U)) • v)) := by
    funext Y
    exact TransportPrimitive.totalIntegral_eq_radialInterval hf hs (U, Y)
  have hc : Continuous (fun z : State => f (z.1, z.2 + (M * (z.1 - U)) • v)) := by
    exact hf.comp (continuous_fst.prodMk
      (continuous_snd.add ((continuous_const.mul (continuous_fst.sub continuous_const)).smul
        continuous_const)))
  change torusMean (fun Y => TransportPrimitive.totalIntegral M v f (U, Y)) = _
  rw [heq, torusMean_intervalIntegral hc hab]
  apply intervalIntegral.integral_congr
  intro s _
  exact torusMean_translate (hp s) ((M * (s - U)) • v)

theorem totalIntegral_periodic {M : ℝ} {v : Plane} {f : State → F}
    (hp : ∀ U, TorusPeriodic (fun Y => f (U, Y))) :
    ∀ U, TorusPeriodic (fun Y => TransportPrimitive.totalIntegral M v f (U, Y)) := by
  intro U Y k
  apply integral_congr_ae
  filter_upwards [] with u
  change f (U + u, (Y + ((k.1 : ℝ), (k.2 : ℝ))) + (M * u) • v) =
    f (U + u, Y + (M * u) • v)
  rw [add_right_comm Y ((k.1 : ℝ), (k.2 : ℝ))]
  exact hp (U + u) (Y + (M * u) • v) k

theorem cutoffAlias_periodic {χ : ℝ → ℝ} {M : ℝ} {v : Plane} {f : State → F}
    (hp : ∀ U, TorusPeriodic (fun Y => f (U, Y))) :
    ∀ U, TorusPeriodic (fun Y => cutoffAlias χ M v f (U, Y)) := by
  intro U Y k
  exact congrArg (fun q => deriv χ U • q) (totalIntegral_periodic hp U Y k)

/-- The exact defect is supported in the transition interval of the cutoff,
which may be strictly inside the radial support interval of the source. -/
theorem cutoffAlias_supported_on_transition {c d M : ℝ} {v : Plane} {f : State → F}
    {χ : ℝ → ℝ} (hleft : ∀ u ≤ c, χ u = 0) (hright : ∀ u, d ≤ u → χ u = 1) :
    RadialAlias.RadiallySupported c d (cutoffAlias χ M v f) := by
  intro z hz
  have hl : c ≤ z.1 := by
    by_contra hn
    have heq : χ =ᶠ[𝓝 z.1] (fun _ => 0) :=
      (eventually_lt_nhds (lt_of_not_ge hn)).mono (fun u hu => hleft u hu.le)
    have hd : deriv χ z.1 = 0 := by simpa using heq.deriv_eq
    exact hz (by simp only [cutoffAlias, hd, zero_smul])
  have hr : z.1 ≤ d := by
    by_contra hn
    have heq : χ =ᶠ[𝓝 z.1] (fun _ => 1) :=
      (eventually_gt_nhds (lt_of_not_ge hn)).mono (fun u hu => hright u hu.le)
    have hd : deriv χ z.1 = 0 := by simpa using heq.deriv_eq
    exact hz (by simp only [cutoffAlias, hd, zero_smul])
  exact ⟨hl, hr⟩

theorem cutoffAlias_zero_mean_of_integratedMean_zero {a b M : ℝ} {v : Plane}
    {f : State → F} (χ : ℝ → ℝ) (hab : a ≤ b) (hf : Continuous f)
    (hp : ∀ U, TorusPeriodic (fun Y => f (U, Y)))
    (hs : RadialAlias.RadiallySupported a b f)
    (hm : (∫ s in a..b, sliceMean f s) = 0) (U : ℝ) :
    sliceMean (cutoffAlias χ M v f) U = 0 := by
  change torusMean (fun Y => deriv χ U • TransportPrimitive.totalIntegral M v f (U, Y)) = 0
  rw [torusMean_smul]
  change deriv χ U • sliceMean (TransportPrimitive.totalIntegral M v f) U = 0
  rw [torusMean_totalIntegral hab hf hp hs, hm, smul_zero]

theorem cutoffAlias_zero_mean {a b M : ℝ} {v : Plane} {f : State → F}
    (χ : ℝ → ℝ) (hab : a ≤ b) (hf : Continuous f)
    (hp : ∀ U, TorusPeriodic (fun Y => f (U, Y)))
    (hs : RadialAlias.RadiallySupported a b f) (hm : ∀ U, sliceMean f U = 0) (U : ℝ) :
    sliceMean (cutoffAlias χ M v f) U = 0 := by
  apply cutoffAlias_zero_mean_of_integratedMean_zero χ hab hf hp hs _ U
  simp only [hm, intervalIntegral.integral_zero]

/-- The alias is an exact term in the constructed inverse identity. -/
theorem transport_compact_eq_sub_alias [CompleteSpace F] {a b M : ℝ} {v : Plane}
    {f : State → F} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) (z : State) :
    TransportPrimitive.fixedDeriv (1, M • v) (TransportPrimitive.compactIntegral χ M v f) z =
      f z - cutoffAlias χ M v f z :=
  TransportPrimitive.transport_compactIntegral hχ hf hs z

theorem iteratedFDeriv_periodic {f : State → F}
    (hp : ∀ U, TorusPeriodic (fun Y => f (U, Y))) (n : ℕ) :
    ∀ U, TorusPeriodic (fun Y => iteratedFDeriv ℝ n f (U, Y)) := by
  intro U Y k
  have heq : (fun z : State => f (z + (0, ((k.1 : ℝ), (k.2 : ℝ))))) = f := by
    funext z
    change f (z.1 + 0, z.2 + ((k.1 : ℝ), (k.2 : ℝ))) = f z
    simpa only [add_zero] using hp z.1 z.2 k
  have h := congrArg (fun g : State → F => iteratedFDeriv ℝ n g (U, Y)) heq
  rw [iteratedFDeriv_comp_add_right] at h
  simpa only [Prod.mk_add_mk, add_zero] using h

/-- Actual smooth periodic fields have bounded finite prefixes of full Fréchet
jets on every compact radial slab. -/
theorem periodic_finiteJet_bound {f : State → F} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ U, TorusPeriodic (fun Y => f (U, Y))) (a b : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m, ∀ U ∈ Icc a b, ∀ Y : Plane,
      ‖iteratedFDeriv ℝ j f (U, Y)‖ ≤ C := by
  let K : Set State := Icc a b ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hc : Continuous (fun z : State => ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j f z‖) :=
    continuous_finsetSum _ (fun j _ => (TransportPrimitive.iteratedFDeriv_contDiff hf
      j).continuous.norm)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro j hj U hU Y
  let k : Frequency := (-⌊Y.1⌋, -⌊Y.2⌋)
  let Z : Plane := Y + ((k.1 : ℝ), (k.2 : ℝ))
  have hZ : Z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [Z, k, Prod.fst_add, Prod.fst, Int.cast_neg, ← sub_eq_add_neg, Int.fract]
        using (show Int.fract Y.1 ∈ Icc (0 : ℝ) 1 from
          ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩)
    · simpa only [Z, k, Prod.snd_add, Prod.snd, Int.cast_neg, ← sub_eq_add_neg, Int.fract]
        using (show Int.fract Y.2 ∈ Icc (0 : ℝ) 1 from
          ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩)
  have hperiod : iteratedFDeriv ℝ j f (U, Z) = iteratedFDeriv ℝ j f (U, Y) :=
    iteratedFDeriv_periodic hp j U Y k
  rw [← hperiod]
  have hj' : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i f (U, Z)‖ :=
      Finset.single_le_sum (fun i _ => norm_nonneg _) hj'
    _ ≤ ‖∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i f (U, Z)‖‖ := Real.le_norm_self _
    _ ≤ C := hC (U, Z) ⟨hU, hZ⟩
    _ ≤ max C 0 := le_max_left _ _

variable [CompleteSpace F]

theorem cutoffAlias_smooth {a b M : ℝ} {v : Plane} {f : State → F} {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) :
    ContDiff ℝ ∞ (cutoffAlias χ M v f) :=
  (((contDiff_infty_iff_deriv.mp hχ).2).comp contDiff_fst).smul
    (TransportPrimitive.totalIntegral_contDiff hf hs)

theorem cutoffAlias_supported {a b M : ℝ} {v : Plane} {f : State → F} {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1) :
    RadialAlias.RadiallySupported a b (cutoffAlias χ M v f) := by
  have hsc := TransportPrimitive.compactIntegral_supported (M := M) (v := v)
    hf.continuous hs hleft hright
  have hsd := TransportPrimitive.fixedDeriv_supported hsc (1, M • v)
  intro z hz
  by_contra hzn
  have hfz : f z = 0 := by
    by_contra hfz
    exact hzn (hs hfz)
  have hdz : TransportPrimitive.fixedDeriv (1, M • v)
      (TransportPrimitive.compactIntegral χ M v f) z = 0 := by
    by_contra hdz
    exact hzn (hsd hdz)
  have heq := transport_compact_eq_sub_alias (M := M) (v := v) hχ hf hs z
  have ha : -cutoffAlias χ M v f z = 0 := by simpa [hfz, hdz] using heq.symm
  exact hz (neg_eq_zero.mp ha)

/-- Before using oscillation, every finite prefix of alias jets has a bound
uniform in both the frequency and the translation direction. -/
theorem cutoffAlias_finiteJet_bound {a b : ℝ} {f : State → F} {χ : ℝ → ℝ}
    (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ U, TorusPeriodic (fun Y => f (U, Y)))
    (hs : RadialAlias.RadiallySupported a b f)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℝ, ∀ v : Plane, ∀ j ≤ m, ∀ z : State,
      ‖iteratedFDeriv ℝ j (cutoffAlias χ M v f) z‖ ≤ C := by
  obtain ⟨A, hA, hsource⟩ := periodic_finiteJet_bound hf hp a b m
  have hc : ContDiff ℝ ∞ (fun z : State => deriv χ z.1) :=
    ((contDiff_infty_iff_deriv.mp hχ).2).comp contDiff_fst
  obtain ⟨B, hB, hcutoff⟩ := periodic_finiteJet_bound hc (fun _ _ _ => rfl) a b m
  have hL : 0 ≤ b - a := sub_nonneg.mpr hab
  refine ⟨(2 : ℝ) ^ m * (B * (A * (b - a))), by positivity, ?_⟩
  intro M v j hj z
  by_cases hz : z.1 ∈ Icc a b
  · have hb := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hc
      (TransportPrimitive.totalIntegral_contDiff (M := M) (v := v) hf hs) z
      (n := j) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    change ‖iteratedFDeriv ℝ j (cutoffAlias χ M v f) z‖ ≤ _ at hb
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y : State => deriv χ y.1) z‖ *
          ‖iteratedFDeriv ℝ (j - i) (TransportPrimitive.totalIntegral M v f) z‖ := hb
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B * (A * (b - a)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ m := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj
        have hni : j - i ≤ m := (Nat.sub_le _ _).trans hj
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hcutoff i hi' z.1 hz z.2) (Nat.cast_nonneg _))
          (TransportPrimitive.iteratedFDeriv_totalIntegral_norm_le hab hf hs (j - i)
            (hsource (j - i) hni) z)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hB)
      _ = (2 : ℝ) ^ j * (B * (A * (b - a))) := by
        have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [← hsum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ (2 : ℝ) ^ m * (B * (A * (b - a))) := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj)
          (by positivity)
  · have hsj := TransportPrimitive.iteratedFDeriv_supported
      (cutoffAlias_supported (M := M) (v := v) hχ hf hs hleft hright) j
    have heq : iteratedFDeriv ℝ j (cutoffAlias χ M v f) z = 0 := by
      by_contra hnz
      exact hz (hsj hnz)
    rw [heq, norm_zero]
    positivity

end Averages

section IntegrationByParts

theorem sourceJet_smooth (J : (State → ℂ) → State → ℂ) (f : State → ℂ) (p : ℕ)
    (hf : ContDiff ℝ ∞ f)
    (hJ : ∀ n < p, ContDiff ℝ ∞ (J (RadialAlias.sourceJet J f n))) :
    ContDiff ℝ ∞ (RadialAlias.sourceJet J f p) := by
  cases p with
  | zero => exact hf
  | succ p =>
    rw [RadialAlias.sourceJet_succ]
    exact TransportPrimitive.fixedDeriv_contDiff (hJ p (Nat.lt_succ_self p)) (1, 0)

/-- The existing repeated IBP identity, now for the actual U-dependent total
integral. No alias is discarded. -/
theorem totalIntegral_sourceJet {a b M : ℝ} {v : Plane}
    (J : (State → ℂ) → State → ℂ) (f : State → ℂ) (p : ℕ) (hM : M ≠ 0)
    (hf : ContDiff ℝ ∞ f) (hsf : RadialAlias.RadiallySupported a b f)
    (hJ : ∀ n < p, ContDiff ℝ ∞ (J (RadialAlias.sourceJet J f n)))
    (hsJ : ∀ n < p, RadialAlias.RadiallySupported a b (J (RadialAlias.sourceJet J f n)))
    (hr : ∀ n < p, RadialAlias.directionalDeriv v (J (RadialAlias.sourceJet J f n)) =
      RadialAlias.sourceJet J f n) (z : State) :
    TransportPrimitive.totalIntegral M v f z = (-M⁻¹) ^ p •
      TransportPrimitive.totalIntegral M v (RadialAlias.sourceJet J f p) z := by
  rw [TransportPrimitive.totalIntegral_eq_wholeAlias hf.continuous hsf,
    TransportPrimitive.totalIntegral_eq_wholeAlias (sourceJet_smooth J f p hf hJ).continuous
      (RadialAlias.sourceJet_radiallySupported J f p hsf hsJ)]
  exact RadialAlias.wholeAlias_sourceJet J f p hM
    (fun n hn => (hJ n hn).of_le (by simp)) hsJ hr

theorem cutoffAlias_sourceJet {a b M : ℝ} {v : Plane}
    (χ : ℝ → ℝ) (J : (State → ℂ) → State → ℂ) (f : State → ℂ) (p : ℕ) (hM : M ≠ 0)
    (hf : ContDiff ℝ ∞ f) (hsf : RadialAlias.RadiallySupported a b f)
    (hJ : ∀ n < p, ContDiff ℝ ∞ (J (RadialAlias.sourceJet J f n)))
    (hsJ : ∀ n < p, RadialAlias.RadiallySupported a b (J (RadialAlias.sourceJet J f n)))
    (hr : ∀ n < p, RadialAlias.directionalDeriv v (J (RadialAlias.sourceJet J f n)) =
      RadialAlias.sourceJet J f n) (z : State) :
    cutoffAlias χ M v f z = (-M⁻¹) ^ p • cutoffAlias χ M v (RadialAlias.sourceJet J f p) z := by
  rw [cutoffAlias, totalIntegral_sourceJet J f p hM hf hsf hJ hsJ hr]
  exact smul_comm _ _ _

/-- Differentiate the exact scalar IBP identity. This controls full derivative
tensors, including every ordinary mixed coordinate derivative. -/
theorem iteratedFDeriv_cutoffAlias_sourceJet {a b M : ℝ} {v : Plane}
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (J : (State → ℂ) → State → ℂ) (f : State → ℂ) (p : ℕ) (hM : M ≠ 0)
    (hf : ContDiff ℝ ∞ f) (hsf : RadialAlias.RadiallySupported a b f)
    (hJ : ∀ n < p, ContDiff ℝ ∞ (J (RadialAlias.sourceJet J f n)))
    (hsJ : ∀ n < p, RadialAlias.RadiallySupported a b (J (RadialAlias.sourceJet J f n)))
    (hr : ∀ n < p, RadialAlias.directionalDeriv v (J (RadialAlias.sourceJet J f n)) =
      RadialAlias.sourceJet J f n) (m : ℕ) (z : State) :
    iteratedFDeriv ℝ m (cutoffAlias χ M v f) z = (-M⁻¹) ^ p •
      iteratedFDeriv ℝ m (cutoffAlias χ M v (RadialAlias.sourceJet J f p)) z := by
  have heq := funext (cutoffAlias_sourceJet χ J f p hM hf hsf hJ hsJ hr)
  rw [heq]
  exact iteratedFDeriv_const_smul_apply'
    (((cutoffAlias_smooth hχ (sourceJet_smooth J f p hf hJ)
      (RadialAlias.sourceJet_radiallySupported J f p hsf hsJ)).of_le
      (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))).contDiffAt)

end IntegrationByParts

section ActualFourierInverse

open ParametricTorusInverse

/-- Remove the actual full torus mean at each fixed radial coordinate. -/
noncomputable def nonbarPart (f : State → ℂ) (z : State) : ℂ := f z - mean f z.1

theorem nonbarPart_smooth {f : State → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (nonbarPart f) :=
  hf.sub ((coefficient_smooth hf 0).comp contDiff_fst)

theorem nonbarPart_periodic {f : State → ℂ} (hp : ParametricTorusInverse.Periodic f) :
    ParametricTorusInverse.Periodic (nonbarPart f) := by
  intro U Y k
  exact congrArg (fun q => q - mean f U) (hp U Y k)

theorem nonbarPart_zeroMean {f : State → ℂ} (hf : ContDiff ℝ ∞ f) :
    ZeroMean (nonbarPart f) := by
  intro U
  rw [mean_eq_integral]
  change torusMean (fun Y => f (U, Y) - mean f U) = 0
  rw [torusMean_sub (f := fun Y => f (U, Y)) (g := fun _ => mean f U)
    (hf.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const, torusMean_const]
  change sliceMean f U - mean f U = 0
  have heq : sliceMean f U = mean f U := (mean_eq_integral f U).symm
  rw [heq, sub_self]

theorem nonbarPart_radiallySupported {a b : ℝ} {f : State → ℂ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (nonbarPart f) := by
  intro z hz
  by_contra hn
  have hsource : ∀ Y : Plane, f (z.1, Y) = 0 := by
    intro Y
    by_contra hY
    exact hn (@hs (z.1, Y) hY)
  have hmean : mean f z.1 = 0 := by
    rw [mean_eq_integral]
    simp only [hsource, intervalIntegral.integral_zero]
  exact hz (by change f z - mean f z.1 = 0; rw [hmean, sub_zero]; exact hsource z.2)

theorem totalIntegral_nonbarPart {a b M : ℝ} {v : Plane} {f : State → ℂ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (hm : (∫ U in a..b, sliceMean f U) = 0) (z : State) :
    TransportPrimitive.totalIntegral M v (nonbarPart f) z =
      TransportPrimitive.totalIntegral M v f z := by
  rw [TransportPrimitive.totalIntegral_eq_radialInterval (nonbarPart_smooth hf).continuous
      (nonbarPart_radiallySupported hs),
    TransportPrimitive.totalIntegral_eq_radialInterval hf.continuous hs]
  change (∫ U in a..b, f (U, z.2 + (M * (U - z.1)) • v) - mean f U) = _
  have hc : Continuous (fun U => f (U, z.2 + (M * (U - z.1)) • v)) :=
    hf.continuous.comp (continuous_id.prodMk
      (continuous_const.add ((continuous_const.mul (continuous_id.sub continuous_const)).smul
        continuous_const)))
  rw [intervalIntegral.integral_sub
    (f := fun U => f (U, z.2 + (M * (U - z.1)) • v)) (g := fun U => mean f U)
    (hc.intervalIntegrable _ _)
    ((coefficient_smooth hf 0).continuous.intervalIntegrable _ _)]
  have hm' : (∫ U in a..b, mean f U) = 0 := by
    simpa only [mean_eq_integral, sliceMean, torusMean] using hm
  rw [hm', sub_zero]

/-- If the integrated bar vanishes, subtracting the bar does not change the
alias at all. This is the exact reduction used for the pressure source. -/
theorem cutoffAlias_eq_nonbarPart {a b M : ℝ} {v : Plane} {f : State → ℂ}
    (χ : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (hm : (∫ U in a..b, sliceMean f U) = 0) :
    cutoffAlias χ M v f = cutoffAlias χ M v (nonbarPart f) := by
  funext z
  unfold cutoffAlias
  rw [totalIntegral_nonbarPart hf hs hm]

/-- The successive slow derivatives of actual directional Fourier inverses. -/
noncomputable def fourierSourceJet (d : Direction) (f : State → ℂ) (p : ℕ) : State → ℂ :=
  RadialAlias.sourceJet (inverse d) f p

/-- The interleaved construction is exactly the manuscript's slow derivative
of the iterated Fourier inverse, because the actual operators commute. -/
theorem fourierSourceJet_eq_parameterJet (d : Direction) {f : State → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : ParametricTorusInverse.Periodic f) (p : ℕ) :
    fourierSourceJet d f p = parameterJet p (iterateInverse d p f) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    have heq : fourierSourceJet d f (p + 1) = parameterPartial (inverse d (fourierSourceJet d f p))
      :=
      RadialAlias.sourceJet_succ (inverse d) f p
    rw [heq, ih, parameterJet_succ, iterateInverse_succ,
      parameterJet_inverse d (iterateInverse_smooth d hf hp p) (iterateInverse_periodic d hp p)]

theorem inverse_radiallySupported (d : Direction) {a b : ℝ} {f : State → ℂ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (inverse d f) := by
  have hh : ∀ U, U ∉ Icc a b → ∀ Y, f (U, Y) = 0 := by
    intro U hU Y
    by_contra hn
    exact hU (hs hn)
  have hi := inverse_preserves_parameter_support d f (Icc a b) hh
  intro z hz
  by_contra hn
  exact hz (hi z.1 hn z.2)

theorem fourierSourceJet_properties (d : Direction) {a b : ℝ} {f : State → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : ParametricTorusInverse.Periodic f)
    (hm : ZeroMean f) (hs : RadialAlias.RadiallySupported a b f) (p : ℕ) :
    ContDiff ℝ ∞ (fourierSourceJet d f p) ∧
      ParametricTorusInverse.Periodic (fourierSourceJet d f p) ∧
      ZeroMean (fourierSourceJet d f p) ∧
      RadialAlias.RadiallySupported a b (fourierSourceJet d f p) := by
  induction p with
  | zero => exact ⟨hf, hp, hm, hs⟩
  | succ p ih =>
    have heq : fourierSourceJet d f (p + 1) = parameterPartial (inverse d (fourierSourceJet d f p))
      :=
      RadialAlias.sourceJet_succ (inverse d) f p
    rw [heq]
    have hi := inverse_smooth d ih.1 ih.2.1
    exact ⟨parameterPartial_smooth hi, parameterPartial_periodic (inverse_periodic d _),
      parameterPartial_zeroMean hi (inverse_zeroMean d ih.1 ih.2.1),
      RadialAlias.radialSupport_slowDeriv (inverse_radiallySupported d ih.2.2.2)⟩

/-- Exact arbitrary-order IBP with the Fourier inverse constructed from the
given source's own coefficients. No antiderivative or decay premise remains. -/
theorem cutoffAlias_fourierSourceJet (d : Direction) {a b M : ℝ} {f : State → ℂ}
    (χ : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hp : ParametricTorusInverse.Periodic f)
    (hm : ZeroMean f) (hs : RadialAlias.RadiallySupported a b f)
    (p : ℕ) (hM : M ≠ 0) (z : State) :
    cutoffAlias χ M (vector d) f z = (-M⁻¹) ^ p •
      cutoffAlias χ M (vector d) (fourierSourceJet d f p) z := by
  apply cutoffAlias_sourceJet χ (inverse d) f p hM hf hs
  · intro n _
    have hn := fourierSourceJet_properties d hf hp hm hs n
    exact inverse_smooth d hn.1 hn.2.1
  · intro n _
    exact inverse_radiallySupported d (fourierSourceJet_properties d hf hp hm hs n).2.2.2
  · intro n _
    have hn := fourierSourceJet_properties d hf hp hm hs n
    exact inverse_solves d hn.1 hn.2.1 hn.2.2.1

/-- All fixed jets of the exact alias gain arbitrarily many inverse powers of
the frequency. The constant precedes the frequency, point, and jet index. -/
theorem cutoffAlias_arbitrary_order (d : Direction) {a b : ℝ} {f : State → ℂ}
    {χ : ℝ → ℝ} (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hp : ParametricTorusInverse.Periodic f) (hm : ZeroMean f)
    (hs : RadialAlias.RadiallySupported a b f)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1) (m p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℝ, M ≠ 0 → ∀ j ≤ m, ∀ z : State,
      ‖iteratedFDeriv ℝ j (cutoffAlias χ M (vector d) f) z‖ ≤ C * (|M|⁻¹) ^ p := by
  have hg := fourierSourceJet_properties d hf hp hm hs p
  obtain ⟨C, hC, hb⟩ := cutoffAlias_finiteJet_bound hab hχ hg.1 hg.2.1 hg.2.2.2
    hleft hright m
  refine ⟨C, hC, ?_⟩
  intro M hM j hj z
  have heq := funext (cutoffAlias_fourierSourceJet d χ hf hp hm hs p hM)
  rw [heq, iteratedFDeriv_const_smul_apply'
    (((cutoffAlias_smooth hχ hg.1 hg.2.2.2).of_le
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt)]
  have hnorm : ‖((-M⁻¹) ^ p : ℝ) •
      iteratedFDeriv ℝ j (cutoffAlias χ M (vector d) (fourierSourceJet d f p)) z‖ =
      |(-M⁻¹) ^ p| *
        ‖iteratedFDeriv ℝ j (cutoffAlias χ M (vector d) (fourierSourceJet d f p)) z‖ :=
    _root_.norm_smul ((-M⁻¹) ^ p : ℝ)
      (iteratedFDeriv ℝ j (cutoffAlias χ M (vector d) (fourierSourceJet d f p)) z)
  rw [hnorm, abs_pow, abs_neg, abs_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb M (vector d) j hj z)
    (pow_nonneg (inv_nonneg.mpr (abs_nonneg M)) p)

theorem cutoffAlias_arbitrary_order_of_integratedMean_zero (d : Direction)
    {a b : ℝ} {f : State → ℂ} {χ : ℝ → ℝ}
    (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hp : ParametricTorusInverse.Periodic f) (hs : RadialAlias.RadiallySupported a b f)
    (hm : (∫ U in a..b, sliceMean f U) = 0)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1) (m p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℝ, M ≠ 0 → ∀ j ≤ m, ∀ z : State,
      ‖iteratedFDeriv ℝ j (cutoffAlias χ M (vector d) f) z‖ ≤ C * (|M|⁻¹) ^ p := by
  obtain ⟨C, hC, hb⟩ := cutoffAlias_arbitrary_order d hab hχ (nonbarPart_smooth hf)
    (nonbarPart_periodic hp) (nonbarPart_zeroMean hf) (nonbarPart_radiallySupported hs)
    hleft hright m p
  refine ⟨C, hC, ?_⟩
  intro M hM j hj z
  rw [cutoffAlias_eq_nonbarPart χ hf hs hm]
  exact hb M hM j hj z

/-- The square average is the normalized Haar average of the actual descent. -/
theorem torusMean_eq_haar {f : Plane → ℂ} (hf : Continuous f) (hp : TorusPeriodic f) :
    torusMean f = ∫ z, SmoothFourierData.descendContinuous f hf hp z ∂torusMeasure := by
  rw [← SmoothFourierData.coefficient_zero_eq_mean]
  exact (SmoothFourierData.coefficient_zero_eq_integral f).symm

theorem cutoffAlias_haar_zero (d : Direction) {a b M : ℝ} {f : State → ℂ}
    {χ : ℝ → ℝ} (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hp : ParametricTorusInverse.Periodic f) (hm : ZeroMean f)
    (hs : RadialAlias.RadiallySupported a b f) (U : ℝ) :
    ∫ z, SmoothFourierData.descendContinuous (fun Y => cutoffAlias χ M (vector d) f (U, Y))
      ((cutoffAlias_smooth hχ hf hs).continuous.comp (continuous_const.prodMk continuous_id))
      (cutoffAlias_periodic hp U) z ∂torusMeasure = 0 := by
  rw [← torusMean_eq_haar]
  apply cutoffAlias_zero_mean χ hab hf.continuous hp hs _ U
  intro u
  exact (mean_eq_integral f u).symm.trans (hm u)

end ActualFourierInverse

section SmallScale

/-- The actual chart slow scale is subpower relative to epsilon. Consequently
an arbitrary fixed slow loss can be absorbed into half of a positive epsilon
gain. The reciprocal-frequency premise alone would not imply this for an
unrestricted scale `S`. -/
theorem inverse_frequency_eventually_small {M : ℕ → ℝ} {h κ A growth : ℝ}
    (hh : 0 < h) (hκ : 0 < κ)
    (hbound : ∀ᶠ n in atTop, |M n|⁻¹ ≤
      A * ChartScales.epsilon h n ^ κ * ChartScales.S n ^ growth) :
    ∀ᶠ n in atTop, |M n|⁻¹ ≤ ChartScales.epsilon h n ^ (κ / 2) := by
  have ht : Tendsto (fun n : ℕ => A * (ChartScales.S n ^ growth *
      ChartScales.epsilon h n ^ (κ / 2))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (ChartScales.slow_power_epsilon_tendsto_zero h hh growth (κ / 2) (half_pos hκ)).const_mul A
  have hs : ∀ᶠ n : ℕ in atTop, A * (ChartScales.S n ^ growth *
      ChartScales.epsilon h n ^ (κ / 2)) < 1 :=
    (tendsto_order.1 ht).2 1 zero_lt_one
  filter_upwards [hbound, hs] with n hn hsn
  have he : ChartScales.epsilon h n ^ κ =
      ChartScales.epsilon h n ^ (κ / 2) * ChartScales.epsilon h n ^ (κ / 2) := by
    rw [← Real.rpow_add (ChartScales.epsilon_pos h n)]
    congr 1
    ring
  calc
    _ ≤ A * ChartScales.epsilon h n ^ κ * ChartScales.S n ^ growth := hn
    _ = (A * (ChartScales.S n ^ growth * ChartScales.epsilon h n ^ (κ / 2))) *
        ChartScales.epsilon h n ^ (κ / 2) := by rw [he]; ring
    _ ≤ 1 * ChartScales.epsilon h n ^ (κ / 2) :=
      mul_le_mul_of_nonneg_right hsn.le (Real.rpow_nonneg (ChartScales.epsilon_pos h n).le _)
    _ = _ := one_mul _

/-- For each requested epsilon power one fixed finite IBP order suffices. -/
theorem inverse_frequency_power_le_epsilon {M : ℕ → ℝ} {h κ A growth : ℝ}
    (hh : 0 < h) (hκ : 0 < κ)
    (hbound : ∀ᶠ n in atTop, |M n|⁻¹ ≤
      A * ChartScales.epsilon h n ^ κ * ChartScales.S n ^ growth) (N : ℕ) :
    ∃ p : ℕ, ∀ᶠ n in atTop, (|M n|⁻¹) ^ p ≤ ChartScales.epsilon h n ^ N := by
  obtain ⟨p, hp⟩ := exists_nat_gt ((N : ℝ) / (κ / 2))
  have hNp : (N : ℝ) ≤ (κ / 2) * (p : ℝ) := by
    have hp' := (div_lt_iff₀ (half_pos hκ)).mp hp
    nlinarith
  refine ⟨p, ?_⟩
  filter_upwards [inverse_frequency_eventually_small hh hκ hbound] with n hn
  calc
    _ ≤ (ChartScales.epsilon h n ^ (κ / 2)) ^ p :=
      pow_le_pow_left₀ (inv_nonneg.mpr (abs_nonneg _)) hn p
    _ = ChartScales.epsilon h n ^ ((κ / 2) * (p : ℝ)) :=
      (Real.rpow_mul_natCast (ChartScales.epsilon_pos h n).le _ p).symm
    _ ≤ ChartScales.epsilon h n ^ (N : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (ChartScales.epsilon_pos h n)
        (ChartScales.epsilon_le_one h hh.le n) hNp
    _ = ChartScales.epsilon h n ^ N := Real.rpow_natCast _ _

/-- Uniform full-jet superflatness of the retained exact alias. Constants and
the eventual threshold may depend on the requested jet order and epsilon
power, but not on the frequency index, evaluation point, or smaller jet. -/
theorem cutoffAlias_superflat (d : Direction) {a b : ℝ} {f : State → ℂ}
    {χ : ℝ → ℝ} (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hp : ParametricTorusInverse.Periodic f) (hm : ParametricTorusInverse.ZeroMean f)
    (hs : RadialAlias.RadiallySupported a b f)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1)
    {M : ℕ → ℝ} {h κ A growth : ℝ} (hh : 0 < h) (hκ : 0 < κ)
    (hM : ∀ᶠ n in atTop, M n ≠ 0)
    (hbound : ∀ᶠ n in atTop, |M n|⁻¹ ≤
      A * ChartScales.epsilon h n ^ κ * ChartScales.S n ^ growth) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ j ≤ m, ∀ z : State,
      ‖iteratedFDeriv ℝ j (cutoffAlias χ (M n) (vector d) f) z‖ ≤
        C * ChartScales.epsilon h n ^ N := by
  obtain ⟨p, hpM⟩ := inverse_frequency_power_le_epsilon hh hκ hbound N
  obtain ⟨C, hC, hCbound⟩ := cutoffAlias_arbitrary_order d hab hχ hf hp hm hs hleft hright m p
  refine ⟨C, hC, ?_⟩
  filter_upwards [hM, hpM] with n hn hnM
  intro j hj z
  exact (hCbound (M n) hn j hj z).trans (mul_le_mul_of_nonneg_left hnM hC)

theorem cutoffAlias_superflat_of_integratedMean_zero (d : Direction)
    {a b : ℝ} {f : State → ℂ} {χ : ℝ → ℝ}
    (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hp : ParametricTorusInverse.Periodic f) (hs : RadialAlias.RadiallySupported a b f)
    (hm : (∫ U in a..b, sliceMean f U) = 0)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1)
    {M : ℕ → ℝ} {h κ A growth : ℝ} (hh : 0 < h) (hκ : 0 < κ)
    (hM : ∀ᶠ n in atTop, M n ≠ 0)
    (hbound : ∀ᶠ n in atTop, |M n|⁻¹ ≤
      A * ChartScales.epsilon h n ^ κ * ChartScales.S n ^ growth) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ j ≤ m, ∀ z : State,
      ‖iteratedFDeriv ℝ j (cutoffAlias χ (M n) (vector d) f) z‖ ≤
        C * ChartScales.epsilon h n ^ N := by
  obtain ⟨C, hC, hb⟩ := cutoffAlias_superflat d hab hχ (nonbarPart_smooth hf)
    (nonbarPart_periodic hp) (nonbarPart_zeroMean hf) (nonbarPart_radiallySupported hs)
    hleft hright hh hκ hM hbound m N
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with n hn
  intro j hj z
  rw [cutoffAlias_eq_nonbarPart χ hf hs hm]
  exact hn j hj z

/-- Specialization to the manuscript's explicitly constructed radial
frequency, whose reciprocal bound is already proved in `ChartScales`. -/
theorem radial_cutoffAlias_superflat {a b : ℝ} {f : State → ℂ}
    {χ : ℝ → ℝ} (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hp : ParametricTorusInverse.Periodic f) (hm : ParametricTorusInverse.ZeroMean f)
    (hs : RadialAlias.RadiallySupported a b f)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1)
    {h : ℝ} (hh : 0 < h) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ j ≤ m, ∀ z : State,
      ‖iteratedFDeriv ℝ j
        (cutoffAlias χ (ChartScales.radialCoefficient h n) (vector .radial) f) z‖ ≤
        C * ChartScales.epsilon h n ^ N := by
  apply cutoffAlias_superflat .radial (A := ChartScales.Lambda) (growth := ChartScales.rho)
    hab hχ hf hp hm hs hleft hright hh
    (show 0 < ChartScales.kappa by norm_num [ChartScales.kappa])
    (Filter.Eventually.of_forall (fun n => ne_of_gt (ChartScales.radialCoefficient_pos h n)))
    _ m N
  filter_upwards [eventually_ge_atTop 4] with n hn
  simpa only [abs_of_pos (ChartScales.radialCoefficient_pos h n)] using
    ChartScales.radialCoefficient_inv_upper h hh.le hn

end SmallScale

end NavierStokes.FourierAlias
