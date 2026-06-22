/-
Copyright (c) 2026 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# LeanPool.RiemannMappingTheorem.Cindex
-/

open Real Complex Function TopologicalSpace Filter Topology Metric MeasureTheory Nat

/-- The argument-principle integral
`(2πi)⁻¹ ∮_{C(z₀, r)} f'(z)/f(z) dz`, which counts zeroes of `f` inside
the circle of radius `r` around `z₀` (with multiplicity). -/
noncomputable def cindex (z₀ : ℂ) (r : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ z in C(z₀, r), deriv f z / f z

section circle_integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E}
  {r : ℝ} {U : Set ℂ} {c : ℂ}

lemma circle_integral_eq_zero (hU : IsOpen U) (hr : 0 < r) (hcr : closedBall c r ⊆ U)
      (f_hol : DifferentiableOn ℂ f U) :
    (∮ z in C(c, r), f z) = 0 :=
  circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
    (f_hol.continuousOn.mono hcr)
    (fun _ hz => f_hol.differentiableAt
      (hU.mem_nhds (hcr (ball_subset_closedBall (Set.sdiff_subset hz)))))

lemma circle_integral_sub_center_inv_smul [CompleteSpace E] {v : E} (hr : 0 < r) :
    (∮ z in C(c, r), (z - c)⁻¹ • v) = (2 * π * I : ℂ) • v := by
  simp [circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr)]

end circle_integral

section dslope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}
  {p : FormalMultilinearSeries ℂ ℂ E} {U : Set ℂ} {z₀ c : ℂ} {n : ℕ}

lemma DifferentiableOn.iterate_dslope (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hc : c ∈ U) :
    DifferentiableOn ℂ (iterate (swap dslope c) n f) U := by
  induction n generalizing f
  case zero => exact hf
  case succ n_ih => exact n_ih ((differentiableOn_dslope (hU.mem_nhds hc)).mpr hf)

lemma HasFPowerSeriesAt.dslope_order_eventually_ne_zero (hp : HasFPowerSeriesAt f p z₀)
    (h : p ≠ 0) :
    ∀ᶠ z in 𝓝 z₀, iterate (swap dslope z₀) p.order f z ≠ 0 := by
  refine ContinuousAt.eventually_ne ?h (hp.iterate_dslope_fslope_ne_zero h)
  obtain ⟨r, hf⟩ := hp
  have hr : 0 < r := hf.r_pos
  refine ContinuousOn.continuousAt ?h1 (Metric.eball_mem_nhds _ hr)
  have hh : DifferentiableOn ℂ (iterate (swap dslope z₀) p.order f) (Metric.eball z₀ r) :=
    DifferentiableOn.iterate_dslope hf.differentiableOn Metric.isOpen_eball
      (Metric.mem_eball_self hr)
  exact hh.continuousOn

end dslope

variable {f g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z z₀ c : ℂ} {n : ℕ} {U : Set ℂ} {r : ℝ}

lemma deriv_div_self_eq_div_add_deriv_div_self (hg : DifferentiableAt ℂ g z) (hgz : g z ≠ 0)
    (hfg : f =ᶠ[𝓝 z] fun w => (w - z₀) ^ n * g w) (hz : z ≠ z₀) :
    deriv f z / f z = n / (z - z₀) + deriv g z / g z := by
  have h1 : DifferentiableAt ℂ (fun y => (y - z₀) ^ n) z :=
    ((differentiable_fun_id.sub_const z₀).pow n).differentiableAt
  simp only [hfg.deriv_eq, hfg.self_of_nhds]
  cases n
  case zero => simp
  case succ n =>
    have hzz : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have h2 : deriv (fun y : ℂ => (y - z₀) ^ (n + 1)) z = (n + 1) * (z - z₀) ^ n := by
      simp only [differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_sub,
        deriv_fun_pow, cast_add, cast_one, add_tsub_cancel_right, deriv_fun_sub, deriv_id'',
        deriv_const', sub_zero, mul_one]
    simp only [cast_add, cast_one]
    rw [deriv_fun_mul h1 hg, h2]
    field_simp [_root_.pow_succ, hzz]
    ring

lemma eventually_deriv_div_self_eq (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) :
    let g := (iterate (swap dslope z₀) p.order) f
    ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → deriv f z / f z = p.order / (z - z₀) + deriv g z / g z := by
  intro g
  obtain ⟨r, h2⟩ := hp.has_fpower_series_iterate_dslope_fslope p.order
  have lh1 := h2.differentiableOn.eventually_differentiableAt (Metric.eball_mem_nhds _ h2.r_pos)
  have lh2 := hp.dslope_order_eventually_ne_zero h
  have lh3 : ∀ᶠ z in 𝓝 z₀, f =ᶠ[𝓝 z] fun w => (w - z₀) ^ p.order * g w := by
    exact Eventually.of_forall fun _ =>
      Eventually.of_forall fun w => by
        simpa [g, smul_eq_mul] using hp.eq_pow_order_mul_iterate_dslope w
  filter_upwards [lh1, lh2, lh3] with z using deriv_div_self_eq_div_add_deriv_div_self

lemma cindex_eq_zero (hU : IsOpen U) (hr : 0 < r) (hcr : closedBall c r ⊆ U)
    (f_hol : DifferentiableOn ℂ f U) (hf : ∀ z ∈ closedBall c r, f z ≠ 0) :
    cindex c r f = 0 := by
  obtain ⟨V, h1, h2, h3, h4⟩ : ∃ V, V ⊆ U ∧ IsOpen V ∧ closedBall c r ⊆ V ∧ ∀ z ∈ V, f z ≠ 0 := by
    set s : Set ℂ := { z ∈ U | f z ≠ 0 }
    have e1 : IsCompact (closedBall c r) := isCompact_closedBall _ _
    have e2 : IsOpen s := f_hol.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
    have e3 : closedBall c r ⊆ s := fun z hz => ⟨hcr hz, hf z hz⟩
    obtain ⟨δ, e4, e5⟩ := e1.exists_thickening_subset_open e2 e3
    refine ⟨thickening δ (closedBall c r), ?_, isOpen_thickening, self_subset_thickening e4 _, ?_⟩
    · exact (e5.trans <| Set.sep_subset _ _)
    · exact fun z hz => (e5 hz).2
  simpa [cindex, Real.pi_ne_zero] using
    circle_integral_eq_zero h2 hr h3 (((f_hol.mono h1).deriv h2).div (f_hol.mono h1) h4)

-- TODO: off-center using `integral_sub_inv_of_mem_ball`

lemma cindex_eq_order_aux (hU : IsOpen U) (hr : 0 < r) (h0 : closedBall z₀ r ⊆ U)
    (h1 : DifferentiableOn ℂ g U) (h2 : ∀ z ∈ closedBall z₀ r, g z ≠ 0)
    (h3 : ∀ {z}, z ∈ sphere z₀ r → deriv f z / f z = c / (z - z₀) + deriv g z / g z) :
    cindex z₀ r f = c := by
  have e2 : sphere z₀ r ⊆ U := sphere_subset_closedBall.trans h0
  have e4 : (∮ z in C(z₀,r), deriv f z / f z) =
      ∮ z in C(z₀,r), c / (z - z₀) + deriv g z / g z :=
    circleIntegral.integral_congr hr.le (fun z hz => h3 hz)
  have e5 : (∮ z in C(z₀,r), c / (z - z₀) + deriv g z / g z) =
      (∮ z in C(z₀, r), c / (z - z₀)) + (∮ z in C(z₀, r), deriv g z / g z) := by
    apply circleIntegral.integral_add
    · apply ContinuousOn.circleIntegrable hr.le
      apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
      exact fun z hz => sub_ne_zero.mpr (ne_of_mem_sphere hz hr.ne.symm)
    · apply ContinuousOn.circleIntegrable hr.le
      refine ContinuousOn.div ?_ (h1.continuousOn.mono e2)
        (fun z hz => h2 _ (sphere_subset_closedBall hz))
      refine ContinuousOn.mono ?_ e2
      apply ContDiffOn.continuousOn_deriv_of_isOpen ?_ hU le_rfl
      exact h1.contDiffOn hU
  have e6 : (∮ z in C(z₀, r), deriv g z / g z) = 0 := by
    have := cindex_eq_zero hU hr h0 h1 h2
    simpa [cindex, Real.pi_ne_zero, I_ne_zero] using this
  have e7 : (∮ z in C(z₀, r), c / (z - z₀)) = 2 * π * I * c := by
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      circle_integral_sub_center_inv_smul (E := ℂ) (c := z₀) (v := c) hr
  simp [field, cindex, e4, e5, e6, e7]

lemma exists_cindex_eq_order' (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) :
    ∃ R > (0 : ℝ), ∀ r ∈ Set.Ioo 0 R, cindex z₀ r f = p.order := by
  set g : ℂ → ℂ := iterate (swap dslope z₀) p.order f
  have lh1 : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hp.dslope_order_eventually_ne_zero h
  have lh2 : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → deriv f z / f z = p.order / (z - z₀) + deriv g z / g z :=
    eventually_deriv_div_self_eq hp h
  have lh3 : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g z :=
    (hp.has_fpower_series_iterate_dslope_fslope p.order).eventually_differentiableAt
  obtain ⟨R, hR₁, hh⟩ := Metric.mem_nhds_iff.mp (lh1.and (lh2.and lh3))
  refine ⟨R, hR₁, fun r hr => ?_⟩
  refine cindex_eq_order_aux isOpen_ball hr.1 (closedBall_subset_ball hr.2)
    (fun z hz => (hh hz).2.2.differentiableWithinAt)
    (fun z hz => (hh (closedBall_subset_ball hr.2 hz)).1)
    (fun hz => ?_)
  refine (hh (sphere_subset_closedBall.trans (closedBall_subset_ball hr.2) hz)).2.1 ?_
  exact ne_of_mem_sphere hz hr.1.ne.symm

lemma exists_cindex_eq_order (hp : HasFPowerSeriesAt f p z₀) :
    ∃ R > (0 : ℝ), ∀ r ∈ Set.Ioo 0 R, cindex z₀ r f = p.order := by
  by_cases h : p = 0
  case neg => exact exists_cindex_eq_order' hp h
  case pos =>
    subst_vars
    obtain ⟨R, hR, hf⟩ := Metric.eventually_nhds_iff.mp (hp.locally_zero_iff.mpr rfl)
    refine ⟨R, hR, fun r hr => ?_⟩
    have heq : Set.EqOn (fun z => deriv f z / f z) 0 (sphere z₀ r) := by
      intro z hz
      have hd : dist z z₀ < R := by
        rw [mem_sphere_iff_norm, ← Complex.dist_eq] at hz
        simpa [hz] using hr.2
      have hfz : f z = 0 := hf hd
      have hev : ∀ᶠ y in 𝓝 z, f y = 0 := by
        have : Metric.ball z (R - dist z z₀) ∈ 𝓝 z :=
          Metric.ball_mem_nhds z (by linarith)
        filter_upwards [this] with y hy
        apply hf
        have h1 : dist y z < R - dist z z₀ := hy
        linarith [dist_triangle y z z₀]
      have hderiv : deriv f z = 0 := by
        have heqz : f =ᶠ[𝓝 z] 0 := hev.mono (fun _ h => h)
        rw [heqz.deriv_eq]; simp
      simp [hderiv, hfz]
    simp only [cindex, mul_inv_rev, inv_I, neg_mul, FormalMultilinearSeries.order_zero,
      CharP.cast_eq_zero, neg_eq_zero, _root_.mul_eq_zero, I_ne_zero, inv_eq_zero,
      ofReal_eq_zero, pi_ne_zero, OfNat.ofNat_ne_zero, or_self, false_or]
    rw [circleIntegral.integral_congr hr.1.le heq]
    simp [circleIntegral]

lemma cindex_eventually_eq_order (hp : HasFPowerSeriesAt f p z₀) :
    ∀ᶠ r in 𝓝[>] 0, cindex z₀ r f = p.order := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  obtain ⟨R, hR, hf⟩ := exists_cindex_eq_order hp
  exact ⟨R, hR, fun r hr1 hr2 => hf r ⟨hr2, by simpa using lt_of_abs_lt hr1⟩⟩
