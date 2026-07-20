/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.SigmaZeta
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Elliptic functions and the Liouville theorems

Statements from chapter 1 of Milla (arXiv:1809.00533v6, file `060_ElliptFunct.tex`):

* `PeriodPair.IsEllipticWith` : an elliptic function for a lattice `L` — a meromorphic
  function on `ℂ` that is `L`-periodic;
* `PeriodPair.fundamentalParallelogram` : the fundamental parallelogram `𝒫` (paper
  Def. `fund`);
* `Chudnovsky.residue` : the residue of a function at a point, defined as the limit of
  circle integrals `(2πi)⁻¹ ∮_{|z-c|=r} f` as `r → 0⁺`;
* the three Liouville theorems (paper `liouville1`, `liouville2`, `liouville3`) and the
  "workhorse" lemma: two elliptic functions with the same zeros and poles (with orders)
  agree up to a nonzero constant factor.

All statements in this file are fully proved (no `sorry`s). The second Liouville theorem is
proved via a self-contained parallelogram residue theorem built from Mathlib's rectangle
Cauchy--Goursat primitives.
-/

noncomputable section

namespace Chudnovsky

open scoped Real

/-- The residue of `f : ℂ → ℂ` at a point `c`, defined as the limit of the circle
integrals `(2πi)⁻¹ ∮_{|z-c|=r} f(z) dz` as `r → 0⁺`. For a function meromorphic at `c`
these integrals are eventually constant in `r`, so the limit exists and is the usual
residue; for other functions the value is junk. -/
def residue (f : ℂ → ℂ) (c : ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin (0 : ℝ) (Set.Ioi 0)) fun r : ℝ ↦
    (2 * (π : ℂ) * Complex.I)⁻¹ * ∮ z in C(c, r), f z

open Filter Topology in
/-- The normalising constant `2πi ≠ 0`. -/
private lemma two_pi_I_ne_zero : (2 * (π : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

open Filter Topology in
/-- If the normalised circle integrals defining the residue are eventually equal to a constant
`a` as the radius `r → 0⁺`, then `residue f c = a`. This is the basic tool for computing residues:
the integrals need only be known for all *small* `r`. -/
lemma residue_eq_of_eventuallyEq {f : ℂ → ℂ} {c a : ℂ}
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (2 * (π : ℂ) * Complex.I)⁻¹ * ∮ z in C(c, r), f z = a) :
    residue f c = a := by
  have h' : (fun r : ℝ ↦ (2 * (π : ℂ) * Complex.I)⁻¹ * ∮ z in C(c, r), f z) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ ↦ a) := h
  exact Filter.Tendsto.limUnder_eq (tendsto_const_nhds.congr' h'.symm)

open Filter Topology in
/-- The residue depends only on the germ of `f` on a punctured neighbourhood of `c`. -/
lemma residue_congr {f₁ f₂ : ℂ → ℂ} {c : ℂ} (h : f₁ =ᶠ[𝓝[≠] c] f₂) :
    residue f₁ c = residue f₂ c := by
  -- Turn the punctured-neighbourhood agreement into agreement of the circle integrals
  -- for small `r`.
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp h
  have hev : (fun r : ℝ ↦ (2 * (π : ℂ) * Complex.I)⁻¹ * ∮ z in C(c, r), f₁ z) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r : ℝ ↦ (2 * (π : ℂ) * Complex.I)⁻¹ * ∮ z in C(c, r), f₂ z) := by
    have hlt : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ε :=
      (show ∀ᶠ r in 𝓝 (0 : ℝ), r < ε from Iio_mem_nhds hε).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hlt] with r hr hrε
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    have hdist : dist (circleMap c r θ) c = r := by
      have h := Metric.mem_sphere.mp (circleMap_mem_sphere' c r θ)
      rwa [abs_of_pos hr] at h
    have hmem : circleMap c r θ ∈ Metric.ball c ε ∩ {c}ᶜ :=
      ⟨Metric.mem_ball.mpr (by rw [hdist]; exact hrε), by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact circleMap_ne_center (ne_of_gt hr)⟩
    have heq := hball hmem
    simp only [Set.mem_setOf_eq] at heq
    change deriv (circleMap c r) θ • f₁ (circleMap c r θ)
      = deriv (circleMap c r) θ • f₂ (circleMap c r θ)
    rw [heq]
  unfold residue
  exact congrArg Filter.lim (Filter.map_congr hev)

open Filter Topology in
/-- The residue of `(z - c)⁻¹` at `c` is `1`. -/
lemma residue_sub_center_inv (c : ℂ) : residue (fun z ↦ (z - c)⁻¹) c = 1 := by
  apply residue_eq_of_eventuallyEq
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [circleIntegral.integral_sub_center_inv c (ne_of_gt hr)]
  exact inv_mul_cancel₀ two_pi_I_ne_zero

open Filter Topology in
/-- **Translation invariance of the residue.** If `f` has period `ω` (`f (z + ω) = f z`), then its
residues at `c` and at `c + ω` agree. This lets one transport a residue count from a fundamental
parallelogram to any lattice translate of it. -/
lemma residue_add_of_periodic {f : ℂ → ℂ} {c ω : ℂ} (h : ∀ z, f (z + ω) = f z) :
    residue f (c + ω) = residue f c := by
  have hfun : (fun r : ℝ ↦ (2 * (π : ℂ) * Complex.I)⁻¹ * ∮ z in C(c + ω, r), f z)
      = fun r : ℝ ↦ (2 * (π : ℂ) * Complex.I)⁻¹ * ∮ z in C(c, r), f z := by
    ext r
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    have hc : circleMap (c + ω) r θ = circleMap c r θ + ω := by
      simp only [circleMap]; ring
    change deriv (circleMap (c + ω) r) θ • f (circleMap (c + ω) r θ)
      = deriv (circleMap c r) θ • f (circleMap c r θ)
    rw [deriv_circleMap, deriv_circleMap, hc, h]
  unfold residue
  rw [hfun]

open Filter Topology in
/-- A function analytic at `c` has residue `0` there. -/
lemma residue_eq_zero_of_analyticAt {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    residue f c = 0 := by
  apply residue_eq_of_eventuallyEq
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
  have hlt : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ε :=
    (show ∀ᶠ r in 𝓝 (0 : ℝ), r < ε from Iio_mem_nhds hε).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with r hr hrε
  have hz : (∮ z in C(c, r), f z) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable (le_of_lt hr)
      Set.countable_empty
    · intro z hz
      have : dist z c < ε := lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hrε
      exact (hball this).continuousAt.continuousWithinAt
    · intro z hz
      have : dist z c < ε := lt_of_lt_of_le (Metric.mem_ball.mp hz.1) (le_of_lt hrε)
      exact (hball this).differentiableAt
  rw [hz, mul_zero]

open Filter Topology in
/-- The residue of a simple pole `a·(z-c)⁻¹` plus an analytic part is the coefficient `a`. -/
lemma residue_simplePole_add_analytic {c a : ℂ} {w : ℂ → ℂ} (hw : AnalyticAt ℂ w c) :
    residue (fun z ↦ a * (z - c)⁻¹ + w z) c = a := by
  apply residue_eq_of_eventuallyEq
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hw.eventually_analyticAt
  have hlt : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ε :=
    (show ∀ᶠ r in 𝓝 (0 : ℝ), r < ε from Iio_mem_nhds hε).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with r hr hrε
  have hr0 : (0 : ℝ) < r := hr
  -- the two pieces are circle-integrable
  have hint1 : CircleIntegrable (fun z ↦ a * (z - c)⁻¹) c r := by
    refine ContinuousOn.circleIntegrable hr0.le (continuousOn_const.mul ?_)
    refine (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => ?_)
    rw [Metric.mem_sphere] at hz
    simp only [id_eq]
    refine sub_ne_zero.2 (fun h => ?_)
    rw [h, dist_self] at hz
    exact hr0.ne' hz.symm
  have hint2 : CircleIntegrable w c r := by
    refine ContinuousOn.circleIntegrable hr0.le (fun z hz => ?_)
    rw [Metric.mem_sphere] at hz
    exact (hball (hz.trans_lt hrε)).continuousAt.continuousWithinAt
  have hw0 : (∮ z in C(c, r), w z) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr0.le
      Set.countable_empty
    · exact fun z hz =>
        (hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hrε)).continuousAt.continuousWithinAt
    · exact fun z hz => (hball (lt_of_lt_of_le (Metric.mem_ball.mp hz.1) hrε.le)).differentiableAt
  rw [circleIntegral.integral_add hint1 hint2, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_center_inv c hr0.ne', hw0, add_zero, mul_comm a,
    ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

open Filter Topology in
/-- **Residue of the logarithmic derivative equals the order.** For a function `f` meromorphic at
`c` with finite order there, the residue of `f'/f = logDeriv f` at `c` equals the order of `f` at
`c` (a simple pole with integer residue). This is the local computation behind the third Liouville
theorem. -/
lemma residue_logDeriv_eq_order {f : ℂ → ℂ} {c : ℂ} (hf : MeromorphicAt f c)
    (hord : meromorphicOrderAt f c ≠ ⊤) :
    residue (logDeriv f) c = ((meromorphicOrderAt f c).untop₀ : ℂ) := by
  set n : ℤ := (meromorphicOrderAt f c).untop₀ with hn
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).1 hord
  -- `hg_eq : f =ᶠ[𝓝[≠] c] fun z ↦ (z - c) ^ n • g z`
  have hlogeq : logDeriv f =ᶠ[𝓝[≠] c] fun z ↦ (n : ℂ) * (z - c)⁻¹ + logDeriv g z := by
    have hderiv : deriv f =ᶠ[𝓝[≠] c] deriv (fun z ↦ (z - c) ^ n • g z) := hg_eq.nhdsNE_deriv
    have hg_ne_nb : ∀ᶠ z in 𝓝[≠] c, g z ≠ 0 :=
      (hg_an.continuousAt.eventually_ne hg_ne).filter_mono nhdsWithin_le_nhds
    have hg_diff_nb : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ g z :=
      (hg_an.eventually_analyticAt.mono fun z hz => hz.differentiableAt).filter_mono
        nhdsWithin_le_nhds
    have hne_nb : ∀ᶠ z in 𝓝[≠] c, z ≠ c := by
      filter_upwards [self_mem_nhdsWithin] with z hz using hz
    filter_upwards [hg_eq, hderiv, hg_ne_nb, hg_diff_nb, hne_nb] with z hfz hdz hgz hgdz hzc
    have hzc' : z - c ≠ 0 := sub_ne_zero.2 hzc
    have hstep : logDeriv f z = logDeriv (fun z ↦ (z - c) ^ n • g z) z := by
      rw [logDeriv_apply, logDeriv_apply, hdz, hfz]
    rw [hstep]
    have hmul : (fun z ↦ (z - c) ^ n • g z) = fun z ↦ (z - c) ^ n * g z := by
      ext z; rw [smul_eq_mul]
    have hbase : DifferentiableAt ℂ (fun z : ℂ ↦ z - c) z := by fun_prop
    have hmulLog : logDeriv (fun z ↦ (z - c) ^ n * g z) z
        = logDeriv (fun z ↦ (z - c) ^ n) z + logDeriv g z :=
      logDeriv_mul (f := fun z ↦ (z - c) ^ n) (g := g) z (zpow_ne_zero n hzc') hgz
        (hbase.zpow (Or.inl hzc')) hgdz
    rw [hmul, hmulLog]
    have hzpow : logDeriv (fun z ↦ (z - c) ^ n) z = (n : ℂ) * (z - c)⁻¹ := by
      rw [logDeriv_fun_zpow (f := fun z : ℂ ↦ z - c) hbase n, logDeriv_apply,
        show deriv (fun z ↦ z - c) z = 1 from ((hasDerivAt_id z).sub_const c).deriv, one_div]
    rw [hzpow]
  rw [residue_congr hlogeq, residue_simplePole_add_analytic]
  exact hg_an.deriv.div hg_an hg_ne

end Chudnovsky

namespace PeriodPair

open Filter Topology

variable (L : PeriodPair)

/-- An elliptic function for the lattice of the period pair `L`: a meromorphic function
`ℂ → ℂ` which is periodic with respect to every lattice point (paper Def. of "elliptic
function", ch. 1). -/
def IsEllipticWith (f : ℂ → ℂ) : Prop :=
  Meromorphic f ∧ ∀ (z : ℂ) (l : L.lattice), f (z + l) = f z

/-- The fundamental parallelogram `𝒫 = {s·ω₁ + t·ω₂ | 0 ≤ s, t < 1}` (paper Def. `fund`).
Every `z : ℂ` is equivalent modulo `L.lattice` to exactly one point of `𝒫`. -/
def fundamentalParallelogram : Set ℂ :=
  {z : ℂ | ∃ s ∈ Set.Ico (0 : ℝ) 1, ∃ t ∈ Set.Ico (0 : ℝ) 1, z = s • L.ω₁ + t • L.ω₂}

/-- `℘` is an elliptic function. -/
theorem isEllipticWith_weierstrassP : L.IsEllipticWith ℘[L] :=
  ⟨L.meromorphic_weierstrassP, fun z l ↦ L.weierstrassP_add_coe z l⟩

/-- `℘'` is an elliptic function. -/
theorem isEllipticWith_derivWeierstrassP : L.IsEllipticWith ℘'[L] :=
  ⟨L.meromorphic_derivWeierstrassP, fun z l ↦ L.derivWeierstrassP_add_coe z l⟩

/-- Every `z : ℂ` differs by a lattice point from a point of the fundamental parallelogram. -/
lemma exists_sub_mem_lattice_of_mem_fundamentalParallelogram (L : PeriodPair) (z : ℂ) :
    ∃ w ∈ L.fundamentalParallelogram, z - w ∈ L.lattice := by
  have hz : (L.basis.repr z 0 • L.ω₁ + L.basis.repr z 1 • L.ω₂ : ℂ) = z := by
    have h := L.basis.sum_repr z
    rwa [Fin.sum_univ_two, L.basis_zero, L.basis_one] at h
  set a := L.basis.repr z 0
  set b := L.basis.repr z 1
  refine ⟨Int.fract a • L.ω₁ + Int.fract b • L.ω₂,
    ⟨Int.fract a, ⟨Int.fract_nonneg a, Int.fract_lt_one a⟩, Int.fract b,
      ⟨Int.fract_nonneg b, Int.fract_lt_one b⟩, rfl⟩, ?_⟩
  rw [PeriodPair.mem_lattice]
  refine ⟨⌊a⌋, ⌊b⌋, ?_⟩
  have e1 : ((⌊a⌋ : ℤ) : ℂ) = (a : ℂ) - ((Int.fract a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub, Int.self_sub_fract, Complex.ofReal_intCast]
  have e2 : ((⌊b⌋ : ℤ) : ℂ) = (b : ℂ) - ((Int.fract b : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub, Int.self_sub_fract, Complex.ofReal_intCast]
  rw [← hz]
  simp only [Complex.real_smul]
  rw [e1, e2]
  ring

variable {L}
variable {f g : ℂ → ℂ}

/-- The fundamental parallelogram intersected with a closed discrete set is finite (used to
turn "codiscretely nice" conditions into finiteness statements over `𝒫`). -/
private lemma finite_fundamentalParallelogram_inter {L : PeriodPair} {S : Set ℂ}
    (hclosed : IsClosed S) (hdisc : IsDiscrete S) :
    (L.fundamentalParallelogram ∩ S).Finite := by
  have hPsub : L.fundamentalParallelogram ⊆ Metric.closedBall (0 : ℂ) (‖L.ω₁‖ + ‖L.ω₂‖) := by
    rintro w ⟨s, hs, t, ht, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2.le
    have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2.le
    calc ‖s • L.ω₁ + t • L.ω₂‖
        ≤ ‖s • L.ω₁‖ + ‖t • L.ω₂‖ := norm_add_le _ _
      _ = |s| * ‖L.ω₁‖ + |t| * ‖L.ω₂‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖L.ω₁‖ + ‖L.ω₂‖ := by nlinarith [norm_nonneg L.ω₁, norm_nonneg L.ω₂]
  exact (Metric.finite_isBounded_inter_isClosed hdisc Metric.isBounded_closedBall hclosed).subset
    (Set.inter_subset_inter_left S hPsub)

/-- **First Liouville theorem** (paper `liouville1`): an elliptic function without poles
(i.e. entire) is constant. -/
theorem IsEllipticWith.exists_eq_const_of_differentiable (hf : L.IsEllipticWith f)
    (hd : Differentiable ℂ f) : ∃ c : ℂ, f = fun _ ↦ c := by
  have hcompact : IsCompact ((fun p : ℝ × ℝ ↦ p.1 • L.ω₁ + p.2 • L.ω₂) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    apply (isCompact_Icc.prod isCompact_Icc).image
    fun_prop
  obtain ⟨M, hM⟩ := (hcompact.image hd.continuous).isBounded.subset_closedBall (0 : ℂ)
  have hbdd : Bornology.IsBounded (Set.range f) := by
    have hsub : Set.range f ⊆ Metric.closedBall (0 : ℂ) M := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨w, ⟨s, hs, t, ht, rfl⟩, hl⟩ :=
        L.exists_sub_mem_lattice_of_mem_fundamentalParallelogram z
      have h := hf.2 (s • L.ω₁ + t • L.ω₂) ⟨z - (s • L.ω₁ + t • L.ω₂), hl⟩
      rw [show (s • L.ω₁ + t • L.ω₂) + ((⟨z - (s • L.ω₁ + t • L.ω₂), hl⟩ : L.lattice) : ℂ) = z
        from by simp] at h
      rw [h]
      exact hM (Set.mem_image_of_mem f
        ⟨(s, t), ⟨⟨hs.1, hs.2.le⟩, ⟨ht.1, ht.2.le⟩⟩, rfl⟩)
    exact Metric.isBounded_closedBall.subset hsub
  obtain ⟨c, hc⟩ := hd.exists_const_forall_eq_of_bounded hbdd
  exact ⟨c, funext hc⟩

/-- An elliptic function has only finitely many singularities in the (bounded)
fundamental parallelogram. Part of the **second Liouville theorem** (paper `liouville2`). -/
theorem IsEllipticWith.finite_nonAnalytic (hf : L.IsEllipticWith f) :
    {z ∈ L.fundamentalParallelogram | ¬AnalyticAt ℂ f z}.Finite := by
  have hcod : {z : ℂ | AnalyticAt ℂ f z} ∈ Filter.codiscrete ℂ :=
    MeromorphicOn.eventually_codiscreteWithin_analyticAt f (meromorphicOn_univ.mpr hf.1)
  have hcd : {z : ℂ | ¬AnalyticAt ℂ f z}ᶜ ∈ Filter.codiscrete ℂ := by
    simpa only [Set.compl_setOf, not_not] using hcod
  obtain ⟨hclosed, hdisc⟩ := compl_mem_codiscrete_iff.mp hcd
  exact (finite_fundamentalParallelogram_inter hclosed hdisc).subset (fun z hz => ⟨hz.1, hz.2⟩)

/-- The integral of `f` along the (positively oriented) boundary of the parallelogram with base
point `v` and sides `ω₁`, `ω₂`, parametrised over `t ∈ [0,1]`. The four terms are the bottom,
right, top (reversed) and left (reversed) edges; this is the contour used in the residue-theorem
proof of the second Liouville theorem. -/
def boundaryIntegral (L : PeriodPair) (f : ℂ → ℂ) (v : ℂ) : ℂ :=
    (∫ t in (0 : ℝ)..1, f (v + (t : ℂ) * L.ω₁) * L.ω₁)
  + (∫ t in (0 : ℝ)..1, f (v + L.ω₁ + (t : ℂ) * L.ω₂) * L.ω₂)
  - (∫ t in (0 : ℝ)..1, f (v + L.ω₂ + (t : ℂ) * L.ω₁) * L.ω₁)
  - (∫ t in (0 : ℝ)..1, f (v + (t : ℂ) * L.ω₂) * L.ω₂)

/-- **Boundary integral of an elliptic function vanishes** (paper `liouville2`, the cancellation of
opposite edges). By double periodicity the top edge repeats the bottom edge and the right edge
repeats the left edge, so with the orientation above the four contributions cancel in pairs. This
is the analysis-free half of the second Liouville theorem: combined with a parallelogram residue
theorem (`boundaryIntegral f v = 2πi · Σ residues inside`, still open) it yields
`sum_residue_eq_zero`. -/
theorem IsEllipticWith.boundaryIntegral_eq_zero (hf : L.IsEllipticWith f) (v : ℂ) :
    L.boundaryIntegral f v = 0 := by
  have per1 : ∀ z, f (z + L.ω₁) = f z := fun z => hf.2 z ⟨L.ω₁, L.ω₁_mem_lattice⟩
  have per2 : ∀ z, f (z + L.ω₂) = f z := fun z => hf.2 z ⟨L.ω₂, L.ω₂_mem_lattice⟩
  have h31 : (∫ t in (0 : ℝ)..1, f (v + L.ω₂ + (t : ℂ) * L.ω₁) * L.ω₁)
      = ∫ t in (0 : ℝ)..1, f (v + (t : ℂ) * L.ω₁) * L.ω₁ := by
    apply intervalIntegral.integral_congr
    intro t _
    change f (v + L.ω₂ + (t : ℂ) * L.ω₁) * L.ω₁ = f (v + (t : ℂ) * L.ω₁) * L.ω₁
    rw [show v + L.ω₂ + (t : ℂ) * L.ω₁ = (v + (t : ℂ) * L.ω₁) + L.ω₂ from by ring, per2]
  have h24 : (∫ t in (0 : ℝ)..1, f (v + L.ω₁ + (t : ℂ) * L.ω₂) * L.ω₂)
      = ∫ t in (0 : ℝ)..1, f (v + (t : ℂ) * L.ω₂) * L.ω₂ := by
    apply intervalIntegral.integral_congr
    intro t _
    change f (v + L.ω₁ + (t : ℂ) * L.ω₂) * L.ω₂ = f (v + (t : ℂ) * L.ω₂) * L.ω₂
    rw [show v + L.ω₁ + (t : ℂ) * L.ω₂ = (v + (t : ℂ) * L.ω₂) + L.ω₁ from by ring, per1]
  rw [boundaryIntegral, h31, h24]
  ring

/-- The boundary of the parallelogram with base point `v`: the union of its four edges. -/
def boundarySet (L : PeriodPair) (v : ℂ) : Set ℂ :=
  ((fun t : ℝ ↦ v + (t : ℂ) * L.ω₁) '' Set.Icc 0 1) ∪
  ((fun t : ℝ ↦ v + L.ω₁ + (t : ℂ) * L.ω₂) '' Set.Icc 0 1) ∪
  ((fun t : ℝ ↦ v + L.ω₂ + (t : ℂ) * L.ω₁) '' Set.Icc 0 1) ∪
  ((fun t : ℝ ↦ v + (t : ℂ) * L.ω₂) '' Set.Icc 0 1)

/-- Fundamental theorem of calculus along one straight edge: if `F` is a primitive of `f` on the
segment `p + [0,1]·ω`, the edge integral is the difference of the endpoint values. -/
private lemma integral_edge_eq_sub {f F : ℂ → ℂ} {p ω : ℂ}
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt F (f (p + (t : ℂ) * ω)) (p + (t : ℂ) * ω))
    (hc : ContinuousOn (fun t : ℝ ↦ f (p + (t : ℂ) * ω)) (Set.Icc 0 1)) :
    ∫ t in (0 : ℝ)..1, f (p + (t : ℂ) * ω) * ω = F (p + ω) - F p := by
  have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ p + (s : ℂ) * ω) ω t := by
    intro t
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const ω).const_add p
  have key : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ F (p + (s : ℂ) * ω)) (f (p + (t : ℂ) * ω) * ω) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h := HasDerivAt.scomp_of_eq t (hF t ht) (hγ t) rfl
    have hcomp : (F ∘ fun s : ℝ ↦ p + (s : ℂ) * ω) = fun s : ℝ ↦ F (p + (s : ℂ) * ω) := rfl
    rw [hcomp] at h
    have hval : ω • f (p + (t : ℂ) * ω) = f (p + (t : ℂ) * ω) * ω := by
      rw [smul_eq_mul, mul_comm]
    rw [← hval]
    exact h
  have hint : IntervalIntegrable (fun t : ℝ ↦ f (p + (t : ℂ) * ω) * ω)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hc.mul continuousOn_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt key hint
  rw [h]
  norm_num

/-- Each edge parametrization lands in the boundary set. -/
private lemma mem_boundarySet_of_edge {L : PeriodPair} {v : ℂ} :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, v + (t : ℂ) * L.ω₁ ∈ L.boundarySet v) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, v + L.ω₁ + (t : ℂ) * L.ω₂ ∈ L.boundarySet v) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, v + L.ω₂ + (t : ℂ) * L.ω₁ ∈ L.boundarySet v) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, v + (t : ℂ) * L.ω₂ ∈ L.boundarySet v) := by
  refine ⟨fun t ht => Or.inl (Or.inl (Or.inl ⟨t, ht, rfl⟩)),
    fun t ht => Or.inl (Or.inl (Or.inr ⟨t, ht, rfl⟩)),
    fun t ht => Or.inl (Or.inr ⟨t, ht, rfl⟩),
    fun t ht => Or.inr ⟨t, ht, rfl⟩⟩

/-- **Loop integral of a derivative vanishes**: if `F` is a primitive of `f` on the boundary of
the parallelogram, then the boundary integral of `f` is zero (fundamental theorem of calculus
along each edge, then telescoping around the closed loop). -/
private lemma boundaryIntegral_eq_zero_of_primitive {L : PeriodPair} {f F : ℂ → ℂ} {v : ℂ}
    (hF : ∀ z ∈ L.boundarySet v, HasDerivAt F (f z) z)
    (hc : ContinuousOn f (L.boundarySet v)) :
    L.boundaryIntegral f v = 0 := by
  obtain ⟨he₁, he₂, he₃, he₄⟩ := mem_boundarySet_of_edge (L := L) (v := v)
  have hcont : ∀ (p ω : ℂ), (∀ t ∈ Set.Icc (0 : ℝ) 1, p + (t : ℂ) * ω ∈ L.boundarySet v) →
      ContinuousOn (fun t : ℝ ↦ f (p + (t : ℂ) * ω)) (Set.Icc 0 1) := by
    intro p ω hmem
    apply hc.comp _ hmem
    fun_prop
  have E1 := integral_edge_eq_sub (fun t ht => hF _ (he₁ t ht)) (hcont _ _ he₁)
  have E2 := integral_edge_eq_sub (fun t ht => hF _ (he₂ t ht)) (hcont _ _ he₂)
  have E3 := integral_edge_eq_sub (fun t ht => hF _ (he₃ t ht)) (hcont _ _ he₃)
  have E4 := integral_edge_eq_sub (fun t ht => hF _ (he₄ t ht)) (hcont _ _ he₄)
  rw [boundaryIntegral, E1, E2, E3, E4,
    show v + L.ω₂ + L.ω₁ = v + L.ω₁ + L.ω₂ from by ring]
  ring

/-- The boundary integral of `(z - c) ^ n`, `n ≠ -1`, vanishes whenever `c` is not on the
boundary (the function has the global primitive `(z - c) ^ (n + 1) / (n + 1)` off `c`). -/
private lemma boundaryIntegral_zpow_eq_zero {L : PeriodPair} {n : ℤ} (hn : n ≠ -1) {c v : ℂ}
    (hc : c ∉ L.boundarySet v) :
    L.boundaryIntegral (fun z ↦ (z - c) ^ n) v = 0 := by
  have hn' : (n + 1 : ℂ) ≠ 0 := by
    rwa [Ne, ← eq_neg_iff_add_eq_zero, ← Int.cast_one, ← Int.cast_neg, Int.cast_inj]
  apply boundaryIntegral_eq_zero_of_primitive (F := fun z ↦ (z - c) ^ (n + 1) / (n + 1))
  · intro z hz
    have hzc : z - c ≠ 0 := sub_ne_zero.2 (fun h => hc (h ▸ hz))
    have h := ((hasDerivAt_zpow (n + 1) (z - c) (Or.inl hzc)).comp z
      ((hasDerivAt_id z).sub_const c)).div_const (n + 1 : ℂ)
    simp only [add_sub_cancel_right, Function.comp_def, id_eq, mul_one] at h
    push_cast at h
    rwa [mul_div_cancel_left₀ _ hn'] at h
  · refine (continuousOn_id.sub continuousOn_const).zpow₀ n (fun z hz => ?_)
    exact Or.inl (sub_ne_zero.2 (fun h => hc (h ▸ hz)))

/-- Two boundary integrals of pointwise equal functions agree. -/
private lemma boundaryIntegral_congr {L : PeriodPair} {f g : ℂ → ℂ} {v : ℂ}
    (h : ∀ z ∈ L.boundarySet v, f z = g z) :
    L.boundaryIntegral f v = L.boundaryIntegral g v := by
  obtain ⟨he₁, he₂, he₃, he₄⟩ := mem_boundarySet_of_edge (L := L) (v := v)
  have key : ∀ (p ω : ℂ), (∀ t ∈ Set.Icc (0 : ℝ) 1, p + (t : ℂ) * ω ∈ L.boundarySet v) →
      (∫ t in (0 : ℝ)..1, f (p + (t : ℂ) * ω) * ω)
        = ∫ t in (0 : ℝ)..1, g (p + (t : ℂ) * ω) * ω := by
    intro p ω hmem
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    change f (p + (t : ℂ) * ω) * ω = g (p + (t : ℂ) * ω) * ω
    rw [h _ (hmem t ht)]
  simp only [boundaryIntegral, key _ _ he₁, key _ _ he₂, key _ _ he₃, key _ _ he₄]

/-- Boundary integrals are additive (for boundary-continuous integrands). -/
private lemma boundaryIntegral_add {L : PeriodPair} {f g : ℂ → ℂ} {v : ℂ}
    (hf : ContinuousOn f (L.boundarySet v)) (hg : ContinuousOn g (L.boundarySet v)) :
    L.boundaryIntegral (fun z ↦ f z + g z) v =
      L.boundaryIntegral f v + L.boundaryIntegral g v := by
  obtain ⟨he₁, he₂, he₃, he₄⟩ := mem_boundarySet_of_edge (L := L) (v := v)
  have key : ∀ (p ω : ℂ), (∀ t ∈ Set.Icc (0 : ℝ) 1, p + (t : ℂ) * ω ∈ L.boundarySet v) →
      (∫ t in (0 : ℝ)..1, (f (p + (t : ℂ) * ω) + g (p + (t : ℂ) * ω)) * ω)
        = (∫ t in (0 : ℝ)..1, f (p + (t : ℂ) * ω) * ω)
          + ∫ t in (0 : ℝ)..1, g (p + (t : ℂ) * ω) * ω := by
    intro p ω hmem
    have hif : IntervalIntegrable (fun t : ℝ ↦ f (p + (t : ℂ) * ω) * ω)
        MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact (hf.comp (by fun_prop) hmem).mul continuousOn_const
    have hig : IntervalIntegrable (fun t : ℝ ↦ g (p + (t : ℂ) * ω) * ω)
        MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact (hg.comp (by fun_prop) hmem).mul continuousOn_const
    rw [← intervalIntegral.integral_add hif hig]
    apply intervalIntegral.integral_congr
    intro t _
    change (f (p + (t : ℂ) * ω) + g (p + (t : ℂ) * ω)) * ω
      = f (p + (t : ℂ) * ω) * ω + g (p + (t : ℂ) * ω) * ω
    ring
  simp only [boundaryIntegral, key _ _ he₁, key _ _ he₂, key _ _ he₃, key _ _ he₄]
  ring

/-- Boundary integrals commute with constant multiplication. -/
private lemma boundaryIntegral_const_mul {L : PeriodPair} (a : ℂ) (f : ℂ → ℂ) (v : ℂ) :
    L.boundaryIntegral (fun z ↦ a * f z) v = a * L.boundaryIntegral f v := by
  have key : ∀ (p ω : ℂ),
      (∫ t in (0 : ℝ)..1, (a * f (p + (t : ℂ) * ω)) * ω)
        = a * ∫ t in (0 : ℝ)..1, f (p + (t : ℂ) * ω) * ω := by
    intro p ω
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    change (a * f (p + (t : ℂ) * ω)) * ω = a * (f (p + (t : ℂ) * ω) * ω)
    ring
  simp only [boundaryIntegral, key]
  ring

/-- Boundary integrals respect subtraction (for boundary-continuous integrands). -/
private lemma boundaryIntegral_sub {L : PeriodPair} {f g : ℂ → ℂ} {v : ℂ}
    (hf : ContinuousOn f (L.boundarySet v)) (hg : ContinuousOn g (L.boundarySet v)) :
    L.boundaryIntegral (fun z ↦ f z - g z) v =
      L.boundaryIntegral f v - L.boundaryIntegral g v := by
  have hneg : ContinuousOn (fun z ↦ -g z) (L.boundarySet v) := hg.neg
  have h := boundaryIntegral_add hf hneg
  have hng : L.boundaryIntegral (fun z ↦ -g z) v = -L.boundaryIntegral g v := by
    have hcongr : L.boundaryIntegral (fun z ↦ -g z) v
        = L.boundaryIntegral (fun z ↦ (-1 : ℂ) * g z) v :=
      boundaryIntegral_congr (fun z _ => by ring)
    rw [hcongr, boundaryIntegral_const_mul]
    ring
  rw [show (fun z ↦ f z - g z) = fun z ↦ f z + -g z from funext fun z => by ring, h, hng]
  ring

/-- Boundary integrals commute with finite sums (of boundary-continuous integrands). -/
private lemma boundaryIntegral_finsetSum {L : PeriodPair} {ι : Type*} {s : Finset ι}
    {f : ι → ℂ → ℂ} {v : ℂ} (h : ∀ i ∈ s, ContinuousOn (f i) (L.boundarySet v)) :
    L.boundaryIntegral (fun z ↦ ∑ i ∈ s, f i z) v = ∑ i ∈ s, L.boundaryIntegral (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : L.boundaryIntegral (fun _ ↦ (0 : ℂ)) v
        = L.boundaryIntegral (fun z ↦ (0 : ℂ) * (0 : ℂ)) v :=
      boundaryIntegral_congr (fun z _ => by ring)
    rw [this, boundaryIntegral_const_mul, zero_mul]
  | insert a s ha ih =>
    have hconta : ContinuousOn (f a) (L.boundarySet v) := h a (Finset.mem_insert_self a s)
    have hcontsum : ContinuousOn (fun z ↦ ∑ i ∈ s, f i z) (L.boundarySet v) := by
      apply continuousOn_finsetSum
      intro i hi
      exact h i (Finset.mem_insert_of_mem hi)
    have hstep : L.boundaryIntegral (fun z ↦ ∑ i ∈ insert a s, f i z) v
        = L.boundaryIntegral (fun z ↦ f a z + ∑ i ∈ s, f i z) v :=
      boundaryIntegral_congr (fun z _ => Finset.sum_insert ha)
    rw [hstep, boundaryIntegral_add hconta hcontsum, Finset.sum_insert ha,
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]

/-- If `z` is not on the segment `[c, c']`, the ratio `(z - c) / (z - c')` lies in the slit
plane `ℂ ∖ (-∞, 0]` (on which `Complex.log` is differentiable). -/
private lemma div_mem_slitPlane_of_notMem_segment {z c c' : ℂ} (hz : z ∉ segment ℝ c c') :
    (z - c) / (z - c') ∈ Complex.slitPlane := by
  have hzc' : z ≠ c' := fun h => hz (h ▸ right_mem_segment ℝ c c')
  by_contra hcon
  rw [Complex.mem_slitPlane_iff] at hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  set u := (z - c) / (z - c') with hu
  have hureal : u = (u.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  set s : ℝ := -u.re with hs
  have hs0 : (0 : ℝ) ≤ s := by rw [hs]; linarith
  have hzc'ne : z - c' ≠ 0 := sub_ne_zero.2 hzc'
  have hmul : z - c = u * (z - c') := by
    rw [hu, div_mul_cancel₀ _ hzc'ne]
  have hmul' : z - c = -((s : ℝ) : ℂ) * (z - c') := by
    rw [hmul, hureal, hs]
    push_cast
    ring
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have h1sC : ((1 + s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1s.ne'
  have hzeq : ((1 + s : ℝ) : ℂ) * z = c + ((s : ℝ) : ℂ) * c' := by
    push_cast at hmul' ⊢
    linear_combination hmul'
  refine hz ⟨1 / (1 + s), s / (1 + s), div_nonneg zero_le_one h1s.le,
    div_nonneg hs0 h1s.le, by field_simp, ?_⟩
  have h1sC' : (1 + (s : ℂ)) ≠ 0 := by push_cast at h1sC; exact h1sC
  simp only [Complex.real_smul]
  push_cast
  push_cast at hzeq
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, ← add_div, div_eq_iff h1sC']
  linear_combination -hzeq

/-- The function `log ((z - c) / (z - c'))` is a primitive of `(z-c)⁻¹ - (z-c')⁻¹` away from the
segment `[c, c']`. -/
private lemma hasDerivAt_log_ratio {c c' z : ℂ} (hz : z ∉ segment ℝ c c') :
    HasDerivAt (fun w ↦ Complex.log ((w - c) / (w - c')))
      ((z - c)⁻¹ - (z - c')⁻¹) z := by
  have hzc : z ≠ c := fun h => hz (h ▸ left_mem_segment ℝ c c')
  have hzc' : z ≠ c' := fun h => hz (h ▸ right_mem_segment ℝ c c')
  have h1 : z - c ≠ 0 := sub_ne_zero.2 hzc
  have h2 : z - c' ≠ 0 := sub_ne_zero.2 hzc'
  have hslit := div_mem_slitPlane_of_notMem_segment hz
  have hφ : HasDerivAt (fun w ↦ (w - c) / (w - c'))
      ((1 * (z - c') - (z - c) * 1) / (z - c') ^ 2) z :=
    ((hasDerivAt_id z).sub_const c).div ((hasDerivAt_id z).sub_const c') h2
  have hlog := (Complex.hasDerivAt_log hslit).comp z hφ
  have hcomp : (Complex.log ∘ fun w ↦ (w - c) / (w - c'))
      = fun w ↦ Complex.log ((w - c) / (w - c')) := rfl
  rw [hcomp] at hlog
  have hval : ((z - c) / (z - c'))⁻¹ * ((1 * (z - c') - (z - c) * 1) / (z - c') ^ 2)
      = (z - c)⁻¹ - (z - c')⁻¹ := by
    field_simp
  rw [← hval]
  exact hlog

/-- **Constancy of the winding factor**: the boundary integrals of `(z - c)⁻¹` and `(z - c')⁻¹`
agree whenever the segment `[c, c']` does not meet the boundary (in application: both points lie
in the open parallelogram, which is convex). -/
private lemma boundaryIntegral_sub_inv_congr {L : PeriodPair} {v c c' : ℂ}
    (hseg : ∀ z ∈ L.boundarySet v, z ∉ segment ℝ c c') :
    L.boundaryIntegral (fun z ↦ (z - c)⁻¹) v = L.boundaryIntegral (fun z ↦ (z - c')⁻¹) v := by
  have hcont1 : ContinuousOn (fun z ↦ (z - c)⁻¹) (L.boundarySet v) := by
    refine (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => ?_)
    simp only [id_eq]
    exact sub_ne_zero.2 (fun h => hseg z hz (h ▸ left_mem_segment ℝ c c'))
  have hcont2 : ContinuousOn (fun z ↦ (z - c')⁻¹) (L.boundarySet v) := by
    refine (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => ?_)
    simp only [id_eq]
    exact sub_ne_zero.2 (fun h => hseg z hz (h ▸ right_mem_segment ℝ c c'))
  have hzero : L.boundaryIntegral (fun z ↦ (z - c)⁻¹ - (z - c')⁻¹) v = 0 :=
    boundaryIntegral_eq_zero_of_primitive
      (fun z hz => hasDerivAt_log_ratio (hseg z hz)) (hcont1.sub hcont2)
  rw [boundaryIntegral_sub hcont1 hcont2] at hzero
  exact sub_eq_zero.mp hzero

/-- Real coordinates with respect to `(ω₁, ω₂)` are unique (linear independence). -/
private lemma coord_eq_zero_of_eq_zero {L : PeriodPair} {r s : ℝ}
    (h : (r : ℂ) * L.ω₁ + (s : ℂ) * L.ω₂ = 0) : r = 0 ∧ s = 0 := by
  have hli := Fintype.linearIndependent_iff.mp L.indep ![r, s]
  have hsum : ∑ i, (![r, s] i) • (![L.ω₁, L.ω₂] i) = 0 := by
    rw [Fin.sum_univ_two]
    simpa [Complex.real_smul] using h
  have hall := hli hsum
  exact ⟨hall 0, hall 1⟩

/-- The "orientation area" `Im(conj ω₁ · ω₂)` of a period pair is nonzero. -/
private lemma im_conj_omega_ne_zero (L : PeriodPair) :
    ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := by
  intro him
  set ρ : ℝ := ((starRingEnd ℂ) L.ω₁ * L.ω₂).re with hρ
  have hreal : (starRingEnd ℂ) L.ω₁ * L.ω₂ = (ρ : ℂ) := by
    apply Complex.ext <;> simp [hρ, him]
  have hns : L.ω₁ * ((starRingEnd ℂ) L.ω₁ * L.ω₂) = (Complex.normSq L.ω₁ : ℂ) * L.ω₂ := by
    rw [← mul_assoc, Complex.mul_conj]
  have key0 : (ρ : ℂ) * L.ω₁ = (Complex.normSq L.ω₁ : ℂ) * L.ω₂ := by
    rw [← hns, hreal]
    ring
  have key : ((ρ : ℝ) : ℂ) * L.ω₁ + ((-(Complex.normSq L.ω₁) : ℝ) : ℂ) * L.ω₂ = 0 := by
    push_cast
    linear_combination key0
  obtain ⟨-, h2⟩ := coord_eq_zero_of_eq_zero key
  have hω₁ : L.ω₁ = 0 := Complex.normSq_eq_zero.mp (neg_eq_zero.mp h2)
  have h1 : (1 : ℝ) = 0 ∧ (0 : ℝ) = 0 :=
    coord_eq_zero_of_eq_zero (L := L) (r := 1) (s := 0) (by simp [hω₁])
  norm_num at h1

/-- The segment joining two interior points of the parallelogram misses its boundary. -/
private lemma notMem_segment_of_mem_boundarySet {L : PeriodPair} {v c c' : ℂ} {a₁ b₁ a₂ b₂ : ℝ}
    (ha₁ : a₁ ∈ Set.Ioo (0 : ℝ) 1) (hb₁ : b₁ ∈ Set.Ioo (0 : ℝ) 1)
    (ha₂ : a₂ ∈ Set.Ioo (0 : ℝ) 1) (hb₂ : b₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c = v + (a₁ : ℂ) * L.ω₁ + (b₁ : ℂ) * L.ω₂)
    (hc' : c' = v + (a₂ : ℂ) * L.ω₁ + (b₂ : ℂ) * L.ω₂) :
    ∀ z ∈ L.boundarySet v, z ∉ segment ℝ c c' := by
  rintro z hz ⟨u₁, u₂, hu₁, hu₂, husum, huz⟩
  have husumC : (u₁ : ℂ) + (u₂ : ℂ) = 1 := by exact_mod_cast husum
  have hzcoord : z = v + ((u₁ * a₁ + u₂ * a₂ : ℝ) : ℂ) * L.ω₁
      + ((u₁ * b₁ + u₂ * b₂ : ℝ) : ℂ) * L.ω₂ := by
    rw [← huz, hc, hc']
    simp only [Complex.real_smul]
    push_cast
    linear_combination v * husumC
  have hX : u₁ * a₁ + u₂ * a₂ ∈ Set.Ioo (0 : ℝ) 1 := by
    have := (convex_Ioo (0 : ℝ) 1) ha₁ ha₂ hu₁ hu₂ husum
    simpa [smul_eq_mul] using this
  have hY : u₁ * b₁ + u₂ * b₂ ∈ Set.Ioo (0 : ℝ) 1 := by
    have := (convex_Ioo (0 : ℝ) 1) hb₁ hb₂ hu₁ hu₂ husum
    simpa [smul_eq_mul] using this
  set X := u₁ * a₁ + u₂ * a₂
  set Y := u₁ * b₁ + u₂ * b₂
  rcases hz with ((⟨t, _, hzt⟩ | ⟨t, _, hzt⟩) | ⟨t, _, hzt⟩) | ⟨t, _, hzt⟩
  · -- bottom edge: `Y = 0` is impossible
    have h0 : ((t - X : ℝ) : ℂ) * L.ω₁ + ((0 - Y : ℝ) : ℂ) * L.ω₂ = 0 := by
      push_cast
      linear_combination hzcoord - hzt.symm
    have hY0 : Y = 0 := by linarith [(coord_eq_zero_of_eq_zero h0).2]
    exact hY.1.ne' hY0
  · -- right edge: `X = 1` is impossible
    have h0 : ((1 - X : ℝ) : ℂ) * L.ω₁ + ((t - Y : ℝ) : ℂ) * L.ω₂ = 0 := by
      push_cast
      linear_combination hzcoord - hzt.symm
    exact absurd ((coord_eq_zero_of_eq_zero h0).1) (by simpa [sub_eq_zero] using hX.2.ne')
  · -- top edge: `Y = 1` is impossible
    have h0 : ((t - X : ℝ) : ℂ) * L.ω₁ + ((1 - Y : ℝ) : ℂ) * L.ω₂ = 0 := by
      push_cast
      linear_combination hzcoord - hzt.symm
    exact absurd ((coord_eq_zero_of_eq_zero h0).2) (by simpa [sub_eq_zero] using hY.2.ne')
  · -- left edge: `X = 0` is impossible
    have h0 : ((0 - X : ℝ) : ℂ) * L.ω₁ + ((t - Y : ℝ) : ℂ) * L.ω₂ = 0 := by
      push_cast
      linear_combination hzcoord - hzt.symm
    have hX0 : X = 0 := by linarith [(coord_eq_zero_of_eq_zero h0).1]
    exact hX.1.ne' hX0

/-- Interval integrals of complex functions commute with the imaginary part. -/
private lemma intervalIntegral_im {f : ℝ → ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1) :
    (∫ t in (0 : ℝ)..1, f t).im = ∫ t in (0 : ℝ)..1, (f t).im := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  have h := integral_im (𝕜 := ℂ) hf.1
  rw [RCLike.im_eq_complex_im] at h
  exact h.symm

/-- The imaginary part of one edge integral of `(z - c)⁻¹`: it is a *constant* multiple of a
positive integral, the constant being the cross product `Im(ω · conj (p - c))`. -/
private lemma edge_inv_im {c p ω : ℂ} (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, p + (t : ℂ) * ω - c ≠ 0) :
    (∫ t in (0 : ℝ)..1, (p + (t : ℂ) * ω - c)⁻¹ * ω).im
      = (ω * (starRingEnd ℂ) (p - c)).im
        * ∫ t in (0 : ℝ)..1, (Complex.normSq (p + (t : ℂ) * ω - c))⁻¹ := by
  have hcont : ContinuousOn (fun t : ℝ ↦ (p + (t : ℂ) * ω - c)⁻¹ * ω) (Set.Icc 0 1) := by
    apply ContinuousOn.mul _ continuousOn_const
    exact ContinuousOn.inv₀ (by fun_prop) hne
  have hint : IntervalIntegrable (fun t : ℝ ↦ (p + (t : ℂ) * ω - c)⁻¹ * ω)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le zero_le_one]
  rw [intervalIntegral_im hint, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  set w := p + (t : ℂ) * ω - c with hw
  have hwne : w ≠ 0 := hne t ht
  have hsplit : w⁻¹ * ω = (ω * (starRingEnd ℂ) w) * (((Complex.normSq w)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.inv_def]
    push_cast
    ring
  change (w⁻¹ * ω).im = (ω * (starRingEnd ℂ) (p - c)).im * (Complex.normSq w)⁻¹
  rw [hsplit]
  have him1 : ((ω * (starRingEnd ℂ) w) * (((Complex.normSq w)⁻¹ : ℝ) : ℂ)).im
      = (ω * (starRingEnd ℂ) w).im * (Complex.normSq w)⁻¹ := by
    simp [Complex.mul_im]
  rw [him1]
  congr 1
  simp only [hw, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- **Nonvanishing of the winding factor**: for `c` in the open parallelogram, the boundary
integral of `(z - c)⁻¹` is nonzero. Its imaginary part is `Im(conj ω₁ · ω₂)` times a positive
quantity: on each edge the "cross-product" numerator is constant of the same sign. -/
private lemma boundaryIntegral_sub_inv_ne_zero {L : PeriodPair} {v c : ℂ} {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c = v + (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) :
    L.boundaryIntegral (fun z ↦ (z - c)⁻¹) v ≠ 0 := by
  set σ : ℝ := ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with hσ
  have hσne : σ ≠ 0 := im_conj_omega_ne_zero L
  -- nonvanishing of `z - c` along each edge, from coordinates
  have hne1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, v + (t : ℂ) * L.ω₁ - c ≠ 0 := by
    intro t _ h0
    have h0' : ((t - a : ℝ) : ℂ) * L.ω₁ + ((0 - b : ℝ) : ℂ) * L.ω₂ = 0 := by
      push_cast
      linear_combination h0 + hc
    exact hb.1.ne ((neg_eq_zero.mp (by simpa using (coord_eq_zero_of_eq_zero h0').2)).symm)
  have hne2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, v + L.ω₁ + (t : ℂ) * L.ω₂ - c ≠ 0 := by
    intro t _ h0
    have h0' : ((1 - a : ℝ) : ℂ) * L.ω₁ + ((t - b : ℝ) : ℂ) * L.ω₂ = 0 := by
      push_cast
      linear_combination h0 + hc
    exact ha.2.ne' (by
      have := (coord_eq_zero_of_eq_zero h0').1
      linarith [this])
  have hne3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, v + L.ω₂ + (t : ℂ) * L.ω₁ - c ≠ 0 := by
    intro t _ h0
    have h0' : ((t - a : ℝ) : ℂ) * L.ω₁ + ((1 - b : ℝ) : ℂ) * L.ω₂ = 0 := by
      push_cast
      linear_combination h0 + hc
    exact hb.2.ne' (by
      have := (coord_eq_zero_of_eq_zero h0').2
      linarith [this])
  have hne4 : ∀ t ∈ Set.Icc (0 : ℝ) 1, v + (t : ℂ) * L.ω₂ - c ≠ 0 := by
    intro t _ h0
    have h0' : ((0 - a : ℝ) : ℂ) * L.ω₁ + ((t - b : ℝ) : ℂ) * L.ω₂ = 0 := by
      push_cast
      linear_combination h0 + hc
    exact ha.1.ne ((neg_eq_zero.mp (by simpa using (coord_eq_zero_of_eq_zero h0').1)).symm)
  -- the four positive edge integrals
  have hpos : ∀ (p ω : ℂ), (∀ t ∈ Set.Icc (0 : ℝ) 1, p + (t : ℂ) * ω - c ≠ 0) →
      0 < ∫ t in (0 : ℝ)..1, (Complex.normSq (p + (t : ℂ) * ω - c))⁻¹ := by
    intro p ω hne
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      apply ContinuousOn.inv₀ (by fun_prop)
      intro t ht
      exact Complex.normSq_pos.mpr (hne t ht) |>.ne'
    · intro t ht
      have := Complex.normSq_pos.mpr (hne t (Set.mem_Icc_of_Ioo ht))
      positivity
    · exact zero_lt_one
  -- the four cross-product constants
  have hD1 : (L.ω₁ * (starRingEnd ℂ) (v - c)).im = b * σ := by
    rw [hc, hσ]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hD2 : (L.ω₂ * (starRingEnd ℂ) (v + L.ω₁ - c)).im = (1 - a) * σ := by
    rw [hc, hσ]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hD3 : (L.ω₁ * (starRingEnd ℂ) (v + L.ω₂ - c)).im = -((1 - b) * σ) := by
    rw [hc, hσ]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hD4 : (L.ω₂ * (starRingEnd ℂ) (v - c)).im = -(a * σ) := by
    rw [hc, hσ]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- assemble the imaginary part of the boundary integral
  intro h0
  have him : (L.boundaryIntegral (fun z ↦ (z - c)⁻¹) v).im = 0 := by rw [h0]; rfl
  rw [boundaryIntegral] at him
  simp only [Complex.sub_im, Complex.add_im] at him
  rw [edge_inv_im hne1, edge_inv_im hne2, edge_inv_im hne3, edge_inv_im hne4,
    hD1, hD2, hD3, hD4] at him
  set I₁ := ∫ t in (0 : ℝ)..1, (Complex.normSq (v + (t : ℂ) * L.ω₁ - c))⁻¹
  set I₂ := ∫ t in (0 : ℝ)..1, (Complex.normSq (v + L.ω₁ + (t : ℂ) * L.ω₂ - c))⁻¹
  set I₃ := ∫ t in (0 : ℝ)..1, (Complex.normSq (v + L.ω₂ + (t : ℂ) * L.ω₁ - c))⁻¹
  set I₄ := ∫ t in (0 : ℝ)..1, (Complex.normSq (v + (t : ℂ) * L.ω₂ - c))⁻¹
  have hI₁ : 0 < I₁ := hpos _ _ hne1
  have hI₂ : 0 < I₂ := hpos _ _ hne2
  have hI₃ : 0 < I₃ := hpos _ _ hne3
  have hI₄ : 0 < I₄ := hpos _ _ hne4
  have hS : b * I₁ + (1 - a) * I₂ + (1 - b) * I₃ + a * I₄ > 0 := by
    have := hb.1
    have := ha.2
    have := hb.2
    have := ha.1
    nlinarith [mul_pos hb.1 hI₁, mul_pos (sub_pos.mpr ha.2) hI₂,
      mul_pos (sub_pos.mpr hb.2) hI₃, mul_pos ha.1 hI₄]
  have him' : σ * (b * I₁ + (1 - a) * I₂ + (1 - b) * I₃ + a * I₄) = 0 := by
    linarith [him]
  rcases mul_eq_zero.mp him' with h | h
  · exact hσne h
  · linarith

/-- `starRingEnd ℂ` commutes with interval integrals. -/
private lemma intervalIntegral_conj {f : ℝ → ℂ} :
    ∫ t in (0 : ℝ)..1, (starRingEnd ℂ) (f t) = (starRingEnd ℂ) (∫ t in (0 : ℝ)..1, f t) := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  exact integral_conj

/-- A double interval integral of `I • G u 1 - G u I` reduces to a scalar multiple of the double
integral of `d`, whenever `G u 1 = c₁ · d u` and `G u I = c₂ · d u`. -/
private lemma double_integral_diff_apply {c₁ c₂ : ℂ} {G : ℂ → ℂ →L[ℝ] ℂ} {d : ℂ → ℂ}
    (h1 : ∀ u, G u 1 = c₁ * d u) (hI : ∀ u, G u Complex.I = c₂ * d u) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        Complex.I * G (↑x + ↑y * Complex.I) 1 - G (↑x + ↑y * Complex.I) Complex.I)
      = (Complex.I * c₁ - c₂) * ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, d (↑x + ↑y * Complex.I) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  change (∫ y in (0 : ℝ)..1, Complex.I * G (↑x + ↑y * Complex.I) 1
      - G (↑x + ↑y * Complex.I) Complex.I)
    = (Complex.I * c₁ - c₂) * ∫ y in (0 : ℝ)..1, d (↑x + ↑y * Complex.I)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  change Complex.I * G (↑x + ↑y * Complex.I) 1 - G (↑x + ↑y * Complex.I) Complex.I
    = (Complex.I * c₁ - c₂) * d (↑x + ↑y * Complex.I)
  rw [h1, hI]
  ring

/-- The conjugated version of `double_integral_diff_apply`: when the `∂/∂zbar`-term is a conjugated
scalar multiple of `d`, the double integral is a conjugated scalar multiple of `M`. -/
private lemma double_integral_conj_apply {ω₁ ω₂ : ℂ} {gc' : ℂ → ℂ →L[ℝ] ℂ} {d : ℂ → ℂ} {M : ℂ}
    (hM : M = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, d (↑x + ↑y * Complex.I))
    (hgc'1 : ∀ u, gc' u 1 = (starRingEnd ℂ) (ω₁ * d u))
    (hgc'I : ∀ u, gc' u Complex.I = (starRingEnd ℂ) (ω₂ * d u)) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        Complex.I * gc' (↑x + ↑y * Complex.I) 1 - gc' (↑x + ↑y * Complex.I) Complex.I)
      = (starRingEnd ℂ) ((-(Complex.I * ω₁) - ω₂) * M) := by
  have hstep : ∀ x : ℝ, (∫ y in (0 : ℝ)..1,
      Complex.I * gc' (↑x + ↑y * Complex.I) 1 - gc' (↑x + ↑y * Complex.I) Complex.I)
      = (starRingEnd ℂ) ((-(Complex.I * ω₁) - ω₂)
          * ∫ y in (0 : ℝ)..1, d (↑x + ↑y * Complex.I)) := by
    intro x
    have hpt : ∀ y : ℝ, Complex.I * gc' (↑x + ↑y * Complex.I) 1
        - gc' (↑x + ↑y * Complex.I) Complex.I
        = (starRingEnd ℂ) ((-(Complex.I * ω₁) - ω₂) * d (↑x + ↑y * Complex.I)) := by
      intro y
      rw [hgc'1, hgc'I]
      simp only [map_mul, map_sub, map_neg, Complex.conj_I]
      ring
    rw [intervalIntegral.integral_congr (g :=
        fun y : ℝ ↦ (starRingEnd ℂ) ((-(Complex.I * ω₁) - ω₂) * d (↑x + ↑y * Complex.I)))
        (fun y _ => hpt y),
      intervalIntegral_conj, intervalIntegral.integral_const_mul]
  calc (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        Complex.I * gc' (↑x + ↑y * Complex.I) 1 - gc' (↑x + ↑y * Complex.I) Complex.I)
      = ∫ x in (0 : ℝ)..1, (starRingEnd ℂ) ((-(Complex.I * ω₁) - ω₂)
          * ∫ y in (0 : ℝ)..1, d (↑x + ↑y * Complex.I)) :=
        intervalIntegral.integral_congr (fun x _ => hstep x)
    _ = (starRingEnd ℂ) (∫ x in (0 : ℝ)..1, (-(Complex.I * ω₁) - ω₂)
          * ∫ y in (0 : ℝ)..1, d (↑x + ↑y * Complex.I)) := intervalIntegral_conj
    _ = (starRingEnd ℂ) ((-(Complex.I * ω₁) - ω₂) * M) := by
        rw [intervalIntegral.integral_const_mul, hM]

/-- Integrability on the closed unit square of `I • G u 1 - G u I` under the same hypotheses. -/
private lemma integrableOn_diff_apply {c₁ c₂ : ℂ} {G : ℂ → ℂ →L[ℝ] ℂ} {d : ℂ → ℂ}
    (h1 : ∀ u, G u 1 = c₁ * d u) (hI : ∀ u, G u Complex.I = c₂ * d u)
    (hd : ContinuousOn d (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) 1)) :
    MeasureTheory.IntegrableOn (fun u ↦ Complex.I • G u 1 - G u Complex.I)
      (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) 1) := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) 1) := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    exact ⟨isClosed_Icc.reProdIm isClosed_Icc,
      (Metric.isBounded_Icc 0 1).reProdIm (Metric.isBounded_Icc 0 1)⟩
  have heq : (fun u ↦ Complex.I • G u 1 - G u Complex.I)
      = fun u ↦ (Complex.I * c₁ - c₂) * d u := by
    funext u
    rw [h1, hI, smul_eq_mul]
    ring
  rw [heq]
  exact (hd.const_smul (Complex.I * c₁ - c₂)).integrableOn_compact hcompact

/-- Pushing `starRingEnd ℂ` through an edge integral of `g` composed with a path `p`. -/
private lemma intervalIntegral_conj_comp {g gc : ℂ → ℂ}
    (hgc : ∀ z, gc z = (starRingEnd ℂ) (g z)) {p : ℝ → ℂ} {Q : ℂ}
    (h : (∫ x in (0 : ℝ)..1, g (p x)) = Q) :
    (∫ x in (0 : ℝ)..1, gc (p x)) = (starRingEnd ℂ) Q := by
  have hc : (∫ x in (0 : ℝ)..1, gc (p x)) = ∫ x in (0 : ℝ)..1, (starRingEnd ℂ) (g (p x)) :=
    intervalIntegral.integral_congr (fun x _ => hgc (p x))
  rw [hc, intervalIntegral_conj, h]

/-- **Cauchy's theorem for a parallelogram.** If `f` is holomorphic on an open set containing
the closed parallelogram, its boundary integral vanishes.

Mathlib only has the Cauchy–Goursat theorem for axis-parallel rectangles; we pull the
parallelogram back to the unit square along the real-affine map
`T u = v + u.re·ω₁ + u.im·ω₂` and apply Mathlib's *real* rectangle formula
(`Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`, which computes the boundary
integral as the area integral of the `∂/∂zbar`-term) to both `f ∘ T` and `conj ∘ f ∘ T`. Since
`T` is not holomorphic the individual `∂/∂zbar`-terms do not vanish, but both are constant complex
multiples of the single area integral `M = ∫∫ f'(T u)`, and the parallelogram boundary integral
is the linear combination of the two identities in which `M` cancels. -/
private lemma boundaryIntegral_eq_zero_of_differentiableOn {L : PeriodPair} {f : ℂ → ℂ} {v : ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hsub : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      v + (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂ ∈ U) :
    L.boundaryIntegral f v = 0 := by
  have hfa : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  have hd_cont : ContinuousOn (deriv f) U := hfa.deriv.continuousOn
  -- the affine pullback map and its (constant) real derivative
  set Tlin : ℂ →L[ℝ] ℂ := Complex.reCLM.smulRight L.ω₁ + Complex.imCLM.smulRight L.ω₂
    with hTlin
  have hTlin_apply : ∀ u : ℂ, Tlin u = (u.re : ℂ) * L.ω₁ + (u.im : ℂ) * L.ω₂ := by
    intro u
    simp [hTlin, Complex.real_smul]
  set T : ℂ → ℂ := fun u ↦ v + (u.re : ℂ) * L.ω₁ + (u.im : ℂ) * L.ω₂ with hT
  have hTcont : Continuous T := by fun_prop
  have hTFDeriv : ∀ u : ℂ, HasFDerivAt T Tlin u := by
    intro u
    have heq : T = fun u ↦ v + Tlin u := by
      funext w
      rw [hTlin_apply]
      simp [hT]
      ring
    rw [heq]
    exact Tlin.hasFDerivAt.const_add v
  set g : ℂ → ℂ := fun u ↦ f (T u) with hg
  set d : ℂ → ℂ := fun u ↦ deriv f (T u) with hd
  set g' : ℂ → ℂ →L[ℝ] ℂ :=
    fun u ↦ ((ContinuousLinearMap.toSpanSingleton ℂ (d u)).restrictScalars ℝ).comp Tlin with hg'
  have hg'1 : ∀ u : ℂ, g' u 1 = L.ω₁ * d u := by
    intro u
    simp [hg', hTlin_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  have hg'I : ∀ u : ℂ, g' u Complex.I = L.ω₂ * d u := by
    intro u
    simp [hg', hTlin_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  -- membership of the closed square image
  have hmemT : ∀ u : ℂ, u.re ∈ Set.Icc (0 : ℝ) 1 → u.im ∈ Set.Icc (0 : ℝ) 1 → T u ∈ U :=
    fun u h1 h2 => hsub u.re h1 u.im h2
  -- differentiability of the pullback
  have hgFDeriv : ∀ u : ℂ, u.re ∈ Set.Icc (0 : ℝ) 1 → u.im ∈ Set.Icc (0 : ℝ) 1 →
      HasFDerivAt g (g' u) u := by
    intro u h1 h2
    have hmem : T u ∈ U := hmemT u h1 h2
    have hdf : HasDerivAt f (d u) (T u) :=
      (hf.differentiableAt (hU.mem_nhds hmem)).hasDerivAt
    have hdF := (hdf.hasFDerivAt.restrictScalars ℝ).comp u (hTFDeriv u)
    have hcomp : (f ∘ T) = g := rfl
    rw [hcomp] at hdF
    exact hdF
  -- continuity of the pullback and of the area integrand
  have hgc : ∀ u : ℂ, u.re ∈ Set.Icc (0 : ℝ) 1 → u.im ∈ Set.Icc (0 : ℝ) 1 →
      ContinuousWithinAt g (Set.Icc (0:ℝ) 1 ×ℂ Set.Icc (0:ℝ) 1) u := by
    intro u h1 h2
    have : ContinuousAt f (T u) :=
      (hfa (T u) (hmemT u h1 h2)).continuousAt
    exact (this.comp hTcont.continuousAt).continuousWithinAt
  -- endpoints of the unit square as a "rectangle" in Mathlib's sense
  have hre0 : (0 : ℂ).re = 0 := rfl
  have him0 : (0 : ℂ).im = 0 := rfl
  have hre1 : (1 + Complex.I).re = 1 := by simp
  have him1 : (1 + Complex.I).im = 1 := by simp
  have hsq : Set.uIcc ((0 : ℂ).re) ((1 + Complex.I).re) ×ℂ
      Set.uIcc ((0 : ℂ).im) ((1 + Complex.I).im)
      = Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) 1 := by
    rw [hre0, him0, hre1, him1, Set.uIcc_of_le zero_le_one]
  have hIoo : Set.Ioo (min (0 : ℂ).re (1 + Complex.I).re) (max (0 : ℂ).re (1 + Complex.I).re) ×ℂ
      Set.Ioo (min (0 : ℂ).im (1 + Complex.I).im) (max (0 : ℂ).im (1 + Complex.I).im)
      = Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (0 : ℝ) 1 := by
    rw [hre0, him0, hre1, him1, min_eq_left zero_le_one, max_eq_right zero_le_one]
  -- hypotheses of the rectangle formula, for `g`
  have Hc₁ : ContinuousOn g (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) 1) := by
    intro u hu
    rw [Complex.mem_reProdIm] at hu
    exact hgc u hu.1 hu.2
  have Hd₁ : ∀ u ∈ (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (0 : ℝ) 1) \ (∅ : Set ℂ),
      HasFDerivAt g (g' u) u := by
    intro u hu
    rw [Set.sdiff_empty, Complex.mem_reProdIm] at hu
    exact hgFDeriv u (Set.mem_Icc_of_Ioo hu.1) (Set.mem_Icc_of_Ioo hu.2)
  have hd_contSq : ContinuousOn d (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) 1) := by
    intro u hu
    rw [Complex.mem_reProdIm] at hu
    exact ((hd_cont (T u) (hmemT u hu.1 hu.2)).continuousAt
      (hU.mem_nhds (hmemT u hu.1 hu.2))).comp hTcont.continuousAt |>.continuousWithinAt
  have Hi₁ : MeasureTheory.IntegrableOn (fun u ↦ Complex.I • g' u 1 - g' u Complex.I)
      (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) 1) :=
    integrableOn_diff_apply hg'1 hg'I hd_contSq
  -- hypotheses for the conjugated pullback
  set gc : ℂ → ℂ := fun u ↦ (starRingEnd ℂ) (g u) with hgcdef
  set gc' : ℂ → ℂ →L[ℝ] ℂ :=
    fun u ↦ (Complex.conjCLE.toContinuousLinearMap).comp (g' u) with hgc'
  have hgc'1 : ∀ u : ℂ, gc' u 1 = (starRingEnd ℂ) (L.ω₁ * d u) := by
    intro u
    simp [hgc', hg'1]
  have hgc'I : ∀ u : ℂ, gc' u Complex.I = (starRingEnd ℂ) (L.ω₂ * d u) := by
    intro u
    simp [hgc', hg'I]
  have Hc₂ : ContinuousOn gc (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) 1) :=
    Complex.continuous_conj.comp_continuousOn Hc₁
  have Hd₂ : ∀ u ∈ (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (0 : ℝ) 1) \ (∅ : Set ℂ),
      HasFDerivAt gc (gc' u) u := by
    intro u hu
    exact (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp u (Hd₁ u hu)
  have Hi₂ : MeasureTheory.IntegrableOn (fun u ↦ Complex.I • gc' u 1 - gc' u Complex.I)
      (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) 1) :=
    integrableOn_diff_apply (c₁ := (starRingEnd ℂ) L.ω₁) (c₂ := (starRingEnd ℂ) L.ω₂)
      (d := fun u ↦ (starRingEnd ℂ) (d u))
      (fun u => by rw [hgc'1]; exact map_mul _ _ _)
      (fun u => by rw [hgc'I]; exact map_mul _ _ _)
      (Complex.continuous_conj.comp_continuousOn hd_contSq)
  -- the two rectangle identities
  have Heq₁ := Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable g g'
    0 (1 + Complex.I) ∅ Set.countable_empty
    (by rw [hsq]; exact Hc₁) (by rw [hIoo]; exact Hd₁) (by rw [hsq]; exact Hi₁)
  have Heq₂ := Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable gc gc'
    0 (1 + Complex.I) ∅ Set.countable_empty
    (by rw [hsq]; exact Hc₂) (by rw [hIoo]; exact Hd₂) (by rw [hsq]; exact Hi₂)
  simp only [hre0, him0, hre1, him1, Complex.ofReal_zero, Complex.ofReal_one, zero_mul,
    one_mul, add_zero, zero_add, smul_eq_mul] at Heq₁ Heq₂
  -- convert the pullback edge integrals to parallelogram edge integrals
  set M : ℂ := ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, d (↑x + ↑y * Complex.I) with hM
  have hsimp : ∀ (x : ℝ) (w : ℂ), g (↑x + w) = f (v + (↑x + w.re) * L.ω₁ + ↑w.im * L.ω₂) := by
    intro x w
    simp [hg, hT]
  have hB : (∫ x in (0 : ℝ)..1, g ↑x) = ∫ t in (0 : ℝ)..1, f (v + ↑t * L.ω₁) := by
    apply intervalIntegral.integral_congr
    intro t _
    change g ↑t = f (v + ↑t * L.ω₁)
    simp [hg, hT]
  have hTop : (∫ x in (0 : ℝ)..1, g (↑x + Complex.I))
      = ∫ t in (0 : ℝ)..1, f (v + L.ω₂ + ↑t * L.ω₁) := by
    apply intervalIntegral.integral_congr
    intro t _
    change g (↑t + Complex.I) = f (v + L.ω₂ + ↑t * L.ω₁)
    simp [hg, hT]
    congr 1
    ring
  have hR : (∫ y in (0 : ℝ)..1, g (1 + ↑y * Complex.I))
      = ∫ t in (0 : ℝ)..1, f (v + L.ω₁ + ↑t * L.ω₂) := by
    apply intervalIntegral.integral_congr
    intro t _
    change g (1 + ↑t * Complex.I) = f (v + L.ω₁ + ↑t * L.ω₂)
    simp [hg, hT]
  have hL : (∫ y in (0 : ℝ)..1, g (↑y * Complex.I))
      = ∫ t in (0 : ℝ)..1, f (v + ↑t * L.ω₂) := by
    apply intervalIntegral.integral_congr
    intro t _
    change g (↑t * Complex.I) = f (v + ↑t * L.ω₂)
    simp [hg, hT]
  have hRHS₁ : (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      Complex.I * g' (↑x + ↑y * Complex.I) 1 - g' (↑x + ↑y * Complex.I) Complex.I)
      = (Complex.I * L.ω₁ - L.ω₂) * M := by
    rw [hM]; exact double_integral_diff_apply hg'1 hg'I
  have hRHS₂ : (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      Complex.I * gc' (↑x + ↑y * Complex.I) 1 - gc' (↑x + ↑y * Complex.I) Complex.I)
      = (starRingEnd ℂ) ((-(Complex.I * L.ω₁) - L.ω₂) * M) :=
    double_integral_conj_apply hM hgc'1 hgc'I
  -- conjugated edge conversions
  have hgcpt : ∀ z, gc z = (starRingEnd ℂ) (g z) := fun z => congrFun hgcdef z
  have hBc : (∫ x in (0 : ℝ)..1, gc ↑x)
      = (starRingEnd ℂ) (∫ t in (0 : ℝ)..1, f (v + ↑t * L.ω₁)) :=
    intervalIntegral_conj_comp hgcpt hB
  have hTopc : (∫ x in (0 : ℝ)..1, gc (↑x + Complex.I))
      = (starRingEnd ℂ) (∫ t in (0 : ℝ)..1, f (v + L.ω₂ + ↑t * L.ω₁)) :=
    intervalIntegral_conj_comp hgcpt hTop
  have hRc : (∫ y in (0 : ℝ)..1, gc (1 + ↑y * Complex.I))
      = (starRingEnd ℂ) (∫ t in (0 : ℝ)..1, f (v + L.ω₁ + ↑t * L.ω₂)) :=
    intervalIntegral_conj_comp hgcpt hR
  have hLc : (∫ y in (0 : ℝ)..1, gc (↑y * Complex.I))
      = (starRingEnd ℂ) (∫ t in (0 : ℝ)..1, f (v + ↑t * L.ω₂)) :=
    intervalIntegral_conj_comp hgcpt hL
  rw [hB, hTop, hR, hL, hRHS₁] at Heq₁
  rw [hBc, hTopc, hRc, hLc, hRHS₂] at Heq₂
  have Heq₂' := congrArg (starRingEnd ℂ) Heq₂
  simp only [map_sub, map_add, map_mul, Complex.conj_conj, Complex.conj_I] at Heq₂'
  -- assemble the boundary integral and eliminate the area term
  rw [boundaryIntegral, intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  linear_combination ((L.ω₁ - Complex.I * L.ω₂) / 2) * Heq₁
    + ((L.ω₁ + Complex.I * L.ω₂) / 2) * Heq₂'
    + ((∫ t in (0 : ℝ)..1, f (v + L.ω₁ + ↑t * L.ω₂)) * L.ω₂
        - (∫ t in (0 : ℝ)..1, f (v + ↑t * L.ω₂)) * L.ω₂
        - L.ω₁ * L.ω₂ * M) * Complex.I_mul_I

/-- `dslope` of a function analytic at a point is analytic there. -/
private lemma analyticAt_dslope_self {g : ℂ → ℂ} {c : ℂ} (hg : AnalyticAt ℂ g c) :
    AnalyticAt ℂ (dslope g c) c := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- Finite Taylor expansion with analytic remainder, in principal-part form: for `g` analytic
at `c`, the function `(z - c)^(-N) · g z` is a sum of finitely many negative powers of `z - c`
and a function analytic at `c` — *exactly*, for every `z ≠ c`. -/
private lemma exists_principalPart (N : ℕ) (g : ℂ → ℂ) (c : ℂ) (hg : AnalyticAt ℂ g c) :
    ∃ (A : ℕ → ℂ) (h : ℂ → ℂ), AnalyticAt ℂ h c ∧ ∀ z, z ≠ c →
      (z - c) ^ (-(N : ℤ)) * g z
        = (∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 1 : ℤ))) + h z := by
  induction N generalizing g with
  | zero =>
    exact ⟨fun _ => 0, g, hg, fun z hz => by simp⟩
  | succ N ih =>
    obtain ⟨A, h, hh, hEq⟩ := ih (dslope g c) (analyticAt_dslope_self hg)
    refine ⟨fun k => if k = N then g c else A k, h, hh, fun z hz => ?_⟩
    have hzc : z - c ≠ 0 := sub_ne_zero.2 hz
    have hsplit : g z = g c + (z - c) * dslope g c z := by
      have hds := sub_smul_dslope g c z
      rw [smul_eq_mul] at hds
      linear_combination -hds
    have hpow : (z - c) ^ (-(N + 1 : ℕ) : ℤ) * (z - c) = (z - c) ^ (-(N : ℤ)) := by
      rw [show (-(N : ℤ)) = (-((N + 1 : ℕ) : ℤ)) + 1 from by push_cast; ring,
        zpow_add_one₀ hzc]
    have hsum : ∑ k ∈ Finset.range (N + 1),
        (if k = N then g c else A k) * (z - c) ^ (-(k + 1 : ℤ))
        = (∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 1 : ℤ)))
          + g c * (z - c) ^ (-(N + 1 : ℕ) : ℤ) := by
      rw [Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        rw [if_neg (Finset.mem_range.mp hk).ne]
      · rw [if_pos rfl]
        norm_cast
    calc (z - c) ^ (-(N + 1 : ℕ) : ℤ) * g z
        = g c * (z - c) ^ (-(N + 1 : ℕ) : ℤ)
          + ((z - c) ^ (-(N + 1 : ℕ) : ℤ) * (z - c)) * dslope g c z := by
          rw [hsplit]; ring
      _ = g c * (z - c) ^ (-(N + 1 : ℕ) : ℤ) + (z - c) ^ (-(N : ℤ)) * dslope g c z := by
          rw [hpow]
      _ = g c * (z - c) ^ (-(N + 1 : ℕ) : ℤ)
          + ((∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 1 : ℤ))) + h z) := by
          rw [hEq z hz]
      _ = (∑ k ∈ Finset.range (N + 1),
            (if k = N then g c else A k) * (z - c) ^ (-(k + 1 : ℤ))) + h z := by
          rw [hsum]; ring

/-- **Local decomposition of a meromorphic function** at a point `c`: a simple-pole part
`a·(z-c)⁻¹` (whose coefficient is the residue), a higher principal part, and an analytic
remainder, valid on a punctured neighbourhood of `c`. -/
private lemma exists_decomposition {f : ℂ → ℂ} {c : ℂ} (hf : MeromorphicAt f c) :
    ∃ (a : ℂ) (N : ℕ) (A : ℕ → ℂ) (h : ℂ → ℂ), AnalyticAt ℂ h c ∧
      ∀ᶠ z in nhdsWithin c {c}ᶜ, f z = a * (z - c)⁻¹
        + (∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 2 : ℤ))) + h z := by
  by_cases hord : meromorphicOrderAt f c = ⊤
  · refine ⟨0, 0, fun _ => 0, fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp hord] with z hz
    simp [hz]
  · obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).1 hord
    set n : ℤ := (meromorphicOrderAt f c).untop₀ with hn
    by_cases hn0 : 0 ≤ n
    · -- nonnegative order: no principal part
      refine ⟨0, 0, fun _ => 0, fun z => (z - c) ^ n.toNat * g z,
        ((analyticAt_id.sub analyticAt_const).pow _).mul hg_an, ?_⟩
      filter_upwards [hg_eq] with z hz
      rw [hz, smul_eq_mul]
      simp only [Finset.sum_empty, Finset.range_zero, zero_mul, zero_add]
      rw [← zpow_natCast (z - c) n.toNat, Int.toNat_of_nonneg hn0]
    · -- negative order `n = -(N+1)`
      push Not at hn0
      have hN₁pos : 0 < (-n).toNat := by
        have : (0 : ℤ) < ((-n).toNat : ℤ) := by
          rw [Int.toNat_of_nonneg (by linarith)]
          linarith
        exact_mod_cast this
      obtain ⟨N, hNN⟩ : ∃ N, (-n).toNat = N + 1 :=
        ⟨(-n).toNat - 1, (Nat.succ_pred_eq_of_pos hN₁pos).symm⟩
      have hN₁n : ((N + 1 : ℕ) : ℤ) = -n := by
        rw [← hNN]
        exact Int.toNat_of_nonneg (by linarith)
      obtain ⟨A, h, hh, hEq⟩ := exists_principalPart (N + 1) g c hg_an
      refine ⟨A 0, N, fun k => A (k + 1), h, hh, ?_⟩
      filter_upwards [hg_eq, self_mem_nhdsWithin] with z hz hzne
      have hzc : z ≠ c := by simpa using hzne
      rw [hz, smul_eq_mul,
        show n = -(((N + 1 : ℕ) : ℤ)) from by linarith [hN₁n], hEq z hzc,
        Finset.sum_range_succ']
      have hre : ∀ k ∈ Finset.range N,
          A (k + 1) * (z - c) ^ (-(((k + 1 : ℕ) : ℤ) + 1))
          = A (k + 1) * (z - c) ^ (-((k : ℤ) + 2)) := by
        intro k _
        congr 1
      rw [Finset.sum_congr rfl hre]
      push_cast
      ring_nf
      rw [show (-1 : ℤ) = -(0 + 1) from by ring, ← zpow_neg_one (z - c)]
      ring_nf

/-- The residue of a decomposition `a·(z-c)⁻¹ + higher principal part + analytic` is `a`. -/
private lemma residue_decomposition {c a : ℂ} {N : ℕ} {A : ℕ → ℂ} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h c) :
    Chudnovsky.residue (fun z ↦ a * (z - c)⁻¹
      + (∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 2 : ℤ))) + h z) c = a := by
  apply Chudnovsky.residue_eq_of_eventuallyEq
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hh.eventually_analyticAt
  have hlt : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), r < ε :=
    (show ∀ᶠ r in nhds (0 : ℝ), r < ε from Iio_mem_nhds hε).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with r hr hrε
  have hr0 : (0 : ℝ) < r := hr
  have hcnot : c ∉ Metric.sphere c |r| := by
    intro hmem
    rw [Metric.mem_sphere, dist_self] at hmem
    rw [abs_of_pos hr0] at hmem
    exact hr0.ne' hmem.symm
  have hint1 : CircleIntegrable (fun z ↦ a * (z - c)⁻¹) c r := by
    refine ContinuousOn.circleIntegrable hr0.le (continuousOn_const.mul ?_)
    refine (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => ?_)
    rw [Metric.mem_sphere] at hz
    simp only [id_eq]
    refine sub_ne_zero.2 (fun hzz => ?_)
    rw [hzz, dist_self] at hz
    exact hr0.ne' hz.symm
  have hint2 : CircleIntegrable
      (fun z ↦ ∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 2 : ℤ))) c r := by
    apply CircleIntegrable.fun_sum
    intro k _
    have hzpow : CircleIntegrable (fun z ↦ (z - c) ^ (-(k + 2 : ℤ))) c r := by
      rw [circleIntegrable_sub_zpow_iff]
      exact Or.inr (Or.inr hcnot)
    exact hzpow.const_smul (a := A k)
  have hint3 : CircleIntegrable h c r := by
    refine ContinuousOn.circleIntegrable hr0.le (fun z hz => ?_)
    rw [Metric.mem_sphere] at hz
    exact (hball (hz.trans_lt hrε)).continuousAt.continuousWithinAt
  have hint12 : CircleIntegrable (fun z ↦ a * (z - c)⁻¹
      + ∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 2 : ℤ))) c r := hint1.add hint2
  have hsplit1 : (∮ z in C(c, r), (a * (z - c)⁻¹
        + ∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 2 : ℤ))) + h z)
      = (∮ z in C(c, r), a * (z - c)⁻¹
        + ∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 2 : ℤ))) + ∮ z in C(c, r), h z :=
    circleIntegral.integral_add hint12 hint3
  have hsplit2 : (∮ z in C(c, r), a * (z - c)⁻¹
        + ∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 2 : ℤ)))
      = (∮ z in C(c, r), a * (z - c)⁻¹)
        + ∮ z in C(c, r), ∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 2 : ℤ)) :=
    circleIntegral.integral_add hint1 hint2
  rw [hsplit1, hsplit2, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_center_inv c hr0.ne']
  have htail : (∮ z in C(c, r), ∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 2 : ℤ))) = 0 := by
    rw [circleIntegral.integral_fun_sum]
    · apply Finset.sum_eq_zero
      intro k _
      rw [circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_zpow_of_ne (by omega : (-(k + 2 : ℤ)) ≠ -1), mul_zero]
    · intro k _
      have hzpow : CircleIntegrable (fun z ↦ (z - c) ^ (-(k + 2 : ℤ))) c r := by
        rw [circleIntegrable_sub_zpow_iff]
        exact Or.inr (Or.inr hcnot)
      exact hzpow.const_smul (a := A k)
  have hzero : (∮ z in C(c, r), h z) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr0.le
      Set.countable_empty
    · exact fun z hz =>
        (hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hrε)).continuousAt.continuousWithinAt
    · exact fun z hz =>
        (hball (lt_of_lt_of_le (Metric.mem_ball.mp hz.1) hrε.le)).differentiableAt
  rw [htail, hzero, add_zero, add_zero, mul_comm a, ← mul_assoc,
    inv_mul_cancel₀ Chudnovsky.two_pi_I_ne_zero, one_mul]

/-- Away from `c`, an integer power `(w - c) ^ n` is analytic. -/
private lemma analyticAt_sub_zpow (c : ℂ) (n : ℤ) {z : ℂ} (hzc : z ≠ c) :
    AnalyticAt ℂ (fun w ↦ (w - c) ^ n) z := by
  have hd : DifferentiableOn ℂ (fun w ↦ (w - c) ^ n) {c}ᶜ := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    have hbase : DifferentiableAt ℂ (fun w : ℂ ↦ w - c) w := by fun_prop
    exact hbase.zpow (Or.inl (sub_ne_zero.2 (by simpa using hw)))
  exact hd.analyticOnNhd isOpen_compl_singleton z (by simpa using hzc)

/-- Away from `c`, the simple pole `(w - c)⁻¹` is analytic. -/
private lemma analyticAt_sub_inv (c : ℂ) {z : ℂ} (hzc : z ≠ c) :
    AnalyticAt ℂ (fun w ↦ (w - c)⁻¹) z := by
  have hd : DifferentiableOn ℂ (fun w ↦ (w - c)⁻¹) {c}ᶜ := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    have hbase : DifferentiableAt ℂ (fun w : ℂ ↦ w - c) w := by fun_prop
    exact hbase.inv (sub_ne_zero.2 (by simpa using hw))
  exact hd.analyticOnNhd isOpen_compl_singleton z (by simpa using hzc)

/-- The boundary integral of a principal part `a·(z-c)⁻¹ + higher-order terms` reduces to
`a` times the boundary integral of the simple pole: the higher-order (order `≤ -2`) terms
integrate to zero over the closed parallelogram contour. -/
private lemma boundaryIntegral_principalPart {L : PeriodPair} {v c : ℂ} (a : ℂ) (N : ℕ)
    (A : ℕ → ℂ) (hbne : ∀ z ∈ L.boundarySet v, z ≠ c) (hcnotb : c ∉ L.boundarySet v) :
    L.boundaryIntegral (fun z ↦ a * (z - c)⁻¹
        + ∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 2 : ℤ))) v
      = a * L.boundaryIntegral (fun z ↦ (z - c)⁻¹) v := by
  have hcinv : ContinuousOn (fun z ↦ (z - c)⁻¹) (L.boundarySet v) := by
    refine (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => ?_)
    simp only [id_eq]
    exact sub_ne_zero.2 (hbne z hz)
  have hcont1 : ContinuousOn (fun z ↦ a * (z - c)⁻¹) (L.boundarySet v) :=
    continuousOn_const.mul hcinv
  have hcont2 : ContinuousOn
      (fun z ↦ ∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 2 : ℤ)))
      (L.boundarySet v) := by
    intro z hz
    have han : AnalyticAt ℂ
        (fun w ↦ ∑ k ∈ Finset.range N, A k * (w - c) ^ (-(k + 2 : ℤ))) z := by
      apply Finset.analyticAt_fun_sum
      intro k _
      exact analyticAt_const.mul (analyticAt_sub_zpow c _ (hbne z hz))
    exact han.continuousAt.continuousWithinAt
  rw [boundaryIntegral_add hcont1 hcont2, boundaryIntegral_const_mul]
  have htail0 : L.boundaryIntegral
      (fun z ↦ ∑ k ∈ Finset.range N, A k * (z - c) ^ (-(k + 2 : ℤ))) v = 0 := by
    have hterm : ∀ k ∈ Finset.range N, ContinuousOn
        (fun z ↦ A k * (z - c) ^ (-(k + 2 : ℤ))) (L.boundarySet v) := by
      intro k _
      apply continuousOn_const.mul
      refine (continuousOn_id.sub continuousOn_const).zpow₀ _ (fun z hz => ?_)
      exact Or.inl (by simpa using sub_ne_zero.2 (hbne z hz))
    rw [boundaryIntegral_finsetSum hterm]
    apply Finset.sum_eq_zero
    intro k _
    rw [boundaryIntegral_const_mul,
      boundaryIntegral_zpow_eq_zero (by omega : (-(k + 2 : ℤ)) ≠ -1) hcnotb, mul_zero]
  rw [htail0, add_zero]

/-- **Residue theorem for the parallelogram contour**: if `f` is meromorphic, its boundary
integral over the parallelogram based at `v` vanishes, all non-analyticity points of the closed
parallelogram lie in the finite set `S'`, and every point of `S'` is interior (coordinates in
`(0,1)`), then the residues of `f` over `S'` sum to zero. Proved by subtracting the principal
parts (`exists_decomposition`), applying Cauchy's theorem for the parallelogram
(`boundaryIntegral_eq_zero_of_differentiableOn`) to the remainder, and evaluating the principal
parts via the winding factor (`boundaryIntegral_sub_inv_congr` / `_ne_zero`). -/
private lemma sum_residue_eq_zero_of_boundaryIntegral_eq_zero {L : PeriodPair} {f : ℂ → ℂ}
    {v : ℂ} {S' : Finset ℂ} (hfm : Meromorphic f)
    (hzero : L.boundaryIntegral f v = 0)
    (hS' : ∀ c ∈ S', ∃ a b : ℝ, a ∈ Set.Ioo (0 : ℝ) 1 ∧ b ∈ Set.Ioo (0 : ℝ) 1 ∧
      c = v + (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂)
    (hcover : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ¬AnalyticAt ℂ f (v + (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂)
        → v + (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂ ∈ S') :
    ∑ c ∈ S', Chudnovsky.residue f c = 0 := by
  classical
  -- boundary points differ from every point of `S'`
  have hbne : ∀ c ∈ S', ∀ z ∈ L.boundarySet v, z ≠ c := by
    intro c hc z hz
    obtain ⟨α, β, hα, hβ, hcoords⟩ := hS' c hc
    have hseg := notMem_segment_of_mem_boundarySet hα hβ hα hβ hcoords hcoords z hz
    rw [segment_same] at hseg
    simpa using hseg
  have hcnotb : ∀ c ∈ S', c ∉ L.boundarySet v := fun c hc hmem => (hbne c hc c hmem) rfl
  -- decompositions at every point
  choose a N A h hana heq using fun z : ℂ => exists_decomposition (hfm z)
  have hres : ∀ z, Chudnovsky.residue f z = a z := by
    intro z
    rw [Chudnovsky.residue_congr (heq z), residue_decomposition (hana z)]
  -- principal parts
  set P : ℂ → ℂ → ℂ := fun c z => a c * (z - c)⁻¹
    + ∑ k ∈ Finset.range (N c), A c k * (z - c) ^ (-(k + 2 : ℤ)) with hP
  have htail_an : ∀ c z : ℂ, z ≠ c →
      AnalyticAt ℂ (fun w ↦ ∑ k ∈ Finset.range (N c), A c k * (w - c) ^ (-(k + 2 : ℤ))) z := by
    intro c z hzc
    apply Finset.analyticAt_fun_sum
    intro k _
    exact analyticAt_const.mul (analyticAt_sub_zpow c _ hzc)
  have hPanalytic : ∀ c z : ℂ, z ≠ c → AnalyticAt ℂ (P c) z := by
    intro c z hzc
    apply AnalyticAt.add
    · exact analyticAt_const.mul (analyticAt_sub_inv c hzc)
    · exact htail_an c z hzc
  -- the corrected remainder function, patched at the singularities
  set G' : ℂ → ℂ := fun z => if z ∈ S' then h z z - ∑ c ∈ S'.erase z, P c z
    else f z - ∑ c ∈ S', P c z with hG'
  -- analyticity of `G'` away from `S'` (where `f` is analytic)
  have hG'an₁ : ∀ z, z ∉ S' → AnalyticAt ℂ f z → AnalyticAt ℂ G' z := by
    intro z hzS hfz
    have hs_an : AnalyticAt ℂ (fun w ↦ ∑ c ∈ S', P c w) z := by
      apply Finset.analyticAt_fun_sum
      intro c hc
      exact hPanalytic c z (fun hzc => hzS (hzc ▸ hc))
    apply (hfz.sub hs_an).congr
    have hev : ∀ᶠ w in nhds z, w ∉ S' :=
      (S'.finite_toSet.isClosed.isOpen_compl).mem_nhds (by simpa using hzS)
    filter_upwards [hev] with w hw
    simp only [hG', if_neg hw, Pi.sub_apply]
  -- analyticity of `G'` at the points of `S'`
  have hG'an₂ : ∀ z ∈ S', AnalyticAt ℂ G' z := by
    intro z hzS
    have hφ : AnalyticAt ℂ (fun w ↦ h z w - ∑ c ∈ S'.erase z, P c w) z := by
      apply (hana z).sub
      apply Finset.analyticAt_fun_sum
      intro c hc
      exact hPanalytic c z (Finset.ne_of_mem_erase hc).symm
    apply hφ.congr
    have key : ∀ᶠ w in nhdsWithin z {z}ᶜ,
        (fun w ↦ h z w - ∑ c ∈ S'.erase z, P c w) w = G' w := by
      have hev2 : ∀ᶠ w in nhdsWithin z {z}ᶜ, w ∉ S' := by
        have hopen : IsOpen ((↑(S'.erase z) : Set ℂ)ᶜ) :=
          (S'.erase z).finite_toSet.isClosed.isOpen_compl
        have hzmem : z ∈ ((↑(S'.erase z) : Set ℂ)ᶜ) := by simp
        have h1 : ∀ᶠ w in nhds z, w ∈ ((↑(S'.erase z) : Set ℂ)ᶜ) :=
          hopen.eventually_mem hzmem
        have h2 : ∀ᶠ w in nhdsWithin z {z}ᶜ, w ∈ ((↑(S'.erase z) : Set ℂ)ᶜ) :=
          h1.filter_mono nhdsWithin_le_nhds
        filter_upwards [h2, self_mem_nhdsWithin] with w hw1 hw2
        intro hwS
        refine hw1 ?_
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw2
        simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
        exact ⟨hwS, hw2⟩
      filter_upwards [heq z, hev2] with w hw1 hw2
      simp only [hG', if_neg hw2]
      have hsum : ∑ c ∈ S', P c w = P z w + ∑ c ∈ S'.erase z, P c w :=
        (Finset.add_sum_erase S' (fun c => P c w) hzS).symm
      have hfw : f w = P z w + h z w := by
        rw [hw1]
      rw [hsum, hfw]
      ring
    change (fun w ↦ h z w - ∑ c ∈ S'.erase z, P c w) =ᶠ[nhds z] G'
    rw [Filter.EventuallyEq, ← nhdsNE_sup_pure z, Filter.eventually_sup]
    refine ⟨key, ?_⟩
    rw [Filter.eventually_pure]
    simp only [hG', if_pos hzS]
  -- Cauchy for the corrected remainder
  have hEzero : L.boundaryIntegral G' v = 0 := by
    apply boundaryIntegral_eq_zero_of_differentiableOn (U := {z | AnalyticAt ℂ G' z})
      (isOpen_analyticAt ℂ G') (fun z hz => hz.differentiableAt.differentiableWithinAt)
    intro s hs t ht
    by_cases hzS : v + (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂ ∈ S'
    · exact hG'an₂ _ hzS
    · by_cases hfz : AnalyticAt ℂ f (v + (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂)
      · exact hG'an₁ _ hzS hfz
      · exact absurd (hcover s hs t ht hfz) hzS
  -- boundary membership gives closed-parallelogram coordinates
  have hbdy_coords : ∀ z ∈ L.boundarySet v, ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ Set.Icc (0 : ℝ) 1,
      z = v + (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂ := by
    rintro z (((⟨τ, hτ, rfl⟩ | ⟨τ, hτ, rfl⟩) | ⟨τ, hτ, rfl⟩) | ⟨τ, hτ, rfl⟩)
    · exact ⟨τ, hτ, 0, ⟨le_refl 0, zero_le_one⟩, by push_cast; ring⟩
    · exact ⟨1, ⟨zero_le_one, le_refl 1⟩, τ, hτ, by push_cast; ring⟩
    · exact ⟨τ, hτ, 1, ⟨zero_le_one, le_refl 1⟩, by push_cast; ring⟩
    · exact ⟨0, ⟨le_refl 0, zero_le_one⟩, τ, hτ, by push_cast; ring⟩
  -- `f` is analytic on the boundary, and `G'` agrees there with `f - Σ P`
  have hfan_bdy : ∀ z ∈ L.boundarySet v, AnalyticAt ℂ f z := by
    intro z hz
    by_contra hcon
    obtain ⟨s, hs, t, ht, rfl⟩ := hbdy_coords z hz
    have hmem := hcover s hs t ht hcon
    exact (hbne _ hmem _ hz) rfl
  have hbnotS : ∀ z ∈ L.boundarySet v, z ∉ S' := fun z hz hmem => (hbne z hmem z hz) rfl
  -- continuity of the pieces on the boundary
  have hPcont : ∀ c ∈ S', ContinuousOn (P c) (L.boundarySet v) := by
    intro c hc z hz
    exact ((hPanalytic c z (hbne c hc z hz)).continuousAt).continuousWithinAt
  have hSumCont : ContinuousOn (fun z ↦ ∑ c ∈ S', P c z) (L.boundarySet v) := by
    apply continuousOn_finsetSum
    intro c hc
    exact hPcont c hc
  have hG'cont : ContinuousOn G' (L.boundarySet v) := by
    intro z hz
    exact ((hG'an₁ z (hbnotS z hz) (hfan_bdy z hz)).continuousAt).continuousWithinAt
  -- splitting the boundary integral of `f`
  have hsplitf : L.boundaryIntegral f v
      = (∑ c ∈ S', L.boundaryIntegral (P c) v) + L.boundaryIntegral G' v := by
    have hcongr : L.boundaryIntegral f v
        = L.boundaryIntegral (fun z ↦ (∑ c ∈ S', P c z) + G' z) v := by
      apply boundaryIntegral_congr
      intro z hz
      simp only [hG', if_neg (hbnotS z hz)]
      ring
    rw [hcongr, boundaryIntegral_add hSumCont hG'cont, boundaryIntegral_finsetSum hPcont]
  -- each principal part integrates to `a c` times the winding factor
  have hPint : ∀ c ∈ S', L.boundaryIntegral (P c) v
      = a c * L.boundaryIntegral (fun z ↦ (z - c)⁻¹) v := by
    intro c hc
    have hPeq : L.boundaryIntegral (P c) v
        = L.boundaryIntegral (fun z ↦ a c * (z - c)⁻¹
            + ∑ k ∈ Finset.range (N c), A c k * (z - c) ^ (-(k + 2 : ℤ))) v := by
      apply boundaryIntegral_congr
      intro z _
      simp only [hP]
    rw [hPeq]
    exact boundaryIntegral_principalPart (a c) (N c) (A c)
      (fun z hz => hbne c hc z hz) (hcnotb c hc)
  -- conclude, using constancy and nonvanishing of the winding factor
  rcases S'.eq_empty_or_nonempty with rfl | ⟨c₀, hc₀⟩
  · simp
  · obtain ⟨α₀, β₀, hα₀, hβ₀, hc₀coords⟩ := hS' c₀ hc₀
    set κ : ℂ := L.boundaryIntegral (fun z ↦ (z - c₀)⁻¹) v with hκ
    have hκne : κ ≠ 0 := boundaryIntegral_sub_inv_ne_zero hα₀ hβ₀ hc₀coords
    have hWconst : ∀ c ∈ S', L.boundaryIntegral (fun z ↦ (z - c)⁻¹) v = κ := by
      intro c hc
      obtain ⟨α, β, hα, hβ, hcoords⟩ := hS' c hc
      exact boundaryIntegral_sub_inv_congr
        (notMem_segment_of_mem_boundarySet hα hβ hα₀ hβ₀ hcoords hc₀coords)
    have hmain : (∑ c ∈ S', a c) * κ = 0 := by
      have h1 : L.boundaryIntegral f v = (∑ c ∈ S', a c * κ) := by
        rw [hsplitf, hEzero, add_zero]
        apply Finset.sum_congr rfl
        intro c hc
        rw [hPint c hc, hWconst c hc]
      rw [Finset.sum_mul, ← h1, hzero]
    have hsum0 : ∑ c ∈ S', a c = 0 := by
      rcases mul_eq_zero.mp hmain with hgood | hbad
      · exact hgood
      · exact absurd hbad hκne
    calc ∑ c ∈ S', Chudnovsky.residue f c = ∑ c ∈ S', a c :=
          Finset.sum_congr rfl (fun c _ => hres c)
      _ = 0 := hsum0

/-- Integer-forcing helper for the choice of base point: if `x ∈ [0,1)`, `ε ∈ (0,1)` avoids the
"bad" value `1 - x`, and `x + ε + k ∈ [0,1]` for an integer `k`, then `k` is determined
(`0` or `-1` according to whether `x + ε < 1`) and the shifted coordinate is *interior*. -/
private lemma int_offset_forced {x ε : ℝ} {k : ℤ} (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hbad : 1 - x ≠ ε)
    (hk : x + ε + k ∈ Set.Icc (0 : ℝ) 1) :
    k = (if x + ε < 1 then 0 else -1) ∧ x + ε + k ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hε0, hε1⟩ := hε
  obtain ⟨hk0, hk1⟩ := hk
  have hne1 : x + ε ≠ 1 := fun hcon => hbad (by linarith)
  have hkub : (k : ℝ) < 1 := by linarith
  have hklb : (-2 : ℝ) < (k : ℝ) := by linarith
  have hkub' : k ≤ 0 := by
    have : k < 1 := by exact_mod_cast hkub
    omega
  have hklb' : (-1 : ℤ) ≤ k := by
    have : (-2 : ℤ) < k := by exact_mod_cast hklb
    omega
  by_cases hcase : x + ε < 1
  · rw [if_pos hcase]
    have hk0' : k = 0 := by
      rcases (by omega : k = -1 ∨ k = 0) with rfl | rfl
      · exfalso
        push_cast at hk0
        linarith
      · rfl
    subst hk0'
    push_cast
    exact ⟨trivial, by linarith, by linarith⟩
  · rw [if_neg hcase]
    rw [not_lt] at hcase
    have hgt : 1 < x + ε := lt_of_le_of_ne hcase (Ne.symm hne1)
    have hkm1 : k = -1 := by
      rcases (by omega : k = -1 ∨ k = 0) with rfl | rfl
      · rfl
      · exfalso
        push_cast at hk1
        linarith
    subst hkm1
    push_cast
    exact ⟨trivial, by linarith, by linarith⟩

/-- The interior-membership half of `int_offset_forced`, stated directly in terms of the
canonical integer offset `if x + ε < 1 then 0 else -1`. -/
private lemma shifted_coord_mem_Ioo {x ε : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hbad : 1 - x ≠ ε) :
    x + ε + ((if x + ε < 1 then (0 : ℤ) else -1 : ℤ) : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
  by_cases hcase : x + ε < 1
  · simp only [if_pos hcase]
    push_cast
    constructor
    · have h1 := hx.1
      have h2 := hε.1
      linarith
    · linarith
  · simp only [if_neg hcase]
    rw [not_lt] at hcase
    have hne1 : x + ε ≠ 1 := fun hcon => hbad (by linarith)
    have hgt : 1 < x + ε := lt_of_le_of_ne hcase (Ne.symm hne1)
    push_cast
    constructor
    · linarith
    · have h1 := hx.2
      have h2 := hε.2
      linarith

/-- Two `[0,1)`-coordinates that differ by an integer must coincide, and the integers agree. -/
private lemma int_coord_unique {a a' : ℝ} {j j' : ℤ} (ha : a ∈ Set.Ico (0 : ℝ) 1)
    (ha' : a' ∈ Set.Ico (0 : ℝ) 1) (h : a + (j : ℝ) - (a' + (j' : ℝ)) = 0) :
    j = j' ∧ a = a' := by
  have hint : ((j - j' : ℤ) : ℝ) = a' - a := by push_cast; linarith
  have hb1 : (-1 : ℝ) < ((j - j' : ℤ) : ℝ) := by
    rw [hint]
    have := ha.2
    have := ha'.1
    linarith
  have hb2 : ((j - j' : ℤ) : ℝ) < 1 := by
    rw [hint]
    have := ha.1
    have := ha'.2
    linarith
  have hz0 : j - j' = 0 := by
    have hlb : (-1 : ℤ) < j - j' := by exact_mod_cast hb1
    have hub : j - j' < 1 := by exact_mod_cast hb2
    omega
  have haeq : a = a' := by
    have h0 : ((0 : ℤ) : ℝ) = a' - a := by rw [← hz0]; exact hint
    push_cast at h0
    linarith
  exact ⟨by omega, haeq⟩

/-- **Second Liouville theorem** (paper `liouville2`): the residues of an elliptic
function over a fundamental parallelogram sum to `0`.

The paper sums over the poles of `f` in a *shifted* parallelogram `𝒫 + v`; since every point
of `ℂ` is equivalent mod `L` to exactly one point of `𝒫` and residues of an elliptic function
are invariant under lattice translation (`Chudnovsky.residue_add_of_periodic`), summing over
the singular points inside `𝒫` itself is an equivalent formulation. The proof chooses a base
point `v' = -ε₁ω₁ - ε₂ω₂` so that every singularity class has a unique representative strictly
inside the shifted parallelogram, then applies the parallelogram residue theorem
(`sum_residue_eq_zero_of_boundaryIntegral_eq_zero`) together with the vanishing of the
boundary integral by double periodicity (`boundaryIntegral_eq_zero`). -/
theorem IsEllipticWith.sum_residue_eq_zero (hf : L.IsEllipticWith f) :
    ∑ z ∈ hf.finite_nonAnalytic.toFinset, Chudnovsky.residue f z = 0 := by
  classical
  set S₀ : Finset ℂ := hf.finite_nonAnalytic.toFinset with hS₀
  have hS₀mem : ∀ c, c ∈ S₀ ↔ c ∈ L.fundamentalParallelogram ∧ ¬AnalyticAt ℂ f c := by
    intro c
    rw [hS₀, Set.Finite.mem_toFinset]
    exact Iff.rfl
  -- coordinates of fundamental-parallelogram points
  have hcoords : ∀ c : ℂ, ∃ s t : ℝ, c ∈ L.fundamentalParallelogram →
      s ∈ Set.Ico (0 : ℝ) 1 ∧ t ∈ Set.Ico (0 : ℝ) 1
        ∧ c = (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂ := by
    intro c
    by_cases hc : c ∈ L.fundamentalParallelogram
    · obtain ⟨s, hs, t, ht, hc'⟩ := hc
      exact ⟨s, t, fun _ => ⟨hs, ht, by rw [hc']; simp [Complex.real_smul]⟩⟩
    · exact ⟨0, 0, fun h => absurd h hc⟩
  choose sc tc hsctc using hcoords
  -- choice of generic offsets ε₁, ε₂
  have hpick : ∀ B : Set ℝ, B.Finite → ∃ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 ∧ ε ∉ B := by
    intro B hB
    have hne : ((Set.Ioo (0 : ℝ) 1) \ B).Nonempty :=
      ((Set.Ioo_infinite zero_lt_one).sdiff hB).nonempty
    obtain ⟨ε, hε1, hε2⟩ := hne
    exact ⟨ε, hε1, hε2⟩
  obtain ⟨ε₁, hε₁, hε₁bad⟩ := hpick ((fun c => 1 - sc c) '' ↑S₀)
    ((S₀.finite_toSet).image _)
  obtain ⟨ε₂, hε₂, hε₂bad⟩ := hpick ((fun c => 1 - tc c) '' ↑S₀)
    ((S₀.finite_toSet).image _)
  have hε₁bad' : ∀ c ∈ S₀, 1 - sc c ≠ ε₁ := by
    intro c hc hcon
    exact hε₁bad ⟨c, by simpa using hc, hcon⟩
  have hε₂bad' : ∀ c ∈ S₀, 1 - tc c ≠ ε₂ := by
    intro c hc hcon
    exact hε₂bad ⟨c, by simpa using hc, hcon⟩
  -- the shifted base point and the translation map
  set v' : ℂ := -(ε₁ : ℂ) * L.ω₁ - (ε₂ : ℂ) * L.ω₂ with hv'
  set m : ℂ → ℤ := fun c => if sc c + ε₁ < 1 then 0 else -1 with hm
  set n : ℂ → ℤ := fun c => if tc c + ε₂ < 1 then 0 else -1 with hn
  set φ : ℂ → ℂ := fun c => c + (m c : ℂ) * L.ω₁ + (n c : ℂ) * L.ω₂ with hφ
  -- lattice translation invariance of analyticity
  have hshift : ∀ l ∈ L.lattice, ∀ w : ℂ, AnalyticAt ℂ f w → AnalyticAt ℂ f (w + l) := by
    intro l hl w hA
    have hfun : f = fun z => f (z - l) := by
      funext z
      have hper := hf.2 (z - l) ⟨l, hl⟩
      simpa using hper
    rw [hfun]
    have hcomp : AnalyticAt ℂ (f ∘ fun z : ℂ => z - l) (w + l) := by
      apply AnalyticAt.comp
      · simpa using hA
      · fun_prop
    exact hcomp
  -- interior coordinates of the translated singularities
  have hφcoords : ∀ c ∈ S₀, (sc c + ε₁ + m c) ∈ Set.Ioo (0 : ℝ) 1
      ∧ (tc c + ε₂ + n c) ∈ Set.Ioo (0 : ℝ) 1
      ∧ φ c = v' + ((sc c + ε₁ + m c : ℝ) : ℂ) * L.ω₁
          + ((tc c + ε₂ + n c : ℝ) : ℂ) * L.ω₂ := by
    intro c hc
    obtain ⟨hsIco, htIco, hceq⟩ := hsctc c ((hS₀mem c).mp hc).1
    have hs' : sc c + ε₁ + m c ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [hm]; exact shifted_coord_mem_Ioo hsIco hε₁ (hε₁bad' c hc)
    have ht' : tc c + ε₂ + n c ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [hn]; exact shifted_coord_mem_Ioo htIco hε₂ (hε₂bad' c hc)
    refine ⟨hs', ht', ?_⟩
    rw [hφ, hv']
    push_cast
    linear_combination hceq
  set S' : Finset ℂ := S₀.image φ with hS'def
  -- the counting claim: every singularity of the closed shifted parallelogram is in `S'`
  have hcover : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ¬AnalyticAt ℂ f (v' + (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂)
        → v' + (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂ ∈ S' := by
    intro s hs t ht hbad
    set z : ℂ := v' + (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂ with hz
    obtain ⟨w, hw𝒫, hlat⟩ := L.exists_sub_mem_lattice_of_mem_fundamentalParallelogram z
    have hAw : ¬AnalyticAt ℂ f w := by
      intro hA
      apply hbad
      have hAz := hshift (z - w) hlat w hA
      simpa using hAz
    have hwS₀ : w ∈ S₀ := (hS₀mem w).mpr ⟨hw𝒫, hAw⟩
    obtain ⟨k, l, hkl⟩ := PeriodPair.mem_lattice.mp hlat
    obtain ⟨hsIco, htIco, hweq⟩ := hsctc w hw𝒫
    have hzcoords : ((s - ε₁ - (sc w + k) : ℝ) : ℂ) * L.ω₁
        + ((t - ε₂ - (tc w + l) : ℝ) : ℂ) * L.ω₂ = 0 := by
      have h1 : (k : ℂ) * L.ω₁ + (l : ℂ) * L.ω₂ = z - w := hkl
      rw [hz, hv', hweq] at h1
      push_cast at h1 ⊢
      linear_combination -h1
    obtain ⟨hks, hlt⟩ := coord_eq_zero_of_eq_zero hzcoords
    have hseq : s = sc w + ε₁ + k := by linarith
    have hteq : t = tc w + ε₂ + l := by linarith
    have hkforced := int_offset_forced hsIco hε₁ (hε₁bad' w hwS₀) (by rw [← hseq]; exact hs)
    have hlforced := int_offset_forced htIco hε₂ (hε₂bad' w hwS₀) (by rw [← hteq]; exact ht)
    have hmw : m w = k := by
      simp only [hm]
      exact hkforced.1.symm
    have hnw : n w = l := by
      simp only [hn]
      exact hlforced.1.symm
    have hzφ : z = φ w := by
      rw [hφ]
      change z = w + ((m w : ℤ) : ℂ) * L.ω₁ + ((n w : ℤ) : ℂ) * L.ω₂
      rw [hmw, hnw]
      linear_combination hkl.symm
    rw [hz] at hzφ ⊢
    rw [hzφ]
    exact Finset.mem_image_of_mem φ hwS₀
  -- interior coordinates for `S'`
  have hS'coords : ∀ c ∈ S', ∃ a b : ℝ, a ∈ Set.Ioo (0 : ℝ) 1 ∧ b ∈ Set.Ioo (0 : ℝ) 1 ∧
      c = v' + (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ := by
    intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hX, hY, hEq⟩ := hφcoords c₀ hc₀
    exact ⟨_, _, hX, hY, hEq⟩
  -- the parallelogram residue theorem for the shifted contour
  have hmain := sum_residue_eq_zero_of_boundaryIntegral_eq_zero (L := L) (v := v') (S' := S')
    hf.1 (hf.boundaryIntegral_eq_zero v') hS'coords hcover
  -- transfer the sum back to the fundamental parallelogram
  have hinj : Set.InjOn φ ↑S₀ := by
    intro c hc c' hc' hφeq
    obtain ⟨hsIco, htIco, hceq⟩ := hsctc c ((hS₀mem c).mp (by simpa using hc)).1
    obtain ⟨hsIco', htIco', hceq'⟩ := hsctc c' ((hS₀mem c').mp (by simpa using hc')).1
    have hdiff : ((sc c + m c - (sc c' + m c') : ℝ) : ℂ) * L.ω₁
        + ((tc c + n c - (tc c' + n c') : ℝ) : ℂ) * L.ω₂ = 0 := by
      simp only [hφ] at hφeq
      push_cast
      linear_combination hφeq - hceq + hceq'
    obtain ⟨h1, h2⟩ := coord_eq_zero_of_eq_zero hdiff
    have hmeq : m c = m c' ∧ sc c = sc c' := int_coord_unique hsIco hsIco' h1
    have hneq : n c = n c' ∧ tc c = tc c' := int_coord_unique htIco htIco' h2
    rw [hceq, hceq', hmeq.2, hneq.2]
  have htransfer : ∑ z ∈ S', Chudnovsky.residue f z = ∑ c ∈ S₀, Chudnovsky.residue f c := by
    rw [hS'def, Finset.sum_image (fun x hx y hy hxy => hinj hx hy hxy)]
    apply Finset.sum_congr rfl
    intro c _
    have hφc : φ c = c + ((m c : ℂ) * L.ω₁ + (n c : ℂ) * L.ω₂) := by rw [hφ]; ring
    rw [hφc]
    apply Chudnovsky.residue_add_of_periodic
    intro z
    exact hf.2 z ⟨(m c : ℂ) * L.ω₁ + (n c : ℂ) * L.ω₂,
      PeriodPair.mem_lattice.mpr ⟨m c, n c, rfl⟩⟩
  rw [← htransfer]
  exact hmain

/-- A not-identically-vanishing elliptic function has only finitely many zeros and poles
in the fundamental parallelogram. -/
theorem IsEllipticWith.finite_order_ne_zero (hf : L.IsEllipticWith f)
    (h0 : ∃ z, meromorphicOrderAt f z ≠ ⊤) :
    {z ∈ L.fundamentalParallelogram | meromorphicOrderAt f z ≠ 0}.Finite := by
  have hforall : ∀ x, meromorphicOrderAt f x ≠ ⊤ := by
    obtain ⟨z₀, hz₀⟩ := h0
    intro y
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (meromorphicOn_univ.mpr hf.1)
      isPreconnected_univ (Set.mem_univ z₀) (Set.mem_univ y) hz₀
  have hcod0 : {z : ℂ | meromorphicOrderAt f z = 0} ∈ Filter.codiscrete ℂ := by
    have h := (meromorphicOn_univ.mpr hf.1).codiscreteWithin_setOf_meromorphicOrderAt_eq_zero_or_top
      (fun u _ => hforall u)
    refine Filter.mem_of_superset h (fun z hz => ?_)
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and] at hz ⊢
    rcases hz with h' | h'
    · exact h'
    · exact absurd h' (hforall z)
  have hcd : {z : ℂ | meromorphicOrderAt f z ≠ 0}ᶜ ∈ Filter.codiscrete ℂ := by
    simpa only [Set.compl_setOf, not_ne_iff] using hcod0
  obtain ⟨hclosed, hdisc⟩ := compl_mem_codiscrete_iff.mp hcd
  exact (finite_fundamentalParallelogram_inter hclosed hdisc).subset (fun z hz => ⟨hz.1, hz.2⟩)

/-- The logarithmic derivative `f'/f` of an elliptic function is again elliptic. -/
theorem isEllipticWith_logDeriv (hf : L.IsEllipticWith f) : L.IsEllipticWith (logDeriv f) := by
  refine ⟨fun z => (hf.1 z).deriv.div (hf.1 z), fun z l => ?_⟩
  have hf_per : f (z + (l : ℂ)) = f z := hf.2 z l
  have hderiv_per : deriv f (z + (l : ℂ)) = deriv f z := by
    have h1 := deriv_comp_add_const f (l : ℂ) z
    rw [show (fun w : ℂ => f (w + (l : ℂ))) = f from funext (fun w => hf.2 w l)] at h1
    exact h1.symm
  rw [logDeriv_apply, logDeriv_apply, hf_per, hderiv_per]

/-- **Third Liouville theorem** (paper `liouville3`): an elliptic function which does not
vanish identically has, modulo `L`, as many zeros as poles, counted with multiplicity —
equivalently, the sum of the orders `ord_z f` over a fundamental parallelogram is `0`.

The proof reduces the statement to the **second Liouville theorem**: `logDeriv f = f'/f` is
again elliptic (`IsEllipticWith.logDeriv`), its residue at every point equals the order of `f`
there (`Chudnovsky.residue_logDeriv_eq_order`), and `f` has a zero/pole exactly where `logDeriv f`
fails to be analytic; so the residue sum of `logDeriv f` is the order sum of `f`. -/
theorem IsEllipticWith.sum_meromorphicOrderAt_eq_zero (hf : L.IsEllipticWith f)
    (h0 : ∃ z, meromorphicOrderAt f z ≠ ⊤) :
    ∑ z ∈ (hf.finite_order_ne_zero h0).toFinset, (meromorphicOrderAt f z).untop₀ = 0 := by
  have hforall : ∀ x, meromorphicOrderAt f x ≠ ⊤ := by
    obtain ⟨z₀, hz₀⟩ := h0
    intro y
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (meromorphicOn_univ.mpr hf.1)
      isPreconnected_univ (Set.mem_univ z₀) (Set.mem_univ y) hz₀
  have hg : L.IsEllipticWith (logDeriv f) := isEllipticWith_logDeriv hf
  -- Residue of `logDeriv f` at every point equals the order of `f` (as a complex number).
  have hres : ∀ z, Chudnovsky.residue (logDeriv f) z = ((meromorphicOrderAt f z).untop₀ : ℂ) :=
    fun z => Chudnovsky.residue_logDeriv_eq_order (hf.1 z) (hforall z)
  -- Second Liouville theorem applied to `logDeriv f`.
  have hsum0 : ∑ z ∈ hg.finite_nonAnalytic.toFinset, Chudnovsky.residue (logDeriv f) z = 0 :=
    hg.sum_residue_eq_zero
  -- The zeros/poles of `f` are among the non-analyticity points of `logDeriv f`.
  have hsub : (hf.finite_order_ne_zero h0).toFinset ⊆ hg.finite_nonAnalytic.toFinset := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz ⊢
    obtain ⟨hzP, hzord⟩ := hz
    refine ⟨hzP, fun hana => ?_⟩
    have hz0 : Chudnovsky.residue (logDeriv f) z = 0 :=
      Chudnovsky.residue_eq_zero_of_analyticAt hana
    rw [hres z] at hz0
    have huntop : (meromorphicOrderAt f z).untop₀ ≠ 0 := fun h =>
      hzord (by rw [← WithTop.coe_untop₀_of_ne_top (hforall z), h]; simp)
    exact huntop (by exact_mod_cast hz0)
  -- At the extra non-analyticity points the order (and hence the residue) is `0`.
  have hzero : ∀ z ∈ hg.finite_nonAnalytic.toFinset,
      z ∉ (hf.finite_order_ne_zero h0).toFinset → Chudnovsky.residue (logDeriv f) z = 0 := by
    intro z hz hznotin
    rw [Set.Finite.mem_toFinset] at hz hznotin
    have hord0 : meromorphicOrderAt f z = 0 := by
      by_contra hne
      exact hznotin ⟨hz.1, hne⟩
    rw [hres z, hord0]; simp
  have key : ∑ z ∈ (hf.finite_order_ne_zero h0).toFinset,
      Chudnovsky.residue (logDeriv f) z = 0 := by
    rw [Finset.sum_subset hsub hzero]; exact hsum0
  have hfin : ((∑ z ∈ (hf.finite_order_ne_zero h0).toFinset,
      (meromorphicOrderAt f z).untop₀ : ℤ) : ℂ) = 0 := by
    rw [Int.cast_sum, Finset.sum_congr rfl (fun z _ => (hres z).symm)]
    exact key
  exact_mod_cast hfin

/-- Codiscreteness is invariant under translation. -/
private lemma codiscrete_add_preimage {S : Set ℂ} (l : ℂ)
    (hS : S ∈ Filter.codiscrete ℂ) :
    (fun z ↦ z + l) ⁻¹' S ∈ Filter.codiscrete ℂ := by
  have he : Topology.IsEmbedding (fun z : ℂ ↦ z + (-l)) := (Homeomorph.addRight (-l)).isEmbedding
  have hrange : Set.range (fun z : ℂ ↦ z + (-l)) = Set.univ :=
    (Homeomorph.addRight (-l)).surjective.range_eq
  have key : (fun z : ℂ ↦ z + (-l)) '' S ∈ Filter.codiscrete ℂ := by
    have hiff := he.image_mem_codiscreteWithin_range (s := S)
    rw [hrange] at hiff
    exact hiff.mpr hS
  have hEq : (fun z : ℂ ↦ z + l) ⁻¹' S = (fun z : ℂ ↦ z + (-l)) '' S := by
    ext z
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hz; exact ⟨z + l, hz, by ring⟩
    · rintro ⟨w, hw, rfl⟩; simpa using hw
  rw [hEq]; exact key

/-- **Workhorse lemma** (used throughout the paper, e.g. in `pstrichprod`,
`fouriersigma`, and Appendix A): two elliptic functions with the same zeros and poles,
counted with orders, agree up to a nonzero constant factor away from a discrete set
(namely, away from their poles and points of non-normality). -/
theorem IsEllipticWith.exists_const_mul_of_meromorphicOrderAt_eq (hf : L.IsEllipticWith f)
    (hg : L.IsEllipticWith g) (h : ∀ z, meromorphicOrderAt f z = meromorphicOrderAt g z) :
    ∃ c : ℂ, c ≠ 0 ∧ f =ᶠ[Filter.codiscrete ℂ] fun z ↦ c * g z := by
  by_cases hex : ∃ z, meromorphicOrderAt f z ≠ ⊤
  · -- Non-degenerate case: `f/g` has order `0` everywhere, so its analytic normal form is
    -- entire, nonvanishing and elliptic, hence a nonzero constant.
    have hforall_f : ∀ z, meromorphicOrderAt f z ≠ ⊤ := by
      obtain ⟨z₀, hz₀⟩ := hex
      intro y
      exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (meromorphicOn_univ.mpr hf.1)
        isPreconnected_univ (Set.mem_univ z₀) (Set.mem_univ y) hz₀
    have hforall_g : ∀ z, meromorphicOrderAt g z ≠ ⊤ := fun z ↦ (h z) ▸ hforall_f z
    have hfg_mero : MeromorphicOn (f / g) Set.univ := fun z _ ↦ (hf.1 z).div (hg.1 z)
    have hord0 : ∀ z, meromorphicOrderAt (f / g) z = 0 := by
      intro z
      rw [meromorphicOrderAt_div (hf.1 z) (hg.1 z), h z]
      rcases WithTop.ne_top_iff_exists.mp (hforall_g z) with ⟨n, hn⟩
      rw [← hn]; simp
    set H := toMeromorphicNFOn (f / g) Set.univ with hHdef
    have hHorder : ∀ z, meromorphicOrderAt H z = 0 := by
      intro z
      rw [hHdef, meromorphicOrderAt_toMeromorphicNFOn hfg_mero (Set.mem_univ z)]
      exact hord0 z
    have hHnf : MeromorphicNFOn H Set.univ := by
      rw [hHdef]; exact meromorphicNFOn_toMeromorphicNFOn (f / g) Set.univ
    have hHanalytic : ∀ z, AnalyticAt ℂ H z := fun z ↦
      (hHnf (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
        (le_of_eq (hHorder z).symm)
    have hHne : ∀ z, H z ≠ 0 := fun z ↦
      (hHnf (Set.mem_univ z)).meromorphicOrderAt_eq_zero_iff.mp (hHorder z)
    have hHon : AnalyticOnNhd ℂ H Set.univ := fun z _ ↦ hHanalytic z
    -- `H` is `L`-periodic (by the identity theorem, using codiscrete agreement with `f/g`).
    have hHper : ∀ l : L.lattice, (fun z ↦ H (z + (l : ℂ))) = H := by
      intro l
      have hshift_an : AnalyticOnNhd ℂ (fun z ↦ H (z + (l : ℂ))) Set.univ := by
        intro z _
        exact (hHanalytic (z + (l : ℂ))).comp (f := fun w : ℂ ↦ w + (l : ℂ)) (by fun_prop)
      have hD : {z : ℂ | (f / g) z = H z} ∈ Filter.codiscrete ℂ :=
        toMeromorphicNFOn_eqOn_codiscrete hfg_mero
      have hInter : {z : ℂ | (f / g) z = H z} ∩
          ((fun z ↦ z + (l : ℂ)) ⁻¹' {z : ℂ | (f / g) z = H z}) ∈ Filter.codiscrete ℂ :=
        Filter.inter_mem hD (codiscrete_add_preimage (l : ℂ) hD)
      have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), (fun z ↦ H (z + (l : ℂ))) z = H z := by
        have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ({z : ℂ | (f / g) z = H z} ∩
            ((fun z ↦ z + (l : ℂ)) ⁻¹' {z : ℂ | (f / g) z = H z})) := by
          have hm := mem_codiscrete.mp hInter (0 : ℂ)
          rwa [Filter.disjoint_principal_right, compl_compl] at hm
        refine (hev.mono ?_).frequently
        rintro z ⟨hz1, hz2⟩
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at hz1 hz2
        have hper : (f / g) (z + (l : ℂ)) = (f / g) z := by
          simp only [Pi.div_apply, hf.2 z l, hg.2 z l]
        change H (z + (l : ℂ)) = H z
        rw [← hz2, hper, hz1]
      exact hshift_an.eq_of_frequently_eq hHon hfreq
    have hHell : L.IsEllipticWith H :=
      ⟨fun z ↦ (hHanalytic z).meromorphicAt, fun z l ↦ congrFun (hHper l) z⟩
    obtain ⟨c, hc⟩ :=
      hHell.exists_eq_const_of_differentiable (fun z ↦ (hHanalytic z).differentiableAt)
    have hcne : c ≠ 0 := by
      have h0 := hHne 0
      rwa [show H 0 = c from congrFun hc 0] at h0
    refine ⟨c, hcne, ?_⟩
    have hgord0 : {z : ℂ | meromorphicOrderAt g z = 0} ∈ Filter.codiscrete ℂ := by
      have hh :=
        (meromorphicOn_univ.mpr hg.1).codiscreteWithin_setOf_meromorphicOrderAt_eq_zero_or_top
          (fun u _ ↦ hforall_g u)
      refine Filter.mem_of_superset hh (fun z hz => ?_)
      simp only [Set.mem_setOf_eq, Set.mem_univ, true_and] at hz ⊢
      rcases hz with h' | h'
      · exact h'
      · exact absurd h' (hforall_g z)
    have hganalytic : {z : ℂ | AnalyticAt ℂ g z} ∈ Filter.codiscrete ℂ :=
      MeromorphicOn.eventually_codiscreteWithin_analyticAt g (meromorphicOn_univ.mpr hg.1)
    have hHeq : {z : ℂ | (f / g) z = H z} ∈ Filter.codiscrete ℂ :=
      toMeromorphicNFOn_eqOn_codiscrete hfg_mero
    filter_upwards [hHeq, hgord0, hganalytic] with z hz1 hz2 hz3
    have hgnz : g z ≠ 0 := hz3.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp hz2
    simp only [Pi.div_apply] at hz1
    rw [show H z = c from congrFun hc z] at hz1
    change f z = c * g z
    exact (div_eq_iff hgnz).mp hz1
  · -- Degenerate case: `f` (hence `g`) vanishes on a codiscrete set; take `c = 1`.
    simp only [not_exists, not_ne_iff] at hex
    have hf0 : {z : ℂ | f z = 0} ∈ Filter.codiscrete ℂ := by
      rw [mem_codiscrete]
      intro x
      rw [Filter.disjoint_principal_right, compl_compl]
      exact meromorphicOrderAt_eq_top_iff.mp (hex x)
    have hg0 : {z : ℂ | g z = 0} ∈ Filter.codiscrete ℂ := by
      rw [mem_codiscrete]
      intro x
      rw [Filter.disjoint_principal_right, compl_compl]
      exact meromorphicOrderAt_eq_top_iff.mp ((h x) ▸ hex x)
    refine ⟨1, one_ne_zero, ?_⟩
    filter_upwards [hf0, hg0] with z hz hz'
    show f z = 1 * g z
    rw [hz, hz', one_mul]

end PeriodPair
