/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.NilpotentVolterra
public import LeanPool.NavierStokesAndEuler.NavierStokes.VolterraParity
public import LeanPool.NavierStokesAndEuler.NavierStokes.CauchyRestriction
public import LeanPool.NavierStokesAndEuler.NavierStokes.CompactSmoothFamily
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-!
# Radial smoothness for the actual regular Volterra integral

The radial integral gains one real derivative, including at the origin.
The intended bootstrap uses bounded parameter-derivative operators between
nested complex disks; no analyticity in the radial variable is assumed.

The radial domain is an open symmetric interval. In particular these results
do not identify the clamped extension of a positive path with a smooth
extension across zero.
-/

noncomputable section

namespace NavierStokes.VolterraRegularity

open Set Filter MeasureTheory
open scoped Topology ContDiff
open NilpotentVolterra

abbrev radialDomain (R : ℝ) : Set ℝ := Metric.ball 0 R

theorem scaled_mem_radialDomain {R r t : ℝ} (hr : r ∈ radialDomain R)
    (ht : t ∈ Icc (0 : ℝ) 1) : t * r ∈ radialDomain R := by
  simp only [radialDomain, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hr ⊢
  rw [abs_mul, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (abs_nonneg r) ht.2).trans_lt hr

section IntegralRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuity of the actual weighted integral needs continuity only on the
radial domain. The integration variable is clamped solely outside `[0,1]`
to apply the global parameter-integral continuity theorem. -/
theorem weightedMean_continuousOn (c : ℕ) {R : ℝ} {f : ℝ → E}
    (hf : ContinuousOn f (radialDomain R)) :
    ContinuousOn (weightedMean c f) (radialDomain R) := by
  let q : ℝ → ℝ := fun t => (projIcc 0 1 zero_le_one t : ℝ)
  have hq : Continuous q := continuous_subtype_val.comp continuous_projIcc
  have hqmem (t : ℝ) : q t ∈ Icc (0 : ℝ) 1 :=
    (projIcc 0 1 zero_le_one t).property
  have harg : Continuous (fun p : radialDomain R × ℝ => q p.2 * (p.1 : ℝ)) :=
    (hq.comp continuous_snd).mul (continuous_subtype_val.comp continuous_fst)
  have hjoint : Continuous (fun p : radialDomain R × ℝ =>
      p.2 ^ c • f (q p.2 * (p.1 : ℝ))) :=
    (continuous_snd.pow c).smul
      (hf.comp_continuous harg (fun p => scaled_mem_radialDomain p.1.property (hqmem p.2)))
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume)
    (f := fun (r : radialDomain R) (t : ℝ) => t ^ c • f (q t * (r : ℝ))) hjoint 0 1
  rw [continuousOn_iff_continuous_domRestrict]
  apply hcont.congr
  intro r
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  have hqt : q t = t := congrArg Subtype.val (projIcc_of_mem zero_le_one ht')
  simp only [hqt]

theorem weightedMean_eq_of_eqOn (c : ℕ) {R : ℝ} {f g : ℝ → E}
    (hfg : EqOn f g (radialDomain R)) {r : ℝ} (hr : r ∈ radialDomain R) :
    weightedMean c f r = weightedMean c g r := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  change t ^ c • f (t * r) = t ^ c • g (t * r)
  rw [hfg (scaled_mem_radialDomain hr ht')]

theorem regularPrimitive_eq_of_eqOn (c : ℕ) {R : ℝ} {f g : ℝ → E}
    (hfg : EqOn f g (radialDomain R)) {r : ℝ} (hr : r ∈ radialDomain R) :
    regularPrimitive c f r = regularPrimitive c g r := by
  rw [regularPrimitive, regularPrimitive, weightedMean_eq_of_eqOn c hfg hr]

variable [CompleteSpace E]

/-- The nonsingular first derivative formula is local on the radial domain.
Its proof uses a continuous extension only to invoke the already established
integral identity; the claimed function remains the original integral. -/
theorem regularPrimitive_hasDerivAt_on (c : ℕ) {R : ℝ} {f : ℝ → E}
    (hf : ContinuousOn f (radialDomain R)) {r : ℝ} (hr : r ∈ radialDomain R) :
    HasDerivAt (regularPrimitive c f)
      (f r - (c : ℝ) • weightedMean c f r) r := by
  have hrR : |r| < R := by simpa only [radialDomain, Metric.mem_ball,
    dist_zero_right, Real.norm_eq_abs] using hr
  obtain ⟨a, hra, haR⟩ := exists_between hrR
  have ha : 0 < a := (abs_nonneg r).trans_lt hra
  let clip : ℝ → ℝ := fun x => max (-a) (min a x)
  have hccont : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
  have hcmem (x : ℝ) : clip x ∈ radialDomain R := by
    have hlo : -a ≤ clip x := le_max_left _ _
    have hhi : clip x ≤ a := max_le (by linarith) (min_le_left _ _)
    have habs := abs_le.mpr ⟨hlo, hhi⟩
    simpa only [radialDomain, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using
      habs.trans_lt haR
  have hceq : EqOn clip id (radialDomain a) := by
    intro x hx
    have hx' : |x| < a := by simpa only [radialDomain, Metric.mem_ball,
      dist_zero_right, Real.norm_eq_abs] using hx
    rcases abs_lt.mp hx' with ⟨hlo, hhi⟩
    simp only [clip, min_eq_right hhi.le, max_eq_right hlo.le, id_eq]
  let g : ℝ → E := fun x => f (clip x)
  have hg : Continuous g := hf.comp_continuous hccont hcmem
  have hfg : EqOn f g (radialDomain a) := by
    intro x hx
    simp only [g, hceq hx, id_eq]
  have hra' : r ∈ radialDomain a := by
    simpa only [radialDomain, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hra
  have heq : regularPrimitive c f =ᶠ[𝓝 r] regularPrimitive c g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hra'] with x hx
    exact regularPrimitive_eq_of_eqOn c hfg hx
  have hd := (regularPrimitive_hasDerivAt c hg r).congr_of_eventuallyEq heq
  rw [← hfg hra', ← weightedMean_eq_of_eqOn c hfg hra'] at hd
  exact hd

omit [CompleteSpace E] in
/-- Differentiation under the actual weighted integral. A compact radial
subinterval supplies the integrable domination, so no global derivative
bound or radial analyticity is needed. -/
theorem weightedMean_hasDerivAt_on (c : ℕ) {R : ℝ} {f : ℝ → E}
    (hf : ContinuousOn f (radialDomain R))
    (hdf : DifferentiableOn ℝ f (radialDomain R))
    (hf' : ContinuousOn (deriv f) (radialDomain R))
    {r : ℝ} (hr : r ∈ radialDomain R) :
    HasDerivAt (weightedMean c f) (weightedMean (c + 1) (deriv f) r) r := by
  let δ : ℝ := (R - |r|) / 2
  let b : ℝ := |r| + δ
  have hrR : |r| < R := by simpa only [radialDomain, Metric.mem_ball,
    dist_zero_right, Real.norm_eq_abs] using hr
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hbR : b < R := by dsimp [b, δ]; linarith
  have hsub : Metric.closedBall (0 : ℝ) b ⊆ radialDomain R := by
    intro x hx
    exact lt_of_le_of_lt hx hbR
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℝ) b).exists_bound_of_continuousOn
    (hf'.mono hsub)
  have htx (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (x : ℝ) (hx : x ∈ Metric.ball r δ) : t * x ∈ Metric.closedBall (0 : ℝ) b := by
    have hx' : |x - r| < δ := by simpa only [Metric.mem_ball, Real.dist_eq] using hx
    have hxn : |x| ≤ b := by
      have ht := abs_add_le (x - r) r
      rw [sub_add_cancel] at ht
      dsimp [b]
      linarith
    change dist (t * x) 0 ≤ b
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg x) ht.2).trans hxn
  have hc (g : ℝ → E) (hg : ContinuousOn g (radialDomain R)) (p : ℕ)
      (x : ℝ) (hx : x ∈ radialDomain R) :
      ContinuousOn (fun t : ℝ => t ^ p • g (t * x)) (Icc (0 : ℝ) 1) :=
    (continuous_id.pow p).continuousOn.smul
      (hg.comp (continuous_id.mul continuous_const).continuousOn
        (fun t ht => scaled_mem_radialDomain hx ht))
  let u : ℝ → ℝ → E := fun x t => t ^ c • f (t * x)
  let v : ℝ → ℝ → E := fun x t => t ^ (c + 1) • deriv f (t * x)
  have hu_meas : ∀ᶠ x in 𝓝 r,
      AEStronglyMeasurable (u x) (volume.restrict (uIoc (0 : ℝ) 1)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hr] with x hx
    simpa only [uIoc_of_le zero_le_one] using
      ((hc f hf c x hx).intervalIntegrable_of_Icc zero_le_one).aestronglyMeasurable
  have hu_int : IntervalIntegrable (u r) volume 0 1 :=
    (hc f hf c r hr).intervalIntegrable_of_Icc zero_le_one
  have hv_meas : AEStronglyMeasurable (v r) (volume.restrict (uIoc (0 : ℝ) 1)) := by
    simpa only [uIoc_of_le zero_le_one] using
      ((hc (deriv f) hf' (c + 1) r hr).intervalIntegrable_of_Icc zero_le_one).aestronglyMeasurable
  have hv_bound : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      ∀ x ∈ Metric.ball r δ, ‖v x t‖ ≤ K := by
    apply Filter.Eventually.of_forall
    intro t ht x hx
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      have ht'' : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
      exact ⟨ht''.1.le, ht''.2⟩
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht'.1 _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht'.1 ht'.2)).trans
      (hK (t * x) (htx t ht' x hx))
  have hv_diff : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      ∀ x ∈ Metric.ball r δ, HasDerivAt (fun x => u x t) (v x t) x := by
    apply Filter.Eventually.of_forall
    intro t ht x hx
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      have ht'' : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
      exact ⟨ht''.1.le, ht''.2⟩
    have hm := hsub (htx t ht' x hx)
    have hd := ((hdf (t * x) hm).differentiableAt (Metric.isOpen_ball.mem_nhds hm)).hasDerivAt
    convert! (hd.scomp x ((hasDerivAt_id x).const_mul t)).const_smul (t ^ c) using 1
    simp only [v, mul_one, smul_smul, pow_succ]
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1) (F := u) (F' := v)
    (bound := fun _ => K) (Metric.ball_mem_nhds r hδ) hu_meas hu_int hv_meas hv_bound
    (intervalIntegrable_const) hv_diff).2

omit [CompleteSpace E] in
/-- The weighted mean preserves every finite radial differentiability order. -/
theorem weightedMean_contDiffOn (n : ℕ) (c : ℕ) {R : ℝ} {f : ℝ → E}
    (hf : ContDiffOn ℝ n f (radialDomain R)) :
    ContDiffOn ℝ n (weightedMean c f) (radialDomain R) := by
  induction n generalizing c f with
  | zero =>
      exact contDiffOn_zero.mpr (weightedMean_continuousOn c hf.continuousOn)
  | succ n ih =>
      have hf_succ : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) f (radialDomain R) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hf
      have hf_split := (contDiffOn_succ_iff_deriv_of_isOpen Metric.isOpen_ball).1 hf_succ
      have hfirst (r : ℝ) (hr : r ∈ radialDomain R) :=
        weightedMean_hasDerivAt_on c hf.continuousOn hf_split.1 hf_split.2.2.continuousOn hr
      have hout : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1)
          (weightedMean c f) (radialDomain R) := by
        apply (contDiffOn_succ_iff_deriv_of_isOpen Metric.isOpen_ball).2
        refine ⟨fun r hr => (hfirst r hr).differentiableAt.differentiableWithinAt, ?_, ?_⟩
        · simp
        · exact (ih (c + 1) hf_split.2.2).congr (fun r hr => (hfirst r hr).deriv)
      simpa only [Nat.cast_add, Nat.cast_one] using hout

/-- The regular Volterra integral gains one full real derivative. The domain
contains zero, so this includes the formerly singular endpoint. -/
theorem regularPrimitive_contDiffOn_succ (n : ℕ) (c : ℕ) {R : ℝ} {f : ℝ → E}
    (hf : ContDiffOn ℝ n f (radialDomain R)) :
    ContDiffOn ℝ (n + 1 : ℕ) (regularPrimitive c f) (radialDomain R) := by
  have hfirst (r : ℝ) (hr : r ∈ radialDomain R) :=
    regularPrimitive_hasDerivAt_on c hf.continuousOn hr
  have hout : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1)
      (regularPrimitive c f) (radialDomain R) := by
    apply (contDiffOn_succ_iff_deriv_of_isOpen Metric.isOpen_ball).2
    refine ⟨fun r hr => (hfirst r hr).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · exact (hf.sub (contDiffOn_const.smul (weightedMean_contDiffOn n c hf))).congr
        (fun r hr => (hfirst r hr).deriv)
  simpa only [Nat.cast_add, Nat.cast_one] using hout

theorem regularPrimitive_contDiffOn_infty (c : ℕ) {R : ℝ} {f : ℝ → E}
    (hf : ContDiffOn ℝ ∞ f (radialDomain R)) :
    ContDiffOn ℝ ∞ (regularPrimitive c f) (radialDomain R) := by
  apply contDiffOn_infty.2
  intro n
  exact (regularPrimitive_contDiffOn_succ n c (contDiffOn_infty.1 hf n)).of_le (by
    exact_mod_cast Nat.le_succ n)

end IntegralRegularity

section DiagonalIntegral

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual coordinatewise regular inverse, for arbitrary nonnegative
integer singular exponents. In the six-component system these are
`(0,0,2,0,3,1)`. -/
noncomputable def diagonalRegularPrimitive (c : ι → ℕ) (f : ℝ → ι → E) : ℝ → ι → E :=
  fun r i => regularPrimitive (c i) (fun s => f s i) r

theorem diagonalRegularPrimitive_contDiffOn_succ [CompleteSpace E]
    (n : ℕ) (c : ι → ℕ) {R : ℝ} {f : ℝ → ι → E}
    (hf : ContDiffOn ℝ n f (radialDomain R)) :
    ContDiffOn ℝ (n + 1 : ℕ) (diagonalRegularPrimitive c f) (radialDomain R) := by
  apply contDiffOn_pi.2
  intro i
  exact regularPrimitive_contDiffOn_succ n (c i) (contDiffOn_pi.1 hf i)

end DiagonalIntegral

section ScaleBootstrap

universe u

variable {ι : Type*} [Fintype ι]
variable {B : ℕ → Type u} [∀ j, NormedAddCommGroup (B j)]
  [∀ j, NormedSpace ℝ (B j)] [∀ j, CompleteSpace (B j)]

/-- A genuine radial bootstrap on a sequence of Banach spaces. The next
level is the larger parameter disk; its bounded Cauchy derivative is folded
into `A₁`. The only initial regularity imposed on the solution is continuity. -/
theorem scale_contDiffOn (c : ι → ℕ) {R : ℝ}
    (W f : ∀ j, ℝ → ι → B j)
    (A₀ : ∀ j, ℝ → (ι → B j) →L[ℝ] (ι → B j))
    (A₁ : ∀ j, ℝ → (ι → B (j + 1)) →L[ℝ] (ι → B j))
    (hW : ∀ j, ContinuousOn (W j) (radialDomain R))
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) (radialDomain R))
    (hA₀ : ∀ j, ContDiffOn ℝ ∞ (A₀ j) (radialDomain R))
    (hA₁ : ∀ j, ContDiffOn ℝ ∞ (A₁ j) (radialDomain R))
    (heq : ∀ j, EqOn (W j)
      (diagonalRegularPrimitive c (fun r =>
        f j r + (A₀ j r) (W j r) + (A₁ j r) (W (j + 1) r))) (radialDomain R)) :
    ∀ j, ContDiffOn ℝ ∞ (W j) (radialDomain R) := by
  have hfinite : ∀ n : ℕ, ∀ j, ContDiffOn ℝ n (W j) (radialDomain R) := by
    intro n
    induction n with
    | zero =>
        intro j
        exact contDiffOn_zero.mpr (hW j)
    | succ n ih =>
        intro j
        have hrhs : ContDiffOn ℝ n (fun r =>
            f j r + (A₀ j r) (W j r) + (A₁ j r) (W (j + 1) r)) (radialDomain R) :=
          ((contDiffOn_infty.1 (hf j) n).add
            ((contDiffOn_infty.1 (hA₀ j) n).clm_apply (ih j))).add
            ((contDiffOn_infty.1 (hA₁ j) n).clm_apply (ih (j + 1)))
        exact (diagonalRegularPrimitive_contDiffOn_succ n c hrhs).congr (heq j)
  intro j
  exact contDiffOn_infty.2 (fun n => hfinite n j)

end ScaleBootstrap

section AlgebraScale

universe u

variable {ι : Type*} [Fintype ι]
variable {B : ℕ → Type u} [∀ j, NormedRing (B j)]
  [∀ j, NormedAlgebra ℝ (B j)] [∀ j, CompleteSpace (B j)]

/-- Entrywise version of the scale bootstrap, convenient for matrices of
continuous functions on compact parameter disks. -/
theorem algebraScale_contDiffOn (c : ι → ℕ) {R : ℝ}
    (W f : ∀ j, ℝ → ι → B j) (a₀ a₁ : ∀ j, ℝ → ι → ι → B j)
    (D : ∀ j, B (j + 1) →L[ℝ] B j)
    (hW : ∀ j i, ContinuousOn (fun r => W j r i) (radialDomain R))
    (hf : ∀ j i, ContDiffOn ℝ ∞ (fun r => f j r i) (radialDomain R))
    (ha₀ : ∀ j i k, ContDiffOn ℝ ∞ (fun r => a₀ j r i k) (radialDomain R))
    (ha₁ : ∀ j i k, ContDiffOn ℝ ∞ (fun r => a₁ j r i k) (radialDomain R))
    (heq : ∀ j i, EqOn (fun r => W j r i)
      (regularPrimitive (c i) (fun r => f j r i +
        ∑ k, a₀ j r i k * W j r k + ∑ k, a₁ j r i k * D j (W (j + 1) r k)))
      (radialDomain R)) :
    ∀ j i, ContDiffOn ℝ ∞ (fun r => W j r i) (radialDomain R) := by
  have hfinite : ∀ n : ℕ, ∀ j i,
      ContDiffOn ℝ n (fun r => W j r i) (radialDomain R) := by
    intro n
    induction n with
    | zero =>
        intro j i
        exact contDiffOn_zero.mpr (hW j i)
    | succ n ih =>
        intro j i
        have h₀ : ContDiffOn ℝ n (fun r => ∑ k, a₀ j r i k * W j r k)
            (radialDomain R) := by
          apply ContDiffOn.sum
          intro k _
          exact (contDiffOn_infty.1 (ha₀ j i k) n).mul (ih j k)
        have h₁ : ContDiffOn ℝ n (fun r => ∑ k, a₁ j r i k * D j (W (j + 1) r k))
            (radialDomain R) := by
          apply ContDiffOn.sum
          intro k _
          exact (contDiffOn_infty.1 (ha₁ j i k) n).mul
            ((D j).contDiff.comp_contDiffOn (ih (j + 1) k))
        exact (regularPrimitive_contDiffOn_succ n (c i)
          (((contDiffOn_infty.1 (hf j i) n).add h₀).add h₁)).congr (heq j i)
  intro j i
  exact contDiffOn_infty.2 (fun n => hfinite n j i)

end AlgebraScale

section CompactEvaluation

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Evaluation commutes with the actual radial integral when its source is
continuous on the radial domain. -/
theorem regularPrimitive_evaluate (c : ℕ) {R : ℝ} {f : ℝ → C(K, E)}
    (hf : ContinuousOn f (radialDomain R)) {r : ℝ} (hr : r ∈ radialDomain R) (z : K) :
    regularPrimitive c f r z = regularPrimitive c (fun s => f s z) r := by
  have hc : ContinuousOn (fun t : ℝ => t ^ c • f (t * r)) (Icc (0 : ℝ) 1) :=
    (continuous_id.pow c).continuousOn.smul
      (hf.comp (continuous_id.mul continuous_const).continuousOn
        (fun t ht => scaled_mem_radialDomain hr ht))
  have hi : IntervalIntegrable (fun t : ℝ => t ^ c • f (t * r)) volume 0 1 :=
    hc.intervalIntegrable_of_Icc zero_le_one
  simp only [regularPrimitive, ContinuousMap.smul_apply]
  congr 1
  exact ((ContinuousMap.evalCLM ℝ z).intervalIntegral_comp_comm hi).symm

end CompactEvaluation

theorem radialDomain_subset_Icc (R : ℝ) : radialDomain R ⊆ Icc (-R) R := by
  intro r hr
  have h : |r| < R := by simpa only [radialDomain, Metric.mem_ball,
    dist_zero_right, Real.norm_eq_abs] using hr
  exact ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩

/-- Continuous global parameterization of the trace. Only its restriction
to the open radial domain will be asserted to be smooth. -/
noncomputable def radiusProjection (R : ℝ) (hR : 0 ≤ R) (r : ℝ) : Icc (-R) R :=
  projIcc (-R) R (by linarith) r

theorem radiusProjection_continuous (R : ℝ) (hR : 0 ≤ R) :
    Continuous (radiusProjection R hR) := continuous_projIcc (h := by linarith)

theorem radiusProjection_eq (R : ℝ) (hR : 0 ≤ R) {r : ℝ} (hr : r ∈ Icc (-R) R) :
    (radiusProjection R hR r : ℝ) = r := by
  exact congrArg Subtype.val (projIcc_of_mem (by linarith : -R ≤ R) hr)

section ActualField

open VolterraAnalyticBounds CauchyRestriction

/-- A continuous parameter-disk curve formed from the actual field. The
projection only defines values outside the radial interval; it is the
identity everywhere used in the regularity theorem. -/
noncomputable def fieldDiskCurve (R : ℝ) (hR : 0 ≤ R) {U : Set ℂ}
    (W : Field)
    (hW : ContinuousOn (fun p : ℝ × ℂ => W p.1 p.2) (Icc (-R) R ×ˢ U))
    (center : ℂ) (ρ : ℝ) (hDisk : Metric.closedBall center ρ ⊆ U)
    (r : ℝ) (i : Fin 6) : C(Disk center ρ, ℂ) where
  toFun z := W (radiusProjection R hR r) z i
  continuous_toFun :=
    (continuous_apply i).comp
      (hW.comp_continuous (continuous_const.prodMk continuous_subtype_val)
        (fun z => ⟨(radiusProjection R hR r).property, hDisk z.property⟩))

theorem fieldDiskCurve_continuous (R : ℝ) (hR : 0 ≤ R) {U : Set ℂ}
    (W : Field)
    (hW : ContinuousOn (fun p : ℝ × ℂ => W p.1 p.2) (Icc (-R) R ×ˢ U))
    (center : ℂ) (ρ : ℝ) (hDisk : Metric.closedBall center ρ ⊆ U) (i : Fin 6) :
    Continuous (fun r => fieldDiskCurve R hR W hW center ρ hDisk r i) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_apply i).comp
    (hW.comp_continuous
      (((continuous_subtype_val.comp (radiusProjection_continuous R hR)).comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun p => ⟨(radiusProjection R hR p.1).property, hDisk p.2.property⟩))

theorem fieldDiskCurve_apply (R : ℝ) (hR : 0 ≤ R) {U : Set ℂ}
    (W : Field)
    (hW : ContinuousOn (fun p : ℝ × ℂ => W p.1 p.2) (Icc (-R) R ×ˢ U))
    (center : ℂ) (ρ : ℝ) (hDisk : Metric.closedBall center ρ ⊆ U)
    {r : ℝ} (hr : r ∈ Icc (-R) R) (i : Fin 6) (z : Disk center ρ) :
    fieldDiskCurve R hR W hW center ρ hDisk r i z = W r z i := by
  change W (radiusProjection R hR r) z i = W r z i
  rw [radiusProjection_eq R hR hr]

/-- Smoothness of the disk-valued curve implies actual scalar radial
smoothness, by bounded evaluation. -/
theorem fieldDiskCurve_radial_contDiffOn (R : ℝ) (hR : 0 ≤ R) {U : Set ℂ}
    (W : Field)
    (hW : ContinuousOn (fun p : ℝ × ℂ => W p.1 p.2) (Icc (-R) R ×ˢ U))
    (center : ℂ) (ρ : ℝ) (hDisk : Metric.closedBall center ρ ⊆ U)
    (i : Fin 6) (n : WithTop ℕ∞)
    (hs : ContDiffOn ℝ n (fun r => fieldDiskCurve R hR W hW center ρ hDisk r i)
      (radialDomain R)) (z : Disk center ρ) :
    ContDiffOn ℝ n (fun r => W r z i) (radialDomain R) := by
  apply ((ContinuousMap.evalCLM ℝ z).contDiff.comp_contDiffOn hs).congr
  intro r hr
  exact (fieldDiskCurve_apply R hR W hW center ρ hDisk
    (radialDomain_subset_Icc R hr) i z).symm

/-- Actual radial regularity of a symmetric integral solution. The smooth
inputs are disk-valued representations of the coefficients and forcing;
their value identities are explicit. Continuity and holomorphy of the
constructed solution come solely from `IsSymmetricIntegralSolution`.

The radii increase with the level. Each induction step spends one disk gap
through the concrete bounded Cauchy operator and gains one radial derivative
through the actual regular Volterra integral. -/
theorem symmetric_solution_disk_curves_contDiffOn
    {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} {A₀ A₁ : Coeff} {f W : Field}
    (hW : VolterraParity.IsSymmetricIntegralSolution R U A₀ A₁ f W)
    (center : ℂ) (ρ : ℕ → ℝ) (hρ : ∀ j, ρ j < ρ (j + 1))
    (hDisk : ∀ j, Metric.closedBall center (ρ j) ⊆ U)
    (b : ∀ j, ℝ → Fin 6 → C(Disk center (ρ j), ℂ))
    (a₀ a₁ : ∀ j, ℝ → Fin 6 → Fin 6 → C(Disk center (ρ j), ℂ))
    (hb : ∀ j i, ContDiffOn ℝ ∞ (fun r => b j r i) (radialDomain R))
    (ha₀ : ∀ j i k, ContDiffOn ℝ ∞ (fun r => a₀ j r i k) (radialDomain R))
    (ha₁ : ∀ j i k, ContDiffOn ℝ ∞ (fun r => a₁ j r i k) (radialDomain R))
    (hbval : ∀ j r, r ∈ radialDomain R → ∀ i (z : Disk center (ρ j)), b j r i z = f r z i)
    (ha₀val : ∀ j r, r ∈ radialDomain R → ∀ i k (z : Disk center (ρ j)),
      a₀ j r i k z = A₀ r z i k)
    (ha₁val : ∀ j r, r ∈ radialDomain R → ∀ i k (z : Disk center (ρ j)),
      a₁ j r i k z = A₁ r z i k) :
    ∀ j i, ContDiffOn ℝ ∞
      (fun r => fieldDiskCurve R hR W hW.jointly_continuous center (ρ j) (hDisk j) r i)
      (radialDomain R) := by
  let V := fun j r i =>
    fieldDiskCurve R hR W hW.jointly_continuous center (ρ j) (hDisk j) r i
  let D := fun j => (CauchyRestriction.derivativeCLM (E := ℂ) center (hρ j)).restrictScalars ℝ
  have hV (j : ℕ) (i : Fin 6) : Continuous (fun r => V j r i) :=
    fieldDiskCurve_continuous R hR W hW.jointly_continuous center (ρ j) (hDisk j) i
  have hVval (j : ℕ) (r : ℝ) (hr : r ∈ radialDomain R) (i : Fin 6)
      (z : Disk center (ρ j)) : V j r i z = W r z i :=
    fieldDiskCurve_apply R hR W hW.jointly_continuous center (ρ j) (hDisk j)
      (radialDomain_subset_Icc R hr) i z
  have hDval (j : ℕ) (r : ℝ) (hr : r ∈ radialDomain R) (i : Fin 6)
      (z : Disk center (ρ j)) :
      D j (V (j + 1) r i) z = deriv (fun w : ℂ => W r w i) z := by
    have hd := (hW.parameter_holomorphic r (radialDomain_subset_Icc R hr) i).mono (hDisk (j + 1))
    exact CauchyRestriction.derivativeCLM_apply_of_eq center (hρ j) (V (j + 1) r i)
      (fun w : ℂ => W r w i)
      (DiffContOnCl.mk_ball (hd.mono Metric.ball_subset_closedBall) hd.continuousOn)
      (hVval (j + 1) r hr i) z
  let g := fun j r i => b j r i + ∑ k, a₀ j r i k * V j r k +
    ∑ k, a₁ j r i k * D j (V (j + 1) r k)
  have hgcont (j : ℕ) (i : Fin 6) : ContinuousOn (fun r => g j r i) (radialDomain R) := by
    apply ContinuousOn.add
    · exact (hb j i).continuousOn.add (continuousOn_finsetSum _
        (fun k _ => (ha₀ j i k).continuousOn.mul (hV j k).continuousOn))
    · exact continuousOn_finsetSum _ (fun k _ => (ha₁ j i k).continuousOn.mul
        ((D j).continuous.comp (hV (j + 1) k)).continuousOn)
  have hgval (j : ℕ) (r : ℝ) (hr : r ∈ radialDomain R) (i : Fin 6)
      (z : Disk center (ρ j)) : g j r i z = NilpotentVolterra.equationRHS A₀ A₁ f W r z i := by
    simp only [g, ContinuousMap.add_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
      NilpotentVolterra.equationRHS, matrixAction, parameterDeriv, Pi.add_apply,
      Matrix.mulVec, dotProduct]
    simp only [hbval j r hr, ha₀val j r hr, ha₁val j r hr, hVval j r hr, hDval j r hr,
      add_assoc]
  apply algebraScale_contDiffOn exponent V b a₀ a₁ D
    (fun j i => (hV j i).continuousOn) hb ha₀ ha₁
  intro j i r hr
  apply ContinuousMap.ext
  intro z
  rw [regularPrimitive_evaluate (exponent i) (hgcont j i) hr z]
  have hraw := congrArg (fun v : VolterraAnalyticBounds.Vec => v i)
    (hW.integral_equation r (radialDomain_subset_Icc R hr) z (hDisk j z.property))
  change W r z i = regularPrimitive (exponent i)
    (fun s => NilpotentVolterra.equationRHS A₀ A₁ f W s z i) r at hraw
  exact (hVval j r hr i z).trans (hraw.trans
    (regularPrimitive_eq_of_eqOn (exponent i) (fun s hs => (hgval j s hs i z).symm) hr))

end ActualField

section ParameterJets

open CauchyRestriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Iterated Cauchy differentiation spends one disk gap at each step. -/
noncomputable def cauchyJetCurve (center : ℂ) (ρ : ℕ → ℝ)
    (hρ : ∀ j, ρ j < ρ (j + 1))
    (V : ∀ j, ℝ → C(Disk center (ρ j), E)) :
    ℕ → ∀ j, ℝ → C(Disk center (ρ j), E)
  | 0, j, r => V j r
  | k + 1, j, r => CauchyRestriction.derivativeCLM center (hρ j)
      (cauchyJetCurve center ρ hρ V k (j + 1) r)

omit [CompleteSpace E] in
theorem cauchyJetCurve_contDiffOn (center : ℂ) (ρ : ℕ → ℝ)
    (hρ : ∀ j, ρ j < ρ (j + 1))
    (V : ∀ j, ℝ → C(Disk center (ρ j), E)) {S : Set ℝ} {n : WithTop ℕ∞}
    (hV : ∀ j, ContDiffOn ℝ n (V j) S) :
    ∀ k j, ContDiffOn ℝ n (cauchyJetCurve center ρ hρ V k j) S := by
  intro k
  induction k with
  | zero => exact hV
  | succ k ih =>
      intro j
      exact ((CauchyRestriction.derivativeCLM (E := E) center (hρ j)).restrictScalars
        ℝ).contDiff.comp_contDiffOn (ih (j + 1))

theorem holomorphic_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) {F : ℂ → E}
    (hF : DifferentiableOn ℂ F U) (k : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv k F) U := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv hU

/-- On holomorphic data the iterated bounded operators are the actual
iterated complex derivatives, at every point of the smaller closed disk. -/
theorem cauchyJetCurve_apply_of_eq (center : ℂ) (ρ : ℕ → ℝ)
    (hρ : ∀ j, ρ j < ρ (j + 1))
    (V : ∀ j, ℝ → C(Disk center (ρ j), E)) {S : Set ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hDisk : ∀ j, Metric.closedBall center (ρ j) ⊆ U)
    (F : ℝ → ℂ → E) (hF : ∀ r ∈ S, DifferentiableOn ℂ (F r) U)
    (hV : ∀ j r, r ∈ S → ∀ z : Disk center (ρ j), V j r z = F r z) :
    ∀ k j r, r ∈ S → ∀ z : Disk center (ρ j),
      cauchyJetCurve center ρ hρ V k j r z = iteratedDeriv k (F r) z := by
  intro k
  induction k with
  | zero => simpa only [cauchyJetCurve, iteratedDeriv_zero] using hV
  | succ k ih =>
      intro j r hr z
      have hd := (holomorphic_iteratedDeriv hU (hF r hr) k).mono (hDisk (j + 1))
      simpa only [cauchyJetCurve, iteratedDeriv_succ] using
        CauchyRestriction.derivativeCLM_apply_of_eq center (hρ j)
        (cauchyJetCurve center ρ hρ V k (j + 1) r) (iteratedDeriv k (F r))
        (DiffContOnCl.mk_ball (hd.mono Metric.ball_subset_closedBall) hd.continuousOn)
        (ih (j + 1) r hr) z

/-- All parameter jets are smooth functions of the real radial variable.
The assertion follows from bounded operators and does not posit mixed
regularity of the original field. -/
theorem parameterJets_radial_contDiffOn (center : ℂ) (ρ : ℕ → ℝ)
    (hρ : ∀ j, ρ j < ρ (j + 1))
    (V : ∀ j, ℝ → C(Disk center (ρ j), E)) {S : Set ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hDisk : ∀ j, Metric.closedBall center (ρ j) ⊆ U)
    (F : ℝ → ℂ → E) (hF : ∀ r ∈ S, DifferentiableOn ℂ (F r) U)
    (hV : ∀ j r, r ∈ S → ∀ z : Disk center (ρ j), V j r z = F r z)
    (hs : ∀ j, ContDiffOn ℝ ∞ (V j) S) (k j : ℕ) (z : Disk center (ρ j)) :
    ContDiffOn ℝ ∞ (fun r => iteratedDeriv k (F r) z) S := by
  apply ((ContinuousMap.evalCLM ℝ z).contDiff.comp_contDiffOn
    (cauchyJetCurve_contDiffOn center ρ hρ V hs k j)).congr
  intro r hr
  exact (cauchyJetCurve_apply_of_eq center ρ hρ V hU hDisk F hF hV k j r hr z).symm

theorem real_iteratedDeriv_contDiffOn {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set ℝ} (hS : IsOpen S) {f : ℝ → G} (hf : ContDiffOn ℝ ∞ f S) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n f) S := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen hS (by simp)

omit [CompleteSpace E] in
/-- Evaluation of a smooth compact-function curve commutes with every
fixed radial derivative. -/
theorem iteratedDeriv_evaluate {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {S : Set ℝ} (hS : IsOpen S) {f : ℝ → C(K, E)} (hf : ContDiffOn ℝ ∞ f S)
    {r : ℝ} (hr : r ∈ S) (n : ℕ) (z : K) :
    iteratedDeriv n f r z = iteratedDeriv n (fun s => f s z) r := by
  let ev : C(K, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ z
  have hcomp := ev.iteratedFDerivWithin_comp_left (hf r hr) hS.uniqueDiffOn hr
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hv := congrArg (fun L : ℝ [×n]→L[ℝ] E => L (fun _ => 1)) hcomp.symm
  change (iteratedFDerivWithin ℝ n f S r (fun _ => 1)) z =
    iteratedFDerivWithin ℝ n (fun s => f s z) S r (fun _ => 1) at hv
  simpa only [iteratedFDerivWithin_of_isOpen n hS hr,
    ← iteratedDeriv_eq_iteratedFDeriv] using hv

/-- Compact radial subintervals have uniform bounds for each fixed mixed
derivative on the full inner parameter disk. Constants may depend on both
derivative orders; no radial analyticity estimate is asserted. -/
theorem parameterJets_uniform_mixed_bound (center : ℂ) (ρ : ℕ → ℝ)
    (hρ : ∀ j, ρ j < ρ (j + 1))
    (V : ∀ j, ℝ → C(Disk center (ρ j), E)) {S : Set ℝ} (hS : IsOpen S) {U : Set ℂ}
    (hU : IsOpen U) (hDisk : ∀ j, Metric.closedBall center (ρ j) ⊆ U)
    (F : ℝ → ℂ → E) (hF : ∀ r ∈ S, DifferentiableOn ℂ (F r) U)
    (hV : ∀ j r, r ∈ S → ∀ z : Disk center (ρ j), V j r z = F r z)
    (hs : ∀ j, ContDiffOn ℝ ∞ (V j) S)
    {K : Set ℝ} (hK : IsCompact K) (hKS : K ⊆ S) (n k j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ K, ∀ z : Disk center (ρ j),
      ‖iteratedDeriv n (fun s => iteratedDeriv k (F s) z) r‖ ≤ B := by
  let G := cauchyJetCurve center ρ hρ V k j
  have hG : ContDiffOn ℝ ∞ G S := cauchyJetCurve_contDiffOn center ρ hρ V hs k j
  have hdG := real_iteratedDeriv_contDiffOn hS hG n
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hdG.continuousOn.mono hKS)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro r hr z
  have heq : EqOn (fun s => G s z) (fun s => iteratedDeriv k (F s) z) S := by
    intro s hs'
    exact cauchyJetCurve_apply_of_eq center ρ hρ V hU hDisk F hF hV k j s hs' z
  have hv := iteratedDeriv_evaluate hS hG (hKS hr) n z
  have hactual := heq.iteratedDeriv_of_isOpen hS n (hKS hr)
  rw [← hactual, ← hv]
  exact ((iteratedDeriv n G r).norm_coe_le_norm z).trans ((hB r hr).trans (le_max_left _ _))

end ParameterJets

section SmoothInputs

open VolterraAnalyticBounds CauchyRestriction CompactSmoothFamily

/-- Regularity assumptions on the input coefficients only. The forcing
and all matrix entries are jointly smooth in the real radial variable
and the two real coordinates of the complex parameter. -/
structure SmoothCoefficientData (R : ℝ) (U : Set ℂ)
    (A₀ A₁ : Coeff) (f : Field) : Prop where
  forcing : ∀ i, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => f p.1 p.2 i) (radialDomain R ×ˢ U)
  zeroth : ∀ i k, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => A₀ p.1 p.2 i k) (radialDomain R ×ˢ U)
  first : ∀ i k, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => A₁ p.1 p.2 i k) (radialDomain R ×ˢ U)

/-- The smooth disk-valued inputs required by the bootstrap are constructed
from the actual jointly smooth coefficient entries. -/
theorem symmetric_solution_disk_curves_of_smooth_coefficients
    {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Coeff} {f W : Field}
    (hW : VolterraParity.IsSymmetricIntegralSolution R U A₀ A₁ f W)
    (hdata : SmoothCoefficientData R U A₀ A₁ f)
    (center : ℂ) (ρ : ℕ → ℝ) (hρ : ∀ j, ρ j < ρ (j + 1))
    (hDisk : ∀ j, Metric.closedBall center (ρ j) ⊆ U) :
    ∀ j i, ContDiffOn ℝ ∞
      (fun r => fieldDiskCurve R hR W hW.jointly_continuous center (ρ j) (hDisk j) r i)
      (radialDomain R) := by
  let b := fun j r i => CompactSmoothFamily.family (Metric.closedBall center (ρ j))
    (fun p : ℝ × ℂ => f p.1 p.2 i) r
  let a₀ := fun j r i k => CompactSmoothFamily.family (Metric.closedBall center (ρ j))
    (fun p : ℝ × ℂ => A₀ p.1 p.2 i k) r
  let a₁ := fun j r i k => CompactSmoothFamily.family (Metric.closedBall center (ρ j))
    (fun p : ℝ × ℂ => A₁ p.1 p.2 i k) r
  apply symmetric_solution_disk_curves_contDiffOn hR hW center ρ hρ hDisk b a₀ a₁
  · intro j i
    exact contDiffOn_family_of_joint _ _ _ Metric.isOpen_ball hU (hDisk j) _ (hdata.forcing i)
  · intro j i k
    exact contDiffOn_family_of_joint _ _ _ Metric.isOpen_ball hU (hDisk j) _ (hdata.zeroth i k)
  · intro j i k
    exact contDiffOn_family_of_joint _ _ _ Metric.isOpen_ball hU (hDisk j) _ (hdata.first i k)
  · intro j r hr i z
    exact family_apply_of_joint _ (hDisk j) _ (hdata.forcing i).continuousOn hr z
  · intro j r hr i k z
    exact family_apply_of_joint _ (hDisk j) _ (hdata.zeroth i k).continuousOn hr z
  · intro j r hr i k z
    exact family_apply_of_joint _ (hDisk j) _ (hdata.first i k).continuousOn hr z

/-- Every fixed complex parameter derivative of the actual symmetric
solution is real smooth through the radial origin. -/
theorem symmetric_solution_parameterJets_radial_contDiffOn
    {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Coeff} {f W : Field}
    (hW : VolterraParity.IsSymmetricIntegralSolution R U A₀ A₁ f W)
    (hdata : SmoothCoefficientData R U A₀ A₁ f)
    (center : ℂ) (ρ : ℕ → ℝ) (hρ : ∀ j, ρ j < ρ (j + 1))
    (hDisk : ∀ j, Metric.closedBall center (ρ j) ⊆ U)
    (k j : ℕ) (i : Fin 6) (z : Disk center (ρ j)) :
    ContDiffOn ℝ ∞ (fun r => iteratedDeriv k (fun w : ℂ => W r w i) z)
      (radialDomain R) := by
  let V := fun j r => fieldDiskCurve R hR W hW.jointly_continuous center (ρ j) (hDisk j) r i
  apply parameterJets_radial_contDiffOn center ρ hρ V hU hDisk (fun r w => W r w i)
  · intro r hr
    exact hW.parameter_holomorphic r (radialDomain_subset_Icc R hr) i
  · intro j r hr z
    exact fieldDiskCurve_apply R hR W hW.jointly_continuous center (ρ j) (hDisk j)
      (radialDomain_subset_Icc R hr) i z
  · intro j
    exact symmetric_solution_disk_curves_of_smooth_coefficients hR hU hW hdata
      center ρ hρ hDisk j i

/-- An explicit sequence of interior radii, with infinitely many positive
gaps before the boundary of the available parameter neighborhood. -/
noncomputable def interiorRadii (δ : ℝ) (j : ℕ) : ℝ := δ - δ / ((j : ℝ) + 2)

theorem interiorRadii_pos {δ : ℝ} (hδ : 0 < δ) (j : ℕ) : 0 < interiorRadii δ j := by
  apply sub_pos.mpr
  apply (div_lt_iff₀ (by positivity : 0 < (j : ℝ) + 2)).mpr
  have hp : 0 ≤ δ * (j : ℝ) := mul_nonneg hδ.le (Nat.cast_nonneg j)
  nlinarith

theorem interiorRadii_lt {δ : ℝ} (hδ : 0 < δ) (j : ℕ) : interiorRadii δ j < δ := by
  exact sub_lt_self _ (div_pos hδ (by positivity))

theorem interiorRadii_increasing {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    interiorRadii δ j < interiorRadii δ (j + 1) := by
  have hdiv : δ / (((j + 1 : ℕ) : ℝ) + 2) < δ / ((j : ℝ) + 2) := by
    apply div_lt_div_of_pos_left hδ (by positivity)
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  exact sub_lt_sub_left hdiv δ

theorem interiorRadii_subset {δ : ℝ} (hδ : 0 < δ) (center : ℂ) {U : Set ℂ}
    (hball : Metric.ball center δ ⊆ U) (j : ℕ) :
    Metric.closedBall center (interiorRadii δ j) ⊆ U :=
  (Metric.closedBall_subset_ball (interiorRadii_lt hδ j)).trans hball

/-- The nested disks can always be selected inside an open parameter
domain. Thus every actual parameter jet is radially smooth at every
parameter point, with no auxiliary disk-family hypothesis. -/
theorem symmetric_solution_parameterJets_radial_contDiffOn_local
    {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Coeff} {f W : Field}
    (hW : VolterraParity.IsSymmetricIntegralSolution R U A₀ A₁ f W)
    (hdata : SmoothCoefficientData R U A₀ A₁ f)
    {z : ℂ} (hz : z ∈ U) (k : ℕ) (i : Fin 6) :
    ContDiffOn ℝ ∞ (fun r => iteratedDeriv k (fun w : ℂ => W r w i) z)
      (radialDomain R) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let z₀ : Disk z (interiorRadii δ 0) :=
    ⟨z, Metric.mem_closedBall_self (interiorRadii_pos hδ 0).le⟩
  exact symmetric_solution_parameterJets_radial_contDiffOn hR hU hW hdata z
    (interiorRadii δ) (interiorRadii_increasing hδ) (interiorRadii_subset hδ z hball) k 0 i z₀

/-- All fixed mixed derivatives of the constructed field exist smoothly
through the real radial origin. The order of operations here is parameter
differentiation followed by radial differentiation. -/
theorem symmetric_solution_mixed_contDiffOn
    {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Coeff} {f W : Field}
    (hW : VolterraParity.IsSymmetricIntegralSolution R U A₀ A₁ f W)
    (hdata : SmoothCoefficientData R U A₀ A₁ f)
    {z : ℂ} (hz : z ∈ U) (n k : ℕ) (i : Fin 6) :
    ContDiffOn ℝ ∞
      (iteratedDeriv n (fun r => iteratedDeriv k (fun w : ℂ => W r w i) z))
      (radialDomain R) :=
  real_iteratedDeriv_contDiffOn Metric.isOpen_ball
    (symmetric_solution_parameterJets_radial_contDiffOn_local hR hU hW hdata hz k i) n

theorem symmetric_solution_mixed_contDiffAt_zero
    {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Coeff} {f W : Field}
    (hW : VolterraParity.IsSymmetricIntegralSolution R U A₀ A₁ f W)
    (hdata : SmoothCoefficientData R U A₀ A₁ f)
    {z : ℂ} (hz : z ∈ U) (n k : ℕ) (i : Fin 6) :
    ContDiffAt ℝ ∞
      (iteratedDeriv n (fun r => iteratedDeriv k (fun w : ℂ => W r w i) z)) 0 :=
  (symmetric_solution_mixed_contDiffOn hR.le hU hW hdata hz n k i).contDiffAt
    (Metric.ball_mem_nhds 0 hR)

theorem symmetric_solution_radial_contDiffOn
    {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Coeff} {f W : Field}
    (hW : VolterraParity.IsSymmetricIntegralSolution R U A₀ A₁ f W)
    (hdata : SmoothCoefficientData R U A₀ A₁ f)
    {z : ℂ} (hz : z ∈ U) :
    ContDiffOn ℝ ∞ (fun r => W r z) (radialDomain R) := by
  apply contDiffOn_pi.mpr
  intro i
  simpa only [iteratedDeriv_zero] using
    symmetric_solution_parameterJets_radial_contDiffOn_local hR hU hW hdata hz 0 i

theorem symmetric_solution_uniform_mixed_bound
    {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Coeff} {f W : Field}
    (hW : VolterraParity.IsSymmetricIntegralSolution R U A₀ A₁ f W)
    (hdata : SmoothCoefficientData R U A₀ A₁ f)
    (center : ℂ) (ρ : ℕ → ℝ) (hρ : ∀ j, ρ j < ρ (j + 1))
    (hDisk : ∀ j, Metric.closedBall center (ρ j) ⊆ U)
    {K : Set ℝ} (hK : IsCompact K) (hKR : K ⊆ radialDomain R)
    (n k j : ℕ) (i : Fin 6) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ K, ∀ z : Disk center (ρ j),
      ‖iteratedDeriv n (fun s => iteratedDeriv k (fun w : ℂ => W s w i) z) r‖ ≤ B := by
  let V := fun j r => fieldDiskCurve R hR W hW.jointly_continuous center (ρ j) (hDisk j) r i
  apply parameterJets_uniform_mixed_bound center ρ hρ V Metric.isOpen_ball hU hDisk
    (fun r w => W r w i)
  · intro r hr
    exact hW.parameter_holomorphic r (radialDomain_subset_Icc R hr) i
  · intro j r hr z
    exact fieldDiskCurve_apply R hR W hW.jointly_continuous center (ρ j) (hDisk j)
      (radialDomain_subset_Icc R hr) i z
  · intro j
    exact symmetric_solution_disk_curves_of_smooth_coefficients hR hU hW hdata
      center ρ hρ hDisk j i
  · exact hK
  · exact hKR

/-- Direct specialization to the two-sided solution constructed from the
convergent nilpotent Volterra series. No regularity of that output is an
input to this theorem. -/
theorem symmetricSolution_mixed_contDiffOn
    {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → VolterraParity.SymmetricCoefficientPath R}
    {f : ℂ → VolterraParity.SymmetricPath R VolterraAnalyticBounds.Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (VolterraParity.symmetricRawCoefficient hR A₁))
    (hdata : SmoothCoefficientData R U (VolterraParity.symmetricRawCoefficient hR A₀)
      (VolterraParity.symmetricRawCoefficient hR A₁) (VolterraParity.symmetricRawField hR f))
    {z : ℂ} (hz : z ∈ U) (n k : ℕ) (i : Fin 6) :
    ContDiffOn ℝ ∞
      (iteratedDeriv n (fun r => iteratedDeriv k
        (fun w : ℂ => VolterraParity.symmetricSolution hR A₀ A₁ f r w i) z))
      (radialDomain R) :=
  symmetric_solution_mixed_contDiffOn hR hU
    (VolterraParity.symmetricSolution_spec hR hU hA₀ hA₁ hf hshape) hdata hz n k i

theorem symmetricSolution_mixed_contDiffAt_zero
    {R : ℝ} (hR : 0 < R)
    {A₀ A₁ : ℂ → VolterraParity.SymmetricCoefficientPath R}
    {f : ℂ → VolterraParity.SymmetricPath R VolterraAnalyticBounds.Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (VolterraParity.symmetricRawCoefficient hR.le A₁))
    (hdata : SmoothCoefficientData R U (VolterraParity.symmetricRawCoefficient hR.le A₀)
      (VolterraParity.symmetricRawCoefficient hR.le A₁) (VolterraParity.symmetricRawField hR.le f))
    {z : ℂ} (hz : z ∈ U) (n k : ℕ) (i : Fin 6) :
    ContDiffAt ℝ ∞
      (iteratedDeriv n (fun r => iteratedDeriv k
        (fun w : ℂ => VolterraParity.symmetricSolution hR.le A₀ A₁ f r w i) z)) 0 :=
  symmetric_solution_mixed_contDiffAt_zero hR hU
    (VolterraParity.symmetricSolution_spec hR.le hU hA₀ hA₁ hf hshape) hdata hz n k i

end SmoothInputs

end NavierStokes.VolterraRegularity

end
