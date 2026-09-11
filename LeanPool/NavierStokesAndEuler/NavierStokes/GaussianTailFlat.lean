/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.GaussianEnvelope
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalGraphBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothCutoffs
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The actual Gaussian slot-cutoff errors

The profile is a constructed smooth bump, with the plateau and support radii
from Section 8.2.  No error field is set to zero: local vanishing on the plateau,
the Gaussian bound off that plateau, and higher Leibniz estimates are used.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.GaussianTailFlat

open Set Filter Function
open scoped ContDiff Topology BigOperators

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

/-- The fixed profile has plateau radius `1/5` and support radius `1/3`. -/
noncomputable def profileBump : ContDiffBump (1 / 2 : ℝ) where
  rIn := 1 / 5
  rOut := 1 / 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Profile, given by `profileBump`. -/
noncomputable def profile : ℝ → ℝ := profileBump

theorem profile_contDiff : ContDiff ℝ ∞ profile := profileBump.contDiff

theorem profile_mem_Icc (v : ℝ) : profile v ∈ Icc (0 : ℝ) 1 :=
  ⟨profileBump.nonneg, profileBump.le_one⟩

theorem profile_one {v : ℝ} (hv : |v - 1 / 2| ≤ 1 / 5) : profile v = 1 := by
  apply profileBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, profileBump] using hv

theorem profile_zero {v : ℝ} (hv : 1 / 3 ≤ |v - 1 / 2|) : profile v = 0 := by
  apply profileBump.zero_of_le_dist
  simpa [Real.dist_eq, profileBump] using hv

theorem profile_eventually_one {v : ℝ} (hv : |v - 1 / 2| < 1 / 5) :
    profile =ᶠ[𝓝 v] fun _ => 1 := by
  apply profileBump.eventuallyEq_one_of_mem_ball
  simpa [Metric.mem_ball, Real.dist_eq, profileBump] using hv

theorem profile_eventually_zero {v : ℝ} (hv : 1 / 3 < |v - 1 / 2|) :
    profile =ᶠ[𝓝 v] fun _ => 0 := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  change v ∉ tsupport (profileBump : ℝ → ℝ)
  rw [profileBump.tsupport_eq]
  simpa [Metric.mem_closedBall, Real.dist_eq, profileBump] using (not_le.mpr hv)

theorem profile_iteratedDeriv_support (m : ℕ) :
    support (iteratedDeriv (m + 1) profile) ⊆
      {v : ℝ | 1 / 5 ≤ |v - 1 / 2| ∧ |v - 1 / 2| ≤ 1 / 3} := by
  intro v hv
  change iteratedDeriv (m + 1) profile v ≠ 0 at hv
  constructor
  · by_contra h
    apply hv
    rw [(profile_eventually_one (lt_of_not_ge h)).iteratedDeriv_eq (m + 1),
      SmoothCutoffs.iteratedDeriv_const_succ]
  · by_contra h
    apply hv
    rw [(profile_eventually_zero (lt_of_not_ge h)).iteratedDeriv_eq (m + 1),
      SmoothCutoffs.iteratedDeriv_const_succ]

theorem profile_iteratedDeriv_compact (m : ℕ) :
    HasCompactSupport (iteratedDeriv m profile) := by
  induction m with
  | zero => exact profileBump.hasCompactSupport
  | succ m ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem profile_jet_bounded (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ‖iteratedFDeriv ℝ m profile v‖ ≤ C := by
  obtain ⟨C, hC⟩ := (profile_iteratedDeriv_compact m).exists_bound_of_continuous
    (profile_contDiff.continuous_iteratedDeriv m (nat_le_infty m))
  refine ⟨max C 0, le_max_right _ _, fun v => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hC v).trans (le_max_left _ _)

/-- Slot cutoff, given by `profile (v / L)`. -/
noncomputable def slotCutoff (L : ℝ) (v : ℝ) : ℝ := profile (v / L)

theorem slotCutoff_contDiff (L : ℝ) : ContDiff ℝ ∞ (slotCutoff L) :=
  profile_contDiff.comp (contDiff_id.div_const L)

theorem slotCutoff_deriv (L v : ℝ) :
    deriv (slotCutoff L) v = L⁻¹ * deriv profile (v / L) := by
  have hp := (profile_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
    (x := v / L)
  have hh := hp.comp v ((hasDerivAt_id v).div_const L)
  unfold slotCutoff
  simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using hh.deriv

theorem slot_normalized_distance {L : ℝ} (hL : 0 < L) (v : ℝ) :
    |v / L - 1 / 2| = |v - L / 2| / L := by
  have he : v / L - 1 / 2 = (v - L / 2) / L := by
    apply (eq_div_iff hL.ne').2
    rw [sub_mul, div_mul_cancel₀ _ hL.ne']
    ring
  rw [he, abs_div, abs_of_pos hL]

theorem slotCutoff_one {L v : ℝ} (hL : 0 < L) (hv : |v - L / 2| ≤ L / 5) :
    slotCutoff L v = 1 := by
  apply profile_one
  rw [slot_normalized_distance hL]
  apply (div_le_iff₀ hL).2
  linarith

theorem slotCutoff_zero {L v : ℝ} (hL : 0 < L) (hv : L / 3 ≤ |v - L / 2|) :
    slotCutoff L v = 0 := by
  apply profile_zero
  rw [slot_normalized_distance hL]
  apply (le_div_iff₀ hL).2
  linarith

/-- The derivative error is supported strictly inside the slot and outside
the central plateau; in particular it lies near the entry or exit. -/
theorem slotCutoff_deriv_support {L v : ℝ} (hL : 0 < L)
    (hv : deriv (slotCutoff L) v ≠ 0) :
    L / 5 ≤ |v - L / 2| ∧ |v - L / 2| ≤ L / 3 := by
  have hd : deriv profile (v / L) ≠ 0 := by
    intro hz
    exact hv (by rw [slotCutoff_deriv, hz, mul_zero])
  have hh := profile_iteratedDeriv_support 0 (by simpa using hd)
  change 1 / 5 ≤ |v / L - 1 / 2| ∧ |v / L - 1 / 2| ≤ 1 / 3 at hh
  rw [slot_normalized_distance hL] at hh
  constructor
  · have ht := (le_div_iff₀ hL).1 hh.1
    linarith
  · have ht := (div_le_iff₀ hL).1 hh.2
    linarith

/-- The precise Gaussian tail bound uses the full plateau radius. -/
theorem gaussian_off_plateau {c L v : ℝ} (hc : 0 ≤ c) (hL : 0 < L)
    (hv : L / 5 ≤ |v - L / 2|) :
    Real.exp (-c * (v - L / 2) ^ 2 / L) ≤ Real.exp (-(c / 25) * L) := by
  have hsq : (L / 5) ^ 2 ≤ (v - L / 2) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (by positivity : 0 ≤ L / 5) hv 2
  apply Real.exp_le_exp.2
  apply (div_le_iff₀ hL).2
  linarith [mul_le_mul_of_nonneg_left hsq hc]

theorem reference_envelope_off_plateau {lam u L v : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L) (hv : v ∈ Icc 0 L)
    (htail : L / 5 ≤ |v - L / 2|) :
    GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u L) (L / 2) v ≤
      Real.exp (-(u * GaussianEnvelope.referenceMinSlope lam u / 50) * L) := by
  have h := (GaussianEnvelope.reference_gaussian_bounds hlam hu hL hv).2
  have hc := GaussianEnvelope.referenceMinSlope_pos hlam hu
  have hg := gaussian_off_plateau
    (c := u * GaussianEnvelope.referenceMinSlope lam u / 2) (by positivity) hL htail
  have he : -(u * GaussianEnvelope.referenceMinSlope lam u / 2) *
      (v - L / 2) ^ 2 / L =
      -(u * GaussianEnvelope.referenceMinSlope lam u) * (v - L / 2) ^ 2 / (2 * L) := by ring
  rw [he] at hg
  convert! h.trans hg using 1
  congr 1
  ring

/-- The square root of the actual flat edge is another member of that family. -/
theorem sqrt_edge (c x : ℝ) : Real.sqrt (FlatCutoff.edge c x) = FlatCutoff.edge (c / 2) x := by
  by_cases hx : x ≤ 0
  · simp [FlatCutoff.edge_of_nonpos _ hx]
  · rw [FlatCutoff.edge_of_pos _ (lt_of_not_ge hx),
      FlatCutoff.edge_of_pos _ (lt_of_not_ge hx)]
    rw [← Real.exp_half]
    congr 1
    ring

theorem sqrt_zeta (cL cR R x : ℝ) :
    Real.sqrt (WeightedRadialPrimitive.zeta cL cR R x) =
      WeightedRadialPrimitive.zeta (cL / 2) (cR / 2) R x := by
  rw [WeightedRadialPrimitive.zeta, Real.sqrt_mul (FlatCutoff.edge_nonneg _ _),
    sqrt_edge, sqrt_edge]
  rfl

/-- A single constant covers the entire slow shell, including approach to
either edge.  This is derived from the constructed `FlatCutoff.edge`. -/
theorem sqrt_zeta_inverse_power_bounded {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (R : ℝ) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioo (0 : ℝ) R,
      Real.sqrt (WeightedRadialPrimitive.zeta cL cR R x) *
        (max 1 (WeightedRadialPrimitive.delta R x)⁻¹) ^ k ≤ C := by
  obtain ⟨C, hC, hb⟩ := WeightedRadialPrimitive.weight_uniform_bound
    (cL := cL / 2) (cR := cR / 2)
    (div_pos hcL (by norm_num)) (div_pos hcR (by norm_num)) R k
  refine ⟨C, hC, fun x hx => ?_⟩
  have hd := WeightedRadialPrimitive.delta_pos hx
  have hm : (1 : ℝ) ≤ (WeightedRadialPrimitive.delta R x)⁻¹ :=
    (one_le_inv₀ hd).2 (WeightedRadialPrimitive.delta_le_one R x)
  rw [max_eq_right hm, sqrt_zeta]
  simpa only [WeightedRadialPrimitive.weight, div_eq_mul_inv, inv_pow] using hb x hx

/-! ## Exponential decay along the actual bands -/

/-- An elementary global bound, including the finite initial part of a sequence. -/
theorem polynomial_exp_bound {c : ℝ} (hc : 0 < c) (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ p * Real.exp (-c * x) ≤
      ((p.factorial : ℝ) / c ^ p) * Real.exp c := by
  have hfac : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  have hb := (div_le_iff₀ hfac).1
    (Real.pow_div_factorial_le_exp (c * (1 + x))
      (mul_nonneg hc.le (by linarith : 0 ≤ 1 + x)) p)
  have hp : 0 < c ^ p := pow_pos hc p
  calc
    _ = ((c * (1 + x)) ^ p / c ^ p) * Real.exp (-c * x) := by
      rw [mul_pow, mul_div_cancel_left₀ _ (ne_of_gt hp)]
    _ ≤ ((Real.exp (c * (1 + x)) * p.factorial) / c ^ p) * Real.exp (-c * x) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hp.le) (Real.exp_pos _).le
    _ = ((p.factorial : ℝ) / c ^ p) *
        (Real.exp (c * (1 + x)) * Real.exp (-c * x)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem Q_rpow_eq_exp (N : ℝ) (n : ℕ) :
    ChartScales.Q n ^ N = Real.exp (-(N * Real.log 2) * (n : ℝ)) := by
  unfold ChartScales.Q SlotColoring.dyadicQ
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- Every polynomial in `S=n²` times a Gaussian tail is bounded by every
real power of the actual dyadic `Q=2⁻ⁿ`. No asymptotic surrogate is used. -/
theorem gaussian_beats_Q_power {c : ℝ} (hc : 0 < c) (p : ℕ) (N : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (1 + ChartScales.S n) ^ p * Real.exp (-c * ChartScales.S n) ≤
        C * ChartScales.Q n ^ N := by
  let A : ℝ := N * Real.log 2
  let K : ℝ := A ^ 2 / (2 * c)
  let B : ℝ := ((p.factorial : ℝ) / (c / 2) ^ p) * Real.exp (c / 2)
  refine ⟨B * Real.exp K, by dsimp [B]; positivity, ?_⟩
  intro n
  have hlin : A * (n : ℝ) ≤ c / 2 * (n : ℝ) ^ 2 + K := by
    have hs := sq_nonneg (c * (n : ℝ) - A)
    have hc2 : 0 < 2 * c := by positivity
    suffices A * (n : ℝ) - c / 2 * (n : ℝ) ^ 2 ≤ K by linarith
    dsimp [K]
    apply (le_div_iff₀ hc2).2
    linarith
  have hexp : Real.exp (-c * ChartScales.S n) ≤
      Real.exp (-(c / 2) * ChartScales.S n) * Real.exp K * ChartScales.Q n ^ N := by
    rw [Q_rpow_eq_exp, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    dsimp [ChartScales.S, A] at *
    linarith
  calc
    _ ≤ (1 + ChartScales.S n) ^ p *
        (Real.exp (-(c / 2) * ChartScales.S n) * Real.exp K * ChartScales.Q n ^ N) :=
      mul_le_mul_of_nonneg_left hexp (by unfold ChartScales.S; positivity)
    _ = ((1 + ChartScales.S n) ^ p * Real.exp (-(c / 2) * ChartScales.S n)) *
        Real.exp K * ChartScales.Q n ^ N := by ring
    _ ≤ B * Real.exp K * ChartScales.Q n ^ N := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).le
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact polynomial_exp_bound (by linarith : 0 < c / 2) p (sq_nonneg (n : ℝ))
    _ = _ := by ring

theorem gaussian_length_comparison {c κ L S : ℝ} (hc : 0 ≤ c) (hL : κ * S ≤ L) :
    Real.exp (-(c / 25) * L) ≤ Real.exp (-(c * κ / 25) * S) := by
  apply Real.exp_le_exp.2
  linarith [mul_le_mul_of_nonneg_left hL hc]

/-- A fixed power loss consumes only half of a Gaussian tail. -/
theorem fixed_power_gaussian_bound {c : ℝ} (hc : 0 < c) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ChartScales.Q n ^ r * Real.exp (-c * ChartScales.S n) ≤
        C * Real.exp (-(c / 2) * ChartScales.S n) := by
  obtain ⟨C, hC, hb⟩ := gaussian_beats_Q_power (by linarith : 0 < c / 2) 0 (-r)
  refine ⟨C, hC, fun n => ?_⟩
  have he : Real.exp (-c * ChartScales.S n) =
      Real.exp (-(c / 2) * ChartScales.S n) * Real.exp (-(c / 2) * ChartScales.S n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hb' : Real.exp (-(c / 2) * ChartScales.S n) ≤ C * ChartScales.Q n ^ (-r) := by
    simpa only [pow_zero, one_mul] using hb n
  have hQ := ChartScales.Q_pos n
  calc
    _ = (ChartScales.Q n ^ r * Real.exp (-(c / 2) * ChartScales.S n)) *
        Real.exp (-(c / 2) * ChartScales.S n) := by rw [he]; ring
    _ ≤ (ChartScales.Q n ^ r * (C * ChartScales.Q n ^ (-r))) *
        Real.exp (-(c / 2) * ChartScales.S n) := by gcongr
    _ = _ := by
      rw [show ChartScales.Q n ^ r * (C * ChartScales.Q n ^ (-r)) =
        C * (ChartScales.Q n ^ r * ChartScales.Q n ^ (-r)) by ring,
        ← Real.rpow_add hQ, add_neg_cancel, Real.rpow_zero, mul_one]

/-! ## The actual cutoff products and all their stripped derivatives -/

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_jet_bounds {g : ℝ → ℝ}
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C := by
  classical
  choose C hC hb using hb
  refine ⟨∑ j ∈ Finset.range (m + 1), C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro j hj x
  exact (hb j x).trans (Finset.single_le_sum (fun i _ => hC i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

theorem profileDeriv_contDiff : ContDiff ℝ ∞ (deriv profile) :=
  (contDiff_infty_iff_deriv.mp profile_contDiff).2

theorem profileDeriv_jet_bounded (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ m (deriv profile) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := profile_jet_bounded (m + 1)
  refine ⟨C, hC, fun x => ?_⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ'] using hb x

theorem omittedProfile_contDiff : ContDiff ℝ ∞ (fun x => 1 - profile x) :=
  contDiff_const.sub profile_contDiff

theorem omittedProfile_jet_bounded (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ m (fun y => 1 - profile y) x‖ ≤ C := by
  cases m with
  | zero =>
    refine ⟨1, zero_le_one, fun x => ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (by
      linarith [(profile_mem_Icc x).2] : 0 ≤ 1 - profile x)]
    linarith [(profile_mem_Icc x).1]
  | succ m =>
    obtain ⟨C, hC, hb⟩ := profile_jet_bounded (m + 1)
    refine ⟨C, hC, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_const_sub (Nat.succ_pos m) (1 : ℝ)]
    change ‖iteratedDeriv (m + 1) (fun y => -profile y) x‖ ≤ C
    rw [iteratedDeriv_fun_neg, norm_neg]
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hb x

theorem norm_affine_comp_jet_le {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (A : D →L[ℝ] ℝ) (b : ℝ) (x : D) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => g (b + A y)) x‖ ≤
      ‖iteratedFDeriv ℝ j g (b + A x)‖ * ‖A‖ ^ j := by
  have hh : ContDiff ℝ ∞ (fun z => g (b + z)) :=
    hg.comp (contDiff_const.add contDiff_id)
  have hd := A.iteratedFDeriv_comp_right hh x (i := j) (nat_le_infty j)
  change ‖iteratedFDeriv ℝ j ((fun z => g (b + z)) ∘ A) x‖ ≤ _
  rw [hd]
  simpa only [iteratedFDeriv_comp_add_left, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using
    (iteratedFDeriv ℝ j (fun z => g (b + z)) (A x)).norm_compContinuousLinearMap_le
      (fun _ : Fin j => A)

open WeightedClasses

/-- The offset never enters the bound. Thus translated copies have the same
constants, even when their centers differ by arbitrarily many periods. -/
theorem affine_profile_memClass (s : StripData D) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g)
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C)
    (A : ℕ → D →L[ℝ] ℝ) (b : ℕ → ℝ)
    (hA : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ, ∀ n, ‖A n‖ ≤ K * s.slow n ^ p) :
    UnweightedClass s 0 (fun n x => g (b n + A n x)) := by
  obtain ⟨K, hK, p, hA⟩ := hA
  refine ⟨fun _ _ _ => zero_le_one,
    fun n => (hg.comp (contDiff_const.add (A n).contDiff)).contDiffOn, ?_⟩
  intro m
  obtain ⟨C, hC, hb⟩ := finite_jet_bounds hb m
  refine ⟨C * K ^ m, by positivity, p * m, ?_⟩
  intro n x hx j hj
  have hgrowth := s.one_le_growth n x
  have hbase : 1 ≤ K * s.growth n x ^ p :=
    one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hgrowth)
  have hAn : ‖A n‖ ≤ K * s.growth n x ^ p :=
    (hA n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) p)
      (zero_le_one.trans hK))
  calc
    _ ≤ ‖iteratedFDeriv ℝ j g (b n + A n x)‖ * ‖A n‖ ^ j :=
      norm_affine_comp_jet_le hg (A n) (b n) x j
    _ ≤ C * (K * s.growth n x ^ p) ^ m :=
      mul_le_mul (hb j hj _) ((pow_le_pow_left₀ (norm_nonneg _) hAn j).trans
        (pow_le_pow_right₀ hbase hj)) (pow_nonneg (norm_nonneg _) _) hC
    _ = majorant s (fun _ _ => 1) 0 (C * K ^ m) (p * m) n x := by
      simp only [majorant, Real.rpow_zero, mul_one, mul_pow, ← pow_mul]
      ring

/-- The two excluded errors, retained as actual functions. `θ` is the
normalized slot coordinate `v/L`. -/
noncomputable def cutoffError (L : ℝ) (θ : D → ℝ) (u f : D → E) (x : D) : E :=
  (L⁻¹ * deriv profile (θ x)) • u x + (1 - profile (θ x)) • f x

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem cutoffError_eq_slot (L : ℝ) (v : D → ℝ) (u f : D → E) (x : D) :
    cutoffError L (fun y => v y / L) u f x =
      deriv (slotCutoff L) (v x) • u x + (1 - slotCutoff L (v x)) • f x := by
  rw [slotCutoff_deriv]
  rfl

theorem cutoffError_contDiffOn {U : Set D} (L : ℝ) {θ : D → ℝ} {u f : D → E}
    (hθ : ContDiffOn ℝ ∞ θ U) (hu : ContDiffOn ℝ ∞ u U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (cutoffError L θ u f) U := by
  exact ((contDiffOn_const.mul (profileDeriv_contDiff.comp_contDiffOn hθ)).smul hu).add
    ((contDiffOn_const.sub (profile_contDiff.comp_contDiffOn hθ)).smul hf)

omit [NormedSpace ℝ D] in
theorem cutoffError_eventually_zero (L : ℝ) {θ : D → ℝ} (u f : D → E) {x : D}
    (hθ : ContinuousAt θ x) (hx : |θ x - 1 / 2| < 1 / 5) :
    cutoffError L θ u f =ᶠ[𝓝 x] fun _ => 0 := by
  have hprofile := (profile_eventually_one hx).comp_tendsto hθ
  have hderiv := (profile_eventually_one hx).deriv.comp_tendsto hθ
  filter_upwards [hprofile, hderiv] with y hy hdy
  have hy' : profile (θ y) = 1 := by simpa using hy
  have hdy' : deriv profile (θ y) = 0 := by simpa using hdy
  simp [cutoffError, hy', hdy']

theorem cutoffError_jet_zero_on_plateau (L : ℝ) {θ : D → ℝ} (u f : D → E) {x : D}
    (hθ : ContinuousAt θ x) (hx : |θ x - 1 / 2| < 1 / 5) (j : ℕ) :
    iteratedFDeriv ℝ j (cutoffError L θ u f) x = 0 := by
  have he := cutoffError_eventually_zero L u f hθ hx
  have he' : cutoffError L θ u f =ᶠ[𝓝[univ] x] fun _ => 0 := by
    simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ, iteratedFDeriv_fun_zero, Pi.zero_apply] using
    he'.iteratedFDerivWithin_eq (𝕜 := ℝ) he.self_of_nhds j

/-- This class bound is derived by all-order Leibniz, from the actual wave
and source classes and the constructed cutoff profile. -/
theorem cutoffError_mem_wave {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    {u f : ℕ → D → E} (hu : WaveClass s P α u) (hf : WaveClass s P α f)
    (L : ℕ → ℝ) (A : ℕ → D →L[ℝ] ℝ) (b : ℕ → ℝ)
    (hA : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ, ∀ n, ‖A n‖ ≤ K * s.slow n ^ p)
    (hL : BandBound s 0 (fun n => (L n)⁻¹)) :
    WaveClass s P α (fun n => cutoffError (L n) (fun x => b n + A n x) (u n) (f n)) := by
  have hd := (affine_profile_memClass s profileDeriv_contDiff profileDeriv_jet_bounded A b
      hA).band_smul hL
  have ho := affine_profile_memClass s omittedProfile_contDiff omittedProfile_jet_bounded A b hA
  have hdu := hd.smul hu
  have hof := ho.smul hf
  have hdu' : WaveClass s P α
      (fun n x => ((L n)⁻¹ * deriv profile (b n + A n x)) • u n x) := by
    simpa only [UnweightedClass, WaveClass, zero_add, add_zero, one_mul, smul_eq_mul] using hdu
  have hof' : WaveClass s P α
      (fun n x => (1 - profile (b n + A n x)) • f n x) := by
    simpa only [UnweightedClass, WaveClass, zero_add, one_mul] using hof
  exact hdu'.add hof'

/-- A slow weight controlled by the actual two-sided exponential-flat edge.
The comparison permits additional cutoffs of size at most one. -/
structure FlatEdges (s : StripData D) where
  /-- Left decay of `FlatEdges`, of type `ℝ`. -/
  leftDecay : ℝ
  /-- Right decay of `FlatEdges`, of type `ℝ`. -/
  rightDecay : ℝ
  left_pos : 0 < leftDecay
  right_pos : 0 < rightDecay
  /-- Width of `FlatEdges`, of type `ℝ`. -/
  width : ℝ
  /-- Position of `FlatEdges`, of type `D → ℝ`. -/
  position : D → ℝ
  position_mem : ∀ x ∈ s.domain, position x ∈ Ioo 0 width
  delta_eq : ∀ x ∈ s.domain, s.delta x = WeightedRadialPrimitive.delta width (position x)
  zeta_le : ∀ x ∈ s.domain,
    s.zeta x ≤ WeightedRadialPrimitive.zeta leftDecay rightDecay width (position x)

theorem FlatEdges.uniform_weight {s : StripData D} (e : FlatEdges s) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s.domain,
      Real.sqrt (s.zeta x) * (max 1 (s.delta x)⁻¹) ^ k ≤ C := by
  obtain ⟨C, hC, hb⟩ := sqrt_zeta_inverse_power_bounded e.left_pos e.right_pos e.width k
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [e.delta_eq x hx]
  exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (e.zeta_le x hx))
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) k)).trans
      (hb (e.position x) (e.position_mem x hx))

/-- Only the actual scale identity and a polynomial slow-scale upper bound
are used. The exponent may be any real number. -/
structure BandScaleControl (s : StripData D) where
  /-- Power of `BandScaleControl`, of type `ℝ`. -/
  power : ℝ
  epsilon_eq : ∀ n, s.epsilon n = ChartScales.Q n ^ power
  /-- Bound constant of `BandScaleControl`, of type `ℝ`. -/
  boundConstant : ℝ
  constant_one_le : 1 ≤ boundConstant
  /-- Degree of `BandScaleControl`, of type `ℕ`. -/
  degree : ℕ
  slow_le : ∀ n, s.slow n ≤ boundConstant * (1 + ChartScales.S n) ^ degree

/-- Native slot data before restriction to the physical graph.  The cutoff
coordinate is affine, and no spatial derivatives of a band index occur. -/
structure SlotFamily (s : StripData D) where
  /-- Length of `SlotFamily`, of type `ℕ → ℝ`. -/
  length : ℕ → ℝ
  length_pos : ∀ n, 0 < length n
  /-- Linear of `SlotFamily`, of type `ℕ → D →L[ℝ] ℝ`. -/
  linear : ℕ → D →L[ℝ] ℝ
  /-- Offset of `SlotFamily`, of type `ℕ → ℝ`. -/
  offset : ℕ → ℝ
  linear_bound : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ, ∀ n, ‖linear n‖ ≤ K * s.slow n ^ p
  inverse_length_bound : BandBound s 0 (fun n => (length n)⁻¹)
  /-- Length scale of `SlotFamily`, of type `ℝ`. -/
  lengthScale : ℝ
  length_scale_pos : 0 < lengthScale
  length_lower : ∀ n, lengthScale * ChartScales.S n ≤ length n

namespace SlotFamily

/-- Coordinate, given by `g.offset n + g.linear n x`. -/
noncomputable def coordinate {s : StripData D} (g : SlotFamily s) (n : ℕ) (x : D) : ℝ :=
  g.offset n + g.linear n x

/-- Cutoff, given by `profile (g.coordinate n x)`. -/
noncomputable def cutoff {s : StripData D} (g : SlotFamily s) (n : ℕ) (x : D) : ℝ :=
  profile (g.coordinate n x)

/-- Error, given by `cutoffError (g.length n) (g.coordinate n) (u n) (f n)`. -/
noncomputable def error {s : StripData D} (g : SlotFamily s) (u f : ℕ → D → E)
    (n : ℕ) : D → E := cutoffError (g.length n) (g.coordinate n) (u n) (f n)

theorem coordinate_contDiff {s : StripData D} (g : SlotFamily s) (n : ℕ) :
    ContDiff ℝ ∞ (g.coordinate n) := contDiff_const.add (g.linear n).contDiff

theorem cutoff_memClass {s : StripData D} (g : SlotFamily s) :
    UnweightedClass s 0 g.cutoff :=
  affine_profile_memClass s profile_contDiff profile_jet_bounded g.linear g.offset g.linear_bound

theorem error_mem_wave {s : StripData D} (g : SlotFamily s) {P : ℕ → D → ℝ}
    {α : ℝ} {u f : ℕ → D → E} (hu : WaveClass s P α u) (hf : WaveClass s P α f) :
    WaveClass s P α (g.error u f) :=
  cutoffError_mem_wave hu hf g.length g.linear g.offset g.linear_bound g.inverse_length_bound

/-- The derivative in a direction with `D(v)=1` is the exact coefficient
used in the retained cutoff error, because `v=L θ`. -/
theorem cutoff_directional {s : StripData D} (g : SlotFamily s) (n : ℕ) (x w : D)
    (hw : g.linear n w = (g.length n)⁻¹) :
    fderiv ℝ (g.cutoff n) x w =
      (g.length n)⁻¹ * deriv profile (g.coordinate n x) := by
  have hp := (profile_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
    (x := g.coordinate n x)
  have hθ : HasFDerivAt (g.coordinate n) (g.linear n) x :=
    (g.linear n).hasFDerivAt.const_add (g.offset n)
  have hd := hp.hasFDerivAt.comp x hθ
  have he := congrArg (fun A : D →L[ℝ] ℝ => A w) hd.fderiv
  unfold cutoff
  simpa [hw, mul_comm, Function.comp_def] using he

theorem error_eq_directional {s : StripData D} (g : SlotFamily s) (u f : ℕ → D → E)
    (n : ℕ) (x w : D) (hw : g.linear n w = (g.length n)⁻¹) :
    g.error u f n x =
      fderiv ℝ (g.cutoff n) x w • u n x + (1 - g.cutoff n x) • f n x := by
  rw [g.cutoff_directional n x w hw]
  rfl

/-- Uniform polynomial-times-Gaussian bound for the two exact cutoff products.
The only field estimates assumed are the original wave/source classes and
the Gaussian upper bound for their common envelope. -/
theorem error_gaussian_bound {s : StripData D} (g : SlotFamily s)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    {P : ℕ → D → ℝ} {α c : ℝ} {u f : ℕ → D → E}
    (hu : WaveClass s P α u) (hf : WaveClass s P α f) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n x, x ∈ s.domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (g.error u f n) x‖ ≤
        C * (1 + ChartScales.S n) ^ d *
          Real.exp (-(c * g.lengthScale / 50) * ChartScales.S n) := by
  obtain ⟨A, hA, p, hb⟩ := (g.error_mem_wave hu hf).bounds m
  obtain ⟨B, hB, hweight⟩ := edges.uniform_weight p
  have hscale := g.length_scale_pos
  have hconstant := scales.constant_one_le
  have hdec : 0 < c * g.lengthScale / 25 := by positivity
  obtain ⟨C, hC, hgauss⟩ := fixed_power_gaussian_bound hdec (scales.power * α)
  refine ⟨A * B * scales.boundConstant ^ p * C, by positivity, scales.degree * p, ?_⟩
  intro n x hx j hj
  have hQ := ChartScales.Q_pos n
  by_cases hmid : |g.coordinate n x - 1 / 2| < 1 / 5
  · have hz := cutoffError_jet_zero_on_plateau (g.length n) (u n) (f n)
      (g.coordinate_contDiff n).continuous.continuousAt hmid j
    change iteratedFDeriv ℝ j (g.error u f n) x = 0 at hz
    rw [hz, norm_zero]
    have hS : 0 ≤ ChartScales.S n := sq_nonneg _
    positivity
  have htail : 1 / 5 ≤ |g.coordinate n x - 1 / 2| := le_of_not_gt hmid
  have hsq : (1 / 25 : ℝ) ≤ (g.coordinate n x - 1 / 2) ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 5) htail 2
    norm_num [sq_abs] at hh ⊢
    exact hh
  have hPg : P n x ≤ Real.exp (-(c * g.lengthScale / 25) * ChartScales.S n) := by
    apply (hP n x hx).trans
    apply (Real.exp_le_exp.2 ?_).trans (gaussian_length_comparison hc.le (g.length_lower n))
    linarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hc.le (g.length_pos n).le)]
  have hslow0 : 0 ≤ s.slow n := zero_le_one.trans (s.one_le_slow n)
  have hK0 : 0 ≤ scales.boundConstant := zero_le_one.trans scales.constant_one_le
  have hslowp : s.slow n ^ p ≤
      scales.boundConstant ^ p * (1 + ChartScales.S n) ^ (scales.degree * p) := by
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ hslow0 (scales.slow_le n) p
  have hmajor : majorant s (fun n x => Real.sqrt (s.zeta x) * P n x) α A p n x ≤
      (A * B * scales.boundConstant ^ p) * ChartScales.Q n ^ (scales.power * α) *
        ((1 + ChartScales.S n) ^ (scales.degree * p) *
          Real.exp (-(c * g.lengthScale / 25) * ChartScales.S n)) := by
    rw [majorant, StripData.growth, mul_pow, scales.epsilon_eq,
      ← Real.rpow_mul hQ.le]
    calc
      _ = (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) *
          (Real.sqrt (s.zeta x) * max 1 (s.delta x)⁻¹ ^ p) * P n x := by ring
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) *
          (Real.sqrt (s.zeta x) * max 1 (s.delta x)⁻¹ ^ p) *
            Real.exp (-(c * g.lengthScale / 25) * ChartScales.S n) :=
        mul_le_mul_of_nonneg_left hPg (by positivity)
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) * B *
            Real.exp (-(c * g.lengthScale / 25) * ChartScales.S n) := by
        gcongr
        exact hweight x hx
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) *
          (scales.boundConstant ^ p * (1 + ChartScales.S n) ^ (scales.degree * p))) * B *
            Real.exp (-(c * g.lengthScale / 25) * ChartScales.S n) := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ majorant s (fun n x => Real.sqrt (s.zeta x) * P n x) α A p n x := hb n x hx j hj
    _ ≤ _ := hmajor
    _ = (A * B * scales.boundConstant ^ p) * (1 + ChartScales.S n) ^ (scales.degree * p) *
        (ChartScales.Q n ^ (scales.power * α) *
          Real.exp (-(c * g.lengthScale / 25) * ChartScales.S n)) := by ring
    _ ≤ (A * B * scales.boundConstant ^ p) * (1 + ChartScales.S n) ^ (scales.degree * p) *
        (C * Real.exp (-((c * g.lengthScale / 25) / 2) * ChartScales.S n)) := by
      have hS : 0 ≤ ChartScales.S n := sq_nonneg _
      exact mul_le_mul_of_nonneg_left (hgauss n) (by positivity)
    _ = _ := by
      rw [show c * g.lengthScale / 25 / 2 = c * g.lengthScale / 50 by ring]
      ring

/-- Every prescribed dyadic power is gained, for all actual stripped jets. -/
theorem error_stripped_bound {s : StripData D} (g : SlotFamily s)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    {P : ℕ → D → ℝ} {α c : ℝ} {u f : ℕ → D → E}
    (hu : WaveClass s P α u) (hf : WaveClass s P α f) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (m : ℕ) (N : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ s.domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (g.error u f n) x‖ ≤ C * ChartScales.Q n ^ N := by
  obtain ⟨A, hA, d, ha⟩ := g.error_gaussian_bound edges scales hu hf hc hP m
  have hscale := g.length_scale_pos
  obtain ⟨B, hB, hb⟩ := gaussian_beats_Q_power (by positivity : 0 < c * g.lengthScale / 50) d N
  refine ⟨A * B, by positivity, fun n x hx j hj => ?_⟩
  calc
    _ ≤ A * (1 + ChartScales.S n) ^ d *
        Real.exp (-(c * g.lengthScale / 50) * ChartScales.S n) := ha n x hx j hj
    _ = A * ((1 + ChartScales.S n) ^ d *
        Real.exp (-(c * g.lengthScale / 50) * ChartScales.S n)) := by ring
    _ ≤ A * (B * ChartScales.Q n ^ N) := mul_le_mul_of_nonneg_left (hb n) hA
    _ = _ := by ring

/-- The excluded field belongs to every unweighted decay class. Its bound
has polynomial degree zero, so no inverse-edge factor remains hidden. -/
theorem error_all_gains {s : StripData D} (g : SlotFamily s)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    {P : ℕ → D → ℝ} {α c : ℝ} {u f : ℕ → D → E}
    (hu : WaveClass s P α u) (hf : WaveClass s P α f) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (N : ℝ) : UnweightedClass s N (g.error u f) := by
  refine ⟨fun _ _ _ => zero_le_one, (g.error_mem_wave hu hf).smooth, ?_⟩
  intro m
  obtain ⟨C, hC, hb⟩ := g.error_stripped_bound edges scales hu hf hc hP m (scales.power * N)
  refine ⟨C, hC, 0, fun n x hx j hj => ?_⟩
  simpa only [majorant, pow_zero, mul_one, scales.epsilon_eq,
    ← Real.rpow_mul (ChartScales.Q_pos n).le] using hb n x hx j hj

end SlotFamily

/-- The true native slot length is uniformly comparable from below to
`1+n²`; finitely many small bands are included by a finite minimum. -/
theorem native_slot_length_lower (r0 h : ℝ) (hr0 : 0 < r0) (hh : 0 ≤ h) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ,
      κ * (1 + ChartScales.S n) ≤ ChartScales.slotLength r0 h n := by
  have hL (n : ℕ) : 0 < ChartScales.slotLength r0 h n :=
    div_pos (mul_pos (by norm_num) hr0) (ChartScales.timeCoefficient_pos h n)
  have hS (n : ℕ) : 0 < 1 + ChartScales.S n := by unfold ChartScales.S; positivity
  obtain ⟨i, hi, hmin⟩ := (Finset.range 4).exists_min_image
    (fun n => ChartScales.slotLength r0 h n / (1 + ChartScales.S n))
    (by exact ⟨0, by decide⟩)
  refine ⟨min r0 (ChartScales.slotLength r0 h i / (1 + ChartScales.S i)),
    lt_min hr0 (div_pos (hL i) (hS i)), ?_⟩
  intro n
  rcases lt_or_ge n 4 with hn | hn
  · apply (le_div_iff₀ (hS n)).1
    exact (min_le_right _ _).trans (hmin n (Finset.mem_range.mpr hn))
  · have hSn : 1 ≤ ChartScales.S n := by
      have hnn : (4 : ℝ) ≤ n := by exact_mod_cast hn
      unfold ChartScales.S
      nlinarith
    calc
      _ ≤ r0 * (1 + ChartScales.S n) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (hS n).le
      _ ≤ 2 * r0 * ChartScales.S n := by nlinarith
      _ ≤ ChartScales.slotLength r0 h n := (ChartScales.slotLength_bounds r0 h hr0.le hh hn).1

/-- Actual native slots. `η` is the fixed longitudinal coordinate functional;
only the centers depend on the band. Normalizing `v` by `L` cancels `ci`. -/
noncomputable def actualSlotFamily (s : StripData D) (r0 h : ℝ)
    (hr0 : 0 < r0) (hh : 0 ≤ h) (η : D →L[ℝ] ℝ) (center : ℕ → ℝ) : SlotFamily s := by
  let κ := Classical.choose (native_slot_length_lower r0 h hr0 hh)
  have hκ := Classical.choose_spec (native_slot_length_lower r0 h hr0 hh)
  have hL (n : ℕ) : 0 < ChartScales.slotLength r0 h n :=
    div_pos (mul_pos (by norm_num) hr0) (ChartScales.timeCoefficient_pos h n)
  have hκL (n : ℕ) : κ ≤ ChartScales.slotLength r0 h n := by
    apply le_trans _ (hκ.2 n)
    have hn : 0 ≤ ChartScales.S n := sq_nonneg _
    nlinarith [hκ.1]
  refine {
    length := ChartScales.slotLength r0 h
    length_pos := hL
    linear := fun _ => (2 * r0)⁻¹ • η
    offset := fun n => (r0 - center n) / (2 * r0)
    linear_bound := ?_
    inverse_length_bound := ?_
    lengthScale := κ
    length_scale_pos := hκ.1
    length_lower := ?_
  }
  · refine ⟨max 1 ‖(2 * r0)⁻¹ • η‖, le_max_left _ _, 0, fun n => ?_⟩
    simpa only [pow_zero, mul_one] using le_max_right 1 ‖(2 * r0)⁻¹ • η‖
  · refine ⟨κ⁻¹, (inv_pos.mpr hκ.1).le, 0, fun n => ?_⟩
    simp only [Real.rpow_zero, pow_zero, mul_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hL n))]
    simpa only [one_div] using one_div_le_one_div_of_le hκ.1 (hκL n)
  · intro n
    apply le_trans _ (hκ.2 n)
    linarith [hκ.1]

@[simp] theorem actualSlotFamily_length (s : StripData D) (r0 h : ℝ)
    (hr0 : 0 < r0) (hh : 0 ≤ h) (η : D →L[ℝ] ℝ) (center : ℕ → ℝ) (n : ℕ) :
    (actualSlotFamily s r0 h hr0 hh η center).length n = ChartScales.slotLength r0 h n := rfl

theorem actualSlotFamily_coordinate (s : StripData D) (r0 h : ℝ)
    (hr0 : 0 < r0) (hh : 0 ≤ h) (η : D →L[ℝ] ℝ) (center : ℕ → ℝ) (n : ℕ) (x : D) :
    (actualSlotFamily s r0 h hr0 hh η center).coordinate n x =
      (η x - center n + r0) / (2 * r0) := by
  change (r0 - center n) / (2 * r0) + ((2 * r0)⁻¹ • η) x = _
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

theorem actualSlotFamily_cutoff (s : StripData D) (r0 h : ℝ)
    (hr0 : 0 < r0) (hh : 0 ≤ h) (η : D →L[ℝ] ℝ) (center : ℕ → ℝ) (n : ℕ) (x : D) :
    (actualSlotFamily s r0 h hr0 hh η center).cutoff n x =
      slotCutoff (ChartScales.slotLength r0 h n)
        ((η x - center n + r0) / ChartScales.timeCoefficient h n) := by
  rw [SlotFamily.cutoff, actualSlotFamily_coordinate]
  unfold slotCutoff ChartScales.slotLength
  congr 1
  field_simp [(ChartScales.timeCoefficient_pos h n).ne', hr0.ne']

/-- The reference Gaussian envelope, extended by zero away from its slot.
This is a weight, not a redefinition of either retained error. -/
noncomputable def referenceSlotEnvelope (lam u L θ : ℝ) : ℝ :=
  if θ ∈ Icc (0 : ℝ) 1 then
    GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u L) (L / 2) (L * θ)
  else 0

theorem referenceSlotEnvelope_bound {lam u L : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L) (θ : ℝ) :
    referenceSlotEnvelope lam u L θ ≤
      Real.exp (-(u * GaussianEnvelope.referenceMinSlope lam u / 2) * (θ - 1 / 2) ^ 2 * L) := by
  by_cases hθ : θ ∈ Icc (0 : ℝ) 1
  · rw [referenceSlotEnvelope, ite_eq_left hθ]
    have ht : L * θ ∈ Icc (0 : ℝ) L := ⟨mul_nonneg hL.le hθ.1, by nlinarith [hθ.2]⟩
    apply (GaussianEnvelope.reference_gaussian_bounds hlam hu hL ht).2.trans_eq
    congr 1
    field_simp [hL.ne']
  · rw [referenceSlotEnvelope, ite_eq_right hθ]
    exact (Real.exp_pos _).le

/-! ## Restriction to the actual physical graph and carrier -/

namespace SlotFamily

theorem error_contDiff {s : StripData D} (g : SlotFamily s) {u f : ℕ → D → E}
    (hu : ∀ n, ContDiff ℝ ∞ (u n)) (hf : ∀ n, ContDiff ℝ ∞ (f n)) (n : ℕ) :
    ContDiff ℝ ∞ (g.error u f n) := by
  apply contDiffOn_univ.mp
  exact cutoffError_contDiffOn (g.length n) (g.coordinate_contDiff n).contDiffOn
    (hu n).contDiffOn (hf n).contDiffOn

/-- The fundamental need only be smooth in the open slot. Away from that
slot the exact error agrees locally with the smooth source. This avoids any
smoothness assertion for a clamped ODE extension across its endpoints. -/
theorem error_contDiff_of_slot {s : StripData D} (g : SlotFamily s) {u f : ℕ → D → E}
    (hu : ∀ n, ContDiffOn ℝ ∞ (u n) {x | g.coordinate n x ∈ Ioo (0 : ℝ) 1})
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (n : ℕ) :
    ContDiff ℝ ∞ (g.error u f n) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : g.coordinate n x ∈ Ioo (0 : ℝ) 1
  · have hU : IsOpen {y | g.coordinate n y ∈ Ioo (0 : ℝ) 1} :=
      isOpen_Ioo.preimage (g.coordinate_contDiff n).continuous
    have hus := (hu n).contDiffAt (hU.mem_nhds hx)
    have ht : ContDiffAt ℝ ∞ (g.coordinate n) x := (g.coordinate_contDiff n).contDiffAt
    exact ((contDiffAt_const.mul (profileDeriv_contDiff.contDiffAt.comp x ht)).smul hus).add
      ((contDiffAt_const.sub (profile_contDiff.contDiffAt.comp x ht)).smul (hf n).contDiffAt)
  · have hout : 1 / 3 < |g.coordinate n x - 1 / 2| := by
      have hx' : g.coordinate n x ≤ 0 ∨ 1 ≤ g.coordinate n x := by
        simpa only [mem_Ioo, not_and_or, not_lt] using hx
      rcases hx' with hx' | hx'
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        linarith
    have hp := (profile_eventually_zero hout).comp_tendsto
      (g.coordinate_contDiff n).continuous.continuousAt
    have hd := (profile_eventually_zero hout).deriv.comp_tendsto
      (g.coordinate_contDiff n).continuous.continuousAt
    have he : g.error u f n =ᶠ[𝓝 x] f n := by
      filter_upwards [hp, hd] with y hpy hdy
      have hp' : profile (g.coordinate n y) = 0 := hpy
      have hd' : deriv profile (g.coordinate n y) = 0 := by simpa using hdy
      simp [error, cutoffError, hp', hd']
    exact (hf n).contDiffAt.congr_of_eventuallyEq he

open PhysicalGraphBounds ProblemStatement

/-- Every fixed physical derivative retains arbitrarily high decay powers.
The loss is supplied by the proved physical graph theorem. -/
theorem error_physical_bound {s : StripData LiftPoint} (g : SlotFamily s)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    {P : ℕ → LiftPoint → ℝ} {α c : ℝ} {u f : ℕ → LiftPoint → E}
    (hu : WaveClass s P α u) (hf : WaveClass s P α f) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (hu_smooth : ∀ n, ContDiffOn ℝ ∞ (u n) {x | g.coordinate n x ∈ Ioo (0 : ℝ) 1})
    (hf_smooth : ∀ n, ContDiff ℝ ∞ (f n))
    {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a) (m : ℕ) (N : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 → physicalLift h n p ∈ s.domain →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ‖iteratedFDeriv ℝ m (g.error u f n ∘ physicalLift h n) p‖ ≤ C * q ^ N := by
  obtain ⟨A, hA, hab⟩ := g.error_stripped_bound edges scales hu hf hc hP m
    (N + (graphLoss m + 1))
  obtain ⟨C, hC, hbound⟩ := stripped_class_physical_bound (E := E) (b := b) hh hh1 ha m
    (N + (graphLoss m + 1)) 0 A hA
  refine ⟨C, hC, fun n hn p hp ht hd q hq hlo hhi => ?_⟩
  have hb := hbound n hn p hp ht q hq hlo hhi (g.error u f n)
    (g.error_contDiff_of_slot hu_smooth hf_smooth n) (fun i hi => by
      simpa only [Real.rpow_zero, mul_one] using hab n (physicalLift h n p) hd i hi)
  simpa only [add_sub_cancel_right] using hb

/-- Big-O formulation along any sequence of physical points in the controlled
annulus and slow domain.  The derivative order and power are arbitrary. -/
theorem error_physical_isBigO {s : StripData LiftPoint} (g : SlotFamily s)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    {P : ℕ → LiftPoint → ℝ} {α c : ℝ} {u f : ℕ → LiftPoint → E}
    (hu : WaveClass s P α u) (hf : WaveClass s P α f) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (hu_smooth : ∀ n, ContDiffOn ℝ ∞ (u n) {x | g.coordinate n x ∈ Ioo (0 : ℝ) 1})
    (hf_smooth : ∀ n, ContDiff ℝ ∞ (f n))
    {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (p : ℕ → SpaceTime)
    (hp : ∀ n, 4 ≤ n → scaledRadial n (p n) ∈ annulus a b ∧ |(p n).1| ≤ 1 ∧
      physicalLift h n (p n) ∈ s.domain) (m : ℕ) (N : ℝ) :
    (fun n => iteratedFDeriv ℝ m (g.error u f n ∘ physicalLift h n) (p n)) =O[atTop]
      (fun n => ChartScales.Q n ^ N) := by
  obtain ⟨C, hC, hb⟩ := g.error_physical_bound edges scales hu hf hc hP hu_smooth hf_smooth
    hh hh1 ha (b := b) m N
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hQ := ChartScales.Q_pos n
  have hpn := hp n hn
  have hh := hb n hn (p n) hpn.1 hpn.2.1 hpn.2.2 (ChartScales.Q n) hQ
    (by linarith) (by linarith)
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hQ N)] using hh

/-- The same result for the actual oscillatory carrier. The phase estimates
are the primitive estimates consumed by `carrier_class_physical_bound`. -/
theorem error_carrier_physical_bound {s : StripData LiftPoint} (g : SlotFamily s)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    {P : ℕ → LiftPoint → ℝ} {α c : ℝ} {u f : ℕ → LiftPoint → ℂ}
    (hu : WaveClass s P α u) (hf : WaveClass s P α f) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (hu_smooth : ∀ n, ContDiffOn ℝ ∞ (u n) {x | g.coordinate n x ∈ Ioo (0 : ℝ) 1})
    (hf_smooth : ∀ n, ContDiff ℝ ∞ (f n))
    {h a b B e H : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (hB : 1 ≤ B) (he : 0 ≤ e) (hH : 0 ≤ H) (m : ℕ) (N : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 → physicalLift h n p ∈ s.domain →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ (Φ : LiftPoint → ℝ) (j : ℤ), ContDiff ℝ ∞ Φ → |(j : ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i Φ (physicalLift h n p)‖ ≤
        B * ChartScales.S n ^ e * ChartScales.Q n ^ (-1 : ℝ)) →
      ‖iteratedFDeriv ℝ m
        ((fun y => g.error u f n y * character ((ChartScales.carrier h n : ℝ) * (j : ℝ)) (Φ y)) ∘
          physicalLift h n) p‖ ≤ C * q ^ N := by
  obtain ⟨A, hA, hab⟩ := g.error_stripped_bound edges scales hu hf hc hP m (N + waveLoss h m)
  obtain ⟨C, hC, hb⟩ := carrier_class_physical_bound (b := b) hh hh1 ha m
    (N + waveLoss h m) 0 e A B H hA hB he hH
  refine ⟨C, hC, fun n hn p hp ht hd q hq hlo hhi Φ j hΦ hj hΦb => ?_⟩
  have hh := hb n hn p hp ht q hq hlo hhi (g.error u f n) Φ j
    (g.error_contDiff_of_slot hu_smooth hf_smooth n) hΦ hj (fun i hi => by
      simpa only [Real.rpow_zero, mul_one] using hab n (physicalLift h n p) hd i hi) hΦb
  simpa only [add_sub_cancel_right] using hh

/-- Version with the manuscript's actual native phase, polar charts and
rounded carrier. No phase-derivative hypothesis replaces the base-field jets. -/
theorem error_native_carrier_physical_bound {s : StripData LiftPoint} (g : SlotFamily s)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    {Penv : ℕ → LiftPoint → ℝ} {α c : ℝ} {u f : ℕ → LiftPoint → ℂ}
    (hu : WaveClass s Penv α u) (hf : WaveClass s Penv α f) (hc : 0 < c)
    (hPenv : ∀ n x, x ∈ s.domain →
      Penv n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (hu_smooth : ∀ n, ContDiffOn ℝ ∞ (u n) {x | g.coordinate n x ∈ Ioo (0 : ℝ) 1})
    (hf_smooth : ∀ n, ContDiff ℝ ∞ (f n))
    {h a b Z r0 P B dBase H : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (hdBase : 0 ≤ dBase)
    (hH : 0 ≤ H) (m : ℕ) (N : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 → physicalLift h n w ∈ s.domain →
      ‖liftZT (physicalLift h n w)‖ ≤ Z →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ (chart : PolarCharts.Index) (center : Plane) (p pz x0 : ℝ),
      |p| ≤ P → |pz| ≤ P → |x0| ≤ P →
      |etaCoordinate (nativeGraph h n w - center)| ≤ r0 →
      ∀ (F G : Slow → ℝ) (j : ℤ), ContDiff ℝ ∞ F → ContDiff ℝ ∞ G → |(j : ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i F
        (slotMap (PolarCharts.chart a chart) (ChartScales.timeCoefficient h n) center r0
          (physicalLift h n w)).1‖ ≤ B * ChartScales.S n ^ dBase) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i G
        (slotMap (PolarCharts.chart a chart) (ChartScales.timeCoefficient h n) center r0
          (physicalLift h n w)).1‖ ≤ B * ChartScales.S n ^ dBase) →
      ‖iteratedFDeriv ℝ m
        ((fun y => g.error u f n y * character ((ChartScales.carrier h n : ℝ) * (j : ℝ))
          (liftedPhase (PolarCharts.chart a chart) h n center r0 p pz x0 F G y)) ∘
          physicalLift h n) w‖ ≤ C * q ^ N := by
  obtain ⟨A, hA, hab⟩ := g.error_stripped_bound edges scales hu hf hc hPenv m (N + waveLoss h m)
  obtain ⟨C, hC, hb⟩ := native_carrier_physical_bound (b := b) hh hh1 ha hZ hr0 hP hB hdBase m
    (N + waveLoss h m) 0 A H hA hH
  refine ⟨C, hC, fun n hn w hw ht hd hz q hq hlo hhi chart center p pz x0 hp hpz hx0 hslot
    F G j hF hG hj hFb hGb => ?_⟩
  have hh := hb n hn w hw ht hz q hq hlo hhi chart center p pz x0 hp hpz hx0 hslot
    (g.error u f n) F G j (g.error_contDiff_of_slot hu_smooth hf_smooth n) hF hG hj (fun i hi => by
      simpa only [Real.rpow_zero, mul_one] using hab n (physicalLift h n w) hd i hi) hFb hGb
  simpa only [add_sub_cancel_right] using hh

end SlotFamily

/-! ## The two summands separately -/

namespace SlotFamily

/-- Derivative error, given by `((g.length n)⁻¹ * deriv profile (g.coordinate n x)) • u n x`. -/
noncomputable def derivativeError {s : StripData D} (g : SlotFamily s)
    (u : ℕ → D → E) (n : ℕ) (x : D) : E :=
  ((g.length n)⁻¹ * deriv profile (g.coordinate n x)) • u n x

/-- Omitted source, given by `(1 - profile (g.coordinate n x)) • f n x`. -/
noncomputable def omittedSource {s : StripData D} (g : SlotFamily s)
    (f : ℕ → D → E) (n : ℕ) (x : D) : E :=
  (1 - profile (g.coordinate n x)) • f n x

theorem error_eq_sum {s : StripData D} (g : SlotFamily s) (u f : ℕ → D → E)
    (n : ℕ) (x : D) :
    g.error u f n x = g.derivativeError u n x + g.omittedSource f n x := rfl

private theorem jet_eq_zero_of_eventually {u : D → E} {x : D}
    (he : u =ᶠ[𝓝 x] fun _ => 0) (j : ℕ) : iteratedFDeriv ℝ j u x = 0 := by
  have he' : u =ᶠ[𝓝[univ] x] fun _ => 0 := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ, iteratedFDeriv_fun_zero, Pi.zero_apply] using
    he'.iteratedFDerivWithin_eq (𝕜 := ℝ) he.self_of_nhds j

theorem derivativeError_jet_support {s : StripData D} (g : SlotFamily s)
    (u : ℕ → D → E) (n j : ℕ) :
    support (iteratedFDeriv ℝ j (g.derivativeError u n)) ⊆
      {x | 1 / 5 ≤ |g.coordinate n x - 1 / 2| ∧ |g.coordinate n x - 1 / 2| ≤ 1 / 3} := by
  classical
  intro x hx
  change iteratedFDeriv ℝ j (g.derivativeError u n) x ≠ 0 at hx
  have hzero (hv : deriv profile =ᶠ[𝓝 (g.coordinate n x)] fun _ => 0) : False := by
    apply hx
    apply jet_eq_zero_of_eventually (j := j)
    have hcomp := hv.comp_tendsto (g.coordinate_contDiff n).continuous.continuousAt
    filter_upwards [hcomp] with y hy
    have hy' : deriv profile (g.coordinate n y) = 0 := hy
    simp [derivativeError, hy']
  constructor
  · by_contra ht
    apply hzero
    filter_upwards [(profile_eventually_one (lt_of_not_ge ht)).deriv] with y hy
    simpa using hy
  · by_contra ht
    apply hzero
    filter_upwards [(profile_eventually_zero (lt_of_not_ge ht)).deriv] with y hy
    simpa using hy

/-- Both transition collars, with the exact normalized slot endpoints. This
holds for every actual parameter jet, without any regularity needed of `u`
where the multiplier vanishes on a neighborhood. -/
theorem derivativeError_jet_near_ends {s : StripData D} (g : SlotFamily s)
    (u : ℕ → D → E) (n j : ℕ) {x : D}
    (hx : iteratedFDeriv ℝ j (g.derivativeError u n) x ≠ 0) :
    g.coordinate n x ∈ Icc (1 / 6 : ℝ) (3 / 10) ∪ Icc (7 / 10 : ℝ) (5 / 6) := by
  have hb := g.derivativeError_jet_support u n j hx
  change 1 / 5 ≤ |g.coordinate n x - 1 / 2| ∧ |g.coordinate n x - 1 / 2| ≤ 1 / 3 at hb
  rcases le_total (g.coordinate n x) (1 / 2) with h | h
  · rw [abs_of_nonpos (by linarith)]
      at hb
    left
    constructor <;> linarith [hb.1, hb.2]
  · rw [abs_of_nonneg (by linarith)]
      at hb
    right
    constructor <;> linarith [hb.1, hb.2]

theorem omittedSource_jet_support {s : StripData D} (g : SlotFamily s)
    (f : ℕ → D → E) (n j : ℕ) :
    support (iteratedFDeriv ℝ j (g.omittedSource f n)) ⊆
      {x | 1 / 5 ≤ |g.coordinate n x - 1 / 2|} := by
  intro x hx
  change 1 / 5 ≤ |g.coordinate n x - 1 / 2|
  by_contra ht
  apply hx
  apply jet_eq_zero_of_eventually (j := j)
  have hcomp := (profile_eventually_one (lt_of_not_ge ht)).comp_tendsto
    (g.coordinate_contDiff n).continuous.continuousAt
  filter_upwards [hcomp] with y hy
  have hy' : profile (g.coordinate n y) = 1 := hy
  simp [omittedSource, hy']

theorem derivativeError_gaussian_bound {s : StripData D} (g : SlotFamily s)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    {P : ℕ → D → ℝ} {α c : ℝ} {u : ℕ → D → E}
    (hu : WaveClass s P α u) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n x, x ∈ s.domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (g.derivativeError u n) x‖ ≤
        C * (1 + ChartScales.S n) ^ d *
          Real.exp (-(c * g.lengthScale / 50) * ChartScales.S n) := by
  have hz : WaveClass s P α (fun _ _ => (0 : E)) := MemClass.zero hu.weight_nonneg
  have he : g.error u (fun _ _ => (0 : E)) = g.derivativeError u := by
    funext n x
    simp only [error, cutoffError, derivativeError, smul_zero, add_zero]
  have hb := g.error_gaussian_bound edges scales hu hz hc hP m
  rwa [he] at hb

theorem omittedSource_gaussian_bound {s : StripData D} (g : SlotFamily s)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    {P : ℕ → D → ℝ} {α c : ℝ} {f : ℕ → D → E}
    (hf : WaveClass s P α f) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n x, x ∈ s.domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (g.omittedSource f n) x‖ ≤
        C * (1 + ChartScales.S n) ^ d *
          Real.exp (-(c * g.lengthScale / 50) * ChartScales.S n) := by
  have hz : WaveClass s P α (fun _ _ => (0 : E)) := MemClass.zero hf.weight_nonneg
  have he : g.error (fun _ _ => (0 : E)) f = g.omittedSource f := by
    funext n x
    simp only [error, cutoffError, omittedSource, smul_zero, zero_add]
  have hb := g.error_gaussian_bound edges scales hz hf hc hP m
  rwa [he] at hb

/-- Full all-gain specialization to the actually constructed reference
Gaussian envelope. Only the proved original wave classes are inputs. -/
theorem reference_error_all_gains {s : StripData D} (g : SlotFamily s)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    {lam v α : ℝ} (hlam : 0 < lam) (hv : 0 < v) {u f : ℕ → D → E}
    (hu : WaveClass s (fun n x => referenceSlotEnvelope lam v (g.length n) (g.coordinate n x)) α u)
    (hf : WaveClass s (fun n x => referenceSlotEnvelope lam v (g.length n) (g.coordinate n x)) α f)
    (N : ℝ) : UnweightedClass s N (g.error u f) := by
  have hm := GaussianEnvelope.referenceMinSlope_pos hlam hv
  apply g.error_all_gains edges scales hu hf
    (c := v * GaussianEnvelope.referenceMinSlope lam v / 2) (by positivity)
  intro n x _
  exact referenceSlotEnvelope_bound hlam hv (g.length_pos n) (g.coordinate n x)

end SlotFamily

end NavierStokes.GaussianTailFlat
