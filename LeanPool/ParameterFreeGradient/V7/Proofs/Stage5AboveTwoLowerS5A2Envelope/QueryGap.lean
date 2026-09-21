/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.ExactPairCompletion

/-!
A persistent query gap and existence of a global minimizer for the completed hard objective.
-/

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open scoped BigOperators
open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5AFinalRepair
open Stage5AboveTwoLowerResume

/-- The comparison point with negative signed separation on each selected coordinate. -/
noncomputable def adversarialPoint (data : LowerCompletionData p d T) : Point d :=
  (Finset.range T).sum fun i =>
    (-data.Delta * data.xi i) • coordinateUnit (data.sigma i)

lemma sigma_injective_below (data : LowerCompletionData p d T)
    (hsteps : ∀ t < T, ∀ s < t, data.sigma s ≠ data.sigma t) :
    Set.InjOn data.sigma {i | i < T} := by
  intro i hi j hj hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijNat | hjiNat
  · exact (hsteps j hj i hijNat) hij
  · exact (hsteps i hi j hjiNat) hij.symm

lemma adversarialPoint_at_used (data : LowerCompletionData p d T)
    (hsteps : ∀ t < T, ∀ s < t, data.sigma s ≠ data.sigma t)
    {i : ℕ} (hi : i < T) :
    adversarialPoint data (data.sigma i) = -data.Delta * data.xi i := by
  have hinj := sigma_injective_below data hsteps
  unfold adversarialPoint
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp [coordinateUnit]
  · intro j hj hji
    have hjT := Finset.mem_range.mp hj
    have hsigma : data.sigma j ≠ data.sigma i := by
      intro hs
      exact hji (hinj hjT hi hs)
    simp [coordinateUnit, hsigma.symm]
  · simp [hi]

lemma adversarialPoint_at_unused (data : LowerCompletionData p d T)
    {j : Fin d} (hj : j ∉ (Finset.range T).image data.sigma) :
    adversarialPoint data j = 0 := by
  unfold adversarialPoint
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i hi
  have hsigma : data.sigma i ≠ j := by
    intro hs
    apply hj
    exact Finset.mem_image.mpr ⟨i, hi, hs⟩
  simp [coordinateUnit, hsigma.symm]

lemma abs_adversarialPoint_at_used (data : LowerCompletionData p d T)
    (hDelta : 0 ≤ data.Delta)
    (hsteps : ∀ t < T,
      (∀ s < t, data.sigma s ≠ data.sigma t) ∧
      (data.xi t = 1 ∨ data.xi t = -1))
    {i : ℕ} (hi : i < T) :
    |adversarialPoint data (data.sigma i)| = data.Delta := by
  rw [adversarialPoint_at_used data (fun t ht => (hsteps t ht).1) hi,
    abs_mul, abs_neg, abs_of_nonneg hDelta]
  rcases (hsteps i hi).2 with hxi | hxi <;> rw [hxi] <;> norm_num

lemma lpPower_adversarialPoint (data : LowerCompletionData p d T)
    (hp : 0 < p) (hDelta : 0 ≤ data.Delta)
    (hsteps : ∀ t < T,
      (∀ s < t, data.sigma s ≠ data.sigma t) ∧
      (data.xi t = 1 ∨ data.xi t = -1)) :
    O3.lpPower p (adversarialPoint data) =
      (T : ℝ) * data.Delta ^ p := by
  let used : Finset (Fin d) := (Finset.range T).image data.sigma
  have hinj : Set.InjOn data.sigma {i | i < T} :=
    sigma_injective_below data (fun t ht => (hsteps t ht).1)
  unfold O3.lpPower
  calc
    (∑ j, |adversarialPoint data j| ^ p) =
        ∑ j ∈ used, |adversarialPoint data j| ^ p := by
      symm
      apply Finset.sum_subset (Finset.subset_univ used)
      intro j _ hj
      rw [adversarialPoint_at_unused data hj,
        abs_zero, Real.zero_rpow hp.ne']
    _ = ∑ i ∈ Finset.range T,
        |adversarialPoint data (data.sigma i)| ^ p := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      exact hinj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    _ = ∑ _i ∈ Finset.range T, data.Delta ^ p := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_adversarialPoint_at_used data hDelta hsteps
        (Finset.mem_range.mp hi)]
    _ = (T : ℝ) * data.Delta ^ p := by simp

lemma lpNorm_adversarialPoint_eq_one (data : LowerCompletionData p d T)
    (hp : 0 < p) (hT : 1 ≤ T)
    (hDelta : data.Delta = (T : ℝ) ^ (-1 / p))
    (hsteps : ∀ t < T,
      (∀ s < t, data.sigma s ≠ data.sigma t) ∧
      (data.xi t = 1 ∨ data.xi t = -1)) :
    lpNorm p (adversarialPoint data) = 1 := by
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hDeltaNonneg : 0 ≤ data.Delta := by rw [hDelta]; positivity
  have hpower := lpPower_adversarialPoint data hp hDeltaNonneg hsteps
  unfold lpNorm O3.lpNorm
  rw [hpower, hDelta, ← Real.rpow_mul hTreal.le]
  have hexp : (-1 / p) * p = -1 := by field_simp [hp.ne']
  rw [hexp, Real.rpow_neg_one]
  have hcancel : (T : ℝ) * (T : ℝ)⁻¹ = 1 := by field_simp [hTreal.ne']
  rw [hcancel, Real.one_rpow]

lemma partialH_final_adversarialPoint_le (data : LowerCompletionData p d T)
    (hp : 0 < p) (hT : 1 ≤ T) (hdelta : 0 < data.delta)
    (hDelta : data.Delta = (T : ℝ) ^ (-1 / p))
    (hsteps : ∀ t < T,
      (∀ s < t, data.sigma s ≠ data.sigma t) ∧
      (data.xi t = 1 ∨ data.xi t = -1) ∧
      ResistingMaximumAt data t ∧
      (∀ x, data.partialH t x =
        max (data.partialG t x / 2) (lpNorm p x - 3 / 2))) :
    data.partialH (T - 1) (adversarialPoint data) ≤ -data.Delta / 2 := by
  have hlast : T - 1 < T := by omega
  have hTreal : 1 ≤ (T : ℝ) := by exact_mod_cast hT
  have hDeltaPos : 0 < data.Delta := by rw [hDelta]; positivity
  have hDeltaLe : data.Delta ≤ 1 := by
    rw [hDelta]
    exact Real.rpow_le_one_of_one_le_of_nonpos hTreal
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hp.le)
  have hnorm := lpNorm_adversarialPoint_eq_one data hp hT hDelta
    (fun t ht => ⟨(hsteps t ht).1, (hsteps t ht).2.1⟩)
  obtain ⟨i, hiLast, hiEq⟩ := (hsteps (T - 1) hlast).2.2.1
    (adversarialPoint data) |>.2
  have hiT : i < T := lt_of_le_of_lt hiLast hlast
  have hG : data.partialG (T - 1) (adversarialPoint data) ≤ -data.Delta := by
    rw [hiEq, adversarialPoint_at_used data
      (fun t ht => (hsteps t ht).1) hiT]
    rcases (hsteps i hiT).2.1 with hxi | hxi <;> rw [hxi] <;> norm_num
    all_goals nlinarith [mul_nonneg (Nat.cast_nonneg i) hdelta.le]
  rw [(hsteps (T - 1) hlast).2.2.2, hnorm]
  apply max_le
  · linarith
  · norm_num at ⊢
    linarith

lemma partialH_query_lower (data : LowerCompletionData p d T)
    {t : ℕ}
    (hstep : (data.xi t = 1 ∨ data.xi t = -1) ∧
      data.xi t * data.queries t (data.sigma t) =
        |data.queries t (data.sigma t)| ∧
      ResistingMaximumAt data t ∧
      (∀ x, data.partialH t x =
        max (data.partialG t x / 2) (lpNorm p x - 3 / 2))) :
    -(t : ℝ) * data.delta / 2 ≤ data.partialH t (data.queries t) := by
  have hpiece := hstep.2.2.1 (data.queries t) |>.1 t le_rfl
  have habs : 0 ≤ |data.queries t (data.sigma t)| := abs_nonneg _
  rw [hstep.2.1] at hpiece
  rw [hstep.2.2.2]
  have hmax := le_max_left (data.partialG t (data.queries t) / 2)
    (lpNorm p (data.queries t) - 3 / 2)
  linarith

/-- Finite-dimensional continuous coercive functions attain a global minimum.
The proof is the compact sublevel-ball reduction needed by the frozen carrier. -/
lemma exists_global_minimizer_of_coercive_lp {f : Point d → ℝ}
    {p : ℝ} (hp : 1 ≤ p) (hcontinuous : Continuous f)
    (hcoercive : IsCoerciveLp p f) :
    ∃ minimizer : Point d, ∀ x, f minimizer ≤ f x := by
  obtain ⟨radius, hradius, houtside⟩ := hcoercive (f 0)
  let ball : Set (Point d) := {x | lpNorm p x ≤ radius}
  have hcompact : IsCompact ball := isCompact_lpNorm_le hp
  have hzero : (0 : Point d) ∈ ball := by
    change O3.lpNorm p (0 : Point d) ≤ radius
    rw [O3.lpNorm_zero (by linarith : 0 < p)]
    exact hradius
  obtain ⟨minimizer, hminBall, hmin⟩ :=
    hcompact.exists_isMinOn ⟨0, hzero⟩ hcontinuous.continuousOn
  refine ⟨minimizer, fun x => ?_⟩
  by_cases hx : lpNorm p x ≤ radius
  · exact hmin hx
  · exact (hmin hzero).trans (houtside x (le_of_not_ge hx))

lemma lower_gap_constant_identity {p Delta chi delta beta M : ℝ} {T : ℕ}
    (hp : 0 < p) (hT : 1 ≤ T) (hM : 0 < M)
    (hDelta : Delta = (T : ℝ) ^ (-1 / p))
    (hdelta : delta = Delta / (2 * T))
    (hchi : chi = delta / 2) (hbeta : beta = chi / M) :
    beta * Delta / 4 =
      1 / (16 * M * (T : ℝ) ^ (1 + 2 / p)) := by
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hpow : ((T : ℝ) ^ (-1 / p)) ^ (2 : ℕ) =
      (T : ℝ) ^ (-2 / p) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hTreal.le]
    congr 1
    ring
  have hcombine : (T : ℝ) ^ (-2 / p) *
      (T : ℝ) ^ (1 + 2 / p) = (T : ℝ) := by
    rw [← Real.rpow_add hTreal]
    convert Real.rpow_one (T : ℝ) using 2; ring
  have hcore : ((T : ℝ) ^ (-1 / p)) ^ (2 : ℕ) *
      (T : ℝ) ^ (1 + 2 / p) = (T : ℝ) := by
    rw [hpow]
    exact hcombine
  rw [hbeta, hchi, hdelta, hDelta]
  rw [div_div]
  field_simp [hM.ne', hTreal.ne', (Real.rpow_pos_of_pos hTreal _).ne']
  ring_nf at hcore ⊢
  simp [hp.ne'] at hcore ⊢
  nlinarith

/-- Frozen S5-C: coercive attainment and the exact chronological query gap. -/
theorem _root_.V7.aboveLowerQueryGap : AboveLowerQueryGapStatement := by
  intro p hp d T data hassum
  rcases hassum with ⟨hcompletion, hobjectiveConvex, hobjectiveGradient⟩
  let base := data.toLowerCompletionData
  rcases hcompletion with
    ⟨hp', hd, hT, hTd, hx0, hkernel, hDelta, hdelta, hchi, hbeta,
      hqueries, hsteps, hcompletedValue, hcompletedGradient⟩
  have hpOne : 1 ≤ p := by linarith
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hDeltaPos : 0 < base.Delta := by rw [hDelta]; positivity
  have hdeltaPos : 0 < base.delta := by rw [hdelta]; positivity
  have hchiPos : 0 < base.chi := by rw [hchi]; positivity
  have hkernelFull := hkernel
  obtain ⟨hMpos, -, -, -, -, -, -, -, -, -, -, -, hsmooth, -, -⟩ := hkernel
  have hbetaPos : 0 < base.beta := by rw [hbeta]; positivity
  have hlast : T - 1 < T := by omega
  let shortSteps : ∀ s < T,
      (base.xi s = 1 ∨ base.xi s = -1) ∧ ResistingMaximumAt base s :=
    fun s hs => ⟨(hsteps s hs).2.2.2.1, (hsteps s hs).2.2.2.2.2.1⟩
  have hpartialLast := partialH_convex_oneLipschitz base hpOne hlast shortSteps
    (hsteps (T - 1) hlast).2.2.2.2.2.2.1
  have hsmoothLast := hsmooth base.chi hchiPos (base.partialH (T - 1))
    hpartialLast.1 hpartialLast.2
  have hcoercive : IsCoerciveLp p data.completedOracle.value := by
    intro B
    let radius : ℝ := max 0 (B / base.beta + 3 / 2 + base.chi)
    refine ⟨radius, le_max_left _ _, ?_⟩
    intro x hx
    have hradius : B / base.beta + 3 / 2 + base.chi ≤ lpNorm p x :=
      (le_max_right _ _).trans hx
    have hHlower := le_max_right
      (base.partialG (T - 1) x / 2) (lpNorm p x - 3 / 2)
    have hsmoothLower := (hsmoothLast.2.1 x).1
    have hdiv : B / base.beta ≤
        (base.kernel.smooth base.chi (base.partialH (T - 1))).value x := by
      have hHformula := (hsteps (T - 1) hlast).2.2.2.2.2.2.1 x
      rw [hHformula] at hsmoothLower
      linarith
    have hscaled : B ≤ base.beta *
        (base.kernel.smooth base.chi (base.partialH (T - 1))).value x := by
      have := (div_le_iff₀ hbetaPos).mp hdiv
      nlinarith
    rw [hcompletedValue]
    exact hscaled
  have hcontinuous : Continuous data.completedOracle.value :=
    continuous_iff_continuousAt.mpr fun x => (hobjectiveGradient x).1.continuousAt
  obtain ⟨minimizer, hminimizer⟩ :=
    exists_global_minimizer_of_coercive_lp hpOne hcontinuous hcoercive
  refine ⟨hcoercive, minimizer, hminimizer, ?_⟩
  intro t ht
  have hcompletionFull : LowerCompletionAssumptions base := by
    exact ⟨hp', hd, hT, hTd, hx0, hkernelFull, hDelta, hdelta, hchi, hbeta,
      hqueries, hsteps, hcompletedValue, hcompletedGradient⟩
  have hObs := V7.aboveLowerExactPairCompletion p hp d T base
    hcompletionFull t ht
  have hqueryValue := congrArg O3.Observation.value hObs
  change data.completedOracle.value (base.queries t) =
    (base.partialOracle t).value (base.queries t) at hqueryValue
  have hpartialT := partialH_convex_oneLipschitz base hpOne ht shortSteps
    (hsteps t ht).2.2.2.2.2.2.1
  have hsmoothT := hsmooth base.chi hchiPos (base.partialH t)
    hpartialT.1 hpartialT.2
  have hHquery := partialH_query_lower base
    ⟨(hsteps t ht).2.2.2.1, (hsteps t ht).2.2.2.2.1,
      (hsteps t ht).2.2.2.2.2.1, (hsteps t ht).2.2.2.2.2.2.1⟩
  have hqueryLower : base.beta * (-(t : ℝ) * base.delta / 2 - base.chi) ≤
      data.completedOracle.value (base.queries t) := by
    have happ := (hsmoothT.2.1 (base.queries t)).1
    have hraw : -(t : ℝ) * base.delta / 2 - base.chi ≤
        (base.kernel.smooth base.chi (base.partialH t)).value
          (base.queries t) := by
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hraw hbetaPos.le
    rw [← (hsteps t ht).2.2.2.2.2.2.2.1, ← hqueryValue] at hscaled
    exact hscaled
  have hcandidateH := partialH_final_adversarialPoint_le base (by linarith)
    hT hdeltaPos hDelta (fun s hs =>
      ⟨(hsteps s hs).1, (hsteps s hs).2.2.2.1,
        (hsteps s hs).2.2.2.2.2.1, (hsteps s hs).2.2.2.2.2.2.1⟩)
  have hcandidateValue : data.completedOracle.value (adversarialPoint base) ≤
      -base.beta * base.Delta / 2 := by
    have happ := (hsmoothLast.2.1 (adversarialPoint base)).2
    rw [hcompletedValue]
    nlinarith [mul_le_mul_of_nonneg_left
      (happ.trans hcandidateH) hbetaPos.le]
  have hminUpper := (hminimizer (adversarialPoint base)).trans hcandidateValue
  have htcast : (t : ℝ) + 1 ≤ (T : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.2 ht)
  have htdelta : ((t : ℝ) + 1) * base.delta ≤ (T : ℝ) * base.delta :=
    mul_le_mul_of_nonneg_right htcast hdeltaPos.le
  have hTdelta : (T : ℝ) * base.delta = base.Delta / 2 := by
    rw [hdelta]
    field_simp [hTreal.ne']
    ring
  have hquarter : base.Delta / 4 ≤
      base.Delta / 2 - (t : ℝ) * base.delta / 2 - base.chi := by
    rw [hchi]
    nlinarith
  have hgapQuarter : base.beta * base.Delta / 4 ≤
      data.completedOracle.value (base.queries t) -
        data.completedOracle.value minimizer := by
    nlinarith [mul_le_mul_of_nonneg_left hquarter hbetaPos.le]
  rw [← lower_gap_constant_identity (p := p) (T := T) (M := base.kernel.Mpd)
    (Delta := base.Delta) (chi := base.chi) (delta := base.delta)
    (beta := base.beta) (by linarith) hT hMpos hDelta hdelta hchi hbeta]
  exact hgapQuarter

end V7.Stage5AboveTwoLowerS5A2Envelope
