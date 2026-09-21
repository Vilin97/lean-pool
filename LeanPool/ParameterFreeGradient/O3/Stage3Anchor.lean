/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Stage3Descent
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Stage 3: the native gradient-ray anchor

This module closes the remaining proof-side bridges for the frozen anchor:
acceptance at the first dyadic scale dominating `L`, the actual infimum
distance to the minimizer set, and the displayed base-two ceiling count.
-/

namespace O3

open Stage3Anchor

/-- The anchor loop configuration contains only data already observed at
`x₀`; neither `L` nor a minimizer nor the solution radius is an input. -/
noncomputable def AdmissibleInstance.anchorConfig {d : ℕ} {p : ℝ}
    (P : AdmissibleInstance d p) : AnchorConfig d :=
  { q := conjugateExponent p
    x₀ := P.x0
    f₀ := P.f P.x0
    g₀ := P.grad P.x0
    G := lpNorm (conjugateExponent p) (P.grad P.x0)
    M₀ := P.M0 }

/-- The first dyadic scale dominating `L` occurs no later than the exact
source base-two ceiling. -/
theorem anchorScaleCap_le_logCeil {M₀ L : ℝ}
    (hM₀ : 0 < M₀) (hL : 0 < L) :
    anchorScaleCap M₀ L hM₀ ≤ Nat.ceil (Real.logb 2 (L / M₀)) := by
  apply Nat.find_min'
  have hr : 0 < L / M₀ := div_pos hL hM₀
  have hlog : Real.logb 2 (L / M₀) ≤
      (Nat.ceil (Real.logb 2 (L / M₀)) : ℝ) := Nat.le_ceil _
  have hratio : L / M₀ ≤ (2 : ℝ) ^ Nat.ceil (Real.logb 2 (L / M₀)) := by
    rw [← Real.rpow_natCast]
    exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hr).mp hlog
  rw [anchorScale, ← div_le_iff₀ hM₀]
  exact hratio

/-- At every dyadic scale dominating the true smoothness constant, the
observable anchor test passes.  This is derived from the exact `L/2` descent
lemma and the native norming identities, rather than supplied as a
certificate. -/
theorem anchor_cap_test_passes {d : ℕ} {p : ℝ}
    (P : AdmissibleInstance d p)
    (hGpos : 0 < lpNorm (conjugateExponent p) (P.grad P.x0))
    {epoch : ℕ} (hscale : P.L ≤ anchorScale P.M0 epoch) :
    let cfg := P.anchorConfig
    let D := anchorRadius cfg.G cfg.M₀ epoch
    let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ epoch
    P.oracle.value y ≤ cfg.f₀ - cfg.G * D / 2 := by
  let q := conjugateExponent p
  let g := P.grad P.x0
  let G := lpNorm q g
  let M := anchorScale P.M0 epoch
  let D := G / M
  let v := anchorNormingVector q g
  let y := P.x0 - D • v
  have hM0 : 0 < P.M0 := P.secant.2.2.2
  have hM : 0 < M := mul_pos (pow_pos (by norm_num) _) hM0
  have hG : 0 < G := hGpos
  have hg : g ≠ 0 := by
    exact (lpNorm_eq_zero_iff (by
      dsimp only [q]
      exact (one_lt_conjugateExponent P.p_gt_one).trans' zero_lt_one)).not.mp hG.ne'
  have hD : 0 < D := div_pos hG hM
  have hvnorm : lpNorm p v = 1 :=
    anchorNormingVector_lpNorm P.p_gt_one g hg
  have hvpair : pairing g v = G :=
    pairing_anchorNormingVector P.p_gt_one g hg
  have hysub : y - P.x0 = (-D) • v := by
    funext i
    simp only [y, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hynorm : lpNorm p (y - P.x0) = D := by
    rw [hysub, Stage2RouteC.lpNorm_smul P.p_gt_one.le, hvnorm,
      abs_of_neg (neg_neg_of_pos hD)]
    ring
  have hypair : pairing g (y - P.x0) = -G * D := by
    rw [hysub, Stage2RouteD.pairing_smul_right, hvpair]
    ring
  have hMD : M * D = G := by
    dsimp only [D]
    field_simp [hM.ne']
  have hdesc := smooth_descent_lp P.p_gt_one
    (holderConjugate_conjugateExponent P.p_gt_one)
    P.gradient_spec P.smooth P.x0 y
  change P.f y ≤ P.f P.x0 - G * D / 2
  rw [hypair, hynorm] at hdesc
  have hLM : P.L ≤ M := hscale
  nlinarith

/-- An accepted test controls the radius by the actual infimum distance to
the nonempty minimizer set.  No closest minimizer is selected or assumed. -/
theorem anchor_radius_le_two_minimizerDistance {d : ℕ} {p : ℝ}
    (P : AdmissibleInstance d p)
    (hGpos : 0 < lpNorm (conjugateExponent p) (P.grad P.x0))
    {D : ℝ} {y : Vec d}
    (haccept : AnchorTest P.f P.x0
      (lpNorm (conjugateExponent p) (P.grad P.x0)) D y) :
    D ≤ 2 * P.radius := by
  let G := lpNorm (conjugateExponent p) (P.grad P.x0)
  let distances : Set ℝ :=
    (fun x : Vec d ↦ lpNorm p (x - P.x0)) '' MinimizerSet P.f
  have hfirst : FirstOrderConvex P.f P.grad :=
    firstOrderConvex_of_coordinateGradient P.convex P.gradient_spec
  have hdistances : distances.Nonempty := P.minimizer_nonempty.image _
  have hhalf : D / 2 ≤ sInf distances := by
    apply le_csInf hdistances
    intro r hr
    rcases hr with ⟨xstar, hxstar, rfl⟩
    have hDx := anchorAccepted_radius P.p_gt_one hfirst hxstar
      (rfl : G = lpNorm (conjugateExponent p) (P.grad P.x0)) hGpos
      (le_refl (lpNorm p (xstar - P.x0))) haccept
    linarith
  change D ≤ 2 * minimizerDistance p P.f P.x0
  change D ≤ 2 * sInf distances
  linarith

/-- Once the deterministic loop has returned, additional unused fuel cannot
change its first accepted result. -/
theorem runAnchor_some_add_fuel {d : ℕ} (oracle : PairOracle d)
    (cfg : AnchorConfig d) {fuel start : ℕ} {history : OracleTrace d}
    {result : AnchorResult d}
    (hrun : runAnchor oracle cfg fuel start history = some result)
    (extra : ℕ) :
    runAnchor oracle cfg (fuel + extra) start history = some result := by
  induction fuel generalizing start history with
  | zero => simp [runAnchor] at hrun
  | succ fuel ih =>
      rw [Nat.succ_add, runAnchor]
      rw [runAnchor] at hrun
      let D := anchorRadius cfg.G cfg.M₀ start
      let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ start
      by_cases hnow : oracle.value y ≤ cfg.f₀ - cfg.G * D / 2
      · dsimp only [D, y] at hnow
        simp only [hnow, ↓reduceIte, Option.some.injEq] at hrun ⊢
        exact hrun
      · dsimp only [D, y] at hnow
        simp only [hnow, ↓reduceIte] at hrun ⊢
        exact ih hrun

/-- Transparent source-level carrier for the frozen gradient-ray anchor.  The
only quantified algorithmic object is the admissible instance; `L`, the
minimizer set, and its distance are used only in the correctness conclusion. -/
def AnchorStatement : Prop :=
  ∀ (p : ℝ) (d : ℕ) (P : AdmissibleInstance d p),
    let cfg := P.anchorConfig
    let N := Nat.ceil (Real.logb 2 (P.L / P.M0))
    P.eps < cfg.G →
    ∃ result,
      runAnchor P.oracle cfg (1 + N) 0 [] = some result ∧
      result.acceptedScale = anchorScale P.M0 result.epoch ∧
      result.acceptedRadius = cfg.G / result.acceptedScale ∧
      result.acceptedPoint =
        anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ result.epoch ∧
      AnchorTest P.f P.x0 cfg.G result.acceptedRadius result.acceptedPoint ∧
      result.acceptedScale < 2 * P.L ∧
      result.acceptedRadius ≤ 2 * P.radius ∧
      result.observations.length ≤ 1 + N ∧
      TraceExact P.oracle result.observations

/-- Native closure of TeX Lemma `lem:anchor`. -/
theorem anchor : AnchorStatement := by
  intro p d P
  dsimp only
  let cfg := P.anchorConfig
  let N := Nat.ceil (Real.logb 2 (P.L / P.M0))
  intro hGeps
  have hGpos : 0 < cfg.G := P.eps_pos.trans hGeps
  have hM0 : 0 < P.M0 := P.secant.2.2.2
  have hM0L : P.M0 ≤ P.L := by
    have hsec := secantScale_le (p := p) (q := conjugateExponent p)
      (L := P.L) P.smooth P.secant.1
    calc
      P.M0 = lpNorm (conjugateExponent p) (P.grad P.z0 - P.grad P.x0) /
          lpNorm p (P.z0 - P.x0) := P.secant.2.2.1
      _ = secantScale p (conjugateExponent p) P.grad P.x0 P.z0 := rfl
      _ ≤ P.L := hsec
  let cap := anchorScaleCap P.M0 P.L hM0
  have hcapN : cap ≤ N := by
    exact anchorScaleCap_le_logCeil hM0 P.L_pos
  have hcapPass :
      let D := anchorRadius cfg.G cfg.M₀ cap
      let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ cap
      P.oracle.value y ≤ cfg.f₀ - cfg.G * D / 2 := by
    apply anchor_cap_test_passes P
    · exact hGpos
    · exact anchorScaleCap_dominates hM0
  obtain ⟨result, hrunCap⟩ :=
    runAnchor_acceptsBy P.oracle cfg 0 cap [] (by simpa using hcapPass)
  have hrun : runAnchor P.oracle cfg (1 + N) 0 [] = some result := by
    have hext := runAnchor_some_add_fuel P.oracle cfg hrunCap (N - cap)
    have harith : cap + 1 + (N - cap) = 1 + N := by omega
    rwa [harith] at hext
  have hvalid := runAnchor_result_valid P.oracle cfg hrunCap
  have hepoch : result.epoch ≤ cap := by
    have he := runAnchor_epoch_lt P.oracle cfg hrunCap
    omega
  have hscale : result.acceptedScale < 2 * P.L := by
    rw [hvalid.1]
    exact (anchorScale_mono hM0.le hepoch).trans_lt
      (anchorScaleCap_lt_two_mul hM0 hM0L)
  have haccept : AnchorTest P.f P.x0 cfg.G result.acceptedRadius
      result.acceptedPoint := by
    exact hvalid.2.2.2
  have hradius : result.acceptedRadius ≤ 2 * P.radius := by
    apply anchor_radius_le_two_minimizerDistance P hGpos
    exact haccept
  have hcount : result.observations.length ≤ 1 + N := by
    have hc := runAnchor_callCount_le P.oracle cfg hrunCap
    simp only [List.length_nil, zero_add] at hc
    omega
  have htrace : TraceExact P.oracle result.observations :=
    runAnchor_traceExact P.oracle cfg (traceExact_nil P.oracle) hrunCap
  refine ⟨result, hrun, hvalid.1, ?_, hvalid.2.2.1, haccept,
    hscale, hradius, hcount, htrace⟩
  rw [hvalid.2.1, hvalid.1]
  rfl

end O3
