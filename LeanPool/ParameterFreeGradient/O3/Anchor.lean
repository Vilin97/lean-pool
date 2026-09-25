/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.Oracle

/-!
# Secant and accepted-anchor certificates

This module proves the parts of the gradient-ray anchor that reduce directly to
finite-dimensional `ell_p/ell_q` Hölder geometry.  It deliberately does not
postulate termination or an accepted trace as data.
-/

@[expose] public section

namespace O3

/-- The exact `ell_p → ell_q` Lipschitz-gradient hypothesis. -/
def LipschitzGradient {d : ℕ} (p q L : ℝ) (grad : Point d → Point d) : Prop :=
  ∀ x y, lpNorm q (grad x - grad y) ≤ L * lpNorm p (x - y)

/-- The supplied nondegenerate secant scale. -/
noncomputable def secantScale {d : ℕ} (p q : ℝ) (grad : Point d → Point d)
    (x₀ z₀ : Point d) : ℝ :=
  lpNorm q (grad z₀ - grad x₀) / lpNorm p (z₀ - x₀)

theorem secantScale_pos {d : ℕ} {p q : ℝ}
    {grad : Point d → Point d} {x₀ z₀ : Point d}
    (hx : z₀ ≠ x₀) (hg : grad z₀ ≠ grad x₀) :
    0 < secantScale p q grad x₀ z₀ := by
  have hxsub : z₀ - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hgsub : grad z₀ - grad x₀ ≠ 0 := sub_ne_zero.mpr hg
  exact div_pos (lpNorm_pos_of_ne_zero hgsub) (lpNorm_pos_of_ne_zero hxsub)

/-- The secant witness automatically gives the lower scale `M₀ ≤ L`. -/
theorem secantScale_le {d : ℕ} {p q L : ℝ}
    {grad : Point d → Point d} (hLip : LipschitzGradient p q L grad)
    {x₀ z₀ : Point d} (hx : z₀ ≠ x₀) :
    secantScale p q grad x₀ z₀ ≤ L := by
  have hxsub : z₀ - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hden : 0 < lpNorm p (z₀ - x₀) := lpNorm_pos_of_ne_zero hxsub
  rw [secantScale, div_le_iff₀ hden]
  simpa [mul_comm] using hLip z₀ x₀

/-- A first-order convexity inequality, kept explicit so that no ambient
Euclidean norm silently replaces the frozen `ell_p` geometry. -/
def FirstOrderConvex {d : ℕ} (f : Point d → ℝ) (grad : Point d → Point d) : Prop :=
  ∀ x y, f x + pairing (grad x) (y - x) ≤ f y

/-- The observable anchor test at distance `D`. -/
def AnchorTest {d : ℕ} (f : Point d → ℝ) (x₀ : Point d) (G D : ℝ)
    (y : Point d) : Prop :=
  f y ≤ f x₀ - G * D / 2

/-- The accepted anchor test and first-order convexity imply the exact radius
certificate `D ≤ 2R`.  No optimizer or radius is supplied to the algorithm;
they occur only in this correctness proof. -/
theorem anchorAccepted_radius {d : ℕ} {p : ℝ} (hp : 1 < p)
    {f : Point d → ℝ} {grad : Point d → Point d}
    (hconv : FirstOrderConvex f grad)
    {x₀ xstar y : Point d} {G D R : ℝ}
    (hmin : ∀ x, f xstar ≤ f x)
    (hG : G = lpNorm (conjugateExponent p) (grad x₀))
    (hGpos : 0 < G)
    (hR : lpNorm p (xstar - x₀) ≤ R)
    (haccept : AnchorTest f x₀ G D y) :
    D ≤ 2 * R := by
  have hpq := holderConjugate_conjugateExponent hp
  have hpair :
      -G * R ≤ pairing (grad x₀) (xstar - x₀) := by
    have hholder := pairing_le_lpNorm_mul hpq (xstar - x₀) (-(grad x₀))
    rw [pairing_neg_right, lpNorm_neg, ← hG] at hholder
    have hnorm : 0 ≤ lpNorm p (xstar - x₀) := lpNorm_nonneg _ _
    have hGR : G * lpNorm p (xstar - x₀) ≤ G * R :=
      mul_le_mul_of_nonneg_left hR hGpos.le
    rw [pairing_comm]
    linarith
  have hlow : f x₀ - G * R ≤ f xstar := by
    have := hconv x₀ xstar
    linarith
  have hchain : f x₀ - G * R ≤ f x₀ - G * D / 2 :=
    hlow.trans ((hmin y).trans haccept)
  have : G * D ≤ 2 * (G * R) := by linarith
  nlinarith

/-- The explicit coordinate norming direction used by the frozen anchor. -/
noncomputable def anchorNormingVector {d : ℕ} (q : ℝ) (g : Vec d) : Vec d :=
  fun i =>
    ((SignType.sign (g i) : ℝ) * |g i| ^ (q - 1)) /
      (lpNorm q g) ^ (q - 1)

/-- Dyadic curvature scale `2^epoch M₀`. -/
noncomputable def anchorScale (M₀ : ℝ) (epoch : ℕ) : ℝ :=
  (2 : ℝ) ^ epoch * M₀

/-- Exact radius tested at one dyadic scale. -/
noncomputable def anchorRadius (G M₀ : ℝ) (epoch : ℕ) : ℝ :=
  G / anchorScale M₀ epoch

/-- Exact gradient-ray point queried at one dyadic scale. -/
noncomputable def anchorProbePoint {d : ℕ} (q : ℝ) (x₀ g₀ : Vec d)
    (G M₀ : ℝ) (epoch : ℕ) : Vec d :=
  x₀ - anchorRadius G M₀ epoch • anchorNormingVector q g₀

/-- Inputs already available after the counted query at `x₀`. -/
structure AnchorConfig (d : ℕ) where
  /-- The exponent used to normalize the anchor search direction. -/
  q : ℝ
  /-- The initial point from which anchor probes are taken. -/
  x₀ : Vec d
  /-- The observed objective value at the initial point. -/
  f₀ : ℝ
  /-- The observed gradient at the initial point. -/
  g₀ : Vec d
  /-- The initial gradient size used to set probe radii. -/
  G : ℝ
  /-- The initial scale estimate for the dyadic anchor search. -/
  M₀ : ℝ

/-- Data returned by the first accepted probe; no correctness claim is a field. -/
structure AnchorResult (d : ℕ) where
  /-- The dyadic epoch at which the anchor probe was accepted. -/
  epoch : ℕ
  /-- The scale estimate associated with the accepted anchor probe. -/
  acceptedScale : ℝ
  /-- The radius associated with the accepted anchor probe. -/
  acceptedRadius : ℝ
  /-- The point returned by the accepted anchor probe. -/
  acceptedPoint : Vec d
  /-- All pair-oracle responses collected during the anchor search. -/
  observations : OracleTrace d

/--
The actual fuel-bounded dyadic anchor loop.  Every iteration makes exactly one
pair-oracle query, tests its returned value, and either stops or doubles the
scale by incrementing `epoch`.
-/
noncomputable def runAnchor {d : ℕ} (oracle : PairOracle d) (cfg : AnchorConfig d) :
    ℕ → ℕ → OracleTrace d → Option (AnchorResult d)
  | 0, _, _ => none
  | fuel + 1, epoch, history =>
      let M := anchorScale cfg.M₀ epoch
      let D := anchorRadius cfg.G cfg.M₀ epoch
      let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ epoch
      let observation := oracle.observe y
      let history' := history ++ [observation]
      if oracle.value y ≤ cfg.f₀ - cfg.G * D / 2 then
        some
          { epoch := epoch
            acceptedScale := M
            acceptedRadius := D
            acceptedPoint := y
            observations := history' }
      else runAnchor oracle cfg fuel (epoch + 1) history'

theorem anchorScale_succ (M₀ : ℝ) (epoch : ℕ) :
    anchorScale M₀ (epoch + 1) = 2 * anchorScale M₀ epoch := by
  simp [anchorScale, pow_succ]
  ring

theorem anchorScale_mono {M₀ : ℝ} (hM₀ : 0 ≤ M₀) {i j : ℕ} (hij : i ≤ j) :
    anchorScale M₀ i ≤ anchorScale M₀ j := by
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hij) hM₀

theorem exists_anchor_scale_ge {M₀ L : ℝ} (hM₀ : 0 < M₀) :
    ∃ epoch, L ≤ anchorScale M₀ epoch := by
  obtain ⟨epoch, hepoch⟩ :=
    pow_unbounded_of_one_lt (L / M₀) (by norm_num : (1 : ℝ) < 2)
  refine ⟨epoch, ?_⟩
  rw [anchorScale, ← div_le_iff₀ hM₀]
  exact hepoch.le

/-- First dyadic scale which dominates `L`; this is proof-side, not method input. -/
noncomputable def anchorScaleCap (M₀ L : ℝ) (hM₀ : 0 < M₀) : ℕ :=
  Nat.find (exists_anchor_scale_ge (L := L) hM₀)

theorem anchorScaleCap_dominates {M₀ L : ℝ} (hM₀ : 0 < M₀) :
    L ≤ anchorScale M₀ (anchorScaleCap M₀ L hM₀) := by
  exact Nat.find_spec (exists_anchor_scale_ge (L := L) hM₀)

theorem anchorScaleCap_lt_two_mul {M₀ L : ℝ}
    (hM₀ : 0 < M₀) (hM₀L : M₀ ≤ L) :
    anchorScale M₀ (anchorScaleCap M₀ L hM₀) < 2 * L := by
  generalize hcap : anchorScaleCap M₀ L hM₀ = cap
  cases cap with
  | zero =>
      simpa [anchorScale] using hM₀L.trans_lt (by linarith : L < 2 * L)
  | succ n =>
      have hnlt : n < anchorScaleCap M₀ L hM₀ := by
        rw [hcap]
        omega
      have hnot := Nat.find_min (exists_anchor_scale_ge (L := L) hM₀) hnlt
      have hn : anchorScale M₀ n < L := lt_of_not_ge hnot
      rw [anchorScale_succ]
      linarith

/-- If a specified later probe passes, the deterministic loop succeeds no later. -/
theorem runAnchor_acceptsBy {d : ℕ} (oracle : PairOracle d) (cfg : AnchorConfig d)
    (start extra : ℕ) (history : OracleTrace d)
    (hpass :
      let epoch := start + extra
      let D := anchorRadius cfg.G cfg.M₀ epoch
      let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ epoch
      oracle.value y ≤ cfg.f₀ - cfg.G * D / 2) :
    ∃ result, runAnchor oracle cfg (extra + 1) start history = some result := by
  induction extra generalizing start history with
  | zero =>
      dsimp only at hpass
      simp only [Nat.add_zero] at hpass
      simp [runAnchor, hpass]
  | succ extra ih =>
      rw [runAnchor]
      let D := anchorRadius cfg.G cfg.M₀ start
      let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ start
      by_cases hnow : oracle.value y ≤ cfg.f₀ - cfg.G * D / 2
      · dsimp only [D, y] at hnow
        simp [hnow]
      · dsimp only [D, y] at hnow
        simp only [hnow, ↓reduceIte]
        apply ih (start := start + 1)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpass

/-- Any successful loop result records the accepted test and exact dyadic data. -/
theorem runAnchor_result_valid {d : ℕ} (oracle : PairOracle d) (cfg : AnchorConfig d)
    {fuel start : ℕ} {history : OracleTrace d} {result : AnchorResult d}
    (hrun : runAnchor oracle cfg fuel start history = some result) :
    result.acceptedScale = anchorScale cfg.M₀ result.epoch ∧
    result.acceptedRadius = anchorRadius cfg.G cfg.M₀ result.epoch ∧
    result.acceptedPoint =
      anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ result.epoch ∧
    oracle.value result.acceptedPoint ≤
      cfg.f₀ - cfg.G * result.acceptedRadius / 2 := by
  induction fuel generalizing start history with
  | zero => simp [runAnchor] at hrun
  | succ fuel ih =>
      rw [runAnchor] at hrun
      let D := anchorRadius cfg.G cfg.M₀ start
      let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ start
      by_cases hnow : oracle.value y ≤ cfg.f₀ - cfg.G * D / 2
      · dsimp only [D, y] at hnow
        simp only [hnow, ↓reduceIte, Option.some.injEq] at hrun
        subst result
        exact ⟨rfl, rfl, rfl, hnow⟩
      · dsimp only [D, y] at hnow
        simp only [hnow, ↓reduceIte] at hrun
        exact ih hrun

/-- Successful execution records only exact oracle observations. -/
theorem runAnchor_traceExact {d : ℕ} (oracle : PairOracle d) (cfg : AnchorConfig d)
    {fuel start : ℕ} {history : OracleTrace d} {result : AnchorResult d}
    (hhistory : TraceExact oracle history)
    (hrun : runAnchor oracle cfg fuel start history = some result) :
    TraceExact oracle result.observations := by
  induction fuel generalizing start history with
  | zero => simp [runAnchor] at hrun
  | succ fuel ih =>
      rw [runAnchor] at hrun
      let D := anchorRadius cfg.G cfg.M₀ start
      let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ start
      have hnext : TraceExact oracle (history ++ [oracle.observe y]) := by
        apply traceExact_append hhistory
        intro observation hobservation
        simp only [List.mem_singleton] at hobservation
        subst observation
        rfl
      by_cases hnow : oracle.value y ≤ cfg.f₀ - cfg.G * D / 2
      · dsimp only [D, y] at hnow
        simp only [hnow, ↓reduceIte, Option.some.injEq] at hrun
        subst result
        exact hnext
      · dsimp only [D, y] at hnow
        simp only [hnow, ↓reduceIte] at hrun
        exact ih hnext hrun

theorem runAnchor_epoch_lt {d : ℕ} (oracle : PairOracle d) (cfg : AnchorConfig d)
    {fuel start : ℕ} {history : OracleTrace d} {result : AnchorResult d}
    (hrun : runAnchor oracle cfg fuel start history = some result) :
    result.epoch < start + fuel := by
  induction fuel generalizing start history with
  | zero => simp [runAnchor] at hrun
  | succ fuel ih =>
      rw [runAnchor] at hrun
      by_cases hnow :
          oracle.value (anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ start) ≤
            cfg.f₀ - cfg.G * anchorRadius cfg.G cfg.M₀ start / 2
      · simp only [hnow, ↓reduceIte, Option.some.injEq] at hrun
        subst result
        change start < start + (fuel + 1)
        omega
      · simp only [hnow, ↓reduceIte] at hrun
        have := ih hrun
        omega

theorem runAnchor_callCount_le {d : ℕ} (oracle : PairOracle d) (cfg : AnchorConfig d)
    {fuel start : ℕ} {history : OracleTrace d} {result : AnchorResult d}
    (hrun : runAnchor oracle cfg fuel start history = some result) :
    result.observations.length ≤ history.length + fuel := by
  induction fuel generalizing start history with
  | zero => simp [runAnchor] at hrun
  | succ fuel ih =>
      rw [runAnchor] at hrun
      by_cases hnow :
          oracle.value (anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ start) ≤
            cfg.f₀ - cfg.G * anchorRadius cfg.G cfg.M₀ start / 2
      · simp [hnow] at hrun
        subst result
        simp
      · simp only [hnow, ↓reduceIte] at hrun
        have hbound := ih hrun
        simp only [List.length_append, List.length_singleton] at hbound
        omega

/--
Everything in the anchor conclusion after the analytic descent implication:
the concrete loop terminates, uses at most `cap+1` probes, returns exact data,
and satisfies both scale and radius certificates.
-/
theorem anchor_of_cap_acceptance {d : ℕ} {p L R : ℝ} (hp : 1 < p)
    (oracle : PairOracle d) (cfg : AnchorConfig d)
    (hM₀ : 0 < cfg.M₀) (hM₀L : cfg.M₀ ≤ L)
    (hbase : cfg.f₀ = oracle.value cfg.x₀)
    (hconv : FirstOrderConvex oracle.value oracle.gradient)
    (xstar : Vec d) (hmin : ∀ x, oracle.value xstar ≤ oracle.value x)
    (hG : cfg.G = lpNorm (conjugateExponent p) (oracle.gradient cfg.x₀))
    (hGpos : 0 < cfg.G) (hR : lpNorm p (xstar - cfg.x₀) ≤ R)
    (hcapPass :
      let cap := anchorScaleCap cfg.M₀ L hM₀
      let D := anchorRadius cfg.G cfg.M₀ cap
      let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ cap
      oracle.value y ≤ cfg.f₀ - cfg.G * D / 2) :
    ∃ result,
      runAnchor oracle cfg (anchorScaleCap cfg.M₀ L hM₀ + 1) 0 [] = some result ∧
      result.acceptedScale < 2 * L ∧
      result.acceptedRadius ≤ 2 * R ∧
      result.observations.length ≤ anchorScaleCap cfg.M₀ L hM₀ + 1 ∧
      TraceExact oracle result.observations := by
  let cap := anchorScaleCap cfg.M₀ L hM₀
  obtain ⟨result, hrun⟩ := runAnchor_acceptsBy oracle cfg 0 cap [] (by simpa [cap] using hcapPass)
  have hvalid := runAnchor_result_valid oracle cfg hrun
  have hepoch : result.epoch ≤ cap := by
    have := runAnchor_epoch_lt oracle cfg hrun
    omega
  have hscaleMono : anchorScale cfg.M₀ result.epoch ≤ anchorScale cfg.M₀ cap :=
    anchorScale_mono hM₀.le hepoch
  have hscaleCap : anchorScale cfg.M₀ cap < 2 * L := by
    simpa [cap] using anchorScaleCap_lt_two_mul hM₀ hM₀L
  have haccept : AnchorTest oracle.value cfg.x₀ cfg.G result.acceptedRadius
      result.acceptedPoint := by
    rw [AnchorTest, ← hbase]
    exact hvalid.2.2.2
  have hradius : result.acceptedRadius ≤ 2 * R :=
    anchorAccepted_radius hp hconv hmin hG hGpos hR haccept
  refine ⟨result, ?_, ?_, hradius, ?_, ?_⟩
  · simpa [cap] using hrun
  · rw [hvalid.1]
    exact hscaleMono.trans_lt hscaleCap
  · simpa [cap] using runAnchor_callCount_le oracle cfg hrun
  · exact runAnchor_traceExact oracle cfg (traceExact_nil oracle) hrun

end O3
