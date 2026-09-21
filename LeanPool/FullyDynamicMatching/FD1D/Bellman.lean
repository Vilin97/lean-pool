/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.PolynomialCertificate

/-! # Bellman -/

namespace FD1D

noncomputable section

/-!
# The deterministic Bellman certificate

This file formalizes the local Bellman inequality and the exact four-chart
certificate in `optimal_dynamic_matching.tex`.  The coefficient checks use
the kernel-checked integer polynomials in `FD1D.PolynomialCertificate`; the
surrounding lemmas connect them to the real-valued Bellman residual.
-/

/-- The cubic scalar weight in the Bellman function. -/
def d (y : ℝ) : ℝ :=
  (1 + 7 * y ^ 3) / 12

/-- The Bellman function from equation (6). -/
def B (h t y : ℝ) : ℝ :=
  d y * (t - y * h) * (2 * h - t - (3 / 2 : ℝ) * y * h)

/-- `W = w²` in the normalized local variables. -/
def normalizedW (s v : ℝ) : ℝ :=
  s * (1 + v) * v / (s + 2)

/-- The normalized residual in equation (8). -/
def normalizedResidual (s r v : ℝ) : ℝ :=
  let A := 1 + v
  let W := normalizedW s v
  let y := (s + r) / (s + 1)
  let Y := (s + r) / (s + 2 + 2 * v)
  Y * (r * A / 2 + W) +
    d Y *
      (-(r ^ 2 / 4 + W) +
        (2 - Y / 2) * (r * A / 2 + W) +
        ((3 / 2 : ℝ) * Y ^ 2 - 2 * Y) * (A ^ 2 + W)) -
    d y * (r - y) * (2 - r - (3 / 2 : ℝ) * y) -
    (1 / 100 : ℝ) * (A ^ 2 + W - 1)

/-- Short mathematical name for the normalized residual. -/
abbrev R (s r v : ℝ) : ℝ := normalizedResidual s r v

/-- The cleared polynomial `P` from the exact certificate. -/
def bellmanPolynomial (s r v : ℝ) : ℝ :=
  let A := 1 + v
  let S := s + 2
  let BB := s + 1
  let C := s + r
  let M := s + 2 + 2 * v
  let W0 := s * A * v
  let dB := BB ^ 3 + 7 * C ^ 3
  let dM := M ^ 3 + 7 * C ^ 3
  let bp :=
    -2 * BB ^ 2 * r ^ 2 + (4 * BB ^ 2 - BB * C) * r +
      3 * C ^ 2 - 4 * BB * C
  let bc :=
    -M ^ 2 * (r ^ 2 * S + 4 * W0) +
      M * (4 * M - C) * (r * A * S + 2 * W0) +
      2 * C * (3 * C - 4 * M) * (A ^ 2 * S + W0)
  600 * BB ^ 5 * M ^ 4 * C * (r * A * S + 2 * W0) +
    25 * BB ^ 5 * dM * bc -
    50 * S * M ^ 5 * dB * bp -
    12 * BB ^ 5 * M ^ 5 * (S * (A ^ 2 - 1) + W0)

/-- Short mathematical name for the cleared polynomial certificate. -/
abbrev P (s r v : ℝ) : ℝ := bellmanPolynomial s r v

/-- The positive denominator used to clear the normalized residual. -/
def bellmanDenominator (s v : ℝ) : ℝ :=
  1200 * (s + 1) ^ 5 * (s + 2) * (s + 2 + 2 * v) ^ 5

/--
The exact bridge omitted by a bare coefficient check: equation (8), after
clearing its rational denominators, is exactly equation (13).
-/
theorem normalizedResidual_mul_denominator
    {s r v : ℝ}
    (hs1 : s + 1 ≠ 0) (hs2 : s + 2 ≠ 0)
    (hM : s + 2 + 2 * v ≠ 0) :
    normalizedResidual s r v * bellmanDenominator s v =
      bellmanPolynomial s r v := by
  dsimp [normalizedResidual, normalizedW, bellmanDenominator,
    bellmanPolynomial, d]
  field_simp
  ring

theorem normalizedResidual_eq_div
    {s r v : ℝ}
    (hs1 : s + 1 ≠ 0) (hs2 : s + 2 ≠ 0)
    (hM : s + 2 + 2 * v ≠ 0) :
    normalizedResidual s r v =
      bellmanPolynomial s r v / bellmanDenominator s v := by
  rw [eq_div_iff]
  · exact normalizedResidual_mul_denominator hs1 hs2 hM
  · unfold bellmanDenominator
    positivity

/-!
## Exact four-chart certificate

Each transformed polynomial has nonnegative integer coefficients.  The
certificate module computes and kernel-checks those coefficients, proves its
evaluator sound, and exposes the resulting real nonnegativity theorems.
-/

private def chartPlus (u v z : ℝ) : ℝ :=
  (2 * (1 + u)) ^ 5 *
    bellmanPolynomial (2 * v + z) (u / (2 * (1 + u))) v

private theorem chartPlus_nonnegative
    {u v z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ chartPlus u v z := by
  have hden : 2 * (1 + u) ≠ 0 := by positivity
  have h := BellmanCertificate.chartPlus_nonnegative hu hv hz
  rw [BellmanCertificate.projectiveBellmanRealAt_eq hden] at h
  simpa [chartPlus, bellmanPolynomial,
    BellmanCertificate.bellmanRealAt] using h

private def chartOne (u v z : ℝ) : ℝ :=
  bellmanPolynomial (2 * u + 2 * v + z) (-u) (u + v)

private theorem chartOne_nonnegative
    {u v z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ chartOne u v z := by
  simpa [chartOne, bellmanPolynomial,
    BellmanCertificate.bellmanRealAt] using
      BellmanCertificate.chartOne_nonnegative hu hv hz

private def chartTwo (u v z : ℝ) : ℝ :=
  bellmanPolynomial (2 * u + 2 * v + z) (-2 * u - v) (u + v)

private theorem chartTwo_nonnegative
    {u v z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ chartTwo u v z := by
  simpa [chartTwo, bellmanPolynomial,
    BellmanCertificate.bellmanRealAt] using
      BellmanCertificate.chartTwo_nonnegative hu hv hz

private def chartThree (u v z : ℝ) : ℝ :=
  bellmanPolynomial (u + 2 * v + z) (-u - 2 * v) v

private theorem chartThree_nonnegative
    {u v z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ chartThree u v z := by
  simpa [chartThree, bellmanPolynomial,
    BellmanCertificate.bellmanRealAt] using
      BellmanCertificate.chartThree_nonnegative hu hv hz

private theorem chartPlus_endpoint_nonnegative
    {v z : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ bellmanPolynomial (2 * v + z) (1 / 2) v := by
  have h :=
    BellmanCertificate.chartEndpoint_nonnegative hv hz
  rw [BellmanCertificate.projectiveBellmanRealAt_eq
    (by norm_num : (2 : ℝ) ≠ 0)] at h
  have hprod :
      0 ≤ (2 : ℝ) ^ 5 *
        bellmanPolynomial (2 * v + z) (1 / 2) v := by
    simpa [bellmanPolynomial, BellmanCertificate.bellmanRealAt] using h
  exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 2 ^ 5)).mp
    hprod

/-- The four charts cover the full closed normalized domain. -/
theorem bellmanPolynomial_nonnegative_closed
    {s r v : ℝ}
    (_hs : 0 ≤ s) (hrLower : -s ≤ r) (hrUpper : r ≤ 1 / 2)
    (hv : 0 ≤ v) (hvUpper : v ≤ s / 2) :
    0 ≤ bellmanPolynomial s r v := by
  by_cases hr : 0 ≤ r
  · by_cases hend : r = 1 / 2
    · subst r
      have hz : 0 ≤ s - 2 * v := by linarith
      simpa [show 2 * v + (s - 2 * v) = s by ring] using
        chartPlus_endpoint_nonnegative hv hz
    · have hrStrict : r < 1 / 2 := lt_of_le_of_ne hrUpper hend
      let u := 2 * r / (1 - 2 * r)
      let z := s - 2 * v
      have hbase : 0 < 1 - 2 * r := by linarith
      have hu : 0 ≤ u := by
        dsimp [u]
        positivity
      have hz : 0 ≤ z := by
        dsimp [z]
        linarith
      have hsCoord : 2 * v + z = s := by
        dsimp [z]
        ring
      have hrCoord : u / (2 * (1 + u)) = r := by
        dsimp [u]
        field_simp
        ring
      have hchart := chartPlus_nonnegative hu hv hz
      rw [chartPlus, hsCoord, hrCoord] at hchart
      have hscale : 0 < (2 * (1 + u)) ^ 5 := by positivity
      exact (mul_nonneg_iff_of_pos_left hscale).mp hchart
  · have hrNonpos : r ≤ 0 := le_of_not_ge hr
    let k : ℝ := -r
    have hk : 0 ≤ k := by
      dsimp [k]
      linarith
    have hkUpper : k ≤ s := by
      dsimp [k]
      linarith
    have hzBase : 0 ≤ s - 2 * v := by linarith
    by_cases hkOne : k ≤ v
    · let u := k
      let v' := v - k
      let z := s - 2 * v
      have hu : 0 ≤ u := by simpa [u] using hk
      have hv' : 0 ≤ v' := by
        dsimp [v']
        linarith
      have hz : 0 ≤ z := by
        dsimp [z]
        linarith
      have hsCoord : 2 * u + 2 * v' + z = s := by
        dsimp [u, v', z]
        ring
      have hrCoord : -u = r := by
        dsimp [u, k]
        ring
      have hvCoord : u + v' = v := by
        dsimp [u, v']
        ring
      simpa [chartOne, hsCoord, hrCoord, hvCoord] using
        chartOne_nonnegative hu hv' hz
    · have hvk : v ≤ k := le_of_not_ge hkOne
      by_cases hkTwo : k ≤ 2 * v
      · let u := k - v
        let v' := 2 * v - k
        let z := s - 2 * v
        have hu : 0 ≤ u := by
          dsimp [u]
          linarith
        have hv' : 0 ≤ v' := by
          dsimp [v']
          linarith
        have hz : 0 ≤ z := by simpa [z] using hzBase
        have hsCoord : 2 * u + 2 * v' + z = s := by
          dsimp [u, v', z]
          ring
        have hrCoord : -2 * u - v' = r := by
          dsimp [u, v', k]
          ring
        have hvCoord : u + v' = v := by
          dsimp [u, v']
          ring
        have hchart := chartTwo_nonnegative hu hv' hz
        rw [chartTwo] at hchart
        convert hchart using 1 ;
          dsimp [u, v', z, k] ;
          ring
      · have hTwoK : 2 * v ≤ k := le_of_not_ge hkTwo
        let u := k - 2 * v
        let z := s - k
        have hu : 0 ≤ u := by
          dsimp [u]
          linarith
        have hz : 0 ≤ z := by
          dsimp [z]
          linarith
        have hsCoord : u + 2 * v + z = s := by
          dsimp [u, z]
          ring
        have hrCoord : -u - 2 * v = r := by
          dsimp [u, k]
          ring
        simpa [chartThree, hsCoord, hrCoord] using
          chartThree_nonnegative hu hv hz

/-- Polynomial nonnegativity on the (strict-lower-bound) physical domain. -/
theorem bellmanPolynomial_nonnegative
    {s r v : ℝ}
    (hs : 0 ≤ s) (hrLower : -s < r) (hrUpper : r ≤ 1 / 2)
    (hv : 0 ≤ v) (hvUpper : v ≤ s / 2) :
    0 ≤ bellmanPolynomial s r v :=
  bellmanPolynomial_nonnegative_closed hs hrLower.le hrUpper hv hvUpper

/-- The normalized local Bellman residual is nonnegative on its full domain. -/
theorem normalizedResidual_nonnegative
    {s r v : ℝ}
    (hs : 0 ≤ s) (hrLower : -s < r) (hrUpper : r ≤ 1 / 2)
    (hv : 0 ≤ v) (hvUpper : v ≤ s / 2) :
    0 ≤ normalizedResidual s r v := by
  have hs1 : 0 < s + 1 := by linarith
  have hs2 : 0 < s + 2 := by linarith
  have hM : 0 < s + 2 + 2 * v := by linarith
  have hP :=
    bellmanPolynomial_nonnegative hs hrLower hrUpper hv hvUpper
  rw [← normalizedResidual_mul_denominator hs1.ne' hs2.ne' hM.ne'] at hP
  have hden : 0 < bellmanDenominator s v := by
    unfold bellmanDenominator
    positivity
  exact nonneg_of_mul_nonneg_left hP hden

/-! ## The local Bellman inequality -/

/--
Equation (7), moved to the left-hand side and written in the canonical
normalized child coordinates.
-/
def localBellmanGap (h s r v w : ℝ) : ℝ :=
  let A := 1 + v
  let y := (s + r) / (s + 1)
  let Y := (s + r) / (s + 2 + 2 * v)
  let hL := h * (A + w)
  let hR := h * (A - w)
  let tL := h * (r / 2 + w)
  let tR := h * (r / 2 - w)
  let ZL := Y * hL
  let ZR := Y * hR
  (tL * ZL + tR * ZR) / 2 +
      (B hL tL Y + B hR tR Y) / 2 -
      B h (h * r) y -
    (1 / 100 : ℝ) * ((hL ^ 2 + hR ^ 2) / 2 - h ^ 2)

/-- Exact algebra connecting the normalized residual to equation (7). -/
theorem localBellmanGap_eq
    {h s r v w : ℝ} (hw : w ^ 2 = normalizedW s v) :
    localBellmanGap h s r v w =
      h ^ 2 * normalizedResidual s r v := by
  unfold localBellmanGap normalizedResidual
  dsimp only
  rw [← hw]
  unfold B d
  ring

/-- Canonical normalized form of the full deterministic local lemma (7). -/
theorem localBellmanGap_nonnegative
    {h s r v w : ℝ}
    (hs : 0 ≤ s) (hrLower : -s < r) (hrUpper : r ≤ 1 / 2)
    (hv : 0 ≤ v) (hvUpper : v ≤ s / 2)
    (hw : w ^ 2 = normalizedW s v) :
    0 ≤ localBellmanGap h s r v w := by
  rw [localBellmanGap_eq hw]
  exact mul_nonneg (sq_nonneg h)
    (normalizedResidual_nonnegative hs hrLower hrUpper hv hvUpper)

/--
A reusable form of (7).  Callers need only provide the normalized identities
for their parent and two children.
-/
theorem local_bellman_inequality
    {h t y hL hR tL tR yL yR ZL ZR s r v w : ℝ}
    (hs : 0 ≤ s) (hrLower : -s < r) (hrUpper : r ≤ 1 / 2)
    (hv : 0 ≤ v) (hvUpper : v ≤ s / 2)
    (hw : w ^ 2 = normalizedW s v)
    (ht : t = h * r)
    (hy : y = (s + r) / (s + 1))
    (hhL : hL = h * (1 + v + w))
    (hhR : hR = h * (1 + v - w))
    (htL : tL = h * (r / 2 + w))
    (htR : tR = h * (r / 2 - w))
    (hyL : yL = (s + r) / (s + 2 + 2 * v))
    (hyR : yR = (s + r) / (s + 2 + 2 * v))
    (hZL : ZL = yL * hL) (hZR : ZR = yR * hR) :
    (tL * ZL + tR * ZR) / 2 +
        (B hL tL yL + B hR tR yR) / 2 - B h t y ≥
      (1 / 100 : ℝ) * ((hL ^ 2 + hR ^ 2) / 2 - h ^ 2) := by
  subst t
  subst y
  subst hL
  subst hR
  subst tL
  subst tR
  subst yL
  subst yR
  subst ZL
  subst ZR
  have hgap :=
    localBellmanGap_nonnegative (h := h) hs hrLower hrUpper hv hvUpper hw
  dsimp [localBellmanGap] at hgap
  linarith

/-! ## Terminal and root bounds -/

theorem d_nonnegative {y : ℝ} (hy : 0 ≤ y) : 0 ≤ d y := by
  unfold d
  positivity

/--
The sign argument used at terminal nodes: if `t = hr`, `r ≤ y ≤ 1`, and
`r ≤ 1/2`, then the Bellman value is nonpositive.
-/
theorem bellman_nonpositive
    {h r y : ℝ}
    (hh : 0 ≤ h) (hr : r ≤ 1 / 2)
    (_hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hry : r ≤ y) :
    B h (h * r) y ≤ 0 := by
  have hfirst : h * r - y * h ≤ 0 := by
    rw [show h * r - y * h = h * (r - y) by ring]
    exact mul_nonpos_of_nonneg_of_nonpos hh (sub_nonpos.mpr hry)
  have hcoefficient : 0 ≤ 2 - r - (3 / 2 : ℝ) * y := by
    linarith
  have hsecond :
      0 ≤ 2 * h - h * r - (3 / 2 : ℝ) * y * h := by
    rw [show 2 * h - h * r - (3 / 2 : ℝ) * y * h =
      h * (2 - r - (3 / 2 : ℝ) * y) by ring]
    exact mul_nonneg hh hcoefficient
  unfold B
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (d_nonnegative _hy0) hfirst) hsecond

/-- The parent Bellman value is nonpositive throughout the normalized domain. -/
theorem normalized_bellman_nonpositive
    {h s r : ℝ}
    (hh : 0 ≤ h) (hs : 0 ≤ s)
    (hrLower : -s < r) (hrUpper : r ≤ 1 / 2) :
    B h (h * r) ((s + r) / (s + 1)) ≤ 0 := by
  have hden : 0 < s + 1 := by linarith
  have hy0 : 0 ≤ (s + r) / (s + 1) := by
    exact div_nonneg (by linarith) hden.le
  have hy1 : (s + r) / (s + 1) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  have hr1 : r ≤ 1 := by linarith
  have hsr : s * r ≤ s := by
    simpa using mul_le_mul_of_nonneg_left hr1 hs
  have hry : r ≤ (s + r) / (s + 1) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  exact bellman_nonpositive hh hrUpper hy0 hy1 hry

/-- Exact polynomial identity behind the root estimate. -/
theorem root_bellman_identity (h y : ℝ) :
    h ^ 2 / 3 + B h 0 y =
      h ^ 2 * (1 - y) *
        (5 + (1 - y) * (3 + 7 * y + 14 * y ^ 2 + 21 * y ^ 3)) / 24 := by
  unfold B d
  ring

/-- At the root, `B(h,0,y) ≥ -h²/3`. -/
theorem bellman_root_bound
    {h y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    -(h ^ 2) / 3 ≤ B h 0 y := by
  have hpoly :
      0 ≤ 5 + (1 - y) * (3 + 7 * y + 14 * y ^ 2 + 21 * y ^ 3) := by
    positivity
  have hrhs :
      0 ≤ h ^ 2 * (1 - y) *
        (5 + (1 - y) * (3 + 7 * y + 14 * y ^ 2 + 21 * y ^ 3)) / 24 := by
    positivity
  nlinarith [root_bellman_identity h y]

/-- Root bound in the `h = 1/m` normalization used in the tree proof. -/
theorem bellman_root_bound_inv
    {m y : ℝ} (hm : 0 < m) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    -1 / (3 * m ^ 2) ≤ B (1 / m) 0 y := by
  have h := bellman_root_bound (h := 1 / m) hy0 hy1
  calc
    -1 / (3 * m ^ 2) = -((1 / m) ^ 2) / 3 := by
      field_simp
    _ ≤ B (1 / m) 0 y := h

end

end FD1D
