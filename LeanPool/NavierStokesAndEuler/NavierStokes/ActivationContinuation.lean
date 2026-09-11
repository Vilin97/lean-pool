/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActivationCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.TransitionRamp
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalEntrance
public import LeanPool.NavierStokesAndEuler.NavierStokes.ReferencePath
import LeanPool.NavierStokesAndEuler.NavierStokes.ReferenceJetBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The relaxed continuation after the initial activation

The comparison formulas use actual stock coordinates. The scalar barrier
uses the differential equation of the primitive-defined angular lag.
-/

section

/-!
# Bounds for the actual reference continuation

The history estimates below use the primitive-defined lags and pressure of
`ProfileHistories`. The reference source estimates and the ordered parameter
choices are derived from the constructed natural and reference profiles.
-/

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.ReferenceBounds

open ProfileHistories

section Histories

variable {D : RadialDomain} (P : Profiles D)

/-- Log slope, given by `1 + p.1 * radialPartial P.f p / P.f p`. -/
noncomputable def logSlope (p : Point) : ℝ :=
  1 + p.1 * radialPartial P.f p / P.f p

/-- Source Q as an element of `ℝ`. -/
noncomputable def sourceQ (h : ℝ) (p : Point) : ℝ :=
  -P.W h p * logSlope P p - h * (1 - 2 * p.2 * P.U p) -
    (StressAlgebra.axialExponent h * p.2 + StressAlgebra.coordinateFactor p.2 * P.U p) *
      (parameterPartial P.f p / P.f p)

/-- P1, given by `p.1 * P.angularLag h p / NaturalAxisData.L h p.2`. -/
noncomputable def p1 (h : ℝ) (p : Point) : ℝ :=
  p.1 * P.angularLag h p / NaturalAxisData.L h p.2

/-- Ns, given by `P.axialLag h p / NaturalAxisData.L h p.2`. -/
noncomputable def ns (h : ℝ) (p : Point) : ℝ :=
  P.axialLag h p / NaturalAxisData.L h p.2

/-- P2, given by `p.1 * ns P h p / P.E p`. -/
noncomputable def p2 (h : ℝ) (p : Point) : ℝ := p.1 * ns P h p / P.E p

/-- Cone size, given by `p1 P h p + p2 P h p ^ 2 / p1 P h p`. -/
noncomputable def coneSize (h : ℝ) (p : Point) : ℝ :=
  p1 P h p + p2 P h p ^ 2 / p1 P h p

theorem H_radialPartial {p : Point} (hp : p ∈ D.carrier) :
    radialPartial P.H p = 2 * P.f p + 2 * p.1 * radialPartial P.f p := by
  have h := ((hasDerivAt_id p.1).const_mul 2).mul
    (radialPartial_hasDerivAt D P.f_smooth hp)
  have he := (radialPartial_hasDerivAt D P.H_smooth hp).unique h
  simpa only [one_mul, mul_one, id_eq, Prod.eta] using he

theorem angularSource_eq {p : Point} (hp : p ∈ D.carrier) (hf : P.f p ≠ 0) (h : ℝ) :
    P.angularSource h p = P.H p * sourceQ P h p := by
  rw [Profiles.angularSource, H_radialPartial P hp, P.parameterPartial_H hp]
  unfold StressAlgebra.angularSource sourceQ logSlope Profiles.H
  field_simp

theorem p1_primitive {p : Point} (hX : p.1 ≠ 0) (h : ℝ) :
    p1 P h p = primitive (P.angularSource h) p /
      (NaturalAxisData.L h p.2 * P.H p) := by
  unfold p1 Profiles.angularLag
  calc
    _ = ((p.1 * primitive (P.angularSource h) p) / (p.1 * P.H p)) /
        NaturalAxisData.L h p.2 := by ring
    _ = (primitive (P.angularSource h) p / P.H p) / NaturalAxisData.L h p.2 := by
      rw [mul_div_mul_left _ _ hX]
    _ = _ := by ring

theorem ns_primitive (p : Point) (h : ℝ) :
    ns P h p = primitive (P.axialSource h) p /
      (NaturalAxisData.L h p.2 * p.1) := by
  unfold ns Profiles.axialLag
  ring

theorem parameterPartial_square {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial (fun q => P.f q ^ 2) p = 2 * P.f p * parameterPartial P.f p := by
  exact (parameterPartial_hasDerivAt D (P.f_smooth.pow 2) hp).unique
    (by simpa only [Nat.cast_ofNat, pow_one, Nat.reduceSub, Prod.eta] using
      (parameterPartial_hasDerivAt D P.f_smooth hp).fun_pow 2)

theorem pressure_parameter_increment {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial P.pressure p - deriv P.pressure0 p.2 =
      ∫ s in (0 : ℝ)..p.1, 2 * P.f (s, p.2) * parameterPartial P.f (s, p.2) := by
  rw [P.parameterPartial_pressure hp, add_sub_cancel_left,
    parameterPartial_primitive D (P.f_smooth.pow 2) hp]
  unfold primitive
  apply intervalIntegral.integral_congr
  intro s hs
  exact parameterPartial_square P (D.segment_mem hp hs)

theorem pressure_increment_bound {p : Point} (_ : p ∈ D.carrier) (hX : 0 ≤ p.1)
    {K C : ℝ} (_ : 0 ≤ K) (_ : 0 < C)
    (hf : ∀ s ∈ Icc (0 : ℝ) p.1, |P.f (s, p.2)| ≤ K / C) :
    |P.pressure p - P.pressure0 p.2| ≤ p.1 * K ^ 2 / C ^ 2 := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := p.1) (C := (K / C) ^ 2)
    (f := fun s => P.f (s, p.2) ^ 2) ?_
  · simp only [Profiles.pressure, add_sub_cancel_left, primitive]
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hX] at hbound
    convert! hbound using 1; ring
  · intro s hs
    have hsi : s ∈ Icc (0 : ℝ) p.1 :=
      ⟨(uIoc_of_le hX ▸ hs).1.le, (uIoc_of_le hX ▸ hs).2⟩
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hf s hsi) 2

theorem pressure_parameter_increment_bound {p : Point} (hp : p ∈ D.carrier) (hX : 0 ≤ p.1)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hf : ∀ s ∈ Icc (0 : ℝ) p.1, |P.f (s, p.2)| ≤ K / C)
    (hfη : ∀ s ∈ Icc (0 : ℝ) p.1, |parameterPartial P.f (s, p.2)| ≤ K / C) :
    |parameterPartial P.pressure p - deriv P.pressure0 p.2| ≤ 2 * p.1 * K ^ 2 / C ^ 2 := by
  rw [pressure_parameter_increment P hp]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := p.1) (C := 2 * (K / C) ^ 2)
    (f := fun s => 2 * P.f (s, p.2) * parameterPartial P.f (s, p.2)) ?_
  · rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hX] at hbound
    convert! hbound using 1; ring
  · intro s hs
    have hsi : s ∈ Icc (0 : ℝ) p.1 :=
      ⟨(uIoc_of_le hX ▸ hs).1.le, (uIoc_of_le hX ▸ hs).2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ (2 * (K / C)) * (K / C) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hf s hsi) (by norm_num))
          (hfη s hsi) (abs_nonneg _) (mul_nonneg (by norm_num) (div_nonneg hK hC.le))
      _ = _ := by ring

theorem pressure_dot_bound {p : Point} (hp : p ∈ D.carrier) (hX : 0 ≤ p.1)
    {K C : ℝ} (hf : |P.f p| ≤ K / C) :
    |p.1 * radialPartial P.pressure p| ≤ p.1 * K ^ 2 / C ^ 2 := by
  rw [P.radialPartial_pressure hp, abs_mul, abs_of_nonneg hX, abs_pow]
  have h := pow_le_pow_left₀ (abs_nonneg _) hf 2
  have hm := mul_le_mul_of_nonneg_left h hX
  convert! hm using 1; ring

theorem p1_lower_from_source {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1)
    (h : ℝ) (hL : 0 < NaturalAxisData.L h p.2) {q : ℝ} (hq : 0 ≤ q)
    (hf : ∀ s ∈ Icc (0 : ℝ) p.1, 0 < P.f (s, p.2))
    (hmono : AntitoneOn (fun s => P.f (s, p.2)) (Icc (0 : ℝ) p.1))
    (hsource : ∀ s ∈ Icc (0 : ℝ) p.1, q ≤ sourceQ P h (s, p.2)) :
    q * p.1 / (2 * NaturalAxisData.L h p.2) ≤ p1 P h p := by
  have hfX := hf p.1 ⟨hX.le, le_rfl⟩
  have hHp : 0 < P.H p := by change 0 < 2 * p.1 * P.f p; positivity
  rw [p1_primitive P hX.ne' h]
  apply (le_div_iff₀ (mul_pos hL hHp)).mpr
  have hsourceInt : (∫ s in (0 : ℝ)..p.1, 2 * P.f p * q * s) ≤
      primitive (P.angularSource h) p := by
    apply intervalIntegral.integral_mono_on (μ := volume) hX.le
      ((continuous_const.fun_mul continuous_id).intervalIntegrable 0 p.1)
      (radial_slice_intervalIntegrable D (P.angularSource_smooth h) hp)
    intro s hs
    have hsD : (s, p.2) ∈ D.carrier := D.segment_mem hp (uIcc_of_le hX.le ▸ hs)
    rw [angularSource_eq P hsD (hf s hs).ne']
    have hm := hmono hs ⟨hX.le, le_rfl⟩ hs.2
    have hHs : 0 ≤ P.H (s, p.2) := by
      change 0 ≤ 2 * s * P.f (s, p.2)
      exact mul_nonneg (mul_nonneg (by norm_num) hs.1) (hf s hs).le
    calc
      _ = (2 * s * P.f p) * q := by (try simp only [id_eq]); ring
      _ ≤ P.H (s, p.2) * q := by
        apply mul_le_mul_of_nonneg_right _ hq
        exact mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) hs.1)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsource s hs) hHs
  rw [intervalIntegral.integral_const_mul, integral_id] at hsourceInt
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] at hsourceInt
  have heq : (q * p.1 / (2 * NaturalAxisData.L h p.2)) *
      (NaturalAxisData.L h p.2 * P.H p) = (2 * P.f p * q) * (p.1 ^ 2 / 2) := by
    unfold Profiles.H
    field_simp
  rwa [heq]

theorem ns_deviation_bound {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1)
    (h : ℝ) (hL : 0 < NaturalAxisData.L h p.2) {Z ε : ℝ}
    (hsource : ∀ s ∈ Icc (0 : ℝ) p.1, |P.axialSource h (s, p.2) - Z| ≤ ε) :
    |ns P h p - Z / NaturalAxisData.L h p.2| ≤ ε / NaturalAxisData.L h p.2 := by
  have heq : ns P h p - Z / NaturalAxisData.L h p.2 =
      (∫ s in (0 : ℝ)..p.1, P.axialSource h (s, p.2) - Z) /
        (NaturalAxisData.L h p.2 * p.1) := by
    rw [intervalIntegral.integral_sub (radial_slice_intervalIntegrable D (P.axialSource_smooth h)
        hp)
      intervalIntegrable_const, intervalIntegral.integral_const]
    rw [ns_primitive]
    unfold primitive
    simp only [sub_zero, smul_eq_mul]
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hL hX)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := p.1) (C := ε) (f := fun s => P.axialSource h (s, p.2) - Z)
    (fun s hs => by
      rw [Real.norm_eq_abs]
      exact hsource s ⟨(uIoc_of_le hX.le ▸ hs).1.le, (uIoc_of_le hX.le ▸ hs).2⟩)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hX] at hb
  apply (div_le_iff₀ (mul_pos hL hX)).mpr
  have he : ε / NaturalAxisData.L h p.2 * (NaturalAxisData.L h p.2 * p.1) = ε * p.1 := by
    field_simp
  rwa [he]

theorem p1_lower_from_initial {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1)
    (h : ℝ) (hL : 0 < NaturalAxisData.L h p.2) {a b q : ℝ}
    (ha : 0 < a) (haX : a ≤ p.1) (hb : 0 ≤ b) (hq : 0 ≤ q)
    (hf : ∀ s ∈ Icc (0 : ℝ) p.1, 0 < P.f (s, p.2))
    (hmono : AntitoneOn (fun s => P.f (s, p.2)) (Icc (0 : ℝ) p.1))
    (hsource : ∀ s ∈ Icc a p.1, q ≤ sourceQ P h (s, p.2))
    (hinit : b ≤ p1 P h (a, p.2)) :
    b * a / p.1 + q / (2 * NaturalAxisData.L h p.2) * (p.1 - a ^ 2 / p.1) ≤ p1 P h p := by
  have hfX := hf p.1 ⟨hX.le, le_rfl⟩
  have hfa := hf a ⟨ha.le, haX⟩
  have hHa : 0 < P.H (a, p.2) := by change 0 < 2 * a * P.f (a, p.2); positivity
  have hHX : 0 < P.H p := by change 0 < 2 * p.1 * P.f p; positivity
  have hfun : ContinuousOn (fun s => P.angularSource h (s, p.2)) (Icc 0 p.1) :=
    (radial_slice_continuous D (P.angularSource_smooth h) p.2).mono
      (fun s hs => D.segment_mem hp (uIcc_of_le hX.le ▸ hs))
  have h0a : IntervalIntegrable (fun s => P.angularSource h (s, p.2)) volume 0 a :=
    ContinuousOn.intervalIntegrable_of_Icc ha.le
      (hfun.mono (fun s hs => ⟨hs.1, hs.2.trans haX⟩))
  have haXint : IntervalIntegrable (fun s => P.angularSource h (s, p.2)) volume a p.1 :=
    ContinuousOn.intervalIntegrable_of_Icc haX
      (hfun.mono (fun s hs => ⟨ha.le.trans hs.1, hs.2⟩))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h0a haXint
  have hlow : (2 * P.f p * q) * ((p.1 ^ 2 - a ^ 2) / 2) ≤
      ∫ s in a..p.1, P.angularSource h (s, p.2) := by
    have hcmp := intervalIntegral.integral_mono_on (μ := volume) haX
      ((continuous_const.fun_mul continuous_id).intervalIntegrable a p.1) haXint
      (f := fun s => (2 * P.f p * q) * s) (g := fun s => P.angularSource h (s, p.2)) ?_
    · rw [intervalIntegral.integral_const_mul, integral_id]
        at hcmp
      exact hcmp
    · intro s hs
      have hs0 : s ∈ Icc (0 : ℝ) p.1 := ⟨ha.le.trans hs.1, hs.2⟩
      have hsD := D.segment_mem hp (uIcc_of_le hX.le ▸ hs0)
      rw [angularSource_eq P hsD (hf s hs0).ne']
      have hm := hmono hs0 ⟨hX.le, le_rfl⟩ hs.2
      have hHs : 0 ≤ P.H (s, p.2) := by
        change 0 ≤ 2 * s * P.f (s, p.2)
        exact mul_nonneg (mul_nonneg (by norm_num) hs0.1) (hf s hs0).le
      calc
        _ = (2 * s * P.f p) * q := by ring
        _ ≤ P.H (s, p.2) * q := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) hs0.1)) hq
        _ ≤ _ := mul_le_mul_of_nonneg_left (hsource s hs) hHs
  rw [p1_primitive P ha.ne' h] at hinit
  have hinit' := (le_div_iff₀ (mul_pos hL hHa)).mp hinit
  have hmonoA := hmono ⟨ha.le, haX⟩ ⟨hX.le, le_rfl⟩ haX
  have hinit0 : b * (NaturalAxisData.L h p.2 * (2 * a * P.f p)) ≤
      primitive (P.angularSource h) (a, p.2) := by
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hmonoA (by positivity : 0 ≤ 2 * a)) hL.le) hb).trans hinit'
  rw [p1_primitive P hX.ne' h]
  apply (le_div_iff₀ (mul_pos hL hHX)).mpr
  have htotal := add_le_add hinit0 hlow
  change _ ≤ primitive (P.angularSource h) (a, p.2) + _ at htotal
  unfold primitive at htotal ⊢
  rw [hsplit] at htotal
  convert! htotal using 1
  unfold Profiles.H
  field_simp [hL.ne', hX.ne']

theorem p1_equation {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1)
    (hf : P.f p ≠ 0) (h : ℝ) :
    p.1 * deriv (fun x => p1 P h (x, p.2)) p.1 + logSlope P p * p1 P h p =
      p.1 * sourceQ P h p / NaturalAxisData.L h p.2 := by
  have hH := P.H_ne_zero hX.ne' hf
  have hQ := P.angularLag_equation h hp hX.ne' hH
  have hQd := P.angularLag_hasDerivAt h hp hX.ne' hH
  have hd := ((hasDerivAt_id p.1).fun_mul hQd).div_const (NaturalAxisData.L h p.2)
  rw [show deriv (fun x => p1 P h (x, p.2)) p.1 =
    (P.angularLag h p + p.1 * deriv (fun x => P.angularLag h (x, p.2)) p.1) /
      NaturalAxisData.L h p.2 by
        simpa only [p1, one_mul, Prod.eta, id_eq, ← hQd.deriv] using hd.deriv]
  rw [angularSource_eq P hp hf, mul_div_cancel_left₀ _ hH] at hQ
  have hs : p.1 * radialPartial P.H p / P.H p = logSlope P p := by
    rw [H_radialPartial P hp]
    unfold Profiles.H logSlope
    field_simp
  rw [hs] at hQ
  unfold p1
  calc
    _ = p.1 * (p.1 * deriv (fun x => P.angularLag h (x, p.2)) p.1 +
        (1 + logSlope P p) * P.angularLag h p) / NaturalAxisData.L h p.2 := by ring
    _ = _ := by rw [hQ]

theorem ns_equation {p : Point} (hp : p ∈ D.carrier) (hX : p.1 ≠ 0) (h : ℝ) :
    p.1 * deriv (fun x => ns P h (x, p.2)) p.1 + ns P h p =
      P.axialSource h p / NaturalAxisData.L h p.2 := by
  have hN := P.axialLag_equation h hp hX
  have hNd := P.axialLag_hasDerivAt h hp hX
  have hd := hNd.div_const (NaturalAxisData.L h p.2)
  rw [show deriv (fun x => ns P h (x, p.2)) p.1 =
    deriv (fun x => P.axialLag h (x, p.2)) p.1 / NaturalAxisData.L h p.2 by
      simpa only [ns, ← hNd.deriv] using hd.deriv]
  unfold ns
  calc
    _ = (p.1 * deriv (fun x => P.axialLag h (x, p.2)) p.1 + P.axialLag h p) /
        NaturalAxisData.L h p.2 := by ring
    _ = _ := by rw [hN]

theorem lower_comparison_preserves {X a L b q : ℝ}
    (ha : 0 < a) (haX : a ≤ X) (hL : 0 < L) (hq : 0 ≤ q) (hqa : b * L ≤ q * a) :
    b ≤ b * a / X + q / (2 * L) * (X - a ^ 2 / X) := by
  have hX : 0 < X := ha.trans_le haX
  have hfac : 0 ≤ q * (X + a) - 2 * b * L := by
    have hm := mul_le_mul_of_nonneg_left haX hq
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr haX) hfac
  have heq : b * a / X + q / (2 * L) * (X - a ^ 2 / X) =
      (2 * L * b * a + q * (X ^ 2 - a ^ 2)) / (2 * L * X) := by
    field_simp
  rw [heq]
  apply (le_div_iff₀ (by positivity : 0 < 2 * L * X)).mpr
  nlinarith

theorem p1_preserves_lower {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1)
    (h : ℝ) (hL : 0 < NaturalAxisData.L h p.2) {a b q : ℝ}
    (ha : 0 < a) (haX : a ≤ p.1) (hb : 0 ≤ b) (hq : 0 ≤ q)
    (hqa : b * NaturalAxisData.L h p.2 ≤ q * a)
    (hf : ∀ s ∈ Icc (0 : ℝ) p.1, 0 < P.f (s, p.2))
    (hmono : AntitoneOn (fun s => P.f (s, p.2)) (Icc (0 : ℝ) p.1))
    (hsource : ∀ s ∈ Icc a p.1, q ≤ sourceQ P h (s, p.2))
    (hinit : b ≤ p1 P h (a, p.2)) : b ≤ p1 P h p :=
  (lower_comparison_preserves ha haX hL hq hqa).trans
    (p1_lower_from_initial P hp hX h hL ha haX hb hq hf hmono hsource hinit)

theorem p1_at_hundred_gt_three {η h : ℝ} (hp : (100, η) ∈ D.carrier)
    (hL : 0 < NaturalAxisData.L h η) (hL1 : NaturalAxisData.L h η ≤ 1)
    (hf : ∀ s ∈ Icc (0 : ℝ) 100, 0 < P.f (s, η))
    (hmono : AntitoneOn (fun s => P.f (s, η)) (Icc (0 : ℝ) 100))
    (hsource : ∀ s ∈ Icc (0 : ℝ) 100, (12 / 5 : ℝ) ≤ sourceQ P h (s, η)) :
    3 < p1 P h (100, η) := by
  have hb := p1_lower_from_source P hp (by norm_num : (0 : ℝ) < 100) h hL
    (by norm_num : (0 : ℝ) ≤ 12 / 5) hf hmono hsource
  have hn : (3 : ℝ) < (12 / 5) * 100 / (2 * NaturalAxisData.L h η) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hL)).mpr
    nlinarith
  exact hn.trans_le hb

theorem p2_large_of_small_f {p : Point} (hX : 0 < p.1) (hX110 : p.1 ≤ 110)
    (h : ℝ) {a K C ν : ℝ} (ha : 0 < a) (haX : a ≤ p.1)
    (_ : 0 < K) (hC : 0 < C) (hν : 0 < ν)
    (hf : 0 < P.f p) (hfbound : P.f p ≤ K / C)
    (hn : ν ≤ |ns P h p|) (hlarge : 18 * K / (a * ν) < C) :
    (6 / 5 : ℝ) < |p2 P h p| := by
  have hs : Real.sqrt (2 * p.1) ≤ 15 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by nlinarith⟩
  have hE : 0 < P.E p := mul_pos (Real.sqrt_pos.mpr (by positivity)) hf
  have hEb : P.E p ≤ 15 * K / C := by
    change Real.sqrt (2 * p.1) * P.f p ≤ _
    calc
      _ ≤ 15 * (K / C) := mul_le_mul hs hfbound hf.le (by norm_num)
      _ = _ := by ring
  have hc : 18 * K / C < a * ν := by
    apply (div_lt_iff₀ hC).mpr
    have hh := (div_lt_iff₀ (mul_pos ha hν)).mp hlarge
    nlinarith
  have hnprod : a * ν ≤ p.1 * |ns P h p| :=
    mul_le_mul haX hn hν.le hX.le
  rw [p2, abs_div, abs_mul, abs_of_pos hX, abs_of_pos hE]
  apply (lt_div_iff₀ hE).mpr
  have hmult := mul_le_mul_of_nonneg_left hEb (by norm_num : (0 : ℝ) ≤ 6 / 5)
  have hid : (6 / 5 : ℝ) * (15 * K / C) = 18 * K / C := by ring
  rw [hid] at hmult
  linarith

theorem cone_margin_of_dichotomy {a b : ℝ} (ha : 0 < a)
    (hlarge : (23 / 10 : ℝ) ≤ a ∨ (6 / 5 : ℝ) < |b|) :
    (9 / 4 : ℝ) < a + b ^ 2 / a := by
  rcases hlarge with hfirst | hsecond
  · have hpos : 0 ≤ b ^ 2 / a := div_nonneg (sq_nonneg _) ha.le
    linarith
  · have hs : (6 / 5 : ℝ) ^ 2 < b ^ 2 := by
      have habs := sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 6 / 5) (abs_nonneg b) |>.mpr hsecond
      simpa only [sq_abs] using habs
    have hm : (12 / 5 : ℝ) * a < a ^ 2 + b ^ 2 := by
      nlinarith [sq_nonneg (a - 6 / 5)]
    have hd : (12 / 5 : ℝ) < a + b ^ 2 / a := by
      calc
        (12 / 5 : ℝ) < (a ^ 2 + b ^ 2) / a := (lt_div_iff₀ ha).mpr hm
        _ = _ := by field_simp
    linarith

end Histories

/-! ## Uniform source estimates from bounded low-level jets

The compact variables below are the normalized axial value and average jets,
the positive natural angular value, and the bounded remainder of its parameter
logarithmic derivative. They are not source or cone assumptions.
-/

open NaturalAxisCoefficients

/-- Bounded jets: an abbreviation for `Metric.closedBall (0 : Fin 5 → ℝ) B instance (B : ℝ) :
CompactSpace (BoundedJets B) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)`. -/
abbrev BoundedJets (B : ℝ) := Metric.closedBall (0 : Fin 5 → ℝ) B

instance (B : ℝ) : CompactSpace (BoundedJets B) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

/-- Source parameter: an abbreviation for `NaturalEntrance.entranceSet × (Icc (0 : ℝ) 1 ×
BoundedJets B)`. -/
abbrev SourceParameter (B : ℝ) :=
  NaturalEntrance.entranceSet × (Icc (0 : ℝ) 1 × BoundedJets B)

/-- `v 0` is the natural positive angular factor, `v 1` the normalized
axial value, `v 2, v 3` the normalized radial-average jets, and `v 4` the
bounded parameter-log-gradient remainder. -/
noncomputable def qRemainder (h j σ : ℝ) (p : Point) (θ : ℝ)
    (v : Fin 5 → ℝ) (t r : ℝ) : ℝ :=
  let W := NaturalAxisData.W h j p.2 -
    t * (2 * NaturalAxisData.D h * p.2 * v 2 + NaturalAxisData.d p.2 * v 3)
  let U := NaturalAxisData.U j p.2 + t * v 1
  let H := NaturalAxisData.H h j p.2 + t * NaturalAxisData.d p.2 * v 1
  show ℝ from -W * (1 + θ * p.1 * r / max (1 / 8 : ℝ) (v 0)) - h * (1 - 2 * p.2 * U) -
    H * v 4 - NaturalAxisData.d p.2 * v 1 * realGradient h j σ p.2

theorem qRemainder_continuous (h j : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun z : ((Point × ℝ) × (Fin 5 → ℝ)) × (ℝ × ℝ) =>
      qRemainder h j σ z.1.1.1 z.1.1.2 z.1.2 z.2.1 z.2.2) := by
  have hc := NaturalEntrance.realGradient_continuous h j hσ
  have hn : ∀ v : Fin 5 → ℝ, max (1 / 8 : ℝ) (v 0) ≠ 0 := by
    intro v
    have hb := le_max_left (1 / 8 : ℝ) (v 0)
    linarith
  dsimp only [qRemainder, NaturalAxisData.W, NaturalAxisData.H,
    NaturalAxisData.U, NaturalAxisData.d, NaturalAxisData.D]
  fun_prop (disch := first | exact fun x => hn x.1.2 | exact hn _)

/-- Q model, constructed using `qRemainder`. -/
noncomputable def qModel {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (B : ℝ) (p : SourceParameter B) (z : ℝ × ℝ) : ℝ :=
  qRemainder h j σ p.1.val p.2.1.val p.2.2.val z.1
    (NaturalEntrance.sourceJets v.epsilon_pos (NaturalEntrance.referencePair v) p.1 1 + z.2)

theorem qModel_continuous {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (B : ℝ) (hσ : 0 < σ) :
    Continuous (fun p : SourceParameter B × (ℝ × ℝ) => qModel v B p.1 p.2) := by
  have hr : Continuous (fun p : SourceParameter B × (ℝ × ℝ) =>
      NaturalEntrance.sourceJets v.epsilon_pos (NaturalEntrance.referencePair v) p.1.1 1) :=
    (continuous_apply 1).comp
      ((NaturalEntrance.sourceJets_continuous v.epsilon_pos (NaturalEntrance.referencePair v)).comp
        (continuous_fst.comp continuous_fst))
  let m : SourceParameter B × (ℝ × ℝ) → ((Point × ℝ) × (Fin 5 → ℝ)) × (ℝ × ℝ) :=
    fun p => (((p.1.1.val, p.1.2.1.val), p.1.2.2.val),
      (p.2.1, NaturalEntrance.sourceJets v.epsilon_pos (NaturalEntrance.referencePair v) p.1.1 1 +
          p.2.2))
  have hm : Continuous m := by
    dsimp [m]
    fun_prop
  simpa only [qModel, m, Function.comp_def] using (qRemainder_continuous h j hσ).comp hm

theorem qModel_at_chi_zero {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (B : ℝ) (hσ : 0 < σ) (p : SourceParameter B)
    (hchi : NaturalAxisData.chi h j σ p.1.val.2 = 0) :
    qModel v B p 0 = -NaturalAxisData.W h j p.1.val.2 -
      h * (1 - 2 * p.1.val.2 * NaturalAxisData.U j p.1.val.2) := by
  have hH := NaturalEntrance.chi_zero_imp_H_zero h j hσ hchi
  have hk := NaturalEntrance.gradient_zero_of_chi_zero h j hσ hchi
  have hr := NaturalEntrance.reference_phiY_zero v p.1 hchi
  simp only [qModel, qRemainder, Prod.fst_zero, Prod.snd_zero, hr, hH, hk, add_zero, zero_mul,
      mul_zero, zero_div, sub_zero, mul_one]

/-- Uniformity in all bounded reference jets is proved before the scale
and normalization are chosen. The growing term supplies no help at `χ=0`;
there the concrete axis source supplies the positive margin. -/
theorem qModel_uniform_lower {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (B : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ M : ℝ, 0 < M ∧ ∀ Λ : ℝ, M ≤ Λ → ∀ p : SourceParameter B,
      ∀ e : ℝ, |e| ≤ K / Λ →
        (47 / 50 : ℝ) * NaturalAxisData.L h p.1.val.2 * Λ *
            NaturalAxisData.chi h j σ p.1.val.2 + 12 / 5 <
          NaturalAxisData.L h p.1.val.2 * Λ * NaturalAxisData.chi h j σ p.1.val.2 +
            qModel v B p (1 / Λ, e) := by
  have hL : Continuous (NaturalAxisData.L h) := by unfold NaturalAxisData.L; fun_prop
  have hp : Continuous (fun p : SourceParameter B => p.1.val.2) := by fun_prop
  have hcoef : Continuous (fun p : SourceParameter B =>
      (3 / 50 : ℝ) * NaturalAxisData.L h p.1.val.2 * NaturalAxisData.chi h j σ p.1.val.2) :=
    ((continuous_const.mul (hL.comp hp)).mul
      ((NaturalEntrance.chi_continuous h j hσ).comp hp))
  have hbase : Continuous (fun p : SourceParameter B => qModel v B p 0) := by
    have hc := (qModel_continuous v B hσ).comp
      (continuous_id.prodMk (continuous_const (y := (0 : ℝ × ℝ))))
    simpa only [Function.comp_def, id_eq] using hc
  obtain ⟨M₀, hM₀, hmain⟩ := NaturalEntrance.compact_absorption _ _ hcoef hbase
    (fun p => mul_nonneg (mul_nonneg (by norm_num)
      (NaturalAxisData.L_pos hsmall p.1.property.2).le)
      (NaturalAxisData.chi_bounds h j hσ p.1.val.2).1) (5 / 2 : ℝ) (by
        intro p hz
        have hf : (3 / 50 : ℝ) * NaturalAxisData.L h p.1.val.2 ≠ 0 :=
          mul_ne_zero (by norm_num) (NaturalAxisData.L_pos hsmall p.1.property.2).ne'
        have hchi := (mul_eq_zero.mp hz).resolve_left hf
        rw [qModel_at_chi_zero v B hσ p hchi]
        linarith [NaturalEntrance.base_source_lower hsmall p.1.property.2])
  obtain ⟨δ, hδ, hpert⟩ := NaturalEntrance.compact_small_perturbation _
    (qModel_continuous v B hσ) (by norm_num : (0 : ℝ) < 1 / 10)
  let M := max M₀ (1 + (1 + K) / δ)
  refine ⟨M, hM₀.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ p e he
  have hΛ0 : 0 < Λ := hM₀.trans_le ((le_max_left _ _).trans hΛ)
  have hΛ' : (1 + K) / δ < Λ := by
    have hm := (le_max_right M₀ (1 + (1 + K) / δ)).trans hΛ
    linarith
  have hmul := (div_lt_iff₀ hδ).mp hΛ'
  have ht : |1 / Λ| < δ := by
    rw [abs_of_pos (one_div_pos.mpr hΛ0), div_lt_iff₀ hΛ0]
    nlinarith
  have he' : |e| < δ := he.trans_lt (by
    apply (div_lt_iff₀ hΛ0).mpr
    nlinarith)
  have hnorm : ‖((1 / Λ), e)‖ < δ := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, max_lt_iff] using And.intro ht he'
  have herror := (abs_lt.mp (hpert p ((1 / Λ), e) hnorm)).1
  have hb := hmain Λ ((le_max_left _ _).trans hΛ) p
  nlinarith

/-- Axial source parameter: an abbreviation for `Icc (-1 : ℝ) 1 × BoundedJets B`. -/
abbrev AxialSourceParameter (B : ℝ) := Icc (-1 : ℝ) 1 × BoundedJets B

/-- The axial source written in normalized axial jets and the actual three
pressure increments. Its zero-perturbation value is exactly `Z*`. -/
noncomputable def nModel (h j : ℝ) (P0 : ℝ → ℝ) (B : ℝ)
    (p : AxialSourceParameter B) (z : Fin 4 → ℝ) : ℝ :=
  let η := p.1.val
  let v := p.2.val
  let t := z 0
  let U := NaturalAxisData.U j η + t * v 0
  let W := NaturalAxisData.W h j η -
    t * (2 * NaturalAxisData.D h * η * v 2 + NaturalAxisData.d η * v 3)
  show ℝ from -W * (t * v 4) - NaturalAxisData.A h * (1 - 2 * η * U) * U -
    (NaturalAxisData.D h * η + NaturalAxisData.d η * U) * (4 + t * v 1) -
    NaturalAxisData.d η * (deriv P0 η + z 2) +
    4 * NaturalAxisData.A h * η * (P0 η + z 1) + 2 * η * z 3

theorem nModel_continuous (h j : ℝ) {P0 : ℝ → ℝ} (hP0 : ContDiff ℝ ∞ P0) (B : ℝ) :
    Continuous (fun p : AxialSourceParameter B × (Fin 4 → ℝ) => nModel h j P0 B p.1 p.2) := by
  have hp := hP0.continuous
  have hd : Continuous (deriv P0) := hP0.continuous_deriv (by simp)
  have he : Continuous (fun p : AxialSourceParameter B × (Fin 4 → ℝ) => p.1.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hv : ∀ i : Fin 5, Continuous (fun p : AxialSourceParameter B × (Fin 4 → ℝ) => p.1.2.val i) :=
    fun i => (continuous_apply i).comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
  have hz : ∀ i : Fin 4, Continuous (fun p : AxialSourceParameter B × (Fin 4 → ℝ) => p.2 i) :=
    fun i => (continuous_apply i).comp continuous_snd
  have hp' := hp.comp he
  have hd' := hd.comp he
  dsimp only [nModel, NaturalAxisData.U, NaturalAxisData.W, NaturalAxisData.D,
    NaturalAxisData.A, NaturalAxisData.d]
  fun_prop

theorem nModel_zero (h j : ℝ) (P0 : ℝ → ℝ) (B : ℝ) (p : AxialSourceParameter B) :
    nModel h j P0 B p 0 = NaturalAxisData.Z h j P0 p.1 := by
  simp only [nModel, Pi.zero_apply, zero_mul, mul_zero, add_zero,
    NaturalAxisData.Z, NaturalAxisData.H, zero_sub]
  ring

theorem nModel_uniform_error (h j : ℝ) {P0 : ℝ → ℝ} (hP0 : ContDiff ℝ ∞ P0)
    (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : AxialSourceParameter B, ∀ z : Fin 4 → ℝ,
      ‖z‖ < δ → |nModel h j P0 B p z - NaturalAxisData.Z h j P0 p.1| < ε := by
  obtain ⟨δ, hδ, he⟩ := NaturalEntrance.compact_small_perturbation _
    (nModel_continuous h j hP0 B) hε
  refine ⟨δ, hδ, fun p z hz => ?_⟩
  simpa only [nModel_zero] using he p z hz

/-! ## The compact models are the actual profile sources -/

section ActualModels

variable {D : RadialDomain} (P : Profiles D)

theorem average_error_bound {F : ProfileHistories.Field} (hF : ContDiffOn ℝ ∞ F D.carrier)
    {p : Point} (hp : p ∈ D.carrier) {Λ b B : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |Λ * (F (t * p.1, p.2) - b)| ≤ B) :
    |Λ * (average F p - b)| ≤ B := by
  have hi : IntervalIntegrable (fun t : ℝ => F (t * p.1, p.2)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact hF.continuousOn.comp (by fun_prop) (fun t ht => D.scale_mem p hp t ht)
  have he : Λ * (average F p - b) =
      ∫ t in (0 : ℝ)..1, Λ * (F (t * p.1, p.2) - b) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi
      intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [sub_zero, one_smul, ProfileHistories.average]
  rw [he]
  have hbt : ∀ t ∈ uIoc (0 : ℝ) 1, ‖Λ * (F (t * p.1, p.2) - b)‖ ≤ B := by
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := (uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht)
    simpa only [Real.norm_eq_abs] using hbound t ⟨ht'.1.le, ht'.2⟩
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := B)
    (f := fun t => Λ * (F (t * p.1, p.2) - b)) hbt
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hb

/-- Q jets as an element of `Fin 5 → ℝ`. -/
noncomputable def qJets (j σ h Λ φ : ℝ) (p : Point) : Fin 5 → ℝ :=
  ![φ, Λ * (P.U p - NaturalAxisData.U j p.2),
    Λ * (P.Ubar p - NaturalAxisData.U j p.2),
    Λ * (average (parameterPartial P.U) p - 4),
    parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2]

/-- N jets as an element of `Fin 5 → ℝ`. -/
noncomputable def nJets (j Λ : ℝ) (p : Point) : Fin 5 → ℝ :=
  ![Λ * (P.U p - NaturalAxisData.U j p.2),
    Λ * (parameterPartial P.U p - 4),
    Λ * (P.Ubar p - NaturalAxisData.U j p.2),
    Λ * (average (parameterPartial P.U) p - 4),
    Λ * (p.1 * radialPartial P.U p)]

/-- Pressure jets, given by `![1 / Λ, P.pressure p - P.pressure0 p.2, parameterPartial
P.pressure p - deriv P.pressure0 p.2, p.1 * P.f p ^ 2]`. -/
noncomputable def pressureJets (Λ : ℝ) (p : Point) : Fin 4 → ℝ :=
  ![1 / Λ, P.pressure p - P.pressure0 p.2,
    parameterPartial P.pressure p - deriv P.pressure0 p.2,
    p.1 * P.f p ^ 2]

theorem sourceQ_model (h j σ : ℝ) {Λ φ Y θ r : ℝ} (hΛ : Λ ≠ 0)
    (hφ : (1 / 8 : ℝ) ≤ φ) (p : Point)
    (hrad : p.1 * radialPartial P.f p / P.f p = θ * Y * r / φ) :
    sourceQ P h p = NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 +
      qRemainder h j σ (Y, p.2) θ (qJets P j σ h Λ φ p) (1 / Λ) r := by
  have hg := NaturalProfile.gradient_identity h j σ p.2
  simp only [qRemainder, qJets, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue, max_eq_right hφ]
  rw [← hrad]
  unfold sourceQ logSlope Profiles.W
  unfold NaturalAxisData.W NaturalAxisData.H at hg ⊢
  change _ = _
  simp only [NaturalAxisData.D, NaturalAxisData.d, StressAlgebra.axialExponent,
    StressAlgebra.coordinateFactor] at hg ⊢
  field_simp [hΛ]
  linear_combination -(2 * Λ) * hg

theorem sourceN_model (h j : ℝ) {Λ B : ℝ} (hΛ : Λ ≠ 0)
    (p : Point) (hη : p.2 ∈ Icc (-1 : ℝ) 1)
    (hv : nJets P j Λ p ∈ Metric.closedBall (0 : Fin 5 → ℝ) B) :
    P.axialSource h p = nModel h j P.pressure0 B
      (⟨p.2, hη⟩, ⟨nJets P j Λ p, hv⟩) (pressureJets P Λ p) := by
  simp only [nModel, nJets, pressureJets, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue]
  unfold Profiles.axialSource StressAlgebra.axialSource Profiles.W
  unfold NaturalAxisData.W NaturalAxisData.d NaturalAxisData.D NaturalAxisData.A
  unfold StressAlgebra.axialExponent StressAlgebra.velocityExponent StressAlgebra.coordinateFactor
  field_simp [hΛ]; ring

theorem qJets_bound (h j σ : ℝ) {Λ B φ : ℝ} (hB : 0 ≤ B) {p : Point}
    (hφ : |φ| ≤ B)
    (hu : |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B)
    (hv : |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B)
    (hvη : |Λ * (average (parameterPartial P.U) p - 4)| ≤ B)
    (hfη : |parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2| ≤ B) :
    qJets P j σ h Λ φ p ∈ Metric.closedBall (0 : Fin 5 → ℝ) B := by
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hB]
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact hφ
  · exact hu
  · exact hv
  · exact hvη
  · exact hfη

theorem nJets_bound (j : ℝ) {Λ B : ℝ} (hB : 0 ≤ B) {p : Point}
    (hu : |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B)
    (huη : |Λ * (parameterPartial P.U p - 4)| ≤ B)
    (hv : |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B)
    (hvη : |Λ * (average (parameterPartial P.U) p - 4)| ≤ B)
    (huX : |Λ * (p.1 * radialPartial P.U p)| ≤ B) :
    nJets P j Λ p ∈ Metric.closedBall (0 : Fin 5 → ℝ) B := by
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hB]
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact hu
  · exact huη
  · exact hv
  · exact hvη
  · exact huX

end ActualModels

/-! ## Exact agreement with the natural entrance histories -/

section NaturalAgreement

open NaturalAxisBridge NaturalProfile ReferencePath

theorem radialPartial_natural {F : ProfileHistories.Field} {p : Point}
    (hF : ContDiffAt ℝ ∞ F p) : radialPartial F p = partialY F p := by
  have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.deriv.symm

theorem parameterPartial_natural {F : ProfileHistories.Field} {p : Point}
    (hF : ContDiffAt ℝ ∞ F p) : parameterPartial F p = partialEta F p := by
  have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact hd.deriv.symm

theorem natural_average_eq {h j Λ : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ProfileHistories.Field} (hs : IsNaturalSolution h j Λ P0 a f U V Pr)
    {p : Point} (hp : p ∈ domain Λ) : ProfileHistories.average U p = V p := by
  by_cases hx : p.1 = 0
  · have he : p = (0, p.2) := Prod.ext hx rfl
    rw [he, average_at_axis, hs.U_axis p.2 hp.2, hs.average_axis p.2 hp.2]
  · rw [average_eq_quotient U hx]
    change (∫ X in (0 : ℝ)..p.1, U (X, p.2)) / p.1 = V p
    rw [← hs.average_integral p hp, mul_div_cancel_left₀ _ hx]

theorem natural_average_eventuallyEq {h j Λ : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ProfileHistories.Field} (hs : IsNaturalSolution h j Λ P0 a f U V Pr)
    {p : Point} (hp : p ∈ domain Λ) : ProfileHistories.average U =ᶠ[𝓝 p] V := by
  filter_upwards [(domain_isOpen Λ).mem_nhds hp] with q hq
  exact natural_average_eq hs hq

variable (N : ReferencePath.Input)

theorem ref_natural_eventuallyEq {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval)
    (hX : p.1 < N.endpoint * Real.exp δ) :
    N.refF δ =ᶠ[𝓝 p] N.f ∧ N.refU δ =ᶠ[𝓝 p] N.U := by
  have he : {q : Point | q.1 < N.endpoint * Real.exp δ ∧ q.2 ∈ parameterInterval} ∈ 𝓝 p :=
    ((isOpen_lt continuous_fst continuous_const).inter
      (parameterInterval_open.preimage continuous_snd)).mem_nhds ⟨hX, hη⟩
  constructor
  · filter_upwards [he] with q hq
    exact N.refF_eq_natural hδ hδT hq.2 hq.1.le
  · filter_upwards [he] with q hq
    exact N.refU_eq_natural hδ hδT hq.2 hq.1.le

theorem average_refU_eq {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval)
    (hX : p.1 ≤ N.endpoint * Real.exp δ) :
    ProfileHistories.average (N.refU δ) p = ProfileHistories.average N.U p := by
  unfold ProfileHistories.average
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := (uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht)
  dsimp only
  apply N.refU_eq_natural hδ hδT (p := (t * p.1, p.2)) hη
  have hpos : 0 < N.endpoint * Real.exp δ := mul_pos N.endpoint_pos (Real.exp_pos _)
  calc
    t * p.1 ≤ t * (N.endpoint * Real.exp δ) := mul_le_mul_of_nonneg_left hX ht'.1
    _ ≤ N.endpoint * Real.exp δ := mul_le_of_le_one_left hpos.le ht'.2

theorem average_refU_eventuallyEq {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval)
    (hX : p.1 < N.endpoint * Real.exp δ) :
    ProfileHistories.average (N.refU δ) =ᶠ[𝓝 p] ProfileHistories.average N.U := by
  have he : {q : Point | q.1 < N.endpoint * Real.exp δ ∧ q.2 ∈ parameterInterval} ∈ 𝓝 p :=
    ((isOpen_lt continuous_fst continuous_const).inter
      (parameterInterval_open.preimage continuous_snd)).mem_nhds ⟨hX, hη⟩
  filter_upwards [he] with q hq
  exact average_refU_eq N hδ hδT hq.2 hq.1.le

end NaturalAgreement

section ReferenceHistories

open NaturalAxisBridge NaturalProfile ReferencePath

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
variable (F : NaturalEntrance.CoefficientProfile d Λ C) (hΛ : 0 < Λ)

/-- All pressure and stock fields of this profile are the literal histories
of the constructed reference continuation. -/
noncomputable def referenceProfiles {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) : Profiles (Input.ofNatural hΛ F.family).radialDomain :=
  (Input.ofNatural hΛ F.family).histories hδ hδT P0 hP0

theorem reference_mem {p : Point} (hX : 0 ≤ p.1) (hη : p.2 ∈ Icc (-1 : ℝ) 1) :
    p ∈ (Input.ofNatural hΛ F.family).radialDomain.carrier := by
  refine ⟨?_, NaturalAxisCoefficients.original_interval_interior hη⟩
  change -20 < Λ * p.1
  exact lt_of_lt_of_le (by norm_num) (mul_nonneg hΛ.le hX)

theorem endpoint_strict_collar {δ : ℝ} (hδ : 0 < δ) :
    (4 / Λ : ℝ) < (Input.ofNatural hΛ F.family).endpoint * Real.exp δ := by
  have he : 1 < Real.exp δ := Real.one_lt_exp_iff.mpr hδ
  change 4 / Λ < (4 / Λ) * Real.exp δ
  nlinarith [show (0 : ℝ) < 4 / Λ by positivity]

theorem reference_sourceQ_natural {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) {p : Point} (hp : p ∈ domain Λ) (hX : p.1 ≤ 4 / Λ) :
    sourceQ (referenceProfiles F hΛ hδ hδT hP0) h p =
      NaturalEntrance.Sq h F.family.f F.family.U F.family.Ubar p := by
  let N := Input.ofNatural hΛ F.family
  let P := referenceProfiles F hΛ hδ hδT hP0
  have hpN : p ∈ N.radialDomain.carrier := ⟨hp.1.1, hp.2⟩
  have hc : p.1 < N.endpoint * Real.exp δ := hX.trans_lt (endpoint_strict_collar F hΛ hδ)
  obtain ⟨hf, hu⟩ := ref_natural_eventuallyEq N hδ hδT (p := p) hp.2 hc
  have hav := (average_refU_eventuallyEq N hδ hδT (p := p) hp.2 hc).trans
    (natural_average_eventuallyEq F.family.natural (p := p) hp)
  have hfv : P.f p = F.family.f p := hf.eq_of_nhds
  have huv : P.U p = F.family.U p := hu.eq_of_nhds
  have hvv : P.Ubar p = F.family.Ubar p := hav.eq_of_nhds
  have hfD : fderiv ℝ P.f p = fderiv ℝ F.family.f p := hf.fderiv_eq
  have hvD : fderiv ℝ P.Ubar p = fderiv ℝ F.family.Ubar p := hav.fderiv_eq
  have hfx : radialPartial P.f p = partialY F.family.f p := by
    unfold radialPartial
    rw [hfD]
    exact radialPartial_natural (F.family.natural.f_smooth.contDiffAt ((domain_isOpen Λ).mem_nhds
        hp))
  have hfe : parameterPartial P.f p = partialEta F.family.f p := by
    unfold parameterPartial
    rw [hfD]
    exact parameterPartial_natural (F.family.natural.f_smooth.contDiffAt ((domain_isOpen
        Λ).mem_nhds hp))
  have hve : parameterPartial P.Ubar p = partialEta F.family.Ubar p := by
    unfold parameterPartial
    rw [hvD]
    exact parameterPartial_natural (F.family.natural.average_smooth.contDiffAt ((domain_isOpen
        Λ).mem_nhds hp))
  change sourceQ P h p = _
  rw [sourceQ, logSlope, P.W_formula h hpN, hfv, huv, hvv, hfx, hfe, hve]
  rfl

theorem reference_p1_natural {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    {p : Point} (hη : p.2 ∈ Icc (-1 : ℝ) 1) (hX : 0 < p.1) (ha : p.1 ≤ 4 / Λ) :
    p1 (referenceProfiles F hΛ hδ hδT hP0) h p = NaturalEntrance.p1 F.family.f p := by
  let N := Input.ofNatural hΛ F.family
  let P := referenceProfiles F hΛ hδ hδT hP0
  have hY : Λ * p.1 ≤ 4 := by nlinarith [(le_div_iff₀ hΛ).mp ha]
  have hpoint : rescalePoint Λ p ∈ NaturalEntrance.entranceSet :=
    ⟨⟨mul_nonneg hΛ.le hX.le, by change Λ * p.1 ≤ 41 / 10; linarith⟩, hη⟩
  have hp := NaturalEntrance.entrance_mem_strip hpoint
  have hpN := reference_mem F hΛ hX.le hη
  have hfp : P.f p = F.family.f p := N.refF_eq_natural_initial δ ha
  have hsegment (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) p.1) :
      (x, p.2) ∈ domain Λ ∧ x ≤ 4 / Λ ∧ 0 ≤ x := by
    have hx' : x ∈ Icc (0 : ℝ) p.1 := (uIcc_of_le hX.le ▸ hx)
    exact ⟨NaturalProfile.domain_segment hΛ hp hx, hx'.2.trans ha, hx'.1⟩
  have hfun : primitive (P.angularSource h) p =
      ∫ x in (0 : ℝ)..p.1, (2 * x * F.family.f (x, p.2)) *
        NaturalEntrance.Sq h F.family.f F.family.U F.family.Ubar (x, p.2) := by
    unfold primitive
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    obtain ⟨hxn, hxa, hx0⟩ := hsegment x hx
    have hxnN := reference_mem F hΛ (p := (x, p.2)) hx0 hη
    have hpos := N.refF_pos δ hxnN hx0
    rw [angularSource_eq P hxnN hpos.ne', reference_sourceQ_natural F hΛ hδ hδT hP0 hxn hxa]
    change (2 * x * N.refF δ (x, p.2)) * _ = _
    rw [N.refF_eq_natural_initial δ hxa]
    rfl
  have hfn : ∀ x ∈ uIcc (0 : ℝ) p.1, F.family.f (x, p.2) ≠ 0 := by
    intro x hx
    obtain ⟨hxn, hxa, hx0⟩ := hsegment x hx
    exact (F.family.positive (x, p.2) hxn (mul_nonneg hΛ.le hx0)
      (by have hh := (le_div_iff₀ hΛ).mp hxa; linarith)).ne'
  have hreg := NaturalEntrance.p1_eq_scaled_regularAngularLag F.family.natural hΛ hp
    hX.ne' (NaturalAxisData.L_pos hsmall hη).ne' hfn
  change NaturalEntrance.p1 F.family.f p = p.1 * NaturalEntrance.regularAngularLag h
    F.family.f F.family.U F.family.Ubar p / NaturalAxisData.L h p.2 at hreg
  rw [hreg]
  change p.1 * (primitive (P.angularSource h) p / (p.1 * (2 * p.1 * P.f p))) /
      NaturalAxisData.L h p.2 = _
  rw [hfun, hfp]
  rfl

end ReferenceHistories

section ReferenceMonotonicity

open NaturalAxisBridge NaturalProfile ReferencePath

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
variable (E : NaturalEntrance.EntranceProfile d Λ C) (hΛ : 0 < Λ)

theorem natural_entrance_of_logTime {p : Point} (hX : 0 < p.1)
    (hη : p.2 ∈ Icc (-1 : ℝ) 1)
    (ht : (Input.ofNatural hΛ E.profile.family).logTime p.1 < rampLimit) :
    rescalePoint Λ p ∈ NaturalEntrance.entranceSet := by
  let N := Input.ofNatural hΛ E.profile.family
  have he : Real.exp (N.logTime p.1) < 41 / 40 := by
    simpa only [rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)] using
      Real.exp_lt_exp.mpr ht
  have hr := N.fromLog_scaled (N.logTime p.1, p.2)
  rw [N.fromLog_logTime hX] at hr
  change Λ * p.1 = 4 * Real.exp (N.logTime p.1) at hr
  exact ⟨⟨mul_nonneg hΛ.le hX.le, by change Λ * p.1 ≤ 41 / 10; linarith⟩, hη⟩

theorem reference_radial_nonpos {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) {p : Point} (hX : 0 < p.1)
    (hη : p.2 ∈ Icc (-1 : ℝ) 1) :
    radialPartial (referenceProfiles E.profile hΛ hδ hδT hP0).f p ≤ 0 := by
  let N := Input.ofNatural hΛ E.profile.family
  let P := referenceProfiles E.profile hΛ hδ hδT hP0
  have hp := reference_mem E.profile hΛ hX.le hη
  have hf : 0 < P.f p := N.refF_pos δ hp hX.le
  have hd := (radialPartial_hasDerivAt N.radialDomain P.f_smooth hp).log hf.ne'
  have hderiv : deriv (fun X => Real.log (N.refF δ (X, p.2))) p.1 =
      radialPartial P.f p / P.f p := hd.deriv
  have hdot : p.1 * radialPartial P.f p / P.f p ≤ 0 := by
    by_cases ht : N.logTime p.1 < rampLimit
    · have hs := N.same_radius_log_slope hδ hδT (p := p)
        (original_interval_interior hη) hX ht
      rw [hderiv] at hs
      have hen := natural_entrance_of_logTime E hΛ hX hη ht
      have hn := E.slope_positive p hen hX
      have hnat := radialPartial_natural
        (E.profile.family.natural.f_smooth.contDiffAt
          ((domain_isOpen Λ).mem_nhds (NaturalEntrance.entrance_mem_strip hen)))
      change radialPartial E.profile.family.f p = partialY E.profile.family.f p at hnat
      have hnonpos : p.1 * radialPartial N.f p / N.f p ≤ 0 := by
        change p.1 * radialPartial E.profile.family.f p / E.profile.family.f p ≤ 0
        rw [hnat]
        change 0 < -2 * p.1 * partialY E.profile.family.f p / E.profile.family.f p at hn
        have he : -2 * p.1 * partialY E.profile.family.f p / E.profile.family.f p =
            -2 * (p.1 * partialY E.profile.family.f p / E.profile.family.f p) := by ring
        rw [he] at hn
        linarith
      have hh := mul_nonpos_of_nonneg_of_nonpos (slopeCutoff_mem δ (N.logTime p.1)).1 hnonpos
      calc
        _ = p.1 * (radialPartial P.f p / P.f p) := by ring
        _ = _ := hs
        _ ≤ 0 := hh
    · have hc := slopeCutoff_zero hδ (hδT.le.trans (le_of_not_gt ht))
      have hz := (N.log_refF_hasDerivAt hδ hδT (p := p) (original_interval_interior hη) hX).deriv
      rw [hc, zero_mul, zero_div, hderiv] at hz
      rw [mul_div_assoc, hz, mul_zero]
  have hm : p.1 * radialPartial P.f p ≤ p.1 * 0 := by
    simpa only [zero_mul, mul_zero] using (div_le_iff₀ hf).mp hdot
  exact (mul_le_mul_iff_right₀ hX).mp hm

theorem reference_logSlope_le_one {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) {p : Point} (hX : 0 ≤ p.1)
    (hη : p.2 ∈ Icc (-1 : ℝ) 1) :
    logSlope (referenceProfiles E.profile hΛ hδ hδT hP0) p ≤ 1 := by
  by_cases hz : p.1 = 0
  · simp only [logSlope, hz, zero_mul, zero_div, add_zero, le_rfl]
  · have hx : 0 < p.1 := lt_of_le_of_ne hX (Ne.symm hz)
    have hd := reference_radial_nonpos E hΛ hδ hδT hP0 hx hη
    have hp := reference_mem E.profile hΛ hX hη
    have hf := (Input.ofNatural hΛ E.profile.family).refF_pos δ hp hX
    have hn := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hX hd) hf.le
    change p.1 * radialPartial (referenceProfiles E.profile hΛ hδ hδT hP0).f p /
      (referenceProfiles E.profile hΛ hδ hδT hP0).f p ≤ 0 at hn
    unfold logSlope
    linarith

theorem reference_antitone {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) {R η : ℝ} (_ : 0 ≤ R)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    AntitoneOn (fun X => (referenceProfiles E.profile hΛ hδ hδT hP0).f (X, η)) (Icc 0 R) := by
  let N := Input.ofNatural hΛ E.profile.family
  let P := referenceProfiles E.profile hΛ hδ hδT hP0
  have hp (X : ℝ) (hx : X ∈ Icc (0 : ℝ) R) : (X, η) ∈ N.radialDomain.carrier :=
    reference_mem E.profile hΛ (p := (X, η)) hx.1 hη
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 R)
  · exact (radial_slice_continuous N.radialDomain P.f_smooth η).mono (fun X hx => hp X hx)
  · intro X hx
    exact (radialPartial_hasDerivAt N.radialDomain P.f_smooth (hp X (interior_subset
        hx))).differentiableAt.differentiableWithinAt
  · intro X hx
    have hXi : X ∈ Ioo (0 : ℝ) R := by simpa only [interior_Icc] using hx
    rw [(radialPartial_hasDerivAt N.radialDomain P.f_smooth (hp X (interior_subset hx))).deriv]
    exact reference_radial_nonpos E hΛ hδ hδT hP0 (p := (X, η)) hXi.1 hη

end ReferenceMonotonicity

/-! ## A normalization chosen before the cutoff time controls pressure -/

section SmallPressure

variable {D : RadialDomain} (P : Profiles D)

theorem pressureJets_small {p : Point} (hp : p ∈ D.carrier)
    (hX : p.1 ∈ Icc (0 : ℝ) 110) {Λ C K ε : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hΛ : 1 + 1 / ε ≤ Λ) (hC : 1 + 220 * K ^ 2 / ε ≤ C)
    (hf : ∀ s ∈ Icc (0 : ℝ) p.1, |P.f (s, p.2)| ≤ K / C)
    (hfη : ∀ s ∈ Icc (0 : ℝ) p.1, |parameterPartial P.f (s, p.2)| ≤ K / C) :
    ‖pressureJets P Λ p‖ < ε := by
  have hΛ0 : 0 < Λ := by linarith [one_div_pos.mpr hε]
  have hC1 : 1 ≤ C := by
    have hn : 0 ≤ 220 * K ^ 2 / ε := by positivity
    linarith
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hinv : |1 / Λ| < ε := by
    rw [abs_of_pos (one_div_pos.mpr hΛ0), div_lt_iff₀ hΛ0]
    have hmul := (div_lt_iff₀ hε).mp (show 1 / ε < Λ by linarith)
    nlinarith
  have hsize : 220 * K ^ 2 / C ^ 2 < ε := by
    apply (div_lt_iff₀ (sq_pos_of_pos hC0)).mpr
    have hb := (div_lt_iff₀ hε).mp (show 220 * K ^ 2 / ε < C by linarith)
    have hh : C ≤ C ^ 2 := by nlinarith
    nlinarith
  have hvnum : p.1 * K ^ 2 ≤ 220 * K ^ 2 :=
    mul_le_mul_of_nonneg_right (hX.2.trans (by norm_num)) (sq_nonneg K)
  have hpnum : (2 * p.1) * K ^ 2 ≤ 220 * K ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hX.2]) (sq_nonneg K)
  have hval : |P.pressure p - P.pressure0 p.2| < ε := by
    apply (pressure_increment_bound P hp hX.1 hK hC0 hf).trans_lt
    exact (div_le_div_of_nonneg_right hvnum (sq_nonneg C)).trans_lt hsize
  have hpar : |parameterPartial P.pressure p - deriv P.pressure0 p.2| < ε := by
    apply (pressure_parameter_increment_bound P hp hX.1 hK hC0 hf hfη).trans_lt
    exact (div_le_div_of_nonneg_right hpnum (sq_nonneg C)).trans_lt hsize
  have hdot : |p.1 * P.f p ^ 2| < ε := by
    have hd := pressure_dot_bound P hp hX.1 (by simpa only [Prod.eta] using hf p.1 ⟨hX.1, le_rfl⟩)
    rw [P.radialPartial_pressure hp] at hd
    exact hd.trans_lt ((div_le_div_of_nonneg_right hvnum (sq_nonneg C)).trans_lt hsize)
  apply (pi_norm_lt_iff (x := pressureJets P Λ p) hε).2
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact hinv
  · exact hval
  · exact hpar
  · exact hdot

end SmallPressure

/-! ## Cone comparison for the actual reference histories -/

/-- Hold region, given by `Icc (0 : ℝ) 110 ×ˢ Icc (-1 : ℝ) 1`. -/
noncomputable def holdRegion : Set Point := Icc (0 : ℝ) 110 ×ˢ Icc (-1 : ℝ) 1

/-- Reference bounds on hold data, collecting `source_lower`, `logarithmic_slope`,
`first_positive`, `cone_margin`, `at_hundred`. -/
structure ReferenceBoundsOnHold {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : NaturalEntrance.CoefficientProfile d Λ C)
    (hΛ : 0 < Λ) {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) : Prop where
  source_lower : ∀ p ∈ holdRegion,
    (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 12 / 5 <
      sourceQ (referenceProfiles F hΛ hδ hδT hP0) h p
  logarithmic_slope : ∀ p ∈ holdRegion,
    logSlope (referenceProfiles F hΛ hδ hδT hP0) p ≤ 1
  first_positive : ∀ p ∈ holdRegion, 0 < p.1 →
    0 < p1 (referenceProfiles F hΛ hδ hδT hP0) h p
  cone_margin : ∀ p ∈ holdRegion, 4 / Λ ≤ p.1 →
    (9 / 4 : ℝ) < coneSize (referenceProfiles F hΛ hδ hδT hP0) h p
  at_hundred : ∀ η ∈ Icc (-1 : ℝ) 1,
    3 < p1 (referenceProfiles F hΛ hδ hδT hP0) h (100, η)

section ConeComparison

open NaturalProfile ReferencePath

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
variable (E : NaturalEntrance.EntranceProfile d Λ C) (hΛ : 0 < Λ)
variable {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) (hP0 : ContDiff ℝ ∞ P0)
variable (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)

/-- This comparison uses only the actual primitive-defined stocks. The source
bounds are supplied below by the compact model and the concrete jet theorem. -/
theorem bounds_from_sources (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)
    {K ν : ℝ} (hK : 0 < K) (hν : 0 < ν) (hC : 0 < C)
    (hcut : ∀ η ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z h j P0 η| ≤ ν →
      99 / 100 < NaturalAxisData.chi h j σ η)
    (hCbig : 18 * K / ((4 / Λ) * (ν / 2)) < C)
    (hq : ∀ p ∈ holdRegion,
      (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 12 / 5 <
        sourceQ (referenceProfiles E.profile hΛ hδ hδT hP0) h p)
    (hn : ∀ p ∈ holdRegion,
      |(referenceProfiles E.profile hΛ hδ hδT hP0).axialSource h p - NaturalAxisData.Z h j P0 p.2|
          < ν / 2)
    (hfbound : ∀ p ∈ holdRegion, |(referenceProfiles E.profile hΛ hδ hδT hP0).f p| ≤ K / C) :
    ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0 := by
  let P := referenceProfiles E.profile hΛ hδ hδT hP0
  let N := Input.ofNatural hΛ E.profile.family
  have hq0 (p : Point) (hp : p ∈ holdRegion) : (12 / 5 : ℝ) ≤ sourceQ P h p := by
    have hg : 0 ≤ (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (NaturalAxisData.L_pos hsmall hp.2).le) hΛ.le) (NaturalAxisData.chi_bounds h j hσ p.2).1
    have hs := hq p hp
    change _ < sourceQ P h p at hs
    linarith
  have hpos (p : Point) (hp : p ∈ holdRegion) (hX : 0 < p.1) : 0 < p1 P h p := by
    have hdom := reference_mem E.profile hΛ hp.1.1 hp.2
    have hs := p1_lower_from_source P hdom hX h (NaturalAxisData.L_pos hsmall hp.2)
      (by norm_num : (0 : ℝ) ≤ 12 / 5)
      (fun s hsp => N.refF_pos δ (reference_mem E.profile hΛ (p := (s, p.2)) hsp.1 hp.2) hsp.1)
      (reference_antitone E hΛ hδ hδT hP0 hX.le hp.2)
      (fun s hsp => hq0 (s, p.2) ⟨⟨hsp.1, hsp.2.trans hp.1.2⟩, hp.2⟩)
    exact (div_pos (mul_pos (by norm_num) hX)
      (mul_pos (by norm_num) (NaturalAxisData.L_pos hsmall hp.2))).trans_le hs
  refine ⟨hq, ?_, hpos, ?_, ?_⟩
  · intro p hp
    exact reference_logSlope_le_one E hΛ hδ hδT hP0 hp.1.1 hp.2
  · intro p hp haX
    have ha : (0 : ℝ) < 4 / Λ := by positivity
    have hX := ha.trans_le haX
    have hdom := reference_mem E.profile hΛ hp.1.1 hp.2
    have hL := NaturalAxisData.L_pos hsmall hp.2
    have hL1 := NaturalEntrance.L_le_one hsmall p.2
    apply cone_margin_of_dichotomy (hpos p hp hX)
    by_cases hchi : 99 / 100 ≤ NaturalAxisData.chi h j σ p.2
    · left
      let q : ℝ := (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2
      have hqpos : 0 ≤ q := by
        dsimp [q]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL.le) hΛ.le)
          (NaturalAxisData.chi_bounds h j hσ p.2).1
      have hqa : (23 / 10 : ℝ) * NaturalAxisData.L h p.2 ≤ q * (4 / Λ) := by
        have he : q * (4 / Λ) = (94 / 25 : ℝ) * NaturalAxisData.L h p.2 *
            NaturalAxisData.chi h j σ p.2 := by dsimp [q]; field_simp ; ring
        rw [he]
        nlinarith
      apply p1_preserves_lower P hdom hX h hL ha haX (by norm_num : (0 : ℝ) ≤ 23 / 10)
        hqpos hqa
        (fun s hsp => N.refF_pos δ (reference_mem E.profile hΛ (p := (s, p.2)) hsp.1 hp.2) hsp.1)
        (reference_antitone E hΛ hδ hδT hP0 hX.le hp.2)
      · intro s hs
        have hsp : (s, p.2) ∈ holdRegion := ⟨⟨ha.le.trans hs.1, hs.2.trans hp.1.2⟩, hp.2⟩
        have hh := hq (s, p.2) hsp
        change q + 12 / 5 < sourceQ P h (s, p.2) at hh
        linarith
      · rw [reference_p1_natural E.profile hΛ hδ hδT hP0 hsmall (p := (4 / Λ, p.2)) hp.2 ha le_rfl]
        exact (E.profile.family.slope p.2 (original_interval_interior hp.2) hchi).le
    · right
      have hZ : ν < |NaturalAxisData.Z h j P0 p.2| := by
        by_contra hh
        exact hchi (hcut p.2 hp.2 (le_of_not_gt hh)).le
      have hdev := ns_deviation_bound P hdom hX h hL
        (Z := NaturalAxisData.Z h j P0 p.2) (ε := ν / 2)
        (fun s hsp => (hn (s, p.2) ⟨⟨hsp.1, hsp.2.trans hp.1.2⟩, hp.2⟩).le)
      have htri : |NaturalAxisData.Z h j P0 p.2| / NaturalAxisData.L h p.2 ≤
          |ns P h p| + (ν / 2) / NaturalAxisData.L h p.2 := by
        have ht := abs_sub (ns P h p) (ns P h p - NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L
            h p.2)
        have he : ns P h p - (ns P h p - NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L h p.2) =
            NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L h p.2 := by ring
        rw [he, abs_div, abs_of_pos hL] at ht
        linarith
      have hdiv : (|NaturalAxisData.Z h j P0 p.2| - ν / 2) / NaturalAxisData.L h p.2 ≤ |ns P h p|
          := by
        rw [sub_div]
        linarith
      have hns : ν / 2 ≤ |ns P h p| := by
        have hm := (div_le_iff₀ hL).mp hdiv
        have hu := mul_le_of_le_one_right (abs_nonneg (ns P h p)) hL1
        linarith
      exact p2_large_of_small_f P hX hp.1.2 h ha haX hK hC (div_pos hν (by norm_num))
        (N.refF_pos δ hdom hp.1.1) ((le_abs_self (P.f p)).trans (hfbound p hp)) hns hCbig
  · intro η hη
    apply p1_at_hundred_gt_three P (reference_mem E.profile hΛ (p := (100, η)) (by norm_num) hη)
      (NaturalAxisData.L_pos hsmall hη) (NaturalEntrance.L_le_one hsmall η)
      (fun s hs => N.refF_pos δ (reference_mem E.profile hΛ (p := (s, η)) hs.1 hη) hs.1)
      (reference_antitone E hΛ hδ hδT hP0 (by norm_num : (0 : ℝ) ≤ 100) hη)
    intro s hs
    exact hq0 (s, η) ⟨⟨hs.1, hs.2.trans (by norm_num)⟩, hη⟩

end ConeComparison

/-! ## Passing from the bounded concrete jets to the sources -/

theorem holdRegion_scale {p : Point} (hp : p ∈ holdRegion) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : (t * p.1, p.2) ∈ holdRegion := by
  refine ⟨⟨mul_nonneg ht.1 hp.1.1, ?_⟩, hp.2⟩
  exact (mul_le_of_le_one_left hp.1.1 ht.2).trans hp.1.2

theorem normalized_history_bounds {D : RadialDomain} (P : Profiles D)
    {Λ B j : ℝ}
    (hU : ∀ p ∈ holdRegion, |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B)
    (hUη : ∀ p ∈ holdRegion, |Λ * (parameterPartial P.U p - 4)| ≤ B)
    {p : Point} (hp : p ∈ holdRegion) (hpD : p ∈ D.carrier) :
    |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B ∧
      |Λ * (average (parameterPartial P.U) p - 4)| ≤ B := by
  constructor
  · exact average_error_bound P.U_smooth hpD (fun t ht => hU (t * p.1, p.2) (holdRegion_scale hp
      ht))
  · exact average_error_bound (parameterPartial_smooth D P.U_smooth) hpD
      (fun t ht => hUη (t * p.1, p.2) (holdRegion_scale hp ht))

/-- The source threshold is fixed before Λ and C. Every occurrence of a
history or derivative on the right is an actual operation on `P`. -/
theorem sourceQ_uniform_threshold {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ M > 0, ∀ Λ : ℝ, M ≤ Λ → ∀ {D : RadialDomain} (P : Profiles D) (p : Point),
      ∀ Y θ φ e : ℝ,
        (Y, p.2) ∈ NaturalEntrance.entranceSet → θ ∈ Icc (0 : ℝ) 1 →
        (1 / 8 : ℝ) ≤ φ → φ ≤ B → |e| ≤ K / Λ →
        |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B →
        |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B →
        |Λ * (average (parameterPartial P.U) p - 4)| ≤ B →
        |parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2| ≤ B →
        p.1 * radialPartial P.f p / P.f p = θ * Y *
          (NaturalEntrance.sourceJets v.epsilon_pos (NaturalEntrance.referencePair v) (Y, p.2) 1 +
              e) / φ →
        (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 12 / 5 <
          sourceQ P h p := by
  obtain ⟨M, hM, he⟩ := qModel_uniform_lower v hsmall hσ B hK
  refine ⟨M, hM, ?_⟩
  intro Λ hΛ D P p Y θ φ e hY hθ hφ hφB herr hu hv hvη hfη hslope
  have hΛ0 := hM.trans_le hΛ
  have hj : qJets P j σ h Λ φ p ∈ Metric.closedBall (0 : Fin 5 → ℝ) B :=
    qJets_bound P h j σ hB (by rw [abs_of_nonneg (by linarith)]; exact hφB) hu hv hvη hfη
  let sample : SourceParameter B := (⟨(Y, p.2), hY⟩, (⟨θ, hθ⟩, ⟨qJets P j σ h Λ φ p, hj⟩))
  have hh := he Λ hΛ sample e herr
  rw [sourceQ_model P h j σ hΛ0.ne' hφ p hslope]
  exact hh

/-! ## The ordered, constructed reference continuation -/

/-- Lemma 5.2 for the actual reference path and its literal histories.
The bounded jet constants and the scale threshold precede Λ; the pressure
normalization threshold precedes C; the short cutoff time is chosen last.
No source estimate, stock estimate, or cone condition is an input. -/
theorem exists_reference_bounds {h j σ ν : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) (hν : 0 < ν)
    (hcut : ∀ η ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z h j P0 η| ≤ ν →
      99 / 100 < NaturalAxisData.chi h j σ η) :
    ∃ M > 0, ∀ Λ : ℝ, ∀ hΛ : 0 < Λ, M ≤ Λ →
      ∃ C₀ > 0, ∀ C : ℝ, C₀ ≤ C →
        ∃ E : NaturalEntrance.EntranceProfile d Λ C,
          ∃ r > 0, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < r →
            ∃ hδT : 2 * δ < ReferencePath.rampLimit,
              ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0 := by
  obtain ⟨B, Mj, Kerr, hB, hMj, hKerr, hjets⟩ := ReferenceJetBounds.ordered_reference_bounds d hσ
  obtain ⟨Mq, hMq, hqmodel⟩ := sourceQ_uniform_threshold d.coefficients hsmall hσ
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) hB.le) hKerr
  obtain ⟨Me, hMe, hentrance⟩ := NaturalEntrance.exists_entranceProfile d hsmall hσ hP0 hν hcut
  obtain ⟨τ, hτ, hnmodel⟩ := nModel_uniform_error h j hP0 B (ε := ν / 2) (div_pos hν (by norm_num))
  let M := max Mj (max Mq (max Me (1 + 1 / τ)))
  refine ⟨M, hMj.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ hM
  have hscalej : Mj ≤ Λ := (le_max_left _ _).trans hM
  have hrest : max Mq (max Me (1 + 1 / τ)) ≤ Λ := (le_max_right _ _).trans hM
  have hscaleq : Mq ≤ Λ := (le_max_left _ _).trans hrest
  have hrest' : max Me (1 + 1 / τ) ≤ Λ := (le_max_right _ _).trans hrest
  have hscalee : Me ≤ Λ := (le_max_left _ _).trans hrest'
  have hscalen : 1 + 1 / τ ≤ Λ := (le_max_right _ _).trans hrest'
  obtain ⟨K, hK, hjetΛ⟩ := hjets Λ hΛ hscalej
  let C₀ := max (d.normalizationThreshold Λ)
    (max (NaturalEntrance.entranceNormalization d Λ ν)
      (max (1 + 220 * K ^ 2 / τ) (1 + 18 * K / ((4 / Λ) * (ν / 2)))))
  have hC₀ : 0 < C₀ := (Real.exp_pos _).trans_le (le_max_left _ _)
  refine ⟨C₀, hC₀, ?_⟩
  intro C hC
  have hnormal : d.normalizationThreshold Λ ≤ C := (le_max_left _ _).trans hC
  have htail : max (NaturalEntrance.entranceNormalization d Λ ν)
      (max (1 + 220 * K ^ 2 / τ) (1 + 18 * K / ((4 / Λ) * (ν / 2)))) ≤ C :=
    (le_max_right _ _).trans hC
  have hentry : NaturalEntrance.entranceNormalization d Λ ν ≤ C := (le_max_left _ _).trans htail
  have hlast : max (1 + 220 * K ^ 2 / τ) (1 + 18 * K / ((4 / Λ) * (ν / 2))) ≤ C :=
    (le_max_right _ _).trans htail
  have hpressure : 1 + 220 * K ^ 2 / τ ≤ C := (le_max_left _ _).trans hlast
  have hcone : 18 * K / ((4 / Λ) * (ν / 2)) < C := by
    have hh := (le_max_right _ _).trans hlast
    linarith
  have hCpos : 0 < C := hC₀.trans_le hC
  obtain ⟨E⟩ := hentrance Λ hscalee C hentry
  obtain ⟨r, hr, hlastChoice⟩ := hjetΛ C hnormal E.profile
  refine ⟨E, r, hr, ?_⟩
  intro δ hδ hδr
  obtain ⟨hc, hj, hsamples⟩ := hlastChoice δ hδ hδr
  refine ⟨hc.length_bound, ?_⟩
  let P := referenceProfiles E.profile hΛ hδ hc.length_bound hP0
  have hJ : ReferenceJetBounds.JetBounds h j σ Λ C B K P.f P.U := hj
  have hB0 : 0 ≤ B := by linarith
  have hhistory (p : Point) (hp : p ∈ holdRegion) :
      |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B ∧
      |Λ * (average (parameterPartial P.U) p - 4)| ≤ B :=
    normalized_history_bounds P hJ.axial_value hJ.axial_parameter hp
      (reference_mem E.profile hΛ hp.1.1 hp.2)
  have hsourceq (p : Point) (hp : p ∈ holdRegion) :
      (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 12 / 5 <
        sourceQ P h p := by
    by_cases hnat : p.1 ≤ 4 / Λ
    · have hY : Λ * p.1 ≤ 4 := by nlinarith [(le_div_iff₀ hΛ).mp hnat]
      have hpoint : NaturalProfile.rescalePoint Λ p ∈ NaturalEntrance.entranceSet :=
        ⟨⟨mul_nonneg hΛ.le hp.1.1, by change Λ * p.1 ≤ 41 / 10; linarith⟩, hp.2⟩
      have he := reference_sourceQ_natural E.profile hΛ hδ hc.length_bound hP0
        (NaturalEntrance.entrance_mem_strip hpoint) hnat
      change sourceQ P h p = _ at he
      rw [he]
      have hh := E.source_lower p hpoint
      have hnonneg : 0 ≤ NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 :=
        mul_nonneg (mul_nonneg (NaturalAxisData.L_pos hsmall hp.2).le hΛ.le)
          (NaturalAxisData.chi_bounds h j hσ p.2).1
      nlinarith
    · obtain ⟨s⟩ := hsamples p hp (le_of_lt (lt_of_not_ge hnat))
      exact hqmodel Λ hscaleq P p s.Y s.theta s.phi s.error s.point_mem s.theta_mem
        s.phi_lower s.phi_upper s.error_bound (hJ.axial_value p hp)
        (hhistory p hp).1 (hhistory p hp).2 (hJ.log_parameter p hp) s.slope_eq
  have hsourcen (p : Point) (hp : p ∈ holdRegion) :
      |P.axialSource h p - NaturalAxisData.Z h j P0 p.2| < ν / 2 := by
    have hdom := reference_mem E.profile hΛ hp.1.1 hp.2
    have hx : |Λ * (p.1 * radialPartial P.U p)| ≤ B := by
      simpa only [mul_assoc] using hJ.axial_radial p hp
    have hv := nJets_bound P j hB0 (hJ.axial_value p hp) (hJ.axial_parameter p hp)
      (hhistory p hp).1 (hhistory p hp).2 hx
    have hz : ‖pressureJets P Λ p‖ < τ :=
      pressureJets_small P hdom hp.1 hτ hK.le hscalen hpressure
        (fun s hs => hJ.angular_value (s, p.2) ⟨⟨hs.1, hs.2.trans hp.1.2⟩, hp.2⟩)
        (fun s hs => hJ.angular_parameter (s, p.2) ⟨⟨hs.1, hs.2.trans hp.1.2⟩, hp.2⟩)
    rw [sourceN_model P h j hΛ.ne' p hp.2 hv]
    exact hnmodel (⟨p.2, hp.2⟩, ⟨nJets P j Λ p, hv⟩) (pressureJets P Λ p) hz
  exact bounds_from_sources E hΛ hδ hc.length_bound hP0 hsmall hσ hK hν hCpos hcut hcone
    hsourceq hsourcen hJ.angular_value

end NavierStokes.ReferenceBounds

end
end

end

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.ActivationContinuation

open ProfileHistories

/-- Shear size, given by `a * (1 + (b / a) ^ 2)`. -/
noncomputable def shearSize (a b : ℝ) : ℝ := a * (1 + (b / a) ^ 2)
/-- Projection, given by `p + q * (b / a)`. -/
noncomputable def projection (p q a b : ℝ) : ℝ := p + q * (b / a)
/-- Transverse, given by `q - p * (b / a)`. -/
noncomputable def transverse (p q a b : ℝ) : ℝ := q - p * (b / a)

/-- Relaxed data, collecting `first_positive`, `projection_positive`, `cone`. -/
structure Relaxed (a b p q : ℝ) : Prop where
  first_positive : 0 < a
  projection_positive : 2 < projection p q a b
  cone : shearSize a b < ConeAlgebra.coneBound (projection p q a b) (transverse p q a b)

/-- Projection constant, given by `1 + 2 * M + M ^ 2`. -/
noncomputable def projectionConstant (M : ℝ) : ℝ := 1 + 2 * M + M ^ 2
/-- Speed constant, given by `M * (1 + 4 * M ^ 2)`. -/
noncomputable def speedConstant (M : ℝ) : ℝ := M * (1 + 4 * M ^ 2)

theorem projectionConstant_pos {M : ℝ} (hM : 0 ≤ M) : 0 < projectionConstant M := by
  unfold projectionConstant
  positivity

theorem speedConstant_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ speedConstant M := by
  unfold speedConstant
  positivity

/-- The axial shutoff factor occurs once in the limiting projection. -/
theorem projection_identity (A B p q θ R : ℝ) :
    p + q * (θ * (B / A) * R) - (A + θ * B ^ 2 / A) =
      (p - A) + (q - B) * θ * (B / A) * R + θ * B * (B / A) * (R - 1) := by
  ring

theorem projection_comparison {A B p q θ R M ε : ℝ} (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hB : |B| ≤ M) (hBA : |B / A| ≤ M)
    (hp : |p - A| ≤ ε) (hq : |q - B| ≤ ε) (hR : |R - 1| ≤ ε) :
    |p + q * (θ * (B / A) * R) - (A + θ * B ^ 2 / A)| ≤
      ε * projectionConstant M := by
  have hR2 : |R| ≤ 2 := by
    have ht := abs_sub R 1
    have he : R = (R - 1) + 1 := by ring
    have hh := abs_add_le (R - 1) 1
    rw [← he] at hh
    norm_num at hh
    linarith
  rw [projection_identity]
  calc
    _ ≤ |p - A| + |q - B| * |θ| * |B / A| * |R| +
        |θ| * |B| * |B / A| * |R - 1| := by
      exact ((abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)).trans_eq (by
          simp only [abs_mul])
    _ ≤ ε + ε * 1 * M * 2 + 1 * M * M * ε := by
      rw [abs_of_nonneg hθ.1]
      gcongr <;> first | exact hθ.1 | exact hθ.2
    _ = _ := by unfold projectionConstant; ring

theorem damped_shear_ratio {κ A : ℝ} (hκ : κ ≠ 0) (hA : A ≠ 0) (θ B R : ℝ) :
    (κ * θ * B * R) / (κ * A) = θ * (B / A) * R := by
  field_simp

theorem damped_shear_bound {κ A B θ R M : ℝ} (hκ : 0 < κ) (hA : 0 < A)
    (hM : 0 ≤ M) (hAM : A ≤ M) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hBA : |B / A| ≤ M) (hR : |R| ≤ 2) :
    shearSize (κ * A) (κ * θ * B * R) ≤ κ * speedConstant M := by
  have hr : |θ * (B / A) * R| ≤ 2 * M := by
    rw [abs_mul, abs_mul, abs_of_nonneg hθ.1]
    calc
      θ * |B / A| * |R| ≤ 1 * M * 2 := by gcongr; exact hθ.2
      _ = _ := by ring
  have hrsq : (θ * (B / A) * R) ^ 2 ≤ (2 * M) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hr 2
  rw [shearSize, damped_shear_ratio hκ.ne' hA.ne']
  calc
    _ ≤ (κ * M) * (1 + (2 * M) ^ 2) := by gcongr
    _ = _ := by unfold speedConstant; ring

/-- Uniform finite-dimensional comparison for both the constant-damping
segment and the axial shutoff. No inverse power of the damping is used. -/
theorem damped_relaxed {κ A B p q θ R M ε : ℝ} (hκ : 0 < κ) (hA : 0 < A)
    (hM : 0 ≤ M) (hAM : A ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (hB : |B| ≤ M) (hBA : |B / A| ≤ M)
    (hp : |p - A| ≤ ε) (hq : |q - B| ≤ ε) (hR : |R - 1| ≤ ε)
    (hprojection : (9 / 4 : ℝ) ≤ A + θ * B ^ 2 / A)
    (herror : ε * projectionConstant M ≤ 1 / 8)
    (hspeed : κ * speedConstant M ≤ 1) :
    Relaxed (κ * A) (κ * θ * B * R) p q := by
  have hcmp := projection_comparison hM hε hε1 hθ hB hBA hp hq hR
  have hproj : 2 < projection p q (κ * A) (κ * θ * B * R) := by
    rw [projection, damped_shear_ratio hκ.ne' hA.ne']
    have hh := (abs_le.mp hcmp).1
    linarith
  have hR2 : |R| ≤ 2 := by
    have hh := abs_add_le (R - 1) 1
    have he : R - 1 + 1 = R := by ring
    rw [he] at hh
    norm_num at hh
    linarith
  have hv : shearSize (κ * A) (κ * θ * B * R) ≤ 2 :=
    (damped_shear_bound hκ hA hM hAM hθ hBA hR2).trans (hspeed.trans (by norm_num))
  exact ⟨mul_pos hκ hA, hproj, ConeAlgebra.relaxed_cone_of_le_two hproj hv⟩

theorem zero_axial_relaxed {a p q : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) (hp : 2 < p) :
    Relaxed a 0 p q := by
  have hproj : projection p q a 0 = p := by simp [projection]
  have hv : shearSize a 0 = a := by simp [shearSize]
  refine ⟨ha, ?_, ?_⟩
  · rwa [hproj]
  · rw [hv, hproj]
    exact ConeAlgebra.relaxed_cone_of_le_two hp ha2

theorem convex_final_shear {a θ : ℝ} (ha : 0 < a) (ha4 : a ≤ 4 / 5)
    (hθ : θ ∈ Icc (0 : ℝ) 1) :
    0 < (1 - θ) * a + θ * (4 / 5) ∧ (1 - θ) * a + θ * (4 / 5) ≤ 4 / 5 := by
  constructor
  · by_cases hz : θ = 0
    · simpa only [hz, sub_zero, one_mul, zero_mul, add_zero] using ha
    · have hp : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hz)
      exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hθ.2) ha.le)
        (mul_pos hp (by norm_num))
  · have hm := mul_le_mul_of_nonneg_left ha4 (sub_nonneg.mpr hθ.2)
    linarith

/-! ## Physical cone coordinates -/

section Physical

variable {D : RadialDomain} (P : Profiles D)

/-- Shear A, given by `-2 * p.1 * radialPartial P.f p / P.f p`. -/
noncomputable def shearA (p : Point) : ℝ := -2 * p.1 * radialPartial P.f p / P.f p
/-- Shear B, given by `-2 * p.1 * radialPartial P.U p / P.E p`. -/
noncomputable def shearB (p : Point) : ℝ := -2 * p.1 * radialPartial P.U p / P.E p

/-- Is relaxed, given by `Relaxed (shearA P p) (shearB P p) (ReferenceBounds.p1 P h p)
(ReferenceBounds.p2 P h p)`. -/
noncomputable def IsRelaxed (h : ℝ) (p : Point) : Prop :=
  Relaxed (shearA P p) (shearB P p) (ReferenceBounds.p1 P h p) (ReferenceBounds.p2 P h p)

theorem logSlope_eq_shear (p : Point) :
    ReferenceBounds.logSlope P p = 1 - shearA P p / 2 := by
  unfold ReferenceBounds.logSlope shearA
  ring

theorem zero_axial_relaxed_profile {h : ℝ} {p : Point} (ha : 0 < shearA P p)
    (ha2 : shearA P p ≤ 2) (hu : radialPartial P.U p = 0)
    (hp : 2 < ReferenceBounds.p1 P h p) : IsRelaxed P h p := by
  unfold IsRelaxed
  rw [show shearB P p = 0 by simp [shearB, hu]]
  exact zero_axial_relaxed ha ha2 hp

end Physical

/-! ## An exact barrier for the final constant-slope hold -/

/-- Weighted gap, given by `Real.exp ((3 / 5 : ℝ) * Real.log X) * (g X - b)`. -/
noncomputable def weightedGap (g : ℝ → ℝ) (b X : ℝ) : ℝ :=
  Real.exp ((3 / 5 : ℝ) * Real.log X) * (g X - b)

theorem weightedGap_hasDerivAt {g : ℝ → ℝ} {g' X : ℝ} (hX : 0 < X)
    (hg : HasDerivAt g g' X) (b : ℝ) :
    HasDerivAt (weightedGap g b)
      (Real.exp ((3 / 5 : ℝ) * Real.log X) / X *
        (X * g' + (3 / 5) * g X - (3 / 5) * b)) X := by
  have hd := (((Real.hasDerivAt_log hX.ne').const_mul (3 / 5 : ℝ)).exp).mul (hg.sub_const b)
  convert! hd using 1
  field_simp; ring

theorem scalar_hold_barrier {g : ℝ → ℝ} {a X b : ℝ} (ha : 0 < a) (haX : a ≤ X)
    (hg : ∀ t ∈ Icc a X, DifferentiableAt ℝ g t)
    (heq : ∀ t ∈ Icc a X, (3 / 5 : ℝ) * b ≤ t * deriv g t + (3 / 5) * g t)
    (hinit : b < g a) : b < g X := by
  have hd (t : ℝ) (ht : t ∈ Icc a X) :=
    weightedGap_hasDerivAt (ha.trans_le ht.1) (hg t ht).hasDerivAt b
  have hm : MonotoneOn (weightedGap g b) (Icc a X) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a X)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have ht' := interior_subset ht
      exact mul_nonneg (div_nonneg (Real.exp_pos _).le (ha.trans_le ht'.1).le)
        (sub_nonneg.mpr (heq t ht'))
  have hin : 0 < weightedGap g b a := mul_pos (Real.exp_pos _) (sub_pos.mpr hinit)
  have hout := hin.trans_le (hm ⟨le_rfl, haX⟩ ⟨haX, le_rfl⟩ haX)
  change 0 < Real.exp ((3 / 5 : ℝ) * Real.log X) * (g X - b) at hout
  exact sub_pos.mp (pos_of_mul_pos_right hout (Real.exp_pos _).le)

theorem actual_hold_barrier {D : RadialDomain} (P : Profiles D) {h η a X : ℝ}
    (ha : 2 ≤ a) (haX : a ≤ X) (hL : 0 < NaturalAxisData.L h η)
    (hL1 : NaturalAxisData.L h η ≤ 1)
    (hmem : ∀ t ∈ Icc a X, (t, η) ∈ D.carrier)
    (hf : ∀ t ∈ Icc a X, 0 < P.f (t, η))
    (hl : ∀ t ∈ Icc a X, ReferenceBounds.logSlope P (t, η) = 3 / 5)
    (hs : ∀ t ∈ Icc a X, 1 < ReferenceBounds.sourceQ P h (t, η))
    (hinit : 2 < ReferenceBounds.p1 P h (a, η)) :
    2 < ReferenceBounds.p1 P h (X, η) := by
  apply scalar_hold_barrier (g := fun t => ReferenceBounds.p1 P h (t, η))
    (by linarith : (0 : ℝ) < a) haX ?_ ?_ hinit
  · intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by linarith : (0 : ℝ) < a) ht.1
    have hlag := P.angularLag_smoothAt h (hmem t ht) htpos.ne' (P.H_ne_zero htpos.ne' (hf t ht).ne')
    exact ((contDiffAt_id.mul (hlag.comp t (contDiffAt_id.prodMk contDiffAt_const))).div_const
      (NaturalAxisData.L h η)).differentiableAt (by simp)
  · intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by linarith : (0 : ℝ) < a) ht.1
    have he := ReferenceBounds.p1_equation P (hmem t ht) htpos (hf t ht).ne' h
    rw [hl t ht] at he
    change _ = t * ReferenceBounds.sourceQ P h (t, η) / NaturalAxisData.L h η at he
    rw [he]
    apply (le_div_iff₀ hL).mpr
    have ht2 : 2 ≤ t := ha.trans ht.1
    have hst := hs t ht
    nlinarith

/-! ## The final hold source is derived from the axis model -/

open NaturalAxisCoefficients

/-- Hold vector, given by `![1, v 1, v 2, v 3, v 4]`. -/
noncomputable def holdVector (v : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![1, v 1, v 2, v 3, v 4]

/-- Hold remainder, given by `ReferenceBounds.qRemainder h j σ (1, η) 1 (holdVector v) t (-2 /
5)`. -/
noncomputable def holdRemainder (h j σ η : ℝ) (v : Fin 5 → ℝ) (t : ℝ) : ℝ :=
  ReferenceBounds.qRemainder h j σ (1, η) 1 (holdVector v) t (-2 / 5)

/-- Hold parameter: an abbreviation for `Icc (-1 : ℝ) 1 × ReferenceBounds.BoundedJets B`. -/
abbrev HoldParameter (B : ℝ) := Icc (-1 : ℝ) 1 × ReferenceBounds.BoundedJets B

/-- Hold model, given by `holdRemainder h j σ p.1.val p.2.val t`. -/
noncomputable def holdModel (h j σ B : ℝ) (p : HoldParameter B) (t : ℝ) : ℝ :=
  holdRemainder h j σ p.1.val p.2.val t

theorem holdModel_continuous (h j B : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun p : HoldParameter B × ℝ => holdModel h j σ B p.1 p.2) := by
  let m : HoldParameter B × ℝ → ((Point × ℝ) × (Fin 5 → ℝ)) × (ℝ × ℝ) :=
    fun p => ((((1, p.1.1.val), 1), holdVector p.1.2.val), (p.2, -2 / 5))
  have hvj (i : Fin 5) : Continuous (fun p : HoldParameter B × ℝ => p.1.2.val i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
  have hv : Continuous (fun p : HoldParameter B × ℝ => holdVector p.1.2.val) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact hvj 1
    · exact hvj 2
    · exact hvj 3
    · exact hvj 4
  have hm : Continuous m := by
    dsimp only [m]
    fun_prop
  simpa only [holdModel, holdRemainder, m, Function.comp_def] using
    (ReferenceBounds.qRemainder_continuous h j hσ).comp hm

theorem hold_axis_source_lower {h j η : ℝ} (hsmall : NaturalAxisData.SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    (17 / 10 : ℝ) < -(3 / 5 : ℝ) * NaturalAxisData.W h j η -
      h * (1 - 2 * η * NaturalAxisData.U j η) := by
  have hW := NaturalAxisData.neg_W_lower_bound hsmall hη
  have habs : |η| ≤ 1 := abs_le.mpr hη
  have hu : |NaturalAxisData.U j η| ≤ 4001 / 1000 := by
    calc
      _ ≤ |4 * η| + |j| := abs_add_le _ _
      _ = 4 * |η| + j := by rw [abs_mul, abs_of_pos hsmall.j_pos]; norm_num
      _ ≤ _ := by linarith [hsmall.j_le]
  have hp : |η * NaturalAxisData.U j η| ≤ 4001 / 1000 := by
    rw [abs_mul]
    exact (mul_le_mul habs hu (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hfac : 1 - 2 * η * NaturalAxisData.U j η ≤ 4501 / 500 := by
    have hh := (abs_le.mp hp).1
    linarith
  have hm := mul_le_mul_of_nonneg_left hfac hsmall.h_pos.le
  have hh := mul_le_mul_of_nonneg_right hsmall.h_le (by norm_num : (0 : ℝ) ≤ 4501 / 500)
  linarith

theorem holdModel_chi_zero (h j B : ℝ) {σ : ℝ} (hσ : 0 < σ) (p : HoldParameter B)
    (hchi : NaturalAxisData.chi h j σ p.1.val = 0) :
    holdModel h j σ B p 0 = -(3 / 5 : ℝ) * NaturalAxisData.W h j p.1.val -
      h * (1 - 2 * p.1.val * NaturalAxisData.U j p.1.val) := by
  have hH := NaturalEntrance.chi_zero_imp_H_zero h j hσ hchi
  have hk := NaturalEntrance.gradient_zero_of_chi_zero h j hσ hchi
  norm_num [holdModel, holdRemainder, holdVector, ReferenceBounds.qRemainder, hH, hk]
  ring

theorem holdModel_uniform_lower {h j σ : ℝ} (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (B : ℝ) :
    ∃ M > 0, ∀ Λ : ℝ, M ≤ Λ → ∀ p : HoldParameter B,
      (5 / 4 : ℝ) < NaturalAxisData.L h p.1.val * Λ * NaturalAxisData.chi h j σ p.1.val +
        holdModel h j σ B p (1 / Λ) := by
  have he : Continuous (fun p : HoldParameter B => p.1.val) := by fun_prop
  have hL : Continuous (NaturalAxisData.L h) := by unfold NaturalAxisData.L; fun_prop
  have hcoef : Continuous (fun p : HoldParameter B =>
      NaturalAxisData.L h p.1.val * NaturalAxisData.chi h j σ p.1.val) :=
    (hL.comp he).mul ((NaturalEntrance.chi_continuous h j hσ).comp he)
  have hbase : Continuous (fun p : HoldParameter B => holdModel h j σ B p 0) := by
    simpa only [Function.comp_def, id_eq] using (holdModel_continuous h j B hσ).comp
      (continuous_id.prodMk (continuous_const (y := (0 : ℝ))))
  obtain ⟨M0, hM0, habsorb⟩ := NaturalEntrance.compact_absorption _ _ hcoef hbase
    (fun p => mul_nonneg (NaturalAxisData.L_pos hsmall p.1.property).le
      (NaturalAxisData.chi_bounds h j hσ p.1.val).1) (3 / 2 : ℝ) (by
        intro p hz
        have hchi := (mul_eq_zero.mp hz).resolve_left (NaturalAxisData.L_pos hsmall
            p.1.property).ne'
        rw [holdModel_chi_zero h j B hσ p hchi]
        linarith [hold_axis_source_lower hsmall p.1.property])
  obtain ⟨τ, hτ, hpert⟩ := NaturalEntrance.compact_small_perturbation _
    (holdModel_continuous h j B hσ) (by norm_num : (0 : ℝ) < 1 / 4)
  let M := max M0 (1 + 1 / τ)
  refine ⟨M, hM0.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ p
  have hΛ0 : 0 < Λ := hM0.trans_le ((le_max_left _ _).trans hΛ)
  have hscale := (le_max_right M0 (1 + 1 / τ)).trans hΛ
  have hnorm : ‖1 / Λ‖ < τ := by
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hΛ0), div_lt_iff₀ hΛ0]
    have hm := (div_lt_iff₀ hτ).mp (show 1 / τ < Λ by linarith)
    nlinarith
  have hp := (abs_lt.mp (hpert p (1 / Λ) hnorm)).1
  have hm := habsorb Λ ((le_max_left _ _).trans hΛ) p
  nlinarith

theorem hold_source_identity {D : RadialDomain} (P : Profiles D) (h j σ : ℝ)
    {Λ : ℝ} (hΛ : Λ ≠ 0) (p : Point)
    (hl : ReferenceBounds.logSlope P p = 3 / 5) :
    ReferenceBounds.sourceQ P h p = NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 +
      holdRemainder h j σ p.2 (ReferenceBounds.qJets P j σ h Λ 1 p) (1 / Λ) := by
  have hrad : p.1 * radialPartial P.f p / P.f p = (1 : ℝ) * 1 * (-2 / 5) / 1 := by
    unfold ReferenceBounds.logSlope at hl
    linarith
  have hv : holdVector (ReferenceBounds.qJets P j σ h Λ 1 p) = ReferenceBounds.qJets P j σ h Λ 1 p
      := by
    ext i
    fin_cases i <;> rfl
  unfold holdRemainder
  rw [hv]
  exact ReferenceBounds.sourceQ_model P h j σ hΛ (by norm_num : (1 / 8 : ℝ) ≤ 1) p hrad

theorem actual_hold_source_threshold {h j σ B : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ) (hB : 1 ≤ B) :
    ∃ M > 0, ∀ Λ : ℝ, M ≤ Λ → ∀ {D : RadialDomain} (P : Profiles D) (p : Point),
      p.2 ∈ Icc (-1 : ℝ) 1 → ReferenceBounds.logSlope P p = 3 / 5 →
      |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B →
      |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B →
      |Λ * (average (parameterPartial P.U) p - 4)| ≤ B →
      |parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2| ≤ B →
      (5 / 4 : ℝ) < ReferenceBounds.sourceQ P h p := by
  obtain ⟨M, hM, hb⟩ := holdModel_uniform_lower hsmall hσ B
  refine ⟨M, hM, ?_⟩
  intro Λ hΛ D P p hη hl hu hv hvη hfη
  have hj := ReferenceBounds.qJets_bound P h j σ (zero_le_one.trans hB)
    (φ := 1) (by simpa only [abs_one] using hB) hu hv hvη hfη
  have hh := hb Λ hΛ (⟨p.2, hη⟩, ⟨ReferenceBounds.qJets P j σ h Λ 1 p, hj⟩)
  rw [hold_source_identity P h j σ (hM.trans_le hΛ).ne' p hl]
  exact hh

/-! ## Uniform transfer of actual field and history jets to the stocks -/

theorem compact_vector_perturbation {K E F : Type*} [MetricSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [ProperSpace E] [NormedAddCommGroup F]
    (G : K × E → F) (hG : Continuous G) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p e, ‖e‖ < δ → ‖G (p, e) - G (p, 0)‖ < ε := by
  have hc : IsCompact ((univ : Set K) ×ˢ Metric.closedBall (0 : E) 1) :=
    isCompact_univ.prod (isCompact_closedBall 0 1)
  obtain ⟨δ, hδ, hb⟩ := Metric.uniformContinuousOn_iff.mp
    (hc.uniformContinuousOn_of_continuous hG.continuousOn) ε hε
  refine ⟨min 1 δ, lt_min zero_lt_one hδ, ?_⟩
  intro p e he
  have he1 : ‖e‖ < 1 := he.trans_le (min_le_left _ _)
  have heδ : ‖e‖ < δ := he.trans_le (min_le_right _ _)
  have hp : (p, e) ∈ (univ : Set K) ×ˢ Metric.closedBall (0 : E) 1 :=
    ⟨mem_univ _, by simpa only [Metric.mem_closedBall, dist_zero_right] using he1.le⟩
  have hp0 : (p, (0 : E)) ∈ (univ : Set K) ×ˢ Metric.closedBall (0 : E) 1 :=
    ⟨mem_univ _, Metric.mem_closedBall_self zero_le_one⟩
  have hd : dist (p, e) (p, (0 : E)) < δ := by
    simpa only [Prod.dist_eq, dist_self, dist_zero_right, max_eq_right (norm_nonneg e)] using heδ
  simpa only [dist_eq_norm] using hb (p, e) hp (p, 0) hp0 hd

/-- Stock jet: an abbreviation for `Fin 12 → ℝ`. -/
abbrev StockJet := Fin 12 → ℝ

/-- Stock jet as an element of `StockJet`. -/
noncomputable def stockJet {D : RadialDomain} (P : Profiles D) (p : Point) : StockJet :=
  ![P.f p, P.U p, P.M p, parameterPartial P.M p, P.I p, parameterPartial P.I p,
    P.J p, parameterPartial P.J p, P.S p, parameterPartial P.S p,
    P.pressure p, parameterPartial P.pressure p]

/-- Stock one map, given by `ActivationStocks.stockOne h p.1 p.2 (z 0) (z 2) (z 3) (z 4) (z 5)
(z 6) (z 7)`. -/
noncomputable def stockOneMap (h : ℝ) (p : Point) (z : StockJet) : ℝ :=
  ActivationStocks.stockOne h p.1 p.2 (z 0) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7)

/-- Stock two map, given by `ActivationStocks.stockTwo h p.1 p.2 (z 0) (z 1) (z 2) (z 3) (z 8)
(z 9) (z 10) (z 11)`. -/
noncomputable def stockTwoMap (h : ℝ) (p : Point) (z : StockJet) : ℝ :=
  ActivationStocks.stockTwo h p.1 p.2 (z 0) (z 1) (z 2) (z 3) (z 8) (z 9) (z 10) (z 11)

theorem stockJet_coordinates {D : RadialDomain} (P : Profiles D) (h : ℝ)
    {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    stockOneMap h p (stockJet P p) = ReferenceBounds.p1 P h p ∧
      stockTwoMap h p (stockJet P p) = ReferenceBounds.p2 P h p := by
  constructor
  · exact (ActivationStocks.profileStockOne_eq P h hp hX.ne' hf).symm
  · have he := (ActivationStocks.profileStockTwo_eq P h hp hX).symm
    change stockTwoMap h p (stockJet P p) = p.1 * P.axialLag h p /
      (NaturalAxisData.L h p.2 * P.E p) at he
    rw [he]
    unfold ReferenceBounds.p2 ReferenceBounds.ns
    ring

/-- Stock ball: an abbreviation for `Metric.closedBall (0 : StockJet) B instance (B : ℝ) :
CompactSpace (StockBall B) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)`. -/
abbrev StockBall (B : ℝ) := Metric.closedBall (0 : StockJet) B

instance (B : ℝ) : CompactSpace (StockBall B) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

/-- Clipped stock map as an element of `Fin 3 → ℝ`. -/
noncomputable def clippedStockMap (h μ : ℝ) (p : Point) (z e : StockJet) : Fin 3 → ℝ :=
  let w := z + e
  let f := max μ (w 0)
  ![ActivationStocks.stockOne h p.1 p.2 f (w 2) (w 3) (w 4) (w 5) (w 6) (w 7),
    ActivationStocks.stockTwo h p.1 p.2 f (w 1) (w 2) (w 3) (w 8) (w 9) (w 10) (w 11),
    z 0 / f]

theorem clippedStockMap_continuous {h j μ B : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j) (hμ : 0 < μ) {S : Set Point}
    (hX : ∀ p ∈ S, 0 < p.1) (hη : ∀ p ∈ S, p.2 ∈ Icc (-1 : ℝ) 1) :
    Continuous (fun q : (S × StockBall B) × StockJet =>
      clippedStockMap h μ q.1.1.val q.1.2.val q.2) := by
  have hx : ∀ q : (S × StockBall B) × StockJet, q.1.1.val.1 ≠ 0 :=
    fun q => (hX q.1.1.val q.1.1.property).ne'
  have hl : ∀ q : (S × StockBall B) × StockJet, NaturalAxisData.L h q.1.1.val.2 ≠ 0 :=
    fun q => (NaturalAxisData.L_pos hsmall (hη q.1.1.val q.1.1.property)).ne'
  have hf : ∀ q : (S × StockBall B) × StockJet, max μ ((q.1.2.val + q.2) 0) ≠ 0 :=
    fun q => (hμ.trans_le (le_max_left _ _)).ne'
  have hs : ∀ q : (S × StockBall B) × StockJet, Real.sqrt (2 * q.1.1.val.1) ≠ 0 :=
    fun q => (Real.sqrt_pos.mpr (mul_pos (by norm_num) (hX q.1.1.val q.1.1.property))).ne'
  have hz : Continuous (fun q : (S × StockBall B) × StockJet => q.1.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hw := hz.add (continuous_snd : Continuous (fun q : (S × StockBall B) × StockJet => q.2))
  have hj (i : Fin 12) : Continuous (fun q : (S × StockBall B) × StockJet => (q.1.2.val + q.2) i) :=
    (continuous_apply i).comp hw
  have hz0 := (continuous_apply (0 : Fin 12)).comp hz
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun q : (S × StockBall B) × StockJet =>
      ActivationStocks.stockOne h q.1.1.val.1 q.1.1.val.2 (max μ ((q.1.2.val + q.2) 0))
        ((q.1.2.val + q.2) 2) ((q.1.2.val + q.2) 3) ((q.1.2.val + q.2) 4)
        ((q.1.2.val + q.2) 5) ((q.1.2.val + q.2) 6) ((q.1.2.val + q.2) 7))
    unfold ActivationStocks.stockOne ActivationStocks.massFlux ActivationStocks.angularRemainder
    unfold NaturalAxisData.L NaturalAxisData.D NaturalAxisData.d
    fun_prop (disch := first
      | exact hl
      | exact fun q => mul_ne_zero (mul_ne_zero (by norm_num) (hx q)) (hf q))
  · change Continuous (fun q : (S × StockBall B) × StockJet =>
      ActivationStocks.stockTwo h q.1.1.val.1 q.1.1.val.2 (max μ ((q.1.2.val + q.2) 0))
        ((q.1.2.val + q.2) 1) ((q.1.2.val + q.2) 2) ((q.1.2.val + q.2) 3)
        ((q.1.2.val + q.2) 8) ((q.1.2.val + q.2) 9) ((q.1.2.val + q.2) 10) ((q.1.2.val + q.2) 11))
    unfold ActivationStocks.stockTwo ActivationStocks.massFlux
    unfold NaturalAxisData.L NaturalAxisData.D NaturalAxisData.d NaturalAxisData.A
    fun_prop (disch := exact fun q => mul_ne_zero (mul_ne_zero (hl q) (hs q)) (hf q))
  · change Continuous (fun q : (S × StockBall B) × StockJet => q.1.2.val 0 / max μ ((q.1.2.val +
      q.2) 0))
    fun_prop (disch := exact hf)

/-- Uniform stock continuity on a bounded set of actual profile/history
jets. The threshold is independent of the particular reference member. -/
theorem uniform_stock_transfer {h j μ B ε : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j) (hμ : 0 < μ) (hε : 0 < ε)
    {S : Set Point} (hS : IsCompact S)
    (hX : ∀ p ∈ S, 0 < p.1) (hη : ∀ p ∈ S, p.2 ∈ Icc (-1 : ℝ) 1) :
    ∃ τ > 0, ∀ p ∈ S, ∀ z w : StockJet, ‖z‖ ≤ B → 2 * μ ≤ z 0 → ‖w - z‖ < τ →
      μ < w 0 ∧ |stockOneMap h p w - stockOneMap h p z| < ε ∧
        |stockTwoMap h p w - stockTwoMap h p z| < ε ∧ |z 0 / w 0 - 1| < ε := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨r, hr, hb⟩ := compact_vector_perturbation
    (fun q : (S × StockBall B) × StockJet => clippedStockMap h μ q.1.1.val q.1.2.val q.2)
    (clippedStockMap_continuous hsmall hμ hX hη) hε
  refine ⟨min r μ, lt_min hr hμ, ?_⟩
  intro p hp z w hz hz0 he
  have he0 : |w 0 - z 0| < μ := by
    have hh := norm_le_pi_norm (w - z) 0
    rw [Real.norm_eq_abs] at hh
    exact hh.trans_lt (he.trans_le (min_le_right _ _))
  have hw0 : μ < w 0 := by have hh := (abs_lt.mp he0).1; linarith
  have hzμ : μ ≤ z 0 := by linarith
  have hzmem : z ∈ Metric.closedBall (0 : StockJet) B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hh := hb (⟨p, hp⟩, ⟨z, hzmem⟩) (w - z) (he.trans_le (min_le_left _ _))
  have heq : z + (w - z) = w := by abel
  have hzero : z + (0 : StockJet) = z := add_zero _
  have hcoord (i : Fin 3) := (norm_le_pi_norm
    (clippedStockMap h μ p z (w - z) - clippedStockMap h μ p z 0) i).trans_lt hh
  refine ⟨hw0, ?_, ?_, ?_⟩
  · simpa only [clippedStockMap, heq, hzero, max_eq_right hw0.le, max_eq_right hzμ,
      Pi.sub_apply, Matrix.cons_val_zero, Real.norm_eq_abs, stockOneMap] using hcoord 0
  · simpa only [clippedStockMap, heq, hzero, max_eq_right hw0.le, max_eq_right hzμ,
      Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Real.norm_eq_abs, stockTwoMap] using
          hcoord 1
  · have hzn : z 0 ≠ 0 := (hμ.trans_le hzμ).ne'
    simpa only [clippedStockMap, heq, hzero, max_eq_right hw0.le, max_eq_right hzμ,
      Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Real.norm_eq_abs, div_self hzn] using
          hcoord 2

/-! ## The five history rows follow from actual first parameter jets -/

open StressActivation

/-- Field jet: an abbreviation for `Fin 4 → ℝ`. -/
abbrev FieldJet := Fin 4 → ℝ

/-- Field jet, given by `![P.f p, P.U p, parameterPartial P.f p, parameterPartial P.U p]`. -/
noncomputable def fieldJet {D : RadialDomain} (P : Profiles D) (p : Point) : FieldJet :=
  ![P.f p, P.U p, parameterPartial P.f p, parameterPartial P.U p]

/-- Density jet as an element of `Fin 10 → ℝ`. -/
noncomputable def densityJet (X : ℝ) (z : FieldJet) : Fin 10 → ℝ :=
  ![z 1, z 3, 2 * X * z 0, 2 * X * z 2,
    z 1 * (2 * X * z 0), z 3 * (2 * X * z 0) + z 1 * (2 * X * z 2),
    z 1 ^ 2 - X * z 0 ^ 2, 2 * z 1 * z 3 - 2 * X * z 0 * z 2,
    z 0 ^ 2, 2 * z 0 * z 2]

theorem densityJet_continuous : Continuous (fun p : ℝ × FieldJet => densityJet p.1 p.2) := by
  unfold densityJet
  repeat' apply Continuous.matrixVecCons
  all_goals fun_prop

/-- Value index, given by `HistoryRow.rec (motive := fun _ => Fin 10) 0 2 4 6 8 r`. -/
noncomputable def valueIndex (r : HistoryRow) : Fin 10 :=
  HistoryRow.rec (motive := fun _ => Fin 10) 0 2 4 6 8 r

/-- Derivative index, given by `HistoryRow.rec (motive := fun _ => Fin 10) 1 3 5 7 9 r`. -/
noncomputable def derivativeIndex (r : HistoryRow) : Fin 10 :=
  HistoryRow.rec (motive := fun _ => Fin 10) 1 3 5 7 9 r

theorem densityJet_value {D : RadialDomain} (P : Profiles D) (r : HistoryRow) (p : Point) :
    densityJet p.1 (fieldJet P p) (valueIndex r) = profileDensity P r p := by
  cases r <;> rfl

theorem densityJet_derivative {D : RadialDomain} (P : Profiles D) (r : HistoryRow)
    {p : Point} (hp : p ∈ D.carrier) :
    densityJet p.1 (fieldJet P p) (derivativeIndex r) = parameterPartial (profileDensity P r) p :=
        by
  cases r with
  | mass => rfl
  | angular => exact (P.parameterPartial_H hp).symm
  | transport =>
    change _ = parameterPartial P.transportDensity p
    rw [P.parameterPartial_transportDensity hp, P.parameterPartial_H hp]
    rfl
  | energy => exact (P.parameterPartial_energyDensity hp).symm
  | pressure => exact (ReferenceBounds.parameterPartial_square P hp).symm

theorem profileHistory_parameter_formula {D : RadialDomain} (P : Profiles D) (r : HistoryRow)
    {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial (profileHistory P r) p = deriv (profileInitial P r) p.2 +
      primitive (parameterPartial (profileDensity P r)) p := by
  cases r with
  | mass =>
    simp only [profileHistory, profileInitial, deriv_const, zero_add]
    exact parameterPartial_primitive D P.U_smooth hp
  | angular =>
    simp only [profileHistory, profileInitial, deriv_const, zero_add]
    exact parameterPartial_primitive D P.H_smooth hp
  | transport =>
    simp only [profileHistory, profileInitial, deriv_const, zero_add]
    exact parameterPartial_primitive D P.transportDensity_smooth hp
  | energy =>
    simp only [profileHistory, profileInitial, deriv_const, zero_add]
    exact parameterPartial_primitive D P.energyDensity_smooth hp
  | pressure =>
    change parameterPartial P.pressure p = _
    rw [P.parameterPartial_pressure hp, parameterPartial_primitive D (P.f_smooth.pow 2) hp]
    rfl

theorem profileHistory_difference {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    (h0 : P.pressure0 = Q.pressure0) (r : HistoryRow) {p : Point}
    (hp : p ∈ D.carrier) (hq : p ∈ E.carrier) :
    profileHistory P r p - profileHistory Q r p =
      ∫ t in (0 : ℝ)..p.1, profileDensity P r (t, p.2) - profileDensity Q r (t, p.2) := by
  have hi : profileInitial P r = profileInitial Q r := by cases r <;> first | rfl | exact h0
  rw [profileHistory_eq_initial_add_primitive, profileHistory_eq_initial_add_primitive, hi]
  rw [add_sub_add_left_eq_sub]
  exact (intervalIntegral.integral_sub
    (radial_slice_intervalIntegrable D (profileDensity_smooth P r) hp)
    (radial_slice_intervalIntegrable E (profileDensity_smooth Q r) hq)).symm

theorem profileHistory_parameter_difference {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    (h0 : P.pressure0 = Q.pressure0) (r : HistoryRow) {p : Point}
    (hp : p ∈ D.carrier) (hq : p ∈ E.carrier) :
    parameterPartial (profileHistory P r) p - parameterPartial (profileHistory Q r) p =
      ∫ t in (0 : ℝ)..p.1, parameterPartial (profileDensity P r) (t, p.2) -
        parameterPartial (profileDensity Q r) (t, p.2) := by
  have hi : profileInitial P r = profileInitial Q r := by cases r <;> first | rfl | exact h0
  rw [profileHistory_parameter_formula P r hp, profileHistory_parameter_formula Q r hq, hi]
  rw [add_sub_add_left_eq_sub]
  exact (intervalIntegral.integral_sub
    (radial_slice_intervalIntegrable D (parameterPartial_smooth D (profileDensity_smooth P r)) hp)
    (radial_slice_intervalIntegrable E (parameterPartial_smooth E (profileDensity_smooth Q r))
        hq)).symm

/-- Field ball: an abbreviation for `Metric.closedBall (0 : FieldJet) B instance (B : ℝ) :
CompactSpace (FieldBall B) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)`. -/
abbrev FieldBall (B : ℝ) := Metric.closedBall (0 : FieldJet) B

instance (B : ℝ) : CompactSpace (FieldBall B) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

theorem uniform_density_transfer (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ > 0, ∀ X ∈ Icc (0 : ℝ) 110, ∀ z w : FieldJet,
      ‖z‖ ≤ B → ‖w - z‖ < τ → ‖densityJet X w - densityJet X z‖ < ε := by
  let G : ((Icc (0 : ℝ) 110) × FieldBall B) × FieldJet → Fin 10 → ℝ :=
    fun q => densityJet q.1.1.val (q.1.2.val + q.2)
  have hc : Continuous G := by
    have hm : Continuous (fun q : ((Icc (0 : ℝ) 110) × FieldBall B) × FieldJet =>
        (q.1.1.val, q.1.2.val + q.2)) := by fun_prop
    exact densityJet_continuous.comp hm
  obtain ⟨τ, hτ, hb⟩ := compact_vector_perturbation G hc hε
  refine ⟨τ, hτ, ?_⟩
  intro X hX z w hz he
  have hz' : z ∈ Metric.closedBall (0 : FieldJet) B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hh := hb (⟨X, hX⟩, ⟨z, hz'⟩) (w - z) he
  have heq : z + (w - z) = w := by abel
  simpa only [G, heq, add_zero] using hh

theorem short_integral_bound {f : ℝ → ℝ} {X ε : ℝ}
    (hX : X ∈ Icc (0 : ℝ) 110) (hε : 0 < ε)
    (hf : ∀ t ∈ Icc (0 : ℝ) X, |f t| ≤ ε / 111) :
    |∫ t in (0 : ℝ)..X, f t| < ε := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := X) (C := ε / 111) (f := f) (fun t ht => by
      rw [Real.norm_eq_abs]
      have ht' : t ∈ Ioc (0 : ℝ) X := (uIoc_of_le hX.1 ▸ ht)
      exact hf t ⟨ht'.1.le, ht'.2⟩)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hX.1] at hb
  have hm := mul_le_mul_of_nonneg_left hX.2 (show 0 ≤ ε / 111 by positivity)
  have hn : ε / 111 * 110 < ε := by linarith
  exact (hb.trans hm).trans_lt hn

/-- Uniform first-jet closeness of actual fields gives uniform closeness of
all five actual history rows and their first parameter derivatives. -/
theorem field_to_stockJet_transfer (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ > 0, ∀ {D E : RadialDomain} (P : Profiles D) (Q : Profiles E),
      P.pressure0 = Q.pressure0 → ∀ p : Point, p ∈ D.carrier → p ∈ E.carrier →
      p.1 ∈ Icc (0 : ℝ) 110 →
      (∀ t ∈ Icc (0 : ℝ) p.1, ‖fieldJet Q (t, p.2)‖ ≤ B) →
      (∀ t ∈ Icc (0 : ℝ) p.1, ‖fieldJet P (t, p.2) - fieldJet Q (t, p.2)‖ < τ) →
      ‖stockJet P p - stockJet Q p‖ < ε := by
  obtain ⟨r, hr, hmap⟩ := uniform_density_transfer B (ε := ε / 111) (by positivity)
  refine ⟨min ε r, lt_min hε hr, ?_⟩
  intro D E P Q h0 p hp hq hX hB he
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) p.1) :
      ‖densityJet t (fieldJet P (t, p.2)) - densityJet t (fieldJet Q (t, p.2))‖ < ε / 111 :=
    hmap t ⟨ht.1, ht.2.trans hX.2⟩ _ _ (hB t ht) ((he t ht).trans_le (min_le_right _ _))
  have hhist (r : HistoryRow) :
      |profileHistory P r p - profileHistory Q r p| < ε ∧
      |parameterPartial (profileHistory P r) p - parameterPartial (profileHistory Q r) p| < ε := by
    constructor
    · rw [profileHistory_difference P Q h0 r hp hq]
      apply short_integral_bound hX hε
      intro t ht
      have hh := (norm_le_pi_norm
        (densityJet t (fieldJet P (t, p.2)) - densityJet t (fieldJet Q (t, p.2))) (valueIndex
            r)).trans_lt (hd t ht)
      simpa only [Real.norm_eq_abs, Pi.sub_apply, densityJet_value P r (t, p.2),
        densityJet_value Q r (t, p.2)] using hh.le
    · rw [profileHistory_parameter_difference P Q h0 r hp hq]
      apply short_integral_bound hX hε
      intro t ht
      have htp := D.segment_mem hp (uIcc_of_le hX.1 ▸ ht)
      have htq := E.segment_mem hq (uIcc_of_le hX.1 ▸ ht)
      have hh := (norm_le_pi_norm
        (densityJet t (fieldJet P (t, p.2)) - densityJet t (fieldJet Q (t, p.2))) (derivativeIndex
            r)).trans_lt (hd t ht)
      simpa only [Real.norm_eq_abs, Pi.sub_apply, densityJet_derivative P r htp,
        densityJet_derivative Q r htq] using hh.le
  have hfield : ‖fieldJet P p - fieldJet Q p‖ < ε := by
    exact (he p.1 ⟨hX.1, le_rfl⟩).trans_le (min_le_left _ _)
  apply (pi_norm_lt_iff hε).2
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact (norm_le_pi_norm (fieldJet P p - fieldJet Q p) 0).trans_lt hfield
  · exact (norm_le_pi_norm (fieldJet P p - fieldJet Q p) 1).trans_lt hfield
  · exact (hhist .mass).1
  · exact (hhist .mass).2
  · exact (hhist .angular).1
  · exact (hhist .angular).2
  · exact (hhist .transport).1
  · exact (hhist .transport).2
  · exact (hhist .energy).1
  · exact (hhist .energy).2
  · exact (hhist .pressure).1
  · exact (hhist .pressure).2

theorem uniform_density_bound (B : ℝ) :
    ∃ K ≥ 0, ∀ X ∈ Icc (0 : ℝ) 110, ∀ z : FieldJet, ‖z‖ ≤ B → ‖densityJet X z‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : FieldJet)
      B)).exists_bound_of_continuousOn
    densityJet_continuous.continuousOn
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro X hX z hz
  exact (hK (X, z) ⟨hX, by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz⟩).trans (le_max_left _ _)

theorem integral_bounded_length {f : ℝ → ℝ} {X K : ℝ} (hX : X ∈ Icc (0 : ℝ) 110)
    (hK : 0 ≤ K) (hf : ∀ t ∈ Icc (0 : ℝ) X, |f t| ≤ K) :
    |∫ t in (0 : ℝ)..X, f t| ≤ 110 * K := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := X) (C := K) (f := f) (fun t ht => by
      rw [Real.norm_eq_abs]
      have ht' : t ∈ Ioc (0 : ℝ) X := (uIoc_of_le hX.1 ▸ ht)
      exact hf t ⟨ht'.1.le, ht'.2⟩)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hX.1] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left hX.2 hK).trans_eq (mul_comm K 110))

/-- A bounded actual first field jet gives a uniform bound for every stock
input, including both pressure entries. This bound precedes the small ramps. -/
theorem stockJet_uniform_bound {B B0 : ℝ} (hB : 0 ≤ B) (hB0 : 0 ≤ B0) :
    ∃ K > 0, ∀ {D : RadialDomain} (P : Profiles D) (p : Point), p ∈ D.carrier →
      p.1 ∈ Icc (0 : ℝ) 110 → |P.pressure0 p.2| ≤ B0 → |deriv P.pressure0 p.2| ≤ B0 →
      (∀ t ∈ Icc (0 : ℝ) p.1, ‖fieldJet P (t, p.2)‖ ≤ B) → ‖stockJet P p‖ ≤ K := by
  obtain ⟨K0, hK0, hb⟩ := uniform_density_bound B
  let K := 1 + B + B0 + 110 * K0
  have hK : 0 < K := by dsimp [K]; positivity
  have hBK : B ≤ K := by dsimp [K]; nlinarith
  have hHK : B0 + 110 * K0 ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro D P p hp hX hp0 hp0' hfield
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) p.1) := hb t ⟨ht.1, ht.2.trans hX.2⟩ _ (hfield t ht)
  have hhist (r : HistoryRow) :
      |profileHistory P r p| ≤ K ∧ |parameterPartial (profileHistory P r) p| ≤ K := by
    have hini : |profileInitial P r p.2| ≤ B0 := by
      cases r <;> simpa only [profileInitial, abs_zero] using (by assumption)
    have hini' : |deriv (profileInitial P r) p.2| ≤ B0 := by
      cases r <;> simpa only [profileInitial, deriv_const, abs_zero] using (by assumption)
    have hv : |primitive (profileDensity P r) p| ≤ 110 * K0 := by
      apply integral_bounded_length hX hK0
      intro t ht
      have hh := (norm_le_pi_norm (densityJet t (fieldJet P (t, p.2))) (valueIndex r)).trans (hd t
          ht)
      simpa only [Real.norm_eq_abs, densityJet_value P r (t, p.2)] using hh
    have he : |primitive (parameterPartial (profileDensity P r)) p| ≤ 110 * K0 := by
      apply integral_bounded_length hX hK0
      intro t ht
      have htp := D.segment_mem hp (uIcc_of_le hX.1 ▸ ht)
      have hh := (norm_le_pi_norm (densityJet t (fieldJet P (t, p.2))) (derivativeIndex r)).trans
          (hd t ht)
      simpa only [Real.norm_eq_abs, densityJet_derivative P r htp] using hh
    constructor
    · rw [profileHistory_eq_initial_add_primitive]
      exact ((abs_add_le _ _).trans (add_le_add hini hv)).trans hHK
    · rw [profileHistory_parameter_formula P r hp]
      exact ((abs_add_le _ _).trans (add_le_add hini' he)).trans hHK
  have hpfield : ‖fieldJet P p‖ ≤ B := hfield p.1 ⟨hX.1, le_rfl⟩
  apply (pi_norm_le_iff_of_nonneg hK.le).2
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact (norm_le_pi_norm (fieldJet P p) 0).trans (hpfield.trans hBK)
  · exact (norm_le_pi_norm (fieldJet P p) 1).trans (hpfield.trans hBK)
  · exact (hhist .mass).1
  · exact (hhist .mass).2
  · exact (hhist .angular).1
  · exact (hhist .angular).2
  · exact (hhist .transport).1
  · exact (hhist .transport).2
  · exact (hhist .energy).1
  · exact (hhist .energy).2
  · exact (hhist .pressure).1
  · exact (hhist .pressure).2

theorem uniform_stock_bound {h j μ B : ℝ} (hsmall : NaturalAxisData.SmallParameters h j)
    (hμ : 0 < μ) {S : Set Point} (hS : IsCompact S)
    (hX : ∀ p ∈ S, 0 < p.1) (hη : ∀ p ∈ S, p.2 ∈ Icc (-1 : ℝ) 1) :
    ∃ M > 0, ∀ p ∈ S, ∀ z : StockJet, ‖z‖ ≤ B → μ ≤ z 0 →
      |stockOneMap h p z| ≤ M ∧ |stockTwoMap h p z| ≤ M := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hc : Continuous (fun q : S × StockBall B => clippedStockMap h μ q.1.val q.2.val 0) := by
    simpa only [Function.comp_def, id_eq] using (clippedStockMap_continuous hsmall hμ hX hη).comp
      (continuous_id.prodMk (continuous_const (y := (0 : StockJet))))
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨1 + |M|, by positivity, ?_⟩
  intro p hp z hz hf
  have hz' : z ∈ Metric.closedBall (0 : StockJet) B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hh := hM (⟨p, hp⟩, ⟨z, hz'⟩) (mem_univ _)
  have hh0 := (norm_le_pi_norm (clippedStockMap h μ p z 0) 0).trans hh
  have hh1 := (norm_le_pi_norm (clippedStockMap h μ p z 0) 1).trans hh
  constructor
  · have he : |stockOneMap h p z| ≤ M := by
      simpa only [clippedStockMap, add_zero, max_eq_right hf, Matrix.cons_val_zero,
        stockOneMap, Real.norm_eq_abs] using hh0
    linarith [le_abs_self M]
  · have he : |stockTwoMap h p z| ≤ M := by
      simpa only [clippedStockMap, add_zero, max_eq_right hf, Matrix.cons_val_one,
          Matrix.cons_val_zero,
        stockTwoMap, Real.norm_eq_abs] using hh1
    linarith [le_abs_self M]

/-! ## Uniform comparison constants from the concrete reference -/

theorem reference_first_lower {h j σ Λ C δ : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    (hΛ : 0 < Λ) (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)
    (hb : ReferenceBounds.ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0)
    {p : Point} (hp : p ∈ ReferenceBounds.holdRegion) (hX : 0 < p.1) :
    (6 / 5 : ℝ) * p.1 ≤ ReferenceBounds.p1 (ReferenceBounds.referenceProfiles E.profile hΛ hδ hδT
        hP0) h p := by
  let P := ReferenceBounds.referenceProfiles E.profile hΛ hδ hδT hP0
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  have hL := NaturalAxisData.L_pos hsmall hp.2
  have hL1 := NaturalEntrance.L_le_one hsmall p.2
  have hsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) p.1) :
      (12 / 5 : ℝ) ≤ ReferenceBounds.sourceQ P h (t, p.2) := by
    have hm := hb.source_lower (t, p.2) ⟨⟨ht.1, ht.2.trans hp.1.2⟩, hp.2⟩
    have hn : 0 ≤ (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL.le) hΛ.le)
        (NaturalAxisData.chi_bounds h j hσ p.2).1
    change _ < ReferenceBounds.sourceQ P h (t, p.2) at hm
    linarith
  have hlow := ReferenceBounds.p1_lower_from_source P
    (ReferenceBounds.reference_mem E.profile hΛ hp.1.1 hp.2) hX h hL
    (by norm_num : (0 : ℝ) ≤ 12 / 5)
    (fun t ht => N.refF_pos δ (ReferenceBounds.reference_mem E.profile hΛ (p := (t, p.2)) ht.1
        hp.2) ht.1)
    (ReferenceBounds.reference_antitone E hΛ hδ hδT hP0 hX.le hp.2) hsource
  apply le_trans _ hlow
  apply (le_div_iff₀ (mul_pos (by norm_num) hL)).mpr
  nlinarith

/-- Exp jet, given by `(Real.exp p.1, Real.exp p.1 * p.2)`. -/
noncomputable def expJet (p : ℝ × ℝ) : ℝ × ℝ := (Real.exp p.1, Real.exp p.1 * p.2)

theorem expJet_continuous : Continuous expJet := by unfold expJet; fun_prop

theorem expJet_uniform (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ > 0, ∀ z w : ℝ × ℝ, ‖z‖ ≤ B → ‖w - z‖ < τ → ‖expJet w - expJet z‖ < ε := by
  let : CompactSpace (Metric.closedBall (0 : ℝ × ℝ) B) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hc : Continuous (fun q : Metric.closedBall (0 : ℝ × ℝ) B × (ℝ × ℝ) => expJet (q.1.val +
      q.2)) :=
    expJet_continuous.comp ((continuous_subtype_val.comp continuous_fst).add continuous_snd)
  obtain ⟨τ, hτ, hb⟩ := compact_vector_perturbation _ hc hε
  refine ⟨τ, hτ, ?_⟩
  intro z w hz he
  have hz' : z ∈ Metric.closedBall (0 : ℝ × ℝ) B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hh := hb ⟨z, hz'⟩ (w - z) he
  simpa only [add_sub_cancel, add_zero] using hh

theorem comparison_tolerances {M : ℝ} (hM : 0 ≤ M) :
    ∃ ε κstar : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < κstar ∧ κstar < 1 ∧
      ε * projectionConstant M ≤ 1 / 8 ∧
      κstar * speedConstant M ≤ 1 ∧ κstar * M ≤ 4 / 5 := by
  let ε := min 1 (1 / (8 * projectionConstant M))
  let κstar := 1 / (2 * (1 + speedConstant M + M))
  have hp := projectionConstant_pos hM
  have hv := speedConstant_nonneg hM
  have hkden : 0 < 2 * (1 + speedConstant M + M) := by linarith
  have hk : 0 < κstar := one_div_pos.mpr hkden
  have hkeq : κstar * (2 * (1 + speedConstant M + M)) = 1 := by
    dsimp [κstar]
    exact one_div_mul_cancel hkden.ne'
  refine ⟨ε, κstar, lt_min zero_lt_one (one_div_pos.mpr (mul_pos (by norm_num) hp)),
    min_le_left _ _, hk, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hk.le hv, mul_nonneg hk.le hM]
  · have hh := (le_div_iff₀ (mul_pos (by
      norm_num : (0 : ℝ) < 8) hp)).mp (min_le_right 1 (1 / (8 * projectionConstant M)))
    dsimp [ε]
    nlinarith
  · nlinarith [mul_nonneg hk.le hM]
  · nlinarith [mul_nonneg hk.le hv]

theorem reference_fieldJet_bound {D : RadialDomain} (P : Profiles D)
    {h j σ Λ C B K : ℝ} (hsmall : NaturalAxisData.SmallParameters h j)
    (hΛ : 1 ≤ Λ) (hC : 1 ≤ C) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hj : ReferenceJetBounds.JetBounds h j σ Λ C B K P.f P.U)
    {p : Point} (hp : p ∈ ReferenceBounds.holdRegion) :
    ‖fieldJet P p‖ ≤ K + B + 6 := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hf : K / C ≤ K := (div_le_iff₀ hC0).mpr (by nlinarith)
  have hu := hj.axial_value p hp
  have huη := hj.axial_parameter p hp
  rw [abs_mul, abs_of_pos hΛ0] at hu huη
  have hdu : |P.U p - NaturalAxisData.U j p.2| ≤ B := by
    nlinarith [abs_nonneg (P.U p - NaturalAxisData.U j p.2)]
  have hduη : |parameterPartial P.U p - 4| ≤ B := by
    nlinarith [abs_nonneg (parameterPartial P.U p - 4)]
  have hη : |p.2| ≤ 1 := abs_le.mpr hp.2
  have hstar : |NaturalAxisData.U j p.2| ≤ 5 := by
    calc
      _ ≤ |4 * p.2| + |j| := abs_add_le _ _
      _ = 4 * |p.2| + j := by rw [abs_mul, abs_of_pos hsmall.j_pos]; norm_num
      _ ≤ 5 := by linarith [hsmall.j_le]
  have huabs : |P.U p| ≤ B + 5 := by
    have hh := abs_add_le (P.U p - NaturalAxisData.U j p.2) (NaturalAxisData.U j p.2)
    rw [sub_add_cancel] at hh
    linarith
  have hueabs : |parameterPartial P.U p| ≤ B + 4 := by
    have hh := abs_add_le (parameterPartial P.U p - 4) (4 : ℝ)
    rw [sub_add_cancel] at hh
    norm_num at hh
    linarith
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ K + B + 6)).2
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact (hj.angular_value p hp).trans (hf.trans (by linarith))
  · exact huabs.trans (by linarith)
  · exact (hj.angular_parameter p hp).trans (hf.trans (by linarith))
  · exact hueabs.trans (by linarith)

theorem pressure_initial_bound {P0 : ℝ → ℝ} (hP0 : ContDiff ℝ ∞ P0) :
    ∃ B0 > 0, ∀ η ∈ Icc (-1 : ℝ) 1, |P0 η| ≤ B0 ∧ |deriv P0 η| ≤ B0 := by
  have hc : Continuous (fun η => (P0 η, deriv P0 η)) :=
    hP0.continuous.prodMk (hP0.continuous_deriv (by simp))
  obtain ⟨B0, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨1 + |B0|, by positivity, ?_⟩
  intro η hη
  have hh := hb η hη
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff] at hh
  exact ⟨hh.1.trans (by linarith [le_abs_self B0]), hh.2.trans (by linarith [le_abs_self B0])⟩

section ReferenceEndpoint

open ReferencePath
variable (N : ReferencePath.Input)

theorem endpoint_field_continuous :
    ContinuousOn (fun η => N.f (N.endpoint, η)) (Icc (-1 : ℝ) 1) := by
  intro η hη
  exact ((N.f_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds
    (ReferenceJetBounds.endpoint_mem N hη))).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt

/-- Endpoint log jet, given by `(Real.log (N.f (N.endpoint, η)), parameterPartial N.f
(N.endpoint, η) / N.f (N.endpoint, η))`. -/
noncomputable def endpointLogJet (η : ℝ) : ℝ × ℝ :=
  (Real.log (N.f (N.endpoint, η)), parameterPartial N.f (N.endpoint, η) / N.f (N.endpoint, η))

theorem endpointLogJet_bound : ∃ B0 ≥ 0, ∀ η ∈ Icc (-1 : ℝ) 1, ‖endpointLogJet N η‖ ≤ B0 := by
  have hpart : ContDiffOn ℝ ∞ (parameterPartial N.f) (NaturalProfile.domain N.scale) :=
    (N.f_smooth.fderiv_of_isOpen (NaturalProfile.domain_isOpen N.scale) (by
        simp)).clm_apply contDiffOn_const
  have hc : ContinuousOn (endpointLogJet N) (Icc (-1 : ℝ) 1) := by
    intro η hη
    have hm := ReferenceJetBounds.endpoint_mem N hη
    have hf := (N.f_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds
        hm)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)
    have hg := (hpart.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds
        hm)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)
    have hn := (N.endpoint_f_pos (original_interval_interior hη)).ne'
    exact ((hf.log hn).prodMk (hg.div hf hn)).continuousWithinAt
  obtain ⟨B0, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨max B0 0, le_max_right _ _, fun η hη => (hb η hη).trans (le_max_left _ _)⟩

theorem reference_positive_uniform :
    ∃ μ r : ℝ, 0 < μ ∧ 0 < r ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      ∀ p : Point, N.endpoint ≤ p.1 → p.2 ∈ Icc (-1 : ℝ) 1 → 2 * μ ≤ N.refF δ p := by
  obtain ⟨α, hα, hmin⟩ := UniformCone.positive_uniform_margin isCompact_Icc
    (endpoint_field_continuous N) (fun η hη => N.endpoint_f_pos (original_interval_interior hη))
  obtain ⟨r, hr, hb⟩ := N.ref_relative_error_jet_close isCompact_Icc original_interval_interior 0
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨α / 4, r, by positivity, hr, ?_⟩
  intro δ hδ hδr p hx hη
  have hh := hb δ hδ hδr p.1 hx p.2 hη
  rw [iteratedDeriv_zero] at hh
  have hp := N.endpoint_f_pos (original_interval_interior hη)
  have hl : (1 / 2 : ℝ) < N.refF δ p / N.f (N.endpoint, p.2) := by
    have hs := (abs_lt.mp hh).1
    change _ < N.refF δ p / N.f (N.endpoint, p.2) - 1 at hs
    linarith
  have hf := (lt_div_iff₀ hp).mp hl
  have hm := hmin p.2 hη
  linarith

theorem reference_endpoint_control {εU εF εL : ℝ} (hU : 0 < εU) (hF : 0 < εF) (hL : 0 < εL) :
    ∃ r > 0, ∀ δ : ℝ, 0 < δ → δ < r →
      ReferenceJetBounds.TransitionControl N δ εU εF ∧
      ∀ p : Point, N.endpoint ≤ p.1 → p.2 ∈ Icc (-1 : ℝ) 1 →
        |parameterPartial (N.refF δ) p / N.refF δ p -
          parameterPartial N.f (N.endpoint, p.2) / N.f (N.endpoint, p.2)| < εL := by
  obtain ⟨r0, hr0, hc⟩ := ReferenceJetBounds.exists_transition_control N hU hF
  obtain ⟨r1, hr1, hl⟩ := N.ref_log_error_jet_close isCompact_Icc original_interval_interior 1 hL
  refine ⟨min r0 r1, lt_min hr0 hr1, ?_⟩
  intro δ hδ hr
  have ht := hc δ hδ (hr.trans_le (min_le_left _ _))
  refine ⟨ht, ?_⟩
  intro p hx hη
  have hp := ReferenceJetBounds.reference_mem N (N.endpoint_pos.le.trans hx) hη
  have hpn := ReferenceJetBounds.endpoint_mem N hη
  have hh := hl δ hδ (hr.trans_le (min_le_right _ _)) p.1 hx p.2 hη
  rw [ReferenceJetBounds.first_log_difference
    ((N.refF_smooth hδ ht.length_bound).contDiffAt (N.radialDomain.isOpen.mem_nhds hp))
    (N.f_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds hpn))
    (N.refF_pos δ hp (N.endpoint_pos.le.trans hx)).ne'
    (N.endpoint_f_pos (original_interval_interior hη)).ne'] at hh
  exact hh

end ReferenceEndpoint

/-! ## Ordered preparation and transfer of normalized source jets -/

/-- The scale and pressure normalization are chosen before any small
activation parameter.  Both estimates concern the same actual REF fields. -/
theorem ordered_reference_preparation {h j σ ν : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) (hν : 0 < ν)
    (hcut : ∀ η ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z h j P0 η| ≤ ν →
      99 / 100 < NaturalAxisData.chi h j σ η) :
    ∃ B M : ℝ, 1 < B ∧ 1 ≤ M ∧
      ∀ Λ : ℝ, ∀ hΛ : 0 < Λ, M ≤ Λ →
        (∀ {D : RadialDomain} (P : Profiles D) (p : Point),
          p.2 ∈ Icc (-1 : ℝ) 1 → ReferenceBounds.logSlope P p = 3 / 5 →
          |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B + 2 →
          |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B + 2 →
          |Λ * (average (parameterPartial P.U) p - 4)| ≤ B + 2 →
          |parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2| ≤ B + 2 →
          (5 / 4 : ℝ) < ReferenceBounds.sourceQ P h p) ∧
        ∃ C0 K : ℝ, 1 ≤ C0 ∧ 0 < K ∧
          ∀ C : ℝ, C0 ≤ C → ∃ E : NaturalEntrance.EntranceProfile d Λ C,
            ∃ r > 0, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < r →
              ∃ hδT : 2 * δ < ReferencePath.rampLimit,
                ReferenceBounds.ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0 ∧
                ReferenceJetBounds.JetBounds h j σ Λ C B K
                  ((ReferencePath.Input.ofNatural hΛ E.profile.family).refF δ)
                  ((ReferencePath.Input.ofNatural hΛ E.profile.family).refU δ) := by
  obtain ⟨B, Mj, Kerr, hB, hMj, hKerr, hjets⟩ := ReferenceJetBounds.ordered_reference_bounds d hσ
  obtain ⟨Mh, hMh, hhold⟩ := actual_hold_source_threshold hsmall hσ (B := B + 2) (by linarith)
  obtain ⟨Mr, hMr, href⟩ := ReferenceBounds.exists_reference_bounds d hsmall hσ hP0 hν hcut
  let M := max 1 (max Mj (max Mh Mr))
  refine ⟨B, M, hB, le_max_left _ _, ?_⟩
  intro Λ hΛ hM
  have hMjΛ : Mj ≤ Λ := (le_trans (le_max_left _ _) (le_max_right 1 _)).trans hM
  have hMhΛ : Mh ≤ Λ := (le_trans (le_max_left Mh Mr)
    (le_trans (le_max_right Mj _) (le_max_right 1 _))).trans hM
  have hMrΛ : Mr ≤ Λ := (le_trans (le_max_right Mh Mr)
    (le_trans (le_max_right Mj _) (le_max_right 1 _))).trans hM
  refine ⟨hhold Λ hMhΛ, ?_⟩
  obtain ⟨K, hK, hj⟩ := hjets Λ hΛ hMjΛ
  obtain ⟨Cr, hCr, hr⟩ := href Λ hΛ hMrΛ
  let C0 := max 1 (max Cr (d.normalizationThreshold Λ))
  refine ⟨C0, K, le_max_left _ _, hK, ?_⟩
  intro C hC
  have hCrC : Cr ≤ C := (le_trans (le_max_left _ _) (le_max_right 1 _)).trans hC
  have hnC : d.normalizationThreshold Λ ≤ C :=
    (le_trans (le_max_right _ _) (le_max_right 1 _)).trans hC
  obtain ⟨E, r0, hr0, he⟩ := hr C hCrC
  obtain ⟨r1, hr1, hj1⟩ := hj C hnC E.profile
  refine ⟨E, min r0 r1, lt_min hr0 hr1, ?_⟩
  intro δ hδ hdr
  obtain ⟨hδT, hb⟩ := he δ hδ (hdr.trans_le (min_le_left _ _))
  exact ⟨hδT, hb, (hj1 δ hδ (hdr.trans_le (min_le_right _ _))).2.1⟩

/-- First parameter derivatives are sufficient for all source histories. -/
theorem nearby_axial_bounds {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    {h j σ Λ C B K : ℝ} (hΛ : 0 < Λ)
    (hj : ReferenceJetBounds.JetBounds h j σ Λ C B K Q.f Q.U)
    (hu : ∀ p ∈ ReferenceBounds.holdRegion, |P.U p - Q.U p| ≤ 1 / Λ)
    (huη : ∀ p ∈ ReferenceBounds.holdRegion,
      |parameterPartial P.U p - parameterPartial Q.U p| ≤ 1 / Λ) :
    (∀ p ∈ ReferenceBounds.holdRegion, |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B + 1) ∧
    (∀ p ∈ ReferenceBounds.holdRegion, |Λ * (parameterPartial P.U p - 4)| ≤ B + 1) := by
  have step_bound {x y z : ℝ} (he : |x - y| ≤ 1 / Λ) (hb : |Λ * (y - z)| ≤ B) :
      |Λ * (x - z)| ≤ B + 1 := by
    have he1 : Λ * |x - y| ≤ 1 := by
      have ht := mul_le_mul_of_nonneg_left he hΛ.le
      rwa [mul_one_div_cancel hΛ.ne'] at ht
    calc
      _ = |Λ * (x - y) + Λ * (y - z)| := by congr 1; ring
      _ ≤ |Λ * (x - y)| + |Λ * (y - z)| := abs_add_le _ _
      _ ≤ 1 + B := by rw [abs_mul, abs_of_pos hΛ]; linarith
      _ = _ := by ring
  exact ⟨fun p hp => step_bound (hu p hp) (hj.axial_value p hp),
    fun p hp => step_bound (huη p hp) (hj.axial_parameter p hp)⟩

theorem nearby_source_jets {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    {h j σ Λ C B K : ℝ} (hΛ : 0 < Λ)
    (hj : ReferenceJetBounds.JetBounds h j σ Λ C B K Q.f Q.U)
    (hu : ∀ p ∈ ReferenceBounds.holdRegion, |P.U p - Q.U p| ≤ 1 / Λ)
    (huη : ∀ p ∈ ReferenceBounds.holdRegion,
      |parameterPartial P.U p - parameterPartial Q.U p| ≤ 1 / Λ)
    (hfη : ∀ p ∈ ReferenceBounds.holdRegion,
      |parameterPartial P.f p / P.f p - parameterPartial Q.f p / Q.f p| ≤ 1)
    {p : Point} (hp : p ∈ ReferenceBounds.holdRegion) (hpD : p ∈ D.carrier) :
    |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B + 2 ∧
    |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B + 2 ∧
    |Λ * (average (parameterPartial P.U) p - 4)| ≤ B + 2 ∧
    |parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2| ≤ B + 2 := by
  obtain ⟨hU, hUη⟩ := nearby_axial_bounds P Q hΛ hj hu huη
  have hh := ReferenceBounds.normalized_history_bounds P hU hUη hp hpD
  refine ⟨(hU p hp).trans (by linarith), hh.1.trans (by linarith), hh.2.trans (by linarith), ?_⟩
  calc
    _ ≤ |parameterPartial P.f p / P.f p - parameterPartial Q.f p / Q.f p| +
        |parameterPartial Q.f p / Q.f p - Λ * realGradient h j σ p.2| := abs_sub_le _ _ _
    _ ≤ 1 + B := add_le_add (hfη p hp) (hj.log_parameter p hp)
    _ ≤ _ := by linarith

/-- A radius interval starting at the natural entrance. -/
noncomputable def continuationRegion (X0 : ℝ) : Set Point := Icc X0 110 ×ˢ Icc (-1 : ℝ) 1

/-- Stock control data, collecting `first_positive`, `first_bound`, `second_bound`,
`ratio_bound`. -/
structure StockControl {D : RadialDomain} (P : Profiles D) (h M : ℝ) (S : Set Point) : Prop where
  first_positive : ∀ p ∈ S, 0 < ReferenceBounds.p1 P h p
  first_bound : ∀ p ∈ S, ReferenceBounds.p1 P h p ≤ M
  second_bound : ∀ p ∈ S, |ReferenceBounds.p2 P h p| ≤ M
  ratio_bound : ∀ p ∈ S, |ReferenceBounds.p2 P h p / ReferenceBounds.p1 P h p| ≤ M

/-- Stock close data, collecting `first`, `second`, `ratio`. -/
structure StockClose {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    (h ε : ℝ) (p : Point) : Prop where
  first : |ReferenceBounds.p1 P h p - ReferenceBounds.p1 Q h p| < ε
  second : |ReferenceBounds.p2 P h p - ReferenceBounds.p2 Q h p| < ε
  ratio : |Q.f p / P.f p - 1| < ε

/-- All constants in this record are selected before the REF cutoff. -/
structure ComparisonScales where
  /-- Bound of `ComparisonScales`, of type `ℝ`. -/
  bound : ℝ
  /-- Error of `ComparisonScales`, of type `ℝ`. -/
  error : ℝ
  /-- Damping of `ComparisonScales`, of type `ℝ`. -/
  damping : ℝ
  /-- Field tolerance of `ComparisonScales`, of type `ℝ`. -/
  fieldTolerance : ℝ
  /-- Reference radius of `ComparisonScales`, of type `ℝ`. -/
  referenceRadius : ℝ
  bound_pos : 0 < bound
  error_pos : 0 < error
  error_le_one : error ≤ 1
  damping_pos : 0 < damping
  damping_lt_one : damping < 1
  fieldTolerance_pos : 0 < fieldTolerance
  referenceRadius_pos : 0 < referenceRadius
  projection_error : error * projectionConstant bound ≤ 1 / 8
  speed_bound : damping * speedConstant bound ≤ 1
  angular_bound : damping * bound ≤ 4 / 5

/-- Compactness is applied to one bounded family of actual field/history
jets.  It does not select a cutoff first and then ask that cutoff to be
smaller than its own continuity threshold. -/
theorem prepare_stock_comparison {h j σ Λ C B K : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    (hΛ : 0 < Λ) (hΛ1 : 1 ≤ Λ) (hC : 1 ≤ C)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) :
    ∃ c : ComparisonScales, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < c.referenceRadius →
      ∀ hδT : 2 * δ < ReferencePath.rampLimit,
      ReferenceBounds.ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0 →
      ReferenceJetBounds.JetBounds h j σ Λ C B K
        ((ReferencePath.Input.ofNatural hΛ E.profile.family).refF δ)
        ((ReferencePath.Input.ofNatural hΛ E.profile.family).refU δ) →
      let Q := ReferenceBounds.referenceProfiles E.profile hΛ hδ hδT hP0
      StockControl Q h c.bound (continuationRegion (4 / Λ)) ∧
        ∀ {D : RadialDomain} (P : Profiles D), P.pressure0 = Q.pressure0 →
          ∀ p ∈ continuationRegion (4 / Λ), p ∈ D.carrier →
            (∀ t ∈ Icc (0 : ℝ) p.1,
              ‖fieldJet P (t, p.2) - fieldJet Q (t, p.2)‖ < c.fieldTolerance) →
              StockClose P Q h c.error p := by
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  let S := continuationRegion (4 / Λ)
  have hX0 : 0 < 4 / Λ := div_pos (by norm_num) hΛ
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hSX : ∀ p ∈ S, 0 < p.1 := fun p hp => hX0.trans_le hp.1.1
  have hSη : ∀ p ∈ S, p.2 ∈ Icc (-1 : ℝ) 1 := fun _ hp => hp.2
  obtain ⟨μ, r, hμ, hr, hfloor⟩ := reference_positive_uniform N
  obtain ⟨B0, hB0, hp0⟩ := pressure_initial_bound hP0
  let BF := K + B + 6
  have hBF : 0 ≤ BF := by dsimp [BF]; positivity
  obtain ⟨BS, hBS, hstate⟩ := stockJet_uniform_bound hBF hB0.le
  obtain ⟨M0, hM0, hstock⟩ := uniform_stock_bound (B := BS) hsmall hμ hS hSX hSη
  let α : ℝ := (6 / 5 : ℝ) * (4 / Λ)
  have hα : 0 < α := mul_pos (by norm_num) hX0
  let M := 1 + M0 + M0 / α
  have hM : 0 < M := by dsimp [M]; positivity
  have hM0M : M0 ≤ M := by dsimp [M]; linarith [div_nonneg hM0.le hα.le]
  have hratioM : M0 / α ≤ M := by dsimp [M]; linarith
  obtain ⟨ε, κs, hε, hε1, hκs, hκs1, he, hv, ha⟩ := comparison_tolerances hM.le
  obtain ⟨τ, hτ, htransfer⟩ := uniform_stock_transfer (B := BS) hsmall hμ hε hS hSX hSη
  obtain ⟨ρ, hρ, hfield⟩ := field_to_stockJet_transfer BF hτ
  let c : ComparisonScales := ⟨M, ε, κs, ρ, r, hM, hε, hε1, hκs, hκs1, hρ, hr, he, hv, ha⟩
  refine ⟨c, ?_⟩
  intro δ hδ hdr hδT href hj
  let Q := ReferenceBounds.referenceProfiles E.profile hΛ hδ hδT hP0
  have hqfield : ∀ p ∈ ReferenceBounds.holdRegion, ‖fieldJet Q p‖ ≤ BF := by
    intro p hp
    exact reference_fieldJet_bound Q hsmall hΛ1 hC hB hK hj hp
  have hqstate (p : Point) (hp : p ∈ S) : ‖stockJet Q p‖ ≤ BS := by
    apply hstate Q p (ReferenceBounds.reference_mem E.profile hΛ (hSX p hp).le hp.2)
      ⟨(hSX p hp).le, hp.1.2⟩ (hp0 p.2 hp.2).1 (hp0 p.2 hp.2).2
    intro t ht
    exact hqfield (t, p.2) ⟨⟨ht.1, ht.2.trans hp.1.2⟩, hp.2⟩
  have hqfloor (p : Point) (hp : p ∈ S) : 2 * μ ≤ Q.f p := hfloor δ hδ hdr p hp.1.1 hp.2
  have hqpositive (p : Point) (hp : p ∈ S) : 0 < Q.f p := by linarith [hqfloor p hp]
  have hqcoords (p : Point) (hp : p ∈ S) := stockJet_coordinates Q h
    (ReferenceBounds.reference_mem E.profile hΛ (hSX p hp).le hp.2) (hSX p hp) (hqpositive p hp).ne'
  have hlow (p : Point) (hp : p ∈ S) : α ≤ ReferenceBounds.p1 Q h p := by
    exact (mul_le_mul_of_nonneg_left hp.1.1 (by norm_num : (0 : ℝ) ≤ 6 / 5)).trans
      (reference_first_lower E hΛ hδ hδT hP0 hsmall hσ href
        ⟨⟨(hSX p hp).le, hp.1.2⟩, hp.2⟩ (hSX p hp))
  have hbnd (p : Point) (hp : p ∈ S) :
      |ReferenceBounds.p1 Q h p| ≤ M0 ∧ |ReferenceBounds.p2 Q h p| ≤ M0 := by
    have hh := hstock p hp (stockJet Q p) (hqstate p hp) (by
        change μ ≤ Q.f p; linarith [hqfloor p hp])
    rwa [(hqcoords p hp).1, (hqcoords p hp).2] at hh
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    exact hα.trans_le (hlow p hp)
  · intro p hp
    exact (le_abs_self _).trans ((hbnd p hp).1.trans hM0M)
  · intro p hp
    exact (hbnd p hp).2.trans hM0M
  · intro p hp
    have hpos := hα.trans_le (hlow p hp)
    calc
      _ = |ReferenceBounds.p2 Q h p| / ReferenceBounds.p1 Q h p := by rw [abs_div, abs_of_pos hpos]
      _ ≤ M0 / α := by
        gcongr
        · exact (hbnd p hp).2
        · exact hlow p hp
      _ ≤ M := hratioM
  · intro D P hp0eq p hp hpD hclose
    have hpQ := ReferenceBounds.reference_mem E.profile hΛ (hSX p hp).le hp.2
    have hhstate := hfield P Q hp0eq p hpD hpQ ⟨(hSX p hp).le, hp.1.2⟩
      (fun t ht => hqfield (t, p.2) ⟨⟨ht.1, ht.2.trans hp.1.2⟩, hp.2⟩) hclose
    have hh := htransfer p hp (stockJet Q p) (stockJet P p) (hqstate p hp) (hqfloor p hp) hhstate
    have hPf0 : μ < P.f p := hh.1
    have hPf : 0 < P.f p := hμ.trans hPf0
    have hpc := stockJet_coordinates P h hpD (hSX p hp) hPf.ne'
    refine ⟨?_, ?_, hh.2.2.2⟩
    · simpa only [hpc.1, (hqcoords p hp).1] using hh.2.1
    · simpa only [hpc.2, (hqcoords p hp).2] using hh.2.2.1

/-! ## The two terminal ramps preserve the actual relaxed inequality -/

theorem two_ramp_relaxed (c : ComparisonScales) {κ A B p q R b w₁ w₂ y : ℝ}
    (hκ : 0 < κ) (hκc : κ ≤ c.damping) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hA : 0 < A) (hAM : A ≤ c.bound) (hB : |B| ≤ c.bound)
    (hBA : |B / A| ≤ c.bound)
    (hp : |p - A| < c.error) (hq : |q - B| < c.error) (hR : |R - 1| < c.error)
    (hc : (9 / 4 : ℝ) ≤ A + B ^ 2 / A) (hbig : b ≤ y → 3 ≤ A) :
    Relaxed
      ((1 - TransitionRamp.step (b + w₁) w₂ y) * κ * A +
        (4 / 5 : ℝ) * TransitionRamp.step (b + w₁) w₂ y)
      (κ * (1 - TransitionRamp.step b w₁ y) * B * R) p q := by
  let θ := 1 - TransitionRamp.step b w₁ y
  have hθ : θ ∈ Icc (0 : ℝ) 1 := by
    have hh := TransitionRamp.step_mem b w₁ y
    constructor <;> dsimp [θ] <;> linarith [hh.1, hh.2]
  have hv : κ * speedConstant c.bound ≤ 1 :=
    (mul_le_mul_of_nonneg_right hκc (speedConstant_nonneg c.bound_pos.le)).trans c.speed_bound
  by_cases hy : y ≤ b + w₁
  · rw [TransitionRamp.step_zero hw₂ hy]
    simp only [sub_zero, one_mul, mul_zero, add_zero]
    apply damped_relaxed hκ hA c.bound_pos.le hAM c.error_pos.le c.error_le_one hθ
      hB hBA hp.le hq.le hR.le ?_ c.projection_error hv
    by_cases hyb : y ≤ b
    · have hz : θ = 1 := by dsimp [θ]; rw [TransitionRamp.step_zero hw₁ hyb]; norm_num
      change (9 / 4 : ℝ) ≤ A + θ * B ^ 2 / A
      simpa only [hz, one_mul] using hc
    · have hAg := hbig (le_of_not_ge hyb)
      have hn : 0 ≤ θ * B ^ 2 / A := div_nonneg (mul_nonneg hθ.1 (sq_nonneg B)) hA.le
      change (9 / 4 : ℝ) ≤ A + θ * B ^ 2 / A
      linarith
  · have hyb : b ≤ y := by linarith [lt_of_not_ge hy]
    have hz := TransitionRamp.step_one hw₁ (le_of_not_ge hy)
    rw [hz]
    simp only [sub_self, mul_zero, zero_mul]
    have ha4 : κ * A ≤ 4 / 5 :=
      (mul_le_mul hκc hAM hA.le c.damping_pos.le).trans c.angular_bound
    have ha := convex_final_shear (mul_pos hκ hA) ha4 (TransitionRamp.step_mem (b + w₁) w₂ y)
    have hae : (1 - TransitionRamp.step (b + w₁) w₂ y) * κ * A +
        (4 / 5 : ℝ) * TransitionRamp.step (b + w₁) w₂ y =
      (1 - TransitionRamp.step (b + w₁) w₂ y) * (κ * A) +
        TransitionRamp.step (b + w₁) w₂ y * (4 / 5) := by ring
    rw [hae]
    apply zero_axial_relaxed ha.1 (ha.2.trans (by norm_num))
    have hh := (abs_lt.mp hp).1
    have hAg := hbig hyb
    linarith [c.error_le_one]

/-! ## Binding the constructed physical ramp to the cone coordinates -/

section PhysicalRamp

open ReferencePath TransitionRamp

variable {h j σ Λ C δ T κ w₁ w₂ : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : NaturalProfile.ProfileFamily d Λ C)
    (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) (hP0 : ContDiff ℝ ∞ P0)
    (hT : 0 < T) (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)

theorem physical_shear_equations {p : Point} (hp : p.2 ∈ parameterInterval) (hX : 0 < p.1)
    (ht : T ≤ (ofNatural F hΛ hsmall hδ hδT hP0).logTime p.1) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
    shearA P p = (1 - step (R.bigTime + w₁) w₂ (R.logTime p.1)) * κ *
        ReferenceBounds.p1 R.profiles h p + (4 / 5 : ℝ) * step (R.bigTime + w₁) w₂ (R.logTime p.1) ∧
    shearB P p = κ * (1 - step R.bigTime w₁ (R.logTime p.1)) *
      ReferenceBounds.p2 R.profiles h p * (R.profiles.f p / P.f p) := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
  have hd := physical_radial_equations F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂ hp hX
  change (p.1 * radialPartial P.f p / P.f p =
      angularSlope T κ R.bigTime w₁ w₂ R.angularStock (R.logPoint p)) ∧
    (p.1 * radialPartial P.U p = axialSlope T κ R.bigTime w₁ R.axialStock (R.logPoint p)) at hd
  have hc : R.chart (R.logPoint p) = p := by
    exact R.chart_logTime hX
  have ha : R.angularStock (R.logPoint p) = ReferenceBounds.p1 R.profiles h p := by
    change ActivationStocks.profileStockOne R.profiles h (R.chart (R.logPoint p)) = _
    rw [hc]
    rfl
  have hu : R.axialStock (R.logPoint p) = p.1 * ReferenceBounds.ns R.profiles h p := by
    change (R.chart (R.logPoint p)).1 * R.profiles.axialLag h (R.chart (R.logPoint p)) /
      NaturalAxisData.L h p.2 = _
    rw [hc]
    unfold ReferenceBounds.ns
    ring
  have hpf : 0 < P.f p := physicalF_positive F hΛ hsmall hδ hδT hP0 T κ w₁ w₂
    ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg hΛ.le hX.le), hp⟩ hX.le
  have hrf : 0 < R.profiles.f p := by
    have hh := R.f_pos (R.logTime p.1) p.2 hp
    change 0 < R.profiles.f (R.chart (R.logPoint p)) at hh
    rwa [hc] at hh
  have hs : Real.sqrt (2 * p.1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < 2 * p.1)).ne'
  constructor
  · change shearA P p = _
    calc
      _ = -2 * (p.1 * radialPartial P.f p / P.f p) := by unfold shearA; ring
      _ = -2 * angularSlope T κ R.bigTime w₁ w₂ R.angularStock (R.logPoint p) := by rw [hd.1]
      _ = _ := by
        unfold angularSlope baseSlope
        rw [show damping T κ (R.logPoint p).1 = κ from damping_eq_constant hT κ ht, ha]
        dsimp only [StockReference.logPoint]
        ring
  · change shearB P p = _
    calc
      _ = -2 * (p.1 * radialPartial P.U p) / P.E p := by unfold shearB; ring
      _ = -2 * axialSlope T κ R.bigTime w₁ R.axialStock (R.logPoint p) / P.E p := by rw [hd.2]
      _ = κ * (1 - step R.bigTime w₁ (R.logTime p.1)) * (p.1 * ReferenceBounds.ns R.profiles h p) /
          P.E p := by
        unfold axialSlope baseSlope
        rw [show damping T κ (R.logPoint p).1 = κ from damping_eq_constant hT κ ht, hu]
        dsimp only [StockReference.logPoint]
        ring
      _ = _ := by
        unfold ReferenceBounds.p2 Profiles.E
        dsimp only [R, P] at hpf hrf ⊢
        field_simp [hs, hpf.ne', hrf.ne']

/-- The whole incoming field jet is exactly preserved, including the
join at the natural endpoint. -/
theorem physical_fieldJet_before {p : Point}
    (hp : p ∈ (Input.ofNatural hΛ F).radialDomain.carrier)
    (hx : p.1 ≤ (Input.ofNatural hΛ F).endpoint) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
    fieldJet P p = fieldJet R.profiles p := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
  have hf : (fun η => P.f (p.1, η)) = (fun η => R.profiles.f (p.1, η)) := by
    funext η
    exact R.physicalF_before T κ w₁ w₂ hx
  have hu : (fun η => P.U (p.1, η)) = (fun η => R.profiles.U (p.1, η)) := by
    funext η
    exact R.physicalU_before T κ w₁ hx
  have hfη : parameterPartial P.f p = parameterPartial R.profiles.f p := by
    have hd := parameterPartial_hasDerivAt (Input.ofNatural hΛ F).radialDomain P.f_smooth hp
    rw [hf] at hd
    exact hd.unique (parameterPartial_hasDerivAt (Input.ofNatural hΛ F).radialDomain
        R.profiles.f_smooth hp)
  have huη : parameterPartial P.U p = parameterPartial R.profiles.U p := by
    have hd := parameterPartial_hasDerivAt (Input.ofNatural hΛ F).radialDomain P.U_smooth hp
    rw [hu] at hd
    exact hd.unique (parameterPartial_hasDerivAt (Input.ofNatural hΛ F).radialDomain
        R.profiles.U_smooth hp)
  change fieldJet P p = fieldJet R.profiles p
  unfold fieldJet
  rw [show P.f p = R.profiles.f p from congrFun hf p.2,
    show P.U p = R.profiles.U p from congrFun hu p.2, hfη, huη]

/-- Rewrite the endpoint in the physical error estimates as the original
natural endpoint, whose bounds were fixed before the reference cutoff. -/
theorem physical_endpoint_control {ε : ℝ}
    (hc : (ofNatural F hΛ hsmall hδ hδT hP0).SmallPhysicalControl
      (Icc (-1 : ℝ) 1) 1 ε T κ w₁ w₂)
    {p : Point} (hp : p ∈ continuationRegion (4 / Λ)) :
    let N := Input.ofNatural hΛ F
    let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
    |P.U p - N.U (N.endpoint, p.2)| < ε ∧
    |parameterPartial P.U p - parameterPartial N.U (N.endpoint, p.2)| < ε ∧
    |parameterPartial P.f p / P.f p - parameterPartial N.f (N.endpoint, p.2) /
      N.f (N.endpoint, p.2)| < ε := by
  let N := Input.ofNatural hΛ F
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
  have hm := ReferenceJetBounds.reference_mem N ((N.endpoint_pos).le.trans hp.1.1) hp.2
  have hme := ReferenceJetBounds.endpoint_mem N hp.2
  have hUi : R.initialU = fun η => N.U (N.endpoint, η) := by
    funext η
    exact N.refU_eq_natural_initial δ le_rfl
  have hLi : R.initialLog = fun η => Real.log (N.f (N.endpoint, η)) := by
    funext η
    exact congrArg Real.log (N.refF_eq_natural_initial δ le_rfl)
  have hu0 := hc.axial_jets p.1 hp.1 p.2 hp.2 0 (by norm_num)
  have hu1 := hc.axial_jets p.1 hp.1 p.2 hp.2 1 le_rfl
  have hl1 := hc.positive_log_jets p.1 hp.1 p.2 hp.2 1 le_rfl (by norm_num)
  change |iteratedDeriv 0 (fun η => P.U (p.1, η) - R.initialU η) p.2| < ε at hu0
  change |iteratedDeriv 1 (fun η => P.U (p.1, η) - R.initialU η) p.2| < ε at hu1
  change |iteratedDeriv 1 (fun η => Real.log (P.f (p.1, η)) - R.initialLog η) p.2| < ε at hl1
  rw [hUi, iteratedDeriv_zero] at hu0
  rw [hUi, ReferenceJetBounds.first_parameter_difference
    (P.U_smooth.contDiffAt (N.radialDomain.isOpen.mem_nhds hm))
    (N.U_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds hme))] at hu1
  have hPf : 0 < P.f p := physicalF_positive F hΛ hsmall hδ hδT hP0 T κ w₁ w₂ hm
    (N.endpoint_pos.le.trans hp.1.1)
  rw [hLi, ReferenceJetBounds.first_log_difference
    (P.f_smooth.contDiffAt (N.radialDomain.isOpen.mem_nhds hm))
    (N.f_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds hme))
    hPf.ne' (N.endpoint_f_pos (original_interval_interior hp.2)).ne'] at hl1
  exact ⟨hu0, hu1, hl1⟩

theorem physical_endpoint_log_value {ε : ℝ}
    (hc : (ofNatural F hΛ hsmall hδ hδT hP0).SmallPhysicalControl
      (Icc (-1 : ℝ) 1) 1 ε T κ w₁ w₂)
    {p : Point} (hη : p.2 ∈ Icc (-1 : ℝ) 1)
    (hx : p.1 ∈ Icc (4 / Λ)
      (radius (4 / Λ) ((ofNatural F hΛ hsmall hδ hδT hP0).bigTime + w₁ + w₂))) :
    let N := Input.ofNatural hΛ F
    let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
    |Real.log (P.f p) - Real.log (N.f (N.endpoint, p.2))| < ε := by
  let N := Input.ofNatural hΛ F
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
  have hh := hc.log_value p.1 hx p.2 hη
  change |Real.log (P.f p) - R.initialLog p.2| < ε at hh
  have he : R.initialLog p.2 = Real.log (N.f (N.endpoint, p.2)) :=
    congrArg Real.log (N.refF_eq_natural_initial δ le_rfl)
  rwa [he] at hh

end PhysicalRamp

/-! ## Uniform logarithmic-to-physical jet conversion -/

theorem angular_endpoint_transfer (N : ReferencePath.Input) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ > 0, ∀ {D : RadialDomain} (P : Profiles D) (p : Point),
      p.2 ∈ Icc (-1 : ℝ) 1 → 0 < P.f p →
      |Real.log (P.f p) - Real.log (N.f (N.endpoint, p.2))| < τ →
      |parameterPartial P.f p / P.f p - parameterPartial N.f (N.endpoint, p.2) /
        N.f (N.endpoint, p.2)| < τ →
      |P.f p - N.f (N.endpoint, p.2)| < ε ∧
      |parameterPartial P.f p - parameterPartial N.f (N.endpoint, p.2)| < ε := by
  obtain ⟨B, hB, hb⟩ := endpointLogJet_bound N
  obtain ⟨τ, hτ, ht⟩ := expJet_uniform B hε
  refine ⟨τ, hτ, ?_⟩
  intro D P p hp hPf hv hd
  let z := endpointLogJet N p.2
  let w : ℝ × ℝ := (Real.log (P.f p), parameterPartial P.f p / P.f p)
  have he : ‖w - z‖ < τ := by
    rw [Prod.norm_def, max_lt_iff]
    exact ⟨hv, hd⟩
  have hh := ht z w (hb p.2 hp) he
  have hNf := N.endpoint_f_pos (original_interval_interior hp)
  have hw : expJet w = (P.f p, parameterPartial P.f p) := by
    dsimp [expJet, w]
    rw [Real.exp_log hPf, mul_div_cancel₀ _ hPf.ne']
  have hz : expJet z = (N.f (N.endpoint, p.2), parameterPartial N.f (N.endpoint, p.2)) := by
    dsimp [expJet, z, endpointLogJet]
    rw [Real.exp_log hNf, mul_div_cancel₀ _ hNf.ne']
  rw [hw, hz, Prod.norm_def, max_lt_iff] at hh
  exact hh

theorem fieldJet_close {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    {p : Point} {ε : ℝ} (hε : 0 < ε)
    (hf : |P.f p - Q.f p| < ε) (hu : |P.U p - Q.U p| < ε)
    (hfη : |parameterPartial P.f p - parameterPartial Q.f p| < ε)
    (huη : |parameterPartial P.U p - parameterPartial Q.U p| < ε) :
    ‖fieldJet P p - fieldJet Q p‖ < ε := by
  apply (pi_norm_lt_iff hε).2
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact hf
  · exact hu
  · exact hfη
  · exact huη

theorem abs_sub_of_common_center {x y z a b : ℝ}
    (hx : |x - z| < a) (hy : |y - z| < b) : |x - y| < a + b := by
  calc
    _ ≤ |x - z| + |y - z| := abs_sub_le _ _ _ |>.trans_eq (by rw [abs_sub_comm z y])
    _ < a + b := add_lt_add hx hy

theorem physical_control_mono {J K : Set ℝ} (R : TransitionRamp.StockReference J)
    {N n : ℕ} {ε ε' T κ w₁ w₂ : ℝ} (hn : n ≤ N) (he : ε ≤ ε')
    (hc : R.SmallPhysicalControl K N ε T κ w₁ w₂) :
    R.SmallPhysicalControl K n ε' T κ w₁ w₂ := by
  refine ⟨hc.finish_before, ?_, ?_, ?_⟩
  · intro X hX η hη k hk
    exact (hc.axial_jets X hX η hη k (hk.trans hn)).trans_le he
  · intro X hX η hη k hk hk0
    exact (hc.positive_log_jets X hX η hη k (hk.trans hn) hk0).trans_le he
  · intro X hX η hη
    exact (hc.log_value X hX η hη).trans_le he

/-! ## Parameters and actual profiles of one common continuation -/

/-- Ramp parameters data, collecting `refTime`, `actTime`, `kappa`, `widthU`, `widthA`,
`refTime_pos` and their compatibility conditions. -/
structure RampParameters {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : NaturalProfile.ProfileFamily d Λ C)
    (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hP0 : ContDiff ℝ ∞ P0) where
  /-- Ref time of `RampParameters`, of type `ℝ`. -/
  refTime : ℝ
  /-- Act time of `RampParameters`, of type `ℝ`. -/
  actTime : ℝ
  /-- Kappa of `RampParameters`, of type `ℝ`. -/
  kappa : ℝ
  /-- Width U of `RampParameters`, of type `ℝ`. -/
  widthU : ℝ
  /-- Width A of `RampParameters`, of type `ℝ`. -/
  widthA : ℝ
  refTime_pos : 0 < refTime
  refTime_bound : 2 * refTime < ReferencePath.rampLimit
  actTime_pos : 0 < actTime
  actTime_le : actTime ≤ refTime
  kappa_pos : 0 < kappa
  kappa_lt_one : kappa < 1
  widthU_pos : 0 < widthU
  widthA_pos : 0 < widthA
  before_big : refTime ≤
    (TransitionRamp.ofNatural F hΛ hsmall refTime_pos refTime_bound hP0).bigTime
  finish_before :
    (TransitionRamp.ofNatural F hΛ hsmall refTime_pos refTime_bound hP0).bigTime + widthU + widthA <
      (TransitionRamp.ofNatural F hΛ hsmall refTime_pos refTime_bound hP0).finalTime

namespace RampParameters

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} {F : NaturalProfile.ProfileFamily d Λ C}
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (r : RampParameters F hΛ hsmall hP0)

/-- Reference, given by `TransitionRamp.ofNatural F hΛ hsmall r.refTime_pos r.refTime_bound
hP0`. -/
noncomputable def reference : TransitionRamp.StockReference ReferencePath.parameterInterval :=
  TransitionRamp.ofNatural F hΛ hsmall r.refTime_pos r.refTime_bound hP0

/-- Profiles, constructed using `TransitionRamp.physicalProfiles`. -/
noncomputable def profiles : Profiles (ReferencePath.Input.ofNatural hΛ F).radialDomain :=
  TransitionRamp.physicalProfiles F hΛ hsmall r.refTime_pos r.refTime_bound hP0
    (κ := r.kappa) r.actTime_pos r.before_big r.widthU_pos r.widthA_pos

/-- Start radius, given by `radius r.reference.radius0 r.actTime`. -/
noncomputable def startRadius : ℝ := radius r.reference.radius0 r.actTime
/-- Hold time, given by `r.reference.bigTime + r.widthU + r.widthA`. -/
noncomputable def holdTime : ℝ := r.reference.bigTime + r.widthU + r.widthA
/-- Hold radius, given by `radius r.reference.radius0 r.holdTime`. -/
noncomputable def holdRadius : ℝ := radius r.reference.radius0 r.holdTime

theorem radius0_eq : r.reference.radius0 = 4 / Λ := rfl

theorem profiles_positive {p : Point} (hp : p.2 ∈ ReferencePath.parameterInterval) (hX : 0 ≤ p.1) :
    0 < r.profiles.f p :=
  TransitionRamp.physicalF_positive F hΛ hsmall r.refTime_pos r.refTime_bound hP0
    r.actTime r.kappa r.widthU r.widthA
    ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg hΛ.le hX), hp⟩ hX

theorem profiles_mem {p : Point} (hp : p.2 ∈ Icc (-1 : ℝ) 1) (hX : 0 ≤ p.1) :
    p ∈ r.reference.domain.carrier :=
  ReferenceJetBounds.reference_mem _ hX hp

theorem bigTime_pos : 0 < r.reference.bigTime := r.refTime_pos.trans_le r.before_big

theorem holdTime_pos : 0 < r.holdTime := by
  dsimp [holdTime]
  linarith [r.bigTime_pos, r.widthU_pos, r.widthA_pos]

theorem startRadius_pos : 0 < r.startRadius :=
  mul_pos r.reference.radius0_pos (Real.exp_pos _)

theorem holdRadius_pos : 0 < r.holdRadius :=
  mul_pos r.reference.radius0_pos (Real.exp_pos _)

theorem radius0_lt_start : r.reference.radius0 < r.startRadius := by
  change r.reference.radius0 < r.reference.radius0 * Real.exp r.actTime
  have he : 1 < Real.exp r.actTime := (Real.one_lt_exp_iff).mpr r.actTime_pos
  nlinarith [r.reference.radius0_pos]

theorem hundred_lt_hold : (100 : ℝ) < r.holdRadius := by
  have he : r.reference.bigTime < r.holdTime := by
      dsimp [holdTime]; linarith [r.widthU_pos, r.widthA_pos]
  have hm := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr he) r.reference.radius0_pos
  have hx : r.reference.radius0 * Real.exp r.reference.bigTime = 100 := by
    rw [TransitionRamp.StockReference.bigTime, Real.exp_log (div_pos (by
        norm_num) r.reference.radius0_pos)]
    field_simp [r.reference.radius0_pos.ne']
  rwa [hx] at hm

theorem hold_lt_final : r.holdRadius < (110 : ℝ) := by
  have hfit : r.holdTime < r.reference.finalTime := r.finish_before
  have hm := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hfit) r.reference.radius0_pos
  have hx : r.reference.radius0 * Real.exp r.reference.finalTime = 110 := by
    rw [TransitionRamp.StockReference.finalTime, Real.exp_log (div_pos (by
        norm_num) r.reference.radius0_pos)]
    field_simp [r.reference.radius0_pos.ne']
  rwa [hx] at hm

theorem start_le_hold : r.startRadius ≤ r.holdRadius := by
  apply mul_le_mul_of_nonneg_left _ r.reference.radius0_pos.le
  apply Real.exp_le_exp.mpr
  have hb : r.refTime ≤ r.reference.bigTime := r.before_big
  dsimp [holdTime]
  linarith [r.actTime_le, r.widthU_pos, r.widthA_pos]

theorem logTime_start {X : ℝ} (hx : r.startRadius ≤ X) : r.actTime ≤ r.reference.logTime X := by
  exact ((ReferencePath.Input.ofNatural hΛ F).le_logTime_iff (r.startRadius_pos.trans_le hx)).mpr hx

theorem logTime_hold {X : ℝ} (hx : r.holdRadius ≤ X) : r.holdTime ≤ r.reference.logTime X := by
  exact ((ReferencePath.Input.ofNatural hΛ F).le_logTime_iff (r.holdRadius_pos.trans_le hx)).mpr hx

theorem physical_shears {p : Point} (hη : p.2 ∈ Icc (-1 : ℝ) 1) (hx : r.startRadius ≤ p.1) :
    shearA r.profiles p =
      (1 - TransitionRamp.step (r.reference.bigTime + r.widthU) r.widthA (r.reference.logTime p.1))
          *
        r.kappa * ReferenceBounds.p1 r.reference.profiles h p +
      (4 / 5 : ℝ) * TransitionRamp.step (r.reference.bigTime + r.widthU) r.widthA
          (r.reference.logTime p.1) ∧
    shearB r.profiles p = r.kappa * (1 - TransitionRamp.step r.reference.bigTime r.widthU
      (r.reference.logTime p.1)) * ReferenceBounds.p2 r.reference.profiles h p *
        (r.reference.profiles.f p / r.profiles.f p) :=
  physical_shear_equations F hΛ hsmall r.refTime_pos r.refTime_bound hP0
    r.actTime_pos r.before_big r.widthU_pos r.widthA_pos
      (original_interval_interior hη) (r.startRadius_pos.trans_le hx) (r.logTime_start hx)

theorem final_shears {p : Point} (hη : p.2 ∈ Icc (-1 : ℝ) 1) (hx : r.holdRadius ≤ p.1) :
    shearA r.profiles p = 4 / 5 ∧ shearB r.profiles p = 0 := by
  have hy := r.logTime_hold hx
  have hh := r.physical_shears hη (r.start_le_hold.trans hx)
  have hA : TransitionRamp.step (r.reference.bigTime + r.widthU) r.widthA (r.reference.logTime p.1)
      = 1 :=
    TransitionRamp.step_one r.widthA_pos hy
  have hU : TransitionRamp.step r.reference.bigTime r.widthU (r.reference.logTime p.1) = 1 :=
    TransitionRamp.step_one r.widthU_pos (by dsimp [holdTime] at hy; linarith [r.widthA_pos])
  simpa only [hA, hU, sub_self, zero_mul, mul_zero, mul_one, zero_add] using hh

theorem final_logSlope {p : Point} (hη : p.2 ∈ Icc (-1 : ℝ) 1) (hx : r.holdRadius ≤ p.1) :
    ReferenceBounds.logSlope r.profiles p = 3 / 5 := by
  rw [logSlope_eq_shear, (r.final_shears hη hx).1]
  norm_num

end RampParameters

/-- The initial collar estimate is retained for the very same chosen
activation width and damping, not for a separately chosen profile. -/
noncomputable def InitialActivationBound {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} {F : NaturalProfile.ProfileFamily d Λ C}
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (r : RampParameters F hΛ hsmall hP0) : Prop :=
  let N := ReferencePath.Input.ofNatural hΛ F
  let L := StressActivation.FromReference.refLog N r.refTime
  let U := StressActivation.FromReference.refAxial N r.refTime
  let I := ActivationStocks.FromReference.initial N r.refTime_pos r.refTime_bound P0 hP0
  ∃ θ > 0, θ ≤ 1 ∧ ∀ y ∈ Ioc (0 : ℝ) r.actTime, ∀ η ∈ Icc (-1 : ℝ) 1,
    activation r.actTime r.kappa y ≤
      ActivationCone.activatedProjection h N.endpoint I L U r.actTime r.kappa (y, η) -
        StressActivation.shearSize r.actTime r.kappa N.endpoint L U (y, η) ∧
    2 + 1 / 32 < ActivationCone.activatedProjection h N.endpoint I L U r.actTime r.kappa (y, η) ∧
    (StressActivation.shearSize r.actTime r.kappa N.endpoint L U (y, η) - 2) *
        ActivationCone.activatedCross h N.endpoint I L U r.actTime r.kappa (y, η) ^ 2 <
      2 * (ActivationCone.activatedProjection h N.endpoint I L U r.actTime r.kappa (y, η) -
        StressActivation.shearSize r.actTime r.kappa N.endpoint L U (y, η)) ^ 2 ∧
    StressActivation.shearSize r.actTime r.kappa N.endpoint L U (y, η) <
      ConeAlgebra.coneBound
        (ActivationCone.activatedProjection h N.endpoint I L U r.actTime r.kappa (y, η))
        (ActivationCone.activatedCross h N.endpoint I L U r.actTime r.kappa (y, η)) ∧
    (y ≤ θ * r.actTime → 2 + 1 / 16 <
      StressActivation.shearSize r.actTime r.kappa N.endpoint L U (y, η))

/-- Quantitative facts established for one actual constructed ramp.  The
existence theorem below supplies every field, including the stock errors. -/
structure ComparableRamp {h j σ Λ C B K : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (r : RampParameters E.profile.family hΛ hsmall hP0)
    (c : ComparisonScales) : Prop where
  reference_bounds : ReferenceBounds.ReferenceBoundsOnHold E.profile hΛ r.refTime_pos
      r.refTime_bound hP0
  reference_jets : ReferenceJetBounds.JetBounds h j σ Λ C B K r.reference.profiles.f
      r.reference.profiles.U
  damping_le : r.kappa ≤ c.damping
  stock_bounds : StockControl r.reference.profiles h c.bound (continuationRegion (4 / Λ))
  stock_close : ∀ p ∈ continuationRegion (4 / Λ), p.1 ≤ r.holdRadius →
    StockClose r.profiles r.reference.profiles h c.error p
  source_jets : ∀ p ∈ ReferenceBounds.holdRegion,
    |Λ * (r.profiles.U p - NaturalAxisData.U j p.2)| ≤ B + 2 ∧
    |Λ * (r.profiles.Ubar p - NaturalAxisData.U j p.2)| ≤ B + 2 ∧
    |Λ * (average (parameterPartial r.profiles.U) p - 4)| ≤ B + 2 ∧
    |parameterPartial r.profiles.f p / r.profiles.f p - Λ * realGradient h j σ p.2| ≤ B + 2

theorem log_control_mono {J K : Set ℝ} (R : TransitionRamp.StockReference J)
    {N n : ℕ} {ε ε' T κ w₁ w₂ : ℝ} (hn : n ≤ N) (he : ε ≤ ε')
    (hc : R.SmallLogControl K N ε T κ w₁ w₂) :
    R.SmallLogControl K n ε' T κ w₁ w₂ := by
  refine ⟨hc.finish_before, ?_, ?_, ?_⟩
  · intro y hy η hη k hk
    exact (hc.axial_jets y hy η hη k (hk.trans hn)).trans_le he
  · intro y hy η hη k hk hk0
    exact (hc.positive_log_jets y hy η hη k (hk.trans hn) hk0).trans_le he
  · intro y hy η hη
    exact (hc.log_value y hy η hη).trans_le he

/-- Construct one shared cutoff, activation and two-ramp schedule.  The
extra finite-jet tolerance is intersected with the cone tolerances, so later
matching does not need to replace this witness. -/
theorem exists_comparable_ramp {h j σ Λ C B K r0 : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    (hΛ : 0 < Λ) (hΛ1 : 1 ≤ Λ) (hC : 1 ≤ C) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0)
    (hr0 : 0 < r0)
    (href : ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < r0 →
      ∃ hδT : 2 * δ < ReferencePath.rampLimit,
        ReferenceBounds.ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0 ∧
        ReferenceJetBounds.JetBounds h j σ Λ C B K
          ((ReferencePath.Input.ofNatural hΛ E.profile.family).refF δ)
          ((ReferencePath.Input.ofNatural hΛ E.profile.family).refU δ))
    (Nextra : ℕ) {εextra : ℝ} (hεextra : 0 < εextra) :
    ∃ r : RampParameters E.profile.family hΛ hsmall hP0, ∃ c : ComparisonScales,
      ComparableRamp (B := B) (K := K) E r c ∧ InitialActivationBound r ∧
      r.reference.SmallPhysicalControl (Icc (-1 : ℝ) 1) Nextra εextra
        r.actTime r.kappa r.widthU r.widthA ∧
      r.reference.SmallLogControl (Icc (-1 : ℝ) 1) Nextra εextra
        r.actTime r.kappa r.widthU r.widthA := by
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  obtain ⟨c, hcompare⟩ := prepare_stock_comparison E hΛ hΛ1 hC hB hK hsmall hσ hP0
  let εF := c.fieldTolerance / 4
  have hεF : 0 < εF := div_pos c.fieldTolerance_pos (by norm_num)
  let εU := min εF (1 / (4 * Λ))
  have hεU : 0 < εU := lt_min hεF (one_div_pos.mpr (mul_pos (by norm_num) hΛ))
  obtain ⟨τ, hτ, hang⟩ := angular_endpoint_transfer N hεF
  let εA := min εU (min τ (1 / 4 : ℝ))
  have hεA : 0 < εA := lt_min hεU (lt_min hτ (by norm_num))
  have hAU : εA ≤ εU := min_le_left _ _
  have hAτ : εA ≤ τ := (min_le_right _ _).trans (min_le_left _ _)
  have hA4 : εA ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨rE, hrE, hend⟩ := reference_endpoint_control N hεU hεF (by norm_num : (0 : ℝ) < 1 / 4)
  let rmin := min r0 (min c.referenceRadius rE)
  have hrmin : 0 < rmin := lt_min hr0 (lt_min c.referenceRadius_pos hrE)
  let δ := rmin / 2
  have hδ : 0 < δ := div_pos hrmin (by norm_num)
  have hδmin : δ < rmin := by dsimp [δ]; linarith
  have hdr0 : δ < r0 := hδmin.trans_le (min_le_left _ _)
  have hdrc : δ < c.referenceRadius := hδmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdrE : δ < rE := hδmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hδT, hRef, hJet⟩ := href δ hδ hdr0
  obtain ⟨hEnd, hEndLog⟩ := hend δ hδ hdrE
  obtain ⟨hStocks, hTransfer⟩ := hcompare δ hδ hdrc hδT hRef hJet
  let R := TransitionRamp.ofNatural E.profile.family hΛ hsmall hδ hδT hP0
  have hb : δ ≤ R.bigTime := by
    have hf := N.freeze_before_Xbig hΛ1 hδT
    have hm : N.endpoint * Real.exp δ ≤ 100 := by
      exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : δ ≤ 2 * δ))
        N.endpoint_pos.le).trans hf.le
    exact (N.le_logTime_iff (by norm_num : (0 : ℝ) < 100)).mpr hm
  obtain ⟨Tstar, θ, hTstar, hTstarδ, hθ, hθ1, hInitial⟩ :=
    ActivationCone.natural_initial_activation hΛ E hP0 hsmall hδ hδT
  let εall := min εA εextra
  have hεall : 0 < εall := lt_min hεA hεextra
  obtain ⟨T0, hT0, κ0, hκ0, w0, hw0, hT0δ, hκ01, hwgap, hControls⟩ :=
    TransitionRamp.exists_joint_small_control E.profile.family hΛ hsmall hδ hδT hP0
      isCompact_Icc original_interval_interior (max Nextra 1) hεall hb
  let T := min T0 Tstar / 2
  have hT : 0 < T := div_pos (lt_min hT0 hTstar) (by norm_num)
  have hTmin : T < min T0 Tstar := by dsimp [T]; linarith [lt_min hT0 hTstar]
  have hTT0 : T < T0 := hTmin.trans_le (min_le_left _ _)
  have hTTstar : T ≤ Tstar := (hTmin.trans_le (min_le_right _ _)).le
  let κ := min κ0 c.damping / 2
  have hκ : 0 < κ := div_pos (lt_min hκ0 c.damping_pos) (by norm_num)
  have hκmin : κ < min κ0 c.damping := by dsimp [κ]; linarith [lt_min hκ0 c.damping_pos]
  have hκκ0 : κ < κ0 := hκmin.trans_le (min_le_left _ _)
  have hκc : κ ≤ c.damping := (hκmin.trans_le (min_le_right _ _)).le
  have hκ1 : κ < 1 := hκκ0.trans hκ01
  let w := w0 / 2
  have hw : 0 < w := div_pos hw0 (by norm_num)
  have hww0 : w < w0 := by dsimp [w]; linarith
  have hJoint := hControls T ⟨hT, hTT0⟩ κ ⟨hκ.le, hκκ0⟩ w ⟨hw, hww0⟩ w ⟨hw, hww0⟩
  have hAll : R.SmallPhysicalControl (Icc (-1 : ℝ) 1) (max Nextra 1) εall T κ w w := hJoint.2
  have hOne : R.SmallPhysicalControl (Icc (-1 : ℝ) 1) 1 εA T κ w w :=
    physical_control_mono R (le_max_right _ _) (min_le_left _ _) hAll
  let r : RampParameters E.profile.family hΛ hsmall hP0 := {
    refTime := δ, actTime := T, kappa := κ, widthU := w, widthA := w
    refTime_pos := hδ, refTime_bound := hδT, actTime_pos := hT
    actTime_le := hTT0.le.trans hT0δ, kappa_pos := hκ, kappa_lt_one := hκ1
    widthU_pos := hw, widthA_pos := hw, before_big := hb, finish_before := hAll.finish_before }
  let P := r.profiles
  let Q := r.reference.profiles
  have hInit : InitialActivationBound r := by
    refine ⟨θ, hθ, hθ1, ?_⟩
    intro y hy η hη
    exact hInitial T ⟨hT, hTTstar⟩ κ ⟨hκ, hκ1⟩ y hy η hη
  have hExtra : r.reference.SmallPhysicalControl (Icc (-1 : ℝ) 1) Nextra εextra
      r.actTime r.kappa r.widthU r.widthA :=
    physical_control_mono R (le_max_left _ _) (min_le_right _ _) hAll
  have hLogExtra : r.reference.SmallLogControl (Icc (-1 : ℝ) 1) Nextra εextra
      r.actTime r.kappa r.widthU r.widthA :=
    log_control_mono R (le_max_left _ _) (min_le_right _ _) hJoint.1
  have hUscale : εU + εU ≤ 1 / Λ := by
    have hu : εU ≤ 1 / (4 * Λ) := min_le_right _ _
    have hid : 1 / (4 * Λ) = (1 / Λ) / 4 := by ring
    rw [hid] at hu
    nlinarith [one_div_pos.mpr hΛ]
  have hUraw : εU + εU < c.fieldTolerance := by
    have hu : εU ≤ εF := min_le_left _ _
    dsimp [εF] at hu
    linarith [c.fieldTolerance_pos]
  have hFraw : εF + εF < c.fieldTolerance := by dsimp [εF]; linarith [c.fieldTolerance_pos]
  have hAct (p : Point) (hp : p ∈ continuationRegion (4 / Λ)) :
      |P.U p - N.U (N.endpoint, p.2)| < εA ∧
      |parameterPartial P.U p - parameterPartial N.U (N.endpoint, p.2)| < εA ∧
      |parameterPartial P.f p / P.f p - parameterPartial N.f (N.endpoint, p.2) /
        N.f (N.endpoint, p.2)| < εA :=
    physical_endpoint_control E.profile.family hΛ hsmall hδ hδT hP0 hT hb hw hw hOne hp
  have hBefore (p : Point) (hp : p ∈ ReferenceBounds.holdRegion) (hx : p.1 ≤ 4 / Λ) :
      fieldJet P p = fieldJet Q p :=
    physical_fieldJet_before E.profile.family hΛ hsmall hδ hδT hP0 hT hb hw hw
      (r.profiles_mem hp.2 hp.1.1) hx
  have hGlobal (p : Point) (hp : p ∈ ReferenceBounds.holdRegion) :
      |P.U p - Q.U p| ≤ 1 / Λ ∧
      |parameterPartial P.U p - parameterPartial Q.U p| ≤ 1 / Λ ∧
      |parameterPartial P.f p / P.f p - parameterPartial Q.f p / Q.f p| ≤ 1 := by
    by_cases hx : p.1 ≤ 4 / Λ
    · have hh := hBefore p hp hx
      have hU : P.U p = Q.U p := congrFun hh 1
      have hUη : parameterPartial P.U p = parameterPartial Q.U p := congrFun hh 3
      have hF : P.f p = Q.f p := congrFun hh 0
      have hFη : parameterPartial P.f p = parameterPartial Q.f p := congrFun hh 2
      rw [hU, hUη, hF, hFη]
      simp only [sub_self, abs_zero]
      exact ⟨(one_div_pos.mpr hΛ).le, (one_div_pos.mpr hΛ).le, zero_le_one⟩
    · have hps : p ∈ continuationRegion (4 / Λ) := ⟨⟨(le_of_not_ge hx), hp.1.2⟩, hp.2⟩
      have ha := hAct p hps
      have hu : |Q.U p - N.U (N.endpoint, p.2)| < εU := hEnd.U_value p hps.1.1 hp.2
      have huη : |parameterPartial Q.U p - parameterPartial N.U (N.endpoint, p.2)| < εU :=
        hEnd.U_parameter p hps.1.1 hp.2
      have hg : |parameterPartial Q.f p / Q.f p - parameterPartial N.f (N.endpoint, p.2) /
          N.f (N.endpoint, p.2)| < 1 / 4 := hEndLog p hps.1.1 hp.2
      refine ⟨(abs_sub_of_common_center (ha.1.trans_le hAU) hu).le.trans hUscale,
        (abs_sub_of_common_center (ha.2.1.trans_le hAU) huη).le.trans hUscale, ?_⟩
      exact (abs_sub_of_common_center (ha.2.2.trans_le hA4) hg).le.trans (by norm_num)
  have hPrefix (p : Point) (hp : p ∈ ReferenceBounds.holdRegion) (hxend : p.1 ≤ r.holdRadius) :
      ‖fieldJet P p - fieldJet Q p‖ < c.fieldTolerance := by
    by_cases hx : p.1 ≤ 4 / Λ
    · rw [hBefore p hp hx, sub_self, norm_zero]
      exact c.fieldTolerance_pos
    · have hps : p ∈ continuationRegion (4 / Λ) := ⟨⟨le_of_not_ge hx, hp.1.2⟩, hp.2⟩
      have ha := hAct p hps
      have hl : |Real.log (P.f p) - Real.log (N.f (N.endpoint, p.2))| < εA :=
        physical_endpoint_log_value E.profile.family hΛ hsmall hδ hδT hP0 hT hb hw hw hOne hp.2
          ⟨hps.1.1, hxend⟩
      have hf := hang P p hp.2 (r.profiles_positive (original_interval_interior hp.2) hp.1.1)
        (hl.trans_le hAτ) (ha.2.2.trans_le hAτ)
      have hfu : |Q.f p - N.f (N.endpoint, p.2)| < εF := hEnd.f_value p hps.1.1 hp.2
      have hfη : |parameterPartial Q.f p - parameterPartial N.f (N.endpoint, p.2)| < εF :=
        hEnd.f_parameter p hps.1.1 hp.2
      have hu : |Q.U p - N.U (N.endpoint, p.2)| < εU := hEnd.U_value p hps.1.1 hp.2
      have huη : |parameterPartial Q.U p - parameterPartial N.U (N.endpoint, p.2)| < εU :=
        hEnd.U_parameter p hps.1.1 hp.2
      exact fieldJet_close P Q c.fieldTolerance_pos
        ((abs_sub_of_common_center hf.1 hfu).trans hFraw)
        ((abs_sub_of_common_center (ha.1.trans_le hAU) hu).trans hUraw)
        ((abs_sub_of_common_center hf.2 hfη).trans hFraw)
        ((abs_sub_of_common_center (ha.2.1.trans_le hAU) huη).trans hUraw)
  refine ⟨r, c, ⟨hRef, hJet, hκc, hStocks, ?_, ?_⟩, hInit, hExtra, hLogExtra⟩
  · intro p hp hendp
    apply hTransfer P rfl p hp (r.profiles_mem hp.2 ((div_pos (by norm_num) hΛ).le.trans hp.1.1))
    intro t ht
    exact hPrefix (t, p.2) ⟨⟨ht.1, ht.2.trans hp.1.2⟩, hp.2⟩ (ht.2.trans hendp)
  · intro p hp
    exact nearby_source_jets P Q hΛ hJet (fun q hq => (hGlobal q hq).1)
      (fun q hq => (hGlobal q hq).2.1) (fun q hq => (hGlobal q hq).2.2)
      hp (r.profiles_mem hp.2 hp.1.1)

/-! ## Cone comparison followed by the actual lag barrier -/

theorem comparable_relaxed_before_hold {h j σ Λ C B K : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (hσ : 0 < σ)
    (r : RampParameters E.profile.family hΛ hsmall hP0) (c : ComparisonScales)
    (hc : ComparableRamp (B := B) (K := K) E r c) {p : Point}
    (hp : p ∈ continuationRegion (4 / Λ))
    (hstart : r.startRadius ≤ p.1) (hend : p.1 ≤ r.holdRadius) :
    IsRelaxed r.profiles h p := by
  have hX := r.startRadius_pos.trans_le hstart
  have hpH : p ∈ ReferenceBounds.holdRegion := ⟨⟨hX.le, hp.1.2⟩, hp.2⟩
  have hs := r.physical_shears hp.2 hstart
  have hclose := hc.stock_close p hp hend
  have hrefcone : (9 / 4 : ℝ) < ReferenceBounds.p1 r.reference.profiles h p +
      ReferenceBounds.p2 r.reference.profiles h p ^ 2 / ReferenceBounds.p1 r.reference.profiles h p
          :=
    hc.reference_bounds.cone_margin p hpH hp.1.1
  have hlarge : r.reference.bigTime ≤ r.reference.logTime p.1 →
      3 ≤ ReferenceBounds.p1 r.reference.profiles h p := by
    intro hy
    change Real.log (100 / r.reference.radius0) ≤ Real.log (p.1 / r.reference.radius0) at hy
    have hd := (Real.log_le_log_iff (div_pos (by norm_num) r.reference.radius0_pos)
      (div_pos hX r.reference.radius0_pos)).mp hy
    have h100 : (100 : ℝ) ≤ p.1 := (div_le_div_iff_of_pos_right r.reference.radius0_pos).mp hd
    have hh := reference_first_lower E hΛ r.refTime_pos r.refTime_bound hP0 hsmall hσ
      hc.reference_bounds hpH hX
    change (6 / 5 : ℝ) * p.1 ≤ ReferenceBounds.p1 r.reference.profiles h p at hh
    linarith
  unfold IsRelaxed
  rw [hs.1, hs.2]
  exact two_ramp_relaxed c r.kappa_pos hc.damping_le r.widthU_pos r.widthA_pos
    (hc.stock_bounds.first_positive p hp) (hc.stock_bounds.first_bound p hp)
    (hc.stock_bounds.second_bound p hp) (hc.stock_bounds.ratio_bound p hp)
    hclose.first hclose.second hclose.ratio hrefcone.le hlarge

/-- A reusable statement of the source estimate already proved by compact
absorption before the scale is chosen. -/
noncomputable def HoldSourceControl (h j σ Λ B : ℝ) : Prop :=
  ∀ {D : RadialDomain} (P : Profiles D) (p : Point),
    p.2 ∈ Icc (-1 : ℝ) 1 → ReferenceBounds.logSlope P p = 3 / 5 →
    |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B →
    |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B →
    |Λ * (average (parameterPartial P.U) p - 4)| ≤ B →
    |parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2| ≤ B →
    (5 / 4 : ℝ) < ReferenceBounds.sourceQ P h p

theorem comparable_final_first {h j σ Λ C B K X η : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (hσ : 0 < σ)
    (r : RampParameters E.profile.family hΛ hsmall hP0) (c : ComparisonScales)
    (hc : ComparableRamp (B := B) (K := K) E r c)
    (hsource : HoldSourceControl h j σ Λ (B + 2))
    (hη : η ∈ Icc (-1 : ℝ) 1) (hX : X ∈ Icc r.holdRadius (110 : ℝ)) :
    2 < ReferenceBounds.p1 r.profiles h (X, η) := by
  have hr0 : 4 / Λ ≤ r.holdRadius := by
    have h0 := r.radius0_lt_start.le.trans r.start_le_hold
    simpa only [r.radius0_eq] using h0
  have hp0 : (r.holdRadius, η) ∈ continuationRegion (4 / Λ) :=
    ⟨⟨hr0, r.hold_lt_final.le⟩, hη⟩
  have hi := comparable_relaxed_before_hold E hσ r c hc hp0 r.start_le_hold le_rfl
  have hinit : 2 < ReferenceBounds.p1 r.profiles h (r.holdRadius, η) := by
    have hp := hi.projection_positive
    change 2 < projection _ _ _ _ at hp
    rw [(r.final_shears hη (le_rfl : r.holdRadius ≤ r.holdRadius)).2] at hp
    simpa only [projection, zero_div, mul_zero, add_zero] using hp
  apply actual_hold_barrier r.profiles (by linarith [r.hundred_lt_hold]) hX.1
    (NaturalAxisData.L_pos hsmall hη) (NaturalEntrance.L_le_one hsmall η)
    (fun t ht => r.profiles_mem hη (r.holdRadius_pos.le.trans ht.1))
    (fun t ht => r.profiles_positive (original_interval_interior hη) (r.holdRadius_pos.le.trans
        ht.1))
    (fun t ht => r.final_logSlope hη ht.1) ?_ hinit
  intro t ht
  have hp : (t, η) ∈ ReferenceBounds.holdRegion :=
    ⟨⟨r.holdRadius_pos.le.trans ht.1, ht.2.trans hX.2⟩, hη⟩
  obtain ⟨hu, hv, hvη, hg⟩ := hc.source_jets (t, η) hp
  have hq := hsource r.profiles (t, η) hη (r.final_logSlope hη ht.1) hu hv hvη hg
  linarith

theorem comparable_relaxed {h j σ Λ C B K : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (hσ : 0 < σ)
    (r : RampParameters E.profile.family hΛ hsmall hP0) (c : ComparisonScales)
    (hc : ComparableRamp (B := B) (K := K) E r c)
    (hsource : HoldSourceControl h j σ Λ (B + 2))
    {p : Point} (hη : p.2 ∈ Icc (-1 : ℝ) 1) (hX : p.1 ∈ Icc r.startRadius (110 : ℝ)) :
    IsRelaxed r.profiles h p := by
  by_cases hend : p.1 ≤ r.holdRadius
  · have hx0 : 4 / Λ ≤ p.1 := by
      have hh := r.radius0_lt_start.le.trans hX.1
      simpa only [r.radius0_eq] using hh
    exact comparable_relaxed_before_hold E hσ r c hc ⟨⟨hx0, hX.2⟩, hη⟩ hX.1 hend
  · have hhold : r.holdRadius ≤ p.1 := (lt_of_not_ge hend).le
    have hfirst := comparable_final_first E hσ r c hc hsource hη ⟨hhold, hX.2⟩
    have hs := r.final_shears hη hhold
    unfold IsRelaxed
    rw [hs.1, hs.2]
    exact zero_axial_relaxed (by norm_num) (by norm_num) hfirst

/-! ## The complete ordered existence statement -/

/-- Continuation witness data, collecting `parameters`, `initial_activation`, `relaxed`,
`final_first`, `final_source`, `physical_control` and their compatibility conditions. -/
structure ContinuationWitness {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hP0 : ContDiff ℝ ∞ P0) (N : ℕ) (ε : ℝ) where
  /-- Parameters of `ContinuationWitness`, of type `RampParameters E.profile.family hΛ hsmall
  hP0`. -/
  parameters : RampParameters E.profile.family hΛ hsmall hP0
  initial_activation : InitialActivationBound parameters
  relaxed : ∀ p : Point, p.2 ∈ Icc (-1 : ℝ) 1 →
    p.1 ∈ Icc parameters.startRadius (110 : ℝ) → IsRelaxed parameters.profiles h p
  final_first : ∀ X ∈ Icc parameters.holdRadius (110 : ℝ), ∀ η ∈ Icc (-1 : ℝ) 1,
    2 < ReferenceBounds.p1 parameters.profiles h (X, η)
  final_source : ∀ X ∈ Icc parameters.holdRadius (110 : ℝ), ∀ η ∈ Icc (-1 : ℝ) 1,
    (5 / 4 : ℝ) < ReferenceBounds.sourceQ parameters.profiles h (X, η)
  physical_control : parameters.reference.SmallPhysicalControl (Icc (-1 : ℝ) 1) N ε
    parameters.actTime parameters.kappa parameters.widthU parameters.widthA
  logarithmic_control : parameters.reference.SmallLogControl (Icc (-1 : ℝ) 1) N ε
    parameters.actTime parameters.kappa parameters.widthU parameters.widthA

/-- The actual relaxed continuation through `X = 110`, with the order
`Λ`, then `C`, then the small cutoff/activation/ramp parameters.  No source,
stock closeness or cone inequality is an input to this theorem. -/
theorem exists_activation_continuation {h j σ ν : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) (hν : 0 < ν)
    (hcut : ∀ η ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z h j P0 η| ≤ ν →
      99 / 100 < NaturalAxisData.chi h j σ η) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ Λ : ℝ, ∀ hΛ : 0 < Λ, M ≤ Λ →
      ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
        ∃ E : NaturalEntrance.EntranceProfile d Λ C,
          ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → Nonempty (ContinuationWitness E hΛ hsmall hP0 N ε) := by
  obtain ⟨B, M, hB, hM, hprep⟩ := ordered_reference_preparation d hsmall hσ hP0 hν hcut
  refine ⟨M, hM, ?_⟩
  intro Λ hΛ hMΛ
  obtain ⟨hsource, C0, K, hC0, hK, hprofiles⟩ := hprep Λ hΛ hMΛ
  refine ⟨C0, hC0, ?_⟩
  intro C hC
  obtain ⟨E, r0, hr0, href⟩ := hprofiles C hC
  refine ⟨E, ?_⟩
  intro N ε hε
  obtain ⟨r, c, hc, hinit, hphysical, hlog⟩ := exists_comparable_ramp E hΛ (hM.trans hMΛ)
    (hC0.trans hC) (zero_lt_one.trans hB).le hK.le hsmall hσ hP0 hr0 href N hε
  refine ⟨{
    parameters := r
    initial_activation := hinit
    relaxed := fun p hη hX => comparable_relaxed E hσ r c hc hsource hη hX
    final_first := fun X hX η hη => comparable_final_first E hσ r c hc hsource hη hX
    final_source := ?_
    physical_control := hphysical
    logarithmic_control := hlog }⟩
  intro X hX η hη
  have hp : (X, η) ∈ ReferenceBounds.holdRegion :=
    ⟨⟨r.holdRadius_pos.le.trans hX.1, hX.2⟩, hη⟩
  obtain ⟨hu, hv, hvη, hg⟩ := hc.source_jets (X, η) hp
  exact hsource r.profiles (X, η) hη (r.final_logSlope hη hX.1) hu hv hvη hg

/-! ## Exact data passed to the shape transition -/

namespace RampParameters

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} {F : NaturalProfile.ProfileFamily d Λ C}
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (r : RampParameters F hΛ hsmall hP0)

/-- Endpoint axial, given by `r.reference.endpointU r.actTime r.kappa r.widthU`. -/
noncomputable def endpointAxial : ℝ → ℝ :=
  r.reference.endpointU r.actTime r.kappa r.widthU

/-- Endpoint logarithm, given by `r.reference.endpointLog r.actTime r.kappa r.widthU r.widthA
C`. -/
noncomputable def endpointLogarithm : ℝ → ℝ :=
  r.reference.endpointLog r.actTime r.kappa r.widthU r.widthA C

theorem endpointAxial_smooth :
    ContDiffOn ℝ ∞ r.endpointAxial ReferencePath.parameterInterval :=
  r.reference.endpointU_smooth ReferencePath.parameterInterval_open _ _ _

theorem endpointLogarithm_smooth :
    ContDiffOn ℝ ∞ r.endpointLogarithm ReferencePath.parameterInterval :=
  r.reference.endpointLog_smooth ReferencePath.parameterInterval_open _ _ _ _ _

theorem initial_fields {p : Point} (hη : p.2 ∈ ReferencePath.parameterInterval)
    (hX : p.1 ≤ (ReferencePath.Input.ofNatural hΛ F).endpoint * Real.exp r.refTime) :
    r.profiles.f p = StressActivation.FromReference.f (ReferencePath.Input.ofNatural hΛ F)
      r.actTime r.kappa r.refTime p ∧
    r.profiles.U p = StressActivation.FromReference.U (ReferencePath.Input.ofNatural hΛ F)
      r.actTime r.kappa r.refTime p :=
  TransitionRamp.physical_fields_eq_activation F hΛ hsmall r.refTime_pos r.refTime_bound hP0
    r.actTime_pos r.before_big r.widthU_pos r.widthA_pos hη hX

theorem terminal_fields (hC : 0 < C) {p : Point} (hη : p.2 ∈ ReferencePath.parameterInterval)
    (hX : 110 ≤ p.1) :
    r.profiles.f p = C⁻¹ * Real.exp (Real.log (p.1 / 110) / 10 + r.endpointLogarithm p.2) /
        Real.sqrt (2 * p.1) ∧ r.profiles.U p = r.endpointAxial p.2 := by
  have hR : r.reference.radius0 < 110 := (r.reference.radius0_lt_100 r.bigTime_pos).trans (by
      norm_num)
  have hfit : r.reference.bigTime + r.widthU + r.widthA ≤ r.reference.finalTime :=
      r.finish_before.le
  refine ⟨r.reference.physicalF_held ReferencePath.parameterInterval_open r.widthA_pos
    hfit hR hC hX hη, ?_⟩
  exact r.reference.physicalU_held ReferencePath.parameterInterval_open r.widthU_pos
    (by linarith [r.widthA_pos]) hR hX hη

theorem endpointLogarithm_eq_actual (hC : 0 < C) {η : ℝ}
    (hη : η ∈ ReferencePath.parameterInterval) :
    r.endpointLogarithm η = Real.log (C * r.profiles.E (110, η)) := by
  have hR : r.reference.radius0 < 110 := (r.reference.radius0_lt_100 r.bigTime_pos).trans (by
      norm_num)
  exact r.reference.endpointLog_eq_actual ReferencePath.parameterInterval_open r.widthA_pos
    r.finish_before.le hR hC hη

end RampParameters

end NavierStokes.ActivationContinuation
