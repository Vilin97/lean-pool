/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityProfile
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

@[expose] public section

/-!
# Radial divisibility and regular slow-order sources

This module removes the apparent `1/X` singularities in the radial source
of equation (22), using the actual differential operators from SimilarityProfile.
-/

noncomputable section

namespace NavierStokes.AxisSourceRegularity

open SimilarityProfile Set Filter
open scoped BigOperators Topology ContDiff

noncomputable def axisFactor (v : InnerProfile) (w : InnerPoint) : ℝ := w.1 * v w

theorem partialX_axisFactor {v : InnerProfile} {w : InnerPoint}
    (hv : DifferentiableAt ℝ v w) :
    partialX (axisFactor v) w = v w + w.1 * partialX v w := by
  change (fderiv ℝ (fun y : InnerPoint => y.1 * v y) w) (1, 0) = _
  rw [(hasFDerivAt_fst.fun_mul hv.hasFDerivAt).fderiv]
  simp [partialX]
  ring

theorem partialEta_axisFactor {v : InnerProfile} {w : InnerPoint}
    (hv : DifferentiableAt ℝ v w) :
    partialEta (axisFactor v) w = w.1 * partialEta v w := by
  change (fderiv ℝ (fun y : InnerPoint => y.1 * v y) w) (0, 1) = _
  rw [(hasFDerivAt_fst.fun_mul hv.hasFDerivAt).fderiv]
  simp [partialEta]

/-- Factoring out X shifts the similarity exponent by one. -/
theorem T_axisFactor (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : DifferentiableAt ℝ v w) :
    T h b (axisFactor v) w = w.1 * T h (b - 1) v w := by
  simp only [T, CoordinateAlgebra.timeCoeff, partialX_axisFactor hv,
    partialEta_axisFactor hv, axisFactor]
  ring

theorem Z_axisFactor (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : DifferentiableAt ℝ v w) :
    Z h b (axisFactor v) w = w.1 * Z h (b - 1) v w := by
  simp only [Z, CoordinateAlgebra.axialCoeff, partialX_axisFactor hv,
    partialEta_axisFactor hv, axisFactor]
  ring

theorem Z_congr_germ (h b : ℝ) {f g : InnerProfile} {w : InnerPoint}
    (hfg : f =ᶠ[𝓝 w] g) : Z h b f w = Z h b g w := by
  simp only [Z, CoordinateAlgebra.axialCoeff, partialX, partialEta,
    hfg.eq_of_nhds, hfg.fderiv_eq]

theorem partialXX_axisFactor {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ 2 v w) :
    partialX (partialX (axisFactor v)) w =
      2 * partialX v w + w.1 * partialX (partialX v) w := by
  have heq : partialX (axisFactor v) =ᶠ[𝓝 w] (fun y => v y + y.1 * partialX v y) := by
    filter_upwards [hv.eventually (by norm_num)] with y hy
    exact partialX_axisFactor (hy.differentiableAt (by norm_num))
  have hx := (partialX_smoothAt hv (m := 1) (by norm_num)).differentiableAt (by norm_num)
  change (fderiv ℝ (partialX (axisFactor v)) w) (1, 0) = _
  rw [heq.fderiv_eq,
    ((hv.differentiableAt (by norm_num)).hasFDerivAt.fun_add
      (hasFDerivAt_fst.fun_mul hx.hasFDerivAt)).fderiv]
  simp [partialX]
  ring

noncomputable def Z2 (h b : ℝ) (v : InnerProfile) : InnerProfile :=
  Z h (b - D h) (Z h b v)

theorem Z2_axisFactor (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ 2 v w) (hL : L h w.2 ≠ 0) :
    Z2 h b (axisFactor v) w = w.1 * Z2 h (b - 1) v w := by
  have heq : Z h b (axisFactor v) =ᶠ[𝓝 w] axisFactor (Z h (b - 1) v) := by
    filter_upwards [hv.eventually (by norm_num)] with y hy
    exact Z_axisFactor h b (hy.differentiableAt (by norm_num))
  change Z h (b - D h) (Z h b (axisFactor v)) w = _
  rw [Z_congr_germ h (b - D h) heq,
    Z_axisFactor h (b - D h) ((Z_smoothAt hv hL).differentiableAt (by norm_num))]
  have he : b - D h - 1 = b - 1 - D h := by ring
  rw [he]
  rfl

theorem radial_advection_axisFactor {vi vj : InnerProfile} {w : InnerPoint}
    (hvj : DifferentiableAt ℝ vj w) :
    axisFactor vi w * (partialX (axisFactor vj) w - axisFactor vj w / (2 * w.1)) =
      w.1 * (vi w * (vj w / 2 + w.1 * partialX vj w)) := by
  rw [partialX_axisFactor hvj]
  unfold axisFactor
  by_cases hX : w.1 = 0
  · simp [hX]
  · field_simp [hX]
    ring

noncomputable def slowOrder (h : ℝ) (k : ℕ) : ℝ := 2 * (k : ℝ) * h

noncomputable def shiftedAxial (h : ℝ) (V : ℕ → InnerProfile) : ℕ → InnerProfile
  | 0 => fun _ => 0
  | k + 1 => Z2 h (slowOrder h k) (V k)

noncomputable def shiftedAxialFactor (h : ℝ) (v : ℕ → InnerProfile) : ℕ → InnerProfile
  | 0 => fun _ => 0
  | k + 1 => Z2 h (slowOrder h k - 1) (v k)

/-- The displayed Ω_k source before canceling its radial factor. -/
noncomputable def omega (h : ℝ) (U V : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint) : ℝ :=
  T h (slowOrder h k) (V k) w +
    (∑ ij ∈ Finset.antidiagonal k,
      (V ij.1 w * (partialX (V ij.2) w - V ij.2 w / (2 * w.1)) +
        U ij.1 w * Z h (slowOrder h ij.2) (V ij.2) w)) -
    2 * w.1 * partialX (partialX (V k)) w - shiftedAxial h V k w

/-- An explicit expression for Ω_k/X with no division by X. -/
noncomputable def omegaDivX (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint) : ℝ :=
  T h (slowOrder h k - 1) (v k) w +
    (∑ ij ∈ Finset.antidiagonal k,
      (v ij.1 w * (v ij.2 w / 2 + w.1 * partialX (v ij.2) w) +
        U ij.1 w * Z h (slowOrder h ij.2 - 1) (v ij.2) w)) -
    (4 * partialX (v k) w + 2 * w.1 * partialX (partialX (v k)) w) -
    shiftedAxialFactor h v k w

theorem shiftedAxial_axisFactor (h : ℝ) (v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    shiftedAxial h (fun j => axisFactor (v j)) k w = w.1 * shiftedAxialFactor h v k w := by
  cases k with
  | zero => simp [shiftedAxial, shiftedAxialFactor]
  | succ k => exact Z2_axisFactor h (slowOrder h k) (hv k (Nat.le_succ k)) hL

/-- Every term in the actual finite Ω_k source has the factor X. -/
theorem omega_axisFactor (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    omega h U (fun j => axisFactor (v j)) k w = w.1 * omegaDivX h U v k w := by
  have hpair : ∀ ij ∈ Finset.antidiagonal k,
      axisFactor (v ij.1) w * (partialX (axisFactor (v ij.2)) w - axisFactor (v ij.2) w / (2 *
        w.1)) +
        U ij.1 w * Z h (slowOrder h ij.2) (axisFactor (v ij.2)) w =
      w.1 * (v ij.1 w * (v ij.2 w / 2 + w.1 * partialX (v ij.2) w) +
        U ij.1 w * Z h (slowOrder h ij.2 - 1) (v ij.2) w) := by
    intro ij hij
    have hj : ij.2 ≤ k := by
      have he := Finset.mem_antidiagonal.mp hij
      omega
    rw [radial_advection_axisFactor ((hv ij.2 hj).differentiableAt (by norm_num)),
      Z_axisFactor h (slowOrder h ij.2) ((hv ij.2 hj).differentiableAt (by norm_num))]
    ring
  unfold omega omegaDivX
  rw [T_axisFactor h (slowOrder h k) ((hv k le_rfl).differentiableAt (by norm_num)),
    Finset.sum_congr rfl hpair, ← Finset.mul_sum,
    partialXX_axisFactor (hv k le_rfl), shiftedAxial_axisFactor h v k w hv hL]
  ring

theorem omega_quotient_eq (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) (hX : w.1 ≠ 0) :
    omega h U (fun j => axisFactor (v j)) k w / w.1 = omegaDivX h U v k w := by
  rw [omega_axisFactor h U v k w hv hL, mul_div_cancel_left₀ _ hX]

theorem partialX_smooth {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) : ContDiffAt ℝ ∞ (partialX v) w :=
  partialX_smoothAt hv (by simp)

theorem partialEta_smooth {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) : ContDiffAt ℝ ∞ (partialEta v) w :=
  partialEta_smoothAt hv (by simp)

theorem T_smooth (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) (hL : L h w.2 ≠ 0) : ContDiffAt ℝ ∞ (T h b v) w := by
  exact (((contDiffAt_const.mul hv).add
    ((contDiffAt_const.mul contDiffAt_snd).mul (partialEta_smooth hv))).add
    (contDiffAt_fst.mul (partialX_smooth hv))).div
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))) hL

theorem Z_smooth (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) (hL : L h w.2 ≠ 0) : ContDiffAt ℝ ∞ (Z h b v) w := by
  exact ((((contDiffAt_const.mul contDiffAt_snd).mul contDiffAt_const).mul hv).add
    ((contDiffAt_const.sub (contDiffAt_snd.pow 2)).mul (partialEta_smooth hv)) |>.sub
    (((contDiffAt_const.mul contDiffAt_snd).mul contDiffAt_fst).mul (partialX_smooth hv))).div
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))) hL

theorem Z2_smooth (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) (hL : L h w.2 ≠ 0) : ContDiffAt ℝ ∞ (Z2 h b v) w :=
  Z_smooth h (b - D h) (Z_smooth h b hv hL) hL

theorem antidiagonal_indices_le {i j k : ℕ} (hij : (i, j) ∈ Finset.antidiagonal k) :
    i ≤ k ∧ j ≤ k := by
  have he := Finset.mem_antidiagonal.mp hij
  omega

/-- The quotient formula is smooth at the axis, using only the finite input
profiles occurring at this order. No division by the radial coordinate remains. -/
theorem omegaDivX_smooth (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hU : ∀ j, j ≤ k → ContDiffAt ℝ ∞ (U j) w)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ ∞ (v j) w) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (omegaDivX h U v k) w := by
  have hs : ContDiffAt ℝ ∞ (fun y => ∑ ij ∈ Finset.antidiagonal k,
      (v ij.1 y * (v ij.2 y / 2 + y.1 * partialX (v ij.2) y) +
        U ij.1 y * Z h (slowOrder h ij.2 - 1) (v ij.2) y)) w := by
    apply ContDiffAt.sum
    intro ij hij
    obtain ⟨hi, hj⟩ := antidiagonal_indices_le hij
    exact ((hv ij.1 hi).mul (((hv ij.2 hj).div contDiffAt_const (by norm_num)).add
      (contDiffAt_fst.mul (partialX_smooth (hv ij.2 hj))))).add
      ((hU ij.1 hi).mul (Z_smooth h _ (hv ij.2 hj) hL))
  have hp : ContDiffAt ℝ ∞ (shiftedAxialFactor h v k) w := by
    cases k with
    | zero => exact contDiffAt_const
    | succ k => exact Z2_smooth h _ (hv k (Nat.le_succ k)) hL
  exact (((T_smooth h _ (hv k le_rfl) hL).add hs).sub
    ((contDiffAt_const.mul (partialX_smooth (hv k le_rfl))).add
      ((contDiffAt_const.mul contDiffAt_fst).mul
        (partialX_smooth (partialX_smooth (hv k le_rfl)))))).sub hp

theorem omegaDivX_smooth_extension_at_axis (h : ℝ) (U v : ℕ → InnerProfile)
    (k : ℕ) (η : ℝ)
    (hU : ∀ j, j ≤ k → ContDiffAt ℝ ∞ (U j) (0, η))
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ ∞ (v j) (0, η)) (hL : L h η ≠ 0) :
    ContDiffAt ℝ ∞ (omegaDivX h U v k) (0, η) :=
  omegaDivX_smooth h U v k (0, η) hU hv hL

theorem partialX_analytic {v : InnerProfile} {w : InnerPoint}
    (hv : AnalyticAt ℝ v w) : AnalyticAt ℝ (partialX v) w :=
  ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : InnerPoint)).analyticAt _).comp hv.fderiv

theorem partialEta_analytic {v : InnerProfile} {w : InnerPoint}
    (hv : AnalyticAt ℝ v w) : AnalyticAt ℝ (partialEta v) w :=
  ((ContinuousLinearMap.apply ℝ ℝ ((0, 1) : InnerPoint)).analyticAt _).comp hv.fderiv

theorem T_analytic (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : AnalyticAt ℝ v w) (hL : L h w.2 ≠ 0) : AnalyticAt ℝ (T h b v) w := by
  exact (((analyticAt_const.mul hv).add
    ((analyticAt_const.mul analyticAt_snd).mul (partialEta_analytic hv))).add
    (analyticAt_fst.mul (partialX_analytic hv))).fun_div
    (analyticAt_const.sub (analyticAt_const.mul (analyticAt_snd.pow 2))) hL

theorem Z_analytic (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : AnalyticAt ℝ v w) (hL : L h w.2 ≠ 0) : AnalyticAt ℝ (Z h b v) w := by
  exact ((((analyticAt_const.mul analyticAt_snd).mul analyticAt_const).mul hv).add
    ((analyticAt_const.sub (analyticAt_snd.pow 2)).mul (partialEta_analytic hv)) |>.sub
    (((analyticAt_const.mul analyticAt_snd).mul analyticAt_fst).mul (partialX_analytic hv))).fun_div
    (analyticAt_const.sub (analyticAt_const.mul (analyticAt_snd.pow 2))) hL

theorem Z2_analytic (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : AnalyticAt ℝ v w) (hL : L h w.2 ≠ 0) : AnalyticAt ℝ (Z2 h b v) w :=
  Z_analytic h (b - D h) (Z_analytic h b hv hL) hL

/-- Joint analytic input germs give an analytic quotient germ, including at X=0. -/
theorem omegaDivX_analytic (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hU : ∀ j, j ≤ k → AnalyticAt ℝ (U j) w)
    (hv : ∀ j, j ≤ k → AnalyticAt ℝ (v j) w) (hL : L h w.2 ≠ 0) :
    AnalyticAt ℝ (omegaDivX h U v k) w := by
  have hs : AnalyticAt ℝ (fun y => ∑ ij ∈ Finset.antidiagonal k,
      (v ij.1 y * (v ij.2 y / 2 + y.1 * partialX (v ij.2) y) +
        U ij.1 y * Z h (slowOrder h ij.2 - 1) (v ij.2) y)) w := by
    apply Finset.analyticAt_fun_sum
    intro ij hij
    obtain ⟨hi, hj⟩ := antidiagonal_indices_le hij
    exact ((hv ij.1 hi).mul (((hv ij.2 hj).fun_div analyticAt_const (by norm_num)).add
      (analyticAt_fst.mul (partialX_analytic (hv ij.2 hj))))).add
      ((hU ij.1 hi).mul (Z_analytic h _ (hv ij.2 hj) hL))
  have hp : AnalyticAt ℝ (shiftedAxialFactor h v k) w := by
    cases k with
    | zero => exact analyticAt_const
    | succ k => exact Z2_analytic h _ (hv k (Nat.le_succ k)) hL
  exact (((T_analytic h _ (hv k le_rfl) hL).add hs).sub
    ((analyticAt_const.mul (partialX_analytic (hv k le_rfl))).add
      ((analyticAt_const.mul analyticAt_fst).mul
        (partialX_analytic (partialX_analytic (hv k le_rfl)))))).sub hp

/-! ## Explicit finite jets and parameter-analytic source formulas -/

structure Jet2 (K : Type*) where
  value : K
  dx : K
  de : K
  dxx : K
  dxe : K
  dex : K
  dee : K

noncomputable def profileJet (v : InnerProfile) (w : InnerPoint) : Jet2 ℝ where
  value := v w
  dx := partialX v w
  de := partialEta v w
  dxx := partialX (partialX v) w
  dxe := partialEta (partialX v) w
  dex := partialX (partialEta v) w
  dee := partialEta (partialEta v) w

noncomputable def jetL {K : Type*} [Field K] (h e : K) : K := 1 - 2 * h * e ^ 2

noncomputable def jetT {K : Type*} [Field K] (h b X e : K) (j : Jet2 K) : K :=
  (-b * j.value + (1 / 2 - h) * e * j.de + X * j.dx) / jetL h e

noncomputable def jetZNumerator {K : Type*} [Field K] (b X e : K) (j : Jet2 K) : K :=
  2 * e * b * j.value + (1 - e ^ 2) * j.de - 2 * e * X * j.dx

noncomputable def jetZNumeratorX {K : Type*} [Field K] (b X e : K) (j : Jet2 K) : K :=
  2 * e * b * j.dx + (1 - e ^ 2) * j.dex - 2 * e * (j.dx + X * j.dxx)

noncomputable def jetZNumeratorE {K : Type*} [Field K] (b X e : K) (j : Jet2 K) : K :=
  2 * b * j.value + 2 * e * b * j.de - 2 * e * j.de +
    (1 - e ^ 2) * j.dee - 2 * X * j.dx - 2 * e * X * j.dxe

noncomputable def jetZ {K : Type*} [Field K] (h b X e : K) (j : Jet2 K) : K :=
  jetZNumerator b X e j / jetL h e

noncomputable def jetZX {K : Type*} [Field K] (h b X e : K) (j : Jet2 K) : K :=
  jetZNumeratorX b X e j / jetL h e

noncomputable def jetZE {K : Type*} [Field K] (h b X e : K) (j : Jet2 K) : K :=
  (jetZNumeratorE b X e j * jetL h e + 4 * h * e * jetZNumerator b X e j) /
    jetL h e ^ 2

noncomputable def jetZ2 {K : Type*} [Field K] (h b X e : K) (j : Jet2 K) : K :=
  (2 * e * (b - (1 / 2 - h)) * jetZ h b X e j +
    (1 - e ^ 2) * jetZE h b X e j - 2 * e * X * jetZX h b X e j) / jetL h e

theorem T_eq_jet (h b : ℝ) (v : InnerProfile) (w : InnerPoint) :
    T h b v w = jetT h b w.1 w.2 (profileJet v w) := rfl

theorem Z_eq_jet (h b : ℝ) (v : InnerProfile) (w : InnerPoint) :
    Z h b v w = jetZ h b w.1 w.2 (profileJet v w) := rfl

theorem Z_partials_eq_jet (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ 2 v w) (hL : L h w.2 ≠ 0) :
    partialX (Z h b v) w = jetZX h b w.1 w.2 (profileJet v w) ∧
      partialEta (Z h b v) w = jetZE h b w.1 w.2 (profileJet v w) := by
  have hvd := (hv.differentiableAt (by norm_num)).hasFDerivAt
  have hxd := ((partialX_smoothAt hv (m := 1) (by norm_num)).differentiableAt (by
    norm_num)).hasFDerivAt
  have hed := ((partialEta_smoothAt hv (m := 1) (by norm_num)).differentiableAt (by
    norm_num)).hasFDerivAt
  have hx : HasFDerivAt (fun y : InnerPoint => y.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) w :=
    hasFDerivAt_fst
  have he : HasFDerivAt (fun y : InnerPoint => y.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) w :=
    hasFDerivAt_snd
  have hn := (((he.const_mul 2).mul_const b).mul hvd).add
    (((hasFDerivAt_const (1 : ℝ) w).sub (he.mul he)).mul hed) |>.sub
    (((he.const_mul 2).mul hx).mul hxd)
  have hl := (hasFDerivAt_const (1 : ℝ) w).sub ((he.mul he).const_mul (2 * h))
  have hL₀ : 1 - 2 * h * (w.2 * w.2) ≠ 0 := by
    simpa only [L, CoordinateAlgebra.L, pow_two] using hL
  have hL₁ : 1 - 2 * h * w.2 ^ 2 ≠ 0 := hL
  have hz := hn.mul ((hasDerivAt_inv hL₀).comp_hasFDerivAt w hl)
  simp only [Function.comp_def, ← pow_two] at hz
  change HasFDerivAt (Z h b v) _ w at hz
  constructor
  · change (fderiv ℝ (Z h b v) w) (1, 0) = _
    rw [hz.fderiv]
    simp [jetZX, jetZNumeratorX, jetL, profileJet, partialX, partialEta, smul_eq_mul]
    field_simp [hL₁] ; ring
  · change (fderiv ℝ (Z h b v) w) (0, 1) = _
    rw [hz.fderiv]
    simp [jetZE, jetZNumeratorE, jetZNumerator, jetL, profileJet, partialX, partialEta,
      smul_eq_mul]
    field_simp [hL₁] ; ring

theorem Z2_eq_jet (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ 2 v w) (hL : L h w.2 ≠ 0) :
    Z2 h b v w = jetZ2 h b w.1 w.2 (profileJet v w) := by
  obtain ⟨hx, he⟩ := Z_partials_eq_jet h b hv hL
  change (2 * w.2 * (b - D h) * Z h b v w + d w.2 * partialEta (Z h b v) w -
    2 * w.2 * w.1 * partialX (Z h b v) w) / L h w.2 = _
  rw [hx, he, Z_eq_jet]
  rfl

noncomputable def jetShifted {K : Type*} [Field K] (h X e : K) (v : ℕ → Jet2 K) : ℕ → K
  | 0 => 0
  | k + 1 => jetZ2 h (2 * (k : K) * h - 1) X e (v k)

/-- The same regular source formula over any field, so complex parameter
extensions use precisely the algebra verified for the real profile derivatives. -/
noncomputable def jetOmegaDivX {K : Type*} [Field K] (h X e : K)
    (U : ℕ → K) (v : ℕ → Jet2 K) (k : ℕ) : K :=
  jetT h (2 * (k : K) * h - 1) X e (v k) +
    (∑ ij ∈ Finset.antidiagonal k,
      ((v ij.1).value * ((v ij.2).value / 2 + X * (v ij.2).dx) +
        U ij.1 * jetZ h (2 * (ij.2 : K) * h - 1) X e (v ij.2))) -
    (4 * (v k).dx + 2 * X * (v k).dxx) - jetShifted h X e v k

theorem omegaDivX_eq_jet (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    omegaDivX h U v k w = jetOmegaDivX h w.1 w.2 (fun j => U j w)
      (fun j => profileJet (v j) w) k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [omegaDivX, jetOmegaDivX, shiftedAxialFactor, jetShifted]
    rw [Z2_eq_jet h (slowOrder h k - 1) (hv k (Nat.le_succ k)) hL]
    rfl

/-- Holomorphic extensions of the seven actual input jets. This is stronger
than separate analyticity of v alone and is the precise parameter hypothesis used. -/
structure AnalyticJetAt (J : ℂ → Jet2 ℂ) (e : ℂ) : Prop where
  value : AnalyticAt ℂ (fun z => (J z).value) e
  dx : AnalyticAt ℂ (fun z => (J z).dx) e
  de : AnalyticAt ℂ (fun z => (J z).de) e
  dxx : AnalyticAt ℂ (fun z => (J z).dxx) e
  dxe : AnalyticAt ℂ (fun z => (J z).dxe) e
  dex : AnalyticAt ℂ (fun z => (J z).dex) e
  dee : AnalyticAt ℂ (fun z => (J z).dee) e

theorem jetL_analytic (h e : ℂ) : AnalyticAt ℂ (jetL h) e :=
  analyticAt_const.sub (analyticAt_const.mul (analyticAt_id.pow 2))

theorem jetT_analytic (h b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetT h b X z (J z)) e := by
  exact (((analyticAt_const.mul hJ.value).add
    ((analyticAt_const.mul analyticAt_id).mul hJ.de)).add
    (analyticAt_const.mul hJ.dx)).fun_div (jetL_analytic h e) hL

theorem jetZNumerator_analytic (b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) : AnalyticAt ℂ (fun z => jetZNumerator b X z (J z)) e := by
  exact ((((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hJ.value).add
    ((analyticAt_const.sub (analyticAt_id.pow 2)).mul hJ.de)).sub
    (((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hJ.dx)

theorem jetZNumeratorX_analytic (b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) : AnalyticAt ℂ (fun z => jetZNumeratorX b X z (J z)) e := by
  exact ((((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hJ.dx).add
    ((analyticAt_const.sub (analyticAt_id.pow 2)).mul hJ.dex)).sub
    ((analyticAt_const.mul analyticAt_id).mul (hJ.dx.add (analyticAt_const.mul hJ.dxx)))

theorem jetZNumeratorE_analytic (b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) : AnalyticAt ℂ (fun z => jetZNumeratorE b X z (J z)) e := by
  exact (((((analyticAt_const.mul hJ.value).add
    (((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hJ.de)).sub
    ((analyticAt_const.mul analyticAt_id).mul hJ.de)).add
    ((analyticAt_const.sub (analyticAt_id.pow 2)).mul hJ.dee)).sub
    (analyticAt_const.mul hJ.dx)).sub
    (((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hJ.dxe)

theorem jetZ_analytic (h b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetZ h b X z (J z)) e :=
  (jetZNumerator_analytic b X hJ).fun_div (jetL_analytic h e) hL

theorem jetZX_analytic (h b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetZX h b X z (J z)) e :=
  (jetZNumeratorX_analytic b X hJ).fun_div (jetL_analytic h e) hL

theorem jetZE_analytic (h b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetZE h b X z (J z)) e := by
  exact (((jetZNumeratorE_analytic b X hJ).mul (jetL_analytic h e)).add
    ((analyticAt_const.mul analyticAt_id).mul (jetZNumerator_analytic b X hJ))).fun_div
    ((jetL_analytic h e).pow 2) (pow_ne_zero _ hL)

theorem jetZ2_analytic (h b X : ℂ) {J : ℂ → Jet2 ℂ} {e : ℂ}
    (hJ : AnalyticJetAt J e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetZ2 h b X z (J z)) e := by
  exact (((((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul
    (jetZ_analytic h b X hJ hL)).add
    ((analyticAt_const.sub (analyticAt_id.pow 2)).mul (jetZE_analytic h b X hJ hL))).sub
    (((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul
      (jetZX_analytic h b X hJ hL))).fun_div (jetL_analytic h e) hL

/-- The finite quotient source is holomorphic in the parameter whenever the
finite input jets have holomorphic extensions and the sole denominator is nonzero. -/
theorem jetOmegaDivX_analytic (h X : ℂ) (U : ℕ → ℂ → ℂ)
    (v : ℕ → ℂ → Jet2 ℂ) (k : ℕ) (e : ℂ)
    (hU : ∀ j, j ≤ k → AnalyticAt ℂ (U j) e)
    (hv : ∀ j, j ≤ k → AnalyticJetAt (v j) e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetOmegaDivX h X z (fun j => U j z) (fun j => v j z) k) e := by
  have hs : AnalyticAt ℂ (fun z => ∑ ij ∈ Finset.antidiagonal k,
      ((v ij.1 z).value * ((v ij.2 z).value / 2 + X * (v ij.2 z).dx) +
        U ij.1 z * jetZ h (2 * (ij.2 : ℂ) * h - 1) X z (v ij.2 z))) e := by
    apply Finset.analyticAt_fun_sum
    intro ij hij
    obtain ⟨hi, hj⟩ := antidiagonal_indices_le hij
    exact ((hv ij.1 hi).value.mul (((hv ij.2 hj).value.fun_div analyticAt_const
      (by norm_num)).add (analyticAt_const.mul (hv ij.2 hj).dx))).add
      ((hU ij.1 hi).mul (jetZ_analytic h _ X (hv ij.2 hj) hL))
  have hp : AnalyticAt ℂ (fun z => jetShifted h X z (fun j => v j z) k) e := by
    cases k with
    | zero => exact analyticAt_const
    | succ k => exact jetZ2_analytic h _ X (hv k (Nat.le_succ k)) hL
  exact (((jetT_analytic h _ X (hv k le_rfl) hL).add hs).sub
    ((analyticAt_const.mul (hv k le_rfl).dx).add
      (analyticAt_const.mul (hv k le_rfl).dxx))).sub hp

noncomputable def complexifyJet (j : Jet2 ℝ) : Jet2 ℂ where
  value := j.value
  dx := j.dx
  de := j.de
  dxx := j.dxx
  dxe := j.dxe
  dex := j.dex
  dee := j.dee

/-- The holomorphic algebra uses the exact real source formula on real inputs. -/
theorem jetOmegaDivX_ofReal (h X e : ℝ) (U : ℕ → ℝ) (v : ℕ → Jet2 ℝ) (k : ℕ) :
    ((jetOmegaDivX h X e U v k : ℝ) : ℂ) =
      jetOmegaDivX (h : ℂ) (X : ℂ) (e : ℂ) (fun j => (U j : ℂ))
        (fun j => complexifyJet (v j)) k := by
  cases k <;> simp [jetOmegaDivX, jetShifted, jetT, jetZ2, jetZ, jetZE, jetZX,
    jetZNumerator, jetZNumeratorX, jetZNumeratorE, jetL, complexifyJet]

theorem omegaDivX_complex_formula (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    (omegaDivX h U v k w : ℂ) =
      jetOmegaDivX (h : ℂ) (w.1 : ℂ) (w.2 : ℂ) (fun j => (U j w : ℂ))
        (fun j => complexifyJet (profileJet (v j) w)) k := by
  rw [omegaDivX_eq_jet h U v k w hv hL, jetOmegaDivX_ofReal]

noncomputable def lowerPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.antidiagonal n).filter (fun ij => 0 < ij.1 ∧ 0 < ij.2)

theorem lowerPairs_lt {n i j : ℕ} (hij : (i, j) ∈ lowerPairs n) : i < n ∧ j < n := by
  obtain ⟨ha, hi, hj⟩ := Finset.mem_filter.mp hij
  have he := Finset.mem_antidiagonal.mp ha
  omega

noncomputable def lowerConvolution (a b : ℕ → InnerProfile) (n : ℕ) (w : InnerPoint) : ℝ :=
  ∑ ij ∈ lowerPairs n, a ij.1 w * b ij.2 w

noncomputable def previousOmegaDivX (h : ℝ) (U v : ℕ → InnerProfile) : ℕ → InnerProfile
  | 0 => fun _ => 0
  | k + 1 => omegaDivX h U v k

/-- The known lower-order pressure source after its radial cancellation. -/
noncomputable def lowerPressureSource (h C : ℝ) (φ U v : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint) : ℝ :=
  C⁻¹ ^ 2 * lowerConvolution φ φ n w - previousOmegaDivX h U v n w / 2

theorem lowerConvolution_smooth (a b : ℕ → InnerProfile) (n : ℕ) (w : InnerPoint)
    (ha : ∀ j, j < n → ContDiffAt ℝ ∞ (a j) w)
    (hb : ∀ j, j < n → ContDiffAt ℝ ∞ (b j) w) :
    ContDiffAt ℝ ∞ (lowerConvolution a b n) w := by
  apply ContDiffAt.sum
  intro ij hij
  obtain ⟨hi, hj⟩ := lowerPairs_lt hij
  exact (ha ij.1 hi).mul (hb ij.2 hj)

theorem lowerPressureSource_smooth (h C : ℝ) (φ U v : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hφ : ∀ j, j < n → ContDiffAt ℝ ∞ (φ j) w)
    (hU : ∀ j, j < n → ContDiffAt ℝ ∞ (U j) w)
    (hv : ∀ j, j < n → ContDiffAt ℝ ∞ (v j) w) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (lowerPressureSource h C φ U v n) w := by
  have hp : ContDiffAt ℝ ∞ (previousOmegaDivX h U v n) w := by
    cases n with
    | zero => exact contDiffAt_const
    | succ k =>
      exact omegaDivX_smooth h U v k w (fun j hj => hU j (Nat.lt_succ_of_le hj))
        (fun j hj => hv j (Nat.lt_succ_of_le hj)) hL
  exact (contDiffAt_const.mul (lowerConvolution_smooth φ φ n w hφ hφ)).sub
    (hp.div contDiffAt_const (by norm_num))

theorem lowerConvolution_analytic (a b : ℕ → InnerProfile) (n : ℕ) (w : InnerPoint)
    (ha : ∀ j, j < n → AnalyticAt ℝ (a j) w)
    (hb : ∀ j, j < n → AnalyticAt ℝ (b j) w) :
    AnalyticAt ℝ (lowerConvolution a b n) w := by
  apply Finset.analyticAt_fun_sum
  intro ij hij
  obtain ⟨hi, hj⟩ := lowerPairs_lt hij
  exact (ha ij.1 hi).mul (hb ij.2 hj)

theorem lowerPressureSource_analytic (h C : ℝ) (φ U v : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hφ : ∀ j, j < n → AnalyticAt ℝ (φ j) w)
    (hU : ∀ j, j < n → AnalyticAt ℝ (U j) w)
    (hv : ∀ j, j < n → AnalyticAt ℝ (v j) w) (hL : L h w.2 ≠ 0) :
    AnalyticAt ℝ (lowerPressureSource h C φ U v n) w := by
  have hp : AnalyticAt ℝ (previousOmegaDivX h U v n) w := by
    cases n with
    | zero => exact analyticAt_const
    | succ k =>
      exact omegaDivX_analytic h U v k w (fun j hj => hU j (Nat.lt_succ_of_le hj))
        (fun j hj => hv j (Nat.lt_succ_of_le hj)) hL
  exact (analyticAt_const.mul (lowerConvolution_analytic φ φ n w hφ hφ)).sub
    (hp.fun_div analyticAt_const (by norm_num))

/-- The regular lower-order source agrees with the displayed pressure source
away from the axis. -/
theorem lowerPressureSource_eq_quotient (h C : ℝ) (φ U v : ℕ → InnerProfile)
    (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w)
    (hL : L h w.2 ≠ 0) (hX : w.1 ≠ 0) :
    lowerPressureSource h C φ U v (k + 1) w =
      C⁻¹ ^ 2 * lowerConvolution φ φ (k + 1) w -
        (omega h U (fun j => axisFactor (v j)) k w / w.1) / 2 := by
  rw [omega_quotient_eq h U v k w hv hL hX]
  rfl

noncomputable def jetPreviousOmega {K : Type*} [Field K] (h X e : K)
    (U : ℕ → K) (v : ℕ → Jet2 K) : ℕ → K
  | 0 => 0
  | k + 1 => jetOmegaDivX h X e U v k

/-- Parameter-analytic algebra for the same finite lower pressure source. -/
noncomputable def jetLowerPressureSource {K : Type*} [Field K] (h C X e : K)
    (φ U : ℕ → K) (v : ℕ → Jet2 K) (n : ℕ) : K :=
  C⁻¹ ^ 2 * (∑ ij ∈ lowerPairs n, φ ij.1 * φ ij.2) -
    jetPreviousOmega h X e U v n / 2

theorem lowerPressureSource_eq_jet (h C : ℝ) (φ U v : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hv : ∀ j, j < n → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    lowerPressureSource h C φ U v n w =
      jetLowerPressureSource h C w.1 w.2 (fun j => φ j w) (fun j => U j w)
        (fun j => profileJet (v j) w) n := by
  cases n with
  | zero => rfl
  | succ k =>
    simp only [lowerPressureSource, previousOmegaDivX, jetLowerPressureSource,
      jetPreviousOmega]
    rw [omegaDivX_eq_jet h U v k w (fun j hj => hv j (Nat.lt_succ_of_le hj)) hL]
    rfl

theorem jetLowerPressureSource_ofReal (h C X e : ℝ) (φ U : ℕ → ℝ)
    (v : ℕ → Jet2 ℝ) (n : ℕ) :
    ((jetLowerPressureSource h C X e φ U v n : ℝ) : ℂ) =
      jetLowerPressureSource (h : ℂ) (C : ℂ) (X : ℂ) (e : ℂ)
        (fun j => (φ j : ℂ)) (fun j => (U j : ℂ))
        (fun j => complexifyJet (v j)) n := by
  cases n <;> simp [jetLowerPressureSource, jetPreviousOmega, jetOmegaDivX_ofReal]

theorem lowerPressureSource_complex_formula (h C : ℝ) (φ U v : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hv : ∀ j, j < n → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    (lowerPressureSource h C φ U v n w : ℂ) =
      jetLowerPressureSource (h : ℂ) (C : ℂ) (w.1 : ℂ) (w.2 : ℂ)
        (fun j => (φ j w : ℂ)) (fun j => (U j w : ℂ))
        (fun j => complexifyJet (profileJet (v j) w)) n := by
  rw [lowerPressureSource_eq_jet h C φ U v n w hv hL, jetLowerPressureSource_ofReal]

/-- Only previously constructed profiles, indexed strictly below n, are needed
for holomorphy of the known source at order n. -/
theorem jetLowerPressureSource_analytic (h C X : ℂ) (φ U : ℕ → ℂ → ℂ)
    (v : ℕ → ℂ → Jet2 ℂ) (n : ℕ) (e : ℂ)
    (hφ : ∀ j, j < n → AnalyticAt ℂ (φ j) e)
    (hU : ∀ j, j < n → AnalyticAt ℂ (U j) e)
    (hv : ∀ j, j < n → AnalyticJetAt (v j) e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetLowerPressureSource h C X z
      (fun j => φ j z) (fun j => U j z) (fun j => v j z) n) e := by
  have hs : AnalyticAt ℂ (fun z => ∑ ij ∈ lowerPairs n, φ ij.1 z * φ ij.2 z) e := by
    apply Finset.analyticAt_fun_sum
    intro ij hij
    obtain ⟨hi, hj⟩ := lowerPairs_lt hij
    exact (hφ ij.1 hi).mul (hφ ij.2 hj)
  have hp : AnalyticAt ℂ (fun z => jetPreviousOmega h X z
      (fun j => U j z) (fun j => v j z) n) e := by
    cases n with
    | zero => exact analyticAt_const
    | succ k =>
      exact jetOmegaDivX_analytic h X U v k e
        (fun j hj => hU j (Nat.lt_succ_of_le hj))
        (fun j hj => hv j (Nat.lt_succ_of_le hj)) hL
  exact (analyticAt_const.mul hs).sub (hp.fun_div analyticAt_const (by norm_num))

/-! ## The other finite lower-order transport sources -/

theorem transport_axisFactor (σ : ℝ) (v f : InnerProfile) (w : InnerPoint)
    (hX : w.1 ≠ 0) :
    axisFactor v w * (partialX f w + σ * f w / w.1) =
      v w * (w.1 * partialX f w + σ * f w) := by
  unfold axisFactor
  field_simp [hX]

noncomputable def shiftedProfileAxial (h b : ℝ) (f : ℕ → InnerProfile) : ℕ → InnerProfile
  | 0 => fun _ => 0
  | k + 1 => Z2 h (b + slowOrder h k) (f k)

/-- The finite known transport part of the angular row has σ=1, and that of
the axial row has σ=0. The base exponents b are supplied separately. -/
noncomputable def lowerTransportSource (h b σ : ℝ) (v U f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint) : ℝ :=
  (∑ ij ∈ lowerPairs n,
    (v ij.1 w * (w.1 * partialX (f ij.2) w + σ * f ij.2 w) +
      U ij.1 w * Z h (b + slowOrder h ij.2) (f ij.2) w)) -
    shiftedProfileAxial h b f n w

theorem lowerTransportSource_eq_quotient (h b σ : ℝ) (v U f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint) (hX : w.1 ≠ 0) :
    lowerTransportSource h b σ v U f n w =
      (∑ ij ∈ lowerPairs n,
        (axisFactor (v ij.1) w * (partialX (f ij.2) w + σ * f ij.2 w / w.1) +
          U ij.1 w * Z h (b + slowOrder h ij.2) (f ij.2) w)) -
        shiftedProfileAxial h b f n w := by
  simp only [lowerTransportSource, transport_axisFactor σ _ _ w hX]

theorem lowerTransportSource_smooth (h b σ : ℝ) (v U f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hv : ∀ j, j < n → ContDiffAt ℝ ∞ (v j) w)
    (hU : ∀ j, j < n → ContDiffAt ℝ ∞ (U j) w)
    (hf : ∀ j, j < n → ContDiffAt ℝ ∞ (f j) w) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (lowerTransportSource h b σ v U f n) w := by
  have hs : ContDiffAt ℝ ∞ (fun y => ∑ ij ∈ lowerPairs n,
      (v ij.1 y * (y.1 * partialX (f ij.2) y + σ * f ij.2 y) +
        U ij.1 y * Z h (b + slowOrder h ij.2) (f ij.2) y)) w := by
    apply ContDiffAt.sum
    intro ij hij
    obtain ⟨hi, hj⟩ := lowerPairs_lt hij
    exact ((hv ij.1 hi).mul ((contDiffAt_fst.mul (partialX_smooth (hf ij.2 hj))).add
      (contDiffAt_const.mul (hf ij.2 hj)))).add
      ((hU ij.1 hi).mul (Z_smooth h _ (hf ij.2 hj) hL))
  have hp : ContDiffAt ℝ ∞ (shiftedProfileAxial h b f n) w := by
    cases n with
    | zero => exact contDiffAt_const
    | succ k => exact Z2_smooth h _ (hf k (Nat.lt_succ_self k)) hL
  exact hs.sub hp

theorem lowerTransportSource_analytic (h b σ : ℝ) (v U f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hv : ∀ j, j < n → AnalyticAt ℝ (v j) w)
    (hU : ∀ j, j < n → AnalyticAt ℝ (U j) w)
    (hf : ∀ j, j < n → AnalyticAt ℝ (f j) w) (hL : L h w.2 ≠ 0) :
    AnalyticAt ℝ (lowerTransportSource h b σ v U f n) w := by
  have hs : AnalyticAt ℝ (fun y => ∑ ij ∈ lowerPairs n,
      (v ij.1 y * (y.1 * partialX (f ij.2) y + σ * f ij.2 y) +
        U ij.1 y * Z h (b + slowOrder h ij.2) (f ij.2) y)) w := by
    apply Finset.analyticAt_fun_sum
    intro ij hij
    obtain ⟨hi, hj⟩ := lowerPairs_lt hij
    exact ((hv ij.1 hi).mul ((analyticAt_fst.mul (partialX_analytic (hf ij.2 hj))).add
      (analyticAt_const.mul (hf ij.2 hj)))).add
      ((hU ij.1 hi).mul (Z_analytic h _ (hf ij.2 hj) hL))
  have hp : AnalyticAt ℝ (shiftedProfileAxial h b f n) w := by
    cases n with
    | zero => exact analyticAt_const
    | succ k => exact Z2_analytic h _ (hf k (Nat.lt_succ_self k)) hL
  exact hs.sub hp

noncomputable def jetShiftedProfileAxial {K : Type*} [Field K] (h b X e : K)
    (f : ℕ → Jet2 K) : ℕ → K
  | 0 => 0
  | k + 1 => jetZ2 h (b + 2 * (k : K) * h) X e (f k)

noncomputable def jetLowerTransportSource {K : Type*} [Field K] (h b σ X e : K)
    (v U : ℕ → K) (f : ℕ → Jet2 K) (n : ℕ) : K :=
  (∑ ij ∈ lowerPairs n,
    (v ij.1 * (X * (f ij.2).dx + σ * (f ij.2).value) +
      U ij.1 * jetZ h (b + 2 * (ij.2 : K) * h) X e (f ij.2))) -
    jetShiftedProfileAxial h b X e f n

theorem lowerTransportSource_eq_jet (h b σ : ℝ) (v U f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hf : ∀ j, j < n → ContDiffAt ℝ 2 (f j) w) (hL : L h w.2 ≠ 0) :
    lowerTransportSource h b σ v U f n w =
      jetLowerTransportSource h b σ w.1 w.2 (fun j => v j w) (fun j => U j w)
        (fun j => profileJet (f j) w) n := by
  cases n with
  | zero => rfl
  | succ k =>
    simp only [lowerTransportSource, jetLowerTransportSource, shiftedProfileAxial,
      jetShiftedProfileAxial]
    rw [Z2_eq_jet h (b + slowOrder h k) (hf k (Nat.lt_succ_self k)) hL]
    rfl

theorem jetLowerTransportSource_ofReal (h b σ X e : ℝ) (v U : ℕ → ℝ)
    (f : ℕ → Jet2 ℝ) (n : ℕ) :
    ((jetLowerTransportSource h b σ X e v U f n : ℝ) : ℂ) =
      jetLowerTransportSource (h : ℂ) (b : ℂ) (σ : ℂ) (X : ℂ) (e : ℂ)
        (fun j => (v j : ℂ)) (fun j => (U j : ℂ))
        (fun j => complexifyJet (f j)) n := by
  cases n <;> simp [jetLowerTransportSource, jetShiftedProfileAxial,
    jetZ2, jetZ, jetZE, jetZX, jetZNumerator, jetZNumeratorX, jetZNumeratorE,
    jetL, complexifyJet]

theorem lowerTransportSource_complex_formula (h b σ : ℝ) (v U f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint)
    (hf : ∀ j, j < n → ContDiffAt ℝ 2 (f j) w) (hL : L h w.2 ≠ 0) :
    (lowerTransportSource h b σ v U f n w : ℂ) =
      jetLowerTransportSource (h : ℂ) (b : ℂ) (σ : ℂ) (w.1 : ℂ) (w.2 : ℂ)
        (fun j => (v j w : ℂ)) (fun j => (U j w : ℂ))
        (fun j => complexifyJet (profileJet (f j) w)) n := by
  rw [lowerTransportSource_eq_jet h b σ v U f n w hf hL, jetLowerTransportSource_ofReal]

theorem jetLowerTransportSource_analytic (h b σ X : ℂ) (v U : ℕ → ℂ → ℂ)
    (f : ℕ → ℂ → Jet2 ℂ) (n : ℕ) (e : ℂ)
    (hv : ∀ j, j < n → AnalyticAt ℂ (v j) e)
    (hU : ∀ j, j < n → AnalyticAt ℂ (U j) e)
    (hf : ∀ j, j < n → AnalyticJetAt (f j) e) (hL : jetL h e ≠ 0) :
    AnalyticAt ℂ (fun z => jetLowerTransportSource h b σ X z
      (fun j => v j z) (fun j => U j z) (fun j => f j z) n) e := by
  have hs : AnalyticAt ℂ (fun z => ∑ ij ∈ lowerPairs n,
      (v ij.1 z * (X * (f ij.2 z).dx + σ * (f ij.2 z).value) +
        U ij.1 z * jetZ h (b + 2 * (ij.2 : ℂ) * h) X z (f ij.2 z))) e := by
    apply Finset.analyticAt_fun_sum
    intro ij hij
    obtain ⟨hi, hj⟩ := lowerPairs_lt hij
    exact ((hv ij.1 hi).mul ((analyticAt_const.mul (hf ij.2 hj).dx).add
      (analyticAt_const.mul (hf ij.2 hj).value))).add
      ((hU ij.1 hi).mul (jetZ_analytic h _ X (hf ij.2 hj) hL))
  have hp : AnalyticAt ℂ (fun z => jetShiftedProfileAxial h b X z
      (fun j => f j z) n) e := by
    cases n with
    | zero => exact analyticAt_const
    | succ k => exact jetZ2_analytic h _ X (hf k (Nat.lt_succ_self k)) hL
  exact hs.sub hp

end NavierStokes.AxisSourceRegularity
