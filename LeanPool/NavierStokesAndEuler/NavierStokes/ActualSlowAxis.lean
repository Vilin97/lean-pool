/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowRecursion
public import LeanPool.NavierStokesAndEuler.NavierStokes.TransitionRamp
public import LeanPool.NavierStokesAndEuler.NavierStokes.ReferenceJetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.StressActivation
import LeanPool.NavierStokesAndEuler.NavierStokes.HolomorphicFamily
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import LeanPool.NavierStokesAndEuler.NavierStokes.CauchyRestriction
public import LeanPool.NavierStokesAndEuler.NavierStokes.CompactSmoothFamily
public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisEvaluation
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The actual natural/ACT base in the all-order local axis recursion

The finite base functions below are the constructed holomorphic natural/ACT
functions. Every regularity field required by `SlowRecursion` is derived
from those functions. In particular the angular slow coefficient is `C*f`.
-/

section

/-!
# Holomorphic parameter extension of the evaluated axis space

The extension is the convergent vertical Taylor series of the genuine compatible
parameter jets. Its Cauchy--Riemann identity follows by termwise differentiation.
-/

@[expose] public section

noncomputable section

open Set Metric Filter Complex
open scoped Topology ContDiff BigOperators
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates
open NavierStokes.AxisEvaluation

namespace NavierStokes.AxisHolomorphic

/-- The polynomial moment of a geometric series. -/
noncomputable def geometricMoment (q : ℝ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) ^ k * q ^ n

theorem summable_geometricMoment {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (k : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * q ^ n) := by
  have hn : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hq] using hq1
  have hs := (summable_pow_mul_geometric_of_norm_lt_one k hn).comp_injective
    (show Function.Injective (fun n : ℕ => n + 1) by
      intro a b hab
      exact Nat.add_right_cancel hab)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, pow_succ, mul_assoc,
    mul_inv_cancel₀ hq.ne', mul_one] using hs.mul_right q⁻¹

theorem geometricMoment_nonneg {q : ℝ} (hq : 0 ≤ q) (k : ℕ) :
    0 ≤ geometricMoment q k := tsum_nonneg (fun n => by positivity)

theorem weight_le_core {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    weight ε n m ≤ coreWeight ε n m := by
  have hden : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 := by
    have hn : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ n by positivity]
    have hm : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ m by positivity]
    nlinarith
  change coreWeight ε n m / _ ≤ coreWeight ε n m
  exact div_le_self (coreWeight_pos hε n m).le hden

theorem choose_geometric_le {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (n m : ℕ) :
    ((n + m).choose m : ℝ) * s ^ n ≤ 1 / (1 - s) ^ (m + 1) := by
  have hn : ‖s‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hs] using hs1
  have hsum := hasSum_choose_mul_geometric_of_norm_lt_one m hn
  rw [← hsum.tsum_eq]
  exact hsum.summable.le_tsum n (fun _ _ => by positivity)

/-- A sharp majorant retaining the binomial factor in the axis norm. -/
theorem term_factorial_bound (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (k m n : ℕ) {p : ℝ × ℝ} (hp : |p.1| ≤ R) :
    ‖term I ε A k m n p‖ ≤
      (‖A‖ / (1 - s) * (m.factorial : ℝ) * ((ε * (1 - s))⁻¹) ^ m) *
        (((n : ℝ) + 1) ^ k * (R / 20 / s) ^ n) := by
  have hs0 : 0 < s := lt_trans (by positivity : 0 < R / 20) hs
  have hb : 0 < 1 - s := by linarith
  have hj : |jet I (weight ε) A.1 n m p.2| ≤ weight ε n m * ‖A‖ := by
    simpa only [abs_of_pos (weight_pos hε n m)] using
      abs_jet_le I (weight ε) A n m p.2
  have hp0 : 0 ≤ (R / 20 / s) ^ n := by positivity
  have hc := mul_le_mul_of_nonneg_right (choose_geometric_le hs0 hs1 n m) hp0
  have he : s ^ n * (R / 20 / s) ^ n = (R / 20) ^ n := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [mul_assoc, he] at hc
  rw [term, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (((n : ℝ) + 1) ^ k * R ^ n) * (weight ε n m * ‖A‖) :=
      mul_le_mul (polynomialJet_bound hR hp n k) hj (abs_nonneg _) (by positivity)
    _ ≤ (((n : ℝ) + 1) ^ k * R ^ n) * (coreWeight ε n m * ‖A‖) := by
      gcongr
      exact weight_le_core hε n m
    _ = (‖A‖ * (ε⁻¹) ^ m * (m.factorial : ℝ) * ((n : ℝ) + 1) ^ k) *
        (((n + m).choose m : ℝ) * (R / 20) ^ n) := by
      simp only [coreWeight, div_pow, one_pow]
      ring
    _ ≤ (‖A‖ * (ε⁻¹) ^ m * (m.factorial : ℝ) * ((n : ℝ) + 1) ^ k) *
        ((1 / (1 - s) ^ (m + 1)) * (R / 20 / s) ^ n) := by
      gcongr
    _ = _ := by
      simp only [mul_inv_rev, mul_pow, pow_succ, div_eq_mul_inv, mul_inv_rev]
      ring

/-- Uniform genuine factorial bounds for all evaluated parameter derivatives.
The positive radius is independent of the fixed radial derivative order `k`. -/
theorem mixedSeries_factorial_bound (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (k m : ℕ) {p : ℝ × ℝ} (hp : |p.1| ≤ R) :
    ‖mixedSeries I ε A k m p‖ ≤
      (‖A‖ / (1 - s) * geometricMoment (R / 20 / s) k) *
        (m.factorial : ℝ) * ((ε * (1 - s))⁻¹) ^ m := by
  have hs0 : 0 < s := lt_trans (by positivity : 0 < R / 20) hs
  have hq0 : 0 < R / 20 / s := by positivity
  have hq1 : R / 20 / s < 1 := (div_lt_one hs0).mpr hs
  have hb : 0 < 1 - s := by linarith
  have ht := (summable_geometricMoment hq0 hq1 k).mul_left
    (‖A‖ / (1 - s) * (m.factorial : ℝ) * ((ε * (1 - s))⁻¹) ^ m)
  calc
    _ ≤ ∑' n : ℕ, (‖A‖ / (1 - s) * (m.factorial : ℝ) * ((ε * (1 - s))⁻¹) ^ m) *
        (((n : ℝ) + 1) ^ k * (R / 20 / s) ^ n) :=
      tsum_of_norm_bounded ht.hasSum (fun n => term_factorial_bound I hε hR hs hs1 A k m n hp)
    _ = _ := by
      rw [tsum_mul_left]
      unfold geometricMoment
      ring

/-- The rectangle above the real window used by the vertical Taylor series. -/
noncomputable def parameterStrip (I : Window) (a : ℝ) : Set ℂ :=
  {z | z.re ∈ Ioo I.left I.right ∧ |z.im| < a / 2}

theorem parameterStrip_isOpen (I : Window) (a : ℝ) : IsOpen (parameterStrip I a) := by
  exact (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_Iio.preimage (Complex.continuous_im.abs))

theorem parameterStrip_convex (I : Window) (a : ℝ) :
    Convex ℝ (parameterStrip I a) := by
  have he : parameterStrip I a =
      (Complex.reCLM ⁻¹' Ioo I.left I.right) ∩
        (Complex.imCLM ⁻¹' Ioo (-(a / 2)) (a / 2)) := by
    ext z
    simp [parameterStrip, abs_lt]
  rw [he]
  exact ((convex_Ioo I.left I.right).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioo (-(a / 2)) (a / 2)).linear_preimage Complex.imCLM.toLinearMap)

/-- A real-linear map specified by its real and imaginary partial derivatives. -/
noncomputable def complexLinearForm (u v : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight u + Complex.imCLM.smulRight v

theorem complexLinearForm_norm (u v : ℂ) :
    ‖complexLinearForm u v‖ ≤ ‖u‖ + ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  calc
    ‖complexLinearForm u v z‖ ≤ ‖z.re • u‖ + ‖z.im • v‖ := norm_add_le _ _
    _ = |z.re| * ‖u‖ + |z.im| * ‖v‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖z‖ * ‖u‖ + ‖z‖ * ‖v‖ := by
      gcongr
      · exact Complex.abs_re_le_norm z
      · exact Complex.abs_im_le_norm z
    _ = (‖u‖ + ‖v‖) * ‖z‖ := by ring

theorem complexLinearForm_tsum {u v : ℕ → ℂ} (hu : Summable u) (hv : Summable v) :
    (∑' n, complexLinearForm (u n) (v n)) =
      complexLinearForm (∑' n, u n) (∑' n, v n) := by
  let R := ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM
  let S := ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM
  change tsum (fun n : ℕ => R (u n) + S (v n)) = R (tsum u) + S (tsum v)
  rw [Summable.tsum_add (R.summable hu) (S.summable hv), R.map_tsum hu, S.map_tsum hv]

/-- A vertical Taylor monomial; `c m` is the normalized genuine real jet. -/
noncomputable def verticalTerm (c : ℕ → ℝ → ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  (c m z.re : ℂ) * ((z.im : ℂ) * Complex.I) ^ m

/-- Vertical X, given by `((m : ℂ) + 1) * verticalTerm (fun n => c (n + 1)) m z`. -/
noncomputable def verticalX (c : ℕ → ℝ → ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  ((m : ℂ) + 1) * verticalTerm (fun n => c (n + 1)) m z

/-- Vertical Y, with branches according to `m = 0`. -/
noncomputable def verticalY (c : ℕ → ℝ → ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  if m = 0 then 0 else Complex.I * verticalX c (m - 1) z

@[simp] theorem verticalY_zero (c : ℕ → ℝ → ℝ) (z : ℂ) : verticalY c 0 z = 0 := by
  simp [verticalY]

@[simp] theorem verticalY_succ (c : ℕ → ℝ → ℝ) (m : ℕ) (z : ℂ) :
    verticalY c (m + 1) z = Complex.I * verticalX c m z := by
  simp [verticalY]

/-- The actual complex extension, defined by a Taylor series in the imaginary direction. -/
noncomputable def verticalExtension (c : ℕ → ℝ → ℝ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, verticalTerm c m z

theorem verticalExtension_ofReal (c : ℕ → ℝ → ℝ) (x : ℝ) :
    verticalExtension c (x : ℂ) = (c 0 x : ℂ) := by
  unfold verticalExtension
  rw [tsum_eq_single 0]
  · simp [verticalTerm]
  · intro m hm
    simp [verticalTerm, hm]

theorem verticalTerm_hasFDerivAt {c : ℕ → ℝ → ℝ} {z : ℂ} (m : ℕ)
    (hc : ∀ n, HasDerivAt (c n) (((n : ℝ) + 1) * c (n + 1) z.re) z.re) :
    HasFDerivAt (verticalTerm c m)
      (complexLinearForm (verticalX c m z) (verticalY c m z)) z := by
  have hR := Complex.ofRealCLM.hasFDerivAt.comp z
    ((hc m).comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)
  have hI := (Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt).mul_const
    Complex.I
  change HasFDerivAt (fun w : ℂ => (c m w.re : ℂ) * ((w.im : ℂ) * Complex.I) ^ m) _ z
  have hp := ((hasDerivAt_pow m ((z.im : ℂ) * Complex.I)).hasFDerivAt.restrictScalars ℝ).comp z hI
  convert! hR.mul hp using 1
  apply ContinuousLinearMap.ext
  intro w
  cases m with
  | zero => simp [verticalX, verticalY, verticalTerm, complexLinearForm, mul_comm]
  | succ m =>
    simp [verticalX, verticalY, verticalTerm, complexLinearForm, pow_succ]
    ring

theorem verticalTerm_bound {c : ℕ → ℝ → ℝ} {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    {z : ℂ} (hz : |z.im| ≤ a / 2)
    (hc : ∀ n, ‖c n z.re‖ ≤ C * (a⁻¹) ^ n) (m : ℕ) :
    ‖verticalTerm c m z‖ ≤ C * (1 / 2 : ℝ) ^ m := by
  have hi : a⁻¹ * |z.im| ≤ 1 / 2 := by
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ ha).mpr (by linarith)
  calc
    _ = ‖c m z.re‖ * |z.im| ^ m := by simp [verticalTerm, norm_pow]
    _ ≤ (C * (a⁻¹) ^ m) * |z.im| ^ m := by gcongr; exact hc m
    _ = C * (a⁻¹ * |z.im|) ^ m := by rw [mul_pow]; ring
    _ ≤ _ := by gcongr

theorem verticalX_bound {c : ℕ → ℝ → ℝ} {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    {z : ℂ} (hz : |z.im| ≤ a / 2)
    (hc : ∀ n, ‖c n z.re‖ ≤ C * (a⁻¹) ^ n) (m : ℕ) :
    ‖verticalX c m z‖ ≤ (C / a) * ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m := by
  have hs : ∀ n, ‖c (n + 1) z.re‖ ≤ (C / a) * (a⁻¹) ^ n := by
    intro n
    convert! hc (n + 1) using 1
    simp only [pow_succ, div_eq_mul_inv]
    ring
  have hm : ‖(m : ℂ) + 1‖ = (m : ℝ) + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, Complex.norm_natCast]
    simp
  rw [verticalX, norm_mul, hm]
  calc
    _ ≤ ((m : ℝ) + 1) * ((C / a) * (1 / 2 : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left (verticalTerm_bound (div_nonneg hC ha.le) ha hz hs m)
        (by positivity)
    _ = _ := by ring

theorem verticalY_bound {c : ℕ → ℝ → ℝ} {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    {z : ℂ} (hz : |z.im| ≤ a / 2)
    (hc : ∀ n, ‖c n z.re‖ ≤ C * (a⁻¹) ^ n) (m : ℕ) :
    ‖verticalY c m z‖ ≤ 2 * ((C / a) * ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m) := by
  cases m with
  | zero => simp only [verticalY_zero, norm_zero]; positivity
  | succ m =>
    simp only [verticalY_succ, norm_mul, Complex.norm_I, one_mul]
    refine (verticalX_bound hC ha hz hc m).trans ?_
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith [mul_nonneg (div_nonneg hC ha.le) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) m)]

theorem summable_verticalTerm {c : ℕ → ℝ → ℝ} {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    {z : ℂ} (hz : |z.im| ≤ a / 2)
    (hc : ∀ n, ‖c n z.re‖ ≤ C * (a⁻¹) ^ n) :
    Summable (fun m => verticalTerm c m z) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left C)
  exact verticalTerm_bound hC ha hz hc

theorem summable_verticalX {c : ℕ → ℝ → ℝ} {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    {z : ℂ} (hz : |z.im| ≤ a / 2)
    (hc : ∀ n, ‖c n z.re‖ ≤ C * (a⁻¹) ^ n) :
    Summable (fun m => verticalX c m z) := by
  have hs := (summable_geometricMoment (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) 1).mul_left (C / a)
  simp only [pow_one, ← mul_assoc] at hs
  exact .of_norm_bounded hs (verticalX_bound hC ha hz hc)

theorem summable_verticalY {c : ℕ → ℝ → ℝ} {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    {z : ℂ} (hz : |z.im| ≤ a / 2)
    (hc : ∀ n, ‖c n z.re‖ ≤ C * (a⁻¹) ^ n) :
    Summable (fun m => verticalY c m z) := by
  have hs := (summable_geometricMoment (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) 1).mul_left (C / a)
  simp only [pow_one, ← mul_assoc] at hs
  exact .of_norm_bounded (hs.mul_left 2) (verticalY_bound hC ha hz hc)

/-- The Cauchy--Riemann identity is an exact shift of the convergent Taylor series. -/
theorem verticalY_tsum {c : ℕ → ℝ → ℝ} {z : ℂ}
    (hX : Summable (fun m => verticalX c m z))
    (hY : Summable (fun m => verticalY c m z)) :
    (∑' m, verticalY c m z) = Complex.I * ∑' m, verticalX c m z := by
  rw [hY.tsum_eq_zero_add]
  simp only [verticalY_zero, verticalY_succ, zero_add]
  exact hX.tsum_mul_left Complex.I

/-- Summing the actual real derivatives gives the complex derivative of the
vertical Taylor series. No analytic continuation is assumed. -/
theorem verticalExtension_hasDerivAt (I : Window) {c : ℕ → ℝ → ℝ} {C a : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a)
    (hderiv : ∀ m x, x ∈ Ioo I.left I.right →
      HasDerivAt (c m) (((m : ℝ) + 1) * c (m + 1) x) x)
    (hbound : ∀ m x, x ∈ Ioo I.left I.right → ‖c m x‖ ≤ C * (a⁻¹) ^ m)
    {z : ℂ} (hz : z ∈ parameterStrip I a) :
    HasDerivAt (verticalExtension c) (∑' m, verticalX c m z) z := by
  have hC' : 0 ≤ C / a := div_nonneg hC ha.le
  have hgeom := (summable_geometricMoment (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) 1).mul_left (C / a)
  simp only [pow_one, ← mul_assoc] at hgeom
  have hu := hgeom.mul_left 3
  have hX := summable_verticalX hC ha hz.2.le (fun m => hbound m z.re hz.1)
  have hY := summable_verticalY hC ha hz.2.le (fun m => hbound m z.re hz.1)
  have hd := hasFDerivAt_tsum_of_isPreconnected
    (f := fun m => verticalTerm c m)
    (f' := fun m w => complexLinearForm (verticalX c m w) (verticalY c m w))
    hu (parameterStrip_isOpen I a) (parameterStrip_convex I a).isPreconnected
    (fun m w hw => verticalTerm_hasFDerivAt m (fun n => hderiv n w.re hw.1))
    (fun m w hw => (complexLinearForm_norm _ _).trans (by
      have hx := verticalX_bound hC ha hw.2.le (fun n => hbound n w.re hw.1) m
      have hy := verticalY_bound hC ha hw.2.le (fun n => hbound n w.re hw.1) m
      linarith))
    hz (summable_verticalTerm hC ha hz.2.le (fun m => hbound m z.re hz.1)) hz
  rw [complexLinearForm_tsum hX hY, verticalY_tsum hX hY] at hd
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasFDerivAt_of_restrictScalars ℝ hd
  rw [Complex.restrictScalars_toSpanSingleton']
  ext w
  simp [complexLinearForm, Complex.real_smul]
  ring

theorem verticalExtension_analytic (I : Window) {c : ℕ → ℝ → ℝ} {C a : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a)
    (hderiv : ∀ m x, x ∈ Ioo I.left I.right →
      HasDerivAt (c m) (((m : ℝ) + 1) * c (m + 1) x) x)
    (hbound : ∀ m x, x ∈ Ioo I.left I.right → ‖c m x‖ ≤ C * (a⁻¹) ^ m) :
    AnalyticOnNhd ℂ (verticalExtension c) (parameterStrip I a) := by
  apply DifferentiableOn.analyticOnNhd _ (parameterStrip_isOpen I a)
  intro z hz
  exact (verticalExtension_hasDerivAt I hC ha hderiv hbound
      hz).differentiableAt.differentiableWithinAt

theorem verticalExtension_bound {c : ℕ → ℝ → ℝ} {C a : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a) {z : ℂ} (hz : |z.im| ≤ a / 2)
    (hbound : ∀ m, ‖c m z.re‖ ≤ C * (a⁻¹) ^ m) :
    ‖verticalExtension c z‖ ≤ 2 * C := by
  have hs := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left C
  have hb := tsum_of_norm_bounded hs (verticalTerm_bound hC ha hz hbound)
  norm_num at hb
  simpa only [verticalExtension, mul_comm C 2] using hb

/-- The actual parameter jets of the evaluated profile, divided by their factorials. -/
noncomputable def normalizedJet (I : Window) (ε : ℝ) (A : AxisSpace I ε) (k : ℕ) (Y : ℝ)
    (m : ℕ) (x : ℝ) : ℝ := mixedSeries I ε A k m (Y, x) / (m.factorial : ℝ)

/-- Jet constant, given by `geometricMoment (R / 20 / s) k / (1 - s)`. -/
noncomputable def jetConstant (R s : ℝ) (k : ℕ) : ℝ :=
  geometricMoment (R / 20 / s) k / (1 - s)

theorem jetConstant_nonneg {R s : ℝ} (hR : 1 ≤ R) (hs : R / 20 < s)
    (hs1 : s < 1) (k : ℕ) : 0 ≤ jetConstant R s k := by
  have hs0 : 0 < s := lt_trans (by positivity : 0 < R / 20) hs
  exact div_nonneg (geometricMoment_nonneg (by positivity) k) (by linarith)

theorem normalizedJet_bound (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (k m : ℕ) {Y : ℝ} (hY : |Y| ≤ R) (x : ℝ) :
    ‖normalizedJet I ε A k Y m x‖ ≤
      (jetConstant R s k * ‖A‖) * ((ε * (1 - s))⁻¹) ^ m := by
  rw [normalizedJet, norm_div, Real.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < m.factorial)).mpr
  calc
    _ ≤ (‖A‖ / (1 - s) * geometricMoment (R / 20 / s) k) *
        (m.factorial : ℝ) * ((ε * (1 - s))⁻¹) ^ m :=
      mixedSeries_factorial_bound I hε hR hs hs1 A k m hY
    _ = _ := by unfold jetConstant; ring

theorem normalizedJet_hasDerivAt_eta (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m : ℕ) {Y x : ℝ}
    (hY : |Y| < 20) (hx : x ∈ Ioo I.left I.right) :
    HasDerivAt (normalizedJet I ε A k Y m)
      (((m : ℝ) + 1) * normalizedJet I ε A k Y (m + 1) x) x := by
  have hd := (mixedSeries_hasDerivAt_eta I hε A k m (abs_lt.mp hY) hx).div_const
    (m.factorial : ℝ)
  convert! hd using 1
  unfold normalizedJet
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem normalizedJet_hasDerivAt_Y (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m : ℕ) {Y x : ℝ}
    (hY : |Y| < 20) (hx : x ∈ Ioo I.left I.right) :
    HasDerivAt (fun y => normalizedJet I ε A k y m x)
      (normalizedJet I ε A (k + 1) Y m x) Y :=
  (mixedSeries_hasDerivAt_Y I hε A k m (abs_lt.mp hY) hx).div_const (m.factorial : ℝ)

/-- The complex extension of the `k`th genuine radial derivative. -/
noncomputable def complexProfile (I : Window) (ε : ℝ) (A : AxisSpace I ε) (k : ℕ) (Y : ℝ) : ℂ → ℂ :=
  verticalExtension (normalizedJet I ε A k Y)

theorem complexProfile_ofReal (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (k : ℕ) (Y x : ℝ) :
    complexProfile I ε A k Y (x : ℂ) = (mixedSeries I ε A k 0 (Y, x) : ℂ) := by
  rw [complexProfile, verticalExtension_ofReal]
  simp [normalizedJet]

theorem complexProfile_zero_ofReal (I : Window) (ε : ℝ) (A : AxisSpace I ε) (Y x : ℝ) :
    complexProfile I ε A 0 Y (x : ℂ) = (profile I ε A (Y, x) : ℂ) := by
  rw [complexProfile_ofReal, mixedSeries_zero]

/-- Holomorphy of every fixed radial derivative, on one common parameter strip. -/
theorem complexProfile_analytic (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (k : ℕ) {Y : ℝ} (hY : |Y| ≤ R) :
    AnalyticOnNhd ℂ (complexProfile I ε A k Y) (parameterStrip I (ε * (1 - s))) := by
  have hY20 : |Y| < 20 := hY.trans_lt (by linarith)
  exact verticalExtension_analytic I
    (mul_nonneg (jetConstant_nonneg hR hs hs1 k) (norm_nonneg A))
    (mul_pos hε (by linarith))
    (fun m x hx => normalizedJet_hasDerivAt_eta I hε A k m hY20 hx)
    (fun m x _ => normalizedJet_bound I hε hR hs hs1 A k m hY x)

/-- The bound is linear in the coefficient norm; the constant and strip width
are independent of the particular solved coefficient vector. -/
theorem complexProfile_bound (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (k : ℕ) {Y : ℝ} (hY : |Y| ≤ R) {z : ℂ} (hz : |z.im| ≤ ε * (1 - s) / 2) :
    ‖complexProfile I ε A k Y z‖ ≤ (2 * jetConstant R s k) * ‖A‖ := by
  unfold complexProfile
  simpa only [mul_assoc] using verticalExtension_bound
    (mul_nonneg (jetConstant_nonneg hR hs hs1 k) (norm_nonneg A))
    (mul_pos hε (by linarith)) hz
    (fun m => normalizedJet_bound I hε hR hs hs1 A k m hY z.re)

theorem verticalTerm_hasDerivAt_Y (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m : ℕ) {Y : ℝ} {z : ℂ}
    (hY : |Y| < 20) (hz : z.re ∈ Ioo I.left I.right) :
    HasDerivAt (fun y => verticalTerm (normalizedJet I ε A k y) m z)
      (verticalTerm (normalizedJet I ε A (k + 1) Y) m z) Y := by
  simpa only [verticalTerm] using
    ((normalizedJet_hasDerivAt_Y I hε A k m hY hz).ofReal_comp).mul_const
      (((z.im : ℂ) * Complex.I) ^ m)

/-- Radial differentiation commutes with the constructed complex extension. -/
theorem complexProfile_hasDerivAt_Y (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (k : ℕ) {Y : ℝ} (hY : |Y| < R) {z : ℂ}
    (hz : z ∈ parameterStrip I (ε * (1 - s))) :
    HasDerivAt (fun y => complexProfile I ε A k y z)
      (complexProfile I ε A (k + 1) Y z) Y := by
  have hR20 : R < 20 := by linarith
  have ha : 0 < ε * (1 - s) := mul_pos hε (by linarith)
  have hC : 0 ≤ jetConstant R s (k + 1) * ‖A‖ :=
    mul_nonneg (jetConstant_nonneg hR hs hs1 (k + 1)) (norm_nonneg A)
  have hgeom := (summable_geometric_of_norm_lt_one
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left (jetConstant R s (k + 1) * ‖A‖)
  exact hasDerivAt_tsum_of_isPreconnected
    (g := fun m y => verticalTerm (normalizedJet I ε A k y) m z)
    (g' := fun m y => verticalTerm (normalizedJet I ε A (k + 1) y) m z)
    hgeom isOpen_Ioo isPreconnected_Ioo
    (fun m y hy => verticalTerm_hasDerivAt_Y I hε A k m ((abs_lt.mpr hy).trans hR20) hz.1)
    (fun m y hy => verticalTerm_bound hC ha hz.2.le
      (fun n => normalizedJet_bound I hε hR hs hs1 A (k + 1) n (abs_lt.mpr hy).le z.re) m)
    (abs_lt.mp hY)
    (summable_verticalTerm
      (mul_nonneg (jetConstant_nonneg hR hs hs1 k) (norm_nonneg A)) ha hz.2.le
      (fun n => normalizedJet_bound I hε hR hs hs1 A k n hY.le z.re))
    (abs_lt.mp hY)

/-- Every member of the holomorphic family is the actual corresponding radial derivative. -/
theorem complexProfile_iteratedDeriv_Y (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (k r : ℕ) {Y : ℝ} (hY : |Y| < R) {z : ℂ}
    (hz : z ∈ parameterStrip I (ε * (1 - s))) :
    iteratedDeriv r (fun y => complexProfile I ε A k y z) Y =
      complexProfile I ε A (k + r) Y z := by
  induction r generalizing Y with
  | zero => simp
  | succ r ih =>
      rw [iteratedDeriv_succ]
      have heq : (iteratedDeriv r (fun y => complexProfile I ε A k y z)) =ᶠ[𝓝 Y]
          (fun y => complexProfile I ε A (k + r) y z) := by
        filter_upwards [Ioo_mem_nhds (abs_lt.mp hY).1 (abs_lt.mp hY).2] with y hy
        exact ih (abs_lt.mpr hy)
      rw [heq.deriv_eq, (complexProfile_hasDerivAt_Y I hε hR hs hs1 A (k + r) hY hz).deriv]
      simp only [Nat.add_assoc]

/-- On the real axis, every genuine complex derivative is the corresponding
already constructed compatible parameter jet. -/
theorem complexProfile_iteratedDeriv_ofReal (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (k m : ℕ) {Y x : ℝ} (hY : |Y| ≤ R) (hx : x ∈ Ioo I.left I.right) :
    iteratedDeriv m (complexProfile I ε A k Y) (x : ℂ) =
      (mixedSeries I ε A k m (Y, x) : ℂ) := by
  have hY20 : |Y| < 20 := hY.trans_lt (by linarith)
  have ha : 0 < ε * (1 - s) := mul_pos hε (by linarith)
  induction m generalizing x with
  | zero => simpa only [iteratedDeriv_zero] using complexProfile_ofReal I ε A k Y x
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have hx' : (x : ℂ) ∈ parameterStrip I (ε * (1 - s)) := by
        exact ⟨hx, by simpa only [Complex.ofReal_im, abs_zero] using half_pos ha⟩
      have han : AnalyticAt ℂ (iteratedDeriv m (complexProfile I ε A k Y)) (x : ℂ) := by
        simpa only [iteratedDeriv_eq_iterate] using
          ((complexProfile_analytic I hε hR hs hs1 A k hY) (x : ℂ) hx').iterated_deriv m
      have heq : (fun t : ℝ => iteratedDeriv m (complexProfile I ε A k Y) (t : ℂ)) =ᶠ[𝓝 x]
          (fun t : ℝ => (mixedSeries I ε A k m (Y, t) : ℂ)) := by
        filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
        exact ih ht
      have hreal := (mixedSeries_hasDerivAt_eta I hε A k m (abs_lt.mp hY20) hx).ofReal_comp
      exact han.differentiableAt.hasDerivAt.comp_ofReal.unique
        (hreal.congr_of_eventuallyEq heq)

/-- The open complex tube around a closed real window. -/
noncomputable def parameterTube (J : Window) (δ : ℝ) : Set ℂ :=
  {z | ∃ x ∈ J.interval, dist z (x : ℂ) < δ}

theorem parameterTube_contains_real (J : Window) {δ : ℝ} (hδ : 0 < δ)
    {x : ℝ} (hx : x ∈ J.interval) : (x : ℂ) ∈ parameterTube J δ :=
  ⟨x, hx, by simpa using hδ⟩

/-- Strict containment of real windows supplies a positive complex tube in the
strip. Its width does not depend on any coefficient vector or derivative order. -/
theorem exists_parameterTube_subset (I J : Window) (hleft : I.left < J.left)
    (hright : J.right < I.right) {a : ℝ} (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ parameterTube J δ ⊆ parameterStrip I a := by
  let δ := min (a / 4) (min ((J.left - I.left) / 2) ((I.right - J.right) / 2))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hδa : δ ≤ a / 4 := min_le_left _ _
  have hδl : δ ≤ (J.left - I.left) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ (I.right - J.right) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  rintro z ⟨x, hx, hz⟩
  have hre : |z.re - x| ≤ dist z (x : ℂ) := by
    simpa only [dist_eq_norm, Complex.sub_re, Complex.ofReal_re] using
      Complex.abs_re_le_norm (z - (x : ℂ))
  have him : |z.im| ≤ dist z (x : ℂ) := by
    simpa only [dist_eq_norm, Complex.sub_im, Complex.ofReal_im, sub_zero] using
      Complex.abs_im_le_norm (z - (x : ℂ))
  have hx' : J.left ≤ x ∧ x ≤ J.right := hx
  have hz' := abs_le.mp hre
  exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- A common, explicitly constructed holomorphic extension exists on a positive
tube over every strictly smaller real window and compact radial interval.

The tube and all bound constants are chosen before the coefficient vector.
Every radial derivative uses this same tube, and all complex parameter jets
match the genuine real jets. -/
theorem exists_common_holomorphic_extension (I J : Window) (hleft : I.left < J.left)
    (hright : J.right < I.right) {ε R : ℝ} (hε : 0 < ε) (hR20 : R < 20) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧
      ∀ (A : AxisSpace I ε) (Y : ℝ), |Y| ≤ R → ∀ k : ℕ,
        AnalyticOnNhd ℂ (complexProfile I ε A k Y) (parameterTube J δ) ∧
        (∀ z ∈ parameterTube J δ, ‖complexProfile I ε A k Y z‖ ≤ B k * ‖A‖) ∧
        (∀ z ∈ parameterTube J δ,
          iteratedDeriv k (fun y => complexProfile I ε A 0 y z) Y =
            complexProfile I ε A k Y z) ∧
        (∀ (m : ℕ) (x : ℝ), x ∈ J.interval →
          iteratedDeriv m (complexProfile I ε A k Y) (x : ℂ) =
            (mixedSeries I ε A k m (Y, x) : ℂ)) := by
  obtain ⟨S, hS, hS20⟩ := exists_between (max_lt (by norm_num : (1 : ℝ) < 20) hR20)
  have hS1 : 1 ≤ S := (le_max_left 1 R).trans hS.le
  have hRS : R < S := (le_max_right 1 R).trans_lt hS
  obtain ⟨s, hs, hs1⟩ := exists_between (show S / 20 < 1 by linarith)
  have ha : 0 < ε * (1 - s) := mul_pos hε (by linarith)
  obtain ⟨δ, hδ, htube⟩ := exists_parameterTube_subset I J hleft hright ha
  refine ⟨δ, hδ, (fun k => 2 * jetConstant S s k), ?_, ?_⟩
  · intro k
    exact mul_nonneg (by norm_num) (jetConstant_nonneg hS1 hs hs1 k)
  · intro A Y hY k
    have hYS : |Y| < S := hY.trans_lt hRS
    refine ⟨(complexProfile_analytic I hε hS1 hs hs1 A k hYS.le).mono htube, ?_, ?_, ?_⟩
    · intro z hz
      exact complexProfile_bound I hε hS1 hs hs1 A k hYS.le (htube hz).2.le
    · intro z hz
      simpa only [Nat.zero_add] using
        complexProfile_iteratedDeriv_Y I hε hS1 hs hs1 A 0 k hYS (htube hz)
    · intro m x hx
      exact complexProfile_iteratedDeriv_ofReal I hε hS1 hs hs1 A k m hYS.le
        ⟨hleft.trans_le hx.1, hx.2.trans_lt hright⟩

end NavierStokes.AxisHolomorphic

end
end

end

section

/-!
# Joint smoothness of the actual holomorphic axis profile

The uniform bounds for the next radial derivative imply continuity in the
supremum norm on every closed parameter disk. A uniform mean-value remainder
then identifies the actual derivative of the disk-valued curve. Iterating this
argument and using the fixed-contour holomorphic-family theorem proves joint
real smoothness of the constructed extension.
-/

@[expose] public section

noncomputable section

open Set Metric Filter Asymptotics
open scoped Topology ContDiff
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisEvaluation
open NavierStokes.AxisHolomorphic NavierStokes.CauchyRestriction

namespace NavierStokes.AxisHolomorphicJoint

/-- A continuous derivative in the supremum norm and the actual coordinate
derivatives give the actual derivative of a compact-family curve. -/
theorem hasDerivAt_compactFamily {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set ℝ} (hS : IsOpen S) (V V' : ℝ → C(K, E))
    (hc : ContinuousOn V' S)
    (hd : ∀ y ∈ S, ∀ z : K, HasDerivAt (fun q => V q z) (V' y z) y)
    {y : ℝ} (hy : y ∈ S) : HasDerivAt V (V' y) y := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  apply isLittleO_iff.mpr
  intro ε hε
  have hsmall : ∀ᶠ q in 𝓝 y, ‖V' q - V' y‖ < ε := by
    simpa only [dist_eq_norm] using
      (Metric.tendsto_nhds.mp (hc.continuousAt (hS.mem_nhds hy)) ε hε)
  have hin : ∀ᶠ q in 𝓝 y, q ∈ S := hS.mem_nhds hy
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp (hin.and hsmall)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with v hv
  have hyv : y + v ∈ ball y δ := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hv
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg v))).mpr
  intro z
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply]
  have hder : ∀ q ∈ ball y δ,
      HasDerivWithinAt (fun q => V q z - q • V' y z)
        (V' q z - V' y z) (ball y δ) q := by
    intro q hq
    simpa only [one_smul, id_eq] using
      ((hd q (hnear hq).1 z).fun_sub ((hasDerivAt_id q).smul_const (V' y z))).hasDerivWithinAt
  have hbound : ∀ q ∈ ball y δ, ‖V' q z - V' y z‖ ≤ ε := by
    intro q hq
    exact ((V' q - V' y).norm_coe_le_norm z).trans (hnear hq).2.le
  have hmean := (convex_ball y δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (mem_ball_self hδ) hyv
  have heq : V (y + v) z - V y z - v • V' y z =
      (V (y + v) z - (y + v) • V' y z) - (V y z - y • V' y z) := by
    rw [add_smul]
    abel
  rw [heq]
  simpa only [add_sub_cancel_left] using hmean

/-- The actual holomorphic profile restricted to a closed parameter disk.
The zero fallback in `family` is used only outside the proved radial domain. -/
noncomputable def diskProfile (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (k : ℕ) : ℝ → C(Disk c σ, ℂ) :=
  CompactSmoothFamily.family (closedBall c σ)
    (fun p : ℝ × ℂ => complexProfile I ε A k p.1 p.2)

theorem diskProfile_apply (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (k : ℕ) {Y : ℝ} (hY : |Y| ≤ R) (z : Disk c σ) :
    diskProfile I ε A c σ k Y z = complexProfile I ε A k Y z := by
  apply CompactSmoothFamily.family_apply
  exact (complexProfile_analytic I hε hR hs hs1 A k hY).continuousOn.comp_continuous
    continuous_subtype_val (fun z => hK z.2)

/-- The next radial derivative controls a whole disk in the supremum norm. -/
theorem diskProfile_norm_sub_le (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (k : ℕ) {Y Y' : ℝ} (hY : |Y| < R) (hY' : |Y'| < R) :
    ‖diskProfile I ε A c σ k Y' - diskProfile I ε A c σ k Y‖ ≤
      ((2 * jetConstant R s (k + 1)) * ‖A‖) * ‖Y' - Y‖ := by
  have hB : 0 ≤ (2 * jetConstant R s (k + 1)) * ‖A‖ :=
    mul_nonneg (mul_nonneg (by norm_num) (jetConstant_nonneg hR hs hs1 _)) (norm_nonneg A)
  apply (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg (Y' - Y)))).mpr
  intro z
  simp only [ContinuousMap.sub_apply,
    diskProfile_apply I hε hR hs hs1 A c σ hK k hY.le z,
    diskProfile_apply I hε hR hs hs1 A c σ hK k hY'.le z]
  apply (convex_Ioo (-R) R).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun y => complexProfile I ε A (k + 1) y z)
    (fun y hy => (complexProfile_hasDerivAt_Y I hε hR hs hs1 A k
      (abs_lt.mpr hy) (hK z.2)).hasDerivWithinAt)
    (fun y hy => complexProfile_bound I hε hR hs hs1 A (k + 1)
      (abs_lt.mpr hy).le (hK z.2).2.le)
    (abs_lt.mp hY) (abs_lt.mp hY')

theorem diskProfile_continuousOn (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (k : ℕ) : ContinuousOn (diskProfile I ε A c σ k) (Ioo (-R) R) := by
  let B : NNReal := ⟨(2 * jetConstant R s (k + 1)) * ‖A‖,
    mul_nonneg (mul_nonneg (by norm_num) (jetConstant_nonneg hR hs hs1 _)) (norm_nonneg A)⟩
  have hLip : LipschitzOnWith B (diskProfile I ε A c σ k) (Ioo (-R) R) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro Y hY Y' hY'
    exact diskProfile_norm_sub_le I hε hR hs hs1 A c σ hK k
      (abs_lt.mpr hY') (abs_lt.mpr hY)
  exact hLip.continuousOn

/-- The derivative in the disk supremum norm is the already constructed
next radial derivative, with no regularity assumption on the output family. -/
theorem diskProfile_hasDerivAt (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (k : ℕ) {Y : ℝ} (hY : |Y| < R) :
    HasDerivAt (diskProfile I ε A c σ k) (diskProfile I ε A c σ (k + 1) Y) Y := by
  apply hasDerivAt_compactFamily isOpen_Ioo _ _
    (diskProfile_continuousOn I hε hR hs hs1 A c σ hK (k + 1)) _ (abs_lt.mp hY)
  intro y hy z
  have hy' : |y| < R := abs_lt.mpr hy
  rw [diskProfile_apply I hε hR hs hs1 A c σ hK (k + 1) hy'.le z]
  apply (complexProfile_hasDerivAt_Y I hε hR hs hs1 A k hy' (hK z.2)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hy] with q hq
  exact diskProfile_apply I hε hR hs hs1 A c σ hK k (abs_lt.mpr hq).le z

theorem diskProfile_contDiffOn_nat (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (n : ℕ) : ∀ k : ℕ, ContDiffOn ℝ n (diskProfile I ε A c σ k) (Ioo (-R) R) := by
  induction n with
  | zero =>
    intro k
    exact contDiffOn_zero.mpr (diskProfile_continuousOn I hε hR hs hs1 A c σ hK k)
  | succ n ih =>
    intro k
    have hd (y : ℝ) (hy : y ∈ Ioo (-R) R) :=
      diskProfile_hasDerivAt I hε hR hs hs1 A c σ hK k (abs_lt.mpr hy)
    have hout : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1)
        (diskProfile I ε A c σ k) (Ioo (-R) R) := by
      apply (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).mpr
      refine ⟨fun y hy => (hd y hy).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · simp
      · exact (ih (k + 1)).congr (fun y hy => (hd y hy).deriv)
    simpa only [Nat.cast_add, Nat.cast_one] using hout

theorem diskProfile_contDiffOn (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (k : ℕ) : ContDiffOn ℝ ∞ (diskProfile I ε A c σ k) (Ioo (-R) R) := by
  apply contDiffOn_infty.mpr
  intro n
  exact diskProfile_contDiffOn_nat I hε hR hs hs1 A c σ hK n k

/-- Genuine joint real smoothness of every radial jet of the holomorphic axis
profile on the same radial interval and the same parameter strip. -/
theorem complexProfile_joint_smooth (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => complexProfile I ε A k p.1 p.2)
      (Ioo (-R) R ×ˢ parameterStrip I (ε * (1 - s))) := by
  intro p hp
  obtain ⟨σ, hσ, hK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((parameterStrip_isOpen I (ε * (1 - s))).mem_nhds hp.2)
  have hlocal := HolomorphicFamily.contDiffOn_of_disk_family p.2 hσ
    (diskProfile I ε A p.2 σ k) (complexProfile I ε A k)
    (diskProfile_contDiffOn I hε hR hs hs1 A p.2 σ hK k)
    (fun y hy => (complexProfile_analytic I hε hR hs hs1 A k (abs_lt.mpr
        hy).le).differentiableOn.mono
      (ball_subset_closedBall.trans hK))
    (fun y hy z => diskProfile_apply I hε hR hs hs1 A p.2 σ hK k (abs_lt.mpr hy).le z)
  exact (hlocal.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds
    ⟨hp.1, mem_ball_self hσ⟩)).contDiffWithinAt

/-- Every tube contained in the constructed strip inherits joint smoothness. -/
theorem complexProfile_joint_smooth_tube (I J : Window) {ε R s δ : ℝ}
    (hε : 0 < ε) (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1)
    (htube : parameterTube J δ ⊆ parameterStrip I (ε * (1 - s)))
    (A : AxisSpace I ε) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => complexProfile I ε A k p.1 p.2)
      (Ioo (-R) R ×ˢ parameterTube J δ) :=
  (complexProfile_joint_smooth I hε hR hs hs1 A k).mono
    (Set.prod_mono Subset.rfl htube)

/-- The jointly smooth extension is exactly the original real radial jet on
the real slice, rather than a separately selected continuation. -/
theorem complexProfile_joint_real_agreement (I : Window) (ε : ℝ)
    (A : AxisSpace I ε) (k : ℕ) (Y x : ℝ) :
    complexProfile I ε A k Y (x : ℂ) = (mixedSeries I ε A k 0 (Y, x) : ℂ) :=
  complexProfile_ofReal I ε A k Y x

theorem complexProfile_joint_zero_real_agreement (I : Window) (ε : ℝ)
    (A : AxisSpace I ε) (Y x : ℝ) :
    complexProfile I ε A 0 Y (x : ℂ) = (profile I ε A (Y, x) : ℂ) :=
  complexProfile_zero_ofReal I ε A Y x

/-- A common positive tube and a genuine open radial neighborhood work for
every coefficient vector and every radial derivative order. The extension is
jointly real smooth, holomorphic in the complex parameter, uniformly bounded,
and agrees with all actual real parameter jets. -/
theorem exists_common_joint_extension (I J : Window) (hleft : I.left < J.left)
    (hright : J.right < I.right) {ε R : ℝ} (hε : 0 < ε) (hR20 : R < 20) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ S : ℝ, R < S ∧ S < 20 ∧ ∃ B : ℕ → ℝ,
      (∀ k, 0 ≤ B k) ∧ ∀ (A : AxisSpace I ε) (k : ℕ),
        ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => complexProfile I ε A k p.1 p.2)
          (Ioo (-S) S ×ˢ parameterTube J δ) ∧
        ∀ Y : ℝ, |Y| ≤ R →
          AnalyticOnNhd ℂ (complexProfile I ε A k Y) (parameterTube J δ) ∧
          (∀ z ∈ parameterTube J δ, ‖complexProfile I ε A k Y z‖ ≤ B k * ‖A‖) ∧
          (∀ z ∈ parameterTube J δ,
            iteratedDeriv k (fun y => complexProfile I ε A 0 y z) Y =
              complexProfile I ε A k Y z) ∧
          (∀ (m : ℕ) (x : ℝ), x ∈ J.interval →
            iteratedDeriv m (complexProfile I ε A k Y) (x : ℂ) =
              (mixedSeries I ε A k m (Y, x) : ℂ)) := by
  obtain ⟨S, hS, hS20⟩ := exists_between (max_lt (by norm_num : (1 : ℝ) < 20) hR20)
  have hS1 : 1 ≤ S := (le_max_left 1 R).trans hS.le
  have hRS : R < S := (le_max_right 1 R).trans_lt hS
  obtain ⟨s, hs, hs1⟩ := exists_between (show S / 20 < 1 by linarith)
  have ha : 0 < ε * (1 - s) := mul_pos hε (by linarith)
  obtain ⟨δ, hδ, htube⟩ := exists_parameterTube_subset I J hleft hright ha
  refine ⟨δ, hδ, S, hRS, hS20, (fun k => 2 * jetConstant S s k), ?_, ?_⟩
  · intro k
    exact mul_nonneg (by norm_num) (jetConstant_nonneg hS1 hs hs1 k)
  · intro A k
    refine ⟨complexProfile_joint_smooth_tube I J hε hS1 hs hs1 htube A k, ?_⟩
    intro Y hY
    have hYS : |Y| < S := hY.trans_lt hRS
    refine ⟨(complexProfile_analytic I hε hS1 hs hs1 A k hYS.le).mono htube, ?_, ?_, ?_⟩
    · intro z hz
      exact complexProfile_bound I hε hS1 hs hs1 A k hYS.le (htube hz).2.le
    · intro z hz
      simpa only [Nat.zero_add] using
        complexProfile_iteratedDeriv_Y I hε hS1 hs hs1 A 0 k hYS (htube hz)
    · intro m x hx
      exact complexProfile_iteratedDeriv_ofReal I hε hS1 hs hs1 A k m hYS.le
        ⟨hleft.trans_le hx.1, hx.2.trans_lt hright⟩

end NavierStokes.AxisHolomorphicJoint

end
end

end

section

/-!
# A common holomorphic parameter neighborhood through initial activation

All continuations below are explicit integrals of the actual natural slopes.
The complex neighborhood is obtained from compactness and real positivity.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActivationHolomorphic

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

/-- C point: an abbreviation for `ℝ × ℂ`. -/
abbrev CPoint := ℝ × ℂ
/-- C field: an abbreviation for `CPoint → ℂ`. -/
abbrev CField := CPoint → ℂ

/-- Radial, given by `deriv (fun x => F (x, p.2)) p.1`. -/
def radial (F : CField) (p : CPoint) : ℂ := deriv (fun x => F (x, p.2)) p.1

/-- Joint real smoothness and actual holomorphic parameter slices. -/
structure Regular (S : Set ℝ) (Ω : Set ℂ) (F : CField) : Prop where
  smooth : ContDiffOn ℝ ∞ F (S ×ˢ Ω)
  holomorphic : ∀ x ∈ S, DifferentiableOn ℂ (fun z => F (x, z)) Ω

theorem radial_smooth {S : Set ℝ} {Ω : Set ℂ} (hS : IsOpen S) (hΩ : IsOpen Ω)
    {F : CField} (hF : ContDiffOn ℝ ∞ F (S ×ˢ Ω)) :
    ContDiffOn ℝ ∞ (radial F) (S ×ˢ Ω) := by
  intro p hp
  have hbase := hF.contDiffAt ((hS.prod hΩ).mem_nhds hp)
  have hG : ContDiffAt ℝ ∞ (fun w : CPoint × ℝ => F (w.2, w.1.2)) (p, p.1) :=
    hbase.comp (p, p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact ((hG.fderiv contDiffAt_fst (by simp)).clm_apply contDiffAt_const).contDiffWithinAt

/-- Radial differentiation preserves holomorphy on an arbitrary open radial
domain. The difference quotients converge uniformly on each compact disk. -/
theorem radial_holomorphic {S : Set ℝ} {Ω : Set ℂ} (hS : IsOpen S) (hΩ : IsOpen Ω)
    {F : CField} (hF : ContDiffOn ℝ ∞ F (S ×ˢ Ω))
    (hhol : ∀ r ∈ S, DifferentiableOn ℂ (fun z => F (r, z)) Ω)
    {r : ℝ} (hr : r ∈ S) : DifferentiableOn ℂ (fun z => radial F (r, z)) Ω := by
  intro z hz
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz)
  let σ := ε / 2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hDisk : closedBall z σ ⊆ Ω :=
    (closedBall_subset_ball (by dsimp [σ]; linarith : σ < ε)).trans hεsub
  let V : ℝ → C(CauchyRestriction.Disk z σ, ℂ) :=
    CompactSmoothFamily.family (closedBall z σ) F
  have hV : ContDiffOn ℝ ∞ V S :=
    CompactSmoothFamily.contDiffOn_family_of_joint (closedBall z σ) S Ω
      hS hΩ hDisk F hF
  have hval (s : ℝ) (hs : s ∈ S) (w : CauchyRestriction.Disk z σ) : V s w = F (s, w) :=
    CompactSmoothFamily.family_apply_of_joint (closedBall z σ) hDisk F hF.continuousOn hs w
  have hd : HasDerivAt V (deriv V r) r :=
    (hV.contDiffAt (hS.mem_nhds hr)).differentiableAt (by simp) |>.hasDerivAt
  have hderiv (w : CauchyRestriction.Disk z σ) : deriv V r w = radial F (r, w) := by
    have he := (ContinuousMap.evalCLM ℝ w).hasFDerivAt.comp_hasDerivAt r hd
    have heq : (fun s => V s w) =ᶠ[𝓝 r] (fun s => F (s, w)) := by
      filter_upwards [hS.mem_nhds hr] with s hs
      exact hval s hs w
    exact (he.congr_of_eventuallyEq heq.symm).deriv.symm
  let Q : ℝ → ℂ → ℂ := fun t w => t⁻¹ • (F (r + t, w) - F (r, w))
  have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), r + t ∈ S := by
    exact
      (continuousAt_const.fun_add continuousAt_id : ContinuousAt (fun t : ℝ => r + t) 0).eventually
        (hS.mem_nhds (by simpa only [add_zero] using hr))
  have hlim : TendstoUniformlyOn Q (fun w => radial F (r, w)) (𝓝[≠] (0 : ℝ)) (ball z σ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have ht := Metric.tendsto_nhds.mp hd.tendsto_slope_zero δ hδ
    filter_upwards [ht, hnear.filter_mono nhdsWithin_le_nhds] with t ht htr
    intro w hw
    let w' : CauchyRestriction.Disk z σ := ⟨w, ball_subset_closedBall hw⟩
    have hb := (deriv V r - t⁻¹ • (V (r + t) - V r)).norm_coe_le_norm w'
    have hn : ‖radial F (r, w) - Q t w‖ ≤
        ‖deriv V r - t⁻¹ • (V (r + t) - V r)‖ := by
      simpa only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, hderiv,
        hval (r + t) htr, hval r hr, Q, w'] using hb
    rw [dist_eq_norm]
    apply hn.trans_lt
    simpa only [dist_eq_norm, norm_sub_rev] using ht
  have hQ : ∀ᶠ t in 𝓝[≠] (0 : ℝ), DifferentiableOn ℂ (Q t) (ball z σ) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with t ht
    exact (((hhol (r + t) ht).sub (hhol r hr)).const_smul t⁻¹).mono
      (ball_subset_closedBall.trans hDisk)
  have hdiff := hlim.tendstoLocallyUniformlyOn.differentiableOn hQ isOpen_ball
  exact (hdiff.differentiableAt (Metric.ball_mem_nhds z hσ)).differentiableWithinAt

theorem Regular.radial {S : Set ℝ} {Ω : Set ℂ} {F : CField}
    (hF : Regular S Ω F) (hS : IsOpen S) (hΩ : IsOpen Ω) : Regular S Ω (radial F) :=
  ⟨radial_smooth hS hΩ hF.smooth, fun _ hr => radial_holomorphic hS hΩ hF.smooth hF.holomorphic hr⟩

theorem Regular.mono {S S' : Set ℝ} {Ω Ω' : Set ℂ} {F : CField}
    (hF : Regular S Ω F) (hS : S' ⊆ S) (hΩ : Ω' ⊆ Ω) : Regular S' Ω' F :=
  ⟨hF.smooth.mono (Set.prod_mono hS hΩ), fun _ hx => (hF.holomorphic _ (hS hx)).mono hΩ⟩

theorem regular_const (S : Set ℝ) (Ω : Set ℂ) (c : ℂ) : Regular S Ω (fun _ => c) :=
  ⟨contDiffOn_const, fun _ _ => differentiableOn_const c⟩

theorem Regular.add {S : Set ℝ} {Ω : Set ℂ} {F G : CField}
    (hF : Regular S Ω F) (hG : Regular S Ω G) : Regular S Ω (fun p => F p + G p) :=
  ⟨hF.smooth.add hG.smooth, fun x hx => (hF.holomorphic x hx).add (hG.holomorphic x hx)⟩

theorem Regular.mul {S : Set ℝ} {Ω : Set ℂ} {F G : CField}
    (hF : Regular S Ω F) (hG : Regular S Ω G) : Regular S Ω (fun p => F p * G p) :=
  ⟨hF.smooth.mul hG.smooth, fun x hx => (hF.holomorphic x hx).mul (hG.holomorphic x hx)⟩

theorem Regular.cexp {S : Set ℝ} {Ω : Set ℂ} {F : CField} (hF : Regular S Ω F) :
    Regular S Ω (fun p => Complex.exp (F p)) :=
  ⟨((Complex.contDiff_exp : ContDiff ℂ ∞ Complex.exp).restrict_scalars ℝ).comp_contDiffOn hF.smooth,
    fun x hx => (hF.holomorphic x hx).cexp⟩

theorem Regular.clog {S : Set ℝ} {Ω : Set ℂ} {F : CField}
    (hF : Regular S Ω F) (hne : ∀ p ∈ S ×ˢ Ω, F p ∈ Complex.slitPlane) :
    Regular S Ω (fun p => Complex.log (F p)) := by
  constructor
  · intro p hp
    exact ((Complex.contDiffAt_log (hne p hp)).restrict_scalars ℝ |>.comp_contDiffWithinAt p
      (hF.smooth p hp))
  · intro x hx z hz
    exact ((hF.holomorphic x hx z hz).clog (hne (x,z) ⟨hx,hz⟩))

theorem regular_parameter {S : Set ℝ} {Ω : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Ω) : Regular S Ω (fun p => g p.2) :=
  ⟨(hg.contDiffOn_of_completeSpace.restrict_scalars ℝ).comp contDiffOn_snd (fun _ hp => hp.2),
    fun _ _ => hg.differentiableOn⟩

theorem regular_radius {S : Set ℝ} {Ω : Set ℂ} {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g S) :
    Regular S Ω (fun p => (g p.1 : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp_contDiffOn (hg.comp contDiffOn_fst (fun _ hp => hp.1)),
    fun x _ => by
      change DifferentiableOn ℂ (fun _ : ℂ => (g x : ℂ)) Ω
      exact differentiableOn_const _⟩

section CompactIntegral

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    {s : Set H} {G : H × ℝ → ℂ}

theorem compact_integral_smooth (hs : IsOpen s)
    (hG : ∀ p ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ G (p, t)) :
    ContDiffOn ℝ ∞ (fun p => ∫ t in (0 : ℝ)..1, G (p,t)) s := by
  apply SmoothParameterIntegral.contDiffOn_intervalIntegral_of_continuous_jet hs zero_le_one
  · intro t ht p hp
    exact ((hG p hp t ht).comp p (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  · intro k
    rintro ⟨p,t⟩ ⟨hp,ht⟩
    have hflip : ContDiffAt ℝ ∞ (Function.uncurry (fun t p => G (p,t))) (t,p) :=
      (hG p hp t ht).comp (t,p) (contDiffAt_snd.prodMk contDiffAt_fst)
    have hd := ParametricFlatFactor.contDiffAt_partial_iteratedFDeriv (fun t p => G (p,t)) k t p
        hflip
    exact ((hd.comp (p,t) (contDiffAt_snd.prodMk contDiffAt_fst)).continuousAt).continuousWithinAt

end CompactIntegral

/-- Segment: an abbreviation for `↥(Icc (0 : ℝ) 1)`. -/
abbrev Segment := ↥(Icc (0 : ℝ) 1)

/-- Segment extend, given by `f (projIcc 0 1 zero_le_one t)`. -/
def segmentExtend (f : C(Segment, ℂ)) (t : ℝ) : ℂ :=
  f (projIcc 0 1 zero_le_one t)

theorem segmentExtend_continuous (f : C(Segment, ℂ)) : Continuous (segmentExtend f) :=
  f.continuous.comp continuous_projIcc

theorem segmentIntegral_norm (f : C(Segment, ℂ)) :
    ‖∫ t in (0 : ℝ)..1, segmentExtend f t‖ ≤ 1 * ‖f‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := segmentExtend f)
    (fun t _ => f.norm_coe_le_norm (projIcc 0 1 zero_le_one t))
  simpa only [sub_zero, abs_one, mul_one, one_mul] using h

/-- Segment integral, constructed using `LinearMap.mkContinuous`. -/
noncomputable def segmentIntegral : C(Segment, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous {
    toFun f := ∫ t in (0 : ℝ)..1, segmentExtend f t
    map_add' := by
      intro f g
      exact intervalIntegral.integral_add
        ((segmentExtend_continuous f).intervalIntegrable 0 1)
        ((segmentExtend_continuous g).intervalIntegrable 0 1)
    map_smul' := by
      intro c f
      exact intervalIntegral.integral_smul c (segmentExtend f)
  } 1 segmentIntegral_norm

/-- Holomorphic integration only requires smoothness near the actual compact
integration segment, with no assumptions outside that segment. -/
theorem compact_integral_holomorphic {Ω : Set ℂ} (hΩ : IsOpen Ω) {G : ℂ × ℝ → ℂ}
    (hG : ∀ z ∈ Ω, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ G (z, t))
    (hhol : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => G (z, t)) Ω) :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..1, G (z,t)) Ω := by
  let K : Set ℝ := Icc 0 1
  let D : ℂ × ℝ → ℂ →L[ℝ] ℂ := fun p => fderiv ℝ (fun z => G (z,p.2)) p.1
  have hGc : ContinuousOn G (Ω ×ˢ K) := by
    rintro ⟨z,t⟩ ⟨hz,ht⟩
    exact (hG z hz t ht).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Ω ×ˢ K) := by
    rintro ⟨z,t⟩ ⟨hz,ht⟩
    have hdup : ContDiffAt ℝ ∞ (fun w : (ℂ × ℝ) × ℂ => G (w.2,w.1.2)) ((z,t),z) :=
      (hG z hz t ht).comp ((z,t),z) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
    have hD : ContDiffAt ℝ ∞ D (z,t) := hdup.fderiv contDiffAt_fst (by simp)
    exact hD.continuousAt.continuousWithinAt
  have hf : DifferentiableOn ℂ (CompactSmoothFamily.family K G) Ω := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply HolomorphicFamily.differentiableAt_of_evaluations (CompactSmoothFamily.family K G)
    · exact (CompactSmoothFamily.hasFDerivAt_family K hΩ G D hGc hDc
        (fun z hz t => ((hG z hz t t.2).comp z
          (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by
              simp) |>.hasFDerivAt) hz).differentiableAt
    · intro t
      apply ((hhol t t.2).differentiableAt (hΩ.mem_nhds hz)).congr_of_eventuallyEq
      filter_upwards [hΩ.mem_nhds hz] with w hw
      exact CompactSmoothFamily.family_apply K G w
        (CompactSmoothFamily.slice_continuous hGc hw) t
  have hi := (segmentIntegral : C(Segment, ℂ) →L[ℂ] ℂ).differentiable.comp_differentiableOn hf
  apply hi.congr
  intro z hz
  change (∫ t in (0 : ℝ)..1, G (z,t)) = ∫ t in (0 : ℝ)..1,
    segmentExtend (CompactSmoothFamily.family K G z) t
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ K := by simpa only [K,uIcc_of_le zero_le_one] using ht
  rw [segmentExtend,projIcc_of_mem zero_le_one ht']
  exact (CompactSmoothFamily.family_apply K G z
    (CompactSmoothFamily.slice_continuous hGc hz) ⟨t,ht'⟩).symm

/-- Average, given by `∫ t in (0 : ℝ)..1, F (t*p.1,p.2)`. -/
def average (F : CField) (p : CPoint) : ℂ := ∫ t in (0 : ℝ)..1, F (t*p.1,p.2)
/-- Primitive, given by `∫ x in (0 : ℝ)..p.1, F (x,p.2)`. -/
def primitive (F : CField) (p : CPoint) : ℂ := ∫ x in (0 : ℝ)..p.1, F (x,p.2)

theorem primitive_eq_mul_average (F : CField) (p : CPoint) :
    primitive F p = (p.1 : ℂ) * average F p := by
  have he := intervalIntegral.smul_integral_comp_mul_left (fun x => F (x,p.2)) p.1 (a := 0) (b := 1)
  simpa only [primitive,average,mul_zero,mul_one,Complex.real_smul,mul_comm] using he.symm

theorem Regular.average {S : Set ℝ} {Ω : Set ℂ} {F : CField}
    (hF : Regular S Ω F) (hS : IsOpen S) (hΩ : IsOpen Ω)
    (hscale : ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, t * x ∈ S) : Regular S Ω (average F) := by
  constructor
  · unfold ActivationHolomorphic.average
    apply compact_integral_smooth (G := fun q : CPoint × ℝ => F (q.2*q.1.1,q.1.2)) (hS.prod hΩ)
    intro p hp t ht
    have hb : ContDiffAt ℝ ∞ F (t*p.1,p.2) :=
      hF.smooth.contDiffAt ((hS.prod hΩ).mem_nhds ⟨hscale p.1 hp.1 t ht,hp.2⟩)
    exact hb.comp (p,t) ((contDiffAt_snd.mul contDiffAt_fst.fst).prodMk contDiffAt_fst.snd)
  · intro x hx
    unfold ActivationHolomorphic.average
    apply compact_integral_holomorphic (G := fun q : ℂ × ℝ => F (q.2*x,q.1)) hΩ
    · intro z hz t ht
      have hb : ContDiffAt ℝ ∞ F (t*x,z) :=
        hF.smooth.contDiffAt ((hS.prod hΩ).mem_nhds ⟨hscale x hx t ht,hz⟩)
      exact hb.comp (z,t) ((contDiffAt_snd.mul contDiffAt_const).prodMk contDiffAt_fst)
    · intro t ht
      exact hF.holomorphic (t*x) (hscale x hx t ht)

theorem Regular.primitive {S : Set ℝ} {Ω : Set ℂ} {F : CField}
    (hF : Regular S Ω F) (hS : IsOpen S) (hΩ : IsOpen Ω)
    (hscale : ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, t * x ∈ S) : Regular S Ω (primitive F) := by
  have hb := (regular_radius (Ω := Ω) (contDiffOn_id : ContDiffOn ℝ ∞ id S)).mul (hF.average hS hΩ
      hscale)
  have he : ActivationHolomorphic.primitive F =
      (fun p => (p.1 : ℂ) * ActivationHolomorphic.average F p) := funext (primitive_eq_mul_average
          F)
  rw [he]
  exact hb

theorem radial_hasDerivAt {S : Set ℝ} {Ω : Set ℂ} {F : CField}
    (hS : IsOpen S) (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ ∞ F (S ×ˢ Ω))
    {p : CPoint} (hp : p ∈ S ×ˢ Ω) :
    HasDerivAt (fun x => F (x,p.2)) (radial F p) p.1 :=
  (((hF.contDiffAt ((hS.prod hΩ).mem_nhds hp)).comp p.1
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)).hasDerivAt

theorem slice_continuous {Ω : Set ℂ} {F : CField} (hΩ : IsOpen Ω)
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ω)) {z : ℂ} (hz : z ∈ Ω) :
    Continuous (fun x => F (x,z)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ((hF.contDiffAt ((isOpen_univ.prod hΩ).mem_nhds ⟨mem_univ _,hz⟩)).comp x
    (contDiffAt_id.prodMk contDiffAt_const)).continuousAt

theorem primitive_hasDerivAt {Ω : Set ℂ} {F : CField} (hΩ : IsOpen Ω)
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ω)) {p : CPoint} (hp : p.2 ∈ Ω) :
    HasDerivAt (fun x => primitive F (x,p.2)) (F p) p.1 := by
  have hc := slice_continuous hΩ hF hp
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 p.1)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- Damped slope, given by `(ReferencePath.slopeCutoff δ p.1 : ℂ) * radial G p`. -/
def dampedSlope (δ : ℝ) (G : CField) (p : CPoint) : ℂ :=
  (ReferencePath.slopeCutoff δ p.1 : ℂ) * radial G p

/-- Continuation, given by `G (0,p.2) + primitive (dampedSlope δ G) p`. -/
def continuation (δ : ℝ) (G : CField) (p : CPoint) : ℂ :=
  G (0,p.2) + primitive (dampedSlope δ G) p

theorem regular_dampedSlope {T δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < T)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {G : CField} (hG : Regular (Iio T) Ω G) :
    Regular univ Ω (dampedSlope δ G) := by
  have hD := hG.radial isOpen_Iio hΩ
  constructor
  · intro p hp
    by_cases ht : p.1 < T
    · exact (((Complex.ofRealCLM.contDiff.comp (ReferencePath.slopeCutoff_smooth δ)).comp
        contDiff_fst).contDiffAt.mul
          (hD.smooth.contDiffAt ((isOpen_Iio.prod hΩ).mem_nhds ⟨ht,hp.2⟩))).contDiffWithinAt
    · have hfar : 2*δ < p.1 := hδT.trans_le (le_of_not_gt ht)
      have heq : dampedSlope δ G =ᶠ[𝓝 p] (fun _ => 0) := by
        filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hfar)] with q hq
        simp only [dampedSlope,ReferencePath.slopeCutoff_zero hδ hq.le,Complex.ofReal_zero,zero_mul]
      exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt
  · intro x _
    by_cases ht : x < T
    · change DifferentiableOn ℂ (fun z => (ReferencePath.slopeCutoff δ x : ℂ) * radial G (x,z)) Ω
      exact (differentiableOn_const _).mul (hD.holomorphic x ht)
    · have hzero : (fun z => dampedSlope δ G (x,z)) = (fun _ => 0) := by
        funext z
        simp [dampedSlope,ReferencePath.slopeCutoff_zero hδ (hδT.le.trans (le_of_not_gt ht))]
      rw [hzero]
      exact differentiableOn_const _

theorem regular_continuation {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : 2 * δ < T)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {G : CField} (hG : Regular (Iio T) Ω G) :
    Regular univ Ω (continuation δ G) := by
  have hi := (regular_dampedSlope hδ hδT hΩ hG).primitive isOpen_univ hΩ (by intros; trivial)
  have hzero : Regular univ Ω (fun p => G (0,p.2)) := by
    constructor
    · exact hG.smooth.comp (contDiff_const.prodMk contDiff_snd).contDiffOn
        (fun _ hp => ⟨hT,hp.2⟩)
    · intro _ _
      exact hG.holomorphic 0 hT
  exact hzero.add hi

theorem continuation_hasDerivAt {T δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < T)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {G : CField} (hG : Regular (Iio T) Ω G)
    {p : CPoint} (hp : p.2 ∈ Ω) :
    HasDerivAt (fun x => continuation δ G (x,p.2)) (dampedSlope δ G p) p.1 := by
  unfold continuation
  simpa only [zero_add] using (hasDerivAt_const p.1 (G (0,p.2))).fun_add
    (primitive_hasDerivAt hΩ (regular_dampedSlope hδ hδT hΩ hG).smooth hp)

theorem continuation_eq_initial {T δ : ℝ} (_ : 0 < T) (hδ : 0 < δ) (hδT : 2 * δ < T)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {G : CField} (hG : Regular (Iio T) Ω G)
    {p : CPoint} (hp : p.2 ∈ Ω) (hx : p.1 ≤ δ) : continuation δ G p = G p := by
  have hd : ∀ t ∈ uIcc 0 p.1,
      HasDerivAt (fun x => G (x,p.2)) (dampedSlope δ G (t,p.2)) t := by
    intro t ht
    have htδ : t ≤ δ := (mem_uIcc.mp ht).elim (fun h => h.2.trans hx) (fun h => h.2.trans hδ.le)
    have htT : t < T := by linarith
    simpa only [dampedSlope,ReferencePath.slopeCutoff_one hδ htδ,Complex.ofReal_one,one_mul] using
      radial_hasDerivAt isOpen_Iio hΩ hG.smooth (p := (t,p.2)) ⟨htT,hp⟩
  have hc := slice_continuous hΩ (regular_dampedSlope hδ hδT hΩ hG).smooth hp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 p.1)
  change G (0,p.2) + _ = _
  rw [show primitive (dampedSlope δ G) p = G p-G (0,p.2) from hi]
  ring

/-- Controlled, given by `G (0,p.2) + primitive (fun q => (StressActivation.damping T κ q.1 : ℂ)
* radial G q) p`. -/
def controlled (T κ : ℝ) (G : CField) (p : CPoint) : ℂ :=
  G (0,p.2) + primitive (fun q => (StressActivation.damping T κ q.1 : ℂ) * radial G q) p

theorem regular_controlled (T κ : ℝ) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {G : CField} (hG : Regular univ Ω G) : Regular univ Ω (controlled T κ G) := by
  have hD := (regular_radius (StressActivation.damping_smooth T κ).contDiffOn).mul
    (hG.radial isOpen_univ hΩ)
  have hi := hD.primitive isOpen_univ hΩ (by intros; trivial)
  have hzero : Regular univ Ω (fun p => G (0,p.2)) := by
    constructor
    · exact hG.smooth.comp (contDiff_const.prodMk contDiff_snd).contDiffOn (fun _ hp =>
        ⟨trivial,hp.2⟩)
    · intro _ _
      exact hG.holomorphic 0 (mem_univ _)
  exact hzero.add hi

theorem controlled_eq_initial {T : ℝ} (hT : 0 < T) (κ : ℝ) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {G : CField} (hG : Regular univ Ω G) {p : CPoint} (hp : p.2 ∈ Ω) (hx : p.1 ≤ 0) :
    controlled T κ G p = G p := by
  have hd : ∀ t ∈ uIcc 0 p.1, HasDerivAt (fun x => G (x,p.2))
      ((StressActivation.damping T κ t : ℂ) * radial G (t,p.2)) t := by
    intro t ht
    have ht0 : t ≤ 0 := (show t ∈ Icc p.1 0 by simpa only [uIcc_of_ge hx] using ht).2
    simpa only [StressActivation.damping,StressActivation.activation_zero hT κ ht0,sub_zero,
      Complex.ofReal_one,one_mul] using
      radial_hasDerivAt isOpen_univ hΩ hG.smooth (p := (t,p.2)) ⟨trivial,hp⟩
  have hD := (regular_radius (StressActivation.damping_smooth T κ).contDiffOn).mul
    (hG.radial isOpen_univ hΩ)
  have hc := slice_continuous hΩ hD.smooth hp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 p.1)
  change G (0,p.2) + _ = _
  unfold primitive
  rw [hi]
  ring

theorem radial_ofReal {S : Set ℝ} (hS : IsOpen S) {G : CField} {g : ProfileHistories.Field}
    {x η : ℝ} (hx : x ∈ S) (hg : ContDiffAt ℝ ∞ g (x, η))
    (heq : ∀ y ∈ S, G (y, (η : ℂ)) = (g (y, η) : ℂ)) :
    radial G (x,(η : ℂ)) = (ProfileHistories.radialPartial g (x,η) : ℂ) := by
  have he : (fun y => G (y,(η : ℂ))) =ᶠ[𝓝 x] (fun y => (g (y,η) : ℂ)) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact heq y hy
  exact he.deriv_eq.trans (ReferenceJetBounds.radial_deriv hg).ofReal_comp.deriv

theorem continuation_ofReal {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : 2 * δ < T)
    {J : Set ℝ} (hJ : IsOpen J) {G : CField} {g : ProfileHistories.Field}
    (hg : ContDiffOn ℝ ∞ g (Iio T ×ˢ J))
    (heq : ∀ x < T, ∀ η ∈ J, G (x, (η : ℂ)) = (g (x, η) : ℂ))
    (x : ℝ) {η : ℝ} (hη : η ∈ J) :
    continuation δ G (x,(η : ℂ)) = (ReferencePath.continuation δ g (x,η) : ℂ) := by
  have hD (y : ℝ) : dampedSlope δ G (y,(η : ℂ)) = (ReferencePath.dampedSlope δ g (y,η) : ℂ) := by
    by_cases hy : y < T
    · have hd := radial_ofReal isOpen_Iio hy
        (hg.contDiffAt ((isOpen_Iio.prod hJ).mem_nhds ⟨hy,hη⟩)) (fun z hz => heq z hz η hη)
      simp only [dampedSlope,ReferencePath.dampedSlope,hd,Complex.ofReal_mul]
    · have hz := ReferencePath.slopeCutoff_zero hδ (hδT.le.trans (le_of_not_gt hy))
      simp only [dampedSlope,ReferencePath.dampedSlope,hz,Complex.ofReal_zero,zero_mul]
  simp only [continuation, ReferencePath.continuation, primitive, ProfileHistories.primitive,
      Complex.ofReal_add]
  rw [heq 0 hT η hη]
  congr 1
  calc
    _ = ∫ y in (0 : ℝ)..x, (ReferencePath.dampedSlope δ g (y,η) : ℂ) :=
      intervalIntegral.integral_congr (fun y _ => hD y)
    _ = _ := intervalIntegral.integral_ofReal

theorem controlled_ofReal (T κ : ℝ) {J : Set ℝ} (hJ : IsOpen J)
    {G : CField} {g : ProfileHistories.Field} (hg : ContDiffOn ℝ ∞ g (univ ×ˢ J))
    (heq : ∀ x η : ℝ, η ∈ J → G (x,(η : ℂ)) = (g (x,η) : ℂ))
    (x : ℝ) {η : ℝ} (hη : η ∈ J) :
    controlled T κ G (x,(η : ℂ)) = (StressActivation.controlled T κ g (x,η) : ℂ) := by
  have hD (y : ℝ) : radial G (y,(η : ℂ)) = (ProfileHistories.radialPartial g (y,η) : ℂ) :=
    radial_ofReal isOpen_univ (mem_univ _)
      (hg.contDiffAt ((isOpen_univ.prod hJ).mem_nhds ⟨mem_univ _,hη⟩)) (fun z _ => heq z η hη)
  simp only [controlled, StressActivation.controlled, primitive, ProfileHistories.primitive,
      Complex.ofReal_add]
  rw [heq 0 η hη]
  congr 1
  calc
    _ = ∫ y in (0 : ℝ)..x,
        ((StressActivation.damping T κ y * ProfileHistories.radialPartial g (y,η) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro y _
      change (StressActivation.damping T κ y : ℂ) * radial G (y,(η : ℂ)) =
        ((StressActivation.damping T κ y * ProfileHistories.radialPartial g (y,η) : ℝ) : ℂ)
      rw [hD y,Complex.ofReal_mul]
    _ = _ := intervalIntegral.integral_ofReal

/-- Log point, given by `(N.logTime p.1,p.2)`. -/
def logPoint (N : ReferencePath.Input) (p : CPoint) : CPoint := (N.logTime p.1,p.2)
/-- Exp point, given by `(N.endpoint*Real.exp p.1,p.2)`. -/
def expPoint (N : ReferencePath.Input) (p : CPoint) : CPoint := (N.endpoint*Real.exp p.1,p.2)

theorem logPoint_smoothAt (N : ReferencePath.Input) {p : CPoint} (hp : 0 < p.1) :
    ContDiffAt ℝ ∞ (logPoint N) p := by
  have hd : ContDiffAt ℝ ∞ (fun q : CPoint => q.1 / N.endpoint) p :=
    contDiffAt_fst.div_const _
  exact (hd.log (div_pos hp N.endpoint_pos).ne').prodMk contDiffAt_snd

theorem expPoint_smooth (N : ReferencePath.Input) : ContDiff ℝ ∞ (expPoint N) :=
  (contDiff_const.mul contDiff_fst.exp).prodMk contDiff_snd

theorem expPoint_logPoint (N : ReferencePath.Input) {p : CPoint} (hp : 0 < p.1) :
    expPoint N (logPoint N p) = p := by
  apply Prod.ext
  · change N.endpoint * Real.exp (Real.log (p.1/N.endpoint)) = p.1
    rw [Real.exp_log (div_pos hp N.endpoint_pos),mul_div_cancel₀ _ N.endpoint_pos.ne']
  · rfl

/-- Attach, with branches according to `p.1 ≤ N.endpoint`. -/
def attach (N : ReferencePath.Input) (F G : CField) (p : CPoint) : ℂ :=
  if p.1 ≤ N.endpoint then F p else G (logPoint N p)

theorem attach_logPoint (N : ReferencePath.Input) {F G : CField} {Ω : Set ℂ}
    (heq : ∀ p : CPoint, 0 < p.1 → p.1 ≤ N.endpoint → p.2 ∈ Ω → G (logPoint N p) = F p)
    {p : CPoint} (hp : 0 < p.1) (hz : p.2 ∈ Ω) : attach N F G p = G (logPoint N p) := by
  by_cases hx : p.1 ≤ N.endpoint
  · exact (ite_eq_left hx).trans (heq p hp hx hz).symm
  · exact ite_eq_right hx

theorem regular_attach (N : ReferencePath.Input) {R : ℝ} (hR : 0 < R) (hXR : N.endpoint < R)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F G : CField}
    (hF : Regular (Ioo (-R) R) Ω F) (hG : Regular univ Ω G)
    (heq : ∀ p : CPoint, 0 < p.1 → p.1 ≤ N.endpoint → p.2 ∈ Ω → G (logPoint N p) = F p) :
    Regular (Ioi (-R)) Ω (attach N F G) := by
  constructor
  · intro p hp
    by_cases hx : 0 < p.1
    · have hb : ContDiffAt ℝ ∞ G (logPoint N p) :=
        hG.smooth.contDiffAt ((isOpen_univ.prod hΩ).mem_nhds ⟨mem_univ _,hp.2⟩)
      have hs := hb.comp p (logPoint_smoothAt N hx)
      have hlocal : attach N F G =ᶠ[𝓝 p] (fun q => G (logPoint N q)) := by
        filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hx),
          continuousAt_snd.eventually (hΩ.mem_nhds hp.2)] with q hq hz
        exact attach_logPoint N heq hq hz
      exact (hs.congr_of_eventuallyEq hlocal).contDiffWithinAt
    · have hbefore : p.1 < N.endpoint := (le_of_not_gt hx).trans_lt N.endpoint_pos
      have hFp : ContDiffAt ℝ ∞ F p := hF.smooth.contDiffAt ((isOpen_Ioo.prod hΩ).mem_nhds
        ⟨⟨hp.1,lt_of_le_of_lt (le_of_not_gt hx) hR⟩,hp.2⟩)
      have hlocal : attach N F G =ᶠ[𝓝 p] F := by
        filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hbefore)] with q hq
        exact ite_eq_left hq.le
      exact (hFp.congr_of_eventuallyEq hlocal).contDiffWithinAt
  · intro x hx
    by_cases hxe : x ≤ N.endpoint
    · have hf := hF.holomorphic x ⟨hx,hxe.trans_lt hXR⟩
      simpa only [attach,ite_eq_left hxe] using hf
    · have hg := hG.holomorphic (N.logTime x) (mem_univ _)
      simpa only [attach,ite_eq_right hxe,logPoint] using hg

/-- An explicit natural extension, including the positivity neighborhood
needed by the logarithm. It is constructed from the coefficient series below. -/
structure NaturalExtension (N : ReferencePath.Input) (Ω : Set ℂ) (R : ℝ) where
  radius_pos : 0 < R
  endpoint_lt : N.endpoint < R
  /-- F of `NaturalExtension`, of type `CField`. -/
  f : CField
  /-- U of `NaturalExtension`, of type `CField`. -/
  U : CField
  f_regular : Regular (Ioo (-R) R) Ω f
  U_regular : Regular (Ioo (-R) R) Ω U
  f_real : ∀ x η : ℝ, f (x,(η : ℂ)) = (N.f (x,η) : ℂ)
  U_real : ∀ x η : ℝ, U (x,(η : ℂ)) = (N.U (x,η) : ℂ)
  exp_mem : ∀ t < ReferencePath.rampLimit, N.endpoint*Real.exp t ∈ Ioo (-R) R
  right_half : ∀ t < ReferencePath.rampLimit, ∀ z ∈ Ω, 0 < (f (N.endpoint*Real.exp t,z)).re
  initial_half : ∀ x ∈ Icc (0 : ℝ) N.endpoint, ∀ z ∈ Ω, 0 < (f (x,z)).re

namespace NaturalExtension

variable {N : ReferencePath.Input} {Ω : Set ℂ} {R : ℝ} (E : NaturalExtension N Ω R)

/-- Log F, defined pointwise by `Complex.log (E.f (expPoint N p))`. -/
def logF : CField := fun p => Complex.log (E.f (expPoint N p))
/-- Log U, defined pointwise by `E.U (expPoint N p)`. -/
def logU : CField := fun p => E.U (expPoint N p)

theorem logF_regular : Regular (Iio ReferencePath.rampLimit) Ω E.logF := by
  have hb : Regular (Iio ReferencePath.rampLimit) Ω (fun p => E.f (expPoint N p)) := by
    constructor
    · exact E.f_regular.smooth.comp (expPoint_smooth N).contDiffOn
        (fun p hp => ⟨E.exp_mem p.1 hp.1,hp.2⟩)
    · intro t ht
      exact E.f_regular.holomorphic _ (E.exp_mem t ht)
  exact hb.clog (fun p hp => Or.inl (E.right_half p.1 hp.1 p.2 hp.2))

theorem logU_regular : Regular (Iio ReferencePath.rampLimit) Ω E.logU := by
  constructor
  · exact E.U_regular.smooth.comp (expPoint_smooth N).contDiffOn
      (fun p hp => ⟨E.exp_mem p.1 hp.1,hp.2⟩)
  · intro t ht
    exact E.U_regular.holomorphic _ (E.exp_mem t ht)

theorem logF_real {t η : ℝ} (ht : t < ReferencePath.rampLimit)
    (hη : η ∈ ReferencePath.parameterInterval) :
    E.logF (t,(η : ℂ)) = (N.logF (t,η) : ℂ) := by
  change Complex.log (E.f (N.endpoint*Real.exp t,(η : ℂ))) = _
  rw [E.f_real]
  exact (Complex.ofReal_log (N.fromLog_f_pos (p := (t,η)) ⟨ht,hη⟩).le).symm

theorem logU_real (t η : ℝ) : E.logU (t,(η : ℂ)) = (N.logU (t,η) : ℂ) := E.U_real _ _

/-- Ref log, given by `continuation δ E.logF`. -/
def refLog (δ : ℝ) : CField := continuation δ E.logF
/-- Ref axial, given by `continuation δ E.logU`. -/
def refAxial (δ : ℝ) : CField := continuation δ E.logU
/-- Ref F, given by `attach N E.f (fun p => Complex.exp (E.refLog δ p))`. -/
def refF (δ : ℝ) : CField := attach N E.f (fun p => Complex.exp (E.refLog δ p))
/-- Ref U, given by `attach N E.U (E.refAxial δ)`. -/
def refU (δ : ℝ) : CField := attach N E.U (E.refAxial δ)
/-- Act log, given by `controlled T κ (E.refLog δ)`. -/
def actLog (T κ δ : ℝ) : CField := controlled T κ (E.refLog δ)
/-- Act axial, given by `controlled T κ (E.refAxial δ)`. -/
def actAxial (T κ δ : ℝ) : CField := controlled T κ (E.refAxial δ)
/-- Act F, given by `attach N E.f (fun p => Complex.exp (E.actLog T κ δ p))`. -/
def actF (T κ δ : ℝ) : CField := attach N E.f (fun p => Complex.exp (E.actLog T κ δ p))
/-- Act U, given by `attach N E.U (E.actAxial T κ δ)`. -/
def actU (T κ δ : ℝ) : CField := attach N E.U (E.actAxial T κ δ)

theorem refLog_regular (hΩ : IsOpen Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    :
    Regular univ Ω (E.refLog δ) :=
  regular_continuation ReferencePath.rampLimit_pos hδ hδT hΩ E.logF_regular

theorem refAxial_regular (hΩ : IsOpen Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ <
    ReferencePath.rampLimit)
    :
    Regular univ Ω (E.refAxial δ) :=
  regular_continuation ReferencePath.rampLimit_pos hδ hδT hΩ E.logU_regular

theorem refLog_initial (hΩ : IsOpen Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    {p : CPoint} (hp : p.2 ∈ Ω) (ht : p.1 ≤ 0) : E.refLog δ p = E.logF p :=
  continuation_eq_initial ReferencePath.rampLimit_pos hδ hδT hΩ E.logF_regular hp (ht.trans hδ.le)

theorem refAxial_initial (hΩ : IsOpen Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ <
    ReferencePath.rampLimit)
    {p : CPoint} (hp : p.2 ∈ Ω) (ht : p.1 ≤ 0) : E.refAxial δ p = E.logU p :=
  continuation_eq_initial ReferencePath.rampLimit_pos hδ hδT hΩ E.logU_regular hp (ht.trans hδ.le)

theorem angular_attach_regular (hΩ : IsOpen Ω) {G : CField} (hG : Regular univ Ω G)
    (hinit : ∀ p : CPoint, p.2 ∈ Ω → p.1 ≤ 0 → G p = E.logF p) :
    Regular (Ioi (-R)) Ω (attach N E.f (fun p => Complex.exp (G p))) := by
  apply regular_attach N E.radius_pos E.endpoint_lt hΩ E.f_regular hG.cexp
  intro p hp hxe hz
  have ht : N.logTime p.1 ≤ 0 := (N.logTime_le_iff hp).2 (by
      simpa only [Real.exp_zero,mul_one] using hxe)
  rw [hinit (logPoint N p) hz ht]
  change Complex.exp (Complex.log (E.f (expPoint N (logPoint N p)))) = E.f p
  rw [expPoint_logPoint N hp]
  apply Complex.exp_log
  have hpos := E.right_half (N.logTime p.1) (ht.trans_lt ReferencePath.rampLimit_pos) p.2 hz
  have he : (N.endpoint*Real.exp (N.logTime p.1),p.2) = p := expPoint_logPoint N hp
  rw [he] at hpos
  intro hn
  simp only [hn,Complex.zero_re,lt_self_iff_false] at hpos

theorem axial_attach_regular (hΩ : IsOpen Ω) {G : CField} (hG : Regular univ Ω G)
    (hinit : ∀ p : CPoint, p.2 ∈ Ω → p.1 ≤ 0 → G p = E.logU p) :
    Regular (Ioi (-R)) Ω (attach N E.U G) := by
  apply regular_attach N E.radius_pos E.endpoint_lt hΩ E.U_regular hG
  intro p hp hxe hz
  have ht : N.logTime p.1 ≤ 0 := (N.logTime_le_iff hp).2 (by
      simpa only [Real.exp_zero,mul_one] using hxe)
  rw [hinit (logPoint N p) hz ht]
  change E.U (expPoint N (logPoint N p)) = E.U p
  rw [expPoint_logPoint N hp]

theorem refF_regular (hΩ : IsOpen Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit) :
    Regular (Ioi (-R)) Ω (E.refF δ) :=
  E.angular_attach_regular hΩ (E.refLog_regular hΩ hδ hδT)
    (fun _ hp ht => E.refLog_initial hΩ hδ hδT hp ht)

theorem refU_regular (hΩ : IsOpen Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit) :
    Regular (Ioi (-R)) Ω (E.refU δ) :=
  E.axial_attach_regular hΩ (E.refAxial_regular hΩ hδ hδT)
    (fun _ hp ht => E.refAxial_initial hΩ hδ hδT hp ht)

theorem actF_regular (hΩ : IsOpen Ω) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) : Regular (Ioi (-R)) Ω (E.actF T κ δ) := by
  apply E.angular_attach_regular hΩ (regular_controlled T κ hΩ (E.refLog_regular hΩ hδ hδT))
  intro p hp ht
  exact (controlled_eq_initial hT κ hΩ (E.refLog_regular hΩ hδ hδT) hp ht).trans
    (E.refLog_initial hΩ hδ hδT hp ht)

theorem actU_regular (hΩ : IsOpen Ω) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) : Regular (Ioi (-R)) Ω (E.actU T κ δ) := by
  apply E.axial_attach_regular hΩ (regular_controlled T κ hΩ (E.refAxial_regular hΩ hδ hδT))
  intro p hp ht
  exact (controlled_eq_initial hT κ hΩ (E.refAxial_regular hΩ hδ hδT) hp ht).trans
    (E.refAxial_initial hΩ hδ hδT hp ht)

theorem refLog_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.refLog δ (x,(η : ℂ)) = (StressActivation.FromReference.refLog N δ (x,η) : ℂ) :=
  continuation_ofReal ReferencePath.rampLimit_pos hδ hδT ReferencePath.parameterInterval_open
    N.logF_smooth (fun _ ht _ hη => E.logF_real ht hη) x hη

theorem refAxial_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.refAxial δ (x,(η : ℂ)) = (StressActivation.FromReference.refAxial N δ (x,η) : ℂ) :=
  continuation_ofReal ReferencePath.rampLimit_pos hδ hδT ReferencePath.parameterInterval_open
    N.logU_smooth (fun _ _ _ _ => E.logU_real _ _) x hη

theorem actLog_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (T κ x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.actLog T κ δ (x,(η : ℂ)) =
      (StressActivation.controlled T κ (StressActivation.FromReference.refLog N δ) (x,η) : ℂ) :=
  controlled_ofReal T κ ReferencePath.parameterInterval_open
    (StressActivation.FromReference.refLog_smooth N hδ hδT)
    (fun x _ hη => E.refLog_real hδ hδT x hη) x hη

theorem actAxial_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (T κ x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.actAxial T κ δ (x,(η : ℂ)) =
      (StressActivation.controlled T κ (StressActivation.FromReference.refAxial N δ) (x,η) : ℂ) :=
  controlled_ofReal T κ ReferencePath.parameterInterval_open
    (StressActivation.FromReference.refAxial_smooth N hδ hδT)
    (fun x _ hη => E.refAxial_real hδ hδT x hη) x hη

theorem refF_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.refF δ (x,(η : ℂ)) = (N.refF δ (x,η) : ℂ) := by
  by_cases hx : x ≤ N.endpoint
  · simp only [refF,attach,ite_eq_left hx,ReferencePath.Input.refF,E.f_real]
  · simp only [refF,attach,ite_eq_right hx,ReferencePath.Input.refF,logPoint]
    rw [E.refLog_real hδ hδT _ hη,Complex.ofReal_exp]
    rfl

theorem refU_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.refU δ (x,(η : ℂ)) = (N.refU δ (x,η) : ℂ) := by
  by_cases hx : x ≤ N.endpoint
  · simp only [refU,attach,ite_eq_left hx,ReferencePath.Input.refU,E.U_real]
  · simp only [refU,attach,ite_eq_right hx,ReferencePath.Input.refU,logPoint]
    exact E.refAxial_real hδ hδT _ hη

theorem actF_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (T κ x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.actF T κ δ (x,(η : ℂ)) = (StressActivation.FromReference.f N T κ δ (x,η) : ℂ) := by
  by_cases hx : x ≤ N.endpoint
  · simp only [actF,attach,ite_eq_left
      hx,StressActivation.FromReference.f,ReferencePath.Input.refF,E.f_real]
  · simp only [actF,attach,ite_eq_right
      hx,StressActivation.FromReference.f,logPoint,StressActivation.activatedAngular]
    rw [E.actLog_real hδ hδT T κ _ hη,Complex.ofReal_exp]

theorem actU_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (T κ x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.actU T κ δ (x,(η : ℂ)) = (StressActivation.FromReference.U N T κ δ (x,η) : ℂ) := by
  by_cases hx : x ≤ N.endpoint
  · simp only [actU,attach,ite_eq_left
      hx,StressActivation.FromReference.U,ReferencePath.Input.refU,E.U_real]
  · simp only [actU,attach,ite_eq_right hx,StressActivation.FromReference.U,logPoint]
    exact E.actAxial_real hδ hδT T κ _ hη

theorem actF_ne_zero (T κ δ : ℝ) {p : CPoint} (hx : 0 ≤ p.1) (hz : p.2 ∈ Ω) :
    E.actF T κ δ p ≠ 0 := by
  by_cases he : p.1 ≤ N.endpoint
  · have hp := E.initial_half p.1 ⟨hx,he⟩ p.2 hz
    rw [actF,attach,ite_eq_left he]
    intro hn
    simp only [hn,Complex.zero_re,lt_self_iff_false] at hp
  · simp only [actF,attach,ite_eq_right he]
    exact Complex.exp_ne_zero _

end NaturalExtension

open NaturalAxisCoefficients NaturalEntrance

/-- Parameter window, bundling `left`, `right`, `nondegenerate`. -/
def parameterWindow : AxisCoefficientSpace.Window where
  left := -21/20
  right := 21/20
  nondegenerate := by norm_num

theorem parameterWindow_subset {η : ℝ} (hη : η ∈ parameterWindow.interval) :
    η ∈ window.interval ∧ η ∈ ReferencePath.parameterInterval := by
  change -21/20 ≤ η ∧ η ≤ 21/20 at hη
  change (-11/10 ≤ η ∧ η ≤ 11/10) ∧ (-11/10 < η ∧ η < 11/10)
  constructor <;> constructor <;> linarith [hη.1,hη.2]

theorem closed_parameter_subset {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) :
    η ∈ parameterWindow.interval := by
  change -21/20 ≤ η ∧ η ≤ 21/20
  constructor <;> linarith [hη.1,hη.2]

theorem parameterTube_open (J : AxisCoefficientSpace.Window) (δ : ℝ) :
    IsOpen (AxisHolomorphic.parameterTube J δ) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨η,hη,hz⟩
  apply Filter.mem_of_superset (isOpen_ball.mem_nhds hz)
  intro w hw
  exact ⟨η,hη,hw⟩

section NaturalConstruction

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
variable (F : CoefficientProfile d Λ C)

/-- Natural F as an element of `ℂ`. -/
def naturalF (p : CPoint) : ℂ :=
  (Complex.exp ((Λ : ℂ) * axisPhase h j σ p.2) / (C : ℂ)) *
    AxisHolomorphic.complexProfile window d.coefficients.epsilon F.coefficients.1 0 (Λ*p.1) p.2

/-- Natural U, given by `complexU j p.2 + (1/(Λ : ℂ)) * AxisHolomorphic.complexProfile window
d.coefficients.epsilon F.coefficients.2 0 (Λ*p.1) p.2`. -/
def naturalU (p : CPoint) : ℂ :=
  complexU j p.2 + (1/(Λ : ℂ)) *
    AxisHolomorphic.complexProfile window d.coefficients.epsilon F.coefficients.2 0 (Λ*p.1) p.2

theorem naturalF_real (x η : ℝ) : naturalF F (x,(η : ℂ)) = (F.family.f (x,η) : ℂ) := by
  rw [F.f_eq]
  simp only [naturalF,axisPhase_ofReal,AxisHolomorphic.complexProfile_zero_ofReal]
  change _ = ((realAmplitude h j σ Λ C η *
    AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.1 (Λ*x,η) : ℝ) : ℂ)
  simp only [realAmplitude,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_exp]

theorem naturalU_real (x η : ℝ) : naturalU F (x,(η : ℂ)) = (F.family.U (x,η) : ℂ) := by
  rw [F.U_eq]
  simp only [naturalU,AxisHolomorphic.complexProfile_zero_ofReal]
  change _ = ((NaturalAxisData.U j η + (1/Λ) *
    AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.2 (Λ*x,η) : ℝ) : ℂ)
  simp only [complexU,NaturalAxisData.U,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat]

theorem scaled_radius_mem (hΛ : 0 < Λ) {x : ℝ} (hx : x ∈ Ioo (-(5 / Λ)) (5 / Λ)) :
    Λ*x ∈ Ioo (-5 : ℝ) 5 := by
  constructor
  · have ht := (mul_lt_mul_of_pos_left hx.1 hΛ)
    have he : Λ * (-(5/Λ)) = -5 := by field_simp
    rwa [he] at ht
  · have ht := (mul_lt_mul_of_pos_left hx.2 hΛ)
    simpa only [mul_div_cancel₀ 5 hΛ.ne'] using ht

theorem coefficient_regular (hΛ : 0 < Λ) {Ω : Set ℂ}
    (hΩ : Ω ⊆ AxisHolomorphic.parameterStrip window (d.coefficients.epsilon * (1 - (1 / 2 : ℝ))))
    (A : AxisCoefficientSpace.AxisSpace window d.coefficients.epsilon) :
    Regular (Ioo (-(5/Λ)) (5/Λ)) Ω
      (fun p => AxisHolomorphic.complexProfile window d.coefficients.epsilon A 0 (Λ*p.1) p.2) := by
  constructor
  · have hb : ContDiffOn ℝ ∞
        (fun p : CPoint => AxisHolomorphic.complexProfile window d.coefficients.epsilon A 0 p.1 p.2)
        (Ioo (-5 : ℝ) 5 ×ˢ AxisHolomorphic.parameterStrip window (d.coefficients.epsilon*(1-(1/2 :
            ℝ)))) :=
      AxisHolomorphicJoint.complexProfile_joint_smooth window d.coefficients.epsilon_pos
      (by norm_num : (1 : ℝ) ≤ 5) (by norm_num : (5 : ℝ)/20 < 1/2)
      (by norm_num : (1/2 : ℝ) < 1) A 0
    have hm : ContDiffOn ℝ ∞ (fun p : CPoint => (Λ*p.1,p.2))
        (Ioo (-(5/Λ)) (5/Λ) ×ˢ Ω) :=
      ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn
    have hout := hb.comp hm (fun p hp => ⟨scaled_radius_mem hΛ hp.1,hΩ hp.2⟩)
    simpa only [Function.comp_def] using hout
  · intro x hx
    exact ((AxisHolomorphic.complexProfile_analytic window d.coefficients.epsilon_pos
      (by norm_num : (1 : ℝ) ≤ 5) (by norm_num : (5 : ℝ)/20 < 1/2)
      (by
          norm_num : (1/2 : ℝ) < 1) A 0 (abs_lt.mpr (scaled_radius_mem hΛ hx)).le).mono
              hΩ).differentiableOn

theorem naturalF_regular (hΛ : 0 < Λ) {Ω : Set ℂ}
    (hstrip : Ω ⊆ AxisHolomorphic.parameterStrip window (d.coefficients.epsilon * (1 - (1 / 2 :
        ℝ))))
    (hphase : Ω ⊆ d.compactSet) : Regular (Ioo (-(5/Λ)) (5/Λ)) Ω (naturalF F) := by
  have hA : AnalyticOnNhd ℂ (fun z => Complex.exp ((Λ : ℂ)*axisPhase h j σ z)/(C : ℂ)) Ω := by
    intro z hz
    have hp : AnalyticAt ℂ (fun w => (Λ : ℂ)*axisPhase h j σ w) z :=
      analyticAt_const.mul (d.phase_analytic z (hphase hz))
    simpa only [div_eq_mul_inv, Function.comp_def] using hp.cexp.fun_mul (analyticAt_const (v := (C
        : ℂ)⁻¹))
  exact (regular_parameter hA).mul (coefficient_regular hΛ hstrip F.coefficients.1)

theorem naturalU_regular (hΛ : 0 < Λ) {Ω : Set ℂ}
    (hstrip : Ω ⊆ AxisHolomorphic.parameterStrip window (d.coefficients.epsilon * (1 - (1 / 2 :
        ℝ)))) :
    Regular (Ioo (-(5/Λ)) (5/Λ)) Ω (naturalU F) := by
  have hbase : AnalyticOnNhd ℂ (complexU j) Ω := by
    intro z _
    unfold complexU
    fun_prop
  exact (regular_parameter hbase).add
    ((regular_const _ _ (1/(Λ : ℂ))).mul (coefficient_regular hΛ hstrip F.coefficients.2))

theorem exists_preliminary_tube (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧
      (∀ η ∈ parameterWindow.interval, (η : ℂ) ∈ Ω) ∧
      Ω ⊆ AxisHolomorphic.parameterStrip window (d.coefficients.epsilon*(1-(1/2 : ℝ))) ∧
      Ω ⊆ d.compactSet ∧ Ω ⊆ regularSet h j σ := by
  obtain ⟨δ,hδ,hsub⟩ := AxisHolomorphic.exists_parameterTube_subset window parameterWindow
    (by norm_num [window,parameterWindow]) (by norm_num [window,parameterWindow])
      (mul_pos d.coefficients.epsilon_pos (by norm_num : 0 < 1-(1/2 : ℝ)))
  let r := min δ d.radius
  have hr : 0 < r := lt_min hδ d.radius_pos
  refine ⟨AxisHolomorphic.parameterTube parameterWindow r ∩ regularSet h j σ,
    (parameterTube_open _ _).inter (regularSet_open _ _ _), ?_, ?_, ?_, inter_subset_right⟩
  · intro η hη
    exact ⟨AxisHolomorphic.parameterTube_contains_real parameterWindow hr hη,
      real_mem_regularSet hsmall hσ (parameterWindow_subset hη).1⟩
  · rintro z ⟨⟨η,hη,hz⟩,_⟩
    exact hsub ⟨η,hη,hz.trans_le (min_le_left _ _)⟩
  · rintro z ⟨⟨η,hη,hz⟩,_⟩
    exact d.covers η (parameterWindow_subset hη).1 (hz.le.trans (min_le_right _ _))

/-- Compact real positivity produces a single complex tube, uniformly over
the whole natural radial interval used by REF. -/
theorem exists_positive_natural_tube (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) :
    ∃ δ : ℝ, 0 < δ ∧
      let Ω := AxisHolomorphic.parameterTube parameterWindow δ
      IsOpen Ω ∧ Ω ⊆ regularSet h j σ ∧
      Regular (Ioo (-(5/Λ)) (5/Λ)) Ω (naturalF F) ∧
      Regular (Ioo (-(5/Λ)) (5/Λ)) Ω (naturalU F) ∧
      ∀ x ∈ Icc (0 : ℝ) ((41/10)/Λ), ∀ z ∈ Ω, 0 < (naturalF F (x,z)).re := by
  obtain ⟨Ω,hΩ,hreal,hstrip,hphase,hreg⟩ := exists_preliminary_tube (d := d) hsmall hσ
  have hf := naturalF_regular F hΛ hstrip hphase
  have hu := naturalU_regular F hΛ hstrip
  let S : Set ℝ := Ioo (-(5/Λ)) (5/Λ)
  let O : Set CPoint := {p | p ∈ S ×ˢ Ω ∧ 0 < (naturalF F p).re}
  have hopen : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hdom := (isOpen_Ioo.prod hΩ).mem_nhds hp.1
    have hpos := (Complex.continuous_re.continuousAt.comp (hf.smooth.contDiffAt
        hdom).continuousAt).eventually
      (Ioi_mem_nhds hp.2)
    filter_upwards [hdom,hpos] with q hq hqpos
    exact ⟨hq,hqpos⟩
  let K : Set CPoint := Icc (0 : ℝ) ((41/10)/Λ) ×ˢ (Complex.ofReal '' parameterWindow.interval)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.image Complex.continuous_ofReal)
  have hKS : ∀ x ∈ Icc (0 : ℝ) ((41/10)/Λ), x ∈ S := by
    intro x hx
    constructor
    · exact lt_of_lt_of_le (neg_neg_of_pos (div_pos (by norm_num) hΛ)) hx.1
    · exact hx.2.trans_lt ((div_lt_div_iff_of_pos_right hΛ).2 (by norm_num))
  have hKO : K ⊆ O := by
    rintro ⟨x,z⟩ ⟨hx,η,hη,rfl⟩
    refine ⟨⟨hKS x hx,hreal η hη⟩,?_⟩
    rw [naturalF_real,Complex.ofReal_re]
    have hY0 : 0 ≤ Λ*x := mul_nonneg hΛ.le hx.1
    have hY1 : Λ*x ≤ 41/10 := by
      have hh := mul_le_mul_of_nonneg_left hx.2 hΛ.le
      simpa only [mul_div_cancel₀ (41/10) hΛ.ne'] using hh
    have hdom : (x,η) ∈ NaturalProfile.domain Λ := by
      change (-20 < Λ*x ∧ Λ*x < 20) ∧ η ∈ ReferencePath.parameterInterval
      exact ⟨⟨by linarith,by linarith⟩,(parameterWindow_subset hη).2⟩
    exact F.family.positive (x,η) hdom hY0 hY1
  obtain ⟨δ,hδ,hδO⟩ := hK.exists_cthickening_subset_open hopen hKO
  have hpos (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ((41/10)/Λ))
      {z : ℂ} (hz : z ∈ AxisHolomorphic.parameterTube parameterWindow δ) : (x,z) ∈ O := by
    rcases hz with ⟨η,hη,hz⟩
    apply hδO
    apply closedBall_subset_cthickening
      (show (x,(η : ℂ)) ∈ K from ⟨hx,mem_image_of_mem Complex.ofReal hη⟩) δ
    change dist (x,z) (x,(η : ℂ)) ≤ δ
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg)] using hz.le
  have hsub : AxisHolomorphic.parameterTube parameterWindow δ ⊆ Ω := by
    intro z hz
    exact (hpos 0 ⟨le_rfl,by positivity⟩ hz).1.2
  refine ⟨δ,hδ,parameterTube_open _ _,hsub.trans hreg,hf.mono Subset.rfl hsub,
    hu.mono Subset.rfl hsub,?_⟩
  intro x hx z hz
  exact (hpos x hx hz).2

theorem natural_log_radius (hΛ : 0 < Λ) {t : ℝ} (ht : t < ReferencePath.rampLimit) :
    0 < (4/Λ)*Real.exp t ∧ (4/Λ)*Real.exp t < (41/10)/Λ := by
  have he : Real.exp t < 41/40 := by
    simpa only [ReferencePath.rampLimit,Real.exp_log (by norm_num : (0 : ℝ) < 41/40)] using
      Real.exp_lt_exp.mpr ht
  constructor
  · positivity
  · rw [div_mul_eq_mul_div]
    exact (div_lt_div_iff_of_pos_right hΛ).2 (by nlinarith)

/-- Construction from the actual coefficient witness. In particular the
natural extension and its common positive neighborhood are not assumptions. -/
theorem exists_natural_extension (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ _ : NaturalExtension (ReferenceJetBounds.referenceInput F hΛ)
      (AxisHolomorphic.parameterTube parameterWindow ρ) (5/Λ),
      AxisHolomorphic.parameterTube parameterWindow ρ ⊆ regularSet h j σ := by
  obtain ⟨ρ,hρ,hopen,hreg,hf,hu,hpos⟩ := exists_positive_natural_tube F hΛ hsmall hσ
  refine ⟨ρ,hρ,{
    radius_pos := div_pos (by norm_num) hΛ
    endpoint_lt := ?_
    f := naturalF F
    U := naturalU F
    f_regular := hf
    U_regular := hu
    f_real := naturalF_real F
    U_real := naturalU_real F
    exp_mem := ?_
    right_half := ?_
    initial_half := ?_ },hreg⟩
  · change 4/Λ < 5/Λ
    exact (div_lt_div_iff_of_pos_right hΛ).2 (by norm_num)
  · intro t ht
    have hb := natural_log_radius hΛ ht
    change -(5/Λ) < (4/Λ)*Real.exp t ∧ (4/Λ)*Real.exp t < 5/Λ
    constructor
    · exact (neg_neg_of_pos (div_pos (by norm_num) hΛ)).trans hb.1
    · exact hb.2.trans ((div_lt_div_iff_of_pos_right hΛ).2 (by norm_num))
  · intro t ht z hz
    exact hpos _ ⟨(natural_log_radius hΛ ht).1.le,(natural_log_radius hΛ ht).2.le⟩ z hz
  · intro x hx z hz
    have he : (ReferenceJetBounds.referenceInput F hΛ).endpoint ≤ (41/10)/Λ := by
      change 4/Λ ≤ (41/10)/Λ
      exact (div_le_div_iff_of_pos_right hΛ).2 (by norm_num)
    exact hpos x ⟨hx.1,hx.2.trans he⟩ z hz

end NaturalConstruction

/-- Radial jet, given by `iteratedDeriv k (fun x => F (x,p.2)) p.1`. -/
def radialJet (F : CField) (k : ℕ) (p : CPoint) : ℂ :=
  iteratedDeriv k (fun x => F (x,p.2)) p.1

theorem radialJet_succ (F : CField) (k : ℕ) : radialJet F (k+1) = radial (radialJet F k) := by
  funext p
  simp only [radialJet,radial,iteratedDeriv_succ]

theorem Regular.radialJet {S : Set ℝ} {Ω : Set ℂ} {F : CField}
    (hF : Regular S Ω F) (hS : IsOpen S) (hΩ : IsOpen Ω) (k : ℕ) :
    Regular S Ω (radialJet F k) := by
  induction k with
  | zero =>
    unfold ActivationHolomorphic.radialJet
    simpa only [iteratedDeriv_zero,Prod.eta] using hF
  | succ k ih => rw [radialJet_succ]; exact ih.radial hS hΩ

theorem scale_half_interval {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x ∈ Ioi (-R))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t*x ∈ Ioi (-R) := by
  rcases le_total x 0 with hn | hp
  · have hb : x ≤ t*x := by simpa only [one_mul] using mul_le_mul_of_nonpos_right ht.2 hn
    exact hx.trans_le hb
  · exact (neg_neg_of_pos hR).trans_le (mul_nonneg ht.1 hp)

theorem Regular.pow {S : Set ℝ} {Ω : Set ℂ} {F : CField} (hF : Regular S Ω F) (n : ℕ) :
    Regular S Ω (fun p => F p ^ n) :=
  ⟨hF.smooth.pow n,fun x hx => (hF.holomorphic x hx).pow n⟩

/-- Pressure, given by `P0 p.2 + primitive (fun q => f q ^ 2) p`. -/
def pressure (P0 : ℂ → ℂ) (f : CField) (p : CPoint) : ℂ :=
  P0 p.2 + primitive (fun q => f q ^ 2) p

theorem regular_pressure {R : ℝ} (hR : 0 < R) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : CField} (hf : Regular (Ioi (-R)) Ω f) {P0 : ℂ → ℂ}
    (hP0 : AnalyticOnNhd ℂ P0 Ω) : Regular (Ioi (-R)) Ω (pressure P0 f) :=
  (regular_parameter hP0).add ((hf.pow 2).primitive isOpen_Ioi hΩ
    (fun _ hx _ ht => scale_half_interval hR hx ht))

theorem average_ofReal {F : CField} {g : ProfileHistories.Field} {η : ℝ}
    (heq : ∀ x : ℝ, F (x,(η : ℂ)) = (g (x,η) : ℂ)) (x : ℝ) :
    average F (x,(η : ℂ)) = (ProfileHistories.average g (x,η) : ℂ) := by
  unfold average ProfileHistories.average
  calc
    _ = ∫ t in (0 : ℝ)..1, (g (t*x,η) : ℂ) := intervalIntegral.integral_congr (fun t _ => heq (t*x))
    _ = _ := intervalIntegral.integral_ofReal

theorem primitive_ofReal {F : CField} {g : ProfileHistories.Field} {η : ℝ}
    (heq : ∀ x : ℝ, F (x,(η : ℂ)) = (g (x,η) : ℂ)) (x : ℝ) :
    primitive F (x,(η : ℂ)) = (ProfileHistories.primitive g (x,η) : ℂ) := by
  unfold primitive ProfileHistories.primitive
  calc
    _ = ∫ t in (0 : ℝ)..x, (g (t,η) : ℂ) := intervalIntegral.integral_congr (fun t _ => heq t)
    _ = _ := intervalIntegral.integral_ofReal

theorem pressure_ofReal {F : CField} {g : ProfileHistories.Field} {η : ℝ}
    (heq : ∀ x : ℝ, F (x,(η : ℂ)) = (g (x,η) : ℂ))
    {P0 : ℂ → ℂ} {p0 : ℝ → ℝ} (hP0 : P0 (η : ℂ) = (p0 η : ℂ)) (x : ℝ) :
    pressure P0 F (x,(η : ℂ)) =
      ((p0 η + ProfileHistories.primitive (fun p => g p ^ 2) (x,η) : ℝ) : ℂ) := by
  rw [pressure,hP0,Complex.ofReal_add]
  congr 1
  apply primitive_ofReal
  intro y
  simp only [heq,Complex.ofReal_pow]

/-- Pull back a complex field along the square of its radial coordinate. -/
def signedSquare (F : CField) (p : CPoint) : ℂ := F (p.1^2,p.2)

theorem Regular.signedSquare {R : ℝ} (hR : 0 < R) {Ω : Set ℂ} {F : CField}
    (hF : Regular (Ioi (-R)) Ω F) : Regular univ Ω (signedSquare F) := by
  constructor
  · exact hF.smooth.comp ((contDiff_fst.pow 2).prodMk contDiff_snd).contDiffOn
      (fun p hp => ⟨(neg_neg_of_pos hR).trans_le (sq_nonneg p.1),hp.2⟩)
  · intro r _
    exact hF.holomorphic (r^2) ((neg_neg_of_pos hR).trans_le (sq_nonneg r))

theorem signedSquare_even (F : CField) (z : ℂ) : Function.Even (fun r => signedSquare F (r,z)) := by
  intro r
  simp only [signedSquare,neg_sq]

/-- The actual base data on one common complex tube. The constructor below
supplies the pressure extension from its proved defining integral. -/
structure InitialTube (N : ReferencePath.Input) (h : ℝ) (P0 : ℝ → ℝ)
    (R : ℝ) (Ω : Set ℂ) where
  /-- Natural of `InitialTube`, of type `NaturalExtension N Ω R`. -/
  natural : NaturalExtension N Ω R
  isOpen : IsOpen Ω
  real_mem : ∀ η ∈ Icc (-1 : ℝ) 1, (η : ℂ) ∈ Ω
  elliptic_ne_zero : ∀ z ∈ Ω, complexL h z ≠ 0
  /-- Pressure0 of `InitialTube`, of type `ℂ → ℂ`. -/
  pressure0 : ℂ → ℂ
  pressure0_analytic : AnalyticOnNhd ℂ pressure0 Ω
  pressure0_real : ∀ η : ℝ, pressure0 (η : ℂ) = (P0 η : ℂ)

namespace InitialTube

variable {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω : Set ℂ}
variable (E : InitialTube N h P0 R Ω)

/-- F, given by `E.natural.actF T κ δ`. -/
def f (T κ δ : ℝ) : CField := E.natural.actF T κ δ
/-- U, given by `E.natural.actU T κ δ`. -/
def U (T κ δ : ℝ) : CField := E.natural.actU T κ δ
/-- Ubar, given by `average (E.U T κ δ)`. -/
def Ubar (T κ δ : ℝ) : CField := average (E.U T κ δ)
/-- Pi, given by `pressure E.pressure0 (E.f T κ δ)`. -/
def Pi (T κ δ : ℝ) : CField := pressure E.pressure0 (E.f T κ δ)

theorem regular {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) :
    Regular (Ioi (-R)) Ω (E.f T κ δ) ∧
    Regular (Ioi (-R)) Ω (E.U T κ δ) ∧
    Regular (Ioi (-R)) Ω (E.Ubar T κ δ) ∧
    Regular (Ioi (-R)) Ω (E.Pi T κ δ) := by
  have hf := E.natural.actF_regular E.isOpen hT hδ hδT κ
  have hu := E.natural.actU_regular E.isOpen hT hδ hδT κ
  exact ⟨hf,hu,hu.average isOpen_Ioi E.isOpen
    (fun _ hx _ ht => scale_half_interval E.natural.radius_pos hx ht),
      regular_pressure E.natural.radius_pos E.isOpen hf E.pressure0_analytic⟩

/-- The width of the holomorphic domain is unchanged at every fixed radial
derivative order. These are actual iterated derivatives of the functions. -/
theorem all_radial_jets {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (k : ℕ) :
    Regular (Ioi (-R)) Ω (radialJet (E.f T κ δ) k) ∧
    Regular (Ioi (-R)) Ω (radialJet (E.U T κ δ) k) ∧
    Regular (Ioi (-R)) Ω (radialJet (E.Ubar T κ δ) k) ∧
    Regular (Ioi (-R)) Ω (radialJet (E.Pi T κ δ) k) := by
  obtain ⟨hf,hu,hv,hp⟩ := E.regular hT hδ hδT κ
  exact ⟨hf.radialJet isOpen_Ioi E.isOpen k,hu.radialJet isOpen_Ioi E.isOpen k,
    hv.radialJet isOpen_Ioi E.isOpen k,hp.radialJet isOpen_Ioi E.isOpen k⟩

/-- The signed-square pullbacks are smooth and holomorphic through the axis,
and are even in the signed radius. -/
theorem signed_regular {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) :
    Regular univ Ω (signedSquare (E.f T κ δ)) ∧
    Regular univ Ω (signedSquare (E.U T κ δ)) ∧
    Regular univ Ω (signedSquare (E.Ubar T κ δ)) ∧
    Regular univ Ω (signedSquare (E.Pi T κ δ)) := by
  obtain ⟨hf,hu,hv,hp⟩ := E.regular hT hδ hδT κ
  exact ⟨hf.signedSquare E.natural.radius_pos,hu.signedSquare E.natural.radius_pos,
    hv.signedSquare E.natural.radius_pos,hp.signedSquare E.natural.radius_pos⟩

theorem f_ne_zero (T κ δ : ℝ) {x : ℝ} (hx : 0 ≤ x) {z : ℂ} (hz : z ∈ Ω) :
    E.f T κ δ (x,z) ≠ 0 := E.natural.actF_ne_zero T κ δ hx hz

/-- Agreement includes the literal axis-to-radius average and pressure,
with no independently prescribed moment data. -/
theorem real_profiles {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    E.f T κ δ (x,(η : ℂ)) = (P.f (x,η) : ℂ) ∧
    E.U T κ δ (x,(η : ℂ)) = (P.U (x,η) : ℂ) ∧
    E.Ubar T κ δ (x,(η : ℂ)) = (P.Ubar (x,η) : ℂ) ∧
    E.Pi T κ δ (x,(η : ℂ)) = (P.pressure (x,η) : ℂ) := by
  refine ⟨E.natural.actF_real hδ hδT T κ x hη,
    E.natural.actU_real hδ hδT T κ x hη,?_,?_⟩
  · exact average_ofReal (fun y => E.natural.actU_real hδ hδT T κ y hη) x
  · exact pressure_ofReal (fun y => E.natural.actF_real hδ hδT T κ y hη) (E.pressure0_real η) x

theorem reference_regular {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit) :
    Regular (Ioi (-R)) Ω (E.natural.refF δ) ∧
    Regular (Ioi (-R)) Ω (E.natural.refU δ) ∧
    Regular (Ioi (-R)) Ω (average (E.natural.refU δ)) ∧
    Regular (Ioi (-R)) Ω (pressure E.pressure0 (E.natural.refF δ)) := by
  have hf := E.natural.refF_regular E.isOpen hδ hδT
  have hu := E.natural.refU_regular E.isOpen hδ hδT
  exact ⟨hf,hu,hu.average isOpen_Ioi E.isOpen
    (fun _ hx _ ht => scale_half_interval E.natural.radius_pos hx ht),
      regular_pressure E.natural.radius_pos E.isOpen hf E.pressure0_analytic⟩

theorem reference_real_profiles {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) (x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    let P := N.histories hδ hδT P0 hP0
    E.natural.refF δ (x,(η : ℂ)) = (P.f (x,η) : ℂ) ∧
    E.natural.refU δ (x,(η : ℂ)) = (P.U (x,η) : ℂ) ∧
    average (E.natural.refU δ) (x,(η : ℂ)) = (P.Ubar (x,η) : ℂ) ∧
    pressure E.pressure0 (E.natural.refF δ) (x,(η : ℂ)) = (P.pressure (x,η) : ℂ) := by
  refine ⟨E.natural.refF_real hδ hδT x hη,E.natural.refU_real hδ hδT x hη,?_,?_⟩
  · exact average_ofReal (fun y => E.natural.refU_real hδ hδT y hη) x
  · exact pressure_ofReal (fun y => E.natural.refF_real hδ hδT y hη) (E.pressure0_real η) x

end InitialTube

/-- Actual coefficient profiles and the actual pressure datum construct the
common tube. The width is chosen before the REF and ACT cutoff lengths. -/
theorem exists_initialTube {h j σ Λ C : ℝ} {g a : ℝ → ℝ} {cap : ℝ}
    (hp : PressureDatum.Admissible g a cap)
    {d : AnalyticInputs h j σ (PressureDatum.pressure g a)}
    (F : CoefficientProfile d Λ C) (hΛ : 0 < Λ)
    (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ) :
    ∃ ρ : ℝ, 0 < ρ ∧ Nonempty (InitialTube (ReferenceJetBounds.referenceInput F hΛ) h
      (PressureDatum.pressure g a) (5/Λ) (AxisHolomorphic.parameterTube parameterWindow ρ)) := by
  obtain ⟨ρ,hρ,E,hreg⟩ := exists_natural_extension F hΛ hsmall hσ
  refine ⟨ρ,hρ,⟨{
    natural := E
    isOpen := parameterTube_open _ _
    real_mem := fun η hη => AxisHolomorphic.parameterTube_contains_real parameterWindow hρ
        (closed_parameter_subset hη)
    elliptic_ne_zero := fun z hz => (hreg hz).1.2
    pressure0 := PressureDatum.complexPressure g a
    pressure0_analytic := (PressureDatum.complexPressure_analytic hp).mono (fun z hz => (hreg
        hz).1.1)
    pressure0_real := PressureDatum.complexPressure_ofReal g a
  }⟩⟩

theorem natural_average_identity {h j Λ : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ProfileHistories.Field} (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a f U V Pr)
    {p : ProfileHistories.Point} (hp : p ∈ NaturalProfile.domain Λ) : ProfileHistories.average U p
        = V p := by
  by_cases hx : p.1 = 0
  · have he : p = (0,p.2) := Prod.ext hx rfl
    rw [he,ProfileHistories.average_at_axis,hs.U_axis p.2 hp.2,hs.average_axis p.2 hp.2]
  · rw [ProfileHistories.average_eq_quotient U hx]
    change (∫ X in (0 : ℝ)..p.1, U (X,p.2)) / p.1 = V p
    rw [← hs.average_integral p hp,mul_div_cancel_left₀ _ hx]

/-- The natural average recovered by complex integration is the original
natural profile's actual average, including the regular value at the axis. -/
theorem natural_Ubar_real {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : CoefficientProfile d Λ C) {p : ProfileHistories.Point} (hp : p ∈ NaturalProfile.domain Λ) :
    average (naturalU F) (p.1,(p.2 : ℂ)) = (F.family.Ubar p : ℂ) := by
  rw [average_ofReal (fun x => naturalU_real F x p.2) p.1]
  exact congrArg Complex.ofReal (natural_average_identity F.family.natural hp)

theorem natural_Pi_real {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : CoefficientProfile d Λ C) {P : ℂ → ℂ} (hP : ∀ η : ℝ, P (η : ℂ) = (P0 η : ℂ))
    {p : ProfileHistories.Point} (hp : p ∈ NaturalProfile.domain Λ) :
    pressure P (naturalF F) (p.1,(p.2 : ℂ)) = (F.family.Pi p : ℂ) := by
  rw [pressure_ofReal (fun x => naturalF_real F x p.2) (hP p.2) p.1]
  congr 1
  have he := F.family.natural.pressure_integral p hp
  change F.family.Pi p - P0 p.2 = ProfileHistories.primitive (fun q => F.family.f q ^ 2) p at he
  linarith

theorem iteratedDeriv_smooth {S : Set ℝ} (hS : IsOpen S) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g S) (k : ℕ) : ContDiffOn ℝ ∞ (iteratedDeriv k g) S := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hg
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen hS (by simp)

theorem iteratedDeriv_ofReal {S : Set ℝ} (hS : IsOpen S) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g S) (k : ℕ) {x : ℝ} (hx : x ∈ S) :
    iteratedDeriv k (fun y => (g y : ℂ)) x = ((iteratedDeriv k g x : ℝ) : ℂ) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ,iteratedDeriv_succ]
    have heq : iteratedDeriv k (fun y => (g y : ℂ)) =ᶠ[𝓝 x]
        (fun y => ((iteratedDeriv k g y : ℝ) : ℂ)) := by
      filter_upwards [hS.mem_nhds hx] with y hy
      exact ih hy
    rw [heq.deriv_eq]
    exact (((iteratedDeriv_smooth hS hg k).contDiffAt (hS.mem_nhds hx)).differentiableAt
      (by simp)).hasDerivAt.ofReal_comp.deriv

/-- The holomorphic radial jets extend the actual real radial derivatives,
including at the axis; agreement is derived from equality of the functions. -/
theorem radialJet_real {S : Set ℝ} {Ω : Set ℂ} (hS : IsOpen S) (_ : IsOpen Ω)
    {F : CField} (hF : Regular S Ω F) {g : ℝ → ℝ} {η : ℝ} (hη : (η : ℂ) ∈ Ω)
    (heq : ∀ x ∈ S, F (x, (η : ℂ)) = (g x : ℂ)) (k : ℕ) {x : ℝ} (hx : x ∈ S) :
    radialJet F k (x,(η : ℂ)) = ((iteratedDeriv k g x : ℝ) : ℂ) := by
  have hs : ContDiffOn ℝ ∞ (fun x => F (x,(η : ℂ))) S :=
    hF.smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hx => ⟨hx,hη⟩)
  have hgr : ContDiffOn ℝ ∞ g S := by
    apply (Complex.reCLM.contDiff.comp_contDiffOn hs).congr
    intro y hy
    change g y = (F (y,(η : ℂ))).re
    rw [heq y hy,Complex.ofReal_re]
  have he : (fun y => F (y,(η : ℂ))) =ᶠ[𝓝 x] (fun y => (g y : ℂ)) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact heq y hy
  exact (he.iteratedDeriv_eq k).trans (iteratedDeriv_ofReal hS hgr k hx)

theorem InitialTube.real_radial_jets {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω : Set ℂ}
    (E : InitialTube N h P0 R Ω) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (k : ℕ) {x η : ℝ} (hx : x ∈ Ioi (-R)) (hη : η ∈ Icc (-1 : ℝ) 1) :
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    radialJet (E.f T κ δ) k (x,(η : ℂ)) = ((iteratedDeriv k (fun y => P.f (y,η)) x : ℝ) : ℂ) ∧
    radialJet (E.U T κ δ) k (x,(η : ℂ)) = ((iteratedDeriv k (fun y => P.U (y,η)) x : ℝ) : ℂ) ∧
    radialJet (E.Ubar T κ δ) k (x,(η : ℂ)) = ((iteratedDeriv k (fun y => P.Ubar (y,η)) x : ℝ) : ℂ) ∧
    radialJet (E.Pi T κ δ) k (x,(η : ℂ)) = ((iteratedDeriv k (fun y => P.pressure (y,η)) x : ℝ) :
        ℂ) := by
  have hη' := NaturalAxisCoefficients.original_interval_interior hη
  obtain ⟨hf,hu,hv,hp⟩ := E.regular hT hδ hδT κ
  refine ⟨radialJet_real isOpen_Ioi E.isOpen hf (E.real_mem η hη) ?_ k hx,
    radialJet_real isOpen_Ioi E.isOpen hu (E.real_mem η hη) ?_ k hx,
    radialJet_real isOpen_Ioi E.isOpen hv (E.real_mem η hη) ?_ k hx,
    radialJet_real isOpen_Ioi E.isOpen hp (E.real_mem η hη) ?_ k hx⟩
  · intro y _
    exact (E.real_profiles hT hδ hδT κ hP0 y hη').1
  · intro y _
    exact (E.real_profiles hT hδ hδT κ hP0 y hη').2.1
  · intro y _
    exact (E.real_profiles hT hδ hδT κ hP0 y hη').2.2.1
  · intro y _
    exact (E.real_profiles hT hδ hδT κ hP0 y hη').2.2.2

theorem scale_symmetric_interval {R x t : ℝ} (hx : x ∈ Ioo (-R) R) (ht : t ∈ Icc (0 : ℝ) 1) :
    t*x ∈ Ioo (-R) R := by
  apply abs_lt.mp
  calc
    |t*x| = t*|x| := by rw [abs_mul,abs_of_nonneg ht.1]
    _ ≤ |x| := mul_le_of_le_one_left (abs_nonneg x) ht.2
    _ < R := abs_lt.mpr hx

theorem InitialTube.natural_regular {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω : Set ℂ}
    (E : InitialTube N h P0 R Ω) :
    Regular (Ioo (-R) R) Ω E.natural.f ∧
    Regular (Ioo (-R) R) Ω E.natural.U ∧
    Regular (Ioo (-R) R) Ω (average E.natural.U) ∧
    Regular (Ioo (-R) R) Ω (pressure E.pressure0 E.natural.f) := by
  refine ⟨E.natural.f_regular,E.natural.U_regular,?_,?_⟩
  · exact E.natural.U_regular.average isOpen_Ioo E.isOpen
      (fun _ hx _ ht => scale_symmetric_interval hx ht)
  · exact (regular_parameter E.pressure0_analytic).add
      ((E.natural.f_regular.pow 2).primitive isOpen_Ioo E.isOpen
        (fun _ hx _ ht => scale_symmetric_interval hx ht))

theorem InitialTube.natural_all_radial_jets {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω :
    Set ℂ}
    (E : InitialTube N h P0 R Ω) (k : ℕ) :
    Regular (Ioo (-R) R) Ω (radialJet E.natural.f k) ∧
    Regular (Ioo (-R) R) Ω (radialJet E.natural.U k) ∧
    Regular (Ioo (-R) R) Ω (radialJet (average E.natural.U) k) ∧
    Regular (Ioo (-R) R) Ω (radialJet (pressure E.pressure0 E.natural.f) k) := by
  obtain ⟨hf,hu,hv,hp⟩ := E.natural_regular
  exact ⟨hf.radialJet isOpen_Ioo E.isOpen k,hu.radialJet isOpen_Ioo E.isOpen k,
    hv.radialJet isOpen_Ioo E.isOpen k,hp.radialJet isOpen_Ioo E.isOpen k⟩

theorem InitialTube.reference_all_radial_jets {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω :
    Set ℂ}
    (E : InitialTube N h P0 R Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit) (k :
        ℕ)
        :
    Regular (Ioi (-R)) Ω (radialJet (E.natural.refF δ) k) ∧
    Regular (Ioi (-R)) Ω (radialJet (E.natural.refU δ) k) ∧
    Regular (Ioi (-R)) Ω (radialJet (average (E.natural.refU δ)) k) ∧
    Regular (Ioi (-R)) Ω (radialJet (pressure E.pressure0 (E.natural.refF δ)) k) := by
  obtain ⟨hf,hu,hv,hp⟩ := E.reference_regular hδ hδT
  exact ⟨hf.radialJet isOpen_Ioi E.isOpen k,hu.radialJet isOpen_Ioi E.isOpen k,
    hv.radialJet isOpen_Ioi E.isOpen k,hp.radialJet isOpen_Ioi E.isOpen k⟩

theorem InitialTube.natural_real_profiles {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : CoefficientProfile d Λ C) (hΛ : 0 < Λ)
    {R : ℝ} {Ω : Set ℂ} (E : InitialTube (ReferenceJetBounds.referenceInput F hΛ) h P0 R Ω)
    {p : ProfileHistories.Point} (hp : p ∈ NaturalProfile.domain Λ) :
    E.natural.f (p.1,(p.2 : ℂ)) = (F.family.f p : ℂ) ∧
    E.natural.U (p.1,(p.2 : ℂ)) = (F.family.U p : ℂ) ∧
    average E.natural.U (p.1,(p.2 : ℂ)) = (F.family.Ubar p : ℂ) ∧
    pressure E.pressure0 E.natural.f (p.1,(p.2 : ℂ)) = (F.family.Pi p : ℂ) := by
  refine ⟨E.natural.f_real _ _,E.natural.U_real _ _,?_,?_⟩
  · rw [average_ofReal (fun x => E.natural.U_real x p.2) p.1]
    exact congrArg Complex.ofReal (natural_average_identity F.family.natural hp)
  · rw [pressure_ofReal (fun x => E.natural.f_real x p.2) (E.pressure0_real p.2) p.1]
    congr 1
    change P0 p.2 + ProfileHistories.primitive (fun q => F.family.f q ^ 2) p = F.family.Pi p
    have he := F.family.natural.pressure_integral p hp
    change F.family.Pi p - P0 p.2 = ProfileHistories.primitive (fun q => F.family.f q ^ 2) p at he
    linarith

end NavierStokes.ActivationHolomorphic

end

end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSlowAxis

open Set Filter
open scoped Topology ContDiff
open ActivationHolomorphic (InitialTube CField signedSquare)
open SlowRecursion (AxisFunction Coefficient)

/-- A conjugation-invariant open neighborhood whose real points remain in
the real profile domain. It retains the entire closed physical window. -/
noncomputable def parameterDomain (Ω : Set ℂ) : Set ℂ :=
  Ω ∩ (starRingEnd ℂ) ⁻¹' Ω ∩ Complex.re ⁻¹' ReferencePath.parameterInterval

theorem parameterDomain_open {Ω : Set ℂ} (hΩ : IsOpen Ω) : IsOpen (parameterDomain Ω) :=
  (hΩ.inter (hΩ.preimage Complex.continuous_conj)).inter
    (ReferencePath.parameterInterval_open.preimage Complex.continuous_re)

theorem parameterDomain_subset (Ω : Set ℂ) : parameterDomain Ω ⊆ Ω := fun _ hz => hz.1.1

theorem parameterDomain_conjugate {Ω : Set ℂ} {z : ℂ} (hz : z ∈ parameterDomain Ω) :
    starRingEnd ℂ z ∈ parameterDomain Ω := by
  exact ⟨⟨hz.1.2, by simpa using hz.1.1⟩, by simpa using hz.2⟩

theorem parameterDomain_real {Ω : Set ℂ}
    (hreal : ∀ eta ∈ Icc (-1 : ℝ) 1, (eta : ℂ) ∈ Ω)
    {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) : (eta : ℂ) ∈ parameterDomain Ω := by
  refine ⟨⟨hreal eta heta, ?_⟩, ?_⟩
  · simpa using hreal eta heta
  · exact NaturalAxisCoefficients.original_interval_interior heta

theorem parameterDomain_real_interval {Ω : Set ℂ} {eta : ℝ}
    (heta : (eta : ℂ) ∈ parameterDomain Ω) : eta ∈ ReferencePath.parameterInterval := heta.2

theorem parameterTube_conjugate (J : AxisCoefficientSpace.Window) {ρ : ℝ} {z : ℂ}
    (hz : z ∈ AxisHolomorphic.parameterTube J ρ) :
    starRingEnd ℂ z ∈ AxisHolomorphic.parameterTube J ρ := by
  rcases hz with ⟨x, hx, hd⟩
  refine ⟨x, hx, ?_⟩
  simpa only [Complex.dist_conj_comm, Complex.conj_ofReal] using hd

theorem smallTube_subset_domain {ρ τ : ℝ} (hτρ : τ ≤ ρ) (hτ : τ ≤ 1 / 40) :
    AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow τ ⊆
      parameterDomain (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow ρ) := by
  intro z hz
  rcases hz with ⟨x, hx, hd⟩
  have hzρ : z ∈ AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow ρ :=
    ⟨x, hx, lt_of_lt_of_le hd hτρ⟩
  refine ⟨⟨hzρ, parameterTube_conjugate _ hzρ⟩, ?_⟩
  have hre : |z.re - x| ≤ dist z (x : ℂ) := by
    simpa only [dist_eq_norm, Complex.sub_re, Complex.ofReal_re] using
      Complex.abs_re_le_norm (z - (x : ℂ))
  have hb := abs_lt.mp (lt_of_le_of_lt hre hd)
  change -21 / 20 ≤ x ∧ x ≤ 21 / 20 at hx
  change -11 / 10 < z.re ∧ z.re < 11 / 10
  constructor <;> linarith [hx.1, hx.2, hb.1, hb.2]

theorem histories_congr_below {D D' : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) (Q : ProfileHistories.Profiles D')
    {X eta : ℝ} (hX : 0 ≤ X) (hP0 : P.pressure0 eta = Q.pressure0 eta)
    (hf : ∀ Y ∈ Icc (0 : ℝ) X, P.f (Y, eta) = Q.f (Y, eta))
    (hu : ∀ Y ∈ Icc (0 : ℝ) X, P.U (Y, eta) = Q.U (Y, eta)) :
    P.Ubar (X, eta) = Q.Ubar (X, eta) ∧ P.pressure (X, eta) = Q.pressure (X, eta) := by
  constructor
  · unfold ProfileHistories.Profiles.Ubar ProfileHistories.average
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    exact hu (t * X) ⟨mul_nonneg ht'.1 hX, mul_le_of_le_one_left hX ht'.2⟩
  · unfold ProfileHistories.Profiles.pressure
    rw [hP0]
    congr 1
    unfold ProfileHistories.primitive
    apply intervalIntegral.integral_congr
    intro Y hY
    have hY' : Y ∈ Icc (0 : ℝ) X := by simpa only [uIcc_of_le hX] using hY
    change P.f (Y, eta) ^ 2 = Q.f (Y, eta) ^ 2
    rw [hf Y hY']

section ActualBase

variable {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω : Set ℂ}
variable (E : InitialTube N h P0 R Ω)

include E in
theorem domain {S : ℝ} (hS : 0 < S) : SlowRecursion.Domain S (parameterDomain Ω) h where
  positive := hS
  open_set := parameterDomain_open E.isOpen
  conjugate := fun _ hz => parameterDomain_conjugate hz
  denominator := fun z hz => E.elliptic_ne_zero z hz.1.1

/-- Fields, given by `![E.f T κ δ, E.U T κ δ, E.Ubar T κ δ, E.Pi T κ δ]`. -/
noncomputable def fields (T κ δ : ℝ) : Fin 4 → CField :=
  ![E.f T κ δ, E.U T κ δ, E.Ubar T κ δ, E.Pi T κ δ]

/-- Real fields, given by `let P := StressActivation.FromReference.histories N hT hδ hδT κ P0
hP0 ![P.f, P.U, P.Ubar, P.pressure]`. -/
noncomputable def realFields {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0) :
    Fin 4 → ProfileHistories.Field :=
  let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
  ![P.f, P.U, P.Ubar, P.pressure]

theorem fields_regular {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (i : Fin 4) :
    ActivationHolomorphic.Regular univ Ω (signedSquare (fields E T κ δ i)) := by
  obtain ⟨hf, hu, hv, hp⟩ := E.signed_regular hT hδ hδT κ
  fin_cases i
  · exact hf
  · exact hu
  · exact hv
  · exact hp

theorem fields_real {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (i : Fin 4) (x : ℝ) {eta : ℝ} (heta : eta ∈ ReferencePath.parameterInterval) :
    fields E T κ δ i (x, (eta : ℂ)) = (realFields (N := N) hT hδ hδT κ hP0 i (x, eta) : ℂ) := by
  obtain ⟨hf, hu, hv, hp⟩ := E.real_profiles hT hδ hδT κ hP0 x heta
  fin_cases i
  · exact hf
  · exact hu
  · exact hv
  · exact hp

/-- Each base component is an actual member of the compatible function
algebra; no separate jet data or extension hypothesis is supplied. -/
noncomputable def element {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) : AxisFunction S (parameterDomain Ω) :=
  ⟨signedSquare (fields E T κ δ i), {
    smooth := (fields_regular E hT hδ hδT κ i).smooth.mono
      (Set.prod_mono (subset_univ _) (parameterDomain_subset Ω))
    holomorphic := fun r _ => ((fields_regular E hT hδ hδT κ i).holomorphic r (mem_univ r)).mono
      (parameterDomain_subset Ω)
    even := fun z _ r _ => ActivationHolomorphic.signedSquare_even _ z r
    real := by
      intro r _ eta heta
      change (fields E T κ δ i (r ^ 2, (eta : ℂ))).im = 0
      rw [fields_real E hT hδ hδT κ hP0 i _ (parameterDomain_real_interval heta)]
      rfl }⟩

theorem element_complexProfile {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) {X : ℝ} (hX : 0 ≤ X) (z : ℂ) :
    SlowRecursion.complexProfile (element E hT hδ hδT κ hP0 S i) (X, z) = fields E T κ δ i (X, z)
        := by
  change fields E T κ δ i (Real.sqrt X ^ 2, z) = _
  rw [Real.sq_sqrt hX]

theorem element_profile {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) {X eta : ℝ} (hX : 0 ≤ X) (heta : eta ∈ ReferencePath.parameterInterval) :
    SlowRecursion.profile (element E hT hδ hδT κ hP0 S i) (X, eta) =
      realFields (N := N) hT hδ hδT κ hP0 i (X, eta) := by
  have hc := (element_complexProfile E hT hδ hδT κ hP0 S i hX (eta : ℂ)).trans
    (fields_real E hT hδ hδT κ hP0 i X heta)
  exact congrArg Complex.re hc

theorem realFields_smooth {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (i : Fin 4) : ContDiffOn ℝ ∞ (realFields (N := N) hT hδ hδT κ hP0 i) N.radialDomain.carrier :=
        by
  let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
  fin_cases i
  · exact P.f_smooth
  · exact P.U_smooth
  · exact P.Ubar_smooth
  · exact P.pressure_smooth

theorem real_domain_mem (N : ReferencePath.Input) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) : (X, eta) ∈ N.radialDomain.carrier := by
  refine ⟨?_, heta⟩
  have := mul_nonneg N.scale_pos.le hX
  linarith

/-- The canonical right jets agree with the actual smooth ACT jets at the
axis as well as at every positive radius. -/
theorem element_right_jets {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) (k : ℕ) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    iteratedDerivWithin k (fun Y => SlowRecursion.profile (element E hT hδ hδT κ hP0 S i) (Y, eta))
        (Ici 0) X =
      iteratedDeriv k (fun Y => realFields (N := N) hT hδ hδT κ hP0 i (Y, eta)) X := by
  have he : EqOn (fun Y => SlowRecursion.profile (element E hT hδ hδT κ hP0 S i) (Y, eta))
      (fun Y => realFields (N := N) hT hδ hδT κ hP0 i (Y, eta)) (Ici 0) :=
    fun Y hY => element_profile E hT hδ hδT κ hP0 S i hY heta
  rw [iteratedDerivWithin_congr he hX]
  have hs : ContDiffAt ℝ ∞ (fun Y => realFields (N := N) hT hδ hδT κ hP0 i (Y, eta)) X :=
    ((realFields_smooth hT hδ hδT κ hP0 i).contDiffAt
      (N.radialDomain.isOpen.mem_nhds (real_domain_mem N hX heta))).comp X
      (contDiffAt_id.prodMk contDiffAt_const)
  simp only [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv_eq_iteratedFDeriv]
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Ici 0)
    (hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)) hX]

theorem element_profile_germ {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) {X eta : ℝ} (hX : 0 < X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    SlowRecursion.profile (element E hT hδ hδT κ hP0 S i) =ᶠ[𝓝 (X, eta)]
      realFields (N := N) hT hδ hδT κ hP0 i := by
  filter_upwards [(isOpen_Ioi.prod ReferencePath.parameterInterval_open).mem_nhds
    (show (X, eta) ∈ Ioi (0 : ℝ) ×ˢ ReferencePath.parameterInterval from ⟨hX, heta⟩)] with p hp
  exact element_profile E hT hδ hδT κ hP0 S i hp.1.le hp.2

/-- Base, constructed using `SlowRecursion.makeBase`. -/
noncomputable def base {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (C : ℝ) {S : ℝ} (hS : 0 < S) : Coefficient S (parameterDomain Ω) :=
  SlowRecursion.makeBase (domain E hS)
    (SlowRecursion.realConstant S (parameterDomain Ω) C * element E hT hδ hδT κ hP0 S 0)
    (element E hT hδ hδT κ hP0 S 1) (element E hT hδ hδT κ hP0 S 2)
    (element E hT hδ hδT κ hP0 S 3)

theorem base_values {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (C : ℝ) {S : ℝ} (hS : 0 < S) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := base E hT hδ hδT κ hP0 C hS
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    SlowRecursion.profile (A 0) (X, eta) = C * P.f (X, eta) ∧
    SlowRecursion.profile (A 1) (X, eta) = P.U (X, eta) ∧
    SlowRecursion.profile (A 2) (X, eta) = P.Ubar (X, eta) - P.U (X, eta) ∧
    SlowRecursion.profile (A 3) (X, eta) = P.pressure (X, eta) := by
  have hv (i : Fin 4) := element_profile E hT hδ hδT κ hP0 S i hX heta
  refine ⟨?_, hv 1, ?_, hv 3⟩
  · change ((C : ℂ) * element E hT hδ hδT κ hP0 S 0 (Real.sqrt X, (eta : ℂ))).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact congrArg (C * ·) (hv 0)
  · change (element E hT hδ hδT κ hP0 S 2 (Real.sqrt X, (eta : ℂ)) -
      element E hT hδ hδT κ hP0 S 1 (Real.sqrt X, (eta : ℂ))).re = _
    exact congrArg₂ (· - ·) (hv 2) (hv 1)

theorem base_beta_value {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (C : ℝ) {S : ℝ} (hS : 0 < S) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (S ^ 2))
    (heta : (eta : ℂ) ∈ parameterDomain Ω) :
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    SlowRecursion.profile (base E hT hδ hδT κ hP0 C hS 4) (X, eta) =
      SlowDivergence.radialFlux h 0 P.U (X, eta) / X := by
  let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
  let u := element E hT hδ hδT κ hP0 S 1
  let k := element E hT hδ hδT κ hP0 S 2 - u
  have hu : SlowRecursion.profile u =ᶠ[𝓝 (X, eta)] P.U :=
    element_profile_germ E hT hδ hδT κ hP0 S 1 hX.1 (parameterDomain_real_interval heta)
  have hk : SlowRecursion.profile k =ᶠ[𝓝 (X, eta)] PositiveAxisSystem.averageDefect P.U := by
    filter_upwards [(isOpen_Ioi.prod ReferencePath.parameterInterval_open).mem_nhds
      (show (X, eta) ∈ Ioi (0 : ℝ) ×ˢ ReferencePath.parameterInterval from
        ⟨hX.1, parameterDomain_real_interval heta⟩)] with q hq
    change (element E hT hδ hδT κ hP0 S 2 (Real.sqrt q.1, (q.2 : ℂ)) -
      element E hT hδ hδT κ hP0 S 1 (Real.sqrt q.1, (q.2 : ℂ))).re = _
    exact congrArg₂ (· - ·)
      (element_profile E hT hδ hδT κ hP0 S 2 hq.1.le hq.2)
      (element_profile E hT hδ hδT κ hP0 S 1 hq.1.le hq.2)
  have hb := congrArg Complex.re (SlowRecursion.betaOperator_value (domain E hS) 0 u k hX heta)
  have hcompare : PositiveAxisExistence.newBeta h 0 (SlowRecursion.profile u)
      (SlowRecursion.profile k) (X, eta) =
      PositiveAxisSystem.betaValue h 0 eta (PositiveAxisSystem.actualJet P.U (X, eta))
        (PositiveAxisSystem.actualJet (PositiveAxisSystem.averageDefect P.U) (X, eta)) := by
    simp only [PositiveAxisExistence.newBeta, PositiveAxisSystem.slowPower, Nat.cast_zero,
        mul_zero, zero_mul,
      PositiveAxisSystem.betaValue, PositiveAxisSystem.actualJet, hu.eq_of_nhds, hk.eq_of_nhds,
      SimilarityProfile.partialEta, hu.fderiv_eq, hk.fderiv_eq]
  exact hb.trans (hcompare.trans (PositiveAxisSystem.betaValue_averageDefect N.radialDomain
      P.U_smooth h 0
    (real_domain_mem N hX.1.le (parameterDomain_real_interval heta)) hX.1.ne'))

/-- A fixed radial rectangle strictly containing the entire initial collar. -/
noncomputable def axisRadius (N : ReferencePath.Input) (δ : ℝ) : ℝ :=
  Real.sqrt (N.endpoint * Real.exp δ) + 1

theorem axisRadius_pos (N : ReferencePath.Input) (δ : ℝ) : 0 < axisRadius N δ := by
  unfold axisRadius
  positivity

theorem collar_lt_square (N : ReferencePath.Input) (δ : ℝ) :
    N.endpoint * Real.exp δ < axisRadius N δ ^ 2 := by
  have hp : 0 ≤ N.endpoint * Real.exp δ := mul_nonneg N.endpoint_pos.le (Real.exp_pos δ).le
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (N.endpoint * Real.exp δ)
  unfold axisRadius
  nlinarith

/-- Hierarchy used in actual slow axis. -/
noncomputable def hierarchy {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0) (C : ℝ) :=
  let hc := axisRadius_pos N δ
  let c := domain E (SlowRecursion.radius_pos (buffer := 1) hc zero_lt_one 0)
  SlowRecursion.buildLocalHierarchy c hc zero_lt_one C
    (base E hT hδ hδT κ hP0 C (SlowRecursion.radius_pos (buffer := 1) hc zero_lt_one 0))

theorem hierarchy_base_values {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (C : ℝ) {X eta : ℝ} (hX : 0 ≤ X) (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := hierarchy E hT hδ hδT κ hP0 C
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    SlowRecursion.profile (A.coefficients 0 0) (X, eta) = C * P.f (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 1) (X, eta) = P.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 2) (X, eta) = P.Ubar (X, eta) - P.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 3) (X, eta) = P.pressure (X, eta) := by
  dsimp only
  simp only [(hierarchy E hT hδ hδT κ hP0 C).starts]
  exact base_values E hT hδ hδT κ hP0 C _ hX heta

theorem hierarchy_physical_swirl {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    {C : ℝ} (hC : C ≠ 0) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := hierarchy E hT hδ hδT κ hP0 C
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    Real.sqrt (2 * X) * SlowRecursion.profile (A.coefficients 0 0) (X, eta) / C = P.E (X, eta) := by
  have hv := (hierarchy_base_values E hT hδ hδT κ hP0 C hX heta).1
  dsimp only
  rw [hv]
  unfold ProfileHistories.Profiles.E
  field_simp

theorem hierarchy_on_collar {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0) (C : ℝ)
    {n : ℕ} (hn : 0 < n) {X eta : ℝ} (hX : 0 < X)
    (hcollar : X ≤ N.endpoint * Real.exp δ) (heta : eta ∈ Icc (-1 : ℝ) 1) :
    SlowRecursion.OrderEquations h C (hierarchy E hT hδ hδT κ hP0 C).coefficients n (X, eta) :=
  (hierarchy E hT hδ hδT κ hP0 C).equations n hn X
    ⟨hX, lt_of_le_of_lt hcollar (collar_lt_square N δ)⟩ eta (parameterDomain_real E.real_mem heta)

end ActualBase

section NaturalConstruction

variable {h j σ Λ C : ℝ} {g a : ℝ → ℝ} {cap : ℝ} {P0 : ℝ → ℝ}
variable (hp : PressureDatum.Admissible g a cap) (hP0 : P0 = PressureDatum.pressure g a)
variable {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
variable (F : NaturalEntrance.CoefficientProfile d Λ C) (hΛ : 0 < Λ)
variable (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)

include hp hP0 hsmall hσ in
theorem exists_tube_of_pressure_eq :
    ∃ ρ : ℝ, 0 < ρ ∧ Nonempty (InitialTube (ReferenceJetBounds.referenceInput F hΛ) h P0 (5 / Λ)
      (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow ρ)) := by
  subst P0
  exact ActivationHolomorphic.exists_initialTube hp F hΛ hsmall hσ

/-- Tube width, given by `Classical.choose (exists_tube_of_pressure_eq hp hP0 F hΛ hsmall hσ)`. -/
noncomputable def tubeWidth : ℝ := Classical.choose (exists_tube_of_pressure_eq hp hP0 F hΛ hsmall
    hσ)

theorem tubeWidth_pos : 0 < tubeWidth hp hP0 F hΛ hsmall hσ :=
  (Classical.choose_spec (exists_tube_of_pressure_eq hp hP0 F hΛ hsmall hσ)).1

/-- This witness is obtained from the actual coefficient-space natural
solution and the proved pressure integral, not supplied by the caller. -/
noncomputable def constructedTube : InitialTube (ReferenceJetBounds.referenceInput F hΛ) h P0 (5 /
    Λ)
    (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow (tubeWidth hp hP0 F hΛ
        hsmall hσ)) :=
  Classical.choice (Classical.choose_spec (exists_tube_of_pressure_eq hp hP0 F hΛ hsmall hσ)).2

include hp hP0 in
theorem actualPressure_smooth : ContDiff ℝ ∞ P0 := by
  rw [hP0]
  exact PressureDatum.pressure_contDiff hp

/-- From natural, given by `hierarchy (constructedTube hp hP0 F hΛ hsmall hσ) hT hδ hδT κ
(actualPressure_smooth hp hP0) C`. -/
noncomputable def fromNatural {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) :=
  hierarchy (constructedTube hp hP0 F hΛ hsmall hσ) hT hδ hδT κ (actualPressure_smooth hp hP0) C

theorem fromNatural_window {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    (eta : ℂ) ∈ parameterDomain
      (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow (tubeWidth hp hP0 F hΛ
          hsmall hσ)) :=
  parameterDomain_real (constructedTube hp hP0 F hΛ hsmall hσ).real_mem heta

theorem fromNatural_uniform_tube :
    ∃ τ : ℝ, 0 < τ ∧
      AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow τ ⊆
        parameterDomain (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow
          (tubeWidth hp hP0 F hΛ hsmall hσ)) := by
  exact ⟨min (tubeWidth hp hP0 F hΛ hsmall hσ) (1 / 40),
    lt_min (tubeWidth_pos hp hP0 F hΛ hsmall hσ) (by norm_num),
    smallTube_subset_domain (min_le_left _ _) (min_le_right _ _)⟩

theorem fromNatural_base_values {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    let P := StressActivation.FromReference.histories (ReferenceJetBounds.referenceInput F hΛ)
      hT hδ hδT κ P0 (actualPressure_smooth hp hP0)
    SlowRecursion.profile (A.coefficients 0 0) (X, eta) = C * P.f (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 1) (X, eta) = P.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 2) (X, eta) = P.Ubar (X, eta) - P.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 3) (X, eta) = P.pressure (X, eta) :=
  hierarchy_base_values (constructedTube hp hP0 F hΛ hsmall hσ) hT hδ hδT κ
    (actualPressure_smooth hp hP0) C hX heta

theorem fromNatural_positive_order {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) {n : ℕ} (hn : 0 < n)
    {X eta : ℝ} (hX : 0 < X)
    (hcollar : X ≤ (ReferenceJetBounds.referenceInput F hΛ).endpoint * Real.exp δ)
    (heta : eta ∈ Icc (-1 : ℝ) 1) :
    SlowRecursion.OrderEquations h C
      (fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ).coefficients n (X, eta) :=
  hierarchy_on_collar (constructedTube hp hP0 F hΛ hsmall hσ) hT hδ hδT κ
    (actualPressure_smooth hp hP0) C hn hX hcollar heta

theorem fromNatural_initial {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) {X eta : ℝ}
    (hX : 0 ≤ X) (hinitial : X ≤ 4 / Λ) (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    SlowRecursion.profile (A.coefficients 0 0) (X, eta) = C * F.family.f (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 1) (X, eta) = F.family.U (X, eta) := by
  have hv := fromNatural_base_values hp hP0 F hΛ hsmall hσ hT hδ hδT κ hX heta
  have he : X ≤ (ReferenceJetBounds.referenceInput F hΛ).endpoint := hinitial
  dsimp only at hv ⊢
  refine ⟨hv.1.trans ?_, hv.2.1.trans ?_⟩
  · change C * StressActivation.FromReference.f _ T κ δ (X, eta) = _
    rw [StressActivation.FromReference.f_eq_reference _ T κ δ he,
      ReferencePath.Input.refF_eq_natural_initial _ δ he]
    rfl
  · change StressActivation.FromReference.U _ T κ δ (X, eta) = _
    rw [StressActivation.FromReference.U_eq_reference _ T κ δ he,
      ReferencePath.Input.refU_eq_natural_initial _ δ he]
    rfl

theorem fromNatural_stock_prefix {T δ κ w₁ w₂ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit)
    (hb : δ ≤ (TransitionRamp.ofNatural F.family hΛ hsmall hδ hδT (actualPressure_smooth hp
        hP0)).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {X eta : ℝ} (hX : 0 ≤ X)
    (hcollar : X ≤ (ReferenceJetBounds.referenceInput F hΛ).endpoint * Real.exp δ)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    let Q := TransitionRamp.physicalProfiles F.family hΛ hsmall hδ hδT
      (actualPressure_smooth hp hP0) (κ := κ) hT hb hw₁ hw₂
    SlowRecursion.profile (A.coefficients 0 0) (X, eta) = C * Q.f (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 1) (X, eta) = Q.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 2) (X, eta) = Q.Ubar (X, eta) - Q.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 3) (X, eta) = Q.pressure (X, eta) := by
  let P := StressActivation.FromReference.histories (ReferenceJetBounds.referenceInput F hΛ)
    hT hδ hδT κ P0 (actualPressure_smooth hp hP0)
  let Q := TransitionRamp.physicalProfiles F.family hΛ hsmall hδ hδT
    (actualPressure_smooth hp hP0) (κ := κ) hT hb hw₁ hw₂
  have he (Y : ℝ) (hY : Y ≤ X) : Q.f (Y, eta) = P.f (Y, eta) ∧ Q.U (Y, eta) = P.U (Y, eta) :=
    TransitionRamp.physical_fields_eq_activation F.family hΛ hsmall hδ hδT
      (actualPressure_smooth hp hP0) hT hb hw₁ hw₂ heta (le_trans hY hcollar)
  have hhist := histories_congr_below Q P hX rfl
    (fun Y hY => (he Y hY.2).1) (fun Y hY => (he Y hY.2).2)
  have hv := fromNatural_base_values hp hP0 F hΛ hsmall hσ hT hδ hδT κ hX heta
  dsimp only at hv ⊢
  exact ⟨hv.1.trans (congrArg (C * ·) (he X le_rfl).1.symm),
    hv.2.1.trans (he X le_rfl).2.symm,
    hv.2.2.1.trans (congrArg₂ (· - ·) hhist.1.symm (he X le_rfl).2.symm),
    hv.2.2.2.trans hhist.2.symm⟩

theorem fromNatural_stock_fields {T δ κ w₁ w₂ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (hC : C ≠ 0)
    (hb : δ ≤ (TransitionRamp.ofNatural F.family hΛ hsmall hδ hδT (actualPressure_smooth hp
        hP0)).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {X eta : ℝ} (hX : 0 ≤ X)
    (hcollar : X ≤ (ReferenceJetBounds.referenceInput F hΛ).endpoint * Real.exp δ)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    let Q := TransitionRamp.physicalProfiles F.family hΛ hsmall hδ hδT
      (actualPressure_smooth hp hP0) (κ := κ) hT hb hw₁ hw₂
    Real.sqrt (2 * X) * SlowRecursion.profile (A.coefficients 0 0) (X, eta) / C = Q.E (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 1) (X, eta) = Q.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 3) (X, eta) = Q.pressure (X, eta) := by
  have hv := fromNatural_stock_prefix hp hP0 F hΛ hsmall hσ (κ := κ) hT hδ hδT hb hw₁ hw₂ hX
      hcollar heta
  refine ⟨?_, hv.2.1, hv.2.2.2⟩
  rw [hv.1]
  unfold ProfileHistories.Profiles.E
  field_simp

theorem fromNatural_profiles_smooth {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (n : ℕ) (i : Fin 5) :
    ContDiffOn ℝ ∞
      (SlowRecursion.profile ((fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ).coefficients n i))
      (Ico (0 : ℝ) (axisRadius (ReferenceJetBounds.referenceInput F hΛ) δ ^ 2) ×ˢ
        PositiveAxisExistence.realParameterDomain (parameterDomain
          (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow (tubeWidth hp hP0 F
              hΛ hsmall hσ)))) :=
  (fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ).profiles_smooth (axisRadius_pos _ _)
    (parameterDomain_open (constructedTube hp hP0 F hΛ hsmall hσ).isOpen) n i

theorem fromNatural_zero_axis {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) {n : ℕ} (hn : 0 < n)
    (i : Fin 5) {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    (fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ).coefficients n i (0, (eta : ℂ)) = 0 :=
  (fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ).zero_axis n hn i (eta : ℂ)
    (fromNatural_window hp hP0 F hΛ hsmall hσ heta)

theorem fromNatural_axis_jets {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (n : ℕ) (i : Fin 5) (k : ℕ)
    {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    let A := fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    iteratedDerivWithin k (fun X => SlowRecursion.profile (A.coefficients n i) (X, eta)) (Ici 0) 0 =
      ((k.factorial : ℝ) / ((2 * k).factorial : ℝ)) •
        iteratedDeriv (2 * k) (fun r => (A.coefficients n i (r, (eta : ℂ))).re) 0 :=
  SlowRecursion.profile_axis_jet (axisRadius_pos _ _) _
    (fromNatural_window hp hP0 F hΛ hsmall hσ heta) k

end NaturalConstruction

end NavierStokes.ActualSlowAxis
