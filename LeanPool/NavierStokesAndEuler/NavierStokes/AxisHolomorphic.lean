/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisEvaluation
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral

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
