/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisCoefficientSpace
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.EReal.Inv
public import Mathlib.Tactic.GCongr

@[expose] public section

/-!
# Evaluation of the complete axis coefficient space

The evaluation series is constructed from the actual coefficient functions.
Its mixed derivative series are proved convergent before their derivatives
and smoothness are established.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates

namespace NavierStokes.AxisEvaluation

def polynomialJet (n k : ℕ) (Y : ℝ) : ℝ :=
  (n.descFactorial k : ℝ) * Y ^ (n - k)

theorem polynomialJet_hasDerivAt (n k : ℕ) (Y : ℝ) :
    HasDerivAt (polynomialJet n k) (polynomialJet n (k + 1) Y) Y := by
  have hd := (hasDerivAt_pow (n - k) Y).const_mul (n.descFactorial k : ℝ)
  change HasDerivAt (fun x : ℝ => (n.descFactorial k : ℝ) * x ^ (n - k)) _ Y
  convert! hd using 1
  simp only [polynomialJet, Nat.descFactorial_succ, Nat.cast_mul]
  have he : n - (k + 1) = n - k - 1 := by omega
  rw [he]
  ring

def term (I : Window) (ε : ℝ) (A : AxisSpace I ε) (k m n : ℕ) (p : ℝ × ℝ) : ℝ :=
  polynomialJet n k p.1 * jet I (weight ε) A.1 n m p.2

def mixedSeries (I : Window) (ε : ℝ) (A : AxisSpace I ε) (k m : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑' n : ℕ, term I ε A k m n p

def profile (I : Window) (ε : ℝ) (A : AxisSpace I ε) (p : ℝ × ℝ) : ℝ :=
  ∑' n : ℕ, p.1 ^ n * coefficient I (weight ε) A n p.2

theorem mixedSeries_zero (I : Window) (ε : ℝ) (A : AxisSpace I ε) :
    mixedSeries I ε A 0 0 = profile I ε A := by
  funext p
  simp [mixedSeries, profile, term, polynomialJet, coefficient]

/-- A deliberately simple polynomial-geometric majorant. -/
def majorant (ε C R : ℝ) (k m n : ℕ) : ℝ :=
  (C * (ε⁻¹) ^ m * (m.factorial : ℝ) * ((m : ℝ) + 1) ^ m) *
    (((n : ℝ) + 1) ^ (k + m) * (R / 20) ^ n)

theorem weight_upper {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    weight ε n m ≤ (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * (m.factorial : ℝ) *
      (((m : ℝ) + 1) ^ m * ((n : ℝ) + 1) ^ m) := by
  have hchoose : ((n + m).choose m : ℝ) ≤ ((n : ℝ) + m) ^ m := by
    exact_mod_cast Nat.choose_le_pow (n + m) m
  have hnm : (n : ℝ) + m ≤ ((m : ℝ) + 1) * ((n : ℝ) + 1) := by
    nlinarith [show (0 : ℝ) ≤ n by positivity, show (0 : ℝ) ≤ m by positivity,
      mul_nonneg (show (0 : ℝ) ≤ n by positivity) (show (0 : ℝ) ≤ m by positivity)]
  have hc : ((n + m).choose m : ℝ) ≤ ((m : ℝ) + 1) ^ m * ((n : ℝ) + 1) ^ m := by
    calc
      _ ≤ ((n : ℝ) + m) ^ m := hchoose
      _ ≤ (((m : ℝ) + 1) * ((n : ℝ) + 1)) ^ m := by gcongr
      _ = _ := mul_pow _ _ _
  have hden : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 := by
    have hn : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [show (0 : ℝ) ≤ n by positivity]
    have hm : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith [show (0 : ℝ) ≤ m by positivity]
    nlinarith
  unfold weight
  calc
    _ ≤ (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * (m.factorial : ℝ) * ((n + m).choose m : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hn : 0 ≤ (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * (m.factorial : ℝ) *
          ((n + m).choose m : ℝ) := by positivity
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

theorem polynomialJet_bound {R Y : ℝ} (hR : 1 ≤ R) (hY : |Y| ≤ R) (n k : ℕ) :
    |polynomialJet n k Y| ≤ ((n : ℝ) + 1) ^ k * R ^ n := by
  have hd : (n.descFactorial k : ℝ) ≤ ((n : ℝ) + 1) ^ k := by
    have hdn : (n.descFactorial k : ℝ) ≤ (n : ℝ) ^ k := by
      exact_mod_cast Nat.descFactorial_le_pow n k
    exact hdn.trans (by gcongr; linarith)
  have hp : |Y| ^ (n - k) ≤ R ^ n := by
    calc
      _ ≤ R ^ (n - k) := by gcongr
      _ ≤ R ^ n := pow_le_pow_right₀ hR (Nat.sub_le n k)
  simp only [polynomialJet, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ n.descFactorial k by positivity), abs_pow]
  exact mul_le_mul hd hp (by positivity) (by positivity)

theorem term_bound (I : Window) {ε R : ℝ} (hε : 0 < ε) (hR : 1 ≤ R)
    (A : AxisSpace I ε) (k m n : ℕ) {p : ℝ × ℝ} (hp : |p.1| ≤ R) :
    ‖term I ε A k m n p‖ ≤ majorant ε ‖A‖ R k m n := by
  have hj : |jet I (weight ε) A.1 n m p.2| ≤ weight ε n m * ‖A‖ := by
    simpa only [abs_of_pos (weight_pos hε n m)] using abs_jet_le I (weight ε) A n m p.2
  rw [term, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (((n : ℝ) + 1) ^ k * R ^ n) * (weight ε n m * ‖A‖) :=
      mul_le_mul (polynomialJet_bound hR hp n k) hj (abs_nonneg _)
        (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
    _ ≤ (((n : ℝ) + 1) ^ k * R ^ n) *
      (((1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * (m.factorial : ℝ) *
        (((m : ℝ) + 1) ^ m * ((n : ℝ) + 1) ^ m)) * ‖A‖) := by
      gcongr
      exact weight_upper hε n m
    _ = _ := by
      unfold majorant
      simp only [pow_add, div_pow, one_pow]
      ring

theorem summable_majorant {ε C R : ℝ} (hR : 1 ≤ R) (hR20 : R < 20) (k m : ℕ) :
    Summable (majorant ε C R k m) := by
  have hr : 0 < R / 20 := by positivity
  have hr1 : ‖R / 20‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr]; linarith
  have hs : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (k + m) * (R / 20) ^ (n + 1)) :=
    (summable_pow_mul_geometric_of_norm_lt_one (k + m) hr1).comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) by intro n j hj; exact Nat.add_right_cancel hj)
  have ht : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (k + m) * (R / 20) ^ n) := by
    simpa only [Nat.cast_add, Nat.cast_one, pow_succ, mul_assoc,
      mul_inv_cancel₀ hr.ne', mul_one] using hs.mul_right (R / 20)⁻¹
  exact ht.mul_left _

theorem summable_term (I : Window) {ε R : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hR20 : R < 20) (A : AxisSpace I ε) (k m : ℕ)
    {p : ℝ × ℝ} (hp : |p.1| ≤ R) : Summable (fun n => term I ε A k m n p) :=
  .of_norm_bounded (summable_majorant hR hR20 k m) (fun n => term_bound I hε hR A k m n hp)

theorem term_continuous (I : Window) (ε : ℝ) (A : AxisSpace I ε) (k m n : ℕ) :
    Continuous (term I ε A k m n) := by
  exact (continuous_const.mul (continuous_fst.pow (n - k))).mul
    ((continuous_jet I (weight ε) A.1 n m).comp continuous_snd)

/-- Uniform convergence of every mixed derivative series on every strictly
smaller closed radial interval, uniformly over the parameter interval. In
fact the clamped coefficient extension gives uniformity over all real `η`. -/
theorem mixedSeries_uniform (I : Window) {ε R : ℝ} (hε : 0 < ε) (hR20 : R < 20)
    (A : AxisSpace I ε) (k m : ℕ) :
    TendstoUniformlyOn
      (fun N (p : ℝ × ℝ) => ∑ n ∈ Finset.range N, term I ε A k m n p)
      (mixedSeries I ε A k m) atTop {p : ℝ × ℝ | |p.1| ≤ R} := by
  have hmax : max 1 R < 20 := max_lt (by norm_num) hR20
  exact tendstoUniformlyOn_tsum_nat (summable_majorant (le_max_left 1 R) hmax k m)
    (fun n p hp => term_bound I hε (le_max_left 1 R) A k m n
      (hp.trans (le_max_right 1 R)))

def strip (I : Window) (R : ℝ) : Set (ℝ × ℝ) :=
  Ioo (-R) R ×ˢ Ioo I.left I.right

theorem strip_isOpen (I : Window) (R : ℝ) : IsOpen (strip I R) :=
  isOpen_Ioo.prod isOpen_Ioo

theorem strip_isPreconnected (I : Window) (R : ℝ) : IsPreconnected (strip I R) :=
  isPreconnected_Ioo.prod isPreconnected_Ioo

def linearForm (u v : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  u • ContinuousLinearMap.fst ℝ ℝ ℝ + v • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem linearForm_norm (u v : ℝ) : ‖linearForm u v‖ ≤ |u| + |v| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (abs_nonneg _) (abs_nonneg _))
  intro x
  calc
    ‖linearForm u v x‖ = |u * x.1 + v * x.2| := rfl
    _ ≤ |u * x.1| + |v * x.2| := abs_add_le _ _
    _ = |u| * ‖x.1‖ + |v| * ‖x.2‖ := by simp only [abs_mul, Real.norm_eq_abs]
    _ ≤ |u| * ‖x‖ + |v| * ‖x‖ := add_le_add
      (mul_le_mul_of_nonneg_left (norm_fst_le x) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (norm_snd_le x) (abs_nonneg _))
    _ = (|u| + |v|) * ‖x‖ := by ring

theorem term_hasFDerivAt (I : Window) (ε : ℝ) (A : AxisSpace I ε) (k m n : ℕ)
    {p : ℝ × ℝ} (hp : p.2 ∈ Ioo I.left I.right) :
    HasFDerivAt (term I ε A k m n)
      (linearForm (term I ε A (k + 1) m n p) (term I ε A k (m + 1) n p)) p := by
  have hy := (polynomialJet_hasDerivAt n k p.1).comp_hasFDerivAt p
    (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ))
  have hη := (hasDerivAt_jet_interior I (weight ε) A n m hp).comp_hasFDerivAt p
    (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ))
  change HasFDerivAt (fun x : ℝ × ℝ => polynomialJet n k x.1 * jet I (weight ε) A.1 n m x.2) _ p
  convert! hy.mul hη using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [linearForm, term]
  ring

theorem linearForm_tsum {u v : ℕ → ℝ} (hu : Summable u) (hv : Summable v) :
    (∑' n, linearForm (u n) (v n)) = linearForm (∑' n, u n) (∑' n, v n) := by
  unfold linearForm
  rw [Summable.tsum_add (hu.smul_const _) (hv.smul_const _),
    hu.tsum_smul_const, hv.tsum_smul_const]

theorem mixedSeries_hasFDerivAt_strip (I : Window) {ε R : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hR20 : R < 20) (A : AxisSpace I ε) (k m : ℕ)
    {p : ℝ × ℝ} (hp : p ∈ strip I R) :
    HasFDerivAt (mixedSeries I ε A k m)
      (linearForm (mixedSeries I ε A (k + 1) m p) (mixedSeries I ε A k (m + 1) p)) p := by
  have hpR : |p.1| ≤ R := (abs_lt.mpr hp.1).le
  have hu := (summable_majorant (ε := ε) (C := ‖A‖) hR hR20 (k + 1) m).add
    (summable_majorant (ε := ε) (C := ‖A‖) hR hR20 k (m + 1))
  have hd := hasFDerivAt_tsum_of_isPreconnected (f := fun n => term I ε A k m n)
    (f' := fun n x => linearForm (term I ε A (k + 1) m n x) (term I ε A k (m + 1) n x))
    hu (strip_isOpen I R) (strip_isPreconnected I R)
    (fun n x hx => term_hasFDerivAt I ε A k m n hx.2)
    (fun n x hx => (linearForm_norm _ _).trans (add_le_add
      (term_bound I hε hR A (k + 1) m n (abs_lt.mpr hx.1).le)
      (term_bound I hε hR A k (m + 1) n (abs_lt.mpr hx.1).le)))
    hp (summable_term I hε hR hR20 A k m hpR) hp
  rw [linearForm_tsum (summable_term I hε hR hR20 A (k + 1) m hpR)
    (summable_term I hε hR hR20 A k (m + 1) hpR)] at hd
  exact hd

/-- Actual joint differentiation of every mixed derivative series. -/
theorem mixedSeries_hasFDerivAt (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m : ℕ) {p : ℝ × ℝ} (hp : p ∈ strip I 20) :
    HasFDerivAt (mixedSeries I ε A k m)
      (linearForm (mixedSeries I ε A (k + 1) m p) (mixedSeries I ε A k (m + 1) p)) p := by
  have hmax : max 1 |p.1| < 20 := max_lt (by norm_num) (abs_lt.mpr hp.1)
  obtain ⟨R, hR, hR20⟩ := exists_between hmax
  have hR1 : 1 ≤ R := (le_max_left 1 |p.1|).trans hR.le
  have hpR : p ∈ strip I R :=
    ⟨abs_lt.mp ((le_max_right 1 |p.1|).trans_lt hR), hp.2⟩
  exact mixedSeries_hasFDerivAt_strip I hε hR1 hR20 A k m hpR

theorem mixedSeries_contDiffAt_nat (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (r : ℕ) :
    ∀ (k m : ℕ) (p : ℝ × ℝ), p ∈ strip I 20 →
      ContDiffAt ℝ r (mixedSeries I ε A k m) p := by
  induction r with
  | zero =>
      intro k m p hp
      refine contDiffAt_zero.mpr ⟨strip I 20, (strip_isOpen I 20).mem_nhds hp, ?_⟩
      intro x hx
      exact (mixedSeries_hasFDerivAt I hε A k m hx).continuousAt.continuousWithinAt
  | succ r ih =>
      intro k m p hp
      apply contDiffAt_succ_iff_hasFDerivAt.mpr
      refine ⟨fun x => linearForm (mixedSeries I ε A (k + 1) m x)
        (mixedSeries I ε A k (m + 1) x), ?_, ?_⟩
      · exact ⟨strip I 20, (strip_isOpen I 20).mem_nhds hp,
          fun x hx => mixedSeries_hasFDerivAt I hε A k m hx⟩
      · exact ((ih (k + 1) m p hp).smul contDiffAt_const).add
          ((ih k (m + 1) p hp).smul contDiffAt_const)

/-- The evaluated profile is jointly smooth. This is a consequence of the
proved derivative equations, not an assumed property of the infinite sum. -/
theorem mixedSeries_smooth (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m : ℕ) {p : ℝ × ℝ} (hp : p ∈ strip I 20) :
    ContDiffAt ℝ ∞ (mixedSeries I ε A k m) p :=
  contDiffAt_infty.mpr (fun r => mixedSeries_contDiffAt_nat I hε A r k m p hp)

theorem profile_smooth (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) : ContDiffOn ℝ ∞ (profile I ε A) (strip I 20) := by
  rw [← mixedSeries_zero]
  intro p hp
  exact (mixedSeries_smooth I hε A 0 0 hp).contDiffWithinAt

theorem mixedSeries_hasDerivAt_Y (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m : ℕ) {Y η : ℝ}
    (hY : Y ∈ Ioo (-20 : ℝ) 20) (hη : η ∈ Ioo I.left I.right) :
    HasDerivAt (fun y => mixedSeries I ε A k m (y, η))
      (mixedSeries I ε A (k + 1) m (Y, η)) Y := by
  have hd := mixedSeries_hasFDerivAt I hε A k m (p := (Y, η)) ⟨hY, hη⟩
  simpa [linearForm, Function.comp_def] using hd.comp_hasDerivAt Y
    ((hasDerivAt_id Y).prodMk (hasDerivAt_const Y η))

theorem mixedSeries_hasDerivAt_eta (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m : ℕ) {Y η : ℝ}
    (hY : Y ∈ Ioo (-20 : ℝ) 20) (hη : η ∈ Ioo I.left I.right) :
    HasDerivAt (fun x => mixedSeries I ε A k m (Y, x))
      (mixedSeries I ε A k (m + 1) (Y, η)) η := by
  have hd := mixedSeries_hasFDerivAt I hε A k m (p := (Y, η)) ⟨hY, hη⟩
  simpa [linearForm, Function.comp_def] using hd.comp_hasDerivAt η
    ((hasDerivAt_const η Y).prodMk (hasDerivAt_id η))

theorem iteratedDeriv_Y (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m r : ℕ) {Y η : ℝ}
    (hY : Y ∈ Ioo (-20 : ℝ) 20) (hη : η ∈ Ioo I.left I.right) :
    iteratedDeriv r (fun y => mixedSeries I ε A k m (y, η)) Y =
      mixedSeries I ε A (k + r) m (Y, η) := by
  induction r generalizing Y with
  | zero => simp
  | succ r ih =>
      rw [iteratedDeriv_succ]
      have heq : (iteratedDeriv r (fun y => mixedSeries I ε A k m (y, η))) =ᶠ[𝓝 Y]
          (fun y => mixedSeries I ε A (k + r) m (y, η)) := by
        filter_upwards [Ioo_mem_nhds hY.1 hY.2] with y hy
        exact ih hy
      rw [heq.deriv_eq, (mixedSeries_hasDerivAt_Y I hε A (k + r) m hY hη).deriv]
      simp only [Nat.add_assoc]

theorem iteratedDeriv_eta (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m r : ℕ) {Y η : ℝ}
    (hY : Y ∈ Ioo (-20 : ℝ) 20) (hη : η ∈ Ioo I.left I.right) :
    iteratedDeriv r (fun x => mixedSeries I ε A k m (Y, x)) η =
      mixedSeries I ε A k (m + r) (Y, η) := by
  induction r generalizing η with
  | zero => simp
  | succ r ih =>
      rw [iteratedDeriv_succ]
      have heq : (iteratedDeriv r (fun x => mixedSeries I ε A k m (Y, x))) =ᶠ[𝓝 η]
          (fun x => mixedSeries I ε A k (m + r) (Y, x)) := by
        filter_upwards [Ioo_mem_nhds hη.1 hη.2] with x hx
        exact ih hx
      rw [heq.deriv_eq, (mixedSeries_hasDerivAt_eta I hε A k (m + r) hY hη).deriv]
      simp only [Nat.add_assoc]

/-- The series is the actual mixed derivative of the evaluated profile. -/
theorem mixed_derivative_profile (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m : ℕ) {Y η : ℝ}
    (hY : Y ∈ Ioo (-20 : ℝ) 20) (hη : η ∈ Ioo I.left I.right) :
    iteratedDeriv m (fun x => iteratedDeriv k (fun y => profile I ε A (y, x)) Y) η =
      ∑' n : ℕ, (n.descFactorial k : ℝ) * Y ^ (n - k) *
        jet I (weight ε) A.1 n m η := by
  rw [← mixedSeries_zero]
  have heq :
      (fun x => iteratedDeriv k (fun y => mixedSeries I ε A 0 0 (y, x)) Y) =ᶠ[𝓝 η]
        (fun x => mixedSeries I ε A k 0 (Y, x)) := by
    filter_upwards [Ioo_mem_nhds hη.1 hη.2] with x hx
    simpa only [Nat.zero_add] using iteratedDeriv_Y I hε A 0 0 k hY hx
  rw [heq.iteratedDeriv_eq m, iteratedDeriv_eta I hε A k 0 m hY hη]
  simp only [Nat.zero_add, mixedSeries, term, polynomialJet]

def jetBound (ε R : ℝ) (k m : ℕ) : ℝ := ∑' n : ℕ, majorant ε 1 R k m n

theorem majorant_scale (ε C R : ℝ) (k m n : ℕ) :
    majorant ε C R k m n = C * majorant ε 1 R k m n := by
  unfold majorant
  ring

theorem jetBound_nonneg {ε R : ℝ} (hε : 0 < ε) (hR : 1 ≤ R) (k m : ℕ) :
    0 ≤ jetBound ε R k m := by
  apply tsum_nonneg
  intro n
  unfold majorant
  positivity

/-- The evaluated mixed derivatives depend boundedly on the coefficient
space norm, uniformly on every smaller radial interval. -/
theorem mixedSeries_bound (I : Window) {ε R : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hR20 : R < 20) (A : AxisSpace I ε) (k m : ℕ)
    {p : ℝ × ℝ} (hp : |p.1| ≤ R) :
    ‖mixedSeries I ε A k m p‖ ≤ jetBound ε R k m * ‖A‖ := by
  calc
    _ ≤ ∑' n : ℕ, majorant ε ‖A‖ R k m n :=
      tsum_of_norm_bounded (summable_majorant hR hR20 k m).hasSum
        (fun n => term_bound I hε hR A k m n hp)
    _ = jetBound ε R k m * ‖A‖ := by
      have he : (fun n => majorant ε ‖A‖ R k m n) =
          (fun n => ‖A‖ * majorant ε 1 R k m n) :=
        funext (fun n => majorant_scale ε ‖A‖ R k m n)
      rw [he]
      rw [tsum_mul_left]
      exact mul_comm _ _

/-- Absolute convergence holds at every point of the radius-20 domain. -/
theorem mixedSeries_summable (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m : ℕ) {p : ℝ × ℝ} (hp : |p.1| < 20) :
    Summable (fun n => term I ε A k m n p) :=
  summable_term I hε (le_max_left 1 |p.1|) (max_lt (by norm_num) hp) A k m
    (le_max_right 1 |p.1|)

theorem profile_hasSum (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {p : ℝ × ℝ} (hp : |p.1| < 20) :
    HasSum (fun n : ℕ => p.1 ^ n * coefficient I (weight ε) A n p.2) (profile I ε A p) := by
  simpa only [term, polynomialJet, Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero,
    one_mul, coefficient, mixedSeries, profile] using (mixedSeries_summable I hε A 0 0 hp).hasSum

theorem term_add (I : Window) (ε : ℝ) (A B : AxisSpace I ε) (k m n : ℕ) (p : ℝ × ℝ) :
    term I ε (A + B) k m n p = term I ε A k m n p + term I ε B k m n p := by
  simp only [term, Submodule.coe_add, jet_add, mul_add]

theorem term_smul (I : Window) (ε c : ℝ) (A : AxisSpace I ε) (k m n : ℕ) (p : ℝ × ℝ) :
    term I ε (c • A) k m n p = c * term I ε A k m n p := by
  simp only [term, Submodule.coe_smul, jet_smul]
  ring

theorem term_sub (I : Window) (ε : ℝ) (A B : AxisSpace I ε) (k m n : ℕ) (p : ℝ × ℝ) :
    term I ε (A - B) k m n p = term I ε A k m n p - term I ε B k m n p := by
  simp only [term, Submodule.coe_sub, jet_sub, mul_sub]

theorem mixedSeries_add (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A B : AxisSpace I ε) (k m : ℕ) {p : ℝ × ℝ} (hp : |p.1| < 20) :
    mixedSeries I ε (A + B) k m p = mixedSeries I ε A k m p + mixedSeries I ε B k m p := by
  simp only [mixedSeries, term_add]
  exact (mixedSeries_summable I hε A k m hp).tsum_add (mixedSeries_summable I hε B k m hp)

theorem mixedSeries_smul (I : Window) (ε c : ℝ)
    (A : AxisSpace I ε) (k m : ℕ) (p : ℝ × ℝ) :
    mixedSeries I ε (c • A) k m p = c * mixedSeries I ε A k m p := by
  simp only [mixedSeries, term_smul, tsum_mul_left]

theorem mixedSeries_sub (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A B : AxisSpace I ε) (k m : ℕ) {p : ℝ × ℝ} (hp : |p.1| < 20) :
    mixedSeries I ε (A - B) k m p = mixedSeries I ε A k m p - mixedSeries I ε B k m p := by
  simp only [mixedSeries, term_sub]
  exact (mixedSeries_summable I hε A k m hp).tsum_sub (mixedSeries_summable I hε B k m hp)

def evaluationLinearMap (I : Window) {ε : ℝ} (hε : 0 < ε)
    (k m : ℕ) (p : ℝ × ℝ) (hp : |p.1| < 20) : AxisSpace I ε →ₗ[ℝ] ℝ where
  toFun A := mixedSeries I ε A k m p
  map_add' A B := mixedSeries_add I hε A B k m hp
  map_smul' c A := by simpa using mixedSeries_smul I ε c A k m p

/-- Bounded evaluation of each actual mixed derivative from the complete
coefficient space. The constant is uniform in the parameter coordinate. -/
def evaluationCLM (I : Window) {ε R : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hR20 : R < 20) (k m : ℕ) (p : ℝ × ℝ) (hp : |p.1| ≤ R) :
    AxisSpace I ε →L[ℝ] ℝ :=
  (evaluationLinearMap I hε k m p (hp.trans_lt hR20)).mkContinuous (jetBound ε R k m)
    (fun A => mixedSeries_bound I hε hR hR20 A k m hp)

@[simp] theorem evaluationCLM_apply (I : Window) {ε R : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hR20 : R < 20) (k m : ℕ) (p : ℝ × ℝ) (hp : |p.1| ≤ R)
    (A : AxisSpace I ε) :
    evaluationCLM I hε hR hR20 k m p hp A = mixedSeries I ε A k m p := rfl

/-- Norm convergence in the coefficient space controls every evaluated jet
uniformly throughout a smaller radial interval. -/
theorem mixedSeries_sub_bound (I : Window) {ε R : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hR20 : R < 20) (A B : AxisSpace I ε) (k m : ℕ)
    {p : ℝ × ℝ} (hp : |p.1| ≤ R) :
    ‖mixedSeries I ε A k m p - mixedSeries I ε B k m p‖ ≤
      jetBound ε R k m * ‖A - B‖ := by
  calc
    _ = ‖mixedSeries I ε (A - B) k m p‖ := by
      rw [mixedSeries_sub I hε A B k m (hp.trans_lt hR20)]
    _ ≤ _ := mixedSeries_bound I hε hR hR20 (A - B) k m hp

theorem profile_smooth_radius (I : Window) {ε R : ℝ} (hε : 0 < ε) (hR20 : R < 20)
    (A : AxisSpace I ε) : ContDiffOn ℝ ∞ (profile I ε A) (strip I R) := by
  apply (profile_smooth I hε A).mono
  intro p hp
  exact ⟨⟨(neg_lt_neg hR20).trans hp.1.1, hp.1.2.trans hR20⟩, hp.2⟩

theorem coefficient_iteratedDeriv (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (n m : ℕ) {η : ℝ} (hη : η ∈ Ioo I.left I.right) :
    iteratedDeriv m (coefficient I (weight ε) A n) η = jet I (weight ε) A.1 n m η := by
  induction m generalizing η with
  | zero => rfl
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv m (coefficient I (weight ε) A n) =ᶠ[𝓝 η]
          jet I (weight ε) A.1 n m := by
        filter_upwards [Ioo_mem_nhds hη.1 hη.2] with x hx
        exact ih hx
      rw [heq.deriv_eq, (hasDerivAt_jet_interior I (weight ε) A n m hη).deriv]

/-- Termwise mixed differentiation stated entirely using ordinary
derivatives of the actual coefficient functions. -/
theorem mixed_derivative_profile_coefficients (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m : ℕ) {Y η : ℝ}
    (hY : Y ∈ Ioo (-20 : ℝ) 20) (hη : η ∈ Ioo I.left I.right) :
    iteratedDeriv m (fun x => iteratedDeriv k (fun y => profile I ε A (y, x)) Y) η =
      ∑' n : ℕ, (n.descFactorial k : ℝ) * Y ^ (n - k) *
        iteratedDeriv m (coefficient I (weight ε) A n) η := by
  rw [mixed_derivative_profile I hε A k m hY hη]
  apply tsum_congr
  intro n
  rw [coefficient_iteratedDeriv I ε A n m hη]

/-- A window larger than the target interval, with arbitrarily small margin. -/
def enlargedUnitWindow (δ : ℝ) (hδ : 0 < δ) : Window where
  left := -1 - δ
  right := 1 + δ
  nondegenerate := by linarith

theorem unitInterval_in_enlargedWindow {δ : ℝ} (hδ : 0 < δ) :
    Icc (-1 : ℝ) 1 ⊆ Ioo (enlargedUnitWindow δ hδ).left (enlargedUnitWindow δ hδ).right := by
  intro x hx
  constructor <;> dsimp [enlargedUnitWindow] <;> linarith [hx.1, hx.2]

/-- In particular both endpoints of the target interval `[-1,1]` have
ordinary open-neighborhood smoothness; no endpoint extension is assumed. -/
theorem profile_smooth_target {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (A : AxisSpace (enlargedUnitWindow δ hδ) ε) {Y η : ℝ}
    (hY : Y ∈ Ioo (-20 : ℝ) 20) (hη : η ∈ Icc (-1 : ℝ) 1) :
    ContDiffAt ℝ ∞ (profile (enlargedUnitWindow δ hδ) ε A) (Y, η) := by
  rw [← mixedSeries_zero]
  exact mixedSeries_smooth _ hε A 0 0 ⟨hY, unitInterval_in_enlargedWindow hδ hη⟩

end NavierStokes.AxisEvaluation
