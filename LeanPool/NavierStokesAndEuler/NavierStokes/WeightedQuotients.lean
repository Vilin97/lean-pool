/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatCutoff
public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatZeroExtension
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Square roots and signed quotients from weighted derivative bounds

The estimates use genuine Fréchet derivatives. A normalization used in a
pointwise estimate is constant in the differentiation variable: no regularity
of the quotient by a variable flat weight is assumed.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace NavierStokes.WeightedQuotients

theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

noncomputable def rpowCoeff (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => rpowCoeff p n * (p - (n : ℝ))

/-- Actual scalar derivatives of a real power on the positive half-line. -/
theorem iteratedDeriv_rpow (p : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv n (fun t : ℝ => t ^ p) t = rpowCoeff p n * t ^ (p - (n : ℝ)) := by
  induction n generalizing t with
  | zero => simp [rpowCoeff]
  | succ n ih =>
      have he : iteratedDeriv n (fun t : ℝ => t ^ p) =ᶠ[𝓝 t]
          (fun t => rpowCoeff p n * t ^ (p - (n : ℝ))) := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
        exact ih hx
      have hd := (Real.hasDerivAt_rpow_const (p := p - (n : ℝ))
        (Or.inl ht.ne')).const_mul (rpowCoeff p n)
      rw [iteratedDeriv_succ, (hd.congr_of_eventuallyEq he).deriv]
      simp only [rpowCoeff, Nat.cast_add, Nat.cast_one]
      rw [show p - (n : ℝ) - 1 = p - ((n : ℝ) + 1) by ring]
      ring

def coeffBound (p : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), |rpowCoeff p k|) + 1

theorem coeffBound_nonneg (p : ℝ) (n : ℕ) : 0 ≤ coeffBound p n := by
  unfold coeffBound
  positivity

theorem abs_coeff_le (p : ℝ) {i n : ℕ} (hi : i ≤ n) : |rpowCoeff p i| ≤ coeffBound p n := by
  have him : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  have hs : |rpowCoeff p i| ≤ ∑ k ∈ Finset.range (n + 1), |rpowCoeff p k| :=
    Finset.single_le_sum (f := fun k => |rpowCoeff p k|) (fun k _ => abs_nonneg _) him
  exact hs.trans (le_add_of_nonneg_right zero_le_one)

theorem rpow_jet_bound (p : ℝ) {B t : ℝ} (hB : 1 ≤ B) (ht : 0 < t)
    (hp : t ^ p ≤ B) (hi : t⁻¹ ≤ B) {i n : ℕ} (hin : i ≤ n) :
    ‖iteratedFDeriv ℝ i (fun t : ℝ => t ^ p) t‖ ≤ coeffBound p n * B ^ (n + 1) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have htpi : 0 ≤ t ^ p := (Real.rpow_pos_of_pos ht p).le
  have hpow : (t⁻¹) ^ i ≤ B ^ i := by gcongr
  have hmain : t ^ (p - (i : ℝ)) ≤ B * B ^ i := by
    rw [Real.rpow_sub ht, Real.rpow_natCast, div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul hp hpow (pow_nonneg (inv_nonneg.mpr ht.le) _) hB0
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_rpow p i ht,
    Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _)]
  calc
    _ ≤ coeffBound p n * (B * B ^ i) :=
      mul_le_mul (abs_coeff_le p hin) hmain (Real.rpow_pos_of_pos ht _).le
        (coeffBound_nonneg p n)
    _ = coeffBound p n * B ^ (i + 1) := by rw [pow_succ]; ring
    _ ≤ coeffBound p n * B ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (Nat.add_le_add_right hin 1))
        (coeffBound_nonneg p n)

theorem sqrt_le_of_bounds {B t : ℝ} (hB : 1 ≤ B) (ht : 0 ≤ t) (hu : t ≤ B) :
    Real.sqrt t ≤ B := by
  have hs := Real.sq_sqrt ht
  have hsn := Real.sqrt_nonneg t
  nlinarith

theorem half_power_bound {B t : ℝ} (hB : 1 ≤ B) (ht : 0 < t) (hu : t ≤ B) :
    t ^ (1 / 2 : ℝ) ≤ B := by
  rw [← Real.sqrt_eq_rpow]
  exact sqrt_le_of_bounds hB ht.le hu

theorem neg_half_power_bound {B t : ℝ} (hB : 1 ≤ B) (ht : 0 < t) (hi : t⁻¹ ≤ B) :
    t ^ (-(1 / 2 : ℝ)) ≤ B := by
  rw [Real.rpow_neg ht.le, ← Real.inv_rpow ht.le, ← Real.sqrt_eq_rpow]
  exact sqrt_le_of_bounds hB (inv_nonneg.mpr ht.le) hi

section Frechet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The local-open form of the genuine Fréchet chain-rule estimate. -/
theorem comp_jet_bound {f : E → ℝ} {g : ℝ → ℝ} {s : Set E} {t : Set ℝ}
    (hs : IsOpen s) (ht : IsOpen t) (hf : ContDiffOn ℝ ∞ f s)
    (hg : ContDiffOn ℝ ∞ g t) (hmap : MapsTo f s t) {x : E} (hx : x ∈ s)
    (n : ℕ) {C D : ℝ}
    (hC : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * D ^ n := by
  have h := norm_iteratedFDerivWithin_comp_le hg hf (nat_le_infty n)
    ht.uniqueDiffOn hs.uniqueDiffOn hmap hx
    (by
      intro i hi
      rw [iteratedFDerivWithin_of_isOpen i ht (hmap hx)]
      exact hC i hi)
    (by
      intro i hi hin
      rw [iteratedFDerivWithin_of_isOpen i hs hx]
      exact hD i hi hin)
  simpa only [iteratedFDerivWithin_of_isOpen n hs hx] using h

theorem rpow_comp_jet_bound {f : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (hfpos : ∀ x ∈ s, 0 < f x)
    {x : E} (hx : x ∈ s) (p : ℝ) (n : ℕ) {B : ℝ} (hB : 1 ≤ B)
    (hp : f x ^ p ≤ B) (hi : (f x)⁻¹ ≤ B)
    (hjet : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => f y ^ p) x‖ ≤
      n.factorial * coeffBound p n * B ^ (2 * n + 1) := by
  have hg : ContDiffOn ℝ ∞ (fun t : ℝ => t ^ p) (Ioi 0) := by
    intro t ht
    exact (Real.contDiffAt_rpow_const_of_ne (show 0 < t from ht).ne').contDiffWithinAt
  have h := comp_jet_bound hs isOpen_Ioi hf hg hfpos hx n
    (fun i hin => rpow_jet_bound p hB (hfpos x hx) hp hi hin)
    (by
      intro i h1 hin
      exact (hjet i h1 hin).trans (by
        simpa only [pow_one] using pow_le_pow_right₀ hB h1))
  convert! h using 1
  rw [show 2 * n + 1 = (n + 1) + n by omega, pow_add]
  ring

theorem norm_jet_const_mul {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (c : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => c * f y) x‖ = |c| * ‖iteratedFDeriv ℝ n f x‖ := by
  have he : iteratedFDeriv ℝ n (fun y => c * f y) x = c • iteratedFDeriv ℝ n f x := by
    simpa only [smul_eq_mul] using
      iteratedFDeriv_const_smul_apply' (a := c) (hf.of_le (nat_le_infty n))
  rw [he]
  exact norm_smul c (iteratedFDeriv ℝ n f x)

/-- The multiplier here is a fixed scalar at the point being estimated. -/
def normalizeAt (w : ℝ) (f : E → ℝ) : E → ℝ := fun y => w⁻¹ * f y

theorem normalized_jet_bound {g : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hg : ContDiffOn ℝ ∞ g s) {x : E} (hx : x ∈ s) {w B : ℝ} (hw : 0 < w)
    (n : ℕ) (hjet : ‖iteratedFDeriv ℝ n g x‖ ≤ w * B) :
    ‖iteratedFDeriv ℝ n (normalizeAt w g) x‖ ≤ B := by
  change ‖iteratedFDeriv ℝ n (fun y => w⁻¹ * g y) x‖ ≤ B
  rw [norm_jet_const_mul (hg.contDiffAt (hs.mem_nhds hx)),
    abs_of_pos (inv_pos.mpr hw)]
  have h := mul_le_mul_of_nonneg_left hjet (inv_pos.mpr hw).le
  simpa only [← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul] using h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem normalized_pos {g : E → ℝ} {s : Set E} {w : ℝ} (hw : 0 < w)
    (hg : ∀ x ∈ s, 0 < g x) {x : E} (hx : x ∈ s) : 0 < normalizeAt w g x :=
  mul_pos (inv_pos.mpr hw) (hg x hx)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem normalized_bounds {g : E → ℝ} {s : Set E} {w B : ℝ} (hw : 0 < w) (hB : 1 ≤ B)
    (hg : ∀ x ∈ s, 0 < g x) {x : E} (hx : x ∈ s)
    (hlo : w / B ≤ g x) (hhi : g x ≤ w * B) :
    normalizeAt w g x ≤ B ∧ (normalizeAt w g x)⁻¹ ≤ B := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  constructor
  · have h := mul_le_mul_of_nonneg_left hhi (inv_pos.mpr hw).le
    simpa only [normalizeAt, ← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul] using h
  · apply (inv_le_iff_one_le_mul₀ (normalized_pos hw hg hx)).2
    have hm := (div_le_iff₀ hBpos).mp hlo
    have h := mul_le_mul_of_nonneg_left hm (inv_pos.mpr hw).le
    simpa only [normalizeAt, mul_left_comm, mul_comm, inv_mul_cancel₀ hw.ne', mul_inv_cancel₀
      hw.ne',
      mul_assoc, one_mul] using h

theorem normalized_contDiffOn {g : E → ℝ} {s : Set E} (hg : ContDiffOn ℝ ∞ g s) (w : ℝ) :
    ContDiffOn ℝ ∞ (normalizeAt w g) s := contDiffOn_const.mul hg

theorem jet_congr {f g : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) (n : ℕ) :
    iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  simp only [← iteratedFDerivWithin_univ]
  exact (h.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq h.eq_of_nhds n

omit [NormedSpace ℝ E] in
/-- Actual powers separate from a fixed positive rescaling on the given open domain. -/
theorem rpow_rescale_eventually {g : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hpos : ∀ x ∈ s, 0 < g x) {x : E} (hx : x ∈ s) {w : ℝ} (hw : 0 < w) (p : ℝ) :
    (fun y => g y ^ p) =ᶠ[𝓝 x] (fun y => w ^ p * (normalizeAt w g y) ^ p) := by
  filter_upwards [hs.mem_nhds hx] with y hy
  rw [← Real.mul_rpow hw.le (normalized_pos hw hpos hy).le]
  congr 1
  simp only [normalizeAt, ← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]

theorem rescaled_rpow_jet_bound {g : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hg : ContDiffOn ℝ ∞ g s) (hpos : ∀ x ∈ s, 0 < g x) {x : E} (hx : x ∈ s)
    {w B : ℝ} (hw : 0 < w) (hB : 1 ≤ B) (p : ℝ) (n : ℕ)
    (hpow : (normalizeAt w g x) ^ p ≤ B) (hinv : (normalizeAt w g x)⁻¹ ≤ B)
    (hjet : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ w * B) :
    ‖iteratedFDeriv ℝ n (fun y => g y ^ p) x‖ ≤
      w ^ p * (n.factorial * coeffBound p n) * B ^ (2 * n + 1) := by
  have hf := normalized_contDiffOn hg w
  have hfp : ∀ y ∈ s, 0 < normalizeAt w g y := fun y hy => normalized_pos hw hpos hy
  have hb := rpow_comp_jet_bound hs hf hfp hx p n hB hpow hinv
    (fun i _ hin => normalized_jet_bound hs hg hx hw i (hjet i hin))
  have he := jet_congr (rpow_rescale_eventually hs hpos hx hw p) n
  rw [he, norm_jet_const_mul ((hf.contDiffAt (hs.mem_nhds hx)).rpow_const_of_ne
    (hfp x hx).ne'), abs_of_pos (Real.rpow_pos_of_pos hw p)]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos hw p).le).trans_eq (by ring)

/-- Square-root estimates retain exactly the square root of the small weight. -/
theorem sqrt_jet_bound {g : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hg : ContDiffOn ℝ ∞ g s) (hpos : ∀ x ∈ s, 0 < g x) {x : E} (hx : x ∈ s)
    {w B : ℝ} (hw : 0 < w) (hB : 1 ≤ B) (n : ℕ)
    (hlo : w / B ≤ g x) (hjet : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ w * B) :
    ‖iteratedFDeriv ℝ n (fun y => Real.sqrt (g y)) x‖ ≤
      Real.sqrt w * (n.factorial * coeffBound (1 / 2) n) * B ^ (2 * n + 1) := by
  have hhi : g x ≤ w * B := by
    have h0 := hjet 0 (Nat.zero_le n)
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (hpos x hx)] using h0
  obtain ⟨hu, hi⟩ := normalized_bounds hw hB hpos hx hlo hhi
  have h := rescaled_rpow_jet_bound hs hg hpos hx hw hB (1 / 2) n
    (half_power_bound hB (normalized_pos hw hpos hx) hu) hi hjet
  simpa only [← Real.sqrt_eq_rpow] using h

def orderBound (p : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), k.factorial * coeffBound p k

theorem orderBound_nonneg (p : ℝ) (n : ℕ) : 0 ≤ orderBound p n := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (Nat.cast_nonneg _) (coeffBound_nonneg p k)

theorem orderBound_le (p : ℝ) {i n : ℕ} (hi : i ≤ n) :
    i.factorial * coeffBound p i ≤ orderBound p n := by
  exact Finset.single_le_sum (f := fun k => (k.factorial : ℝ) * coeffBound p k)
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (coeffBound_nonneg p k))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem rpow_comp_jets_bound {f : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (hfpos : ∀ x ∈ s, 0 < f x)
    {x : E} (hx : x ∈ s) (p : ℝ) (n : ℕ) {B : ℝ} (hB : 1 ≤ B)
    (hp : f x ^ p ≤ B) (hi : (f x)⁻¹ ≤ B)
    (hjet : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ B) {i : ℕ} (hin : i ≤ n) :
    ‖iteratedFDeriv ℝ i (fun y => f y ^ p) x‖ ≤ orderBound p n * B ^ (2 * n + 1) := by
  have h := rpow_comp_jet_bound hs hf hfpos hx p i hB hp hi
    (fun k _ hk => hjet k (hk.trans hin))
  apply h.trans
  exact mul_le_mul (orderBound_le p hin)
    (pow_le_pow_right₀ hB (by omega)) (pow_nonneg (zero_le_one.trans hB) _)
    (orderBound_nonneg p n)

def chooseSum (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)

theorem chooseSum_nonneg (n : ℕ) : 0 ≤ chooseSum n := by
  unfold chooseSum
  positivity

/-- A common bound for each input jet yields the usual Leibniz bound. -/
theorem mul_jets_bound {f g : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) {x : E} (hx : x ∈ s)
    (n : ℕ) {C D : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hfj : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hgj : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ chooseSum n * C * D := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hs.uniqueDiffOn hx (nat_le_infty n)
  simp only [iteratedFDerivWithin_of_isOpen _ hs hx] at h
  apply h.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      gcongr
      · exact hfj i hin
      · exact hgj (n - i) (Nat.sub_le _ _)
    _ = chooseSum n * C * D := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl

omit [NormedSpace ℝ E] in
theorem signed_rescale_eventually {g r : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hpos : ∀ x ∈ s, 0 < g x) {x : E} (hx : x ∈ s) {w : ℝ} (hw : 0 < w) :
    (fun y => r y / (2 * Real.sqrt (g y))) =ᶠ[𝓝 x]
      (fun y => (Real.sqrt w / 2) *
        (normalizeAt w r y * (normalizeAt w g y) ^ (-(1 / 2 : ℝ)))) := by
  filter_upwards [hs.mem_nhds hx] with y hy
  have hG := normalized_pos hw hpos hy
  have hsq : Real.sqrt (g y) = Real.sqrt w * Real.sqrt (normalizeAt w g y) := by
    rw [← Real.sqrt_mul hw.le]
    congr 1
    simp only [normalizeAt, ← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]
  have hR : r y = w * normalizeAt w r y := by
    simp only [normalizeAt, ← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]
  rw [Real.rpow_neg hG.le, ← Real.sqrt_eq_rpow]
  have hwroot := Real.sq_sqrt hw.le
  calc
    _ = (Real.sqrt w) ^ 2 * normalizeAt w r y /
        (2 * (Real.sqrt w * Real.sqrt (normalizeAt w g y))) := by rw [hwroot, ← hR, ← hsq]
    _ = _ := by
      field_simp [(Real.sqrt_pos.mpr hw).ne', (Real.sqrt_pos.mpr hG).ne']

/-- Signed updates inherit the same half-weight as the primary square root. -/
theorem signed_jet_bound {g r : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hg : ContDiffOn ℝ ∞ g s) (hr : ContDiffOn ℝ ∞ r s)
    (hpos : ∀ x ∈ s, 0 < g x) {x : E} (hx : x ∈ s)
    {w B : ℝ} (hw : 0 < w) (hB : 1 ≤ B) (n : ℕ)
    (hlo : w / B ≤ g x)
    (hgj : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ w * B)
    (hrj : ∀ i ≤ n, ‖iteratedFDeriv ℝ i r x‖ ≤ w * B) :
    ‖iteratedFDeriv ℝ n (fun y => r y / (2 * Real.sqrt (g y))) x‖ ≤
      Real.sqrt w * (chooseSum n * orderBound (-(1 / 2 : ℝ)) n / 2) * B ^ (2 * n + 2) := by
  have hhi : g x ≤ w * B := by
    have h0 := hgj 0 (Nat.zero_le n)
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (hpos x hx)] using h0
  obtain ⟨hu, hi⟩ := normalized_bounds hw hB hpos hx hlo hhi
  have hG := normalized_contDiffOn hg w
  have hR := normalized_contDiffOn hr w
  have hGp : ∀ y ∈ s, 0 < normalizeAt w g y := fun y hy => normalized_pos hw hpos hy
  have hP : ContDiffOn ℝ ∞ (fun y => normalizeAt w g y ^ (-(1 / 2 : ℝ))) s :=
    hG.rpow_const_of_ne (fun y hy => (hGp y hy).ne')
  have hPj : ∀ i ≤ n,
      ‖iteratedFDeriv ℝ i (fun y => normalizeAt w g y ^ (-(1 / 2 : ℝ))) x‖ ≤
        orderBound (-(1 / 2 : ℝ)) n * B ^ (2 * n + 1) := by
    intro i hin
    exact rpow_comp_jets_bound hs hG hGp hx _ n hB
      (neg_half_power_bound hB (hGp x hx) hi) hi
      (fun k hk => normalized_jet_bound hs hg hx hw k (hgj k hk)) hin
  have hp := mul_jets_bound hs hR hP hx n (zero_le_one.trans hB)
    (mul_nonneg (orderBound_nonneg _ n) (pow_nonneg (zero_le_one.trans hB) _))
    (fun i hin => normalized_jet_bound hs hr hx hw i (hrj i hin)) hPj
  rw [jet_congr (signed_rescale_eventually hs hpos hx hw) n,
    norm_jet_const_mul ((hR.mul hP).contDiffAt (hs.mem_nhds hx)),
    abs_of_pos (div_pos (Real.sqrt_pos.mpr hw) (by norm_num))]
  apply (mul_le_mul_of_nonneg_left hp (div_pos (Real.sqrt_pos.mpr hw) (by norm_num)).le).trans_eq
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]
  ring

end Frechet

section PolynomialControl

variable {X : Type*}

/-- An upper bound with a fixed finite power of each allowed large scale.
The controlled function need not have any regularity. -/
def PolyBound (s : Set X) (S T : X → ℝ) (f : X → ℝ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∃ K N : ℕ, ∀ x ∈ s, f x ≤ C * S x ^ K * T x ^ N

variable {s : Set X} {S T f g : X → ℝ}

theorem PolyBound.mono (hf : PolyBound s S T f) (h : ∀ x ∈ s, g x ≤ f x) :
    PolyBound s S T g := by
  obtain ⟨C, hC, K, N, hb⟩ := hf
  exact ⟨C, hC, K, N, fun x hx => (h x hx).trans (hb x hx)⟩

theorem polyBound_one : PolyBound s S T (fun _ => 1) := by
  exact ⟨1, le_rfl, 0, 0, by simp⟩

theorem polyBound_zero : PolyBound s S T (fun _ => 0) :=
  polyBound_one.mono (by intro x hx; norm_num)

theorem PolyBound.add (hS : ∀ x ∈ s, 1 ≤ S x) (hT : ∀ x ∈ s, 1 ≤ T x)
    (hf : PolyBound s S T f) (hg : PolyBound s S T g) :
    PolyBound s S T (fun x => f x + g x) := by
  obtain ⟨C, hC, K, N, hb⟩ := hf
  obtain ⟨D, hD, L, M, hd⟩ := hg
  refine ⟨C + D, by linarith, K + L, N + M, ?_⟩
  intro x hx
  have hS0 := zero_le_one.trans (hS x hx)
  have hT0 := zero_le_one.trans (hT x hx)
  have hk : S x ^ K ≤ S x ^ (K + L) := pow_le_pow_right₀ (hS x hx) (Nat.le_add_right _ _)
  have hl : S x ^ L ≤ S x ^ (K + L) := pow_le_pow_right₀ (hS x hx) (Nat.le_add_left _ _)
  have hn : T x ^ N ≤ T x ^ (N + M) := pow_le_pow_right₀ (hT x hx) (Nat.le_add_right _ _)
  have hm : T x ^ M ≤ T x ^ (N + M) := pow_le_pow_right₀ (hT x hx) (Nat.le_add_left _ _)
  calc
    _ ≤ C * S x ^ K * T x ^ N + D * S x ^ L * T x ^ M := add_le_add (hb x hx) (hd x hx)
    _ ≤ C * S x ^ (K + L) * T x ^ (N + M) + D * S x ^ (K + L) * T x ^ (N + M) := by
      apply add_le_add
      · gcongr
      · gcongr
    _ = _ := by ring

theorem PolyBound.sum {ι : Type*} (u : Finset ι) (F : ι → X → ℝ)
    (hS : ∀ x ∈ s, 1 ≤ S x) (hT : ∀ x ∈ s, 1 ≤ T x)
    (hF : ∀ i ∈ u, PolyBound s S T (F i)) :
    PolyBound s S T (fun x => ∑ i ∈ u, F i x) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (polyBound_zero (s := s) (S := S) (T := T))
  | @insert i u hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hF i (Finset.mem_insert_self _ _)).add hS hT
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

theorem PolyBound.pow (_hS : ∀ x ∈ s, 1 ≤ S x) (_hT : ∀ x ∈ s, 1 ≤ T x)
    (hf : PolyBound s S T f) (hf0 : ∀ x ∈ s, 0 ≤ f x) (k : ℕ) :
    PolyBound s S T (fun x => f x ^ k) := by
  obtain ⟨C, hC, K, N, hb⟩ := hf
  refine ⟨C ^ k, one_le_pow₀ hC, K * k, N * k, ?_⟩
  intro x hx
  calc
    _ ≤ (C * S x ^ K * T x ^ N) ^ k := pow_le_pow_left₀ (hf0 x hx) (hb x hx) k
    _ = _ := by simp only [mul_pow, pow_mul]

theorem PolyBound.const_mul (hS : ∀ x ∈ s, 1 ≤ S x) (hT : ∀ x ∈ s, 1 ≤ T x)
    (hf : PolyBound s S T f) {a : ℝ} (ha : 0 ≤ a) :
    PolyBound s S T (fun x => a * f x) := by
  obtain ⟨C, hC, K, N, hb⟩ := hf
  refine ⟨(a + 1) * C, ?_, K, N, ?_⟩
  · nlinarith
  · intro x hx
    have hm : 0 ≤ C * S x ^ K * T x ^ N :=
      mul_nonneg (mul_nonneg (zero_le_one.trans hC)
        (pow_nonneg (zero_le_one.trans (hS x hx)) _))
        (pow_nonneg (zero_le_one.trans (hT x hx)) _)
    calc
      _ ≤ a * (C * S x ^ K * T x ^ N) := mul_le_mul_of_nonneg_left (hb x hx) ha
      _ ≤ (a + 1) * (C * S x ^ K * T x ^ N) := by nlinarith
      _ = _ := by ring

end PolynomialControl

section WeightedJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite envelope of the input jets and the positive denominator lower bound.
This function is never differentiated. -/
def envelope (w g r : E → ℝ) (n : ℕ) (x : E) : ℝ :=
  1 + w x / g x + ∑ i ∈ Finset.range (n + 1),
    (‖iteratedFDeriv ℝ i g x‖ / w x + ‖iteratedFDeriv ℝ i r x‖ / w x)

theorem envelope_bounds {w g r : E → ℝ} {x : E} (hw : 0 < w x) (hg : 0 < g x) (n : ℕ) :
    1 ≤ envelope w g r n x ∧ w x / envelope w g r n x ≤ g x ∧
      (∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ w x * envelope w g r n x) ∧
      (∀ i ≤ n, ‖iteratedFDeriv ℝ i r x‖ ≤ w x * envelope w g r n x) := by
  have hterm (i : ℕ) : 0 ≤ ‖iteratedFDeriv ℝ i g x‖ / w x +
      ‖iteratedFDeriv ℝ i r x‖ / w x := by positivity
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n + 1),
      (‖iteratedFDeriv ℝ i g x‖ / w x + ‖iteratedFDeriv ℝ i r x‖ / w x) :=
    Finset.sum_nonneg (fun i _ => hterm i)
  have hB : 1 ≤ envelope w g r n x := by
    dsimp only [envelope]
    have hfrac : 0 ≤ w x / g x := (div_pos hw hg).le
    linarith
  have hlow : w x / g x ≤ envelope w g r n x := by
    dsimp only [envelope]
    linarith
  have hlow' : w x / envelope w g r n x ≤ g x := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hB)).2
    simpa only [mul_comm] using (div_le_iff₀ hg).mp hlow
  have hi (i : ℕ) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i g x‖ / w x + ‖iteratedFDeriv ℝ i r x‖ / w x ≤
        envelope w g r n x := by
    have ht := Finset.single_le_sum
      (f := fun i => ‖iteratedFDeriv ℝ i g x‖ / w x + ‖iteratedFDeriv ℝ i r x‖ / w x)
      (fun i _ => hterm i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hin))
    dsimp only [envelope]
    have hlo : 0 ≤ w x / g x := (div_pos hw hg).le
    linarith
  refine ⟨hB, hlow', ?_, ?_⟩
  · intro i hin
    have hnonneg : 0 ≤ ‖iteratedFDeriv ℝ i r x‖ / w x := by positivity
    have h : ‖iteratedFDeriv ℝ i g x‖ / w x ≤ envelope w g r n x := by linarith [hi i hin]
    simpa only [mul_comm] using (div_le_iff₀ hw).mp h
  · intro i hin
    have hnonneg : 0 ≤ ‖iteratedFDeriv ℝ i g x‖ / w x := by positivity
    have h : ‖iteratedFDeriv ℝ i r x‖ / w x ≤ envelope w g r n x := by linarith [hi i hin]
    simpa only [mul_comm] using (div_le_iff₀ hw).mp h

theorem envelope_polyBound {s : Set E} {S T w g r : E → ℝ}
    (hS : ∀ x ∈ s, 1 ≤ S x) (hT : ∀ x ∈ s, 1 ≤ T x)
    (hlower : PolyBound s S T (fun x => w x / g x))
    (hg : ∀ n, PolyBound s S T (fun x => ‖iteratedFDeriv ℝ n g x‖ / w x))
    (hr : ∀ n, PolyBound s S T (fun x => ‖iteratedFDeriv ℝ n r x‖ / w x)) (n : ℕ) :
    PolyBound s S T (envelope w g r n) := by
  apply PolyBound.add hS hT (PolyBound.add hS hT polyBound_one hlower)
  exact PolyBound.sum (Finset.range (n + 1)) _ hS hT
    (fun i _ => PolyBound.add hS hT (hg i) (hr i))

/-- All input jets carry `w`; the square root and arbitrary signed quotient
carry exactly `sqrt w`, with only polynomial changes in the allowed scales. -/
theorem weighted_half_control {s : Set E} {S T w g r : E → ℝ}
    (hs : IsOpen s) (hS : ∀ x ∈ s, 1 ≤ S x) (hT : ∀ x ∈ s, 1 ≤ T x)
    (hw : ∀ x ∈ s, 0 < w x) (hpos : ∀ x ∈ s, 0 < g x)
    (hg : ContDiffOn ℝ ∞ g s) (hr : ContDiffOn ℝ ∞ r s)
    (hlower : PolyBound s S T (fun x => w x / g x))
    (hgj : ∀ n, PolyBound s S T (fun x => ‖iteratedFDeriv ℝ n g x‖ / w x))
    (hrj : ∀ n, PolyBound s S T (fun x => ‖iteratedFDeriv ℝ n r x‖ / w x)) :
    (∀ n, PolyBound s S T (fun x =>
      ‖iteratedFDeriv ℝ n (fun y => Real.sqrt (g y)) x‖ / Real.sqrt (w x))) ∧
    (∀ n, PolyBound s S T (fun x =>
      ‖iteratedFDeriv ℝ n (fun y => r y / (2 * Real.sqrt (g y))) x‖ / Real.sqrt (w x))) := by
  have henv (n : ℕ) := envelope_polyBound hS hT hlower hgj hrj n
  have hnonneg (n : ℕ) (x : E) (hx : x ∈ s) : 0 ≤ envelope w g r n x :=
    zero_le_one.trans (envelope_bounds (hw x hx) (hpos x hx) n).1
  constructor
  · intro n
    have hc : 0 ≤ (n.factorial : ℝ) * coeffBound (1 / 2) n :=
      mul_nonneg (Nat.cast_nonneg _) (coeffBound_nonneg _ _)
    apply ((henv n).pow hS hT (hnonneg n) (2 * n + 1)).const_mul hS hT hc |>.mono
    intro x hx
    obtain ⟨hB, hlo, hG, hR⟩ := envelope_bounds (hw x hx) (hpos x hx) n
    have h := sqrt_jet_bound hs hg hpos hx (hw x hx) hB n hlo hG
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (hw x hx))).2
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  · intro n
    have hc : 0 ≤ chooseSum n * orderBound (-(1 / 2 : ℝ)) n / 2 :=
      div_nonneg (mul_nonneg (chooseSum_nonneg n) (orderBound_nonneg _ _)) (by norm_num)
    apply ((henv n).pow hS hT (hnonneg n) (2 * n + 2)).const_mul hS hT hc |>.mono
    intro x hx
    obtain ⟨hB, hlo, hG, hR⟩ := envelope_bounds (hw x hx) (hpos x hx) n
    have h := signed_jet_bound hs hg hr hpos hx (hw x hx) hB n hlo hG hR
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (hw x hx))).2
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- An explicit weighted lower estimate supplies the reciprocal envelope.
This assumption is pointwise, with no normalized smooth factor. -/
theorem polyBound_of_lower {s : Set E} {S T w g : E → ℝ}
    (hS : ∀ x ∈ s, 1 ≤ S x) (hT : ∀ x ∈ s, 1 ≤ T x)
    (hg : ∀ x ∈ s, 0 < g x) {c₀ : ℝ} (hc₀ : 0 < c₀) (K N : ℕ)
    (hlower : ∀ x ∈ s, c₀ * w x / (S x ^ K * T x ^ N) ≤ g x) :
    PolyBound s S T (fun x => w x / g x) := by
  refine ⟨c₀⁻¹ + 1, by have := inv_pos.mpr hc₀; linarith, K, N, ?_⟩
  intro x hx
  have hP : 0 < S x ^ K * T x ^ N :=
    mul_pos (pow_pos (zero_lt_one.trans_le (hS x hx)) _)
      (pow_pos (zero_lt_one.trans_le (hT x hx)) _)
  have h := (div_le_iff₀ hP).mp (hlower x hx)
  apply (div_le_iff₀ (hg x hx)).2
  calc
    w x = c₀⁻¹ * (c₀ * w x) := by rw [← mul_assoc, inv_mul_cancel₀ hc₀.ne', one_mul]
    _ ≤ c₀⁻¹ * (g x * (S x ^ K * T x ^ N)) :=
      mul_le_mul_of_nonneg_left h (inv_pos.mpr hc₀).le
    _ ≤ (c₀⁻¹ + 1) * (g x * (S x ^ K * T x ^ N)) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (mul_pos (hg x hx) hP).le
    _ = _ := by ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Convert the usual weighted upper inequality to the envelope notation. -/
theorem polyBound_of_weighted {s : Set E} {S T w F : E → ℝ}
    (hS : ∀ x ∈ s, 1 ≤ S x) (hT : ∀ x ∈ s, 1 ≤ T x)
    (hw : ∀ x ∈ s, 0 < w x) {C : ℝ} (hC : 0 ≤ C) (K N : ℕ)
    (hbound : ∀ x ∈ s, F x ≤ C * S x ^ K * T x ^ N * w x) :
    PolyBound s S T (fun x => F x / w x) := by
  refine ⟨C + 1, by linarith, K, N, ?_⟩
  intro x hx
  apply ((div_le_iff₀ (hw x hx)).mpr (hbound x hx)).trans
  have hP : 0 ≤ S x ^ K * T x ^ N :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (hS x hx)) _)
      (pow_nonneg (zero_le_one.trans (hT x hx)) _)
  nlinarith

end WeightedJets

section GaussianEdge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev edgeStrip (U : Set E) : Set (E × ℝ) := U ×ˢ Ioo 0 1

/-- All full derivative tensors satisfy an exponential weight times fixed
powers of the allowed scale and inverse edge distance. -/
def WeightedJets (c : ℝ) (U : Set E) (S : E × ℝ → ℝ) (f : E × ℝ → ℝ) : Prop :=
  ∀ n : ℕ, PolyBound (edgeStrip U) S (fun p => p.2⁻¹)
    (fun p => ‖iteratedFDeriv ℝ n f p‖ / FlatCutoff.edge c p.2)

/-- An external scale may vary with parameters, but is locally bounded at
the edge. Any fixed `S ≥ 1` satisfies this condition. -/
def LocallyBoundedScale (U : Set E) (S : E × ℝ → ℝ) : Prop :=
  ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ M : ℝ, 1 ≤ M ∧
    ∀ y ∈ V ∩ U, ∀ δ ∈ Ioo (0 : ℝ) 1, S (y, δ) ≤ M

omit [NormedSpace ℝ E] in
theorem locallyBoundedScale_const (U : Set E) {S : ℝ} (hS : 1 ≤ S) :
    LocallyBoundedScale U (fun _ => S) := by
  intro x hx
  exact ⟨univ, univ_mem, S, hS, by simp⟩

theorem sqrt_edge (c δ : ℝ) : Real.sqrt (FlatCutoff.edge c δ) = FlatCutoff.edge (c / 2) δ := by
  by_cases hδ : δ ≤ 0
  · simp [FlatCutoff.edge_of_nonpos c hδ, FlatCutoff.edge_of_nonpos (c / 2) hδ]
  · have hp : 0 < δ := lt_of_not_ge hδ
    rw [FlatCutoff.edge_of_pos c hp, FlatCutoff.edge_of_pos (c / 2) hp, ← Real.exp_half]
    congr 1
    ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem inverse_distance_one_le {U : Set E} {p : E × ℝ} (hp : p ∈ edgeStrip U) :
    1 ≤ p.2⁻¹ := (one_le_inv₀ hp.2.1).mpr hp.2.2.le

/-- The hypotheses are inequalities for the input's actual derivatives. -/
theorem WeightedJets.of_bounds {c : ℝ} {U : Set E} {S : E × ℝ → ℝ} {f : E × ℝ → ℝ}
    (hS : ∀ p ∈ edgeStrip U, 1 ≤ S p)
    (h : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ K N : ℕ, ∀ p ∈ edgeStrip U,
      ‖iteratedFDeriv ℝ n f p‖ ≤ C * S p ^ K * FlatCutoff.edge c p.2 / p.2 ^ N) :
    WeightedJets c U S f := by
  intro n
  obtain ⟨C, hC, K, N, hb⟩ := h n
  apply polyBound_of_weighted hS (fun p hp => inverse_distance_one_le hp)
    (fun p hp => FlatCutoff.edge_pos c hp.2.1) hC K N
  intro p hp
  convert! hb p hp using 1
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem weighted_half_jets {c : ℝ} {U : Set E} (hU : IsOpen U)
    {S g r : E × ℝ → ℝ} (hS : ∀ p ∈ edgeStrip U, 1 ≤ S p)
    (hpos : ∀ p ∈ U ×ˢ Ioi (0 : ℝ), 0 < g p)
    (hg : ContDiffOn ℝ ∞ g (U ×ˢ Ioi 0)) (hr : ContDiffOn ℝ ∞ r (U ×ˢ Ioi 0))
    (hlower : PolyBound (edgeStrip U) S (fun p => p.2⁻¹)
      (fun p => FlatCutoff.edge c p.2 / g p))
    (hgj : WeightedJets c U S g) (hrj : WeightedJets c U S r) :
    WeightedJets (c / 2) U S (fun p => Real.sqrt (g p)) ∧
      WeightedJets (c / 2) U S (fun p => r p / (2 * Real.sqrt (g p))) := by
  have hsub : edgeStrip U ⊆ U ×ˢ Ioi (0 : ℝ) := fun p hp => ⟨hp.1, hp.2.1⟩
  have h := weighted_half_control (hU.prod isOpen_Ioo) hS
    (fun p hp => inverse_distance_one_le hp)
    (fun p hp => FlatCutoff.edge_pos c hp.2.1) (fun p hp => hpos p (hsub hp))
    (hg.mono hsub) (hr.mono hsub) hlower hgj hrj
  constructor
  · intro n
    simpa only [sqrt_edge] using h.1 n
  · intro n
    simpa only [sqrt_edge] using h.2 n

theorem WeightedJets.localGaussian {c : ℝ} {U : Set E} {S f : E × ℝ → ℝ}
    (hS : ∀ p ∈ edgeStrip U, 1 ≤ S p) (hscale : LocallyBoundedScale U S)
    (hf : WeightedJets c U S f) : FlatZeroExtension.LocalGaussianJets c U f := by
  intro n x hx
  obtain ⟨C, hC, K, N, hb⟩ := hf n
  obtain ⟨V, hV, M, hM, hm⟩ := hscale x hx
  refine ⟨V, hV, C * M ^ K,
    mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hM) _), N, ?_⟩
  intro y hy δ hδ
  have hp : (y, δ) ∈ edgeStrip U := ⟨hy.2, hδ⟩
  have he := FlatCutoff.edge_pos c hδ.1
  have hbase : 0 ≤ S (y, δ) := zero_le_one.trans (hS _ hp)
  have hδinv : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ.1).le
  calc
    ‖iteratedFDeriv ℝ n f (y, δ)‖ ≤
        (C * S (y, δ) ^ K * (δ⁻¹) ^ N) * FlatCutoff.edge c δ :=
      (div_le_iff₀ he).mp (hb (y, δ) hp)
    _ ≤ (C * M ^ K * (δ⁻¹) ^ N) * FlatCutoff.edge c δ := by
      gcongr
      exact hm y hy δ hδ
    _ = C * M ^ K * FlatCutoff.edge c δ / δ ^ N := by
      simp only [div_eq_mul_inv, inv_pow]
      ring

/-- Joint smooth zero extension, and vanishing of every full edge tensor,
derived solely from weighted input-jet inequalities and a positive lower bound. -/
theorem weighted_zero_extension {c : ℝ} (hc : 0 < c) {U : Set E} (hU : IsOpen U)
    {S g r : E × ℝ → ℝ} (hS : ∀ p ∈ edgeStrip U, 1 ≤ S p)
    (hscale : LocallyBoundedScale U S)
    (hpos : ∀ p ∈ U ×ˢ Ioi (0 : ℝ), 0 < g p)
    (hg : ContDiffOn ℝ ∞ g (U ×ˢ Ioi 0)) (hr : ContDiffOn ℝ ∞ r (U ×ˢ Ioi 0))
    (hlower : PolyBound (edgeStrip U) S (fun p => p.2⁻¹)
      (fun p => FlatCutoff.edge c p.2 / g p))
    (hgj : WeightedJets c U S g) (hrj : WeightedJets c U S r) :
    ContDiffOn ℝ ∞ (FlatZeroExtension.zeroExtension (fun p => Real.sqrt (g p))) (U ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (FlatZeroExtension.zeroExtension (fun p => r p / (2 * Real.sqrt (g p))))
      (U ×ˢ univ) ∧
    ∀ n : ℕ, ∀ x ∈ U,
      iteratedFDeriv ℝ n (FlatZeroExtension.zeroExtension (fun p => Real.sqrt (g p))) (x, 0) = 0 ∧
      iteratedFDeriv ℝ n (FlatZeroExtension.zeroExtension
        (fun p => r p / (2 * Real.sqrt (g p)))) (x, 0) = 0 := by
  obtain ⟨ha, hb⟩ := weighted_half_jets hU hS hpos hg hr hlower hgj hrj
  have haB := ha.localGaussian hS hscale
  have hbB := hb.localGaussian hS hscale
  have has : ContDiffOn ℝ ∞ (fun p => Real.sqrt (g p)) (U ×ˢ Ioi (0 : ℝ)) :=
    hg.sqrt (fun p hp => (hpos p hp).ne')
  have hbs : ContDiffOn ℝ ∞ (fun p => r p / (2 * Real.sqrt (g p))) (U ×ˢ Ioi (0 : ℝ)) :=
    hr.div (contDiffOn_const.mul has) (fun p hp =>
      mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (hpos p hp)).ne')
  have hc2 : 0 < c / 2 := by linarith
  refine ⟨FlatZeroExtension.contDiffOn_zeroExtension hc2 hU has haB,
    FlatZeroExtension.contDiffOn_zeroExtension hc2 hU hbs hbB, ?_⟩
  intro n x hx
  exact ⟨FlatZeroExtension.iteratedFDeriv_zeroExtension_edge hc2 hU has haB n hx,
    FlatZeroExtension.iteratedFDeriv_zeroExtension_edge hc2 hU hbs hbB n hx⟩

/-- Direct interface using only the original weighted input inequalities. -/
theorem weighted_zero_extension_of_bounds {c : ℝ} (hc : 0 < c) {U : Set E} (hU : IsOpen U)
    {S g r : E × ℝ → ℝ} (hS : ∀ p ∈ edgeStrip U, 1 ≤ S p)
    (hscale : LocallyBoundedScale U S)
    (hpos : ∀ p ∈ U ×ˢ Ioi (0 : ℝ), 0 < g p)
    (hg : ContDiffOn ℝ ∞ g (U ×ˢ Ioi 0)) (hr : ContDiffOn ℝ ∞ r (U ×ˢ Ioi 0))
    {c₀ : ℝ} (hc₀ : 0 < c₀) (K₀ N₀ : ℕ)
    (hlower : ∀ p ∈ edgeStrip U,
      c₀ * FlatCutoff.edge c p.2 / (S p ^ K₀ * (p.2⁻¹) ^ N₀) ≤ g p)
    (hgBounds : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ K N : ℕ, ∀ p ∈ edgeStrip U,
      ‖iteratedFDeriv ℝ n g p‖ ≤ C * S p ^ K * FlatCutoff.edge c p.2 / p.2 ^ N)
    (hrBounds : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ K N : ℕ, ∀ p ∈ edgeStrip U,
      ‖iteratedFDeriv ℝ n r p‖ ≤ C * S p ^ K * FlatCutoff.edge c p.2 / p.2 ^ N) :
    ContDiffOn ℝ ∞ (FlatZeroExtension.zeroExtension (fun p => Real.sqrt (g p))) (U ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (FlatZeroExtension.zeroExtension (fun p => r p / (2 * Real.sqrt (g p))))
      (U ×ˢ univ) ∧
    ∀ n : ℕ, ∀ x ∈ U,
      iteratedFDeriv ℝ n (FlatZeroExtension.zeroExtension (fun p => Real.sqrt (g p))) (x, 0) = 0 ∧
      iteratedFDeriv ℝ n (FlatZeroExtension.zeroExtension
        (fun p => r p / (2 * Real.sqrt (g p)))) (x, 0) = 0 := by
  apply weighted_zero_extension hc hU hS hscale hpos hg hr
  · exact polyBound_of_lower hS (fun p hp => inverse_distance_one_le hp)
      (fun p hp => hpos p ⟨hp.1, hp.2.1⟩) hc₀ K₀ N₀ hlower
  · exact WeightedJets.of_bounds hS hgBounds
  · exact WeightedJets.of_bounds hS hrBounds

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem zeroExtension_sqrt_sq {U : Set E} {g : E × ℝ → ℝ}
    (hpos : ∀ p ∈ U ×ˢ Ioi (0 : ℝ), 0 < g p) {p : E × ℝ} (hp : p.1 ∈ U) :
    (FlatZeroExtension.zeroExtension (fun p => Real.sqrt (g p)) p) ^ 2 =
      FlatZeroExtension.zeroExtension g p := by
  by_cases hδ : 0 < p.2
  · simp only [FlatZeroExtension.zeroExtension_of_pos _ hδ]
    exact Real.sq_sqrt (hpos p ⟨hp, hδ⟩).le
  · simp only [FlatZeroExtension.zeroExtension_of_nonpos _ (le_of_not_gt hδ), zero_pow (by decide :
    2 ≠ 0)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem zeroExtension_signed_identity {U : Set E} {g r : E × ℝ → ℝ}
    (hpos : ∀ p ∈ U ×ˢ Ioi (0 : ℝ), 0 < g p) {p : E × ℝ} (hp : p.1 ∈ U) :
    2 * FlatZeroExtension.zeroExtension (fun p => Real.sqrt (g p)) p *
      FlatZeroExtension.zeroExtension (fun p => r p / (2 * Real.sqrt (g p))) p =
      FlatZeroExtension.zeroExtension r p := by
  by_cases hδ : 0 < p.2
  · simp only [FlatZeroExtension.zeroExtension_of_pos _ hδ]
    field_simp [(Real.sqrt_pos.mpr (hpos p ⟨hp, hδ⟩)).ne']
  · simp only [FlatZeroExtension.zeroExtension_of_nonpos _ (le_of_not_gt hδ), mul_zero]

end GaussianEdge

end NavierStokes.WeightedQuotients
