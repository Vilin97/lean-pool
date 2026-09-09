/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketGrowth
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketRay
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset

/-!
# Packet Frame Stability
-/

@[expose] public section

noncomputable section

open Set

namespace EulerPacketFrameStability

open Real EulerPacketGrowth EulerPacketRay

/-- Exact relation between the original and inverted logarithmic slopes. -/
theorem inverted_logarithmic_identity
    {ε y : ℝ} {V V₁ : ℝ → ℝ} (hε : ε ≠ 0) (hy : y ≠ 0)
    (hV : V (y⁻¹ / ε) ≠ 0) :
    y ^ 2 * (-ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y) - ε * y =
      V₁ (y⁻¹ / ε) / V (y⁻¹ / ε) := by
  have halg (v w : ℝ) (hv : v ≠ 0) :
      y ^ 2 * (-ε * (-v / y ^ 2 - w / (ε * y ^ 3)) / (v / y)) - ε * y = w / v := by
    field_simp
    ring
  exact halg (V (y⁻¹ / ε)) (V₁ (y⁻¹ / ε)) hV

/-- The logarithmic slope is bounded uniformly in the initial nonnegative
slope after time one. -/
theorem equation30_primary_logderivative_bound
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t, 1 ≤ t → |V₁ t / V t| ≤ 4 := by
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hVp := equation30_global_positive hε hεsmall hV hflux hV0 hV₁0 t htpos.le
  by_cases hpre : t ≤ 1 / ε
  · have hT : 0 ≤ 1 / ε := by positivity
    have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
    have hp := equation30_positive (sq_nonneg ε) (by nlinarith : ε ^ 2 ≤ 1 / 2)
      hT hscale (fun s hs => hV s hs.1) (fun s hs => hflux s hs.1) hV0 hV₁0 t ⟨htpos.le, hpre⟩
    have hu := equation30_log_derivative_upper (sq_nonneg ε) (by nlinarith : ε ^ 2 ≤ 1 / 2)
      hT hscale (fun s hs => hV s hs.1) (fun s hs => hflux s hs.1) hV0 hV₁0 t ⟨htpos, hpre⟩
    have hnonneg : 0 ≤ V₁ t / V t := div_nonneg hp.2 hVp.le
    rw [abs_of_nonneg hnonneg]
    have hinv : 1 / t ≤ 1 := (div_le_one htpos).mpr ht
    linarith
  · have hεt : 1 ≤ ε * t := by
      have hh := (div_le_iff₀ hε).mp (le_of_not_ge hpre)
      nlinarith only [hh]
    let y := 1 / (ε * t)
    have hy : 0 < y := by dsimp [y]; positivity
    have hy1 : y ≤ 1 := by dsimp [y]; exact (div_le_one (by positivity)).mpr hεt
    have harg : y⁻¹ / ε = t := by dsimp [y]; rw [one_div, inv_inv]; field_simp
    have hz := equation30_inverted_riccati_range hε hεsmall hV hflux hV0 hV₁0 y hy hy1
    have hid := inverted_logarithmic_identity (V₁ := V₁) hεne (ne_of_gt hy)
      (show V (y⁻¹ / ε) ≠ 0 by rw [harg]; exact ne_of_gt hVp)
    rw [harg] at hid
    let z := -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y
    have hz0 : 0 ≤ z := hz.1
    have hz4 : z ≤ 4 := hz.2
    have hy2 : y ^ 2 ≤ 1 := by nlinarith only [hy.le, hy1]
    have hmul := mul_le_mul_of_nonneg_left hz4 (sq_nonneg y)
    have hepsy : 0 ≤ ε * y := mul_nonneg hε.le hy.le
    have hepsyUpper : ε * y ≤ 1 := by nlinarith only [hε, hεsmall, hy.le, hy1]
    have hzmul : 0 ≤ y ^ 2 * z := mul_nonneg (sq_nonneg y) hz0
    apply abs_le.mpr
    dsimp [z] at hmul hzmul
    constructor <;> nlinarith only [hid, hmul, hepsy, hepsyUpper, hzmul, hy2]

/-- The ideal pressure numerator has the sign required for the next-frame
construction, throughout the forward evolution. -/
theorem equation30_ideal_numerator_positive
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t, 0 ≤ t → ε ^ 2 * V t ≤
      (ε ^ 2 * t ^ 2 + ε ^ 2) * V t + 2 * ε ^ 2 * t * V₁ t := by
  intro t ht
  have hVp := equation30_global_positive hε hεsmall hV hflux hV0 hV₁0 t ht
  have hεne : ε ≠ 0 := ne_of_gt hε
  by_cases hpre : t ≤ 1 / ε
  · have hT : 0 ≤ 1 / ε := by positivity
    have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
    have hp := equation30_positive (sq_nonneg ε) (by nlinarith : ε ^ 2 ≤ 1 / 2)
      hT hscale (fun s hs => hV s hs.1) (fun s hs => hflux s hs.1) hV0 hV₁0 t ⟨ht, hpre⟩
    have h₁ := mul_nonneg (mul_nonneg (sq_nonneg ε) (sq_nonneg t)) hVp.le
    have h₂ := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * ε ^ 2) ht) hp.2
    nlinarith only [h₁, h₂]
  · have hpost : 1 / ε ≤ t := le_of_not_ge hpre
    have hposit := equation30_post_inversion_positive_derivative hε hεsmall hV hflux hV0 hV₁0 t
        hpost
    have hεt : 1 ≤ ε * t := by
      have hh := (div_le_iff₀ hε).mp hpost
      nlinarith only [hh]
    have hεt2 : 1 ≤ ε ^ 2 * t ^ 2 := by nlinarith only [hεt]
    have hε2 : 2 * ε ^ 2 ≤ 1 := by nlinarith only [hε, hεsmall]
    have h₁ := mul_nonneg (show 0 ≤ ε ^ 2 * t ^ 2 - 2 * ε ^ 2 by linarith) hVp.le
    have h₂ := mul_nonneg (by positivity : 0 ≤ 2 * ε ^ 2) hposit.le
    nlinarith only [h₁, h₂]

/-- Relative control of both components gives positivity and control of
the logarithmic ratio without dividing by an uncontrolled quantity. -/
theorem relative_state_error_consequences
    {U V Z Z₁ η : ℝ} (hZ : 0 < Z) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2)
    (herror : |V - Z| + |U + Z₁| ≤ η * Z) (hslope : |Z₁ / Z| ≤ 4) :
    0 < V ∧ |V / Z - 1| ≤ η ∧ |U / V + Z₁ / Z| ≤ 10 * η := by
  have hVerror : |V - Z| ≤ η * Z := by linarith [abs_nonneg (U + Z₁)]
  have hUerror : |U + Z₁| ≤ η * Z := by linarith [abs_nonneg (V - Z)]
  have hVlower : Z / 2 ≤ V := by
    have hh := (abs_le.mp hVerror).1
    have hm := mul_le_mul_of_nonneg_right hηsmall hZ.le
    nlinarith only [hh, hm]
  have hVp : 0 < V := by linarith only [hZ, hVlower]
  have hZne : Z ≠ 0 := ne_of_gt hZ
  have hVne : V ≠ 0 := ne_of_gt hVp
  have hZ₁abs : |Z₁| ≤ 4 * Z := by
    rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ] at hslope
    exact hslope
  refine ⟨hVp, ?_, ?_⟩
  · have hid : V / Z - 1 = (V - Z) / Z := by field_simp
    rw [hid, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    exact hVerror
  · have hnum : |U * Z + Z₁ * V| ≤ 5 * η * Z ^ 2 := by
      have h₁ := mul_le_mul_of_nonneg_right hUerror hZ.le
      have h₂ := mul_le_mul hZ₁abs hVerror (abs_nonneg _) (by positivity : 0 ≤ 4 * Z)
      have ht := abs_add_le ((U + Z₁) * Z) (Z₁ * (V - Z))
      rw [abs_mul, abs_mul, abs_of_pos hZ] at ht
      have hid : (U + Z₁) * Z + Z₁ * (V - Z) = U * Z + Z₁ * V := by ring
      rw [hid] at ht
      nlinarith only [ht, h₁, h₂]
    have hid : U / V + Z₁ / Z = (U * Z + Z₁ * V) / (V * Z) := by field_simp
    rw [hid, abs_div, abs_of_pos (mul_pos hVp hZ), div_le_iff₀ (mul_pos hVp hZ)]
    have hm := mul_le_mul_of_nonneg_right hVlower (by positivity : 0 ≤ 10 * η * Z)
    nlinarith only [hnum, hm]

/-- Stability relative to the growing primary solution, with constants
independent of its nonnegative initial slope. -/
theorem equation30_relative_state_consequences
    {ε lam δ t U V : ℝ} {F F₁ Z Z₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hlam : 0 ≤ lam) (ht : 1 ≤ t)
    (hδ : 0 ≤ δ) (hsmall : 4 * exp 6 * δ ≤ 1)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F₁ t) t)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxF : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * F t) t)
    (hfluxZ : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Z t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : |V - Z t| + |U + Z₁ t| ≤ δ * (1 + lam) * F t) :
    0 < V ∧ |V / Z t - 1| ≤ 2 * exp 6 * δ ∧
      |U / V + Z₁ t / Z t| ≤ 20 * exp 6 * δ := by
  have hZ₁0pos : 0 ≤ Z₁ 0 := by rw [hZ₁0]; exact hlam
  have hZpos := equation30_global_positive hε hεsmall hZ hfluxZ hZ0 hZ₁0pos t (by linarith)
  have hlower := equation30_slope_uniform_lower hε hεsmall hlam hF hZ hfluxF hfluxZ
    hF0 hF₁0 hZ0 hZ₁0 t ht
  have hslope := equation30_primary_logderivative_bound hε hεsmall hZ hfluxZ hZ0 hZ₁0pos t ht
  have hη : 0 ≤ 2 * exp 6 * δ := by positivity
  have hηsmall : 2 * exp 6 * δ ≤ 1 / 2 := by nlinarith only [hsmall]
  have hrelative : |V - Z t| + |U + Z₁ t| ≤ (2 * exp 6 * δ) * Z t := by
    calc
      |V - Z t| + |U + Z₁ t| ≤ δ * (1 + lam) * F t := herror
      _ = (2 * exp 6 * δ) * (((1 + lam) / (2 * exp 6)) * F t) := by field_simp
      _ ≤ (2 * exp 6 * δ) * Z t := mul_le_mul_of_nonneg_left hlower hη
  obtain ⟨hv, hratio, hs⟩ := relative_state_error_consequences hZpos hη hηsmall hrelative hslope
  refine ⟨hv, hratio, ?_⟩
  nlinarith only [hs]

/-- Division of the pressure-numerator error is safe once positivity and
the logarithmic-ratio bounds have been derived. -/
theorem pressure_ratio_error
    {Θ η j P₀ Q₀ β U V r₀ J : ℝ}
    (hΘ : 1 ≤ Θ) (_hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2) (hj : 0 ≤ j)
    (hV : 0 < V) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2) (hr₀ : |r₀| ≤ 4)
    (hr : |U / V - r₀| ≤ 10 * η)
    (hJ : |J - ((P₀ + β) * V + Q₀ * U)| ≤ j * (|U| + |V|)) :
    |J / V - (P₀ + β + Q₀ * r₀)| ≤ 10 * j + 20 * Θ ^ 2 * η := by
  have hVne : V ≠ 0 := ne_of_gt hV
  have hrabs : |U / V| ≤ 9 := by
    have hh := abs_add_le (U / V - r₀) r₀
    have hid : U / V - r₀ + r₀ = U / V := by ring
    rw [hid] at hh
    nlinarith only [hh, hr, hr₀, hηsmall]
  have hUabs : |U| ≤ 9 * V := by
    rw [abs_div, abs_of_pos hV, div_le_iff₀ hV] at hrabs
    exact hrabs
  have hJdiv : |(J - ((P₀ + β) * V + Q₀ * U)) / V| ≤ 10 * j := by
    rw [abs_div, abs_of_pos hV, div_le_iff₀ hV]
    rw [abs_of_pos hV] at hJ
    have hm := mul_le_mul_of_nonneg_left hUabs hj
    nlinarith only [hJ, hm]
  have hQerr : |Q₀ * (U / V - r₀)| ≤ 20 * Θ ^ 2 * η := by
    rw [abs_mul]
    have hh := mul_le_mul hQ₀ hr (abs_nonneg _) (by positivity : 0 ≤ 2 * Θ ^ 2)
    nlinarith only [hh]
  have hid : J / V - (P₀ + β + Q₀ * r₀) =
      (J - ((P₀ + β) * V + Q₀ * U)) / V + Q₀ * (U / V - r₀) := by field_simp; ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hJdiv hQerr)

/-- The actual pressure numerator preserves the required positive sign
under the quantitatively derived relative state error. -/
theorem equation30_pressure_sign_stable
    {ε Θ t η j U V J : ℝ} {Z Z₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ) (ht : 1 ≤ t) (htΘ : t ≤ Θ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2) (hj : 0 ≤ j)
    (hsmall : 10 * j + 20 * Θ ^ 2 * η ≤ ε ^ 2 / 2)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (herror : |V - Z t| + |U + Z₁ t| ≤ η * Z t)
    (hJ : |J - ((ε ^ 2 * t ^ 2 + ε ^ 2) * V + (-2 * ε ^ 2 * t) * U)| ≤
      j * (|U| + |V|)) :
    0 < V ∧ ε ^ 2 / 2 ≤ J / V ∧ 0 < J := by
  have ht0 : 0 ≤ t := by linarith
  have hZpos := equation30_global_positive hε hεsmall hZ hfluxZ hZ0 hZ₁0 t ht0
  have hslope := equation30_primary_logderivative_bound hε hεsmall hZ hfluxZ hZ0 hZ₁0 t ht
  obtain ⟨hVp, _, hr⟩ := relative_state_error_consequences hZpos hη hηsmall herror hslope
  have hQ₀ : |-2 * ε ^ 2 * t| ≤ 2 * Θ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ε), abs_of_nonneg ht0]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have he2 : ε ^ 2 ≤ 1 := by nlinarith only [hε, hεsmall]
    have htTheta2 : t ≤ Θ ^ 2 := by nlinarith only [htΘ, hΘ]
    have hm := mul_le_mul_of_nonneg_right he2 ht0
    nlinarith only [hm, htTheta2]
  have hr₀ : |-Z₁ t / Z t| ≤ 4 := by simpa only [neg_div, abs_neg] using hslope
  have hr' : |U / V - (-Z₁ t / Z t)| ≤ 10 * η := by simpa only [neg_div, sub_neg_eq_add] using hr
  have hpressure := pressure_ratio_error hΘ hη hηsmall hj hVp hQ₀ hr₀ hr' hJ
  have hideal := equation30_ideal_numerator_positive hε hεsmall hZ hfluxZ hZ0 hZ₁0 t ht0
  have hidealRatio : ε ^ 2 ≤ ε ^ 2 * t ^ 2 + ε ^ 2 + (-2 * ε ^ 2 * t) * (-Z₁ t / Z t) := by
    apply (mul_le_mul_iff_right₀ hZpos).mp
    have hZne : Z t ≠ 0 := ne_of_gt hZpos
    have hid : (ε ^ 2 * t ^ 2 + ε ^ 2 + (-2 * ε ^ 2 * t) * (-Z₁ t / Z t)) * Z t =
        (ε ^ 2 * t ^ 2 + ε ^ 2) * Z t + 2 * ε ^ 2 * t * Z₁ t := by field_simp
    nlinarith only [hideal, hid]
  have hJlower : ε ^ 2 / 2 ≤ J / V := by
    have hh := (abs_le.mp hpressure).1
    nlinarith only [hh, hidealRatio, hsmall]
  have hJpositive : 0 < J := by
    have hratioPos : 0 < J / V := lt_of_lt_of_le (by positivity : 0 < ε ^ 2 / 2) hJlower
    exact (div_pos_iff.mp hratioPos).resolve_right (by intro hh; linarith [hh.2]) |>.1
  exact ⟨hVp, hJlower, hJpositive⟩

/-- The third normalized velocity ratio follows from orthogonality and
the already controlled ray and first velocity ratio. -/
theorem third_ratio_error
    {Θ ρ η P Q N P₀ Q₀ r r₀ : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 2)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ ρ) (hQ : |Q - Q₀| ≤ ρ) (hN : |N - 1| ≤ ρ)
    (hr₀ : |r₀| ≤ 4) (hr : |r - r₀| ≤ 10 * η) :
    |r| ≤ 9 ∧ |-(P₀ * r₀ + Q₀)| ≤ 6 * Θ ^ 2 ∧
      |velocityThird P Q N r 1| ≤ 60 * Θ ^ 2 ∧
      |velocityThird P Q N r 1 - (-(P₀ * r₀ + Q₀))| ≤ (32 * ρ + 20 * η) * Θ ^ 2 := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hrabs : |r| ≤ 9 := by
    have hh := abs_add_le (r - r₀) r₀
    have hid : r - r₀ + r₀ = r := by ring
    rw [hid] at hh
    nlinarith only [hh, hr, hr₀, hηsmall]
  have hw₀ : |-(P₀ * r₀ + Q₀)| ≤ 6 * Θ ^ 2 := by
    rw [abs_neg]
    have hh := abs_add_le (P₀ * r₀) Q₀
    rw [abs_mul] at hh
    have hm := mul_le_mul hP₀ hr₀ (abs_nonneg _) (sq_nonneg Θ)
    nlinarith only [hh, hm, hQ₀]
  obtain ⟨hn, _, _, _, hw, _, _⟩ :=
    ray_geometric_bounds (ε := 0) (U := r) (V := 1) hΘ hρ hρsmall hP₀ hQ₀ hP hQ hN
  have hwabs : |velocityThird P Q N r 1| ≤ 60 * Θ ^ 2 := by
    norm_num only [abs_one] at hw
    have hm := mul_le_mul_of_nonneg_left hrabs (by positivity : 0 ≤ 6 * Θ ^ 2)
    nlinarith only [hw, hm]
  have hNpos : 0 < N := by linarith only [hn]
  have hNne : N ≠ 0 := ne_of_gt hNpos
  let w₀ := -(P₀ * r₀ + Q₀)
  have hPr := abs_product_difference hP hr hP₀ hrabs
  have hNw : |(N - 1) * w₀| ≤ 6 * ρ * Θ ^ 2 := by
    rw [abs_mul]
    have hh := mul_le_mul hN hw₀ (abs_nonneg _) hρ
    nlinarith only [hh]
  have hsum : |(P * r - P₀ * r₀) + (Q - Q₀) + (N - 1) * w₀| ≤
      (16 * ρ + 10 * η) * Θ ^ 2 := by
    have h₁ := abs_add_le (P * r - P₀ * r₀) (Q - Q₀)
    have h₂ := abs_add_le ((P * r - P₀ * r₀) + (Q - Q₀)) ((N - 1) * w₀)
    have hm := mul_le_mul_of_nonneg_left hΘ2 (by positivity : 0 ≤ 10 * ρ)
    nlinarith only [h₁, h₂, hPr, hQ, hNw, hm]
  refine ⟨hrabs, hw₀, hwabs, ?_⟩
  have hid : velocityThird P Q N r 1 - w₀ =
      -((P * r - P₀ * r₀) + (Q - Q₀) + (N - 1) * w₀) / N := by
    dsimp [velocityThird, w₀]
    field_simp
    ring
  change |velocityThird P Q N r 1 - w₀| ≤ _
  rw [hid, abs_div, abs_neg, abs_of_pos hNpos, div_le_iff₀ hNpos]
  have hm := mul_le_mul_of_nonneg_left hn
    (by positivity : 0 ≤ (32 * ρ + 20 * η) * Θ ^ 2)
  nlinarith only [hsum, hm]

/-- A normalized parent-gradient row applied to the velocity ratios. -/
def rowAction (A : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (r w : ℝ) : ℝ :=
  A i 0 * r + A i 1 + A i 2 * w

/-- Rowwise control of the normalized parent action on the new velocity. -/
theorem normalized_action_error
    {Θ e β r w : ℝ} {A : Fin 3 → Fin 3 → ℝ}
    (hΘ : 1 ≤ Θ) (he : 0 ≤ e) (hr : |r| ≤ 9) (hw : |w| ≤ 60 * Θ ^ 2)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ e) :
    |rowAction A 0 r w - 1| ≤ 70 * e * Θ ^ 2 ∧
    |rowAction A 1 r w - r| ≤ 70 * e * Θ ^ 2 ∧
    |rowAction A 2 r w - β| ≤ 70 * e * Θ ^ 2 := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hnorm : norm3 r 1 w ≤ 70 * Θ ^ 2 := by
    unfold norm3
    norm_num only [abs_one]
    nlinarith only [hr, hw, hΘ2]
  have hrow : ∀ i, |(A i 0 - idealVelocityEntry β i 0) * r +
      (A i 1 - idealVelocityEntry β i 1) * 1 + (A i 2 - idealVelocityEntry β i 2) * w| ≤
      70 * e * Θ ^ 2 := by
    intro i
    have hh := three_term_bound (p := r) (q := 1) (n := w) (hA i 0) (hA i 1) (hA i 2)
    have hm := mul_le_mul_of_nonneg_left hnorm he
    nlinarith only [hh, hm]
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  norm_num [idealVelocityEntry, Fin.ext_iff] at h0 h1 h2
  constructor
  · convert! h0 using 1
    unfold rowAction
    congr 1
    ring
  constructor
  · convert! h1 using 1
    unfold rowAction
    congr 1
    ring
  · convert! h2 using 1
    unfold rowAction
    congr 1
    ring

/-- The cross-product numerator for the next normalized coupling.
The middle argument `Tq` denotes ε times the physical middle component. -/
def frameCrossNumerator (ε P Q N r w Tp Tq Tn : ℝ) : ℝ :=
  (-N + ε ^ 2 * Q * w) * Tp + (N * r - P * w) * Tq + (P - ε ^ 2 * Q * r) * Tn

/-- The ideal next-frame cross numerator in original scalar coordinates. -/
def idealCrossNumerator (β P Q r : ℝ) : ℝ :=
  -1 + β * P + (1 + P ^ 2) * r ^ 2 + P * Q * r

/-- Quantitative stability of the exact cross-product numerator. -/
theorem frame_cross_numerator_error
    {Θ ρ η σ ε β P Q N P₀ Q₀ r r₀ w Tp Tq Tn : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hσ : 0 ≤ σ)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hP : |P - P₀| ≤ ρ) (hQ : |Q| ≤ 3 * Θ ^ 2)
    (hN : |N - 1| ≤ ρ) (hr₀ : |r₀| ≤ 4) (hrabs : |r| ≤ 9)
    (hr : |r - r₀| ≤ 10 * η) (hwabs : |w| ≤ 60 * Θ ^ 2)
    (hw₀ : |-(P₀ * r₀ + Q₀)| ≤ 6 * Θ ^ 2)
    (hw : |w - (-(P₀ * r₀ + Q₀))| ≤ (32 * ρ + 20 * η) * Θ ^ 2)
    (hTp : |Tp - 1| ≤ σ) (hTq : |Tq - r₀| ≤ σ + 10 * η) (hTn : |Tn - β| ≤ σ)
    (hTpabs : |Tp| ≤ 2) (hTqabs : |Tq| ≤ 10) (hTnabs : |Tn| ≤ 2) :
    |frameCrossNumerator ε P Q N r w Tp Tq Tn - idealCrossNumerator β P₀ Q₀ r₀| ≤
      (1100 * ρ + 400 * η + 12 * σ + 500 * ε ^ 2) * Θ ^ 4 := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hΘ4 : 1 ≤ Θ ^ 4 := one_le_pow₀ hΘ
  have h24 : Θ ^ 2 ≤ Θ ^ 4 := pow_le_pow_right₀ hΘ (by decide)
  let w₀ := -(P₀ * r₀ + Q₀)
  let c₀ := -N + ε ^ 2 * Q * w
  let c₁ := N * r - P * w
  let c₂ := P - ε ^ 2 * Q * r
  let c₁₀ := r₀ - P₀ * w₀
  have hQw : |ε ^ 2 * Q * w| ≤ 180 * ε ^ 2 * Θ ^ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have hh := mul_le_mul hQ hwabs (abs_nonneg _) (by positivity : 0 ≤ 3 * Θ ^ 2)
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ε)
    nlinarith only [hm]
  have hQr : |ε ^ 2 * Q * r| ≤ 27 * ε ^ 2 * Θ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have hh := mul_le_mul hQ hrabs (abs_nonneg _) (by positivity : 0 ≤ 3 * Θ ^ 2)
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ε)
    nlinarith only [hm]
  have hc₀ : |c₀ - (-1)| ≤ ρ + 180 * ε ^ 2 * Θ ^ 4 := by
    have hh := abs_add_le (-(N - 1)) (ε ^ 2 * Q * w)
    rw [abs_neg] at hh
    have hid : c₀ - (-1) = -(N - 1) + ε ^ 2 * Q * w := by dsimp [c₀]; ring
    rw [hid]
    linarith only [hh, hN, hQw]
  have hc₂ : |c₂ - P₀| ≤ ρ + 27 * ε ^ 2 * Θ ^ 2 := by
    have hh := abs_add_le (P - P₀) (-(ε ^ 2 * Q * r))
    rw [abs_neg] at hh
    have hid : c₂ - P₀ = (P - P₀) + -(ε ^ 2 * Q * r) := by dsimp [c₂]; ring
    rw [hid]
    linarith only [hh, hP, hQr]
  have hNr := abs_product_difference hN hr (by norm_num : |(1 : ℝ)| ≤ 1) hrabs
  have hPw := abs_product_difference hP hw hP₀ hwabs
  have hc₁ : |c₁ - c₁₀| ≤ (101 * ρ + 30 * η) * Θ ^ 4 := by
    have hh := abs_add_le (N * r - r₀) (-(P * w - P₀ * w₀))
    rw [abs_neg] at hh
    have hid : c₁ - c₁₀ = (N * r - r₀) + -(P * w - P₀ * w₀) := by dsimp [c₁, c₁₀]; ring
    rw [hid]
    have hm₁ := mul_le_mul_of_nonneg_left hΘ4 (by positivity : 0 ≤ 9 * ρ)
    have hm₂ := mul_le_mul_of_nonneg_left h24 (by positivity : 0 ≤ 60 * ρ)
    have hm₃ := mul_le_mul_of_nonneg_left hΘ4 (by positivity : 0 ≤ 10 * η)
    norm_num only [one_mul] at hNr
    nlinarith only [hh, hNr, hPw, hm₁, hm₂, hm₃]
  have hc₁₀ : |c₁₀| ≤ 10 * Θ ^ 4 := by
    have hh := abs_add_le r₀ (-(P₀ * w₀))
    rw [abs_neg, abs_mul] at hh
    have hm := mul_le_mul hP₀ hw₀ (abs_nonneg _) (sq_nonneg Θ)
    change |r₀ - P₀ * w₀| ≤ _
    have hid : r₀ + -(P₀ * w₀) = r₀ - P₀ * w₀ := by ring
    rw [hid] at hh
    nlinarith only [hh, hr₀, hm, hΘ4]
  have hS₀ := abs_product_difference hc₀ hTp (by norm_num : |(-1 : ℝ)| ≤ 1) hTpabs
  have hS₁ := abs_product_difference hc₁ hTq hc₁₀ hTqabs
  have hS₂ := abs_product_difference hc₂ hTn hP₀ hTnabs
  have hsum := abs_add_le (c₀ * Tp - (-1) * 1) (c₁ * Tq - c₁₀ * r₀)
  have hsum' := abs_add_le ((c₀ * Tp - (-1) * 1) + (c₁ * Tq - c₁₀ * r₀))
    (c₂ * Tn - P₀ * β)
  have hid : frameCrossNumerator ε P Q N r w Tp Tq Tn - idealCrossNumerator β P₀ Q₀ r₀ =
      (c₀ * Tp - (-1) * 1) + (c₁ * Tq - c₁₀ * r₀) + (c₂ * Tn - P₀ * β) := by
    dsimp [frameCrossNumerator, idealCrossNumerator, c₀, c₁, c₂, c₁₀, w₀]
    ring
  rw [hid]
  have hmρ := mul_le_mul_of_nonneg_left hΘ4 (by positivity : 0 ≤ 4 * ρ)
  have hmσ := mul_le_mul_of_nonneg_left hΘ4 hσ
  have hmσ2 := mul_le_mul_of_nonneg_left h24 hσ
  have hmε := mul_le_mul_of_nonneg_left h24 (by positivity : 0 ≤ 54 * ε ^ 2)
  have hpρ : 0 ≤ 86 * ρ * Θ ^ 4 := by positivity
  have hpε : 0 ≤ 86 * ε ^ 2 * Θ ^ 4 := by positivity
  nlinarith only [hsum, hsum', hS₀, hS₁, hS₂, hmρ, hmσ, hmσ2, hmε, hpρ, hpε]

/-- The cross numerator bound with every velocity-ratio and parent-action
estimate derived from ray, state, and matrix coefficient errors. -/
theorem frame_cross_error_from_matrix
    {Θ ρ η e ε β P Q N P₀ Q₀ r r₀ : ℝ} {A : Fin 3 → Fin 3 → ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 2)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2) (he : 0 ≤ e)
    (hsmall : 70 * e * Θ ^ 2 ≤ 1) (hβ : |β| ≤ 1)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ ρ) (hQ : |Q - Q₀| ≤ ρ) (hN : |N - 1| ≤ ρ)
    (hr₀ : |r₀| ≤ 4) (hr : |r - r₀| ≤ 10 * η)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ e) :
    let w := velocityThird P Q N r 1
    |frameCrossNumerator ε P Q N r w (rowAction A 0 r w) (rowAction A 1 r w) (rowAction A 2 r w) -
      idealCrossNumerator β P₀ Q₀ r₀| ≤
        (1100 * ρ + 400 * η + 840 * e * Θ ^ 2 + 500 * ε ^ 2) * Θ ^ 4 := by
  let w := velocityThird P Q N r 1
  obtain ⟨hrabs, hw₀, hwabs, hw⟩ := third_ratio_error hΘ hρ hρsmall hη hηsmall
    hP₀ hQ₀ hP hQ hN hr₀ hr
  obtain ⟨hTp, hTq, hTn⟩ := normalized_action_error hΘ he hrabs hwabs hA
  have hTq' : |rowAction A 1 r w - r₀| ≤ 70 * e * Θ ^ 2 + 10 * η := by
    have hh := abs_add_le (rowAction A 1 r w - r) (r - r₀)
    have hid : rowAction A 1 r w - r + (r - r₀) = rowAction A 1 r w - r₀ := by ring
    rw [hid] at hh
    linarith only [hh, hTq, hr]
  have hTpabs : |rowAction A 0 r w| ≤ 2 := by
    have hh := abs_add_le (rowAction A 0 r w - 1) 1
    norm_num at hh
    linarith only [hh, hTp, hsmall]
  have hTqabs : |rowAction A 1 r w| ≤ 10 := by
    have hh := abs_add_le (rowAction A 1 r w - r) r
    have hid : rowAction A 1 r w - r + r = rowAction A 1 r w := by ring
    rw [hid] at hh
    linarith only [hh, hTq, hsmall, hrabs]
  have hTnabs : |rowAction A 2 r w| ≤ 2 := by
    have hh := abs_add_le (rowAction A 2 r w - β) β
    have hid : rowAction A 2 r w - β + β = rowAction A 2 r w := by ring
    rw [hid] at hh
    linarith only [hh, hTn, hsmall, hβ]
  have hQabs : |Q| ≤ 3 * Θ ^ 2 := by
    have hh := abs_add_le (Q - Q₀) Q₀
    have hid : Q - Q₀ + Q₀ = Q := by ring
    rw [hid] at hh
    have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
    linarith only [hh, hQ, hQ₀, hρsmall, hΘ2]
  have hh := frame_cross_numerator_error (ε := ε) hΘ hρ hη
    (by positivity : 0 ≤ 70 * e * Θ ^ 2) hP₀ hP hQabs hN hr₀ hrabs hr hwabs hw₀ hw
    hTp hTq' hTn hTpabs hTqabs hTnabs
  dsimp only
  nlinarith only [hh]

/-- Squared norm of the normalized velocity direction. -/
def velocityDirectionNormSq (ε r w : ℝ) : ℝ := 1 + ε ^ 2 * (r ^ 2 + w ^ 2)

theorem velocity_direction_norm_bound
    {Θ ε r w : ℝ} (hΘ : 1 ≤ Θ) (hr : |r| ≤ 9) (hw : |w| ≤ 60 * Θ ^ 2) :
    1 ≤ velocityDirectionNormSq ε r w ∧
      velocityDirectionNormSq ε r w - 1 ≤ 3681 * ε ^ 2 * Θ ^ 4 := by
  have hΘ4 : 1 ≤ Θ ^ 4 := one_le_pow₀ hΘ
  have hr2 : r ^ 2 ≤ 81 := by
    have hh := (sq_le_sq₀ (abs_nonneg r) (by norm_num : (0 : ℝ) ≤ 9)).mpr hr
    rw [sq_abs] at hh
    norm_num at hh
    exact hh
  have hw2 : w ^ 2 ≤ 3600 * Θ ^ 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg w) (by positivity : 0 ≤ 60 * Θ ^ 2)).mpr hw
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hsum : r ^ 2 + w ^ 2 ≤ 3681 * Θ ^ 4 := by nlinarith only [hr2, hw2, hΘ4]
  have hm := mul_le_mul_of_nonneg_left hsum (sq_nonneg ε)
  unfold velocityDirectionNormSq
  constructor
  · nlinarith only [mul_nonneg (sq_nonneg ε) (add_nonneg (sq_nonneg r) (sq_nonneg w))]
  · nlinarith only [hm]

end EulerPacketFrameStability
