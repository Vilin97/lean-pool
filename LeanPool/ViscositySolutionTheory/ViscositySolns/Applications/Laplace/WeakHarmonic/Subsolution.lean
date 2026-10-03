/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.WeakHarmonic.SupConvolution
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Comparison

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Viscosity subharmonic functions are distributionally subharmonic

Let `u` be a continuous viscosity subsolution of `-Δu = 0` on an open set `C`
and let `χ ≥ 0` be a `C²` function with compact support in `C`. We prove
`0 ≤ ∫ Δχ · u`.

The proof follows the sup-convolution route:

1. Replace `u` by its sup-convolution `w = u^λ` over a compact neighbourhood
   `K` of `supp χ`. The function `w` is continuous and `λ`-semiconvex, so its
   coordinate second differences are bounded below by `-n λ`.
2. By Aleksandrov's theorem `w` has a two-sided second-order jet `(p, X)` at
   almost every point. At such a point of `supp χ`, the superjet transfer lemma
   moves `(p, X)` to a superjet of `u` at a nearby maximizer, so
   `trace X ≥ 0`, and the second differences of `w` converge to `trace X`.
3. Fatou's lemma, applied to `(Δ_h w + c) χ ≥ 0`, together with the discrete
   integration by parts `∫ (Δ_h w) χ = ∫ w (Δ_h χ)` and `Δ_h χ → Δχ`, gives
   `0 ≤ ∫ w Δχ` (`integral_mul_lapTrace_nonneg_of_ae_tendsto`).
4. Since `w → u` uniformly on `K` as `λ → ∞`, `0 ≤ ∫ Δχ · u`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Metric Set
open scoped Topology ENNReal

namespace ViscositySolns

variable {n : Nat}

/-! ### Fatou's lemma for second differences -/

/--
Fatou step. Let `w` be continuous with second differences bounded below, and
suppose that at almost every point of `supp χ` the second differences of `w`
converge to a nonnegative limit. Then `0 ≤ ∫ w Δχ` for every nonnegative `C²`
function `χ` with compact support.
-/
theorem integral_mul_lapTrace_nonneg_of_ae_tendsto {w χ : Point n → ℝ}
    (hw : Continuous w) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχ0 : 0 ≤ χ)
    {c : ℝ} (hlow : ∀ h : ℝ, h ≠ 0 → ∀ x, -c ≤ coordSecondDifference w h x)
    (hae : ∀ᵐ x, x ∈ tsupport χ → ∃ T : ℝ, 0 ≤ T ∧
      Tendsto (fun h => coordSecondDifference w h x) (𝓝[≠] 0) (𝓝 T)) :
    0 ≤ ∫ x, w x * lapTrace χ x := by
  by_cases hzero : ∀ x, χ x = 0
  · have hχeq : χ = 0 := funext hzero
    have hL : ∀ x, lapTrace χ x = 0 := fun x =>
      lapTrace_eq_zero_of_notMem_tsupport (by rw [hχeq, tsupport_zero]; exact notMem_empty x)
    simp [hL]
  push Not at hzero
  obtain ⟨x₀, hx₀⟩ := hzero
  have hχcont : Continuous χ := hχ.continuous
  have hpos : 0 < ∫ x, χ x :=
    hχcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hχc hχ0 hx₀
  set c' : ℝ := |c| + 1 with hc'def
  have hc'pos : 0 < c' := by positivity
  have hcc' : c ≤ c' := by
    have := le_abs_self c
    linarith
  -- the sequence of steps `h_k = 1 / (k + 1)`
  set hs : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hsdef
  have hs_ne : ∀ k, hs k ≠ 0 := fun k => by
    simp only [hs]
    positivity
  have hs_pos : ∀ k, 0 < hs k := fun k => by
    simp only [hs]
    positivity
  have hs_tendsto_pos : Tendsto hs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hs_pos⟩
  have hs_tendsto : Tendsto hs atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_mono_right (fun x hx => ne_of_gt hx) hs_tendsto_pos
  -- the nonnegative functions for Fatou's lemma
  set F : ℕ → Point n → ℝ := fun k x => (coordSecondDifference w (hs k) x + c') * χ x
    with hFdef
  have hFcont : ∀ k, Continuous (F k) := fun k =>
    ((continuous_coordSecondDifference hw (hs k)).add continuous_const).mul hχcont
  have hFint : ∀ k, Integrable (F k) := fun k =>
    (hFcont k).integrable_of_hasCompactSupport hχc.mul_left
  have hFnn : ∀ k x, 0 ≤ F k x := by
    intro k x
    have := hlow (hs k) (hs_ne k) x
    exact mul_nonneg (by linarith) (hχ0 x)
  set I : ℝ := ∫ x, w x * lapTrace χ x with hIdef
  set B : ℝ := ∫ x, χ x with hBdef
  have hFintegral : ∀ k, ∫ x, F k x =
      (∫ x, w x * coordSecondDifference χ (hs k) x) + c' * B := by
    intro k
    have hsplit : (fun x => F k x) =
        fun x => coordSecondDifference w (hs k) x * χ x + c' * χ x := by
      funext x
      simp only [F]
      ring
    rw [hsplit, integral_add, integral_const_mul,
      integral_coordSecondDifference_mul hw hχcont hχc]
    · exact ((continuous_coordSecondDifference hw (hs k)).mul
        hχcont).integrable_of_hasCompactSupport hχc.mul_left
    · exact (hχcont.integrable_of_hasCompactSupport hχc).const_mul c'
  have hFlim : Tendsto (fun k => ∫ x, F k x) atTop (𝓝 (I + c' * B)) := by
    simp only [hFintegral]
    exact ((tendsto_integral_mul_coordSecondDifference hw hχ hχc).comp
      hs_tendsto_pos).add_const _
  -- Fatou's lemma
  have hfatou := lintegral_liminf_le (μ := volume) (u := atTop)
    (f := fun k x => ENNReal.ofReal (F k x))
    (fun k => (hFcont k).measurable.ennreal_ofReal)
  have hlintF : ∀ k, ∫⁻ x, ENNReal.ofReal (F k x) = ENNReal.ofReal (∫ x, F k x) := fun k =>
    (ofReal_integral_eq_lintegral_ofReal (hFint k) (ae_of_all _ (hFnn k))).symm
  have hliminf : liminf (fun k => ∫⁻ x, ENNReal.ofReal (F k x)) atTop =
      ENNReal.ofReal (I + c' * B) := by
    simp only [hlintF]
    exact ((ENNReal.continuous_ofReal.tendsto _).comp hFlim).liminf_eq
  have hpoint : ∀ᵐ x, ENNReal.ofReal (c' * χ x) ≤
      liminf (fun k => ENNReal.ofReal (F k x)) atTop := by
    filter_upwards [hae] with x hx
    by_cases hxs : x ∈ tsupport χ
    · obtain ⟨T, hT, hTt⟩ := hx hxs
      have hlim : Tendsto (fun k => F k x) atTop (𝓝 ((T + c') * χ x)) :=
        ((hTt.comp hs_tendsto).add_const c').mul_const (χ x)
      have hlimeq : liminf (fun k => ENNReal.ofReal (F k x)) atTop =
          ENNReal.ofReal ((T + c') * χ x) :=
        ((ENNReal.continuous_ofReal.tendsto _).comp hlim).liminf_eq
      rw [hlimeq]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) (hχ0 x))
    · rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero, ENNReal.ofReal_zero]
      exact bot_le
  have hlintχ : ∫⁻ x, ENNReal.ofReal (c' * χ x) = ENNReal.ofReal (c' * B) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hχcont.integrable_of_hasCompactSupport hχc).const_mul c')
      (ae_of_all _ fun x => mul_nonneg hc'pos.le (hχ0 x)), integral_const_mul]
  have hchain : ENNReal.ofReal (c' * B) ≤ ENNReal.ofReal (I + c' * B) := by
    rw [← hlintχ, ← hliminf]
    exact (lintegral_mono_ae hpoint).trans hfatou
  rcases ENNReal.ofReal_le_ofReal_iff'.mp hchain with hle | hle
  · linarith
  · exfalso
    have : 0 < c' * B := mul_pos hc'pos hpos
    linarith

/-! ### Subsolutions of the Laplace equation -/

/--
Superjets relative to `K` and to a larger set `C` agree at every point of
which `K` is a neighbourhood.
-/
theorem superjet_eq_of_mem_nhds {C K : Set (Point n)} (hKC : K ⊆ C)
    {u : Point n → ℝ} {y : Point n} (hK : K ∈ 𝓝 y) :
    Superjet K u y = Superjet C u y := by
  apply superjet_congr_nhdsWithin
  rw [nhdsWithin_eq_nhds.mpr hK, nhdsWithin_eq_nhds.mpr (Filter.mem_of_superset hK hKC)]

/--
**Viscosity subharmonic functions are distributionally subharmonic.**

If `u` is a continuous viscosity subsolution of `-Δu = 0` on an open set `C`,
then `∫ Δχ · u ≥ 0` for every nonnegative `C²` function `χ` with compact
support in `C`.
-/
theorem integral_lapTrace_mul_nonneg_of_viscositySubsolution_laplace
    {C : Set (Point n)} (hC : IsOpen C) {u : Point n → ℝ}
    (hu : ViscositySubsolution C laplaceOperator u) (hcont : ContinuousOn u C)
    {χ : Point n → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχC : tsupport χ ⊆ C) (hχ0 : 0 ≤ χ) :
    0 ≤ ∫ x, lapTrace χ x * u x := by
  set K₀ := tsupport χ with hK₀def
  have hK₀ : IsCompact K₀ := hχc
  rcases K₀.eq_empty_or_nonempty with hempty | hK₀ne
  · have hL : ∀ x, lapTrace χ x = 0 := fun x =>
      lapTrace_eq_zero_of_notMem_tsupport (by rw [← hK₀def, hempty]; exact notMem_empty x)
    simp [hL]
  obtain ⟨r, hr, hrC⟩ := hK₀.exists_cthickening_subset_open hC hχC
  set K := cthickening r K₀ with hKdef
  have hK : IsCompact K := hK₀.cthickening
  have hK₀K : K₀ ⊆ K := self_subset_cthickening _
  have hKne : K.Nonempty := hK₀ne.mono hK₀K
  have hKC : K ⊆ C := hrC
  have hcontK : ContinuousOn u K := hcont.mono hKC
  have husc : UpperSemicontinuousOn u K :=
    (continuousOn_iff_lower_upperSemicontinuousOn.mp hcontK).2
  -- `K` is a neighbourhood of every point within `r / 2` of `K₀`
  have hKnhds : ∀ x ∈ K₀, ∀ y, dist y x < r / 2 → K ∈ 𝓝 y := by
    intro x hx y hy
    refine Metric.mem_nhds_iff.mpr ⟨r / 2, by positivity, fun z hz => ?_⟩
    refine mem_cthickening_of_dist_le z x r K₀ hx ?_
    have := dist_triangle z y x
    rw [mem_ball] at hz
    linarith
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn hcontK
  have hM : ∀ z ∈ K, |u z| ≤ M₀ := fun z hz => by
    simpa [Real.norm_eq_abs] using hM₀ z hz
  -- the test function side
  set L := lapTrace χ with hLdef
  have hLcont : Continuous L := continuous_lapTrace hχ
  have hLzero : ∀ x, x ∉ K₀ → L x = 0 := fun x hx => lapTrace_eq_zero_of_notMem_tsupport hx
  have hLint : Integrable L :=
    hLcont.integrable_of_hasCompactSupport (hasCompactSupport_lapTrace hχc)
  have hLuint : Integrable (fun x => L x * u x) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero
      ((hLcont.continuousOn.mul hcontK).integrableOn_compact hK) ?_
    intro x hx
    rw [hLzero x (fun h => hx (hK₀K h)), zero_mul]
  set A : ℝ := ∫ x, ‖L x‖ with hAdef
  have hA : 0 ≤ A := integral_nonneg fun x => norm_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set ε' := ε / (A + 1) with hε'def
  have hε' : 0 < ε' := by positivity
  obtain ⟨lam, hlam, hlamδ, happrox⟩ :=
    exists_lambda_abs_compactSupConvolution_sub_le hKne hK hcontK hM hε'
      (half_pos hr)
  set w : Point n → ℝ := fun ξ => compactSupConvolution lam K u ξ with hwdef
  have hw : Continuous w := continuous_compactSupConvolution_of_isCompact hKne hK husc
  have hsemi : CoordinateSemiconvexOn lam Set.univ w :=
    coordinateSemiconvexOn_compactSupConvolution_of_isCompact hKne hK husc
  -- Step 1: `0 ≤ ∫ w Δχ`.
  obtain ⟨R, hRpos, hK₀R⟩ := hK₀.isBounded.subset_closedBall_lt 0 (0 : Point n)
  have hnull := AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external n
    w 0 R hRpos ⟨lam, hsemi.mono_set (subset_univ _)⟩
  have hae : ∀ᵐ x, x ∈ tsupport χ → ∃ T : ℝ, 0 ≤ T ∧
      Tendsto (fun h => coordSecondDifference w h x) (𝓝[≠] 0) (𝓝 T) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxK₀
    have hjet : HasSomeSecondOrderJet w x := by
      by_contra hno
      exact hx ⟨hK₀R hxK₀, hno⟩
    obtain ⟨p, X, _, hJ⟩ := hjet
    refine ⟨Matrix.trace X, ?_, tendsto_coordSecondDifference_of_hasSecondOrderJet hJ⟩
    obtain ⟨y, hy, hmax⟩ := exists_isMaxOn_supConvolutionKernel_of_isCompact
      (lambda := lam) (ξ := x) hKne hK husc
    have hsuperK : ({ gradient := p, hessian := X } : Jet n) ∈ Superjet K u y :=
      superjet_of_superjet_compactSupConvolution_of_isCompact hKne hK husc hy hmax hJ.1
    have hdist : dist y x < r / 2 :=
      dist_lt_of_isMaxOn_supConvolutionKernel (half_pos hr) hlamδ hM (hK₀K hxK₀) hy hmax
    rw [superjet_eq_of_mem_nhds hKC (hKnhds x hxK₀ y hdist)] at hsuperK
    have hsub := hu.2 y (hKC hy) _ hsuperK
    simp only [laplaceOperator_apply] at hsub
    linarith
  have hstep1 : 0 ≤ ∫ x, w x * L x :=
    integral_mul_lapTrace_nonneg_of_ae_tendsto hw hχ hχc hχ0
      (fun h hh x => neg_mul_le_coordSecondDifference_of_coordinateSemiconvexOn hsemi hh x)
      hae
  -- Step 2: compare `∫ w Δχ` with `∫ Δχ u`.
  have hwLint : Integrable (fun x => w x * L x) :=
    (hw.mul hLcont).integrable_of_hasCompactSupport (hasCompactSupport_lapTrace hχc).mul_left
  have hbound : ∀ x, ‖w x * L x - L x * u x‖ ≤ ε' * ‖L x‖ := by
    intro x
    by_cases hx : x ∈ K
    · have hdiff : w x * L x - L x * u x = (w x - u x) * L x := by ring
      rw [hdiff, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (happrox x hx) (norm_nonneg _)
    · rw [hLzero x (fun h => hx (hK₀K h))]
      simp
  have hle := norm_integral_le_of_norm_le (hLint.norm.const_mul ε') (ae_of_all _ hbound)
  rw [integral_sub hwLint hLuint, integral_const_mul, ← hAdef] at hle
  have habs := (le_abs_self _).trans (le_of_eq_of_le (Real.norm_eq_abs _).symm hle)
  have hεA : ε' * A ≤ ε := by
    rw [hε'def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end ViscositySolns
