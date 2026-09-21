/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall

/-!
# Linear functionals in `𝔻₁,₂` and the derivative of a Brownian coordinate

The Sobolev space `𝔻₁,₂` is the graph closure of the Malliavin derivative on *bounded* smooth
functionals, so unbounded Gaussian functionals such as `B T` are not in it by definition.  We show
that every continuous linear functional `L` lies in `𝔻₁,₂` with derivative the constant
Cameron--Martin generator `ofDual μ L` (`dualLp_mem_domD12`), by approximating `L` with the smooth
bounded cutoffs `(n + 1) arctan (L / (n + 1))` and using dominated convergence in `L²`
(`tendsto_toLp_of_dominated`).

On a Brownian-generated Gaussian space this gives the first example of every textbook,
`Dₜ (B T) = 1_{(0, T]}` (`timeDerivative_mderivClosure_brownianLp`), and, since the whole
Cameron--Martin space lies in `𝔻₁,₂` by closedness (`coe_space_mem_domD12`),
`Dₜ (∫ g dB) = g(t)` for every `g ∈ L²(ℝ≥0)` (`timeDerivative_mderivClosure_wienerIntegral`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

universe u_1 u_2

recall MeasureTheory.tendsto_integral_of_dominated_convergence {α : Type u_1} {G : Type u_2}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {m : MeasurableSpace α} {μ : Measure α}
    {F : ℕ → α → G} {f : α → G} (bound : α → ℝ) (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ)
    (bound_integrable : Integrable bound μ) (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n ↦ F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ))

namespace Malliavin

/-! ### A smooth cutoff -/

/-- `|arctan u| ≤ |u|`. -/
theorem abs_arctan_le_abs (u : ℝ) : |Real.arctan u| ≤ |u| := by
  have hmono : Monotone fun x : ℝ ↦ x - Real.arctan x := by
    refine monotone_of_deriv_nonneg (differentiable_id.sub Real.differentiable_arctan) fun x ↦ ?_
    rw [((hasDerivAt_id' x).fun_sub (Real.hasDerivAt_arctan x)).deriv]
    have : 1 / (1 + x ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [sq_nonneg x]
    linarith
  rcases le_total 0 u with hu | hu
  · have h := hmono hu
    simp only [Real.arctan_zero, sub_zero] at h
    rw [abs_of_nonneg hu, abs_of_nonneg (Real.arctan_nonneg.mpr hu)]
    linarith
  · have h := hmono hu
    simp only [Real.arctan_zero, sub_zero] at h
    have hle : Real.arctan u ≤ 0 := by
      rw [← Real.arctan_zero]
      exact Real.arctan_le_arctan_iff.mpr hu
    rw [abs_of_nonpos hu, abs_of_nonpos hle]
    linarith

/-- The smooth cutoff `x ↦ (n + 1) arctan (x / (n + 1))`. -/
noncomputable def cutoff (n : ℕ) (x : ℝ) : ℝ := (n + 1 : ℝ) * Real.arctan (x / (n + 1))

theorem cutoff_contDiff (n : ℕ) : ContDiff ℝ 1 (cutoff n) :=
  contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_id.div_const _))

theorem abs_cutoff_le (n : ℕ) (x : ℝ) : |cutoff n x| ≤ |x| := by
  unfold cutoff
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
  calc (n + 1 : ℝ) * |Real.arctan (x / (n + 1))| ≤ (n + 1) * |x / (n + 1)| :=
        mul_le_mul_of_nonneg_left (abs_arctan_le_abs _) (by positivity)
    _ = |x| := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1),
          mul_div_cancel₀ _ (by positivity : (n + 1 : ℝ) ≠ 0)]

theorem abs_cutoff_le_const (n : ℕ) (x : ℝ) : |cutoff n x| ≤ (n + 1) * (Real.pi / 2) := by
  unfold cutoff
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact (abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩)

theorem hasDerivAt_cutoff (n : ℕ) (x : ℝ) :
    HasDerivAt (cutoff n) (1 / (1 + (x / (n + 1)) ^ 2)) x := by
  have h := ((Real.hasDerivAt_arctan (x / (n + 1))).comp x
    ((hasDerivAt_id x).div_const (n + 1 : ℝ))).const_mul (n + 1 : ℝ)
  refine h.congr_deriv ?_
  field_simp

theorem deriv_cutoff (n : ℕ) (x : ℝ) : deriv (cutoff n) x = 1 / (1 + (x / (n + 1)) ^ 2) :=
  (hasDerivAt_cutoff n x).deriv

theorem deriv_cutoff_nonneg (n : ℕ) (x : ℝ) : 0 ≤ deriv (cutoff n) x := by
  rw [deriv_cutoff]
  positivity

theorem deriv_cutoff_le_one (n : ℕ) (x : ℝ) : deriv (cutoff n) x ≤ 1 := by
  rw [deriv_cutoff, div_le_one (by positivity)]
  linarith [sq_nonneg (x / (n + 1))]

theorem abs_deriv_cutoff_le (n : ℕ) (x : ℝ) : |deriv (cutoff n) x| ≤ 1 := by
  rw [abs_of_nonneg (deriv_cutoff_nonneg n x)]
  exact deriv_cutoff_le_one n x

theorem tendsto_div_nat_succ (x : ℝ) :
    Tendsto (fun n : ℕ ↦ x / (n + 1 : ℝ)) atTop (𝓝 0) := by
  have := (tendsto_const_div_atTop_nhds_zero_nat x).comp (tendsto_add_atTop_nat 1)
  refine this.congr fun n ↦ ?_
  simp only [Function.comp_apply]
  push_cast
  ring

theorem tendsto_deriv_cutoff (x : ℝ) :
    Tendsto (fun n : ℕ ↦ deriv (cutoff n) x) atTop (𝓝 1) := by
  simp_rw [deriv_cutoff]
  have h := ((tendsto_div_nat_succ x).pow 2).const_add 1
  have h2 : Tendsto (fun n : ℕ ↦ 1 / (1 + (x / (n + 1 : ℝ)) ^ 2)) atTop (𝓝 (1 / (1 + 0 ^ 2))) :=
    tendsto_const_nhds.div h (by norm_num)
  simpa using h2

theorem tendsto_cutoff (x : ℝ) : Tendsto (fun n : ℕ ↦ cutoff n x) atTop (𝓝 x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [cutoff, zero_div, Real.arctan_zero, mul_zero, tendsto_const_nhds_iff]
  -- `cutoff n x = x * (arctan h / h)` with `h = x / (n + 1) → 0`
  have hslope : Tendsto (fun h : ℝ ↦ Real.arctan h / h) (𝓝[≠] 0) (𝓝 1) := by
    have := (Real.hasDerivAt_arctan 0).tendsto_slope_zero
    simp only [zero_add, Real.arctan_zero, sub_zero, smul_eq_mul] at this
    norm_num at this
    exact this.congr fun h ↦ by rw [inv_mul_eq_div]
  have hn : Tendsto (fun n : ℕ ↦ x / (n + 1 : ℝ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_div_nat_succ x, ?_⟩
    exact Filter.Eventually.of_forall fun n ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      positivity
  have h := (hslope.comp hn).const_mul x
  rw [mul_one] at h
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_apply, cutoff]
  field_simp

/-! ### Dominated convergence in `L²` -/

section DCT

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

/-- **Dominated convergence in `L²`.** -/
theorem tendsto_toLp_of_dominated {f : ℕ → α → E} {g : α → E} (hf : ∀ n, MemLp (f n) 2 μ)
    (hg : MemLp g 2 μ) {bound : α → ℝ} (hbound : Integrable bound μ)
    (h : ∀ n, ∀ᵐ x ∂μ, ‖f n x - g x‖ ^ 2 ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ n, ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2 = ∫ x, ‖f n x - g x‖ ^ 2 ∂μ := by
    intro n
    rw [norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (hf n), MemLp.coeFn_toLp hg,
      Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g)] with x h2 h3 h4
    rw [h4, Pi.sub_apply, h2, h3]
  have hint : Tendsto (fun n ↦ ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 (∫ _, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence bound
      (fun n ↦ ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2) hbound
      (fun n ↦ (h n).mono fun x hx ↦ ?_)
      (hlim.mono fun x hx ↦ ?_)
    · rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · have := (tendsto_iff_norm_sub_tendsto_zero.mp hx).pow 2
      simpa using this
  rw [integral_zero] at hint
  have hsq : Tendsto (fun n ↦ ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hnorm] using hint
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

end DCT

/-! ### Linear functionals lie in `𝔻₁,₂` -/

section Dual

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

/-- The `L²` class of a continuous linear functional. -/
noncomputable def dualLp (L : StrongDual ℝ W) : Lp ℝ 2 μ :=
  (IsGaussian.memLp_dual μ L 2 (by simp)).toLp L

omit [CompleteSpace W] [SecondCountableTopology W] in
theorem coeFn_dualLp (L : StrongDual ℝ W) : (dualLp μ L : W → ℝ) =ᵐ[μ] L :=
  MemLp.coeFn_toLp _

/-- The constant `H`-valued random variable `ofDual μ L`. -/
noncomputable def constOfDual (L : StrongDual ℝ W) : Lp (Space μ) 2 μ :=
  (memLp_const (ofDual μ L)).toLp _

/-- **Continuous linear functionals lie in `𝔻₁,₂`, with Malliavin derivative the constant
Cameron--Martin generator `ofDual μ L`.** -/
theorem dualLp_mem_domD12 (L : StrongDual ℝ W) :
    dualLp μ L ∈ domD12 μ ∧ mderivClosure μ (dualLp μ L) = constOfDual μ L := by
  have hn : ∀ n, IsSmoothBounded fun x ↦ cutoff n (L x) := fun n ↦
    IsSmoothBounded.comp_dual (cutoff_contDiff n) ⟨_, abs_cutoff_le_const n⟩
      ⟨1, abs_deriv_cutoff_le n⟩ L
  refine mem_domD12_of_tendsto μ (F := fun n ↦ (hn n).toLp μ)
    (fun n ↦ (hn n).toLp_mem_domD12 μ) ?_ ?_
  · -- `cutoff n ∘ L → L` in `L²(μ)`
    refine tendsto_toLp_of_dominated (hf := fun n ↦ (hn n).memLp μ 2)
      (hg := IsGaussian.memLp_dual μ L 2 (by simp)) (bound := fun x ↦ 4 * (L x) ^ 2)
      ((IsGaussian.memLp_dual μ L 2 (by simp)).integrable_sq.const_mul 4)
      (fun n ↦ Filter.Eventually.of_forall fun x ↦ ?_)
      (Filter.Eventually.of_forall fun x ↦ tendsto_cutoff (L x))
    have h1 : |cutoff n (L x) - L x| ≤ 2 * |L x| := by
      calc |cutoff n (L x) - L x| ≤ |cutoff n (L x)| + |L x| := abs_sub _ _
        _ ≤ |L x| + |L x| := add_le_add_left (abs_cutoff_le n _) _
        _ = 2 * |L x| := by ring
    calc ‖cutoff n (L x) - L x‖ ^ 2 = |cutoff n (L x) - L x| ^ 2 := by rw [Real.norm_eq_abs]
      _ ≤ (2 * |L x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = 4 * (L x) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  · -- `D (cutoff n ∘ L) = cutoff n' (L) • ofDual L → ofDual L` in `L²(μ; H)`
    simp_rw [mderivClosure_toLp]
    unfold IsSmoothBounded.mderivLp constOfDual
    have hm : ∀ n x,
        mderiv μ (fun y ↦ cutoff n (L y)) x = deriv (cutoff n) (L x) • ofDual μ L := by
      intro n x
      rw [mderiv_comp μ ((cutoff_contDiff n).differentiable one_ne_zero _) L.differentiableAt,
        mderiv_dual]
    refine tendsto_toLp_of_dominated (hf := fun n ↦ (hn n).memLp_mderiv μ 2)
      (hg := memLp_const _) (bound := fun _ ↦ 4 * ‖ofDual μ L‖ ^ 2) (integrable_const _)
      (fun n ↦ Filter.Eventually.of_forall fun x ↦ ?_)
      (Filter.Eventually.of_forall fun x ↦ ?_)
    · rw [hm]
      have h1 : deriv (cutoff n) (L x) • ofDual μ L - ofDual μ L =
          (deriv (cutoff n) (L x) - 1) • ofDual μ L := by
        rw [sub_smul, one_smul]
      rw [h1, norm_smul, Real.norm_eq_abs, mul_pow]
      have h2 : |deriv (cutoff n) (L x) - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [deriv_cutoff_nonneg n (L x), deriv_cutoff_le_one n (L x)]
      calc |deriv (cutoff n) (L x) - 1| ^ 2 * ‖ofDual μ L‖ ^ 2
          ≤ 1 ^ 2 * ‖ofDual μ L‖ ^ 2 := by gcongr
        _ ≤ 4 * ‖ofDual μ L‖ ^ 2 := by linarith [sq_nonneg ‖ofDual μ L‖]
    · rw [show (fun n ↦ mderiv μ (fun y ↦ cutoff n (L y)) x) =
          fun n ↦ deriv (cutoff n) (L x) • ofDual μ L from funext fun n ↦ hm n x]
      have := (tendsto_deriv_cutoff (L x)).smul_const (ofDual μ L)
      simpa using this

omit [CompleteSpace W] [SecondCountableTopology W] in
theorem constOfDual_eq_smulLp (L : StrongDual ℝ W) :
    constOfDual μ L = smulLp (ofDual μ L) (Lp.const 2 μ (1 : ℝ)) := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_const (ofDual μ L)),
    coeFn_smulLp (ofDual μ L) (Lp.const 2 μ (1 : ℝ)), Lp.coeFn_const 2 μ (1 : ℝ)] with x h1 h2 h3
  rw [constOfDual, h1, h2, h3]
  simp only [Function.const_apply, one_smul]

end Dual

/-! ### The derivative of a Brownian coordinate -/

section Brownian

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The Brownian coordinate `B t` is the class of the functional `L t`. -/
theorem brownianLp_eq_dualLp (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (t : ℝ≥0) : brownianLp hB t = dualLp P (L t) := by
  apply Lp.ext
  filter_upwards [coeFn_brownianLp hB t, coeFn_dualLp P (L t)] with w h1 h2
  rw [h1, h2, hL]

/-- Brownian coordinates lie in `𝔻₁,₂`. -/
theorem brownianLp_mem_domD12 (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (t : ℝ≥0) : brownianLp hB t ∈ domD12 P := by
  rw [brownianLp_eq_dualLp hB L hL t]
  exact (dualLp_mem_domD12 P (L t)).1

/-- **`Dₜ (B T) = 1_{(0, T]}`**: the time derivative of the Brownian coordinate `B T` is the
deterministic process `(t, ω) ↦ 1_{(0, T]}(t)`. -/
theorem timeDerivative_mderivClosure_brownianLp (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P (brownianLp hB T)) =
      tensor (intervalIndicator T) (Lp.const 2 P (1 : ℝ)) := by
  rw [brownianLp_eq_dualLp hB L hL T, (dualLp_mem_domD12 P (L T)).2, constOfDual_eq_smulLp,
    timeDerivative_smulLp hB L hL hgen, wienerIntegralEquiv_symm_ofDual hB L hL hgen]

end Brownian

/-! ### The Cameron--Martin space lies in `𝔻₁,₂`

By closedness of the graph, every element `h` of the Cameron--Martin space (an `L²` limit of
centered linear functionals) lies in `𝔻₁,₂` with derivative the constant `h`; on a Wiener space
this reads `Dₜ (∫ g dB) = g(t)`. -/

section Space

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

/-- The constant `H`-valued random variable `h`, as a linear isometry `H → L²(μ; H)`. -/
noncomputable def constLp : Space μ →ₗᵢ[ℝ] Lp (Space μ) 2 μ :=
  ⟨(Lp.constL 2 μ ℝ : Space μ →L[ℝ] Lp (Space μ) 2 μ).toLinearMap, fun h ↦ by
    rw [ContinuousLinearMap.coe_coe, Lp.constL_apply]
    have hsq : ‖(Lp.const 2 μ h : Lp (Space μ) 2 μ)‖ ^ 2 = ‖h‖ ^ 2 := by
      rw [norm_sq_eq_integral_norm_sq, integral_congr_ae ((Lp.coeFn_const 2 μ h).mono
        fun x hx ↦ by rw [hx])]
      simp only [Function.const_apply, integral_const, measureReal_def, measure_univ,
        ENNReal.toReal_one, one_smul]
    exact (sq_eq_sq₀ (norm_nonneg (Lp.const 2 μ h : Lp (Space μ) 2 μ)) (norm_nonneg h)).mp hsq⟩

omit [CompleteSpace W] [SecondCountableTopology W] in
theorem constLp_apply (h : Space μ) : constLp μ h = Lp.const 2 μ h := rfl

omit [CompleteSpace W] [SecondCountableTopology W] in
theorem constOfDual_eq_constLp (L : StrongDual ℝ W) : constOfDual μ L = constLp μ (ofDual μ L) := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_const (ofDual μ L)), Lp.coeFn_const 2 μ (ofDual μ L)]
    with x h1 h2
  rw [constOfDual, h1, constLp_apply, h2]
  rfl

/-- **The Cameron--Martin space lies in `𝔻₁,₂`**, and the Malliavin derivative of `h ∈ H` (as an
`L²(μ)` random variable) is the constant `h`. -/
theorem coe_space_mem_domD12 (h : Space μ) :
    (h : Lp ℝ 2 μ) ∈ domD12 μ ∧ mderivClosure μ (h : Lp ℝ 2 μ) = constLp μ h := by
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.mp (denseRange_ofDual μ h)
  choose L hL using hx
  -- `dualLp μ (L n)` differs from `ofDual μ (L n)` by the centering constant `L n (mean μ)`
  have hcenter : ∀ n, dualLp μ (L n) =
      (ofDual μ (L n) : Lp ℝ 2 μ) + Lp.const 2 μ (L n (mean μ)) := by
    intro n
    apply Lp.ext
    filter_upwards [coeFn_dualLp μ (L n), centeredDualToLp_ae_eq μ (L n),
      Lp.coeFn_add (ofDual μ (L n) : Lp ℝ 2 μ) (Lp.const 2 μ (L n (mean μ))),
      Lp.coeFn_const 2 μ (L n (mean μ))] with x h1 h2 h3 h4
    rw [h1, h3, Pi.add_apply, coe_ofDual, h2, h4]
    simp only [Function.const_apply, sub_add_cancel]
  -- the functional `dualLp μ (L n) - const` has the same derivative as `dualLp μ (L n)`
  have hmem : ∀ n, (ofDual μ (L n) : Lp ℝ 2 μ) ∈ domD12 μ ∧
      mderivClosure μ (ofDual μ (L n) : Lp ℝ 2 μ) = constLp μ (ofDual μ (L n)) := by
    intro n
    have hc : (Lp.const 2 μ (L n (mean μ)) : Lp ℝ 2 μ) ∈ domD12 μ ∧
        mderivClosure μ (Lp.const 2 μ (L n (mean μ))) = 0 := by
      have hsb := IsSmoothBounded.const (W := W) (L n (mean μ))
      have heq : hsb.toLp μ = Lp.const 2 μ (L n (mean μ)) := by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (hsb.memLp μ 2), Lp.coeFn_const 2 μ (L n (mean μ))]
          with x h1 h2
        rw [IsSmoothBounded.toLp, h1, h2]
        rfl
      refine ⟨heq ▸ hsb.toLp_mem_domD12 μ, ?_⟩
      rw [← heq, mderivClosure_toLp]
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp (hsb.memLp_mderiv μ 2), Lp.coeFn_zero (Space μ) 2 μ]
        with x h1 h2
      rw [IsSmoothBounded.mderivLp, h1, h2, mderiv_const]
      rfl
    have hsub : (ofDual μ (L n) : Lp ℝ 2 μ) =
        dualLp μ (L n) + (-1 : ℝ) • Lp.const 2 μ (L n (mean μ)) := by
      rw [hcenter n, neg_one_smul, add_neg_cancel_right]
    have hc' : ((-1 : ℝ) • Lp.const 2 μ (L n (mean μ)) : Lp ℝ 2 μ) ∈ domD12 μ :=
      Submodule.smul_mem (D12 μ) _ hc.1
    rw [hsub]
    refine ⟨Submodule.add_mem (D12 μ) (dualLp_mem_domD12 μ (L n)).1 hc', ?_⟩
    rw [mderivClosure_add μ (dualLp_mem_domD12 μ (L n)).1 hc', mderivClosure_smul μ hc.1,
      (dualLp_mem_domD12 μ (L n)).2, hc.2, smul_zero, add_zero, constOfDual_eq_constLp]
  refine mem_domD12_of_tendsto μ (F := fun n ↦ (ofDual μ (L n) : Lp ℝ 2 μ))
    (fun n ↦ (hmem n).1) ?_ ?_
  · have : Tendsto (fun n ↦ ((x n : Space μ) : Lp ℝ 2 μ)) atTop (𝓝 (h : Lp ℝ 2 μ)) :=
      (continuous_subtype_val.tendsto h).comp hlim
    refine this.congr fun n ↦ ?_
    rw [← hL n]
  · simp_rw [(hmem _).2]
    have := ((constLp μ).continuous.tendsto h).comp hlim
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply, ← hL n]

omit [CompleteSpace W] [SecondCountableTopology W] in
theorem constLp_eq_smulLp (h : Space μ) : constLp μ h = smulLp h (Lp.const 2 μ (1 : ℝ)) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_const 2 μ h, coeFn_smulLp h (Lp.const 2 μ (1 : ℝ)),
    Lp.coeFn_const 2 μ (1 : ℝ)] with x h1 h2 h3
  rw [constLp_apply, h1, h2, h3]
  simp only [Function.const_apply, one_smul]

end Space

section WienerSpace

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

/-- Wiener integrals lie in the Cameron--Martin space. -/
theorem wienerIntegral_mem_space (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) : wienerIntegral hB g ∈ Space P := by
  rw [space_eq_firstChaos hB L hL hgen, ← range_wienerIntegral]
  exact ⟨g, rfl⟩

/-- **`Dₜ (∫ g dB) = g(t)`**: the time derivative of a Wiener integral is the deterministic
process `(t, ω) ↦ g t`. -/
theorem timeDerivative_mderivClosure_wienerIntegral (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    timeDerivative hB L hL hgen (mderivClosure P (wienerIntegral hB g)) =
      tensor g (Lp.const 2 P (1 : ℝ)) := by
  have hmem := wienerIntegral_mem_space hB L hL hgen g
  rw [(coe_space_mem_domD12 P ⟨_, hmem⟩).2, constLp_eq_smulLp, timeDerivative_smulLp hB L hL hgen]
  congr 1
  apply (wienerIntegralEquiv hB).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

end WienerSpace

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
