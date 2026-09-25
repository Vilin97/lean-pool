/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.Dynkin
public import LeanPool.MarkovProcess.MarkovProcess.Feller.Resolvent
public import Mathlib.Probability.Distributions.Gaussian.Real


/-!
# The one-dimensional heat semigroup and its continuous-path process

The transition semigroup on the real line whose kernel at time `t` is the Gaussian law with mean
the starting point and variance `t`.  It is conservative, Feller, and satisfies the Kolmogorov
moment criterion with exponents `p = 4`, `q = 2` and the fourth moment of the standard Gaussian as
constant, so the existence-and-uniqueness theorem of `MarkovProcess.Main` applies to it.  The
process it produces is named `brownianMotion`.

Main results:

* `heatSemigroup`, `heatSemigroup_apply`: the semigroup and its Gaussian transition measures.
* `isConservative_heatSemigroup`: no mass is lost.
* `kernelIntegral_heatSemigroup`: the scaling representation of the transition operator.
* `isFellerKernelSemigroup_heatSemigroup`: the Feller property.
* `heatResolvent`: its positive contractive `C₀` resolvent.
* `heatExhaustion`: the explicit exhaustion `x ↦ 1 / (1 + |x|)`.
* `hasKolmogorovMoments_heatSemigroup`: the intrinsic Kolmogorov moment bound.
* `existsUnique_continuousProcess_heatSemigroup`: the main theorem, applied.
* `brownianMotion`, `brownianMotion_map_eval`, `brownianMotion_map_finsetEvaluation`: the
  continuous-path process and its finite-dimensional distributions.

Only one space dimension is treated: the multidimensional heat semigroup is not constructed here.
Nothing in this file asserts independence of increments; that is proved in
`MarkovProcess.Examples.BrownianMotion`.
-/

@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

section

section Gaussian

/-- Every real Gaussian is the image of the standard Gaussian under an affine map: the law with
mean `x` and variance `t` is the law of `x + √t * z` for a standard normal `z`. -/
theorem gaussianReal_eq_map_add_sqrt_mul (x : ℝ) (t : ℝ≥0) :
    gaussianReal x t = (gaussianReal 0 1).map (fun z ↦ x + Real.sqrt t * z) := by
  have hmul : (gaussianReal 0 1).map (fun z : ℝ ↦ Real.sqrt t * z) = gaussianReal 0 t := by
    rw [gaussianReal_map_const_mul (Real.sqrt t)]
    congr 1
    · ring
    · rw [mul_one]
      ext
      simp [Real.sq_sqrt t.coe_nonneg]
  have hadd := gaussianReal_map_const_add (μ := 0) (v := t) x
  rw [zero_add] at hadd
  rw [← hadd, ← hmul, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Translating a real Gaussian by a constant translates its mean. -/
theorem gaussianReal_eq_map_const_add (x : ℝ) (t : ℝ≥0) :
    gaussianReal x t = (gaussianReal 0 t).map (fun u ↦ x + u) := by
  rw [gaussianReal_map_const_add x, zero_add]

end Gaussian

section Definition

/-- The Gaussian transition kernel of the heat semigroup, jointly in the time and the starting
point.  It is built from the standard Gaussian by the affine map `(t, x, z) ↦ x + √t * z`, which
makes joint measurability automatic. -/
def heatKernelJoint : Kernel (NNReal × ℝ) ℝ :=
  (Kernel.id ×ₖ Kernel.const (NNReal × ℝ) (gaussianReal 0 1)).map
    (fun q : (NNReal × ℝ) × ℝ ↦ q.1.2 + Real.sqrt q.1.1 * q.2)

theorem heatKernelJoint_apply (p : NNReal × ℝ) : heatKernelJoint p = gaussianReal p.2 p.1 := by
  have hmeas : Measurable (fun q : (NNReal × ℝ) × ℝ ↦ q.1.2 + Real.sqrt q.1.1 * q.2) := by
    fun_prop
  rw [heatKernelJoint, Kernel.map_apply _ hmeas, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hmeas (by fun_prop)]
  conv_rhs => rw [gaussianReal_eq_map_add_sqrt_mul p.2 p.1]
  rfl

/-- The transition kernel of the heat semigroup at time `t`. -/
def heatKernel (t : NNReal) : Kernel ℝ ℝ :=
  Kernel.comap heatKernelJoint (fun x : ℝ ↦ (t, x)) (by fun_prop)

@[simp]
theorem heatKernel_apply (t : NNReal) (x : ℝ) : heatKernel t x = gaussianReal x t := by
  rw [heatKernel, Kernel.comap_apply, heatKernelJoint_apply]

instance isMarkovKernel_heatKernel (t : NNReal) : IsMarkovKernel (heatKernel t) :=
  ⟨fun x ↦ by rw [heatKernel_apply]; infer_instance⟩

/-- The mean of a real Gaussian of fixed variance is a measurable parameter. -/
theorem measurable_gaussianReal_left (t : NNReal) : Measurable (fun x : ℝ ↦ gaussianReal x t) := by
  have hfun : (fun x : ℝ ↦ gaussianReal x t) = fun x ↦ heatKernel t x :=
    funext fun x ↦ (heatKernel_apply t x).symm
  rw [hfun]
  exact (heatKernel t).measurable

/-- The real Gaussians of a fixed mean form a convolution semigroup in the variance: sampling a
Gaussian of variance `s` and then, from the value obtained, a Gaussian of variance `t` gives a
Gaussian of variance `s + t`. -/
theorem bind_gaussianReal (x : ℝ) (s t : NNReal) :
    (gaussianReal x s).bind (fun y ↦ gaussianReal y t) = gaussianReal x (s + t) := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [Measure.lintegral_bind (measurable_gaussianReal_left t).aemeasurable hf.aemeasurable]
  have hinner : ∀ y : ℝ, ∫⁻ z, f z ∂(gaussianReal y t)
      = ∫⁻ u, f (y + u) ∂(gaussianReal 0 t) := by
    intro y
    rw [gaussianReal_eq_map_const_add y t, lintegral_map hf (by fun_prop)]
  simp_rw [hinner]
  rw [← Measure.lintegral_conv hf, gaussianReal_conv_gaussianReal, add_zero]

/-- **The one-dimensional heat semigroup.**  Its transition measure at time `t` from `x` is the
Gaussian law with mean `x` and variance `t`. -/
def heatSemigroup : SubMarkovKernelSemigroup ℝ where
  kernel := heatKernel
  measurable_kernel := by
    have hfun : (fun p : NNReal × ℝ ↦ heatKernel p.1 p.2) = fun p ↦ heatKernelJoint p := by
      funext p
      rw [heatKernel, Kernel.comap_apply]
    rw [hfun]
    exact heatKernelJoint.measurable
  kernel_zero := Kernel.ext fun x ↦ by
    rw [heatKernel_apply, gaussianReal_zero_var, Kernel.id_apply]
  kernel_add := fun s t ↦ Kernel.ext fun x ↦ by
    have hfun : ⇑(heatKernel t) = fun y ↦ gaussianReal y t := funext (heatKernel_apply t)
    rw [Kernel.comp_apply, heatKernel_apply, heatKernel_apply, hfun, bind_gaussianReal]
  isSubMarkovKernel := fun _ ↦ IsSubMarkovKernel.of_isMarkovKernel _

@[simp]
theorem heatSemigroup_apply (t : NNReal) (x : ℝ) : heatSemigroup t x = gaussianReal x t :=
  heatKernel_apply t x

/-- The heat semigroup is conservative: every transition measure has total mass one. -/
theorem isConservative_heatSemigroup : heatSemigroup.IsConservative := by
  intro t x
  rw [heatSemigroup_apply]
  exact measure_univ

end Definition

section Feller

/-- **The scaling representation of the heat semigroup.**  Integrating a `C₀` function against the
transition measure at time `t` from `x` is integrating its translate `z ↦ f (x + √t * z)` against
the standard Gaussian. -/
theorem kernelIntegral_heatSemigroup (t : NNReal) (f : C₀(ℝ, ℝ)) (x : ℝ) :
    kernelIntegral (heatSemigroup t) f x =
      ∫ z, f (x + Real.sqrt t * z) ∂(gaussianReal 0 1) := by
  rw [kernelIntegral, heatSemigroup_apply, gaussianReal_eq_map_add_sqrt_mul]
  exact integral_map (φ := fun z : ℝ ↦ x + Real.sqrt t * z) (f := fun y : ℝ ↦ f y)
    (by fun_prop) f.continuous.aestronglyMeasurable

/-- A `C₀` function is bounded by its norm. -/
theorem norm_apply_le_norm_c0 (f : C₀(ℝ, ℝ)) (x : ℝ) : ‖f x‖ ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact f.toBCF.norm_coe_le_norm x

private theorem integrable_c0_comp (f : C₀(ℝ, ℝ)) (t : NNReal) (x : ℝ) :
    Integrable (fun z ↦ f (x + Real.sqrt t * z)) (gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_const ‖f‖) ?_ (Filter.Eventually.of_forall fun z ↦ ?_)
  · exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact norm_apply_le_norm_c0 f _

/-- The heat semigroup maps `C₀` into itself. -/
theorem mapsC0_heatSemigroup : heatSemigroup.MapsC0 := by
  intro t f
  have hrep : kernelIntegral (heatSemigroup t) f =
      fun x ↦ ∫ z, f (x + Real.sqrt t * z) ∂(gaussianReal 0 1) :=
    funext (kernelIntegral_heatSemigroup t f)
  rw [hrep]
  constructor
  · refine continuous_of_dominated (F := fun (x z : ℝ) ↦ f (x + Real.sqrt t * z))
      (bound := fun _ ↦ ‖f‖) ?_ ?_ (integrable_const (μ := gaussianReal 0 1) ‖f‖) ?_
    · exact fun x ↦ (f.continuous.comp (by fun_prop)).aestronglyMeasurable
    · exact fun x ↦ Filter.Eventually.of_forall fun z ↦ norm_apply_le_norm_c0 f _
    · exact Filter.Eventually.of_forall fun z ↦ f.continuous.comp (by fun_prop)
  · have hcg : (Filter.cocompact ℝ).IsCountablyGenerated := by
      rw [cocompact_eq_atBot_atTop]
      infer_instance
    refine Filter.tendsto_iff_seq_tendsto.mpr fun u hu ↦ ?_
    have hlim : Filter.Tendsto
        (fun n ↦ ∫ z, f (u n + Real.sqrt t * z) ∂(gaussianReal 0 1)) atTop
        (nhds (∫ _z : ℝ, (0 : ℝ) ∂(gaussianReal 0 1))) := by
      refine tendsto_integral_of_dominated_convergence
        (F := fun (n : ℕ) (z : ℝ) ↦ f (u n + Real.sqrt t * z)) (fun _ ↦ ‖f‖)
        (fun _ ↦ (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
        (integrable_const (μ := gaussianReal 0 1) ‖f‖)
        (fun _ ↦ Filter.Eventually.of_forall fun _ ↦ norm_apply_le_norm_c0 f _)
        (Filter.Eventually.of_forall fun z ↦ ?_)
      have htranslate : Filter.Tendsto (fun y : ℝ ↦ y + Real.sqrt t * z)
          (Filter.cocompact ℝ) (Filter.cocompact ℝ) :=
        CocompactMapClass.cocompact_tendsto
          ((Homeomorph.addRight (Real.sqrt t * z)).toCocompactMap)
      exact f.zero_at_infty'.comp (htranslate.comp hu)
    rw [integral_zero] at hlim
    exact hlim

/-- A finite measure on the real line puts arbitrarily little mass far from the origin. -/
theorem exists_measure_abs_ge_lt (nu : Measure ℝ) [IsFiniteMeasure nu] {eps : ℝ}
    (heps : 0 < eps) : ∃ R : ℝ, 0 < R ∧ (nu {z : ℝ | R ≤ |z|}).toReal < eps := by
  have hmeasA : ∀ n : ℕ, NullMeasurableSet {z : ℝ | (n : ℝ) ≤ |z|} nu := fun n ↦
    ((isClosed_le continuous_const continuous_abs).measurableSet).nullMeasurableSet
  have hanti : Antitone (fun n : ℕ ↦ {z : ℝ | (n : ℝ) ≤ |z|}) := by
    intro n m hnm z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    exact le_trans (Nat.cast_le.mpr hnm) hz
  have hempty : (⋂ n : ℕ, {z : ℝ | (n : ℝ) ≤ |z|}) = (∅ : Set ℝ) := by
    refine Set.eq_empty_of_forall_notMem fun z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_gt |z|
    exact absurd (Set.mem_iInter.mp hz n) (not_le.mpr hn)
  have htend := tendsto_measure_iInter_atTop hmeasA hanti ⟨0, measure_ne_top nu _⟩
  rw [hempty, measure_empty] at htend
  have hev : ∀ᶠ n : ℕ in atTop, nu {z : ℝ | (n : ℝ) ≤ |z|} < ENNReal.ofReal eps :=
    htend.eventually_lt_const (by simpa using heps)
  obtain ⟨n, hn⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
  exact ⟨(n : ℝ), by exact_mod_cast hn.2, ENNReal.toReal_lt_of_lt_ofReal hn.1⟩

/-- The `C₀` orbit displacement of the heat semigroup is uniformly small over short times: for
every `ε > 0` there is a `δ > 0` such that the transition operator moves a `C₀` function by at
most `ε` in the uniform norm over every time shorter than `δ`. -/
theorem exists_norm_c0Operator_sub_le_heatSemigroup (f : C₀(ℝ, ℝ)) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ h : NNReal, (h : ℝ) < delta →
      ‖heatSemigroup.c0Operator mapsC0_heatSemigroup h f - f‖ ≤ eps := by
  obtain ⟨delta0, hdelta0, huc⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous f) (eps / 2) (half_pos heps)
  have hfpos : (0 : ℝ) < 4 * (‖f‖ + 1) := by positivity
  obtain ⟨R, hR, hRmeas⟩ := exists_measure_abs_ge_lt (gaussianReal 0 1)
    (eps := eps / (4 * (‖f‖ + 1))) (by positivity)
  set S : Set ℝ := {z : ℝ | R ≤ |z|} with hS
  have hSmeas : MeasurableSet S := (isClosed_le continuous_const continuous_abs).measurableSet
  set bound : ℝ → ℝ := fun z ↦ eps / 2 + 2 * ‖f‖ * S.indicator (fun _ ↦ (1 : ℝ)) z with hbound
  have hindInt : Integrable (S.indicator (fun _ ↦ (1 : ℝ))) (gaussianReal 0 1) :=
    (integrable_indicator_iff hSmeas).mpr (integrableOn_const (measure_ne_top _ _))
  have hboundInt : Integrable bound (gaussianReal 0 1) :=
    (integrable_const (μ := gaussianReal 0 1) (eps / 2)).add (hindInt.const_mul _)
  have hboundIntegral : ∫ z, bound z ∂(gaussianReal 0 1) ≤ eps := by
    rw [hbound, integral_add (integrable_const (μ := gaussianReal 0 1) (eps / 2))
      (hindInt.const_mul _), integral_const, MeasureTheory.integral_const_mul,
      integral_indicator_const (1 : ℝ) hSmeas]
    have hnorm : 0 ≤ ‖f‖ := norm_nonneg f
    have hkey : 2 * ‖f‖ * ((gaussianReal 0 1).real S) ≤ eps / 2 := by
      have hpos : (0 : ℝ) ≤ (gaussianReal 0 1).real S := measureReal_nonneg
      calc 2 * ‖f‖ * ((gaussianReal 0 1).real S)
          ≤ 2 * (‖f‖ + 1) * (eps / (4 * (‖f‖ + 1))) := by
            apply mul_le_mul _ (le_of_lt hRmeas) hpos (by positivity)
            exact mul_le_mul_of_nonneg_left (by linarith only []) (by norm_num)
        _ = eps / 2 := by field_simp; ring
    rw [probReal_univ]
    simp only [smul_eq_mul, mul_one]
    linarith only [hkey]
  refine ⟨(delta0 / R) ^ 2, by positivity, fun h hh ↦ ?_⟩
  have hsqrt : Real.sqrt h * R < delta0 := by
    have h1 : Real.sqrt h < delta0 / R := by
      have := Real.sqrt_lt_sqrt h.coe_nonneg hh
      rwa [Real.sqrt_sq (by positivity)] at this
    calc Real.sqrt h * R < (delta0 / R) * R := by
          exact mul_lt_mul_of_pos_right h1 hR
      _ = delta0 := div_mul_cancel₀ delta0 (ne_of_gt hR)
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (le_of_lt heps)).2 fun x ↦ ?_
  change ‖heatSemigroup.c0Operator mapsC0_heatSemigroup h f x - f x‖ ≤ eps
  rw [SubMarkovKernelSemigroup.c0Operator_apply, kernelIntegral_heatSemigroup]
  have hsub : (∫ z, f (x + Real.sqrt h * z) ∂(gaussianReal 0 1)) - f x =
      ∫ z, (f (x + Real.sqrt h * z) - f x) ∂(gaussianReal 0 1) := by
    rw [integral_sub (integrable_c0_comp f h x) (integrable_const (f x)), integral_const,
      probReal_univ, one_smul]
  rw [hsub]
  refine le_trans (norm_integral_le_of_norm_le hboundInt
    (Filter.Eventually.of_forall fun z ↦ ?_)) hboundIntegral
  by_cases hz : z ∈ S
  · have h1 : ‖f (x + Real.sqrt h * z) - f x‖ ≤ 2 * ‖f‖ := by
      calc ‖f (x + Real.sqrt h * z) - f x‖ ≤ ‖f (x + Real.sqrt h * z)‖ + ‖f x‖ :=
            norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (norm_apply_le_norm_c0 f _) (norm_apply_le_norm_c0 f _)
        _ = 2 * ‖f‖ := by ring
    rw [hbound]
    simp only [Set.indicator_of_mem hz, mul_one]
    linarith only [h1, heps]
  · have hdist : dist (x + Real.sqrt h * z) x < delta0 := by
      rw [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hzR : |z| < R := lt_of_not_ge (by simpa only [hS, Set.mem_ofPred_eq] using hz)
      calc Real.sqrt h * |z| ≤ Real.sqrt h * R :=
            mul_le_mul_of_nonneg_left (le_of_lt hzR) (Real.sqrt_nonneg _)
        _ < delta0 := hsqrt
    have h2 : ‖f (x + Real.sqrt h * z) - f x‖ ≤ eps / 2 := by
      rw [← dist_eq_norm]
      exact le_of_lt (huc hdist)
    rw [hbound]
    simp only [Set.indicator_of_notMem hz, mul_zero, add_zero]
    exact h2

/-- The `C₀` orbits of the heat semigroup are continuous in time. -/
theorem hasContinuousC0Orbits_heatSemigroup :
    heatSemigroup.HasContinuousC0Orbits mapsC0_heatSemigroup := by
  intro f
  rw [Metric.continuous_iff]
  intro b eps heps
  obtain ⟨delta, hdelta, hkey⟩ :=
    exists_norm_c0Operator_sub_le_heatSemigroup f (half_pos heps)
  refine ⟨delta, hdelta, fun a hab ↦ ?_⟩
  have hcontraction : ∀ c d : NNReal, c ≤ d → (d : ℝ) - (c : ℝ) < delta →
      dist (heatSemigroup.c0Operator mapsC0_heatSemigroup d f)
        (heatSemigroup.c0Operator mapsC0_heatSemigroup c f) ≤ eps / 2 := by
    intro c d hcd hlt
    have hdc : c + (d - c) = d := add_tsub_cancel_of_le hcd
    have hcoe : ((d - c : NNReal) : ℝ) < delta := by
      rw [NNReal.coe_sub hcd]
      exact hlt
    have hop : heatSemigroup.c0Operator mapsC0_heatSemigroup d f =
        heatSemigroup.c0Operator mapsC0_heatSemigroup c
          (heatSemigroup.c0Operator mapsC0_heatSemigroup (d - c) f) := by
      conv_lhs => rw [← hdc]
      rw [SubMarkovKernelSemigroup.c0Operator_add]
      rfl
    rw [dist_eq_norm, hop, ← map_sub]
    calc ‖heatSemigroup.c0Operator mapsC0_heatSemigroup c
            (heatSemigroup.c0Operator mapsC0_heatSemigroup (d - c) f - f)‖
        ≤ ‖heatSemigroup.c0Operator mapsC0_heatSemigroup c‖ *
            ‖heatSemigroup.c0Operator mapsC0_heatSemigroup (d - c) f - f‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (eps / 2) := by
          refine mul_le_mul (SubMarkovKernelSemigroup.norm_c0Operator_le _ _ c)
            (hkey _ hcoe) (norm_nonneg _) zero_le_one
      _ = eps / 2 := one_mul _
  have habs : |(a : ℝ) - (b : ℝ)| < delta := by
    rw [← NNReal.dist_eq]
    exact hab
  rcases le_total b a with hba | hab'
  · have := hcontraction b a hba (by
      rw [abs_of_nonneg (by
        have : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
        linarith only [this])] at habs
      exact habs)
    linarith only [this, heps]
  · have := hcontraction a b hab' (by
      rw [abs_sub_comm, abs_of_nonneg (by
        have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab'
        linarith only [this])] at habs
      exact habs)
    rw [dist_comm]
    linarith only [this, heps]

/-- **The heat semigroup is a Feller semigroup.** -/
theorem isFellerKernelSemigroup_heatSemigroup :
    heatSemigroup.IsFellerKernelSemigroup :=
  ⟨mapsC0_heatSemigroup, hasContinuousC0Orbits_heatSemigroup⟩

/-- The positive contractive `C₀` resolvent obtained from the heat semigroup. -/
noncomputable def heatResolvent : PositiveC0ContractiveResolvent ℝ :=
  isFellerKernelSemigroup_heatSemigroup.positiveC0ContractiveResolvent

/-- The semigroup generated by the heat resolvent is the original heat `C₀` semigroup. -/
theorem generatedSemigroup_heatResolvent :
    heatResolvent.toContractiveResolvent.generatedSemigroup =
      isFellerKernelSemigroup_heatSemigroup.c0Semigroup :=
  isFellerKernelSemigroup_heatSemigroup.generatedSemigroup_positiveC0ContractiveResolvent

end Feller

section OnePointExhaustion

/-- The explicit positive exhaustion used to metrize the one-point compactification of the real
line. -/
def heatExhaustion (x : ℝ) : ℝ :=
  1 / (1 + |x|)

/-- The heat exhaustion is `1`-Lipschitz. -/
theorem lipschitzWith_one_heatExhaustion : LipschitzWith 1 heatExhaustion := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rw [heatExhaustion, heatExhaustion, one_div, one_div,
    inv_sub_inv (by positivity) (by positivity), abs_div]
  calc
    |(1 + |y|) - (1 + |x|)| / |(1 + |x|) * (1 + |y|)|
        = |(|y| - |x|)| / |(1 + |x|) * (1 + |y|)| := by ring_nf
    _ ≤ |(|y| - |x|)| := by
      apply div_le_self (abs_nonneg _)
      rw [abs_of_nonneg (mul_nonneg (by positivity) (by positivity))]
      calc
        (1 : ℝ) = 1 * 1 := (mul_one 1).symm
        _ ≤ (1 + |x|) * (1 + |y|) :=
          mul_le_mul (le_add_of_nonneg_right (abs_nonneg x))
            (le_add_of_nonneg_right (abs_nonneg y)) zero_le_one (by positivity)
    _ ≤ |y - x| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |x - y| := abs_sub_comm y x

/-- The heat exhaustion is continuous. -/
theorem continuous_heatExhaustion : Continuous heatExhaustion :=
  lipschitzWith_one_heatExhaustion.continuous

/-- The heat exhaustion is strictly positive. -/
theorem heatExhaustion_pos (x : ℝ) : 0 < heatExhaustion x := by
  unfold heatExhaustion
  positivity

/-- The heat exhaustion is bounded above by one. -/
theorem heatExhaustion_le_one (x : ℝ) : heatExhaustion x ≤ 1 := by
  unfold heatExhaustion
  exact (div_le_one₀ (by positivity)).2 (le_add_of_nonneg_right (abs_nonneg x))

/-- Every positive superlevel set of the heat exhaustion is compact. -/
theorem isCompact_heatExhaustion_superlevel (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    IsCompact {x : ℝ | epsilon ≤ heatExhaustion x} := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc : IsCompact (Set.Icc (-epsilon⁻¹) epsilon⁻¹))
    (isClosed_le continuous_const continuous_heatExhaustion)
  intro x hx
  have hmul : epsilon * (1 + |x|) ≤ 1 := by
    change epsilon ≤ 1 / (1 + |x|) at hx
    exact (le_div_iff₀ (by positivity : 0 < 1 + |x|)).mp hx
  have habs : |x| ≤ epsilon⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hepsilon]
    calc
      |x| * epsilon ≤ (1 + |x|) * epsilon :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hepsilon.le
      _ = epsilon * (1 + |x|) := mul_comm _ _
      _ ≤ 1 := hmul
  exact (abs_le.mp habs)

end OnePointExhaustion

section Moments

/-- The fourth moment of the standard Gaussian is finite. -/
theorem lintegral_enorm_pow_gaussianReal_lt_top :
    ∫⁻ z, ‖z‖ₑ ^ (4 : ℕ) ∂(gaussianReal 0 1) < ⊤ := by
  have hmem : MemLp id ((4 : ℝ≥0) : ℝ≥0∞) (gaussianReal 0 1) := memLp_id_gaussianReal 4
  have hfin := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := ((4 : ℝ≥0) : ℝ≥0∞)) (f := (id : ℝ → ℝ)) (by simp) (by simp) hmem.eLpNorm_lt_top
  have hp : (((4 : ℝ≥0) : ℝ≥0∞)).toReal = (4 : ℝ) := by simp
  rw [hp] at hfin
  simpa only [id_eq, ENNReal.rpow_ofNat] using hfin

/-- The fourth moment of the standard Gaussian, as a nonnegative real number. -/
def gaussianFourthMoment : NNReal :=
  (∫⁻ z, ‖z‖ₑ ^ (4 : ℕ) ∂(gaussianReal 0 1)).toNNReal

@[simp]
theorem coe_gaussianFourthMoment :
    (gaussianFourthMoment : ℝ≥0∞) = ∫⁻ z, ‖z‖ₑ ^ (4 : ℕ) ∂(gaussianReal 0 1) :=
  ENNReal.coe_toNNReal (ne_of_lt lintegral_enorm_pow_gaussianReal_lt_top)

private theorem enorm_sqrt_sq (h : NNReal) :
    ‖Real.sqrt (h : ℝ)‖ₑ ^ (2 : ℕ) = (h : ℝ≥0∞) := by
  rw [← enorm_pow, Real.sq_sqrt h.coe_nonneg, Real.enorm_of_nonneg h.coe_nonneg,
    ENNReal.ofReal_coe_nnreal]

/-- **The heat semigroup satisfies the Kolmogorov moment criterion** with exponents `p = 4` and
`q = 2` and the fourth moment of the standard Gaussian as constant: the fourth moment of the
displacement over a time step `h` is exactly `h ^ 2` times that constant. -/
theorem hasKolmogorovMoments_heatSemigroup :
    heatSemigroup.HasKolmogorovMoments 4 2 gaussianFourthMoment := by
  refine ⟨by norm_num, by norm_num, fun h y ↦ ?_⟩
  have hmeasf : Measurable (fun w : ℝ ↦ edist w y ^ (4 : ℝ)) :=
    (measurable_edist_left (x := y)).pow_const 4
  have hmeasg : Measurable (fun z : ℝ ↦ y + Real.sqrt (h : ℝ) * z) := by fun_prop
  rw [heatSemigroup_apply, gaussianReal_eq_map_add_sqrt_mul, lintegral_map hmeasf hmeasg]
  have hint : ∀ z : ℝ, edist (y + Real.sqrt (h : ℝ) * z) y ^ (4 : ℝ) =
      ‖Real.sqrt (h : ℝ)‖ₑ ^ (4 : ℕ) * ‖z‖ₑ ^ (4 : ℕ) := by
    intro z
    rw [ENNReal.rpow_ofNat, edist_eq_enorm_sub, add_sub_cancel_left, enorm_mul, mul_pow]
  simp_rw [hint]
  rw [lintegral_const_mul _ (by fun_prop), coe_gaussianFourthMoment, ENNReal.rpow_ofNat,
    show (4 : ℕ) = 2 * 2 from rfl, pow_mul, enorm_sqrt_sq]
  exact le_of_eq (mul_comm _ _)

end Moments

section Process

/-- The heat semigroup is Kolmogorov regular, by its moment bound. -/
theorem kolmogorovRegular_heatSemigroup :
    heatSemigroup.KolmogorovRegular isConservative_heatSemigroup :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    isConservative_heatSemigroup hasKolmogorovMoments_heatSemigroup

/-- **The main theorem, applied to the heat semigroup.**  There is exactly one Markov kernel from
the line to continuous paths whose finite-dimensional distributions are the Gaussian transition
laws of the heat semigroup. -/
theorem existsUnique_continuousProcess_heatSemigroup :
    ∃! Q : Kernel ℝ (ContinuousPath ℝ), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel heatSemigroup I :=
  isFellerKernelSemigroup_heatSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments
    heatSemigroup isConservative_heatSemigroup hasKolmogorovMoments_heatSemigroup

/-- **Brownian motion on the line**, as a Markov kernel from the starting point to continuous
paths: the continuous-path process of the heat semigroup. -/
def brownianMotion : Kernel ℝ (ContinuousPath ℝ) :=
  SubMarkovKernelSemigroup.IsConservative.continuousProcess heatSemigroup
    isConservative_heatSemigroup

instance isMarkovKernel_brownianMotion : IsMarkovKernel brownianMotion := by
  unfold brownianMotion
  infer_instance

/-- Every one-time marginal of Brownian motion started at `x` is the Gaussian law with mean `x`
and variance the elapsed time. -/
theorem brownianMotion_map_eval (t : NNReal) (x : ℝ) :
    (brownianMotion x).map (fun omega ↦ omega t) = gaussianReal x t := by
  have hmeas : Measurable (fun omega : ContinuousPath ℝ ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t
  rw [brownianMotion, ← Kernel.map_apply _ hmeas,
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_eval_nnreal
      heatSemigroup isConservative_heatSemigroup isFellerKernelSemigroup_heatSemigroup
      kolmogorovRegular_heatSemigroup t, heatSemigroup_apply]

/-- Every finite-dimensional distribution of Brownian motion is the corresponding finite-set
kernel of the heat semigroup. -/
theorem brownianMotion_map_finsetEvaluation (I : Finset NNReal) :
    brownianMotion.map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel heatSemigroup I :=
  isFellerKernelSemigroup_heatSemigroup.continuousProcess_map_finiteEvaluation heatSemigroup
    isConservative_heatSemigroup kolmogorovRegular_heatSemigroup I

/-- Brownian motion is the only Markov kernel into continuous paths with the finite-dimensional
distributions of the heat semigroup. -/
theorem eq_brownianMotion_of_map_finsetEvaluation (Q : Kernel ℝ (ContinuousPath ℝ))
    [IsFiniteKernel Q]
    (hQ : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel heatSemigroup I) :
    Q = brownianMotion :=
  SubMarkovKernelSemigroup.IsConservative.eq_continuousProcess_of_map_finiteEvaluation
    heatSemigroup isConservative_heatSemigroup kolmogorovRegular_heatSemigroup Q hQ

end Process

end

end MarkovProcess

end PortComputability
