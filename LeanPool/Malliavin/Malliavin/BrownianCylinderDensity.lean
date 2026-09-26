/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.PastCylinderDensity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Polynomial density for Brownian cylinders

This file proves that powers of finite linear combinations of Brownian coordinates span the
ambient real `L²` space whenever the Brownian process generates the ambient measurable space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open NormedSpace
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin

variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

section GaussianPolynomial

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (μ : Measure E) [IsGaussian μ]

omit [CompleteSpace E] [SecondCountableTopology E] in
/-- Every natural power of a continuous linear functional on a Gaussian space belongs to
`L²`. -/
theorem memLp_two_dual_pow (L : StrongDual ℝ E) (n : ℕ) :
    MemLp (fun x ↦ L x ^ n) 2 μ := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have hL : MemLp L (2 * n : ℕ) μ :=
    IsGaussian.memLp_dual μ L (2 * n : ℕ) (ENNReal.natCast_ne_top (2 * n))
  convert hL.integrable_norm_pow' using 1
  funext x
  simp only [Real.norm_eq_abs]
  have hnonneg : 0 ≤ L x ^ (2 * n) := by
    rw [mul_comm, pow_mul]
    positivity
  rw [← abs_pow, abs_of_nonneg hnonneg]
  ring

/-- A natural power of a continuous linear functional, represented in Gaussian `L²`. -/
def gaussianLinearPowerLp (L : StrongDual ℝ E) (n : ℕ) : Lp ℝ 2 μ :=
  (memLp_two_dual_pow μ L n).toLp fun x ↦ L x ^ n

/-- The algebraic span of powers of continuous linear functionals on a Gaussian space. -/
def gaussianPolynomialSpan : Submodule ℝ (Lp ℝ 2 μ) :=
  Submodule.span ℝ (Set.range fun a : StrongDual ℝ E × ℕ ↦
    gaussianLinearPowerLp μ a.1 a.2)

omit [CompleteSpace E] [SecondCountableTopology E] in
private theorem integrable_exp_mul_dual (L : StrongDual ℝ E) (t : ℝ) :
    Integrable (fun x ↦ Real.exp (t * L x)) μ := by
  have h := integrable_exp_mul_gaussianReal
    (μ := μ[L]) (v := Var[L; μ].toNNReal) t
  rw [← IsGaussian.map_eq_gaussianReal (μ := μ) L] at h
  exact h.comp_measurable L.measurable

omit [CompleteSpace E] [SecondCountableTopology E] in
private theorem memLp_two_exp_abs_dual (L : StrongDual ℝ E) :
    MemLp (fun x ↦ Real.exp |L x|) 2 μ := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have hsum := (integrable_exp_mul_dual μ L 2).add
    (integrable_exp_mul_dual μ L (-2))
  refine hsum.mono (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos (Real.exp_pos _))]
  calc
    Real.exp |L x| ^ 2 = Real.exp |2 * L x| := by
      rw [← Real.exp_nat_mul]
      congr 2
      simp [abs_mul]
    _ ≤ Real.exp (2 * L x) + Real.exp (-(2 * L x)) := Real.exp_abs_le _
    _ = ‖((fun x ↦ Real.exp (2 * L x)) +
        fun x ↦ Real.exp (-2 * L x)) x‖ := by
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      congr 1
      ring_nf

omit [CompleteSpace E] [SecondCountableTopology E] in
private theorem integrable_abs_coe_mul_exp_abs_dual
    (g : Lp ℝ 2 μ) (L : StrongDual ℝ E) :
    Integrable (fun x ↦ |g x| * Real.exp |L x|) μ := by
  have hmul := (Lp.memLp g).integrable_mul (memLp_two_exp_abs_dual μ L)
  have hnorm := hmul.norm
  simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)] using hnorm

/-- Powers of continuous linear functionals are total in Gaussian `L²`. -/
theorem dense_gaussianPolynomialSpan :
    Dense (gaussianPolynomialSpan μ : Set (Lp ℝ 2 μ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have key (L : StrongDual ℝ E) (n : ℕ) :
      ∫ x, L x ^ n * g x ∂μ = 0 := by
    have hinner := hg (gaussianLinearPowerLp μ L n)
      (Submodule.subset_span ⟨(L, n), rfl⟩)
    rw [L2.inner_def] at hinner
    rw [← hinner]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (memLp_two_dual_pow μ L n)] with x hx
    have hx' : gaussianLinearPowerLp μ L n x = L x ^ n := hx
    rw [hx']
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hchar (L : StrongDual ℝ E) :
      ∫ x, Complex.exp (L x * Complex.I) * (g x : ℂ) ∂μ = 0 := by
    let F : ℕ → E → ℂ := fun n x ↦
      ((L x : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ) * (g x : ℂ)
    let bound : ℕ → E → ℝ := fun n x ↦
      |g x| * (|L x| ^ n / Nat.factorial n)
    have hbound_sum (x : E) :
        HasSum (fun n ↦ bound n x) (|g x| * Real.exp |L x|) := by
      simpa only [bound, mul_div_assoc, ← Real.exp_eq_exp_ℝ] using
        (expSeries_div_hasSum_exp |L x|).mul_left |g x|
    have hsum : HasSum (fun n ↦ ∫ x, F n x ∂μ)
        (∫ x, Complex.exp ((L x : ℂ) * Complex.I) * (g x : ℂ) ∂μ) :=
      hasSum_integral_of_dominated_convergence (F := F)
      (f := fun x ↦ Complex.exp ((L x : ℂ) * Complex.I) * (g x : ℂ)) bound
      (fun n ↦ by dsimp only [F]; fun_prop)
      (fun n ↦ by
        filter_upwards with x
        dsimp only [F, bound]
        rw [norm_mul, norm_div, norm_pow]
        simp only [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
          norm_natCast, Real.norm_eq_abs]
        rw [mul_comm])
      (Filter.Eventually.of_forall fun x ↦ (hbound_sum x).summable)
      (by
        convert integrable_abs_coe_mul_exp_abs_dual μ g L using 1
        funext x
        exact (hbound_sum x).tsum_eq)
      (Filter.Eventually.of_forall fun x ↦ by
        dsimp only [F]
        simpa only [← Complex.exp_eq_exp_ℂ] using
          (expSeries_div_hasSum_exp ((L x : ℂ) * Complex.I)).mul_right (g x : ℂ))
    have hterm (n : ℕ) : ∫ x, F n x ∂μ = 0 := by
      calc
        ∫ x, F n x ∂μ =
            (Complex.I ^ n / (Nat.factorial n : ℂ)) *
              ∫ x, ((L x ^ n * g x : ℝ) : ℂ) ∂μ := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          dsimp only [F]
          push_cast
          rw [mul_pow]
          ring
        _ = (Complex.I ^ n / (Nat.factorial n : ℂ)) *
              ((∫ x, L x ^ n * g x ∂μ : ℝ) : ℂ) := by
          rw [integral_complex_ofReal]
        _ = 0 := by rw [key L n]; simp
    rw [← hsum.tsum_eq]
    simp only [hterm, tsum_zero]
  have hg_int : Integrable (g : E → ℝ) μ :=
    (Lp.memLp g).integrable one_le_two
  have hcos (L : StrongDual ℝ E) :
      ∫ x, Real.cos (L x) * g x ∂μ = 0 := by
    have hc : Integrable (fun x ↦ Real.cos (L x) * g x) μ :=
      hg_int.bdd_mul (by fun_prop)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (L x))
    have hs : Integrable (fun x ↦ Real.sin (L x) * g x) μ :=
      hg_int.bdd_mul (by fun_prop)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (L x))
    have hz := hchar L
    have heq : ∀ x, Complex.exp (L x * Complex.I) * (g x : ℂ) =
        ((Real.cos (L x) * g x : ℝ) : ℂ) +
          ((Real.sin (L x) * g x : ℝ) : ℂ) * Complex.I := by
      intro x
      rw [Complex.exp_mul_I]
      push_cast
      ring
    simp_rw [heq] at hz
    rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal] at hz
    have hre := congrArg Complex.re hz
    simpa using hre
  have hsin (L : StrongDual ℝ E) :
      ∫ x, Real.sin (L x) * g x ∂μ = 0 := by
    have hc : Integrable (fun x ↦ Real.cos (L x) * g x) μ :=
      hg_int.bdd_mul (by fun_prop)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (L x))
    have hs : Integrable (fun x ↦ Real.sin (L x) * g x) μ :=
      hg_int.bdd_mul (by fun_prop)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (L x))
    have hz := hchar L
    have heq : ∀ x, Complex.exp (L x * Complex.I) * (g x : ℂ) =
        ((Real.cos (L x) * g x : ℝ) : ℂ) +
          ((Real.sin (L x) * g x : ℝ) : ℂ) * Complex.I := by
      intro x
      rw [Complex.exp_mul_I]
      push_cast
      ring
    simp_rw [heq] at hz
    rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal] at hz
    have him := congrArg Complex.im hz
    simpa using him
  exact Lp.eq_zero_iff_ae_eq_zero.mpr
    (ae_eq_zero_of_forall_integral_cos_sin μ hg_int hcos hsin)

end GaussianPolynomial

section BrownianPolynomial

variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- A natural power of a finite Brownian step sum belongs to `L²(P)`. -/
theorem memLp_two_stepSum_pow (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    MemLp (fun w ↦ stepSum B v w ^ n) 2 P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [memLp_two_iff_integrable_sq
    ((hasGaussianLaw_stepSum hB v).aemeasurable.pow_const n).aestronglyMeasurable]
  have hX : MemLp (stepSum B v) (2 * n : ℕ) P :=
    (hasGaussianLaw_stepSum hB v).memLp (ENNReal.natCast_ne_top (2 * n))
  convert hX.integrable_norm_pow' using 1
  funext w
  simp only [Real.norm_eq_abs]
  have hnonneg : 0 ≤ stepSum B v w ^ (2 * n) := by
    rw [mul_comm, pow_mul]
    positivity
  rw [← abs_pow, abs_of_nonneg hnonneg]
  ring

/-- A polynomial generator obtained by taking a power of a finite Brownian step sum. -/
def brownianStepPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) : RandomL2 P :=
  (memLp_two_stepSum_pow hB v n).toLp fun w ↦ stepSum B v w ^ n

/-- The algebraic space of Brownian polynomial cylinders. -/
def brownianPolynomialSpan (hB : IsPreBrownianReal B P) :
    Submodule ℝ (RandomL2 P) :=
  Submodule.span ℝ (Set.range fun a : (ℝ≥0 →₀ ℝ) × ℕ ↦
    brownianStepPowerLp hB a.1 a.2)

/-- The full Brownian path viewed as a product-valued random variable. -/
def brownianProcess (B : ℝ≥0 → W → ℝ) : W → (ℝ≥0 → ℝ) :=
  fun w t ↦ B t w

/-- Pullbacks of finite-coordinate measurable cylinders along the Brownian path. -/
def brownianCylinderEvents (B : ℝ≥0 → W → ℝ) : Set (Set W) :=
  Set.preimage (brownianProcess B) '' measurableCylinders (fun _ : ℝ≥0 ↦ ℝ)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
theorem isSetAlgebra_brownianCylinderEvents (B : ℝ≥0 → W → ℝ) :
    IsSetAlgebra (brownianCylinderEvents B) where
  empty_mem := ⟨∅, empty_mem_measurableCylinders _, Set.preimage_empty⟩
  compl_mem := by
    rintro s ⟨C, hC, rfl⟩
    exact ⟨Cᶜ, compl_mem_measurableCylinders hC, Set.preimage_compl⟩
  union_mem := by
    rintro s t ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩
    exact ⟨C ∪ D, union_mem_measurableCylinders hC hD, Set.preimage_union⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Brownian cylinders generate the ambient measurable space under `IsWienerGenerated`. -/
theorem ambient_eq_generateFrom_brownianCylinderEvents
    (hgen : IsWienerGenerated B) :
    ‹MeasurableSpace W› = MeasurableSpace.generateFrom (brownianCylinderEvents B) := by
  rw [← hgen]
  change (⨆ t : ℝ≥0, MeasurableSpace.comap (B t) (borel ℝ)) = _
  rw [← MeasurableSpace.comap_process_pi,
    ← generateFrom_measurableCylinders, MeasurableSpace.comap_generateFrom]
  rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Brownian cylinders are measurable when the process generates the ambient sigma-algebra. -/
theorem measurableSet_brownianCylinderEvents (hgen : IsWienerGenerated B)
    {s : Set W} (hs : s ∈ brownianCylinderEvents B) : MeasurableSet s := by
  rw [ambient_eq_generateFrom_brownianCylinderEvents hgen]
  exact MeasurableSpace.measurableSet_generateFrom hs

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Brownian cylinders are measure-dense in a Brownian-generated probability space. -/
theorem measureDense_brownianCylinderEvents
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B) :
    P.MeasureDense (brownianCylinderEvents B) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
    (μ := P) (isSetAlgebra_brownianCylinderEvents B)
    (ambient_eq_generateFrom_brownianCylinderEvents hgen)

/-- Coefficients of a finite-dimensional linear functional, extended by zero to all times. -/
private def brownianDualCoefficients (I : Finset ℝ≥0)
    (K : StrongDual ℝ (I → ℝ)) : ℝ≥0 →₀ ℝ :=
  (Finsupp.equivFunOnFinite.symm fun i ↦ K (Pi.single i 1)).embDomain
    (Function.Embedding.subtype fun t ↦ t ∈ I)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    [IsGaussian P] in
private theorem stepSum_brownianDualCoefficients (I : Finset ℝ≥0)
    (K : StrongDual ℝ (I → ℝ)) (w : W) :
    stepSum B (brownianDualCoefficients I K) w = K (fun i ↦ B i w) := by
  classical
  rw [show K (fun i ↦ B i w) =
      K (∑ i : I, B i w • (Pi.single i (1 : ℝ) : I → ℝ)) by
    congr 1
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_ite_eq]]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  simp only [stepSum, brownianDualCoefficients, Finsupp.sum_embDomain]
  rw [Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)]
  apply Finset.sum_congr rfl
  intro i _hi
  change K (Pi.single i 1) * B i w = B i w * K (Pi.single i 1)
  ring

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The indicator of one finite Brownian cylinder is approximable by Brownian polynomials. -/
theorem indicator_brownianCylinder_mem_closure
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B)
    {s : Set W} (hs : s ∈ brownianCylinderEvents B) :
    indicatorConstLp 2 (measurableSet_brownianCylinderEvents hgen hs)
        (measure_ne_top P s) (1 : ℝ) ∈
      (brownianPolynomialSpan hB).topologicalClosure := by
  rcases hs with ⟨C, hC, rfl⟩
  rcases (mem_measurableCylinders C).mp hC with ⟨I, A, hA, rfl⟩
  let L : W → (I → ℝ) := fun w i ↦ B i w
  have hL : Measurable L := by
    apply Measurable.of_eval
    intro i
    exact hgen.measurable i
  let ν : Measure (I → ℝ) := P.map L
  let _ : IsGaussian ν := by
    dsimp only [ν, L]
    exact (hB.isGaussianProcess.hasGaussianLaw I).isGaussian_map
  let hmp : MeasurePreserving L P ν := hL.measurePreserving P
  let Y : Lp ℝ 2 ν :=
    indicatorConstLp 2 hA (measure_ne_top ν A) (1 : ℝ)
  have hset : brownianProcess B ⁻¹' cylinder I A = L ⁻¹' A := by
    ext w
    simp only [Set.mem_preimage, mem_cylinder, Finset.restrict_def,
      brownianProcess, L]
  change indicatorConstLp 2
      (measurableSet_brownianCylinderEvents hgen
        ⟨cylinder I A, hC, rfl⟩)
      (measure_ne_top P (brownianProcess B ⁻¹' cylinder I A)) (1 : ℝ) ∈
    closure (brownianPolynomialSpan hB : Set (RandomL2 P))
  refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  have hY : Y ∈ closure (gaussianPolynomialSpan ν : Set (Lp ℝ 2 ν)) :=
    dense_gaussianPolynomialSpan ν Y
  rcases Metric.mem_closure_iff.mp hY ε hε with ⟨Z, hZ, hdist⟩
  let pull : Lp ℝ 2 ν →ₗ[ℝ] RandomL2 P :=
    Lp.compMeasurePreservingₗ ℝ L hmp
  have hpull (K : StrongDual ℝ (I → ℝ)) (n : ℕ) :
      pull (gaussianLinearPowerLp ν K n) =
        brownianStepPowerLp hB (brownianDualCoefficients I K) n := by
    unfold pull gaussianLinearPowerLp brownianStepPowerLp
    change Lp.compMeasurePreserving L hmp
        ((memLp_two_dual_pow ν K n).toLp fun x ↦ K x ^ n) = _
    rw [Lp.toLp_compMeasurePreserving]
    apply MemLp.toLp_congr
    filter_upwards with w
    simp only [Function.comp_apply, stepSum_brownianDualCoefficients]
    rfl
  have hpull_mem {Z : Lp ℝ 2 ν} (hZ : Z ∈ gaussianPolynomialSpan ν) :
      pull Z ∈ brownianPolynomialSpan hB := by
    induction hZ using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨⟨K, n⟩, rfl⟩ := hz
        rw [hpull K n]
        exact Submodule.subset_span
          ⟨(brownianDualCoefficients I K, n), rfl⟩
    | zero => exact (brownianPolynomialSpan hB).zero_mem
    | add x y _hx _hy hx hy =>
        rw [map_add]
        exact (brownianPolynomialSpan hB).add_mem hx hy
    | smul c x _hx hx =>
        rw [map_smul]
        exact (brownianPolynomialSpan hB).smul_mem c hx
  refine ⟨pull Z, hpull_mem hZ, ?_⟩
  have hI : indicatorConstLp 2
      (measurableSet_brownianCylinderEvents hgen
        ⟨cylinder I A, hC, rfl⟩)
      (measure_ne_top P (brownianProcess B ⁻¹' cylinder I A)) (1 : ℝ) =
      Lp.compMeasurePreserving L hmp Y := by
    rw [Lp.indicatorConstLp_compMeasurePreserving]
    congr 1
  rw [hI]
  change dist (Lp.compMeasurePreserving L hmp Y)
      (Lp.compMeasurePreserving L hmp Z) < ε
  rw [(Lp.isometry_compMeasurePreserving hmp).dist_eq]
  exact hdist

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- If the Brownian coordinates generate the ambient measurable space, finite Brownian
polynomials are dense in ambient `L²(P)`. -/
theorem dense_brownianPolynomialSpan
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B) :
    Dense (brownianPolynomialSpan hB : Set (RandomL2 P)) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let _ : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let K := brownianPolynomialSpan hB
  have hMD := measureDense_brownianCylinderEvents hB hgen
  have hone {s : Set W} (hs : MeasurableSet s) (hPs : P s ≠ ∞) :
      indicatorConstLp 2 hs hPs (1 : ℝ) ∈ K.topologicalClosure := by
    have happ := Measure.MeasureDense.indicatorConstLp_subset_closure
      (X := W) (E := ℝ) (μ := P) (𝒜 := brownianCylinderEvents B)
      2 hMD (1 : ℝ) ⟨s, hs, hPs, rfl⟩
    apply (closure_minimal _ K.isClosed_topologicalClosure) happ
    rintro y ⟨t, ht, hPt, rfl⟩
    exact indicator_brownianCylinder_mem_closure hB hgen ht
  have hall : ∀ f : RandomL2 P, f ∈ K.topologicalClosure := by
    refine @Lp.induction W ℝ _ _ 2 P _ (by norm_num)
      (fun f ↦ f ∈ K.topologicalClosure) ?_ ?_ K.isClosed_topologicalClosure
    · intro c s hs hPs
      change indicatorConstLp 2 hs hPs.ne c ∈ K.topologicalClosure
      have heq : indicatorConstLp 2 hs hPs.ne c =
          c • indicatorConstLp 2 hs hPs.ne (1 : ℝ) := by
        ext1
        grw [Lp.coeFn_smul, indicatorConstLp_coeFn, indicatorConstLp_coeFn]
        filter_upwards [] with x
        by_cases hx : x ∈ s <;> simp [hx]
      rw [heq]
      exact K.topologicalClosure.smul_mem c (hone hs hPs.ne)
    · intro f g _hf _hg _hdisjoint hfm hgm
      exact K.topologicalClosure.add_mem hfm hgm
  rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
  intro f _hf
  exact hall f

end BrownianPolynomial

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
