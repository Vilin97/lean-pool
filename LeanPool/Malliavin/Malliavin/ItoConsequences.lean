/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.ItoConstruction

/-!
# Consequences of the constructed Brownian Itô integral

The construction-level natural-filtration Itô integral agrees with the first-order Wiener
integral on every deterministic square-integrable time integrand. In particular it integrates
`1_(a,b]` to `B_b - B_a` and `1_(0,t]` to `B_t`.

The deterministic integrals inherit their centered Gaussian laws from the Wiener integral. The
global Itô inner-product identity also computes covariance of an arbitrary predictable integral
with every deterministic Wiener integral and Brownian coordinate.

This file also isolates the precise remaining martingale-representation input. The usual
terminal-value representation is equivalent to surjectivity of the constructed centered Itô
isometry. Under that hypothesis, predictable processes and centered terminal random variables
are linearly isometrically equivalent.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-! ## Deterministic restriction -/

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The construction-level terminal value with constant adapted coefficient `1` is the
corresponding Brownian increment. -/
theorem elementaryBrownianValue_adaptedOne
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) :
    elementaryBrownianValue hB hsm hnat hab (adaptedOne (P := P) 𝓅 a) =
      brownianLp hB b - brownianLp hB a := by
  apply Lp.ext
  have hOne : (adaptedOne (P := P) 𝓅 a : W → ℝ) =ᵐ[P]
      fun _ ↦ (1 : ℝ) := by
    change (Lp.const 2 P (1 : ℝ) : W → ℝ) =ᵐ[P] fun _ ↦ (1 : ℝ)
    exact Lp.coeFn_const 2 P (1 : ℝ)
  filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat hab
      (adaptedOne (P := P) 𝓅 a), hOne,
    Lp.coeFn_sub (brownianLp hB b) (brownianLp hB a),
    coeFn_brownianLp hB b, coeFn_brownianLp hB a]
    with w hvalue hone hsub hb ha
  rw [hvalue, hone, hsub]
  simp only [Pi.sub_apply]
  rw [hb, ha]
  simp only [one_mul]

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- At initial time zero, the construction-level constant-coefficient elementary value is the
Brownian coordinate itself. -/
theorem elementaryBrownianValue_adaptedOne_zero
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (t : ℝ≥0) :
    elementaryBrownianValue hB hsm hnat (zero_le : (0 : ℝ≥0) ≤ t)
        (adaptedOne (P := P) 𝓅 0) = brownianLp hB t := by
  rw [elementaryBrownianValue_adaptedOne, brownianLp_zero, sub_zero]

/-- Restriction of the constructed natural-filtration Itô integral to deterministic predictable
processes. -/
noncomputable def naturalItoDeterministicIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →L[ℝ] RandomL2 P :=
  (naturalItoIntegral hB hsm hnat).comp
    (deterministicPredictableEmbedding 𝓅).toContinuousLinearMap

omit [CompleteSpace W] [BorelSpace W] in
/-- Evaluation of the deterministic restriction is composition with the deterministic
predictable embedding. -/
theorem naturalItoDeterministicIntegral_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    naturalItoDeterministicIntegral hB hsm hnat f =
      naturalItoIntegral hB hsm hnat (deterministicPredictableEmbedding 𝓅 f) :=
  rfl

omit [CompleteSpace W] [BorelSpace W] in
/-- On an initial interval indicator, the deterministic restriction is the Brownian
coordinate. -/
theorem naturalItoDeterministicIntegral_intervalIndicator
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (t : ℝ≥0) :
    naturalItoDeterministicIntegral hB hsm hnat (intervalIndicator t) =
      brownianLp hB t := by
  rw [naturalItoDeterministicIntegral_apply,
    ← elementaryPredictable_adaptedOne]
  rw [naturalItoIntegral_elementaryPredictable hB hsm hnat
    (zero_le : (0 : ℝ≥0) ≤ t) (adaptedOne (P := P) 𝓅 0)]
  exact elementaryBrownianValue_adaptedOne_zero hB hsm hnat t

omit [CompleteSpace W] [BorelSpace W] in
/-- The deterministic restriction of the constructed Itô integral is exactly the genuine Wiener
integral on all of deterministic `L²`. -/
theorem naturalItoDeterministicIntegral_eq_wienerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    naturalItoDeterministicIntegral hB hsm hnat = wienerIntegral hB := by
  apply ContinuousLinearMap.ext_on dense_span_intervalIndicator
  intro f hf
  obtain ⟨t, rfl⟩ := hf
  rw [naturalItoDeterministicIntegral_intervalIndicator,
    wienerIntegral_intervalIndicator]

omit [CompleteSpace W] [BorelSpace W] in
/-- The deterministic restriction preserves the `L²` norm. -/
theorem norm_naturalItoDeterministicIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖naturalItoDeterministicIntegral hB hsm hnat f‖ = ‖f‖ := by
  rw [naturalItoDeterministicIntegral_eq_wienerIntegral,
    norm_wienerIntegral]

/-- The deterministic restriction bundled as a linear isometry. -/
noncomputable def naturalItoDeterministicIntegralIsometry
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →ₗᵢ[ℝ] RandomL2 P where
  toLinearMap := (naturalItoDeterministicIntegral hB hsm hnat).toLinearMap
  norm_map' := norm_naturalItoDeterministicIntegral hB hsm hnat

omit [CompleteSpace W] [BorelSpace W] in
/-- The range of the deterministic restriction is precisely the Gaussian first chaos. -/
theorem range_naturalItoDeterministicIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    LinearMap.range (naturalItoDeterministicIntegral hB hsm hnat).toLinearMap =
      firstChaos hB := by
  rw [naturalItoDeterministicIntegral_eq_wienerIntegral]
  exact range_wienerIntegral hB

omit [CompleteSpace W] [BorelSpace W] in
/-- The constructed Itô integral agrees with the Wiener integral on every deterministic
square-integrable time integrand. -/
theorem naturalItoIntegral_deterministic
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    naturalItoIntegral hB hsm hnat (deterministicPredictableEmbedding 𝓅 f) =
      wienerIntegral hB f := by
  rw [← naturalItoDeterministicIntegral_apply,
    naturalItoDeterministicIntegral_eq_wienerIntegral]

omit [CompleteSpace W] [BorelSpace W] in
/-- On the deterministic indicator of `(a,b]`, the constructed Itô integral is the Brownian
increment `B_b - B_a` in `L²(P)`. -/
theorem naturalItoIntegral_deterministic_Ioc
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) :
    naturalItoIntegral hB hsm hnat (deterministicPredictableEmbedding 𝓅
      (indicatorConstLp 2 measurableSet_Ioc
        (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ))) =
      brownianLp hB b - brownianLp hB a := by
  rw [naturalItoIntegral_deterministic,
    wienerIntegral_indicatorConstLp_Ioc hB hab]

omit [CompleteSpace W] [BorelSpace W] in
/-- On `1_(0,t]`, the constructed Itô integral is the Brownian coordinate `B_t` in `L²(P)`. -/
theorem naturalItoIntegral_deterministic_intervalIndicator
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (t : ℝ≥0) :
    naturalItoIntegral hB hsm hnat
        (deterministicPredictableEmbedding 𝓅 (intervalIndicator t)) =
      brownianLp hB t := by
  rw [naturalItoIntegral_deterministic, wienerIntegral_intervalIndicator]

omit [CompleteSpace W] [BorelSpace W] in
/-- The preceding `L²(P)` identity has the designated Brownian coordinate as a representative. -/
theorem naturalItoIntegral_deterministic_intervalIndicator_ae_eq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (t : ℝ≥0) :
    (naturalItoIntegral hB hsm hnat
      (deterministicPredictableEmbedding 𝓅 (intervalIndicator t)) : W → ℝ) =ᵐ[P]
        B t := by
  rw [naturalItoIntegral_deterministic_intervalIndicator]
  exact coeFn_brownianLp hB t

omit [CompleteSpace W] [BorelSpace W] in
/-- The constructed integral of every deterministic integrand has a Gaussian law. -/
theorem hasGaussianLaw_naturalItoIntegral_deterministic
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    HasGaussianLaw
      (naturalItoIntegral hB hsm hnat
        (deterministicPredictableEmbedding 𝓅 f) : W → ℝ) P := by
  rw [naturalItoIntegral_deterministic]
  exact hasGaussianLaw_wienerIntegral hB f

omit [CompleteSpace W] [BorelSpace W] in
/-- The law is the centered Gaussian whose variance is the deterministic integrand's squared
`L²` norm. -/
theorem map_naturalItoIntegral_deterministic_eq_gaussianReal
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    P.map (naturalItoIntegral hB hsm hnat
      (deterministicPredictableEmbedding 𝓅 f)) =
        gaussianReal 0 (‖f‖₊ ^ 2) := by
  rw [naturalItoIntegral_deterministic,
    map_wienerIntegral_eq_gaussianReal]

omit [CompleteSpace W] [BorelSpace W] in
/-- The covariance with a deterministic Wiener integral is the predictable-space inner product
against the deterministic embedding. -/
theorem inner_naturalItoIntegral_wienerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓅 P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    inner ℝ (naturalItoIntegral hB hsm hnat U) (wienerIntegral hB f) =
      inner ℝ U (deterministicPredictableEmbedding 𝓅 f) := by
  rw [← naturalItoIntegral_deterministic hB hsm hnat f]
  exact inner_naturalItoIntegral hB hsm hnat U _

omit [CompleteSpace W] [BorelSpace W] in
/-- In particular, covariance with `B_t` is the predictable inner product against
`1_(0,t]`. -/
theorem inner_naturalItoIntegral_brownianLp
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓅 P) (t : ℝ≥0) :
    inner ℝ (naturalItoIntegral hB hsm hnat U) (brownianLp hB t) =
      inner ℝ U
        (deterministicPredictableEmbedding 𝓅 (intervalIndicator t)) := by
  rw [← wienerIntegral_intervalIndicator hB t]
  exact inner_naturalItoIntegral_wienerIntegral hB hsm hnat U (intervalIndicator t)

/-! ## Martingale representation as surjectivity -/

/-- The martingale-representation property for the constructed natural Itô integral. -/
def NaturalMartingaleRepresentation
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) : Prop :=
  ∀ G : RandomL2 P, ∃ U : PredictableProcessL2 𝓅 P,
    G = expectationL2 G + naturalItoIntegral hB hsm hnat U

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The expectation-valued constant has the same expectation as the original random variable. -/
theorem expectationMap_expectationL2 (G : RandomL2 P) :
    CameronMartin.expectationMap P (expectationL2 G) =
      CameronMartin.expectationMap P G := by
  rw [CameronMartin.expectationMap_apply, CameronMartin.expectationMap_apply,
    expectationL2]
  simp only [Lp.const_val, AEEqFun.coeFn_const_eq, integral_const, probReal_univ, smul_eq_mul, one_mul]

omit [CompleteSpace W] [BorelSpace W] in
/-- Martingale representation is exactly surjectivity onto the centered subspace. -/
theorem naturalMartingaleRepresentation_iff_surjective
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      Function.Surjective (centeredNaturalItoIntegralIsometry hB hsm hnat) := by
  constructor
  · intro hMRT G
    obtain ⟨U, hU⟩ := hMRT (G : RandomL2 P)
    have hexpect : expectationL2 (G : RandomL2 P) = 0 := by
      rw [expectationL2]
      have hmean : ∫ w, (G : RandomL2 P) w ∂P = 0 := by
        rw [← CameronMartin.expectationMap_apply]
        exact G.property
      rw [hmean]
      simp only [map_zero]
    refine ⟨U, Subtype.ext ?_⟩
    change naturalItoIntegral hB hsm hnat U = (G : RandomL2 P)
    rw [hexpect, zero_add] at hU
    exact hU.symm
  · intro hsurj G
    let G₀ : (CameronMartin.expectationMap P).ker :=
      ⟨G - expectationL2 G, by
        rw [LinearMap.mem_ker, map_sub]
        exact sub_eq_zero.mpr (expectationMap_expectationL2 (P := P) G).symm⟩
    obtain ⟨U, hU⟩ := hsurj G₀
    refine ⟨U, ?_⟩
    have hambient : naturalItoIntegral hB hsm hnat U = G - expectationL2 G := by
      exact congrArg Subtype.val hU
    rw [hambient]
    abel

/-- Under martingale representation, predictable processes and centered terminal variables are
linearly isometrically equivalent. -/
noncomputable def centeredNaturalItoEquiv
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat) :
    PredictableProcessL2 𝓅 P ≃ₗᵢ[ℝ] (CameronMartin.expectationMap P).ker :=
  LinearIsometryEquiv.ofSurjective
    (centeredNaturalItoIntegralIsometry hB hsm hnat)
    ((naturalMartingaleRepresentation_iff_surjective hB hsm hnat).mp hMRT)

omit [CompleteSpace W] [BorelSpace W] in
@[simp]
theorem centeredNaturalItoEquiv_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (U : PredictableProcessL2 𝓅 P) :
    ((centeredNaturalItoEquiv hB hsm hnat hMRT U :
      (CameronMartin.expectationMap P).ker) : RandomL2 P) =
      naturalItoIntegral hB hsm hnat U :=
  rfl

omit [CompleteSpace W] [BorelSpace W] in
/-- Every terminal value of the constructed Itô integral is centered. -/
theorem range_naturalItoIntegral_le_expectationMap_ker
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap ≤
      (CameronMartin.expectationMap P).ker := by
  rintro _ ⟨U, rfl⟩
  rw [LinearMap.mem_ker]
  change CameronMartin.expectationMap P (naturalItoIntegral hB hsm hnat U) = 0
  rw [CameronMartin.expectationMap_apply]
  exact integral_naturalItoIntegral hB hsm hnat U

omit [CompleteSpace W] [BorelSpace W] in
/-- In particular, the range of the constructed Itô integral contains the entire first chaos. -/
theorem firstChaos_le_range_naturalItoIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    firstChaos hB ≤
      LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap := by
  rw [← range_naturalItoDeterministicIntegral hB hsm hnat]
  rintro _ ⟨f, rfl⟩
  exact ⟨deterministicPredictableEmbedding 𝓅 f, rfl⟩

omit [CompleteSpace W] [BorelSpace W] in
/-- Equivalently, martingale representation says that the constructed Itô range is the entire
closed subspace of centered random variables. -/
theorem naturalMartingaleRepresentation_iff_range_eq_expectationMap_ker
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap =
        (CameronMartin.expectationMap P).ker := by
  rw [naturalMartingaleRepresentation_iff_surjective]
  constructor
  · intro hsurj
    apply le_antisymm (range_naturalItoIntegral_le_expectationMap_ker hB hsm hnat)
    intro G hG
    obtain ⟨U, hU⟩ := hsurj ⟨G, hG⟩
    refine ⟨U, ?_⟩
    exact congrArg Subtype.val hU
  · intro hrange G
    have hG : (G : RandomL2 P) ∈
        LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap := by
      rw [hrange]
      exact G.property
    obtain ⟨U, hU⟩ := hG
    refine ⟨U, Subtype.ext ?_⟩
    exact hU

omit [CompleteSpace W] [BorelSpace W] in
/-- The range of the constructed Itô isometry is closed. -/
theorem isClosed_range_naturalItoIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    IsClosed (LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap :
      Set (RandomL2 P)) := by
  let : Fact (𝓅.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × W))) :=
    ⟨predictable_le_prod 𝓅⟩
  exact (naturalItoIntegralIsometry hB hsm hnat).isometry.isClosedEmbedding.isClosed_range

/-! ## Compatibility of constructed families -/

/-- Equality with the constructed natural Itô operator entails the elementary Brownian formula.
This is the converse of
`ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_eq_naturalItoIntegral`. -/
theorem ClarkOconeFamily.isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓅)
    (hC : C.itoIntegral =
      naturalItoIntegral C.isPreBrownian C.stronglyMeasurable
        C.naturalFiltration) :
    C.IsBrownianOnElementary := by
  intro a b hab Z
  rw [hC, naturalItoIntegral_elementaryPredictable]
  exact (C.elementaryIntegralValue_eq_elementaryBrownianValue hab Z).symm

/-- Brownian compatibility on elementary adapted steps is equivalent to using the constructed
natural-filtration Itô integral. -/
theorem ClarkOconeFamily.isBrownianOnElementary_iff_itoIntegral_eq_naturalItoIntegral
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓅) :
    C.IsBrownianOnElementary ↔
      C.itoIntegral = naturalItoIntegral C.isPreBrownian C.stronglyMeasurable
        C.naturalFiltration :=
  ⟨fun hC ↦ hC.itoIntegral_eq_naturalItoIntegral,
    C.isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral⟩

/-- A family built by `ofNaturalIto` automatically satisfies the textbook elementary formula
`∫_a^b Z dB = Z (B_b - B_a)`. Martingale representation and duality are irrelevant to this
compatibility; they are present only because `ofNaturalIto` produces a full family. -/
theorem ClarkOconeFamily.ofNaturalIto_isBrownianOnElementary
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : ∀ G : RandomL2 P, ∃ U : PredictableProcessL2 𝓅 P,
      G = expectationL2 G + naturalItoIntegral hB hsm hnat U)
    (hDuality : ∀ (F : D12 P) (U : PredictableProcessL2 𝓅 P),
      inner ℝ (F.1 - expectationL2 F.1)
          (naturalItoIntegral hB hsm hnat U) =
        inner ℝ (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) U) :
    (ClarkOconeFamily.ofNaturalIto (W := W) (P := P) (B := B)
      hB coordinate coordinate_apply generated hsm hnat
      hMRT hDuality).IsBrownianOnElementary := by
  intro a b hab Z
  change naturalItoIntegral hB hsm hnat
      (elementaryPredictable 𝓅 a b Z) = _
  rw [naturalItoIntegral_elementaryPredictable]
  exact
    ((ClarkOconeFamily.ofNaturalIto (W := W) (P := P) (B := B)
      hB coordinate coordinate_apply generated hsm hnat hMRT hDuality
      ).elementaryIntegralValue_eq_elementaryBrownianValue hab Z).symm

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
