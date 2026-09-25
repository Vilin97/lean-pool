/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.ClarkOcone
public import LeanPool.Malliavin.Malliavin.DualDerivative
public import LeanPool.Malliavin.Malliavin.CylindricalGrowth
public import LeanPool.Malliavin.Malliavin.ChainRule

/-!
# Consistency of the Clark--Ocone contract on the first chaos

For a functional `F = ∫ g dB` in the first chaos and a deterministic integrand `u = h ⊗ 1`, all
pieces of the `ClarkOconeFamily` contract are now concrete: `F - E F = F`, the integral of `u` is
`∫ h dB` for any family that is Brownian on deterministic integrands, `Dₜ F = g ⊗ 1`
(`DualDerivative.lean`), and the predictable projection fixes deterministic integrands.  The
Malliavin--Itô duality stipulated by the contract therefore holds *as a theorem* on this subspace
(`ClarkOconeFamily.IsBrownianOnDeterministic.duality_wienerIntegral`): both sides equal
`⟪g, h⟫`.

Beyond the first chaos, `CylindricalGrowth.lean` identifies the Malliavin derivative of
`g (B T)` for `C¹` functions `g` of exponential growth.  The abstract representation then reads
`g (B T) = E[g (B T)] + ∫ Π (g' (B T) 1_{(0, T]}) dB` where `Π` is the predictable projection
(`clarkOcone_comp_brownian`, and `clarkOcone_polynomial_brownian` for polynomials); likewise
`φ (∫ g dB) = E[φ (∫ g dB)] + ∫ Π (φ' (∫ g dB) g) dB` for `φ` of class `C¹` with bounded
derivative (`clarkOcone_comp_wienerIntegral`, via the chain rule of `ChainRule.lean`), with the
Poincaré-type consequence `‖φ (F) - E[φ (F)]‖ ≤ K ‖D_cl F‖` for every `F ∈ 𝔻₁,₂`
(`norm_comp_sub_expectationL2_le`).  With the time-form chain and product rules of
`ChainRule.lean` the representation is explicit for `φ (F)`, `f (F₁, …, Fₙ)` and `F · f (B)` with
`F, Fᵢ ∈ 𝔻₁,₂` arbitrary (`clarkOcone_comp`, `clarkOcone_comp_pi`, `clarkOcone_mul_cylinder`),
and for the Wick exponential `exp (B T - T / 2)` (`clarkOcone_wickExp`).  The textbook form
`E[g' (B T) | 𝓕ₜ]` of the integrand is the pointwise identification still missing from the
contract.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Malliavin

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

omit [CompleteSpace W] [BorelSpace W] in
/-- A deterministic time integrand `g ⊗ 1` is the tensor `tensor g 1`. -/
theorem deterministicTimeEmbedding_eq_tensor (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    deterministicTimeEmbedding (P := P) g = tensor g (Lp.const 2 P (1 : ℝ)) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (μ := nonnegativeLebesgueMeasure.prod P)
    g (measurePreserving_fst (ν := P)), coeFn_tensor g (Lp.const 2 P (1 : ℝ)),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_const 2 P (1 : ℝ))] with p h1 h2 h3
  change (Lp.compMeasurePreserving Prod.fst _ g) p = _
  rw [h1, h2]
  simp only [Function.comp_apply] at h3
  rw [h3]
  simp only [Function.comp_apply, Function.const_apply, mul_one]

omit [CompleteSpace W] [BorelSpace W] in
/-- The predictable projection fixes deterministic integrands. -/
theorem predictableProjection_deterministic (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    predictableProjection (P := P) 𝓕 (deterministicTimeEmbedding g) =
      deterministicPredictableEmbedding 𝓕 g := by
  have : Fact (𝓕.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × W))) :=
    ⟨predictable_le_prod 𝓕⟩
  unfold predictableProjection condExpL2
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (deterministicPredictableEmbedding (P := P) 𝓕 g)

/-- **The Malliavin--Itô duality holds on the first chaos against deterministic integrands** for
every family whose integral is Brownian on deterministic integrands: for `F = ∫ g dB` and
`u = h ⊗ 1`, `⟪F - E F, itoIntegral u⟫ = ⟪predictableProjection (Dₜ F), u⟫ = ⟪g, h⟫`. -/
theorem ClarkOconeFamily.IsBrownianOnDeterministic.duality_wienerIntegral
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) (g h : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ⟪wienerIntegral C.isPreBrownian g - expectationL2 (wienerIntegral C.isPreBrownian g),
        C.itoIntegral (deterministicPredictableEmbedding 𝓕 h)⟫_ℝ =
      ⟪predictableProjection 𝓕
        (C.timeDerivative (mderivClosure P (wienerIntegral C.isPreBrownian g))),
        deterministicPredictableEmbedding 𝓕 h⟫_ℝ := by
  -- left side: `E F = 0` and the integral of `h ⊗ 1` is `J₁ h`
  have hE : expectationL2 (wienerIntegral C.isPreBrownian g) = 0 := by
    unfold expectationL2
    rw [integral_wienerIntegral]
    exact map_zero _
  have hI : C.itoIntegral (deterministicPredictableEmbedding 𝓕 h) =
      wienerIntegral C.isPreBrownian h := by
    have := congrArg (fun φ ↦ φ h) hC.deterministicIntegral_eq_wienerIntegral
    simpa [ClarkOconeFamily.deterministicIntegral_apply] using this
  rw [hE, sub_zero, hI, inner_wienerIntegral]
  -- right side: `Dₜ (J₁ g) = g ⊗ 1`, fixed by the predictable projection
  rw [ClarkOconeFamily.timeDerivative_apply, timeDerivative_mderivClosure_wienerIntegral
    C.isPreBrownian C.coordinate C.coordinate_apply C.generated,
    ← deterministicTimeEmbedding_eq_tensor, predictableProjection_deterministic]
  rw [Submodule.coe_inner, ← LinearIsometry.inner_map_map (deterministicTimeEmbedding (P := P))]
  rfl

/-- The Wiener integral `∫ g dB` as an element of `𝔻₁,₂`. -/
noncomputable def wienerIntegralD12 (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) : D12 P :=
  ⟨wienerIntegral hB g, (coe_space_mem_domD12 P ⟨_, wienerIntegral_mem_space hB L hL hgen g⟩).1⟩

/-- **The Clark--Ocone integrand of `∫ g dB` is `g`**: the predictable derivative of a first-chaos
functional is its deterministic kernel. -/
theorem predictableDerivative_wienerIntegralD12 {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    predictableDerivative C
        (wienerIntegralD12 C.isPreBrownian C.coordinate C.coordinate_apply C.generated g) =
      deterministicPredictableEmbedding 𝓕 g := by
  unfold predictableDerivative wienerIntegralD12
  rw [mderivD12_apply, ClarkOconeFamily.timeDerivative_apply,
    timeDerivative_mderivClosure_wienerIntegral C.isPreBrownian C.coordinate C.coordinate_apply
      C.generated, ← deterministicTimeEmbedding_eq_tensor, predictableProjection_deterministic]

/-- **Clark--Ocone is tautological on the first chaos**: for a family Brownian on deterministic
integrands, the Clark--Ocone integral of `∫ g dB` is `∫ g dB` itself. -/
theorem ClarkOconeFamily.IsBrownianOnDeterministic.clarkOconeIntegral_wienerIntegralD12
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    clarkOconeIntegral C
        (wienerIntegralD12 C.isPreBrownian C.coordinate C.coordinate_apply C.generated g) =
      wienerIntegral C.isPreBrownian g := by
  unfold clarkOconeIntegral
  rw [predictableDerivative_wienerIntegralD12]
  have := congrArg (fun φ ↦ φ g) hC.deterministicIntegral_eq_wienerIntegral
  simpa [ClarkOconeFamily.deterministicIntegral_apply] using this

/-! ### Functions of one Brownian coordinate -/

/-- `g (B T)` as an element of `𝔻₁,₂`, for `g` of class `C¹` with exponential growth. -/
noncomputable def compBrownianD12 (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C)
    (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ C * Real.exp (c * |x|))
    (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|)) (T : ℝ≥0) : D12 P :=
  ⟨(memLp_comp_brownian L hL hg hC hc hgb T).toLp _,
    comp_brownian_mem_domD12 L hL hg hC hc hgb hgb' T⟩

/-- `g' (B T)` is square integrable. -/
theorem memLp_deriv_comp_brownian (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|)) (T : ℝ≥0) :
    MemLp (fun w ↦ deriv g (B T w)) 2 P := by
  have h : (fun w ↦ deriv g (B T w)) = fun w ↦ deriv g (L T w) := by
    funext w
    rw [hL]
  rw [h]
  have hc' : Continuous fun w ↦ deriv g (L T w) :=
    hg.continuous_deriv_one.comp (L T).continuous
  refine memLp_of_le_of_integrable_sq P hc'.aestronglyMeasurable
    (integrable_expGrowth_sq P C c ‖L T‖) fun w ↦ ?_
  rw [Real.norm_eq_abs]
  refine (hgb' _).trans ?_
  gcongr
  exact (Real.norm_eq_abs _).symm.le.trans ((L T).le_opNorm w)

/-- **The Clark--Ocone integrand of `g (B T)`** is the predictable projection of the textbook
derivative `g' (B T) 1_{(0, T]}(t)`. -/
theorem predictableDerivative_compBrownianD12 {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {K c : ℝ} (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ K * Real.exp (c * |x|))
    (hgb' : ∀ x, |deriv g x| ≤ K * Real.exp (c * |x|)) (T : ℝ≥0) :
    predictableDerivative C
        (compBrownianD12 C.coordinate C.coordinate_apply hg hK hc hgb hgb' T) =
      predictableProjection 𝓕 (tensor (intervalIndicator T)
        ((memLp_deriv_comp_brownian C.coordinate C.coordinate_apply hg hK hc hgb' T).toLp _)) := by
  unfold predictableDerivative compBrownianD12
  rw [mderivD12_apply, ClarkOconeFamily.timeDerivative_apply,
    timeDerivative_mderivClosure_comp_brownian C.isPreBrownian C.coordinate C.coordinate_apply
      C.generated hg hK hc hgb hgb' T
      (memLp_deriv_comp_brownian C.coordinate C.coordinate_apply hg hK hc hgb' T)]

/-- **Clark--Ocone for `g (B T)`**:
`g (B T) = E[g (B T)] + C.itoIntegral (Π (g' (B T) 1_{(0, T]}))`, where `Π` is the predictable
projection.  Reading `Π (g' (B T) 1_{(0, T]})` timewise as `E[g' (B T) | 𝓕ₜ] 1_{t ≤ T}` is the
pointwise identification not yet part of the contract. -/
theorem clarkOcone_comp_brownian {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {K c : ℝ} (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ K * Real.exp (c * |x|))
    (hgb' : ∀ x, |deriv g x| ≤ K * Real.exp (c * |x|)) (T : ℝ≥0) :
    (memLp_comp_brownian C.coordinate C.coordinate_apply hg hK hc hgb T).toLp _ =
      expectationL2 ((memLp_comp_brownian C.coordinate C.coordinate_apply hg hK hc hgb T).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (tensor (intervalIndicator T)
          ((memLp_deriv_comp_brownian C.coordinate C.coordinate_apply hg hK hc hgb' T).toLp
            _))) := by
  have h := clarkOcone C (compBrownianD12 C.coordinate C.coordinate_apply hg hK hc hgb hgb' T)
  rw [clarkOconeIntegral, predictableDerivative_compBrownianD12] at h
  exact h

/-- **Clark--Ocone for polynomials of a Brownian coordinate**:
`p (B T) = E[p (B T)] + C.itoIntegral (Π (p' (B T) 1_{(0, T]}))` for every real polynomial `p`. -/
theorem clarkOcone_polynomial_brownian {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (p : Polynomial ℝ) (T : ℝ≥0) :
    (memLp_polynomial_brownian C.coordinate C.coordinate_apply p T).toLp _ =
      expectationL2 ((memLp_polynomial_brownian C.coordinate C.coordinate_apply p T).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (tensor (intervalIndicator T)
          ((memLp_polynomial_derivative_brownian C.coordinate C.coordinate_apply p T).toLp
            _))) := by
  have h := clarkOcone_comp_brownian C (contDiff_polynomial_eval p)
    (add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)) (Nat.cast_nonneg _)
    (abs_polynomial_eval_le' p) (abs_polynomial_deriv_le' p) T
  simpa only [Polynomial.deriv] using h

/-! ### Polynomial-growth functions of several Brownian coordinates -/

/-- `f (B t₁, …, B tₙ)` as an element of `𝔻₁,₂`, for `f` of class `C¹` with polynomial growth. -/
noncomputable def cylinderGrowthD12 (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
    {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k)
    (t : Fin n → ℝ≥0) : D12 P :=
  ⟨(memLp_cylinder_growth_brownian L hL hf hC hfg t).toLp _,
    (cylinder_growth_brownian_mem_domD12 L hL hf hC hfg hfg' t).1⟩

/-- **The Clark--Ocone integrand of `f (B t₁, …, B tₙ)`** is the predictable projection of
`∑ᵢ ∂ᵢ f (B) 1_{(0, tᵢ]}(t)`. -/
theorem predictableDerivative_cylinderGrowthD12 {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {K : ℝ} (hK : 0 ≤ K) (hfg : ∀ y, |f y| ≤ K * (1 + ‖y‖) ^ k)
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ K * (1 + ‖y‖) ^ k) (t : Fin n → ℝ≥0) :
    predictableDerivative C
        (cylinderGrowthD12 C.coordinate C.coordinate_apply hf hK hfg hfg' t) =
      predictableProjection 𝓕 (∑ i, tensor (intervalIndicator (t i))
        (cylinderPartialGrowth C.coordinate C.coordinate_apply hf hK hfg' t i)) := by
  unfold predictableDerivative cylinderGrowthD12
  rw [mderivD12_apply, ClarkOconeFamily.timeDerivative_apply,
    timeDerivative_mderivClosure_cylinder_growth C.isPreBrownian C.coordinate
      C.coordinate_apply C.generated hf hK hfg hfg' t]

/-- **Clark--Ocone for polynomial-growth functions of Brownian coordinates**:
`f (B t₁, …, B tₙ) = E[f (B)] + C.itoIntegral (Π (∑ᵢ ∂ᵢ f (B) 1_{(0, tᵢ]}))`. -/
theorem clarkOcone_cylinder_growth {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {K : ℝ} (hK : 0 ≤ K) (hfg : ∀ y, |f y| ≤ K * (1 + ‖y‖) ^ k)
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ K * (1 + ‖y‖) ^ k) (t : Fin n → ℝ≥0) :
    (memLp_cylinder_growth_brownian C.coordinate C.coordinate_apply hf hK hfg t).toLp _ =
      expectationL2
          ((memLp_cylinder_growth_brownian C.coordinate C.coordinate_apply hf hK hfg t).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (∑ i, tensor (intervalIndicator (t i))
          (cylinderPartialGrowth C.coordinate C.coordinate_apply hf hK hfg' t i))) := by
  have h := clarkOcone C (cylinderGrowthD12 C.coordinate C.coordinate_apply hf hK hfg hfg' t)
  rw [clarkOconeIntegral, predictableDerivative_cylinderGrowthD12] at h
  exact h

/-- **Clark--Ocone for the Wick exponential** `exp (B T - T / 2)`:
`exp (B T - T/2) = E[exp (B T - T/2)] + C.itoIntegral (Π (exp (B T - T/2) 1_{(0, T]}))`. -/
theorem clarkOcone_wickExp {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (T : ℝ≥0) :
    (memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _ =
      expectationL2 ((memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (tensor (intervalIndicator T)
          ((memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _))) := by
  have hmem : (memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _ ∈ domD12 P :=
    (comp_brownian_mem_domD12 C.coordinate C.coordinate_apply (contDiff_exp_sub (T / 2))
      zero_le_one zero_le_one (fun x ↦ abs_exp_sub_le_exp_abs (T / 2) x (by positivity))
      (fun x ↦ by rw [deriv_exp_sub]; exact abs_exp_sub_le_exp_abs (T / 2) x (by positivity)) T)
  have h := clarkOcone C ⟨_, hmem⟩
  rw [clarkOconeIntegral, predictableDerivative, mderivD12_apply,
    ClarkOconeFamily.timeDerivative_apply] at h
  change (memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _ =
    expectationL2 ((memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _) +
      C.itoIntegral (predictableProjection 𝓕 (timeDerivative C.isPreBrownian C.coordinate
        C.coordinate_apply C.generated (mderivClosure P
          ((memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _)))) at h
  rwa [timeDerivative_mderivClosure_wickExp_brownian C.isPreBrownian C.coordinate
    C.coordinate_apply C.generated T] at h

/-! ### Functions of Wiener integrals -/

/-- `φ (∫ g dB)` as an element of `𝔻₁,₂`, for `φ` of class `C¹` with bounded derivative. -/
noncomputable def compWienerIntegralD12 (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) {φ : ℝ → ℝ} {K : ℝ≥0}
    (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    D12 P :=
  ⟨(memLp_comp_of_deriv_le P hφ hK (wienerIntegral hB g)).toLp _,
    (comp_mem_domD12 P hφ hK (wienerIntegralD12 hB L hL hgen g).2).1⟩

/-- **The Clark--Ocone integrand of `φ (∫ g dB)`** is the predictable projection of
`φ' (∫ g dB) g(t)`. -/
theorem predictableDerivative_compWienerIntegralD12 {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    predictableDerivative C (compWienerIntegralD12 C.isPreBrownian C.coordinate
        C.coordinate_apply C.generated hφ hK g) =
      predictableProjection 𝓕
        (tensor g ((memLp_deriv_comp hφ hK (wienerIntegral C.isPreBrownian g)).toLp _)) := by
  unfold predictableDerivative compWienerIntegralD12
  rw [mderivD12_apply, ClarkOconeFamily.timeDerivative_apply,
    timeDerivative_mderivClosure_comp_wienerIntegral C.isPreBrownian C.coordinate
      C.coordinate_apply C.generated hφ hK g]

/-- **Clark--Ocone for `φ (∫ g dB)`**:
`φ (∫ g dB) = E[φ (∫ g dB)] + C.itoIntegral (Π (φ' (∫ g dB) g(t)))`. -/
theorem clarkOcone_comp_wienerIntegral {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (memLp_comp_of_deriv_le P hφ hK (wienerIntegral C.isPreBrownian g)).toLp _ =
      expectationL2 ((memLp_comp_of_deriv_le P hφ hK (wienerIntegral C.isPreBrownian g)).toLp _)
        + C.itoIntegral (predictableProjection 𝓕
          (tensor g ((memLp_deriv_comp hφ hK (wienerIntegral C.isPreBrownian g)).toLp _))) := by
  have h := clarkOcone C (compWienerIntegralD12 C.isPreBrownian C.coordinate C.coordinate_apply
    C.generated hφ hK g)
  rw [clarkOconeIntegral, predictableDerivative_compWienerIntegralD12] at h
  exact h

/-- `f (∫ g₁ dB, …, ∫ gₙ dB)` as an element of `𝔻₁,₂`. -/
noncomputable def compPiWienerIntegralD12 (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ} (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K)
    (g : Fin n → Lp ℝ 2 nonnegativeLebesgueMeasure) : D12 P :=
  ⟨(memLp_comp_pi P hf hK fun i ↦ wienerIntegral hB (g i)).toLp _,
    (comp_pi_mem_domD12 P hf hK fun i ↦ (wienerIntegralD12 hB L hL hgen (g i)).2).1⟩

/-- **The Clark--Ocone integrand of `f (∫ g₁ dB, …, ∫ gₙ dB)`** is the predictable projection of
`∑ᵢ ∂ᵢ f (∫ g dB) gᵢ(t)`. -/
theorem predictableDerivative_compPiWienerIntegralD12 {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (g : Fin n → Lp ℝ 2 nonnegativeLebesgueMeasure) :
    predictableDerivative C (compPiWienerIntegralD12 C.isPreBrownian C.coordinate
        C.coordinate_apply C.generated hf hK g) =
      predictableProjection 𝓕 (∑ i, tensor (g i)
        ((memLp_fderiv_pi_comp hf hK (fun i ↦ wienerIntegral C.isPreBrownian (g i)) i).toLp
          _)) := by
  unfold predictableDerivative compPiWienerIntegralD12
  rw [mderivD12_apply, ClarkOconeFamily.timeDerivative_apply,
    timeDerivative_mderivClosure_comp_pi_wienerIntegral C.isPreBrownian C.coordinate
      C.coordinate_apply C.generated hf hK g]

/-- **Clark--Ocone for `f (∫ g₁ dB, …, ∫ gₙ dB)`**:
`f (∫ g dB) = E[f (∫ g dB)] + C.itoIntegral (Π (∑ᵢ ∂ᵢ f (∫ g dB) gᵢ(t)))`. -/
theorem clarkOcone_comp_pi_wienerIntegral {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (g : Fin n → Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (memLp_comp_pi P hf hK fun i ↦ wienerIntegral C.isPreBrownian (g i)).toLp _ =
      expectationL2
          ((memLp_comp_pi P hf hK fun i ↦ wienerIntegral C.isPreBrownian (g i)).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (∑ i, tensor (g i)
          ((memLp_fderiv_pi_comp hf hK (fun i ↦ wienerIntegral C.isPreBrownian (g i)) i).toLp
            _))) := by
  have h := clarkOcone C (compPiWienerIntegralD12 C.isPreBrownian C.coordinate
    C.coordinate_apply C.generated hf hK g)
  rw [clarkOconeIntegral, predictableDerivative_compPiWienerIntegralD12] at h
  exact h

/-- **The Clark--Ocone integrand of `φ (F)`** for an arbitrary `F ∈ 𝔻₁,₂` is the predictable
projection of `φ' (F) Dₜ F`. -/
theorem predictableDerivative_comp {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 P) :
    predictableDerivative C (D12.comp P hφ hK F) =
      predictableProjection 𝓕 (boundedSMul
        (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
          (hφ.continuous_deriv_one.comp_aestronglyMeasurable
            (Lp.aestronglyMeasurable (F : Lp ℝ 2 P))))
        (C := K) (fun p ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK ((F : Lp ℝ 2 P) p.2))
        (C.timeDerivative (mderivD12 P F))) := by
  unfold predictableDerivative
  rw [mderivD12_apply, ClarkOconeFamily.timeDerivative_apply, D12.coe_comp,
    timeDerivative_mderivClosure_comp C.isPreBrownian C.coordinate C.coordinate_apply C.generated
      hφ hK F.2, ClarkOconeFamily.timeDerivative_apply, mderivD12_apply]

/-- **Energy identity for `φ (F)`**: `‖φ (F) - E[φ (F)]‖ = ‖Π (φ' (F) Dₜ F)‖`. -/
theorem norm_comp_sub_expectationL2_eq {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 P) :
    ‖(D12.comp P hφ hK F : Lp ℝ 2 P) - expectationL2 (D12.comp P hφ hK F : Lp ℝ 2 P)‖ =
      ‖predictableProjection 𝓕 (boundedSMul
        (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
          (hφ.continuous_deriv_one.comp_aestronglyMeasurable
            (Lp.aestronglyMeasurable (F : Lp ℝ 2 P))))
        (C := K) (fun p ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK ((F : Lp ℝ 2 P) p.2))
        (C.timeDerivative (mderivD12 P F)))‖ := by
  rw [norm_sub_expectationL2 C, predictableDerivative_comp]

/-- **Clark--Ocone for `φ (F)`, `F ∈ 𝔻₁,₂` arbitrary**:
`φ (F) = E[φ (F)] + C.itoIntegral (Π (φ' (F) Dₜ F))`. -/
theorem clarkOcone_comp {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 P) :
    (D12.comp P hφ hK F : Lp ℝ 2 P) =
      expectationL2 (D12.comp P hφ hK F : Lp ℝ 2 P) +
        C.itoIntegral (predictableProjection 𝓕 (boundedSMul
          (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
            (hφ.continuous_deriv_one.comp_aestronglyMeasurable
              (Lp.aestronglyMeasurable (F : Lp ℝ 2 P))))
          (C := K) (fun p ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK ((F : Lp ℝ 2 P) p.2))
          (C.timeDerivative (mderivD12 P F)))) := by
  have h := clarkOcone C (D12.comp P hφ hK F)
  rw [clarkOconeIntegral, predictableDerivative_comp] at h
  exact h

/-- **Clark--Ocone for `f (F₁, …, Fₙ)`, `Fᵢ ∈ 𝔻₁,₂` arbitrary**:
`f (F) = E[f (F)] + C.itoIntegral (Π (∑ᵢ ∂ᵢ f (F) Dₜ Fᵢ))`. -/
theorem clarkOcone_comp_pi {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (F : Fin n → D12 P) :
    (D12.compPi P hf hK F : Lp ℝ 2 P) =
      expectationL2 (D12.compPi P hf hK F : Lp ℝ 2 P) +
        C.itoIntegral (predictableProjection 𝓕 (∑ i,
          boundedSMul (G := fun p : ℝ≥0 × W ↦ fderiv ℝ f (fun i ↦ (F i : Lp ℝ 2 P) p.2)
              (Pi.single i 1))
            (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
              (memLp_fderiv_pi_comp hf hK (fun i ↦ (F i : Lp ℝ 2 P)) i).aestronglyMeasurable)
            (C := K) (fun _ ↦ abs_fderiv_pi_single_le hK _ i)
            (C.timeDerivative (mderivD12 P (F i))))) := by
  have h := clarkOcone C (D12.compPi P hf hK F)
  rw [clarkOconeIntegral, predictableDerivative, mderivD12_apply,
    ClarkOconeFamily.timeDerivative_apply] at h
  change (D12.compPi P hf hK F : Lp ℝ 2 P) = expectationL2 (D12.compPi P hf hK F : Lp ℝ 2 P) +
    C.itoIntegral (predictableProjection 𝓕 (timeDerivative C.isPreBrownian C.coordinate
      C.coordinate_apply C.generated (mderivClosure P
        ((memLp_comp_pi P hf hK fun i ↦ (F i : Lp ℝ 2 P)).toLp _)))) at h
  rw [timeDerivative_mderivClosure_comp_pi C.isPreBrownian C.coordinate C.coordinate_apply
    C.generated hf hK fun i ↦ (F i).2] at h
  simpa only [ClarkOconeFamily.timeDerivative_apply, mderivD12_apply] using h

/-- **Clark--Ocone for `F · f (B t₁, …, B tₙ)`, `F ∈ 𝔻₁,₂` arbitrary**:
`F f (B) = E[F f (B)] + C.itoIntegral (Π (f (B) Dₜ F + F ∑ᵢ ∂ᵢ f (B) 1_{(0, tᵢ]}))`. -/
theorem clarkOcone_mul_cylinder {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hb : ∀ y, |f y| ≤ K) (hb' : ∃ K', ∀ y, ‖fderiv ℝ f y‖ ≤ K') (t : Fin n → ℝ≥0)
    {F : Lp ℝ 2 P} (hF : F ∈ domD12 P) :
    (memLp_mul_smoothBounded P
        (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t) F).toLp _ =
      expectationL2 ((memLp_mul_smoothBounded P
        (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t) F).toLp _)
        + C.itoIntegral (predictableProjection 𝓕
          (boundedSMul (G := fun p : ℝ≥0 × W ↦ f (fun i ↦ B (t i) p.2))
            (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
              (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb'
                t).continuous.aestronglyMeasurable)
            (C := K) (fun p ↦ hb (fun i ↦ B (t i) p.2))
            (C.timeDerivative (mderivD12 P ⟨F, hF⟩)) +
          ∑ i, tensor (intervalIndicator (t i))
            ((memLp_mul_cylinderPartial C.coordinate C.coordinate_apply f hf hb' t F i).toLp
              _))) := by
  have hmem := (mul_mem_domD12 P
    (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t) hF).1
  have h := clarkOcone C ⟨_, hmem⟩
  rw [clarkOconeIntegral, predictableDerivative, mderivD12_apply,
    ClarkOconeFamily.timeDerivative_apply] at h
  change (memLp_mul_smoothBounded P
      (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t) F).toLp _ =
    expectationL2 ((memLp_mul_smoothBounded P
      (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t) F).toLp _)
      + C.itoIntegral (predictableProjection 𝓕 (timeDerivative C.isPreBrownian C.coordinate
        C.coordinate_apply C.generated (mderivClosure P ((memLp_mul_smoothBounded P
          (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t)
            F).toLp _)))) at h
  rwa [timeDerivative_mderivClosure_mul_cylinder C.isPreBrownian C.coordinate
    C.coordinate_apply C.generated f hf hb hb' t hF] at h

/-- **Poincaré-type estimate for composites**: `‖φ (F) - E[φ (F)]‖ ≤ K ‖D_cl F‖` for every
`F ∈ 𝔻₁,₂` and `φ` of class `C¹` with `|φ'| ≤ K`, via the abstract representation. -/
theorem norm_comp_sub_expectationL2_le {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 P) :
    ‖(D12.comp P hφ hK F : Lp ℝ 2 P) - expectationL2 (D12.comp P hφ hK F : Lp ℝ 2 P)‖ ≤
      K * ‖mderivD12 P F‖ :=
  (norm_sub_expectationL2_le_mderivD12 C (D12.comp P hφ hK F)).trans
    (norm_mderivClosure_comp_le P hφ hK F.2)

/-- **Poincaré-type estimate for multivariate composites**:
`‖f (F) - E[f (F)]‖ ≤ K ∑ᵢ ‖D_cl Fᵢ‖` for `F₁, …, Fₙ ∈ 𝔻₁,₂` and `f` of class `C¹` with
`‖f'‖ ≤ K`. -/
theorem norm_compPi_sub_expectationL2_le {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (F : Fin n → D12 P) :
    ‖(D12.compPi P hf hK F : Lp ℝ 2 P) - expectationL2 (D12.compPi P hf hK F : Lp ℝ 2 P)‖ ≤
      K * ∑ i, ‖mderivD12 P (F i)‖ :=
  (norm_sub_expectationL2_le_mderivD12 C (D12.compPi P hf hK F)).trans
    (norm_mderivClosure_comp_pi_le P hf hK fun i ↦ (F i).2)

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
