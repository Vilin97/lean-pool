/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.WienerIntegral
import LeanPool.Malliavin.Malliavin.FubiniLift
import LeanPool.Malliavin.Malliavin.MalliavinDerivative
import Mathlib.Tactic.Recall

/-!
# The time derivative: from `H`-valued random variables to processes

The Clark--Ocone contract (`ClarkOconeFamily.timeDerivative`) asks for an isometry
`L²(P; H) → L²(ℝ≥0 × Ω)` realizing an `H`-valued random variable `U` as the process
`(t, ω) ↦ (U ω)(t)`, where `H` is the Cameron--Martin space.  On a Wiener space the
Cameron--Martin directions are identified with deterministic `L²` time functions through the
Wiener integral: `J₁ : L²(ℝ≥0) ≃ firstChaos` (`wienerIntegralEquiv`).  Applying `J₁⁻¹`
pointwise (`compLpₗᵢ`) and then the Fubini lift (`fubiniLift`) gives the time derivative on
first-chaos-valued random variables (`timeDerivativeOfFirstChaos`).

For a Gaussian measure whose Brownian coordinates are continuous linear functionals and generate
the sigma-algebra, the Cameron--Martin space *is* the first chaos (`space_eq_firstChaos`): a
Cameron--Martin element orthogonal to all coordinates is jointly Gaussian with every finite family
of them, hence independent of `σ(B) = ⊤`, hence zero.  The construction therefore produces the
contract's `timeDerivative` unconditionally (`timeDerivative`).

## Main definitions

* `Malliavin.compLpₗᵢ`: the isometry `Lp E 2 μ →ₗᵢ Lp F 2 μ` induced by an isometry `E →ₗᵢ F`;
* `Malliavin.wienerIntegralEquiv`: `L²(ℝ≥0) ≃ₗᵢ firstChaos`;
* `Malliavin.timeDerivativeOfFirstChaos`, `timeDerivativeOfEq`, `timeDerivative`: the time
  derivative.

## Main results

* `Malliavin.inner_timeDerivativeOfFirstChaos_tensorLp`: the weak Fubini identity
  `⟪Dₜ U, g ⊗ 1_A⟫ = ∫ ω in A, ⟪J₁ g, U ω⟫ ∂P`;
* `Malliavin.space_eq_firstChaos`: on a Brownian-generated Gaussian space with linear-functional
  coordinates, the Cameron--Martin space is the first chaos;
* `Malliavin.timeDerivative`, `timeDerivativeEquiv`: the contract's time derivative, an
  isometric equivalence `L²(P; Space P) ≃ L²(ℝ≥0 × W)`;
* `Malliavin.timeDerivative_mderivLp_cylinder`: the textbook formula
  `Dₜ f(B t₁, …, B tₙ) = ∑ᵢ ∂ᵢ f (B t₁, …, B tₙ) · 1_{(0, tᵢ]}(t)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Malliavin

/-! ### `L²` functoriality along isometries -/

section CompLp

variable {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Postcomposition with a linear isometry preserves `L²` inner products. -/
theorem inner_compLpL_compLpL (L : E →ₗᵢ[ℝ] F) (f g : Lp E 2 μ) :
    ⟪L.toContinuousLinearMap.compLpL 2 μ f, L.toContinuousLinearMap.compLpL 2 μ g⟫_ℝ =
      ⟪f, g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [L.toContinuousLinearMap.coeFn_compLpL f,
    L.toContinuousLinearMap.coeFn_compLpL g] with ω h1 h2
  rw [h1, h2, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.inner_map_map]

/-- Postcomposition with a linear isometry `E →ₗᵢ F` as a linear isometry `L²(μ; E) → L²(μ; F)`. -/
noncomputable def compLpₗᵢ (L : E →ₗᵢ[ℝ] F) : Lp E 2 μ →ₗᵢ[ℝ] Lp F 2 μ :=
  ⟨(L.toContinuousLinearMap.compLpL 2 μ).toLinearMap, fun f ↦ by
    have h := inner_compLpL_compLpL L f f
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h⟩

theorem coeFn_compLpₗᵢ (L : E →ₗᵢ[ℝ] F) (f : Lp E 2 μ) :
    (compLpₗᵢ L f : Ω → F) =ᵐ[μ] fun ω ↦ L (f ω) :=
  L.toContinuousLinearMap.coeFn_compLpL f

/-- Pointwise linear maps commute with bounded multipliers. -/
theorem compLpₗᵢ_boundedSMul (L : E →ₗᵢ[ℝ] F) {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ)
    {C : ℝ} (hC : ∀ x, |G x| ≤ C) (f : Lp E 2 μ) :
    compLpₗᵢ L (boundedSMul hG hC f) = boundedSMul hG hC (compLpₗᵢ L f) := by
  apply Lp.ext
  filter_upwards [coeFn_compLpₗᵢ L (boundedSMul hG hC f), coeFn_boundedSMul hG hC f,
    coeFn_boundedSMul hG hC (compLpₗᵢ L f), coeFn_compLpₗᵢ L f] with ω h1 h2 h3 h4
  rw [h1, h2, h3, h4, map_smul]

theorem compLpₗᵢ_indicatorConstLp (L : E →ₗᵢ[ℝ] F) {A : Set Ω} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) (c : E) :
    compLpₗᵢ L (indicatorConstLp 2 hA hμA c) = indicatorConstLp 2 hA hμA (L c) := by
  apply Lp.ext
  filter_upwards [coeFn_compLpₗᵢ L (indicatorConstLp 2 hA hμA c),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := c),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := L c)] with ω h1 h2 h3
  rw [h1, h2, h3]
  by_cases hω : ω ∈ A <;> simp [hω]

/-- `compLpₗᵢ` is natural on rank-one elements. -/
theorem compLpₗᵢ_smulLp (L : E →ₗᵢ[ℝ] F) (e : E) (G : Lp ℝ 2 μ) :
    compLpₗᵢ L (smulLp e G) = smulLp (L e) G := by
  apply Lp.ext
  filter_upwards [coeFn_compLpₗᵢ L (smulLp e G), coeFn_smulLp e G, coeFn_smulLp (L e) G]
    with ω h1 h2 h3
  rw [h1, h2, h3, map_smul]

theorem compLpₗᵢ_comp_compLpₗᵢ (e : E ≃ₗᵢ[ℝ] F) (f : Lp F 2 μ) :
    compLpₗᵢ e.toLinearIsometry (compLpₗᵢ e.symm.toLinearIsometry f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_compLpₗᵢ e.toLinearIsometry (compLpₗᵢ e.symm.toLinearIsometry f),
    coeFn_compLpₗᵢ e.symm.toLinearIsometry f] with ω h1 h2
  rw [h1, h2, LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply]

/-- Postcomposition with a linear isometric equivalence `E ≃ F` as an equivalence
`L²(μ; E) ≃ L²(μ; F)`. -/
noncomputable def compLpEquiv (e : E ≃ₗᵢ[ℝ] F) : Lp E 2 μ ≃ₗᵢ[ℝ] Lp F 2 μ :=
  LinearIsometryEquiv.ofSurjective (compLpₗᵢ e.toLinearIsometry) fun f ↦
    ⟨compLpₗᵢ e.symm.toLinearIsometry f, compLpₗᵢ_comp_compLpₗᵢ e f⟩

theorem compLpEquiv_apply (e : E ≃ₗᵢ[ℝ] F) (f : Lp E 2 μ) :
    compLpEquiv e f = compLpₗᵢ e.toLinearIsometry f := rfl

end CompLp

/-! ### The Wiener integral as an equivalence onto the first chaos -/

section WienerEquiv

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The Wiener integral as a linear isometric equivalence `L²(ℝ≥0) ≃ firstChaos`. -/
noncomputable def wienerIntegralEquiv (hB : IsPreBrownianReal B P) :
    Lp ℝ 2 nonnegativeLebesgueMeasure ≃ₗᵢ[ℝ] firstChaos hB :=
  (wienerIntegralₗᵢ hB).equivRange.trans (LinearIsometryEquiv.ofEq _ _ (range_wienerIntegral hB))

theorem coe_wienerIntegralEquiv_apply (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (wienerIntegralEquiv hB f : RandomL2 P) = wienerIntegral hB f := rfl

theorem wienerIntegralEquiv_symm_apply (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (wienerIntegralEquiv hB).symm ⟨wienerIntegral hB f, by
      rw [← range_wienerIntegral]; exact ⟨f, rfl⟩⟩ = f := by
  apply (wienerIntegralEquiv hB).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Applying the Wiener integral after its inverse on the first chaos recovers the ambient
random variable. -/
theorem wienerIntegral_wienerIntegralEquiv_symm_apply (hB : IsPreBrownianReal B P)
    (Z : firstChaos hB) :
    wienerIntegral hB ((wienerIntegralEquiv hB).symm Z) = (Z : RandomL2 P) := by
  rw [← coe_wienerIntegralEquiv_apply]
  exact congrArg Subtype.val ((wienerIntegralEquiv hB).apply_symm_apply Z)

/-- Pairing with `J₁⁻¹` is pairing with `J₁`: `⟪g, J₁⁻¹ Z⟫ = ⟪J₁ g, Z⟫`. -/
theorem inner_wienerIntegralEquiv_symm (hB : IsPreBrownianReal B P)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) (Z : firstChaos hB) :
    ⟪g, (wienerIntegralEquiv hB).symm Z⟫_ℝ = ⟪wienerIntegral hB g, (Z : RandomL2 P)⟫_ℝ := by
  rw [← (wienerIntegralEquiv hB).inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  rfl

end WienerEquiv

/-! ### The time derivative on first-chaos-valued random variables -/

section TimeDerivative

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} [SFinite P]

/-- **The time derivative** on first-chaos-valued square-integrable random variables:
apply `J₁⁻¹` pointwise, then the Fubini lift. -/
noncomputable def timeDerivativeOfFirstChaos (hB : IsPreBrownianReal B P) :
    Lp (firstChaos hB) 2 P →ₗᵢ[ℝ] Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P) :=
  fubiniLift.comp (compLpₗᵢ (wienerIntegralEquiv hB).symm.toLinearIsometry)

theorem timeDerivativeOfFirstChaos_apply (hB : IsPreBrownianReal B P)
    (U : Lp (firstChaos hB) 2 P) :
    timeDerivativeOfFirstChaos hB U =
      fubiniLift (compLpₗᵢ (wienerIntegralEquiv hB).symm.toLinearIsometry U) := rfl

/-- On a simple tensor `1_A • J₁ g` the time derivative is `(t, ω) ↦ g t · 1_A ω`. -/
theorem timeDerivativeOfFirstChaos_indicatorConstLp (hB : IsPreBrownianReal B P)
    (A : FiniteMeasurableSet P) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    timeDerivativeOfFirstChaos hB (indicatorConstLp 2 A.2.1 A.2.2 (wienerIntegralEquiv hB g)) =
      tensorLp A g := by
  rw [timeDerivativeOfFirstChaos_apply, compLpₗᵢ_indicatorConstLp]
  change fubiniLift (indicatorLp A ((wienerIntegralEquiv hB).symm (wienerIntegralEquiv hB g))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, fubiniLift_indicatorLp]

/-- **Weak Fubini identity for the time derivative**:
`⟪Dₜ U, g ⊗ 1_A⟫ = ∫ ω in A, ⟪J₁ g, U ω⟫ ∂P`. -/
theorem inner_timeDerivativeOfFirstChaos_tensorLp (hB : IsPreBrownianReal B P)
    (U : Lp (firstChaos hB) 2 P) (A : FiniteMeasurableSet P)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ⟪timeDerivativeOfFirstChaos hB U, tensorLp A g⟫_ℝ =
      ∫ ω in A.1, ⟪wienerIntegral hB g, (U ω : RandomL2 P)⟫_ℝ ∂P := by
  rw [timeDerivativeOfFirstChaos_apply, inner_fubiniLift_tensorLp]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
    (coeFn_compLpₗᵢ (wienerIntegralEquiv hB).symm.toLinearIsometry U)] with ω hω
  rw [hω, LinearIsometryEquiv.coe_toLinearIsometry, inner_wienerIntegralEquiv_symm]

end TimeDerivative

/-! ### The first chaos inside the Cameron--Martin space -/

section CameronMartin

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

/-- If the Brownian coordinates are continuous linear functionals, each is the centered class of
that functional, i.e. a generator of the Cameron--Martin space. -/
theorem brownianLp_eq_ofDual (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (t : ℝ≥0) :
    brownianLp hB t = (ofDual P (L t) : Lp ℝ 2 P) := by
  have hmean : L t (mean P) = 0 := by
    rw [mean, ← IsGaussian.integral_dual (L t), ← hB.integral_eval t]
    congr 1
    funext w
    exact (hL t w).symm
  apply Lp.ext
  filter_upwards [coeFn_brownianLp hB t, centeredDualToLp_ae_eq P (L t)] with w h1 h2
  rw [h1, coe_ofDual, h2, hmean, sub_zero, hL]

/-- The first chaos of linear-functional coordinates lies in the Cameron--Martin space. -/
theorem firstChaos_le_space (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) :
    firstChaos hB ≤ Space P := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  rw [brownianLp_eq_ofDual hB L hL t]
  exact (ofDual P (L t)).2

/-- **The contract's time derivative**, given the identification of the Cameron--Martin space with
the first chaos: `L²(P; Space P) → L²(ℝ≥0 × W)`, an isometry. -/
noncomputable def timeDerivativeOfEq (hB : IsPreBrownianReal B P)
    (hS : Space P = firstChaos hB) :
    Lp (Space P) 2 P →ₗᵢ[ℝ] Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P) :=
  (timeDerivativeOfFirstChaos hB).comp
    (compLpₗᵢ (LinearIsometryEquiv.ofEq _ _ hS).toLinearIsometry)

omit [CompleteSpace W] in
theorem norm_timeDerivativeOfEq (hB : IsPreBrownianReal B P) (hS : Space P = firstChaos hB)
    (U : Lp (Space P) 2 P) : ‖timeDerivativeOfEq hB hS U‖ = ‖U‖ :=
  (timeDerivativeOfEq hB hS).norm_map U

/-! ### The Cameron--Martin space is the first chaos

On a Brownian-generated Gaussian space whose coordinates are continuous linear functionals, the
Cameron--Martin space (closed span of all centered functionals) coincides with the first chaos
(closed span of the coordinates).  An element `Z` of the Cameron--Martin space orthogonal to all
coordinates is jointly Gaussian with every finite family of coordinates (because all linear
combinations lie in the Gaussian space `Space P`), hence independent of each finite family, hence
of `σ(B) = ⊤`, hence of itself, hence zero. -/

/-- Brownian coordinates that are linear functionals lie in the Cameron--Martin space. -/
theorem brownianLp_mem_space (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (t : ℝ≥0) : brownianLp hB t ∈ Space P := by
  rw [brownianLp_eq_ofDual hB L hL t]
  exact (ofDual P (L t)).2

/-- The finite Gaussian vector `(Z, (B i)_{i ∈ I})` attached to `Z ∈ Space P`. -/
noncomputable def spaceVector (B : ℝ≥0 → W → ℝ) (Z : RandomL2 P) (I : Finset ℝ≥0) (w : W) :
    ℝ × (I → ℝ) :=
  (Z w, fun i ↦ B i w)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P] in
theorem aemeasurable_spaceVector (hB : IsPreBrownianReal B P) (Z : RandomL2 P)
    (I : Finset ℝ≥0) : AEMeasurable (spaceVector B Z I) P := by
  refine AEMeasurable.prodMk (Lp.aestronglyMeasurable Z).aemeasurable ?_
  exact aemeasurable_pi_iff.mpr fun i ↦ hB.aemeasurable i

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P] in
/-- A linear functional of `spaceVector` is a.e. a linear combination of `Z` and the `B i`. -/
theorem coeFn_combination_spaceVector (hB : IsPreBrownianReal B P) (Z : RandomL2 P)
    (I : Finset ℝ≥0) (ℓ : (ℝ × (I → ℝ)) →L[ℝ] ℝ) :
    ((ℓ (1, 0) • Z + ∑ i : I, ℓ (0, Pi.single i 1) • brownianLp hB i : RandomL2 P) : W → ℝ)
      =ᵐ[P] fun w ↦ ℓ (spaceVector B Z I w) := by
  have hsum := Lp.coeFn_finsetSum (μ := P) Finset.univ
    (fun i : I ↦ ℓ (0, Pi.single i 1) • brownianLp hB i)
  have hB' : ∀ᵐ w ∂P, ∀ i : I, (brownianLp hB i : W → ℝ) w = B i w :=
    ae_all_iff.2 fun i ↦ coeFn_brownianLp hB i
  have hsmul : ∀ᵐ w ∂P, ∀ i : I,
      ((ℓ (0, Pi.single i 1) • brownianLp hB i : RandomL2 P) : W → ℝ) w =
        ℓ (0, Pi.single i 1) * (brownianLp hB i : W → ℝ) w :=
    ae_all_iff.2 fun i ↦ by
      filter_upwards [Lp.coeFn_smul (ℓ (0, Pi.single i 1)) (brownianLp hB i)] with w hw
      rw [hw, Pi.smul_apply, smul_eq_mul]
  filter_upwards [Lp.coeFn_add (ℓ (1, 0) • Z) (∑ i : I, ℓ (0, Pi.single i 1) • brownianLp hB i),
    Lp.coeFn_smul (ℓ (1, 0)) Z, hsum, hB', hsmul] with w h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, h3, Finset.sum_apply]
  simp_rw [h5, h4]
  -- expand ℓ on the decomposition of the vector
  have hdec : spaceVector B Z I w =
      Z w • ((1 : ℝ), (0 : I → ℝ)) + ∑ i : I, B i w • ((0 : ℝ), Pi.single i (1 : ℝ)) := by
    ext x
    · simp only [spaceVector, Prod.smul_mk, smul_eq_mul, mul_one, smul_zero,
        Finset.univ_eq_attach, mul_zero,
        Prod.fst_add, Prod.fst_sum, Finset.sum_const_zero, add_zero]
    · simp only [spaceVector, Prod.smul_mk, smul_eq_mul, mul_one, smul_zero,
        Finset.univ_eq_attach, mul_zero,
        Prod.snd_add, Prod.snd_sum, Pi.add_apply, Pi.zero_apply, Finset.sum_apply,
        Pi.smul_apply, Pi.single_apply, mul_ite,
        Finset.sum_ite_eq, Finset.mem_attach, ↓reduceIte, zero_add]
  rw [hdec, map_add, map_smul, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  refine congrArg₂ (· + ·) (mul_comm _ _) (Finset.sum_congr rfl fun i _ ↦ mul_comm _ _)

/-- **Joint Gaussianity inside the Cameron--Martin space**: for `Z ∈ Space P` and finitely many
Brownian coordinates, the vector `(Z, (B i)_{i ∈ I})` is Gaussian. -/
theorem hasGaussianLaw_spaceVector (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) {Z : RandomL2 P} (hZ : Z ∈ Space P) (I : Finset ℝ≥0) :
    HasGaussianLaw (spaceVector B Z I) P := by
  refine ⟨aemeasurable_spaceVector hB Z I,
    isGaussian_of_isGaussian_map fun ℓ ↦ ?_⟩
  have hmeas := aemeasurable_spaceVector hB Z I
  rw [AEMeasurable.map_map_of_aemeasurable ℓ.continuous.measurable.aemeasurable hmeas]
  have hmem : ℓ (1, 0) • Z + ∑ i : I, ℓ (0, Pi.single i 1) • brownianLp hB i ∈ Space P :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hZ)
      (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (brownianLp_mem_space hB L hL i))
  have hG := (space_hasGaussianLaw P ⟨_, hmem⟩).congr (coeFn_combination_spaceVector hB Z I ℓ)
  exact hG.isGaussian_map

/-- Covariance of `Z ∈ Space P` with a Brownian coordinate is the `L²` pairing. -/
theorem covariance_coe_eval (hB : IsPreBrownianReal B P) {Z : RandomL2 P} (hZ : Z ∈ Space P)
    (t : ℝ≥0) : cov[(Z : W → ℝ), B t; P] = ⟪Z, brownianLp hB t⟫_ℝ := by
  rw [covariance_eq_sub (Lp.memLp Z) ((hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two),
    integral_coe_eq_zero P ⟨Z, hZ⟩, zero_mul, sub_zero, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_brownianLp hB t] with w hw
  rw [Pi.mul_apply, hw]
  simp only [mul_comm, RCLike.inner_apply, conj_trivial]

/-- **Uncorrelated ⇒ independent** inside the Cameron--Martin space: `Z ∈ Space P` orthogonal to
all Brownian coordinates is independent of every finite family of them. -/
theorem indepFun_of_orthogonal (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) {Z : RandomL2 P} (hZ : Z ∈ Space P)
    (horth : ∀ t, ⟪Z, brownianLp hB t⟫_ℝ = 0) (I : Finset ℝ≥0) :
    IndepFun (Z : W → ℝ) (fun w ↦ fun i : I ↦ B i w) P := by
  refine (hasGaussianLaw_spaceVector hB L hL hZ I).indepFun_of_covariance_strongDual
    fun L₁ L₂ ↦ ?_
  have h1 : (L₁ ∘ fun w ↦ (Z : W → ℝ) w) = fun w ↦ L₁ 1 * (Z : W → ℝ) w := by
    funext w
    calc L₁ ((Z : W → ℝ) w) = L₁ ((Z : W → ℝ) w • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
      _ = (Z : W → ℝ) w • L₁ 1 := map_smul _ _ _
      _ = L₁ 1 * (Z : W → ℝ) w := by rw [smul_eq_mul, mul_comm]
  have h2 : (L₂ ∘ fun w ↦ fun i : I ↦ B i w) = fun w ↦ ∑ i : I, L₂ (Pi.single i 1) * B i w := by
    funext w
    rw [Function.comp_apply]
    have : (fun i : I ↦ B i w) = ∑ i : I, B i w • Pi.single i (1 : ℝ) := by
      funext x
      simp only [Finset.univ_eq_attach, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
        smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_attach, ↓reduceIte]
    rw [this, map_sum]
    simp_rw [map_smul, smul_eq_mul, mul_comm]
  rw [h1, h2, covariance_const_mul_left, covariance_fun_sum_right
    (X := fun i : I ↦ fun w ↦ L₂ (Pi.single i 1) * B i w)
    (fun i ↦ ((hB.isGaussianProcess.hasGaussianLaw_eval i).memLp_two).const_mul _) (Lp.memLp Z)]
  simp only [covariance_const_mul_right, covariance_coe_eval hB hZ, horth, mul_zero,
    Finset.sum_const_zero]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
  [BorelSpace W] [SecondCountableTopology W] in
/-- The sigma-algebra generated by finitely many Brownian coordinates is the comap of the
finite vector. -/
theorem comap_finset_eq (B : ℝ≥0 → W → ℝ) (I : Finset ℝ≥0) :
    MeasurableSpace.comap (fun w ↦ fun i : I ↦ B i w) MeasurableSpace.pi =
      ⨆ i : I, MeasurableSpace.comap (B i) (borel ℝ) := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_congr fun i ↦ ?_
  rw [MeasurableSpace.comap_comp]
  rfl

/-- **Independence from the whole Brownian sigma-algebra**: `Z ∈ Space P` orthogonal to all
Brownian coordinates is independent of `σ(B)`. -/
theorem indep_comap_processMeasurableSpace (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) {Z : RandomL2 P} (hZ : Z ∈ Space P)
    (horth : ∀ t, ⟪Z, brownianLp hB t⟫_ℝ = 0) :
    Indep (processMeasurableSpace B) (MeasurableSpace.comap (Z : W → ℝ) (borel ℝ)) P := by
  have : IsProbabilityMeasure P := inferInstance
  have hfin : ∀ I : Finset ℝ≥0, Indep (⨆ i : I, MeasurableSpace.comap (B i) (borel ℝ))
      (MeasurableSpace.comap (Z : W → ℝ) (borel ℝ)) P := fun I ↦ by
    rw [← comap_finset_eq]
    exact ((IndepFun_iff_Indep _ _ _).mp (indepFun_of_orthogonal hB L hL hZ horth I)).symm
  have hdir : Directed (· ≤ ·) fun I : Finset ℝ≥0 ↦
      ⨆ i : I, MeasurableSpace.comap (B i) (borel ℝ) := by
    intro I J
    refine ⟨I ∪ J, ?_, ?_⟩
    · exact iSup_le fun i ↦ le_iSup_of_le ⟨i.1, Finset.mem_union_left _ i.2⟩ le_rfl
    · exact iSup_le fun i ↦ le_iSup_of_le ⟨i.1, Finset.mem_union_right _ i.2⟩ le_rfl
  have hmeas : ∀ t, Measurable (B t) := fun t ↦ by
    have : B t = fun w ↦ L t w := funext (hL t)
    rw [this]
    exact (L t).continuous.measurable
  have hle : ∀ I : Finset ℝ≥0,
      (⨆ i : I, MeasurableSpace.comap (B i) (borel ℝ)) ≤ ‹MeasurableSpace W› :=
    fun I ↦ iSup_le fun i ↦ (hmeas i).comap_le
  have hZle : MeasurableSpace.comap (Z : W → ℝ) (borel ℝ) ≤ ‹MeasurableSpace W› :=
    (Lp.stronglyMeasurable Z).measurable.comap_le
  have h := indep_iSup_of_directed_le hfin hle hZle hdir
  have hproc : processMeasurableSpace B =
      ⨆ I : Finset ℝ≥0, ⨆ i : I, MeasurableSpace.comap (B i) (borel ℝ) := by
    unfold processMeasurableSpace
    rw [iSup_eq_iSup_finset]
    exact iSup_congr fun I ↦ (iSup_subtype (p := (· ∈ I))
      (f := fun t ↦ MeasurableSpace.comap (B t) (borel ℝ))).symm ▸ rfl
  rw [hproc]
  exact h

/-- **Orthogonal to all Brownian coordinates ⇒ zero**: on a Brownian-generated Gaussian space,
an element of the Cameron--Martin space orthogonal to every coordinate vanishes. -/
theorem eq_zero_of_mem_space_of_orthogonal (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    {Z : RandomL2 P} (hZ : Z ∈ Space P) (horth : ∀ t, ⟪Z, brownianLp hB t⟫_ℝ = 0) : Z = 0 := by
  have hind := indep_comap_processMeasurableSpace hB L hL hZ horth
  rw [hgen] at hind
  have hself : IndepFun (Z : W → ℝ) (Z : W → ℝ) P :=
    (IndepFun_iff_Indep _ _ _).mpr
      (indep_of_indep_of_le_left hind (Lp.stronglyMeasurable Z).measurable.comap_le)
  have hsq := hself.integral_fun_mul_eq_mul_integral (Lp.aestronglyMeasurable Z)
    (Lp.aestronglyMeasurable Z)
  rw [integral_coe_eq_zero P ⟨Z, hZ⟩, mul_zero] at hsq
  have hinner : ⟪Z, Z⟫_ℝ = 0 := by
    rw [L2.inner_def, ← hsq]
    apply integral_congr_ae
    filter_upwards with w
    simp only [inner_self_eq_norm_sq_to_K, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq, sq,
      abs_mul_abs_self]
  exact inner_self_eq_zero.mp hinner

/-- The first chaos is a closed subspace of `L²(P)`, hence complete. -/
instance instCompleteSpaceFirstChaos (hB : IsPreBrownianReal B P) : CompleteSpace (firstChaos hB) :=
  inferInstanceAs
    (CompleteSpace ((Submodule.span ℝ (Set.range (brownianLp hB))).topologicalClosure))

/-- **The Cameron--Martin space is the first chaos of the coordinate process** on a
Brownian-generated Gaussian space whose coordinates are continuous linear functionals. -/
theorem space_eq_firstChaos (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) :
    Space P = firstChaos hB := by
  refine le_antisymm (fun Z hZ ↦ ?_) (firstChaos_le_space hB L hL)
  set K := firstChaos hB with hK
  have hproj : K.starProjection Z ∈ Space P :=
    firstChaos_le_space hB L hL (K.starProjection_apply_mem Z)
  have hmem : Z - K.starProjection Z ∈ Space P := Submodule.sub_mem _ hZ hproj
  have horth : ∀ t, ⟪Z - K.starProjection Z, brownianLp hB t⟫_ℝ = 0 := fun t ↦
    (Submodule.mem_orthogonal' K _).mp (K.sub_starProjection_mem_orthogonal Z) _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t, rfl⟩))
  have h0 := eq_zero_of_mem_space_of_orthogonal hB L hL hgen hmem horth
  rw [sub_eq_zero] at h0
  rw [h0]
  exact K.starProjection_apply_mem Z

/-- **The Clark--Ocone time derivative on a Brownian-generated Gaussian space** with
linear-functional coordinates: an isometry `L²(P; Space P) → L²(ℝ≥0 × W)`. -/
noncomputable def timeDerivative (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) :
    Lp (Space P) 2 P →ₗᵢ[ℝ] Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P) :=
  timeDerivativeOfEq hB (space_eq_firstChaos hB L hL hgen)

/-- **The time derivative is an isometric equivalence** `L²(P; Space P) ≃ L²(ℝ≥0 × W)`. -/
noncomputable def timeDerivativeEquiv (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) :
    Lp (Space P) 2 P ≃ₗᵢ[ℝ] Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P) :=
  ((compLpEquiv (LinearIsometryEquiv.ofEq _ _ (space_eq_firstChaos hB L hL hgen))).trans
    (compLpEquiv (wienerIntegralEquiv hB).symm)).trans fubiniEquiv

/-- **The time derivative commutes with bounded multipliers**:
`Dₜ (G • U) = G(ω) Dₜ U` for bounded measurable `G : W → ℝ`. -/
theorem timeDerivative_boundedSMul (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) {G : W → ℝ}
    (hG : AEStronglyMeasurable G P) {C : ℝ} (hC : ∀ x, |G x| ≤ C) (U : Lp (Space P) 2 P) :
    timeDerivative hB L hL hgen (boundedSMul hG hC U) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure) hG)
        (fun p ↦ hC p.2) (timeDerivative hB L hL hgen U) := by
  unfold timeDerivative timeDerivativeOfEq timeDerivativeOfFirstChaos
  simp only [LinearIsometry.coe_comp, Function.comp_apply]
  rw [compLpₗᵢ_boundedSMul, compLpₗᵢ_boundedSMul, fubiniLift_boundedSMul]

theorem timeDerivativeEquiv_apply (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) (U : Lp (Space P) 2 P) :
    timeDerivativeEquiv hB L hL hgen U = timeDerivative hB L hL hgen U := rfl

/-! ### The textbook formula for cylindrical functionals

For `F = f (B t₁, …, B tₙ)` the Malliavin derivative is `∑ᵢ ∂ᵢ f (B) • ofDual (L tᵢ)`
(`mderiv_cylindrical`), and under the time derivative each generator `ofDual (L tᵢ)` becomes the
interval indicator `1_{(0, tᵢ]}`, giving `Dₜ F = ∑ᵢ ∂ᵢ f (B t₁, …, B tₙ) 1_{t ≤ tᵢ}`. -/

/-- The time derivative of a rank-one element `G • h` (`h` in the Cameron--Martin space) is the
tensor `J₁⁻¹ h ⊗ G`. -/
theorem timeDerivative_smulLp (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) (h : Space P) (G : Lp ℝ 2 P) :
    timeDerivative hB L hL hgen (smulLp h G) =
      tensor ((wienerIntegralEquiv hB).symm
        (LinearIsometryEquiv.ofEq _ _ (space_eq_firstChaos hB L hL hgen) h)) G := by
  unfold timeDerivative timeDerivativeOfEq timeDerivativeOfFirstChaos
  simp only [LinearIsometry.coe_comp, Function.comp_apply]
  rw [compLpₗᵢ_smulLp, compLpₗᵢ_smulLp, fubiniLift_smulLp]
  rfl

/-- `J₁⁻¹` of the Cameron--Martin generator `ofDual P (L t)` is the interval indicator
`1_{(0, t]}`. -/
theorem wienerIntegralEquiv_symm_ofDual (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (t : ℝ≥0) :
    (wienerIntegralEquiv hB).symm
        (LinearIsometryEquiv.ofEq _ _ (space_eq_firstChaos hB L hL hgen) (ofDual P (L t))) =
      intervalIndicator t := by
  apply (wienerIntegralEquiv hB).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [LinearIsometryEquiv.coe_ofEq_apply, coe_wienerIntegralEquiv_apply,
    wienerIntegral_intervalIndicator, brownianLp_eq_ofDual hB L hL t]

variable (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- A bounded `C¹` function of finitely many Brownian coordinates is smooth bounded. -/
theorem isSmoothBounded_cylinder {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ C, ∀ y, |f y| ≤ C) (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) :
    IsSmoothBounded (fun w ↦ f (fun i ↦ B (t i) w)) := by
  have : (fun w ↦ f (fun i ↦ B (t i) w)) = fun w ↦ f (fun i ↦ L (t i) w) := by
    funext w
    simp only [hL]
  rw [this]
  exact IsSmoothBounded.cylindrical f hf hb hb' _

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The partial derivative `∂ᵢ f (B t₁, …, B tₙ)` is square integrable. -/
theorem memLp_cylinderPartial {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) (i : Fin n) :
    MemLp (fun w ↦ fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1)) 2 P := by
  obtain ⟨C, hC⟩ := hb'
  have hcont : Continuous fun w ↦ fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1) := by
    have : (fun w ↦ fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1)) =
        fun w ↦ fderiv ℝ f (fun j ↦ L (t j) w) (Pi.single i 1) := by
      funext w
      simp only [hL]
    rw [this]
    exact ((hf.continuous_fderiv one_ne_zero).comp
      (continuous_pi fun j ↦ (L (t j)).continuous)).clm_apply continuous_const
  refine MemLp.of_bound hcont.aestronglyMeasurable (C * ‖(Pi.single i 1 : Fin n → ℝ)‖)
    (Filter.Eventually.of_forall fun w ↦ ?_)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))

/-- The partial derivative `∂ᵢ f (B t₁, …, B tₙ)` as an element of `L²(P)`. -/
noncomputable def cylinderPartial {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) (i : Fin n) : Lp ℝ 2 P :=
  (memLp_cylinderPartial L hL f hf hb' t i).toLp _

/-- The Malliavin derivative of a cylindrical functional in `L²(P; H)`:
`D f(B t₁, …, B tₙ) = ∑ᵢ ∂ᵢ f (B) • ofDual (L tᵢ)`. -/
theorem mderivLp_cylinder {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ C, ∀ y, |f y| ≤ C) (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) :
    (isSmoothBounded_cylinder L hL f hf hb hb' t).mderivLp P =
      ∑ i, smulLp (ofDual P (L (t i))) (cylinderPartial L hL f hf hb' t i) := by
  apply Lp.ext
  have hpart : ∀ᵐ w ∂P, ∀ i : Fin n,
      (smulLp (ofDual P (L (t i))) (cylinderPartial L hL f hf hb' t i) : W → Space P) w =
        fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1) • ofDual P (L (t i)) :=
    ae_all_iff.2 fun i ↦ by
      filter_upwards [coeFn_smulLp (ofDual P (L (t i))) (cylinderPartial L hL f hf hb' t i),
        MemLp.coeFn_toLp (memLp_cylinderPartial L hL f hf hb' t i)] with w h1 h2
      rw [h1, cylinderPartial, h2]
  filter_upwards [MemLp.coeFn_toLp ((isSmoothBounded_cylinder L hL f hf hb hb' t).memLp_mderiv P 2),
    Lp.coeFn_finsetSum Finset.univ
      (fun i ↦ smulLp (ofDual P (L (t i))) (cylinderPartial L hL f hf hb' t i)), hpart]
    with w h1 h2 h3
  rw [IsSmoothBounded.mderivLp, h1, h2, Finset.sum_apply]
  simp_rw [h3]
  have hF : (fun w ↦ f (fun i ↦ B (t i) w)) = fun w ↦ f (fun i ↦ L (t i) w) := by
    funext w
    simp only [hL]
  have hBL : (fun j ↦ B (t j) w) = fun j ↦ L (t j) w := by
    funext j
    simp only [hL]
  rw [hF, mderiv_cylindrical P f (fun i ↦ L (t i)) w ((hf.differentiable one_ne_zero) _), hBL]

/-- **The textbook Malliavin derivative of a cylindrical functional**:
`Dₜ f(B t₁, …, B tₙ) = ∑ᵢ ∂ᵢ f (B t₁, …, B tₙ) · 1_{(0, tᵢ]}(t)` in `L²(ℝ≥0 × W)`. -/
theorem timeDerivative_mderivLp_cylinder (hgen : IsWienerGenerated B) {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hb : ∃ C, ∀ y, |f y| ≤ C)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) :
    timeDerivative hB L hL hgen ((isSmoothBounded_cylinder L hL f hf hb hb' t).mderivLp P) =
      ∑ i, tensor (intervalIndicator (t i)) (cylinderPartial L hL f hf hb' t i) := by
  rw [mderivLp_cylinder L hL f hf hb hb' t]
  have hsum := map_sum (timeDerivative hB L hL hgen).toLinearMap
    (fun i ↦ smulLp (ofDual P (L (t i))) (cylinderPartial L hL f hf hb' t i)) Finset.univ
  simp only [LinearIsometry.coe_toLinearMap] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [timeDerivative_smulLp hB L hL hgen, wienerIntegralEquiv_symm_ofDual hB L hL hgen]

end CameronMartin

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
