/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.NaturalItoRange
import LeanPool.Malliavin.Malliavin.ClarkOconeExamples

/-!
# Malliavin--Itô duality on the first chaos

The full Malliavin--Itô duality needed for Clark--Ocone remains an analytic input. This file
proves it unconditionally when the terminal functional is in the first chaos. More precisely,
for `F = ∫ g dB` and **every** random predictable `U`, not just deterministic `U`,

`inner (F - E[F]) (naturalItoIntegral U) = inner (predictableProjection (Dₜ F)) U`.

Both sides reduce to the predictable-space inner product of `U` with the deterministic embedding
of `g`: `Dₜ F = g`, predictable projection fixes deterministic processes, and the deterministic
restriction of `naturalItoIntegral` is the Wiener integral. Thus the unresolved duality begins
beyond the first chaos. The theorem `naturalClarkOcone_wienerIntegral` also records the resulting
unconditional Clark--Ocone representation on this subspace.

Once martingale representation is assumed, the general duality identity is equivalent to the
direct integrand identification
`bestNaturalItoIntegrand (F - E[F]) = predictableProjection (Dₜ F)`.
`ClarkOconeFamily.ofNaturalItoBestIntegrand` therefore offers a version of the family constructor
whose final input is this textbook statement instead of an inner-product duality axiom.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- A Wiener integral has zero expectation, stated in the `RandomL2` API used by Clark--Ocone. -/
@[simp]
theorem expectationL2_wienerIntegral
    (hB : IsPreBrownianReal B P) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    expectationL2 (wienerIntegral hB g) = 0 := by
  unfold expectationL2
  rw [integral_wienerIntegral]
  exact map_zero _

/-- On the first chaos, the canonical best Itô integrand is exactly the predictable projection
of the time-realized Malliavin derivative. Both are the deterministic kernel `g`. -/
theorem bestNaturalItoIntegrand_centeredWienerIntegral_eq_predictableProjection
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    bestNaturalItoIntegrand hB hsm hnat (centeredWienerIntegral hB g) =
      predictableProjection 𝓅
        (timeDerivative hB L hL hgen
          (mderivClosure P (wienerIntegral hB g))) := by
  rw [bestNaturalItoIntegrand_centeredWienerIntegral,
    timeDerivative_mderivClosure_wienerIntegral,
    ← deterministicTimeEmbedding_eq_tensor, predictableProjection_deterministic]

/-- **Unconditional Clark--Ocone on the first chaos.** The predictable projection of the
Malliavin derivative of a Wiener integral integrates back to that same Wiener integral under the
constructed natural-filtration Itô operator; no martingale-representation assumption is needed. -/
theorem naturalClarkOcone_wienerIntegral
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    wienerIntegral hB g = expectationL2 (wienerIntegral hB g) +
      naturalItoIntegral hB hsm hnat
        (predictableProjection 𝓅
          (timeDerivative hB L hL hgen
            (mderivClosure P (wienerIntegral hB g)))) := by
  rw [expectationL2_wienerIntegral, zero_add,
    timeDerivative_mderivClosure_wienerIntegral,
    ← deterministicTimeEmbedding_eq_tensor, predictableProjection_deterministic,
    naturalItoIntegral_deterministic]

/-- Unconditional Clark--Ocone representation for an arbitrary element of the first chaos. -/
theorem naturalClarkOcone_firstChaos
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (Z : firstChaos hB) :
    (Z : RandomL2 P) = expectationL2 (Z : RandomL2 P) +
      naturalItoIntegral hB hsm hnat
        (predictableProjection 𝓅
          (timeDerivative hB L hL hgen
            (mderivClosure P (Z : RandomL2 P)))) := by
  let g := (wienerIntegralEquiv hB).symm Z
  have hZ : (Z : RandomL2 P) = wienerIntegral hB g :=
    (wienerIntegral_wienerIntegralEquiv_symm_apply hB Z).symm
  rw [hZ]
  exact naturalClarkOcone_wienerIntegral hB L hL hgen hsm hnat g

/-- On the whole first chaos, the canonical best integrand is the predictable projection of the
Malliavin derivative, without any martingale-representation assumption. -/
theorem bestNaturalItoIntegrand_firstChaos_eq_predictableProjection
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (Z : firstChaos hB) :
    bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 (Z : RandomL2 P)) =
      predictableProjection 𝓅
        (timeDerivative hB L hL hgen
          (mderivClosure P (Z : RandomL2 P))) := by
  let g := (wienerIntegralEquiv hB).symm Z
  have hZ : (Z : RandomL2 P) = wienerIntegral hB g :=
    (wienerIntegral_wienerIntegralEquiv_symm_apply hB Z).symm
  rw [hZ]
  have hcentered : centeredPartL2 (wienerIntegral hB g) = centeredWienerIntegral hB g := by
    apply Subtype.ext
    simp only [centeredPartL2_coe, expectationL2_wienerIntegral, sub_zero,
      centeredWienerIntegral_coe]
  rw [hcentered]
  exact bestNaturalItoIntegrand_centeredWienerIntegral_eq_predictableProjection
    hB L hL hgen hsm hnat g

/-- Equivalently, on a Wiener-integral `D12` functional the canonical best integrand agrees with
the `predictableDerivative` used in the abstract Clark--Ocone statement. -/
theorem bestNaturalItoIntegrand_centeredWienerIntegral_eq_predictableDerivative
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓅)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    bestNaturalItoIntegrand C.isPreBrownian C.stronglyMeasurable
        C.naturalFiltration (centeredWienerIntegral C.isPreBrownian g) =
      predictableDerivative C
        (wienerIntegralD12 C.isPreBrownian C.coordinate
          C.coordinate_apply C.generated g) := by
  rw [bestNaturalItoIntegrand_centeredWienerIntegral,
    predictableDerivative_wienerIntegralD12]

/-- **Malliavin--Itô duality for the constructed integral on the first chaos**, against an
arbitrary predictable integrand. -/
theorem naturalItoDuality_wienerIntegral
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure)
    (U : PredictableProcessL2 𝓅 P) :
    inner ℝ (wienerIntegral hB g - expectationL2 (wienerIntegral hB g))
        (naturalItoIntegral hB hsm hnat U) =
      inner ℝ (predictableProjection 𝓅
        (timeDerivative hB L hL hgen
          (mderivClosure P (wienerIntegral hB g)))) U := by
  rw [expectationL2_wienerIntegral, sub_zero,
    timeDerivative_mderivClosure_wienerIntegral,
    ← deterministicTimeEmbedding_eq_tensor, predictableProjection_deterministic]
  calc
    inner ℝ (wienerIntegral hB g) (naturalItoIntegral hB hsm hnat U) =
        inner ℝ (naturalItoIntegral hB hsm hnat U) (wienerIntegral hB g) :=
      real_inner_comm _ _
    _ = inner ℝ U (deterministicPredictableEmbedding 𝓅 g) :=
      inner_naturalItoIntegral_wienerIntegral hB hsm hnat U g
    _ = inner ℝ (deterministicPredictableEmbedding 𝓅 g) U :=
      real_inner_comm _ _

/-- Malliavin--Itô duality for an arbitrary first-chaos terminal variable against every
predictable integrand. -/
theorem naturalItoDuality_firstChaos
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (Z : firstChaos hB) (U : PredictableProcessL2 𝓅 P) :
    inner ℝ ((Z : RandomL2 P) - expectationL2 (Z : RandomL2 P))
        (naturalItoIntegral hB hsm hnat U) =
      inner ℝ (predictableProjection 𝓅
        (timeDerivative hB L hL hgen
          (mderivClosure P (Z : RandomL2 P)))) U := by
  let g := (wienerIntegralEquiv hB).symm Z
  have hZ : (Z : RandomL2 P) = wienerIntegral hB g :=
    (wienerIntegral_wienerIntegralEquiv_symm_apply hB Z).symm
  rw [hZ]
  exact naturalItoDuality_wienerIntegral hB L hL hgen hsm hnat g U

/-- The preceding identity in exactly the `D12` form used by the full duality contract. -/
theorem naturalItoDuality_wienerIntegralD12
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure)
    (U : PredictableProcessL2 𝓅 P) :
    let F := wienerIntegralD12 hB L hL hgen g
    inner ℝ (F.1 - expectationL2 F.1) (naturalItoIntegral hB hsm hnat U) =
      inner ℝ (predictableProjection 𝓅
        (timeDerivative hB L hL hgen (mderivD12 P F))) U := by
  dsimp only
  rw [mderivD12_apply]
  exact naturalItoDuality_wienerIntegral hB L hL hgen hsm hnat g U

/-- Assuming martingale representation, Malliavin--Itô duality for `F` is equivalent to the
textbook integrand identification: the canonical inverse-Itô integrand of `F - E[F]` equals the
predictable projection of its time-realized Malliavin derivative. -/
theorem naturalItoDuality_iff_bestNaturalItoIntegrand_eq_predictableProjection
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (F : D12 P) :
    (∀ U : PredictableProcessL2 𝓅 P,
      inner ℝ (F.1 - expectationL2 F.1)
          (naturalItoIntegral hB hsm hnat U) =
        inner ℝ (predictableProjection 𝓅
          (timeDerivative hB L hL hgen (mderivD12 P F))) U) ↔
      bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
        predictableProjection 𝓅
          (timeDerivative hB L hL hgen (mderivD12 P F)) := by
  let V := predictableProjection 𝓅
    (timeDerivative hB L hL hgen (mderivD12 P F))
  let Uₑ := bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1)
  have hcenter : naturalItoIntegral hB hsm hnat Uₑ =
      F.1 - expectationL2 F.1 := by
    have h := centeredNaturalItoIntegral_bestNaturalItoIntegrand
      hB hsm hnat hMRT (centeredPartL2 F.1)
    exact congrArg Subtype.val h
  constructor
  · intro hDuality
    apply ext_inner_right ℝ
    intro U
    calc
      inner ℝ Uₑ U =
          inner ℝ (naturalItoIntegral hB hsm hnat Uₑ)
            (naturalItoIntegral hB hsm hnat U) :=
        (inner_naturalItoIntegral hB hsm hnat Uₑ U).symm
      _ = inner ℝ (F.1 - expectationL2 F.1)
          (naturalItoIntegral hB hsm hnat U) := by rw [hcenter]
      _ = inner ℝ V U := hDuality U
  · intro hbest U
    change Uₑ = V at hbest
    calc
      inner ℝ (F.1 - expectationL2 F.1)
          (naturalItoIntegral hB hsm hnat U) =
          inner ℝ (naturalItoIntegral hB hsm hnat Uₑ)
            (naturalItoIntegral hB hsm hnat U) := by rw [hcenter]
      _ = inner ℝ Uₑ U := inner_naturalItoIntegral hB hsm hnat Uₑ U
      _ = inner ℝ V U := by rw [hbest]

/-- **Concrete conditional Clark--Ocone formula.** This statement uses the constructed natural
Itô integral directly, with no abstract family: MRT supplies the canonical inverse integrand, and
the remaining textbook identification says that integrand is `predictableProjection (DₜF)`. -/
theorem naturalClarkOcone
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (F : D12 P)
    (hBest : bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
      predictableProjection 𝓅
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) :
    F.1 = expectationL2 F.1 + naturalItoIntegral hB hsm hnat
      (predictableProjection 𝓅
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) := by
  rw [← hBest]
  exact naturalMartingaleRepresentation_canonical hB hsm hnat hMRT F.1

/-- Centered form of the concrete conditional Clark--Ocone formula. -/
theorem sub_expectationL2_eq_naturalItoIntegral_predictableProjection
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (F : D12 P)
    (hBest : bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
      predictableProjection 𝓅
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) :
    F.1 - expectationL2 F.1 = naturalItoIntegral hB hsm hnat
      (predictableProjection 𝓅
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) := by
  exact sub_eq_iff_eq_add'.mpr
    (naturalClarkOcone hB coordinate coordinate_apply generated hsm hnat hMRT F hBest)

/-- Build a full Clark--Ocone family from martingale representation and the textbook
identification of the canonical inverse-Itô integrand with the predictable Malliavin derivative.
This is equivalent to supplying Malliavin--Itô duality, but exposes the remaining hypothesis in
the form used by the Clark--Ocone formula itself. -/
noncomputable def ClarkOconeFamily.ofNaturalItoBestIntegrand
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (hBest : ∀ F : D12 P,
      bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
        predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) :
    ClarkOconeFamily B P 𝓅 :=
  ClarkOconeFamily.ofNaturalIto (W := W) (P := P) (B := B)
    hB coordinate coordinate_apply generated hsm hnat hMRT fun F U ↦
      (naturalItoDuality_iff_bestNaturalItoIntegrand_eq_predictableProjection
        hB coordinate coordinate_apply generated hsm hnat hMRT F).mpr (hBest F) U

/-- The best-integrand constructor automatically has the textbook Brownian value on every
elementary adapted process. -/
theorem ClarkOconeFamily.ofNaturalItoBestIntegrand_isBrownianOnElementary
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (hBest : ∀ F : D12 P,
      bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
        predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) :
    (ClarkOconeFamily.ofNaturalItoBestIntegrand (W := W) (P := P) (B := B)
      hB coordinate coordinate_apply generated hsm hnat hMRT hBest
      ).IsBrownianOnElementary := by
  apply ClarkOconeFamily.isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral
  rfl

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
