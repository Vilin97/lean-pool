/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.ItoConsequences

/-!
# The closed range of the constructed Itô integral

This packages the natural Itô terminal values as closed subspaces of ambient and centered
`L²(P)`, constructs the orthogonal projection onto the centered range, and restates martingale
representation as triviality of the corresponding orthogonal complement.
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

/-! ## The ambient closed range -/

/-- The subspace of terminal `L²(P)` random variables obtained from the constructed natural Itô
integral. -/
noncomputable def naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) : Submodule ℝ (RandomL2 P) :=
  LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap

omit [CompleteSpace W] [BorelSpace W] in
/-- The natural Itô terminal-value subspace is closed in `L²(P)`. -/
theorem isClosed_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    IsClosed (naturalItoRange hB hsm hnat : Set (RandomL2 P)) := by
  simpa only [naturalItoRange] using isClosed_range_naturalItoIntegral hB hsm hnat

omit [CompleteSpace W] [BorelSpace W] in
/-- Every natural Itô terminal value is centered. -/
theorem naturalItoRange_le_expectationMap_ker
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    naturalItoRange hB hsm hnat ≤ (CameronMartin.expectationMap P).ker := by
  simpa only [naturalItoRange] using
    range_naturalItoIntegral_le_expectationMap_ker hB hsm hnat

omit [CompleteSpace W] [BorelSpace W] in
/-- The natural Itô terminal-value subspace contains the full Gaussian first chaos. -/
theorem firstChaos_le_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    firstChaos hB ≤ naturalItoRange hB hsm hnat := by
  simpa only [naturalItoRange] using
    firstChaos_le_range_naturalItoIntegral hB hsm hnat

/-! ## The range inside centered `L²` -/

/-- The same terminal-value range, intrinsically regarded as a subspace of centered `L²(P)`. -/
noncomputable def centeredNaturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    Submodule ℝ (CameronMartin.expectationMap P).ker :=
  LinearMap.range (centeredNaturalItoIntegralIsometry hB hsm hnat).toLinearMap

omit [CompleteSpace W] [BorelSpace W] in
/-- The centered natural Itô range is closed. -/
theorem isClosed_centeredNaturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    IsClosed (centeredNaturalItoRange hB hsm hnat :
      Set (CameronMartin.expectationMap P).ker) := by
  let _ : Fact (𝓅.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × W))) :=
    ⟨predictable_le_prod 𝓅⟩
  exact (centeredNaturalItoIntegralIsometry hB hsm hnat).isometry
    |>.isClosedEmbedding.isClosed_range

omit [CompleteSpace W] [BorelSpace W] in
/-- Membership in the intrinsic centered range is equivalent to ambient membership in the
natural Itô range. -/
theorem mem_centeredNaturalItoRange_iff
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker) :
    G ∈ centeredNaturalItoRange hB hsm hnat ↔
      (G : RandomL2 P) ∈ naturalItoRange hB hsm hnat := by
  constructor
  · rintro ⟨U, hU⟩
    refine ⟨U, ?_⟩
    have h := congrArg Subtype.val hU
    change naturalItoIntegral hB hsm hnat U = (G : RandomL2 P) at h
    exact h
  · rintro ⟨U, hU⟩
    refine ⟨U, Subtype.ext ?_⟩
    change naturalItoIntegral hB hsm hnat U = (G : RandomL2 P)
    exact hU

/-- Orthogonal projection from centered `L²(P)` onto the closed centered natural Itô range. -/
noncomputable def centeredNaturalItoRangeProjection
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    (CameronMartin.expectationMap P).ker →L[ℝ]
      centeredNaturalItoRange hB hsm hnat := by
  let _ : CompleteSpace (centeredNaturalItoRange hB hsm hnat) :=
    (isClosed_centeredNaturalItoRange hB hsm hnat).completeSpace_coe
  exact (centeredNaturalItoRange hB hsm hnat).orthogonalProjectionOnto

/-- The constructed Itô isometry, with codomain restricted to its intrinsic centered range. -/
noncomputable def centeredNaturalItoRangeEquiv
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    PredictableProcessL2 𝓅 P ≃ₗᵢ[ℝ] centeredNaturalItoRange hB hsm hnat :=
  (centeredNaturalItoIntegralIsometry hB hsm hnat).equivRange

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The centered part `G - E[G]`, intrinsically regarded as an element of the expectation
kernel. -/
noncomputable def centeredPartL2 (G : RandomL2 P) :
    (CameronMartin.expectationMap P).ker :=
  ⟨G - expectationL2 G, by
    rw [LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr (expectationMap_expectationL2 (P := P) G).symm⟩

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The ambient value of `centeredPartL2 G` is `G - E[G]`. -/
@[simp]
theorem centeredPartL2_coe (G : RandomL2 P) :
    (centeredPartL2 G : RandomL2 P) = G - expectationL2 G :=
  rfl

/-- The canonical best predictable integrand for a centered terminal variable: orthogonally
project onto the closed natural Itô range, then invert the Itô isometry on that range. -/
noncomputable def bestNaturalItoIntegrand
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    (CameronMartin.expectationMap P).ker →L[ℝ] PredictableProcessL2 𝓅 P :=
  (centeredNaturalItoRangeEquiv hB hsm hnat).toContinuousLinearEquiv.symm
    |>.toContinuousLinearMap.comp (centeredNaturalItoRangeProjection hB hsm hnat)

/-- The canonical best predictable integrand of an arbitrary terminal variable, obtained by
first subtracting its expectation. -/
noncomputable def bestNaturalItoIntegrandOfRandom
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : RandomL2 P) : PredictableProcessL2 𝓅 P :=
  bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 G)

omit [CompleteSpace W] [BorelSpace W] in
/-- Integrating the best integrand gives exactly the ambient value of the range projection. -/
theorem naturalItoIntegral_bestNaturalItoIntegrand
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker) :
    naturalItoIntegral hB hsm hnat (bestNaturalItoIntegrand hB hsm hnat G) =
      (((centeredNaturalItoRangeProjection hB hsm hnat G :
        centeredNaturalItoRange hB hsm hnat) :
          (CameronMartin.expectationMap P).ker) : RandomL2 P) := by
  change naturalItoIntegral hB hsm hnat
      ((centeredNaturalItoRangeEquiv hB hsm hnat).symm
        (centeredNaturalItoRangeProjection hB hsm hnat G)) = _
  have h := (centeredNaturalItoRangeEquiv hB hsm hnat).apply_symm_apply
    (centeredNaturalItoRangeProjection hB hsm hnat G)
  exact congrArg (fun X : centeredNaturalItoRange hB hsm hnat ↦
    ((X : (CameronMartin.expectationMap P).ker) : RandomL2 P)) h

omit [CompleteSpace W] [BorelSpace W] in
/-- The best-integrand operator is contractive. -/
theorem norm_bestNaturalItoIntegrand_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker) :
    ‖bestNaturalItoIntegrand hB hsm hnat G‖ ≤ ‖G‖ := by
  change ‖(centeredNaturalItoRangeEquiv hB hsm hnat).symm
    (centeredNaturalItoRangeProjection hB hsm hnat G)‖ ≤ ‖G‖
  rw [(centeredNaturalItoRangeEquiv hB hsm hnat).symm.norm_map]
  let _ : CompleteSpace (centeredNaturalItoRange hB hsm hnat) :=
    (isClosed_centeredNaturalItoRange hB hsm hnat).completeSpace_coe
  simpa only [centeredNaturalItoRangeProjection] using
    (centeredNaturalItoRange hB hsm hnat).norm_orthogonalProjectionOnto_apply_le G

omit [CompleteSpace W] [BorelSpace W] in
/-- On an actual natural Itô terminal value, the best-integrand operator recovers its unique
predictable integrand. -/
@[simp]
theorem bestNaturalItoIntegrand_centeredNaturalItoIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓅 P) :
    bestNaturalItoIntegrand hB hsm hnat
      (centeredNaturalItoIntegralIsometry hB hsm hnat U) = U := by
  change (centeredNaturalItoRangeEquiv hB hsm hnat).symm
    (centeredNaturalItoRangeProjection hB hsm hnat
      (centeredNaturalItoIntegralIsometry hB hsm hnat U)) = U
  let _ : CompleteSpace (centeredNaturalItoRange hB hsm hnat) :=
    (isClosed_centeredNaturalItoRange hB hsm hnat).completeSpace_coe
  have hproj : centeredNaturalItoRangeProjection hB hsm hnat
      (centeredNaturalItoIntegralIsometry hB hsm hnat U) =
        ⟨centeredNaturalItoIntegralIsometry hB hsm hnat U, ⟨U, rfl⟩⟩ := by
    simpa only [centeredNaturalItoRangeProjection] using
      (centeredNaturalItoRange hB hsm hnat).orthogonalProjectionOnto_mem_subspace_eq_self
        (⟨centeredNaturalItoIntegralIsometry hB hsm hnat U, ⟨U, rfl⟩⟩ :
          centeredNaturalItoRange hB hsm hnat)
  rw [hproj]
  exact (centeredNaturalItoRangeEquiv hB hsm hnat).symm_apply_apply U

/-- A deterministic Wiener integral intrinsically regarded as a centered terminal variable. -/
noncomputable def centeredWienerIntegral
    (hB : IsPreBrownianReal B P)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (CameronMartin.expectationMap P).ker :=
  ⟨wienerIntegral hB g, by
    rw [LinearMap.mem_ker]
    change CameronMartin.expectationMap P (wienerIntegral hB g) = 0
    rw [CameronMartin.expectationMap_apply]
    exact integral_wienerIntegral hB g⟩

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The ambient value of `centeredWienerIntegral` is the Wiener integral. -/
@[simp]
theorem centeredWienerIntegral_coe
    (hB : IsPreBrownianReal B P)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (centeredWienerIntegral hB g : RandomL2 P) = wienerIntegral hB g :=
  rfl

omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical best integrand of a first-chaos Wiener integral is exactly its deterministic
kernel, without any martingale-representation assumption. -/
theorem bestNaturalItoIntegrand_centeredWienerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    bestNaturalItoIntegrand hB hsm hnat (centeredWienerIntegral hB g) =
      deterministicPredictableEmbedding 𝓅 g := by
  have hG : centeredWienerIntegral hB g =
      centeredNaturalItoIntegralIsometry hB hsm hnat
        (deterministicPredictableEmbedding 𝓅 g) := by
    apply Subtype.ext
    rw [centeredNaturalItoIntegralIsometry_apply,
      naturalItoIntegral_deterministic]
    rfl
  rw [hG, bestNaturalItoIntegrand_centeredNaturalItoIntegral]

omit [CompleteSpace W] [BorelSpace W] in
/-- The residual after projecting a centered terminal variable is orthogonal to the entire
natural Itô range. -/
theorem sub_centeredNaturalItoRangeProjection_mem_orthogonal
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker) :
    G - (centeredNaturalItoRangeProjection hB hsm hnat G :
      (CameronMartin.expectationMap P).ker) ∈
        (centeredNaturalItoRange hB hsm hnat)ᗮ := by
  let _ : CompleteSpace (centeredNaturalItoRange hB hsm hnat) :=
    (isClosed_centeredNaturalItoRange hB hsm hnat).completeSpace_coe
  exact (centeredNaturalItoRange hB hsm hnat).sub_starProjection_mem_orthogonal G

omit [CompleteSpace W] [BorelSpace W] in
/-- Equivalently, the residual is orthogonal to the integral of every predictable process. -/
theorem inner_sub_centeredNaturalItoRangeProjection
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker)
    (U : PredictableProcessL2 𝓅 P) :
    inner ℝ (G - (centeredNaturalItoRangeProjection hB hsm hnat G :
        (CameronMartin.expectationMap P).ker))
      (centeredNaturalItoIntegralIsometry hB hsm hnat U) = 0 := by
  rw [real_inner_comm]
  exact (sub_centeredNaturalItoRangeProjection_mem_orthogonal hB hsm hnat G)
    (centeredNaturalItoIntegralIsometry hB hsm hnat U) ⟨U, rfl⟩

omit [CompleteSpace W] [BorelSpace W] in
/-- The best integrand minimizes the centered `L²` reconstruction error among all predictable
integrands. -/
theorem norm_sub_centeredNaturalItoIntegral_bestNaturalItoIntegrand_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker)
    (U : PredictableProcessL2 𝓅 P) :
    ‖G - centeredNaturalItoIntegralIsometry hB hsm hnat
        (bestNaturalItoIntegrand hB hsm hnat G)‖ ≤
      ‖G - centeredNaturalItoIntegralIsometry hB hsm hnat U‖ := by
  have hbest : centeredNaturalItoIntegralIsometry hB hsm hnat
      (bestNaturalItoIntegrand hB hsm hnat G) =
        (centeredNaturalItoRangeProjection hB hsm hnat G :
          (CameronMartin.expectationMap P).ker) := by
    apply Subtype.ext
    exact naturalItoIntegral_bestNaturalItoIntegrand hB hsm hnat G
  rw [hbest]
  let _ : CompleteSpace (centeredNaturalItoRange hB hsm hnat) :=
    (isClosed_centeredNaturalItoRange hB hsm hnat).completeSpace_coe
  have hmin := (centeredNaturalItoRange hB hsm hnat).starProjection_minimal G
  have hle : (⨅ X : centeredNaturalItoRange hB hsm hnat,
      ‖G - (X : (CameronMartin.expectationMap P).ker)‖) ≤
      ‖G - centeredNaturalItoIntegralIsometry hB hsm hnat U‖ := by
    exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩
      (⟨centeredNaturalItoIntegralIsometry hB hsm hnat U, ⟨U, rfl⟩⟩ :
        centeredNaturalItoRange hB hsm hnat)
  rw [← hmin] at hle
  simpa only [centeredNaturalItoRangeProjection,
    Submodule.starProjection_apply] using hle

omit [CompleteSpace W] [BorelSpace W] in
/-- Martingale representation is equivalent to the centered natural Itô range being the whole
centered `L²(P)` space. -/
theorem naturalMartingaleRepresentation_iff_centeredNaturalItoRange_eq_top
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      centeredNaturalItoRange hB hsm hnat = ⊤ := by
  rw [naturalMartingaleRepresentation_iff_surjective]
  exact LinearMap.range_eq_top.symm

omit [CompleteSpace W] [BorelSpace W] in
/-- Martingale representation holds exactly when no nonzero centered random variable is
orthogonal to every natural Itô terminal value. -/
theorem naturalMartingaleRepresentation_iff_centeredNaturalItoRange_orthogonal_eq_bot
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      (centeredNaturalItoRange hB hsm hnat)ᗮ = ⊥ := by
  let _ : CompleteSpace (centeredNaturalItoRange hB hsm hnat) :=
    (isClosed_centeredNaturalItoRange hB hsm hnat).completeSpace_coe
  rw [naturalMartingaleRepresentation_iff_centeredNaturalItoRange_eq_top]
  exact Submodule.orthogonal_eq_bot_iff.symm

omit [CompleteSpace W] [BorelSpace W] in
/-- Under martingale representation, the best integrand recovers every centered terminal
variable exactly. -/
theorem centeredNaturalItoIntegral_bestNaturalItoIntegrand
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (G : (CameronMartin.expectationMap P).ker) :
    centeredNaturalItoIntegralIsometry hB hsm hnat
      (bestNaturalItoIntegrand hB hsm hnat G) = G := by
  have hres := sub_centeredNaturalItoRangeProjection_mem_orthogonal hB hsm hnat G
  have horth :=
    (naturalMartingaleRepresentation_iff_centeredNaturalItoRange_orthogonal_eq_bot
      hB hsm hnat).mp hMRT
  rw [horth] at hres
  have hproj : G = (centeredNaturalItoRangeProjection hB hsm hnat G :
      (CameronMartin.expectationMap P).ker) :=
    sub_eq_zero.mp (by simpa using hres)
  apply Subtype.ext
  rw [centeredNaturalItoIntegralIsometry_apply,
    naturalItoIntegral_bestNaturalItoIntegrand]
  exact congrArg Subtype.val hproj.symm

omit [CompleteSpace W] [BorelSpace W] in
/-- Under martingale representation, the canonical best integrand gives a chosen representation
of every terminal variable, rather than merely an existential one. -/
theorem naturalMartingaleRepresentation_canonical
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (G : RandomL2 P) :
    G = expectationL2 G +
      naturalItoIntegral hB hsm hnat
        (bestNaturalItoIntegrandOfRandom hB hsm hnat G) := by
  have h := centeredNaturalItoIntegral_bestNaturalItoIntegrand
    hB hsm hnat hMRT (centeredPartL2 G)
  have hambient := congrArg Subtype.val h
  change naturalItoIntegral hB hsm hnat
    (bestNaturalItoIntegrandOfRandom hB hsm hnat G) =
      G - expectationL2 G at hambient
  rw [hambient]
  abel

omit [CompleteSpace W] [BorelSpace W] in
/-- Martingale representation holds exactly when the canonical best-integrand formula reconstructs
every terminal variable. -/
theorem naturalMartingaleRepresentation_iff_canonical
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      ∀ G : RandomL2 P,
        G = expectationL2 G + naturalItoIntegral hB hsm hnat
          (bestNaturalItoIntegrandOfRandom hB hsm hnat G) := by
  constructor
  · exact naturalMartingaleRepresentation_canonical hB hsm hnat
  · intro hCanonical G
    exact ⟨bestNaturalItoIntegrandOfRandom hB hsm hnat G, hCanonical G⟩

omit [CompleteSpace W] [BorelSpace W] in
/-- Martingale representation is also equivalent to the canonical best-integrand operator being
an exact right inverse on every centered terminal variable. -/
theorem naturalMartingaleRepresentation_iff_bestNaturalItoIntegrand_exact
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      ∀ G : (CameronMartin.expectationMap P).ker,
        centeredNaturalItoIntegralIsometry hB hsm hnat
          (bestNaturalItoIntegrand hB hsm hnat G) = G := by
  constructor
  · exact fun hMRT G ↦
      centeredNaturalItoIntegral_bestNaturalItoIntegrand hB hsm hnat hMRT G
  · intro hExact
    rw [naturalMartingaleRepresentation_iff_surjective]
    intro G
    exact ⟨bestNaturalItoIntegrand hB hsm hnat G, hExact G⟩

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
