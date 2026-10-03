/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.Directional.Transport.DirectionalMeasure
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Aleksandrov.Core

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Linear-isometry transport for Aleksandrov statement interfaces
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory Topology

namespace AleksandrovDifferentiability

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- Pull a concrete second-order expansion back from an isometric coordinate model. -/
theorem HasSecondOrderExpansionAt.of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {u : E → ℝ} {x : E} {p : F} {B : F →L[ℝ] F}
    (h : HasSecondOrderExpansionAt (u ∘ e.symm) (e x) p B) :
    HasSecondOrderExpansionAt u x (e.symm p) (linearIsometryEquivConjCLM e B) := by
  dsimp [HasSecondOrderExpansionAt] at h ⊢
  have htendsto : Filter.Tendsto (fun z : E => e z) (𝓝 0) (𝓝 0) := by
    simpa using (e.continuous.continuousAt (x := 0)).tendsto
  have hcomp := h.comp_tendsto htendsto
  refine (hcomp.congr_right ?_).congr_left ?_
  · intro z
    simp
  · intro z
    have hslope : inner ℝ p (e z) = inner ℝ (e.symm p) z := by
      simpa using (LinearIsometryEquiv.inner_map_map e (e.symm p) z)
    have hquad := inner_linearIsometryEquivConjCLM_self e B z
    simp [hslope, hquad]

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- Pull second-order differentiability back from an isometric coordinate model. -/
theorem SecondOrderDifferentiableAt.of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {u : E → ℝ} {x : E}
    (h : SecondOrderDifferentiableAt (u ∘ e.symm) (e x)) :
    SecondOrderDifferentiableAt u x := by
  rcases h with ⟨p, B, hB, hquad⟩
  exact
    ⟨e.symm p, linearIsometryEquivConjCLM e B,
      isSymmetricOperator_linearIsometryEquivConjCLM e hB,
      hquad.of_image_linearIsometryEquiv e⟩

/-- Restricted volume is preserved by a linear isometry equivalence, with the domain carried to
its image. -/
theorem map_volume_restrict_linearIsometryEquiv_image
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) :
    ((volume : Measure E).restrict Ω).map e =
      (volume : Measure F).restrict (e '' Ω) := by
  have hpre : e ⁻¹' (e '' Ω) = Ω := by
    ext x
    simp
  calc
    ((volume : Measure E).restrict Ω).map e =
        ((volume : Measure E).restrict (e ⁻¹' (e '' Ω))).map e := by
          rw [hpre]
    _ = ((volume : Measure E).map e).restrict (e '' Ω) := by
          simpa using
            (e.toMeasurableEquiv.restrict_map (volume : Measure E) (e '' Ω)).symm
    _ = (volume : Measure F).restrict (e '' Ω) := by
          rw [(LinearIsometryEquiv.measurePreserving e).map_eq]

/-- Pull the final a.e. Aleksandrov statement back from an isometric coordinate model. -/
theorem ConvexAleksandrovAEStatement.of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : ConvexAleksandrovAEStatement F (e '' Ω) (u ∘ e.symm)) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  have hΩF : IsOpen (e '' Ω) := isOpen_image_linearIsometryEquiv e hΩ
  have huF : ConvexOn ℝ (e '' Ω) (u ∘ e.symm) :=
    ConvexOn.image_linearIsometryEquiv e hu
  have hF := h hΩF huF
  have hmap :
      ((volume : Measure E).restrict Ω).map e =
        (volume : Measure F).restrict (e '' Ω) :=
    map_volume_restrict_linearIsometryEquiv_image e Ω
  have hpull :
      ∀ᵐ x ∂((volume : Measure E).restrict Ω),
        SecondOrderDifferentiableAt (u ∘ e.symm) (e x) := by
    rw [← hmap] at hF
    exact e.toMeasurableEquiv.measurableEmbedding.ae_map_iff.mp hF
  exact hpull.mono fun x hx =>
    SecondOrderDifferentiableAt.of_image_linearIsometryEquiv (e := e) hx

omit [BorelSpace F] [FiniteDimensional ℝ F] [MeasurableSpace F] in
/-- Pull a scalar slicewise statement back from an isometric coordinate model. -/
theorem DirectionalLineScalarEstimateSlicewiseStatement.of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarEstimateSlicewiseStatement F (e '' Ω) (u ∘ e.symm)) :
    DirectionalLineScalarEstimateSlicewiseStatement E Ω u := by
  intro hΩ hu x ξ
  have hΩF := isOpen_image_linearIsometryEquiv e hΩ
  have huF := ConvexOn.image_linearIsometryEquiv e hu
  have hdomain : lineDomain (e '' Ω) (e x) (e ξ) = lineDomain Ω x ξ := by
    ext t
    constructor
    · intro ht
      rcases ht with ⟨y, hy, hy_eq⟩
      have hy_point : y = x + t • ξ := by
        apply e.injective
        simpa using hy_eq
      simpa [lineDomain, ← hy_point] using hy
    · intro ht
      exact ⟨x + t • ξ, ht, by simp⟩
  have hae := h hΩF huF (e x) (e ξ)
  rw [hdomain] at hae
  exact hae.mono fun t ht => by
    have hpoint : e (x + t • ξ) = e x + t • e ξ := by
      simp
    have hmem :
        x + t • ξ ∈ directionalLineScalarEstimateSet ξ ((u ∘ e.symm) ∘ e) :=
      (mem_directionalLineScalarEstimateSet_comp_linearIsometryEquiv (e := e)).mpr
        (by simpa [hpoint] using ht)
    simpa [Function.comp_def] using hmem

omit [BorelSpace F] [FiniteDimensional ℝ F] [MeasurableSpace F] in
/-- Push a scalar slicewise statement forward to an isometric coordinate model. -/
theorem DirectionalLineScalarEstimateSlicewiseStatement.image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarEstimateSlicewiseStatement E Ω u) :
    DirectionalLineScalarEstimateSlicewiseStatement F (e '' Ω) (u ∘ e.symm) := by
  intro hΩF huF y η
  have hdomain :
      lineDomain (e '' Ω) y η = lineDomain Ω (e.symm y) (e.symm η) := by
    ext t
    constructor
    · intro ht
      rcases ht with ⟨z, hz, hz_eq⟩
      have hz_point : z = e.symm y + t • e.symm η := by
        apply e.injective
        rw [hz_eq]
        simp
      simpa [lineDomain, ← hz_point] using hz
    · intro ht
      exact ⟨e.symm y + t • e.symm η, ht, by simp⟩
  have hΩ : IsOpen Ω := by
    have hpre : IsOpen (e ⁻¹' (e '' Ω)) := hΩF.preimage e.continuous
    have hset : e ⁻¹' (e '' Ω) = Ω := by
      ext z
      simp
    rwa [hset] at hpre
  have hu : ConvexOn ℝ Ω u := by
    have hconv := ConvexOn.image_linearIsometryEquiv e.symm huF
    have hset : e.symm '' (e '' Ω) = Ω := by
      ext z
      simp
    simpa [hset, Function.comp_def] using hconv
  have hae := h hΩ hu (e.symm y) (e.symm η)
  rw [← hdomain] at hae
  exact hae.mono fun t ht => by
    have hpoint : e (e.symm y + t • e.symm η) = y + t • η := by
      simp
    have hmem :
        e (e.symm y + t • e.symm η) ∈
          directionalLineScalarEstimateSet (e (e.symm η)) (u ∘ e.symm) :=
      (mem_directionalLineScalarEstimateSet_comp_linearIsometryEquiv (e := e)).mp
        (by simpa [Function.comp_def] using ht)
    simpa [hpoint] using hmem

omit [BorelSpace F] [FiniteDimensional ℝ F] [MeasurableSpace F] in
/-- Pull a scalar quotient slicewise statement back from an isometric coordinate model. -/
theorem DirectionalLineScalarQuotientSlicewiseStatement.of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarQuotientSlicewiseStatement F (e '' Ω) (u ∘ e.symm)) :
    DirectionalLineScalarQuotientSlicewiseStatement E Ω u := by
  intro hΩ hu x ξ
  have hΩF := isOpen_image_linearIsometryEquiv e hΩ
  have huF := ConvexOn.image_linearIsometryEquiv e hu
  have hdomain : lineDomain (e '' Ω) (e x) (e ξ) = lineDomain Ω x ξ := by
    ext t
    constructor
    · intro ht
      rcases ht with ⟨y, hy, hy_eq⟩
      have hy_point : y = x + t • ξ := by
        apply e.injective
        simpa using hy_eq
      simpa [lineDomain, ← hy_point] using hy
    · intro ht
      exact ⟨x + t • ξ, ht, by simp⟩
  have hae := h hΩF huF (e x) (e ξ)
  rw [hdomain] at hae
  exact hae.mono fun t ht => by
    have hpoint : e (x + t • ξ) = e x + t • e ξ := by
      simp
    have hmem :
        x + t • ξ ∈ directionalLineScalarQuotientEstimateSet ξ ((u ∘ e.symm) ∘ e) :=
      (mem_directionalLineScalarQuotientEstimateSet_comp_linearIsometryEquiv (e := e)).mpr
        (by simpa [hpoint] using ht)
    simpa [Function.comp_def] using hmem

omit [BorelSpace F] [FiniteDimensional ℝ F] [MeasurableSpace F] in
/-- Push a scalar quotient slicewise statement forward to an isometric coordinate model. -/
theorem DirectionalLineScalarQuotientSlicewiseStatement.image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarQuotientSlicewiseStatement E Ω u) :
    DirectionalLineScalarQuotientSlicewiseStatement F (e '' Ω) (u ∘ e.symm) := by
  intro hΩF huF y η
  have hdomain :
      lineDomain (e '' Ω) y η = lineDomain Ω (e.symm y) (e.symm η) := by
    ext t
    constructor
    · intro ht
      rcases ht with ⟨z, hz, hz_eq⟩
      have hz_point : z = e.symm y + t • e.symm η := by
        apply e.injective
        rw [hz_eq]
        simp
      simpa [lineDomain, ← hz_point] using hz
    · intro ht
      exact ⟨e.symm y + t • e.symm η, ht, by simp⟩
  have hΩ : IsOpen Ω := by
    have hpre : IsOpen (e ⁻¹' (e '' Ω)) := hΩF.preimage e.continuous
    have hset : e ⁻¹' (e '' Ω) = Ω := by
      ext z
      simp
    rwa [hset] at hpre
  have hu : ConvexOn ℝ Ω u := by
    have hconv := ConvexOn.image_linearIsometryEquiv e.symm huF
    have hset : e.symm '' (e '' Ω) = Ω := by
      ext z
      simp
    simpa [hset, Function.comp_def] using hconv
  have hae := h hΩ hu (e.symm y) (e.symm η)
  rw [← hdomain] at hae
  exact hae.mono fun t ht => by
    have hpoint : e (e.symm y + t • e.symm η) = y + t • η := by
      simp
    have hmem :
        e (e.symm y + t • e.symm η) ∈
          directionalLineScalarQuotientEstimateSet (e (e.symm η)) (u ∘ e.symm) :=
      (mem_directionalLineScalarQuotientEstimateSet_comp_linearIsometryEquiv (e := e)).mp
        (by simpa [Function.comp_def] using ht)
    simpa [hpoint] using hmem

/-- Pull a directional-line scalar Fubini statement back from an isometric coordinate model. -/
theorem DirectionalLineScalarEstimateFubiniStatement.of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarEstimateFubiniStatement F (e '' Ω) (u ∘ e.symm)) :
    DirectionalLineScalarEstimateFubiniStatement E Ω u := by
  intro hΩ hu ξ
  exact measure_diff_directionalLineScalarEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) (Ω := Ω) (u := u) (v := ξ)
    (h (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu)
      (e ξ))

/-- Pull a directional-line scalar quotient Fubini statement back from an isometric coordinate
model. -/
theorem DirectionalLineScalarQuotientFubiniStatement.of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarQuotientFubiniStatement F (e '' Ω) (u ∘ e.symm)) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u := by
  intro hΩ hu ξ
  exact measure_diff_directionalLineScalarQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) (Ω := Ω) (u := u) (v := ξ)
    (h (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu)
      (e ξ))

/-- Unit-direction version of
`DirectionalLineScalarEstimateFubiniStatement.of_image_linearIsometryEquiv`. -/
theorem DirectionalLineScalarUnitFubiniStatement.of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarUnitFubiniStatement F (e '' Ω) (u ∘ e.symm)) :
    DirectionalLineScalarUnitFubiniStatement E Ω u := by
  intro hΩ hu ξ hξ
  exact measure_diff_directionalLineScalarEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) (Ω := Ω) (u := u) (v := ξ)
    (h (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu)
      (e ξ) (by simpa using hξ))

/-- Unit-direction quotient version of
`DirectionalLineScalarEstimateFubiniStatement.of_image_linearIsometryEquiv`. -/
theorem DirectionalLineScalarQuotientUnitFubiniStatement.of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarQuotientUnitFubiniStatement F (e '' Ω) (u ∘ e.symm)) :
    DirectionalLineScalarQuotientUnitFubiniStatement E Ω u := by
  intro hΩ hu ξ hξ
  exact measure_diff_directionalLineScalarQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) (Ω := Ω) (u := u) (v := ξ)
    (h (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu)
      (e ξ) (by simpa using hξ))

/-- Pull a slicewise-to-Fubini transfer theorem back from an isometric coordinate model. -/
theorem directionalLineScalarSlicewiseTransfer_of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarSlicewiseToFubiniStatement F (e '' Ω) (u ∘ e.symm)) :
    DirectionalLineScalarSlicewiseToFubiniStatement E Ω u := by
  intro hslice
  exact DirectionalLineScalarEstimateFubiniStatement.of_image_linearIsometryEquiv (e := e)
    (h (hslice.image_linearIsometryEquiv e))

/-- Quotient version of
`directionalLineScalarSlicewiseTransfer_of_image_linearIsometryEquiv`. -/
theorem directionalLineScalarQuotientSlicewiseTransfer_of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarQuotientSlicewiseToFubiniStatement F (e '' Ω) (u ∘ e.symm)) :
    DirectionalLineScalarQuotientSlicewiseToFubiniStatement E Ω u := by
  intro hslice
  exact DirectionalLineScalarQuotientFubiniStatement.of_image_linearIsometryEquiv (e := e)
    (h (hslice.image_linearIsometryEquiv e))

/-- Unit-direction version of
`directionalLineScalarSlicewiseTransfer_of_image_linearIsometryEquiv`. -/
theorem directionalLineScalarUnitSlicewiseTransfer_of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h : DirectionalLineScalarUnitSlicewiseToFubiniStatement F (e '' Ω) (u ∘ e.symm)) :
    DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u := by
  intro hslice
  exact DirectionalLineScalarUnitFubiniStatement.of_image_linearIsometryEquiv (e := e)
    (h (hslice.image_linearIsometryEquiv e))

/-- Unit-direction quotient version of
`directionalLineScalarSlicewiseTransfer_of_image_linearIsometryEquiv`. -/
theorem directionalLineScalarQuotientUnitTransfer_of_image_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (h :
      DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement F (e '' Ω) (u ∘ e.symm)) :
    DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u := by
  intro hslice
  exact DirectionalLineScalarQuotientUnitFubiniStatement.of_image_linearIsometryEquiv (e := e)
    (h (hslice.image_linearIsometryEquiv e))

/-- Pull a finite-family slicewise-to-full-measure transfer theorem back from an isometric
coordinate model. -/
theorem finiteDirectionalLineScalarSlicewiseToFullMeasure_of_image_linearIsometryEquiv
    {ι : Type*} (D : Finset ι)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v := by
  intro hslice hΩ hu
  have hsliceF := hslice.image_linearIsometryEquiv e
  have hΩF := isOpen_image_linearIsometryEquiv e hΩ
  have huF := ConvexOn.image_linearIsometryEquiv e hu
  rcases h hsliceF hΩF huF with ⟨hpureF, hpairF⟩
  constructor
  · intro i hi
    exact measure_diff_directionalLineScalarEstimateSet_image_linearIsometryEquiv_eq_zero
      (e := e) (Ω := Ω) (u := u) (v := v i) (hpureF hi)
  · intro i hi j hj hij
    exact measure_diff_directionalLineScalarEstimateSet_image_linearIsometryEquiv_eq_zero
      (e := e) (Ω := Ω) (u := u) (v := v i + v j) (by
        simpa [map_add] using hpairF hi hj hij)

/-- Quotient version of
`finiteDirectionalLineScalarSlicewiseToFullMeasure_of_image_linearIsometryEquiv`. -/
theorem finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_image_linearIsometryEquiv
    {ι : Type*} (D : Finset ι)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v := by
  intro hslice hΩ hu
  have hsliceF := hslice.image_linearIsometryEquiv e
  have hΩF := isOpen_image_linearIsometryEquiv e hΩ
  have huF := ConvexOn.image_linearIsometryEquiv e hu
  rcases h hsliceF hΩF huF with ⟨hpureF, hpairF⟩
  constructor
  · intro i hi
    exact measure_diff_directionalLineScalarQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
      (e := e) (Ω := Ω) (u := u) (v := v i) (hpureF hi)
  · intro i hi j hj hij
    exact measure_diff_directionalLineScalarQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
      (e := e) (Ω := Ω) (u := u) (v := v i + v j) (by
        simpa [map_add] using hpairF hi hj hij)

/-- Pull a compatible finite-slice full-measure statement back from an isometric coordinate
model. -/
theorem CompatibleDirectionalSliceFullMeasureStatement.of_image_linearIsometryEquiv
    {ι : Type*} (D : Finset ι)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : CompatibleDirectionalSliceFullMeasureStatement D F (e '' Ω) (u ∘ e.symm)
      (fun i ↦ e (v i))) :
    CompatibleDirectionalSliceFullMeasureStatement D E Ω u v := by
  intro hΩ hu
  exact measure_diff_compatibleDirectionalSliceEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) (D := D) (v := v) (u := u)
    (h (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu))

/-- Quotient-estimate version of
`CompatibleDirectionalSliceFullMeasureStatement.of_image_linearIsometryEquiv`. -/
theorem CompatibleDirectionalSliceQuotientFullMeasureStatement.of_image_linearIsometryEquiv
    {ι : Type*} (D : Finset ι)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : CompatibleDirectionalSliceQuotientFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    CompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v := by
  intro hΩ hu
  exact
    measure_diff_compatibleDirectionalSliceQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
      (e := e) (D := D) (v := v) (u := u)
      (h (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu))

/-- Symmetric-compatible version of
`CompatibleDirectionalSliceFullMeasureStatement.of_image_linearIsometryEquiv`. -/
theorem SymmetricCompatibleDirectionalSliceFullMeasureStatement.of_image_linearIsometryEquiv
    {ι : Type*} (D : Finset ι)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : SymmetricCompatibleDirectionalSliceFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    SymmetricCompatibleDirectionalSliceFullMeasureStatement D E Ω u v := by
  intro hΩ hu
  exact
    measure_diff_symmetricCompatibleDirectionalSliceEstimateSet_image_linearIsometryEquiv_eq_zero
      (e := e) (D := D) (v := v) (u := u)
      (h (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu))

/-- Symmetric-compatible quotient-estimate version of
`CompatibleDirectionalSliceFullMeasureStatement.of_image_linearIsometryEquiv`. -/
theorem
    SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement.of_image_linearIsometryEquiv
    {ι : Type*} (D : Finset ι)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (h : SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement D F (e '' Ω)
      (u ∘ e.symm) (fun i ↦ e (v i))) :
    SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement D E Ω u v := by
  intro hΩ hu
  exact measure_diff_symmetricCompatibleSliceQuotientSet_image_linearIsometryEquiv_eq_zero
    (e := e) (D := D) (v := v) (u := u)
    (h (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu))

end AleksandrovDifferentiability
