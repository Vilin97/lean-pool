/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.QuadraticTrap.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Ambient quadratic estimates

Ambient quadratic remainder estimate predicates and their connection to second-order expansions.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The second-order expansion predicate can be read as a quadratic expansion of the affine
remainder after subtracting the first-order slope. -/
theorem hasSecondOrderExpansionAt_iff_affineRemainder
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E} :
    HasSecondOrderExpansionAt u x p B ↔
      (fun z : E =>
          affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z))
        =o[nhds 0] (fun z : E => ‖z‖ ^ 2) := by
  rw [HasSecondOrderExpansionAt]
  simp only [affineRemainder, add_sub_cancel_left]
  have hfun :
      (fun z : E =>
          u (x + z) - u x - inner ℝ p z - (1 / 2 : ℝ) * inner ℝ z (B z)) =
        (fun z : E =>
          u (x + z) - (u x + inner ℝ p z) - (1 / 2 : ℝ) * inner ℝ z (B z)) := by
    funext z
    ring
  rw [hfun]

theorem HasSecondOrderExpansionAt.affineRemainder_isLittleO
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : HasSecondOrderExpansionAt u x p B) :
      (fun z : E =>
        affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z))
      =o[nhds 0] (fun z : E => ‖z‖ ^ 2) :=
  hasSecondOrderExpansionAt_iff_affineRemainder.mp h

theorem hasSecondOrderExpansionAt_of_affineRemainder_isLittleO
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h :
      (fun z : E =>
        affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z))
      =o[nhds 0] (fun z : E => ‖z‖ ^ 2)) :
    HasSecondOrderExpansionAt u x p B :=
  hasSecondOrderExpansionAt_iff_affineRemainder.mpr h

/-- Finite eventually-valid norm bounds can be summed on a common neighborhood. This packages
the filter bookkeeping needed when several one-dimensional remainder estimates are combined. -/
theorem eventually_norm_sum_le_sum_mul
    {α V ι : Type*} [SeminormedAddCommGroup V] {l : Filter α}
    (s : Finset ι) (F : ι → α → V) (c : ι → ℝ) (φ : α → ℝ)
    (h : ∀ i, i ∈ s → ∀ᶠ x in l, ‖F i x‖ ≤ c i * φ x) :
    ∀ᶠ x in l, ‖∑ i ∈ s, F i x‖ ≤ (∑ i ∈ s, c i) * φ x := by
  have hall : ∀ᶠ x in l, ∀ i ∈ s, ‖F i x‖ ≤ c i * φ x := by
    rw [Finset.eventually_all]
    exact h
  filter_upwards [hall] with x hx
  calc
    ‖∑ i ∈ s, F i x‖ ≤ ∑ i ∈ s, ‖F i x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, c i * φ x := Finset.sum_le_sum fun i hi => hx i hi
    _ = (∑ i ∈ s, c i) * φ x := by rw [Finset.sum_mul]

/-- Common-constant version of `eventually_norm_sum_le_sum_mul`. -/
theorem eventually_norm_sum_le_card_mul
    {α V ι : Type*} [SeminormedAddCommGroup V] {l : Filter α}
    (s : Finset ι) (F : ι → α → V) (c : ℝ) (φ : α → ℝ)
    (h : ∀ i, i ∈ s → ∀ᶠ x in l, ‖F i x‖ ≤ c * φ x) :
    ∀ᶠ x in l, ‖∑ i ∈ s, F i x‖ ≤ (s.card : ℝ) * c * φ x := by
  have hsum :=
    eventually_norm_sum_le_sum_mul s F (fun _ => c) φ h
  filter_upwards [hsum] with x hx
  simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc] using hx

/-- Finite summation for punctured normalized quotient bounds. -/
theorem eventually_norm_sum_div_le_sum
    {α V ι : Type*} [SeminormedAddCommGroup V] {l : Filter α}
    (s : Finset ι) (F : ι → α → V) (c : ι → ℝ) (φ : α → ℝ)
    (hφ : ∀ᶠ x in l, 0 < φ x)
    (h : ∀ i, i ∈ s → ∀ᶠ x in l, ‖F i x‖ / φ x ≤ c i) :
    ∀ᶠ x in l, ‖∑ i ∈ s, F i x‖ / φ x ≤ ∑ i ∈ s, c i := by
  have hmul :
      ∀ i, i ∈ s → ∀ᶠ x in l, ‖F i x‖ ≤ c i * φ x := by
    intro i hi
    filter_upwards [hφ, h i hi] with x hφx hx
    exact (div_le_iff₀ hφx).mp hx
  filter_upwards [hφ, eventually_norm_sum_le_sum_mul s F c φ hmul] with x hφx hx
  exact (div_le_iff₀ hφx).mpr hx

/-- A neighborhood family of quadratic norm bounds for the remainder after subtracting a proposed
quadratic part is exactly the estimate needed for the project second-order expansion predicate. -/
theorem affineRemainder_sub_quadratic_isLittleO_of_eventually_norm_le_mul
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
          ε * ‖z‖ ^ 2) :
    (fun z : E =>
        affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z))
      =o[nhds 0] (fun z : E => ‖z‖ ^ 2) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [h c hc] with z hz
  have hsq_norm : ‖(‖z‖ ^ 2 : ℝ)‖ = ‖z‖ ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
  simpa [hsq_norm] using hz

/-- Local quadratic norm estimates after subtracting a proposed quadratic part give the
corresponding second-order expansion. -/
theorem hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
          ε * ‖z‖ ^ 2) :
    HasSecondOrderExpansionAt u x p B :=
  hasSecondOrderExpansionAt_of_affineRemainder_isLittleO
    (affineRemainder_sub_quadratic_isLittleO_of_eventually_norm_le_mul h)

/-- Local quadratic norm estimates after subtracting a symmetric proposed quadratic part give
second-order differentiability. -/
theorem secondOrderDifferentiableAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (hB : IsSymmetricOperator B)
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
          ε * ‖z‖ ^ 2) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt hB
    (hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul h)

/-- A punctured-neighborhood normalized quotient bound after subtracting a proposed quadratic
part gives the little-o estimate for the project second-order expansion predicate. -/
theorem affineRemainder_sub_quadratic_isLittleO_of_eventually_norm_div_norm_sq_le
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε) :
    (fun z : E =>
        affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z))
      =o[nhds 0] (fun z : E => ‖z‖ ^ 2) := by
  apply affineRemainder_sub_quadratic_isLittleO_of_eventually_norm_le_mul
  intro ε hε
  have hpunctured :=
    (eventually_nhdsWithin_iff.mp (h ε hε) :
      ∀ᶠ z in nhds (0 : E), z ∈ ({z : E | z ≠ 0}) →
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε)
  filter_upwards [hpunctured] with z hz
  by_cases hz0 : z = 0
  · subst z
    simp
  · have hquot :
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε := by
      exact hz hz0
    have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz0)
    exact (div_le_iff₀ hden).mp hquot

/-- A punctured-neighborhood normalized quotient bound after subtracting a proposed quadratic
part gives the corresponding second-order expansion. -/
theorem hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε) :
    HasSecondOrderExpansionAt u x p B :=
  hasSecondOrderExpansionAt_of_affineRemainder_isLittleO
    (affineRemainder_sub_quadratic_isLittleO_of_eventually_norm_div_norm_sq_le h)

/-- A punctured-neighborhood normalized quotient bound after subtracting a symmetric proposed
quadratic part gives second-order differentiability. -/
theorem secondOrderDifferentiableAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (hB : IsSymmetricOperator B)
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt hB
    (hasSecondOrderExpansionAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le h)

/-- Pointwise ambient quadratic estimate data: a first-order slope, a symmetric Hessian
candidate, and local `ε * ‖z‖ ^ 2` control of the quadratic remainder. -/
def QuadraticEstimateAt (u : E → ℝ) (x : E) : Prop :=
  ∃ p : E, ∃ B : E →L[ℝ] E,
    IsSymmetricOperator B ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ z in nhds 0,
          ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
            ε * ‖z‖ ^ 2

/-- Punctured normalized quotient version of `QuadraticEstimateAt`. -/
def QuadraticQuotientEstimateAt (u : E → ℝ) (x : E) : Prop :=
  ∃ p : E, ∃ B : E →L[ℝ] E,
    IsSymmetricOperator B ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
          ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
              ‖z‖ ^ 2 ≤ ε

/-- Points carrying ambient quadratic estimate data. -/
def quadraticEstimateSet (u : E → ℝ) : Set E :=
  {x | QuadraticEstimateAt u x}

/-- Points carrying punctured normalized ambient quadratic estimate data. -/
def quadraticQuotientEstimateSet (u : E → ℝ) : Set E :=
  {x | QuadraticQuotientEstimateAt u x}

@[simp]
theorem mem_quadraticEstimateSet {u : E → ℝ} {x : E} :
    x ∈ quadraticEstimateSet u ↔ QuadraticEstimateAt u x :=
  Iff.rfl

@[simp]
theorem mem_quadraticQuotientEstimateSet {u : E → ℝ} {x : E} :
    x ∈ quadraticQuotientEstimateSet u ↔ QuadraticQuotientEstimateAt u x :=
  Iff.rfl

/-- Conjugate a continuous linear operator by a linear isometry equivalence. This is the Hessian
candidate obtained when pulling quadratic estimate data back from an isometric coordinate model. -/
def linearIsometryEquivConjCLM (e : E ≃ₗᵢ[ℝ] F) (B : F →L[ℝ] F) : E →L[ℝ] E :=
  e.symm.toLinearIsometry.toContinuousLinearMap.comp
    (B.comp e.toLinearIsometry.toContinuousLinearMap)

/-- Symmetry of a Hessian candidate is preserved by isometric coordinate conjugation. -/
theorem isSymmetricOperator_linearIsometryEquivConjCLM
    (e : E ≃ₗᵢ[ℝ] F) {B : F →L[ℝ] F} (hB : IsSymmetricOperator B) :
    IsSymmetricOperator (linearIsometryEquivConjCLM e B) := by
  have hconj :
      ((e.symm.toLinearMap : F →ₗ[ℝ] E) ∘ₗ (B : F →ₗ[ℝ] F) ∘ₗ
          (e.toLinearMap : E →ₗ[ℝ] F)).IsSymmetric := by
    exact
      (LinearMap.isSymmetric_linearIsometryEquiv_conj_iff
        (T := (B : F →ₗ[ℝ] F)) (f := e.symm)).2 hB
  change ((e.symm.toLinearIsometry.toLinearMap : F →ₗ[ℝ] E) ∘ₗ
    (B : F →ₗ[ℝ] F) ∘ₗ (e.toLinearIsometry.toLinearMap : E →ₗ[ℝ] F)).IsSymmetric
  exact hconj

/-- The quadratic form of a conjugated operator is the coordinate-model quadratic form. -/
theorem inner_linearIsometryEquivConjCLM_self
    (e : E ≃ₗᵢ[ℝ] F) (B : F →L[ℝ] F) (z : E) :
    inner ℝ z ((linearIsometryEquivConjCLM e B) z) =
      inner ℝ (e z) (B (e z)) := by
  have hinner :=
    LinearIsometryEquiv.inner_map_map e z ((linearIsometryEquivConjCLM e B) z)
  rw [← hinner]
  congr 1
  simp [linearIsometryEquivConjCLM]

/-- Pull back ambient quadratic estimate data from an isometric coordinate model. -/
theorem QuadraticEstimateAt.of_image_linearIsometryEquiv
    {u : E → ℝ} (e : E ≃ₗᵢ[ℝ] F) {x : E}
    (h : QuadraticEstimateAt (u ∘ e.symm) (e x)) :
    QuadraticEstimateAt u x := by
  rcases h with ⟨pF, BF, hBF, hest⟩
  refine ⟨e.symm pF, linearIsometryEquivConjCLM e BF,
    isSymmetricOperator_linearIsometryEquivConjCLM e hBF, ?_⟩
  intro ε hε
  have htend : Filter.Tendsto (fun z : E ↦ e z) (nhds 0) (nhds 0) := by
    simpa using (e.continuous.continuousAt (x := 0)).tendsto
  filter_upwards [htend.eventually (hest ε hε)] with z hz
  have hpoint : e x + e z = e (x + z) := by
    simp [map_add]
  have hslope : pF = e (e.symm pF) := by
    simp
  have hquad := inner_linearIsometryEquivConjCLM_self e BF z
  have hnorm : ‖e z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp
  rw [hpoint] at hz
  rw [hslope] at hz
  rw [affineRemainder_comp_linearIsometryEquiv] at hz
  rw [← hquad] at hz
  rw [hnorm] at hz
  exact hz

/-- Pull back punctured normalized ambient quadratic estimate data from an isometric coordinate
model. -/
theorem QuadraticQuotientEstimateAt.of_image_linearIsometryEquiv
    {u : E → ℝ} (e : E ≃ₗᵢ[ℝ] F) {x : E}
    (h : QuadraticQuotientEstimateAt (u ∘ e.symm) (e x)) :
    QuadraticQuotientEstimateAt u x := by
  rcases h with ⟨pF, BF, hBF, hest⟩
  refine ⟨e.symm pF, linearIsometryEquivConjCLM e BF,
    isSymmetricOperator_linearIsometryEquivConjCLM e hBF, ?_⟩
  intro ε hε
  have htend_nhds :
      Filter.Tendsto (fun z : E ↦ e z) (nhdsWithin 0 {z : E | z ≠ 0}) (nhds 0) := by
    simpa using
      ((e.continuous.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds)
  have htend_principal :
      Filter.Tendsto (fun z : E ↦ e z) (nhdsWithin 0 {z : E | z ≠ 0})
        (Filter.principal {z : F | z ≠ 0}) := by
    rw [Filter.tendsto_principal]
    filter_upwards [self_mem_nhdsWithin] with z hz
    intro hez
    apply hz
    have hpre := congrArg e.symm hez
    simpa using hpre
  have htend :
      Filter.Tendsto (fun z : E ↦ e z) (nhdsWithin 0 {z : E | z ≠ 0})
        (nhdsWithin 0 {z : F | z ≠ 0}) := by
    rw [nhdsWithin]
    exact Filter.tendsto_inf.2 ⟨htend_nhds, htend_principal⟩
  filter_upwards [htend.eventually (hest ε hε)] with z hz
  have hpoint : e x + e z = e (x + z) := by
    simp [map_add]
  have hslope : pF = e (e.symm pF) := by
    simp
  have hquad := inner_linearIsometryEquivConjCLM_self e BF z
  have hnorm : ‖e z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp
  rw [hpoint] at hz
  rw [hslope] at hz
  rw [affineRemainder_comp_linearIsometryEquiv] at hz
  rw [← hquad] at hz
  rw [hnorm] at hz
  exact hz

/-- Pointwise transport of ambient quadratic estimate data through a linear isometry
equivalence. -/
theorem quadraticEstimateAt_comp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) {u : F → ℝ} {x : E} :
    QuadraticEstimateAt (u ∘ e) x ↔ QuadraticEstimateAt u (e x) := by
  constructor
  · intro h
    have h' :=
      QuadraticEstimateAt.of_image_linearIsometryEquiv
        (e := e.symm) (u := u) (x := e x)
        (by simpa [Function.comp_def] using h)
    simpa using h'
  · intro h
    have h' :=
      QuadraticEstimateAt.of_image_linearIsometryEquiv
        (e := e) (u := u ∘ e) (x := x)
        (by simpa [Function.comp_def] using h)
    simpa using h'

/-- Set-level transport of ambient quadratic estimate data through a linear isometry
equivalence. -/
theorem quadraticEstimateSet_comp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ) :
    quadraticEstimateSet (u ∘ e) = e ⁻¹' quadraticEstimateSet u := by
  ext x
  exact quadraticEstimateAt_comp_linearIsometryEquiv (e := e)

/-- Pointwise transport of punctured normalized ambient quadratic estimate data through a linear
isometry equivalence. -/
theorem quadraticQuotientEstimateAt_comp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) {u : F → ℝ} {x : E} :
    QuadraticQuotientEstimateAt (u ∘ e) x ↔ QuadraticQuotientEstimateAt u (e x) := by
  constructor
  · intro h
    have h' :=
      QuadraticQuotientEstimateAt.of_image_linearIsometryEquiv
        (e := e.symm) (u := u) (x := e x)
        (by simpa [Function.comp_def] using h)
    simpa using h'
  · intro h
    have h' :=
      QuadraticQuotientEstimateAt.of_image_linearIsometryEquiv
        (e := e) (u := u ∘ e) (x := x)
        (by simpa [Function.comp_def] using h)
    simpa using h'

/-- Set-level transport of punctured normalized ambient quadratic estimate data through a linear
isometry equivalence. -/
theorem quadraticQuotientEstimateSet_comp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ) :
    quadraticQuotientEstimateSet (u ∘ e) = e ⁻¹' quadraticQuotientEstimateSet u := by
  ext x
  exact quadraticQuotientEstimateAt_comp_linearIsometryEquiv (e := e)

/-- Ambient quadratic estimate data implies project second-order differentiability. -/
theorem QuadraticEstimateAt.secondOrderDifferentiableAt
    {u : E → ℝ} {x : E} (h : QuadraticEstimateAt u x) :
    SecondOrderDifferentiableAt u x := by
  rcases h with ⟨p, B, hB, hest⟩
  exact secondOrderDifferentiableAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul
    hB hest

/-- Ambient quadratic quotient-estimate data implies project second-order differentiability. -/
theorem QuadraticQuotientEstimateAt.secondOrderDifferentiableAt
    {u : E → ℝ} {x : E} (h : QuadraticQuotientEstimateAt u x) :
    SecondOrderDifferentiableAt u x := by
  rcases h with ⟨p, B, hB, hest⟩
  exact secondOrderDifferentiableAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le
    hB hest

/-- A local ambient quadratic estimate implies the punctured normalized quotient estimate. -/
theorem QuadraticEstimateAt.quadraticQuotientEstimateAt
    {u : E → ℝ} {x : E} (h : QuadraticEstimateAt u x) :
    QuadraticQuotientEstimateAt u x := by
  rcases h with ⟨p, B, hB, hest⟩
  refine ⟨p, B, hB, ?_⟩
  intro ε hε
  filter_upwards [(hest ε hε).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hz_ne
  have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz_ne)
  exact (div_le_iff₀ hden).mpr hz

/-- The ambient quadratic estimate set is contained in the second-order differentiability locus. -/
theorem quadraticEstimateSet_subset_secondOrderDifferentiabilitySet {u : E → ℝ} :
    quadraticEstimateSet u ⊆ secondOrderDifferentiabilitySet u := by
  intro x hx
  exact hx.secondOrderDifferentiableAt

/-- The ambient quadratic quotient-estimate set is contained in the second-order differentiability
locus. -/
theorem quadraticQuotientEstimateSet_subset_secondOrderDifferentiabilitySet {u : E → ℝ} :
    quadraticQuotientEstimateSet u ⊆ secondOrderDifferentiabilitySet u := by
  intro x hx
  exact hx.secondOrderDifferentiableAt

/-- The local ambient quadratic estimate set is contained in the quotient-estimate set. -/
theorem quadraticEstimateSet_subset_quadraticQuotientEstimateSet {u : E → ℝ} :
    quadraticEstimateSet u ⊆ quadraticQuotientEstimateSet u := by
  intro x hx
  exact hx.quadraticQuotientEstimateAt


end AleksandrovDifferentiability
