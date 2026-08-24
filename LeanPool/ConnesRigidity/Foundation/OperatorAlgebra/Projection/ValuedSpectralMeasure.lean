/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 16191-16348.
Modifications: extracted the projection-valued spectral interface and
positive-atom argument, adapted namespace and local spectral interfaces, and
added the later quotient-approximation bridge. Paper: §4. See the upstream PORT_MAP.md.
-/
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.SpectralCriterion
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.NormalFixed

/-!
The valued spectral measure component of the Connes rigidity formalization.
-/

namespace Connes

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

universe u v

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A]
  [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]
variable [MeasurableSingletonClass (DiscreteCharacterSpace A)]

/-- Projection-valued spectral data for a unitary representation. Paper: §4. -/
structure ProjectionValuedSpectralMeasure
    (E : SplitAbelianExtension A G H)
    (K : Type v) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation G K) where
  /--
  The `projection` component of `ProjectionValuedSpectralMeasure`.
  -/
  projection : Set (DiscreteCharacterSpace A) → (K →L[ℂ] K)
  projection_empty : projection ∅ = 0
  projection_univ : projection Set.univ = 1
  projection_inter : ∀ s t,
    MeasurableSet s → MeasurableSet t →
      projection (s ∩ t) = (projection s).comp (projection t)
  projection_self_adjoint : ∀ s, MeasurableSet s → ∀ x y : K,
    inner ℂ (projection s x) y = inner ℂ x (projection s y)
  projection_iUnion : ∀ (s : ℕ → Set (DiscreteCharacterSpace A)),
    (∀ n, MeasurableSet (s n)) →
    (∀ i j, i ≠ j → Disjoint (s i) (s j)) →
      ∀ x : K,
        HasSum (fun n ↦ projection (s n) x)
          (projection (⋃ n, s n) x)
  /--
  The `scalar` component of `ProjectionValuedSpectralMeasure`.
  -/
  scalar : K → Measure (DiscreteCharacterSpace A)
  scalar_apply : ∀ (x : K) (s : Set (DiscreteCharacterSpace A)),
    MeasurableSet s →
      (scalar x).real s = (inner ℂ x (projection s x)).re
  projection_covariance : ∀ (h : H) (s : Set (DiscreteCharacterSpace A))
    (x : K),
      (π (E.splitting h) : K →L[ℂ] K) (projection s x) =
        projection (dualCharacterAction E.action h '' s)
          ((π (E.splitting h) : K →L[ℂ] K) x)
  scalar_covariance : ∀ (h : H) (x : K),
    (scalar x).map (dualCharacterAction E.action h) =
      scalar ((π (E.splitting h) : K →L[ℂ] K) x)
  kernel_eigenprojection : ∀ (a : A) (χ : DiscreteCharacterSpace A) (x : K),
    (π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K)
        (projection {χ} x) =
      (((χ (Multiplicative.ofAdd a) : Circle) : ℂ) • projection {χ} x)
  energy_identity : ∀ (x : K) (a : A),
    (∫ χ : DiscreteCharacterSpace A,
      ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2
        ∂(scalar x)) =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K) x - x‖ ^ 2

namespace ProjectionValuedSpectralMeasure

variable {E : SplitAbelianExtension A G H}
variable {K : Type v} [NormedAddCommGroup K]
  [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRepresentation G K}

omit [BorelSpace (DiscreteCharacterSpace A)]
  [MeasurableSingletonClass (DiscreteCharacterSpace A)] in
/-- The scalar spectral measure has total mass equal to squared norm. Paper: §4. -/
theorem scalar_univ_real
    (P : ProjectionValuedSpectralMeasure E K π) (x : K) :
    (P.scalar x).real Set.univ = ‖x‖ ^ 2 := by
  rw [P.scalar_apply x Set.univ MeasurableSet.univ, P.projection_univ]
  simpa only [one_apply_eq_self, inner_self_eq_norm_sq_to_K,
    Complex.coe_algebraMap, RCLike.re_to_complex] using
    (inner_self_eq_norm_sq (𝕜 := ℂ) x)

omit [BorelSpace (DiscreteCharacterSpace A)]
  [MeasurableSingletonClass (DiscreteCharacterSpace A)] in
/-- A unit vector normalizes its scalar spectral measure. Paper: §4. -/
theorem scalar_isProbabilityMeasure
    (P : ProjectionValuedSpectralMeasure E K π)
    (x : K) (hx : ‖x‖ = 1) :
    IsProbabilityMeasure (P.scalar x) where
  measure_univ := by
    apply (ENNReal.toReal_eq_one_iff _).mp
    change (P.scalar x).real Set.univ = 1
    rw [P.scalar_univ_real x, hx]
    norm_num

/-- Package a unit vector's scalar measure as a probability measure. Paper: §4. -/
def probabilityMeasure
    (P : ProjectionValuedSpectralMeasure E K π)
    (x : K) (hx : ‖x‖ = 1) :
    ProbabilityMeasure (DiscreteCharacterSpace A) :=
  ⟨P.scalar x, P.scalar_isProbabilityMeasure x hx⟩

omit [BorelSpace (DiscreteCharacterSpace A)]
  [MeasurableSingletonClass (DiscreteCharacterSpace A)] in
/-- Quotient-fixed vectors produce invariant scalar spectral measures. Paper: §4. -/
theorem probabilityMeasure_invariant
    (P : ProjectionValuedSpectralMeasure E K π)
    (x : QuotientFixedUnitVector E K π) :
    IsInvariantSpectralMeasure E.action
      (P.probabilityMeasure x.vector x.norm_one) := by
  intro h
  change (P.scalar x.vector).map (dualCharacterAction E.action h) =
    P.scalar x.vector
  rw [P.scalar_covariance h x.vector, x.quotient_fixed h]

omit [BorelSpace (DiscreteCharacterSpace A)]
  [MeasurableSingletonClass (DiscreteCharacterSpace A)] in
/-- The scalar spectral energy is the kernel displacement energy. Paper: §4. -/
theorem probabilityMeasure_energy
    (P : ProjectionValuedSpectralMeasure E K π)
    (x : QuotientFixedUnitVector E K π) (a : A) :
    spectralDetectionEnergy
        (P.probabilityMeasure x.vector x.norm_one) a =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K) x.vector - x.vector‖ ^ 2 := by
  exact P.energy_identity x.vector a

omit [BorelSpace (DiscreteCharacterSpace A)] in
/-- A positive trivial atom gives a nonzero trivial spectral projection. Paper: §4. -/
theorem trivialProjection_ne_zero_of_atom_pos
    (P : ProjectionValuedSpectralMeasure E K π)
    (x : QuotientFixedUnitVector E K π)
    (hx : 0 < spectralTrivialAtom
      (P.probabilityMeasure x.vector x.norm_one)) :
    P.projection {1} x.vector ≠ 0 := by
  intro hzero
  have hatom := P.scalar_apply x.vector {1}
    (measurableSet_singleton 1)
  change (P.scalar x.vector).real {1} =
    (inner ℂ x.vector (P.projection {1} x.vector)).re at hatom
  rw [hzero, inner_zero_right] at hatom
  change 0 < (P.scalar x.vector).real {1} at hx
  rw [hatom] at hx
  norm_num at hx

omit [BorelSpace (DiscreteCharacterSpace A)]
  [MeasurableSingletonClass (DiscreteCharacterSpace A)] in
/-- The trivial spectral projection is fixed by every kernel element. Paper: §4. -/
theorem trivialProjection_kernel_fixed
    (P : ProjectionValuedSpectralMeasure E K π)
    (x : K) (a : A) :
    (π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K)
        (P.projection {1} x) = P.projection {1} x := by
  simpa only [PontryaginDual.one_apply, Circle.coe_one, one_smul] using
    P.kernel_eigenprojection a 1 x

omit [BorelSpace (DiscreteCharacterSpace A)]
  [MeasurableSingletonClass (DiscreteCharacterSpace A)] in
/-- The trivial spectral projection is fixed by every quotient section. Paper: §4. -/
theorem trivialProjection_quotient_fixed
    (P : ProjectionValuedSpectralMeasure E K π)
    (x : QuotientFixedUnitVector E K π) (h : H) :
    (π (E.splitting h) : K →L[ℂ] K)
      (P.projection {1} x.vector) = P.projection {1} x.vector := by
  have hcov := P.projection_covariance h {1} x.vector
  rw [Set.image_singleton, dualCharacterAction_trivial] at hcov
  rw [x.quotient_fixed h] at hcov
  exact hcov

omit [BorelSpace (DiscreteCharacterSpace A)] in
/-- A positive trivial atom yields a vector fixed by the split extension. Paper: §4. -/
theorem positive_atom_invariant
    (P : ProjectionValuedSpectralMeasure E K π)
    (x : QuotientFixedUnitVector E K π)
    (hx : 0 < spectralTrivialAtom
      (P.probabilityMeasure x.vector x.norm_one)) :
    ∃ η : K, η ≠ 0 ∧
      (∀ a : A,
        (π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K) η = η) ∧
      (∀ h : H,
        (π (E.splitting h) : K →L[ℂ] K) η = η) := by
  refine ⟨P.projection {1} x.vector,
    P.trivialProjection_ne_zero_of_atom_pos x hx, ?_, ?_⟩
  · exact P.trivialProjection_kernel_fixed x.vector
  · exact P.trivialProjection_quotient_fixed x

/- Approximation of quotient-fixed vectors supplied by the quotient property-(T)
step. Paper: §4.
-/
/--
The `HasQuotientFixedApproximation` construction used in the Connes rigidity formalization.
-/
def HasQuotientFixedApproximation
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G K) : Prop :=
  HasKazhdanPropertyT.{u, v} H →
    π.HasAlmostInvariantUnitVectors →
      ∀ (J : Finset A) (ε : ℝ), 0 < ε →
        ∃ x : QuotientFixedUnitVector E K π,
          (∑ a ∈ J,
            ‖(π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K)
                x.vector - x.vector‖ ^ 2) < ε
/- The qualitative definition of property (T) supplies a Kazhdan gap on the
orthogonal complement of the fixed vectors.  Projecting a sufficiently almost
invariant unit vector to the fixed subspace therefore preserves any prescribed
finite family of displacement estimates. -/
omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]
  [MeasurableSingletonClass (DiscreteCharacterSpace A)] in
theorem exists_quotientFixedUnitVector_with_displacement
    (hH : HasKazhdanPropertyT.{u, v} H)
    (hπ : π.HasAlmostInvariantUnitVectors)
    (T : Finset G) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : QuotientFixedUnitVector E K π,
      ∀ g ∈ T, ‖(π g : K →L[ℂ] K) x.vector - x.vector‖ < ε := by
  classical
  let ρ : UnitaryRepresentation H K := π.comp E.splitting
  let N : Subgroup H := ⊤
  let M : Submodule ℂ K := normalFixedSubmodule N ρ
  have hno :
      ¬(normalFixedOrthogonalRepresentation N ρ).HasAlmostInvariantUnitVectors := by
    intro horth
    obtain ⟨ξ, hξ, hinv⟩ :=
      hH ((normalFixedSubmodule N ρ)ᗮ)
        inferInstance inferInstance inferInstance
        (normalFixedOrthogonalRepresentation N ρ) horth
    have hzero := normalFixedOrthogonalRepresentation_no_fixed N ρ ξ
      (fun n => hinv n)
    exact hξ hzero
  have hgap : ∃ S : Finset H, ∃ κ : ℝ, 0 < κ ∧
      ∀ z : (normalFixedSubmodule N ρ)ᗮ, ‖z‖ = 1 →
        ∃ h ∈ S,
          κ ≤ ‖(normalFixedOrthogonalRepresentation N ρ h :
            (normalFixedSubmodule N ρ)ᗮ →L[ℂ]
              (normalFixedSubmodule N ρ)ᗮ) z - z‖ := by
    by_contra h
    push Not at h
    exact hno h
  obtain ⟨S, κ, hκ, hgap⟩ := hgap
  let α : ℝ := min (κ / 4) (min (ε * κ / 16) (ε / 16))
  have hα : 0 < α := by
    dsimp [α]
    positivity
  let U : Finset G := S.image E.splitting ∪ T
  obtain ⟨x, hx, hclose⟩ := hπ U α hα
  let z : K := x - M.starProjection x
  have hzmem : z ∈ Mᗮ := by
    dsimp [z]
    exact Submodule.sub_starProjection_mem_orthogonal x
  have hzbound : ‖z‖ < α / κ := by
    by_contra hnot
    have hzlower : α / κ ≤ ‖z‖ := le_of_not_gt hnot
    have hz : z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hzlower
      exact (not_le_of_gt (div_pos hα hκ)) hzlower
    let w : Mᗮ :=
      ⟨((‖z‖ : ℂ)⁻¹) • z, Mᗮ.smul_mem _ hzmem⟩
    have hwnorm : ‖w‖ = 1 := norm_smul_inv_norm hz
    obtain ⟨h, hhS, hhκ⟩ := hgap w hwnorm
    have hcontract :
        ‖(normalFixedOrthogonalRepresentation N ρ h :
          Mᗮ →L[ℂ] Mᗮ) ⟨z, hzmem⟩ - ⟨z, hzmem⟩‖ ≤
          ‖(ρ h : K →L[ℂ] K) x - x‖ := by
      exact normalFixed_orthogonalResidual_displacement_le N ρ h x
    have hwformula :
        ‖(normalFixedOrthogonalRepresentation N ρ h :
          Mᗮ →L[ℂ] Mᗮ) w - w‖ =
          ‖(ρ h : K →L[ℂ] K) z - z‖ / ‖z‖ := by
      change ‖(ρ h : K →L[ℂ] K)
        (((‖z‖ : ℂ)⁻¹) • z) - ((‖z‖ : ℂ)⁻¹) • z‖ = _
      rw [map_smul, ← smul_sub, norm_smul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
      simp only [div_eq_mul_inv, mul_comm]
    rw [hwformula] at hhκ
    have hhsmall : ‖(ρ h : K →L[ℂ] K) x - x‖ < α := by
      exact hclose (E.splitting h)
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨h, hhS, rfl⟩))
    have hreslt : ‖(ρ h : K →L[ℂ] K) z - z‖ < α :=
      lt_of_le_of_lt hcontract hhsmall
    have hresdiv :
        ‖(ρ h : K →L[ℂ] K) z - z‖ / ‖z‖ < α / ‖z‖ :=
      (div_lt_div_iff_of_pos_right (norm_pos_iff.mpr hz)).2 hreslt
    have halphadiv : α / ‖z‖ ≤ κ := by
      apply (div_le_iff₀ (norm_pos_iff.mpr hz)).2
      have hακ : α ≤ ‖z‖ * κ := (div_le_iff₀ hκ).mp hzlower
      simpa [mul_comm] using hακ
    linarith
  let p : M := ⟨M.starProjection x, Submodule.starProjection_apply_mem _ _⟩
  have hp_lower : 1 - α / κ < ‖p‖ := by
    by_contra hnot
    have hpupper : ‖p‖ ≤ 1 - α / κ := le_of_not_gt hnot
    have htriangle : ‖x‖ ≤ ‖(p : K)‖ + ‖z‖ := by
      calc
        ‖x‖ = ‖(p : K) + z‖ := by
          congr 1
          dsimp [p, z]
          abel
        _ ≤ ‖(p : K)‖ + ‖z‖ := norm_add_le _ _
    rw [hx] at htriangle
    have hsum : ‖p‖ + ‖z‖ < (1 - α / κ) + α / κ :=
      add_lt_add_of_le_of_lt hpupper hzbound
    have hsum' : ‖p‖ + ‖z‖ < 1 := by
      convert hsum using 1
      all_goals ring
    exact (not_lt_of_ge htriangle) hsum'
  have halpha_kappa : α / κ ≤ 1 / 4 := by
    apply (div_le_iff₀ hκ).2
    dsimp [α]
    have hmin := min_le_left (κ / 4) (min (ε * κ / 16) (ε / 16))
    nlinarith
  have hp_lower' : 3 / 4 < ‖p‖ := by linarith
  have hp_pos : 0 < ‖p‖ := lt_trans (by norm_num) hp_lower'
  let η : M := ((‖p‖ : ℂ)⁻¹) • p
  have hηnorm : ‖η‖ = 1 := by
    dsimp [η]
    exact norm_smul_inv_norm (norm_pos_iff.mp hp_pos)
  let η' : QuotientFixedUnitVector E K π :=
    { vector := (η : K)
      norm_one := hηnorm
      quotient_fixed := by
        intro h
        exact η.property ⟨h, Subgroup.mem_top h⟩ }
  refine ⟨η', ?_⟩
  intro g hgT
  have hgsmall : ‖(π g : K →L[ℂ] K) x - x‖ < α :=
    hclose g (Finset.mem_union_right _ hgT)
  have hpdisp :
      ‖(π g : K →L[ℂ] K) (p : K) - (p : K)‖ ≤
        ‖(π g : K →L[ℂ] K) x - x‖ + 2 * ‖z‖ := by
    calc
      ‖(π g : K →L[ℂ] K) (p : K) - (p : K)‖ =
          ‖((π g : K →L[ℂ] K) x - x) -
            ((π g : K →L[ℂ] K) z - z)‖ := by
        congr 1
        dsimp [p, z]
        rw [map_sub]
        abel
      _ ≤ ‖(π g : K →L[ℂ] K) x - x‖ +
            ‖(π g : K →L[ℂ] K) z - z‖ := norm_sub_le _ _
      _ ≤ ‖(π g : K →L[ℂ] K) x - x‖ + 2 * ‖z‖ := by
        calc
          _ ≤ ‖(π g : K →L[ℂ] K) x - x‖ +
              (‖(π g : K →L[ℂ] K) z‖ + ‖z‖) :=
            add_le_add_right (norm_sub_le _ _) _
          _ = ‖(π g : K →L[ℂ] K) x - x‖ + 2 * ‖z‖ := by
            rw [Unitary.norm_map]
            ring
  have hnum : α + 2 * (α / κ) ≤ 3 * ε / 16 := by
    have ha : α ≤ ε / 16 := by
      dsimp [α]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have har : α / κ ≤ ε / 16 := by
      apply (div_le_iff₀ hκ).2
      have hα2 : α ≤ ε * κ / 16 := by
        dsimp [α]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      calc
        α ≤ ε * κ / 16 := hα2
        _ = (ε / 16) * κ := by ring
    nlinarith
  have hpdisplt :
      ‖(π g : K →L[ℂ] K) (p : K) - (p : K)‖ < 3 * ε / 16 := by
    exact lt_of_le_of_lt hpdisp (by nlinarith [hgsmall, hzbound, hnum])
  have hfrac :
      ‖(π g : K →L[ℂ] K) (p : K) - (p : K)‖ / ‖p‖ < ε := by
    apply (div_lt_iff₀ hp_pos).2
    have hpbound : 3 / 4 ≤ ‖p‖ := by linarith
    nlinarith
  change ‖(π g : K →L[ℂ] K) (η : K) - (η : K)‖ < ε
  dsimp [η]
  rw [map_smul, ← smul_sub, norm_smul]
  have hscalar :
      ‖((‖(p : K)‖ : ℂ)⁻¹)‖ = (‖(p : K)‖ : ℝ)⁻¹ := by
    simp [norm_inv, Complex.norm_real]
  rw [hscalar]
  simpa only [Submodule.coe_norm, div_eq_mul_inv, mul_comm] using hfrac

omit [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]
  [MeasurableSingletonClass (DiscreteCharacterSpace A)] in
/- Consequently the quotient-fixed approximation field is not additional
spectral data: it follows from quotient property (T) and almost invariance. -/
theorem hasQuotientFixedApproximation :
    HasQuotientFixedApproximation E π := by
  intro hH hπ J ε hε
  classical
  let denominator : ℝ := J.card + 1
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  let δ : ℝ := Real.sqrt (ε / denominator)
  have hquotient : 0 < ε / denominator := div_pos hε hdenominator
  have hδ : 0 < δ := Real.sqrt_pos.2 hquotient
  let T : Finset G := J.image
    (fun a => E.inclusion (Multiplicative.ofAdd a))
  obtain ⟨x, hx⟩ :=
    exists_quotientFixedUnitVector_with_displacement
      (E := E) (π := π) hH hπ T δ hδ
  refine ⟨x, ?_⟩
  by_cases hJ : J.Nonempty
  · calc
      (∑ a ∈ J,
          ‖(π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K)
              x.vector - x.vector‖ ^ 2) <
          ∑ _a ∈ J, δ ^ 2 :=
        Finset.sum_lt_sum_of_nonempty hJ (fun a ha => by
          apply (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hδ)).2
          exact hx _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
      _ = (J.card : ℝ) * δ ^ 2 := by simp
      _ = (J.card : ℝ) * (ε / denominator) := by
        rw [Real.sq_sqrt (le_of_lt hquotient)]
      _ < ε := by
        rw [show (J.card : ℝ) * (ε / denominator) =
          ((J.card : ℝ) * ε) / denominator by ring]
        apply (div_lt_iff₀ hdenominator).2
        dsimp [denominator]
        nlinarith
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hJ,
      Finset.sum_empty]
    exact hε

/-- Convert a PVM and quotient approximation into the generic spectral interface. Paper: §4. -/
def toSpectralMeasureInterface
    (P : ProjectionValuedSpectralMeasure E K π)
    (approximation : ProjectionValuedSpectralMeasure.HasQuotientFixedApproximation E π) :
    SpectralMeasureInterface E K π where
  quotient_fixed_approximation := approximation
  measure := fun x => P.probabilityMeasure x.vector x.norm_one
  measure_invariant := fun x => P.probabilityMeasure_invariant x
  energy_eq := fun x a => P.probabilityMeasure_energy x a
  positive_atom_invariant := fun x hx => P.positive_atom_invariant x hx

end ProjectionValuedSpectralMeasure

omit [BorelSpace (DiscreteCharacterSpace A)] in
/-- Relative property-(T) from an analytic PVM and detector.  Quotient
approximation follows generically from quotient property (T). Paper: §4. -/
theorem relative_propertyT_of_projectionValuedSpectralMeasure
    (E : SplitAbelianExtension A G H)
    (hH : HasKazhdanPropertyT.{u, v} H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c)
    (pvm : ∀ (K : Type v)
      (_ : NormedAddCommGroup K)
      (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K)
      (π : UnitaryRepresentation G K),
        ProjectionValuedSpectralMeasure E K π) :
    HasKazhdanPropertyT.{u, v} G := by
  apply spectral_criterion E hH J hc hdetection
  intro K _ _ _ π
  exact ProjectionValuedSpectralMeasure.toSpectralMeasureInterface
    (pvm K inferInstance inferInstance inferInstance π)
    ProjectionValuedSpectralMeasure.hasQuotientFixedApproximation

end
end Connes
