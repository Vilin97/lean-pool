/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 29950-30030.
Modifications: split crossed-product transport into a reusable module, added
continuous-coefficient closure and nonadditive homeomorphic transport, and
changed imports and namespace. Paper: §3. See the upstream PORT_MAP.md.
-/
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.CrossedProductTransport
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.SemidirectClosure

/-!
# Crossed-product factor transport

This module first transports the full measurable crossed-product generator
family across an equivariant Haar equivalence. It then treats the continuous
coefficient closure used in Zhou's §3: a norm-dense coefficient family has the
same von Neumann closure as all continuous coefficients, and an equivariant
measure-preserving homeomorphism transports that closure. The homeomorphism is
not required to preserve the addition on either compact group.
-/

namespace Connes
namespace CrossedProduct

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

universe u v w

variable {K : Type u} [Group K]
variable {Ω : Type v} [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
variable {Ξ : Type w} [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]

/- The base multiplier conjugacy is the pointwise transport theorem lifted to
the crossed Hilbert space. Paper: §3. -/
theorem crossedHaarHilbertEquiv_multiplier_conj
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y)
    (f : crossedCoefficient X) :
    (crossedHaarHilbertEquiv e).conjStarAlgEquiv
        (crossedMultiplier X f) =
      crossedMultiplier Y
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
          (EquivariantHaarEquiv.symm e).measure_preserving f) := by
  apply ContinuousLinearMap.ext
  intro η
  obtain ⟨ξ, rfl⟩ := (crossedHaarHilbertEquiv e).surjective η
  apply lp.ext
  funext k
  change
    crossedHaarHilbertEquiv e
      (crossedMultiplier X f
        ((crossedHaarHilbertEquiv e).symm
          ((crossedHaarHilbertEquiv e) ξ))) k =
      crossedBaseMultiplier Y
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
          (EquivariantHaarEquiv.symm e).measure_preserving f)
        (crossedBaseHaarEquiv e (ξ k))
  rw [LinearIsometryEquiv.symm_apply_apply]
  change
    crossedBaseHaarEquiv e (crossedBaseMultiplier X f (ξ k)) =
      crossedBaseMultiplier Y
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
          (EquivariantHaarEquiv.symm e).measure_preserving f)
        (crossedBaseHaarEquiv e (ξ k))
  exact crossedBaseHaarEquiv_multiplier_apply e f (ξ k)

/- The coefficient pullback has the expected inverse. Paper: §3. -/
theorem crossedCoefficient_pullback_symm_apply
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y)
    (f : crossedCoefficient Y) :
    Lp.compMeasurePreserving e.toMeasurableEquiv.symm
      (EquivariantHaarEquiv.symm e).measure_preserving
      (Lp.compMeasurePreserving e.toMeasurableEquiv
        e.measure_preserving f) = f := by
  let hs : MeasurePreserving
      (e.toMeasurableEquiv.symm : Ξ → Ω) Y.measure X.measure :=
    (EquivariantHaarEquiv.symm e).measure_preserving
  have h := Lp.compMeasurePreserving_comp_apply f e.measure_preserving hs
  simpa only [Function.comp_def, MeasurableEquiv.apply_symm_apply,
    show (fun z : Ξ ↦ z) = id from rfl, Lp.compMeasurePreserving_id,
    AddMonoidHom.id_apply] using h.symm

/- The two crossed-product generator families are transported exactly.
Paper: §3. -/
theorem crossedGeneratorSet_image
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) :
    (crossedHaarHilbertEquiv e).conjStarAlgEquiv '' crossedGeneratorSet X =
      crossedGeneratorSet Y := by
  ext T
  constructor
  · rintro ⟨S, hS, rfl⟩
    rcases hS with ⟨f, rfl⟩ | ⟨k, rfl⟩
    · exact Or.inl ⟨_, (crossedHaarHilbertEquiv_multiplier_conj e f).symm⟩
    · exact Or.inr ⟨k, (crossedHaarHilbertEquiv_group_conj e k).symm⟩
  · rintro (⟨f, rfl⟩ | ⟨k, rfl⟩)
    · let g : crossedCoefficient X :=
        Lp.compMeasurePreserving e.toMeasurableEquiv
          e.measure_preserving f
      refine ⟨crossedMultiplier X g, Or.inl ⟨g, rfl⟩, ?_⟩
      rw [crossedHaarHilbertEquiv_multiplier_conj]
      congr 1
      exact crossedCoefficient_pullback_symm_apply e f
    · exact ⟨(crossedGroupUnitary X k).toContinuousLinearEquiv.toContinuousLinearMap,
        Or.inr ⟨k, rfl⟩,
        crossedHaarHilbertEquiv_group_conj e k⟩

/- Membership in the generated crossed algebra is invariant under transport.
Paper: §3. -/
theorem crossedHaarHilbertEquiv_mem_algebra_iff
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y)
    (T : crossedHilbert X →L[ℂ] crossedHilbert X) :
    T ∈ (crossedProductModel X).algebra ↔
      (crossedHaarHilbertEquiv e).conjStarAlgEquiv T ∈
        (crossedProductModel Y).algebra := by
  change
    T ∈ vonNeumannClosure (crossedGeneratorSet X) ↔
      (crossedHaarHilbertEquiv e).conjStarAlgEquiv T ∈
        vonNeumannClosure (crossedGeneratorSet Y)
  rw [← crossedGeneratorSet_image e]
  exact (mem_vonNeumannClosure_iff_of_conj_image_eq
    (crossedHaarHilbertEquiv e) (crossedGeneratorSet X)
      ((crossedHaarHilbertEquiv e).conjStarAlgEquiv '' crossedGeneratorSet X)
      (by rfl) T)

/-- An equivariant measure-preserving homeomorphism between Haar actions.
Unlike a compact-group equivalence, the homeomorphism need not preserve
addition; this is the boundary needed by Zhou's quadratic fiber shear. -/
structure EquivariantHaarHomeomorph
    (X : HaarProbabilityAction K Ω) (Y : HaarProbabilityAction K Ξ) where
  /--
  The `toHomeomorph` component of `EquivariantHaarHomeomorph`.
  -/
  toHomeomorph : Ω ≃ₜ Ξ
  measure_preserving : MeasurePreserving toHomeomorph X.measure Y.measure
  equivariant : ∀ (k : K) (z : Ω),
    toHomeomorph (X.action k z) = Y.action k (toHomeomorph z)

namespace EquivariantHaarHomeomorph

variable [BorelSpace Ω] [BorelSpace Ξ]
variable {X : HaarProbabilityAction K Ω} {Y : HaarProbabilityAction K Ξ}

/-- Forget the topology of an equivariant Haar homeomorphism, retaining its
measurable, measure-preserving, equivariant action equivalence. -/
def toEquivariantHaarEquiv (e : EquivariantHaarHomeomorph X Y) :
    EquivariantHaarEquiv X Y where
  toMeasurableEquiv := e.toHomeomorph.toMeasurableEquiv
  measure_preserving := e.measure_preserving
  equivariant := e.equivariant

end EquivariantHaarHomeomorph

variable [CompactSpace Ω] [BorelSpace Ω]
variable [CompactSpace Ξ] [BorelSpace Ξ]

local instance haarProbabilitySource
    (X : HaarProbabilityAction K Ω) : IsProbabilityMeasure X.measure :=
  X.probability

local instance haarProbabilityTarget
    (Y : HaarProbabilityAction K Ξ) : IsProbabilityMeasure Y.measure :=
  Y.probability

private def crossedFiberwiseOperatorContinuousLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    (E →L[ℂ] E) →L[ℂ]
      (lp (fun _ : K ↦ E) 2 →L[ℂ] lp (fun _ : K ↦ E) 2) := by
  let F : (E →L[ℂ] E) →ₗ[ℂ]
      (lp (fun _ : K ↦ E) 2 →L[ℂ] lp (fun _ : K ↦ E) 2) :=
    { toFun := crossedFiberwiseOperator
      map_add' := by
        intro S T
        apply ContinuousLinearMap.ext
        intro ξ
        apply lp.ext
        funext k
        rfl
      map_smul' := by
        intro c T
        apply ContinuousLinearMap.ext
        intro ξ
        apply lp.ext
        funext k
        rfl }
  exact F.mkContinuous 1 (by
    intro T
    rw [one_mul]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro ξ
    calc
      ‖crossedFiberwiseOperator T ξ‖ ≤ ‖(‖T‖ : ℂ) • ξ‖ :=
        lp.norm_mono (by norm_num) (by
          intro k
          -- Expose the pointwise operator bound underneath the `lp` norm.
          change ‖T (ξ k)‖ ≤ ‖(‖T‖ : ℂ) • ξ k‖
          simpa only [Complex.coe_smul, norm_smul, norm_norm] using
            T.le_opNorm (ξ k))
      _ = ‖T‖ * ‖ξ‖ := by
        rw [lp.norm_const_smul (by norm_num : (2 : ℝ≥0∞) ≠ 0)]
        simp only [Complex.norm_real, norm_norm])

/-- Continuous coefficients act as a continuous family of fiberwise
multipliers on the regular crossed-product Hilbert space. -/
def continuousCrossedMultiplier
    (X : HaarProbabilityAction K Ω) :
    C(Ω, ℂ) →L[ℂ] (crossedHilbert X →L[ℂ] crossedHilbert X) :=
  (crossedFiberwiseOperatorContinuousLinearMap (K := K)
      (E := crossedBaseHilbert X)).comp
    (((ContinuousLinearMap.mul ℂ ℂ).holderL X.measure ⊤ 2 2).comp
      (ContinuousMap.toLp ⊤ X.measure ℂ))

/-- Evaluating the continuous-coefficient multiplier agrees with the
crossed-product multiplier of the corresponding `L∞` coefficient. -/
@[simp] theorem continuousCrossedMultiplier_apply
    (X : HaarProbabilityAction K Ω) (q : C(Ω, ℂ)) :
    continuousCrossedMultiplier X q =
      crossedMultiplier X (ContinuousMap.toLp ⊤ X.measure ℂ q) := rfl

/-- The regular crossed-product generators with all continuous coefficient
multipliers and all action unitaries. -/
def continuousCrossedGeneratorSet
    (X : HaarProbabilityAction K Ω) :
    Set (crossedHilbert X →L[ℂ] crossedHilbert X) :=
  Set.range (continuousCrossedMultiplier X) ∪
    Set.range fun k : K ↦
      (crossedGroupUnitary X k).toContinuousLinearEquiv.toContinuousLinearMap

/-- The regular crossed-product generators cut down to a specified family of
continuous coefficients, together with all action unitaries. -/
def crossedGeneratorSetOfContinuousCoefficients
    (X : HaarProbabilityAction K Ω) {I : Type*} (v : I → C(Ω, ℂ)) :
    Set (crossedHilbert X →L[ℂ] crossedHilbert X) :=
  Set.range (fun i ↦ continuousCrossedMultiplier X (v i)) ∪
    Set.range fun k : K ↦
      (crossedGroupUnitary X k).toContinuousLinearEquiv.toContinuousLinearMap

private theorem subset_vonNeumannClosure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (S : Set (E →L[ℂ] E)) :
    S ⊆ vonNeumannClosure S := by
  intro x hx
  rw [coe_vonNeumannClosure, StarSubalgebra.coe_centralizer_centralizer]
  exact Set.subset_centralizer_centralizer (Or.inl hx)

private theorem mem_vonNeumannClosure_of_subset
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {S T : Set (E →L[ℂ] E)} (hST : S ⊆ T)
    {x : E →L[ℂ] E} (hx : x ∈ vonNeumannClosure S) :
  x ∈ vonNeumannClosure T := by
  -- Membership is compared through the double-centralizer representation.
  rw [mem_vonNeumannClosure] at hx ⊢
  simp only [StarSubalgebra.mem_centralizer_iff] at hx ⊢
  intro z hzT
  apply hx z
  intro y hyS
  apply hzT y
  rcases hyS with hyS | hyS
  · exact Or.inl (hST hyS)
  · exact Or.inr (Set.mem_star.mpr (hST (Set.mem_star.mp hyS)))

private theorem continuousLinearMap_mem_vonNeumannClosure_of_dense_span
    {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {I : Type*} (F : Q →L[ℂ] (E →L[ℂ] E))
    (v : I → Q)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (S : Set (E →L[ℂ] E))
    (hgen : ∀ i, F (v i) ∈ vonNeumannClosure S)
    (q : Q) : F q ∈ vonNeumannClosure S := by
  let P : Submodule ℂ Q :=
    (vonNeumannClosure S).toStarSubalgebra.toSubalgebra.toSubmodule.comap
      F.toLinearMap
  have hspan : Submodule.span ℂ (Set.range v) ≤ P := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hgen i
  have hclosed : IsClosed (P : Set Q) := by
    -- Coercing the comap to a set exposes the preimage used by continuity.
    change IsClosed (F ⁻¹' (vonNeumannClosure S : Set (E →L[ℂ] E)))
    apply IsClosed.preimage F.continuous
    rw [coe_vonNeumannClosure]
    exact Set.isClosed_centralizer _
  have htop : (⊤ : Submodule ℂ Q) ≤ P := by
    rw [← hv]
    exact (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal
      hspan hclosed
  exact htop Submodule.mem_top

private theorem vonNeumannClosure_coe_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (M : VonNeumannAlgebra E) :
    vonNeumannClosure (M : Set (E →L[ℂ] E)) = M := by
  apply SetLike.coe_injective
  rw [coe_vonNeumannClosure, StarSubalgebra.coe_centralizer_centralizer,
    StarMemClass.star_coe_eq, Set.union_self, M.centralizer_centralizer]

private theorem vonNeumannClosure_le_of_subset
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {S T : Set (E →L[ℂ] E)}
    (hTS : T ⊆ vonNeumannClosure S) :
    (vonNeumannClosure T : Set (E →L[ℂ] E)) ⊆
      vonNeumannClosure S := by
  intro x hx
  have hx' := mem_vonNeumannClosure_of_subset hTS hx
  rw [vonNeumannClosure_coe_self] at hx'
  exact hx'

private theorem crossedGeneratorSetOfContinuousCoefficients_subset
    (X : HaarProbabilityAction K Ω) {I : Type*} (v : I → C(Ω, ℂ)) :
    crossedGeneratorSetOfContinuousCoefficients X v ⊆
      continuousCrossedGeneratorSet X := by
  rintro T (⟨i, rfl⟩ | ⟨k, rfl⟩)
  · exact Or.inl ⟨v i, rfl⟩
  · exact Or.inr ⟨k, rfl⟩

private theorem continuousCrossedGeneratorSet_subset_closure
    (X : HaarProbabilityAction K Ω) {I : Type*} (v : I → C(Ω, ℂ))
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    continuousCrossedGeneratorSet X ⊆
      vonNeumannClosure (crossedGeneratorSetOfContinuousCoefficients X v) := by
  rintro T (⟨q, rfl⟩ | ⟨k, rfl⟩)
  · apply continuousLinearMap_mem_vonNeumannClosure_of_dense_span
      (continuousCrossedMultiplier X) v hv
      (crossedGeneratorSetOfContinuousCoefficients X v)
    intro i
    exact subset_vonNeumannClosure
      (crossedGeneratorSetOfContinuousCoefficients X v)
      (Or.inl ⟨i, rfl⟩)
  · exact subset_vonNeumannClosure
      (crossedGeneratorSetOfContinuousCoefficients X v)
      (Or.inr ⟨k, rfl⟩)

/-- If a family of continuous coefficients has norm-dense linear span, then
its multipliers and the action unitaries generate the same von Neumann closure
as all continuous-coefficient multipliers and the action unitaries. -/
theorem vonNeumannClosure_crossedGeneratorSetOfContinuousCoefficients_eq
    (X : HaarProbabilityAction K Ω) {I : Type*} (v : I → C(Ω, ℂ))
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    vonNeumannClosure (crossedGeneratorSetOfContinuousCoefficients X v) =
      vonNeumannClosure (continuousCrossedGeneratorSet X) := by
  apply VonNeumannAlgebra.ext
  intro T
  constructor
  · exact mem_vonNeumannClosure_of_subset
      (crossedGeneratorSetOfContinuousCoefficients_subset X v)
  · intro hT
    exact vonNeumannClosure_le_of_subset
      (continuousCrossedGeneratorSet_subset_closure X v hv) hT

private theorem continuousCoefficient_toLp
    {X : HaarProbabilityAction K Ω} {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarHomeomorph X Y) (q : C(Ω, ℂ)) :
    Lp.compMeasurePreserving
        (EquivariantHaarEquiv.symm
          e.toEquivariantHaarEquiv).toMeasurableEquiv
        (EquivariantHaarEquiv.symm e.toEquivariantHaarEquiv).measure_preserving
        (ContinuousMap.toLp ⊤ X.measure ℂ q) =
      ContinuousMap.toLp ⊤ Y.measure ℂ
        ((e.toHomeomorph.symm.compStarAlgEquiv' ℂ ℂ) q) := by
  apply Lp.ext
  let he :=
    (EquivariantHaarEquiv.symm e.toEquivariantHaarEquiv).measure_preserving
  have hcomp := Lp.coeFn_compMeasurePreserving
    (ContinuousMap.toLp ⊤ X.measure ℂ q) he
  have hq := ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℂ) X.measure q
  have hq' := he.quasiMeasurePreserving.tendsto_ae hq
  have htarget := ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℂ)
    Y.measure ((e.toHomeomorph.symm.compStarAlgEquiv' ℂ ℂ) q)
  filter_upwards [hcomp, hq', htarget] with z hcomp hq' htarget
  rw [hcomp, htarget]
  -- Compare the two `Lp` representatives pointwise after pullback.
  change (ContinuousMap.toLp ⊤ X.measure ℂ q) (e.toHomeomorph.symm z) =
    ((e.toHomeomorph.symm.compStarAlgEquiv' ℂ ℂ) q) z
  rw [show (ContinuousMap.toLp ⊤ X.measure ℂ q) (e.toHomeomorph.symm z) =
      q (e.toHomeomorph.symm z) from hq']
  rfl

private theorem continuousCrossedMultiplier_conj
    {X : HaarProbabilityAction K Ω} {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarHomeomorph X Y) (q : C(Ω, ℂ)) :
    (crossedHaarHilbertEquiv e.toEquivariantHaarEquiv).conjStarAlgEquiv
        (continuousCrossedMultiplier X q) =
      continuousCrossedMultiplier Y
        ((e.toHomeomorph.symm.compStarAlgEquiv' ℂ ℂ) q) := by
  rw [continuousCrossedMultiplier_apply,
    continuousCrossedMultiplier_apply,
    crossedHaarHilbertEquiv_multiplier_conj]
  -- The multiplier theorem is stated for `L∞`; expose its pulled-back term.
  change crossedMultiplier Y
      (Lp.compMeasurePreserving
        (EquivariantHaarEquiv.symm
          e.toEquivariantHaarEquiv).toMeasurableEquiv
        (EquivariantHaarEquiv.symm
          e.toEquivariantHaarEquiv).measure_preserving
        (ContinuousMap.toLp ⊤ X.measure ℂ q)) = _
  rw [continuousCoefficient_toLp]

private theorem continuousCrossedGeneratorSet_image
    {X : HaarProbabilityAction K Ω} {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarHomeomorph X Y) :
    (crossedHaarHilbertEquiv e.toEquivariantHaarEquiv).conjStarAlgEquiv ''
        continuousCrossedGeneratorSet X =
      continuousCrossedGeneratorSet Y := by
  ext T
  constructor
  · rintro ⟨S, (⟨q, rfl⟩ | ⟨k, rfl⟩), rfl⟩
    · exact Or.inl ⟨(e.toHomeomorph.symm.compStarAlgEquiv' ℂ ℂ) q,
        (continuousCrossedMultiplier_conj e q).symm⟩
    · exact Or.inr ⟨k,
        (crossedHaarHilbertEquiv_group_conj
          e.toEquivariantHaarEquiv k).symm⟩
  · rintro (⟨q, rfl⟩ | ⟨k, rfl⟩)
    · obtain ⟨p, rfl⟩ :=
        (e.toHomeomorph.symm.compStarAlgEquiv' ℂ ℂ).surjective q
      exact ⟨continuousCrossedMultiplier X p, Or.inl ⟨p, rfl⟩,
        continuousCrossedMultiplier_conj e p⟩
    · exact ⟨_, Or.inr ⟨k, rfl⟩,
        crossedHaarHilbertEquiv_group_conj e.toEquivariantHaarEquiv k⟩

/-- An equivariant measure-preserving homeomorphism transports membership in
the von Neumann closure generated by continuous multipliers and action
unitaries. No compatibility with the compact-group additions is required. -/
theorem continuousCrossedClosure_mem_iff
    {X : HaarProbabilityAction K Ω} {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarHomeomorph X Y)
    (T : crossedHilbert X →L[ℂ] crossedHilbert X) :
    T ∈ vonNeumannClosure (continuousCrossedGeneratorSet X) ↔
      (crossedHaarHilbertEquiv e.toEquivariantHaarEquiv).conjStarAlgEquiv T ∈
        vonNeumannClosure (continuousCrossedGeneratorSet Y) := by
  exact mem_vonNeumannClosure_iff_of_conj_image_eq
    (crossedHaarHilbertEquiv e.toEquivariantHaarEquiv)
    (continuousCrossedGeneratorSet X) (continuousCrossedGeneratorSet Y)
    (continuousCrossedGeneratorSet_image e) T

end
end CrossedProduct
end Connes
