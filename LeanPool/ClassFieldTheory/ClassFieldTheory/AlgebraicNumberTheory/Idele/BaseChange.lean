/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.FiniteRestrictedProductBaseChange
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.InfinitePlaceTensorBlock
/-!
# Scalar extension from relative to ordinary ideles

The finite restricted-product comparison is combined here with the
archimedean form of the canonical local tensor decomposition. Infinite places above a fixed
infinite place of the base field are identified with exact extensions of
its absolute value.  Surjectivity is reduced through the finite normal
closure to the Galois valuation-extension comparison.
-/

@[expose] public section

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable
section


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Restriction of an infinite place of `L` to the base field. -/
def infinitePlaceBelow
    (W : InfinitePlace L) : InfinitePlace K :=
  W.comap (algebraMap K L)

omit [NumberField K] in
/-- Restricting an infinite place along the identity extension fixes it. -/
@[simp]
theorem infinitePlaceBelow_self
    (W : InfinitePlace K) :
    infinitePlaceBelow (K := K) W = W := by
  rw [infinitePlaceBelow,
    Algebra.algebraMap_self, InfinitePlace.comap_id]

section InfinitePlaceTower

variable {M : Type*}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]

omit [NumberField K] [NumberField L] [NumberField M]
    [FiniteDimensional K L] in
/-- Restriction of infinite places is transitive in a tower of number
fields. -/
@[simp]
theorem infinitePlaceBelow_infinitePlaceBelow
    (W : InfinitePlace L) :
    infinitePlaceBelow (K := K)
        (infinitePlaceBelow (K := M) W) =
      infinitePlaceBelow (K := K) W := by
  rw [infinitePlaceBelow, infinitePlaceBelow, infinitePlaceBelow,
    ← InfinitePlace.comap_comp,
    IsScalarTower.algebraMap_eq K M L]

end InfinitePlaceTower

omit [NumberField K] in
/-- The map on infinite-place completions induced by the identity field
extension is the identity map. -/
@[simp]
theorem infinitePlaceCompletionMap_self_apply
    (W : InfinitePlace K)
    (x : W.Completion) :
    letI : W.1.LiesOver W.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1)
        (infinitePlaceBelow_self (K := K) W)⟩
    NumberField.LiesOver.completionMap
        (v := W) (w := W) x = x := by
  let : W.1.LiesOver W.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1)
      (infinitePlaceBelow_self (K := K) W)⟩
  refine InfinitePlace.Completion.induction_on W x ?_ ?_
  · exact isClosed_eq
      NumberField.LiesOver.continuous_completionMap
      continuous_id
  · intro y
    change
      NumberField.LiesOver.completionMap
          (y : W.Completion) =
        (y : W.Completion)
    rw [NumberField.LiesOver.completionMap_coe
      (v := W) (w := W) y]
    have hy :
        algebraMap (WithAbs W.1) (WithAbs W.1) y = y := by
      apply (WithAbs.equiv W.1).injective
      change
        algebraMap K K (WithAbs.equiv W.1 y) =
          WithAbs.equiv W.1 y
      rw [Algebra.algebraMap_self]
      rfl
    exact
      congrArg
        (fun z : WithAbs W.1 => (z : W.Completion)) hy

/-- Completion maps at infinite places compose in a tower of number
fields. -/
theorem infinitePlaceCompletionMap_comp_apply
    {M : Type*}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]
    (W : InfinitePlace L)
    (x :
      (infinitePlaceBelow
        (K := K) W).Completion) :
    let V :=
      infinitePlaceBelow (K := M) W
    let v :=
      infinitePlaceBelow (K := K) W
    letI : V.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1)
        (infinitePlaceBelow_infinitePlaceBelow
          (K := K) (M := M) (L := L) W)⟩
    letI : W.1.LiesOver V.1 := ⟨rfl⟩
    letI : W.1.LiesOver v.1 := ⟨rfl⟩
    NumberField.LiesOver.completionMap
        (v := V) (w := W)
        (NumberField.LiesOver.completionMap
          (v := v) (w := V) x) =
      NumberField.LiesOver.completionMap
        (v := v) (w := W) x := by
  dsimp only
  let V :=
    infinitePlaceBelow (K := M) W
  let v :=
    infinitePlaceBelow (K := K) W
  let : V.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1)
      (infinitePlaceBelow_infinitePlaceBelow
        (K := K) (M := M) (L := L) W)⟩
  let : W.1.LiesOver V.1 := ⟨rfl⟩
  let : W.1.LiesOver v.1 := ⟨rfl⟩
  refine InfinitePlace.Completion.induction_on v x ?_ ?_
  · exact isClosed_eq
      ((NumberField.LiesOver.continuous_completionMap
          (v := V) (w := W)).comp
        (NumberField.LiesOver.continuous_completionMap
          (v := v) (w := V)))
      (NumberField.LiesOver.continuous_completionMap
        (v := v) (w := W))
  · intro y
    rw [NumberField.LiesOver.completionMap_coe
        (v := v) (w := V) y,
      NumberField.LiesOver.completionMap_coe
        (v := V) (w := W)
        (algebraMap (WithAbs v.1) (WithAbs V.1) y),
      NumberField.LiesOver.completionMap_coe
        (v := v) (w := W) y]
    apply congrArg
      (fun z : WithAbs W.1 => (z : W.Completion))
    apply (WithAbs.equiv W.1).injective
    change
      algebraMap M L
          (algebraMap K M (WithAbs.equiv v.1 y)) =
        algebraMap K L (WithAbs.equiv v.1 y)
    rw [IsScalarTower.algebraMap_apply K M L]

/-- An infinite place above `w`, regarded as an exact extension of the
underlying absolute value. -/
def infinitePlaceAboveToExtension
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    AbsoluteValueExtension w.1 L := by
  refine ⟨W.1.1, ?_⟩
  intro x
  have h :=
    congrArg (fun v : InfinitePlace K => v x) W.2
  exact h

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- For a finite Galois extension, every extension of an infinite-place
absolute value is represented by an infinite place above the base
place. -/
theorem
    infinitePlaceAboveToExtension_surjective_of_isGalois
    [IsGalois K L]
    (w : InfinitePlace K) :
    Function.Surjective
      (infinitePlaceAboveToExtension
        (K := K) (L := L) w) := by
  intro u
  obtain ⟨W₀, hW₀⟩ :=
    InfinitePlace.comap_surjective
      (k := K) (K := L) w
  let W₀' :
      {W : InfinitePlace L //
        infinitePlaceBelow (K := K) W = w} :=
    ⟨W₀, hW₀⟩
  let u₀ : AbsoluteValueExtension w.1 L :=
    infinitePlaceAboveToExtension
      (K := K) (L := L) w W₀'
  obtain ⟨σ, hσ⟩ :=
    absoluteValueConjugacy w.1 w.isNontrivial u₀ u
  let Wσ : InfinitePlace L :=
    W₀.comap σ.toRingEquiv.toRingHom
  have hWσ :
      infinitePlaceBelow (K := K) Wσ = w := by
    apply InfinitePlace.ext
    intro x
    change W₀ (σ (algebraMap K L x)) = w x
    rw [σ.commutes]
    exact congrArg (fun v : InfinitePlace K => v x) hW₀
  refine ⟨⟨Wσ, hWσ⟩, ?_⟩
  rw [hσ]
  apply Subtype.ext
  rfl

/-- Infinite places of `L` above `w` are exactly the exact extensions of
the absolute value represented by `w`. -/
noncomputable def infinitePlaceAboveEquivExtension
    (w : InfinitePlace K) :
    {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w} ≃
      AbsoluteValueExtension w.1 L := by
  apply Equiv.ofBijective
    (infinitePlaceAboveToExtension
      (K := K) (L := L) w)
  constructor
  · intro W W' h
    have habs : W.1.1 = W'.1.1 :=
      congrArg
        (fun u : AbsoluteValueExtension w.1 L => u.1) h
    apply Subtype.ext
    apply Subtype.ext
    exact habs
  · intro u
    let M := finiteNormalClosure K L
    let e : L →ₐ[K] M :=
      finiteNormalClosureEmbedding K L
    let : Algebra L M :=
      e.toRingHom.toAlgebra
    let : IsScalarTower K L M :=
      IsScalarTower.of_algebraMap_eq'
        e.comp_algebraMap.symm
    let : FiniteDimensional L M :=
      FiniteDimensional.right K L M
    let hu : u.1.IsNontrivial :=
      u.isNontrivial w.isNontrivial
    let uOverL : AbsoluteValueExtension u.1 M :=
      pullbackAbsoluteValueExtension
        u.1 hu IsAlgClosed.lift
    let uM : AbsoluteValueExtension w.1 M :=
      { val := uOverL.1
        property := by
          intro x
          rw [IsScalarTower.algebraMap_apply K L M,
            uOverL.2, u.2] }
    obtain ⟨WM, hWM⟩ :=
      infinitePlaceAboveToExtension_surjective_of_isGalois
        (K := K) (L := M) w uM
    let WL : InfinitePlace L :=
      WM.1.comap (algebraMap L M)
    have hWL :
        infinitePlaceBelow (K := K) WL = w := by
      apply InfinitePlace.ext
      intro x
      change
        WM.1
            (algebraMap L M
              (algebraMap K L x)) =
          w x
      rw [← IsScalarTower.algebraMap_apply K L M]
      exact congrArg (fun v : InfinitePlace K => v x) WM.2
    refine ⟨⟨WL, hWL⟩, ?_⟩
    apply Subtype.ext
    ext x
    have hWMval :
        WM.1.1 = uM.1 :=
      congrArg Subtype.val hWM
    change
      WM.1.1 (algebraMap L M x) = u.1 x
    rw [hWMval]
    exact uOverL.2 x

/-- The absolute value underlying the extension corresponding to an
infinite place above `w`. -/
@[simp]
theorem infinitePlaceAboveEquivExtension_apply_val
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    (infinitePlaceAboveEquivExtension
      (K := K) (L := L) w W).1 = W.1.1 :=
  rfl

/-- Reindex the relative completion product by actual infinite
places above `w`. -/
noncomputable def infiniteCompletionProductReindexAbove
    (w : InfinitePlace K) :
    (∀ u : AbsoluteValueExtension w.1 L,
      u.1.Completionˣ) ≃*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.1.Completionˣ := by
  let e :=
    Equiv.piCongrLeft'
      (fun u : AbsoluteValueExtension w.1 L =>
        u.1.Completionˣ)
      (infinitePlaceAboveEquivExtension
        (K := K) (L := L) w).symm
  exact
    { e with
      map_mul' := by
        intro x y
        funext W
        rfl }

/-- Replace the absolute-value completion in every factor by mathlib's
concrete infinite-place completion. -/
noncomputable def infiniteCompletionProductEquivAbove
    (w : InfinitePlace K) :
    (∀ u : AbsoluteValueExtension w.1 L,
      u.1.Completionˣ) ≃*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completionˣ :=
  (infiniteCompletionProductReindexAbove
    (K := K) (L := L) w).trans
    (MulEquiv.piCongrRight fun W =>
      Units.mapEquiv
        (InfinitePlace.Completion.equiv W.1).symm.toMulEquiv)

/-- The canonical local tensor decomposition for the actual archimedean tensor component, with
codomain indexed by concrete infinite places above the base place. -/
noncomputable def infinitePlaceTensorUnitsEquivAbove
    (w : InfinitePlace K) :
    (w.Completion ⊗[K] L)ˣ ≃*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completionˣ := by
  letI : ∀ u : AbsoluteValueExtension w.1 L,
      Algebra w.1.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra w.1 u.1 u.2
  exact
    (infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) w).trans
      ((localTensorUnitsEquivCompletionProduct
        (K := K) (L := L) w.1 w.isNontrivial).trans
        (infiniteCompletionProductEquivAbove
          (K := K) (L := L) w))

/-- Evaluation formula for the archimedean relative-to-ordinary
comparison at a concrete infinite place above the base place. -/
@[simp]
theorem infinitePlaceTensorUnitsEquivAbove_apply
    (w : InfinitePlace K)
    (z : (w.Completion ⊗[K] L)ˣ)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    infinitePlaceTensorUnitsEquivAbove
        (K := K) (L := L) w z W =
      Units.mapEquiv
          (InfinitePlace.Completion.equiv W.1).symm.toMulEquiv
        (localTensorUnitsEquivCompletionProduct
          w.1 w.isNontrivial
          (infinitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) w z)
        (infinitePlaceAboveEquivExtension
          (K := K) (L := L) w W)) :=
  rfl

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- After replacing the concrete completion by the underlying
absolute-value completion, scalar extension of a local unit is the pure
tensor with right factor one. -/
@[simp]
theorem infinitePlaceLocalTensorUnitsEquiv_infiniteLocalIdeleInclusion_coe
    (w : InfinitePlace K) (x : w.Completionˣ) :
    (infinitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) w
        (infiniteLocalIdeleInclusion
          (K := K) (L := L) w x) :
      LocalClassFieldTheory.LocalTensorAlgebra (L := L) w.1) =
      infinitePlaceCompletionAlgEquiv w
          (x : w.Completion) ⊗ₜ[K] (1 : L) := by
  rfl

/-- On a diagonal extension-field unit, the infinite local
relative-to-ordinary comparison is the ordinary diagonal embedding. -/
theorem infinitePlaceTensorUnitsEquivAbove_localFieldIdeleInclusion
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w})
    (x : Lˣ) :
    infinitePlaceTensorUnitsEquivAbove
        (K := K) (L := L) w
        (infiniteLocalFieldIdeleInclusion
          (K := K) (L := L) w x) W =
      Units.map
        (algebraMap L W.1.Completion)
        x := by
  rw [infinitePlaceTensorUnitsEquivAbove_apply]
  apply Units.ext
  simp only [Units.coe_map]
  change
    (InfinitePlace.Completion.equiv W.1).symm
        (completionTensorDecompositionLeft
          w.1 w.isNontrivial
          (1 ⊗ₜ[K] (x : L))
          (infinitePlaceAboveEquivExtension
            (K := K) (L := L) w W)) =
      algebraMap L W.1.Completion (x : L)
  rw [completionTensorDecomposition_left_tmul_apply]
  simp only [map_one, one_mul]
  apply InfinitePlace.Completion.ext
  rfl

/-- Flatten the products over base infinite places and places above them
to the product over all infinite places of `L`. -/
noncomputable def infinitePlaceAbovePiMulEquiv :
    (∀ w : InfinitePlace K,
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completionˣ) ≃*
      ∀ W : InfinitePlace L, W.Completionˣ where
  toFun f W :=
    f (infinitePlaceBelow (K := K) W) ⟨W, rfl⟩
  invFun f w W := f W.1
  left_inv f := by
    funext w W
    rcases W with ⟨W, hW⟩
    subst w
    rfl
  right_inv f := by
    funext W
    rfl
  map_mul' f g := by
    funext W
    rfl

/-- The unrestricted product of all archimedean tensor-unit factors is
the product of the concrete archimedean local unit groups of `L`. -/
noncomputable def relativeInfiniteTensorPiMulEquiv :
    (∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ) ≃*
      ∀ W : InfinitePlace L, W.Completionˣ :=
  (MulEquiv.piCongrRight fun w =>
    infinitePlaceTensorUnitsEquivAbove
      (K := K) (L := L) w).trans
    (infinitePlaceAbovePiMulEquiv
      (K := K) (L := L))

/-- Evaluation of the archimedean tensor-product comparison at an
infinite place of the extension field. -/
@[simp]
theorem relativeInfiniteTensorPiMulEquiv_apply
    (f : ∀ w : InfinitePlace K, (w.Completion ⊗[K] L)ˣ)
    (W : InfinitePlace L) :
    relativeInfiniteTensorPiMulEquiv (K := K) (L := L) f W =
      infinitePlaceTensorUnitsEquivAbove
        (K := K) (L := L)
        (infinitePlaceBelow (K := K) W)
        (f (infinitePlaceBelow (K := K) W))
        ⟨W, rfl⟩ := rfl

/-- The archimedean relative tensor factors form the ordinary infinite
idele group of `L`. -/
noncomputable def relativeInfiniteIdeleMulEquiv :
    (∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ) ≃*
      InfiniteIdeleGroup L :=
  (relativeInfiniteTensorPiMulEquiv
    (K := K) (L := L)).trans
    ContinuousMulEquiv.piUnits.symm.toMulEquiv

/-- Multiplication in the transported finite relative restricted product
is pointwise on its local tensor factors. -/
@[simp]
theorem RelativeFiniteIdeleData.finite_mul
    (a b : RelativeFiniteIdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    (a * b).finite w = a.finite w * b.finite w := by
  change
    (relativeFiniteTensorPiMulEquiv
      (K := K) (L := L)).symm
        (relativeFiniteTensorPiMulEquiv
            (K := K) (L := L) a.finite *
          relativeFiniteTensorPiMulEquiv
            (K := K) (L := L) b.finite) w =
      a.finite w * b.finite w
  rw [← map_mul,
    (relativeFiniteTensorPiMulEquiv
      (K := K) (L := L)).symm_apply_apply]
  rfl

/-- Forget the infinite component of restricted local idele data. -/
noncomputable def RelativeLocalIdeleData.toFiniteData
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    RelativeFiniteIdeleData (K := K) (L := L) where
  finite := a.finite
  eventually_integral := a.eventually_integral
  eventually_inverse_integral :=
    a.eventually_inverse_integral

/-- Passing relative local idele data to finite data preserves
multiplication. -/
@[simp]
theorem RelativeLocalIdeleData.toFiniteData_mul
    (a b : RelativeLocalIdeleData (K := K) (L := L)) :
    (a * b).toFiniteData =
      a.toFiniteData * b.toFiniteData := by
  apply RelativeFiniteIdeleData.ext
  funext w
  rw [RelativeFiniteIdeleData.finite_mul]
  change (a * b).finite w = a.finite w * b.finite w
  exact RelativeLocalIdeleData.finite_mul
    (K := K) (L := L) a b w

/-- Split restricted local idele data into its unrestricted infinite part
and finite restricted part. -/
noncomputable def relativeLocalIdeleDataSplitMulEquiv :
    RelativeLocalIdeleData (K := K) (L := L) ≃*
      ((∀ w : InfinitePlace K,
          (w.Completion ⊗[K] L)ˣ) ×
        RelativeFiniteIdeleData (K := K) (L := L)) where
  toFun a :=
    ⟨a.infinite, a.toFiniteData⟩
  invFun a :=
    { infinite := a.1
      finite := a.2.finite
      eventually_integral := a.2.eventually_integral
      eventually_inverse_integral :=
        a.2.eventually_inverse_integral }
  left_inv a := by
    apply RelativeLocalIdeleData.ext <;> rfl
  right_inv a := by
    rcases a with ⟨a, b⟩
    rfl
  map_mul' a b := by
    apply Prod.ext
    · funext w
      exact RelativeLocalIdeleData.infinite_mul
        (K := K) (L := L) a b w
    · exact RelativeLocalIdeleData.toFiniteData_mul
        (K := K) (L := L) a b

/-- Scalar extension identifies the actual relative
idele group `I_K ⊗_K L` with the ordinary idele group `I_L`. -/
noncomputable def relativeIdeleBaseChangeMulEquiv :
    RelativeIdeleGroup K L ≃* IdeleGroup L :=
  (relativeIdeleMulEquivLocalData
    (K := K) (L := L)).trans
    ((relativeLocalIdeleDataSplitMulEquiv
      (K := K) (L := L)).trans
      ((relativeInfiniteIdeleMulEquiv
        (K := K) (L := L)).prodCongr
        (relativeFiniteIdeleMulEquiv
          (K := K) (L := L))))

/-- The infinite component of the relative idele base-change
equivalence. -/
@[simp]
theorem relativeIdeleBaseChangeMulEquiv_infinite
    (z : RelativeIdeleGroup K L) :
    (relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L) z).1 =
      relativeInfiniteIdeleMulEquiv
        (K := K) (L := L)
        (relativeIdeleToLocalData
          (K := K) (L := L) z).infinite :=
  rfl

/-- The finite component of the relative idele base-change
equivalence. -/
@[simp]
theorem relativeIdeleBaseChangeMulEquiv_finite
    (z : RelativeIdeleGroup K L) :
    (relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L) z).2 =
      relativeFiniteIdeleToFiniteIdele
        (K := K) (L := L)
        (relativeIdeleToLocalData
          (K := K) (L := L) z).toFiniteData :=
  rfl
