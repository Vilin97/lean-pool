/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitExtensionNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm
/-!
# Core comparisons for finite-tower idèle-class norms

This internal provider isolates the tensor base-change, embedding-product,
and direct-limit comparison lemmas used by the non-Galois finite-tower norm
theorem.  Keeping these commands in their own leaf prevents the endpoint
proof from rebuilding the helper environment.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity
namespace FiniteTowerNormCore

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

universe u

private theorem finiteTowerIdeleIsMulCommutative
    {K M L : Type u}
    [Field K] [NumberField K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] :
    IsMulCommutative (TowerRelativeIdeleGroup K M L) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] finiteTowerIdeleIsMulCommutative

/-- Algebra homomorphisms into an ambient field are equivalent to algebra
homomorphisms into the normal closure inside that field. -/
noncomputable def normalClosureAlgHomEquiv
    {F E L : Type u}
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] :
    (E →ₐ[F] L) ≃
      (E →ₐ[F] IntermediateField.normalClosure F E L) :=
  (normalClosure.algHomEquiv F E L).symm

/-- Lift an algebra homomorphism to the normal closure in its codomain. -/
noncomputable def normalClosureLiftAlgHom
    {F E L : Type u}
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L]
    (f : E →ₐ[F] L) :
    E →ₐ[F] IntermediateField.normalClosure F E L :=
  normalClosureAlgHomEquiv f

/-- Promote a ring homomorphism compatible with the scalar maps to an
algebra homomorphism. -/
def algHomOfCompatibleRingHom
    {R S A : Type u}
    [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R S] [Algebra R A]
    (f : S →+* A)
    (h : ∀ x : R, f (algebraMap R S x) = algebraMap R A x) :
    S →ₐ[R] A where
  toRingHom := f
  commutes' := h

private theorem relativeAdeleEmbedding_toAlgHom_unflatten
    {K M L : Type u}
    [Field K] [NumberField K]
    [Field M]
    [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    (a : RelativeAdeleRing K M) :
    towerRelativeAdeleUnflatten K M L
        (RelativeIdeleGroup.adeleEmbedding
          (IsScalarTower.toAlgHom K M L) a) =
      a ⊗ₜ[M] (1 : L) := by
  have hflatten :
      towerRelativeAdeleFlatten K M L
          (towerRelativeAdeleUnflatten K M L
            (RelativeIdeleGroup.adeleEmbedding
              (IsScalarTower.toAlgHom K M L) a)) =
        RelativeIdeleGroup.adeleEmbedding
          (IsScalarTower.toAlgHom K M L) a :=
    (towerRelativeAdeleRingEquiv K M L).apply_symm_apply _
  apply (towerRelativeAdeleRingEquiv K M L).injective
  change
    towerRelativeAdeleFlatten K M L
        (towerRelativeAdeleUnflatten K M L
          (RelativeIdeleGroup.adeleEmbedding
            (IsScalarTower.toAlgHom K M L) a)) =
      towerRelativeAdeleFlatten K M L
        (a ⊗ₜ[M] (1 : L))
  rw [hflatten, towerRelativeAdeleFlatten_tmul]
  simp only [map_one, mul_one]
  rfl

private theorem relativeIdeleEmbedding_toAlgHom_unflatten
    {K M L : Type u}
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    (a : RelativeIdeleGroup K M) :
    letI : Algebra M (RelativeAdeleRing K M) :=
      relativeAdeleRingIntermediateAlgebra K M
    (towerRelativeIdeleEquiv K M L).symm
        (RelativeIdeleGroup.ideleEmbedding
          (IsScalarTower.toAlgHom K M L) a) =
      (Units.map
        (@Algebra.TensorProduct.includeLeft
          M M (RelativeAdeleRing K M) L
          inferInstance inferInstance
          (relativeAdeleRingIntermediateAlgebra K M)
          inferInstance inferInstance inferInstance
          (relativeAdeleRingIntermediateAlgebra K M)
          (smulCommClass_self M (RelativeAdeleRing K M))).toRingHom a :
        TowerRelativeIdeleGroup K M L) := by
  let _ : Algebra M (RelativeAdeleRing K M) :=
    relativeAdeleRingIntermediateAlgebra K M
  apply Units.ext
  exact relativeAdeleEmbedding_toAlgHom_unflatten
    (K := K) (M := M) (L := L) (a : RelativeAdeleRing K M)

private theorem
    relativeIdeleClassEmbedding_toAlgHom_towerBaseChange
    {K M L : Type u}
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    (c : RelativeIdeleGroup.ClassGroup K M) :
    towerRelativeIdeleClassBaseChangeMulEquiv K M L
        ((TowerRelativeIdeleGroup.classGroupEquiv K M L).symm
          (RelativeIdeleGroup.classEmbedding
            (IsScalarTower.toAlgHom K M L) c)) =
      RelativeIdeleGroup.classInclusion M L
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M) c) := by
  let _ : Algebra M (RelativeAdeleRing K M) :=
    relativeAdeleRingIntermediateAlgebra K M
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup M L)
        (towerRelativeIdeleBaseChangeMulEquiv K M L
          ((towerRelativeIdeleEquiv K M L).symm
            (RelativeIdeleGroup.ideleEmbedding
              (IsScalarTower.toAlgHom K M L) a))) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup M L)
        (RelativeIdeleGroup.inclusion M L
          (relativeIdeleBaseChangeMulEquiv
            (K := K) (L := M) a))
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup M L))
  rw [relativeIdeleEmbedding_toAlgHom_unflatten
    (K := K) (M := M) (L := L) a]
  exact towerRelativeIdeleBaseChangeMulEquiv_includeLeft K M L a

theorem
    relativeIdeleClassBaseChange_classEmbedding_toAlgHom
    {K M L : Type u}
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    (c : RelativeIdeleGroup.ClassGroup K M) :
    _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.classEmbedding
          (IsScalarTower.toAlgHom K M L) c) =
      _root_.ideleClassExtension M L
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M) c) := by
  calc
    _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.classEmbedding
          (IsScalarTower.toAlgHom K M L) c) =
      _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := M) (L := L)
        (towerRelativeIdeleClassBaseChangeMulEquiv K M L
          ((TowerRelativeIdeleGroup.classGroupEquiv K M L).symm
            (RelativeIdeleGroup.classEmbedding
              (IsScalarTower.toAlgHom K M L) c))) :=
      (relativeIdeleClassBaseChangeMulEquiv_tower K M L _).symm
    _ = _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := M) (L := L)
        (RelativeIdeleGroup.classInclusion M L
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := K) (L := M) c)) := by
      rw [relativeIdeleClassEmbedding_toAlgHom_towerBaseChange
        (K := K) (M := M) (L := L) c]
    _ = _root_.ideleClassExtension M L
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M) c) :=
      relativeIdeleClassBaseChangeMulEquiv_classInclusion _

theorem classEmbedding_smul_eq_classEmbedding_comp
    {K E U : Type u}
    [Field K] [NumberField K]
    [Field E] [Field U]
    [Algebra K E] [Algebra K U]
    (j : E →ₐ[K] U) (σ : U ≃ₐ[K] U)
    (c : RelativeIdeleGroup.ClassGroup K E) :
    σ • RelativeIdeleGroup.classEmbedding j c =
      RelativeIdeleGroup.classEmbedding (σ.toAlgHom.comp j) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K U)
        (σ • RelativeIdeleGroup.ideleEmbedding j a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K U)
        (RelativeIdeleGroup.ideleEmbedding
          (σ.toAlgHom.comp j) a)
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K U))
  apply Units.ext
  change
    RelativeIdeleGroup.conjugation K U σ
        (RelativeIdeleGroup.adeleEmbedding j
          (a : RelativeAdeleRing K E)) =
      RelativeIdeleGroup.adeleEmbedding
        (σ.toAlgHom.comp j) (a : RelativeAdeleRing K E)
  induction (a : RelativeAdeleRing K E) using
      TensorProduct.inductionOn with
  | tmul y x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul,
        RelativeIdeleGroup.conjugation_tmul]
      congr 1
  | add x y hx hy =>
      simp only [map_add, hx, hy]

private theorem classEmbedding_changeBase
    {k F E U : Type u}
    [Field k] [NumberField k]
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Field U] [NumberField U]
    [Algebra k F] [Algebra F E] [Algebra k E]
    [Algebra E U] [Algebra F U] [Algebra k U]
    [IsScalarTower k F E] [IsScalarTower F E U]
    [IsScalarTower k F U] [IsScalarTower k E U]
    [FiniteDimensional k F] [FiniteDimensional F E]
    [FiniteDimensional E U] [FiniteDimensional F U]
    [IsGalois F U]
    (f : E →ₐ[F] U) (c : IdeleClassGroup E) :
    towerRelativeIdeleClassBaseChangeMulEquiv k F U
        ((TowerRelativeIdeleGroup.classGroupEquiv k F U).symm
          (RelativeIdeleGroup.classEmbedding
            (f.restrictScalars k)
            ((_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := k) (L := E)).symm c))) =
      RelativeIdeleGroup.classEmbedding f
        ((_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F) (L := E)).symm c) := by
  let jₖ : E →ₐ[k] U := IsScalarTower.toAlgHom k E U
  let jF : E →ₐ[F] U := IsScalarTower.toAlgHom F E U
  let dₖ : RelativeIdeleGroup.ClassGroup k E :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := k) (L := E)).symm c
  let dF : RelativeIdeleGroup.ClassGroup F E :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := F) (L := E)).symm c
  have hcanonical :
      towerRelativeIdeleClassBaseChangeMulEquiv k F U
          ((TowerRelativeIdeleGroup.classGroupEquiv k F U).symm
            (RelativeIdeleGroup.classEmbedding jₖ dₖ)) =
        RelativeIdeleGroup.classEmbedding jF dF := by
    apply (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := F) (L := U)).injective
    calc
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F) (L := U)
          (towerRelativeIdeleClassBaseChangeMulEquiv k F U
            ((TowerRelativeIdeleGroup.classGroupEquiv k F U).symm
              (RelativeIdeleGroup.classEmbedding jₖ dₖ))) =
          _root_.relativeIdeleClassBaseChangeMulEquiv
            (K := k) (L := U)
            (RelativeIdeleGroup.classEmbedding jₖ dₖ) :=
        relativeIdeleClassBaseChangeMulEquiv_tower k F U _
      _ = _root_.ideleClassExtension E U c := by
        rw [relativeIdeleClassBaseChange_classEmbedding_toAlgHom
          (K := k) (M := E) (L := U) dₖ]
        exact congrArg (_root_.ideleClassExtension E U)
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := k) (L := E)).apply_symm_apply c)
      _ = _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F) (L := U)
          (RelativeIdeleGroup.classEmbedding jF dF) := by
        rw [relativeIdeleClassBaseChange_classEmbedding_toAlgHom
          (K := F) (M := E) (L := U) dF]
        exact congrArg (_root_.ideleClassExtension E U)
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := F) (L := E)).apply_symm_apply c).symm
  let σ : U ≃ₐ[F] U :=
    RelativeIdeleGroup.liftSubextensionEmbedding f
  have hσ : RelativeIdeleGroup.restrictToSubextension σ = f :=
    RelativeIdeleGroup.restrict_liftSubextensionEmbedding f
  have hrestrict :
      (σ.restrictScalars k).toAlgHom.comp jₖ =
        f.restrictScalars k := by
    apply AlgHom.ext
    intro x
    have hx := DFunLike.congr_fun hσ x
    exact hx
  have hrestrictF : σ.toAlgHom.comp jF = f := by
    exact hσ
  rw [← hrestrict, ← hrestrictF]
  calc
    towerRelativeIdeleClassBaseChangeMulEquiv k F U
        ((TowerRelativeIdeleGroup.classGroupEquiv k F U).symm
          (RelativeIdeleGroup.classEmbedding
            ((σ.restrictScalars k).toAlgHom.comp jₖ) dₖ)) =
      towerRelativeIdeleClassBaseChangeMulEquiv k F U
        ((TowerRelativeIdeleGroup.classGroupEquiv k F U).symm
          ((σ.restrictScalars k) •
            RelativeIdeleGroup.classEmbedding jₖ dₖ)) := by
        rw [classEmbedding_smul_eq_classEmbedding_comp]
    _ = σ •
        towerRelativeIdeleClassBaseChangeMulEquiv k F U
          ((TowerRelativeIdeleGroup.classGroupEquiv k F U).symm
            (RelativeIdeleGroup.classEmbedding jₖ dₖ)) :=
      towerRelativeIdeleClassBaseChangeMulEquiv_smul
        k F U σ (RelativeIdeleGroup.classEmbedding jₖ dₖ)
    _ = σ • RelativeIdeleGroup.classEmbedding jF dF := by
      rw [hcanonical]
    _ = RelativeIdeleGroup.classEmbedding
        (σ.toAlgHom.comp jF) dF :=
      classEmbedding_smul_eq_classEmbedding_comp jF σ dF

theorem relativeIdeleClassBaseChange_classEmbedding_changeBase
    {k F E U : Type u}
    [Field k] [NumberField k]
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Field U] [NumberField U]
    [Algebra k F] [Algebra F E] [Algebra k E]
    [Algebra E U] [Algebra F U] [Algebra k U]
    [IsScalarTower k F E] [IsScalarTower F E U]
    [IsScalarTower k F U] [IsScalarTower k E U]
    [FiniteDimensional k F] [FiniteDimensional F E]
    [FiniteDimensional E U] [FiniteDimensional F U]
    [IsGalois F U]
    (f : E →ₐ[F] U) (c : IdeleClassGroup E) :
    _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := k) (L := U)
        (RelativeIdeleGroup.classEmbedding
          (f.restrictScalars k)
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := k) (L := E)).symm c)) =
      _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F) (L := U)
        (RelativeIdeleGroup.classEmbedding f
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := F) (L := E)).symm c)) := by
  have hchange := classEmbedding_changeBase
    (k := k) (F := F) (E := E) (U := U) f c
  rw [← hchange]
  exact (relativeIdeleClassBaseChangeMulEquiv_tower
    k F U
    (RelativeIdeleGroup.classEmbedding
      (f.restrictScalars k)
      ((_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := k) (L := E)).symm c))).symm

private theorem classEmbedding_comp
    {K E N U : Type u}
    [Field K] [NumberField K]
    [Field E] [Field N] [Field U]
    [Algebra K E] [Algebra K N] [Algebra K U]
    (f : E →ₐ[K] N) (g : N →ₐ[K] U)
    (c : RelativeIdeleGroup.ClassGroup K E) :
    RelativeIdeleGroup.classEmbedding g
        (RelativeIdeleGroup.classEmbedding f c) =
      RelativeIdeleGroup.classEmbedding (g.comp f) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K U)
        (RelativeIdeleGroup.ideleEmbedding g
          (RelativeIdeleGroup.ideleEmbedding f a)) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K U)
        (RelativeIdeleGroup.ideleEmbedding (g.comp f) a)
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K U))
  apply Units.ext
  change
    RelativeIdeleGroup.adeleEmbedding g
        (RelativeIdeleGroup.adeleEmbedding f
          (a : RelativeAdeleRing K E)) =
      RelativeIdeleGroup.adeleEmbedding (g.comp f)
        (a : RelativeAdeleRing K E)
  induction (a : RelativeAdeleRing K E) using
      TensorProduct.inductionOn with
  | tmul y x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul]
      rfl
  | add x y hx hy =>
      simp only [map_add, hx, hy]

theorem relativeIdeleClassBaseChange_prod_embeddings
    {F E N U Q : Type u}
    [Field F] [NumberField F]
    [Field E] [Field N]
    [Field U] [NumberField U]
    [Algebra F E] [Algebra F N] [Algebra F U]
    [Algebra E N] [IsScalarTower F E N]
    [FiniteDimensional F E] [FiniteDimensional F N]
    [FiniteDimensional F U] [IsGalois F N]
    [Fintype Q]
    (e : Q ≃ (E →ₐ[F] N)) (j : N →ₐ[F] U)
    (c : RelativeIdeleGroup.ClassGroup F E) :
    (∏ q : Q,
      _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F) (L := U)
        (RelativeIdeleGroup.classEmbedding (j.comp (e q)) c)) =
      _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F) (L := U)
        (RelativeIdeleGroup.classEmbedding j
          (RelativeIdeleGroup.classInclusion F N
            (RelativeIdeleGroup.classNorm F E c))) := by
  rw [← map_prod]
  apply congrArg
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := F) (L := U))
  calc
    ∏ q : Q, RelativeIdeleGroup.classEmbedding (j.comp (e q)) c =
        ∏ f : E →ₐ[F] N,
          RelativeIdeleGroup.classEmbedding (j.comp f) c := by
      exact Fintype.prod_equiv e
        (fun q => RelativeIdeleGroup.classEmbedding (j.comp (e q)) c)
        (fun f => RelativeIdeleGroup.classEmbedding (j.comp f) c)
        (fun _ => rfl)
    _ = RelativeIdeleGroup.classEmbedding j
        (∏ f : E →ₐ[F] N,
          RelativeIdeleGroup.classEmbedding f c) := by
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro f _
      exact (classEmbedding_comp f j c).symm
    _ = RelativeIdeleGroup.classEmbedding j
        (RelativeIdeleGroup.classInclusion F N
          (RelativeIdeleGroup.classNorm F E c)) := by
      rw [RelativeIdeleGroup.classInclusion_ideleClassNorm_eq_prod_embeddings]

theorem
    rationalIntermediateIdeleClassToDirectLimit_classEmbedding
    (E : IntermediateField ℚ (SeparableClosure ℚ))
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ E]
    (hEU : E ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)))
    (c : IdeleClassGroup E) :
    rationalIntermediateIdeleClassToDirectLimit E c =
      rationalRelativeIdeleClassToDirectLimit U
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU)
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E)).symm c)) := by
  let d : RelativeIdeleGroup.ClassGroup ℚ E :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := E)).symm c
  calc
    rationalIntermediateIdeleClassToDirectLimit E c =
        rationalIntermediateIdeleClassToDirectLimit U
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := U)
            (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
              (IntermediateField.inclusion hEU) d)) := by
      rw [show c = _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) d by
        exact ((_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E)).apply_symm_apply c).symm]
      exact (rationalIntermediateIdeleClassToDirectLimit_extension
        hEU d).symm
    _ = rationalRelativeIdeleClassToDirectLimit U
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) d) :=
      rationalFiniteGaloisIdeleClassToDirectLimit_baseChange
        U (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) d)

end FiniteTowerNormCore
end Reciprocity
end GlobalClassFieldTheory
