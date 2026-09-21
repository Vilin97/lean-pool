/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
/-!
# The fixed-bottom tower model and the actual intermediate-field model

For a tower `K ⊂ M ⊂ L`, `IdeleClassTower` presents the ideles of `L`
as units of `(𝔸_K ⊗[K] M) ⊗[M] L`.  Here we compare that presentation
with the actual relative idele group `𝔸_M ⊗[M] L`, by passing through
the ordinary ideles of `L`.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u

variable
    (K M L : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]

-- These canonical commutativity proofs are local to the imported tower
-- module; retain them here for the quotient-group instances.
local instance
    towerBaseChange_towerRelativeIdeleGroupIsMulCommutative
    (A B C : Type u) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance
    towerBaseChange_relativeIdeleClassGroupIsMulCommutative
    (A B : Type u) [Field A] [NumberField A]
    [Field B] [Algebra A B] :
    IsMulCommutative (RelativeIdeleGroup.ClassGroup A B) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance towerBaseChange_ideleClassGroupIsMulCommutative
    (A : Type u) [Field A] [NumberField A] :
    IsMulCommutative (IdeleClassGroup A) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

section RingComparison

/-- The ring-level relative-to-ordinary comparison, regarded as an
equivalence of `M`-algebras. -/
noncomputable def intermediateRelativeAdeleBaseChangeAlgEquiv :
    RelativeAdeleRing K M ≃ₐ[M]
      NumberField.AdeleRing (𝓞 M) M :=
  AlgEquiv.ofRingEquiv
    (f := relativeAdeleBaseChangeRingEquiv
      (K := K) (L := M))
    (by
      intro m
      change
        relativeAdeleBaseChangeRingEquiv
            (K := K) (L := M)
            ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] m) =
          algebraMap M
            (NumberField.AdeleRing (𝓞 M) M) m
      exact relativeAdeleBaseChangeRingEquiv_fieldInclusion
        (K := K) (L := M) m)

/-- Extend the intermediate adele-ring comparison along `M → L`. -/
noncomputable def towerActualRelativeAdeleRingEquiv :
    TowerRelativeAdeleRing K M L ≃+*
      RelativeAdeleRing M L :=
  (Algebra.TensorProduct.congr
    (intermediateRelativeAdeleBaseChangeAlgEquiv K M)
    (AlgEquiv.refl : L ≃ₐ[M] L)).toRingEquiv

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
@[simp]
theorem towerActualRelativeAdeleRingEquiv_tmul
    (b : RelativeAdeleRing K M)
    (x : L) :
    towerActualRelativeAdeleRingEquiv K M L (b ⊗ₜ[M] x) =
      intermediateRelativeAdeleBaseChangeAlgEquiv K M b ⊗ₜ[M] x :=
  rfl

omit [NumberField L] [FiniteDimensional M L] in
/-- Passing from the fixed-bottom tower presentation to the actual
relative adele ring over the intermediate field intertwines
conjugation by an automorphism of the top field. -/
theorem towerActualRelativeAdeleRingEquiv_unflatten_conjugation
    (σ : L ≃ₐ[M] L)
    (z : RelativeAdeleRing K L) :
    towerActualRelativeAdeleRingEquiv K M L
        (towerRelativeAdeleUnflatten K M L
          (RelativeIdeleGroup.conjugation K L
            (σ.restrictScalars K) z)) =
      RelativeIdeleGroup.conjugation M L σ
        (towerActualRelativeAdeleRingEquiv K M L
          (towerRelativeAdeleUnflatten K M L z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      simp [RelativeIdeleGroup.conjugation_tmul,
        towerRelativeAdeleUnflatten_tmul,
        bottomAdeleToTower_apply, topFieldToTower_apply,
        towerActualRelativeAdeleRingEquiv_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

private theorem relativeAdeleBaseChangeRingEquiv_tower_finiteComponent
    (z : TowerRelativeAdeleRing K M L)
    (W : HeightOneSpectrum (𝓞 L)) :
    (relativeAdeleBaseChangeRingEquiv
        (K := M) (L := L)
        (towerActualRelativeAdeleRingEquiv K M L z)).2 W =
      (relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L)
        (towerRelativeAdeleRingEquiv K M L z)).2 W := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
      simp only [map_add]
      change
        (relativeAdeleBaseChangeRingEquiv
            (towerActualRelativeAdeleRingEquiv K M L z₁)).2 W +
          (relativeAdeleBaseChangeRingEquiv
            (towerActualRelativeAdeleRingEquiv K M L z₂)).2 W =
        (relativeAdeleBaseChangeRingEquiv
            (towerRelativeAdeleRingEquiv K M L z₁)).2 W +
          (relativeAdeleBaseChangeRingEquiv
            (towerRelativeAdeleRingEquiv K M L z₂)).2 W
      exact congrArg₂ (· + ·) hz₁ hz₂
  | tmul b x =>
      induction b using TensorProduct.inductionOn with
      | add b₁ b₂ hb₁ hb₂ =>
          simp only [TensorProduct.add_tmul, map_add]
          change
            (relativeAdeleBaseChangeRingEquiv
                (towerActualRelativeAdeleRingEquiv K M L
                  (b₁ ⊗ₜ[M] x))).2 W +
              (relativeAdeleBaseChangeRingEquiv
                (towerActualRelativeAdeleRingEquiv K M L
                  (b₂ ⊗ₜ[M] x))).2 W =
            (relativeAdeleBaseChangeRingEquiv
                (towerRelativeAdeleRingEquiv K M L
                  (b₁ ⊗ₜ[M] x))).2 W +
              (relativeAdeleBaseChangeRingEquiv
                (towerRelativeAdeleRingEquiv K M L
                  (b₂ ⊗ₜ[M] x))).2 W
          exact congrArg₂ (· + ·) hb₁ hb₂
      | tmul a m =>
          have hflatten :
              towerRelativeAdeleRingEquiv K M L
                  ((a ⊗ₜ[K] m) ⊗ₜ[M] x) =
                a ⊗ₜ[K] (algebraMap M L m * x) := by
            change
              towerRelativeAdeleFlatten K M L
                  ((a ⊗ₜ[K] m) ⊗ₜ[M] x) =
                a ⊗ₜ[K] (algebraMap M L m * x)
            rw [
              towerRelativeAdeleFlatten_tmul,
              intermediateAdeleInclusion_tmul,
              topFieldToOneStep_apply,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]
          let V := finitePlaceBelow (K := M) W
          let v := finitePlaceBelow (K := K) W
          have hv :
              finitePlaceBelow (K := K) V = v :=
            finitePlaceBelow_finitePlaceBelow
              (K := K) (M := M) (L := L) W
          have hcomponent
              (v' : HeightOneSpectrum (𝓞 K))
              (hv' : v' = v)
              (hV : finitePlaceBelow (K := K) V = v')
              (hWV : finitePlaceBelow (K := M) W = V)
              (hWv : finitePlaceBelow (K := K) W = v) :
              finitePlaceAdicCompletionMap M L V ⟨W, hWV⟩
                    (finitePlaceAdicCompletionMap K M v' ⟨V, hV⟩
                        (a.2 v') *
                      algebraMap M (V.adicCompletion M) m) *
                  algebraMap L (W.adicCompletion L) x =
                finitePlaceAdicCompletionMap K L v ⟨W, hWv⟩
                    (a.2 v) *
                  algebraMap L (W.adicCompletion L)
                    (algebraMap M L m * x) := by
            subst v'
            have hm :
                finitePlaceAdicCompletionMap M L V ⟨W, hWV⟩
                    (algebraMap M (V.adicCompletion M) m) =
                  algebraMap L (W.adicCompletion L)
                    (algebraMap M L m) := by
              change
                finitePlaceAdicCompletionMap M L V ⟨W, hWV⟩
                    (m : V.adicCompletion M) =
                  (algebraMap M L m : W.adicCompletion L)
              exact
                finitePlaceAdicCompletionMap_coe M L
                  V ⟨W, hWV⟩ m
            rw [map_mul,
              finitePlaceAdicCompletionMap_comp K L (M := M) v V W
                hV hWV hWv,
              hm,
              map_mul, mul_assoc]
          rw [towerActualRelativeAdeleRingEquiv_tmul, hflatten]
          rw [
            relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul
              (K := M) (L := L)]
          change
            finitePlaceAdicCompletionMap M L V ⟨W, rfl⟩
                ((relativeAdeleBaseChangeRingEquiv
                  (K := K) (L := M) (a ⊗ₜ[K] m)).2 V) *
              algebraMap L (W.adicCompletion L) x =
            (relativeAdeleBaseChangeRingEquiv
              (K := K) (L := L)
              (a ⊗ₜ[K] (algebraMap M L m * x))).2 W
          rw [
            relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul
              (K := K) (L := M),
            relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul
              (K := K) (L := L)]
          exact hcomponent
            (finitePlaceBelow (K := K) V) hv rfl rfl rfl

private theorem relativeAdeleBaseChangeRingEquiv_tower_infiniteComponent
    (z : TowerRelativeAdeleRing K M L)
    (W : InfinitePlace L) :
    (relativeAdeleBaseChangeRingEquiv
        (K := M) (L := L)
        (towerActualRelativeAdeleRingEquiv K M L z)).1 W =
      (relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L)
        (towerRelativeAdeleRingEquiv K M L z)).1 W := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
      simp only [map_add]
      change
        (relativeAdeleBaseChangeRingEquiv
            (towerActualRelativeAdeleRingEquiv K M L z₁)).1 W +
          (relativeAdeleBaseChangeRingEquiv
            (towerActualRelativeAdeleRingEquiv K M L z₂)).1 W =
        (relativeAdeleBaseChangeRingEquiv
            (towerRelativeAdeleRingEquiv K M L z₁)).1 W +
          (relativeAdeleBaseChangeRingEquiv
            (towerRelativeAdeleRingEquiv K M L z₂)).1 W
      exact congrArg₂ (· + ·) hz₁ hz₂
  | tmul b x =>
      induction b using TensorProduct.inductionOn with
      | add b₁ b₂ hb₁ hb₂ =>
          simp only [TensorProduct.add_tmul, map_add]
          change
            (relativeAdeleBaseChangeRingEquiv
                (towerActualRelativeAdeleRingEquiv K M L
                  (b₁ ⊗ₜ[M] x))).1 W +
              (relativeAdeleBaseChangeRingEquiv
                (towerActualRelativeAdeleRingEquiv K M L
                  (b₂ ⊗ₜ[M] x))).1 W =
            (relativeAdeleBaseChangeRingEquiv
                (towerRelativeAdeleRingEquiv K M L
                  (b₁ ⊗ₜ[M] x))).1 W +
              (relativeAdeleBaseChangeRingEquiv
                (towerRelativeAdeleRingEquiv K M L
                  (b₂ ⊗ₜ[M] x))).1 W
          exact congrArg₂ (· + ·) hb₁ hb₂
      | tmul a m =>
          have hflatten :
              towerRelativeAdeleRingEquiv K M L
                  ((a ⊗ₜ[K] m) ⊗ₜ[M] x) =
                a ⊗ₜ[K] (algebraMap M L m * x) := by
            change
              towerRelativeAdeleFlatten K M L
                  ((a ⊗ₜ[K] m) ⊗ₜ[M] x) =
                a ⊗ₜ[K] (algebraMap M L m * x)
            rw [
              towerRelativeAdeleFlatten_tmul,
              intermediateAdeleInclusion_tmul,
              topFieldToOneStep_apply,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]
          let V := infinitePlaceBelow (K := M) W
          let v := infinitePlaceBelow (K := K) W
          have hv :
              infinitePlaceBelow (K := K) V = v :=
            infinitePlaceBelow_infinitePlaceBelow
              (K := K) (M := M) (L := L) W
          have hcomponent
              (v' : InfinitePlace K)
              (hv' : v' = v)
              [hVv : V.1.LiesOver v'.1]
              [hWV : W.1.LiesOver V.1]
              [hWv : W.1.LiesOver v.1] :
              NumberField.LiesOver.completionMap
                    (v := V) (w := W)
                    (NumberField.LiesOver.completionMap
                        (v := v') (w := V) (a.1 v') *
                      algebraMap M V.Completion m) *
                  algebraMap L W.Completion x =
                NumberField.LiesOver.completionMap
                    (v := v) (w := W) (a.1 v) *
                  algebraMap L W.Completion
                    (algebraMap M L m * x) := by
            subst v'
            have hm :
                NumberField.LiesOver.completionMap
                    (v := V) (w := W)
                    (algebraMap M V.Completion m) =
                  algebraMap L W.Completion
                    (algebraMap M L m) := by
              have h :
                  algebraMap M V.Completion m =
                    ((WithAbs.toAbs V.1 m : WithAbs V.1) :
                      V.Completion) :=
                rfl
              rw [h,
                NumberField.LiesOver.completionMap_coe
                  (v := V) (w := W)]
              apply InfinitePlace.Completion.ext
              rw [
                InfinitePlace.Completion.algebraMap_toCompletion,
                UniformSpace.Completion.algebraMap_def]
              simp [WithAbs.algebraMap_left_apply,
                WithAbs.algebraMap_right_apply]
            rw [map_mul,
              infinitePlaceCompletionMap_comp_apply
                (K := K) (M := M) (L := L) W,
              hm,
              map_mul, mul_assoc]
          let : V.1.LiesOver v.1 :=
            ⟨congrArg (fun q : InfinitePlace K => q.1)
              hv⟩
          let : W.1.LiesOver V.1 := ⟨rfl⟩
          let : W.1.LiesOver v.1 := ⟨rfl⟩
          rw [towerActualRelativeAdeleRingEquiv_tmul, hflatten]
          rw [
            relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul
              (K := M) (L := L)]
          change
            NumberField.LiesOver.completionMap
                (v := V) (w := W)
                ((relativeAdeleBaseChangeRingEquiv
                  (K := K) (L := M) (a ⊗ₜ[K] m)).1 V) *
              algebraMap L W.Completion x =
            _
          rw [
            relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul
              (K := K) (L := M),
            relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul
              (K := K) (L := L)]
          exact hcomponent
            (infinitePlaceBelow (K := K) V) hv
            (hVv := ⟨rfl⟩)
            (hWV := ⟨rfl⟩)
            (hWv := ⟨rfl⟩)

/-- Passing from the fixed-bottom tower presentation to ordinary adeles
is independent of whether one first changes to the actual relative
presentation over the intermediate field. -/
theorem relativeAdeleBaseChangeRingEquiv_tower
    (z : TowerRelativeAdeleRing K M L) :
    relativeAdeleBaseChangeRingEquiv
        (K := M) (L := L)
        (towerActualRelativeAdeleRingEquiv K M L z) =
      relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L)
        (towerRelativeAdeleRingEquiv K M L z) := by
  apply Prod.ext
  · funext W
    exact
      relativeAdeleBaseChangeRingEquiv_tower_infiniteComponent
        K M L z W
  · apply DFunLike.coe_injective
    funext W
    exact
      relativeAdeleBaseChangeRingEquiv_tower_finiteComponent
        K M L z W

end RingComparison

section IdeleComparison

section ViaOrdinary

/-- The comparison through ordinary ideles, recording the compatibility
with the original fixed-bottom flattening construction. -/
noncomputable def towerRelativeIdeleViaOrdinaryMulEquiv :
    TowerRelativeIdeleGroup K M L ≃*
      RelativeIdeleGroup M L :=
  (towerRelativeIdeleEquiv K M L).trans
    ((relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)).trans
      (relativeIdeleBaseChangeMulEquiv
        (K := M) (L := L)).symm)

omit [FiniteDimensional K M] in
@[simp]
theorem towerRelativeIdeleViaOrdinaryMulEquiv_apply
    (a : TowerRelativeIdeleGroup K M L) :
    towerRelativeIdeleViaOrdinaryMulEquiv K M L a =
      (relativeIdeleBaseChangeMulEquiv
        (K := M) (L := L)).symm
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L)
          (towerRelativeIdeleEquiv K M L a)) :=
  rfl

end ViaOrdinary

/-- The fixed-bottom tower presentation of the ideles of `L` is
canonically equivalent to the actual relative idele group over `M`,
using the underlying adele-ring scalar-extension equivalence. -/
noncomputable def towerRelativeIdeleBaseChangeMulEquiv :
    TowerRelativeIdeleGroup K M L ≃*
      RelativeIdeleGroup M L :=
  Units.mapEquiv
    (towerActualRelativeAdeleRingEquiv K M L).toMulEquiv

/-- The ring-level tower coherence identifies the direct
tower-to-actual comparison with the comparison through ordinary ideles. -/
theorem towerRelativeIdeleBaseChangeMulEquiv_eq_viaOrdinary
    (a : TowerRelativeIdeleGroup K M L) :
    towerRelativeIdeleBaseChangeMulEquiv K M L a =
      towerRelativeIdeleViaOrdinaryMulEquiv K M L a := by
  apply
    (relativeIdeleBaseChangeMulEquiv
      (K := M) (L := L)).injective
  rw [towerRelativeIdeleViaOrdinaryMulEquiv_apply,
    (relativeIdeleBaseChangeMulEquiv
      (K := M) (L := L)).apply_symm_apply]
  apply (IdeleGroup.equivAdeleRingUnits (K := L)).injective
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits
      (K := M) (L := L),
    relativeIdeleBaseChangeMulEquiv_eq_ringUnits
      (K := K) (L := L)]
  apply Units.ext
  exact
    relativeAdeleBaseChangeRingEquiv_tower
      K M L (a : TowerRelativeAdeleRing K M L)

/-- Scalar extension from the tower presentation to ordinary ideles is
the same along the direct and intermediate-field routes. -/
theorem relativeIdeleBaseChangeMulEquiv_tower
    (a : TowerRelativeIdeleGroup K M L) :
    relativeIdeleBaseChangeMulEquiv
        (K := M) (L := L)
        (towerRelativeIdeleBaseChangeMulEquiv K M L a) =
      relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)
        (towerRelativeIdeleEquiv K M L a) := by
  rw [towerRelativeIdeleBaseChangeMulEquiv_eq_viaOrdinary,
    towerRelativeIdeleViaOrdinaryMulEquiv_apply,
    (relativeIdeleBaseChangeMulEquiv
      (K := M) (L := L)).apply_symm_apply]

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
/-- The comparison preserves the diagonal copy of `Lˣ`. -/
@[simp]
theorem towerRelativeIdeleBaseChangeMulEquiv_principalIdele
    (x : Lˣ) :
    towerRelativeIdeleBaseChangeMulEquiv K M L
        (TowerRelativeIdeleGroup.principalIdele K M L x) =
      RelativeIdeleGroup.principalIdele M L x := by
  apply Units.ext
  change
    towerActualRelativeAdeleRingEquiv K M L
        ((1 : RelativeAdeleRing K M) ⊗ₜ[M] (x : L)) =
      (1 : NumberField.AdeleRing (𝓞 M) M) ⊗ₜ[M] (x : L)
  rw [towerActualRelativeAdeleRingEquiv_tmul]
  simp

omit [NumberField L] [FiniteDimensional M L] in
/-- The tower-to-actual comparison transports the restricted
bottom-field conjugation to conjugation over the intermediate field. -/
theorem towerRelativeIdeleBaseChangeMulEquiv_unflatten_conjugation
    (σ : L ≃ₐ[M] L)
    (a : RelativeIdeleGroup K L) :
    towerRelativeIdeleBaseChangeMulEquiv K M L
        ((towerRelativeIdeleEquiv K M L).symm
          (RelativeIdeleGroup.conjugationIdele K L
            (σ.restrictScalars K) a)) =
      RelativeIdeleGroup.conjugationIdele M L σ
        (towerRelativeIdeleBaseChangeMulEquiv K M L
          ((towerRelativeIdeleEquiv K M L).symm a)) := by
  apply Units.ext
  exact
    towerActualRelativeAdeleRingEquiv_unflatten_conjugation
      K M L σ (a : RelativeAdeleRing K L)

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
/-- Extending an idele from the intermediate relative adele ring into
the tower and then passing to the actual `M`-relative presentation is
the ordinary relative class-field-theoretic inclusion. -/
theorem towerRelativeIdeleBaseChangeMulEquiv_includeLeft
    (a : RelativeIdeleGroup K M) :
    towerRelativeIdeleBaseChangeMulEquiv K M L
        (Units.map
          (Algebra.TensorProduct.includeLeft
            (R := M) (S := M)
            (A := RelativeAdeleRing K M) (B := L)).toRingHom a) =
      RelativeIdeleGroup.inclusion M L
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := M) a) := by
  apply Units.ext
  change
    towerActualRelativeAdeleRingEquiv K M L
        ((a : RelativeAdeleRing K M) ⊗ₜ[M] (1 : L)) =
      ((IdeleGroup.equivAdeleRingUnits (K := M)
          (relativeIdeleBaseChangeMulEquiv
            (K := K) (L := M) a) :
        (NumberField.AdeleRing (𝓞 M) M)ˣ) :
          NumberField.AdeleRing (𝓞 M) M) ⊗ₜ[M] (1 : L)
  rw [towerActualRelativeAdeleRingEquiv_tmul]
  congr 1
  simpa [intermediateRelativeAdeleBaseChangeAlgEquiv] using
    congrArg Units.val
      (relativeIdeleBaseChangeMulEquiv_eq_ringUnits
        (K := K) (L := M) a).symm

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
/-- The comparison maps tower principal ideles exactly onto the actual
relative principal-ideles subgroup over `M`. -/
theorem towerPrincipalSubgroup_map_baseChange :
    (TowerRelativeIdeleGroup.principalSubgroup K M L).map
        (towerRelativeIdeleBaseChangeMulEquiv K M L) =
      RelativeIdeleGroup.principalSubgroup M L := by
  rw [TowerRelativeIdeleGroup.principalSubgroup,
    RelativeIdeleGroup.principalSubgroup,
    MonoidHom.map_range]
  congr 1
  ext x
  exact congrArg Units.val
    (towerRelativeIdeleBaseChangeMulEquiv_principalIdele
      K M L x)

/-- The fixed-bottom tower class group is canonically the actual
relative idele class group of `L/M`. -/
noncomputable def towerRelativeIdeleClassBaseChangeMulEquiv :
    TowerRelativeIdeleGroup.ClassGroup K M L ≃*
      RelativeIdeleGroup.ClassGroup M L :=
  QuotientGroup.congr
    (TowerRelativeIdeleGroup.principalSubgroup K M L)
    (RelativeIdeleGroup.principalSubgroup M L)
    (towerRelativeIdeleBaseChangeMulEquiv K M L)
    (towerPrincipalSubgroup_map_baseChange K M L)

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
@[simp]
theorem towerRelativeIdeleClassBaseChangeMulEquiv_mk
    (a : TowerRelativeIdeleGroup K M L) :
    towerRelativeIdeleClassBaseChangeMulEquiv K M L
        (QuotientGroup.mk'
          (TowerRelativeIdeleGroup.principalSubgroup K M L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup M L)
        (towerRelativeIdeleBaseChangeMulEquiv K M L a) :=
  rfl

/-- Scalar extension from a fixed-bottom tower class group to the
ordinary top-field idele class group is independent of the intermediate
presentation. -/
theorem relativeIdeleClassBaseChangeMulEquiv_tower
    (c : RelativeIdeleGroup.ClassGroup K L) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := M) (L := L)
        (towerRelativeIdeleClassBaseChangeMulEquiv K M L
          ((TowerRelativeIdeleGroup.classGroupEquiv
            K M L).symm c)) =
      relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := L) c := by
  obtain ⟨d, hd⟩ :=
    (TowerRelativeIdeleGroup.classGroupEquiv
      K M L).surjective c
  rw [← hd]
  rw [(TowerRelativeIdeleGroup.classGroupEquiv
    K M L).symm_apply_apply]
  refine QuotientGroup.induction_on d ?_
  intro a
  change
    QuotientGroup.mk' (IdeleGroup.principalSubgroup L)
        (relativeIdeleBaseChangeMulEquiv
          (K := M) (L := L)
          (towerRelativeIdeleBaseChangeMulEquiv K M L a)) =
      QuotientGroup.mk' (IdeleGroup.principalSubgroup L)
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L)
          (towerRelativeIdeleEquiv K M L a))
  exact
    congrArg
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L))
      (relativeIdeleBaseChangeMulEquiv_tower K M L a)

omit [NumberField L] [FiniteDimensional M L] in
/-- The class-group comparison transports the Galois action obtained
by restricting scalars from the bottom field to the natural action
over the intermediate field. -/
theorem towerRelativeIdeleClassBaseChangeMulEquiv_smul
    (σ : L ≃ₐ[M] L)
    (c : RelativeIdeleGroup.ClassGroup K L) :
    towerRelativeIdeleClassBaseChangeMulEquiv K M L
        ((TowerRelativeIdeleGroup.classGroupEquiv K M L).symm
          ((σ.restrictScalars K) • c)) =
      σ •
        towerRelativeIdeleClassBaseChangeMulEquiv K M L
          ((TowerRelativeIdeleGroup.classGroupEquiv K M L).symm c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup M L)
        (towerRelativeIdeleBaseChangeMulEquiv K M L
          ((towerRelativeIdeleEquiv K M L).symm
            (RelativeIdeleGroup.conjugationIdele K L
              (σ.restrictScalars K) a))) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup M L)
        (RelativeIdeleGroup.conjugationIdele M L σ
          (towerRelativeIdeleBaseChangeMulEquiv K M L
            ((towerRelativeIdeleEquiv K M L).symm a)))
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup M L))
    (towerRelativeIdeleBaseChangeMulEquiv_unflatten_conjugation
      K M L σ a)

end IdeleComparison

section NormComparison

/-- The actual finite component of the tower model after the
intermediate adele-ring comparison. -/
noncomputable def towerActualFiniteComponent
    (W : HeightOneSpectrum (𝓞 M)) :
    TowerRelativeIdeleGroup K M L →*
      (W.adicCompletion M ⊗[M] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.map
      ((finiteAdeleComponentAlgHom W).comp
        (intermediateRelativeAdeleBaseChangeAlgEquiv
          K M).toAlgHom)
      (AlgHom.id M L)).toRingHom

/-- The actual archimedean component of the tower model after the
intermediate adele-ring comparison. -/
noncomputable def towerActualInfiniteComponent
    (W : InfinitePlace M) :
    TowerRelativeIdeleGroup K M L →*
      (W.Completion ⊗[M] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.map
      ((infiniteAdeleComponentAlgHom W).comp
        (intermediateRelativeAdeleBaseChangeAlgEquiv
          K M).toAlgHom)
      (AlgHom.id M L)).toRingHom

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
/-- Finite-component identification for the norm-compatible tower
comparison. -/
@[simp]
theorem towerRelativeIdeleBaseChangeMulEquiv_finiteComponent
    (W : HeightOneSpectrum (𝓞 M))
    (a : TowerRelativeIdeleGroup K M L) :
    RelativeIdeleGroup.finiteComponent
        (K := M) (L := L) W
        (towerRelativeIdeleBaseChangeMulEquiv K M L a) =
      towerActualFiniteComponent K M L W a := by
  apply Units.ext
  change
    relativeAdeleFiniteComponent
        (K := M) (L := L) W
        (towerActualRelativeAdeleRingEquiv K M L
          (a : TowerRelativeAdeleRing K M L)) =
      Algebra.TensorProduct.map
        ((finiteAdeleComponentAlgHom W).comp
          (intermediateRelativeAdeleBaseChangeAlgEquiv
            K M).toAlgHom)
        (AlgHom.id M L)
        (a : TowerRelativeAdeleRing K M L)
  induction (a : TowerRelativeAdeleRing K M L) using
      TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul b x =>
      simp [towerActualRelativeAdeleRingEquiv_tmul,
        relativeAdeleFiniteComponent_tmul]

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
/-- Archimedean-component identification for the norm-compatible tower
comparison. -/
@[simp]
theorem towerRelativeIdeleBaseChangeMulEquiv_infiniteComponent
    (W : InfinitePlace M)
    (a : TowerRelativeIdeleGroup K M L) :
    RelativeIdeleGroup.infiniteComponent
        (K := M) (L := L) W
        (towerRelativeIdeleBaseChangeMulEquiv K M L a) =
      towerActualInfiniteComponent K M L W a := by
  apply Units.ext
  change
    relativeAdeleInfiniteComponent
        (K := M) (L := L) W
        (towerActualRelativeAdeleRingEquiv K M L
          (a : TowerRelativeAdeleRing K M L)) =
      Algebra.TensorProduct.map
        ((infiniteAdeleComponentAlgHom W).comp
          (intermediateRelativeAdeleBaseChangeAlgEquiv
            K M).toAlgHom)
        (AlgHom.id M L)
        (a : TowerRelativeAdeleRing K M L)
  induction (a : TowerRelativeAdeleRing K M L) using
      TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul b x =>
      simp [towerActualRelativeAdeleRingEquiv_tmul,
        relativeAdeleInfiniteComponent_tmul]

/-- Evaluation of the fixed-bottom relative adele ring at one exact
finite extension of a place of `K`, as an `M`-algebra map. -/
noncomputable def towerIntermediateFiniteComponentAlgHom
    (w : HeightOneSpectrum (𝓞 K))
    (uM : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) M) :
    RelativeAdeleRing K M →ₐ[M] uM.1.Completion := by
  let f : RelativeAdeleRing K M →+* uM.1.Completion :=
    (finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := M) w uM).comp
        (relativeAdeleFiniteComponent
          (K := K) (L := M) w).toRingHom
  exact
    { f with
      commutes' := by
        intro m
        change
          finitePlaceLocalTensorDecompositionComponent
              (K := K) (L := M) w uM
              (relativeAdeleFiniteComponent
                (K := K) (L := M) w
                ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] m)) =
            algebraMap M uM.1.Completion m
        rw [relativeAdeleFiniteComponent_tmul,
          finitePlaceLocalTensorDecompositionComponent_tmul]
        have hOne :
            ((1 : NumberField.AdeleRing (𝓞 K) K).2 w) = 1 :=
          rfl
        rw [hOne, map_one, map_one, one_mul]
        rfl }

/-- The local tensor component of a tower idele at an exact finite
extension place of `M`. -/
noncomputable def towerIntermediateFiniteComponent
    (w : HeightOneSpectrum (𝓞 K))
    (uM : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) M) :
    TowerRelativeIdeleGroup K M L →*
      (uM.1.Completion ⊗[M] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.map
      (towerIntermediateFiniteComponentAlgHom K M w uM)
      (AlgHom.id M L)).toRingHom

/-- Evaluation of a relative idele over `K` at the same exact finite
extension place of `M`. -/
noncomputable def intermediateFiniteComponent
    (w : HeightOneSpectrum (𝓞 K))
    (uM : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) M) :
    RelativeIdeleGroup K M →* uM.1.Completionˣ :=
  Units.map
    (towerIntermediateFiniteComponentAlgHom K M w uM).toRingHom

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L] in
/-- Determinant norm commutes with the exact finite-place component of
the fixed-bottom tower model. -/
theorem towerIntermediateFiniteComponent_norm
    (w : HeightOneSpectrum (𝓞 K))
    (uM : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) M)
    (a : TowerRelativeIdeleGroup K M L) :
    intermediateFiniteComponent K M w uM
        (TowerRelativeIdeleGroup.norm K M L a) =
      Units.map (Algebra.norm uM.1.Completion)
        (towerIntermediateFiniteComponent K M L w uM a) := by
  apply Units.ext
  exact
    map_norm_tensorProduct_baseChange
      (K := M) (L := L)
      (towerIntermediateFiniteComponentAlgHom K M w uM)
      (a : TowerRelativeAdeleRing K M L)

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
/-- The actual relative-idele norm is the tower determinant norm after
the intermediate relative-to-ordinary adele comparison. -/
theorem towerRelativeIdeleBaseChangeMulEquiv_norm
    (a : TowerRelativeIdeleGroup K M L) :
    relativeIdeleBaseChangeMulEquiv
        (K := K) (L := M)
        (TowerRelativeIdeleGroup.norm K M L a) =
      RelativeIdeleGroup.norm M L
        (towerRelativeIdeleBaseChangeMulEquiv K M L a) := by
  let e₁ :=
    relativeAdeleBaseChangeRingEquiv
      (K := K) (L := M)
  let e₂ :=
    towerActualRelativeAdeleRingEquiv K M L
  have he :
      (algebraMap
          (NumberField.AdeleRing (𝓞 M) M)
          (RelativeAdeleRing M L)).comp e₁.toRingHom =
        e₂.toRingHom.comp
          (algebraMap
            (RelativeAdeleRing K M)
            (TowerRelativeAdeleRing K M L)) := by
    apply DFunLike.ext _ _
    intro b
    change
      (e₁ b) ⊗ₜ[M] (1 : L) =
        e₂ (b ⊗ₜ[M] (1 : L))
    rw [towerActualRelativeAdeleRingEquiv_tmul]
    rfl
  have hnorm :=
    Algebra.norm_eq_of_equiv_equiv
      e₁ e₂ he (a : TowerRelativeAdeleRing K M L)
  have hnorm' :
      e₁
          (Algebra.norm
            (RelativeAdeleRing K M)
            (a : TowerRelativeAdeleRing K M L)) =
        Algebra.norm
          (NumberField.AdeleRing (𝓞 M) M)
          (e₂ (a : TowerRelativeAdeleRing K M L)) := by
    simpa using congrArg e₁ hnorm
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := M)).injective
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits
    (K := K) (L := M)]
  simp only [RelativeIdeleGroup.norm,
    MonoidHom.comp_apply]
  simp only [MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  apply Units.ext
  change
    e₁
        (Algebra.norm
          (RelativeAdeleRing K M)
          (a : TowerRelativeAdeleRing K M L)) =
      Algebra.norm
        (NumberField.AdeleRing (𝓞 M) M)
        (e₂ (a : TowerRelativeAdeleRing K M L))
  exact hnorm'

end NormComparison

section ClassNormComparison

omit [NumberField L] [Algebra K L] [IsScalarTower K M L] in
/-- After both relative presentations are replaced by the ordinary
idele class groups, the fixed-bottom tower class norm is the actual
class norm for `L/M`. -/
theorem towerRelativeIdeleClassBaseChangeMulEquiv_classNorm
    (c : TowerRelativeIdeleGroup.ClassGroup K M L) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := M)
        (TowerRelativeIdeleGroup.classNorm K M L c) =
      RelativeIdeleGroup.classNorm M L
        (towerRelativeIdeleClassBaseChangeMulEquiv K M L c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup M))
    (towerRelativeIdeleBaseChangeMulEquiv_norm K M L a)

omit [NumberField L] [Algebra K L] [IsScalarTower K M L] in
/-- The fixed-bottom tower norm subgroup becomes exactly the actual
`L/M` class-norm subgroup after base change to the ordinary class group
of `M`. -/
theorem towerClassNorm_range_map_baseChange :
    (TowerRelativeIdeleGroup.classNorm K M L).range.map
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M)).toMonoidHom =
      (RelativeIdeleGroup.classNorm M L).range := by
  ext c
  constructor
  · rintro ⟨d, ⟨a, rfl⟩, rfl⟩
    exact
      ⟨towerRelativeIdeleClassBaseChangeMulEquiv K M L a,
        (towerRelativeIdeleClassBaseChangeMulEquiv_classNorm
          K M L a).symm⟩
  · rintro ⟨d, rfl⟩
    have h :
        relativeIdeleClassBaseChangeMulEquiv
            (K := K) (L := M)
            (TowerRelativeIdeleGroup.classNorm K M L
              ((towerRelativeIdeleClassBaseChangeMulEquiv
                K M L).symm d)) =
          RelativeIdeleGroup.classNorm M L d := by
      simpa using
        (towerRelativeIdeleClassBaseChangeMulEquiv_classNorm
          K M L
          ((towerRelativeIdeleClassBaseChangeMulEquiv
            K M L).symm d))
    exact
      ⟨TowerRelativeIdeleGroup.classNorm K M L
          ((towerRelativeIdeleClassBaseChangeMulEquiv
            K M L).symm d),
        ⟨(towerRelativeIdeleClassBaseChangeMulEquiv
            K M L).symm d, rfl⟩, h⟩

/-- The fixed-bottom quotient `C_M / N_{L/M} C_L` is canonically the
ordinary idele-class norm quotient for the actual extension `L/M`. -/
noncomputable def intermediateClassNormQuotientBaseChangeMulEquiv :
    IntermediateClassNormQuotient K M L ≃*
      RelativeIdeleGroup.ClassNormQuotient M L :=
  QuotientGroup.congr
    (TowerRelativeIdeleGroup.classNorm K M L).range
    (RelativeIdeleGroup.classNorm M L).range
    (relativeIdeleClassBaseChangeMulEquiv
      (K := K) (L := M))
    (towerClassNorm_range_map_baseChange K M L)

omit [NumberField L] [Algebra K L] [IsScalarTower K M L] in
@[simp]
theorem intermediateClassNormQuotientBaseChangeMulEquiv_mk
    (c : RelativeIdeleGroup.ClassGroup K M) :
    intermediateClassNormQuotientBaseChangeMulEquiv K M L
        (QuotientGroup.mk'
          (TowerRelativeIdeleGroup.classNorm K M L).range c) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.classNorm M L).range
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M) c) :=
  rfl

end ClassNormComparison

section OrdinaryNormTower

/-- Ordinary idele-class norms are pointwise transitive in an arbitrary
finite tower of number fields.  This is determinant-norm transitivity,
transported through the actual relative-idele presentations over the
bottom and intermediate fields. -/
theorem ordinaryIdeleClassNorm_tower
    (c : IdeleClassGroup L) :
    _root_.ideleClassNorm K M
        (_root_.ideleClassNorm M L c) =
      _root_.ideleClassNorm K L c := by
  let d : RelativeIdeleGroup.ClassGroup K L :=
    (relativeIdeleClassBaseChangeMulEquiv
      (K := K) (L := L)).symm c
  let t : TowerRelativeIdeleGroup.ClassGroup K M L :=
    (TowerRelativeIdeleGroup.classGroupEquiv
      K M L).symm d
  have htop :
      relativeIdeleClassBaseChangeMulEquiv
          (K := M) (L := L)
          (towerRelativeIdeleClassBaseChangeMulEquiv
            K M L t) =
        c := by
    calc
      relativeIdeleClassBaseChangeMulEquiv
          (K := M) (L := L)
          (towerRelativeIdeleClassBaseChangeMulEquiv
            K M L t) =
          relativeIdeleClassBaseChangeMulEquiv
            (K := K) (L := L) d := by
        change
          relativeIdeleClassBaseChangeMulEquiv
              (K := M) (L := L)
              (towerRelativeIdeleClassBaseChangeMulEquiv K M L
                ((TowerRelativeIdeleGroup.classGroupEquiv
                  K M L).symm d)) =
            relativeIdeleClassBaseChangeMulEquiv
              (K := K) (L := L) d
        exact relativeIdeleClassBaseChangeMulEquiv_tower K M L d
      _ = c := by
        exact
          (relativeIdeleClassBaseChangeMulEquiv
            (K := K) (L := L)).apply_symm_apply c
  calc
    _root_.ideleClassNorm K M
        (_root_.ideleClassNorm M L c) =
      _root_.ideleClassNorm K M
        (_root_.ideleClassNorm M L
          (relativeIdeleClassBaseChangeMulEquiv
            (K := M) (L := L)
            (towerRelativeIdeleClassBaseChangeMulEquiv
              K M L t))) := by
                rw [htop]
    _ = _root_.ideleClassNorm K M
        (RelativeIdeleGroup.classNorm M L
          (towerRelativeIdeleClassBaseChangeMulEquiv
            K M L t)) := by
      exact congrArg
        (_root_.ideleClassNorm K M)
        (ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
          (K := M) (L := L)
          (towerRelativeIdeleClassBaseChangeMulEquiv
            K M L t))
    _ = _root_.ideleClassNorm K M
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M)
          (TowerRelativeIdeleGroup.classNorm K M L t)) := by
              rw [
                towerRelativeIdeleClassBaseChangeMulEquiv_classNorm]
    _ = RelativeIdeleGroup.classNorm K M
        (TowerRelativeIdeleGroup.classNorm K M L t) := by
      exact
        ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
          (K := K) (L := M)
          (TowerRelativeIdeleGroup.classNorm K M L t)
    _ = towerCompositeClassNorm K M L t := rfl
    _ = RelativeIdeleGroup.classNorm K L
        (TowerRelativeIdeleGroup.classGroupEquiv K M L t) :=
      towerCompositeClassNorm_eq_ideleClassNorm K M L t
    _ = RelativeIdeleGroup.classNorm K L d := by
      exact congrArg
        (RelativeIdeleGroup.classNorm K L)
        ((TowerRelativeIdeleGroup.classGroupEquiv
          K M L).apply_symm_apply d)
    _ = _root_.ideleClassNorm K L
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L) d) := by
      exact
        (ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
          (K := K) (L := L) d).symm
    _ = _root_.ideleClassNorm K L c := by
      exact congrArg
        (_root_.ideleClassNorm K L)
        ((relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L)).apply_symm_apply c)

/-- In an arbitrary finite tower of number fields, every ordinary
idele-class norm from the top field is already a norm from the
intermediate field.  No normality hypothesis is needed: this is
determinant-norm transitivity transported from the fixed-bottom tower
presentation to the ordinary idele class groups. -/
theorem ordinaryIdeleClassNorm_range_le_of_tower :
    (_root_.ideleClassNorm K L).range ≤
      (_root_.ideleClassNorm K M).range := by
  rw [
    ordinaryIdeleClassNorm_range_eq_relative
      (K := K) (L := L),
    ordinaryIdeleClassNorm_range_eq_relative
      (K := K) (L := M),
    ← towerCompositeClassNorm_range_eq K M L]
  rintro _ ⟨c, rfl⟩
  exact
    ⟨TowerRelativeIdeleGroup.classNorm K M L c, rfl⟩

end OrdinaryNormTower
