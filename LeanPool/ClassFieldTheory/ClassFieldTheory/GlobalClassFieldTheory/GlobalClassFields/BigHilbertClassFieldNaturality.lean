/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassField
/-!
# Naturality of the big Hilbert class field

An equivalence of number fields preserves both finite integrality and
positivity at the real infinite places.  Consequently the actual
idele-class transport carries the big-Hilbert norm subgroup exactly onto
the corresponding subgroup of the target field.  This gives canonical
transport on the big-Hilbert reciprocity quotient and on the narrow class
group, with formulas on genuine idele representatives.
-/

@[expose] public section

open scoped NumberField NumberField.LiesOver TensorProduct

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M]

open scoped Classical in
private theorem bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk
    (a : IdeleGroup K) :
    bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K))
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      QuotientGroup.mk'
        (RayClass.narrowDenominator (K := K)) a :=
  rfl

open scoped Classical in
private noncomputable def infinitePlaceCompletionCongrHom
    (e : K ≃ₐ[ℚ] M)
    (W : InfinitePlace M) :
    (W.comap e.toRingHom).Completion →+*
      W.Completion := by
  letI : Algebra K M :=
    e.toRingHom.toAlgebra
  let v :=
    W.comap e.toRingHom
  letI : W.1.LiesOver v.1 :=
    ⟨rfl⟩
  exact
    NumberField.LiesOver.completionMap
      (v := v) (w := W)

open scoped Classical in
private theorem infinitePlaceCompletionCongrHom_algebraMap
    (e : K ≃ₐ[ℚ] M)
    (W : InfinitePlace M)
    (x : K) :
    infinitePlaceCompletionCongrHom e W
        (algebraMap K (W.comap e.toRingHom).Completion x) =
      algebraMap M W.Completion (e x) := by
  let : Algebra K M :=
    e.toRingHom.toAlgebra
  let v : InfinitePlace K :=
    W.comap e.toRingHom
  let : W.1.LiesOver v.1 :=
    ⟨rfl⟩
  change
    NumberField.LiesOver.completionMap
        (v := v) (w := W)
        (algebraMap K v.Completion x) =
      algebraMap M W.Completion
        (algebraMap K M x)
  have hx :
      algebraMap K v.Completion x =
        ((WithAbs.toAbs v.1 x : WithAbs v.1) :
          v.Completion) :=
    rfl
  rw [hx,
    NumberField.LiesOver.completionMap_coe
      (v := v) (w := W)]
  apply InfinitePlace.Completion.ext
  rw [
    InfinitePlace.Completion.algebraMap_toCompletion,
    UniformSpace.Completion.algebraMap_def]
  simp only [WithAbs.algebraMap_left_apply,
    WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply]

open scoped Classical in
private theorem
    relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr_infiniteComponent_tmul
    (e : K ≃ₐ[ℚ] M)
    (b : NumberField.AdeleRing (𝓞 ℚ) ℚ)
    (x : K)
    (W : InfinitePlace M) :
    (relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M) (b ⊗ₜ[ℚ] e x)).1 W =
      infinitePlaceCompletionCongrHom e W
        ((relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) (b ⊗ₜ[ℚ] x)).1
            (W.comap e.toRingHom)) := by
  let : Algebra K M :=
    e.toRingHom.toAlgebra
  let v : InfinitePlace K :=
    W.comap e.toRingHom
  let : W.1.LiesOver v.1 :=
    ⟨rfl⟩
  change
    (relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M) (b ⊗ₜ[ℚ] e x)).1 W =
      NumberField.LiesOver.completionMap
        (v := v) (w := W)
        ((relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) (b ⊗ₜ[ℚ] x)).1 v)
  let qv :=
    infinitePlaceBelow (K := ℚ) v
  let qW :=
    infinitePlaceBelow (K := ℚ) W
  have hW :
      infinitePlaceBelow (K := K) W = v :=
    rfl
  have hq : qv = qW := by
    dsimp only [qv, qW]
    rw [← hW]
    exact
      infinitePlaceBelow_infinitePlaceBelow
        (K := ℚ) (M := K) (L := M) W
  let : v.1.LiesOver qv.1 :=
    ⟨rfl⟩
  let : W.1.LiesOver qW.1 :=
    ⟨rfl⟩
  let : W.1.LiesOver qv.1 :=
    ⟨congrArg (fun q : InfinitePlace ℚ => q.1) hq.symm⟩
  have hxMap :
      NumberField.LiesOver.completionMap
          (v := v) (w := W)
          (algebraMap K v.Completion x) =
        algebraMap M W.Completion (e x) := by
    simpa only [infinitePlaceCompletionCongrHom] using
      infinitePlaceCompletionCongrHom_algebraMap e W x
  have hcomponent
      (qv' : InfinitePlace ℚ)
      (h : qv' = qW)
      [v.1.LiesOver qv'.1] :
      NumberField.LiesOver.completionMap
            (v := qW) (w := W) (b.1 qW) *
          algebraMap M W.Completion (e x) =
        NumberField.LiesOver.completionMap
            (v := v) (w := W)
            (NumberField.LiesOver.completionMap
                (v := qv') (w := v) (b.1 qv') *
              algebraMap K v.Completion x) := by
    subst qv'
    have hcomp :
        NumberField.LiesOver.completionMap
            (v := v) (w := W)
            (NumberField.LiesOver.completionMap
              (v := qW) (w := v) (b.1 qW)) =
          NumberField.LiesOver.completionMap
            (v := qW) (w := W) (b.1 qW) := by
      convert
        (infinitePlaceCompletionMap_comp_apply
          (K := ℚ) (M := K) (L := M) W (b.1 qW)) using 1
      rfl
    rw [map_mul, hcomp, hxMap]
  rw [relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul,
    relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul]
  exact hcomponent qv hq

open scoped Classical in
private theorem adeleCongr_infiniteComponent
    (e : K ≃ₐ[ℚ] M)
    (a : NumberField.AdeleRing (𝓞 K) K)
    (W : InfinitePlace M) :
    (adeleCongr e a).1 W =
      infinitePlaceCompletionCongrHom e W
        (a.1 (W.comap e.toRingHom)) := by
  let v : InfinitePlace K :=
    W.comap e.toRingHom
  let componentK :=
    (infiniteAdeleComponentAlgHom v).toAddMonoidHom
  let componentM :=
    (infiniteAdeleComponentAlgHom W).toAddMonoidHom
  change
    componentM (adeleCongr e a) =
      infinitePlaceCompletionCongrHom e W (componentK a)
  let z :=
    (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).symm a
  have ha :
      relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) z = a :=
    (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).apply_symm_apply a
  have htransport :
      componentM
          (relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := M)
            (relativeAdeleCongr (K := ℚ) e z)) =
        componentM
          (adeleCongr e
            (relativeAdeleBaseChangeRingEquiv
              (K := ℚ) (L := K) z)) :=
    congrArg componentM
      (relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr e z)
  rw [← ha, ← htransport]
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [map_add, Prod.fst_add, Pi.add_apply] using
        congrArg₂ (· + ·) hx hy
  | tmul b x =>
      exact
        relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr_infiniteComponent_tmul
          e b x W

open scoped Classical in
private theorem ideleCongr_infiniteComponent
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K)
    (W : InfinitePlace M) :
    IdeleGroup.infiniteComponent W (ideleCongr e a) =
      Units.map
        (infinitePlaceCompletionCongrHom e W).toMonoidHom
        (IdeleGroup.infiniteComponent
          (W.comap e.toRingHom) a) := by
  apply Units.ext
  exact
    adeleCongr_infiniteComponent e
      (((IdeleGroup.equivAdeleRingUnits
        (K := K) a :
          (NumberField.AdeleRing (𝓞 K) K)ˣ) :
        NumberField.AdeleRing (𝓞 K) K)) W

open scoped Classical in
private theorem
    infinitePlaceCompletionCongrHom_extensionEmbeddingOfIsReal
    (e : K ≃ₐ[ℚ] M)
    (W : InfinitePlace M)
    (hW : W.IsReal)
    (x : (W.comap e.toRingHom).Completion) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hW
        (infinitePlaceCompletionCongrHom e W x) =
      InfinitePlace.Completion.extensionEmbeddingOfIsReal
        (hW.comap e.toRingHom) x := by
  let : Algebra K M :=
    e.toRingHom.toAlgebra
  let v :=
    W.comap e.toRingHom
  let : W.1.LiesOver v.1 :=
    ⟨rfl⟩
  let :
      NumberField.ComplexEmbedding.LiesOver
        (InfinitePlace.Completion.extensionEmbedding W)
        (InfinitePlace.Completion.extensionEmbedding v) :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
      W (hW.comap e.toRingHom)
  have hComplex :
      InfinitePlace.Completion.extensionEmbedding W
          (NumberField.LiesOver.completionMap
            (v := v) (w := W) x) =
        InfinitePlace.Completion.extensionEmbedding v x := by
    exact
      InfinitePlace.Completion.liesOver_extensionEmbedding_apply
        (v := v) (w := W)
  apply Complex.ofReal_injective
  simpa only [
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply,
    infinitePlaceCompletionCongrHom] using hComplex

open scoped Classical in
private theorem
    infinitePlaceCompletionCongrHom_mem_infinitePositiveSubgroup_iff
    (e : K ≃ₐ[ℚ] M)
    (W : InfinitePlace M)
    (x : (W.comap e.toRingHom).Completionˣ) :
    Units.map
          (infinitePlaceCompletionCongrHom e W).toMonoidHom x ∈
        RayClass.infinitePositiveSubgroup W ↔
      x ∈
        RayClass.infinitePositiveSubgroup
          (W.comap e.toRingHom) := by
  rw [RayClass.mem_infinitePositiveSubgroup_iff,
    RayClass.mem_infinitePositiveSubgroup_iff]
  constructor
  · intro h hv
    have hW :
        W.IsReal :=
      (InfinitePlace.isReal_comap_iff
        e.toRingEquiv).1 hv
    have hpos :=
      h hW
    change
      0 <
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hW
          (infinitePlaceCompletionCongrHom e W
            (x : (W.comap e.toRingHom).Completion)) at hpos
    rw [
      infinitePlaceCompletionCongrHom_extensionEmbeddingOfIsReal
        e W hW] at hpos
    simpa only using hpos
  · intro h hW
    have hv :
        (W.comap e.toRingHom).IsReal :=
      hW.comap e.toRingHom
    have hpos :=
      h hv
    change
      0 <
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hW
          (infinitePlaceCompletionCongrHom e W
            (x : (W.comap e.toRingHom).Completion))
    rw [
      infinitePlaceCompletionCongrHom_extensionEmbeddingOfIsReal
        e W hW]
    simpa only using hpos

open scoped Classical in
private theorem ideleCongr_mem_infiniteCongruenceSubgroup_iff
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K) :
    (ideleCongr e a).1 ∈
        RayClass.narrowInfiniteCongruenceSubgroup (K := M) ↔
      a.1 ∈
        RayClass.narrowInfiniteCongruenceSubgroup (K := K) := by
  rw [RayClass.mem_narrowInfiniteCongruenceSubgroup_iff,
    RayClass.mem_narrowInfiniteCongruenceSubgroup_iff]
  constructor
  · intro h v
    let W : InfinitePlace M :=
      v.comap e.symm.toRingHom
    have hcomap :
        W.comap e.toRingHom = v := by
      change
        (v.comap e.symm.toRingHom).comap e.toRingHom = v
      rw [← InfinitePlace.comap_comp]
      convert InfinitePlace.comap_id v using 1
      ext x
      change v.1 (e.symm (e x)) = v.1 x
      exact congrArg v.1 (e.symm_apply_apply x)
    have hW :
        IdeleGroup.infiniteComponent W (ideleCongr e a) ∈
          RayClass.infinitePositiveSubgroup W := by
      simpa only [IdeleGroup.infiniteComponent_apply] using h W
    rw [ideleCongr_infiniteComponent] at hW
    have hv :=
      (infinitePlaceCompletionCongrHom_mem_infinitePositiveSubgroup_iff
        e W
        (IdeleGroup.infiniteComponent
          (W.comap e.toRingHom) a)).1 hW
    rw [hcomap] at hv
    simpa only [IdeleGroup.infiniteComponent_apply] using hv
  · intro h W
    have hW :
        IdeleGroup.infiniteComponent W (ideleCongr e a) ∈
          RayClass.infinitePositiveSubgroup W := by
      rw [ideleCongr_infiniteComponent]
      apply
        (infinitePlaceCompletionCongrHom_mem_infinitePositiveSubgroup_iff
          e W
          (IdeleGroup.infiniteComponent
            (W.comap e.toRingHom) a)).2
      simpa only [IdeleGroup.infiniteComponent_apply] using
        h (W.comap e.toRingHom)
    simpa only [IdeleGroup.infiniteComponent_apply] using hW

open scoped Classical in
private theorem ideleCongr_mem_ideleCongruenceSubgroup_zero_iff
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K) :
    ideleCongr e a ∈
        (RayClass.Modulus.narrowOfFinite
          (0 : RayClass.FiniteModulus M)).ideleCongruenceSubgroup ↔
      a ∈
        (RayClass.Modulus.narrowOfFinite
          (0 : RayClass.FiniteModulus K)).ideleCongruenceSubgroup := by
  have hfinite :=
    ideleCongr_mem_integralAtFinitePlaces_iff e a
  change
    (ideleCongr e a).2 ∈
          FiniteIdeleGroup.integralSubgroup (K := M) ↔
      a.2 ∈
        FiniteIdeleGroup.integralSubgroup (K := K) at hfinite
  have hfiniteZero :
      (ideleCongr e a).2 ∈
            RayClass.finiteCongruenceSubgroup
              (0 : RayClass.FiniteModulus M) ↔
        a.2 ∈
          RayClass.finiteCongruenceSubgroup
            (0 : RayClass.FiniteModulus K) := by
    simpa only [RayClass.finiteCongruenceSubgroup_zero] using
      hfinite
  rw [RayClass.Modulus.ideleCongruenceSubgroup_narrowOfFinite,
    RayClass.Modulus.ideleCongruenceSubgroup_narrowOfFinite]
  exact
    and_congr
      (ideleCongr_mem_infiniteCongruenceSubgroup_iff e a)
      hfiniteZero

open scoped Classical in
private theorem ideleCongruenceSubgroup_zero_map_ideleCongr
    (e : K ≃ₐ[ℚ] M) :
    ((RayClass.Modulus.narrowOfFinite
        (0 : RayClass.FiniteModulus K)).ideleCongruenceSubgroup).map
          (ideleCongr e).toMonoidHom =
      (RayClass.Modulus.narrowOfFinite
        (0 : RayClass.FiniteModulus M)).ideleCongruenceSubgroup := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact
      (ideleCongr_mem_ideleCongruenceSubgroup_zero_iff
        e a).2 ha
  · intro hb
    let a : IdeleGroup K :=
      (ideleCongr e).symm b
    refine ⟨a, ?_, ?_⟩
    · apply
        (ideleCongr_mem_ideleCongruenceSubgroup_zero_iff
          e a).1
      simpa only [a, (ideleCongr e).apply_symm_apply] using hb
    · exact
        (ideleCongr e).apply_symm_apply b

open scoped Classical in
private theorem narrowDenominator_map_ideleCongr
    (e : K ≃ₐ[ℚ] M) :
    (RayClass.narrowDenominator (K := K)).map
        (ideleCongr e).toMonoidHom =
      RayClass.narrowDenominator (K := M) := by
  rw [RayClass.narrowDenominator,
    RayClass.narrowDenominator,
    Subgroup.map_sup,
    ideleCongruenceSubgroup_zero_map_ideleCongr]
  apply congrArg
    (fun H =>
      (RayClass.Modulus.narrowOfFinite
        (0 : RayClass.FiniteModulus M)).ideleCongruenceSubgroup ⊔ H)
  change
    (IdeleGroup.principalSubgroup K).map
        (ideleCongr e) =
      IdeleGroup.principalSubgroup M
  exact idelePrincipalSubgroup_map_congr e

open scoped Classical in
/-- Transport of actual idele classes along a number-field equivalence
carries the big-Hilbert norm subgroup exactly onto the big-Hilbert norm
subgroup of the target field. -/
theorem bigHilbertClassFieldNormSubgroup_map_ideleClassCongr
    (e : K ≃ₐ[ℚ] M) :
    (bigHilbertClassFieldNormSubgroup (K := K)).map
        (ideleClassCongr e).toMonoidHom =
      bigHilbertClassFieldNormSubgroup (K := M) := by
  have hcomp :
      (ideleClassCongr e).toMonoidHom.comp
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)) =
        (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup M)).comp
          (ideleCongr e).toMonoidHom := by
    ext a
    exact ideleClassCongr_mk e a
  rw [bigHilbertClassFieldNormSubgroup,
    bigHilbertClassFieldNormSubgroup,
    RayClass.Modulus.congruenceSubgroup,
    RayClass.Modulus.congruenceSubgroup,
    Subgroup.map_map, hcomp,
    ← Subgroup.map_map]
  rw [show
      ((RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus K)).ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K).map
            (ideleCongr e).toMonoidHom =
        (RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus M)).ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup M by
    simpa only [RayClass.narrowDenominator] using
      narrowDenominator_map_ideleCongr e]

open scoped Classical in
/-- The canonical equivalence of big-Hilbert reciprocity quotients
induced by an equivalence of number fields. -/
noncomputable def bigHilbertClassFieldQuotientCongr
    (e : K ≃ₐ[ℚ] M) :
    (IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K)) ≃*
      (IdeleClassGroup M ⧸
        bigHilbertClassFieldNormSubgroup (K := M)) :=
  QuotientGroup.congr
    (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup (K := M))
    (ideleClassCongr e)
    (bigHilbertClassFieldNormSubgroup_map_ideleClassCongr e)

open scoped Classical in
/-- The big-Hilbert quotient equivalence is induced on representatives
by the actual transport of idele classes. -/
theorem bigHilbertClassFieldQuotientCongr_mk
    (e : K ≃ₐ[ℚ] M)
    (c : IdeleClassGroup K) :
    bigHilbertClassFieldQuotientCongr e
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K)) c) =
      QuotientGroup.mk'
        (bigHilbertClassFieldNormSubgroup (K := M))
        (ideleClassCongr e c) :=
  rfl

open scoped Classical in
/-- Canonical transport of narrow ideal classes determined by the
big-Hilbert reciprocity quotient. -/
noncomputable def bigHilbertNarrowClassGroupCongr
    (e : K ≃ₐ[ℚ] M) :
    RayClass.NarrowClassGroup K ≃*
      RayClass.NarrowClassGroup M :=
  (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).symm |>.trans
    ((bigHilbertClassFieldQuotientCongr e).trans
      (bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := M)))

open scoped Classical in
/-- Naturality of the canonical identification of the big-Hilbert
reciprocity quotient with the narrow class group. -/
@[simp]
theorem bigHilbertClassFieldQuotientEquivNarrowClassGroup_naturality
    (e : K ≃ₐ[ℚ] M)
    (q : IdeleClassGroup K ⧸
      bigHilbertClassFieldNormSubgroup (K := K)) :
    bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := M)
        (bigHilbertClassFieldQuotientCongr e q) =
      bigHilbertNarrowClassGroupCongr e
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K) q) := by
  simp only [bigHilbertNarrowClassGroupCongr,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

open scoped Classical in
/-- Homomorphism form of naturality for the big-Hilbert
quotient--narrow-class-group identification. -/
theorem
    bigHilbertClassFieldQuotientEquivNarrowClassGroup_naturality_hom
    (e : K ≃ₐ[ℚ] M) :
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := M)).toMonoidHom.comp
        (bigHilbertClassFieldQuotientCongr
          (K := K) (M := M) e).toMonoidHom =
      (bigHilbertNarrowClassGroupCongr
        (K := K) (M := M) e).toMonoidHom.comp
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K)).toMonoidHom := by
  ext q
  exact
    bigHilbertClassFieldQuotientEquivNarrowClassGroup_naturality
      (K := K) (M := M) e q

open scoped Classical in
/-- On an idele representative, canonical transport of narrow ideal
classes is represented by the transported idele itself. -/
theorem bigHilbertNarrowClassGroupCongr_mk
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K) :
    bigHilbertNarrowClassGroupCongr e
        (QuotientGroup.mk'
          (RayClass.narrowDenominator (K := K)) a) =
      QuotientGroup.mk'
        (RayClass.narrowDenominator (K := M))
        (ideleCongr e a) := by
  let q :
      IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K) :=
    QuotientGroup.mk'
      (bigHilbertClassFieldNormSubgroup (K := K))
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a)
  calc
    bigHilbertNarrowClassGroupCongr e
          (QuotientGroup.mk'
            (RayClass.narrowDenominator (K := K)) a) =
        bigHilbertNarrowClassGroupCongr e
          (bigHilbertClassFieldQuotientEquivNarrowClassGroup
            (K := K) q) := by
              simp only [q,
                bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk]
    _ =
        bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := M)
          (bigHilbertClassFieldQuotientCongr e q) :=
      (bigHilbertClassFieldQuotientEquivNarrowClassGroup_naturality
        e q).symm
    _ =
        QuotientGroup.mk'
          (RayClass.narrowDenominator (K := M))
          (ideleCongr e a) := by
      simp only [q, bigHilbertClassFieldQuotientCongr_mk,
        ideleClassCongr_mk,
        bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk]

open scoped Classical in
/-- Homomorphism form of naturality for narrow ideal classes under the
big-Hilbert narrow-class-group transport. -/
theorem bigHilbertNarrowClassGroupCongr_naturality
    (e : K ≃ₐ[ℚ] M) :
    (bigHilbertNarrowClassGroupCongr e).toMonoidHom.comp
        (QuotientGroup.mk'
          (RayClass.narrowDenominator (K := K))) =
      (QuotientGroup.mk'
        (RayClass.narrowDenominator (K := M))).comp
          (ideleCongr e).toMonoidHom := by
  ext a
  exact bigHilbertNarrowClassGroupCongr_mk e a

end GlobalClassFields
end GlobalClassFieldTheory
