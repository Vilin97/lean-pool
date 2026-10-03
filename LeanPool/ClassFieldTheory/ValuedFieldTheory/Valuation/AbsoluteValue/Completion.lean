/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Extension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
/-!
# Completions of absolute-valued fields

This file supplies the canonical absolute value, completion maps, density,
and complete-target universal property for real-valued absolute values.  An
extension is expressed directly by AbsoluteValue.Extends; no extra
container is introduced.  The base-to-completion algebra instance is the
canonical one inherited from WithAbs; algebras between different completions
remain explicit.
-/

@[expose] public section

noncomputable
section

open scoped Topology

namespace AbsoluteValue

universe u v w

/-- The norm absolute value on the completion attached to `vK`. -/
noncomputable def completionAbsoluteValue
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :
    AbsoluteValue vK.Completion ℝ :=
  NormedField.toAbsoluteValue vK.Completion

/-- The extended absolute value on the completion agrees with the original value
on embedded elements. -/
@[simp]
theorem completionAbsoluteValue_coe
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (x : K) :
    completionAbsoluteValue vK (x : vK.Completion) = vK x := by
  change ‖(x : vK.Completion)‖ = vK x
  rw [UniformSpace.Completion.norm_coe]
  rfl

/-- The uniformity defined by the completion absolute value is the native
completion uniformity. -/
theorem completionAbsoluteValue_uniformSpace_eq
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :
    (completionAbsoluteValue vK).uniformSpace =
      (@UniformSpace.Completion.uniformSpace (WithAbs vK) inferInstance) := by
  ext s
  rw [(AbsoluteValue.hasBasis_uniformity
      (completionAbsoluteValue vK)).mem_iff,
    Metric.uniformity_basis_dist.mem_iff]
  have hdist : ∀ p : vK.Completion × vK.Completion,
      dist p.1 p.2 = completionAbsoluteValue vK (p.1 - p.2) := by
    intro p
    rw [dist_eq_norm]
    rfl
  simp [hdist, AbsoluteValue.map_sub]

/-- The field equipped with its completion absolute value is complete. -/
theorem completionAbsoluteValue_complete
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :
    CompleteSpace (WithAbs (completionAbsoluteValue vK)) := by
  let e := WithAbs.equiv (completionAbsoluteValue vK)
  have he : Isometry e :=
    AddMonoidHomClass.isometry_of_norm e.toRingHom fun _ ↦ rfl
  exact (completeSpace_congr (e := e.toEquiv) he.isUniformEmbedding).2 inferInstance

/-- Nontriviality passes to the completion absolute value. -/
theorem completionAbsoluteValue_isNontrivial
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    (completionAbsoluteValue vK).IsNontrivial := by
  rcases hvK with ⟨x, hx0, hx1⟩
  refine ⟨(x : vK.Completion), ?_, ?_⟩
  · intro hx
    have hx' : (WithAbs.equiv vK).symm x = 0 :=
      UniformSpace.Completion.coe_injective (α := WithAbs vK) hx
    exact hx0 (by simpa using congrArg (WithAbs.equiv vK) hx')
  · simpa using hx1

/-- The canonical embedding of an absolute-valued field in its completion. -/
noncomputable def toCompletion
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :
    K →+* vK.Completion :=
  UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv vK).symm.toRingHom

/-- The canonical map into the completion sends an element to its constant Cauchy class. -/
@[simp]
theorem toCompletion_apply
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (x : K) :
    toCompletion vK x = ((WithAbs.equiv vK).symm x : vK.Completion) :=
  rfl

/-- The canonical completion embedding agrees with the completion algebra map. -/
theorem toCompletion_eq_algebraMap
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (x : K) :
    toCompletion vK x = algebraMap K vK.Completion x :=
  rfl

/-- The canonical copy of a field is dense in its completion. -/
theorem denseRange_toCompletion
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :
    DenseRange (toCompletion vK) := by
  change DenseRange
    (UniformSpace.Completion.coe' ∘ WithAbs.toAbs vK)
  exact
    (@UniformSpace.Completion.denseRange_coe (WithAbs vK) inferInstance).comp
      (WithAbs.toAbs_surjective vK).denseRange
      (@UniformSpace.Completion.continuous_coe (WithAbs vK) inferInstance)

/-- Embed the valued base field into the completion of the extension field. -/
noncomputable def baseToExtensionCompletion
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ) :
    WithAbs vK →+* wL.Completion :=
  UniformSpace.Completion.coeRingHom.comp
    (algebraMap (WithAbs vK) (WithAbs wL))

private theorem baseToExtensionCompletion_norm
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : WithAbs vK) :
    ‖baseToExtensionCompletion vK wL x‖ = ‖x‖ := by
  change
    ‖((algebraMap (WithAbs vK) (WithAbs wL)) x : wL.Completion)‖ = ‖x‖
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs,
    WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_algebraMap]
  exact hw x.ofAbs

private theorem baseToExtensionCompletion_isometry
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    Isometry (baseToExtensionCompletion vK wL) :=
  AddMonoidHomClass.isometry_of_norm _
    (baseToExtensionCompletion_norm vK wL hw)

/-- The isometric embedding between completions induced by an exact extension
of absolute values. -/
noncomputable def completionMap
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    vK.Completion →+* wL.Completion :=
  UniformSpace.Completion.extensionHom
    (baseToExtensionCompletion vK wL)
    (by exact (baseToExtensionCompletion_isometry vK wL hw).continuous)

private theorem completionMap_withAbs_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : WithAbs vK) :
    completionMap vK wL hw (x : vK.Completion) =
      baseToExtensionCompletion vK wL x :=
  UniformSpace.Completion.extensionHom_coe
    (baseToExtensionCompletion vK wL)
    (by exact (baseToExtensionCompletion_isometry vK wL hw).continuous) x

/-- On the canonical copy of the base field, the map between completions is
the original algebra map followed by the canonical completion map. -/
@[simp]
theorem completionMap_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : K) :
    completionMap vK wL hw (algebraMap K vK.Completion x) =
      toCompletion wL (algebraMap K L x) := by
  change completionMap vK wL hw
      (((WithAbs.equiv vK).symm x : WithAbs vK) : vK.Completion) =
    (((WithAbs.equiv wL).symm (algebraMap K L x) : WithAbs wL) :
      wL.Completion)
  rw [completionMap_withAbs_coe]
  rfl

/-- The map induced between completions is an isometry. -/
theorem completionMap_isometry
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    Isometry (completionMap vK wL hw) :=
  (baseToExtensionCompletion_isometry vK wL hw).completion_extension

/-- The algebra structure on the extension completion induced by the
completion map.  It is deliberately explicit rather than a global instance. -/
@[reducible] noncomputable def completionAlgebra
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    Algebra vK.Completion wL.Completion :=
  (completionMap vK wL hw).toAlgebra

/-- The algebra structure on the completion uses the canonical completion embedding. -/
@[simp]
theorem completionAlgebra_algebraMap
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : vK.Completion) :
    @algebraMap vK.Completion wL.Completion _ _
        (completionAlgebra vK wL hw) x = completionMap vK wL hw x :=
  rfl

/-- The algebra structure on an extension completion induced by the dense
copy of the extension field.  It is deliberately explicit. -/
@[reducible] noncomputable def extensionCompletionAlgebra
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (wL : AbsoluteValue L ℝ) :
    Algebra K wL.Completion :=
  ((toCompletion wL).comp (algebraMap K L)).toAlgebra

/-- The canonical dense embedding as an algebra homomorphism. -/
noncomputable def toCompletionAlgHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (wL : AbsoluteValue L ℝ) :
    letI := extensionCompletionAlgebra (K := K) wL
    L →ₐ[K] wL.Completion := by
  letI := extensionCompletionAlgebra (K := K) wL
  exact
    { __ := toCompletion wL
      commutes' _ := rfl }

/-- The scalar tower `K → K_v → L_w` supplied by an exact extension. -/
theorem completion_isScalarTower
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    letI hK := extensionCompletionAlgebra (K := K) wL
    letI : SMul K wL.Completion := hK.toSMul
    letI := completionAlgebra vK wL hw
    IsScalarTower K vK.Completion wL.Completion := by
  let hK := extensionCompletionAlgebra (K := K) wL
  let : SMul K wL.Completion := hK.toSMul
  let := completionAlgebra vK wL hw
  exact IsScalarTower.of_algebraMap_eq fun x ↦
    (completionMap_coe vK wL hw x).symm

/-- The completion absolute value on `L_w` extends that on `K_v`. -/
theorem completionAbsoluteValue_extends
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    letI := completionAlgebra vK wL hw
    Extends (completionAbsoluteValue vK) (completionAbsoluteValue wL) := by
  let := completionAlgebra vK wL hw
  intro x
  change ‖algebraMap vK.Completion wL.Completion x‖ = ‖x‖
  exact (completionMap_isometry vK wL hw).norm_map_of_map_zero
    (map_zero _) x

/-- Nonarchimedeanness passes to the completion absolute value. -/
theorem completionAbsoluteValue_isNonarchimedean
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ)) :
    IsNonarchimedean
      (completionAbsoluteValue vK : vK.Completion → ℝ) := by
  rw [isNonarchimedean_iff_bounded_nat]
  refine ⟨1, fun n ↦ ?_⟩
  rw [← map_natCast (algebraMap K vK.Completion) n,
    ← toCompletion_eq_algebraMap vK (n : K)]
  change completionAbsoluteValue vK
    (((WithAbs.equiv vK).symm (n : K) : WithAbs vK) :
      vK.Completion) ≤ 1
  rw [completionAbsoluteValue_coe]
  change vK (n : K) ≤ 1
  simpa using hvK.apply_natCast_le_one (by simp) (by simp)

/-- A nonarchimedean absolute value and its completion absolute value have the
same range. -/
theorem completionAbsoluteValue_range_eq
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ)) :
    Set.range (completionAbsoluteValue vK) = Set.range vK := by
  let vC := completionAbsoluteValue vK
  have hvC : IsNonarchimedean (vC : vK.Completion → ℝ) :=
    completionAbsoluteValue_isNonarchimedean vK hvK
  apply Set.Subset.antisymm
  · rintro r ⟨y, rfl⟩
    by_cases hy : y = 0
    · subst y
      exact ⟨0, by simp⟩
    · have hypos : 0 < vC y := vC.pos hy
      obtain ⟨x, hx⟩ :=
        (denseRange_toCompletion vK).exists_dist_lt y hypos
      have hclose :
          vC (y - algebraMap K vK.Completion x) < vC y := by
        change dist y (toCompletion vK x) < ‖y‖ at hx
        change ‖y - toCompletion vK x‖ < ‖y‖
        simpa only [dist_eq_norm] using hx
      have hne : vC y ≠ vC (-(y - algebraMap K vK.Completion x)) := by
        rw [AbsoluteValue.map_neg]
        exact ne_of_gt hclose
      have hsum := IsNonarchimedean.add_eq_max_of_ne
        (fun a => vC.map_neg a) hvC hne
      refine ⟨x, ?_⟩
      calc
        vK x = vC (algebraMap K vK.Completion x) :=
          (completionAbsoluteValue_coe vK x).symm
        _ = vC (y + -(y - algebraMap K vK.Completion x)) := by
          congr 1
          ring
        _ = max (vC y) (vC (-(y - algebraMap K vK.Completion x))) := hsum
        _ = vC y := by
          rw [AbsoluteValue.map_neg]
          exact max_eq_left hclose.le
  · rintro r ⟨x, rfl⟩
    exact ⟨algebraMap K vK.Completion x,
      completionAbsoluteValue_coe vK x⟩

section CompleteTarget

variable {K : Type u} {D : Type w} [Field K] [Field D]

/-- Transport a ring homomorphism to the absolute-value models of its fields. -/
noncomputable def toCompleteTargetRingHom
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    (i : K →+* D) :
    WithAbs vK →+* WithAbs vD :=
  (WithAbs.equiv vD).symm.toRingHom.comp
    (i.comp (WithAbs.equiv vK).toRingHom)

private theorem toCompleteTargetRingHom_norm
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    (i : K →+* D) (hi : ∀ x : K, vD (i x) = vK x)
    (x : WithAbs vK) :
    ‖toCompleteTargetRingHom vK vD i x‖ = ‖x‖ := by
  change vD (i (WithAbs.equiv vK x)) = vK (WithAbs.equiv vK x)
  exact hi _

private theorem toCompleteTargetRingHom_isometry
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    (i : K →+* D) (hi : ∀ x : K, vD (i x) = vK x) :
    Isometry (toCompleteTargetRingHom vK vD i) :=
  AddMonoidHomClass.isometry_of_norm _
    (toCompleteTargetRingHom_norm vK vD i hi)

/-- A value-preserving embedding into a complete target extends uniquely from
the field to its metric completion. -/
noncomputable def completionMapToCompleteTarget
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    [CompleteSpace (WithAbs vD)]
    (i : K →+* D) (hi : ∀ x : K, vD (i x) = vK x) :
    vK.Completion →+* WithAbs vD :=
  UniformSpace.Completion.extensionHom
    (toCompleteTargetRingHom vK vD i)
    (by exact (toCompleteTargetRingHom_isometry vK vD i hi).continuous)

private theorem completionMapToCompleteTarget_withAbs_coe
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    [CompleteSpace (WithAbs vD)]
    (i : K →+* D) (hi : ∀ x : K, vD (i x) = vK x)
    (x : WithAbs vK) :
    completionMapToCompleteTarget vK vD i hi
        (x : vK.Completion) =
      toCompleteTargetRingHom vK vD i x :=
  UniformSpace.Completion.extensionHom_coe
    (toCompleteTargetRingHom vK vD i)
    (by exact (toCompleteTargetRingHom_isometry vK vD i hi).continuous) x

/-- The extension map to a complete target agrees with the original map on
embedded source elements. -/
@[simp]
theorem completionMapToCompleteTarget_coe
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    [CompleteSpace (WithAbs vD)]
    (i : K →+* D) (hi : ∀ x : K, vD (i x) = vK x)
    (x : K) :
    completionMapToCompleteTarget vK vD i hi
        (algebraMap K vK.Completion x) =
      (WithAbs.equiv vD).symm (i x) := by
  change completionMapToCompleteTarget vK vD i hi
      (((WithAbs.equiv vK).symm x : WithAbs vK) : vK.Completion) = _
  rw [completionMapToCompleteTarget_withAbs_coe]
  rfl

/-- An isometric source map extends to an isometry from the completion. -/
theorem completionMapToCompleteTarget_isometry
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    [CompleteSpace (WithAbs vD)]
    (i : K →+* D) (hi : ∀ x : K, vD (i x) = vK x) :
    Isometry (completionMapToCompleteTarget vK vD i hi) :=
  (toCompleteTargetRingHom_isometry vK vD i hi).completion_extension

/-- A continuous map from the completion is determined by its restriction to
the canonical dense copy of the source field. -/
theorem completionMapToCompleteTarget_eq_of_coe_eq
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    [CompleteSpace (WithAbs vD)]
    (i : K →+* D) (hi : ∀ x : K, vD (i x) = vK x)
    (g : vK.Completion →+* WithAbs vD) (hg : Continuous g)
    (hcoe : ∀ x : K,
      completionMapToCompleteTarget vK vD i hi
          (algebraMap K vK.Completion x) =
        g (algebraMap K vK.Completion x)) :
    completionMapToCompleteTarget vK vD i hi = g := by
  ext x
  refine UniformSpace.Completion.induction_on (α := WithAbs vK) x ?_ ?_
  · exact isClosed_eq
      (completionMapToCompleteTarget_isometry vK vD i hi).continuous hg
  · intro a
    have ha : (a : vK.Completion) =
        algebraMap K vK.Completion (WithAbs.equiv vK a) := by
      change (a : vK.Completion) =
        (((WithAbs.equiv vK).symm (WithAbs.equiv vK a) : WithAbs vK) :
          vK.Completion)
      exact congrArg (fun z : WithAbs vK ↦ (z : vK.Completion))
        ((WithAbs.equiv vK).symm_apply_apply a).symm
    rw [ha]
    exact hcoe (WithAbs.equiv vK a)

end CompleteTarget

section CompleteTargetTower

variable {K : Type u} {L : Type v} {D : Type w}
variable [Field K] [Field L] [Field D] [Algebra K L]

/-- Dense-point compatibility for extending `L → D` and first embedding the
completed base in the completion of `L`. -/
theorem completionMapToCompleteTarget_comp_completionMap_coe
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (vD : AbsoluteValue D ℝ)
    [CompleteSpace (WithAbs vD)]
    (i : L →+* D) (hi : ∀ x : L, vD (i x) = wL x)
    (x : K) :
    completionMapToCompleteTarget wL vD i hi
        (completionMap vK wL hw (algebraMap K vK.Completion x)) =
      (WithAbs.equiv vD).symm (i (algebraMap K L x)) := by
  rw [completionMap_coe, toCompletion_eq_algebraMap,
    completionMapToCompleteTarget_coe]

/-- Two continuous maps out of the completed base agree if they agree on the
original base field after passage through the extension completion. -/
theorem completionMapToCompleteTarget_comp_completionMap_eq_of_coe_eq
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (vD : AbsoluteValue D ℝ)
    [CompleteSpace (WithAbs vD)]
    (i : L →+* D) (hi : ∀ x : L, vD (i x) = wL x)
    (g : vK.Completion →+* WithAbs vD) (hg : Continuous g)
    (hcoe : ∀ x : K,
      (WithAbs.equiv vD).symm (i (algebraMap K L x)) =
        g (algebraMap K vK.Completion x)) :
    (completionMapToCompleteTarget wL vD i hi).comp
        (completionMap vK wL hw) = g := by
  ext x
  refine UniformSpace.Completion.induction_on (α := WithAbs vK) x ?_ ?_
  · exact isClosed_eq
      ((completionMapToCompleteTarget_isometry wL vD i hi).continuous.comp
        (completionMap_isometry vK wL hw).continuous) hg
  · intro a
    have ha : (a : vK.Completion) =
        algebraMap K vK.Completion (WithAbs.equiv vK a) := by
      change (a : vK.Completion) =
        (((WithAbs.equiv vK).symm (WithAbs.equiv vK a) : WithAbs vK) :
          vK.Completion)
      exact congrArg (fun z : WithAbs vK ↦ (z : vK.Completion))
        ((WithAbs.equiv vK).symm_apply_apply a).symm
    rw [ha]
    exact
      (completionMapToCompleteTarget_comp_completionMap_coe
        vK wL hw vD i hi (WithAbs.equiv vK a)).trans
        (hcoe (WithAbs.equiv vK a))

end CompleteTargetTower

end AbsoluteValue

end
