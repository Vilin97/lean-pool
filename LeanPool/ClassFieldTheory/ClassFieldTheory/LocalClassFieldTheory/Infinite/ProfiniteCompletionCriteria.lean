/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion
/-!
# Bijectivity criteria for maps out of the open-quotient completion

The universal lift to a profinite target is onto when the original map has
dense range.  It is one-to-one when pullbacks of open normal subgroups of the
target are cofinal among the defining open finite-index normal subgroups of
the source.  These criteria isolate the purely topological part of infinite
local reciprocity from the arithmetic existence theorem.
-/

noncomputable section

open CategoryTheory

namespace LocalClassFieldTheory

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Quotienting by the exact pullback of an open normal subgroup gives an
injective map to the corresponding finite quotient of the target. -/
theorem topologicalProfiniteCompletionFiniteQuotientMap_injective
    (P : ProfiniteGrp.{u}) (f : G →ₜ* P) (N : OpenNormalSubgroup P) :
    Function.Injective
      (topologicalProfiniteCompletionFiniteQuotientMap P f N) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      (topologicalProfiniteCompletionPreimageIndex P f N).toOpenNormalSubgroup.toSubgroup x
    change QuotientGroup.mk' (N : Subgroup P) (f g) = 1 at hx
    apply (QuotientGroup.eq_one_iff g).2
    exact (QuotientGroup.eq_one_iff (f g)).1 hx
  · exact bot_le

variable [IsTopologicalGroup G]

/-- Dense range of the original map implies surjectivity of its canonical
extension from the open-quotient completion. -/
theorem topologicalProfiniteCompletionLift_surjective_of_denseRange
    (P : ProfiniteGrp.{u}) (f : G →ₜ* P) (hf : DenseRange f) :
    Function.Surjective (topologicalProfiniteCompletionLift P f) := by
  let F := topologicalProfiniteCompletionLift P f
  have hF_dense : DenseRange F := by
    intro y
    apply closure_mono (s := Set.range f) (t := Set.range F) ?_ (hf y)
    rintro z ⟨g, rfl⟩
    exact ⟨topologicalProfiniteCompletionMap G g,
      topologicalProfiniteCompletionLift_map P f g⟩
  have hclosed : IsClosed (Set.range F) :=
    F.continuous_toFun.isClosedMap.isClosed_range
  rw [← Set.range_eq_univ, ← closure_eq_iff_isClosed.mpr hclosed]
  exact hF_dense.closure_eq

/-- Cofinality of pulled-back target quotients implies injectivity of the
canonical lift from the open-quotient completion. -/
theorem topologicalProfiniteCompletionLift_injective_of_preimage_cofinal
    (P : ProfiniteGrp.{u}) (f : G →ₜ* P)
    (hcofinal : ∀ H : OpenFiniteIndexNormalSubgroup G,
      ∃ N : OpenNormalSubgroup P,
        topologicalProfiniteCompletionPreimageIndex P f N ≤ H) :
    Function.Injective (topologicalProfiniteCompletionLift P f) := by
  change Function.Injective
    (topologicalProfiniteCompletionLift P f).toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro x hx
    change x = 1
    apply Subtype.ext
    funext H
    obtain ⟨N, hNH⟩ := hcofinal H
    let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
    have hlimit :
        topologicalProfiniteCompletionToFiniteQuotientLimit P f x = 1 := by
      have he := congrArg e hx
      simpa [topologicalProfiniteCompletionLift, e] using he
    have hfinite :
        topologicalProfiniteCompletionFiniteProjection P f N x = 1 := by
      exact congrFun (congrArg Subtype.val hlimit) N
    have hpreimage :
        topologicalProfiniteCompletionProjection G
          (topologicalProfiniteCompletionPreimageIndex P f N) x = 1 := by
      have hinjective : Function.Injective
          (topologicalProfiniteCompletionFiniteQuotientMorphism P f N) := by
        change Function.Injective
          (topologicalProfiniteCompletionFiniteQuotientMap P f N)
        exact topologicalProfiniteCompletionFiniteQuotientMap_injective P f N
      change
        topologicalProfiniteCompletionFiniteQuotientMorphism P f N
            (topologicalProfiniteCompletionProjection G
              (topologicalProfiniteCompletionPreimageIndex P f N) x) = 1
        at hfinite
      apply hinjective
      simpa only [map_one] using hfinite
    let i : topologicalProfiniteCompletionPreimageIndex P f N ⟶ H :=
      hNH.hom
    have htransition :=
      topologicalProfiniteCompletionProjection_transition G i x
    have hmap :
        (ProfiniteGrp.Hom.hom ((openFiniteQuotientDiagram G).map i))
            (topologicalProfiniteCompletionProjection G
              (topologicalProfiniteCompletionPreimageIndex P f N) x) =
          (ProfiniteGrp.Hom.hom ((openFiniteQuotientDiagram G).map i))
            (1 : (openFiniteQuotientDiagram G).obj
              (topologicalProfiniteCompletionPreimageIndex P f N)) :=
      congrArg
        (ProfiniteGrp.Hom.hom ((openFiniteQuotientDiagram G).map i))
        hpreimage
    have hone :
        (ProfiniteGrp.Hom.hom ((openFiniteQuotientDiagram G).map i))
            (1 : (openFiniteQuotientDiagram G).obj
              (topologicalProfiniteCompletionPreimageIndex P f N)) =
          (1 : (openFiniteQuotientDiagram G).obj H) :=
      map_one _
    exact htransition.symm.trans (hmap.trans hone)
  · exact bot_le

end LocalClassFieldTheory
