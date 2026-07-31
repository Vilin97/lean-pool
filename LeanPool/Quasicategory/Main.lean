/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import LeanPool.Quasicategory._007F
import LeanPool.Quasicategory.Quasicategory
import LeanPool.Quasicategory.InternalHom
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

universe w

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory MonoidalClosed Limits PushoutProduct

variable {S : SSet} {m : ℕ}

noncomputable
def hornFromPullbackPower (S : SSet) : internalHom.PullbackObjObj Λ[2, 1].ι (isTerminalZero.from S) :=
  Functor.PullbackObjObj.ofHasPullback ..

noncomputable
def pullback_ihom_terminal_iso {S : SSet} :
    pullback ((ihom Λ[2, 1].toSSet).map (isTerminalZero.from S)) ((pre Λ[2, 1].ι).app Δ[0]) ≅
      (ihom Λ[2, 1].toSSet).obj S where
  hom := pullback.fst _ _
  inv := pullback.lift (𝟙 _) ((isTerminalZeroPow isTerminalZero).from _) rfl

noncomputable
def hornFromPullbackPower_π_arrowIso :
    Arrow.mk (S.hornFromPullbackPower.π) ≅ Arrow.mk ((internalHom.map Λ[2, 1].ι.op).app S) := by
  dsimp [hornFromPullbackPower]
  refine Arrow.isoMk (Iso.refl _) pullback_ihom_terminal_iso ?_
  simp [pullback_ihom_terminal_iso, Functor.PullbackObjObj.π]

-- `0079`
open HasLiftingProperty ParametrizedAdjunction in
/-- `S` is a quasi-category iff `ihom(Δ[2], S) ⟶ ihom(Λ[2, 1], S)` is a trivial fibration. -/
instance quasicategory_iff_internalHom_horn_trivialFibration (S : SSet) :
    Quasicategory S ↔
      trivialFibration ((internalHom.map Λ[2, 1].ι.op).app S) := by
  rw [quasicategory_iff_from_innerAnodyne_rlp, morphism_rlp_iff,
    innerAnodyne_eq_saturation_hornBoundaryPushouts, ← Saturated.le_iff, le_llp_iff_le_rlp, morphism_le_iff]
  constructor
  · intro h _ _ _ ⟨m⟩
    rw [← iff_of_arrow_iso_right _ hornFromPullbackPower_π_arrowIso,
      ← hasLiftingProperty_iff internalHomAdjunction₂ _ _]
    exact h _ ⟨m⟩
  · intro h _ _ _ ⟨m⟩
    rw [hasLiftingProperty_iff internalHomAdjunction₂,
      iff_of_arrow_iso_right _ hornFromPullbackPower_π_arrowIso]
    exact h _ ⟨m⟩

/-- `0071` (special case of `0070`) if `p : X ⟶ Y` is a trivial fibration, then `ihom(B, X) ⟶ ihom(B, Y)` is -/
instance trivialFibration_of_ihom_map_trivialFibration {X Y : SSet} (B : SSet) (p : X ⟶ Y) (hp: trivialFibration p) :
    trivialFibration ((ihom B).map p) := by
  intro _ _ i ⟨n⟩
  rw [trivialFibration_eq_rlp_monomorphisms] at hp
  have := hp _ ((tensorLeft_PreservesMonomorphisms B).preserves ∂Δ[n].ι)
  constructor
  intro f g sq
  exact (CommSq.left_adjoint_hasLift_iff sq (FunctorToTypes.adj B)).1
      (this.sq_hasLift (sq.left_adjoint (Closed.adj)))

open MonoidalClosed in
/-- if `D` is a quasi-category, then the restriction map
  `ihom(Δ[2], ihom(S, D)) ⟶ ihom(Λ[2, 1], ihom(S, D))` is a trivial fibration. -/
def trivialFibration_internalHom_horn_map (S D : SSet) [Quasicategory D] :
    trivialFibration ((internalHom.map Λ[2, 1].ι.op).app ((ihom S).obj D)) := by
  intro _ _ i ⟨n⟩
  have := (quasicategory_iff_internalHom_horn_trivialFibration D).1 (by infer_instance)
  have := (trivialFibration_of_ihom_map_trivialFibration S ((internalHom.map Λ[2, 1].ι.op).app D)) this _ (.mk n)
  dsimp at this
  have H : Arrow.mk ((ihom S).map ((pre Λ[2, 1].ι).app D)) ≅
      Arrow.mk ((internalHom.map Λ[2, 1].ι.op).app ((ihom S).obj D)) :=
    CategoryTheory.Comma.isoMk (ihom_ihom_symm_iso _ _ _) (ihom_ihom_symm_iso _ _ _)
  exact HasLiftingProperty.of_arrow_iso_right ∂Δ[n].ι H

section _00J8

variable {A B X Y : SSet} (f : A ⟶ B) {g : X ⟶ Y} [hf : Mono f]

inductive hornMonoPushout : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk {X Y : SSet} (i : X ⟶ Y) (hi : Mono i) : hornMonoPushout (Λ[2, 1].ι □ i)

def hornMonoPushouts : MorphismProperty SSet := fun _ _ p ↦ hornMonoPushout p

lemma saturation_hornMonoPushouts_eq : saturation.{w} hornMonoPushouts = innerAnodyne.{w} := by
  apply le_antisymm
  · rw [← Saturated.le_iff]
    intro _ _ _ ⟨i, _⟩
    exact hornMonoPushout_innerAnodyne i
  · rw [innerAnodyne_eq_saturation_hornBoundaryPushouts, ← Saturated.le_iff]
    intro _ _ _ ⟨m⟩
    exact .of _ (.mk _ (instMonoι _))

lemma innerAnodyne_le_T : innerAnodyne ≤ (innerAnodyne.pushoutProduct f) := by
  rw [← saturation_hornMonoPushouts_eq, ← Saturated.le_iff,
    saturation_hornMonoPushouts_eq]
  intro _ _ _ ⟨i, _⟩
  have : Arrow.mk (f □ Λ[2, 1].ι □ i) ≅ Arrow.mk (Λ[2, 1].ι □ f □ i) :=
    (comm_iso _ _) ≪≫
    (PushoutProduct.associator _ _ _) ≪≫
    (iso_of_arrow_iso Λ[2, 1].ι _ _ (comm_iso i f))
  dsimp only [MorphismProperty.pushoutProduct]
  rw [innerAnodyne.arrow_mk_iso_iff this]
  sorry--exact hornMonoPushout_innerAnodyne (f □ i)

lemma _00J8 (hg : innerAnodyne g) :
    innerAnodyne (f □ g) := innerAnodyne_le_T _ _ hg

end _00J8

open ParametrizedAdjunction in
lemma _01BT {X S A B : SSet} (p : X ⟶ S) (i : A ⟶ B)
    (hp : innerFibration p) [hi : Mono i] :
    innerFibration (Functor.PullbackObjObj.ofHasPullback internalHom i p).π := by
  rw [innerFibration_eq_rlp_innerAnodyne] at hp ⊢
  intro _ _ f hf
  rw [← hasLiftingProperty_iff internalHomAdjunction₂]
  exact hp _ (_00J8 i hf)

end SSet
