/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.Kurosh.SchreierCover
import Mathlib.CategoryTheory.Groupoid.FreeGroupoid

/-!
# Index Formula

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

open Set Function
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

universe u

namespace GraphCoveringTheory

noncomputable instance actionCategoryFintype (M : Type u) (A : Type u)
    [Monoid M] [MulAction M A] [Fintype A] : Fintype (ActionCategory M A) :=
  Fintype.ofEquiv A (ActionCategory.objEquiv M A)

noncomputable instance coverHomFintype (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] [Fintype α] (a b : CoverVertex α A) :
    Fintype (a ⟶ b) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter (fun e : α => FreeGroup.of e • a.back = b.back)) (by simp)

/-- A Schreier edge is determined by its source and its free generator. -/
def coverGeneratorTotalEquiv (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] :
    Quiver.Total (CoverVertex α A) ≃ A × α where
  toFun e := ⟨e.left.back, e.hom.val⟩
  invFun e :=
    ⟨(e.1 : CoverVertex α A),
      ((FreeGroup.of e.2 • e.1 : A) : CoverVertex α A),
      ⟨e.2, rfl⟩⟩
  left_inv e := by
    rcases e with ⟨x, y, ⟨e, h⟩⟩
    cases x with | mk x
    cases y with | mk y
    cases h
    rfl
  right_inv e := by
    rcases e with ⟨a, e⟩
    rfl

/-- The action groupoid's chosen generating edges are indexed by a point and a generator. -/
def freeActionGeneratorTotalEquiv (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] :
    @Quiver.Total (CoverVertex α A)
      (freeActionGroupoidIsFree α A).quiverGenerators ≃ A × α :=
  coverGeneratorTotalEquiv α A

/-- The geodesic spanning tree in the symmetrified generating quiver, rooted at `r`. -/
noncomputable def freeGroupoidTree (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G] (r : G) :
    WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G)) :=
  @geodesicSubtree
    (Symmetrify (IsFreeGroupoid.Generators G))
    (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators G))
    (show Symmetrify (IsFreeGroupoid.Generators G) from r)
    (@IsFreeGroupoid.generators_connected G _ _ _ r)

/-- The chosen geodesic spanning tree is an arborescence rooted at `r`. -/
@[reducible] noncomputable def freeGroupoidTreeArborescence (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G] (r : G) :
    Arborescence (freeGroupoidTree G r) := by
  dsimp [freeGroupoidTree]
  exact @Quiver.geodesicArborescence
    (Symmetrify (IsFreeGroupoid.Generators G)) _
    (show Symmetrify (IsFreeGroupoid.Generators G) from r)
    (@IsFreeGroupoid.generators_connected G _ _ _ r)

/-- The generators outside the chosen geodesic spanning tree. -/
noncomputable abbrev freeGroupoidGeneratorSet (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    (r : G) :
    Set (Quiver.Total (IsFreeGroupoid.Generators G)) :=
  (wideSubquiverEquivSetTotal
    (wideSubquiverSymmetrify (freeGroupoidTree G r)))ᶜ

noncomputable instance freeGroupoidGeneratorSetFintype (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)] (r : G) :
    Fintype (freeGroupoidGeneratorSet G r) := by
  classical
  exact inferInstance

/-- The generating edges outside a given wide subquiver and its reverse. -/
noncomputable abbrev generatorComplement (G : Type u) [Groupoid G]
    [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) :
    Set (Quiver.Total (IsFreeGroupoid.Generators G)) :=
  (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ

noncomputable instance generatorComplementFintype (G : Type u) [Groupoid G]
    [IsFreeGroupoid G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) :
    Fintype (generatorComplement G T) := by
  classical
  exact inferInstance

lemma generatorComplement_card (G : Type u) [Groupoid G]
    [IsFreeGroupoid G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G)))
    [Arborescence T] :
    Fintype.card (generatorComplement G T) =
      Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G) := by
  classical
  let G' := IsFreeGroupoid.Generators G
  let S : Set (Quiver.Total G') :=
    wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)
  have hS : Fintype.card S = Fintype.card G' - 1 := by
    simpa [S] using (FiniteGraphFreeGroup.symmetrified_tree_set_card T)
  have hcomp : Fintype.card (Sᶜ : Set (Quiver.Total G')) =
      Fintype.card (Quiver.Total G') - Fintype.card S := by
    exact @Fintype.card_subtype_compl _ _ (fun e : Quiver.Total G' => e ∈ S)
      inferInstance inferInstance
  have htreele : Fintype.card S ≤ Fintype.card (Quiver.Total G') :=
    Fintype.card_subtype_le _
  have htreele' : Fintype.card G' - 1 ≤ Fintype.card (Quiver.Total G') := by
    rw [← hS]
    exact htreele
  have hGpos : 1 ≤ Fintype.card G' := by
    exact Fintype.card_pos_iff.mpr ⟨show G' from root T⟩
  change Fintype.card (Sᶜ : Set (Quiver.Total G')) =
    Fintype.card (Quiver.Total G') + 1 - Fintype.card G'
  rw [hcomp, hS]
  omega

lemma freeGroupoidGeneratorSet_card (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)] (r : G) :
    Fintype.card (freeGroupoidGeneratorSet G r) =
      Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G) := by
  let : Arborescence (freeGroupoidTree G r) := freeGroupoidTreeArborescence G r
  exact generatorComplement_card G (freeGroupoidTree G r)

theorem freeGroupoid_end_free_basis (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)] (r : G) :
    Nonempty (FreeGroupBasis (Fin
      (Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G))) (End r)) := by
  classical
  let T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G)) :=
    @geodesicSubtree
      (Symmetrify (IsFreeGroupoid.Generators G))
      (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators G))
      (show Symmetrify (IsFreeGroupoid.Generators G) from r)
      (@IsFreeGroupoid.generators_connected G _ _ _ r)
  let : Arborescence T := @Quiver.geodesicArborescence
    (Symmetrify (IsFreeGroupoid.Generators G)) _
    (show Symmetrify (IsFreeGroupoid.Generators G) from r)
    (@IsFreeGroupoid.generators_connected G _ _ _ r)
  let X := generatorComplement G T
  have hroot : (show G from root T) = r := by
    rfl
  let B : FreeGroupBasis X (End r) := by
    rw [← hroot]
    simpa [X, generatorComplement] using (FiniteGraphFreeGroup.spanningTreeBasis T)
  have hcard := generatorComplement_card G T
  let eX : X ≃ Fin
      (Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G)) :=
    hcard ▸ Fintype.equivFin X
  exact ⟨B.reindex eX⟩

theorem freeGroupoid_end_free_rank (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)] (r : G) :
    Nonempty (End r ≃* FreeGroup (Fin
      (Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G)))) := by
  rcases freeGroupoid_end_free_basis G r with ⟨B⟩
  exact ⟨B.repr⟩

theorem schreier_basis_fintype (α : Type u) [Fintype α]
    (H : Subgroup (FreeGroup α)) [H.FiniteIndex] :
    Nonempty (FreeGroupBasis
      (Fin (H.index * Fintype.card α + 1 - H.index)) H) := by
  let : Fintype (FreeGroup α ⧸ H) := H.fintypeQuotientOfFiniteIndex
  let : Nonempty (FreeGroup α ⧸ H) :=
    ⟨((1 : FreeGroup α) : FreeGroup α ⧸ H)⟩
  let : MulAction.IsPretransitive (FreeGroup α) (FreeGroup α ⧸ H) :=
    MulAction.isPretransitive_quotient (FreeGroup α) H
  let : IsFreeGroupoid
      (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H)) :=
    freeActionGroupoidIsFree α (FreeGroup α ⧸ H)
  let : Fintype (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H)) :=
    actionCategoryFintype (FreeGroup α) (FreeGroup α ⧸ H)
  let : Fintype
      (IsFreeGroupoid.Generators
        (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H))) :=
    Fintype.ofEquiv (FreeGroup α ⧸ H)
      (ActionCategory.objEquiv (FreeGroup α) (FreeGroup α ⧸ H))
  let : ∀ a b : IsFreeGroupoid.Generators
      (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H)), Fintype (a ⟶ b) :=
    fun a b => coverHomFintype α (FreeGroup α ⧸ H) a b
  let : Fintype (Quiver.Total (CoverVertex α (FreeGroup α ⧸ H))) :=
    FiniteGraphFreeGroup.baseTotalFintype
  let : Fintype
      (@Quiver.Total (CoverVertex α (FreeGroup α ⧸ H))
        (freeActionGroupoidIsFree α (FreeGroup α ⧸ H)).quiverGenerators) :=
    Fintype.ofEquiv
      ((FreeGroup α ⧸ H) × α)
      (freeActionGeneratorTotalEquiv α (FreeGroup α ⧸ H)).symm
  let : Fintype
      (Quiver.Total
        (IsFreeGroupoid.Generators
          (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H)))) :=
    FiniteGraphFreeGroup.baseTotalFintype
  let r : ActionCategory (FreeGroup α) (FreeGroup α ⧸ H) :=
    ActionCategory.objEquiv (FreeGroup α) (FreeGroup α ⧸ H)
      ((1 : FreeGroup α) : FreeGroup α ⧸ H)
  have hconn : IsConnected
      (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H)) := inferInstance
  have h := @freeGroupoid_end_free_basis
    (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H))
    (by infer_instance)
    (freeActionGroupoidIsFree α (FreeGroup α ⧸ H))
    hconn
    (by infer_instance)
    (by exact fun a b => coverHomFintype α (FreeGroup α ⧸ H) a b)
    r
  have hvertices : Fintype.card
      (IsFreeGroupoid.Generators
      (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H))) = H.index := by
    change Fintype.card (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H)) = H.index
    calc
      Fintype.card (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H)) =
          Fintype.card (FreeGroup α ⧸ H) :=
        Fintype.card_congr (ActionCategory.objEquiv
          (FreeGroup α) (FreeGroup α ⧸ H)).symm
      _ = Nat.card (FreeGroup α ⧸ H) := Nat.card_eq_fintype_card.symm
      _ = H.index := (Subgroup.index_eq_card H).symm
  have hquotient : Fintype.card (FreeGroup α ⧸ H) = H.index := by
    calc
      Fintype.card (FreeGroup α ⧸ H) =
          Nat.card (FreeGroup α ⧸ H) := Nat.card_eq_fintype_card.symm
      _ = H.index := (Subgroup.index_eq_card H).symm
  have hedges : Fintype.card
      (Quiver.Total
        (IsFreeGroupoid.Generators
          (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H)))) =
      H.index * Fintype.card α := by
    have htotal : Fintype.card
        (Quiver.Total
          (IsFreeGroupoid.Generators
            (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H)))) =
        Fintype.card ((FreeGroup α ⧸ H) × α) :=
      Fintype.card_congr (freeActionGeneratorTotalEquiv α
        (FreeGroup α ⧸ H))
    rw [htotal]
    simp only [Fintype.card_prod]
    simp [hquotient]
  rcases h with ⟨B⟩
  have e' : End r ≃* H := by
    simpa [r] using (ActionCategory.endMulEquivSubgroup H)
  have hdim :
      Fintype.card (Quiver.Total
          (IsFreeGroupoid.Generators
            (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H)))) + 1 -
          Fintype.card (IsFreeGroupoid.Generators
            (ActionCategory (FreeGroup α) (FreeGroup α ⧸ H))) =
        H.index * Fintype.card α + 1 - H.index := by
    rw [hedges, hvertices]
  rw [hdim] at B
  exact ⟨B.map e'⟩

theorem schreier_index_formula_fintype (α : Type u) [Fintype α]
    (H : Subgroup (FreeGroup α)) [H.FiniteIndex] :
    Nonempty (H ≃* FreeGroup (Fin
      (H.index * Fintype.card α + 1 - H.index))) := by
  rcases schreier_basis_fintype α H with ⟨B⟩
  exact ⟨B.repr⟩

theorem schreier_index_formula_nat (n : ℕ) (H : Subgroup (FreeGroup (Fin n)))
    [H.FiniteIndex] :
    Nonempty (H ≃* FreeGroup (Fin (H.index * n + 1 - H.index))) := by
  let : Fintype (Fin n) := Fin.fintype n
  have h := schreier_index_formula_fintype (Fin n) H
  rw [Fintype.card_fin] at h
  exact h

theorem schreier_basis_fintype_proved (α : Type u) [Fintype α]
    [Nonempty α] (H : Subgroup (FreeGroup α)) [H.FiniteIndex] :
    Nonempty (FreeGroupBasis
      (Fin (1 + H.index * (Fintype.card α - 1))) H) := by
  rcases schreier_basis_fintype α H with ⟨B⟩
  have hα : 0 < Fintype.card α := Fintype.card_pos_iff.mpr inferInstance
  have hm : H.index * (Fintype.card α - 1) =
      H.index * Fintype.card α - H.index := by
    rw [Nat.sub_one]
    exact Nat.mul_pred H.index (Fintype.card α)
  have hindex : H.index * Fintype.card α + 1 - H.index =
      1 + H.index * (Fintype.card α - 1) := by
    calc
      H.index * Fintype.card α + 1 - H.index =
          1 + H.index * Fintype.card α - H.index := by
        rw [Nat.add_comm (H.index * Fintype.card α) 1]
      _ = 1 + (H.index * Fintype.card α - H.index) :=
        Nat.add_sub_assoc (Nat.le_mul_of_pos_right H.index hα) 1
      _ = 1 + H.index * (Fintype.card α - 1) := by rw [← hm]
  rw [hindex] at B
  exact ⟨B⟩

theorem schreier_index_formula_fintype_proved (α : Type u) [Fintype α]
    [Nonempty α] (H : Subgroup (FreeGroup α)) [H.FiniteIndex] :
    Nonempty (H ≃* FreeGroup (Fin
      (1 + H.index * (Fintype.card α - 1)))) := by
  rcases schreier_basis_fintype_proved α H with ⟨B⟩
  exact ⟨B.repr⟩

theorem schreier_index_formula_proved (n : ℕ)
    (H : Subgroup (FreeGroup (Fin n))) [H.FiniteIndex] (hn : 0 < n) :
    Nonempty (H ≃* FreeGroup (Fin (1 + H.index * (n - 1)))) := by
  let : Fintype (Fin n) := Fin.fintype n
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := schreier_index_formula_fintype_proved (Fin n) H
  rw [Fintype.card_fin] at h
  exact h

end GraphCoveringTheory
