/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.TrivalentExpansion
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreExpansionClosed
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations

/-!
# The closed centipede face

Contracting the internal edges of the centipede expansion recovers the
original subdivision.  This file expresses that observation in the closed
orthant language consumed by the Atanasov--Ranganathan row constructions.
-/

@[expose] public section
namespace Utilities.Subdivision.TrivalentExpansion

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ExplicitPotential
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.DegenerateSpec
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.PseudocorePresentation
open Utilities.Subdivision.CoreExpansion
open Utilities.Subdivision.CoreExpansion.ExpansionData
open AtanasovRanganathan.Configurations

section ClosedFace

variable {n p : ℕ} (C : Core n p)
variable (hDeg : ∀ w : Fin n, 3 ≤ slotValence C w)

/-- Number of vertices in the trivalent centipede expansion. -/
abbrev expandedVertexCount := 2 * (p - n)
/-- Number of edge slots in the trivalent centipede expansion. -/
abbrev expandedSlotCount := 3 * (p - n)

/-- The distinguished first vertex of each centipede fibre. -/
noncomputable def firstVertex (w : Fin n) : Fin (expandedVertexCount (n := n) (p := p)) :=
  vEquiv C hDeg ⟨w, ⟨0, by have := hDeg w; omega⟩⟩

@[simp] theorem data_fib_firstVertex (w : Fin n) :
    (data C hDeg).fib (firstVertex C hDeg w) = w := by
  simp [firstVertex]

theorem firstVertex_injective : Function.Injective (firstVertex C hDeg) := by
  intro a b hab
  have h := (vEquiv C hDeg).injective hab
  exact congrArg Sigma.fst h

/-- The retraction choosing the first vertex in each centipede fibre. -/
noncomputable def firstRep (v : Fin (expandedVertexCount (n := n) (p := p))) :
    Fin (expandedVertexCount (n := n) (p := p)) :=
  firstVertex C hDeg ((data C hDeg).fib v)

@[simp] theorem firstRep_firstVertex (w : Fin n) :
    firstRep C hDeg (firstVertex C hDeg w) = firstVertex C hDeg w := by
  simp [firstRep]

theorem firstRep_idem (v : Fin (expandedVertexCount (n := n) (p := p))) :
    firstRep C hDeg (firstRep C hDeg v) = firstRep C hDeg v := by
  simp [firstRep]

theorem firstRep_eq_iff_fib_eq (a b : Fin (expandedVertexCount (n := n) (p := p))) :
    firstRep C hDeg a = firstRep C hDeg b ↔
      (data C hDeg).fib a = (data C hDeg).fib b := by
  exact (firstVertex_injective C hDeg).eq_iff

theorem card_image_firstRep :
    (Finset.univ.image (firstRep C hDeg)).card = n := by
  classical
  have hImage :
      Finset.univ.image (firstRep C hDeg) =
        Finset.univ.image (firstVertex C hDeg) := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr
        ⟨(data C hDeg).fib x, Finset.mem_univ _, rfl⟩
    · intro hv
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr
        ⟨firstVertex C hDeg w, Finset.mem_univ _, by simp⟩
  rw [hImage, Finset.card_image_of_injective Finset.univ
    (firstVertex_injective C hDeg)]
  simp

/-- The closed length vector: centipede edges vanish and carrier slots retain
the lengths of the original subdivision. -/
noncomputable def closedLength (small : Spec n p)
    (e : Fin (expandedSlotCount (n := n) (p := p))) : ℕ :=
  match (eEquiv C hDeg).symm e with
  | Sum.inl _ => 0
  | Sum.inr j => small.length j

@[simp] theorem closedLength_internal (x : Σ w : Fin n, Fin (slotValence C w - 3))
    (small : Spec n p) :
    closedLength C hDeg small (eEquiv C hDeg (Sum.inl x)) = 0 := by
  simp [closedLength]

@[simp] theorem closedLength_carrier (j : Fin p) (small : Spec n p) :
    closedLength C hDeg small (eEquiv C hDeg (Sum.inr j)) = small.length j := by
  simp [closedLength]

theorem zeroSlots_closedLength (small : Spec n p) :
    zeroSlots (closedLength C hDeg small) = (data C hDeg).contractedSlots := by
  ext e
  obtain ⟨a, rfl⟩ := exists_slot C hDeg e
  cases a with
  | inl x => simp
  | inr j =>
      simp only [mem_zeroSlots, closedLength_carrier, data_kind_inr,
        ExpansionData.mem_contractedSlots]
      exact iff_of_false (Nat.ne_of_gt (small.length_pos j)) (by simp)

theorem card_contractedSlots :
    (data C hDeg).contractedSlots.card = expandedVertexCount (n := n) (p := p) - n := by
  classical
  let internal := Σ w : Fin n, Fin (slotValence C w - 3)
  let embed : internal → Fin (expandedSlotCount (n := n) (p := p)) :=
    fun x => eEquiv C hDeg (Sum.inl x)
  have hEmbed : Function.Injective embed := by
    intro a b hab
    exact Sum.inl.inj ((eEquiv C hDeg).injective hab)
  have hSet : (data C hDeg).contractedSlots = Finset.univ.image embed := by
    ext e
    obtain ⟨a, rfl⟩ := exists_slot C hDeg e
    cases a with
    | inl x =>
        simp [embed]
    | inr j =>
        simp [embed]
  rw [hSet, Finset.card_image_of_injective Finset.univ hEmbed]
  simp only [Finset.card_univ]
  dsimp only [internal]
  simp only [Fintype.card_sigma, Fintype.card_fin]
  change (∑ w : Fin n, (slotValence C w - 3)) =
    2 * (p - n) - n
  have hSum := sum_valence_sub_three C hDeg
  omega

theorem card_image_compFold_contracted
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e) :
    (Finset.univ.image
      (compFold (data C hDeg).bigCore (data C hDeg).contractedSlots)).card = n := by
  apply le_antisymm
  · have hCard := card_image_le_of_rep_iff
      (compFold_idem (data C hDeg).bigCore (data C hDeg).contractedSlots)
      (fun a b => (compFold_eq_iff_fib_eq (conditions C hDeg hLoop) a b).trans
        (firstRep_eq_iff_fib_eq C hDeg a b).symm)
    simpa only [card_image_firstRep C hDeg] using hCard
  · have hCard := card_image_le_of_rep_iff (firstRep_idem C hDeg)
      (fun a b => (firstRep_eq_iff_fib_eq C hDeg a b).trans
        (compFold_eq_iff_fib_eq (conditions C hDeg hLoop) a b).symm)
    simpa only [card_image_firstRep C hDeg] using hCard

theorem closedLength_isForest
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e) (small : Spec n p) :
    IsForest (data C hDeg).bigCore (zeroSlots (closedLength C hDeg small)) := by
  rw [zeroSlots_closedLength C hDeg small]
  unfold IsForest
  rw [card_contractedSlots C hDeg,
    card_image_compFold_contracted C hDeg hLoop]

theorem closedLength_not_isLoopy
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e) (small : Spec n p) :
    ¬ IsLoopy (data C hDeg).bigCore (zeroSlots (closedLength C hDeg small)) := by
  rw [zeroSlots_closedLength C hDeg small]
  rintro ⟨e, he, hEq⟩
  obtain ⟨a, rfl⟩ := exists_slot C hDeg e
  cases a with
  | inl x =>
      exact he ((data C hDeg).mem_contractedSlots _ |>.mpr (by simp))
  | inr j =>
      have hFib := (compFold_eq_iff_fib_eq (conditions C hDeg hLoop) _ _).mp hEq
      exact hLoop j (by simpa [bigTail, bigHead] using hFib)

/-- The canonical closed face of the centipede expansion. -/
noncomputable def closedFace (small : Spec n p)
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e) :
    DegSpec (expandedVertexCount (n := n) (p := p)) (expandedSlotCount (n := n) (p := p)) :=
  faceSpec (data C hDeg).bigCore
    (Nat.zero_lt_of_lt (firstVertex C hDeg ⟨0, small.core_nonempty⟩).isLt)
    (closedLength C hDeg small)
    (closedLength_isForest C hDeg hLoop small)
    (closedLength_not_isLoopy C hDeg hLoop small)

@[simp] theorem closedFace_core (small : Spec n p)
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e) :
    (closedFace C hDeg small hLoop).core = (data C hDeg).bigCore := rfl

@[simp] theorem closedFace_length (small : Spec n p)
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e) :
    (closedFace C hDeg small hLoop).length = closedLength C hDeg small := rfl

theorem closedFace_rep (small : Spec n p)
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e)
    (v : Fin (expandedVertexCount (n := n) (p := p))) :
    (closedFace C hDeg small hLoop).rep v =
      compFold (data C hDeg).bigCore (data C hDeg).contractedSlots v := by
  unfold closedFace faceSpec
  change compFold (data C hDeg).bigCore
      (zeroSlots (closedLength C hDeg small)) v = _
  exact congrArg (fun F => compFold (data C hDeg).bigCore F v)
    (zeroSlots_closedLength C hDeg small)

/-- The contracted closed face is the original positive subdivision. -/
noncomputable def closedContraction (small : Spec n p)
    (hCore : small.core = C)
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e) :
    DegSpec.Contraction (closedFace C hDeg small hLoop) small where
  vtx := fun w => compFold (data C hDeg).bigCore
    (data C hDeg).contractedSlots (firstVertex C hDeg w)
  vtx_rep := by
    intro w
    rw [closedFace_rep]
    exact compFold_idem _ _ _
  vtx_inj := by
    intro a b hab
    have hFib := (compFold_eq_iff_fib_eq (conditions C hDeg hLoop) _ _).mp hab
    simpa using hFib
  vtx_surj := by
    intro v
    refine ⟨(data C hDeg).fib v, ?_⟩
    rw [closedFace_rep]
    exact (compFold_eq_iff_fib_eq (conditions C hDeg hLoop) _ _).mpr (by simp)
  slot := fun j => eEquiv C hDeg (Sum.inr j)
  slot_inj := by
    intro a b hab
    exact Sum.inr.inj ((eEquiv C hDeg).injective hab)
  slot_surj := by
    intro e hPos
    obtain ⟨a, rfl⟩ := exists_slot C hDeg e
    cases a with
    | inl x =>
        change 0 < closedLength C hDeg small (eEquiv C hDeg (Sum.inl x)) at hPos
        simp at hPos
    | inr j =>
        exact ⟨j, rfl⟩
  length_eq := by
    intro j
    change small.length j = closedLength C hDeg small (eEquiv C hDeg (Sum.inr j))
    simp
  tail_eq := by
    intro j
    rw [closedFace_rep]
    exact (compFold_eq_iff_fib_eq (conditions C hDeg hLoop) _ _).mpr (by
      simp only [closedFace_core]
      rw [data_tail, data_fib_firstVertex, data_fib]
      simp [bigTail, hCore])
  head_eq := by
    intro j
    rw [closedFace_rep]
    exact (compFold_eq_iff_fib_eq (conditions C hDeg hLoop) _ _).mpr (by
      simp only [closedFace_core]
      rw [data_head, data_fib_firstVertex, data_fib]
      simp [bigHead, hCore])

/-- Laplacian equivalence between the canonical closed centipede face and the
subdivision it collapses onto. -/
noncomputable def closedFaceEquiv (small : Spec n p)
    (hCore : small.core = C)
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e) :
    LaplacianEquiv small.graph (closedFace C hDeg small hLoop).graph :=
  (closedContraction C hDeg small hCore hLoop).laplacianEquiv

/-- A closed-orthant Brill--Noether existence theorem on the cubic centipede
expansion descends to the original positive subdivision, at arbitrary rank
and degree. -/
theorem bnExists_of_closedPencil
    (small : Spec n p)
    (hCore : small.core = C)
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e)
    {r degree : ℤ}
    (closed : ∀ (length : Fin (expandedSlotCount (n := n) (p := p)) → ℕ)
      (hForest : IsForest (data C hDeg).bigCore (zeroSlots length))
      (hNotLoopy : ¬ IsLoopy (data C hDeg).bigCore (zeroSlots length)),
      BNExists
        (faceSpec (data C hDeg).bigCore
          (Nat.zero_lt_of_lt (firstVertex C hDeg
            ⟨0, small.core_nonempty⟩).isLt)
          length hForest hNotLoopy).graph r degree) :
    BNExists small.graph r degree := by
  have hFace := closed (closedLength C hDeg small)
    (closedLength_isForest C hDeg hLoop small)
    (closedLength_not_isLoopy C hDeg hLoop small)
  exact ((closedFaceEquiv C hDeg small hCore hLoop).bnExists_iff r degree).mpr hFace

/-- A closed construction on the cubic centipede expansion supplies a
degree-four pencil on the original subdivision. -/
theorem bnExists_of_closedConstruction
    (small : Spec n p)
    (hCore : small.core = C)
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e)
    (construction : ClosedSubdivisionDharConstruction
      (data C hDeg).bigCore
      (Nat.zero_lt_of_lt (firstVertex C hDeg ⟨0, small.core_nonempty⟩).isLt)) :
    BNExists small.graph 1 4 := by
  apply bnExists_of_closedPencil C hDeg small hCore hLoop
  intro length hForest hNotLoopy
  obtain ⟨pencil⟩ := construction length hForest hNotLoopy
  exact pencil.bnExists

end ClosedFace

end Utilities.Subdivision.TrivalentExpansion
