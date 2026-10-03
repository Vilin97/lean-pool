/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.PathRanks
public import Mathlib.Data.Fin.Tuple.Basic

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-!
The concrete path operations used by the source induction, PT-01/PT-02/PT-04/PT-09.
The protected finite-sequence representation is unchanged. Appending one vertex
is enough for the source proof; no injectivity of the sequence is imposed.
-/

public section

namespace TutteFormalization

variable {α : Type*} {M : Matroid α}

namespace TuttePath

/-- PT-01: a one-vertex path has no edge conditions. -/
@[expose] def singleton (H : Set α) (hH : IsHyperplane M H) : TuttePath M where
  length := 0
  vertex := fun _ => H
  isHyperplane := fun _ => hH
  adjacent := fun i => Fin.elim0 i

@[simp] theorem singleton_origin (H : Set α) (hH : IsHyperplane M H) :
    (singleton H hH).origin = H := rfl

@[simp] theorem singleton_terminus (H : Set α) (hH : IsHyperplane M H) :
    (singleton H hH).terminus = H := rfl

theorem singleton_on {H F : Set α} (hH : IsHyperplane M H) (hF : F ⊆ H) :
    (singleton H hH).On F := fun _ => hF

theorem singleton_off {H : Set α} {Γ : Set (Set α)} (hH : IsHyperplane M H)
    (hΓ : H ∉ Γ) : (singleton H hH).Off Γ := fun _ => hΓ

/-- PT-04: a path on a larger flat is also on any subset of that flat. -/
theorem On.mono {p : TuttePath M} {F G : Set α} (h : p.On G) (hFG : F ⊆ G) :
    p.On F := fun i => hFG.trans (h i)

/-- PT-09: append a hyperplane joined to the old terminus by a Tutte edge. -/
def snoc (p : TuttePath M) (H : Set α) (hH : IsHyperplane M H)
    (hEdge : TutteAdjacent M p.terminus H) : TuttePath M where
  length := p.length + 1
  vertex := Fin.snoc (α := fun _ => Set α) p.vertex H
  isHyperplane := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hH
    · simpa using p.isHyperplane j
  adjacent := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [terminus] using hEdge
    · simpa only [← Fin.castSucc_succ, Fin.snoc_castSucc] using p.adjacent j

@[simp] theorem snoc_origin (p : TuttePath M) (H : Set α) (hH : IsHyperplane M H)
    (hEdge : TutteAdjacent M p.terminus H) : (p.snoc H hH hEdge).origin = p.origin := by
  change Fin.snoc (α := fun _ => Set α) p.vertex H (Fin.castSucc 0) = p.vertex 0
  rw [Fin.snoc_castSucc]

@[simp] theorem snoc_terminus (p : TuttePath M) (H : Set α) (hH : IsHyperplane M H)
    (hEdge : TutteAdjacent M p.terminus H) : (p.snoc H hH hEdge).terminus = H := by
  simp [snoc, terminus]

theorem On.snoc {p : TuttePath M} {F H : Set α} (h : p.On F)
    (hH : IsHyperplane M H) (hEdge : TutteAdjacent M p.terminus H) (hFH : F ⊆ H) :
    (p.snoc H hH hEdge).On F := by
  change ∀ i : Fin (p.length + 1 + 1), F ⊆ Fin.snoc (α := fun _ => Set α) p.vertex H i
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [TuttePath.snoc] using hFH
  · simpa [TuttePath.snoc] using h j

theorem Off.snoc {p : TuttePath M} {Γ : Set (Set α)} {H : Set α} (h : p.Off Γ)
    (hH : IsHyperplane M H) (hEdge : TutteAdjacent M p.terminus H) (hHoff : H ∉ Γ) :
    (p.snoc H hH hEdge).Off Γ := by
  change ∀ i : Fin (p.length + 1 + 1), Fin.snoc (α := fun _ => Set α) p.vertex H i ∉ Γ
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [TuttePath.snoc] using hHoff
  · simpa [TuttePath.snoc] using h j

end TuttePath

/-- PT-01: the singleton case with the full endpoint and On/Off conclusions. -/
theorem exists_singleton_path {F X : Set α} {Γ : Set (Set α)}
    (hX : IsHyperplane M X) (hFX : F ⊆ X) (hXoff : X ∉ Γ) :
    ∃ p : TuttePath M, p.origin = X ∧ p.terminus = X ∧ p.On F ∧ p.Off Γ :=
  ⟨TuttePath.singleton X hX, rfl, rfl, TuttePath.singleton_on hX hFX,
    TuttePath.singleton_off hX hXoff⟩

/-- PT-02: a single edge, with all finite-sequence and vertex constraints. -/
theorem exists_edge_path {F X Y : Set α} {Γ : Set (Set α)}
    (hX : IsHyperplane M X) (hY : IsHyperplane M Y) (hXY : TutteAdjacent M X Y)
    (hFX : F ⊆ X) (hFY : F ⊆ Y) (hXoff : X ∉ Γ) (hYoff : Y ∉ Γ) :
    ∃ p : TuttePath M, p.origin = X ∧ p.terminus = Y ∧ p.On F ∧ p.Off Γ := by
  let p := TuttePath.singleton X hX
  have hEdge : TutteAdjacent M p.terminus Y := hXY
  refine ⟨p.snoc Y hY hEdge, ?_, ?_, ?_, ?_⟩
  · simp [p]
  · simp
  · exact (TuttePath.singleton_on hX hFX).snoc hY hEdge hFY
  · exact (TuttePath.singleton_off hX hXoff).snoc hY hEdge hYoff

/-- PT-02: complete corank-two base path, including equal endpoints. -/
theorem exists_path_of_corankTwo [M.Finite] {F X Y : Set α} {Γ : Set (Set α)}
    (hF : Indecomposable M F) (hc : CorankTwo M F)
    (hX : IsHyperplane M X) (hY : IsHyperplane M Y)
    (hFX : F ⊆ X) (hFY : F ⊆ Y) (hXoff : X ∉ Γ) (hYoff : Y ∉ Γ) :
    ∃ p : TuttePath M, p.origin = X ∧ p.terminus = Y ∧ p.On F ∧ p.Off Γ := by
  by_cases hXY : X = Y
  · subst Y
    exact exists_singleton_path hX hFX hXoff
  exact exists_edge_path hX hY (tutteAdjacent_of_corankTwo hF hc hX hY hXY hFX hFY)
    hFX hFY hXoff hYoff

end TutteFormalization
