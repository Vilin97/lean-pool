/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import Mathlib.Combinatorics.Matroid.Minor.Contract
public import Mathlib.Combinatorics.Matroid.Rank.ENat

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-!
Source vocabulary for Baker–Jin–Lorscheid, arXiv:2601.02582, Sections 1 and 4.
We reuse Mathlib flats, closure, contraction and `eRk`. In the finite-ground-set
setting all ranks here are finite, so their equations are natural-rank equations.
The pinned matroid API has no connectedness, hyperplane or modular-cut predicate.
-/

public section

namespace TutteFormalization

variable {α : Type*}

/-- `def:matroid-operations`: no partition into two nonempty additive-rank parts.
In particular, no nonemptiness of the ground set is required. -/
@[expose] def Connected (M : Matroid α) : Prop :=
  ¬ ∃ A B : Set α, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
    A ∪ B = M.E ∧ M.eRk A + M.eRk B = M.eRk M.E

/-- `def:matroid`: a maximal proper flat. Ground containment follows from `IsFlat`. -/
@[expose] def IsHyperplane (M : Matroid α) (H : Set α) : Prop :=
  M.IsFlat H ∧ H ≠ M.E ∧
    ∀ G : Set α, M.IsFlat G → H ⊆ G → G = H ∨ G = M.E

/-- `def:indecomposable`: flatness and source connectedness of the contraction. -/
@[expose] def Indecomposable (M : Matroid α) (F : Set α) : Prop :=
  M.IsFlat F ∧ Connected (M.contract F)

/-- `def:modular-cut`: a pair of flats satisfying the modular rank equality.
Their join is the Mathlib closure of their union. -/
@[expose] def ModularPair (M : Matroid α) (F G : Set α) : Prop :=
  M.IsFlat F ∧ M.IsFlat G ∧
    M.eRk F + M.eRk G = M.eRk (F ∩ G) + M.eRk (M.closure (F ∪ G))

/-- `def:modular-cut`: a collection of flats, upward closed among flats and
closed under intersections of modular pairs. The empty collection is allowed. -/
structure ModularCut (M : Matroid α) (Γ : Set (Set α)) : Prop where
  isFlat : ∀ F ∈ Γ, M.IsFlat F
  upward : ∀ F G : Set α, F ∈ Γ → M.IsFlat G → F ⊆ G → G ∈ Γ
  inter_mem : ∀ F G : Set α, F ∈ Γ → G ∈ Γ → ModularPair M F G → F ∩ G ∈ Γ

/-- A corank-two flat: for finite ground set, this rank equation says
`rk(M.E) - rk(F) = 2`, without truncated subtraction or conversion from `ℕ∞`. -/
@[expose] def CorankTwo (M : Matroid α) (F : Set α) : Prop :=
  M.IsFlat F ∧ M.eRk F + 2 = M.eRk M.E

/-- `def:tutte-path`: the condition on two consecutive vertices.
Hyperplane conditions are imposed on every vertex by `TuttePath`. -/
@[expose] def TutteAdjacent (M : Matroid α) (H K : Set α) : Prop :=
  H ≠ K ∧ Indecomposable M (H ∩ K) ∧ CorankTwo M (H ∩ K)

/-- `def:tutte-path`: `length` counts edges, and there are `length + 1` vertices.
`i.castSucc` and `i.succ` index positions `i` and `i+1`. Length zero is allowed;
there is no injectivity requirement or restriction on nonconsecutive repetitions. -/
structure TuttePath (M : Matroid α) where
  /-- Number of edges. -/
  length : ℕ
  /-- The nonempty finite sequence of hyperplanes. -/
  vertex : Fin (length + 1) → Set α
  isHyperplane : ∀ i, IsHyperplane M (vertex i)
  adjacent : ∀ i : Fin length, TutteAdjacent M (vertex i.castSucc) (vertex i.succ)

namespace TuttePath

variable {M : Matroid α}

/-- The first vertex. -/
@[expose] def origin (p : TuttePath M) : Set α := p.vertex 0

/-- The last vertex. -/
@[expose] def terminus (p : TuttePath M) : Set α := p.vertex (Fin.last p.length)

/-- Every vertex contains `F`; this does not assert that `F` is the carrier. -/
@[expose] def On (p : TuttePath M) (F : Set α) : Prop := ∀ i, F ⊆ p.vertex i

/-- Every vertex lies outside the cut. -/
@[expose] def Off (p : TuttePath M) (Γ : Set (Set α)) : Prop := ∀ i, p.vertex i ∉ Γ

/-- The carrier from `def:tutte-path`. The index type is always nonempty. -/
def carrier (p : TuttePath M) : Set α := ⋂ i, p.vertex i

end TuttePath
end TutteFormalization
