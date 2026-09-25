/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.MarshallHall.MarshallHall.Hall
public import LeanPool.MarshallHall.MarshallHall.GrushkoGeneral
public import LeanPool.MarshallHall.MarshallHall.GrushkoReduction
public import LeanPool.MarshallHall.MarshallHall.GrushkoFold
public import LeanPool.MarshallHall.MarshallHall.GrushkoGraph
public import LeanPool.MarshallHall.MarshallHall.GrushkoFoldStep
public import LeanPool.MarshallHall.MarshallHall.GrushkoRose
public import LeanPool.MarshallHall.MarshallHall.GrushkoEdge
public import LeanPool.MarshallHall.MarshallHall.GrushkoUnfold
public import LeanPool.MarshallHall.MarshallHall.GrushkoInvariant
public import LeanPool.MarshallHall.MarshallHall.GrushkoReductionChain
public import LeanPool.MarshallHall.MarshallHall.GrushkoFull


/-!
# Marshall Hall's theorem through finite cores

The finite-core completion developed in `MarshallHall.Hall` proves the
inclusion-compatible free-factor form of Marshall Hall's theorem.  The same
repository also contains the LERF consequence, the binary and finite-indexed
free-group Grushko rank calculations, and the factorwise infrastructure for
the arbitrary-factor theorem.
-/

@[expose] public section



universe u

open Monoid.Coprod

namespace MarshallHall

/-! ### Arbitrary-factor Grushko--Neumann -/

/-- The rank of a free product of two finitely generated groups is additive.

The proof is the finite labelled-graph reduction: a minimal null path yields
either a safe fold or, after source-unfolding, a safe fold followed by an
explicit monochromatic-vertex contraction.  The resulting strict decrease in
the finite graph supplies the strong induction on the number of vertices.
-/
theorem rank_freeProduct_eq_add {G H : Type u} [Group G] [Group H]
    [Group.FG G] [Group.FG H] :
    Group.rank (G ∗ H) = Group.rank G + Group.rank H :=
  GeneralGrushko.rank_coprod_eq_add

end MarshallHall

/-! Public LERF surfaces.  The explicit permutation separator is the primary
finite-quotient formulation; the stabilizer formulation is its existential
finite-index corollary. -/

theorem freeGroup_finite_permutation_separator
    {α : Type*}
    (H : Subgroup (FreeGroup α))
    [Group.FG H]
    (g : FreeGroup α)
    (hg : g ∉ H) :
    Nonempty (MarshallHall.FinitePermutationSeparator H g) :=
  MarshallHall.freeGroup_finite_permutation_separator_proved H g hg

theorem freeGroup_subgroup_separable
    {α : Type*}
    (H : Subgroup (FreeGroup α))
    [Group.FG H]
    (g : FreeGroup α)
    (hg : g ∉ H) :
    ∃ K : Subgroup (FreeGroup α),
      H ≤ K ∧ K.index ≠ 0 ∧ g ∉ K :=
  MarshallHall.freeGroup_subgroup_separable_proved H g hg
