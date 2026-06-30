/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Form.Short

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

public section

namespace Form

open Classical in
/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}\def\adjr#1{\operatorname{adj}_r\left(#1\right)}$
The *rooted adjoint* of `g` with *root* `r`. It is the same construction as the
`adjoint`, except that we place an arbitrary *root* `r` at the ends rather than
`0`:
$$
\adjr{G} =
\begin{cases}
\form<r>[r]
& \text{if } G \text{ has no ordinary options},\\
\form<\adjr{G^\mathcal{R}}>[r]
& \text{if } G \text{ has ordinary Right options, but no ordinary Left options},\\
\form<r>[\adjr{G^\mathcal{L}}]
& \text{if } G \text{ has ordinary Left options, but no ordinary Right options},\\
\form<\adjr{G^\mathcal{R}}>[\adjr{G^\mathcal{L}}]
& \text{otherwise}.
\end{cases}
$$

Taking `r = 0` recovers the standard `adjoint`.
-/
@[expose]
noncomputable def rootedAdjoint {G : Type (u + 1)} [Form G] (r g : G) : G :=
  have := moves_small.{u} .left g
  have := moves_small.{u} .right g
  if IsEnd .left g ∧ IsEnd .right g then !{{r} | {r}}
  else if IsEnd .left g then !{Set.range fun gr : moves .right g => rootedAdjoint r (gr : G) | {r}}
  else if IsEnd .right g then !{{r} | Set.range fun gl : moves .left g => rootedAdjoint r (gl : G)}
  else !{ Set.range fun gr : moves .right g => rootedAdjoint r (gr : G)
        | Set.range fun gl : moves .left g => rootedAdjoint r (gl : G)}
termination_by g
decreasing_by all_goals form_wf

/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
This extends the notion of the _adjoint_ of a short augmented form, as defined
by [Siegel (Definition 5.6 on p. 214)][siegel:GeneralDeadendingUniverse:2025],
to transfinite forms:
$$
G^\circ =
\begin{cases}
*
& \text{if } G \text{ has no ordinary options},\\
\form<\left(G^\mathcal{R}\right)^\circ>[0]
& \text{if} G \text{ has ordinary Right options, but no ordinary Left options},\\
\form<0>[\left(G^\mathcal{L}\right)^\circ]
& \text{if} G \text{ has ordinary Left options, but no ordinary Right options},\\
\form<\left(G^\mathcal{R}\right)^\circ>[\left(G^\mathcal{L}\right)^\circ]
& \text{otherwise}.
\end{cases}
$$

[Siegel (Definition 3.2 on p. 228)][siegel:CanonicalPartizan:2015] originally
defined this just for short game forms, which was a partizan analogue to the
impartial _mate_ due to [Conway (p. 147)][conway:NumbersAndGames:2001].

It is the special case of `rootedAdjoint` with root `0`.
-/
@[expose]
noncomputable def adjoint {G : Type (u + 1)} [Form G] (g : G) : G :=
  rootedAdjoint 0 g

@[inherit_doc adjoint]
notation g"°" => adjoint g

recommended_spelling "adjoint" for "°" in [adjoint, «term_°»]

open Classical in
/--
The defining equation of `adjoint`, for when things like `unfold adjoint` (now
just `rootedAdjoint 0`) won't expose the cases.
-/
theorem adjoint_def {G : Type (u + 1)} [Form G] (g : G) :
    g° = if IsEnd .left g ∧ IsEnd .right g then !{{0} | {0}}
      else if IsEnd .left g then !{Set.range fun gr : moves .right g => (gr : G)° | {0}}
      else if IsEnd .right g then !{{0} | Set.range fun gl : moves .left g => (gl : G)°}
      else !{ Set.range fun gr : moves .right g => (gr : G)°
            | Set.range fun gl : moves .left g => (gl : G)° } := by
  rw [adjoint, rootedAdjoint]
  rfl

namespace Adjoint

variable {G : Type (u + 1)} [Form G]

theorem rootedAdjoint_zero (r : G) : rootedAdjoint r (0 : G) = !{{r} | {r}} := by
  unfold rootedAdjoint
  simp only [isEnd_zero, and_self, ↓reduceIte]

@[simp]
theorem adjoint_zero_eq_star : ((0 : G)°) = !{{0} | {0}} :=
  rootedAdjoint_zero 0

theorem rootedAdjoint_not_isEnd (r g : G) (p : Player) : ¬(IsEnd p (rootedAdjoint r g)) := by
  unfold rootedAdjoint
  simp only [isEnd_def]
  by_cases h1 : moves .left g = ∅ ∧ moves .right g = ∅ <;>
    simp only [h1, and_self, ↓reduceIte, moves_ofSets, Player.cases]
  all_goals by_cases h2 : moves .left g = ∅ <;> cases p
  all_goals by_cases h3 : moves .right g = ∅ <;>
    simp only [h2, h3, ↓reduceIte, moves_ofSets, Set.singleton_ne_empty,
      not_false_eq_true, Set.range_eq_empty_iff, Set.isEmpty_coe_sort, not_true_eq_false]
  rw [not_and] at h1
  exact h1 h2 h3

theorem adjoint_not_isEnd (g : G) (p : Player) : ¬(IsEnd p (g°)) :=
  rootedAdjoint_not_isEnd 0 g p

theorem rootedAdjoint_not_isEndLike (r g : G) (p : Player) :
    ¬(IsEndLike p (rootedAdjoint r g)) := by
  unfold rootedAdjoint
  simp only [isEnd_def]
  by_cases h1 : moves .left g = ∅ ∧ moves .right g = ∅ <;>
    simp only [h1, and_self, ↓reduceIte, ofSets_isEndLike_iff, isEnd_def, moves_ofSets,
      Player.cases]
  all_goals by_cases h2 : moves .left g = ∅ <;> cases p
  all_goals by_cases h3 : moves .right g = ∅ <;>
    simp only [h2, h3, ↓reduceIte, ofSets_isEndLike_iff, isEnd_def, moves_ofSets,
      Set.singleton_ne_empty, not_false_eq_true, Set.range_eq_empty_iff,
      Set.isEmpty_coe_sort, not_true_eq_false]
  rw [not_and] at h1
  exact h1 h2 h3

theorem adjoint_not_isEndLike (g : G) (p : Player) : ¬(IsEndLike p (g°)) :=
  rootedAdjoint_not_isEndLike 0 g p

private theorem mem_leftMoves_mem_rootedAdjoint_rightMoves {r g gl : G} (h1 : gl ∈ moves .left g) :
    rootedAdjoint r gl ∈ moves .right (rootedAdjoint r g) := by
  rw [rootedAdjoint, isEnd_def, isEnd_def]
  have h2 : g ≠ 0 := mem_moves_ne_zero h1
  by_cases h3 : moves .left g = ∅ <;> by_cases h4 : moves .right g = ∅
  · simp only [and_self, ↓reduceIte, rightMoves_ofSets, Set.mem_singleton_iff, h3, h4]
    simp only [h3, Set.mem_empty_iff_false] at h1
  · simp only [and_false, ↓reduceIte, rightMoves_ofSets, Set.mem_singleton_iff, h3, h4]
    simp only [h3, Set.mem_empty_iff_false] at h1
  · simp only [and_true, ↓reduceIte, rightMoves_ofSets, Set.mem_range, Subtype.exists,
      exists_prop, h3, h4]
    use gl
  · simp only [and_self, ↓reduceIte, rightMoves_ofSets, Set.mem_range, Subtype.exists,
      exists_prop, h3, h4]
    use gl

private theorem mem_rightMoves_mem_rootedAdjoint_leftMoves {r g gr : G} (h1 : gr ∈ moves .right g) :
    rootedAdjoint r gr ∈ moves .left (rootedAdjoint r g) := by
  rw [rootedAdjoint, isEnd_def, isEnd_def]
  have h2 : g ≠ 0 := mem_moves_ne_zero h1
  by_cases h3 : moves .left g = ∅ <;> by_cases h4 : moves .right g = ∅
  · simp only [and_self, ↓reduceIte, leftMoves_ofSets, Set.mem_singleton_iff, h3, h4]
    simp only [h4, Set.mem_empty_iff_false] at h1
  · simp only [and_false, ↓reduceIte, leftMoves_ofSets, Set.mem_range, Subtype.exists,
      exists_prop, h3, h4]
    use gr
  · simp only [and_true, ↓reduceIte, leftMoves_ofSets, Set.mem_singleton_iff, h3, h4]
    simp only [h4, Set.mem_empty_iff_false] at h1
  · simp only [and_self, ↓reduceIte, leftMoves_ofSets, Set.mem_range, Subtype.exists,
      exists_prop, h3, h4]
    use gr

theorem mem_rootedAdjoint_mem_opposite {r g gp : G} {p : Player}
    (h1 : gp ∈ moves p g) : rootedAdjoint r gp ∈ moves (-p) (rootedAdjoint r g) := by
  cases p
  · exact mem_leftMoves_mem_rootedAdjoint_rightMoves h1
  · exact mem_rightMoves_mem_rootedAdjoint_leftMoves h1

theorem mem_adjoint_mem_opposite {g gp : G} {p : Player}
    (h1 : gp ∈ moves p g) : gp° ∈ moves (-p) (g°) :=
  mem_rootedAdjoint_mem_opposite h1

theorem mem_rootedAdjoint_exists_opposite {r g gp : G} {p : Player}
    (h1 : gp ∈ moves p (rootedAdjoint r g)) (h2 : ¬(IsEnd (-p) g)) :
    ∃ gnp ∈ moves (-p) g, gp = rootedAdjoint r gnp := by
  unfold rootedAdjoint at h1
  have h3 : g ≠ 0 := not_isEnd_ne_zero h2
  by_cases h4 : IsEnd p g <;> cases p
  any_goals rw [Player.neg_left] at h2
  any_goals rw [Player.neg_right] at h2
  all_goals
  · simp only [h4, h2, and_false, false_and, ↓reduceIte, moves_ofSets, Player.cases,
               Set.mem_range, Subtype.exists, exists_prop] at h1
    obtain ⟨gnp, h5, h6⟩ := h1
    use gnp
    exact And.symm ⟨Eq.symm h6, h5⟩

theorem mem_adjoint_exists_opposite {g gp : G} {p : Player} (h1 : gp ∈ moves p (g°))
    (h2 : ¬(IsEnd (-p) g)) : ∃ gnp ∈ moves (-p) g, gp = gnp° :=
  mem_rootedAdjoint_exists_opposite h1 h2

theorem mem_rootedAdjoint_end_opposite {r g gp : G} {p : Player}
    (h1 : gp ∈ moves p (rootedAdjoint r g)) (h2 : IsEnd (-p) g) : gp = r := by
  unfold rootedAdjoint at h1
  by_cases h3 : IsEnd p g
  · cases p
    all_goals
    · simp only [Player.neg_left, Player.neg_right] at h2
      simp only [h2, h3, and_self, ↓reduceIte, moves_ofSets, Player.cases,
        Set.mem_singleton_iff] at h1
      exact h1
  · have h4 : g ≠ 0 := not_isEnd_ne_zero h3
    cases p
    all_goals
    · simp only [Player.neg_left, Player.neg_right] at h2
      simp only [h2, h3, and_true, and_false, ↓reduceIte, moves_ofSets, Player.cases,
        Set.mem_singleton_iff] at h1
      exact h1

theorem mem_adjoint_end_opposite {g gp : G} {p : Player}
    (h1 : gp ∈ moves p (g°)) (h2 : IsEnd (-p) g) : gp = 0 :=
  mem_rootedAdjoint_end_opposite h1 h2

/--
The rooted adjoint of a short game is short, provided the root is short.
-/
theorem short_rootedAdjoint {r : G} (h_root_short : IsShort r) {g : G} (h1 : IsShort g) :
    IsShort (rootedAdjoint r g) := by
  unfold rootedAdjoint
  by_cases hleft : IsEnd .left g
  · by_cases hright : IsEnd .right g
    · simp only [hleft, hright, and_self, ↓reduceIte]
      apply Short.ofSets
      · exact Set.finite_singleton r
      · intro y hy
        simp only [Set.mem_singleton_iff] at hy
        subst y
        exact h_root_short
      · exact Set.finite_singleton r
      · intro y hy
        simp only [Set.mem_singleton_iff] at hy
        subst y
        exact h_root_short
    · simp only [hleft, hright, and_false, ↓reduceIte]
      apply Short.ofSets
      · have : Finite (moves .right g) := Short.finite_moves .right h1
        exact Set.finite_range (fun gr : moves .right g => rootedAdjoint r (gr : G))
      · intro gr hgr
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgr
        obtain ⟨gr', hgr', rfl⟩ := hgr
        exact short_rootedAdjoint h_root_short (Short.of_mem_moves h1 hgr')
      · exact Set.finite_singleton r
      · intro gr hgr
        simp only [Set.mem_singleton_iff] at hgr
        subst gr
        exact h_root_short
  · by_cases hright : IsEnd .right g
    · simp only [hleft, hright, and_true, ↓reduceIte]
      apply Short.ofSets
      · exact Set.finite_singleton r
      · intro gl hgl
        simp only [Set.mem_singleton_iff] at hgl
        subst gl
        exact h_root_short
      · have : Finite (moves .left g) := Short.finite_moves .left h1
        exact Set.finite_range (fun gl : moves .left g => rootedAdjoint r (gl : G))
      · intro gl hgl
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgl
        obtain ⟨gl', hgl', rfl⟩ := hgl
        exact short_rootedAdjoint h_root_short (Short.of_mem_moves h1 hgl')
    · simp only [hleft, hright, and_self, ↓reduceIte]
      apply Short.ofSets
      · have : Finite (moves .right g) := Short.finite_moves .right h1
        exact Set.finite_range (fun gr : moves .right g => rootedAdjoint r (gr : G))
      · intro gr hgr
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgr
        obtain ⟨gr', hgr', rfl⟩ := hgr
        exact short_rootedAdjoint h_root_short (Short.of_mem_moves h1 hgr')
      · have : Finite (moves .left g) := Short.finite_moves .left h1
        exact Set.finite_range (fun gl : moves .left g => rootedAdjoint r (gl : G))
      · intro gl hgl
        simp only [Set.mem_range, Subtype.exists, exists_prop] at hgl
        obtain ⟨gl', hgl', rfl⟩ := hgl
        exact short_rootedAdjoint h_root_short (Short.of_mem_moves h1 hgl')
termination_by g
decreasing_by all_goals form_wf

/--
The adjoint of a short game is also short.
-/
theorem short_adjoint {g : G} (h1 : IsShort g) : IsShort (g°) :=
  short_rootedAdjoint Short.zero h1

open Classical in
theorem rootedAdjoint_moves (r : G) (p : Player) (g : G) :
    moves p (rootedAdjoint r g) =
      if IsEnd (-p) g then {r} else (rootedAdjoint r ·) '' moves (-p) g := by
  rw [rootedAdjoint]
  by_cases hl : IsEnd .left g <;> by_cases hr : IsEnd .right g <;> cases p <;>
    simp only [hl, hr, and_true, and_false, and_self, if_true, if_false,
      Player.neg_left, Player.neg_right, leftMoves_ofSets, rightMoves_ofSets,
      Set.image_eq_range]

open Classical in
protected theorem moves (p : Player) (g : G) :
    moves p (g°) = if IsEnd (-p) g then {(0 : G)} else ( · °) '' moves (-p) g :=
  rootedAdjoint_moves 0 p g

/--
The rooted adjoint of the conjugate is the conjugate of the rooted adjoint,
with the root conjugated.
-/
theorem rootedAdjoint_neg (r g : G) : rootedAdjoint (-r) (-g) = -(rootedAdjoint r g) := by
  have key : ∀ p : Player,
      Set.range (fun x : moves p (-g) => rootedAdjoint (-r) (x : G))
        = -Set.range (fun x : moves (-p) g => rootedAdjoint r (x : G)) := by
    intro p
    ext y
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_neg]
    rw [exists_moves_neg]
    refine exists_congr fun x => and_congr_right fun hx => ?_
    rw [rootedAdjoint_neg r x]
    exact neg_eq_iff_eq_neg
  unfold rootedAdjoint
  by_cases hl : IsEnd .left g <;> by_cases hr : IsEnd .right g <;>
    simp only [IsEnd.neg_iff_neg, Player.neg_left, Player.neg_right, hl, hr, and_self,
      and_true, and_false, ↓reduceIte, neg_ofSets, Set.neg_singleton, key]
termination_by g
decreasing_by all_goals form_wf

/--
The adjoint of the conjugate is the conjugate of the adjoint.
-/
theorem adjoint_neg (g : G) : (-g)° = -(g°) := by
  have h := rootedAdjoint_neg (0 : G) g
  rwa [neg_zero] at h

end Adjoint

end Form

end

end MisereGames
