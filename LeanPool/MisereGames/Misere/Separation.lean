/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import LeanPool.MisereGames.Form.Misere.Adjoint
public import LeanPool.MisereGames.Misere.Hereditary.MaintenanceProviso

/-!
Misere combinatorial games.
-/

namespace MisereGames

/-!
# Separation and downlinking

This file defines downlinked and separated pairs of forms, and develops the
machinery necessary to prove that $G\ge_\mathcal{U}H$ implies that both
`Form.Maintenance` and `Form.Proviso` are satisfied.

Here, $G$ and $H$ will always refer to arbitrary forms (possibly augmented,
possibly not), $\mathcal{A}$ to an arbitrary set of forms, and $\mathcal{U}$ to
a universe (which may or may not be `Short`).

## References

* [A. N. Siegel, *On the general dead-ending universe of partizan games*
(Section 5 on pp. 207–222)][siegel:GeneralDeadendingUniverse:2025]
-/

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Form.Misere.Adjoint
open Form.Misere.Outcome

public section

namespace Form

/--
We say $G$ is _downlinked_ to $H$ (with respect to $\mathcal{A}$) if there
exists some $T\in\mathcal{A}$ with $\operatorname{o_L}(G+T)=\mathscr{R}$ and
$\operatorname{o_R}(H+T)=\mathscr{L}$.

This generalises the definition given by [Siegel (Definition 5.9 on p.
214)][siegel:GeneralDeadendingUniverse:2025], where all forms were short, and
the sets were short universes.
-/
@[expose] def Downlinked (A : G → Prop) (g h : G) : Prop :=
  ∃ t, A t ∧ ¬WinsGoingFirst .left (g + t) ∧
    ¬WinsGoingFirst .right (h + t)


/--
If there exists some $X\in\mathcal{A}$ whereby
$\operatorname{o_L}(G+X)=\mathscr{R}$ and
$\operatorname{o_L}(H+X)=\mathscr{L}$, then we say that $G$ and $H$ are _Left
separated_ (with respect to $\mathcal{A}$). (See `LeftSeparating` and
`RightSeparating`.)
-/
@[expose] def AreSeparating (A : G → Prop) (p : Player) (g h : G) : Prop :=
  match p with
  | .left => ∃ x, A x ∧ ¬WinsGoingFirst .left (g + x) ∧
      WinsGoingFirst .left (h + x)
  | .right => ∃ x, A x ∧ WinsGoingFirst .right (g + x) ∧
      ¬WinsGoingFirst .right (h + x)

/--
There exists some $X\in\mathcal{A}$ whereby
$\operatorname{o_L}(G+X)=\mathscr{R}$ and
$\operatorname{o_L}(H+X)=\mathscr{L}$. (See `Separating`.)
-/
abbrev AreLeftSeparating (A : G → Prop) (g h : G) : Prop :=
  AreSeparating A .left g h

/--
There exists some $X\in\mathcal{A}$ whereby
$\operatorname{o_R}(G+X)=\mathscr{R}$ and
$\operatorname{o_R}(H+X)=\mathscr{L}$. (See `Separating`.)
-/
abbrev AreRightSeparating (A : G → Prop) (g h : G) : Prop :=
  AreSeparating A .right g h

/--
We have `g ≥ h` modulo `A` exactly when `g` and `h` are neither Left- nor
Right-separating.
-/
theorem misereGE_iff_not_separating {A : G → Prop} {g h : G} :
    g ≥m A h ↔ ¬ AreLeftSeparating A g h ∧ ¬ AreRightSeparating A g h := by
  constructor
  · intro hge
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx, h1, h2⟩
      have hcmp := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (hge x hx) .left
      rw [miserePlayerOutcome_eq_iff_winsGoingFirst.mpr h2] at hcmp
      have hg : MiserePlayerOutcome (g + x) .left = .right := by
        cases hgx : MiserePlayerOutcome (g + x) .left with
        | left => exact absurd (miserePlayerOutcome_eq_iff_winsGoingFirst.mp hgx) h1
        | right => rfl
      rw [hg] at hcmp
      exact Player.left_le_right hcmp
    · rintro ⟨x, hx, h1, h2⟩
      have hcmp := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (hge x hx) .right
      have hh : MiserePlayerOutcome (h + x) .right = .left := by
        cases hhx : MiserePlayerOutcome (h + x) .right with
        | left => rfl
        | right => exact absurd (miserePlayerOutcome_eq_iff_winsGoingFirst.mp hhx) h2
      rw [miserePlayerOutcome_eq_iff_winsGoingFirst.mpr h1, hh] at hcmp
      exact Player.left_le_right hcmp
  · rintro ⟨h1, h2⟩
    by_contra h_not_ge
    rw [MisereGE] at h_not_ge
    simp only [not_forall] at h_not_ge
    obtain ⟨x, hx, h_not_outcome_ge⟩ := h_not_ge
    have h_not_player_ge :
        ¬∀ p, MiserePlayerOutcome (g + x) p ≥ MiserePlayerOutcome (h + x) p := by
      intro h_player_ge
      exact h_not_outcome_ge (misereOutcome_ge_iff_miserePlayerOutcome_ge.mpr h_player_ge)
    simp only [Player.forall, not_and_or] at h_not_player_ge
    cases h_not_player_ge with
    | inl h_left =>
        absurd h1
        cases hg : MiserePlayerOutcome (g + x) .left
        <;> cases hh : MiserePlayerOutcome (h + x) .left
        <;> simp [hg, hh] at h_left
        refine ⟨x, hx, ?_, ?_⟩
        · intro h_win
          have h_out := miserePlayerOutcome_eq_iff_winsGoingFirst.mpr h_win
          rw [hg] at h_out
          cases h_out
        · exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp hh
    | inr h_right =>
        absurd h2
        cases hg : MiserePlayerOutcome (g + x) .right
        <;> cases hh : MiserePlayerOutcome (h + x) .right
        <;> simp [hg, hh] at h_right
        refine ⟨x, hx, ?_, ?_⟩
        · exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp hg
        · intro h_win
          have h_out := miserePlayerOutcome_eq_iff_winsGoingFirst.mpr h_win
          rw [hh] at h_out
          cases h_out

/--
Negation of `misereGE_iff_not_separating`.
-/
theorem not_misereGE_iff_separating {A : G → Prop} {g h : G} :
    ¬(g ≥m A h) ↔ AreLeftSeparating A g h ∨ AreRightSeparating A g h := by
  constructor
  · intro h1
    have := misereGE_iff_not_separating.not.mp h1
    exact or_iff_not_and_not.mpr this
  · rintro (h1 | h2)
    · exact misereGE_iff_not_separating.not.mpr (or_iff_not_and_not.mp (Or.inl h1))
    · exact misereGE_iff_not_separating.not.mpr (or_iff_not_and_not.mp (Or.inr h2))

namespace Separation

/--
Given $H$ and a root $r$, this constructs the set of games
$\{r,\operatorname{adj}_r(H^\mathcal{R})\}$, which will act as Left's set of
options in the construction of `rightSeparatorCandidate`. Taking $r=0$ recovers
the set $\{0,(H^\mathcal{R})^\circ\}$.
-/
abbrev rightSeparatorLeftSet (r h : G) : Set G :=
  {r} ∪ Set.range (fun hr : moves .right h => rootedAdjoint r (hr : G))

/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
Given forms $H$ and $X$ and a root $r$, this constructs the form
$\form<r,\operatorname{adj}_r(H^\mathcal{R})>[X]$, which is used by
`Separating.pair_of_not_misereGE` to show that $G$ and $H$ must be both
`LeftSeparating` and `RightSeparating` whenever $G\ngeq_\mathcal{U}H$.
-/
noncomputable abbrev rightSeparatorCandidate (r h x : G) : G :=
  !{rightSeparatorLeftSet r h | {x}}

/--
Given $G$ and a root $r$, this constructs the set of games
$\{r,\operatorname{adj}_r(G^\mathcal{L})\}$, the Left/Right mirror of
`rightSeparatorLeftSet`, which will act as Right's set of options in the
construction of `leftSeparatorCandidate`.
-/
abbrev leftSeparatorRightSet (r g : G) : Set G :=
  {r} ∪ Set.range (fun gl : moves .left g => rootedAdjoint r (gl : G))

/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
Given forms $G$ and $X$ and a root $r$, this constructs the form
$\form<X>[r,\operatorname{adj}_r(G^\mathcal{L})]$, the Left/Right mirror of
`rightSeparatorCandidate`.
-/
noncomputable abbrev leftSeparatorCandidate (r g x : G) : G :=
  !{{x} | leftSeparatorRightSet r g}

/--
The Left separator is the conjugate of a Right separator, with the root
conjugated.
-/
theorem leftSeparatorCandidate_eq_neg (r g x : G) :
    leftSeparatorCandidate r g x = -rightSeparatorCandidate (-r) (-g) (-x) := by
  have hset : leftSeparatorRightSet r g = -rightSeparatorLeftSet (-r) (-g) := by
    ext y
    simp only [leftSeparatorRightSet, rightSeparatorLeftSet, Set.mem_union,
      Set.mem_singleton_iff, Set.mem_range, Set.mem_neg, Subtype.exists, exists_prop]
    rw [exists_moves_neg]
    refine or_congr ?_ (exists_congr fun a => and_congr_right fun _ => ?_)
    · exact neg_inj.symm
    · rw [Adjoint.rootedAdjoint_neg]
      exact neg_inj.symm
  have hx : ({x} : Set G) = -{-x} := by rw [Set.neg_singleton, neg_neg]
  unfold leftSeparatorCandidate rightSeparatorCandidate
  simp only [neg_ofSets, hx, hset]

/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
If $G$ and $H$ are `LeftSeparating`, and
$\form<r,\operatorname{adj}_r(H^\mathcal{R})>[X]\in\mathcal{A}$ for every
$X\in\mathcal{A}$, then $G$ and $H$ are `RightSeparating`.
-/
lemma rightSeparating_of_leftSeparating_of_rightSeparatorCandidate_mem
    {A IsAmbient : G → Prop} [Hereditary IsAmbient] {r g h : G}
    (h_isRoot : IsRoot IsAmbient r) (hh : IsAmbient h)
    (h_candidate : ∀ {x : G}, A x → A (rightSeparatorCandidate r h x))
    (h_left_sep : AreLeftSeparating A g h) :
    AreRightSeparating A g h := by
  obtain ⟨x, hx, hgx, hhx⟩ := h_left_sep
  let y := rightSeparatorCandidate r h x
  have hy : A y := h_candidate hx
  refine ⟨y, hy, ?_, ?_⟩
  · apply winsGoingFirst_of_moves
    refine ⟨g + x, ?_, ?_⟩
    · apply add_left_mem_moves_add
      change x ∈ moves .right (rightSeparatorCandidate r h x)
      unfold rightSeparatorCandidate
      rw [rightMoves_ofSets (s := rightSeparatorLeftSet r h) (t := {x})]
      simp only [Set.mem_singleton_iff]
    · exact hgx
  · rw [not_winsGoingFirst_iff]
    constructor
    · intro h_end
      have hy_end : IsEndLike .right y := (IsEndLike.add_iff.mp h_end).right
      rw [ofSets_isEndLike_iff, isEnd_def, rightMoves_ofSets] at hy_end
      exact Set.singleton_ne_empty x hy_end
    · intro k hk
      rw [moves_add] at hk
      cases hk with
      | inl h_h_move =>
          obtain ⟨hr, hhr, rfl⟩ := h_h_move
          apply winsGoingFirst_of_moves
          refine ⟨hr + rootedAdjoint r hr, ?_, ?_⟩
          · apply add_left_mem_moves_add
            change rootedAdjoint r hr ∈ moves .left (rightSeparatorCandidate r h x)
            unfold rightSeparatorCandidate
            rw [leftMoves_ofSets (s := rightSeparatorLeftSet r h) (t := {x})]
            simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
            right
            exact ⟨⟨hr, hhr⟩, rfl⟩
          · exact not_winsGoingFirst_of_misereOutcome_P
              (misereOutcome_add_rootedAdjoint_eq_P h_isRoot (Hereditary.of_mem_moves hh hhr))
      | inr h_y_move =>
          obtain ⟨yr, hyr, rfl⟩ := h_y_move
          change yr ∈ moves .right (rightSeparatorCandidate r h x) at hyr
          unfold rightSeparatorCandidate at hyr
          rw [rightMoves_ofSets (s := rightSeparatorLeftSet r h) (t := {x})] at hyr
          simp only [Set.mem_singleton_iff] at hyr
          rw [hyr]
          exact hhx

/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
If $G$ and $H$ are `RightSeparating`, and
$\form<X>[r,\operatorname{adj}_r(G^\mathcal{L})]\in\mathcal{A}$ for every
$X\in\mathcal{A}$, then $G$ and $H$ are `LeftSeparating`. The Left/Right mirror
of `rightSeparating_of_leftSeparating_of_rightSeparatorCandidate_mem`.
-/
lemma leftSeparating_of_rightSeparating_of_leftSeparatorCandidate_mem
    {A IsAmbient : G → Prop} [Hereditary IsAmbient] {r g h : G}
    (h_isRoot : IsRoot IsAmbient r) (hg : IsAmbient g)
    (h_candidate : ∀ {x : G}, A x → A (leftSeparatorCandidate r g x))
    (h_right_sep : AreRightSeparating A g h) :
    AreLeftSeparating A g h := by
  obtain ⟨x, hx, hgx, hhx⟩ := h_right_sep
  let y := leftSeparatorCandidate r g x
  have hy : A y := h_candidate hx
  refine ⟨y, hy, ?_, ?_⟩
  · rw [not_winsGoingFirst_iff]
    constructor
    · intro h_end
      have hy_end : IsEndLike .left y := (IsEndLike.add_iff.mp h_end).right
      rw [ofSets_isEndLike_iff, isEnd_def, leftMoves_ofSets] at hy_end
      exact Set.singleton_ne_empty x hy_end
    · intro k hk
      rw [moves_add] at hk
      cases hk with
      | inl h_g_move =>
          obtain ⟨gl, hgl, rfl⟩ := h_g_move
          apply winsGoingFirst_of_moves
          refine ⟨gl + rootedAdjoint r gl, ?_, ?_⟩
          · apply add_left_mem_moves_add
            change rootedAdjoint r gl ∈ moves .right (leftSeparatorCandidate r g x)
            unfold leftSeparatorCandidate
            rw [rightMoves_ofSets (s := {x}) (t := leftSeparatorRightSet r g)]
            simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
            right
            exact ⟨⟨gl, hgl⟩, rfl⟩
          · exact not_winsGoingFirst_of_misereOutcome_P
              (misereOutcome_add_rootedAdjoint_eq_P h_isRoot (Hereditary.of_mem_moves hg hgl))
      | inr h_y_move =>
          obtain ⟨yl, hyl, rfl⟩ := h_y_move
          change yl ∈ moves .left (leftSeparatorCandidate r g x) at hyl
          unfold leftSeparatorCandidate at hyl
          rw [leftMoves_ofSets (s := {x}) (t := leftSeparatorRightSet r g)] at hyl
          simp only [Set.mem_singleton_iff] at hyl
          rw [hyl]
          exact hgx
  · apply winsGoingFirst_of_moves
    refine ⟨h + x, ?_, ?_⟩
    · apply add_left_mem_moves_add
      change x ∈ moves .left (leftSeparatorCandidate r g x)
      unfold leftSeparatorCandidate
      rw [leftMoves_ofSets (s := {x}) (t := leftSeparatorRightSet r g)]
      simp only [Set.mem_singleton_iff]
    · exact hhx

attribute [local instance] Classical.propDecidable

/-- The optional root contribution to a downlink witness. -/
public abbrev downlinkZero (r : G) (p : Player) (g h : G) : Set G :=
  if IsEnd (-p) g ∧ IsEnd (-p) h then {r} else ∅

/-- The options used in one side of a downlink witness. -/
public abbrev downlinkOptions (r : G) (p : Player) (g h : G) (z : moves (-p) h → G) : Set G :=
  Set.range z ∪ Set.range (fun gp : moves (-p) g => rootedAdjoint r (gp : G)) ∪ downlinkZero r p g h

/-- The Left option set of a downlink witness. -/
abbrev downlinkLeftSet (r g h : G) (y : moves .right h → G) : Set G :=
  downlinkOptions r .left g h y

/-- The Right option set of a downlink witness. -/
abbrev downlinkRightSet (r g h : G) (x : moves .left g → G) : Set G :=
  downlinkOptions r .right h g x

lemma downlinkOptions_nonempty
    (r : G) (p : Player) (g h : G) (z : moves (-p) h → G) :
    (downlinkOptions r p g h z).Nonempty := by
  by_cases hz : IsEnd (-p) g ∧ IsEnd (-p) h
  · exact ⟨r, by simp [downlinkOptions, downlinkZero, hz]⟩
  · rw [not_and_or] at hz
    cases hz with
    | inl hg =>
        obtain ⟨gp, hgp⟩ := not_isEnd_exists_move hg
        exact ⟨rootedAdjoint r gp, by
          simp only [downlinkOptions, Set.mem_union, Set.mem_range]
          exact Or.inl (Or.inr ⟨⟨gp, hgp⟩, rfl⟩)⟩
    | inr hh =>
        obtain ⟨hp, hhp⟩ := not_isEnd_exists_move hh
        exact ⟨z ⟨hp, hhp⟩, by
          simp only [downlinkOptions, Set.mem_union, Set.mem_range]
          exact Or.inl (Or.inl ⟨⟨hp, hhp⟩, rfl⟩)⟩

/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
This constructs the following game form, which is similar to a construction by
[Siegel (Proof of Lemma 5.10 on p. 215)][siegel:GeneralDeadendingUniverse:2025]
for short forms:
$$
T=
\begin{cases}
\form<r>[r]
& \text{if neither }G\text{ nor }H\text{ has any ordinary options},\\
\form<r>[X_i,\operatorname{adj}_r(H^\mathcal{L})]
& \text{if }G,H\text{ are both Right ends but not both Left ends},\\
\form<Y_j,\operatorname{adj}_r(G^\mathcal{R})>[r]
& \text{if }G,H\text{ are both Left ends but not both Right ends},\\
\form<Y_j,\operatorname{adj}_r(G^\mathcal{R})>[X_i,\operatorname{adj}_r(H^\mathcal{L})]
& \text{otherwise}.
\end{cases}
$$
Here $r$ is the root; taking $r=0$ recovers Siegel's construction.

(Note that the $X_i$ and $Y_j$ are chosen as a function of the Left and Right
options of $G$ and $H$ respectively.)
-/
noncomputable abbrev downlinkWitness
    (r g h : G) (x : moves .left g → G) (y : moves .right h → G)
    [Small (downlinkLeftSet r g h y)] [Small (downlinkRightSet r g h x)] : G :=
  !{downlinkLeftSet r g h y | downlinkRightSet r g h x}

lemma downlinked_of_downlinkWitness_mem
    {A IsAmbient : G → Prop} [Hereditary IsAmbient] {r g h : G}
    {x : moves .left g → G} {y : moves .right h → G}
    [Small (downlinkLeftSet r g h y)] [Small (downlinkRightSet r g h x)]
    (h_isRoot : IsRoot IsAmbient r) (hg : IsAmbient g) (hh : IsAmbient h)
    (htA : A (downlinkWitness r g h x y))
    (hxLose : ∀ gl : moves .left g, ¬WinsGoingFirst .left ((gl : G) + x gl))
    (hxWin : ∀ gl : moves .left g, WinsGoingFirst .left (h + x gl))
    (hyWin : ∀ hr : moves .right h, WinsGoingFirst .right (g + y hr))
    (hyLose : ∀ hr : moves .right h, ¬WinsGoingFirst .right ((hr : G) + y hr)) :
    Downlinked A g h := by
  let L := downlinkLeftSet r g h y
  let R := downlinkRightSet r g h x
  let t : G := !{L | R}
  have hLnonempty : L.Nonempty := downlinkOptions_nonempty r .left g h y
  have hRnonempty : R.Nonempty := downlinkOptions_nonempty r .right h g x
  change A t at htA
  refine ⟨t, htA, ?_, ?_⟩
  all_goals
    rw [not_winsGoingFirst_iff]
    refine ⟨?_, ?_⟩
  · intro hEnd
    apply hLnonempty.ne_empty
    simpa [t, L, ofSets_isEndLike_iff, isEnd_def] using
      (IsEndLike.add_iff.mp hEnd).right
  · rw [moves_add]
    rintro k (⟨gl, hgl, rfl⟩ | ⟨tl, htl, rfl⟩)
    · exact winsGoingFirst_of_moves ⟨gl + x ⟨gl, hgl⟩,
        add_left_mem_moves_add (by simp [t, R, downlinkRightSet, downlinkOptions]) gl,
        hxLose ⟨gl, hgl⟩⟩
    · simp only [downlinkLeftSet, downlinkOptions, Player.neg_left, downlinkZero,
        leftMoves_ofSets, Set.mem_union, Set.mem_range, Subtype.exists, exists_prop,
        Set.mem_ite_empty_right, Set.mem_singleton_iff, t, L] at htl
      rcases htl with (⟨hr, hhr, rfl⟩ | ⟨gr, hgr, rfl⟩) | htl_zero
      · exact hyWin ⟨hr, hhr⟩
      · exact winsGoingFirst_of_moves ⟨gr + rootedAdjoint r gr,
          add_right_mem_moves_add hgr (rootedAdjoint r gr),
          not_winsGoingFirst_of_misereOutcome_P
            (misereOutcome_add_rootedAdjoint_eq_P h_isRoot (Hereditary.of_mem_moves hg hgr))⟩
      · by_cases hz : IsEnd .right g ∧ IsEnd .right h
        all_goals simp [hz] at htl_zero
        have hwin : WinsGoingFirst .right (g + r) := h_isRoot hg hz.left
        simpa [htl_zero] using hwin
  · intro hEnd
    apply hRnonempty.ne_empty
    simpa [t, R, ofSets_isEndLike_iff, isEnd_def] using
      (IsEndLike.add_iff.mp hEnd).right
  · rw [moves_add]
    rintro k (⟨hr, hhr, rfl⟩ | ⟨tr, htr, rfl⟩)
    · exact winsGoingFirst_of_moves ⟨hr + y ⟨hr, hhr⟩,
        add_left_mem_moves_add (by simp [t, L, downlinkLeftSet, downlinkOptions]) hr,
        hyLose ⟨hr, hhr⟩⟩
    · simp only [downlinkRightSet, downlinkOptions, Player.neg_right, downlinkZero,
        rightMoves_ofSets, Set.mem_union, Set.mem_range, Subtype.exists, exists_prop,
        Set.mem_ite_empty_right, Set.mem_singleton_iff, t, R] at htr
      rcases htr with (⟨gl, hgl, rfl⟩ | ⟨hl, hhl, rfl⟩) | htr_zero
      · exact hxWin ⟨gl, hgl⟩
      · exact winsGoingFirst_of_moves ⟨hl + rootedAdjoint r hl,
          add_right_mem_moves_add hhl (rootedAdjoint r hl),
          not_winsGoingFirst_of_misereOutcome_P
            (misereOutcome_add_rootedAdjoint_eq_P h_isRoot (Hereditary.of_mem_moves hh hhl))⟩
      · by_cases hz : IsEnd .left h ∧ IsEnd .left g
        all_goals simp [hz] at htr_zero
        have hwin : WinsGoingFirst .left (h + r) := h_isRoot hh hz.left
        simpa [htr_zero] using hwin

/--
If $G$ and $H$ are `RightSeparating`, then $\overline{H}$ and $\overline{G}$
must be `LeftSeparating`.
-/
lemma leftSeparating_neg_of_rightSeparating {A : G → Prop} [ClosedUnderNeg A]
    {g h : G} (h_right_sep : AreRightSeparating A g h) :
    AreLeftSeparating A (-h) (-g) := by
  obtain ⟨y, hy, hgy, hhy⟩ := h_right_sep
  refine ⟨-y, ClosedUnderNeg.neg_of hy, ?_, ?_⟩
  · intro h_win
    have h_win' : WinsGoingFirst .right (h + y) := by
      apply (winsGoingFirst_neg_iff (h + y) .left).mp
      simpa [neg_add_rev, add_comm] using h_win
    exact hhy h_win'
  · have h_win : WinsGoingFirst .left (-(g + y)) :=
      (winsGoingFirst_neg_iff (g + y) .left).mpr hgy
    simpa [neg_add_rev, add_comm] using h_win

/--
If $\overline{H}$ and $\overline{G}$ are `RightSeparating`, then $G$ and $H$
must be `LeftSeparating`.
-/
lemma leftSeparating_of_rightSeparating_neg {A : G → Prop} [ClosedUnderNeg A]
    {g h : G} (h_right_sep : AreRightSeparating A (-h) (-g)) :
    AreLeftSeparating A g h := by
  simpa using (leftSeparating_neg_of_rightSeparating h_right_sep)

end Separation

end Form

end

end MisereGames
