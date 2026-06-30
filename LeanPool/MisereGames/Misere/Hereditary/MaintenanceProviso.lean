/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Form.Misere.Outcome
public import LeanPool.MisereGames.GameForm

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

public section

namespace Form

open Form.Misere.Outcome

variable {G : Type (u + 1)} [Form G]

/-- The maintenance condition for comparison modulo `A`. -/
@[expose]
def Maintenance (A : G → Prop) (g h : G) (p : Player) : Prop :=
  match p with
  | .right => ∀ gr ∈ moves .right g,
      (∃ hr ∈ moves .right h, gr ≥m A hr) ∨
      (∃ grl ∈ moves .left gr, grl ≥m A h)
  | .left => ∀ hl ∈ moves .left h,
      (∃ gl ∈ moves .left g, gl ≥m A hl) ∨
      (∃ hlr ∈ moves .right hl, g ≥m A hlr)

private theorem Maintenance.neg_aux
    {A : G → Prop} [ClosedUnderNeg A] {g h : G} {p : Player}
    (h_maintenance : Maintenance A (-h) (-g) (-p)) :
    Maintenance A g h p := by
  cases p
  · intro hl hhl
    rcases h_maintenance (-hl) (by simp [moves_neg, hhl]) with hopt | hreply
    · rcases hopt with ⟨ngl, hngl, hge⟩
      left
      refine ⟨-ngl, ?_, ?_⟩
      · simpa [moves_neg] using hngl
      · exact (ClosedUnderNeg.neg_ge_neg_iff (-ngl) hl).mp (by simpa using hge)
    · rcases hreply with ⟨nhlr, hnhlr, hge⟩
      right
      refine ⟨-nhlr, ?_, ?_⟩
      · simpa [moves_neg] using hnhlr
      · exact (ClosedUnderNeg.neg_ge_neg_iff g (-nhlr)).mp (by simpa using hge)
  · intro gr hgr
    rcases h_maintenance (-gr) (by simp [moves_neg, hgr]) with hopt | hreply
    · rcases hopt with ⟨nhr, hnhr, hge⟩
      left
      refine ⟨-nhr, ?_, ?_⟩
      · simpa [moves_neg] using hnhr
      · exact (ClosedUnderNeg.neg_ge_neg_iff gr (-nhr)).mp (by simpa using hge)
    · rcases hreply with ⟨ngrl, hngrl, hge⟩
      right
      refine ⟨-ngrl, ?_, ?_⟩
      · simpa [moves_neg] using hngrl
      · exact (ClosedUnderNeg.neg_ge_neg_iff (-ngrl) h).mp (by simpa using hge)

protected theorem Maintenance.neg_iff
    {A : G → Prop} [ClosedUnderNeg A] {g h : G} (p : Player) :
    Maintenance A (-h) (-g) (-p) ↔ Maintenance A g h p := by
  constructor
  · exact Maintenance.neg_aux
  · intro hm
    have hm_neg : Maintenance A (- -g) (- -h) (- -p) := by simpa only [neg_neg] using hm
    simpa using Maintenance.neg_aux (g := -h) (h := -g) (p := -p) hm_neg

/-- The strong outcome condition for a form against ends in `A`. -/
@[expose]
def Strong (A : G → Prop) (g : G) (p : Player) : Prop :=
  ∀ x, A x → IsEndLike p x → WinsGoingFirst p (g + x)

theorem strong_of_isEnd {A : GameForm → Prop} {p : Player} {g : GameForm}
    (he : IsEnd p g) : Strong A g p :=
  fun _x _ hx => winsGoingFirst_add_of_isEnd he (GameForm.isEndLike_iff_isEnd.mp hx)

private theorem strong_neg_imp {A : GameForm → Prop} [ClosedUnderNeg A] {p : Player} {g : GameForm}
    (h_strong : Strong A (-g) p) :
    Strong A g (-p) := by
  intro x hx h_endLike
  simp only [← winsGoingFirst_neg_iff, neg_add_rev]
  have := h_strong (-x) (ClosedUnderNeg.neg_of hx) ((isEndLike_neg_iff_neg' p x).mpr h_endLike)
  rwa [add_comm]

protected theorem Strong.neg_iff {A : GameForm → Prop} [ClosedUnderNeg A] {p : Player} {g :
    GameForm} :
    Strong A (-g) p ↔ Strong A g (-p) := by
  constructor
  · exact strong_neg_imp
  · intro h_strong
    rw [<-neg_neg g] at h_strong
    have := strong_neg_imp h_strong
    rwa [neg_neg p] at this

/--
This is the test given by [Davies, Milley (Theorem 3.1 on p.
7)][davies:OrderInversesMonoid:2026].
-/
def IsStrongTest (p : Player) (g : GameForm) : Prop :=
  IsEnd p g ∨ ∃ gl, ∃ (_ : gl ∈ moves p g), MisereOutcome gl = Outcome.ofPlayer p ∧
    IsStrongTest p gl ∧ ∀ glr ∈ moves (-p) gl, IsStrongTest p glr
termination_by g
decreasing_by form_wf

theorem isStrongTest_def (p : Player) (g : GameForm) :
    IsStrongTest p g ↔
      IsEnd p g ∨ ∃ gl, ∃ (_ : gl ∈ moves p g), MisereOutcome gl = Outcome.ofPlayer p ∧
        IsStrongTest p gl ∧ ∀ glr ∈ moves (-p) gl, IsStrongTest p glr := by
  nth_rw 1 [IsStrongTest]

private theorem isStrongTest_neg_imp {p : Player} {g : GameForm} (h : IsStrongTest p (-g)) :
    IsStrongTest (-p) g := by
  rw [isStrongTest_def] at h
  rw [isStrongTest_def]
  rcases h with hend | ⟨gl', hgl', houtcome, htestgl, hglr⟩
  · exact Or.inl (IsEnd.neg_iff_neg.mp hend)
  · have hmem : -gl' ∈ moves (-p) g := by
      have t := hgl'; rw [moves_neg] at t; exact Set.mem_neg.mp t
    refine Or.inr ⟨-gl', hmem, ?_, ?_, ?_⟩
    · rw [← misereOutcome_conjugate_neg, houtcome]; cases p <;> rfl
    · exact isStrongTest_neg_imp (by rw [neg_neg]; exact htestgl)
    · intro glr hglr2
      rw [neg_neg] at hglr2
      have hmem2 : -glr ∈ moves (-p) gl' := by
        have t := hglr2; rw [moves_neg] at t; exact Set.mem_neg.mp t
      exact isStrongTest_neg_imp (hglr (-glr) hmem2)
termination_by g
decreasing_by form_wf

protected theorem IsStrongTest.neg_iff {p : Player} {g : GameForm} :
    IsStrongTest p (-g) ↔ IsStrongTest (-p) g := by
  constructor
  · exact isStrongTest_neg_imp
  · intro h1
    have h2 : IsStrongTest (-p) (-(-g)) := by rwa [neg_neg]
    have h3 := isStrongTest_neg_imp (p := -p) h2
    rwa [neg_neg] at h3

/-- The proviso condition for comparison modulo `A`. -/
@[expose]
def Proviso (A : G → Prop) (g h : G) (p : Player) : Prop :=
  IsEndLike p g → Strong A h p

private theorem Proviso.neg_aux
    {A : G → Prop} [ClosedUnderNeg A] {g h : G} {p : Player}
    (h_proviso : Proviso A (-g) (-h) (-p)) :
    Proviso A g h p := by
  intro hg_end x hx hx_end
  have hwin_neg : WinsGoingFirst (-p) ((-h) + (-x)) :=
    h_proviso (by simpa [IsEndLike.neg_iff_neg] using hg_end)
      (-x) (ClosedUnderNeg.neg_of hx)
      (by simpa [IsEndLike.neg_iff_neg] using hx_end)
  rw [← winsGoingFirst_neg_iff, neg_add_rev, neg_neg, neg_neg, add_comm] at hwin_neg
  exact hwin_neg

protected theorem Proviso.neg_iff
    {A : G → Prop} [ClosedUnderNeg A] {g h : G} (p : Player) :
    Proviso A (-g) (-h) (-p) ↔ Proviso A g h p := by
  constructor
  · exact Proviso.neg_aux
  · intro hp
    have hp_neg : Proviso A (- -g) (- -h) (- -p) := by simpa only [neg_neg] using hp
    simpa using Proviso.neg_aux (g := -g) (h := -h) (p := -p) hp_neg

private theorem auxCases {h x : G} {p : Player} (h1 : MiserePlayerOutcome (h + x) p = p)
    : (∃ xl ∈ moves p x, MiserePlayerOutcome (h + xl) (-p) = p)
    ∨ (∃ hl ∈ moves p h, MiserePlayerOutcome (hl + x) (-p) = p)
    ∨ (IsEndLike p (h + x)) := by
  apply Or.elim ((winsGoingFirst_iff _ _).mp (miserePlayerOutcome_eq_iff_winsGoingFirst.mp h1))
  · intro h1
    exact (Or.inr (Or.inr h1))
  · intro ⟨hxl, h1, h2⟩
    simp only [moves_add, Set.mem_union, Set.mem_image] at h1 h2
    apply Or.elim h1
    · intro ⟨hl, h3, h4⟩
      refine Or.inr (Or.inl ?_)
      use hl
      apply And.intro h3
      rw [h4]
      simp [MiserePlayerOutcome, h2]
    · intro ⟨xl, h3, h4⟩
      apply Or.inl
      use xl
      apply And.intro h3
      rw [h4]
      simp [MiserePlayerOutcome, h2]

mutual

-- TODO: Combine proofs

private theorem auxR (A : G → Prop) [Hereditary A]
    {g h x : G}
    (hx : A x)
    (h2 : Maintenance A g h .right) (h3 : Maintenance A g h .left)
    (h4 : Proviso A g h .right) (h5 : Proviso A h g .left)
    (h6 : MiserePlayerOutcome (g + x) .right = .right)
    : MiserePlayerOutcome (h + x) .right = .right := by
  -- We must be in one of three cases:
  apply Or.elim3 (auxCases h6)
  · -- 1. o^L(G + X^R) = R for some X^R.
    intro ⟨xr, h7, h8⟩
    rw [Player.neg_right] at h8
    -- By induction on X^R, since A is hereditary, we have o^L(H + X^R) = R.
    have h9 : MiserePlayerOutcome (g + xr) .left ≥ MiserePlayerOutcome (h + xr) .left := by
      exact misereOutcome_ge_iff_miserePlayerOutcome_ge.mp
        (aux A h2 h3 h4 h5
          (Hereditary.has_option hx (IsOption.of_mem_moves h7))) .left
    have h10 : MiserePlayerOutcome (h + xr) .left = .right := by
      have h11 : MiserePlayerOutcome (h + xr) .left ≤ .right := by
        simpa [h8] using h9
      exact Player.le_right_eq _ h11
    -- and hence oR(H + X) = R.
    exact miserePlayerOutcome_of_rightMoves (add_left_mem_moves_add h7 h) h10
  · -- 2. o^L(G^R + X) = R for some G^R.
    intro ⟨gr, h7, h8⟩
    rw [Player.neg_right] at h8
    -- By hypothesis,
    apply Or.elim (h2 gr h7)
    · -- either there exists some H^R with G^R ≥A H^R,
      intro ⟨hr, h9, h10⟩
      -- In the first case, we have immediately that o^L(G^R + X) ≥ o^L(H^R + X),
      have h11 : MiserePlayerOutcome (gr + x) .left ≥ MiserePlayerOutcome (hr + x) .left := by
        exact misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (h10 x hx) .left
      -- and hence o^R(H + X) = R.
      have h12 : MiserePlayerOutcome (hr + x) .left = .right := by
        have h13 : MiserePlayerOutcome (hr + x) .left ≤ .right := by
          simpa [h8] using h11
        exact Player.le_right_eq _ h13
      exact miserePlayerOutcome_of_rightMoves (add_right_mem_moves_add h9 x) h12
    · -- or else there exists some G^RL with G^RL ≥A H
      intro ⟨grl, h9, h10⟩
      -- In the latter, we observe that o^R(G^RL + X) = R (since o^L(G^R + X) = R),
      have h11 : MiserePlayerOutcome (grl + x) .right = .right := by
        simp only [MiserePlayerOutcome, Player.neg_left, ite_eq_right_iff, reduceCtorEq,
          imp_false] at h8
        rw [not_winsGoingFirst_iff] at h8
        have h8 := h8.right (grl + x) (add_right_mem_moves_add h9 x)
        rw [Player.neg_left, <-miserePlayerOutcome_eq_iff_winsGoingFirst] at h8
        exact h8
      -- and so o^R(H + X) ≤ o(G^RL + X) = R.
      have h12 := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (h10 x hx) .right
      rw [h11] at h12
      exact Player.le_right_eq _ h12
  · -- 3. G + X is Right end-like.
    intro h7
    -- Since X ∈ A, it must follow that X is a Right end and G is Right end-like.
    rw [IsEndLike.add_iff] at h7
    have ⟨h8, h9⟩ := h7
    -- By hypothesis, H is Right A-strong, and hence o^R(H + X) = R.
    have h11 := h4 h8 x hx h9
    rwa [miserePlayerOutcome_eq_iff_winsGoingFirst]
termination_by (x, (0 : Nat))
decreasing_by
  all_goals
    first
    | form_wf

private theorem auxL (A : G → Prop) [Hereditary A]
    {g h x : G}
    (hx : A x)
    (h2 : Maintenance A g h .right) (h3 : Maintenance A g h .left)
    (h4 : Proviso A g h .right) (h5 : Proviso A h g .left)
    (h6 : MiserePlayerOutcome (h + x) .left = .left)
    : MiserePlayerOutcome (g + x) .left = .left := by
  -- We must be in one of three cases:
  apply Or.elim3 (auxCases h6)
  · -- 1. o^R(H + X^L) = L for some X^L.
    intro ⟨xl, h7, h8⟩
    rw [Player.neg_left] at h8
    -- By induction on X^L, since A is hereditary, we have o^R(G + X^L) = L.
    have h9 : MiserePlayerOutcome (g + xl) .right ≥ MiserePlayerOutcome (h + xl) .right := by
      exact misereOutcome_ge_iff_miserePlayerOutcome_ge.mp
        (aux A h2 h3 h4 h5
          (Hereditary.has_option hx (IsOption.of_mem_moves h7))) .right
    have h10 : MiserePlayerOutcome (g + xl) .right = .left := by
      have h11 : .left ≤ MiserePlayerOutcome (g + xl) .right := by
        simpa [h8] using h9
      exact Player.le_left_eq _ h11
    -- and hence oL(G + X) = L.
    exact miserePlayerOutcome_of_leftMoves (add_left_mem_moves_add h7 g) h10
  · -- 2. o^R(H^L + X) = L for some H^L.
    intro ⟨hl, h7, h8⟩
    rw [Player.neg_left] at h8
    -- By hypothesis,
    apply Or.elim (h3 hl h7)
    · -- either there exists some G^L with G^L ≥A HL,
      intro ⟨gl, h9, h10⟩
      -- In the first case, we have immediately that o^R(G^L + X) ≥ o^R(H^L + X),
      have h11 : MiserePlayerOutcome (gl + x) .right ≥ MiserePlayerOutcome (hl + x) .right := by
        exact misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (h10 x hx) .right
      -- and hence o^L(G + X) = L.
      refine miserePlayerOutcome_of_leftMoves (add_right_mem_moves_add h9 x) ?_
      simp [h8] at h11
      simp [h11]
    · -- or else there exists some H^LR with G ≥A H^LR
      intro ⟨hlr, h9, h10⟩
      -- In the latter, we observe that o^L(H^LR + X) = L (since o^R(H^L + X) = L ),
      have h11 : MiserePlayerOutcome (hlr + x) .left = .left := by
        simp only [MiserePlayerOutcome, Player.neg_right, ite_eq_right_iff, reduceCtorEq,
          imp_false] at h8
        rw [not_winsGoingFirst_iff] at h8
        have h8 := h8.right (hlr + x) (add_right_mem_moves_add h9 x)
        rw [Player.neg_right, <-miserePlayerOutcome_eq_iff_winsGoingFirst] at h8
        exact h8
      -- and so o^L(G + X) ≥ o(H^LR + X) = L.
      have h12 := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (h10 x hx) .left
      rw [h11] at h12
      exact Player.le_left_eq _ h12
  · -- 3. H + X is Left end-like.
    intro h7
    -- Since X ∈ A, it must follow that X is a Left end and H is Left end-like.
    rw [IsEndLike.add_iff] at h7
    have ⟨h8, h9⟩ := h7
    -- By hypothesis, G is Left A-strong, and hence o^L(G + X) = L.
    have h11 := h5 h8 x hx h9
    rwa [miserePlayerOutcome_eq_iff_winsGoingFirst]
termination_by (x, (0 : Nat))
decreasing_by
  all_goals
    first
    | form_wf

private theorem aux (A : G → Prop) [Hereditary A]
    {g h x : G}
    (h2 : Maintenance A g h .right) (h3 : Maintenance A g h .left)
    (h4 : Proviso A g h .right) (h5 : Proviso A h g .left)
    (hx : A x)
    : MisereOutcome (g + x) ≥ MisereOutcome (h + x) := by
  rw [misereOutcome_ge_iff_miserePlayerOutcome_ge]
  intro p; cases p
  · cases h6 : MiserePlayerOutcome (h + x) Player.left
    · simp [auxL A hx h2 h3 h4 h5 h6]
    · simp
  · cases h6 : MiserePlayerOutcome (g + x) Player.right
    · simp
    · simp [auxR A hx h2 h3 h4 h5 h6]
termination_by (x, (1 : Nat))
decreasing_by
  all_goals
    first
    | form_wf

end

theorem _root_.MisereGames.Form.proviso_right_of_misereGE {A : G → Prop}
    {g h : G} (hge : g ≥m A h) :
    Proviso A g h .right := by
  intro hg_end x hx hx_end
  have hgt : MiserePlayerOutcome (g + x) .right = .right :=
    miserePlayerOutcome_eq_iff_winsGoingFirst.mpr
      (winsGoingFirst_of_isEndLike (IsEndLike.add_iff.mpr ⟨hg_end, hx_end⟩))
  have h_cmp := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (hge x hx) .right
  rw [hgt] at h_cmp
  exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp (Player.le_right_eq _ h_cmp)

theorem _root_.MisereGames.Form.proviso_left_of_misereGE {A : G → Prop}
    {g h : G} (hge : g ≥m A h) :
    Proviso A h g .left := by
  intro hh_end x hx hx_end
  have hht : MiserePlayerOutcome (h + x) .left = .left :=
    miserePlayerOutcome_eq_iff_winsGoingFirst.mpr
      (winsGoingFirst_of_isEndLike (IsEndLike.add_iff.mpr ⟨hh_end, hx_end⟩))
  have h_cmp := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (hge x hx) .left
  rw [hht] at h_cmp
  exact miserePlayerOutcome_eq_iff_winsGoingFirst.mp (Player.le_left_eq _ h_cmp)

namespace Hereditary

theorem _root_.MisereGames.Form.Hereditary.misereGE_of_maintenance_proviso
    (A : G → Prop) [Hereditary A]
    {g h : G}
    (h2 : Maintenance A g h .right) (h3 : Maintenance A g h .left)
    (h4 : Proviso A g h .right) (h5 : Proviso A h g .left)
    : g ≥m A h := by
  intro x hx
  exact aux A h2 h3 h4 h5 hx

theorem _root_.MisereGames.Form.Hereditary.misereGE_of_moves
    {A : GameForm → Prop} [Hereditary A] {g h : GameForm}
    (hl1 : ∀ gl ∈ moves .left g, ∃ hl, hl ∈ moves .left h)
    (hl2 : ∀ hl ∈ moves .left h, ∃ gl ∈ moves .left g, gl ≥m A hl)
    (hr1 : ∀ gr ∈ moves .right g, ∃ hr ∈ moves .right h, gr ≥m A hr)
    (hr2 : ∀ hr ∈ moves .right h, ∃ gr, gr ∈ moves .right g)
    : g ≥m A h := by
  refine misereGE_of_maintenance_proviso A ?_ ?_ ?_ ?_
  · intro gr h1
    apply Or.inl
    have ⟨hr, h3, h4⟩ := hr1 gr h1
    use hr, h3
  · intro hl h1
    apply Or.inl
    have ⟨hr, h3, h4⟩ := hl2 hl h1
    use hr, h3
  · intro h2 y hy h1
    rw [GameForm.isEndLike_iff_isEnd] at h2 h1
    refine winsGoingFirst_add_of_isEnd (isEnd_of_not_mem ?_) h1
    simpa only [h2, not_mem_moves_of_isEnd, exists_const, imp_false] using hr2
  · intro h2 y hy h1
    rw [GameForm.isEndLike_iff_isEnd] at h2 h1
    refine winsGoingFirst_add_of_isEnd (isEnd_of_not_mem ?_) h1
    simpa only [h2, not_mem_moves_of_isEnd, exists_const, imp_false] using hl1

private theorem misereEQ_of_moves.aux {A : GameForm → Prop} [Hereditary A] {g h : GameForm}
    (hl1 : ∀ gl ∈ moves .left g, ∃ hl ∈ moves .left h, gl =m A hl)
    (hl2 : ∀ hl ∈ moves .left h, ∃ gl ∈ moves .left g, hl =m A gl)
    (hr1 : ∀ gr ∈ moves .right g, ∃ hr ∈ moves .right h, gr =m A hr)
    (hr2 : ∀ hr ∈ moves .right h, ∃ gr ∈ moves .right g, hr =m A gr)
    : g ≥m A h := by
  apply misereGE_of_moves
  · intro gl h_gl
    have ⟨hl, h1, _⟩ := hl1 gl h_gl
    use hl, h1
  · intro hl h_hl
    have ⟨gl, h1, h2⟩ := hl2 hl h_hl
    use gl, h1, misereGE_of_misereEQ (MisereEQ.symm h2)
  · intro gr h_gr
    have ⟨hr, h1, h2⟩ := hr1 gr h_gr
    use hr, h1, misereGE_of_misereEQ h2
  · intro hr h_hr
    have ⟨gr, h1, h2⟩ := hr2 hr h_hr
    use gr, h1

theorem _root_.MisereGames.Form.Hereditary.misereEQ_of_moves
    {A : GameForm → Prop} [Hereditary A] {g h : GameForm}
    (hl1 : ∀ gl ∈ moves .left g, ∃ hl ∈ moves .left h, gl =m A hl)
    (hl2 : ∀ hl ∈ moves .left h, ∃ gl ∈ moves .left g, hl =m A gl)
    (hr1 : ∀ gr ∈ moves .right g, ∃ hr ∈ moves .right h, gr =m A hr)
    (hr2 : ∀ hr ∈ moves .right h, ∃ gr ∈ moves .right g, hr =m A gr)
    : g =m A h := by
  apply MisereEq.of_antisymm
  · exact misereEQ_of_moves.aux hl1 hl2 hr1 hr2
  · exact misereEQ_of_moves.aux hl2 hl1 hr2 hr1

end Hereditary

end Form

end

end MisereGames
