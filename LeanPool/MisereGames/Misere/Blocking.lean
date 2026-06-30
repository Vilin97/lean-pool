/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Misere.DeadEnding

/-!
Misere combinatorial games.
-/

namespace MisereGames

public section

namespace Form

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Form.Misere.Outcome

/--
A *blocked end* for player `p`: `g` is a `p`-end, and for every opponent move
`gr`, either `gr` is again a `p` blocked end, or else `p` has a move from `gr`
to a `p` blocked end. This is weaker than `IsDeadEnd`: every `p` dead end is a
`p` blocked end (`isBlockedEnd_of_isDeadEnd`), but not the other way around.
-/
def IsBlockedEnd (p : Player) (g : G) : Prop :=
  IsEnd p g ∧ (∀ gr ∈ moves (-p) g,
    IsBlockedEnd p gr ∨ (∃ grl, ∃ (_ : grl ∈ moves p gr), IsBlockedEnd p grl))
termination_by g
decreasing_by form_wf

theorem isBlockedEnd_def (p : Player) (g : G) :
    IsBlockedEnd p g ↔ IsEnd p g ∧ (∀ gr ∈ moves (-p) g,
      IsBlockedEnd p gr ∨ (∃ grl, ∃ (_ : grl ∈ moves p gr), IsBlockedEnd p grl)) := by
  nth_rw 1 [IsBlockedEnd]

theorem isEnd_of_isBlockedEnd {g : G} {p : Player} (h1 : IsBlockedEnd p g) : IsEnd p g := by
  unfold IsBlockedEnd at h1
  exact h1.left

theorem IsBlockedEnd.hereditary_def {g : G} {p : Player} (h1 : IsBlockedEnd p g) :
    ∀ gr ∈ moves (-p) g, IsBlockedEnd p gr ∨ (∃ grl, ∃ (_ : grl ∈ moves p gr),
      IsBlockedEnd p grl) := by
  unfold IsBlockedEnd at h1
  exact h1.right

@[simp]
theorem not_mem_moves_of_isBlockedEnd {g gp : G} {p : Player} (h1 : IsBlockedEnd p g) :
    gp ∉ moves p g := by
  simp [isEnd_of_isBlockedEnd h1]

/-- A dead end is a blocked end. -/
theorem isBlockedEnd_of_isDeadEnd {g : G} {p : Player} (h1 : IsDeadEnd p g) : IsBlockedEnd p g := by
  rw [isBlockedEnd_def]
  refine ⟨isEnd_of_isDeadEnd h1, fun gr hgr => Or.inl ?_⟩
  exact isBlockedEnd_of_isDeadEnd (isDeadEnd_of_mem_moves h1 hgr)
termination_by g
decreasing_by exact Moves.Subposition.of_mem_moves (by assumption)

protected theorem IsBlockedEnd.add {g h : G} {p : Player}
    (h1 : IsBlockedEnd p g) (h2 : IsBlockedEnd p h) : IsBlockedEnd p (g + h) := by
  rw [isBlockedEnd_def]
  refine ⟨IsEnd.add_iff.mpr ⟨isEnd_of_isBlockedEnd h1, isEnd_of_isBlockedEnd h2⟩, ?_⟩
  intro gr hgr
  rw [moves_add, Set.mem_union, Set.mem_image, Set.mem_image] at hgr
  rcases hgr with ⟨g', hg', rfl⟩ | ⟨h', hh', rfl⟩
  · rcases (IsBlockedEnd.hereditary_def h1) g' hg' with hbe | ⟨grl, hgrl, hbgrl⟩
    · exact Or.inl (IsBlockedEnd.add hbe h2)
    · exact Or.inr ⟨grl + h, add_right_mem_moves_add hgrl h, IsBlockedEnd.add hbgrl h2⟩
  · rcases (IsBlockedEnd.hereditary_def h2) h' hh' with hbe | ⟨hrl, hhrl, hbhrl⟩
    · exact Or.inl (IsBlockedEnd.add h1 hbe)
    · exact Or.inr ⟨g + hrl, add_left_mem_moves_add hhrl g, IsBlockedEnd.add h1 hbhrl⟩
termination_by (g, h)
decreasing_by form_wf

private protected theorem IsBlockedEnd.neg {g : G} {p : Player} (h1 : IsBlockedEnd p (-g)) :
    IsBlockedEnd (-p) g := by
  rw [isBlockedEnd_def] at h1
  rw [isBlockedEnd_def]
  obtain ⟨h3, h2⟩ := h1
  refine ⟨IsEnd.neg_iff_neg.mp h3, ?_⟩
  rw [neg_neg]
  intro gr hgr
  have hmem : -gr ∈ moves (-p) (-g) := by
    simpa [moves_neg, Set.mem_neg] using hgr
  rcases h2 (-gr) hmem with hbe | ⟨z, hz, hbz⟩
  · exact Or.inl (IsBlockedEnd.neg hbe)
  · have hz2 : -z ∈ moves (-p) gr := by
      rw [moves_neg, Set.mem_neg] at hz; exact hz
    refine Or.inr ⟨-z, hz2, ?_⟩
    have hbz' : IsBlockedEnd p (-(-z)) := by rw [neg_neg]; exact hbz
    exact IsBlockedEnd.neg hbz'
termination_by g
decreasing_by form_wf

@[simp]
protected theorem IsBlockedEnd.neg_iff {g : G} {p : Player} :
    IsBlockedEnd p (-g) ↔ IsBlockedEnd (-p) g := by
  constructor <;> intro h1
  · exact IsBlockedEnd.neg h1
  · rw [← neg_neg g] at h1
    rw [← neg_neg p]
    exact IsBlockedEnd.neg h1

theorem isBlockedEnd_zero {p : Player} : IsBlockedEnd p (0 : G) :=
  isBlockedEnd_of_isDeadEnd isDeadEnd_zero

theorem isBlockedEnd_right_natCast (n : ℕ) : IsBlockedEnd .right (n : G) :=
  isBlockedEnd_of_isDeadEnd (isDeadEnd_right_natCast n)

theorem isBlockedEnd_right_nonneg_intCast (k : ℤ) (h1 : k ≥ 0) : IsBlockedEnd .right (k : G) :=
  isBlockedEnd_of_isDeadEnd (isDeadEnd_right_nonneg_intCast k h1)

theorem isBlockedEnd_left_nonpos_intCast (k : ℤ) (h1 : k ≤ 0) : IsBlockedEnd .left (k : G) :=
  isBlockedEnd_of_isDeadEnd (isDeadEnd_left_nonpos_intCast k h1)

/--
A game is *blocking* if every end is a blocked end, hereditarily.
-/
@[expose] def IsBlocking (g : G) : Prop :=
  (∀ p, IsEnd p g → IsBlockedEnd p g) ∧ (∀ p, ∀ gp ∈ moves p g, IsBlocking gp)
termination_by g
decreasing_by form_wf

@[simp]
theorem isBlockedEnd_of_isBlocking {g : G} {p : Player} (h1 : IsBlocking g) (h2 : IsEnd p g) :
    IsBlockedEnd p g := by
  unfold IsBlocking at h1
  exact h1.left p h2

theorem isBlocking_of_mem_moves {g h : G} {p : Player} (h1 : IsBlocking g) (h2 : h ∈ moves p g) :
    IsBlocking h := by
  unfold IsBlocking at h1
  exact h1.right p h h2

theorem isBlocking_of_isOption {g g' : G} (h1 : IsBlocking g) (h2 : Moves.IsOption g' g) :
    IsBlocking g' := by
  rw [isOption_iff_mem_union, Set.mem_union] at h2
  apply Or.elim h2 <;> exact fun h2 => isBlocking_of_mem_moves h1 h2

/--
Every dead-ending game is blocking.
-/
theorem isBlocking_of_isDeadEnding {g : G} (h1 : IsDeadEnding g) : IsBlocking g := by
  rw [IsBlocking]
  refine ⟨fun p hp => isBlockedEnd_of_isDeadEnd (isDeadEnd_of_isDeadEnding h1 hp),
    fun p gp hgp => ?_⟩
  exact isBlocking_of_isDeadEnding (isDeadEnding_of_mem_moves h1 hgp)
termination_by g
decreasing_by form_wf

@[simp]
theorem IsBlocking.add {g h : G} (h1 : IsBlocking g) (h2 : IsBlocking h) :
    IsBlocking (g + h) := by
  unfold IsBlocking
  simp only [moves_add, Set.mem_union, Set.mem_image]
  constructor <;> intro p
  · intro h3
    have ⟨h4, h5⟩ := IsEnd.add_iff.mp h3
    exact IsBlockedEnd.add (isBlockedEnd_of_isBlocking h1 h4) (isBlockedEnd_of_isBlocking h2 h5)
  · intro gp h3
    apply Or.elim h3 <;> intro ⟨g', h3, h4⟩ <;> rw [← h4]
    · exact IsBlocking.add (isBlocking_of_mem_moves h1 h3) h2
    · exact IsBlocking.add h1 (isBlocking_of_mem_moves h2 h3)
termination_by (g, h)
decreasing_by form_wf

instance : ClosedUnderAdd (IsBlocking (G := G)) where
  has_add _ _ h_g h_h := IsBlocking.add h_g h_h

private protected theorem IsBlocking.neg {g : G} (h1 : IsBlocking (-g)) : IsBlocking g := by
  unfold IsBlocking at h1 ⊢
  obtain ⟨h1, h2⟩ := h1
  apply And.intro
  · intro p h3
    rw [← neg_neg p, ← IsEnd.neg_iff_neg] at h3
    have h4 := IsBlockedEnd.neg_iff.mp (h1 (-p) h3)
    rwa [neg_neg] at h4
  · intro p gp h3
    have h4 := h2 (-p) (-gp) (by simp only [moves_neg, neg_neg, Set.mem_neg, h3])
    exact IsBlocking.neg h4
termination_by g
decreasing_by form_wf

instance : ClosedUnderNeg (IsBlocking (G := G)) where
  neg_of {g} h := by
    rw [← neg_neg g] at h
    exact IsBlocking.neg h

@[simp]
theorem isBlocking_zero : IsBlocking (0 : G) :=
  isBlocking_of_isDeadEnding DeadEnding.isDeadEnding_zero

@[simp]
theorem isBlocking_natCast (n : ℕ) : IsBlocking (n : G) :=
  isBlocking_of_isDeadEnding (DeadEnding.isDeadEnding_natCast n)

@[simp]
theorem isBlocking_intCast (k : ℤ) : IsBlocking (k : G) :=
  isBlocking_of_isDeadEnding (DeadEnding.isDeadEnding_intCast k)

@[simp]
theorem isBlocking_one : IsBlocking (1 : G) :=
  isBlocking_of_isDeadEnding DeadEnding.isDeadEnding_one

/-- The short blocking universe. -/
structure ShortBlocking (g : G) : Prop where
  short : IsShort g
  blocking : IsBlocking g

instance : Hereditary (ShortBlocking (G := G)) where
  has_option h1 h2 :=
  { short := Short.isOption h1.short h2
  , blocking := isBlocking_of_isOption h1.blocking h2 }

instance : ClosedUnderNeg (ShortBlocking (G := G)) where
  neg_of h :=
    { short := ClosedUnderNeg.neg_iff.mpr h.short
    , blocking := ClosedUnderNeg.neg_iff.mpr h.blocking
    }

instance : ClosedUnderAdd (ShortBlocking (G := G)) where
  has_add _ _ h_g h_h :=
    { short := Short.add h_g.short h_h.short
    , blocking := IsBlocking.add h_g.blocking h_h.blocking
    }

instance : ClosedUnderDicotic IsShort (ShortBlocking (G := G)) where
  closed_dicotic B C _ _ hB hC hBnon hCnon hAmbient :=
    { short := hAmbient
    , blocking := by
        unfold IsBlocking
        apply And.intro <;> intro p
        · cases p <;> intro h1 <;> simp only [isEnd_def, moves_ofSets, Player.cases] at h1
          · simp only [h1, Set.not_nonempty_empty] at hBnon
          · simp only [h1, Set.not_nonempty_empty] at hCnon
        · cases p <;> simp only [moves_ofSets, Player.cases] <;> intro gp hgp
          · exact (hB gp hgp).blocking
          · exact (hC gp hgp).blocking
    }

instance : ShortUniverse (ShortBlocking (G := G)) where
  zero_mem :=
  { short := Short.zero
  , blocking := isBlocking_zero
  }
  isAmbient_of_mem h := h.short
  has_add := ClosedUnderAdd.has_add

instance : HasNat (ShortBlocking (G := G)) where
  has_nat n :=
    { short := Short.natCast n
    , blocking := isBlocking_natCast n }

instance : ClosedUnderAddNat (ShortBlocking (G := G)) where
  has_add h_g n := ClosedUnderAdd.has_add _ _ h_g (HasNat.has_nat n)

instance : HasInt (ShortBlocking (G := G)) where
  has_int k :=
    { short := Short.intCast k
    , blocking := isBlocking_intCast k }

end Form

namespace GameForm

open Form
open Form.Misere.Outcome

private theorem winsGoingFirst_left_natSub_add_blocking :
    ∀ (a b : ℕ) (y : GameForm), IsBlocking y → IsBlockedEnd .left y →
    (a ≤ b → WinsGoingFirst .left (((a : GameForm) - (b : GameForm)) + y)) ∧
    (a < b → ¬ WinsGoingFirst .right (((a : GameForm) - (b : GameForm)) + y)) := by
  intro a b y hyB hye
  have hyend : IsEnd .left y := isEnd_of_isBlockedEnd hye
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rcases Nat.eq_zero_or_pos a with rfl | hpos
    · refine winsGoingFirst_of_isEnd ?_
      rw [isEnd_def, Set.eq_empty_iff_forall_notMem]
      intro g' hg'
      rw [mem_leftMoves_natSub_add_isEnd hyend] at hg'
      obtain ⟨a', ha', _⟩ := hg'
      exact (Nat.succ_ne_zero a' ha'.symm).elim
    · obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      refine winsGoingFirst_of_moves ⟨((a' : GameForm) - (b : GameForm)) + y, ?_, ?_⟩
      · rw [mem_leftMoves_natSub_add_isEnd hyend]; exact ⟨a', rfl, rfl⟩
      · rw [Player.neg_left]
        exact (winsGoingFirst_left_natSub_add_blocking a' b y hyB hye).2 (by omega)
  · rw [not_winsGoingFirst_iff]
    refine ⟨?_, fun g' hg' => ?_⟩
    · rw [GameForm.isEndLike_iff_isEnd, isEnd_def]
      intro hend
      have hmem : ((a : GameForm) - ((b - 1 : ℕ) : GameForm)) + y
          ∈ moves .right (((a : GameForm) - (b : GameForm)) + y) := by
        rw [mem_rightMoves_natSub_add]; exact Or.inl ⟨b - 1, by omega, rfl⟩
      rw [hend] at hmem
      exact (Set.notMem_empty _ hmem)
    · rw [Player.neg_right]
      rw [mem_rightMoves_natSub_add] at hg'
      rcases hg' with ⟨b', hb', rfl⟩ | ⟨yr, hyr, rfl⟩
      · subst hb'
        exact (winsGoingFirst_left_natSub_add_blocking a b' y hyB hye).1 (by omega)
      · have hyrB : IsBlocking yr := isBlocking_of_mem_moves hyB hyr
        rcases (IsBlockedEnd.hereditary_def hye) yr hyr with hyrbe | ⟨yrl, hyrl, hyrlbe⟩
        · exact (winsGoingFirst_left_natSub_add_blocking a b yr hyrB hyrbe).1 (le_of_lt hab)
        · have hyrlB : IsBlocking yrl := isBlocking_of_mem_moves hyrB hyrl
          refine winsGoingFirst_of_moves ⟨((a : GameForm) - (b : GameForm)) + yrl, ?_, ?_⟩
          · exact add_left_mem_moves_add hyrl _
          · rw [Player.neg_left]
            exact (winsGoingFirst_left_natSub_add_blocking a b yrl hyrlB hyrlbe).2 hab
termination_by a b y => (b, y, a)
decreasing_by
  all_goals
    first
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (Moves.Subposition.of_mem_moves (by assumption)))
      | exact Prod.Lex.right _ (Prod.Lex.left _ _
          (Moves.Subposition.trans (Moves.Subposition.of_mem_moves (by assumption))
            (Moves.Subposition.of_mem_moves (by assumption))))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

private theorem winsGoingFirst_right_natSub_add_blocking (n : ℕ) (y : GameForm)
    (hyB : IsBlocking y) (hye : IsBlockedEnd .right y) :
    WinsGoingFirst .right (((n : GameForm) - (n : GameForm)) + y) := by
  have h_neg : WinsGoingFirst .right (((n : GameForm) - n) + y)
      ↔ WinsGoingFirst .left (-(((n : GameForm) - n) + y)) :=
    (winsGoingFirst_neg_iff _ Player.left).symm
  rw [h_neg]
  have h_symm : WinsGoingFirst .left (-(((n : GameForm) - n) + y))
      ↔ WinsGoingFirst .left (((n : GameForm) - n) + (-y)) := by
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  rw [h_symm]
  exact (winsGoingFirst_left_natSub_add_blocking n n (-y) (ClosedUnderNeg.neg_of hyB)
    (IsBlockedEnd.neg_iff.mpr hye)).left le_rfl

private theorem nat_add_neg_misereEQ_blocking (n : ℕ) :
    ((n : GameForm) - (n : GameForm)) =m ShortBlocking 0 := by
  induction n with
  | zero => intro x _; simp only [Nat.cast_zero, sub_zero, zero_add]
  | succ k ih =>
    apply MisereEq.of_antisymm
    · refine Hereditary.misereGE_of_maintenance_proviso ShortBlocking ?_ ?_ ?_ ?_
      · simp only [Maintenance]
        intro gr h_gr
        simp_all only [sub_eq_add_neg, Nat.cast_add, Nat.cast_one, neg_add_rev, Set.mem_image,
                       moves_add, rightMoves_natCast, Set.image_empty, rightMoves_one, moves_zero,
                       Set.union_self, moves_neg, Player.le_left, Player.neg_right, and_true,
                       Player.le_left_eq, leftMoves_one, Set.neg_singleton,neg_zero, ↓existsAndEq,
                       Set.image_singleton, zero_add, Set.singleton_union, Set.empty_union,
                       exists_eq_or_imp, Set.mem_empty_iff_false, false_and, exists_const,
                       Set.mem_insert_iff, Set.mem_neg, Set.exists_neg_mem, false_or]
        rcases h_gr with ( rfl | ⟨ x, hx, rfl ⟩ )
        · simp [moves_add, moves_neg, misereGE_of_misereEQ ih]
        · rcases k with ( _ | k )
          · simp at hx
          · simp only [Nat.cast_add, Nat.cast_one, leftMoves_natCast_succ,
                       Set.mem_singleton_iff] at hx
            subst hx
            simpa [leftMoves_natCast_succ] using misereGE_of_misereEQ ih
      · simp [Maintenance]
      · simp [Proviso]
      · intro _ x hx hxe
        exact (winsGoingFirst_left_natSub_add_blocking (k+1) (k+1) x hx.blocking
          (isBlockedEnd_of_isBlocking hx.blocking (GameForm.isEndLike_iff_isEnd.mp hxe))).1 le_rfl
    · refine Hereditary.misereGE_of_maintenance_proviso ShortBlocking ?_ ?_ ?_ ?_
      · simp [Maintenance]
      · simp only [Maintenance]
        intro hl h_hl
        simp [sub_eq_add_neg] at h_hl
        simp only [moves_zero, Set.mem_empty_iff_false, h_hl, false_and, exists_const,
          moves_add, rightMoves_natCast, Set.image_empty, moves_neg, Player.neg_right,
          leftMoves_one, Set.neg_singleton, neg_zero, Set.image_singleton, zero_add,
          Set.singleton_union, Set.empty_union, Set.mem_image, Set.mem_insert_iff, Set.mem_neg,
          Set.exists_neg_mem, exists_eq_or_imp, ↓existsAndEq, and_true, exists_eq_or_imp',
          false_or]
        exact Or.inl (misereGE_of_misereEQ (MisereEQ.symm ih))
      · intro _ x hx hxe
        exact winsGoingFirst_right_natSub_add_blocking (k + 1) x hx.blocking
          (isBlockedEnd_of_isBlocking hx.blocking (GameForm.isEndLike_iff_isEnd.mp hxe))
      · simp [Proviso]

private theorem int_add_neg_misereEQ_blocking (n : ℤ) :
    ((n : GameForm) - (n : GameForm)) =m ShortBlocking 0 := by
  convert nat_add_neg_misereEQ_blocking ( Int.natAbs n ) using 1;
  cases n <;> simp [sub_eq_add_neg, add_comm, add_left_comm]

/--
This is [Davies, Miller, Milley (Lemma 4.5 on p. 26)][davies:SumsPFreeForms:2025]
-/
instance : IntegerInvertible ShortBlocking where
  int_add_neg_misereEQ := int_add_neg_misereEQ_blocking

end GameForm

end

end MisereGames
