/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Misere.Comparison
public import LeanPool.MisereGames.Misere.PFree
public import LeanPool.MisereGames.Misere.Universe
public import LeanPool.MisereGames.Misere.OutcomeStable.PropertyX

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

/-- A `p`-dead end is a `p`-end whose options are again `p`-dead ends. -/
def IsDeadEnd (p : Player) (g : G) : Prop :=
  IsEnd p g ∧ (∀ gp ∈ moves (-p) g, IsDeadEnd p gp)
termination_by g
decreasing_by form_wf

theorem isDeadEnd_def (p : Player) (g : G) :
    IsDeadEnd p g ↔ IsEnd p g ∧ (∀ gp ∈ moves (-p) g, IsDeadEnd p gp) := by nth_rw 1 [IsDeadEnd]

theorem isEnd_of_isDeadEnd {g : G} {p : Player} (h1 : IsDeadEnd p g) : IsEnd p g := by
  unfold IsDeadEnd at h1
  exact h1.left

theorem IsDeadEnd.hereditary_def {g : G} {p : Player} (h1 : IsDeadEnd p g) :
    ∀ gp ∈ moves (-p) g, IsDeadEnd p gp := by
  unfold IsDeadEnd at h1
  exact h1.right

@[simp]
theorem not_mem_moves_of_isDeadEnd {g gp : G} {p : Player} (h1 : IsDeadEnd p g) :
    gp ∉ moves p g := by
  simp [isEnd_of_isDeadEnd h1]

theorem player_eq_neg_of_isDeadEnd_mem_moves {g gp : G} {p1 p2 : Player} (h1 : IsDeadEnd p1 g)
    (h2 : gp ∈ moves p2 g) : p2 = -p1 := by
  by_cases h3 : p2 = p1
  · rw [h3] at h2
    absurd h2
    simp only [h1, not_mem_moves_of_isDeadEnd, not_false_eq_true]
  · exact Player.ne_iff_eq_neg.mp h3

theorem isDeadEnd_of_mem_moves {g gp : G} {p1 p2 : Player} (h1 : IsDeadEnd p1 g) (h2 :
    gp ∈ moves p2 g)
      : IsDeadEnd p1 gp := by
  rw [player_eq_neg_of_isDeadEnd_mem_moves h1 h2] at h2
  exact IsDeadEnd.hereditary_def h1 gp h2

theorem isDeadEnd_isOption {p : Player} {g gp : G} (h1 : IsDeadEnd p g) (h2 : IsOption gp g) :
    gp ∈ moves (-p) g := isOption_not_mem h2 (not_mem_moves_of_isDeadEnd h1)

theorem isDeadEnd_of_isOption {g gp : G} {p : Player} (h1 : IsDeadEnd p g) (h2 : IsOption gp g) :
    IsDeadEnd p gp := isDeadEnd_of_mem_moves h1 (isDeadEnd_isOption h1 h2)

protected theorem IsDeadEnd.add {g h : G} {p : Player} (h1 : IsDeadEnd p g) (h2 : IsDeadEnd p h) :
    IsDeadEnd p (g + h) := by
  unfold IsDeadEnd
  simp only [moves_add, Set.mem_union, Set.mem_image]
  apply And.intro (IsEnd.add_iff.mpr ⟨isEnd_of_isDeadEnd h1, isEnd_of_isDeadEnd h2⟩)
  intro gp h3
  apply Or.elim h3 <;> intro ⟨gpp, h3, h4⟩ <;> rw [<-h4]
  · exact IsDeadEnd.add (isDeadEnd_of_mem_moves h1 h3) h2
  · exact IsDeadEnd.add h1 (isDeadEnd_of_mem_moves h2 h3)
termination_by (g, h)
decreasing_by all_goals form_wf

private protected theorem IsDeadEnd.neg {g : G} {p : Player} (h1 : IsDeadEnd p (-g)) :
    IsDeadEnd (-p) g := by
  have h0 := h1
  unfold IsDeadEnd at h1 ⊢
  have ⟨h3, h2⟩ := h1
  apply And.intro (IsEnd.neg_iff_neg.mp h3)
  rw [neg_neg]
  intro gp h4
  have h5 : IsDeadEnd p (-gp) := by
    rw [<-neg_neg g, moves_neg] at h4
    exact h2 (-gp) (Set.mem_neg.mp h4)
  exact IsDeadEnd.neg h5
termination_by g
decreasing_by form_wf

@[simp]
protected theorem IsDeadEnd.neg_iff {g : G} {p : Player} : IsDeadEnd p (-g) ↔ IsDeadEnd (-p) g := by
  constructor <;> intro h1
  · exact IsDeadEnd.neg h1
  · rw [<-neg_neg g] at h1
    rw [<-neg_neg p]
    exact IsDeadEnd.neg h1

theorem isDeadEnd_zero {p : Player} : IsDeadEnd p (0 : G) := by
  unfold IsDeadEnd
  simp only [isEnd_zero, moves_zero (G := G), Set.mem_empty_iff_false,
             IsEmpty.forall_iff, implies_true, and_self]

theorem isDeadEnd_right_natCast (n : ℕ) : IsDeadEnd .right (n : G) := by
  match n with
  | .zero => exact isDeadEnd_zero
  | .succ k => unfold IsDeadEnd; simp [isDeadEnd_right_natCast k]

theorem isDeadEnd_right_nonneg_intCast (k : ℤ) (h1 : k ≥ 0) : IsDeadEnd .right (k : G) := by
  rw [<-Int.toNat_of_nonneg h1]
  norm_cast
  simp only [isDeadEnd_right_natCast]

theorem isDeadEnd_left_nonpos_intCast (k : ℤ) (h1 : k ≤ 0) : IsDeadEnd .left (k : G) := by
  rw [<-Player.neg_right, <-IsDeadEnd.neg_iff]
  norm_cast
  exact isDeadEnd_right_nonneg_intCast (-k) (by omega)

theorem isPFree_of_isDeadEnd {g : G} {p : Player} (h1 : IsDeadEnd p g) : IsPFree g := by
  unfold IsPFree
  apply And.intro
  · have h2 :=
      miserePlayerOutcome_eq_iff_winsGoingFirst.mpr
        (winsGoingFirst_of_isEnd (isEnd_of_isDeadEnd h1))
    cases p
    · cases h3 : MiserePlayerOutcome g .right <;> simp [MisereOutcome, Outcome.ofPlayers, h2, h3]
    · cases h3 : MiserePlayerOutcome g .left <;> simp [MisereOutcome, Outcome.ofPlayers, h2, h3]
  · intro p' gp h_gp
    exact isPFree_of_isDeadEnd (isDeadEnd_of_mem_moves h1 h_gp)
termination_by g
decreasing_by form_wf

/-- A form is dead-ending when all of its end options are dead ends, hereditarily. -/
@[expose] def IsDeadEnding (g : G) : Prop :=
  (∀ p, IsEnd p g → IsDeadEnd p g) ∧ (∀ p, ∀gp ∈ moves p g, IsDeadEnding gp)
termination_by g
decreasing_by form_wf

@[simp]
theorem isDeadEnd_of_isDeadEnding {g : G} {p : Player} (h1 : IsDeadEnding g) (h2 : IsEnd p g) :
    IsDeadEnd p g := by
  unfold IsDeadEnding at h1
  exact h1.left p h2

theorem isDeadEnding_of_mem_moves {g h : G} {p : Player} (h1 : IsDeadEnding g) (h2 :
    h ∈ moves p g) :
    IsDeadEnding h := by
  unfold IsDeadEnding at h1
  exact h1.right p h h2

theorem isDeadEnding_of_isOption {g g' : G} (h1 : IsDeadEnding g) (h2 : Moves.IsOption g' g)
    : IsDeadEnding g' := by
  rw [isOption_iff_mem_union, Set.mem_union] at h2
  apply Or.elim h2 <;> exact fun h2 => isDeadEnding_of_mem_moves h1 h2

instance : Hereditary (IsDeadEnding (G := G)) where
  has_option := isDeadEnding_of_isOption

/-- A predicate whose members are dead-ending forms. -/
class DeadEnding (A : G → Prop) where
  isDeadEnding {g : G} (hA : A g) : IsDeadEnding g

instance : DeadEnding (IsDeadEnding (G := G)) where
  isDeadEnding := id

namespace DeadEnding

@[simp]
protected theorem IsDeadEnding.add {g h : G} (h1 : IsDeadEnding g) (h2 : IsDeadEnding h) :
    IsDeadEnding (g + h) := by
  unfold IsDeadEnding
  simp only [moves_add, Set.mem_union, Set.mem_image]
  constructor <;> intro p
  · intro h3
    have ⟨h4, h5⟩ := IsEnd.add_iff.mp h3
    exact IsDeadEnd.add (isDeadEnd_of_isDeadEnding h1 h4) (isDeadEnd_of_isDeadEnding h2 h5)
  · intro gp h3
    apply Or.elim h3 <;> intro ⟨g', h3, h4⟩ <;> rw [<-h4]
    · exact IsDeadEnding.add (isDeadEnding_of_mem_moves h1 h3) h2
    · exact IsDeadEnding.add h1 (isDeadEnding_of_mem_moves h2 h3)
termination_by (g, h)
decreasing_by all_goals form_wf

private protected theorem IsDeadEnding.neg {g : G} (h1 : IsDeadEnding (-g)) : IsDeadEnding g := by
  unfold IsDeadEnding at h1 ⊢
  obtain ⟨h1, h2⟩ := h1
  apply And.intro
  · intro p h3
    rw [<-neg_neg p, <-IsEnd.neg_iff_neg] at h3
    have h4 := IsDeadEnd.neg_iff.mp (h1 (-p) h3)
    rwa [neg_neg] at h4
  · intro p gp h3
    have h4 := h2 (-p) (-gp) (by simp [h3])
    exact IsDeadEnding.neg h4
termination_by g
decreasing_by form_wf

instance : ClosedUnderNeg (IsDeadEnding (G := G)) where
  neg_of {g} h := by
    rw [<-neg_neg g] at h
    exact IsDeadEnding.neg h

@[simp]
theorem isDeadEnding_zero : IsDeadEnding (0 : G) := by
  unfold IsDeadEnding IsDeadEnd
  simp

@[simp]
theorem isDeadEnding_natCast (n : ℕ) : IsDeadEnding (n : G) := by
  match n with
  | .zero => exact isDeadEnding_zero
  | .succ k =>
    unfold IsDeadEnding
    refine And.intro ?_ (nat_forall_moves (isDeadEnding_natCast k))
    intro p h
    simp only [succ_nat_end_right.mp h, isDeadEnd_right_natCast k.succ]

@[simp]
theorem isDeadEnding_intCast (k : ℤ) : IsDeadEnding (k : G) := by
  match k with
  | .ofNat n => exact isDeadEnding_natCast n
  | .negSucc n =>
    rw [Int.negSucc_eq, Form.intCast_neg, ClosedUnderNeg.neg_iff (A := IsDeadEnding)]
    norm_cast
    exact isDeadEnding_natCast (n + 1)

@[simp]
theorem isDeadEnding_one : IsDeadEnding (1 : G) := by
  rw [<-Form.intCast_one]
  exact isDeadEnding_intCast 1

/-- Forms that are both short and dead-ending. -/
structure ShortDeadEnding (g : G) : Prop where
  short : IsShort g
  dead_ending : IsDeadEnding g

instance : DeadEnding (ShortDeadEnding (G := G)) where
  isDeadEnding hA := hA.dead_ending

instance : Hereditary (ShortDeadEnding (G := G)) where
  has_option h1 h2 :=
  { short := Short.isOption h1.short h2
  , dead_ending := isDeadEnding_of_isOption h1.dead_ending h2
  }

instance : ShortUniverse (ShortDeadEnding (G := G)) where
  zero_mem :=
  { short := by
      rw [short_def]
      intro p
      simp
  , dead_ending := isDeadEnding_zero
  }
  isAmbient_of_mem h := h.short
  has_add _ _ h_g h_h :=
    { short := Short.add h_g.short h_h.short
    , dead_ending := IsDeadEnding.add h_g.dead_ending h_h.dead_ending
    }
  has_option := Hereditary.has_option
  neg_of h :=
    { short := ClosedUnderNeg.neg_iff.mpr h.short
    , dead_ending := ClosedUnderNeg.neg_iff.mpr h.dead_ending
    }
  closed_dicotic B C _ _ hB hC hBnon hCnon hAmbient :=
    { short := hAmbient
    , dead_ending := by
        unfold IsDeadEnding
        apply And.intro <;> intro p
        · cases p <;> intro h1 <;> simp only [isEnd_def, moves_ofSets, Player.cases] at h1
          · simp only [h1, Set.not_nonempty_empty] at hBnon
          · simp only [h1, Set.not_nonempty_empty] at hCnon
        · cases p <;> simp only [moves_ofSets, Player.cases] <;> intro gp hgp
          · exact (hB gp hgp).dead_ending
          · exact (hC gp hgp).dead_ending
    }

instance : HasNat (ShortDeadEnding (G := G)) where
  has_nat n :=
    { short := Short.natCast n
    , dead_ending := isDeadEnding_natCast n
    }

instance : HasInt (ShortDeadEnding (G := G)) where
  has_int k :=
    { short := Short.intCast k
    , dead_ending := isDeadEnding_intCast k
    }

end DeadEnding

end Form

namespace GameForm.DeadEnding

open Form
open Form.Misere.Outcome
open Form.DeadEnding

/--
This is [Milley, Renault (Lemma 3 on p. 5)][milley:DeadEndsMisere:2013].
-/
private theorem lemma3.aux {g : GameForm} {p : Player} (h1 : g ≠ 0) (h2 : IsDeadEnd p g) :
    MisereOutcome g = Outcome.ofPlayer p := by
  rw [misereOutcome_eq_player_iff]
  apply And.intro (winsGoingFirst_of_isEnd (isEnd_of_isDeadEnd h2))
  simp only [not_winsGoingFirst_iff, neg_neg, isEndLike_iff_isEnd]
  apply And.intro (zero_not_both_end h1 (isEnd_of_isDeadEnd h2))
  intro gr h4
  exact winsGoingFirst_of_isEnd (isEnd_of_isDeadEnd (isDeadEnd_of_mem_moves h2 h4))

/--
This is [Milley, Renault (Lemma 3 on p. 5)][milley:DeadEndsMisere:2013].
-/
theorem isDeadEnd_left_misereOutcome_L (g : GameForm) (h1 : g ≠ 0) (h2 : IsDeadEnd .left g) :
    MisereOutcome g = .L := lemma3.aux h1 h2

/--
This is [Milley, Renault (Lemma 3 on p. 5)][milley:DeadEndsMisere:2013].
-/
theorem isDeadEnd_right_misereOutcome_R (g : GameForm) (h1 : g ≠ 0) (h2 : IsDeadEnd .right g) :
    MisereOutcome g = .R := lemma3.aux h1 h2

-- TODO: Split
private theorem winsGoingFirst_left_natSub_add :
    ∀ (a b : ℕ) (y : GameForm), IsDeadEnding y → IsEnd .left y →
    (a ≤ b → WinsGoingFirst .left (((a : GameForm) - (b : GameForm)) + y)) ∧
    (a < b → ¬ WinsGoingFirst .right (((a : GameForm) - (b : GameForm)) + y)) := by
  intro a b y hy hye
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rcases Nat.eq_zero_or_pos a with rfl | hpos
    · refine winsGoingFirst_of_isEnd ?_
      rw [isEnd_def, Set.eq_empty_iff_forall_notMem]
      intro g' hg'
      rw [mem_leftMoves_natSub_add_isEnd hye] at hg'
      obtain ⟨a', ha', _⟩ := hg'
      exact (Nat.succ_ne_zero a' ha'.symm).elim
    · obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      refine winsGoingFirst_of_moves ⟨((a' : GameForm) - (b : GameForm)) + y, ?_, ?_⟩
      · rw [mem_leftMoves_natSub_add_isEnd hye]; exact ⟨a', rfl, rfl⟩
      · rw [Player.neg_left]
        exact (winsGoingFirst_left_natSub_add a' b y hy hye).2 (by omega)
  · rw [not_winsGoingFirst_iff]
    refine ⟨?_, fun g' hg' => ?_⟩
    · rw [GameForm.isEndLike_iff_isEnd, isEnd_def]
      intro hend
      have hmem : ((a : GameForm) - ((b - 1 : ℕ) : GameForm)) + y
          ∈ moves .right (((a : GameForm) - (b : GameForm)) + y) := by
        rw [mem_rightMoves_natSub_add]
        exact Or.inl ⟨b - 1, by omega, rfl⟩
      rw [hend] at hmem
      exact (Set.notMem_empty _ hmem)
    · rw [Player.neg_right]
      rw [mem_rightMoves_natSub_add] at hg'
      rcases hg' with ⟨b', hb', rfl⟩ | ⟨yr, hyr, rfl⟩
      · subst hb'
        exact (winsGoingFirst_left_natSub_add a b' y hy hye).1 (by omega)
      · have hyr_de : IsDeadEnding yr := isDeadEnding_of_mem_moves hy hyr
        have hyr_e : IsEnd .left yr :=
          isEnd_of_isDeadEnd (isDeadEnd_of_mem_moves (isDeadEnd_of_isDeadEnding hy hye) hyr)
        exact (winsGoingFirst_left_natSub_add a b yr hyr_de hyr_e).1 (le_of_lt hab)
termination_by a b y => (b, y, a)
decreasing_by
  all_goals
    first
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (Moves.Subposition.of_mem_moves (by assumption)))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

private theorem winsGoingFirst_right_natSub_add (n : ℕ) (y : GameForm)
    (hy : IsDeadEnding y) (hye : IsEnd .right y) :
    WinsGoingFirst .right (((n : GameForm) - (n : GameForm)) + y) := by
  have h_neg : WinsGoingFirst .right (↑n - ↑n + y) ↔ WinsGoingFirst .left (-((↑n - ↑n) + y)) := by
    grind only [winsGoingFirst_neg_iff, Player.neg_left]
  have h_symm :
      WinsGoingFirst .left (-(↑n - ↑n + y)) ↔ WinsGoingFirst .left ((↑n - ↑n) + (-y)) := by
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  rw [h_neg, h_symm]
  convert (winsGoingFirst_left_natSub_add n n ( -y ) _ _).1 le_rfl
  · exact ClosedUnderNeg.neg_of hy
  · exact IsEnd.neg_iff_neg.mpr hye

private theorem nat_add_neg_misereEQ' (n : ℕ) :
    ((n : GameForm) - (n : GameForm)) =m ShortDeadEnding 0 := by
  induction n with
  | zero =>
    intro x _
    simp only [Nat.cast_zero, sub_zero, zero_add]
  | succ k ih =>
    apply MisereEq.of_antisymm
    · refine Hereditary.misereGE_of_maintenance_proviso ShortDeadEnding ?_ ?_ ?_ ?_
      · simp only [Maintenance, moves_zero, Set.mem_empty_iff_false, false_and, exists_const,
          false_or, Nat.cast_add, Nat.cast_one]
        intro gr h_gr
        simp only [sub_eq_add_neg, neg_add_rev, moves_add, rightMoves_natCast, Set.image_empty,
          rightMoves_one, Set.union_self, moves_neg, Player.neg_right, leftMoves_one,
          Set.neg_singleton, neg_zero, Set.image_singleton, zero_add, Set.singleton_union,
          Set.empty_union, Set.mem_image, Set.mem_insert_iff, Set.mem_neg, Set.exists_neg_mem,
          exists_eq_or_imp, ↓existsAndEq, and_true] at h_gr
        rcases h_gr with (rfl | ⟨x, hx, rfl⟩)
        · use (↑k - ↑k)
          refine ⟨?_, misereGE_of_misereEQ ih⟩
          simp [sub_eq_add_neg]
        · rcases k with (_ | k)
          · simp only [Nat.cast_zero, moves_zero, Set.mem_empty_iff_false] at hx
          · simp only [Nat.cast_add, Nat.cast_one, leftMoves_natCast_succ,
            Set.mem_singleton_iff] at hx
            simp only [Nat.cast_add, Nat.cast_one, sub_eq_add_neg, neg_add_rev] at ih
            simp [leftMoves_natCast_succ, hx, misereGE_of_misereEQ ih] at ⊢
      · simp [Maintenance]
      · simp [Proviso]
      · intro _ x hx hxe
        exact
          (winsGoingFirst_left_natSub_add (k + 1) (k + 1) x hx.dead_ending
            (GameForm.isEndLike_iff_isEnd.mp hxe)).1 le_rfl
    · refine Hereditary.misereGE_of_maintenance_proviso ShortDeadEnding ?_ ?_ ?_ ?_
      · simp [Maintenance]
      · simp only [Maintenance]
        intro hl h_hl
        have h_hl' : hl = ↑k + (-1 + -↑k) := by
          simpa [sub_eq_add_neg, moves_add, moves_neg] using h_hl
        rw [h_hl']
        simp only [moves_zero, Set.mem_empty_iff_false, false_and, exists_const, moves_add,
          rightMoves_natCast, Set.image_empty, moves_neg, Player.neg_right, leftMoves_one,
          Set.neg_singleton, neg_zero, Set.image_singleton, zero_add, Set.singleton_union,
          Set.empty_union, Set.mem_image, Set.mem_insert_iff, Set.mem_neg, Set.exists_neg_mem,
          exists_eq_or_imp, ↓existsAndEq, and_true, exists_eq_or_imp', false_or]
        rcases k with (_ | k)
        · simp
        · simp only [Nat.cast_add, Nat.cast_one, sub_eq_add_neg, neg_add_rev] at ih
          simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, leftMoves_natCast_succ,
                     Set.mem_singleton_iff, exists_eq_left, or_self,
                     misereGE_of_misereEQ ih.symm]
      · intro _ x hx hxe
        exact
          winsGoingFirst_right_natSub_add (k + 1) x hx.dead_ending
            (GameForm.isEndLike_iff_isEnd.mp hxe)
      · simp [Proviso]

private theorem int_add_neg_misereEQ' (n : ℤ) :
    ((n : GameForm) - (n : GameForm)) =m ShortDeadEnding 0 := by
  by_cases hn : 0 ≤ n
  · convert nat_add_neg_misereEQ' (Int.natAbs n) using 1
    match n with
    | .ofNat k =>
      simp only [Int.ofNat_eq_natCast, Form.intCast_nat, Int.natAbs_natCast]
  · match n with
    | .ofNat k =>
    · absurd hn
      exact Int.zero_le_ofNat _
    | .negSucc k =>
      convert nat_add_neg_misereEQ' (k + 1) using 1
      simp only [Form.intCast_negSucc, neg_add_rev, add_comm, sub_eq_add_neg, neg_neg,
                 add_left_comm, add_assoc, Nat.cast_add, Nat.cast_one]

instance : IntegerInvertible ShortDeadEnding where
  int_add_neg_misereEQ := int_add_neg_misereEQ'

instance : IntegerInvertible.PropertyX ShortDeadEnding where
  prop_left := by
    intro g h hAg hAh hsg hsh hNg hNh hge hnge hrg hlh
    by_cases hg0 : g = 0
    · subst hg0
      rw [zero_add]
      exact hNh
    · have hdead :=
        isDeadEnd_left_misereOutcome_L g hg0
          (isDeadEnd_of_isDeadEnding hAg.mem.dead_ending hge)
      absurd (hNg.symm.trans hdead)
      decide
  prop_right := by
    intro g h hAg hAh hsg hsh hNg hNh hge hnge hlg hrh
    by_cases hh0 : h = 0
    · subst hh0
      rw [add_zero]
      exact hNg
    · have hdead :=
        isDeadEnd_right_misereOutcome_R h hh0
          (isDeadEnd_of_isDeadEnding hAh.mem.dead_ending hge)
      absurd (hNh.symm.trans hdead)
      decide

end GameForm.DeadEnding

namespace Form

universe u

variable {G : Type (u + 1)} [Form G]

open Form.Misere.Outcome

/--
For Left dead ends `g` and `h` (with `A` promain), comparison `g ≥m A h`
reduces to the Right proviso plus maintenance of Right's moves.
-/
theorem misereGE_iff_strong_of_isDeadEnd_left
    {A IsAmbient : G → Prop} (h_promain : Promain IsAmbient A)
    {g h : G} (h_g_dead : IsDeadEnd .left g) (h_h_dead : IsDeadEnd .left h)
    (h_g : IsAmbient g) (h_h : IsAmbient h) :
    g ≥m A h ↔
      (IsEndLike .right g → Strong A h .right) ∧
      (∀ gr ∈ moves .right g, ∃ hr ∈ moves .right h, gr ≥m A hr) := by
  rw [h_promain h_g h_h]
  constructor
  · intro ⟨h_maint_right, _, h_proviso_right, _⟩
    refine ⟨h_proviso_right, fun gr h_gr => ?_⟩
    rcases h_maint_right gr h_gr with ⟨hr, h_hr, h_ge⟩ | ⟨grl, h_grl, _⟩
    · exact ⟨hr, h_hr, h_ge⟩
    · exact absurd h_grl (not_mem_moves_of_isDeadEnd (isDeadEnd_of_mem_moves h_g_dead h_gr))
  · intro ⟨h_right_strong, h_right_moves⟩
    refine ⟨fun gr h_gr => Or.inl (h_right_moves gr h_gr), ?_, h_right_strong, ?_⟩
    · intro hl h_hl
      exact absurd h_hl (not_mem_moves_of_isDeadEnd h_h_dead)
    · intro _ x _ h_x_left_end
      exact winsGoingFirst_of_isEndLike
        (IsEndLike.add_iff.mpr
          ⟨isEndLike_of_isEnd (isEnd_of_isDeadEnd h_g_dead), h_x_left_end⟩)

/--
For Left dead ends, if `A` has a form that is an end for both players (such as
`0`), the Right proviso simplifies to Right end-like positions being preserved.
-/
theorem misereGE_iff_isEndLike_of_isDeadEnd_left
    {A IsAmbient : G → Prop} (h_promain : Promain IsAmbient A)
    (hA_end : ∃ x, A x ∧ IsEnd .left x ∧ IsEnd .right x)
    {g h : G} (h_g_dead : IsDeadEnd .left g) (h_h_dead : IsDeadEnd .left h)
    (h_g : IsAmbient g) (h_h : IsAmbient h) :
    g ≥m A h ↔
      (IsEndLike .right g → IsEndLike .right h) ∧
      (∀ gr ∈ moves .right g, ∃ hr ∈ moves .right h, gr ≥m A hr) := by
  rw [misereGE_iff_strong_of_isDeadEnd_left h_promain h_g_dead h_h_dead h_g h_h]
  refine and_congr_left' ⟨fun h_right_strong h_g_right_end => ?_,
    fun h_right_end h_g_right_end x _ h_x_right_end => winsGoingFirst_of_isEndLike
      (IsEndLike.add_iff.mpr ⟨h_right_end h_g_right_end, h_x_right_end⟩)⟩
  obtain ⟨x, hxA, hx_left_end, hx_right_end⟩ := hA_end
  have h_win : WinsGoingFirst .right (h + x) :=
    h_right_strong h_g_right_end x hxA (isEndLike_of_isEnd hx_right_end)
  rw [winsGoingFirst_iff] at h_win
  rcases h_win with h_hx_right_end | ⟨hx', h_hx', h_not_win⟩
  · exact (IsEndLike.add_iff.mp h_hx_right_end).left
  · simp only [moves_add, Set.mem_union, Set.mem_image] at h_hx'
    rcases h_hx' with ⟨hr, h_hr, rfl⟩ | ⟨xr, h_xr, rfl⟩
    · exact absurd (winsGoingFirst_of_isEndLike (IsEndLike.add_iff.mpr
        ⟨isEndLike_of_isEnd (isEnd_of_isDeadEnd (isDeadEnd_of_mem_moves h_h_dead h_hr)),
          isEndLike_of_isEnd hx_left_end⟩)) h_not_win
    · exact absurd h_xr (not_mem_moves_of_isEnd hx_right_end)

mutual

theorem isDeadEnd_left_strongTest_winsGoingFirst {x g : GameForm}
    (hxd : IsDeadEnd .left x) (h_test : IsStrongTest .left g) :
    WinsGoingFirst .left (g + x) := by
  have hxe : IsEnd .left x := isEnd_of_isDeadEnd hxd
  rw [isStrongTest_def] at h_test
  rcases h_test with h_isEnd | ⟨gl, hgl, houtcome, htestgl, hglr⟩
  · exact winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨h_isEnd, hxe⟩)
  · apply winsGoingFirst_of_moves
    refine ⟨gl + x, add_right_mem_moves_add hgl x, ?_⟩
    rw [Player.neg_left]
    have hglr' : ∀ gr ∈ moves .right gl, IsStrongTest .left gr := by
      intro gr hgr; exact hglr gr (by rw [Player.neg_left]; exact hgr)
    exact isDeadEnd_left_strongTest_not_winsGoingFirst hxd houtcome htestgl hglr'
termination_by (x, g)
decreasing_by form_wf

theorem isDeadEnd_left_strongTest_not_winsGoingFirst {x g : GameForm}
    (h_isDeadEnd : IsDeadEnd .left x) (h_outcome : MisereOutcome g = .L)
    (h_test : IsStrongTest .left g) (h_gr : ∀ gr ∈ moves .right g, IsStrongTest .left gr) :
    ¬ WinsGoingFirst .right (g + x) := by
  rw [not_winsGoingFirst_iff]
  refine ⟨?_, ?_⟩
  · rw [GameForm.isEndLike_iff_isEnd, IsEnd.add_iff]
    rintro ⟨hgend, _⟩
    exact (misereOutcome_L_iff_winsGoingFirst.mp h_outcome).2 (winsGoingFirst_of_isEnd hgend)
  · intro g' hg'
    rw [Player.neg_right]
    rw [moves_add] at hg'
    rcases hg' with ⟨gr, hgr', rfl⟩ | ⟨xr, hxr, rfl⟩
    · exact (isDeadEnd_left_strongTest_winsGoingFirst h_isDeadEnd) (h_gr gr hgr')
    · have hxr' : xr ∈ moves (-Player.left) x := by rw [Player.neg_left]; exact hxr
      have h_isDeadEnd_xr := isDeadEnd_of_mem_moves h_isDeadEnd hxr'
      exact isDeadEnd_left_strongTest_winsGoingFirst h_isDeadEnd_xr h_test
termination_by (x, g)
decreasing_by form_wf

end

theorem _root_.MisereGames.Form.isDeadEnd_right_strongTest_winsGoingFirst {x g : GameForm}
    (hxd : IsDeadEnd .right x) (h_test : IsStrongTest .right g) :
    WinsGoingFirst .right (g + x) := by
  rw [<-neg_neg x, IsDeadEnd.neg_iff, Player.neg_right] at hxd
  rw [<-neg_neg g, IsStrongTest.neg_iff, Player.neg_right] at h_test
  rw [<-Player.neg_left, <-winsGoingFirst_neg_iff, neg_add_rev, add_comm]
  exact isDeadEnd_left_strongTest_winsGoingFirst hxd h_test

/--
This is one direction specialized to dead-ending of
[Davies, Milley (Theorem 3.1 on p. 7)][davies:OrderInversesMonoid:2026]
-/
theorem _root_.MisereGames.Form.IsStrongTest.left_strong {A : GameForm → Prop} [DeadEnding A]
    {g : GameForm}
    (h_test : IsStrongTest .left g) :
    Strong A g .left := by
  intro x hx h_isEnd
  rw [GameForm.isEndLike_iff_isEnd] at h_isEnd
  have h_deadEnd := isDeadEnd_of_isDeadEnding (DeadEnding.isDeadEnding hx) h_isEnd
  exact isDeadEnd_left_strongTest_winsGoingFirst h_deadEnd h_test

/--
This is mirror of one direction specialized to dead-ending of
[Davies, Milley (Theorem 3.1 on p. 7)][davies:OrderInversesMonoid:2026]
-/
theorem _root_.MisereGames.Form.IsStrongTest.right_strong {A : GameForm → Prop} [DeadEnding A]
    {g : GameForm}
    (h_test : IsStrongTest .right g) :
    Strong A g .right := by
  intro x hx h_isEnd
  rw [GameForm.isEndLike_iff_isEnd] at h_isEnd
  have h_deadEnd := isDeadEnd_of_isDeadEnding (DeadEnding.isDeadEnding hx) h_isEnd
  exact isDeadEnd_right_strongTest_winsGoingFirst h_deadEnd h_test

theorem _root_.MisereGames.Form.PFree.strong_right_iff_misereOutcome_L {A : GameForm → Prop}
    [DeadEnding A] [HasZero A]
    {g : GameForm} (h_isPFree : IsPFree g) :
    Strong A g .right ↔ MisereOutcome g ≠ .L := by
  constructor
  · intro h_strong h_outcome
    rw [misereOutcome_L_iff_winsGoingFirst] at h_outcome
    have h_wins := h_strong 0 HasZero.has_zero (isEndLike_of_isEnd isEnd_zero)
    rw [add_zero] at h_wins
    exact h_outcome.right h_wins
  · intro h_outcome
    exact IsStrongTest.right_strong (PFree.isStrongTest_right h_isPFree h_outcome)

theorem _root_.MisereGames.Form.PFree.strong_left_iff_misereOutcome_R {A : GameForm → Prop}
    [DeadEnding A] [HasZero A]
    {g : GameForm} (h_isPFree : IsPFree g) :
    Strong A g .left ↔ MisereOutcome g ≠ .R := by
  constructor
  · intro h_strong h_outcome
    rw [misereOutcome_R_iff_winsGoingFirst] at h_outcome
    have h_wins := h_strong 0 HasZero.has_zero (isEndLike_of_isEnd isEnd_zero)
    rw [add_zero] at h_wins
    exact h_outcome.right h_wins
  · intro h_outcome
    exact IsStrongTest.left_strong (PFree.isStrongTest_left h_isPFree h_outcome)

end Form

end

end MisereGames
