/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Form.Classes
public import LeanPool.MisereGames.Form.Birthday

/-!
Misere combinatorial games.
-/

namespace MisereGames

public section

namespace Form.Misere.Outcome

open Form

universe u

variable {G : Type (u + 1)} [Form G]

/-- In misère play, `p` can force a win when moving first from `g`. -/
def WinsGoingFirst (p : Player) (g : G) : Prop := IsEndLike p g ∨ (∃ g', ∃ (_ : g' ∈ moves p g),
  ¬WinsGoingFirst (-p) g')
  termination_by g
  decreasing_by exact Moves.Subposition.of_mem_moves (by assumption)

theorem winsGoingFirst_iff (g : G) (p : Player)
    : WinsGoingFirst p g ↔ IsEndLike p g ∨ (∃ g' ∈ moves p g, ¬WinsGoingFirst (-p) g') := by
  apply Iff.intro <;> intro h1
  · unfold WinsGoingFirst at h1
    obtain h1 | ⟨g', h2, h3⟩ := h1
    · exact Or.inl h1
    · apply Or.inr
      use g'
  · unfold WinsGoingFirst
    obtain h1 | ⟨g', h2⟩ := h1
    · exact Or.inl h1
    · apply Or.inr
      use g'

@[simp]
theorem winsGoingFirst_of_isEndLike {g : G} {p : Player} (h1 : IsEndLike p g) :
    WinsGoingFirst p g :=
  (winsGoingFirst_iff g p).mpr (Or.inl h1)

@[simp]
theorem winsGoingFirst_of_isEnd {g : G} {p : Player} (h1 : IsEnd p g) : WinsGoingFirst p g :=
  (winsGoingFirst_iff g p).mpr (Or.inl (isEndLike_of_isEnd h1))

theorem winsGoingFirst_of_moves {g : G} {p : Player}
    (h1 : ∃ g' ∈ Form.moves p g, ¬WinsGoingFirst (-p) g')
    : WinsGoingFirst p g := by
  rw [winsGoingFirst_iff]
  exact Or.inr h1

theorem winsGoingFirst_neg_iff (g : G) (p : Player) :
    (WinsGoingFirst p (-g)) ↔ (WinsGoingFirst (-p) g) := by
  constructor
    <;> intro h1
    <;> rw [winsGoingFirst_iff] at h1
    <;> apply Or.elim h1
    <;> intro h1
  · refine winsGoingFirst_of_isEndLike ?_
    rwa [<-IsEndLike.neg_iff_neg]
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [(winsGoingFirst_iff g (-p))]
    refine Or.inr ?_
    use -gp
    constructor
    · rwa [moves_neg, Set.mem_neg] at h1
    · rwa [neg_neg, winsGoingFirst_neg_iff]
  · refine winsGoingFirst_of_isEndLike ?_
    rwa [IsEndLike.neg_iff_neg]
  · obtain ⟨gp, h1, h2⟩ := h1
    rw [neg_neg] at h2
    rw [winsGoingFirst_iff]
    apply Or.inr
    use -gp
    constructor
    · rwa [moves_neg, Set.mem_neg, neg_neg]
    · rwa [winsGoingFirst_neg_iff, neg_neg]
termination_by birthday g
decreasing_by
  all_goals
    first
    | exact Form.birthday_lt_of_mem_moves h1
    | simpa only [Form.birthday_neg] using Form.birthday_lt_of_mem_moves h1

theorem not_winsGoingFirst_iff {g : G} {p : Player}
    : ¬WinsGoingFirst p g ↔ (¬Form.IsEndLike p g ∧ (∀ g' ∈ Form.moves p g,
      WinsGoingFirst (-p) g')) := by
  rw [winsGoingFirst_iff]
  simp only [not_or, not_exists, not_and, not_not]

theorem winsGoingFirst_zero (p : Player) : WinsGoingFirst p (0 : G) :=
  winsGoingFirst_of_isEnd isEnd_zero

open scoped Classical in
/-- The winning player when `p` starts from `g`. -/
@[expose] noncomputable def MiserePlayerOutcome : G → Player → Player :=
  fun g p => if WinsGoingFirst p g then p else -p

open scoped Classical in
/-- The four-outcome misère outcome of a form. -/
@[expose] noncomputable def MisereOutcome : G → Outcome :=
  fun g => Outcome.ofPlayers (MiserePlayerOutcome g .left) (MiserePlayerOutcome g .right)

@[simp]
theorem miserePlayerOutcome_eq_iff_winsGoingFirst {g : G} {p : Player}
    : (MiserePlayerOutcome g p = p) ↔ WinsGoingFirst p g := by
  apply Iff.intro <;> intro h1
  · simp only [MiserePlayerOutcome] at h1
    by_cases h2 : WinsGoingFirst p g
    · exact h2
    · simp [h2] at h1
      cases p <;> simp at h1
  · simp only [MiserePlayerOutcome, h1, ↓reduceIte]

theorem misereOutcome_L_iff_miserePlayerOutcome {g : G}
    : (MisereOutcome g = .L) ↔
      ((MiserePlayerOutcome g .left = .left) ∧ (MiserePlayerOutcome g .right = .left)) := by
  simp [MiserePlayerOutcome, MisereOutcome, Outcome.ofPlayers]
  by_cases h1 : WinsGoingFirst Player.left g
  <;> by_cases h2 : WinsGoingFirst Player.right g
  <;> simp [h1, h2]

theorem misereOutcome_N_iff_miserePlayerOutcome {g : G}
    : (MisereOutcome g = .N) ↔
      ((MiserePlayerOutcome g .left = .left) ∧ (MiserePlayerOutcome g .right = .right)) := by
  simp [MiserePlayerOutcome, MisereOutcome, Outcome.ofPlayers]
  by_cases h1 : WinsGoingFirst Player.left g
  <;> by_cases h2 : WinsGoingFirst Player.right g
  <;> simp [h1, h2]

theorem misereOutcome_P_iff_miserePlayerOutcome {g : G}
    : (MisereOutcome g = .P) ↔
      ((MiserePlayerOutcome g .left = .right) ∧ (MiserePlayerOutcome g .right = .left)) := by
  simp [MiserePlayerOutcome, MisereOutcome, Outcome.ofPlayers]
  by_cases h1 : WinsGoingFirst Player.left g
  <;> by_cases h2 : WinsGoingFirst Player.right g
  <;> simp [h1, h2]

theorem misereOutcome_R_iff_miserePlayerOutcome {g : G}
    : (MisereOutcome g = .R) ↔
      ((MiserePlayerOutcome g .left = .right) ∧ (MiserePlayerOutcome g .right = .right)) := by
  simp [MiserePlayerOutcome, MisereOutcome, Outcome.ofPlayers]
  by_cases h1 : WinsGoingFirst Player.left g
  <;> by_cases h2 : WinsGoingFirst Player.right g
  <;> simp [h1, h2]

@[simp]
theorem minsGoingFirst_left_of_misereOutcome_L {g : G}
    (h1 : MisereOutcome g = .L) : WinsGoingFirst .left g := by
  rw [misereOutcome_L_iff_miserePlayerOutcome, miserePlayerOutcome_eq_iff_winsGoingFirst] at h1
  exact h1.left

@[simp]
theorem winsGoingFirst_right_of_misereOutcome_R {g : G}
    (h1 : MisereOutcome g = .R) : WinsGoingFirst .right g := by
  rw [misereOutcome_R_iff_miserePlayerOutcome, miserePlayerOutcome_eq_iff_winsGoingFirst] at h1
  exact h1.right

private theorem conjugate_misereOutcome_of_ofPlayers_neg (g : G) :
    Outcome.ofPlayers
      (-(MiserePlayerOutcome g .right))
      (-(MiserePlayerOutcome g .left))
    = Outcome.Conjugate (MisereOutcome g) := by
  cases h1 : MiserePlayerOutcome g .right
  <;> cases h2 : MiserePlayerOutcome g .left
  all_goals simp only [h1, h2, Outcome.Conjugate, Outcome.ofPlayers, MisereOutcome]

@[simp]
theorem miserePlayerOutcome_neg_player_neg (g : G) (p : Player) :
    MiserePlayerOutcome (-g) p = -(MiserePlayerOutcome g (-p)) := by
  unfold MiserePlayerOutcome
  rw [winsGoingFirst_neg_iff g p, neg_neg]
  cases p
  · by_cases h1 : WinsGoingFirst .right g <;> simp [h1]
  · by_cases h1 : WinsGoingFirst .left g <;> simp [h1]

@[simp]
theorem misereOutcome_conjugate_neg (g : G) :
    (MisereOutcome g).Conjugate = MisereOutcome (-g) := by
  unfold Outcome.Conjugate
  cases h1 : MisereOutcome g
  all_goals
  · unfold MisereOutcome
    rw [miserePlayerOutcome_neg_player_neg, Player.neg_left,
        miserePlayerOutcome_neg_player_neg, Player.neg_right,
        conjugate_misereOutcome_of_ofPlayers_neg g, h1]
    rfl

theorem misereOutcome_ge_P_of_not_winsGoingFirst_right {g : G} (h1 : ¬WinsGoingFirst .right g) :
    MisereOutcome g ≥ Outcome.P := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
  by_cases h2 : WinsGoingFirst .left g
  all_goals simp only [h1, h2, reduceIte, ge_iff_le, le_refl, Outcome.L_ge]

theorem misereOutcome_le_N_of_winsGoingFirst_right {g : G} (h1 : WinsGoingFirst .right g) :
    MisereOutcome g ≤ Outcome.N := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
  by_cases h2 : WinsGoingFirst .left g <;> simp [h1, h2]

theorem not_winsGoingFirst_of_misereOutcome_P {g : G} {p : Player}
    (h1 : MisereOutcome g = Outcome.P) : ¬WinsGoingFirst p g := by
  intro h2
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h1
  by_cases h3 : WinsGoingFirst .left g
  <;> by_cases h4 : WinsGoingFirst .right g
  <;> simp only [h3, h4, reduceIte, reduceCtorEq, Player.neg_left, Player.neg_right] at h1
  cases p
  · exact h3 h2
  · exact h4 h2

theorem misereOutcome_P_of_miserePlayerOutcome_neg {g : G} (h1 : ∀ p,
  MiserePlayerOutcome g p = -p) :
    MisereOutcome g = Outcome.P := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [h1 .left, h1 .right]

@[simp]
theorem misereOutcome_eq_player_iff (g : G) (p : Player) :
    (MisereOutcome g = Outcome.ofPlayer p) ↔ (WinsGoingFirst p g ∧ ¬WinsGoingFirst (-p) g) := by
  constructor <;> intro h1
  · unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h1
    by_cases h2 : WinsGoingFirst .left g
      <;> by_cases h3 : WinsGoingFirst .right g
      <;> cases p
      <;> simp only [h2, h3, Outcome.ofPlayer, Player.neg_left, Player.neg_right, reduceIte,
                     reduceCtorEq] at h1
    · exact And.intro h2 h3
    · exact And.intro h3 h2
  · unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
    cases p
    <;> simp only [Player.neg_left, Player.neg_right] at h1
    <;> simp only [h1, reduceIte, Player.neg_right, Outcome.ofPlayer]

theorem misereOutcome_L_iff_winsGoingFirst {g : G} :
    (MisereOutcome g = .L) ↔ (WinsGoingFirst .left g ∧ ¬WinsGoingFirst .right g) := by
  have h1 : Outcome.L = Outcome.ofPlayer .left := by rfl
  have h2 : Player.right = -Player.left := rfl
  rw [h1, h2]
  exact misereOutcome_eq_player_iff g Player.left

theorem misereOutcome_R_iff_winsGoingFirst {g : G} :
    (MisereOutcome g = .R) ↔ (WinsGoingFirst .right g ∧ ¬WinsGoingFirst .left g) := by
  have h1 : Outcome.R = Outcome.ofPlayer .right := by rfl
  have h2 : Player.left = -Player.right := by rfl
  rw [h1, h2]
  exact misereOutcome_eq_player_iff g Player.right

theorem misereOutcome_P_iff_winsGoingFirst' {g : G} {p : Player} :
    (MisereOutcome g = .P) ↔ (¬WinsGoingFirst p g ∧ ¬WinsGoingFirst (-p) g) := by
  constructor
  · intro h1
    exact ⟨not_winsGoingFirst_of_misereOutcome_P h1, not_winsGoingFirst_of_misereOutcome_P h1⟩
  · intro ⟨h1, h2⟩
    unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome
    cases p
    all_goals
    · simp only [Player.neg_right, Player.neg_left] at h2
      simp only [h1, h2, Player.neg_left, Player.neg_right, Player.neg_right, reduceIte]

theorem misereOutcome_P_iff_winsGoingFirst {g : G} :
    (MisereOutcome g = .P) ↔ (¬WinsGoingFirst .right g ∧ ¬WinsGoingFirst .left g) := by
  rw [<-Player.neg_right]
  exact misereOutcome_P_iff_winsGoingFirst'

theorem misereOutcome_N_iff_winsGoingFirst {g : G} :
    (MisereOutcome g = .N) ↔ (WinsGoingFirst .left g ∧ WinsGoingFirst .right g) := by
  simp only [← miserePlayerOutcome_eq_iff_winsGoingFirst]
  cases h_left : MiserePlayerOutcome g .left
  <;> cases h_right : MiserePlayerOutcome g .right
  <;> simp [MisereOutcome, Outcome.ofPlayers, h_left, h_right]

/--
If `o(x) ≥ N` then Left wins going first on `x`.
-/
theorem winsGoingFirst_left_of_ge_N {x : G} (h : MisereOutcome x ≥ .N) :
    WinsGoingFirst .left x := by
  rcases hc : MisereOutcome x with _ | _ | _ | _
  · exact (misereOutcome_L_iff_winsGoingFirst.mp hc).1
  · exact (misereOutcome_N_iff_winsGoingFirst.mp hc).1
  · rw [hc] at h; exact absurd h (by decide)
  · rw [hc] at h; exact absurd h (by decide)

@[simp]
theorem miserePlayerOutcome_zero (p : Player) : MiserePlayerOutcome (0 : G) p = p := by
  unfold MiserePlayerOutcome
  simp only [isEnd_zero, winsGoingFirst_of_isEnd, ↓reduceIte]

@[simp]
theorem misereOutcome_zero_N : MisereOutcome (0 : G) = .N := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [miserePlayerOutcome_zero]

@[simp]
theorem misereOutcome_neg_R_iff_misereOutcome {g : G}
    : (MisereOutcome (-g) = .R) ↔ (MisereOutcome g = .L) := by
  unfold MisereOutcome Outcome.ofPlayers
  simp only [miserePlayerOutcome_neg_player_neg, Player.neg_left, Player.neg_right]
  cases MiserePlayerOutcome g Player.right
  <;> cases MiserePlayerOutcome g Player.left
  <;> simp

@[simp]
theorem misereOutcome_neg_L_iff_misereOutcome {g : G}
    : (MisereOutcome (-g) = .L) ↔ (MisereOutcome g = .R) := by
  rw [<-neg_neg g, misereOutcome_neg_R_iff_misereOutcome, neg_neg]

@[simp]
theorem misereOutcome_neg_N_iff_misereOutcome {g : G}
    : (MisereOutcome (-g) = .N) ↔ (MisereOutcome g = .N) := by
  rw [← misereOutcome_conjugate_neg]
  cases MisereOutcome g <;> simp [Outcome.Conjugate]

theorem winsGoingFirst_left_of_move_misereOutcome_P {g gl : G} (h1 : gl ∈ moves .left g)
    (h2 : MisereOutcome gl = Outcome.P) : WinsGoingFirst .left g := by
  unfold MisereOutcome Outcome.ofPlayers MiserePlayerOutcome at h2
  by_cases h3 : WinsGoingFirst .left gl
    <;> by_cases h4 : WinsGoingFirst .right gl
    <;> simp only [h3, h4, reduceIte, reduceCtorEq] at h2
  apply winsGoingFirst_of_moves
  simp only [Player.neg_left]
  use gl

theorem winsGoingFirst_add_of_isEndLike {g h : G} {p : Player} (h1 : IsEndLike p g)
    (h2 : IsEndLike p h) : WinsGoingFirst p (g + h) :=
  winsGoingFirst_of_isEndLike (IsEndLike.add_iff.mpr ⟨h1, h2⟩)

theorem winsGoingFirst_add_of_isEnd {g h : G} {p : Player} (h1 : IsEnd p g)
    (h2 : IsEnd p h) : WinsGoingFirst p (g + h) :=
  winsGoingFirst_of_isEnd (IsEnd.add_iff.mpr ⟨h1, h2⟩)

theorem miserePlayerOutcome_of_leftMoves {g gl : G} (h1 : gl ∈ moves .left g)
    (h2 : MiserePlayerOutcome gl .right = .left) : MiserePlayerOutcome g .left = .left := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst, winsGoingFirst_iff]
  apply Or.inr
  use gl
  apply And.intro h1
  simp only [Player.neg_left, Player.right_le, Player.le_right_eq]
  unfold MiserePlayerOutcome at h2
  simp only [Player.le_left, Player.neg_right, Player.le_left_eq, ite_eq_right_iff,
             reduceCtorEq, imp_false] at h2
  exact h2

theorem miserePlayerOutcome_of_rightMoves {g gr : G} (h1 : gr ∈ moves .right g)
    (h2 : MiserePlayerOutcome gr .left = .right) : MiserePlayerOutcome g .right = .right := by
  rw [miserePlayerOutcome_eq_iff_winsGoingFirst, winsGoingFirst_iff]
  refine Or.inr ⟨gr, h1, ?_⟩
  intro h3
  have h4 : MiserePlayerOutcome gr .left = .left := by
    rwa [miserePlayerOutcome_eq_iff_winsGoingFirst]
  rw [h4] at h2
  cases h2

theorem misereOutcome_ge_iff_miserePlayerOutcome_ge {g h : G}
    : MisereOutcome g ≥ MisereOutcome h ↔ (∀ p,
      MiserePlayerOutcome g p ≥ MiserePlayerOutcome h p) := by
  cases hgl : MiserePlayerOutcome g .left <;>
    cases hgr : MiserePlayerOutcome g .right <;>
    cases hhl : MiserePlayerOutcome h .left <;>
    cases hhr : MiserePlayerOutcome h .right <;>
    simp [MisereOutcome, Outcome.ofPlayers, hgl, hgr, hhl, hhr, LE.le, LT.lt]

/--
Restricted misère equivalence, working modulo a set `A`.
-/
@[expose] def MisereEQ (A : G → Prop) (g h : G) : Prop :=
  ∀ (x : G), A x → MisereOutcome (g + x) = MisereOutcome (h + x)

@[inherit_doc MisereEQ]
syntax (name := misereEQ) term:51 " =m " term:max term:51 : term

macro_rules (kind := misereEQ)
  | `($x =m $u $y) => `(MisereEQ $u $x $y)

recommended_spelling "misereEQ" for "=m" in [MisereEQ, misereEQ]

open Lean PrettyPrinter Delaborator SubExpr

/-- Delaborator for restricted misère equivalence notation. -/
@[app_delab MisereEQ]
meta def delabMisereEQ : Delab := do
  let y ← withAppArg delab
  let x ← withAppFn do withAppArg delab
  let u ← withAppFn do withAppFn do withAppArg delab
  `($x =m $u $y)

theorem MisereEQ.symm {A : G → Prop} {g h : G} (h1 : g =m A h) : h =m A g := by
  intro x h2
  have h3 := h1 x h2
  exact Eq.symm h3

theorem MisereEQ.trans {A : G → Prop} {g h k : G} (h1 : g =m A h) (h2 : h =m A k) :
    g =m A k := by
  unfold MisereEQ at *
  intro x h3
  exact cast (congrArg (Eq (MisereOutcome (g + x))) (h2 x h3)) (h1 x h3)

/--
The restricted misère preorder, working modulo a set `A`.
-/
@[expose] def MisereGE (A : G → Prop) (g h : G) : Prop :=
  ∀ x, (A x → MisereOutcome (g + x) ≥ MisereOutcome (h + x))

@[inherit_doc MisereGE]
syntax (name := misereGE) term:51 " ≥m " term:max term:51 : term

macro_rules (kind := misereGE)
  | `($x ≥m $u $y) => `(MisereGE $u $x $y)

recommended_spelling "misereGE" for "≥m" in [MisereGE, misereGE]

/-- Delaborator for restricted misère preorder notation. -/
@[app_delab MisereGE]
meta def delabMisereGE : Delab := do
  let y ← withAppArg delab
  let x ← withAppFn do withAppArg delab
  let u ← withAppFn do withAppFn do withAppArg delab
  `($x ≥m $u $y)

theorem MisereEq.of_antisymm {A : G → Prop} {g h : G} (h1 : g ≥m A h) (h2 : h ≥m A g) :
    g =m A h := fun x h3 =>
  PartialOrder.le_antisymm (MisereOutcome (g + x)) (MisereOutcome (h + x)) (h2 x h3) (h1 x h3)

theorem MisereGE.trans {A : G → Prop} {g h k : G} (h1 : g ≥m A h) (h2 : h ≥m A k) :
    g ≥m A k := by
  unfold MisereGE at *
  intro x h3
  exact le_trans (h2 x h3) (h1 x h3)

theorem misereGE_rw_left {A : G → Prop} {a b c : G} (h2 : b =m A c) (h1 : b ≥m A a) : c ≥m A a := by
  unfold MisereGE at h1 ⊢
  unfold MisereEQ at h2
  intro x hx
  rw [<-h2 x hx]
  exact h1 x hx

theorem misereGE_rw_right {A : G → Prop} {a b c : G} (h2 : b =m A c) (h1 : a ≥m A c) :
    a ≥m A b := by
  unfold MisereGE at h1 ⊢
  unfold MisereEQ at h2
  intro x hx
  rw [h2 x hx]
  exact h1 x hx

theorem misereGE_of_misereEQ {A : G → Prop} {g h : G} (h1 : g =m A h) : g ≥m A h := by
  intro x hx
  have := h1 x hx
  exact Std.le_of_eq (Eq.symm this)

theorem misereGE_of_subset (U : G → Prop) {V : G → Prop}
    (h_v_subset_u : ∀ g, V g → U g) (g h : G) (h2 : g ≥m U h) : g ≥m V h := by
  unfold MisereGE at h2 ⊢
  intro x hv
  exact h2 x (h_v_subset_u x hv)

/--
Adding a fixed element `c ∈ A` on the right preserves the restricted misère
inequality.
-/
theorem misereGE_add_right {A : G → Prop} [ClosedUnderAdd A] {g h c : G}
    (hc : A c) (h1 : g ≥m A h) : (g + c) ≥m A (h + c) := by
  intro x hx
  have hcx : A (c + x) := ClosedUnderAdd.has_add c x hc hx
  have := h1 (c + x) hcx
  rwa [← add_assoc, ← add_assoc] at this

/--
Adding a fixed element `c ∈ A` on the right preserves the restricted misère
equivalence.
-/
theorem misereEQ_add_right {A : G → Prop} [ClosedUnderAdd A] {g h c : G}
    (hc : A c) (h1 : g =m A h) : (g + c) =m A (h + c) := by
  intro x hx
  have hcx : A (c + x) := ClosedUnderAdd.has_add c x hc hx
  have := h1 (c + x) hcx
  rwa [← add_assoc, ← add_assoc] at this

/--
Adding a fixed element `c ∈ A` on the left preserves the restricted misère
equivalence.
-/
theorem misereEQ_add_left {A : G → Prop} [ClosedUnderAdd A] {g h c : G}
    (hc : A c) (h1 : g =m A h) : (c + g) =m A (c + h) := by
  have := misereEQ_add_right hc h1
  intro x hx
  have h2 := this x hx
  rwa [add_comm c g, add_comm c h]

@[simp]
theorem MisereGE.refl {A : G → Prop} (g : G) : g ≥m A g := by
  unfold MisereGE
  intro x h3
  exact le_refl MisereOutcome (g + x)

theorem not_misereEQ_of_not_misereGE {A : G → Prop} {g h : G} (h1 : ¬(g ≥m A h)) :
    ¬(g =m A h) := by
  simp only [MisereGE, ge_iff_le, not_forall] at h1
  obtain ⟨x, ⟨h1, h2⟩⟩ := h1
  simp only [MisereEQ, not_forall]
  use x
  use h1
  exact Ne.symm (ne_of_not_le h2)

private theorem ClosedUnderNeg.not_ge_neg_iff.aux {A : G → Prop} [ClosedUnderNeg A]
    {g h : G} (h1 : g ≥m A h) : (-h) ≥m A (-g) := by
  unfold MisereGE at *
  intro x h0
  have h2 := h1 (-x) (ClosedUnderNeg.neg_iff.mpr h0)
  have h4 : MisereOutcome (-h + x) = (MisereOutcome (-h + x)).Conjugate.Conjugate :=
    Eq.symm Outcome.conjugate_conjugate_eq_self
  have h5 : (MisereOutcome (-h + x)).Conjugate.Conjugate = (MisereOutcome (h + (-x))).Conjugate :=
    by simp only [misereOutcome_conjugate_neg, neg_add_rev, neg_neg, add_comm]
  rw [h4, h5]
  have h6 : (MisereOutcome (g + (-x))).Conjugate = MisereOutcome (-g + x) := by
    simp only [misereOutcome_conjugate_neg, neg_add_rev, neg_neg, add_comm]
  rw [<-h6]
  apply Outcome.outcome_ge_conjugate_le
  exact h2

@[simp]
theorem ClosedUnderNeg.neg_ge_neg_iff {A : G → Prop} [ClosedUnderNeg A]
    (g h : G) : (-h) ≥m A (-g) ↔ g ≥m A h := by
  constructor <;> intro h1
  · have h2 := not_ge_neg_iff.aux h1
    simp only [neg_neg] at h2
    exact h2
  · exact not_ge_neg_iff.aux h1

private theorem misereEQ_neg' {A : G → Prop} [ClosedUnderNeg A] {g h : G}
    (h1 : MisereEQ A (-g) (-h)) :
    g =m A h := by
  apply MisereEq.of_antisymm
  · have := misereGE_of_misereEQ (MisereEQ.symm h1)
    rwa [<-ClosedUnderNeg.neg_ge_neg_iff, neg_neg, neg_neg] at this
  · have := misereGE_of_misereEQ h1
    rwa [<-ClosedUnderNeg.neg_ge_neg_iff, neg_neg, neg_neg] at this

theorem misereEQ_neg_iff {A : G → Prop} [ClosedUnderNeg A] {g h : G} :
    ((-g) =m A (-h)) ↔ (g =m A h) := by
  constructor <;> intro h1
  · exact misereEQ_neg' h1
  · rw [<-neg_neg g, <-neg_neg h] at h1
    exact misereEQ_neg' h1

@[simp]
theorem winsGoingFirst_left_intCast_iff (n : ℤ) : WinsGoingFirst .left (n : G) ↔ n ≤ 0 := by
  have not_winsGoingFirst_left_natCast_pos {n : ℕ} (h_pos : 0 < n) :
      ¬WinsGoingFirst .left (n : G) := by
    rw [not_winsGoingFirst_iff]
    constructor
    · simp [Nat.ne_zero_iff_zero_lt.mpr h_pos]
    · intro g' h_g'_mem
      simp only [leftMoves_eq_natCast_zero_lt h_pos] at h_g'_mem
      subst h_g'_mem
      match (n - 1) with
      | 0 =>
        norm_cast
        exact winsGoingFirst_zero _
      | k + 1 =>
        apply winsGoingFirst_of_isEndLike
        rw [natCast_isEndLike_iff]
        exact succ_nat_end_right.mpr rfl
  constructor <;> intro h1
  · match n with
    | .ofNat n =>
      simp only [Int.ofNat_eq_natCast] at h1
      have : n = 0 := by
        by_contra h2
        absurd h1
        apply not_winsGoingFirst_left_natCast_pos
        exact Nat.ne_zero_iff_zero_lt.mp h2
      exact Int.toNat_eq_zero.mp this
    | .negSucc n =>
      exact Int.negSucc_le_zero n
  · match n with
    | .ofNat n =>
      simp only [Int.ofNat_eq_natCast, Int.natCast_nonpos_iff] at h1
      subst h1
      simp only [Int.ofNat_eq_natCast, Int.cast_ofNat_Int, Form.intCast_ofNat, Nat.cast_zero,
                 isEnd_zero, winsGoingFirst_of_isEnd]
    | .negSucc n =>
      simp only [Form.intCast_negSucc, neg_add_rev, IsEndLike.add_iff, winsGoingFirst_of_isEndLike,
                 IsEndLike.neg_iff_neg, Player.neg_left, Player.right_le, Player.le_right_eq,
                 one_isEndLike_right, natCast_isEndLike_iff, natCast_isEnd_right, and_self]

@[simp]
theorem winsGoingFirst_left_natCast_iff (n : ℕ) : WinsGoingFirst .left (n : G) ↔ n = 0 := by
  rw [<-Form.intCast_nat, winsGoingFirst_left_intCast_iff]
  exact Int.natCast_nonpos_iff

@[simp]
theorem winsGoingFirst_right_intCast_iff (n : ℤ) : WinsGoingFirst .right (n : G) ↔ 0 ≤ n := by
  constructor <;> intro h1
  · match n with
    | .ofNat n => simp
    | .negSucc n =>
      absurd h1
      rw [not_winsGoingFirst_iff]
      simp only [Form.intCast_negSucc, neg_add_rev, IsEndLike.add_iff, IsEndLike.neg_iff_neg,
        Player.neg_right, not_isEndLike_left_one, natCast_isEndLike_iff,
        isEnd_left_natCast_iff, false_and, not_false_eq_true, moves_add, moves_neg,
        leftMoves_one, Set.neg_singleton, neg_zero, Set.image_singleton, zero_add,
        Set.singleton_union, Set.mem_insert_iff, Set.mem_image, Set.mem_neg,
        Set.exists_neg_mem, forall_eq_or_imp, Player.neg_left, isEnd_right_natCast,
        winsGoingFirst_of_isEndLike, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        true_and]
      intro g h_g
      match n with
      | 0 => simp at h_g
      | n + 1 =>
        simp only [Nat.cast_add, Nat.cast_one, leftMoves_natCast_succ, Set.mem_singleton_iff] at h_g
        subst h_g
        apply winsGoingFirst_of_isEndLike
        simp
  · match n with
    | .ofNat n => simp

theorem winsGoingFirst_right_natCast (n : ℕ) : WinsGoingFirst .right (n : G) := by
  rw [<-Form.intCast_nat, winsGoingFirst_right_intCast_iff]
  exact Int.natCast_nonneg n

@[simp]
theorem not_winsGoingFirst_left_one : ¬WinsGoingFirst .left (1 : G) := by
  rw [<-Form.intCast_one, winsGoingFirst_left_intCast_iff]
  omega

theorem winsGoingFirst_right_one : WinsGoingFirst .right (1 : G) := by
  rw [<-Form.natCast_one]
  simp only [Nat.cast_one, one_isEndLike_right, winsGoingFirst_of_isEndLike]

@[simp]
theorem one_misereOutcome_R : MisereOutcome (1 : G) = .R := by
  simp [misereOutcome_R_iff_winsGoingFirst]

@[simp]
theorem misereOutcome_R_intCast_iff (n : ℤ) : MisereOutcome (n : G) = .R ↔ 0 < n := by
  rw [misereOutcome_R_iff_winsGoingFirst]
  constructor <;> intro h
  · exact not_le.mp ((winsGoingFirst_left_intCast_iff n).not.mp h.right)
  · constructor
    · exact (winsGoingFirst_right_intCast_iff n).mpr h.le
    · exact (winsGoingFirst_left_intCast_iff n).not.mpr (not_le.mpr h)

@[simp]
theorem misereOutcome_R_natCast_iff (n : ℕ) : MisereOutcome (n : G) = .R ↔ 0 < n := by
  rw [<-Form.intCast_nat, misereOutcome_R_intCast_iff]
  simp only [Int.natCast_pos]

@[simp]
theorem misereOutcome_L_intCast_iff (n : ℤ) : MisereOutcome (n : G) = .L ↔ n < 0 := by
  rw [misereOutcome_L_iff_winsGoingFirst]
  constructor <;> intro h
  · exact not_le.mp ((winsGoingFirst_right_intCast_iff n).not.mp h.right)
  · constructor
    · exact (winsGoingFirst_left_intCast_iff n).mpr h.le
    · exact (winsGoingFirst_right_intCast_iff n).not.mpr (not_le.mpr h)

@[simp]
theorem misereOutcome_L_natCast (n : ℕ) : ¬MisereOutcome (n : G) = .L := by
  rw [<-Form.intCast_nat, misereOutcome_L_intCast_iff]
  simp only [not_lt, Int.natCast_nonneg]

@[simp]
theorem misereOutcome_N_intCast_iff (n : ℤ) : MisereOutcome (n : G) = .N ↔ n = 0 := by
  rw [misereOutcome_N_iff_winsGoingFirst]
  constructor <;> intro h
  · have h1 := (winsGoingFirst_left_intCast_iff (G := G) n).mp h.left
    have h2 := (winsGoingFirst_right_intCast_iff (G := G) n).mp h.right
    exact Eq.symm (Int.le_antisymm h2 h1)
  · constructor
    · exact (winsGoingFirst_left_intCast_iff n).mpr h.le
    · exact (winsGoingFirst_right_intCast_iff (G := G) n).mpr (Int.le_of_eq (Eq.symm h))

@[simp]
theorem misereOutcome_N_natCast_iff (n : ℕ) : MisereOutcome (n : G) = .N ↔ n = 0 := by
  rw [<-Form.intCast_nat, misereOutcome_N_intCast_iff]
  simp only [Int.natCast_eq_zero]

@[simp]
theorem misereOutcome_P_intCast (n : ℤ) : ¬MisereOutcome (n : G) = .P := by
  apply Or.elim3 (Int.lt_trichotomy n 0) <;> intro h
  · rw [<-misereOutcome_L_intCast_iff (G := G)] at h
    rw [h]
    decide
  · rw [<-misereOutcome_N_intCast_iff (G := G)] at h
    rw [h]
    decide
  · rw [<-misereOutcome_R_intCast_iff (G := G)] at h
    rw [h]
    decide

@[simp]
theorem misereOutcome_P_natCast (n : ℕ) : ¬MisereOutcome (n : G) = .P := by
  rw [<-Form.intCast_nat]
  exact misereOutcome_P_intCast (G := G) _

end Form.Misere.Outcome

end

end MisereGames
