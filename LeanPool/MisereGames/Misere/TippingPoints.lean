/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import LeanPool.MisereGames.Form.Misere.Outcome
public import LeanPool.MisereGames.Form.Short

/-!
Misere combinatorial games.
-/

namespace MisereGames

open Form
open Form.Misere.Outcome

universe u

public section

mutual

private theorem right_wins_of_birthday_le (g : GameForm) (b : ℕ) (h1 : birthday g ≤ b) :
    WinsGoingFirst .right (g + b) := by
  by_cases h2 : IsEnd .right g
  · exact winsGoingFirst_add_of_isEnd h2 (natCast_isEnd_right b)
  · obtain ⟨gr, h3⟩ := not_isEnd_exists_move h2
    refine winsGoingFirst_of_moves ?_
    refine ⟨gr + b, Form.add_right_mem_moves_add h3 b, ?_⟩
    exact not_left_wins_of_birthday_lt gr b ((Form.birthday_lt_of_mem_moves h3).trans_le h1)
termination_by g
decreasing_by form_wf

private theorem not_left_wins_of_birthday_lt (g : GameForm) (b : ℕ) (h1 : birthday g < b) :
    ¬WinsGoingFirst .left (g + b) := by
  have hbpos : 0 < b := by
    by_contra hb
    have : b = 0 := Nat.eq_zero_of_not_pos hb
    subst this
    simp at h1
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hbpos)
  rw [not_winsGoingFirst_iff]
  constructor
  · intro h2
    rw [GameForm.isEndLike_iff_isEnd] at h2
    have h4 : ¬IsEnd .left ((k + 1 : ℕ) : GameForm.{u_1}) := by simp
    exact h4 (by simpa [hk] using (IsEnd.add_iff.mp h2).right)
  · intro gl h2
    rw [moves_add] at h2
    rcases h2 with ⟨gl', h3, rfl⟩ | ⟨bl, h3, rfl⟩
    · exact right_wins_of_birthday_le gl' b (((Form.birthday_lt_of_mem_moves h3).trans h1).le)
    · have h6 : bl = (k : GameForm) := by
        simpa [hk, Nat.succ_eq_add_one] using h3
      rw [h6]
      have h7 : birthday g ≤ (k : ℕ) := by
        apply Order.lt_add_one_iff.mp
        simpa [hk, Nat.cast_add, Nat.cast_one] using h1
      by_cases h8 : IsEnd .right g
      · exact winsGoingFirst_add_of_isEnd h8 (natCast_isEnd_right k)
      · obtain ⟨gr, h9⟩ := not_isEnd_exists_move h8
        refine winsGoingFirst_of_moves ?_
        refine ⟨gr + k, Form.add_right_mem_moves_add h9 k, ?_⟩
        exact not_left_wins_of_birthday_lt gr k ((Form.birthday_lt_of_mem_moves h9).trans_le h7)
termination_by g
decreasing_by form_wf

end

private theorem add_gt_birthday_R (g : GameForm) (b : ℕ) (h1 : birthday g < b) :
    MisereOutcome (g + b) = .R := by
  exact misereOutcome_R_iff_winsGoingFirst.mpr
    ⟨right_wins_of_birthday_le g b h1.le, not_left_wins_of_birthday_lt g b h1⟩

theorem _root_.MisereGames.add_birthday_plus_one_R
    (g : GameForm) (b : ℕ) (h1 : birthday g = b) :
    MisereOutcome (g + (b + (1 : ℕ))) = .R := by
  have h2 : (b : NatOrdinal) < (b + 1 : ℕ) := by
    simp
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using add_gt_birthday_R g (b + 1) (h1 ▸ h2)

theorem _root_.MisereGames.add_neg_birthday_plus_one_L
    (g : GameForm) (b : ℕ) (h1 : birthday g = b) :
    MisereOutcome (g + (-(b + (1 : ℕ)))) = .L := by
  have h2 := congrArg Outcome.Conjugate
    (add_birthday_plus_one_R (-g) b (by simpa [Form.birthday_neg] using h1))
  rw [misereOutcome_conjugate_neg] at h2
  simpa [Outcome.Conjugate, neg_add_rev, add_comm, add_left_comm, add_assoc] using h2

theorem _root_.MisereGames.RTippingPoint.aux {g : GameForm} (h1 : IsShort g) :
    ∃ (n : ℕ), MisereOutcome (g + n) = .R := by
  let ⟨b, h2⟩ := GameForm.short_iff_birthday_nat.mp h1
  use (b + 1)
  rw [Nat.cast_add]
  exact add_birthday_plus_one_R g b h2

theorem _root_.MisereGames.LTippingPoint.aux {g : GameForm} (h1 : IsShort g) :
    ∃ (n : ℕ), MisereOutcome (g + (-n)) = .L := by
  let ⟨b, h2⟩ := GameForm.short_iff_birthday_nat.mp h1
  use (b + 1)
  rw [Nat.cast_add]
  exact add_neg_birthday_plus_one_L g b h2

private theorem left_wins_second_implies_left_wins_first_add_one {g : GameForm}
    (h1 : ¬WinsGoingFirst .right g) : WinsGoingFirst .left (g + 1) := by
  refine winsGoingFirst_of_moves ?_
  refine ⟨g, ?_, ?_⟩
  · rw [moves_add, leftMoves_one]
    right
    refine ⟨0, by simp, by simp⟩
  · simpa [Player.neg_left] using h1

private theorem exists_add_nat_N_of_not_R {g : GameForm} (h0 : IsShort g) (h1 :
    MisereOutcome g ≠ .R) :
    ∃ n : ℕ, MisereOutcome (g + n) = .N := by
  let hR : ∃ n : ℕ, MisereOutcome (g + n) = .R := RTippingPoint.aux h0
  let r : ℕ := Nat.find hR
  have hrR : MisereOutcome (g + r) = .R := Nat.find_spec hR
  have hrpos : 0 < r := by
    by_contra h2
    have h3 : r = 0 := Nat.eq_zero_of_not_pos h2
    exact h1 (by simpa [r, h3, Nat.cast_zero, add_zero] using hrR)
  let n : ℕ := r - 1
  have hnsucc : n + 1 = r := by
    dsimp [n]
    omega
  have hnlt : n < r := by
    omega
  have hnotR_n : MisereOutcome (g + n) ≠ .R := by
    exact Nat.find_min hR (by simpa [r] using hnlt)
  have hnotLeft_r : ¬WinsGoingFirst .left (g + r) := (misereOutcome_R_iff_winsGoingFirst.mp hrR).2
  have hright_n : WinsGoingFirst .right (g + n) := by
    by_contra h2
    have h3 : WinsGoingFirst .left ((g + n) + 1) :=
      left_wins_second_implies_left_wins_first_add_one h2
    have h4 : WinsGoingFirst .left (g + (n + 1 : ℕ)) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using h3
    exact hnotLeft_r (by simpa [hnsucc] using h4)
  refine ⟨n, ?_⟩
  cases hn : MisereOutcome (g + n)
  · exact False.elim ((misereOutcome_L_iff_winsGoingFirst.mp hn).right hright_n)
  · simp
  · exact False.elim ((misereOutcome_P_iff_winsGoingFirst.mp hn).left hright_n)
  · exact False.elim (hnotR_n hn)

theorem _root_.MisereGames.NTippingPoint.aux {g : GameForm} (h1 : IsShort g) :
    ∃ (n : ℕ), MisereOutcome (g + n) = .N ∨ MisereOutcome (g + (-n)) = .N := by
  by_cases h2 : MisereOutcome g = .R
  · have h3 : MisereOutcome (-g) = .L := by simp [h2]
    obtain ⟨n, hn⟩ := exists_add_nat_N_of_not_R (Short.neg h1) (by simp [h3])
    refine ⟨n, Or.inr ?_⟩
    have h4 : (MisereOutcome (-g + n)).Conjugate = .N := by
      rw [hn]
      rfl
    simpa [misereOutcome_conjugate_neg, neg_add_rev, add_comm, add_left_comm, add_assoc] using h4
  · obtain ⟨n, hn⟩ := exists_add_nat_N_of_not_R h1 h2
    exact ⟨n, Or.inl hn⟩

/-- The least absolute integer shift at which a short game has outcome `N`. -/
noncomputable def _root_.MisereGames.NTippingPoint {g : GameForm} (h1 : IsShort g) : ℕ :=
  Nat.find (NTippingPoint.aux h1)

/--
The defining property of the $\mathscr{N}$-tipping point: at
$\operatorname{n}(G)$ itself, either the positive or the negative shift has
outcome $\mathscr{N}$.
-/
theorem _root_.MisereGames.NTippingPoint_spec {g : GameForm} (h1 : IsShort g) :
    MisereOutcome (g + (NTippingPoint h1 : GameForm)) = .N ∨
      MisereOutcome (g + (-(NTippingPoint h1 : GameForm))) = .N :=
  Nat.find_spec (NTippingPoint.aux h1)

/--
Minimality of the $\mathscr{N}$-tipping point: below $\operatorname{n}(G)$,
neither the positive nor the negative shift has outcome $\mathscr{N}$.
-/
theorem _root_.MisereGames.NTippingPoint_min
    {g : GameForm} (h1 : IsShort g) {k : ℕ} (hk : k < NTippingPoint h1) :
    ¬ (MisereOutcome (g + (k : GameForm)) = .N ∨
        MisereOutcome (g + (-(k : GameForm))) = .N) :=
  Nat.find_min (NTippingPoint.aux h1) hk

/--
$\operatorname{n}(-G) = \operatorname{n}(G)$
-/
@[simp]
theorem _root_.MisereGames.NTippingPoint.neg {g : GameForm} (h1 : IsShort g) :
    NTippingPoint (Short.neg h1) = NTippingPoint h1 := by
  unfold NTippingPoint
  apply Nat.find_congr'
  intro n
  have hconjN : ∀ x : GameForm, MisereOutcome x = .N ↔ MisereOutcome (-x) = .N := by
    intro x
    constructor <;> intro hx
    · have : (MisereOutcome x).Conjugate = .N := by rw [hx]; rfl
      simpa [misereOutcome_conjugate_neg] using this
    · have : (MisereOutcome (-x)).Conjugate = .N := by rw [hx]; rfl
      simpa [misereOutcome_conjugate_neg] using this
  have h1 : MisereOutcome (g + n) = .N ↔ MisereOutcome (-g + (-n)) = .N := by
    simpa [neg_add_rev, add_comm, add_left_comm, add_assoc] using hconjN (g + n)
  have h2 : MisereOutcome (g + (-n)) = .N ↔ MisereOutcome (-g + n) = .N := by
    simpa [neg_add_rev, add_comm, add_left_comm, add_assoc] using hconjN (g + (-n))
  constructor <;> intro h
  · simpa [or_comm] using Or.imp h2.mpr h1.mpr h
  · simpa [or_comm] using Or.imp h1.mp h2.mp h

/-- The least nonnegative shift at which a short game has outcome `R`. -/
noncomputable def _root_.MisereGames.RTippingPoint {g : GameForm} (h1 : IsShort g) : ℕ :=
  Nat.find (RTippingPoint.aux h1)

theorem _root_.MisereGames.RTippingPoint_iff {g : GameForm} (h1 : IsShort g) (n : ℕ) :
    (RTippingPoint h1 = n)
     ↔ ((MisereOutcome (g + n) = .R) ∧ ∀ (x : ℕ), MisereOutcome (g + x) = .R → n ≤ x) := by
  unfold RTippingPoint
  rw [Nat.find_eq_iff]
  constructor <;> intro ⟨h2, h3⟩ <;> apply And.intro h2 <;> intro x h4
  · exact Nat.le_of_not_lt fun h5 ↦ h3 x h5 h4
  · intro h5
    have h6 := h3 x h5
    omega

/-- The least nonnegative negative shift at which a short game has outcome `L`. -/
noncomputable def _root_.MisereGames.LTippingPoint {g : GameForm} (h1 : IsShort g) : ℕ :=
  Nat.find (LTippingPoint.aux h1)

theorem _root_.MisereGames.LTippingPoint_iff {g : GameForm} (h1 : IsShort g) (n : ℕ) :
    (LTippingPoint h1 = n)
     ↔ ((MisereOutcome (g + (-n)) = .L) ∧ ∀ (x : ℕ), MisereOutcome (g + (-x)) = .L → n ≤ x) := by
  unfold LTippingPoint
  rw [Nat.find_eq_iff]
  constructor <;> intro ⟨h2, h3⟩ <;> apply And.intro h2 <;> intro x h4
  · exact Nat.le_of_not_lt fun h5 ↦ h3 x h5 h4
  · intro h5
    have h6 := h3 x h5
    omega

theorem _root_.MisereGames.LTippingPoint_spec {g : GameForm} (h1 : IsShort g) :
    MisereOutcome (g + (-(LTippingPoint h1 : GameForm))) = .L :=
  Nat.find_spec (LTippingPoint.aux h1)

/--
Negation sends the $\mathscr{R}$-tipping point to the $\mathscr{L}$-tipping
point: $\operatorname{r}(-G) = \operatorname{l}(G)$.
-/
theorem _root_.MisereGames.RTippingPoint_neg {g : GameForm} (hsg : IsShort g) :
    RTippingPoint (Short.neg hsg) = LTippingPoint hsg := by
  apply (RTippingPoint_iff (Short.neg hsg) (LTippingPoint hsg)).mpr
  constructor
  · have : -g + ↑ (LTippingPoint hsg) = -( g + -↑ (LTippingPoint hsg)) := by rw [neg_add, neg_neg]
    have h_neg :
        MisereOutcome (-g + (LTippingPoint hsg : GameForm))
        = (MisereOutcome (g + (-(LTippingPoint hsg : GameForm)))).Conjugate := by
      rw [this]
      exact (misereOutcome_conjugate_neg _).symm
    have := LTippingPoint_iff hsg ( LTippingPoint hsg ) |>.1 rfl
    simp_all only [neg_add_rev, neg_neg]
    decide
  · intro x hx
    have h_conj : MisereOutcome (g + (-(x : GameForm))) = .L := by
      have : -g + ↑x = - ( g + -↑x ) := by rw [neg_add, neg_neg]
      have h_neg : MisereOutcome (-g + x) = (MisereOutcome (g + (-x))).Conjugate := by
        rw [this, misereOutcome_conjugate_neg]
      cases h : MisereOutcome (g + -↑x) <;> simp_all +decide only [Outcome.Conjugate]
    exact (LTippingPoint_iff hsg (LTippingPoint hsg)).mp rfl |>.2 _ h_conj

/--
Negation sends the $\mathscr{L}$-tipping point to the $\mathscr{R}$-tipping
point: $\operatorname{l}(-G) = \operatorname{r}(G)$.
-/
theorem _root_.MisereGames.LTippingPoint_neg {g : GameForm} (hsg : IsShort g) :
    LTippingPoint (Short.neg hsg) = RTippingPoint hsg := by
  have : RTippingPoint hsg = RTippingPoint (ClosedUnderNeg.neg_of (ClosedUnderNeg.neg_of hsg)) := by
    simp only [neg_neg]
  rw [this, RTippingPoint_neg]

/--
The $\mathscr{R}$-tipping point is a witness: $\operatorname{o}(G +
\operatorname{r}(G)) = \mathscr{R}$.
-/
theorem _root_.MisereGames.misereOutcome_add_RTippingPoint_R {g : GameForm} (hsg : IsShort g) :
    MisereOutcome (g + (RTippingPoint hsg : GameForm)) = .R :=
  ((RTippingPoint_iff hsg (RTippingPoint hsg)).mp rfl).left

/--
The $\mathscr{L}$-tipping point is a witness: $\operatorname{o}(G -
\operatorname{l}(G)) = \mathscr{L}$.
-/
theorem _root_.MisereGames.misereOutcome_add_neg_LTippingPoint_L
    {g : GameForm} (hsg : IsShort g) :
    MisereOutcome (g + (-(LTippingPoint hsg : GameForm))) = .L :=
  ((LTippingPoint_iff hsg (LTippingPoint hsg)).mp rfl).left

/--
Minimality of the $\mathscr{R}$-tipping point: below $\operatorname{r}(G)$, the
positive shift is not $\mathscr{R}$.
-/
theorem _root_.MisereGames.misereOutcome_add_nat_ne_R_of_lt_RTippingPoint
    {g : GameForm} (hsg : IsShort g)
    {k : ℕ} (hk : k < RTippingPoint hsg) :
    MisereOutcome (g + (k : GameForm)) ≠ .R := by
  contrapose! hk
  exact ( RTippingPoint_iff hsg _ |>.mp rfl |>.2 _ hk )

/-
Minimality of the $\mathscr{L}$-tipping point: below $\operatorname{l}(G)$, the
negative shift is not $\mathscr{L}$.
-/
theorem _root_.MisereGames.misereOutcome_add_neg_nat_ne_L_of_lt_LTippingPoint
    {g : GameForm} (hsg : IsShort g)
    {k : ℕ} (hk : k < LTippingPoint hsg) :
    MisereOutcome (g + (-(k : GameForm))) ≠ .L := by
  intro hL
  have h := ((LTippingPoint_iff hsg (LTippingPoint hsg)).mp rfl).2 k hL
  omega

/--
For a Left-win game, $1 \le \operatorname{n}(G)$.
-/
theorem _root_.MisereGames.one_le_NTippingPoint_of_misereOutcome_L
    {g : GameForm} (hsg : IsShort g)
    (hL : MisereOutcome g = .L) : 1 ≤ NTippingPoint hsg := by
  by_contra h
  have h0 : NTippingPoint hsg = 0 := by omega
  rcases NTippingPoint_spec hsg with hs | hs <;>
    rw [h0] at hs <;>
    simp only [Nat.cast_zero, add_zero, neg_zero, hL] at hs <;>
    exact absurd hs (by decide)

/--
For a next-win game, $\operatorname{n}(G) = 0$.
-/
theorem _root_.MisereGames.NTippingPoint_eq_zero_of_N {g : GameForm} (hsg : IsShort g)
    (hN : MisereOutcome g = .N) : NTippingPoint hsg = 0 := by
  contrapose! hN
  obtain ⟨ k, hk ⟩ := Nat.exists_eq_succ_of_ne_zero hN
  have := NTippingPoint_min hsg (hk.symm ▸ Nat.succ_pos _)
  simpa only [ne_eq, Nat.cast_zero, add_zero, neg_zero, or_self] using this

end

end MisereGames
