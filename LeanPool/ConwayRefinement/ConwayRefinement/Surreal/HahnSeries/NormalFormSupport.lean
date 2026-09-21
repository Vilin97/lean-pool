/-
Copyright (c) 2026 Dan Abramov, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Violeta Hernández Palacios
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Birthday.Basic
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Pow

/-!
# Support lemmas for the Conway normal-form construction

These inequalities and equivalences are used in the axiom-free Conway normal-form construction
of CombinatorialGames PR #263. Their names, statements, and namespaces agree with the
corresponding upstream declarations.
-/

public noncomputable section

universe u

namespace IGame

namespace Numeric

theorem mul_wpow_lt_mul_wpow_of_pos {x y : IGame} [Numeric x] [Numeric y]
    (r : ℝ) {s : ℝ} (hs : 0 < s) (h : x < y) : r * ω^ x < s * ω^ y :=
  mul_wpow_lt_mul_wpow r hs h

theorem mul_wpow_lt_mul_wpow_of_neg {x y : IGame} [Numeric x] [Numeric y]
    {r : ℝ} (s : ℝ) (hr : r < 0) (h : y < x) : r * ω^ x < s * ω^ y := by
  rw [← Surreal.mk_lt_mk]
  change (r : Surreal) * ω^ (Surreal.mk x) < (s : Surreal) * ω^ (Surreal.mk y)
  rw [← neg_lt_neg_iff]
  simpa [neg_mul] using
    Surreal.mul_wpow_lt_mul_wpow (-s) (Left.neg_pos_iff.mpr hr)
      (Surreal.mk_lt_mk.mpr h)

theorem realCast_mul_wpow_equiv (r : ℝ) (x : IGame.{u}) [Numeric x] :
    r * ω^ x ≈ !{(fun s : ℝ ↦ s * ω^ x) '' Set.Iio r | (fun s : ℝ ↦ s * ω^ x) '' Set.Ioi r} := by
  apply Fits.equiv_of_forall_moves
  · simp [Fits]
  all_goals
    simp only [forall_moves_mul, Player.mul_left, Player.mul_right,
      moves_ofSets, Player.cases, Set.mem_image]
    rintro (_ | _) a ha b hb
  · rw [Real.leftMoves_toIGame] at ha
    rw [leftMoves_wpow] at hb
    obtain ⟨s, hs, rfl⟩ := ha
    obtain (rfl | ⟨a, -, y, hy, rfl⟩) := hb
    · aesop
    numeric
    obtain ⟨t, ht, ht'⟩ := exists_between (α := ℝ) hs
    refine ⟨(t : IGame) * ω^ x, ⟨t, ht', rfl⟩, ?_⟩
    rw [← Surreal.mk_le_mk]
    dsimp [mulOption]
    simp_rw [Surreal.mk_dyadic]
    rw [add_sub_assoc, ← sub_mul, ← le_sub_iff_add_le, sub_eq_add_neg, add_comm,
      ← sub_le_iff_le_add, le_neg, neg_sub, ← sub_mul, ← mul_assoc]
    convert Surreal.mk_le_mk.mpr
      (mul_wpow_lt_mul_wpow_of_pos ((r - s) * a) (s := t - s) _ (left_lt hy)).le <;>
      simp_all
  · rw [Real.rightMoves_toIGame] at ha
    rw [rightMoves_wpow] at hb
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨a, ha, y, hy, rfl⟩ := hb
    numeric
    obtain ⟨t, ht⟩ := exists_lt r
    refine ⟨(t : IGame) * ω^ x, ⟨t, ht, rfl⟩, ?_⟩
    rw [← Surreal.mk_le_mk]
    dsimp [mulOption]
    simp_rw [Surreal.mk_dyadic]
    rw [add_sub_assoc, ← sub_mul, ← le_sub_iff_add_le, sub_eq_add_neg, add_comm,
      ← sub_le_iff_le_add, ← neg_mul, ← sub_mul, neg_sub, ← mul_assoc]
    convert Surreal.mk_le_mk.mpr
      (mul_wpow_lt_mul_wpow_of_pos (s - t) (s := (s - r) * a) _ (lt_right hy)).le <;>
      simp_all
  · rw [Real.leftMoves_toIGame] at ha
    rw [Player.neg_left, rightMoves_wpow] at hb
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨a, ha, y, hy, rfl⟩ := hb
    numeric
    obtain ⟨t, ht⟩ := exists_gt r
    refine ⟨(t : IGame) * ω^ x, ⟨t, ht, rfl⟩, ?_⟩
    rw [← Surreal.mk_le_mk]
    dsimp [mulOption]
    simp_rw [Surreal.mk_dyadic]
    rw [add_sub_assoc, ← sub_mul, ← sub_le_iff_le_add', ← sub_mul, ← mul_assoc]
    convert Surreal.mk_le_mk.mpr
      (mul_wpow_lt_mul_wpow_of_pos (t - s) (s := (r - s) * a) _ (lt_right hy)).le <;>
      simp_all
  · rw [Real.rightMoves_toIGame] at ha
    rw [Player.neg_right, leftMoves_wpow] at hb
    obtain ⟨s, hs, rfl⟩ := ha
    obtain (rfl | ⟨a, -, y, hy, rfl⟩) := hb
    · aesop
    numeric
    obtain ⟨t, ht, ht'⟩ := exists_between (α := ℝ) hs
    refine ⟨(t : IGame) * ω^ x, ⟨t, ht, rfl⟩, ?_⟩
    rw [← Surreal.mk_le_mk]
    dsimp [mulOption]
    simp_rw [Surreal.mk_dyadic]
    rw [add_sub_assoc, ← sub_mul, ← sub_le_iff_le_add', ← sub_mul, ← neg_le_neg_iff,
      ← neg_mul, neg_sub, ← neg_mul, neg_sub, ← mul_assoc]
    convert Surreal.mk_le_mk.mpr
      (mul_wpow_lt_mul_wpow_of_pos ((s - r) * a) (s := s - t) _ (left_lt hy)).le <;>
      simp_all

end Numeric

/-- A simplicity-theorem variant using an equivalent game whose moves are easier to enumerate. -/
theorem Fits.equiv_of_forall_moves_of_equiv {x y : IGame} (a : IGame) (h : x ≈ a)
    (hx : x.Fits y) (hl : ∀ z ∈ aᴸ, ∃ w ∈ yᴸ, z ≤ w)
    (hr : ∀ z ∈ aᴿ, ∃ w ∈ yᴿ, w ≤ z) : x ≈ y :=
  h.trans <| Fits.equiv_of_forall_moves (hx.congr h) hl hr

end IGame

namespace Surreal

theorem birthday_eq_iInf_fits (x : IGame) [hx : IGame.Numeric x] :
    birthday (.mk x) =
      ⨅ y : {y : Subtype IGame.Numeric // IGame.Fits y x}, birthday (.mk y.1.1) := by
  let f (y : {y : Subtype IGame.Numeric // IGame.Fits y x}) := birthday (.mk y.1)
  let : Inhabited {y : Subtype IGame.Numeric // IGame.Fits y x} :=
    ⟨⟨x, hx⟩, IGame.Fits.refl _⟩
  apply (ciInf_le' f default).antisymm'
  obtain ⟨⟨⟨y, _⟩, hy⟩, hy'⟩ := ciInf_mem f
  obtain ⟨z, _, hz, hz'⟩ := birthday_eq_iGameBirthday (.mk y)
  rw [← hz'.trans hy']
  apply (birthday_mk_le z).trans'
  congr! 1
  rw [eq_comm, mk_eq_mk] at hz ⊢
  refine (hy.congr hz).equiv_of_forall_birthday_le fun w hw hw' ↦ hz' ▸ ?_
  exact hy'.trans_le <| (ciInf_le' f ⟨⟨w, hw⟩, hw'⟩).trans (birthday_mk_le _)

end Surreal

namespace IGame

theorem Fits.birthday_le {x y : IGame} [hx : Numeric x] [Numeric y] (h : Fits x y) :
    Surreal.birthday (.mk y) ≤ Surreal.birthday (.mk x) := by
  let f (x : {x : Subtype Numeric // Fits x y}) := Surreal.birthday (.mk x.1)
  rw [Surreal.birthday_eq_iInf_fits y]
  exact ciInf_le' f ⟨⟨x, hx⟩, h⟩

theorem Fits.birthday_lt {x y : IGame} [Numeric x] [Numeric y]
    (h : Fits x y) (he : ¬ x ≈ y) : Surreal.birthday (.mk y) < Surreal.birthday (.mk x) := by
  apply h.birthday_le.lt_of_not_ge
  contrapose he
  obtain ⟨z, _, hz, hz'⟩ := Surreal.birthday_eq_iGameBirthday (.mk x)
  rw [← hz'] at he
  rw [eq_comm, Surreal.mk_eq_mk] at hz
  exact hz.trans <| (h.congr hz).equiv_of_forall_birthday_le fun w _ hw ↦
    he.trans (hw.birthday_le.trans <| Surreal.birthday_mk_le _)

end IGame
