/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Real
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.NormalFormSupport

/-!
# Rounding surreal numbers by a positive radius

For positive `r`, `x.round r` is the simplest surreal strictly between `x - r` and `x + r`.
For nonpositive `r` it is defined to be `x`. The addition and multiplication fixed-point lemmas
follow the option formulas for surreal arithmetic. This downstream module follows the rounding
infrastructure from CombinatorialGames PR #317.
-/

universe u

public noncomputable section

namespace Surreal

open IGame Set

/-- A surreal cut is represented by the game cut on chosen representatives of its options. -/
theorem ofSets_eq_mk {s t : Set Surreal.{u}} [Small.{u} s] [Small.{u} t]
    {H : ∀ x ∈ s, ∀ y ∈ t, x < y} :
    !{s | t} = @mk !{out '' s | out '' t} (.mk (by
      rw [moves_ofSets, moves_ofSets]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← Surreal.mk_lt_mk, out_eq, out_eq]
      exact H x hx y hy) (by simp)) := by
  rw [← toGame_inj, toGame_ofSets, toGame_mk, Game.mk_ofSets]
  simp_rw [image_image, gameMk_out]

/-- A surreal cut is no more complex than any surreal strictly between all its options. -/
theorem birthday_ofSets_le_of_mem {s t : Set Surreal.{u}} {z : Surreal}
    [Small.{u} s] [Small.{u} t] {H : ∀ x ∈ s, ∀ y ∈ t, x < y}
    (hL : ∀ x ∈ s, x < z) (hR : ∀ y ∈ t, z < y) :
    !{s | t}.birthday ≤ z.birthday := by
  rw [ofSets_eq_mk, ← out_eq z]
  generalize_proofs
  apply IGame.Fits.birthday_le
  constructor
  · intro x hx
    letI := IGame.Numeric.of_mem_moves hx
    rw [IGame.Numeric.not_le]
    simp only [moves_ofSets, Player.cases] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← Surreal.mk_lt_mk, out_eq, out_eq]
    exact hL a ha
  · intro y hy
    letI := IGame.Numeric.of_mem_moves hy
    rw [IGame.Numeric.not_le]
    simp only [moves_ofSets, Player.cases] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [← Surreal.mk_lt_mk, out_eq, out_eq]
    exact hR a ha

/-- A distinct surreal strictly between all options of a cut has strictly larger birthday. -/
theorem birthday_ofSets_lt_of_mem {s t : Set Surreal.{u}} {z : Surreal}
    [Small.{u} s] [Small.{u} t] {H : ∀ x ∈ s, ∀ y ∈ t, x < y}
    (hL : ∀ x ∈ s, x < z) (hR : ∀ y ∈ t, z < y) (h : !{s | t} ≠ z) :
    !{s | t}.birthday < z.birthday := by
  rw [ofSets_eq_mk, ← out_eq z]
  generalize_proofs
  apply IGame.Fits.birthday_lt
  · constructor
    · intro x hx
      letI := IGame.Numeric.of_mem_moves hx
      rw [IGame.Numeric.not_le]
      simp only [moves_ofSets, Player.cases] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      rw [← Surreal.mk_lt_mk, out_eq, out_eq]
      exact hL a ha
    · intro y hy
      letI := IGame.Numeric.of_mem_moves hy
      rw [IGame.Numeric.not_le]
      simp only [moves_ofSets, Player.cases] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      rw [← Surreal.mk_lt_mk, out_eq, out_eq]
      exact hR a ha
  · rwa [← mk_eq_mk, ← ofSets_eq_mk, out_eq, eq_comm]

/-- The least-birthday surreal lying strictly between all options is the surreal cut. -/
theorem ofSets_eq_of_forall_birthday_le {s t : Set Surreal.{u}} {z : Surreal}
    [Small.{u} s] [Small.{u} t] {H : ∀ x ∈ s, ∀ y ∈ t, x < y}
    (hL : ∀ x ∈ s, x < z) (hR : ∀ y ∈ t, z < y)
    (h : ∀ w, (∀ x ∈ s, x < w) → (∀ y ∈ t, w < y) →
      z.birthday ≤ w.birthday) :
    !{s | t} = z := by
  by_contra hz
  exact (birthday_ofSets_lt_of_mem hL hR hz).not_ge <|
    h _ (fun _ ↦ lt_ofSets_of_mem_left) (fun _ ↦ ofSets_lt_of_mem_right)

private theorem sub_lt_add_of_pos (x : Surreal) {r : Surreal} (hr : 0 < r) :
    x - r < x + r := by
  simpa only [sub_eq_add_neg, add_comm] using add_lt_add_left (neg_lt_self hr) x

/-- For positive `r`, the simplest surreal strictly between `x - r` and `x + r`; for nonpositive
`r`, the junk value `x`. -/
def round (x r : Surreal) : Surreal :=
  if hr : 0 < r then !{{x - r} | {x + r}}' (by
    rintro _ rfl _ rfl
    exact sub_lt_add_of_pos x hr) else x

theorem round_of_pos {x r : Surreal} (hr : 0 < r) :
    x.round r = !{{x - r} | {x + r}}' (by
      rintro _ rfl _ rfl
      exact sub_lt_add_of_pos x hr) :=
  dite_eq_left hr

theorem round_of_nonpos {x r : Surreal} (hr : r ≤ 0) : x.round r = x :=
  dite_eq_right hr.not_gt

/-- The singleton rounding cut of a positive numeric game is numeric. -/
@[implicit_reducible]
def roundGameNumeric {x r : IGame} [x.Numeric] [r.Numeric] (hr : 0 < r) :
    IGame.Numeric !{{x - r} | {x + r}} :=
  .mk (by
    intro y hy z hz
    simp only [IGame.leftMoves_ofSets, IGame.rightMoves_ofSets,
      mem_singleton_iff] at hy hz
    subst y
    subst z
    rw [← Surreal.mk_lt_mk]
    simpa only [Surreal.mk_sub, Surreal.mk_add] using
      sub_lt_add_of_pos (Surreal.mk x) (by
        simpa only [Surreal.mk_zero] using
          (Surreal.mk_lt_mk (x := (0 : IGame)) (y := r)).mpr hr)) (by
    intro p y hy
    cases p with
    | left =>
        simp only [IGame.leftMoves_ofSets, mem_singleton_iff] at hy
        subst y
        infer_instance
    | right =>
        simp only [IGame.rightMoves_ofSets, mem_singleton_iff] at hy
        subst y
        infer_instance)

theorem round_mk_of_pos {x r : IGame} (hr : 0 < r) [x.Numeric] [r.Numeric] :
    (mk x).round (mk r) = @mk !{{x - r} | {x + r}}
      (roundGameNumeric hr) := by
  rw [round_of_pos hr, mk_ofSets]
  congr
  · rw [range_singleton]
    congr 1
  · rw [range_singleton]
    congr 1

/-- The rounding cut is no more complex than any surreal strictly inside its defining interval. -/
theorem birthday_round_le {x y r : Surreal} (h : y ∈ Ioo (x - r) (x + r)) :
    (x.round r).birthday ≤ y.birthday := by
  have hr : 0 < r := by
    rw [← neg_lt_self_iff]
    apply (add_lt_add_iff_left x).mp
    simpa only [sub_eq_add_neg] using h.1.trans h.2
  cases h
  rw [round_of_pos hr]
  apply birthday_ofSets_le_of_mem <;> simpa

/-- The simplest surreal in the open rounding interval is the rounding cut. -/
theorem round_eq_of_forall_birthday_le {x y r : Surreal}
    (h : y ∈ Ioo (x - r) (x + r))
    (hy : ∀ z, z ∈ Ioo (x - r) (x + r) → y.birthday ≤ z.birthday) :
    x.round r = y := by
  have hr : 0 < r := by
    rw [← neg_lt_self_iff]
    apply (add_lt_add_iff_left x).mp
    simpa only [sub_eq_add_neg] using h.1.trans h.2
  cases h
  rw [round_of_pos hr, ofSets_eq_of_forall_birthday_le]
  · simpa
  · simpa
  · simpa using hy

theorem round_of_zero_mem {x r : Surreal} (h : 0 ∈ Ioo (x - r) (x + r)) : x.round r = 0 := by
  have hr : 0 < r := by
    rw [← neg_lt_self_iff]
    apply (add_lt_add_iff_left x).mp
    simpa only [sub_eq_add_neg] using h.1.trans h.2
  cases x with | mk x
  cases r with | mk r
  have hr' : (0 : IGame) < r := by
    rw [← Surreal.mk_lt_mk]
    simpa only [Surreal.mk_zero] using hr
  letI : IGame.Numeric !{{x - r} | {x + r}} :=
    roundGameNumeric (x := x) (r := r) hr'
  rw [← mk_zero, round_mk_of_pos hr, mk_eq_mk, ← fits_zero_iff_equiv]
  simpa [Fits]

@[simp]
theorem round_zero (r : Surreal) : round 0 r = 0 := by
  obtain h | h := le_or_gt r 0
  · rw [round_of_nonpos h]
  · apply round_of_zero_mem
    simpa

@[simp]
theorem round_neg {x r : Surreal} : (-x).round r = -x.round r := by
  obtain h | h := le_or_gt r 0
  · simp_rw [round_of_nonpos h]
  cases x with | mk x
  cases r with | mk r
  simp only [← mk_neg, round_mk_of_pos h, neg_ofSets, neg_singleton,
    sub_eq_add_neg, neg_add, neg_neg]

theorem round_add_of_eq {x y r : Surreal} (hx : x.round r = x) (hy : y.round r = y) :
    (x + y).round r = x + y := by
  obtain h | h := le_or_gt r 0
  · rw [round_of_nonpos h]
  cases x with | mk x
  cases y with | mk y
  cases r with | mk r
  conv_rhs => rw [← hx, ← hy]
  simp only [← mk_add, round_mk_of_pos h] at *
  generalize_proofs at hx hy
  simp only [ofSets_add_ofSets, mk_ofSets, image_singleton, union_singleton,
    range_singleton, range_insert]
  dsimp
  congr <;> rw [hx, hy] <;> grind

theorem round_mul_of_eq {x y r : Surreal} (h : 0 < r)
    (hx : x.round r = x) (hy : y.round r = y) :
    (x * y).round (r * r) = x * y := by
  have h' : 0 < r * r := mul_self_pos.2 h.ne'
  cases x with | mk x
  cases y with | mk y
  cases r with | mk r
  conv_rhs => rw [← hx, ← hy]
  simp only [← mk_mul, round_mk_of_pos h, round_mk_of_pos h'] at *
  generalize_proofs at hx hy
  simp only [ofSets_mul_ofSets, mk_ofSets, mulOption, singleton_prod_singleton,
    union_singleton, image_insert_eq, image_singleton, range_singleton, range_insert]
  congr <;> dsimp <;> rw [hx, hy] <;> grind

end Surreal
