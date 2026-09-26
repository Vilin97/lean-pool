/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Ordinal
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Real
public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Pow
public import Mathlib.Algebra.Order.Ring.Archimedean
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Surreal exponentiation

We define here the ω-map on games and on surreal numbers, representing exponentials with base `ω`.

Among other things, we prove that every non-zero surreal number is commensurate to some unique
`ω^ x`. We express this using `ArchimedeanClass`. There's two important things to note:

- The definition of `ArchimedeanClass` involves absolute values, such that e.g.
  `-ω` is commensurate to `ω`.
- The order in `ArchimedeanClass` is defined so that the equivalence class of `0` is the **largest**
  equivalence class, rather than the smallest.

## Todo

- Define the normal form of a surreal number.
-/

universe u

open Set

public section

/-! ## For Mathlib -/

-- TODO: upstream
theorem Set.image2_eq_range {α β γ : Type*} (f : α → β → γ) (s : Set α) (t : Set β) :
    Set.image2 f s t = Set.range (fun x : s × t ↦ f x.1 x.2) := by
  aesop

namespace ArchimedeanClass

theorem mk_le_mk_iff_dyadic {x y : Surreal} :
    mk x ≤ mk y ↔ ∃ q : Dyadic, 0 < q ∧ q * |y| ≤ |x| := by
  convert! mk_le_mk_iff_denselyOrdered ((Rat.castHom _).comp Dyadic.coeRingHom) (x := x) ?_
  · simp
  · exact Rat.cast_strictMono.comp fun x y ↦ Dyadic.coe_lt_coe.mpr

end ArchimedeanClass

/-! ### ω-map on `IGame` -/

noncomputable section
namespace IGame

/-- The ω-map on games, which is defined so that `ω^ !{s | t} = {0, r * ω^ a | r * ω^ b}` for
`a ∈ s`, `b ∈ t`, and `r` ranging over positive dyadic rationals.

The standard definition in the literature instead has `r` ranging over positive reals,
but this makes no difference as to the equivalence class of the games. -/
private def wpow (x : IGame.{u}) : IGame.{u} :=
  !{insert 0 (range (fun y : Ioi (0 : Dyadic) × xᴸ ↦ y.1 * wpow y.2)) |
    range (fun y : Ioi (0 : Dyadic) × xᴿ ↦ y.1 * wpow y.2)}
termination_by x
decreasing_by igame_wf

#adaptation_note /-- noncomputable is now needed -/ in
@[no_expose]
noncomputable instance : Wpow IGame where
  wpow := wpow

theorem wpow_def (x : IGame.{u}) : ω^ x =
    !{insert 0 (image2 (fun r y ↦ ↑r * ω^ (y : IGame)) (Ioi (0 : Dyadic)) xᴸ) |
      image2 (fun r y ↦ ↑r * ω^ y) (Ioi (0 : Dyadic)) xᴿ} := by
  change wpow _ = _
  rw [wpow]
  simp_rw [Set.image2_eq_range]
  rfl

theorem leftMoves_wpow (x : IGame) : (ω^ x)ᴸ =
    insert 0 (image2 (fun r y ↦ ↑r * ω^ (y : IGame)) (Ioi (0 : Dyadic)) xᴸ) := by
  rw [wpow_def, leftMoves_ofSets, Set.image2_eq_range]

theorem rightMoves_wpow (x : IGame) : (ω^ x)ᴿ =
    image2 (fun r y ↦ ↑r * ω^ (y : IGame)) (Ioi (0 : Dyadic)) xᴿ := by
  rw [wpow_def, rightMoves_ofSets, Set.image2_eq_range]

@[simp]
theorem forall_leftMoves_wpow {x : IGame} {P : IGame → Prop} : (∀ y ∈ (ω^ x)ᴸ, P y) ↔
    P 0 ∧ ∀ r : Dyadic, 0 < r → ∀ y ∈ xᴸ, P (r * ω^ y) := by
  rw [leftMoves_wpow, forall_mem_insert, forall_mem_image2]
  rfl

@[simp]
theorem forall_rightMoves_wpow {x : IGame} {P : IGame → Prop} : (∀ y ∈ (ω^ x)ᴿ, P y) ↔
    ∀ r : Dyadic, 0 < r → ∀ y ∈ xᴿ, P (r * ω^ y) := by
  rw [rightMoves_wpow]
  exact forall_mem_image2

@[simp]
theorem exists_leftMoves_wpow {x : IGame} {P : IGame → Prop} : (∃ y ∈ (ω^ x)ᴸ, P y) ↔
    P 0 ∨ ∃ r : Dyadic, 0 < r ∧ ∃ y ∈ xᴸ, P (r * ω^ y) := by
  rw [leftMoves_wpow, exists_mem_insert, exists_mem_image2]
  rfl

@[simp]
theorem exists_rightMoves_wpow {x : IGame} {P : IGame → Prop} : (∃ y ∈ (ω^ x)ᴿ, P y) ↔
    ∃ r : Dyadic, 0 < r ∧ ∃ y ∈ xᴿ, P (r * ω^ y) := by
  rw [rightMoves_wpow]
  exact exists_mem_image2

@[simp]
theorem zero_mem_leftMoves_wpow (x : IGame) : 0 ∈ (ω^ x)ᴸ := by
  simp [leftMoves_wpow]

theorem mul_wpow_mem_leftMoves_wpow {x y : IGame} {r : Dyadic} (hr : 0 ≤ r)
    (hy : y ∈ xᴸ) : r * ω^ y ∈ (ω^ x)ᴸ := by
  obtain rfl | hr := hr.eq_or_lt
  · simp
  · rw [leftMoves_wpow]
    apply mem_insert_of_mem
    use r, hr, y

theorem mul_wpow_mem_rightMoves_wpow {x y : IGame} {r : Dyadic} (hr : 0 < r)
    (hy : y ∈ xᴿ) : r * ω^ y ∈ (ω^ x)ᴿ := by
  rw [rightMoves_wpow]
  use r, hr, y

theorem natCast_mul_wpow_mem_leftMoves_wpow {x y : IGame} (n : ℕ) (hy : y ∈ xᴸ) :
    n * ω^ y ∈ (ω^ x)ᴸ := by
  simpa using mul_wpow_mem_leftMoves_wpow n.cast_nonneg hy

theorem natCast_mul_wpow_mem_rightMoves_wpow {x y : IGame} {n : ℕ} (hn : 0 < n)
    (hy : y ∈ xᴿ) : n * ω^ y ∈ (ω^ x)ᴿ := by
  simpa using mul_wpow_mem_rightMoves_wpow (n.cast_pos.2 hn) hy

theorem wpow_mem_leftMoves_wpow {x y : IGame} (hy : y ∈ xᴸ) :
    ω^ y ∈ (ω^ x)ᴸ := by
  simpa using natCast_mul_wpow_mem_leftMoves_wpow 1 hy

theorem wpow_mem_rightMoves_wpow {x y : IGame} (hy : y ∈ xᴿ) :
    ω^ y ∈ (ω^ x)ᴿ := by
  simpa using natCast_mul_wpow_mem_rightMoves_wpow one_pos hy

theorem zero_lf_wpow (x : IGame) : 0 ⧏ ω^ x :=
  left_lf (zero_mem_leftMoves_wpow x)

private theorem wpow_pos' (x : IGame) [Numeric (ω^ x)] : 0 < ω^ x := by
  simpa using zero_lf_wpow x

@[simp]
theorem wpow_zero : ω^ (0 : IGame) = 1 := by
  ext p; cases p <;> simp [leftMoves_wpow, rightMoves_wpow]

namespace Numeric

variable {x y z w : IGame} [Numeric x] [Numeric y] [Numeric z] [Numeric w]

private theorem wpow_strictMono_aux {x y : IGame} [Numeric x] [Numeric y]
    [Numeric (ω^ x)] [Numeric (ω^ y)] :
    (x < y → ∀ {r : ℝ}, 0 < r → r * ω^ x < ω^ y) ∧ (x ≤ y → ω^ x ≤ ω^ y) := by
  refine ⟨fun hxy r hr ↦ ?_, fun hxy ↦ ?_⟩
  · obtain (⟨z, hz, hxz⟩ | ⟨z, hz, hzy⟩) := lf_iff_exists_le.1 hxy.not_ge
    · have := wpow_mem_leftMoves_wpow hz
      numeric
      apply ((Numeric.mul_le_mul_iff_right (mod_cast hr)).2 (wpow_strictMono_aux.2 hxz)).trans_lt
      obtain ⟨n, hn⟩ := exists_nat_gt r
      exact ((Numeric.mul_lt_mul_iff_left (wpow_pos' z)).2 (mod_cast hn)).trans
        (Numeric.left_lt (natCast_mul_wpow_mem_leftMoves_wpow n hz))
    · have := wpow_mem_rightMoves_wpow hz
      numeric
      apply (wpow_strictMono_aux.2 hzy).trans_lt'
      rw [← Numeric.lt_div_iff' (mod_cast hr), IGame.div_eq_mul_inv, mul_comm]
      grw [← Numeric.mul_congr_left r.toIGame_inv_equiv]
      obtain ⟨q, hq, hq'⟩ := exists_dyadic_btwn (inv_pos.2 hr)
      apply (Numeric.lt_right (mul_wpow_mem_rightMoves_wpow (mod_cast hq) hz)).trans
      rw [Numeric.mul_lt_mul_iff_left (wpow_pos' z)]
      simpa
  · rw [le_iff_forall_lf, forall_leftMoves_wpow, forall_rightMoves_wpow]
    refine ⟨⟨zero_lf_wpow _, ?_⟩, ?_⟩ <;> intro r hr z hz
    · have := wpow_mem_leftMoves_wpow hz
      numeric
      grw [← Numeric.mul_congr_left (Real.toIGame_dyadic_equiv r)]
      exact (wpow_strictMono_aux.1 ((Numeric.left_lt hz).trans_le hxy) (mod_cast hr)).not_ge
    · have := wpow_mem_rightMoves_wpow hz
      numeric
      have hr' : 0 < (r : ℝ)⁻¹ := by simpa
      rw [← Surreal.mk_le_mk, Surreal.mk_mul, ← le_div_iff₀' (by simpa), div_eq_inv_mul]
      simpa [← Surreal.mk_lt_mk] using
        wpow_strictMono_aux.1 (hxy.trans_lt (Numeric.lt_right hz)) hr'
termination_by (x, y)
decreasing_by igame_wf

protected instance wpow (x : IGame) [Numeric x] : Numeric (ω^ x) := by
  rw [numeric_def]
  simp_rw [Player.forall, forall_leftMoves_wpow, forall_rightMoves_wpow]
  refine ⟨⟨fun r hr y hy ↦ ?_, fun r hr y hy s hs z hz ↦ ?_⟩,
    ⟨.zero, fun r hr y hy ↦ ?_⟩, fun r hr y hy ↦ ?_⟩
  all_goals numeric; have := Numeric.wpow y
  · exact Numeric.mul_pos (mod_cast hr) (wpow_pos' y)
  · have := Numeric.wpow z
    rw [← Numeric.div_lt_iff' (mod_cast hs), ← Surreal.mk_lt_mk]
    dsimp
    simp_rw [div_eq_inv_mul, ← mul_assoc, Surreal.mk_dyadic,
      ← Real.toSurreal_ratCast, ← Real.toSurreal_inv, ← Real.toSurreal_mul]
    apply wpow_strictMono_aux.1 (Numeric.left_lt_right hy hz) (mul_pos ..) <;> simpa
  all_goals infer_instance
termination_by x
decreasing_by igame_wf

@[simp] theorem wpow_pos (x : IGame) [Numeric x] : 0 < ω^ x := wpow_pos' x
@[simp] theorem wpow_nonneg (x : IGame) [Numeric x] : 0 ≤ ω^ x := (wpow_pos x).le

theorem mul_wpow_lt_wpow (r : ℝ) (h : x < y) : r * ω^ x < ω^ y := by
  obtain hr | hr := le_or_gt r 0
  · apply (Numeric.mul_nonpos_of_nonpos_of_nonneg _ (wpow_nonneg x)).trans_lt (wpow_pos y)
    exact Real.toIGame_le_zero.mpr hr
  · exact wpow_strictMono_aux.1 h hr

/-- A version of `mul_wpow_lt_wpow` stated using dyadic rationals. -/
theorem mul_wpow_lt_wpow' (r : Dyadic) (h : x < y) : r * ω^ x < ω^ y := by
  simpa [← Surreal.mk_lt_mk] using mul_wpow_lt_wpow r h

theorem wpow_lt_mul_wpow {r : ℝ} (hr : 0 < r) (h : x < y) : ω^ x < r * ω^ y := by
  rw [← Numeric.div_lt_iff' (mod_cast hr), IGame.div_eq_mul_inv, mul_comm]
  simpa [← Surreal.mk_lt_mk] using mul_wpow_lt_wpow (r⁻¹) h

/-- A version of `wpow_lt_mul_wpow` stated using dyadic rationals. -/
theorem wpow_lt_mul_wpow' {r : Dyadic} (hr : 0 < r) (h : x < y) : ω^ x < r * ω^ y := by
  have hr : (0 : ℝ) < r := by simpa
  simpa [← Surreal.mk_lt_mk] using wpow_lt_mul_wpow hr h

theorem mul_wpow_lt_mul_wpow (r : ℝ) {s : ℝ} (hs : 0 < s) (h : x < y) : r * ω^ x < s * ω^ y := by
  rw [← Numeric.div_lt_iff' (mod_cast hs), ← Surreal.mk_lt_mk]
  dsimp
  rw [div_eq_mul_inv, mul_comm, ← mul_assoc, ← Real.toSurreal_inv, ← Real.toSurreal_mul]
  exact mul_wpow_lt_wpow _ h

/-- A version of `mul_wpow_lt_mul_wpow` stated using dyadic rationals. -/
theorem mul_wpow_lt_mul_wpow' (r : Dyadic) {s : Dyadic} (hs : 0 < s) (h : x < y) :
    r * ω^ x < s * ω^ y := by
  have hs : (0 : ℝ) < s := by simpa
  simpa [← Surreal.mk_lt_mk] using mul_wpow_lt_mul_wpow r hs h

theorem mul_wpow_add_mul_wpow_lt_mul_wpow (r s : ℝ) {t : ℝ} (ht : 0 < t)
     (hx : x < z) (hy : y < z) : r * ω^ x + s * ω^ y < t * ω^ z := by
  have h : 0 < t / 2 := by simpa
  apply (add_lt_add (mul_wpow_lt_mul_wpow r h hx) (mul_wpow_lt_mul_wpow s h hy)).trans_le
  simp [← Surreal.mk_le_mk, ← add_mul]

/-- A version of `mul_wpow_add_mul_wpow_lt_mul_wpow` stated using dyadic rationals. -/
theorem mul_wpow_add_mul_wpow_lt_mul_wpow' (r s : Dyadic) {t : Dyadic} (ht : 0 < t)
    (hx : x < z) (hy : y < z) : r * ω^ x + s * ω^ y < t * ω^ z := by
  have ht : (0 : ℝ) < t := by simpa
  simpa [← Surreal.mk_lt_mk] using mul_wpow_add_mul_wpow_lt_mul_wpow r s ht hx hy

theorem mul_wpow_lt_mul_wpow_add_mul_wpow (r : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hx : x < y) (hy : x < z) : r * ω^ x < s * ω^ y + t * ω^ z := by
  apply (add_lt_add (mul_wpow_lt_mul_wpow (r/2) hs hx) (mul_wpow_lt_mul_wpow (r/2) ht hy)).trans_le'
  simp [← Surreal.mk_le_mk, ← add_mul]

/-- A version of `mul_wpow_lt_mul_wpow_add_mul_wpow` stated using dyadic rationals. -/
theorem mul_wpow_lt_mul_wpow_add_mul_wpow' (r : Dyadic) {s t : Dyadic} (hs : 0 < s) (ht : 0 < t)
    (hx : x < y) (hy : x < z) : r * ω^ x < s * ω^ y + t * ω^ z := by
  have hs : (0 : ℝ) < s := by simpa
  have ht : (0 : ℝ) < t := by simpa
  simpa [← Surreal.mk_lt_mk] using mul_wpow_lt_mul_wpow_add_mul_wpow r hs ht hx hy

@[simp]
theorem wpow_lt_wpow : ω^ x < ω^ y ↔ x < y := by
  constructor
  · contrapose
    repeat rw [Numeric.not_lt]
    exact wpow_strictMono_aux.2
  · simpa using mul_wpow_lt_wpow' 1

@[simp]
theorem wpow_le_wpow : ω^ x ≤ ω^ y ↔ x ≤ y := by
  rw [← Numeric.not_lt, wpow_lt_wpow, Numeric.not_lt]

theorem wpow_congr (h : x ≈ y) : ω^ x ≈ ω^ y := by
  simpa [AntisymmRel] using h

private theorem mulOption_lt_wpow {r s : Dyadic} (hr : 0 < r) (hs : 0 < s)
    (h₁ : x < z) (h₂ : y < w) (IH₁ : ω^ (x + w) ≈ ω^ x * ω^ w)
    (IH₂ : ω^ (z + y) ≈ ω^ z * ω^ y) (IH₃ : ω^ (z + w) ≈ ω^ z * ω^ w) :
    mulOption (ω^ x) (ω^ y) (r * ω^ z) (s * ω^ w) < ω^ (x + y) := by
  apply IGame.sub_lt_iff_lt_add.2
  have H : r * ω^ (z + y) + s * ω^ (x + w) < ω^ (x + y) + ↑(r * s) * ω^ (z + w) := by
    apply (mul_wpow_add_mul_wpow_lt_mul_wpow' ..).trans (lt_add_of_pos_left ..) <;> simp_all
  rw [← Surreal.mk_lt_mk, ← Surreal.mk_eq_mk] at *
  convert H using 1 <;> simp_all <;> ring_nf

private theorem mulOption_lt_wpow' {r s : Dyadic} (hr : 0 < r) (hs : 0 < s)
    (h₁ : z < x) (h₂ : w < y) (IH₁ : ω^ (x + w) ≈ ω^ x * ω^ w)
    (IH₂ : ω^ (z + y) ≈ ω^ z * ω^ y) (IH₃ : ω^ (z + w) ≈ ω^ z * ω^ w) :
    mulOption (ω^ x) (ω^ y) (r * ω^ z) (s * ω^ w) < ω^ (x + y) := by
  apply IGame.sub_lt_iff_lt_add.2
  have H : r * ω^ (z + y) + s * ω^ (x + w) < (1 : Dyadic) * ω^ (x + y) + (r * s) * ω^ (z + w) := by
    apply (mul_wpow_add_mul_wpow_lt_mul_wpow' ..).trans (lt_add_of_pos_right ..) <;> simp_all
  rw [← Surreal.mk_lt_mk, ← Surreal.mk_eq_mk] at *
  convert H using 1 <;> simp_all <;> ring_nf

private theorem wpow_lt_mulOption {r s : Dyadic} (hr : 0 < r) (hs : 0 < s)
    (h₁ : x < z) (h₂ : w < y) (IH₁ : ω^ (z + y) ≈ ω^ z * ω^ y) (IH₂ : ω^ (z + w) ≈ ω^ z * ω^ w) :
    ω^(x + y) < mulOption (ω^ x) (ω^ y) (r * ω^ z) (s * ω^ w) := by
  apply IGame.lt_sub_iff_add_lt.2
  have H : (1 : Dyadic) * ω^ (x + y) + ↑(r * s) * ω^ (z + w)
      < r * ω^ (z + y) + s * ω^ x * ω^ w := by
    apply (mul_wpow_add_mul_wpow_lt_mul_wpow' ..).trans (lt_add_of_pos_right ..) <;> simp_all
  rw [← Surreal.mk_lt_mk, ← Surreal.mk_eq_mk] at *
  convert H using 1 <;> simp_all <;> ring_nf

theorem wpow_add_equiv (x y : IGame) [Numeric x] [Numeric y] : ω^ (x + y) ≈ ω^ x * ω^ y := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf]
  simp only [forall_leftMoves_wpow, forall_rightMoves_wpow, forall_and,
    forall_moves_add, forall_moves_mul, Player.forall,
    Player.left_mul, Player.right_mul, Player.neg_left, Player.neg_right]
  repeat any_goals constructor
  on_goal 1 => exact (Numeric.mul_pos (wpow_pos _) (wpow_pos _)).not_ge
  on_goal 7 => simp
  all_goals intro r hr z hz
  any_goals intro s hs w hw
  all_goals numeric; apply not_le_of_gt
  · grw [mul_congr_right (wpow_add_equiv ..), ← mul_assoc_equiv]
    rw [Numeric.mul_lt_mul_iff_left (wpow_pos _)]
    exact mul_wpow_lt_wpow' r (Numeric.left_lt hz)
  · grw [mul_congr_right (wpow_add_equiv ..), mul_comm (r : IGame), mul_assoc_equiv]
    rw [Numeric.mul_lt_mul_iff_right (wpow_pos _), mul_comm]
    exact mul_wpow_lt_wpow' r (Numeric.left_lt hz)
  · rw [mulOption_zero_left, mul_comm (r : IGame)]
    grw [← mul_assoc_equiv, mul_comm, ← mul_congr_right (wpow_add_equiv ..)]
    exact wpow_lt_mul_wpow' hr (add_right_strictMono (Numeric.lt_right hz))
  · rw [mulOption_comm, add_comm]
    apply wpow_lt_mulOption hs hr (Numeric.lt_right hw) (Numeric.left_lt hz) <;>
      rw [add_comm, mul_comm] <;> exact wpow_add_equiv ..
  · rw [mulOption_zero_right]
    grw [mul_assoc_equiv, ← mul_congr_right (wpow_add_equiv ..)]
    exact wpow_lt_mul_wpow' hr (add_left_strictMono (Numeric.lt_right hz))
  · exact wpow_lt_mulOption hr hs (Numeric.lt_right hz) (Numeric.left_lt hw)
      (wpow_add_equiv ..) (wpow_add_equiv ..)
  · rw [mulOption_zero_right]
    grw [mul_assoc_equiv, ← mul_congr_right (wpow_add_equiv ..)]
    exact mul_wpow_lt_wpow' r (add_left_strictMono (Numeric.left_lt hz))
  · rw [mulOption_zero_left, mul_comm]
    grw [mul_assoc_equiv, mul_comm (ω^ z), ← mul_congr_right (wpow_add_equiv ..)]
    exact mul_wpow_lt_wpow' _ (add_right_strictMono (Numeric.left_lt hz))
  · exact mulOption_lt_wpow' hr hs (Numeric.left_lt hz) (Numeric.left_lt hw)
      (wpow_add_equiv ..) (wpow_add_equiv ..) (wpow_add_equiv ..)
  · exact mulOption_lt_wpow hr hs (Numeric.lt_right hz) (Numeric.lt_right hw)
      (wpow_add_equiv ..) (wpow_add_equiv ..) (wpow_add_equiv ..)
  · grw [mul_congr_right (wpow_add_equiv ..), ← mul_assoc_equiv]
    rw [Numeric.mul_lt_mul_iff_left (wpow_pos _)]
    exact wpow_lt_mul_wpow' hr (Numeric.lt_right hz)
  · grw [mul_congr_right (wpow_add_equiv ..), mul_comm (r : IGame), mul_assoc_equiv]
    rw [Numeric.mul_lt_mul_iff_right (wpow_pos _), mul_comm]
    exact wpow_lt_mul_wpow' hr (Numeric.lt_right hz)
termination_by (x, y)
decreasing_by igame_wf

theorem wpow_neg_equiv (x : IGame) [Numeric x] : ω^ -x ≈ (ω^ x)⁻¹ := by
  apply equiv_inv_of_mul_eq_one ((wpow_add_equiv ..).symm.trans _)
  rw [← wpow_zero]
  exact wpow_congr (neg_add_equiv x)

theorem wpow_sub_equiv (x y : IGame) [Numeric x] [Numeric y] : ω^ (x - y) ≈ ω^ x / ω^ y :=
  (wpow_add_equiv ..).trans (mul_congr_right (wpow_neg_equiv _))

end Numeric

open NatOrdinal in
theorem toIGame_wpow_equiv (x : NatOrdinal) : (ω^ x).toIGame ≈ ω^ x.toIGame := by
  have H {y} (h : y < x) (n : ℕ) : toIGame (ω^ y * n) ≈ ω^ y.toIGame * n :=
    (toIGame_mul ..).trans <| Numeric.mul_congr (toIGame_wpow_equiv y) (toIGame_natCast_equiv n)
  obtain rfl | hx := eq_or_ne x 0; · simp
  constructor <;> refine le_iff_forall_lf.2 ⟨?_, ?_⟩
  · simp_rw [forall_leftMoves_toIGame, lt_wpow_iff hx]
    intro z ⟨y, hy, n, hz⟩
    apply ((toIGame.strictMono hz).trans_le _).not_ge
    grw [H hy n]
    rw [mul_comm]
    simpa using (Numeric.mul_wpow_lt_wpow' n (toIGame.strictMono hy)).le
  · simp
  · simp_rw [forall_leftMoves_wpow, forall_leftMoves_toIGame]
    constructor
    · rw [← toIGame_zero, toIGame.le_iff_le]
      simp
    · intro r hr y hy
      obtain ⟨n, hn⟩ := exists_nat_gt r
      rw [mul_comm]
      apply ((toIGame.strictMono <| wpow_mul_natCast_lt hy n).trans' _).not_ge
      grw [H hy n]
      rw [Numeric.mul_lt_mul_iff_right]
      · exact_mod_cast hn
      · exact Numeric.wpow_pos _
  · simp
termination_by x

end IGame

/-! ### ω-pow on `Surreal` -/

namespace Surreal
open IGame

variable {x y : Surreal}

instance : Wpow Surreal where
  wpow := Quotient.lift (fun x ↦ mk (ω^ x)) fun _ _ h ↦ mk_eq (Numeric.wpow_congr h)

@[simp]
theorem mk_wpow (x : IGame) [Numeric x] : mk (ω^ x) = ω^ (mk x) :=
  rfl

@[simp]
theorem wpow_zero : ω^ (0 : Surreal) = 1 :=
  mk_eq IGame.wpow_zero.antisymmRel

@[simp]
theorem wpow_pos : ∀ x : Surreal, 0 < ω^ x := by
  rintro ⟨x, _⟩
  exact Numeric.wpow_pos x

@[simp]
theorem wpow_nonneg (x : Surreal) : 0 ≤ ω^ x :=
  (wpow_pos x).le

@[simp]
theorem wpow_ne_zero (x : Surreal) : ω^ x ≠ 0 :=
  (wpow_pos x).ne'

@[simp]
theorem wpow_abs (x : Surreal) : |ω^ x| = ω^ x :=
  abs_of_pos (wpow_pos x)

theorem strictMono_wpow : StrictMono (ω^ · : Surreal → _) := by
  rintro ⟨x, _⟩ ⟨y, _⟩
  exact Numeric.wpow_lt_wpow.2

@[simp]
theorem wpow_lt_wpow : ω^ x < ω^ y ↔ x < y :=
  strictMono_wpow.lt_iff_lt

@[simp]
theorem wpow_le_wpow : ω^ x ≤ ω^ y ↔ x ≤ y :=
  strictMono_wpow.le_iff_le

@[simp]
theorem wpow_inj : ω^ x = ω^ y ↔ x = y :=
  strictMono_wpow.injective.eq_iff

@[simp]
theorem wpow_add : ∀ x y : Surreal, ω^ (x + y) = ω^ x * ω^ y := by
  rintro ⟨x, _⟩ ⟨y, _⟩
  exact mk_eq (Numeric.wpow_add_equiv x y)

@[simp]
theorem wpow_neg : ∀ x : Surreal, ω^ -x = (ω^ x)⁻¹ := by
  rintro ⟨x, _⟩
  exact mk_eq (Numeric.wpow_neg_equiv x)

@[simp]
theorem wpow_sub : ∀ x y : Surreal, ω^ (x - y) = ω^ x / ω^ y := by
  rintro ⟨x, _⟩ ⟨y, _⟩
  exact mk_eq (Numeric.wpow_sub_equiv x y)

theorem mul_wpow_lt_wpow (r : ℝ) (h : x < y) : r * ω^ x < ω^ y := by
  cases x; cases y; exact IGame.Numeric.mul_wpow_lt_wpow r h

theorem wpow_lt_mul_wpow {r : ℝ} (hr : 0 < r) (h : x < y) : ω^ x < r * ω^ y := by
  cases x; cases y; exact IGame.Numeric.wpow_lt_mul_wpow hr h

theorem mul_wpow_lt_mul_wpow (r : ℝ) {s : ℝ} (hs : 0 < s) (h : x < y) : r * ω^ x < s * ω^ y := by
  cases x; cases y; exact IGame.Numeric.mul_wpow_lt_mul_wpow r hs h

/-! ### Archimedean classes -/

open ArchimedeanClass

@[simp]
theorem mk_realCast {r : ℝ} (hr : r ≠ 0) : ArchimedeanClass.mk (r : Surreal) = 0 :=
  mk_map_of_archimedean' Real.toSurrealRingHom hr

/-- We define a `ValuativeRel` instance on `Surreal` which is compatible with
`ArchimedeanClass.addValuation`. In particular, you can write `x =ᵥ y` to mean that `x` is
commensurate with `y`. -/
instance : ValuativeRel Surreal :=
  .ofValuation (ArchimedeanClass.addValuation _)

instance : (ArchimedeanClass.addValuation Surreal).Compatible where
  vle_iff_le _ _ := .rfl

theorem vle_def {x y : Surreal} : x ≤ᵥ y ↔ ArchimedeanClass.mk y ≤ .mk x :=
  .rfl

theorem vlt_def {x y : Surreal} : x <ᵥ y ↔ ArchimedeanClass.mk y < .mk x :=
  (ArchimedeanClass.addValuation _).vlt_iff_lt

theorem veq_def {x y : Surreal} : x =ᵥ y ↔ ArchimedeanClass.mk x = .mk y :=
  (ArchimedeanClass.addValuation _).veq_iff_eq

@[simp] theorem neg_veq {x y : Surreal} : -x =ᵥ y ↔ x =ᵥ y := by simp [veq_def]
@[simp] theorem veq_neg {x y : Surreal} : x =ᵥ -y ↔ x =ᵥ y := by simp [veq_def]
@[simp] theorem vle_neg {x y : Surreal} : x ≤ᵥ -y ↔ x ≤ᵥ y := by simp [vle_def]
@[simp] theorem neg_vle {x y : Surreal} : -x ≤ᵥ y ↔ x ≤ᵥ y := by simp [vle_def]
@[simp] theorem vlt_neg {x y : Surreal} : x <ᵥ -y ↔ x <ᵥ y := by simp [vlt_def]
@[simp] theorem neg_vlt {x y : Surreal} : -x <ᵥ y ↔ x <ᵥ y := by simp [vlt_def]

theorem archimedeanClassMk_wpow_strictAnti :
    StrictAnti fun x : Surreal ↦ ArchimedeanClass.mk (ω^ x) := by
  refine fun x y h ↦ (mk_antitoneOn (wpow_nonneg _) (wpow_nonneg _)
    (wpow_le_wpow.2 h.le)).lt_of_not_ge fun ⟨n, hn⟩ ↦ hn.not_gt ?_
  simpa using mul_wpow_lt_wpow n h

@[simp]
theorem wpow_vlt_wpow_iff : ω^ x <ᵥ ω^ y ↔ x < y :=
  vlt_def.trans archimedeanClassMk_wpow_strictAnti.lt_iff_gt

@[simp]
theorem wpow_vle_wpow_iff : ω^ x ≤ᵥ ω^ y ↔ x ≤ y :=
  vle_def.trans archimedeanClassMk_wpow_strictAnti.le_iff_ge

/-- `ω^ x` and `ω^ y` are commensurate iff `x = y`. -/
@[simp]
theorem wpow_veq_wpow_iff : ω^ x =ᵥ ω^ y ↔ x = y :=
  veq_def.trans archimedeanClassMk_wpow_strictAnti.injective.eq_iff

private theorem mk_lt_mk_of_ne {x : IGame} [Numeric x] (h : 0 < x)
    (Hl : ∀ y (h : y ∈ xᴸ), 0 < y → have := Numeric.of_mem_moves h;
      ArchimedeanClass.mk (mk y) ≠ .mk (mk x)) :
    ∀ y (h : y ∈ xᴸ), 0 < y → have := Numeric.of_mem_moves h;
      ArchimedeanClass.mk (mk x) < .mk (mk y) :=
  fun y hy hy' ↦ lt_of_le_of_ne' (mk_antitoneOn hy'.le h.le (Numeric.left_lt hy).le) (Hl y hy hy')

private theorem mk_lt_mk_of_ne' {x : IGame} [Numeric x] (h : 0 < x)
    (Hr : ∀ y (h : y ∈ xᴿ), have := Numeric.of_mem_moves h;
      ArchimedeanClass.mk (mk y) ≠ .mk (mk x)) :
    ∀ y (h : y ∈ xᴿ), have := Numeric.of_mem_moves h;
      ArchimedeanClass.mk (mk y) < .mk (mk x) :=
  fun y hy ↦ have hy' := (Numeric.lt_right hy);
    lt_of_le_of_ne (mk_antitoneOn h.le (h.trans hy').le hy'.le) (Hr y hy)

local instance (x : IGame) [Numeric x] (y : (xᴸ ∩ Ioi 0 :)) : Numeric y :=
  .of_mem_moves y.2.1

private theorem numeric_of_forall_mk_ne_mk' {x : IGame} [Numeric x] (h : 0 < x)
    {f : (xᴸ ∩ Ioi 0 :) → Subtype Numeric.{u}} {g : xᴿ → Subtype Numeric.{u}}
    (hf : ∀ y, ArchimedeanClass.mk (ω^ (mk (f y).1)) = .mk (mk y.1))
    (hg : ∀ y, ArchimedeanClass.mk (ω^ (mk (g y).1)) = .mk (mk y.1))
    (Hl : ∀ y (h : y ∈ xᴸ), 0 < y → have := Numeric.of_mem_moves h;
      ArchimedeanClass.mk (mk y) ≠ .mk (mk x))
    (Hr : ∀ y (h : y ∈ xᴿ), have := Numeric.of_mem_moves h;
      ArchimedeanClass.mk (mk y) ≠ .mk (mk x)) :
    Numeric !{range (Subtype.val ∘ f) | range (Subtype.val ∘ g)} := by
  apply Numeric.mk
  · simp_rw [leftMoves_ofSets, rightMoves_ofSets]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp_rw [Function.comp_apply, ← mk_lt_mk, ← wpow_vlt_wpow_iff, vlt_def, hf, hg]
    exact (mk_lt_mk_of_ne' h Hr _ b.2).trans (mk_lt_mk_of_ne h Hl _ a.2.1 a.2.2)
  · aesop (add simp [Subtype.prop])

private theorem wpow_equiv_of_forall_mk_ne_mk' {x : IGame.{u}} [Numeric x] (h : 0 < x)
    {f : (xᴸ ∩ Ioi 0 :) → Subtype Numeric.{u}} {g : xᴿ → Subtype Numeric.{u}}
    (hf : ∀ y, ArchimedeanClass.mk (ω^ (mk (f y).1)) = .mk (mk y.1))
    (hg : ∀ y, ArchimedeanClass.mk (ω^ (mk (g y).1)) = .mk (mk y.1))
    (Hl : ∀ y (h : y ∈ xᴸ), 0 < y → have := Numeric.of_mem_moves h;
      ArchimedeanClass.mk (mk y) ≠ .mk (mk x))
    (Hr : ∀ y (h : y ∈ xᴿ), have := Numeric.of_mem_moves h;
      ArchimedeanClass.mk (mk y) ≠ .mk (mk x)) :
    ω^ !{range (Subtype.val ∘ f) | range (Subtype.val ∘ g)} ≈ x := by
  have Hl' := mk_lt_mk_of_ne h Hl
  have Hr' := mk_lt_mk_of_ne' h Hr
  have := numeric_of_forall_mk_ne_mk' h hf hg Hl Hr
  apply (Fits.equiv_of_forall_moves ..).symm
  · constructor
    · simp_rw [forall_leftMoves_wpow, leftMoves_ofSets, forall_mem_range,
        Function.comp_apply, ← Surreal.mk_le_mk]
      refine ⟨h.not_ge, fun r hr y ↦ (lt_of_mk_lt_mk_of_nonneg ?_ h.le).not_ge⟩
      simpa [hr.ne', hf] using Hl' _ y.2.1 y.2.2
    · simp_rw [forall_rightMoves_wpow, rightMoves_ofSets, forall_mem_range,
        Function.comp_apply, ← Surreal.mk_le_mk]
      refine fun r hr y ↦ (lt_of_mk_lt_mk_of_nonneg ?_ ?_).not_ge
      · simpa [hr.ne', hg] using Hr' _ y.2
      · simpa using hr.le
  all_goals
    intro y hy
    numeric
    simp only [exists_rightMoves_wpow, exists_leftMoves_wpow]
  · refine or_iff_not_imp_left.2 fun hy' ↦ ?_
    rw [Numeric.not_le] at hy'
    obtain ⟨(_ | n), hn⟩ := (hf ⟨y, hy, hy'⟩).le
    · apply (hy'.not_antisymmRel_symm _).elim
      simpa [← mk_eq_mk] using hn
    · refine ⟨n + 1, mod_cast n.succ_pos, ?_⟩
      simp_rw [leftMoves_ofSets, exists_range_iff, Function.comp_apply, ← Surreal.mk_le_mk]
      use ⟨y, hy, hy'⟩
      convert ←hn
      · exact abs_of_pos hy'
      · simp
  · obtain ⟨r, hr, hr'⟩ := mk_le_mk_iff_dyadic.1 (hg ⟨y, hy⟩).ge
    refine ⟨r, hr, ?_⟩
    simp_rw [rightMoves_ofSets, exists_range_iff, Function.comp_apply, ← Surreal.mk_le_mk]
    use ⟨y, hy⟩
    convert ←hr' using 1
    · simp
    · exact abs_of_pos <| h.trans (Numeric.lt_right hy)

private theorem exists_mk_wpow_eq {x : IGame.{u}} [Numeric x] (h : 0 < x) :
    ∃ y : Subtype Numeric, ArchimedeanClass.mk (ω^ mk y) = .mk (mk x) := by
  have IHl (y : (xᴸ ∩ Ioi 0 :)) :
      ∃ z : Subtype Numeric, ArchimedeanClass.mk (ω^ mk z) = .mk (mk y) :=
    have := y.2.1; exists_mk_wpow_eq y.2.2
  have IHr (y : xᴿ) :
      ∃ z : Subtype Numeric, ArchimedeanClass.mk (ω^ mk z) = .mk (mk y) :=
    exists_mk_wpow_eq (h.trans (Numeric.lt_right y.2))
  choose f hf using IHl
  choose g hg using IHr
  by_contra! H
  have Hf (y : IGame) (h : y ∈ xᴸ) (hy : 0 < y) :
      have := Numeric.of_mem_moves h; ArchimedeanClass.mk (mk y) ≠ ArchimedeanClass.mk (mk x) := by
    dsimp
    rw [← hf ⟨y, h, hy⟩]
    exact H _
  have Hg (y : IGame) (h : y ∈ xᴿ) :
      have := Numeric.of_mem_moves h; ArchimedeanClass.mk (mk y) ≠ ArchimedeanClass.mk (mk x) := by
    dsimp
    rw [← hg ⟨y, h⟩]
    exact H _
  have := numeric_of_forall_mk_ne_mk' h hf hg Hf Hg
  apply H ⟨_, this⟩
  congr
  rw [← mk_wpow, mk_eq_mk]
  exact wpow_equiv_of_forall_mk_ne_mk' h hf hg Hf Hg
termination_by x
decreasing_by igame_wf

/-- Every non-zero surreal is commensurate to some `ω^ x`. -/
theorem exists_wpow_veq (h : x ≠ 0) : ∃ y, ω^ y =ᵥ x := by
  simp_rw [veq_def]
  obtain h | h := h.lt_or_gt <;> cases x
  · obtain ⟨⟨y, _⟩, hy⟩ := exists_mk_wpow_eq (IGame.zero_lt_neg.2 h)
    use .mk y
    simpa using hy
  · obtain ⟨⟨y, _⟩, hy⟩ := exists_mk_wpow_eq h
    exact ⟨_, hy⟩

/-! ### ω-logarithm -/

/-- The ω-logarithm of a positive surreal `x` is the unique surreal `y` such that `x` is
commensurate with `ω^ y`.

As with `Real.log`, we set junk values `wlog 0 = 0` and `wlog (-x) = wlog x`. -/
def wlog (x : Surreal) : Surreal :=
  if h : x = 0 then 0 else Classical.choose (exists_wpow_veq h)

/-- Returns an arbitrary representative for `Surreal.wlog`. -/
def _root_.IGame.wlog (x : IGame) : IGame := by
  classical exact if _ : Numeric x then (Surreal.mk x).wlog.out else 0

instance _root_.IGame.Numeric.wlog (x : IGame) : Numeric x.wlog := by
  rw [IGame.wlog]
  split_ifs <;> infer_instance

@[simp]
theorem mk_wlog (x : IGame) [h : Numeric x] : mk x.wlog = (mk x).wlog := by
  simp_rw [IGame.wlog, dite_eq_left h, Surreal.out_eq]

@[simp]
theorem wlog_zero : wlog 0 = 0 :=
  dite_eq_left rfl

theorem wpow_wlog_veq (h : x ≠ 0) : ω^ wlog x =ᵥ x := by
  rw [wlog, dite_eq_right h]
  exact Classical.choose_spec (exists_wpow_veq h)

@[simp]
theorem archimedeanClassMk_wpow_wlog (h : x ≠ 0) : ArchimedeanClass.mk (ω^ x.wlog) = .mk x :=
  veq_def.1 (wpow_wlog_veq h)

theorem wlog_eq_of_wpow_veq (h : ω^ y =ᵥ x) : wlog x = y := by
  obtain rfl | hx := eq_or_ne x 0
  · simp at h
  · grw [← wpow_wlog_veq hx, wpow_veq_wpow_iff] at h
    rwa [eq_comm] at h

@[simp]
theorem wlog_eq_iff (h : x ≠ 0) : wlog x = y ↔ ω^ y =ᵥ x :=
  ⟨fun hy ↦ hy ▸ wpow_wlog_veq h, wlog_eq_of_wpow_veq⟩

theorem wlog_congr (h : x =ᵥ y) : wlog x = wlog y := by
  obtain rfl | hy := eq_or_ne y 0; · simp_all
  apply wlog_eq_of_wpow_veq
  grw [wpow_wlog_veq hy]
  rwa [ValuativeRel.veq_comm]

@[simp]
theorem wlog_wpow (x : Surreal) : wlog (ω^ x) = x := by
  simp

@[simp]
theorem wlog_neg (x : Surreal) : wlog (-x) = wlog x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · apply wlog_eq_of_wpow_veq
    simpa using wpow_wlog_veq hx

@[simp]
theorem wlog_abs (x : Surreal) : wlog |x| = wlog x :=
  abs_by_cases (wlog · = _) rfl (wlog_neg _)

theorem wlog_surjective : Function.Surjective wlog :=
  fun _ ↦ ⟨_, wlog_wpow _⟩

theorem wlog_monotoneOn : MonotoneOn wlog (Ioi 0) := by
  intro a ha b hb h
  grw [← wpow_vle_wpow_iff, wpow_wlog_veq ha.ne', wpow_wlog_veq hb.ne']
  apply mk_antitoneOn ha.le hb.le h

theorem wlog_antitoneOn : AntitoneOn wlog (Iio 0) := by
  intro a ha b hb h
  rw [← neg_le_neg_iff] at h
  convert wlog_monotoneOn _ _ h using 1 <;> simp_all

theorem wlog_add_eq_left {x y : Surreal} (h : y <ᵥ x) : wlog (x + y) = wlog x := by
  apply wlog_congr
  rw [veq_def, mk_add_eq_mk_left (vlt_def.1 h)]

theorem wlog_add_eq_right {x y : Surreal} (h : y <ᵥ x) : wlog (y + x) = wlog x := by
  rw [add_comm, wlog_add_eq_left h]

theorem wlog_sub_eq_left {x y : Surreal} : y <ᵥ x → wlog (x - y) = wlog x := by
  simpa [sub_eq_add_neg] using @wlog_add_eq_left x (-y)

theorem wlog_sub_eq_right {x y : Surreal} : y <ᵥ x → wlog (y - x) = wlog x := by
  simpa [sub_eq_add_neg] using @wlog_add_eq_right (-x) y

theorem wlog_le_wlog_iff (hx : x ≠ 0) (hy : y ≠ 0) : wlog x ≤ wlog y ↔ x ≤ᵥ y := by
  rw [← wpow_vle_wpow_iff]
  -- TODO: why does `grw` not work on the iff?
  constructor
  · intro h
    grw [wpow_wlog_veq hx, wpow_wlog_veq hy] at h
    exact h
  · intro h
    grw [wpow_wlog_veq hx, wpow_wlog_veq hy]
    exact h

theorem wlog_le_wlog_of_vle (hx : x ≠ 0) (h : x ≤ᵥ y) : wlog x ≤ wlog y := by
  obtain rfl | hy := eq_or_ne y 0; · simp_all
  rwa [wlog_le_wlog_iff hx hy]

theorem wlog_lt_wlog_iff (hx : x ≠ 0) (hy : y ≠ 0) : wlog x < wlog y ↔ x <ᵥ y := by
  rw [← not_le, wlog_le_wlog_iff hy hx, ValuativeRel.not_vle]

theorem wlog_lt_wlog_of_vlt (hx : x ≠ 0) (h : x <ᵥ y) : wlog x < wlog y := by
  obtain rfl | hy := eq_or_ne y 0; · simp at h
  rwa [wlog_lt_wlog_iff hx hy]

@[simp]
theorem wlog_mul {x y : Surreal} (hx : x ≠ 0) (hy : y ≠ 0) : wlog (x * y) = wlog x + wlog y := by
  apply wlog_eq_of_wpow_veq
  rw [wpow_add]
  apply ValuativeRel.mul_veq_mul <;> exact wpow_wlog_veq ‹_›

@[simp]
theorem wlog_realCast (r : ℝ) : wlog r = 0 := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  · rw [wlog_eq_iff (mod_cast hr), veq_def, mk_realCast hr, wpow_zero, ArchimedeanClass.mk_one]

@[simp] theorem wlog_ratCast (q : ℚ) : wlog q = 0 := by simpa using wlog_realCast q
@[simp] theorem wlog_intCast (n : ℤ) : wlog n = 0 := by simpa using wlog_realCast n
@[simp] theorem wlog_natCast (n : ℕ) : wlog n = 0 := by simpa using wlog_realCast n
@[simp] theorem wlog_one : wlog 1 = 0 := mod_cast wlog_natCast 1

@[simp]
theorem wlog_inv (x : Surreal) : x⁻¹.wlog = -x.wlog := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  rw [← add_eq_zero_iff_eq_neg, ← wlog_mul (inv_ne_zero hx) hx, inv_mul_cancel₀ hx, wlog_one]

@[simp]
theorem wlog_pow (x : Surreal) (n : ℕ) : wlog (x ^ n) = n * wlog x := by
  obtain rfl | hx := eq_or_ne x 0
  · cases n <;> simp
  · induction n with
    | zero => simp
    | succ n IH => rw [pow_succ, wlog_mul (pow_ne_zero n hx) hx, IH, Nat.cast_add_one, add_one_mul]

@[simp]
theorem wlog_zpow (x : Surreal) (n : ℤ) : wlog (x ^ n) = n * wlog x := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp

@[simp high] -- This should fire before `ArchimedeanClass.mk_div`
theorem archimedeanClassMk_div_wpow_wlog (x : Surreal) :
    ArchimedeanClass.mk (x / ω^ x.wlog) = .mk x - .mk x := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp_all

theorem mk_div_wpow_wlog_of_ne_zero {x : Surreal} (hx : x ≠ 0) :
    ArchimedeanClass.mk (x / ω^ x.wlog) = 0 := by
  rw [archimedeanClassMk_div_wpow_wlog, LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top]
  simpa

private theorem ofSets_wlog_eq {x : IGame} :
    !{IGame.wlog '' {y ∈ xᴸ | 0 < y} | IGame.wlog '' xᴿ} =
    !{range (Subtype.val ∘ fun x : (xᴸ ∩ Ioi 0 :) ↦ ⟨_, Numeric.wlog x⟩) |
      range (Subtype.val ∘ fun x : xᴿ ↦ ⟨_, Numeric.wlog x⟩)} := by
  congr! <;> exact image_eq_range ..

private theorem mk_wpow_wlog_left {x : IGame} [Numeric x] :
    ∀ y : (xᴸ ∩ Ioi 0 :), ArchimedeanClass.mk (ω^ mk y.1.wlog) = .mk (mk y) := by
  intro ⟨y, hy, hy'⟩
  numeric
  rw [mk_wlog, ← veq_def]
  exact wpow_wlog_veq hy'.ne'

private theorem mk_wpow_wlog_right {x : IGame} [Numeric x] (h : 0 < x) :
    ∀ y : xᴿ, ArchimedeanClass.mk (ω^ mk y.1.wlog) = .mk (mk y) := by
  intro ⟨y, hy⟩
  numeric
  rw [mk_wlog, ← veq_def]
  apply wpow_wlog_veq
  simpa [← mk_eq_mk] using (h.trans (Numeric.lt_right hy)).not_antisymmRel_symm

theorem numeric_of_forall_mk_ne_mk {x : IGame} [Numeric x] (h : 0 < x)
    (Hl : ∀ y (hy : y ∈ xᴸ), 0 < y →
      ArchimedeanClass.mk (@mk y (Numeric.of_mem_moves hy)) ≠ .mk (mk x))
    (Hr : ∀ y (hy : y ∈ xᴿ),
      ArchimedeanClass.mk (@mk y (Numeric.of_mem_moves hy)) ≠ .mk (mk x)) :
    Numeric !{IGame.wlog '' {y ∈ xᴸ | 0 < y} | IGame.wlog '' xᴿ} := by
  rw [ofSets_wlog_eq]
  exact numeric_of_forall_mk_ne_mk' h mk_wpow_wlog_left (mk_wpow_wlog_right h) Hl Hr

theorem wpow_equiv_of_forall_mk_ne_mk {x : IGame} [Numeric x] (h : 0 < x)
    (Hl : ∀ y (hy : y ∈ xᴸ), 0 < y →
      ArchimedeanClass.mk (@mk y (Numeric.of_mem_moves hy)) ≠ .mk (mk x))
    (Hr : ∀ y (hy : y ∈ xᴿ),
      ArchimedeanClass.mk (@mk y (Numeric.of_mem_moves hy)) ≠ .mk (mk x)) :
    ω^ !{IGame.wlog '' {y ∈ xᴸ | 0 < y} | IGame.wlog '' xᴿ} ≈ x := by
  rw [ofSets_wlog_eq]
  exact wpow_equiv_of_forall_mk_ne_mk' h mk_wpow_wlog_left (mk_wpow_wlog_right h) Hl Hr

/-- A game not commensurate with its positive options is a power of `ω`. -/
theorem mem_range_wpow_of_forall_mk_ne_mk {x : IGame} [Numeric x] (h : 0 < x)
    (Hl : ∀ y (hy : y ∈ xᴸ), 0 < y →
      ArchimedeanClass.mk (@mk y (Numeric.of_mem_moves hy)) ≠ .mk (mk x))
    (Hr : ∀ y (hy : y ∈ xᴿ),
      ArchimedeanClass.mk (@mk y (Numeric.of_mem_moves hy)) ≠ .mk (mk x)) :
    mk x ∈ range (ω^ ·) := by
  have hn := numeric_of_forall_mk_ne_mk h Hl Hr
  exact ⟨@mk _ hn, mk_eq (wpow_equiv_of_forall_mk_ne_mk h Hl Hr)⟩

@[simp]
theorem toSurreal_wpow (x : NatOrdinal) : (ω^ x).toSurreal = ω^ x.toSurreal :=
  Surreal.mk_eq (toIGame_wpow_equiv x)

end Surreal
end
