/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise516ThueMorse

/-!
# Exercise 5.16 follow-up (Scott 1981, PRG-19, Lecture V) — overlap-freeness of
`t`

The second Thue–Morse property Scott asks for: `t` is **overlap-free**, `t ≠
u·a·a·a·v` for any
finite `u` and nonempty `a`. This is a self-contained theorem of combinatorics on
words (Thue 1912);
it uses **no domain theory** (only the parity recurrences `tm (2n) = tm n`, `tm
(2n+1) = ¬ tm n` of
the bit-function `tm` from `Exercise516ThueMorse`) and has no leverage from
Mathlib, so it is proved
from scratch here.

We phrase an **overlap** of period `p ≥ 1` at offset `i` as a factor of length
`2p+1` with period
`p`: `Overlap i p := 1 ≤ p ∧ ∀ k ≤ p, tm (i+k) = tm (i+p+k)`. The main theorem
`no_overlap` shows no
overlap exists, and `overlap_free` is Scott's literal cube form `t ≠ u·a·a·a·v`
(an overlap is
weaker than a cube, so the cube form follows).

The proof is the classical descent: the two base facts are *no three consecutive
equal symbols*
(`no_three_consec`, the period-1 case) and a direct period-3 computation; an even
period `2q`
contracts to a period-`q` overlap via the substitution structure, and an odd
period `≥ 5` forces a
run of three equal symbols.
-/

namespace Domain.Neighborhood.Exercise516

open Domain.Neighborhood

/-! ### The two basic facts about consecutive symbols. -/

/-- An even-indexed symbol differs from its successor: `tm (2x) ≠ tm (2x+1)`. -/
theorem tm_two_mul_ne (x : ℕ) : tm (2 * x) ≠ tm (2 * x + 1) := by
  rw [tm_two_mul, tm_two_mul_add_one]
  cases tm x <;> simp

/-- `tm x = tm (x+1)` forces `x` to be **odd**: equal consecutive symbols only
straddle a block
boundary `(2m+1, 2m+2)`, never a block `(2m, 2m+1)`. -/
theorem odd_of_consec_eq {x : ℕ} (h : tm x = tm (x + 1)) : Odd x := by
  rcases Nat.even_or_odd x with ⟨m, hm⟩ | hodd
  · exfalso; rw [hm, ← two_mul] at h; exact tm_two_mul_ne m h
  · exact hodd

/-- **No three consecutive equal symbols** (the period-`1` case): `¬ (tm j = tm
(j+1) ∧
tm (j+1) = tm (j+2))`. If both held, `j` and `j+1` would both be odd. -/
theorem no_three_consec (j : ℕ) : ¬ (tm j = tm (j + 1) ∧ tm (j + 1) = tm (j + 2)) := by
  rintro ⟨h1, h2⟩
  have hj : Odd j := odd_of_consec_eq h1
  have hj1 : Odd (j + 1) := odd_of_consec_eq h2
  rcases hj with ⟨a, rfl⟩
  rcases hj1 with ⟨b, hb⟩
  omega

/-! ### Index reductions for `tm`. -/

theorem tm_of_eq_two_mul {x y : ℕ} (h : x = 2 * y) : tm x = tm y := by
  rw [h, tm_two_mul]

theorem tm_of_eq_two_mul_add_one {x y : ℕ} (h : x = 2 * y + 1) : tm x = !tm y := by
  rw [h, tm_two_mul_add_one]

/-! ### Overlaps. -/

/-- An **overlap** of period `p ≥ 1` at offset `i`: a factor of length `2p+1` with
period `p`. -/
def Overlap (i p : ℕ) : Prop := 1 ≤ p ∧ ∀ k, k ≤ p → tm (i + k) = tm (i + p + k)

/-- **Overlap-freeness of the Thue–Morse sequence** (Scott 1981, PRG-19; Thue
1912). No overlap
exists at any offset and period. -/
theorem no_overlap (p : ℕ) : ∀ i, ¬ Overlap i p := by
  induction p using Nat.strong_induction_on with
  | _ p IH =>
    intro i hov
    obtain ⟨hp1, hrel⟩ := hov
    obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' p
    · -- Even period `p = 2q`: contract to a period-`q` overlap.
      subst hq
      have hq1 : 1 ≤ q := by omega
      obtain ⟨a, hi | hi⟩ := Nat.even_or_odd' i
      · -- `i = 2a`: even positions give `tm (a+c) = tm (a+q+c)`.
        refine IH q (by omega) a ⟨hq1, fun c hc => ?_⟩
        have hk : 2 * c ≤ 2 * q := by omega
        have := hrel (2 * c) hk
        rw [tm_of_eq_two_mul (show i + 2 * c = 2 * (a + c) by omega),
          tm_of_eq_two_mul (show i + 2 * q + 2 * c = 2 * (a + q + c) by omega)] at this
        exact this
      · -- `i = 2a+1`: odd positions give `tm (a+c) = tm (a+q+c)` after stripping the `¬`.
        refine IH q (by omega) a ⟨hq1, fun c hc => ?_⟩
        have hk : 2 * c ≤ 2 * q := by omega
        have := hrel (2 * c) hk
        rw [tm_of_eq_two_mul_add_one (show i + 2 * c = 2 * (a + c) + 1 by omega),
          tm_of_eq_two_mul_add_one (show i + 2 * q + 2 * c = 2 * (a + q + c) + 1 by omega)] at this
        exact Bool.not_inj this
    · -- Odd period `p = 2q+1`.
      subst hq
      rcases Nat.eq_zero_or_pos q with rfl | hq1
      · -- `p = 1`: three consecutive equal symbols.
        refine no_three_consec i ⟨?_, ?_⟩
        · have := hrel 0 (by omega); simpa using this
        · have := hrel 1 (by omega); simpa [show i + 1 + 1 = i + 2 by omega] using this
      · -- `p = 2q+1 ≥ 3`.
        obtain ⟨a, hi | hi⟩ := Nat.even_or_odd' i
        · -- `i = 2a`: relations at `k = 0,1,2,3` give a run of three equal symbols at `a+q`.
          subst hi
          have r0 := hrel 0 (by omega)
          have r1 := hrel 1 (by omega)
          have r2 := hrel 2 (by omega)
          have r3 := hrel 3 (by omega)
          rw [tm_of_eq_two_mul (show 2 * a + 0 = 2 * a by omega),
            tm_of_eq_two_mul_add_one (show 2 * a + (2 * q + 1) + 0 = 2 * (a + q) +
              1 by omega)] at r0
          rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 = 2 * a + 1 by omega),
            tm_of_eq_two_mul (show 2 * a + (2 * q + 1) + 1 = 2 * (a + q + 1) by omega)] at r1
          rw [tm_of_eq_two_mul (show 2 * a + 2 = 2 * (a + 1) by omega),
            tm_of_eq_two_mul_add_one
              (show 2 * a + (2 * q + 1) + 2 = 2 * (a + q + 1) + 1 by omega)] at r2
          rw [tm_of_eq_two_mul_add_one (show 2 * a + 3 = 2 * (a + 1) + 1 by omega),
            tm_of_eq_two_mul (show 2 * a + (2 * q + 1) + 3 = 2 * (a + q + 2) by omega)] at r3
          refine no_three_consec (a + q) ⟨?_, ?_⟩
          · revert r0 r1; cases tm a <;> cases tm (a + q) <;> cases tm (a + q + 1) <;>
              simp_all
          · revert r1 r2 r3
            cases tm (a + 1) <;> cases tm (a + q + 1) <;> cases tm (a + q + 2) <;> cases tm a <;>
              simp_all
        · -- `i = 2a+1`.
          subst hi
          rcases Nat.eq_or_lt_of_le hq1 with hq2 | hq2
          · -- `q = 1`, i.e. `p = 3`: a direct contradiction from the four relations.
            subst hq2
            have r0 := hrel 0 (by omega)
            have r1 := hrel 1 (by omega)
            have r2 := hrel 2 (by omega)
            have r3 := hrel 3 (by omega)
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 0 = 2 * a + 1 by omega),
              tm_of_eq_two_mul (show 2 * a + 1 + (2 * 1 + 1) + 0 = 2 * (a + 2) by omega)] at r0
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 1 = 2 * (a + 1) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * 1 + 1) + 1 = 2 * (a + 2) + 1 by omega)] at r1
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 2 = 2 * (a + 1) + 1 by omega),
              tm_of_eq_two_mul (show 2 * a + 1 + (2 * 1 + 1) + 2 = 2 * (a + 3) by omega)] at r2
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 3 = 2 * (a + 2) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * 1 + 1) + 3 = 2 * (a + 3) + 1 by omega)] at r3
            revert r0 r1 r2 r3
            cases tm a <;> cases tm (a + 1) <;> cases tm (a + 2) <;> cases tm (a + 3) <;> simp_all
          · -- `q ≥ 2`, i.e. `p ≥ 5`: relations at `k = 1,2,3,4` give a run of three at `a+q+1`.
            have r1 := hrel 1 (by omega)
            have r2 := hrel 2 (by omega)
            have r3 := hrel 3 (by omega)
            have r4 := hrel 4 (by omega)
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 1 = 2 * (a + 1) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * q + 1) + 1 = 2 * (a + q + 1) + 1 by omega)] at r1
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 2 = 2 * (a + 1) + 1 by omega),
              tm_of_eq_two_mul
                (show 2 * a + 1 + (2 * q + 1) + 2 = 2 * (a + q + 2) by omega)] at r2
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 3 = 2 * (a + 2) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * q + 1) + 3 = 2 * (a + q + 2) + 1 by omega)] at r3
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 4 = 2 * (a + 2) + 1 by omega),
              tm_of_eq_two_mul
                (show 2 * a + 1 + (2 * q + 1) + 4 = 2 * (a + q + 3) by omega)] at r4
            refine no_three_consec (a + q + 1) ⟨?_, ?_⟩
            · revert r1 r2; cases tm (a + 1) <;> cases tm (a + q + 1) <;> cases tm (a + q + 2) <;>
                simp_all
            · revert r3 r4; cases tm (a + 2) <;> cases tm (a + q + 2) <;> cases tm (a + q + 3) <;>
                simp_all

/-! ### Cube-freeness — Scott's literal form `t ≠ u·a·a·a·v`. -/

/-- **The Thue–Morse sequence is cube-free.** A cube of period `p ≥ 1` (the factor
`a·a·a` with
`|a| = p`) is in particular an overlap, so none exists. -/
theorem no_cube (i p : ℕ) (hp : 1 ≤ p) :
    ¬ ∀ k, k < 2 * p → tm (i + k) = tm (i + p + k) := by
  intro hcube
  exact no_overlap p i ⟨hp, fun k hk => hcube k (by omega)⟩

open Example44 ExampleB NeighborhoodSystem

/-- The `j`-th bit of the length-`n` Thue–Morse prefix is `tm j`. -/
theorem tmListGetElemOptional {n j : ℕ} (h : j < n) : (tmList n)[j]? = some (tm j) := by
  rw [tmList, List.getElem?_map, List.getElem?_range h]
  rfl

/-- Positions differing by `|a|` inside `a ++ (a ++ a)` carry the same symbol, for
indices `< 2|a|`
(the three copies of `a` are identical). -/
theorem append_three_period {α : Type*} (a : List α) (m : ℕ) (hm : m < 2 * a.length) :
    (a ++ (a ++ a))[m]? = (a ++ (a ++ a))[m + a.length]? := by
  rcases lt_or_ge m a.length with h | h
  · rw [List.getElem?_append_left h,
      List.getElem?_append_right (by omega : a.length ≤ m + a.length),
      show m + a.length - a.length = m by omega, List.getElem?_append_left h]
  · rw [List.getElem?_append_right h,
      List.getElem?_append_right (by omega : a.length ≤ m + a.length),
      show m + a.length - a.length = m by omega,
      List.getElem?_append_left (by omega : m - a.length < a.length),
      List.getElem?_append_right (by omega : a.length ≤ m)]

/-- **Exercise 5.16 (Scott 1981, PRG-19) — `t` is cube-free.** Scott's literal
statement: `t` is not
of the form `u·a·a·a·v` for any finite prefix `u` and nonempty finite block `a`.
(`v` is whatever
follows; we phrase "`u·a·a·a` is a prefix of `t`" as `(u·a·a·a)⊥ ⊑ t`.) -/
theorem tElt_cube_free (u a : Str) (ha : a ≠ []) :
    ¬ strBot (u ++ a ++ a ++ a) ≤ tElt := by
  intro hle
  -- `u·a·a·a` is a prefix of `t`, hence equals the Thue–Morse prefix of its
  -- length.
  have hmem : tElt.mem (cone (u ++ a ++ a ++ a)) :=
    hle _ (strBot_mem_cone.mpr List.prefix_rfl)
  have heq : u ++ a ++ a ++ a = tmList (u ++ a ++ a ++ a).length :=
    (tElt_mem_cone_iff _).mp hmem
  -- Read off a cube in `tm` at offset `|u|`, period `|a|`.
  set N := (u ++ a ++ a ++ a).length with hN
  have hlen : N = u.length + 3 * a.length := by simp only [hN, List.length_append]; omega
  have hp : 1 ≤ a.length := by
    cases a with
    | nil => exact (ha rfl).elim
    | cons _ _ => simp
  refine no_cube u.length a.length hp (fun k hk => ?_)
  -- Both `tm (|u|+k)` and `tm (|u|+|a|+k)` read the same bit of `u·a·a·a`.
  have hk3 : u.length + k < N := by omega
  have hk3' : u.length + a.length + k < N := by omega
  have e1 : (tmList N)[u.length + k]? = some (tm (u.length + k)) := tmListGetElemOptional hk3
  have e2 : (tmList N)[u.length + a.length + k]? = some (tm (u.length + a.length + k)) :=
    tmListGetElemOptional hk3'
  -- Rewrite the prefix as `u ++ (a ++ (a ++ a))` and strip `u`.
  have hassoc : u ++ a ++ a ++ a = u ++ (a ++ (a ++ a)) := by
    simp [List.append_assoc]
  rw [← heq, hassoc] at e1 e2
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + k),
    show u.length + k - u.length = k by omega] at e1
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + a.length + k),
    show u.length + a.length + k - u.length = k + a.length by omega] at e2
  -- Period: `(a++(a++a))[k]? = (a++(a++a))[k+|a|]?`.
  have hper := append_three_period a k (by omega)
  have : some (tm (u.length + k)) = some (tm (u.length + a.length + k)) := by
    rw [← e1, hper, e2]
  exact Option.some.inj this

end Domain.Neighborhood.Exercise516
