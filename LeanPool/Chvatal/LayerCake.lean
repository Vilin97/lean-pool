/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Finite layer-cake decomposition

Section 5 lifts inequalities for hereditary families to inequalities for
nonnegative decreasing weights by layer cake. On a finite space, integration can
be replaced by repeatedly subtracting the smallest positive weight from its
support. The support is a lower set, and each step strictly shrinks it.
-/

@[expose] public section

open scoped BigOperators

namespace Chvatal

variable {α : Type*} [Fintype α] [Preorder α]

/-- The finite layer-cake principle used in Section 5 (Proposition 5.3): if a
signed function has nonnegative sum on every lower set, then its scalar product
with every nonnegative antitone weight is nonnegative. This also covers an empty
underlying type. -/
theorem sum_mul_antitone_nonneg_of_lowerSets (c : α → ℝ)
    (hc : ∀ D : Finset α, IsLowerSet (D : Set α) → 0 ≤ ∑ x ∈ D, c x)
    (ω : α → ℝ) (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    0 ≤ ∑ x, c x * ω x := by
  classical
  suffices hmain : ∀ n (w : α → ℝ),
      (Finset.univ.filter (fun x => 0 < w x)).card = n →
      (∀ x, 0 ≤ w x) → Antitone w → 0 ≤ ∑ x, c x * w x by
    exact hmain _ ω rfl hω hanti
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn hw hwanti
    let D := Finset.univ.filter (fun x => 0 < w x)
    have hDlower : IsLowerSet (D : Set α) := by
      intro x y hxy hy
      simp only [D, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact lt_of_lt_of_le hy (hwanti hxy)
    by_cases hD : D.Nonempty
    · obtain ⟨a, ha, hamin⟩ := Finset.exists_min_image D w hD
      have ha_pos : 0 < w a := (Finset.mem_filter.mp ha).2
      let w' : α → ℝ := fun x => max (w x - w a) 0
      have hw' : ∀ x, 0 ≤ w' x := fun x => le_max_right _ _
      have hw'anti : Antitone w' := by
        intro x y hxy
        exact max_le_max (sub_le_sub_right (hwanti hxy) (w a)) le_rfl
      have hw'le (x) : w' x ≤ w x :=
        max_le (sub_le_self _ ha_pos.le) (hw x)
      have hsmaller : (Finset.univ.filter (fun x => 0 < w' x)).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact lt_of_lt_of_le hx (hw'le x)
        · intro heq
          have ha' : a ∈ Finset.univ.filter (fun x => 0 < w' x) := by
            rw [heq]
            exact ha
          simpa [w'] using (Finset.mem_filter.mp ha').2
      have hrec : 0 ≤ ∑ x, c x * w' x := ih _ hsmaller w' rfl hw' hw'anti
      have hdecomp (x) : w x = w' x + if x ∈ D then w a else 0 := by
        by_cases hx : x ∈ D
        · have hax : w a ≤ w x := hamin x hx
          simp only [w', max_eq_left (sub_nonneg.mpr hax), ite_eq_left hx]
          ring
        · have hxzero : w x = 0 := by
            have hxle : w x ≤ 0 := by simpa [D] using hx
            exact le_antisymm hxle (hw x)
          simp [w', hx, hxzero, ha_pos.le]
      have hsum : (∑ x, c x * w x) =
          (∑ x, c x * w' x) + w a * ∑ x ∈ D, c x := by
        have hpoint (x) : c x * w x =
            c x * w' x + c x * (if x ∈ D then w a else 0) := by
          rw [hdecomp x, mul_add]
        simp_rw [hpoint]
        rw [Finset.sum_add_distrib]
        congr 1
        simp only [mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      rw [hsum]
      exact add_nonneg hrec (mul_nonneg ha_pos.le (hc D hDlower))
    · have hwzero (x) : w x = 0 := by
        have hx : ¬0 < w x := by
          intro hx
          exact hD ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
        exact le_antisymm (le_of_not_gt hx) (hw x)
      simp [hwzero]

end Chvatal
