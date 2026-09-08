/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132N14.HopfPannwitzGeometry

/-!
# Bichromatic maximal distances

See the project entry module for the exact coordinate restrictions and source roles.
For two finite planar point sets, the number of pairs attaining their positive
cross-distance maximum is at most the sum of their cardinalities. The charging
proof treats singleton color classes and antipodal rays explicitly.
-/

namespace LeanPool.RareDistanceFields.BipartiteDiameter

open LeanPool.Erdos132N14
noncomputable section

open Classical in
theorem normSq_sub_of_dist_eq {a b : ℂ} {d : ℝ} (h : dist a b = d) :
    Complex.normSq (b - a) = d ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have hn : ‖b - a‖ = d := by simpa [Complex.dist_eq, norm_sub_rev] using h
  rw [hn]

open Classical in
theorem normSq_sub_of_dist_le {a b : ℂ} {d : ℝ} (hd : 0 ≤ d) (h : dist a b ≤ d) :
    Complex.normSq (b - a) ≤ d ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have hn : ‖b - a‖ ≤ d := by simpa [Complex.dist_eq, norm_sub_rev] using h
  exact (sq_le_sq₀ (norm_nonneg _) hd).mpr hn

open Classical in
/-- A second center excludes distinct antipodal equal rays. -/
theorem equal_rays_of_second_center {u v w a : ℂ} {d : ℝ}
    (huv : dist u v = d) (huw : dist u w = d) (hd : 0 < d)
    (hav : dist a v ≤ d) (haw : dist a w ≤ d) (hau : a ≠ u)
    (hc : planeCross (v - u) (w - u) = 0) : v = w := by
  let x := v - u
  let y := w - u
  let z := a - u
  have hx : diameterDot x x = d ^ 2 := by rw [planeDot_self]; exact normSq_sub_of_dist_eq huv
  have hy : diameterDot y y = d ^ 2 := by rw [planeDot_self]; exact normSq_sub_of_dist_eq huw
  have hxy : (diameterDot x y) ^ 2 = (d ^ 2) ^ 2 := by
    have h := plane_lagrange x y y
    rw [hc, mul_zero, add_zero, hx, hy] at h
    simpa [pow_two] using h.symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy with hplus|hminus
  · have hn : Complex.normSq (y - x) = 0 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      simp only [diameterDot] at hx hy hplus
      nlinarith
    have he := sub_eq_zero.mp (Complex.normSq_eq_zero.mp hn)
    dsimp [x, y] at he
    exact sub_left_injective he.symm
  · have hn : Complex.normSq (y + x) = 0 := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
      simp only [diameterDot] at hx hy hminus
      nlinarith
    have he : y = -x := eq_neg_of_add_eq_zero_left (Complex.normSq_eq_zero.mp hn)
    have hzv : Complex.normSq (x - z) ≤ d ^ 2 := by
      have h := normSq_sub_of_dist_le hd.le hav
      convert h using 1; dsimp [x, z]; congr 1; ring
    have hzw : Complex.normSq (y - z) ≤ d ^ 2 := by
      have h := normSq_sub_of_dist_le hd.le haw
      convert h using 1; dsimp [y, z]; congr 1; ring
    rw [he] at hzw
    have hz : Complex.normSq z = 0 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.neg_re, Complex.neg_im] at hzv hzw ⊢
      simp only [diameterDot] at hx
      nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    exact False.elim (hau (sub_eq_zero.mp (Complex.normSq_eq_zero.mp hz)))

variable {A B : Type*} [Fintype A] [Fintype B]

open Classical in
/-- All cross-color label pairs realizing the specified Euclidean distance. -/
def edges (a : A → ℂ) (b : B → ℂ) (d : ℝ) : Finset (A × B) :=
  Finset.univ.filter fun e => dist (a e.1) (b e.2) = d

open Classical in
/-- All equal-length rays at the left endpoint turn nonnegatively from this edge. -/
def leftExtreme (a : A → ℂ) (b : B → ℂ) (d : ℝ) (e : A × B) : Prop :=
  ∀ j, dist (a e.1) (b j) = d → 0 ≤ planeTurn (a e.1) (b e.2) (b j)

open Classical in
/-- All equal-length rays at the right endpoint turn nonnegatively from this edge. -/
def rightExtreme (a : A → ℂ) (b : B → ℂ) (d : ℝ) (e : A × B) : Prop :=
  ∀ i, dist (a i) (b e.2) = d → 0 ≤ planeTurn (b e.2) (a e.1) (a i)

omit [Fintype A] [Fintype B] in
open Classical in
theorem extreme_at_endpoint (a : A → ℂ) (b : B → ℂ) {d : ℝ} (hd : 0 < d)
    (hmax : ∀ i j, dist (a i) (b j) ≤ d) (e : A × B)
    (he : dist (a e.1) (b e.2) = d) :
    leftExtreme a b d e ∨ rightExtreme a b d e := by
  by_contra h
  have hl : ¬ leftExtreme a b d e := fun h' => h (Or.inl h')
  have hr : ¬ rightExtreme a b d e := fun h' => h (Or.inr h')
  simp only [leftExtreme, not_forall, not_le] at hl
  simp only [rightExtreme, not_forall, not_le] at hr
  obtain ⟨j, hj, htj⟩ := hl
  obtain ⟨i, hi, hti⟩ := hr
  have hh := opposite_turns_force_longer_pair he hj (by simpa only [dist_comm] using hi) hd htj hti
  have hm := hmax i j
  rw [dist_comm] at hh
  linarith

omit [Fintype A] [Fintype B] in
open Classical in
theorem left_unique (a : A → ℂ) (b : B → ℂ) (hb : Function.Injective b)
    {d : ℝ} (hd : 0 < d) (hmax : ∀ i j, dist (a i) (b j) ≤ d)
    (hother : ∀ i, ∃ i', a i' ≠ a i) {i : A} {j k : B}
    (hj : dist (a i) (b j) = d) (hk : dist (a i) (b k) = d)
    (hle : leftExtreme a b d (i, j)) (hke : leftExtreme a b d (i, k)) : j = k := by
  apply hb
  obtain ⟨i', hi'⟩ := hother i
  apply equal_rays_of_second_center hj hk hd (hmax i' j) (hmax i' k) hi'
  have h1 := hle k hk
  have h2 := hke j hj
  rw [planeTurn_swap] at h2
  change planeTurn (a i) (b j) (b k) = 0
  linarith

open Classical in
/-- The complete bipartite maximum-distance bound, with no position assumption. -/
theorem edges_card_le (a : A → ℂ) (b : B → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b) {d : ℝ}
    (hd : 0 < d) (hmax : ∀ i j, dist (a i) (b j) ≤ d) :
    (edges a b d).card ≤ Fintype.card A + Fintype.card B := by
  by_cases hA : Fintype.card A ≤ 1
  · calc
      (edges a b d).card ≤ Fintype.card A * Fintype.card B := by
        simpa [edges] using Finset.card_le_card (Finset.filter_subset (fun e : A × B => dist (a
          e.1) (b e.2) = d) Finset.univ)
      _ ≤ Fintype.card B := by nlinarith
      _ ≤ _ := Nat.le_add_left _ _
  by_cases hB : Fintype.card B ≤ 1
  · calc
      (edges a b d).card ≤ Fintype.card A * Fintype.card B := by
        simpa [edges] using Finset.card_le_card (Finset.filter_subset (fun e : A × B => dist (a
          e.1) (b e.2) = d) Finset.univ)
      _ ≤ Fintype.card A := by nlinarith
      _ ≤ _ := Nat.le_add_right _ _
  have hotherA (i : A) : ∃ i', a i' ≠ a i := by
    have : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨i', hi'⟩ := exists_ne i
    exact ⟨i', ha.ne hi'⟩
  have hotherB (j : B) : ∃ j', b j' ≠ b j := by
    have : Nontrivial B := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨j', hj'⟩ := exists_ne j
    exact ⟨j', hb.ne hj'⟩
  let owner : A × B → A ⊕ B := fun e =>
    if leftExtreme a b d e then Sum.inl e.1 else Sum.inr e.2
  have hinj : Set.InjOn owner (edges a b d) := by
    intro e he f hf hef
    have he' : dist (a e.1) (b e.2) = d := (Finset.mem_filter.mp he).2
    have hf' : dist (a f.1) (b f.2) = d := (Finset.mem_filter.mp hf).2
    dsimp [owner] at hef
    by_cases hl : leftExtreme a b d e <;> by_cases hr : leftExtreme a b d f
    all_goals simp only [hl, hr, ite_true, ite_false, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl] at hef
    · have hfirst : e.1 = f.1 := hef
      apply Prod.ext hfirst
      apply left_unique a b hb hd hmax hotherA he'
      · simpa [hfirst] using hf'
      · exact hl
      · simpa [hfirst] using hr
    · have hsecond : e.2 = f.2 := hef
      have heR := (extreme_at_endpoint a b hd hmax e he').resolve_left hl
      have hfR := (extreme_at_endpoint a b hd hmax f hf').resolve_left hr
      apply Prod.ext ?_ hsecond
      apply left_unique b a ha hd (fun j i => by simpa [dist_comm] using hmax i j)
        hotherB (by simpa [dist_comm] using he')
      · simpa [dist_comm, hsecond] using hf'
      · simpa [leftExtreme, rightExtreme, dist_comm] using heR
      · simpa [leftExtreme, rightExtreme, dist_comm, hsecond] using hfR
  have hcard := Finset.card_le_card_of_injOn owner (fun _ _ => Finset.mem_univ _) hinj
  simpa using hcard

end
end LeanPool.RareDistanceFields.BipartiteDiameter
