/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.DyadicLevels

/-!
# Binary descent with a height independent of Euclidean length

See the project entry module for the exact coordinate restrictions and source roles.
The height controls termination and labels distance classes. The maximum
at each height valuation is taken in actual Euclidean distance.
-/

namespace LeanPool.RareDistanceFields.BinaryDescent

open SplitCounts DyadicCoordinates
noncomputable section
universe u

open Classical in
/-- A planar embedding with binary partitions and a height halved by descent. -/
structure Model (P : Type*) where
  /-- The complex embedding of the model. -/
  point : P → ℂ
  point_injective : Function.Injective point
  /-- An integer pair height determined by Euclidean distance. -/
  height : P → P → ℤ
  height_nonneg : ∀ p q, 0 ≤ height p q
  height_zero : ∀ p q, height p q = 0 ↔ p = q
  distance_height : ∀ p q r s, dist (point p) (point q) = dist (point r) (point s) →
    height p q = height r s
  /-- The binary class assigned to each point. -/
  parity : P → ℤ
  parity_values : ∀ p, parity p = 0 ∨ parity p = 1
  even_iff : ∀ p q, 2∣height p q ↔ parity p = parity q
  /-- The descent map within a chosen binary class. -/
  half : ℤ → P → P
  /-- The positive factor relating distances before and after descent. -/
  scale : ℝ
  scale_pos : 0 < scale
  half_height : ∀ e p q, parity p = e → parity q = e → height p q = 2 * height (half e p) (half e q)
  half_distance : ∀ e p q, parity p = e → parity q = e →
    dist (point p) (point q) = scale * dist (point (half e p)) (point (half e q))

namespace Model

variable {P : Type*} (S : Model P)

open Classical in
/-- Euclidean distance between the embedded model points. -/
abbrev distance (p q : P) : ℝ := dist (S.point p) (S.point q)

open Classical in
theorem height_pos (p q : P) (h : p ≠ q) : 0 < S.height p q := by
  have hn := (S.height_zero p q).not.mpr h
  have hp := S.height_nonneg p q
  omega

open Classical in
theorem bichromatic_count {A B : Type*} [Fintype A] [Fintype B]
    (x : A → P) (y : B → P) (hx : Function.Injective x) (hy : Function.Injective y)
    (d : ℝ) (hd : 0 < d) (hmax : ∀ a b, S.distance (x a) (y b) ≤ d) :
    count (fun a b => S.distance (x a) (y b)) d ≤ Fintype.card A + Fintype.card B := by
  have h := BipartiteDiameter.edges_card_le
    (S.point ∘ x) (S.point ∘ y) (S.point_injective.comp hx) (S.point_injective.comp hy) hd hmax
  simpa only [BipartiteDiameter.edges, Finset.card_filter, Fintype.sum_prod_type, count,
    Function.comp_apply] using h

open Classical in
theorem level_count (N : ℕ) : ∀ {V : Type u} [Fintype V] (x : V → P),
    Function.Injective x → 0 < N → ∀ d : ℝ, 0 < d →
    (∀ a b, S.distance (x a) (x b) = d → S.height (x a) (x b) = N) →
    (∀ a b, a ≠ b → padicValInt 2 (S.height (x a) (x b)) = padicValInt 2 (N : ℤ) →
      S.distance (x a) (x b) ≤ d) →
    count (fun a b => S.distance (x a) (x b)) d ≤ 2 * Fintype.card V := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro V inst x hx hN d hd hclass hmax
    let p : V → Prop := fun a => S.parity (x a) = 0
    let x0 : {a // p a} → P := fun a => x a.1
    let x1 : {a // ¬p a} → P := fun a => x a.1
    have hp0 (a : {a // p a}) : S.parity (x0 a) = 0 := a.2
    have hp1 (a : {a // ¬p a}) : S.parity (x1 a) = 1 :=
      (S.parity_values (x1 a)).resolve_left a.2
    have hcross (a : {a // p a}) (b : {a // ¬p a}) : ¬2∣S.height (x0 a) (x1 b) := by
      rw [S.even_iff, hp0 a, hp1 b]
      norm_num
    have hreverse : count (fun a b => S.distance (x1 a) (x0 b)) d =
        count (fun a b => S.distance (x0 a) (x1 b)) d := by
      rw [count_symm]
      simp only [distance, dist_comm]
    have hsplit := count_split (fun a b => S.distance (x a) (x b)) d p
    change count (fun a b => S.distance (x a) (x b)) d =
      count (fun a b => S.distance (x0 a) (x0 b)) d +
      count (fun a b => S.distance (x0 a) (x1 b)) d +
      count (fun a b => S.distance (x1 a) (x0 b)) d +
      count (fun a b => S.distance (x1 a) (x1 b)) d at hsplit
    have hcards := card_split p
    by_cases h2 : 2∣N
    · obtain ⟨M, hNM⟩ := h2
      have hM : 0 < M := by omega
      have hMN : M < N := by omega
      have hNM' : (N : ℤ) = 2 * M := by exact_mod_cast hNM
      have hc0 : count (fun a b => S.distance (x0 a) (x1 b)) d = 0 := by
        apply count_zero
        intro a b he
        apply hcross a b
        rw [hclass a.1 b.1 he, hNM']
        exact dvd_mul_right 2 (M : ℤ)
      have hwithin {W : Type u} [Fintype W] (z : W → V) (hz : Function.Injective z)
          (e : ℤ) (hpar : ∀ w, S.parity (x (z w)) = e) :
          count (fun a b => S.distance (x (z a)) (x (z b))) d ≤ 2 * Fintype.card W := by
        let y : W → P := fun w => S.half e (x (z w))
        have hs (a b : W) : S.height (x (z a)) (x (z b)) = 2 * S.height (y a) (y b) :=
          S.half_height e _ _ (hpar a) (hpar b)
        have hdscale (a b : W) : S.distance (x (z a)) (x (z b)) = S.scale * S.distance (y a) (y
          b) :=
          S.half_distance e _ _ (hpar a) (hpar b)
        have hy : Function.Injective y := by
          intro a b he
          apply hz
          apply hx
          apply (S.height_zero _ _).mp
          rw [hs, he, (S.height_zero _ _).mpr rfl, mul_zero]
        have heq (a b : W) : S.distance (x (z a)) (x (z b)) = d ↔
            S.distance (y a) (y b) = d / S.scale := by
          rw [hdscale, eq_div_iff (ne_of_gt S.scale_pos), mul_comm]
        have hcy (a b : W) (he : S.distance (y a) (y b) = d / S.scale) :
            S.height (y a) (y b) = M := by
          have hh := hclass (z a) (z b) ((heq a b).mpr he)
          rw [hs, hNM'] at hh
          omega
        have hby (a b : W) (hab : a ≠ b)
            (hv : padicValInt 2 (S.height (y a) (y b)) = padicValInt 2 (M : ℤ)) :
            S.distance (y a) (y b) ≤ d / S.scale := by
          have hn := (S.height_zero _ _).not.mpr (hy.ne hab)
          have hnM : (M : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hM
          have hh := hmax (z a) (z b) (hz.ne hab) (by
            rw [hs, hNM', valuation_double _ hn, valuation_double _ hnM, hv])
          rw [hdscale] at hh
          apply (le_div_iff₀ S.scale_pos).mpr
          simpa only [mul_comm] using hh
        have hh := ih M hMN y hy hM (d / S.scale) (div_pos hd S.scale_pos) hcy hby
        exact (count_congr _ _ d (d / S.scale) heq) ▸ hh
      have h0 := hwithin (fun a : {a // p a} => a.1) Subtype.val_injective 0 hp0
      have h1 := hwithin (fun a : {a // ¬p a} => a.1) Subtype.val_injective 1 hp1
      change count (fun a b => S.distance (x0 a) (x0 b)) d ≤
        2 * Fintype.card {a // p a} at h0
      change count (fun a b => S.distance (x1 a) (x1 b)) d ≤
        2 * Fintype.card {a // ¬p a} at h1
      rw [hreverse, hc0] at hsplit
      omega
    · have hnN : (N : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hN
      have h2' : ¬(2 : ℤ)∣N := by exact_mod_cast h2
      have hvN := (valuation_zero_iff (N : ℤ) hnN).mpr h2'
      have hwithin {W : Type u} [Fintype W] (z : W → V) (e : ℤ)
          (he : ∀ w, S.parity (x (z w)) = e) :
          count (fun a b => S.distance (x (z a)) (x (z b))) d = 0 := by
        apply count_zero
        intro a b hab
        apply h2'
        rw [←hclass (z a) (z b) hab, S.even_iff, he a, he b]
      have h0 := hwithin (fun a : {a // p a} => a.1) 0 hp0
      have h1 := hwithin (fun a : {a // ¬p a} => a.1) 1 hp1
      have hbound (a : {a // p a}) (b : {a // ¬p a}) : S.distance (x0 a) (x1 b) ≤ d := by
        have hab : a.1 ≠ b.1 := by intro h; exact b.2 (h ▸ a.2)
        have hn := (S.height_zero _ _).not.mpr (hx.ne hab)
        exact hmax a.1 b.1 hab (by rw [(valuation_zero_iff _ hn).mpr (hcross a b), hvN])
      have hc := S.bichromatic_count x0 x1 (hx.comp Subtype.val_injective)
        (hx.comp Subtype.val_injective) d hd hbound
      rw [hreverse, h0, h1] at hsplit
      omega

end Model
end
end LeanPool.RareDistanceFields.BinaryDescent
