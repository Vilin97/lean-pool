/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.BipartiteDiameter
import LeanPool.RareDistanceFields.DyadicCoordinates
import LeanPool.RareDistanceFields.SplitCounts

/-!
# A rare distance at every occurring dyadic level

See the project entry module for the exact coordinate restrictions and source roles.
For any positive integer squared distance R maximal among distances with its
2-adic valuation, the unordered multiplicity of R is at most n.
-/

namespace LeanPool.RareDistanceFields.DyadicLevels

open IntegerPlane DyadicCoordinates SplitCounts
noncomputable section
universe u

open Classical in
theorem bichromatic_count_le {A B : Type*} [Fintype A] [Fintype B]
    (x : A → Point) (y : B → Point) (hx : Function.Injective x) (hy : Function.Injective y)
    (N : ℕ) (hN : 0 < N) (hmax : ∀ a b, sqDist (x a) (y b) ≤ N) :
    count (fun a b => sqDist (x a) (y b)) (N : ℤ) ≤ Fintype.card A + Fintype.card B := by
  classical
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := Real.sq_sqrt hpos.le
  have hb (a : A) (b : B) : dist (complexPoint (x a)) (complexPoint (y b)) ≤ Real.sqrt N := by
    have hh : (sqDist (x a) (y b) : ℝ) ≤ N := by exact_mod_cast hmax a b
    rw [← complex_dist_sq] at hh
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have he (a : A) (b : B) : dist (complexPoint (x a)) (complexPoint (y b)) = Real.sqrt N ↔
      sqDist (x a) (y b) = N := by
    constructor
    · intro h
      have hh := complex_dist_sq (x a) (y b)
      rw [h, hs] at hh
      exact_mod_cast hh.symm
    · intro h
      have hh := complex_dist_sq (x a) (y b)
      rw [h, Int.cast_natCast] at hh
      nlinarith [dist_nonneg (x := complexPoint (x a)) (y := complexPoint (y b)),
        Real.sqrt_nonneg (N : ℝ)]
  have hh := BipartiteDiameter.edges_card_le
    (fun a => complexPoint (x a)) (fun b => complexPoint (y b))
    (complexPoint_injective.comp hx) (complexPoint_injective.comp hy) (Real.sqrt_pos.mpr hpos) hb
  have hc : (BipartiteDiameter.edges (fun a => complexPoint (x a))
      (fun b => complexPoint (y b)) (Real.sqrt N)).card =
      count (fun a b => sqDist (x a) (y b)) (N : ℤ) := by
    simp only [BipartiteDiameter.edges, Finset.card_filter, Fintype.sum_prod_type, count]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hq : sqDist (x a) (y b) = N <;> simp [he, hq]
  rw [hc] at hh
  exact hh

open Classical in
/-- Ordered count form; induction divides each parity class by 1+i. -/
theorem level_max_count_le (N : ℕ) : ∀ {V : Type u} [Fintype V]
    (x : V → Point), Function.Injective x → 0 < N →
    (∀ p q, p ≠ q → padicValInt 2 (sqDist (x p) (x q)) = padicValInt 2 (N : ℤ) →
      sqDist (x p) (x q) ≤ N) →
    count (fun p q => sqDist (x p) (x q)) (N : ℤ) ≤ 2 * Fintype.card V := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro V inst x hx hN hmax
    let p : V → Prop := fun a => parity (x a) = 0
    let x0 : {a // p a} → Point := fun a => x a.1
    let x1 : {a // ¬p a} → Point := fun a => x a.1
    have hx0 : Function.Injective x0 := hx.comp Subtype.val_injective
    have hx1 : Function.Injective x1 := hx.comp Subtype.val_injective
    have hp0 (a : {a // p a}) : parity (x0 a) = 0 := a.2
    have hp1 (a : {a // ¬p a}) : parity (x1 a) = 1 :=
      (parity_zero_or_one (x1 a)).resolve_left a.2
    have hcross (a : {a // p a}) (b : {a // ¬p a}) : ¬2 ∣ sqDist (x0 a) (x1 b) := by
      rw [norm_even_iff, hp0 a, hp1 b]
      norm_num
    have hreverse : count (fun a b => sqDist (x1 a) (x0 b)) (N : ℤ) =
        count (fun a b => sqDist (x0 a) (x1 b)) (N : ℤ) := by
      rw [count_symm]
      simp only [sqDist_symm]
    have hsplit := count_split (fun a b => sqDist (x a) (x b)) (N : ℤ) p
    change count (fun a b => sqDist (x a) (x b)) (N : ℤ) =
      count (fun a b => sqDist (x0 a) (x0 b)) (N : ℤ) +
      count (fun a b => sqDist (x0 a) (x1 b)) (N : ℤ) +
      count (fun a b => sqDist (x1 a) (x0 b)) (N : ℤ) +
      count (fun a b => sqDist (x1 a) (x1 b)) (N : ℤ) at hsplit
    have hcards := card_split p
    by_cases h2 : 2 ∣ N
    · obtain ⟨M, hNM⟩ := h2
      have hM : 0 < M := by omega
      have hMN : M < N := by omega
      have hNM' : (N : ℤ) = 2 * M := by exact_mod_cast hNM
      have hc0 : count (fun a b => sqDist (x0 a) (x1 b)) (N : ℤ) = 0 := by
        apply count_zero
        intro a b he
        apply hcross a b
        rw [he, hNM']
        exact dvd_mul_right 2 (M : ℤ)
      have hwithin {W : Type u} [Fintype W] (z : W → V) (hz : Function.Injective z)
          (e : ℤ) (hpar : ∀ w, parity (x (z w)) = e) :
          count (fun a b => sqDist (x (z a)) (x (z b))) (N : ℤ) ≤ 2 * Fintype.card W := by
        let y : W → Point := fun w => halfPoint e (x (z w))
        have hscale (a b : W) : sqDist (x (z a)) (x (z b)) = 2 * sqDist (y a) (y b) :=
          halfPoint_scale e _ _ (hpar a) (hpar b)
        have hy : Function.Injective y := by
          intro a b he
          apply hz
          apply hx
          apply (sqDist_eq_zero _ _).mp
          rw [hscale, he]
          simp [sqDist, DyadicNorm.normSq]
        have hbound (a b : W) (hab : a ≠ b)
            (hv : padicValInt 2 (sqDist (y a) (y b)) = padicValInt 2 (M : ℤ)) :
            sqDist (y a) (y b) ≤ M := by
          have hnq := (sqDist_eq_zero (y a) (y b)).not.mpr (hy.ne hab)
          have hnM : (M : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hM
          have hh := hmax (z a) (z b) (hz.ne hab) (by
            rw [hscale, hNM', valuation_double _ hnq, valuation_double _ hnM, hv])
          rw [hscale, hNM'] at hh
          omega
        have hcount := ih M hMN y hy hM hbound
        have heq := count_congr (fun a b => sqDist (x (z a)) (x (z b)))
          (fun a b => sqDist (y a) (y b)) (N : ℤ) (M : ℤ) (by
            intro a b
            rw [hscale, hNM']
            omega)
        exact heq ▸ hcount
      have h0 := hwithin (fun a : {a // p a} => a.1) Subtype.val_injective 0 hp0
      have h1 := hwithin (fun a : {a // ¬p a} => a.1) Subtype.val_injective 1 hp1
      change count (fun a b => sqDist (x0 a) (x0 b)) (N : ℤ) ≤
        2 * Fintype.card {a // p a} at h0
      change count (fun a b => sqDist (x1 a) (x1 b)) (N : ℤ) ≤
        2 * Fintype.card {a // ¬p a} at h1
      rw [hreverse, hc0] at hsplit
      omega
    · have hnN : (N : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hN
      have h2' : ¬(2 : ℤ) ∣ N := by exact_mod_cast h2
      have hvN := (valuation_zero_iff (N : ℤ) hnN).mpr h2'
      have hwithin {W : Type u} [Fintype W] (y : W → Point) (e : ℤ)
          (he : ∀ w, parity (y w) = e) : count (fun a b => sqDist (y a) (y b)) (N : ℤ) = 0 := by
        apply count_zero
        intro a b hab
        apply h2'
        rw [← hab, norm_even_iff, he a, he b]
      have h0 := hwithin x0 0 hp0
      have h1 := hwithin x1 1 hp1
      have hbound (a : {a // p a}) (b : {a // ¬p a}) : sqDist (x0 a) (x1 b) ≤ N := by
        have hab : a.1 ≠ b.1 := by intro h; exact b.2 (h ▸ a.2)
        have hnq := (sqDist_eq_zero (x0 a) (x1 b)).not.mpr (hx.ne hab)
        exact hmax a.1 b.1 hab (by rw [(valuation_zero_iff _ hnq).mpr (hcross a b), hvN])
      have hc := bichromatic_count_le x0 x1 hx0 hx1 N hN hbound
      rw [hreverse, h0, h1] at hsplit
      omega

open Classical in
theorem level_max_multiplicity_le {V : Type*} [Fintype V] (x : V → Point)
    (hx : Function.Injective x) (N : ℕ) (hN : 0 < N)
    (hmax : ∀ p q, p ≠ q → padicValInt 2 (sqDist (x p) (x q)) = padicValInt 2 (N : ℤ) →
      sqDist (x p) (x q) ≤ N) : (graph x (N : ℤ)).edgeFinset.card ≤ Fintype.card V := by
  have hh := level_max_count_le N x hx hN hmax
  have he := count_eq_twice_edges (fun p q => sqDist (x p) (x q))
    (fun p q => sqDist_symm (x p) (x q)) (N : ℤ) (by
      intro p
      have hn : (0 : ℤ) < N := by exact_mod_cast hN
      simpa [sqDist, DyadicNorm.normSq] using ne_of_lt hn)
  change _ = 2 * (graph x (N : ℤ)).edgeFinset.card at he
  omega

end
end LeanPool.RareDistanceFields.DyadicLevels
