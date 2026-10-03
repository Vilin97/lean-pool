/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.Pullback
public import LeanPool.Zeta5Irrational.Arith.DirectBound
import LeanPool.Zeta5Irrational.Arith.DirectPoly
import Mathlib.Tactic.Ring.Basic

/-! # Entry bounds for numerators `∏ (t + γ²)`

For a multiset `M` of integers, `tpol M = ∏_{γ ∈ M} (t + γ²)`. Its pullback is
`pull K (tpol M) = ± x⁵ ∏_{γ ∈ M} (x - γ)(x + γ)`, so the direct bound applies to
`μ_X(tpol M / D_K)`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

/-- `∏_{γ ∈ M} (t + γ²)`. -/
@[expose] noncomputable def tpol (M : Multiset ℤ) : ℚ[X] :=
  (M.map fun γ : ℤ => X + C ((γ : ℚ) ^ 2)).prod

lemma tpol_add (M M' : Multiset ℤ) : tpol (M + M') = tpol M * tpol M' := by
  simp [tpol, Multiset.map_add, Multiset.prod_add]

/-- The `x`-roots of the pullback of `tpol M`. -/
def xroots (M : Multiset ℤ) : Multiset ℤ :=
  Multiset.replicate 5 0 + M + M.map (fun γ => -γ)

lemma pull_tpol (K : ℕ) (M : Multiset ℤ) :
    pull K (tpol M) = numOf ((-1 : ℚ) ^ (K + M.card)) (xroots M) := by
  unfold pull tpol numOf xroots
  rw [multiset_prod_comp, Multiset.map_map]
  simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]
  have h1 :
    ∀ γ : ℤ,
      ((fun q : ℚ[X] => q.comp (-X ^ 2)) ∘ fun γ : ℤ => X + C ((γ : ℚ) ^ 2)) γ =
        C (-1 : ℚ) * ((X - C (γ : ℚ)) * (X - C ((-γ : ℤ) : ℚ))) := by
    intro γ
    simp only [Function.comp, add_comp, X_comp, C_comp]
    push_cast
    rw [map_neg, map_one, C_neg, C_pow]; ring
  rw [Multiset.map_congr rfl fun γ _ => h1 γ, Multiset.prod_map_mul, Multiset.prod_map_mul]
  simp only [Multiset.map_const', Multiset.prod_replicate, Multiset.map_map, Function.comp]
  simp only [Int.cast_zero, map_zero, sub_zero]
  rw [pow_add, map_mul, map_pow, map_pow]
  ring

/-- Number of `x`-roots in the class `c`. -/
lemma cnt_xroots (p : ℕ) (M : Multiset ℤ) (c : ZMod p) :
    cnt p (xroots M) c =
      (if c = 0 then 5 else 0) + (M.filter fun γ : ℤ => (γ : ZMod p) = c).card +
        (M.filter fun γ : ℤ => (γ : ZMod p) = -c).card := by
  unfold cnt xroots
  rw [Multiset.filter_add, Multiset.filter_add, Multiset.card_add, Multiset.card_add]
  congr 1
  · congr 1
    by_cases h : (0 : ZMod p) = c
    · rw [ite_eq_left h.symm,
        Multiset.filter_eq_self.mpr
          (fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; simpa using h)]
      simp
    · rw [ite_eq_right (Ne.symm h),
        Multiset.filter_eq_nil.mpr
          (fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; simpa using h)]
      simp
  · rw [Multiset.filter_map, Multiset.card_map]
    congr 1
    refine Multiset.filter_congr fun γ _ => ?_
    simp only [Function.comp, Int.cast_neg]
    constructor <;> intro h <;> [rw [← h]; rw [h]] <;> ring

/-- **Entry bound** for `μ_X(tpol M / D_K)`. -/
theorem μX_tpol_bound {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (K : ℕ) (M : Multiset ℤ)
    (hsep : Sep p (PlK K)) (hK : K < p ^ 2) (hdeg : 5 + 2 * M.card - 2 * K + 1 < p ^ 2) (β : ℚ)
    (hβ :
      ∀ c : ZMod p,
        β ≤
          ((if c = 0 then 5 else 0) + (M.filter fun γ : ℤ => (γ : ZMod p) = c).card +
                (M.filter fun γ : ℤ => (γ : ZMod p) = -c).card :
              ℕ) -
            (plc p (PlK K) c).card) :
    GV p (μX K (tpol M)) (β - 4) := by
  rw [μX_eq_tauX, pull_tpol]
  have hκ : VG p ((-1 : ℚ) ^ (K + M.card)) 0 := by
    rcases neg_one_pow_eq_or ℚ (K + M.card) with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  refine tauX_direct hp5 _ hκ _ _ hsep ?_ ?_ β ?_
  · intro r hr
    rw [PlK, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hr
    rcases hr with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [dd_nat]; have := (Finset.mem_Icc.mp hj).2; omega
    · rw [dd_neg (Finset.mem_Icc.mp hj).1]; have := (Finset.mem_Icc.mp hj).2; omega
  · have : (xroots M).card = 5 + 2 * M.card := by simp [xroots]; ring
    rw [this, card_PlK]; exact hdeg
  · intro c
    rw [cnt_xroots]; exact hβ c

end Zeta5Irrational
