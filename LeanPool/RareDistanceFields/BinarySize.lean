/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.BinaryDescent

/-!
# Binary size bound for a separate integral descent height

See the project entry module for the exact coordinate restrictions and source roles.
A binary descent model with k occupied height valuations has at most 2^k points.
The induction height need not equal or increase with Euclidean distance.
-/

namespace LeanPool.RareDistanceFields.BinarySize

open BinaryDescent DyadicCoordinates SplitCounts
noncomputable section
universe u

variable {P : Type*} (S : Model P)

open Classical in
theorem card_le_pow_of_bound (M : ℕ) : ∀ {V : Type u} [Fintype V]
    (x : V → P), Function.Injective x → ∀ L : Finset ℕ,
    (∀ a b, S.height (x a) (x b) ≤ M) →
    (∀ a b, a ≠ b → padicValInt 2 (S.height (x a) (x b)) ∈ L) →
    Fintype.card V ≤ 2 ^ L.card := by
  classical
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro V inst x hx L hbound hL
    by_cases hM : M = 0
    · have hc : Fintype.card V ≤ 1 := by
        apply Fintype.card_le_one_iff.mpr
        intro a b
        apply hx
        apply (S.height_zero _ _).mp
        have hh := hbound a b
        have hn : 0 ≤ S.height (x a) (x b) := by
          exact S.height_nonneg _ _
        rw [hM] at hh
        omega
      exact hc.trans (Nat.one_le_pow _ _ (by decide))
    have hMpos : 0 < M := by omega
    have hsmaller : M / 2 < M := Nat.div_lt_self hMpos (by decide)
    let p : V → Prop := fun a => S.parity (x a) = 0
    let L' : Finset ℕ := (L.erase 0).image Nat.pred
    have hcardL : L'.card ≤ (L.erase 0).card := Finset.card_image_le
    have hcardL' : L'.card ≤ L.card := hcardL.trans (Finset.card_le_card (Finset.erase_subset _ _))
    have hpow : 2 ^ L'.card ≤ 2 ^ L.card := Nat.pow_le_pow_right (by decide) hcardL'
    have hwithin {W : Type u} [Fintype W] (z : W → V) (hz : Function.Injective z)
        (e : ℤ) (hpar : ∀ w, S.parity (x (z w)) = e) : Fintype.card W ≤ 2 ^ L'.card := by
      let y : W → P := fun w => S.half e (x (z w))
      have hscale (a b : W) : S.height (x (z a)) (x (z b)) = 2 * S.height (y a) (y b) :=
        S.half_height e _ _ (hpar a) (hpar b)
      have hy : Function.Injective y := by
        intro a b he
        apply hz
        apply hx
        apply (S.height_zero _ _).mp
        rw [hscale, he, (S.height_zero _ _).mpr rfl, mul_zero]
      apply ih (M / 2) hsmaller y hy L'
      · intro a b
        have hh := hbound (z a) (z b)
        rw [hscale] at hh
        rw [Int.natCast_ediv]
        omega
      · intro a b hab
        have hn := (S.height_zero (y a) (y b)).not.mpr (hy.ne hab)
        have hs : padicValInt 2 (S.height (x (z a)) (x (z b))) =
            1 + padicValInt 2 (S.height (y a) (y b)) := by rw [hscale, valuation_double _ hn]
        apply Finset.mem_image.mpr
        refine ⟨padicValInt 2 (S.height (x (z a)) (x (z b))), ?_, ?_⟩
        · apply Finset.mem_erase.mpr
          exact ⟨by omega, hL (z a) (z b) (hz.ne hab)⟩
        · rw [hs]
          simp
    have h0 := hwithin (fun a : {a // p a} => a.1) Subtype.val_injective 0 (fun a => a.2)
    have h1 := hwithin (fun a : {a // ¬p a} => a.1) Subtype.val_injective 1
      (fun a => (S.parity_values (x a.1)).resolve_left a.2)
    have hcards := card_split p
    by_cases hz : 0 ∈ L
    · have hLpos : 0 < L.card := Finset.card_pos.mpr ⟨0, hz⟩
      rw [Finset.card_erase_of_mem hz] at hcardL
      have hp : 2 * 2 ^ L'.card ≤ 2 ^ L.card := by
        calc
          2 * 2 ^ L'.card = 2 ^ (L'.card + 1) := by rw [pow_succ]; omega
          _ ≤ 2 ^ L.card := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · by_cases h0empty : Fintype.card {a // p a} = 0
      · omega
      · have h0pos : 0 < Fintype.card {a // p a} := by omega
        obtain ⟨a⟩ := Fintype.card_pos_iff.mp h0pos
        have hempty : IsEmpty {b // ¬p b} := by
          constructor
          intro b
          have hab : a.1 ≠ b.1 := by intro h; exact b.2 (h ▸ a.2)
          have hpar : S.parity (x b.1) = 1 := (S.parity_values _).resolve_left b.2
          have hn := (S.height_zero (x a.1) (x b.1)).not.mpr (hx.ne hab)
          have hodd : ¬2 ∣ S.height (x a.1) (x b.1) := by
            rw [S.even_iff, a.2, hpar]
            norm_num
          have hv := (valuation_zero_iff _ hn).mpr hodd
          exact hz (hv ▸ hL a.1 b.1 hab)
        have he : Fintype.card {a // ¬p a} = 0 := Fintype.card_eq_zero
        omega

open Classical in
/-- The 2-adic height levels realized between distinct configuration labels. -/
def levels {V : Type*} [Fintype V] (x : V → P) : Finset ℕ :=
  Finset.univ.offDiag.image (fun ab => padicValInt 2 (S.height (x ab.1) (x ab.2)))

open Classical in
theorem mem_levels {V : Type*} [Fintype V] (x : V → P) (a b : V) (hab : a ≠ b) :
    padicValInt 2 (S.height (x a) (x b)) ∈ levels S x := by
  exact Finset.mem_image.mpr ⟨(a, b), by simp [hab], rfl⟩

open Classical in
theorem card_le_pow_levels {V : Type*} [Fintype V] (x : V → P)
    (hx : Function.Injective x) : Fintype.card V ≤ 2 ^ (levels S x).card := by
  classical
  let M := (Finset.univ : Finset (V × V)).sup (fun ab => (S.height (x ab.1) (x ab.2)).toNat)
  apply card_le_pow_of_bound S M x hx (levels S x)
  · intro a b
    have hn : 0 ≤ S.height (x a) (x b) := by
      exact S.height_nonneg _ _
    have hh : (S.height (x a) (x b)).toNat ≤ M :=
      Finset.le_sup (f := fun ab => (S.height (x ab.1) (x ab.2)).toNat) (Finset.mem_univ (a, b))
    omega
  · exact mem_levels S x

end
end LeanPool.RareDistanceFields.BinarySize
