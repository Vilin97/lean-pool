/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.Sensitivity.Defs
import LeanPool.Sensitivity.Multilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum

/-!
# Parity Function and the Imbalance Lemma

The parity function `(-1)^{|x|}` and its interaction with the Möbius
expansion of a Boolean function. The main quantitative output is a parity
imbalance lemma: a Boolean function whose top Möbius coefficient is nonzero
must have a "majority" parity-sign class strictly larger than `2^{n-1}`.

## Main results

* `LeanPoolSensitivity.parity_flipBit` — flipping any bit negates the parity.
* `LeanPoolSensitivity.moebius_parity_sum` — the sum of `f`'s parity-signed
  values equals `2 · (-1)^n · c_univ(f)`.
* `LeanPoolSensitivity.fullDegree_imbalance` — if `f` has full multilinear
  degree, one parity-sign class has more than `2^{n-1}` vertices.
-/

namespace LeanPoolSensitivity

variable {n : ℕ}

/-- The parity sign of an input: `(-1)^{number of true coordinates}`. -/
def parity (x : Fin n → Bool) : ℤ :=
  (-1) ^ (Finset.univ.filter (fun i => x i)).card

namespace BoolFun

/-- The `±1`-valued encoding of a Boolean function: `true ↦ 1`,
`false ↦ -1`. -/
def pmOne (f : BoolFun n) (x : Fin n → Bool) : ℤ :=
  if f x then 1 else -1

/-- The parity-signed function `g(x) = f_pm(x) · parity(x)`. -/
def paritySigned (f : BoolFun n) (x : Fin n → Bool) : ℤ :=
  f.pmOne x * parity x

/-- The `±1` encoding is never zero. -/
theorem pmOne_ne_zero (f : BoolFun n) (x : Fin n → Bool) :
    f.pmOne x ≠ 0 := by
  unfold pmOne; split <;> omega

end BoolFun

/-- The parity sign is never zero. -/
theorem parity_ne_zero (x : Fin n → Bool) : parity x ≠ 0 := by
  unfold parity; positivity

/-- Flipping any single bit negates the parity. -/
theorem parity_flipBit (x : Fin n → Bool) (i : Fin n) :
    parity (flipBit x i) = -parity x := by
  unfold parity
  have key : ∀ (a b : ℕ), a + 1 = b ∨ b + 1 = a →
      (-1 : ℤ) ^ a = -((-1 : ℤ) ^ b) := by
    intro a b hab
    rcases hab with ⟨rfl⟩ | ⟨rfl⟩ <;> simp [pow_succ]
  apply key
  cases hxi : x i
  · right
    have hS : Finset.univ.filter (fun j : Fin n => flipBit x i j) =
              insert i (Finset.univ.filter (fun j : Fin n => x j)) := by
      ext j; simp [flipBit]; by_cases h : j = i <;> simp [h, hxi, Function.update]
    have hni : i ∉ Finset.univ.filter (fun j : Fin n => x j) := by simp [hxi]
    rw [hS, Finset.card_insert_of_notMem hni]
  · left
    have hS : Finset.univ.filter (fun j : Fin n => flipBit x i j) =
              (Finset.univ.filter (fun j : Fin n => x j)).erase i := by
      ext j; simp [flipBit]; by_cases h : j = i <;> simp [h, hxi, Function.update]
    have hi : i ∈ Finset.univ.filter (fun j : Fin n => x j) := by simp [hxi]
    rw [hS, Finset.card_erase_of_mem hi]
    have hpos := Finset.card_pos.mpr ⟨i, hi⟩
    omega

namespace BoolFun

/-- If the parity-signed value of `f` is unchanged by a bit flip, then `f` is
sensitive at that input in that direction. -/
theorem sensitiveAt_of_paritySigned_eq (f : BoolFun n)
    (x : Fin n → Bool) (i : Fin n)
    (h : f.paritySigned (flipBit x i) = f.paritySigned x) :
    f.sensitiveAt x i := by
  unfold sensitiveAt paritySigned pmOne at *
  rw [parity_flipBit] at h
  intro heq
  rw [heq] at h
  have hpnz := parity_ne_zero x
  rcases mul_eq_zero.mp (by linarith : (if f x then (1 : ℤ) else -1) * (-2 * parity x) = 0)
    with h1 | h1
  · split_ifs at h1
    omega
  · exact hpnz (by linarith)

end BoolFun

/-- For `n ≥ 1`, the sum of parity signs over all inputs is zero, since
flipping bit `0` is an involution that negates parity. -/
private theorem parity_sum_zero (hn : 0 < n) :
    ∑ x : Fin n → Bool, parity x = 0 := by
  have i₀ : Fin n := ⟨0, hn⟩
  have hbij : Function.Bijective (fun x : Fin n → Bool => flipBit x i₀) :=
    ⟨fun a b h => by simpa [flipBit_flipBit_same] using congr_arg (flipBit · i₀) h,
     fun y => ⟨flipBit y i₀, flipBit_flipBit_same y i₀⟩⟩
  have h : ∑ x : Fin n → Bool, parity x = ∑ x : Fin n → Bool, -parity x := by
    rw [← Fintype.sum_bijective _ hbij _ _ (fun x => rfl)]
    simp [parity_flipBit]
  linarith [Finset.sum_neg_distrib (f := fun x : Fin n → Bool => parity x) (s := Finset.univ)]

/-- The indicator function is a left inverse to the "true bits" map. -/
private theorem indicator_filter_true (x : Fin n → Bool) :
    indicator (Finset.univ.filter (fun i => x i)) = x := by
  ext i
  simp [indicator]

/-- The "true bits" map is a left inverse to indicator. -/
private theorem filter_true_indicator (T : Finset (Fin n)) :
    Finset.univ.filter (fun i => indicator T i = true) = T := by
  ext i
  simp [indicator]

/-- Key identity: the parity-weighted sum recovers the top Möbius coefficient,
`∑_x f_pm(x) · parity(x) = 2 · (-1)^n · c_univ(f)`. -/
theorem moebius_parity_sum (f : BoolFun n) (hn : 0 < n) :
    ∑ x : Fin n → Bool, f.paritySigned x =
    2 * (-1 : ℤ) ^ n * f.moebius Finset.univ := by
  have pmOne_eq : ∀ x, f.pmOne x = 2 * boolToInt (f x) - 1 := fun x => by
    unfold BoolFun.pmOne boolToInt; split <;> ring
  simp_rw [BoolFun.paritySigned, pmOne_eq, sub_mul, Finset.sum_sub_distrib, one_mul,
    parity_sum_zero hn, sub_zero]
  suffices h : ∑ x : Fin n → Bool, boolToInt (f x) * parity x =
               (-1 : ℤ) ^ n * f.moebius Finset.univ by
    simp_rw [show ∀ x : Fin n → Bool,
      2 * boolToInt (f x) * parity x = 2 * (boolToInt (f x) * parity x) from fun x => by ring]
    rw [← Finset.mul_sum, h]; ring
  unfold BoolFun.moebius parity
  rw [Finset.mul_sum]
  conv_rhs =>
    arg 2; ext T
    rw [← mul_assoc, ← pow_add, Finset.card_univ, Fintype.card_fin]
    rw [show n + (n - Finset.card T) = Finset.card T + 2 * (n - Finset.card T) from by
      have : T.card ≤ n := by simpa using Finset.card_le_univ T
      omega]
    rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  rw [show Finset.univ.powerset = (Finset.univ : Finset (Finset (Fin n))) from by ext S; simp]
  symm
  apply Fintype.sum_equiv
    (Equiv.ofBijective (fun T : Finset (Fin n) => indicator T)
      ⟨fun S T h => by
         have h' : indicator S = indicator T := h
         rw [← filter_true_indicator S, h', filter_true_indicator],
       fun x => ⟨Finset.univ.filter (fun i => x i), indicator_filter_true x⟩⟩)
  intro T
  simp only [Equiv.ofBijective_apply]
  have hcard := congrArg Finset.card (filter_true_indicator T)
  rw [show
        (-1 : ℤ) ^ T.card * boolToInt (f (indicator T)) =
          boolToInt (f (indicator T)) * (-1) ^ T.card from by ring]
  congr 2
  exact hcard.symm

/-- If `f` has full multilinear degree (`c_univ(f) ≠ 0`), then the
parity-weighted sum is nonzero. -/
theorem fullDegree_paritySigned_sum_ne_zero (f : BoolFun n) (hn : 0 < n)
    (h : f.moebius Finset.univ ≠ 0) :
    ∑ x : Fin n → Bool, f.paritySigned x ≠ 0 := by
  rw [moebius_parity_sum _ hn]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) h
  · omega
  · positivity

/-- **Parity imbalance.** If `f` has full multilinear degree, then one of the
two parity-sign classes contains more than `2^{n-1}` inputs. -/
theorem fullDegree_imbalance (f : BoolFun n) (hn : 0 < n)
    (h : f.moebius Finset.univ ≠ 0) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      2 ^ (n - 1) < (Finset.univ.filter (fun x : Fin n → Bool =>
        f.paritySigned x = c)).card := by
  have hne := fullDegree_paritySigned_sum_ne_zero f hn h
  have hval : ∀ x : Fin n → Bool, f.paritySigned x = 1 ∨ f.paritySigned x = -1 := by
    intro x; unfold BoolFun.paritySigned BoolFun.pmOne parity
    rcases neg_one_pow_eq_or (R := ℤ)
      (Finset.univ.filter (fun i => x i)).card with h | h <;>
      cases f x <;> simp [h]
  set A := Finset.univ.filter (fun x : Fin n → Bool => f.paritySigned x = 1)
  set B := Finset.univ.filter (fun x : Fin n → Bool => f.paritySigned x = -1)
  have hunion : A ∪ B = Finset.univ := by
    ext x; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, A, B]
    exact iff_of_true (hval x) trivial
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hxA hxB
    linarith
  have hsum : ∑ x : Fin n → Bool, f.paritySigned x = ↑A.card - ↑B.card := by
    have hA_sum : ∑ x ∈ A, f.paritySigned x = (A.card : ℤ) := by
      calc ∑ x ∈ A, f.paritySigned x = ∑ _ ∈ A, (1 : ℤ) :=
            Finset.sum_congr rfl (fun x hx => by
              simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx)
        _ = ↑A.card := by simp
    have hB_sum : ∑ x ∈ B, f.paritySigned x = -(↑B.card : ℤ) := by
      calc ∑ x ∈ B, f.paritySigned x = ∑ _ ∈ B, (-1 : ℤ) :=
            Finset.sum_congr rfl (fun x hx => by
              simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx)
        _ = -(↑B.card : ℤ) := by simp
    have key : ∑ x ∈ A ∪ B, f.paritySigned x = ↑A.card - ↑B.card := by
      rw [Finset.sum_union hdisj, hA_sum, hB_sum]; ring
    rwa [hunion] at key
  have htotal : A.card + B.card = 2 ^ n := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ,
        Fintype.card_pi_const, Fintype.card_bool]
  by_cases hA : A.card > 2 ^ (n - 1)
  · exact ⟨1, Or.inl rfl, hA⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have hA : A.card ≤ 2 ^ (n - 1) := Nat.not_lt.mp hA
    change 2 ^ (n - 1) < B.card
    have h2pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 from by omega]
      rw [pow_succ]; ring
    suffices hne' : B.card ≠ 2 ^ (n - 1) by
      set p := 2 ^ (n - 1)
      omega
    intro heq
    have hA_eq : A.card = 2 ^ (n - 1) := by
      set p := 2 ^ (n - 1)
      omega
    apply hne
    rw [hsum, hA_eq, heq]; push_cast; omega

end LeanPoolSensitivity
