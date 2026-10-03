/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Interfaces
public import LeanPool.Zeta32.Arith.Local.PoleFun

/-!
# The greedy allocation (the proof notes, §3)

Columns `b < p` with entries `c_b, c_b + 2, c_b + 4, …` (`c_b = colVal n p b`).
At step `i` take the smallest untaken entry `gval i`, from column `gpick i`; `galloc i b` is the
number of entries taken from column `b` before step `i`.

* `sum_galloc` : `∑_{b<p} galloc i b = i`;
* `allocCost_galloc` : `allocCost n p (galloc i) = ∑_{j<i} gval j`;
* `gval_le` : `gval i ≤ c_b + 2 galloc i b` for every `b < p` (greedy rule);
* `gbasis i = ∏_{b<p} (X + b)^{galloc i b}` is monic of degree `i`, with `galloc i b` zeros in the
  class of `-b` (`Adm_gbasis`).
-/

public section

open Finset Polynomial

namespace Zeta32.Arith.Local

variable (n p : ℕ)

lemma exists_greedy_choice (hp : 0 < p) (κ : ℕ → ℕ) :
    ∃ b ∈ Finset.range p, ∀ b' ∈ Finset.range p,
      colVal n p b + 2 * (κ b : ℤ) ≤ colVal n p b' + 2 * (κ b' : ℤ) :=
  Finset.exists_min_image (Finset.range p) (fun b => colVal n p b + 2 * (κ b : ℤ))
    ⟨0, Finset.mem_range.mpr hp⟩

/-- The greedy choice of a column. -/
noncomputable def gchoice (κ : ℕ → ℕ) : ℕ :=
  if h : 0 < p then (exists_greedy_choice n p h κ).choose else 0

/-- The allocation before step `i`. -/
@[expose]
noncomputable def galloc : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | i + 1 => fun b => galloc i b + if b = gchoice n p (galloc i) then 1 else 0

/-- The column chosen at step `i`. -/
@[expose]
noncomputable def gpick (i : ℕ) : ℕ := gchoice n p (galloc n p i)

/-- The entry taken at step `i`. -/
noncomputable def gval (i : ℕ) : ℤ := colVal n p (gpick n p i) + 2 * (galloc n p i (gpick n p i)
  : ℤ)

lemma galloc_succ (i b : ℕ) :
    galloc n p (i + 1) b = galloc n p i b + if b = gpick n p i then 1 else 0 := rfl

variable {n p}

lemma gpick_mem (hp : 0 < p) (i : ℕ) : gpick n p i ∈ Finset.range p := by
  unfold gpick gchoice
  rw [dite_eq_left hp]
  exact (exists_greedy_choice n p hp _).choose_spec.1

lemma gval_le (hp : 0 < p) (i : ℕ) {b : ℕ} (hb : b ∈ Finset.range p) :
    gval n p i ≤ colVal n p b + 2 * (galloc n p i b : ℤ) := by
  unfold gval gpick gchoice
  rw [dite_eq_left hp]
  exact (exists_greedy_choice n p hp _).choose_spec.2 b hb

lemma sum_galloc (hp : 0 < p) (i : ℕ) : ∑ b ∈ Finset.range p, galloc n p i b = i := by
  induction i with
  | zero => simp [galloc]
  | succ i ih =>
    simp only [galloc_succ, Finset.sum_add_distrib, ih]
    rw [Finset.sum_ite_eq' (Finset.range p) (gpick n p i), ite_eq_left (gpick_mem hp i)]

lemma allocCost_galloc (hp : 0 < p) (i : ℕ) :
    allocCost n p (galloc n p i) = ∑ j ∈ Finset.range i, gval n p j := by
  induction i with
  | zero => simp [allocCost, galloc]
  | succ i ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold allocCost
    have hterm : ∀ b ∈ Finset.range p,
        ((galloc n p (i + 1) b : ℤ) * colVal n p b +
            (galloc n p (i + 1) b : ℤ) * ((galloc n p (i + 1) b : ℤ) - 1)) =
          ((galloc n p i b : ℤ) * colVal n p b + (galloc n p i b : ℤ) * ((galloc n p i b : ℤ) - 1))
            + if b = gpick n p i then colVal n p b + 2 * (galloc n p i b : ℤ) else 0 := by
      intro b _
      rw [galloc_succ]
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_ite_eq' (Finset.range p) (gpick n p i), ite_eq_left (gpick_mem hp i)]
    rfl

/-! ### The basis -/

/-- `∏_{b<p} (X + b)^{galloc i b}`. -/
noncomputable def gbasis (n p i : ℕ) : ℚ[X] :=
  ∏ b ∈ Finset.range p, (X + C (b : ℚ)) ^ galloc n p i b

lemma gbasis_monic (i : ℕ) : (gbasis n p i).Monic :=
  monic_prod_of_monic _ _ fun _b _ => (monic_X_add_C _).pow _

lemma gbasis_natDegree (hp : 0 < p) (i : ℕ) : (gbasis n p i).natDegree = i := by
  unfold gbasis
  rw [natDegree_prod_of_monic _ _ fun b _ => (monic_X_add_C _).pow _]
  simp only [natDegree_pow, natDegree_X_add_C, mul_one]
  exact sum_galloc hp i

/-! ### Class counts -/

variable [hp : Fact p.Prime]

lemma X_add_C_eq (b : ℕ) : (X + C (b : ℚ) : ℚ[X]) = X - C (((-(b : ℤ)) : ℤ) : ℚ) := by
  push_cast; rw [C_neg, sub_neg_eq_add]

lemma Adm.X_add_C (b : ℕ) :
    Adm p (X + C (b : ℚ)) (fun c => if (((-(b : ℤ)) : ℤ) : ZMod p) = c then 1 else 0) := by
  rw [X_add_C_eq]; exact Adm.X_sub_C _

lemma neg_class_iff (j : ℕ) (c : ZMod p) :
    (((-(j : ℤ)) : ℤ) : ZMod p) = c ↔ j % p = (-c).val := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg, ← ZMod.val_natCast]
  exact ⟨fun h => by rw [h], fun h => ZMod.val_injective p (by rw [h])⟩

lemma neg_val_lt (c : ZMod p) : (-c).val ∈ Finset.range p := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  exact Finset.mem_range.mpr (ZMod.val_lt _)

lemma neg_val_eq_zero_iff (c : ZMod p) : (-c).val = 0 ↔ c = 0 := by
  rw [ZMod.val_eq_zero, neg_eq_zero]

lemma card_class (m : ℕ) (c : ZMod p) :
    ((Finset.Icc 1 m).filter fun j : ℕ => (((-(j : ℤ)) : ℤ) : ZMod p) = c).card =
      ((Finset.Icc 1 m).filter fun j : ℕ => j % p = (-c).val).card := by
  congr 1
  exact Finset.filter_congr fun j _ => neg_class_iff j c

lemma Adm_gbasis (i : ℕ) : Adm p (gbasis n p i) (fun c => (galloc n p i (-c).val : ℤ)) := by
  unfold gbasis
  have h := Adm.prod (Finset.range p) (fun b => (X + C (b : ℚ)) ^ galloc n p i b)
    (fun b c => (galloc n p i b : ℤ) * if (((-(b : ℤ)) : ℤ) : ZMod p) = c then 1 else 0)
    (fun b _ => (Adm.X_add_C b).pow _)
  refine h.mono fun c => ?_
  have hmem := neg_val_lt c
  have hle := Finset.single_le_sum (f := fun b => (galloc n p i b : ℤ) *
      if (((-(b : ℤ)) : ℤ) : ZMod p) = c then 1 else 0)
    (fun b _ => by positivity) hmem
  refine le_trans (le_of_eq ?_) hle
  have : (((-(((-c).val : ℕ) : ℤ)) : ℤ) : ZMod p) = c := by
    rw [neg_class_iff]
    have : NeZero p := ⟨hp.out.ne_zero⟩
    exact Nat.mod_eq_of_lt (ZMod.val_lt _)
  simp only [this, ite_true, mul_one]

lemma Adm_D (m : ℕ) :
    Adm p (Zeta32.D m)
      (fun c => (((Finset.Icc 1 m).filter fun j : ℕ => j % p = (-c).val).card : ℤ)) := by
  unfold Zeta32.D
  have h := Adm.prod (Finset.Icc 1 m) (fun j => X + C (j : ℚ))
    (fun j c => if (((-(j : ℤ)) : ℤ) : ZMod p) = c then (1 : ℤ) else 0)
    (fun j _ => Adm.X_add_C j)
  refine h.mono fun c => le_of_eq ?_
  rw [Finset.sum_boole, card_class]

end Zeta32.Arith.Local

end
