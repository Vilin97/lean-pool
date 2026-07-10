/-
Copyright (c) 2026 Nick Adfor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Adfor
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Set
import Mathlib.Tactic.Common
import Aesop
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Factorial
import LeanPool.PolynomialMethodRestrictedSums.ANRPolynomialMethod
import LeanPool.PolynomialMethodRestrictedSums.VandermondeCoefficientFormula

/-!
# Restricted sums of sets with distinct sizes

The Alon-Nathanson-Ruzsa lower bound `restricted_sum_distinct_sizes` on the
set of sums `a 0 + ... + a k` with `a i ∈ A i` pairwise distinct, when the
sets `A i` have distinct sizes.
-/

open MvPolynomial

open Finset

open Matrix

open BigOperators

variable {R : Type*} [CommRing R]

variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

/-- S = {a + ... + a | a ∈ A, a ≠ a for all i ≠ j} -/
def restrictedSumSet (k : ℕ) (A : Fin (k + 1) → Finset (ZMod p)) : Finset (ZMod p) :=
  ((Fintype.piFinset A).filter fun f =>
    ∀ (i j : Fin (k + 1)), i < j → f i ≠ f j)
    |>.image (fun f => ∑ i, f i)

/-- Vandermonde: ∏_{i>j} (X - X) -/
noncomputable def vandermondePolynomial (k : ℕ) : MvPolynomial (Fin (k + 1)) (ZMod p) :=
  ∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
    if j.val < i.val then (X i - X j) else 1


/-- (Used in CompressedSizesRestrictedSum and DiasDaSilvaHamidoune)
The compressed sizes b'_i defined recursively:
    b'_0 = b_0, b'_i = min{b'_{i-1} - 1, b_i} for i ≥ 1 -/
def compressedSizes (b : Fin (k + 1) → ℕ) : Fin (k + 1) → ℕ :=
  fun i =>
    match i with
    | 0 => b 0
    | ⟨i + 1, hi⟩ =>
      let prev : Fin (k + 1) := ⟨i, by omega⟩
      min (compressedSizes b prev - 1) (b ⟨i + 1, hi⟩)

/-
Proposition 1.2:
Let p be a prime, and let A₀, A₁, ..., Aₖ be nonempty subsets of Z_p.
If |A_i| ≠ |A_j| for all 0 ≤ i < j ≤ k and ∑_{i=0}^k |A_i| ≤ p + (k + 2 choose 2) - 1,
then |{a₀ + ... + aₖ : a_i ∈ A_i, a_i ≠ a_j for all i ≠ j}| ≥ ∑_{i=0}^k |A_i| - (k + 2 choose 2) +
1.

Detailed proof:
1. Define the Vandermonde polynomial h(x₀, ..., xₖ) = ∏_{k ≥ i > j ≥ 0} (x_i - x_j).
   This polynomial is nonzero exactly when all x_i are distinct.

2. Let c_i = |A_i| - 1, so that |A_i| = c_i + 1.

3. Compute m = ∑_{i=0}^k c_i - (k + 1 choose 2)
            = (∑_{i=0}^k |A_i| - (k + 1)) - (k + 1 choose 2)
            = ∑_{i=0}^k |A_i| - (k + 2 choose 2)

4. We need m < p. From the hypothesis ∑ |A_i| ≤ p + (k + 2 choose 2) - 1,
   we get m = ∑ |A_i| - (k + 2 choose 2) ≤ p - 1 < p.

5. By Lemma 3.1, the coefficient of the monomial ∏ x_i^{c_i} in h·(∑ x_i)^m is:
      (m! / ∏ c_i!) · ∏_{i>j} (c_i - c_j)
   Since the c_i are all distinct and m < p, this coefficient is nonzero modulo p.

6. Apply Theorem 2.1 with this h, the sets A_i, and parameters c_i, m.
   The theorem gives:
      |⊕_h ∑_{i=0}^k A_i| ≥ m + 1

7. Note that ⊕_h ∑ A_i = {∑ a_i : a_i ∈ A_i, h(a) ≠ 0}
                     = {∑ a_i : a_i ∈ A_i, a_i ≠ a_j for all i ≠ j}
   since h(a) = 0 iff some a_i = a_j for i ≠ j.

8. Therefore:
      |{∑ a_i : a_i ∈ A_i, a_i distinct}| ≥ m + 1
                                        = ∑ |A_i| - (k + 2 choose 2) + 1
   which completes the proof.
-/
noncomputable section AristotleLemmas

/-
The total degree of the Vandermonde polynomial is (k + 1) choose 2.
-/
lemma vandermonde_degree_eq (k : ℕ) (p : ℕ) [Fact (Nat.Prime p)] :
  (vandermondePolynomial k : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree = (k + 1).choose 2 :=
      by
    -- The Vandermonde polynomial is a product of linear terms, each contributing a degree of 1.
    have van_deg : ∀ i j : Fin (k + 1),
        j.val < i.val → (X i - X j : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree = 1 := by
      intro i j a
      refine le_antisymm ?_ ?_ <;> norm_num [MvPolynomial.totalDegree];
      · intro b hb; rw [MvPolynomial.coeff_X, MvPolynomial.coeff_X] at hb; aesop;
      · refine ⟨Finsupp.single i 1, ?_, ?_⟩ <;> aesop;
    -- The total degree of a product of polynomials is the sum of their total degrees.
    have h_total_deg : ∀ (S : Finset (Fin (k + 1) × Fin (k + 1))),
        (∀ (ij : Fin (k + 1) × Fin (k + 1)), ij ∈ S → ij.1.val > ij.2.val) →
            (Finset.prod S
                (fun ij => (X ij.1 - X ij.2 : MvPolynomial (Fin (k + 1)) (ZMod p)))).totalDegree
              = Finset.card S := by
      intro S hS; induction S using Finset.induction
      · simp_all only [Fin.val_fin_lt, notMem_empty, gt_iff_lt, IsEmpty.forall_iff,
          implies_true, prod_empty, totalDegree_one, card_empty]
      rename_i a s a_1 a_2
      simp_all only [Fin.val_fin_lt, gt_iff_lt, mem_insert, or_true, implies_true,
          forall_const, forall_eq_or_imp, Prod.forall, not_false_eq_true, prod_insert,
          card_insert_of_notMem]
      obtain ⟨fst, snd⟩ := a
      obtain ⟨left, right⟩ := hS
      simp_all only
      rw [totalDegree_mul_of_isDomain, a_2, van_deg] <;> norm_num [left];
      · ring;
      · intro hcontra
        replace hcontra := congr_arg
          (MvPolynomial.eval (fun i => if i = fst then 1 else 0)) hcontra
        aesop;
      · simp? +decide [Finset.prod_eq_zero_iff, sub_eq_zero];
        exact fun x hx => lt_irrefl x (right _ _ hx);
    convert h_total_deg
        (Finset.filter (fun ij => ij.2.val < ij.1.val)
          (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1)))) _ using 1;
    · unfold vandermondePolynomial
      simp? (config := { decide := Bool.true }) [Finset.prod_filter];
      erw [Finset.prod_product];
    · rw [show
            (Finset.filter (fun ij : Fin (k + 1) × Fin (k + 1) => (ij.2 : ℕ) < ij.1) Finset.univ
              : Finset _)
            = Finset.biUnion (Finset.univ : Finset (Fin (k + 1)))
                fun i => Finset.image (fun j => (i, j)) (Finset.Iio i)
          from ?_, Finset.card_biUnion];
      · simp? +decide [Finset.card_image_of_injective, Function.Injective];
        exact Eq.symm (Nat.recOn k (by norm_num) fun n ih => by
          norm_num [Fin.sum_univ_castSucc, Nat.choose] at *; linarith);
      · exact fun i _ j _ hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
      · ext ⟨i, j⟩; aesop;
    · aesop

/-
If the sum of sizes of A_i is bounded by p + (k + 2 choose 2) - 1, then m < p.
-/
lemma restricted_sum_m_bound (A : Fin (k + 1) → Finset (ZMod p))
    (h_nonempty : ∀ i, (A i).Nonempty)
    (h_sum_bound : ∑ i, (A i).card ≤ p + (Nat.choose (k + 2) 2) - 1) :
    let c := fun i => (A i).card - 1
    let m := ∑ i, c i - (k + 1).choose 2
    m < p := by
      -- Therefore, $\sum |A_i| \le p + \binom{k + 1}{2} + (k + 1) - 1$, so $\sum c_i \le p +
      -- \binom{k + 1}{2} - 1$.
      have h_c_sum_bound : ∑ i, (#(A i) - 1) ≤ p + Nat.choose (k + 1) 2 - 1 := by
        -- We know that $\sum |A_i| = \sum (c_i + 1) = \sum c_i + (k + 1)$.
        have h_card_sum : ∑ i, #(A i) = ∑ i, ((#(A i)) - 1) + (k + 1) := by
          zify;
          rw [Finset.sum_congr rfl fun _ _ => Nat.cast_sub <| Finset.card_pos.mpr <| h_nonempty _];
              norm_num;
        simp_all +decide [Nat.choose];
        omega;
      rcases p with (_ | p) <;> (try simp_all (config := { decide := Bool.true }))

/-
The coefficient of the monomial corresponding to c in the product of the power sum and the
Vandermonde polynomial is non-zero in ZMod p, provided c_i and m are small enough.
-/
lemma vandermonde_coeff_nonzero (c : Fin (k + 1) → ℕ) (m : ℕ)
    (hc : ∀ i, c i < p)
    (h_distinct : ∀ i j, i < j → c i ≠ c j)
    (hm : m < p)
    (h_sum : ∑ i, c i = m + (k + 1).choose 2) :
    MvPolynomial.coeff (toFinsupp c)
      ((∑ i : Fin (k + 1), (X i : MvPolynomial (Fin (k + 1)) (ZMod p))) ^ m *
       vandermondePolynomial k) ≠ 0 := by
         -- Therefore, the coefficient in ZMod p is non-zero because none of the factors in
         -- `expectedValue c m` are divisible by `p`.
         intro h_coeff_zero_in_charP
         have h_coeff_not_zero_in_K : (expectedValue c m : ℚ) ≠ 0 := by
           norm_num [expectedValue, h_sum];
           simp_all? +decide [Finset.prod_eq_zero_iff];
           exact ⟨⟨Nat.factorial_ne_zero _,
               fun i j => by split_ifs <;> norm_num; exact sub_ne_zero_of_ne <|
                   mod_cast Ne.symm <| by aesop⟩, fun i => Nat.factorial_ne_zero _⟩;
         have h_coeff_not_zero_in_K :
             (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) ((∑ i : Fin (k + 1),
                 MvPolynomial.X i) ^ m * ∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
                     if j.val < i.val then (X i - X j) else 1 : MvPolynomial (Fin (k + 1)) (ℤ)))
                         = expectedValue c m := by
           have h_index : (Finsupp.equivFunOnFinite.symm c : (Fin (k + 1)) →₀ ℕ) = toFinsupp c := by
             ext i; simp [Finsupp.equivFunOnFinite, toFinsupp]
           -- By definition of polynomial multiplication and the properties of coefficients, the
           -- coefficient of the monomial corresponding to `c` in the product of the power sum and
           -- the Vandermonde polynomial is equal to the coefficient of the monomial corresponding
           -- to `c` in the product of the power sum and the Vandermonde polynomial over the
           -- integers.
           have h_coeff_eq : ∀ (f : MvPolynomial (Fin (k + 1)) ℤ) (
               g :
               MvPolynomial (Fin (k + 1)) ℤ),
                   MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (f * g)
                       = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c)
                           (MvPolynomial.map (algebraMap ℤ ℚ) (f * g)) := by
             intros f g; rw [MvPolynomial.coeff_map]; aesop;
           rw [h_coeff_eq, h_index, ← Vandermonde_coefficient_formula c m h_sum]
           congr 1
           -- Push `map` through the polynomial product.
           rw [map_mul, map_pow, map_sum, map_prod]
           refine congrArg₂ (· * ·) ?_ ?_
           · refine congrArg (· ^ m) ?_
             refine Finset.sum_congr rfl fun i _ => ?_
             rw [MvPolynomial.map_X]
           · refine Finset.prod_congr rfl fun i _ => ?_
             rw [map_prod]
             refine Finset.prod_congr rfl fun j _ => ?_
             rw [apply_ite (MvPolynomial.map (algebraMap ℤ ℚ))]
             simp only [Fin.val_fin_lt, map_sub, MvPolynomial.map_X, map_one]
         have h_coeff_not_zero_in_K' : (algebraMap ℤ (ZMod p)) (
             MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (
             (∑ i : Fin (k + 1), MvPolynomial.X i) ^ m * ∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
             if j.val < i.val then (X i - X j) else 1 : MvPolynomial (Fin (k + 1)) (ℤ))) = 0 := by
           convert h_coeff_zero_in_charP using 1;
           unfold vandermondePolynomial;
           -- By definition of polynomial multiplication and the fact that the coefficients are
           -- integers, the coefficient of the polynomial in ZMod p is the same as the coefficient
           -- of the polynomial in ℤ.
           have h_coeff_eq : ∀ (P : MvPolynomial (Fin (k + 1)) ℤ),
               MvPolynomial.coeff (toFinsupp c) (
                   MvPolynomial.map (algebraMap ℤ (ZMod p)) P)
                       = (algebraMap ℤ (ZMod p))
                           (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) P) := by
             intro P; erw [MvPolynomial.coeff_map]
             simp_all only [ne_eq, Fin.val_fin_lt, algebraMap_int_eq, eq_intCast];
             congr! 2;
             ext i; simp [toFinsupp];
           convert h_coeff_eq _ |> Eq.symm;
           norm_num [MvPolynomial.map_X];
           exact Or.inl
             (Finset.prod_congr rfl fun i hi =>
               Finset.prod_congr rfl fun j hj => by split_ifs <;> simp +decide [*]);
         simp_all? +decide [ZMod.intCast_zmod_eq_zero_iff_dvd];
         obtain ⟨a, ha⟩ := h_coeff_not_zero_in_K';
         simp_all? +decide [expectedValue];
         rw [eq_div_iff] at h_coeff_not_zero_in_K <;> norm_cast at *
             <;> simp_all? +decide [Finset.prod_eq_zero_iff, Nat.factorial_ne_zero];
         -- Since $p$ is prime and $p \mid m! \prod_{i>j} (c_i - c_j)$, it must divide one of the
         -- factors.
         have h_div :
             (p : ℤ) ∣ (∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
                 if j.val < i.val then (c i - c j : ℤ) else 1) := by
           have h_div : (p : ℤ) ∣ (m.factorial : ℤ) *
               (∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
                   if j.val < i.val then (c i - c j : ℤ) else 1) := by
             simp_all? +decide [Int.subNatNat_eq_coe];
             exact h_coeff_not_zero_in_K ▸ dvd_mul_of_dvd_left (dvd_mul_right _ _) _;
           exact Or.resolve_left (Int.Prime.dvd_mul' (Fact.out : Nat.Prime p) h_div) (
               by norm_cast; exact mt (Nat.Prime.dvd_factorial (Fact.out : Nat.Prime p) |>.1) (
               by linarith));
         -- Since $p$ is prime and $p \mid \prod_{i>j} (c_i - c_j)$, it must divide one of the
         -- factors.
         obtain ⟨i, j, hij, h_div_factor⟩ : ∃ i j : Fin (k + 1),
             i > j ∧ (p : ℤ) ∣ (c i - c j : ℤ) := by
           haveI :=
               Fact.mk (Fact.out : Nat.Prime p);
                   simp_all? +decide
                       [← ZMod.intCast_zmod_eq_zero_iff_dvd, Finset.prod_eq_zero_iff];
           obtain ⟨i, j, h⟩ := h_div; use i, j; aesop;
         exact h_distinct _ _ hij (by
           obtain ⟨x, hx⟩ := h_div_factor
           nlinarith [show x = 0 by nlinarith [hc i, hc j]])

end AristotleLemmas

theorem restricted_sum_distinct_sizes (A : Fin (k + 1) → Finset (ZMod p))
    (h_nonempty : ∀ i, (A i).Nonempty)
    (h_sizes_distinct : ∀ i j, i < j → (A i).card ≠ (A j).card)
    (h_sum_bound : ∑ i, (A i).card ≤ p + (Nat.choose (k + 2) 2) - 1) :
    (restrictedSumSet k A).card ≥ ∑ i, (A i).card - (Nat.choose (k + 2) 2) + 1 := by
      -- Let $c_i = |A_i| - 1$, so that $|A_i| = c_i + 1$. Then $m = \sum_{i=0}^k c_i -
      -- \binom{k + 1}{2}$.
      set c : Fin (k + 1) → ℕ := fun i => (A i).card - 1
      set m : ℕ := ∑ i, c i - (k + 1).choose 2;
      -- Show that $m < p$ and that the coefficient of $\prod X_i^{c_i}$ in $(\sum X_i)^m \cdot
      -- \text{vandermonde}$ is non-zero modulo $p$.
      have hm_lt_p : m < p := restricted_sum_m_bound A h_nonempty h_sum_bound
      have h_coeff_nonzero :
          (MvPolynomial.coeff (toFinsupp c) ((∑ i,
              (X i : MvPolynomial (Fin (k + 1)) (ZMod p))) ^ m *
            vandermondePolynomial k)) ≠ 0 := by
        -- Since $|A_i|$ are distinct, $c_i$ are distinct.
        have hc_distinct : ∀ i j, i < j → c i ≠ c j :=
          fun i j hij => fun h => h_sizes_distinct i j hij <|
              by
                linarith [
                  Nat.sub_add_cancel <| show 1 ≤ Finset.card (A i)
                    from Finset.card_pos.mpr <| h_nonempty i,
                  Nat.sub_add_cancel <| show 1 ≤ Finset.card (A j)
                    from Finset.card_pos.mpr <| h_nonempty j];
        apply vandermonde_coeff_nonzero c m;
        · intro i
          exact lt_of_lt_of_le (Nat.sub_lt (Finset.card_pos.mpr (h_nonempty i)) zero_lt_one) (
              le_trans (Finset.card_le_univ _) (by norm_num));
        · assumption;
        · assumption;
        · rw [Nat.sub_add_cancel];
          -- Since $c_i$ are distinct and non-negative, we can order them as $c_{(0)} < c_{(1)} <
          -- \cdots < c_{(k)}$.
          obtain ⟨σ, hσ⟩ : ∃ σ : Fin (k + 1) ≃ Fin (k + 1), ∀ i j, i < j → c (σ i) < c (σ j) := by
            -- Since $c_i$ are distinct and non-negative, we can order them as $c_{(0)} < c_{(1)} <
            -- \cdots < c_{(k)}$ by definition of `Finset.sort`.
            have h_sorted : ∃ l : Fin (k + 1) → ℕ, StrictMono l ∧ ∀ i,
                l i ∈ Finset.image c Finset.univ := by
              have h_sorted : Finset.card (Finset.image c Finset.univ) = k + 1 := by
                rw [Finset.card_image_of_injective _ fun i j hij =>
                      le_antisymm
                        (le_of_not_gt fun hi => hc_distinct _ _ hi hij.symm)
                        (le_of_not_gt fun hj => hc_distinct _ _ hj hij),
                    Finset.card_fin];
              exact ⟨fun i => Finset.orderEmbOfFin _ h_sorted i,
                  (Finset.orderEmbOfFin _ h_sorted).strictMono,
                  fun i => Finset.orderEmbOfFin_mem _ h_sorted _⟩;
            obtain ⟨l, hl₁, hl₂⟩ := h_sorted;
            choose f hf using fun i => Finset.mem_image.mp (hl₂ i);
            norm_num +zetaDelta at *;
            exact
              ⟨Equiv.ofBijective f
                (Finite.injective_iff_bijective.mp
                  (show Function.Injective f from fun i j hij =>
                    hl₁.injective <| by have := hf i; have := hf j; aesop)),
              fun i j hij => by simpa [hf] using hl₁ hij⟩;
          -- Since $c_{(i)}$ are distinct and non-negative, we have $c_{(i)} \geq i$ for all $i$.
          have hc_ge_id : ∀ i, c (σ i) ≥ i := by
            intro i; induction i using Fin.inductionOn with
            | zero =>
              simp_all only [ne_eq, Fin.coe_ofNat_eq_mod, Nat.zero_mod, ge_iff_le, zero_le, m, c]
            | succ i a =>
              simp_all only [ne_eq, Fin.val_castSucc, ge_iff_le, Fin.val_succ,
                  Order.add_one_le_iff, m, c]
              -- The origin is `exact lt_of_le_of_lt a (h _ _ (Fin.castSucc_lt_succ i ))`.
              -- Here delete `i`, as Aristotle wrote it in v4.24.0, but in v4.26.0
              -- `Fin.castSucc_lt_succ` doesn't need a variable.
              exact lt_of_le_of_lt a (hσ _ _ (Fin.castSucc_lt_succ));
          have hc_ge_id_sum : ∑ i, c (σ i) ≥ ∑ i ∈ Finset.range (k + 1), i := by
            simpa only [Finset.sum_range] using Finset.sum_le_sum fun i _ => hc_ge_id i;
          simp_all? +decide [Finset.sum_range_id, Equiv.sum_comp σ fun i => c i];
          rwa [Nat.choose_two_right];
      -- Apply Theorem 2.1 with this h, the sets A_i, and parameters c_i, m. The theorem gives |S| ≥
      -- m + 1.
      have h_theorem : let h := vandermondePolynomial k;
        let S := (Fintype.piFinset A).filter (fun f => h.eval f ≠ 0) |>.image (fun f => ∑ i, f i);
        S.card ≥ m + 1 := by
          convert ANR_polynomial_method (vandermondePolynomial k) A c _ _ _ using 1;
          any_goals exact m;
          · refine Iff.intro (fun h_card_ge h_coeff => ⟨h_card_ge, ?_⟩) (fun a => ?_)
            · exact restricted_sum_m_bound A h_nonempty h_sum_bound
            · convert a _ |>.1;
              convert h_coeff_nonzero using 1;
              congr;
              ext i; simp [toFinsupp];
          · exact fun i => by rw [Nat.sub_add_cancel (Finset.card_pos.mpr (h_nonempty i))];
          · rw [vandermonde_degree_eq, Nat.sub_add_cancel];
            -- Since the sizes of the sets $A_i$ are distinct, the sum of their sizes is at least
            -- the sum of the first $k + 1$ natural numbers.
            have h_sum_ge_sum_first_k : ∑ i : Fin (k + 1), (A i).card ≥ ∑ i ∈ Finset.range (k + 1),
                (i + 1) := by
              -- Since the sizes of the sets $A_i$ are distinct, we can order them as $|A_{i_1}| <
              -- |A_{i_2}| < \cdots < |A_{i_{k + 1}}|$.
              have h_order : ∃ f : Fin (k + 1) → ℕ, StrictMono f ∧ ∀ i,
                  f i ∈ Finset.image (fun i => (A i).card) Finset.univ := by
                have h_order : Finset.card (Finset.image (fun i => (A i).card) Finset.univ) = k +
                    1 := by
                  rw [Finset.card_image_of_injective _ fun i j hij =>
                        le_antisymm
                          (le_of_not_gt fun hi => h_sizes_distinct _ _ hi hij.symm)
                          (le_of_not_gt fun hj => h_sizes_distinct _ _ hj hij),
                      Finset.card_fin];
                exact ⟨fun i => Finset.orderEmbOfFin _ h_order i,
                    (Finset.orderEmbOfFin _ h_order).strictMono,
                    fun i => Finset.orderEmbOfFin_mem _ h_order _⟩;
              -- Since $f$ is strictly monotone, we have $f i ≥ i + 1$ for all $i$.
              obtain ⟨f, hf_mono, hf_image⟩ := h_order
              have h_f_ge : ∀ i, f i ≥ i + 1 := by
                intro i; induction i using Fin.inductionOn with
                | zero =>
                  simp_all only [ne_eq, mem_image, mem_univ, true_and, Fin.coe_ofNat_eq_mod,
                      Nat.zero_mod, zero_add, ge_iff_le, m, c]
                  obtain ⟨a, ha⟩ := hf_image 0; linarith [Finset.card_pos.mpr (h_nonempty a)];
                | succ i a =>
                  simp_all only [ne_eq, mem_image, mem_univ, true_and, Fin.val_castSucc,
                      ge_iff_le, Order.add_one_le_iff, Fin.val_succ, m, c]
                  -- The origin is `exact lt_of_le_of_lt a (hf_mono (Fin.castSucc_lt_succ i))`.
                  -- Here delete `i`, as Aristotle wrote it in v4.24.0, but in v4.26.0
                  -- `Fin.castSucc_lt_succ` doesn't need a variable.
                  exact lt_of_le_of_lt a (hf_mono (Fin.castSucc_lt_succ));
              -- Since $f$ is strictly monotone, we have $\sum_{i=0}^k f(i) \geq \sum_{i=0}^k (i +
              -- 1)$.
              have h_sum_f_ge_sum_first_k : ∑ i : Fin (k + 1), f i ≥ ∑ i ∈ Finset.range (k + 1),
                  (i + 1) := by
                simpa only [Finset.sum_range] using Finset.sum_le_sum fun i _ => h_f_ge i;
              have h_sum_f_eq_sum_A : ∑ i : Fin (k + 1), f i = ∑ i : Fin (k + 1), (A i).card := by
                have h_sum_f_eq_sum_A : ∑ i : Fin (k + 1),
                    f i = ∑ i ∈ Finset.image (fun i => (A i).card) Finset.univ, i := by
                  have h_sum_f_eq_sum_A :
                      Finset.image f Finset.univ =
                          Finset.image (fun i => (A i).card) Finset.univ := by
                    exact Finset.eq_of_subset_of_card_le
                      (Finset.image_subset_iff.mpr fun i _ => hf_image i)
                      (by
                        rw [Finset.card_image_of_injective _ hf_mono.injective,
                            Finset.card_image_of_injective _ (fun i j hij =>
                              le_antisymm
                                (le_of_not_gt fun hi => h_sizes_distinct _ _ hi hij.symm)
                                (le_of_not_gt fun hj => h_sizes_distinct _ _ hj hij))]);
                  rw [← h_sum_f_eq_sum_A, Finset.sum_image <| by
                    simp (config := { decide := Bool.true }) only [coe_univ, Set.injOn_univ]
                    exact StrictMono.injective hf_mono]
                rw [h_sum_f_eq_sum_A,
                    Finset.sum_image <| by
                      intros i hi j hj hij
                      exact le_antisymm
                        (le_of_not_gt fun hi' => h_sizes_distinct _ _ hi' hij.symm)
                        (le_of_not_gt fun hj' => h_sizes_distinct _ _ hj' hij)];
              linarith;
            convert Nat.sub_le_sub_right h_sum_ge_sum_first_k (k + 1) using 1;
            · exact eq_tsub_of_add_eq <|
                Nat.recOn k (by norm_num) fun n ih =>
                    by simp (config := { decide := Bool.true }) [Nat.choose,
                        Finset.sum_range_succ] at *; linarith;
            · norm_num +zetaDelta at *;
              exact eq_tsub_of_add_eq (by
                rw [← Finset.sum_congr rfl fun _ _ =>
                  Nat.sub_add_cancel (Finset.card_pos.mpr (h_nonempty _))]
                simp +arith +decide [Finset.sum_add_distrib]);
      -- Note that $h(f) \ne 0$ corresponds to $f_i$ being distinct. So $S$ is the restricted sum
      -- set.
      have hS_eq_restrictedSumSet : let h := vandermondePolynomial k;
        let S := (Fintype.piFinset A).filter (fun f => h.eval f ≠ 0) |>.image (fun f => ∑ i, f i);
        S = restrictedSumSet k A := by
          ext; simp only [restrictedSumSet, vandermondePolynomial, ne_eq, mem_image, mem_filter,
            Fintype.mem_piFinset];
          constructor <;> rintro ⟨a, ⟨ha₁, ha₂⟩,
              rfl⟩ <;> use a <;> simp_all? +decide [Finset.prod_eq_zero_iff];
          · intro i j hij; specialize ha₂ j i; aesop;
          · intro i j; split_ifs
              <;> simp_all? (config := { decide := Bool.true }) [sub_eq_iff_eq_add];
            exact Ne.symm (ha₂ _ _ ‹_›);
      simp_all only [ne_eq, ge_iff_le, Order.add_one_le_iff, gt_iff_lt, m, c]
      -- After `aesop`, the goal is
      --   ∑ i, #(A i) - (k + 2).choose 2 < #(restrictedSumSet k A).
      -- We have
      --   h_theorem : ∑ x, (#(A x) - 1) - (k + 1).choose 2 < #(restrictedSumSet k A).
      -- The two LHSs are equal because each `#(A i) ≥ 1` and
      -- `(k + 2).choose 2 = (k + 1).choose 2 + (k + 1)`.
      have h_card_pos : ∀ i, 1 ≤ #(A i) := fun i => Finset.card_pos.mpr (h_nonempty i)
      have h_sum_succ : ∑ i, #(A i) = ∑ i, (#(A i) - 1) + (k + 1) := by
        have : ∀ i, #(A i) = (#(A i) - 1) + 1 := fun i =>
          (Nat.sub_add_cancel (h_card_pos i)).symm
        calc
          ∑ i, #(A i) = ∑ i : Fin (k + 1), ((#(A i) - 1) + 1) :=
              Finset.sum_congr rfl fun i _ => this i
          _ = ∑ i, (#(A i) - 1) + (k + 1) := by
              rw [Finset.sum_add_distrib]; simp
      have h_choose_succ : (k + 2).choose 2 = (k + 1).choose 2 + (k + 1) := by
        rw [show ((k + 2 : ℕ).choose 2) = ((k + 1 + 1 : ℕ).choose (1 + 1)) from rfl,
            Nat.choose_succ_succ' (k + 1) 1, Nat.choose_one_right,
            show (1 : ℕ) + 1 = 2 from rfl]
        omega
      -- Compare LHSes via h_sum_succ and h_choose_succ.
      have h_lhs_eq :
          ∑ i, #(A i) - (k + 2).choose 2 = ∑ i, (#(A i) - 1) - (k + 1).choose 2 := by
        rw [h_sum_succ, h_choose_succ]
        omega
      rwa [h_lhs_eq]
