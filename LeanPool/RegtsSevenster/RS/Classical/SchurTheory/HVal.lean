/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.PowerSums

/-!
# Evaluated symmetric values and the power–complete Newton identity

The specialization layer works with complex
values rather than a formal symmetric-function ring: for a finite
family `x : Fin N → ℂ` we define the power sums `pVal x c` and the
complete homogeneous values `hVal x k` (a sum over size-`k`
multisets), and prove the Newton identity

    `(k+1) · h_{k+1} = ∑_{i ≤ k} p_{i+1} · h_{k−i}`

by double counting: adding `i+1` copies of a marked variable to a
size-`(k−i)` multiset produces each size-`(k+1)` multiset once per
unit of multiplicity.  Consequently `hVal x` satisfies the defining
recursion of `newtonH (pVal x)`.
-/

namespace RS

open Finset

variable {N : ℕ}

/-- The power sum of exponent `c` of a finite family. -/
noncomputable def pVal (x : Fin N → ℂ) (c : ℕ) : ℂ :=
  ∑ j : Fin N, x j ^ c

/-- The complete homogeneous value of degree `k` of a finite
family: the sum of the products of all size-`k` multisets. -/
noncomputable def hVal (x : Fin N → ℂ) (k : ℕ) : ℂ :=
  ∑ s : Sym (Fin N) k, (s.1.map x).prod

/-- The degree-zero complete homogeneous value is `1`. -/
@[simp] theorem hVal_zero (x : Fin N → ℂ) : hVal x 0 = 1 := by
  rw [hVal]
  rw [show (Finset.univ : Finset (Sym (Fin N) 0)) = {Sym.nil} from
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_univ _, fun s _ => Sym.eq_nil_of_card_zero s⟩]
  simp

/-- The per-variable splitting identity: marking `i+1` copies of
`j` inside a size-`(k+1)` multiset, every multiset arises once per
unit of the multiplicity of `j`. -/
theorem sum_split_eq_count (x : Fin N → ℂ) (k : ℕ) (j : Fin N) :
    (∑ i ∈ range (k + 1), ∑ s : Sym (Fin N) (k - i),
        x j ^ (i + 1) * (s.1.map x).prod) =
      ∑ S : Sym (Fin N) (k + 1),
        (S.1.count j : ℂ) * (S.1.map x).prod := by
  classical
  rw [← Finset.sum_sigma (range (k + 1))
    (fun i => (Finset.univ : Finset (Sym (Fin N) (k - i))))
    (fun p => x j ^ (p.1 + 1) * (p.2.1.map x).prod)]
  rw [show (∑ S : Sym (Fin N) (k + 1),
      (S.1.count j : ℂ) * (S.1.map x).prod) =
    ∑ q ∈ (Finset.univ : Finset (Sym (Fin N) (k + 1))).sigma
        (fun S => range (S.1.count j)),
      ((q.1 : Sym (Fin N) (k + 1)).1.map x).prod from by
    rw [Finset.sum_sigma
      (Finset.univ : Finset (Sym (Fin N) (k + 1)))
      (fun S => range (S.1.count j))
      (fun q => ((q.1 : Sym (Fin N) (k + 1)).1.map x).prod)]
    refine Finset.sum_congr rfl fun S _ => ?_
    show (S.1.count j : ℂ) * (S.1.map x).prod =
      ∑ _s ∈ range (S.1.count j), (S.1.map x).prod
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]]
  refine Finset.sum_bij'
    (fun p hp => ⟨⟨p.2.1 + Multiset.replicate (p.1 + 1) j, by
      have hik : p.1 < k + 1 :=
        Finset.mem_range.mp (Finset.mem_sigma.mp hp).1
      rw [Multiset.card_add, p.2.2, Multiset.card_replicate]
      omega⟩, p.1⟩)
    (fun q hq => ⟨q.2, ⟨q.1.1 - Multiset.replicate (q.2 + 1) j, by
      have hd : q.2 < q.1.1.count j :=
        Finset.mem_range.mp (Finset.mem_sigma.mp hq).2
      have hle : Multiset.replicate (q.2 + 1) j ≤ q.1.1 :=
        Multiset.le_count_iff_replicate_le.mp hd
      rw [Multiset.card_sub hle, q.1.2, Multiset.card_replicate]
      omega⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro p hp
    refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩
    refine Finset.mem_range.mpr ?_
    show p.1 < Multiset.count j (p.2.1 + Multiset.replicate (p.1 + 1) j)
    rw [Multiset.count_add, Multiset.count_replicate, if_pos rfl]
    omega
  · -- backward membership
    intro q hq
    refine Finset.mem_sigma.mpr ⟨?_, Finset.mem_univ _⟩
    refine Finset.mem_range.mpr ?_
    have hd : q.2 < q.1.1.count j :=
      Finset.mem_range.mp (Finset.mem_sigma.mp hq).2
    have hcc := Multiset.count_le_card j q.1.1
    rw [q.1.2] at hcc
    show q.2 < k + 1
    omega
  · -- left inverse
    intro p hp
    refine Sigma.ext rfl (heq_of_eq ?_)
    refine Subtype.ext ?_
    show (p.2.1 + Multiset.replicate (p.1 + 1) j) -
      Multiset.replicate (p.1 + 1) j = p.2.1
    exact Multiset.add_sub_cancel_right
  · -- right inverse
    intro q hq
    refine Sigma.ext ?_ (heq_of_eq rfl)
    refine Subtype.ext ?_
    have hd : q.2 < q.1.1.count j :=
      Finset.mem_range.mp (Finset.mem_sigma.mp hq).2
    have hle : Multiset.replicate (q.2 + 1) j ≤ q.1.1 :=
      Multiset.le_count_iff_replicate_le.mp hd
    show (q.1.1 - Multiset.replicate (q.2 + 1) j) +
      Multiset.replicate (q.2 + 1) j = q.1.1
    exact Multiset.sub_add_cancel hle
  · -- weights
    intro p hp
    show x j ^ (p.1 + 1) * (p.2.1.map x).prod =
      ((p.2.1 + Multiset.replicate (p.1 + 1) j).map x).prod
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
      Multiset.prod_replicate, mul_comm]

/-- **The power–complete Newton identity**, at the level of
values. -/
theorem hVal_newton (x : Fin N → ℂ) (k : ℕ) :
    ((k : ℂ) + 1) * hVal x (k + 1) =
      ∑ i ∈ range (k + 1), pVal x (i + 1) * hVal x (k - i) := by
  classical
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ range (k + 1)) =>
    show pVal x (i + 1) * hVal x (k - i) =
      ∑ j : Fin N, x j ^ (i + 1) * hVal x (k - i) from by
        rw [pVal, Finset.sum_mul])]
  rw [Finset.sum_comm]
  rw [show (∑ j : Fin N, ∑ i ∈ range (k + 1),
      x j ^ (i + 1) * hVal x (k - i)) =
    ∑ j : Fin N, ∑ S : Sym (Fin N) (k + 1),
      (S.1.count j : ℂ) * (S.1.map x).prod from
    Finset.sum_congr rfl fun j _ => by
      rw [← sum_split_eq_count x k j]
      exact Finset.sum_congr rfl fun i _ => by
        rw [hVal, Finset.mul_sum]]
  rw [Finset.sum_comm]
  rw [hVal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [← Nat.cast_sum]
  rw [show (∑ j : Fin N, S.1.count j) = Multiset.card S.1 from ?_]
  · rw [S.2, Nat.cast_add, Nat.cast_one]
  · rw [← Multiset.toFinset_sum_count_eq S.1]
    exact (Finset.sum_subset (Finset.subset_univ _)
      (fun a _ ha => Multiset.count_eq_zero.mpr
        (fun hmem => ha (Multiset.mem_toFinset.mpr hmem)))).symm

/-- `hVal` satisfies the `newtonH` recursion: the complete
homogeneous values are the Newton lifts of the power sums. -/
theorem newtonH_pVal (x : Fin N → ℂ) : ∀ k, newtonH (pVal x) k = hVal x k
  | 0 => by rw [newtonH, hVal_zero]
  | k + 1 => by
    rw [newtonH]
    have hrec : ∀ i ∈ range (k + 1),
        pVal x (i + 1) * newtonH (pVal x) (k - i) =
        pVal x (i + 1) * hVal x (k - i) := fun i _ => by
      rw [newtonH_pVal x (k - i)]
    rw [Finset.sum_congr rfl hrec, ← hVal_newton]
    rw [← mul_assoc, inv_mul_cancel₀
      (Nat.cast_add_one_ne_zero k : ((k : ℂ) + 1) ≠ 0), one_mul]
  decreasing_by exact Nat.lt_succ_of_le (Nat.sub_le k i)

end RS
