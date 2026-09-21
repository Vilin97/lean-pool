/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.CycleFactor

/-!
# Preparation for the cycle-sum identity

The Fubini exchange between permutations and their fixed
colourings, and the congruence lemmas allowing transfer of the
cycle-sum identity from realized power sums to arbitrary
prospective ones.
-/

namespace RS

open Finset Equiv Equiv.Perm

variable {n N : ℕ}

/-- `newtonH` only depends on the first `k` power sums. -/
theorem newtonH_congr {t t' : ℕ → ℂ} :
    ∀ k, (∀ c, 1 ≤ c → c ≤ k → t c = t' c) →
      newtonH t k = newtonH t' k
  | 0, _ => by rw [newtonH, newtonH]
  | k + 1, h => by
    rw [newtonH, newtonH]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i < k + 1 := Finset.mem_range.mp hi
    rw [h (i + 1) (by omega) (by omega),
      newtonH_congr (k - i) (fun c h1 hc => h c h1 (by omega))]
  decreasing_by exact Nat.lt_succ_of_le (Nat.sub_le k i)

/-- `cycleProd` only depends on the first `n` power sums. -/
theorem cycleProd_congr {t t' : ℕ → ℂ} (π : Equiv.Perm (Fin n))
    (h : ∀ c, 1 ≤ c → c ≤ n → t c = t' c) :
    cycleProd t π = cycleProd t' π := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [cycleProd, cycleProd]
    rw [show π.cycleType = 0 from by
      rw [Equiv.Perm.cycleType_eq_zero]
      exact Subsingleton.elim π 1]
    simp
  · rw [cycleProd, cycleProd, h 1 le_rfl hn]
    congr 2
    refine Multiset.map_congr rfl fun c hc => ?_
    have h2 : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hc
    have hle : c ≤ π.cycleType.sum :=
      Multiset.single_le_sum (fun x _ => Nat.zero_le x) c hc
    have hsupp := Equiv.Perm.sum_cycleType π
    have hcard : π.support.card ≤ n := by
      have := Finset.card_le_univ π.support
      simpa using this
    exact h c (by omega) (by omega)

/-- **Fubini for fixed colourings**: summing a colouring weight
over all permutations and their fixed colourings counts each
colouring once per stabilizing permutation. -/
theorem sum_perm_fixed_weight (w : (Fin n → Fin N) → ℂ) :
    (∑ π : Equiv.Perm (Fin n),
        ∑ f : {f : Fin n → Fin N // f ∘ π = f}, w f.1) =
      ∑ f : Fin n → Fin N,
        ((Finset.univ.filter
            (fun π : Equiv.Perm (Fin n) => f ∘ π = f)).card : ℂ) *
          w f := by
  classical
  calc (∑ π : Equiv.Perm (Fin n),
        ∑ f : {f : Fin n → Fin N // f ∘ π = f}, w f.1)
      = ∑ π : Equiv.Perm (Fin n),
          ∑ f ∈ Finset.univ.filter
            (fun f : Fin n → Fin N => f ∘ π = f), w f :=
        Finset.sum_congr rfl (fun π _ =>
          (Finset.sum_subtype _ (fun f => by simp) w).symm)
    _ = ∑ π : Equiv.Perm (Fin n), ∑ f : Fin n → Fin N,
          if f ∘ π = f then w f else 0 :=
        Finset.sum_congr rfl (fun π _ =>
          Finset.sum_filter (fun f : Fin n → Fin N => f ∘ π = f) w)
    _ = ∑ f : Fin n → Fin N, ∑ π : Equiv.Perm (Fin n),
          if f ∘ π = f then w f else 0 := Finset.sum_comm
    _ = ∑ f : Fin n → Fin N,
          ((Finset.univ.filter
            (fun π : Equiv.Perm (Fin n) => f ∘ π = f)).card : ℂ) *
          w f :=
        Finset.sum_congr rfl (fun f _ => by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul])

end RS
