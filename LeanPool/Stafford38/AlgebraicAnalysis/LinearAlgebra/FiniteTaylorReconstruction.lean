/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Finite Taylor reconstruction

Application-independent finite Taylor reconstruction for a nilpotent
endomorphism. Extracted from Stafford38 commit c8a513d553b24c7c08da82f496c44dbbaeb1f2fc.
-/

namespace AlgebraicAnalysis.FiniteTaylorReconstruction

open scoped BigOperators

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- The finite alternating Taylor projector associated with two endomorphisms. -/
def projectorMapG (K : ℕ) (S D : V →ₗ[𝕜] V) : V →ₗ[𝕜] V :=
  ∑ r ∈ Finset.range (K + 1),
    ((-1 : 𝕜) ^ r / (r.factorial : 𝕜)) • (S ^ r * D ^ r)

omit [CharZero 𝕜] in
private lemma projectorMap_term_all
    (K j : ℕ) (S D : V →ₗ[𝕜] V) (x : V) :
    ((S ^ j * projectorMapG K S D * D ^ j) x) =
      ∑ r ∈ Finset.range (K + 1),
        ((-1 : 𝕜) ^ r / (r.factorial : 𝕜)) •
          ((S ^ (j + r) * D ^ (j + r)) x) := by
  unfold projectorMapG
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_apply,
    smul_mul_assoc, mul_smul_comm, smul_add, Module.End.mul_apply]
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  change ((-1 : 𝕜) ^ r / (r.factorial : 𝕜)) •
      ((S ^ j * (S ^ r * D ^ r) * D ^ j) x) =
    ((-1 : 𝕜) ^ r / (r.factorial : 𝕜)) •
      ((S ^ (j + r) * D ^ (j + r)) x)
  congr 1
  change ((S ^ j * (S ^ r * D ^ r) * D ^ j) x) = _
  calc
    (S ^ j * (S ^ r * D ^ r) * D ^ j) x =
        ((S ^ j * S ^ r) * (D ^ r * D ^ j)) x := by
          congr 1
    _ = (S ^ (j + r) * D ^ (r + j)) x := by
          rw [← pow_add, ← pow_add]
    _ = (S ^ (j + r) * D ^ (j + r)) x := by
          rw [Nat.add_comm r j]

private lemma triangular_reindex_all {α : Type*} [AddCommMonoid α]
    (K : ℕ) (f : ℕ → ℕ → α) :
    (∑ j ∈ Finset.range (K + 1),
      ∑ r ∈ Finset.range (K + 1 - j), f j r) =
      ∑ q ∈ Finset.range (K + 1),
        ∑ j ∈ Finset.range (q + 1), f j (q - j) := by
  let s : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.range (K + 1)).sigma (fun j => Finset.range (K + 1 - j))
  let t : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.range (K + 1)).sigma (fun q => Finset.range (q + 1))
  have hs :
      (∑ j ∈ Finset.range (K + 1),
        ∑ r ∈ Finset.range (K + 1 - j), f j r) =
        ∑ a ∈ s, f a.1 a.2 := by
    dsimp [s]
    rw [Finset.sum_sigma']
  have ht :
      (∑ q ∈ Finset.range (K + 1),
        ∑ j ∈ Finset.range (q + 1), f j (q - j)) =
        ∑ a ∈ t, f a.2 (a.1 - a.2) := by
    dsimp [t]
    rw [Finset.sum_sigma']
  rw [hs, ht]
  apply Finset.sum_bij (fun a ha => ⟨a.1 + a.2, a.1⟩) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_sigma] at ha ⊢
    constructor
    · simp only [Finset.mem_range]
      have ha1 : a.1 < K + 1 := Finset.mem_range.mp ha.1
      have ha2 : a.2 < K + 1 - a.1 := Finset.mem_range.mp ha.2
      omega
    · simp only [Finset.mem_range]
      omega
  · intro a₁ ha₁ a₂ ha₂ h
    simp only [Sigma.mk.inj_iff] at h
    rcases h with ⟨hsum, hfirst⟩
    have hfirst' : a₁.1 = a₂.1 := eq_of_heq hfirst
    apply Sigma.ext
    · exact hfirst'
    · simpa [hfirst'] using (show a₁.2 = a₂.2 from by omega)
  · intro b hb
    rw [Finset.mem_sigma] at hb
    use ⟨b.2, b.1 - b.2⟩
    have hsrc : (⟨b.2, b.1 - b.2⟩ : Σ _ : ℕ, ℕ) ∈ s := by
      rw [Finset.mem_sigma]
      constructor
      · have hbq : b.1 < K + 1 := Finset.mem_range.mp hb.1
        have hbj : b.2 < b.1 + 1 := Finset.mem_range.mp hb.2
        simpa only [Finset.mem_range] using (show b.2 < K + 1 by omega)
      · simp only [Finset.mem_range]
        have hbq : b.1 < K + 1 := Finset.mem_range.mp hb.1
        have hbj : b.2 < b.1 + 1 := Finset.mem_range.mp hb.2
        omega
    refine ⟨hsrc, ?_⟩
    apply Sigma.ext
    · change b.2 + (b.1 - b.2) = b.1
      have hbj : b.2 ≤ b.1 := Nat.le_of_lt_succ (Finset.mem_range.mp hb.2)
      omega
    · simp
  · intro a ha
    simp

omit [CharZero 𝕜] in
private lemma alternating_choose_sum (q : ℕ) :
    (∑ j ∈ Finset.range (q + 1),
      ((-1 : 𝕜) ^ (q - j) * (q.choose j : 𝕜))) =
      if q = 0 then 1 else 0 := by
  have h := add_pow (1 : 𝕜) (-1 : 𝕜) q
  rw [show (1 : 𝕜) + (-1 : 𝕜) = 0 by norm_num] at h
  simp only [one_pow, one_mul] at h
  by_cases hq : q = 0
  · subst q
    norm_num at h ⊢
  · simp [hq] at h ⊢
    simpa [mul_comm] using h.symm

private lemma reciprocal_binomial_term (q j : ℕ) (hjq : j ≤ q) :
    (1 / (j.factorial : 𝕜)) *
        ((-1 : 𝕜) ^ (q - j) / ((q - j).factorial : 𝕜)) =
      (1 / (q.factorial : 𝕜)) *
        ((-1 : 𝕜) ^ (q - j) * (q.choose j : 𝕜)) := by
  have hfac : q.choose j * j.factorial * (q - j).factorial = q.factorial :=
    Nat.choose_mul_factorial_mul_factorial hjq
  have hfacQ : (q.choose j : 𝕜) * (j.factorial : 𝕜) *
      ((q - j).factorial : 𝕜) = (q.factorial : 𝕜) := by
    exact_mod_cast hfac
  have hjfac : (j.factorial : 𝕜) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have hqfac : (q.factorial : 𝕜) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero q
  have hqjfac : ((q - j).factorial : 𝕜) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (q - j)
  have hrec :
      (1 / (j.factorial : 𝕜)) * (1 / ((q - j).factorial : 𝕜)) =
        (q.choose j : 𝕜) / (q.factorial : 𝕜) := by
    field_simp
    rw [← hfacQ]
    ring
  calc
    (1 / (j.factorial : 𝕜)) *
        ((-1 : 𝕜) ^ (q - j) / ((q - j).factorial : 𝕜)) =
        ((-1 : 𝕜) ^ (q - j)) *
          ((1 / (j.factorial : 𝕜)) * (1 / ((q - j).factorial : 𝕜))) := by
            ring
    _ = ((-1 : 𝕜) ^ (q - j)) *
          ((q.choose j : 𝕜) / (q.factorial : 𝕜)) := by rw [hrec]
    _ = (1 / (q.factorial : 𝕜)) *
          ((-1 : 𝕜) ^ (q - j) * (q.choose j : 𝕜)) := by ring

private lemma reciprocal_binomial_sum (q : ℕ) :
    (∑ j ∈ Finset.range (q + 1),
      (1 / (j.factorial : 𝕜)) *
        ((-1 : 𝕜) ^ (q - j) / ((q - j).factorial : 𝕜))) =
      if q = 0 then 1 else 0 := by
  rw [show (∑ j ∈ Finset.range (q + 1),
      (1 / (j.factorial : 𝕜)) *
        ((-1 : 𝕜) ^ (q - j) / ((q - j).factorial : 𝕜))) =
      ∑ j ∈ Finset.range (q + 1),
        (1 / (q.factorial : 𝕜)) *
          ((-1 : 𝕜) ^ (q - j) * (q.choose j : 𝕜)) by
    apply Finset.sum_congr rfl
    intro j hj
    exact reciprocal_binomial_term q j
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  rw [← Finset.mul_sum]
  rw [alternating_choose_sum]
  by_cases hq : q = 0
  · simp [hq]
  · simp [hq]

omit [CharZero 𝕜] in
private lemma projectorMap_term_trim
    (K j : ℕ) (S D : V →ₗ[𝕜] V) (x : V)
    (hj : j ≤ K) (hnil : (D ^ (K + 1)) x = 0) :
    ((S ^ j * projectorMapG K S D * D ^ j) x) =
      ∑ r ∈ Finset.range (K + 1 - j),
        ((-1 : 𝕜) ^ r / (r.factorial : 𝕜)) •
          ((S ^ (j + r) * D ^ (j + r)) x) := by
  rw [projectorMap_term_all]
  symm
  apply Finset.sum_subset
  · intro r hr
    exact Finset.mem_range.mpr (by
      have hr' := Finset.mem_range.mp hr
      omega)
  · intro r hrbig hrsmall
    have hrbig' := Finset.mem_range.mp hrbig
    have hrsmall' : K + 1 - j ≤ r := by
      exact Nat.le_of_not_gt (fun hlt => hrsmall (Finset.mem_range.mpr hlt))
    have hpow : (D ^ (j + r)) x = 0 := by
      apply Module.End.pow_map_zero_of_le (m := x) (k := K + 1) (l := j + r)
      · omega
      · exact hnil
    simp [Module.End.mul_apply, hpow]

/-- The all-order finite Taylor reconstruction for a nilpotent derivative. -/
theorem reconstruction_all
    (K : ℕ) (S D : V →ₗ[𝕜] V) (x : V)
    (hnil : (D ^ (K + 1)) x = 0) :
    x =
      ∑ j ∈ Finset.range (K + 1),
        ((1 : 𝕜) / (j.factorial : 𝕜)) •
          ((S ^ j * projectorMapG K S D * D ^ j) x) := by
  have hexpand :
      (∑ j ∈ Finset.range (K + 1),
        ((1 : 𝕜) / (j.factorial : 𝕜)) •
          ((S ^ j * projectorMapG K S D * D ^ j) x)) =
      ∑ j ∈ Finset.range (K + 1),
        ∑ r ∈ Finset.range (K + 1 - j),
          (((1 : 𝕜) / (j.factorial : 𝕜)) *
              ((-1 : 𝕜) ^ r / (r.factorial : 𝕜))) •
            ((S ^ (j + r) * D ^ (j + r)) x) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [projectorMap_term_trim K j S D x hjK hnil]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [smul_smul]
  rw [hexpand, triangular_reindex_all]
  have hreindex :
      (∑ q ∈ Finset.range (K + 1),
        ∑ j ∈ Finset.range (q + 1),
          (((1 : 𝕜) / (j.factorial : 𝕜)) *
              ((-1 : 𝕜) ^ (q - j) / ((q - j).factorial : 𝕜))) •
            ((S ^ (j + (q - j)) * D ^ (j + (q - j))) x)) =
      ∑ q ∈ Finset.range (K + 1),
        ∑ j ∈ Finset.range (q + 1),
          (((1 : 𝕜) / (j.factorial : 𝕜)) *
              ((-1 : 𝕜) ^ (q - j) / ((q - j).factorial : 𝕜))) •
            ((S ^ q * D ^ q) x) := by
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro j hj
    have hjq : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [Nat.add_sub_of_le hjq]
  rw [hreindex]
  have hcollapse :
      (∑ q ∈ Finset.range (K + 1),
        ∑ j ∈ Finset.range (q + 1),
          (((1 : 𝕜) / (j.factorial : 𝕜)) *
              ((-1 : 𝕜) ^ (q - j) / ((q - j).factorial : 𝕜))) •
            ((S ^ q * D ^ q) x)) = x := by
    -- The inner scalar convolution is the inverse factorial binomial sum.
    -- The remaining q=0 term is exactly x; all q>0 terms are zero.
    have hterm (q : ℕ) :
        (∑ j ∈ Finset.range (q + 1),
          (((1 : 𝕜) / (j.factorial : 𝕜)) *
              ((-1 : 𝕜) ^ (q - j) / ((q - j).factorial : 𝕜))) •
            ((S ^ q * D ^ q) x)) =
          (if q = 0 then (1 : 𝕜) else 0) • ((S ^ q * D ^ q) x) := by
      rw [← Finset.sum_smul]
      rw [reciprocal_binomial_sum]
    simp_rw [hterm]
    simp
  exact hcollapse.symm

/-!
The following wrapper turns the endomorphism statement into the concrete
algebraic form used in a Weyl chart.  It deliberately stops at the abstract
ring/module interface: the A₂-specific work of constructing `s`, proving
`D s = 1`, and proving nilpotence on the chosen element remains external.
-/
end AlgebraicAnalysis.FiniteTaylorReconstruction
