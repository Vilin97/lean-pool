/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PieriPos

/-!
# Hook bounds on induction and Kronecker multiplicities

Deligne 1.10 and 1.12, character side: if the induction
multiplicity `[λ : μ, ν]` is nonzero and `λ` contains the cell
`(p + r, q + s)`, then `μ` contains `(p, q)` or `ν` contains
`(r, s)`; and the Kronecker analogue at
`(pr + qs, ps + qr)`.  Both by evaluation: the Schur
specialisation of `λ` at the corresponding super power sum
vanishes, every term of the bilinear splitting is a natural
number, so every term vanishes; hook positivity makes the two
specialisation factors nonzero, killing the multiplicity.
-/

@[expose] public section

namespace RS

/-- A finite sum of natural values vanishing termwise: if every
summand is a natural number and the sum is zero, each summand is
zero. -/
theorem eq_zero_of_sum_nat_eq_zero {ι : Type*} {s : Finset ι}
    {f : ι → ℂ} (h : ∀ i ∈ s, ∃ m : ℕ, f i = m)
    (h0 : ∑ i ∈ s, f i = 0) : ∀ i ∈ s, f i = 0 := by
  classical
  -- Replace each value by its chosen natural witness.
  have hg : ∀ i ∈ s, f i =
      ((if h' : i ∈ s then Classical.choose (h i h') else 0 : ℕ) :
        ℂ) := by
    intro i hi
    rw [dite_eq_left hi]
    exact Classical.choose_spec (h i hi)
  have hsum : ((∑ i ∈ s,
      (if h' : i ∈ s then Classical.choose (h i h') else 0) : ℕ) :
        ℂ) = 0 := by
    rw [Nat.cast_sum, ← h0]
    exact (Finset.sum_congr rfl hg).symm
  rw [Nat.cast_eq_zero] at hsum
  intro i hi
  rw [hg i hi]
  have := (Finset.sum_eq_zero_iff.mp hsum) i hi
  rw [this, Nat.cast_zero]

/-- **Deligne 1.10, character side**: an induction multiplicity
dies against the fat hook — if `λ` contains `(p + r, q + s)` while
`μ` avoids `(p, q)` and `ν` avoids `(r, s)`, then `[λ : μ, ν] = 0`.
-/
theorem indMult_eq_zero_of_cells {a b : ℕ} (lam : Shape (a + b))
    (μ : Shape a) (ν : Shape b) {p q r s : ℕ}
    (hμ : (p, q) ∉ μ.val) (hν : (r, s) ∉ ν.val)
    (hlam : (p + r, q + s) ∈ lam.val) : indMult lam μ ν = 0 := by
  classical
  -- The specialisation of `λ` at the summed point vanishes.
  have hzero : diagramSchur lam.val
      (fun c => superPS p q c + superPS r s c) = 0 := by
    rw [show (fun c => superPS p q c + superPS r s c) =
      superPS (p + r) (q + s) from superPS_add p q r s]
    exact diagramSchur_superPS_eq_zero lam.val hlam
  rw [diagramSchur_add] at hzero
  -- Every outer summand is a natural number.
  have houter : ∀ ab ∈ (Finset.antidiagonal lam.val.card).attach,
      ∃ m : ℕ,
      (∑ μ' : Shape ab.1.1, ∑ ν' : Shape ab.1.2,
        indMult ⟨lam.val,
            (Finset.mem_antidiagonal.mp ab.2).symm⟩ μ' ν' *
          diagramSchur μ'.val (superPS p q) *
          diagramSchur ν'.val (superPS r s)) = m := by
    intro ab _
    refine exists_nat_sum _ _ fun μ' _ => ?_
    refine exists_nat_sum _ _ fun ν' _ => ?_
    obtain ⟨m₁, h₁⟩ := indMult_exists_nat
      (⟨lam.val, (Finset.mem_antidiagonal.mp ab.2).symm⟩ :
        Shape (ab.1.1 + ab.1.2)) μ' ν'
    obtain ⟨m₂, h₂⟩ := diagramSchur_superPS_exists_nat p q μ'.val
    obtain ⟨m₃, h₃⟩ := diagramSchur_superPS_exists_nat r s ν'.val
    exact ⟨m₁ * m₂ * m₃, by
      rw [h₁, h₂, h₃, Nat.cast_mul, Nat.cast_mul]⟩
  -- Extract the `(a, b)` term, then the `(μ, ν)` term.
  have hab : ((a, b) : ℕ × ℕ) ∈
      Finset.antidiagonal lam.val.card :=
    Finset.mem_antidiagonal.mpr lam.prop.symm
  have hterm := eq_zero_of_sum_nat_eq_zero houter hzero
    ⟨(a, b), hab⟩ (Finset.mem_attach _ _)
  have hinner : ∀ μ' ∈ (Finset.univ : Finset (Shape a)),
      ∃ m : ℕ,
      (∑ ν' : Shape b,
        indMult ⟨lam.val, lam.prop⟩ μ' ν' *
          diagramSchur μ'.val (superPS p q) *
          diagramSchur ν'.val (superPS r s)) = m := by
    intro μ' _
    refine exists_nat_sum _ _ fun ν' _ => ?_
    obtain ⟨m₁, h₁⟩ := indMult_exists_nat
      (⟨lam.val, lam.prop⟩ : Shape (a + b)) μ' ν'
    obtain ⟨m₂, h₂⟩ := diagramSchur_superPS_exists_nat p q μ'.val
    obtain ⟨m₃, h₃⟩ := diagramSchur_superPS_exists_nat r s ν'.val
    exact ⟨m₁ * m₂ * m₃, by
      rw [h₁, h₂, h₃, Nat.cast_mul, Nat.cast_mul]⟩
  have hμterm := eq_zero_of_sum_nat_eq_zero hinner
    (by exact hterm) μ (Finset.mem_univ μ)
  have hνnat : ∀ ν' ∈ (Finset.univ : Finset (Shape b)),
      ∃ m : ℕ,
      indMult ⟨lam.val, lam.prop⟩ μ ν' *
        diagramSchur μ.val (superPS p q) *
        diagramSchur ν'.val (superPS r s) = m := by
    intro ν' _
    obtain ⟨m₁, h₁⟩ := indMult_exists_nat
      (⟨lam.val, lam.prop⟩ : Shape (a + b)) μ ν'
    obtain ⟨m₂, h₂⟩ := diagramSchur_superPS_exists_nat p q μ.val
    obtain ⟨m₃, h₃⟩ := diagramSchur_superPS_exists_nat r s ν'.val
    exact ⟨m₁ * m₂ * m₃, by
      rw [h₁, h₂, h₃, Nat.cast_mul, Nat.cast_mul]⟩
  have hfinal := eq_zero_of_sum_nat_eq_zero hνnat hμterm ν
    (Finset.mem_univ ν)
  -- Both specialisation factors are nonzero; the multiplicity dies.
  obtain ⟨m₂, hm₂, h₂⟩ := diagramSchur_superPS_pos μ.val hμ
  obtain ⟨m₃, hm₃, h₃⟩ := diagramSchur_superPS_pos ν.val hν
  have h₂' : diagramSchur μ.val (superPS p q) ≠ 0 := by
    rw [h₂]
    exact_mod_cast hm₂.ne'
  have h₃' : diagramSchur ν.val (superPS r s) ≠ 0 := by
    rw [h₃]
    exact_mod_cast hm₃.ne'
  have := mul_eq_zero.mp hfinal
  rcases this with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · rwa [show (⟨lam.val, lam.prop⟩ : Shape (a + b)) = lam from
        Subtype.ext rfl] at h'
    · exact absurd h' h₂'
  · exact absurd h h₃'

/-- Deligne 1.10 in its positive form: a nonzero induction
multiplicity pushes a fat-hook cell of `λ` into `μ` or `ν`. -/
theorem cell_of_indMult_ne_zero {a b : ℕ} (lam : Shape (a + b))
    (μ : Shape a) (ν : Shape b) {p q r s : ℕ}
    (h : indMult lam μ ν ≠ 0)
    (hlam : (p + r, q + s) ∈ lam.val) :
    (p, q) ∈ μ.val ∨ (r, s) ∈ ν.val := by
  by_contra hcon
  push Not at hcon
  exact h (indMult_eq_zero_of_cells lam μ ν hcon.1 hcon.2 hlam)

/-- **Deligne 1.12, character side**: a Kronecker multiplicity
dies against the product hook. -/
theorem kronMult_eq_zero_of_cells {n : ℕ} (lam μ ν : Shape n)
    {p q r s : ℕ} (hμ : (p, q) ∉ μ.val) (hν : (r, s) ∉ ν.val)
    (hlam : (p * r + q * s, p * s + q * r) ∈ lam.val) :
    kronMult lam μ ν = 0 := by
  classical
  obtain ⟨L, hL⟩ := lam
  obtain ⟨M, hM⟩ := μ
  obtain ⟨N, hN⟩ := ν
  subst hL
  simp only at hμ hν hlam ⊢
  have hzero : diagramSchur L
      (fun c => superPS p q c * superPS r s c) = 0 := by
    rw [show (fun c => superPS p q c * superPS r s c) =
      superPS (p * r + q * s) (p * s + q * r) from
        superPS_mul p q r s]
    exact diagramSchur_superPS_eq_zero L hlam
  rw [diagramSchur_pointwise_mul] at hzero
  have houter : ∀ μ' ∈ (Finset.univ : Finset (Shape L.card)),
      ∃ m : ℕ,
      (∑ ν' : Shape L.card,
        kronMult ⟨L, rfl⟩ μ' ν' *
          diagramSchur μ'.val (superPS p q) *
          diagramSchur ν'.val (superPS r s)) = m := by
    intro μ' _
    refine exists_nat_sum _ _ fun ν' _ => ?_
    obtain ⟨m₁, h₁⟩ := kronMult_exists_nat
      (⟨L, rfl⟩ : Shape L.card) μ' ν'
    obtain ⟨m₂, h₂⟩ := diagramSchur_superPS_exists_nat p q μ'.val
    obtain ⟨m₃, h₃⟩ := diagramSchur_superPS_exists_nat r s ν'.val
    exact ⟨m₁ * m₂ * m₃, by
      rw [h₁, h₂, h₃, Nat.cast_mul, Nat.cast_mul]⟩
  have hμterm := eq_zero_of_sum_nat_eq_zero houter hzero
    ⟨M, hM⟩ (Finset.mem_univ _)
  have hνnat : ∀ ν' ∈ (Finset.univ : Finset (Shape L.card)),
      ∃ m : ℕ,
      kronMult ⟨L, rfl⟩ ⟨M, hM⟩ ν' *
        diagramSchur M (superPS p q) *
        diagramSchur ν'.val (superPS r s) = m := by
    intro ν' _
    obtain ⟨m₁, h₁⟩ := kronMult_exists_nat
      (⟨L, rfl⟩ : Shape L.card) ⟨M, hM⟩ ν'
    obtain ⟨m₂, h₂⟩ := diagramSchur_superPS_exists_nat p q M
    obtain ⟨m₃, h₃⟩ := diagramSchur_superPS_exists_nat r s ν'.val
    exact ⟨m₁ * m₂ * m₃, by
      rw [h₁, h₂, h₃, Nat.cast_mul, Nat.cast_mul]⟩
  have hfinal := eq_zero_of_sum_nat_eq_zero hνnat hμterm
    ⟨N, hN⟩ (Finset.mem_univ _)
  obtain ⟨m₂, hm₂, h₂⟩ := diagramSchur_superPS_pos M hμ
  obtain ⟨m₃, hm₃, h₃⟩ := diagramSchur_superPS_pos N hν
  have h₂' : diagramSchur M (superPS p q) ≠ 0 := by
    rw [h₂]
    exact_mod_cast hm₂.ne'
  have h₃' : diagramSchur N (superPS r s) ≠ 0 := by
    rw [h₃]
    exact_mod_cast hm₃.ne'
  rcases mul_eq_zero.mp hfinal with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' h₂'
  · exact absurd h h₃'

/-- Deligne 1.12 in its positive form. -/
theorem cell_of_kronMult_ne_zero {n : ℕ} (lam μ ν : Shape n)
    {p q r s : ℕ} (h : kronMult lam μ ν ≠ 0)
    (hlam : (p * r + q * s, p * s + q * r) ∈ lam.val) :
    (p, q) ∈ μ.val ∨ (r, s) ∈ ν.val := by
  by_contra hcon
  push Not at hcon
  exact h (kronMult_eq_zero_of_cells lam μ ν hcon.1 hcon.2 hlam)

end RS
