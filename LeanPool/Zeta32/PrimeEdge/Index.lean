/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! the proof notes, §6: the greedy layout for `n = p - 1`, layout (4,5,3).

Classes `b ∈ {0, …, p-1}` of the disc `t = -b + p u`:
* zero class `b = 0`: column base `c_0 = -5`, multiplicity `4`, levels `-5, -3, -1, 1`;
* low classes `1 ≤ b ≤ p-5` (`b + 5 ≤ p`): `c_b = -3`, multiplicity `3`, levels `-3, -1, 1`;
* high classes `p-4 ≤ b ≤ p-1`: `c_b = -2`, multiplicity `2`, levels `-2, 0`.

A basis vector is `a = ⟨b, i⟩ : Idx p` with `i < mult p b`; its greedy level is
`level a = c_b + 2 i` and its weight is `rho a = level a / 2`.
`kmul a d` is the multiplicity of `(t + d)` in the CRT basis vector `a`, and
`discExp a c d = c_d + kmul a d + kmul c d` is the Lemma 4 exponent of the entry `(a, c)` on
disc `d`. -/

public section

open scoped BigOperators
namespace Zeta32.PrimeEdge

/-- Multiplicity `m_b` of the class `b` in the CRT basis. -/
def mult (p b : ℕ) : ℕ := if b = 0 then 4 else if b + 5 ≤ p then 3 else 2

/-- Greedy column base `c_b = s N_b - C_b + [b = 0] - 2` for `n = p - 1`. -/
def colBase (p b : ℕ) : ℤ := if b = 0 then -5 else if b + 5 ≤ p then -3 else -2

/-- Basis index: a class `b` and an order `i < m_b`. -/
abbrev Idx (p : ℕ) := (b : Fin p) × Fin (mult p b.val)

/-- Greedy level `π_a = c_b + 2 i`. -/
def level (p : ℕ) (a : Idx p) : ℤ := colBase p a.1.val + 2 * (a.2.val : ℤ)

/-- Row/column weight `ρ_a = π_a / 2`. -/
def rho (p : ℕ) (a : Idx p) : ℚ := (level p a : ℚ) / 2

/-- Multiplicity of `(t + d)` in the basis vector `a`. -/
def kmul (p : ℕ) (a : Idx p) (d : ℕ) : ℕ := if a.1.val = d then a.2.val else mult p d

/-- Lemma 4 exponent of the entry `(a, c)` on the disc `d`. -/
def discExp (p : ℕ) (a c : Idx p) (d : ℕ) : ℤ :=
  colBase p d + (kmul p a d : ℤ) + (kmul p c d : ℤ)

variable {p : ℕ}

theorem sum_mult (hp : 5 ≤ p) : ∑ b ∈ Finset.range p, mult p b = 3 * (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 5 := ⟨p - 5, by omega⟩
  rw [show q + 5 = (q + 1) + 4 by ring, Finset.sum_range_add, Finset.sum_range_succ']
  have h1 : ∀ x ∈ Finset.range q, mult (q + 1 + 4) (x + 1) = 3 := fun x hx => by
    simp only [Finset.mem_range] at hx
    simp only [mult]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  have h2 : ∀ x ∈ Finset.range 4, mult (q + 1 + 4) (q + 1 + x) = 2 := fun x hx => by
    simp only [Finset.mem_range] at hx
    simp only [mult]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  simp [mult]
  omega

theorem card_Idx (hp : 5 ≤ p) : Fintype.card (Idx p) = 3 * (p - 1) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun b => mult p b) p]
  exact sum_mult hp

lemma level_le_one (a : Idx p) : level p a ≤ 1 := by
  obtain ⟨b, i⟩ := a
  have hi := i.isLt
  simp only [level, colBase, mult] at hi ⊢
  split_ifs at hi ⊢ <;> omega

lemma two_le_colBase_add_mult (d : ℕ) : 2 ≤ colBase p d + 2 * (mult p d : ℤ) := by
  simp only [colBase, mult]
  split_ifs <;> norm_num

/-- Greedy property: `c_d + 2 k_d(a) ≥ π_a` on every disc. -/
lemma level_le_disc (a : Idx p) (d : ℕ) : level p a ≤ colBase p d + 2 * (kmul p a d : ℤ) := by
  unfold kmul
  split_ifs with h
  · rw [← h]; simp [level]
  · linarith [level_le_one a, two_le_colBase_add_mult (p := p) d]

lemma level_add_le_discExp (a c : Idx p) (d : ℕ) :
    level p a + level p c ≤ 2 * discExp p a c d := by
  unfold discExp
  linarith [level_le_disc a d, level_le_disc c d]

/-- No tie: across two different classes the greedy inequality is strict. -/
lemma level_add_lt_discExp (a c : Idx p) (hac : a.1 ≠ c.1) (d : ℕ) :
    level p a + level p c + 1 ≤ 2 * discExp p a c d := by
  unfold discExp
  have ha := level_le_disc a d
  have hc := level_le_disc c d
  have h2 := two_le_colBase_add_mult (p := p) d
  have hla := level_le_one a
  have hlc := level_le_one c
  by_cases h : a.1.val = d
  · have hc' : kmul p c d = mult p d := by
      unfold kmul
      rw [ite_eq_right (fun h' => hac (Fin.ext (h.trans h'.symm)))]
    rw [hc']
    linarith
  · have ha' : kmul p a d = mult p d := by
      unfold kmul
      rw [ite_eq_right h]
    rw [ha']
    linarith

lemma rho_add_le_discExp (a c : Idx p) (d : ℕ) :
    rho p a + rho p c ≤ (discExp p a c d : ℚ) := by
  have h := level_add_le_discExp a c d
  have h' : ((level p a + level p c : ℤ) : ℚ) ≤ ((2 * discExp p a c d : ℤ) : ℚ) := by
    exact_mod_cast h
  push_cast at h'
  unfold rho
  linarith

lemma rho_add_half_le_discExp (a c : Idx p) (hac : a.1 ≠ c.1) (d : ℕ) :
    rho p a + rho p c + 1/2 ≤ (discExp p a c d : ℚ) := by
  have h := level_add_lt_discExp a c hac d
  have h' : ((level p a + level p c + 1 : ℤ) : ℚ) ≤ ((2 * discExp p a c d : ℤ) : ℚ) := by
    exact_mod_cast h
  push_cast at h'
  unfold rho
  linarith

/-- Same class `b`: `ρ_a + ρ_c = c_b + i + k`, an integer. -/
lemma rho_add_of_same (a c : Idx p) (hac : a.1 = c.1) :
    rho p a + rho p c = ((colBase p a.1.val + a.2.val + c.2.val : ℤ) : ℚ) := by
  have hb : colBase p c.1.val = colBase p a.1.val := by rw [hac]
  unfold rho level
  rw [hb]
  push_cast
  ring

end Zeta32.PrimeEdge

end
