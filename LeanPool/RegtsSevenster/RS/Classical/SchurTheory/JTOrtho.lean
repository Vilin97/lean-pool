/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PairChar
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PairTuple
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.TCount
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.JTChar

/-!
# Orthonormality of the Jacobi–Trudi characters

The Jacobi–Trudi characters are orthonormal for the class inner
product of the symmetric group, which is what makes them the
irreducible characters.
-/

@[expose] public section

namespace RS

open Finset Equiv

open scoped Classical in
/-- **The Jacobi–Trudi characters are of unit norm** for the class
inner product — which is what makes them irreducible characters. -/
theorem jtChar_orthonormal (μ : YoungDiagram) :
    ((μ.card.factorial : ℂ))⁻¹ *
      ∑ π : Equiv.Perm (Fin μ.card), jtChar μ π * jtChar μ π = 1 := by
  set n := μ.card with hn_def
  -- ═══════ SETUP: THE SORT HYPOTHESIS FOR `t_count` ═══════
  have hsort : ∀ i j : Fin μ.rowLens.length, i ≤ j →
      (fun i : Fin μ.rowLens.length => μ.rowLens.get i) j ≤
      (fun i : Fin μ.rowLens.length => μ.rowLens.get i) i :=
    μ.rowLens_sorted.antitone_get
  suffices hsum : (∑ π : Equiv.Perm (Fin n),
      jtChar μ π * jtChar μ π : ℂ) = (n.factorial : ℂ) by
    rw [hsum, inv_mul_cancel₀
      (by exact_mod_cast Nat.factorial_ne_zero n)]
  -- ═══════ STAGE 1: EXPAND `jtChar` AND EXCHANGE THE SUMS ═══════
  -- to ∑ σ ∑ τ ... (∑ π colourChar * colourChar)
  have hstep1 : (∑ π : Equiv.Perm (Fin n),
      jtChar μ π * jtChar μ π : ℂ) =
    ∑ σ : Equiv.Perm (Fin μ.rowLens.length), ∑ τ : Equiv.Perm (Fin
      μ.rowLens.length),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
        (if (∀ i, 0 ≤ jtSigned μ σ i) ∧ (∀ i, 0 ≤ jtSigned μ τ i)
          then ∑ π : Equiv.Perm (Fin n),
            (colourChar (jtComp μ σ) π : ℂ) * (colourChar (jtComp μ τ) π : ℂ)
          else 0) := by
    -- Expand jtChar * jtChar as a double sum
    rw [Finset.sum_congr rfl (fun (π : Equiv.Perm (Fin n)) (_ : π ∈ Finset.univ)
      =>
      show jtChar μ π * jtChar μ π =
        ∑ σ : Equiv.Perm (Fin μ.rowLens.length), ∑ τ : Equiv.Perm (Fin
          μ.rowLens.length),
          (((Equiv.Perm.sign σ : ℤ) : ℂ) *
            (if ∀ i, 0 ≤ jtSigned μ σ i
              then (colourChar (jtComp μ σ) π : ℂ) else 0)) *
          (((Equiv.Perm.sign τ : ℤ) : ℂ) *
            (if ∀ i, 0 ≤ jtSigned μ τ i
              then (colourChar (jtComp μ τ) π : ℂ) else 0))
      from by rw [jtChar, Finset.sum_mul_sum])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    by_cases hσ : ∀ i, 0 ≤ jtSigned μ σ i
    · by_cases hτ : ∀ i, 0 ≤ jtSigned μ τ i
      · rw [ite_eq_left ⟨hσ, hτ⟩, Finset.mul_sum]
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [ite_eq_left hσ, ite_eq_left hτ]; ring
      · rw [ite_eq_right (fun hc => hτ hc.2)]
        rw [Finset.sum_eq_zero fun π _ => by
          rw [ite_eq_right hτ, mul_zero, mul_zero]]
        rw [mul_zero]
    · rw [ite_eq_right (fun hc => hσ hc.1)]
      rw [show (∑ π : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          (if ∀ i, 0 ≤ jtSigned μ σ i
            then (colourChar (jtComp μ σ) π : ℂ) else 0) *
          (((Equiv.Perm.sign τ : ℤ) : ℂ) *
            (if ∀ i, 0 ≤ jtSigned μ τ i
              then (colourChar (jtComp μ τ) π : ℂ) else 0))) = 0
        from Finset.sum_eq_zero fun π _ => by
          rw [ite_eq_right hσ, mul_zero, zero_mul]]
      rw [mul_zero]
  -- ═══════ STAGE 2: PRODUCTS OF CHARACTERS AS FILTER CARDS ═══════
  -- colourChar values are ℕ, so colourChar * colourChar is ℕ too
  have hstep2 : ∀ (σ τ : Equiv.Perm (Fin μ.rowLens.length)),
      (∀ i, 0 ≤ jtSigned μ σ i) → (∀ i, 0 ≤ jtSigned μ τ i) →
      (∑ π : Equiv.Perm (Fin n),
        (colourChar (jtComp μ σ) π : ℂ) *
        (colourChar (jtComp μ τ) π : ℂ)) =
      ((∑ π : Equiv.Perm (Fin n),
        colourChar (jtComp μ σ) π * colourChar (jtComp μ τ) π : ℕ) : ℂ) := by
    intro σ τ _ _
    push_cast
    rfl
  -- ═══════ STAGE 3: THE COUNT IS `n!` TIMES A PAIR COUNT ═══════
  have hstep3 : ∀ (σ τ : Equiv.Perm (Fin μ.rowLens.length)),
      (∀ i, 0 ≤ jtSigned μ σ i) → (∀ i, 0 ≤ jtSigned μ τ i) →
      (∑ π : Equiv.Perm (Fin n),
        colourChar (jtComp μ σ) π * colourChar (jtComp μ τ) π : ℕ) =
      n.factorial * Fintype.card {s : Sym (Fin μ.rowLens.length × Fin
        μ.rowLens.length) n //
        (∀ a, (∑ b : Fin μ.rowLens.length, s.1.count (a, b)) = jtComp μ σ a) ∧
        (∀ b, (∑ a : Fin μ.rowLens.length, s.1.count (a, b)) = jtComp μ τ b)}
          := by
    intro σ τ _ _
    rw [Finset.sum_congr rfl (fun (π : Equiv.Perm (Fin n)) (_ : π ∈ Finset.univ)
      =>
      colourChar_mul (jtComp μ σ) (jtComp μ τ) π)]
    exact pair_count_sum (jtComp μ σ) (jtComp μ τ)
  -- ═══════ STAGE 4: PAIR COUNT AS TUPLE COUNT ═══════
  have hstep4 : ∀ (σ τ : Equiv.Perm (Fin μ.rowLens.length)),
      (hσ : ∀ i, 0 ≤ jtSigned μ σ i) → (hτ : ∀ i, 0 ≤ jtSigned μ τ i) →
      Fintype.card {s : Sym (Fin μ.rowLens.length × Fin μ.rowLens.length) n //
        (∀ a, (∑ b : Fin μ.rowLens.length, s.1.count (a, b)) = jtComp μ σ a) ∧
        (∀ b, (∑ a : Fin μ.rowLens.length, s.1.count (a, b)) = jtComp μ τ b)} =
      Fintype.card {W : ∀ a : Fin μ.rowLens.length, Sym (Fin μ.rowLens.length)
        (jtComp μ σ a) //
        ∀ b : Fin μ.rowLens.length, (∑ a : Fin μ.rowLens.length, (W a).1.count
          b) = jtComp μ τ b} := by
    intro σ τ hσ _
    exact pair_tuple_card (jtComp μ σ) (jtComp μ τ) (sum_jtComp μ σ hσ)
  -- ═══════ ASSEMBLY: CHAIN THE FOUR STAGES INTO `t_count` ═══════
  rw [hstep1]
  -- Rewrite each (σ, τ) term
  have hterm : ∀ (σ τ : Equiv.Perm (Fin μ.rowLens.length)),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
        (if (∀ i, 0 ≤ jtSigned μ σ i) ∧ (∀ i, 0 ≤ jtSigned μ τ i)
          then ∑ π : Equiv.Perm (Fin n),
            (colourChar (jtComp μ σ) π : ℂ) * (colourChar (jtComp μ τ) π : ℂ)
          else 0) =
      (n.factorial : ℂ) *
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
          (if (∀ i, 0 ≤ jtSigned μ σ i) ∧ (∀ i, 0 ≤ jtSigned μ τ i)
            then (Fintype.card {W : ∀ a : Fin μ.rowLens.length,
                Sym (Fin μ.rowLens.length) (jtComp μ σ a) //
              ∀ b : Fin μ.rowLens.length, (∑ a : Fin μ.rowLens.length, (W
                a).1.count b) =
                jtComp μ τ b} : ℂ)
            else 0)) := by
    intro σ τ
    by_cases hboth : (∀ i, 0 ≤ jtSigned μ σ i) ∧ (∀ i, 0 ≤ jtSigned μ τ i)
    · rw [ite_eq_left hboth, ite_eq_left hboth]
      rw [hstep2 σ τ hboth.1 hboth.2, hstep3 σ τ hboth.1 hboth.2,
        hstep4 σ τ hboth.1 hboth.2]
      push_cast; ring
    · rw [ite_eq_right hboth, ite_eq_right hboth, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl (fun (σ : Equiv.Perm (Fin μ.rowLens.length)) (_ : σ ∈
    Finset.univ) =>
    Finset.sum_congr rfl (fun (τ : Equiv.Perm (Fin μ.rowLens.length)) (_ : τ ∈
      Finset.univ) =>
      hterm σ τ))]
  simp only [← Finset.mul_sum]
  -- Now need: n.factorial * (∑ σ ∑ τ ...) = n.factorial
  -- Suffices: the double sum = 1
  suffices hdbl : (∑ σ : Equiv.Perm (Fin μ.rowLens.length), ∑ τ : Equiv.Perm
    (Fin μ.rowLens.length),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
        (if (∀ i, 0 ≤ jtSigned μ σ i) ∧ (∀ i, 0 ≤ jtSigned μ τ i)
          then (Fintype.card {W : ∀ a : Fin μ.rowLens.length,
              Sym (Fin μ.rowLens.length) (jtComp μ σ a) //
            ∀ b : Fin μ.rowLens.length, (∑ a : Fin μ.rowLens.length, (W
              a).1.count b) =
              jtComp μ τ b} : ℂ)
          else 0)) = 1 by
    rw [hdbl, mul_one]
  -- Swap sum order to match t_count (which has τ outer, σ inner)
  rw [Finset.sum_comm]
  -- Now: ∑ τ ∑ σ, sign σ * sign τ * if ... then card{W...} else 0
  -- Swap sign σ and sign τ to match t_count
  rw [Finset.sum_congr rfl (fun (τ : Equiv.Perm (Fin μ.rowLens.length)) (_ : τ ∈
    Finset.univ) =>
    Finset.sum_congr rfl (fun (σ : Equiv.Perm (Fin μ.rowLens.length)) (_ : σ ∈
      Finset.univ) =>
      show ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
        (if (∀ i, 0 ≤ jtSigned μ σ i) ∧ (∀ i, 0 ≤ jtSigned μ τ i)
          then (Fintype.card {W : ∀ a : Fin μ.rowLens.length,
              Sym (Fin μ.rowLens.length) (jtComp μ σ a) //
            ∀ b : Fin μ.rowLens.length, (∑ a : Fin μ.rowLens.length, (W
              a).1.count b) =
              jtComp μ τ b} : ℂ)
          else 0) =
        ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        (if (∀ i, 0 ≤ jtSigned μ σ i) ∧ (∀ i, 0 ≤ jtSigned μ τ i)
          then (Fintype.card {W : ∀ a : Fin μ.rowLens.length,
              Sym (Fin μ.rowLens.length) (jtComp μ σ a) //
            ∀ b : Fin μ.rowLens.length, (∑ a : Fin μ.rowLens.length, (W
              a).1.count b) =
              jtComp μ τ b} : ℂ)
          else 0) from by ring_nf))]
  -- Now match with t_count
  -- t_count uses v = μ.rowLens.get; jtSigned/jtComp are defined in terms of
  --   this
  -- Need to show-retype to align definitional forms
  convert t_count (fun i : Fin μ.rowLens.length => μ.rowLens.get i) hsort
    using 2
  exact rfl

end RS
