/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.TensorTrace
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.BinomialH
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PackageAssembly

/-!
# Signed tensor identities

The sign-twisted cycle product for constant sequences, and the
signed Frobenius sum expressing the twisted trace in terms of
Schur values at the negated sequence.
-/

@[expose] public section

namespace RS

open Finset

/-! ## Helper: cycleProd at a constant sequence -/

/-- `cycleProd` at a constant sequence is a single power. -/
theorem cycleProd_const {n : ℕ} (c : ℂ) (π : Equiv.Perm (Fin n)) :
    cycleProd (fun _ => c) π =
      c ^ (Multiset.card π.cycleType + (n - π.cycleType.sum)) := by
  unfold cycleProd
  rw [Multiset.map_const', Multiset.prod_replicate, pow_add]

/-! ## Helper: ℤˣ sign cast to ℂ -/

/-- The sign of a permutation, cast ℤˣ → ℤ → ℂ, equals `(-1 : ℂ)` raised
    to `cycleType.sum + card cycleType`. -/
theorem sign_cast_complex {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign π : ℤ) : ℂ) =
      (-1 : ℂ) ^ (π.cycleType.sum + Multiset.card π.cycleType) := by
  rw [Equiv.Perm.sign_of_cycleType]
  push_cast
  ring

/-! ## Helper: parity identity -/

private theorem neg_one_pow_parity {s c n : ℕ} (hsn : s ≤ n) :
    (-1 : ℂ) ^ (s + c) = (-1 : ℂ) ^ (n + (c + (n - s))) := by
  apply neg_one_pow_congr
  constructor
  · intro ⟨k, hk⟩; exact ⟨k + (n - s), by omega⟩
  · intro ⟨k, hk⟩; exact ⟨k - (n - s), by omega⟩

/-! ## The sign twist of a constant cycle product -/

open scoped Classical in
/-- The sign twist of a constant cycle product is the product at the
negated constant. -/
theorem sign_mul_cycleProd_const {n : ℕ} (m : ℕ)
    (π : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign π : ℤ) : ℂ) *
      cycleProd (fun _ => (m : ℂ)) π =
    ((-1 : ℂ)) ^ n * cycleProd (fun _ => -(m : ℂ)) π := by
  rw [cycleProd_const (m : ℂ) π, cycleProd_const (-(m : ℂ)) π]
  rw [sign_cast_complex π]
  set s := π.cycleType.sum
  set c := Multiset.card π.cycleType
  set K := c + (n - s)
  have hsn : s ≤ n := by
    have := Equiv.Perm.sum_cycleType_le π
    simp? [Fintype.card_fin] at this
    exact this
  -- RHS: (-1)^n * ((-m)^K) = (-1)^n * ((-1)^K * m^K)
  have hneg : (-(m : ℂ)) ^ K = (-1 : ℂ) ^ K * (m : ℂ) ^ K :=
    neg_pow (m : ℂ) K
  rw [hneg]
  -- LHS = (-1)^(s+c) * m^K, RHS = (-1)^n * ((-1)^K * m^K)
  -- Rewrite RHS: (-1)^n * ((-1)^K * m^K) = (-1)^(n+K) * m^K
  rw [← mul_assoc, ← pow_add]
  -- Now: (-1)^(s+c) * m^K = (-1)^(n+K) * m^K
  congr 1
  exact neg_one_pow_parity hsn

/-! ## The signed Frobenius sum -/

open scoped Classical in
/-- **The signed Frobenius sum**: the twisted trace is the Schur
value at the negated sequence, up to the sign and the factorial. -/
theorem signed_tensor_sum (m : ℕ) (μ : YoungDiagram) :
    (∑ π : Equiv.Perm (Fin μ.card),
      jtChar μ π * (((Equiv.Perm.sign π : ℤ) : ℂ) *
        cycleProd (fun _ => (m : ℂ)) π)) =
    ((-1 : ℂ)) ^ μ.card * (μ.card.factorial : ℂ) *
      diagramSchur μ (fun _ => -(m : ℂ)) := by
  -- Step 1: rewrite each summand using sign_mul_cycleProd_const
  have hrew : ∀ π : Equiv.Perm (Fin μ.card), π ∈ Finset.univ →
      jtChar μ π * (((Equiv.Perm.sign π : ℤ) : ℂ) *
        cycleProd (fun _ => (m : ℂ)) π) =
      jtChar μ π * (((-1 : ℂ)) ^ μ.card *
        cycleProd (fun _ => -(m : ℂ)) π) := by
    intro π _
    rw [sign_mul_cycleProd_const m π]
  rw [Finset.sum_congr rfl hrew]
  -- Step 2: factor out (-1)^μ.card and reassociate
  have hassoc : ∀ π : Equiv.Perm (Fin μ.card), π ∈ Finset.univ →
      jtChar μ π * (((-1 : ℂ)) ^ μ.card *
        cycleProd (fun _ => -(m : ℂ)) π) =
      ((-1 : ℂ)) ^ μ.card *
        (jtChar μ π * cycleProd (fun _ => -(m : ℂ)) π) := by
    intro π _
    ring
  rw [Finset.sum_congr rfl hassoc, ← Finset.mul_sum]
  -- Step 3: apply jtChar_frobenius'
  have hfrob := jtChar_frobenius' μ (fun _ => -(m : ℂ))
  have hfac : ((μ.card.factorial : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero μ.card
  have hsum : (∑ π : Equiv.Perm (Fin μ.card),
      jtChar μ π * cycleProd (fun _ => -(m : ℂ)) π) =
      (μ.card.factorial : ℂ) *
        diagramSchur μ (fun _ => -(m : ℂ)) := by
    rw [← hfrob, ← mul_assoc, mul_inv_cancel₀ hfac, one_mul]
  rw [hsum]
  ring

end RS
