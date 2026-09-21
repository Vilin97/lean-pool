/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Derivation.Escape

/-!
# Right-sided span consequences of escape

The preceding file proves the scalar/unit-production kernel.  This file
records the next unconditional module step, with right-sided order visible:
the free module `Fin n → S` is regarded as a left module over `Sᵐᵒᵖ`, so
scalar multiplication by `op a` is right multiplication by `a` in `S`.

No claim is made here that a particular escape family produces the pure
coordinate vectors.  That is the remaining Stafford correction construction.
-/

namespace AlgebraicAnalysis.EscapeSpan

open AlgebraicAnalysis.Escape

noncomputable section

variable {S : Type*} [Ring S] {n : ℕ}

/-- Coordinatewise right multiplication in the free right `S`-module. -/
def rightMulVector (v : Fin n → S) (a : S) : Fin n → S :=
  fun i => v i * a

@[simp]
theorem rightMulVector_apply (v : Fin n → S) (a : S) (i : Fin n) :
    rightMulVector v a i = v i * a := rfl

@[simp]
theorem op_smul_vector (v : Fin n → S) (a : S) :
    (MulOpposite.op a : Sᵐᵒᵖ) • v = rightMulVector v a := by
  rfl

/-- Coordinatewise commutator with the distinguished escape coordinate. -/
def commutatorVector (x : S) (v : Fin n → S) : Fin n → S :=
  fun i => commutator x (v i)

@[simp]
theorem commutatorVector_apply (x : S) (v : Fin n → S) (i : Fin n) :
    commutatorVector x v i = commutator x (v i) := rfl

@[simp]
theorem commutatorVector_iterate_apply (x : S) (v : Fin n → S)
    (k : ℕ) (i : Fin n) :
    (commutatorVector x)^[k] v i =
      (commutator x)^[k] (v i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc
        ((commutatorVector x)^[k.succ] v) i =
            commutatorVector x ((commutatorVector x)^[k] v) i := by
              rw [Function.iterate_succ_apply']
        _ = commutator x (((commutatorVector x)^[k] v) i) := rfl
        _ = commutator x ((commutator x)^[k] (v i)) :=
          congrArg (commutator x) (ih)
        _ = ((commutator x)^[k.succ]) (v i) := by
          rw [Function.iterate_succ_apply']

/-/ The left action needed to close a right submodule under `adₓ`. -/
theorem commutatorVector_mem
    (H : Submodule Sᵐᵒᵖ (Fin n → S)) (x : S)
    (hleft : ∀ v : Fin n → S, v ∈ H → (fun i => x * v i) ∈ H)
    {v : Fin n → S} (hv : v ∈ H) :
    commutatorVector x v ∈ H := by
  have hright : rightMulVector v x ∈ H := by
    simpa only [op_smul_vector] using
      H.smul_mem (MulOpposite.op x) hv
  have hleft' : (fun i => x * v i) ∈ H := hleft v hv
  change (fun i => v i * x - x * v i) ∈ H
  change rightMulVector v x - (fun i => x * v i) ∈ H
  exact H.sub_mem hright hleft'

/-!
The key right-sided module consequence.  A unit coordinate can be inverted
on the right, so a pure vector `single i u` gives every `single i a`.
-/

theorem single_mem_of_unit_single_mem
    (H : Submodule Sᵐᵒᵖ (Fin n → S))
    (i : Fin n) {u : S} (hu : IsUnit u)
    (hmem : (Pi.single i u : Fin n → S) ∈ H) (a : S) :
    (Pi.single i a : Fin n → S) ∈ H := by
  let w : S := (hu.unit⁻¹ : Sˣ) * a
  have hsmul := H.smul_mem (MulOpposite.op w) hmem
  have hunit : u * (hu.unit⁻¹ : Sˣ) = 1 := hu.mul_val_inv
  have hcoord : u * w = a := by
    dsimp [w]
    rw [← mul_assoc, hunit, one_mul]
  have heq : (MulOpposite.op w : Sᵐᵒᵖ) •
      (Pi.single i u : Fin n → S) = Pi.single i a := by
    funext j
    by_cases hji : i = j
    · subst j
      change (Pi.single i u : Fin n → S) i * w =
        (Pi.single i a : Fin n → S) i
      simpa only [Pi.single_eq_same] using hcoord
    · have hji' : j ≠ i := Ne.symm hji
      simp [ hji']
  rw [← heq]
  exact hsmul

/--
If a right `S`-submodule contains a pure unit vector in every coordinate,
then it is the whole free right module.  The proof uses the finite standard
basis decomposition and never reverses the right-sided scalar order.
-/
theorem top_of_unit_singletons
    (H : Submodule Sᵐᵒᵖ (Fin n → S))
    (hunit : ∀ i : Fin n, ∃ u : S, IsUnit u ∧
      (Pi.single i u : Fin n → S) ∈ H) :
    H = ⊤ := by
  apply top_unique
  intro v hv
  have hsingle : ∀ i : Fin n,
      (Pi.single i (v i) : Fin n → S) ∈ H := by
    intro i
    obtain ⟨u, hu, hmem⟩ := hunit i
    exact single_mem_of_unit_single_mem H i hu hmem (v i)
  have hdecomp : (∑ i : Fin n, Pi.single i (v i)) = v := by
    funext j
    simp
  rw [← hdecomp]
  exact H.sum_mem (fun i _ => hsingle i)


end
end AlgebraicAnalysis.EscapeSpan
