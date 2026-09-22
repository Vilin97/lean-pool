/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBinaryAdd
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd

/-!
# Correctness of the composed polynomial-time binary adder

The bounded Cobham loop in `MachineBinaryAdd` is proved here to implement the
same ripple-carry recurrence as Complexitylib's canonical binary adder.  This
connects the concrete `FP` construction to arithmetic addition.
-/

namespace BeyondBethe

open Complexity

private theorem machineBinaryAddIterate_max
    (x y accRev : List Bool) (carry : Bool) :
    machineBinaryAddStep^[max x.length y.length + 1]
        (machineBinaryAddPack x y [carry] accRev) =
      machineBinaryAddPack [] [] [false]
        ((BinaryRippleAdd.ripple carry x y).reverse ++ accRev) := by
  induction hmeasure : x.length + y.length using Nat.strongRecOn
      generalizing x y carry accRev with
  | ind measure ih =>
      cases x with
      | nil =>
          cases y with
          | nil =>
              cases carry <;>
                simp [machineBinaryAddStep_pack, BinaryRippleAdd.ripple,
                  Function.iterate_succ_apply]
          | cons y ys =>
              simp only [List.length_nil, List.length_cons, Nat.zero_add]
                at hmeasure
              have hrec := ih ys.length (by omega) [] ys
                (BinaryRippleAdd.sumBit carry false y :: accRev)
                (BinaryRippleAdd.carryBit carry false y) (by simp)
              have hrec' := hrec
              simp only [List.length_nil] at hrec'
              simp only [List.length_nil, List.length_cons]
              rw [show max 0 (ys.length + 1) + 1 =
                  (max 0 ys.length + 1).succ by omega,
                Function.iterate_succ_apply, machineBinaryAddStep_pack]
              simp only [List.nil_eq, List.cons_ne_nil, and_false,
                ↓reduceIte, List.tail_cons, List.tail_nil, List.head?_nil,
                Option.getD_none, List.head?_cons, Option.getD_some]
              simp only [true_and, false_and, ↓reduceIte]
              rw [show
                  ((false && y) || (false && carry) || (y && carry)) =
                    BinaryRippleAdd.carryBit carry false y by
                    cases carry <;> cases y <;> rfl,
                show xor (xor false y) carry =
                    BinaryRippleAdd.sumBit carry false y by
                    cases carry <;> cases y <;> rfl,
                hrec']
              simp [BinaryRippleAdd.ripple, List.reverse_cons,
                List.append_assoc]
      | cons x xs =>
          cases y with
          | nil =>
              simp only [List.length_nil, List.length_cons, Nat.add_zero]
                at hmeasure
              have hrec := ih xs.length (by omega) xs []
                (BinaryRippleAdd.sumBit carry x false :: accRev)
                (BinaryRippleAdd.carryBit carry x false) (by simp)
              have hrec' := hrec
              simp only [List.length_nil] at hrec'
              simp only [List.length_nil, List.length_cons]
              rw [show max (xs.length + 1) 0 + 1 =
                  (max xs.length 0 + 1).succ by omega,
                Function.iterate_succ_apply, machineBinaryAddStep_pack]
              simp only [List.cons_ne_nil, List.nil_eq, and_false,
                ↓reduceIte, List.tail_cons, List.tail_nil, List.head?_cons,
                Option.getD_some, List.head?_nil, Option.getD_none]
              simp only [false_and, ↓reduceIte]
              rw [show
                  ((x && false) || (x && carry) || (false && carry)) =
                    BinaryRippleAdd.carryBit carry x false by
                    cases carry <;> cases x <;> rfl,
                show xor (xor x false) carry =
                    BinaryRippleAdd.sumBit carry x false by
                    cases carry <;> cases x <;> rfl,
                hrec']
              simp [BinaryRippleAdd.ripple, List.reverse_cons,
                List.append_assoc]
          | cons y ys =>
              simp only [List.length_cons] at hmeasure
              have hrec := ih (xs.length + ys.length) (by omega)
                xs ys
                (BinaryRippleAdd.sumBit carry x y :: accRev)
                (BinaryRippleAdd.carryBit carry x y) rfl
              simp only [List.length_cons]
              rw [show max (xs.length + 1) (ys.length + 1) + 1 =
                  (max xs.length ys.length + 1).succ by omega,
                Function.iterate_succ_apply, machineBinaryAddStep_pack]
              simp only [List.cons_ne_nil, and_false, ↓reduceIte,
                List.tail_cons, List.head?_cons, Option.getD_some]
              simp only [false_and, ↓reduceIte]
              rw [show
                  ((x && y) || (x && carry) || (y && carry)) =
                    BinaryRippleAdd.carryBit carry x y by
                    cases carry <;> cases x <;> cases y <;> rfl,
                show xor (xor x y) carry =
                    BinaryRippleAdd.sumBit carry x y by
                    cases carry <;> cases x <;> cases y <;> rfl,
                hrec]
              simp [BinaryRippleAdd.ripple, List.reverse_cons,
                List.append_assoc]

private theorem machineBinaryAddStep_done (accRev : List Bool) :
    machineBinaryAddStep (machineBinaryAddPack [] [] [false] accRev) =
      machineBinaryAddPack [] [] [false] accRev := by
  rw [machineBinaryAddStep_pack]
  simp

private theorem machineBinaryAddIterate_done (accRev : List Bool) (k : ℕ) :
    machineBinaryAddStep^[k]
        (machineBinaryAddPack [] [] [false] accRev) =
      machineBinaryAddPack [] [] [false] accRev := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, machineBinaryAddStep_done, ih]

/-- The composed adder agrees with ripple carry on arbitrary operand words.
This stronger total-input statement is what later arithmetic machines use for
their size bounds; canonicality is needed only when interpreting the answer as
`Nat.bits`. -/
theorem machineBinaryAddBits_pair_lists (x y : List Bool) :
    machineBinaryAddBits (pair x y) =
      BinaryRippleAdd.ripple false x y := by
  simp only [machineBinaryAddBits, machineBinaryAddFinalState,
    machineBinaryAddRuler, machineBinaryAddInit, machinePairFirst_pair,
    machinePairSecond_pair, List.length_append, List.length_cons,
    List.length_nil]
  rw [show x.length + y.length + 1 =
      min x.length y.length + (max x.length y.length + 1) by
        have hminmax := min_add_max x.length y.length
        omega,
    Function.iterate_add_apply, machineBinaryAddIterate_max,
    machineBinaryAddIterate_done]
  simp [machineBinaryAddAccRev, machineBinaryAddPack]

/-- Ripple carry emits at most one bit beyond the longer input word. -/
theorem binaryRippleAdd_length_le : ∀ (carry : Bool) (x y : List Bool),
    (BinaryRippleAdd.ripple carry x y).length ≤
      max x.length y.length + 1 := by
  intro carry x y
  induction x generalizing carry y with
  | nil =>
      induction y generalizing carry with
      | nil => cases carry <;> simp [BinaryRippleAdd.ripple]
      | cons bit rest ih =>
          simp only [BinaryRippleAdd.ripple, List.length_cons,
            List.length_nil]
          have hrec := ih (BinaryRippleAdd.carryBit carry false bit)
          have hrec' :
              (BinaryRippleAdd.ripple
                (BinaryRippleAdd.carryBit carry false bit) [] rest).length ≤
                rest.length + 1 := by
            simpa using! hrec
          omega
  | cons bit rest ih =>
      cases y with
      | nil =>
          simp only [BinaryRippleAdd.ripple, List.length_cons,
            List.length_nil]
          have hrec := ih (BinaryRippleAdd.carryBit carry bit false) []
          have hrec' :
              (BinaryRippleAdd.ripple
                (BinaryRippleAdd.carryBit carry bit false) rest []).length ≤
                rest.length + 1 := by
            simpa using! hrec
          omega
      | cons other tail =>
          simp only [BinaryRippleAdd.ripple, List.length_cons]
          have hrec := ih (BinaryRippleAdd.carryBit carry bit other) tail
          omega

theorem machineBinaryAddBits_pair_length_le (x y : List Bool) :
    (machineBinaryAddBits (pair x y)).length ≤
      max x.length y.length + 1 := by
  rw [machineBinaryAddBits_pair_lists]
  exact binaryRippleAdd_length_le false x y

/-- The composed bounded-loop machine returns the canonical binary expansion
of the sum of canonically encoded natural-number inputs. -/
theorem machineBinaryAddBits_pair_natBits (x y : ℕ) :
    machineBinaryAddBits (pair x.bits y.bits) = (x + y).bits := by
  simp only [machineBinaryAddBits, machineBinaryAddFinalState,
    machineBinaryAddRuler, machineBinaryAddInit, machinePairFirst_pair,
    machinePairSecond_pair, List.length_append, List.length_cons,
    List.length_nil]
  rw [show x.bits.length + y.bits.length + 1 =
      min x.bits.length y.bits.length +
        (max x.bits.length y.bits.length + 1) by
        have hminmax := min_add_max x.bits.length y.bits.length
        omega,
    Function.iterate_add_apply, machineBinaryAddIterate_max,
    machineBinaryAddIterate_done]
  simp [machineBinaryAddAccRev, machineBinaryAddPack,
    BinaryRippleAdd.ripple_natBits]

end BeyondBethe
