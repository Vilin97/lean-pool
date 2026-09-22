/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Order.Iterate
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.CharacterMap

/-! # Finite Order Valuation -/
namespace RamificationTheory.HilbertRamification.ValuationSubring

noncomputable section

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- A finite-order element of the valuation-subring decomposition group fixes
all values. The induced map on the canonical value group is monotone, and a
positive iterate equal to the identity forces a monotone map to be the identity. -/
theorem valuation_decomposition_apply_eq_of_isOfFinOrder
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A)
    (hσ : IsOfFinOrder σ) (x : L) :
    A.valuation ((σ : L ≃ₐ[K] L) x) = A.valuation x := by
  have hle {a b : L} (hab : A.valuation a ≤ A.valuation b) :
      A.valuation ((σ : L ≃ₐ[K] L) a) ≤
        A.valuation ((σ : L ≃ₐ[K] L) b) := by
    obtain ⟨c, hc⟩ := (A.valuation_le_iff a b).1 hab
    apply (A.valuation_le_iff _ _).2
    refine ⟨σ • c, ?_⟩
    change (σ : L ≃ₐ[K] L) (c : L) * (σ : L ≃ₐ[K] L) b =
      (σ : L ≃ₐ[K] L) a
    rw [← map_mul, hc]
  let f : A.ValueGroup → A.ValueGroup := fun γ =>
    A.valuation ((σ : L ≃ₐ[K] L)
      (Function.surjInv A.valuation_surjective γ))
  have hfv (a : L) :
      f (A.valuation a) = A.valuation ((σ : L ≃ₐ[K] L) a) := by
    dsimp only [f]
    apply le_antisymm
    · apply hle
      exact le_of_eq (Function.surjInv_eq A.valuation_surjective _)
    · apply hle
      exact le_of_eq (Function.surjInv_eq A.valuation_surjective _).symm
  have hf : Monotone f := by
    intro a b hab
    apply hle
    simpa only [Function.surjInv_eq] using hab
  have hiter (n : ℕ) (a : L) :
      f^[n] (A.valuation a) = A.valuation (((σ : L ≃ₐ[K] L) ^ n) a) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, hfv, pow_succ', AlgEquiv.mul_apply]
  obtain ⟨n, hn, hσn⟩ := hσ.exists_pow_eq_one
  have hσn' : (σ : L ≃ₐ[K] L) ^ n = 1 :=
    congrArg (fun τ : decompositionGroup K A => (τ : L ≃ₐ[K] L)) hσn
  have hperiod : f^[n] (A.valuation x) = A.valuation x := by
    rw [hiter, hσn', AlgEquiv.one_apply]
  have hcomm : Function.Commute f id := fun _ => rfl
  have hfixed : f (A.valuation x) = A.valuation x :=
    (hcomm.iterate_pos_eq_iff_map_eq hf strictMono_id hn).1 (by
      simpa only [Function.iterate_id, id_eq] using hperiod)
  rwa [hfv] at hfixed

/-- Each finite-order inertia element lies in the actual value-trivial subgroup. -/
theorem mem_valueTrivialInertiaGroup_of_isOfFinOrder
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A)
    (hσ : IsOfFinOrder σ) : σ ∈ valueTrivialInertiaGroup K A := by
  change ∀ x : Lˣ,
    valueDisplacementClass K A (σ : decompositionGroup K A) x = 1
  intro x
  rw [valueDisplacementClass_eq_one_iff, A.mem_unitGroup_iff]
  simp only [automorphismUnitQuotient, Units.val_div_eq_div_val]
  change A.valuation
    ((((σ : decompositionGroup K A) : L ≃ₐ[K] L) (x : L)) / (x : L)) = 1
  rw [map_div₀, valuation_decomposition_apply_eq_of_isOfFinOrder K A
    (σ : decompositionGroup K A)
    ((inertiaGroup K A).subtype.isOfFinOrder hσ)]
  exact div_self (A.valuation.ne_zero_iff.mpr x.ne_zero)

/-- Finite inertia acts trivially on the actual value group, without any
finiteness assumption on the full group of field automorphisms. -/
theorem valueTrivialInertiaGroup_eq_top_of_finite
    (A : _root_.ValuationSubring L) [Finite (inertiaGroup K A)] :
    valueTrivialInertiaGroup K A = ⊤ := by
  apply top_unique
  intro σ _
  exact mem_valueTrivialInertiaGroup_of_isOfFinOrder K A σ (isOfFinOrder_of_finite σ)

end

end RamificationTheory.HilbertRamification.ValuationSubring
