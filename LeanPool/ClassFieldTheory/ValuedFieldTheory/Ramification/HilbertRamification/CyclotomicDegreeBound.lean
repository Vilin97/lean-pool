/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring
/-!
# Cyclotomic degree bounds for inertia

An inertia group is bounded by the degree of its Galois extension.  An
embedding into a concrete cyclotomic field therefore bounds its cardinality
by Euler's totient.
-/

noncomputable section

namespace HilbertRamification

open Polynomial

/-- The inertia group of a finite Galois extension has cardinality at most
the degree of the extension. -/
theorem natCard_inertiaGroup_le_finrank
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (A : _root_.ValuationSubring E) :
    Nat.card
        (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K A) ≤
      Module.finrank K E := by
  let f :
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K A →
        (E ≃ₐ[K] E) :=
    fun σ ↦
      ((σ :
        RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K A) :
        E ≃ₐ[K] E)
  have hf : Function.Injective f := by
    intro σ τ hστ
    apply Subtype.ext
    apply Subtype.ext
    exact hστ
  calc
    Nat.card
        (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K A) ≤
        Nat.card (E ≃ₐ[K] E) :=
      Nat.card_le_card_of_injective f hf
    _ = Module.finrank K E := IsGalois.card_aut_eq_finrank K E

/-- Over a characteristic-zero field, the concrete cyclotomic field of
order `m` has degree at most `φ(m)`. -/
theorem cyclotomicField_finrank_le_totient
    (K : Type*) [Field K] [CharZero K] (m : ℕ) (hm : 0 < m) :
    Module.finrank K (CyclotomicField m K) ≤ Nat.totient m := by
  let : NeZero m := ⟨hm.ne'⟩
  let C := CyclotomicField m K
  let : IsCyclotomicExtension {m} K C :=
    CyclotomicField.isCyclotomicExtension m K
  let : FiniteDimensional K C :=
    IsCyclotomicExtension.finiteDimensional {m} K C
  obtain ⟨ζ, hζ⟩ :=
    (CyclotomicField.isCyclotomicExtension m K).exists_isPrimitiveRoot
      (Set.mem_singleton m) hm.ne'
  have hgen : Algebra.adjoin K ({ζ} : Set C) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have htop : IntermediateField.adjoin K ({ζ} : Set C) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra K ({ζ} : Set C) hgen
  have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic m K) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic, ← Polynomial.IsRoot.def]
    exact hζ.isRoot_cyclotomic hm
  have hdegree :
      (minpoly K ζ).natDegree ≤ (Polynomial.cyclotomic m K).natDegree :=
    Polynomial.natDegree_le_natDegree
      (minpoly.min K ζ (Polynomial.cyclotomic.monic m K) hroot)
  calc
    Module.finrank K (CyclotomicField m K) = Module.finrank K C := rfl
    _ = Module.finrank K (IntermediateField.adjoin K ({ζ} : Set C)) := by
      rw [htop]
      simp
    _ = (minpoly K ζ).natDegree :=
      IntermediateField.adjoin.finrank (IsIntegral.of_finite K ζ)
    _ ≤ (Polynomial.cyclotomic m K).natDegree := hdegree
    _ = Nat.totient m := Polynomial.natDegree_cyclotomic m K

/-- A concrete cyclotomic embedding bounds the inertia cardinality by the
totient of its defining order. -/
theorem natCard_inertiaGroup_le_totient_of_cyclotomicEmbedding
    {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (A : _root_.ValuationSubring E) {m : ℕ} (hm : 0 < m)
    (i : E →ₐ[K] CyclotomicField m K) :
    Nat.card
        (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K A) ≤
      Nat.totient m := by
  let : NeZero m := ⟨hm.ne'⟩
  let : FiniteDimensional K (CyclotomicField m K) :=
    IsCyclotomicExtension.finiteDimensional {m} K (CyclotomicField m K)
  exact (natCard_inertiaGroup_le_finrank A).trans
    ((i.toLinearMap.finrank_le_finrank_of_injective i.injective).trans
      (cyclotomicField_finrank_le_totient K m hm))

end HilbertRamification
