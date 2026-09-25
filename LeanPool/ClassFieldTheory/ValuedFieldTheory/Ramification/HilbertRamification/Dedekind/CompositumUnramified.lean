/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFields
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.NumberFieldPrimes
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.OrbitCardinality
/-!
# Unramifiedness in a compositum

This file contains reusable criteria for proving that a prime in a number
field compositum is unramified from the inertia groups of its two factors.
-/

@[expose] public section

noncomputable section

namespace HilbertRamification.Dedekind

open NumberField
open scoped NumberField

attribute [local instance] Ideal.Quotient.field

/-- If two normal intermediate fields generate a number-field extension
and the inertia of a prime restricts trivially to both, then the original
inertia group is trivial.  The base field is arbitrary; in particular this
applies to the Kummer composita used in the global existence theorem. -/
theorem inertiaGroup_eq_bot_of_restrictNormal_of_sup_eq_top
    {K M : Type*}
    [Field K]
    [Field M] [Algebra K M]
    (A B : IntermediateField K M) [Normal K A] [Normal K B]
    (Q : Ideal (𝓞 M))
    (hsup : A ⊔ B = ⊤)
    (hIA :
      inertiaGroup (Q.under (𝓞 A)) Gal(A/K) = ⊥)
    (hIB :
      inertiaGroup (Q.under (𝓞 B)) Gal(B/K) = ⊥) :
    inertiaGroup Q Gal(M/K) = ⊥ := by
  let rA : Gal(M/K) →* Gal(A/K) :=
    AlgEquiv.restrictNormalHom A
  let rB : Gal(M/K) →* Gal(B/K) :=
    AlgEquiv.restrictNormalHom B
  apply le_antisymm
  · intro σ hσ
    have hσA :
        rA σ ∈ inertiaGroup (Q.under (𝓞 A)) Gal(A/K) := by
      rw [mem_inertiaGroup_iff]
      intro x
      change algebraMap (𝓞 A) (𝓞 M) (rA σ • x - x) ∈ Q
      rw [map_sub]
      have hcompat :
          algebraMap (𝓞 A) (𝓞 M) (rA σ • x) =
            σ • algebraMap (𝓞 A) (𝓞 M) x := by
        apply RingOfIntegers.coe_injective
        change algebraMap A M (σ.restrictNormal A x.1) =
          σ (algebraMap A M x.1)
        exact AlgEquiv.restrictNormal_commutes σ A x.1
      rw [hcompat]
      exact (mem_inertiaGroup_iff.mp hσ)
        (algebraMap (𝓞 A) (𝓞 M) x)
    have hσB :
        rB σ ∈ inertiaGroup (Q.under (𝓞 B)) Gal(B/K) := by
      rw [mem_inertiaGroup_iff]
      intro x
      change algebraMap (𝓞 B) (𝓞 M) (rB σ • x - x) ∈ Q
      rw [map_sub]
      have hcompat :
          algebraMap (𝓞 B) (𝓞 M) (rB σ • x) =
            σ • algebraMap (𝓞 B) (𝓞 M) x := by
        apply RingOfIntegers.coe_injective
        change algebraMap B M (σ.restrictNormal B x.1) =
          σ (algebraMap B M x.1)
        exact AlgEquiv.restrictNormal_commutes σ B x.1
      rw [hcompat]
      exact (mem_inertiaGroup_iff.mp hσ)
        (algebraMap (𝓞 B) (𝓞 M) x)
    have hAone : rA σ = 1 := by
      rw [← Subgroup.mem_bot, ← hIA]
      exact hσA
    have hBone : rB σ = 1 := by
      rw [← Subgroup.mem_bot, ← hIB]
      exact hσB
    have hmemA : σ ∈ A.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      calc
        σ x = algebraMap A M ((rA σ) ⟨x, hx⟩) := by
          change σ x =
            algebraMap A M ((σ.restrictNormal A) ⟨x, hx⟩)
          exact (AlgEquiv.restrictNormal_commutes σ A ⟨x, hx⟩).symm
        _ = algebraMap A M ((1 : Gal(A/K)) ⟨x, hx⟩) :=
          congrArg (fun τ : Gal(A/K) ↦ algebraMap A M (τ ⟨x, hx⟩)) hAone
        _ = x := rfl
    have hmemB : σ ∈ B.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      calc
        σ x = algebraMap B M ((rB σ) ⟨x, hx⟩) := by
          change σ x =
            algebraMap B M ((σ.restrictNormal B) ⟨x, hx⟩)
          exact (AlgEquiv.restrictNormal_commutes σ B ⟨x, hx⟩).symm
        _ = algebraMap B M ((1 : Gal(B/K)) ⟨x, hx⟩) :=
          congrArg (fun τ : Gal(B/K) ↦ algebraMap B M (τ ⟨x, hx⟩)) hBone
        _ = x := rfl
    have hmem : σ ∈ (A ⊔ B).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hmemA, hmemB⟩
    simpa [hsup] using hmem
  · exact bot_le

/-- If a finite family of normal simple intermediate fields generates a
finite Galois number-field extension and the inertia at a prime restricts
trivially to every member of the family, then the inertia of the full
extension is trivial.  This is the finite-radical form of the compositum
argument used for the full `S`-unit Kummer extension. -/
theorem inertiaGroup_eq_bot_of_finset_adjoin_eq_top
    {K M : Type*}
    [Field K]
    [Field M] [NumberField M] [Algebra K M]
    (T : Finset M)
    (Q : Ideal (𝓞 M))
    (hnormal :
      ∀ x : M, x ∈ T →
        Normal K (IntermediateField.adjoin K {x}))
    (hI :
      ∀ (x : M) (_ : x ∈ T),
        inertiaGroup
            (Q.under
              (𝓞 (IntermediateField.adjoin K {x})))
            Gal((IntermediateField.adjoin K {x})/K) =
          ⊥)
    (hadjoin :
      IntermediateField.adjoin K (T : Set M) = ⊤) :
    inertiaGroup Q Gal(M/K) = ⊥ := by
  apply le_antisymm
  · intro sigma hsigma
    have hfix :
        ∀ x : M, x ∈ T → sigma x = x := by
      intro x hx
      let B : IntermediateField K M :=
        IntermediateField.adjoin K {x}
      let : Normal K B := hnormal x hx
      let rB : Gal(M/K) →* Gal(B/K) :=
        AlgEquiv.restrictNormalHom B
      have hsigmaB :
          rB sigma ∈
            inertiaGroup (Q.under (𝓞 B)) Gal(B/K) := by
        rw [mem_inertiaGroup_iff]
        intro y
        change
          algebraMap (𝓞 B) (𝓞 M)
              (rB sigma • y - y) ∈ Q
        rw [map_sub]
        have hcompat :
            algebraMap (𝓞 B) (𝓞 M) (rB sigma • y) =
              sigma • algebraMap (𝓞 B) (𝓞 M) y := by
          apply RingOfIntegers.coe_injective
          change
            algebraMap B M
                (sigma.restrictNormal B y.1) =
              sigma (algebraMap B M y.1)
          exact
            AlgEquiv.restrictNormal_commutes sigma B y.1
        rw [hcompat]
        exact
          (mem_inertiaGroup_iff.mp hsigma)
            (algebraMap (𝓞 B) (𝓞 M) y)
      have hsigmaBone : rB sigma = 1 := by
        rw [← Subgroup.mem_bot, ← hI x hx]
        exact hsigmaB
      have hxB : x ∈ B :=
        IntermediateField.subset_adjoin K {x}
          (Set.mem_singleton x)
      calc
        sigma x =
            algebraMap B M
              ((rB sigma) ⟨x, hxB⟩) := by
          change
            sigma x =
              algebraMap B M
                (sigma.restrictNormal B ⟨x, hxB⟩)
          exact
            (AlgEquiv.restrictNormal_commutes
              sigma B ⟨x, hxB⟩).symm
        _ =
            algebraMap B M
              ((1 : Gal(B/K)) ⟨x, hxB⟩) :=
          congrArg
            (fun tau : Gal(B/K) =>
              algebraMap B M (tau ⟨x, hxB⟩))
            hsigmaBone
        _ = x := rfl
    have hmem :
        sigma ∈
          (IntermediateField.adjoin K
            (T : Set M)).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem x hx =>
          exact hfix x hx
      | algebraMap a =>
          exact sigma.commutes a
      | add x y hx hy ihx ihy =>
          rw [map_add, ihx, ihy]
      | inv x hx ihx =>
          rw [map_inv₀, ihx]
      | mul x y hx hy ihx ihy =>
          rw [map_mul, ihx, ihy]
    simpa [hadjoin] using hmem
  · exact bot_le

/-- For a finite Galois extension of number fields, ramification index
one at a prime forces the corresponding inertia group to be trivial.
The residue extension is separable because the residue field of a number
field is finite. -/
theorem inertiaGroup_eq_bot_of_ramificationIdx_eq_one
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (p : Ideal (𝓞 K)) (P : Ideal (𝓞 M))
    [p.IsPrime] [P.IsPrime] [P.IsMaximal] [P.LiesOver p]
    (hp0 : p ≠ ⊥)
    (he : P.ramificationIdx (𝓞 K) = 1) :
    inertiaGroup P Gal(M/K) = ⊥ := by
  let : p.IsMaximal :=
    (inferInstance : p.IsPrime).isMaximal hp0
  let : Finite ((𝓞 K) ⧸ p) :=
    Ideal.finiteQuotientOfFreeOfNeBot p hp0
  let : PerfectField ((𝓞 K) ⧸ p) :=
    PerfectField.ofFinite
  let : Algebra.IsSeparable
      ((𝓞 K) ⧸ p) ((𝓞 M) ⧸ P) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [← Subgroup.card_eq_one,
    inertia_card_eq_ramificationIdx
      (A := 𝓞 K) (B := 𝓞 M) p P Gal(M/K) hp0]
  exact he

/-- Algebraic unramifiedness at a prime of a finite Galois number-field
extension forces the corresponding inertia group to be trivial. -/
theorem inertiaGroup_eq_bot_of_isUnramifiedAt
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.IsMaximal]
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) P) :
    inertiaGroup P Gal(M/K) = ⊥ := by
  let p : Ideal (𝓞 K) := P.under (𝓞 K)
  let : p.IsPrime := inferInstance
  let : P.LiesOver p := ⟨rfl⟩
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := P) inferInstance (RingOfIntegers.not_isField M)
  have hp0 : p ≠ ⊥ :=
    Ideal.under_ne_bot (𝓞 K) hP0
  let : Algebra.IsUnramifiedAt (𝓞 K) P := hunram
  apply inertiaGroup_eq_bot_of_ramificationIdx_eq_one
    (K := K) (M := M) p P hp0
  exact Ideal.ramificationIdx_eq_one P (𝓞 K)

/-- Trivial inertia at a prime of a finite Galois number-field
extension gives algebraic unramifiedness at that prime. -/
theorem isUnramifiedAt_of_inertiaGroup_eq_bot
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.IsMaximal]
    (hI : inertiaGroup P Gal(M/K) = ⊥) :
    Algebra.IsUnramifiedAt (𝓞 K) P := by
  let p : Ideal (𝓞 K) := P.under (𝓞 K)
  let : p.IsPrime := inferInstance
  let : P.LiesOver p := ⟨rfl⟩
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := P) inferInstance (RingOfIntegers.not_isField M)
  have hp0 : p ≠ ⊥ :=
    Ideal.under_ne_bot (𝓞 K) hP0
  let : p.IsMaximal :=
    (inferInstance : p.IsPrime).isMaximal hp0
  let : Finite ((𝓞 K) ⧸ p) :=
    Ideal.finiteQuotientOfFreeOfNeBot p hp0
  let : PerfectField ((𝓞 K) ⧸ p) :=
    PerfectField.ofFinite
  let : Algebra.IsSeparable
      ((𝓞 K) ⧸ p) ((𝓞 M) ⧸ P) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have he :
      P.ramificationIdx (𝓞 K) = 1 := by
    rw [← inertia_card_eq_ramificationIdx
      (A := 𝓞 K) (B := 𝓞 M)
      p P Gal(M/K) hp0, hI]
    simp
  exact Ideal.ramificationIdx_eq_one_iff.mp he

/-- In the rational-base case, ramification index one forces the
corresponding inertia group to be trivial. -/
theorem inertiaGroup_eq_bot_of_ramificationIdx_eq_one_int
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (p : Ideal ℤ) (P : Ideal (𝓞 K))
    [p.IsPrime] [P.IsPrime] [P.IsMaximal] [P.LiesOver p]
    (hp0 : p ≠ ⊥)
    (he : P.ramificationIdx ℤ = 1) :
    inertiaGroup P Gal(K/ℚ) = ⊥ := by
  let : p.IsMaximal :=
    (inferInstance : p.IsPrime).isMaximal hp0
  let : Finite (ℤ ⧸ p) :=
    Ideal.finiteQuotientOfFreeOfNeBot p hp0
  let : PerfectField (ℤ ⧸ p) := PerfectField.ofFinite
  let : Algebra.IsSeparable (ℤ ⧸ p) ((𝓞 K) ⧸ P) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [← Subgroup.card_eq_one,
    inertia_card_eq_ramificationIdx
      (A := ℤ) (B := 𝓞 K) p P Gal(K/ℚ) hp0]
  exact he

/-- Trivial rational inertia gives unramifiedness at the chosen finite
prime. -/
theorem isUnramifiedAt_int_of_inertiaGroup_eq_bot
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.IsMaximal]
    (hI : inertiaGroup P Gal(K/ℚ) = ⊥) :
    Algebra.IsUnramifiedAt ℤ P := by
  let p : Ideal ℤ := P.under ℤ
  let : p.IsPrime := inferInstance
  let : P.LiesOver p := ⟨rfl⟩
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := P) inferInstance (RingOfIntegers.not_isField K)
  have hp0 : p ≠ ⊥ := Ideal.under_ne_bot ℤ hP0
  let : p.IsMaximal :=
    (inferInstance : p.IsPrime).isMaximal hp0
  let : Finite (ℤ ⧸ p) :=
    Ideal.finiteQuotientOfFreeOfNeBot p hp0
  let : PerfectField (ℤ ⧸ p) := PerfectField.ofFinite
  let : Algebra.IsSeparable (ℤ ⧸ p) ((𝓞 K) ⧸ P) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have he :
      P.ramificationIdx ℤ = 1 := by
    rw [← inertia_card_eq_ramificationIdx
      (A := ℤ) (B := 𝓞 K) p P Gal(K/ℚ) hp0, hI]
    simp
  exact Ideal.ramificationIdx_eq_one_iff.mp he

end HilbertRamification.Dedekind
