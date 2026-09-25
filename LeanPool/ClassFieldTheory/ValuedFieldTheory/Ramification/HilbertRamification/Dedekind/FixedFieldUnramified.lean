/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.NumberFieldPrimes
/-!
# Global cyclotomic inertia argument: the inertia-generated fixed field is unramified

This file records the ramification-theoretic step in the proof of the global
Kronecker--Weber theorem.  If a subgroup of a finite Galois group contains
the inertia group at every prime of the top field, then its fixed field is
unramified at every finite prime.
-/

@[expose] public section

noncomputable section

namespace HilbertRamification.Dedekind

open NumberField
open scoped NumberField

attribute [local instance] Ideal.Quotient.field

variable {G M : Type*}
variable [Group G]
variable [Field M] [NumberField M]
variable [MulSemiringAction G M]
variable [IsGaloisGroup G ℚ M]

/-- Fixed-field unramifiedness from the global cyclotomic inertia argument.

If `H` contains every inertia group of `M / ℚ`, then every finite prime of
the fixed field `Mᴴ` is unramified over `ℤ`.  For a prime `P` of the fixed
field, choose a prime `Q` of `M` above it.  The inertia group of `Q` for
`M / Mᴴ` has the same cardinality as the inertia group for `M / ℚ`, because
the latter is contained in `H`.  prime-decomposition theory identifies these cardinalities
with the two upper ramification indices.  Multiplicativity of ramification
indices in the tower then forces the lower ramification index to be one. -/
theorem fixedFieldOfSubgroup_forall_isUnramifiedAt_of_inertiaGroup_le
    (H : Subgroup G)
    (hI : ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.IsMaximal],
      inertiaGroup Q G ≤ H) :
    ∀ (P : Ideal
        (𝓞 (fixedFieldOfSubgroup (K := ℚ) (L := M) G H)))
      [P.IsPrime],
      Algebra.IsUnramifiedAt ℤ P := by
  intro P _
  let F : IntermediateField ℚ M :=
    fixedFieldOfSubgroup (K := ℚ) (L := M) G H
  change Algebra.IsUnramifiedAt ℤ (show Ideal (𝓞 F) from P)
  let : Finite G := IsGaloisGroup.finite G ℚ M
  let : IsGaloisGroup H F M := by
    dsimp only [F, fixedFieldOfSubgroup]
    infer_instance
  let : IsGaloisGroup H (𝓞 F) (𝓞 M) :=
    IsGaloisGroup.of_isFractionRing H (𝓞 F) (𝓞 M) F M
  by_cases hP0 : P = ⊥
  · subst P
    rw [← not_dvd_differentIdeal_iff]
    simp_rw [← Ideal.zero_eq_bot, zero_dvd_iff]
    simpa only [Submodule.zero_eq_bot] using
      (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  let : P.IsMaximal :=
    (inferInstance : P.IsPrime).isMaximal hP0
  obtain ⟨⟨Q, hQprime, hQP⟩⟩ :=
    P.nonempty_primesOver (S := 𝓞 M)
  let : Q.IsPrime := hQprime
  let : Q.LiesOver P := hQP
  have hQ0 : Q ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hP0 Q
  let : Q.IsMaximal :=
    (inferInstance : Q.IsPrime).isMaximal hQ0
  let p : Ideal ℤ := P.under ℤ
  let : p.IsPrime := inferInstance
  let : P.LiesOver p := ⟨rfl⟩
  let : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have hp0 : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := p) inferInstance Int.not_isField
  let : Module.Finite (𝓞 F) (𝓞 M) :=
    ringOfIntegers_moduleFinite (K := F) (L := M)
  let : Finite (ℤ ⧸ p) :=
    Ring.HasFiniteQuotients.finiteQuotient hp0
  let : PerfectField (ℤ ⧸ p) := PerfectField.ofFinite
  let : Algebra.IsSeparable (ℤ ⧸ p) ((𝓞 M) ⧸ Q) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  let : Finite ((𝓞 F) ⧸ P) :=
    inferInstance
  let : PerfectField ((𝓞 F) ⧸ P) := PerfectField.ofFinite
  let : Algebra.IsSeparable ((𝓞 F) ⧸ P) ((𝓞 M) ⧸ Q) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hIH :
      inertiaGroup Q H = (inertiaGroup Q G).subgroupOf H := by
    ext σ
    rfl
  have hcard :
      Nat.card (inertiaGroup Q H) = Nat.card (inertiaGroup Q G) := by
    rw [hIH]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (hI Q)).toEquiv
  have hcard_base :
      Nat.card (inertiaGroup Q G) =
        Q.ramificationIdx ℤ :=
    inertia_card_eq_ramificationIdx
      (A := ℤ) (B := 𝓞 M) p Q G hp0
  have hcard_relative :
      Nat.card (inertiaGroup Q H) =
        Q.ramificationIdx (𝓞 F) :=
    inertia_card_eq_ramificationIdx
      (A := 𝓞 F) (B := 𝓞 M) P Q H hP0
  have heq :
      Q.ramificationIdx ℤ = Q.ramificationIdx (𝓞 F) := by
    exact hcard_base.symm.trans (hcard.symm.trans hcard_relative)
  have htower :
      Q.ramificationIdx ℤ =
        P.ramificationIdx ℤ * Q.ramificationIdx (𝓞 F) :=
    Ideal.ramificationIdx_tower (R := ℤ) P Q
  have hrelative0 :
      Q.ramificationIdx (𝓞 F) ≠ 0 :=
    (Ideal.ramificationIdx_pos Q (𝓞 F)).ne'
  have hlower :
      P.ramificationIdx ℤ = 1 := by
    apply Eq.symm
    apply Nat.mul_right_cancel (Nat.pos_of_ne_zero hrelative0)
    calc
      1 * Q.ramificationIdx (𝓞 F) =
          Q.ramificationIdx (𝓞 F) := by simp
      _ = Q.ramificationIdx ℤ := heq.symm
      _ = P.ramificationIdx ℤ * Q.ramificationIdx (𝓞 F) := htower
  exact
    (Ideal.ramificationIdx_eq_one_iff
      (R := ℤ) (S := 𝓞 F) (q := P)).1 hlower

end HilbertRamification.Dedekind

end
