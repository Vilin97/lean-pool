/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.Core
/-!
# Compact surjectivity criterion for the principal-unit inverse limit

This is the compactness step in the local-field structure theory, the equal-characteristic
  field-unit structure theorem.
For a map from a compact space to the inverse limit
`lim U^1 / U^(n+1)`, surjectivity on every finite coordinate implies
surjectivity on the inverse limit.  Indeed, the fibers over the coordinates
of a fixed target form a decreasing sequence of nonempty compact closed sets.
-/

@[expose] public section

noncomputable
section

universe u v w

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

open Internal

variable {K : Type u} [Field K]

/-- A continuous map from a compact space to the principal-unit inverse limit
is surjective as soon as all of its finite-coordinate maps are surjective.

The finite quotients carry the discrete topology.  Compatibility makes the
fiber over coordinate `n + 1` a subset of the fiber over coordinate `n`, so
Cantor's intersection theorem supplies a simultaneous preimage of all
coordinates. -/
theorem Internal.surjective_principalUnitInverseLimitCarrier_of_surjective_coordinates
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {A : Type w} [TopologicalSpace A] [CompactSpace A]
    (g : A → Internal.principalUnitInverseLimitCarrier F) :
    letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
      fun _ => ⊥
    Continuous g →
      (∀ n, Function.Surjective (fun a : A => (g a).1 n)) →
        Function.Surjective g := by
  let : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  let : (n : ℕ) → DiscreteTopology (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⟨rfl⟩
  intro hg hsur y
  let C : ℕ → Set A := fun n => {a | (g a).1 n = y.1 n}
  have hcoord : ∀ n, Continuous (fun a : A => (g a).1 n) := by
    intro n
    exact ((continuous_apply n).comp continuous_subtype_val).comp hg
  have hclosed : ∀ n, IsClosed (C n) := by
    intro n
    exact isClosed_eq (hcoord n) continuous_const
  have hnonempty : ∀ n, (C n).Nonempty := by
    intro n
    obtain ⟨a, ha⟩ := hsur n (y.1 n)
    exact ⟨a, ha⟩
  have hdecreasing : ∀ n, C (n + 1) ⊆ C n := by
    intro n a ha
    change (g a).1 n = y.1 n
    calc
      (g a).1 n =
          principalUnitQuotientCarrierTransition F (Nat.le_succ n)
            ((g a).1 (n + 1)) := ((g a).2 (Nat.le_succ n)).symm
      _ = principalUnitQuotientCarrierTransition F (Nat.le_succ n)
            (y.1 (n + 1)) := congrArg
              (principalUnitQuotientCarrierTransition F (Nat.le_succ n)) ha
      _ = y.1 n := y.2 (Nat.le_succ n)
  have hintersection : (⋂ n, C n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      C hdecreasing hnonempty (hclosed 0).isCompact hclosed
  obtain ⟨a, ha⟩ := hintersection
  refine ⟨a, ?_⟩
  apply Subtype.ext
  funext n
  exact Set.mem_iInter.mp ha n

/-- Additive-tag version of
`surjective_principalUnitInverseLimitCarrier_of_surjective_coordinates`, in
the form used by
  Iwasawa's additive homomorphism in the equal-characteristic field-unit structure theorem. -/
theorem Internal.surjective_additive_principalUnitInverseLimitCarrier_of_surjective_coordinates
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {A : Type w} [TopologicalSpace A] [CompactSpace A]
    (g : A → Additive (Internal.principalUnitInverseLimitCarrier F)) :
    letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
      fun _ => ⊥
    Continuous g →
      (∀ n, Function.Surjective (fun a : A =>
        Additive.ofMul ((Additive.toMul (g a)).1 n))) →
        Function.Surjective g := by
  let : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  intro hg hsur
  let gm : A → Internal.principalUnitInverseLimitCarrier F := fun a =>
    Additive.toMul (g a)
  have hgm : Continuous gm := hg
  have hsurm : ∀ n, Function.Surjective (fun a : A => (gm a).1 n) := by
    intro n y
    obtain ⟨a, ha⟩ := hsur n (Additive.ofMul y)
    exact ⟨a, Additive.ofMul.injective ha⟩
  have hgmSur : Function.Surjective gm :=
    Internal.surjective_principalUnitInverseLimitCarrier_of_surjective_coordinates
      F gm hgm hsurm
  intro y
  obtain ⟨a, ha⟩ := hgmSur (Additive.toMul y)
  exact ⟨a, Additive.toMul.injective ha⟩

/-- Type-safe compact surjectivity criterion for the prodiscrete
principal-unit limit.  Both the inverse-limit topology and the discrete
coordinate topologies are part of the codomain types. -/
theorem Internal.surjective_principalUnitProdiscreteLimit_of_surjective_coordinates
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {A : Type w} [TopologicalSpace A] [CompactSpace A]
    (g : A → PrincipalUnitProdiscreteLimit F)
    (hg : Continuous g)
    (hsur : ∀ n, Function.Surjective fun a : A =>
      PrincipalUnitProdiscreteLimit.coordinate F n (g a)) :
    Function.Surjective g := by
  let : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  let e := Internal.principalUnitProdiscreteLimitHomeomorphUnderlying F
  let gCarrier : A → Additive (Internal.principalUnitInverseLimitCarrier F) := fun a =>
    e (g a)
  have hgCarrier : Continuous gCarrier := e.continuous.comp hg
  have hsurCarrier : ∀ n, Function.Surjective fun a : A =>
      Additive.ofMul ((Additive.toMul (gCarrier a)).1 n) := by
    intro n y
    obtain ⟨a, ha⟩ := hsur n
      (DiscretePrincipalUnitQuotient.of F n y)
    refine ⟨a, ?_⟩
    exact congrArg DiscretePrincipalUnitQuotient.val ha
  have hCarrier : Function.Surjective gCarrier :=
    Internal.surjective_additive_principalUnitInverseLimitCarrier_of_surjective_coordinates
      F gCarrier hgCarrier hsurCarrier
  intro y
  obtain ⟨a, ha⟩ := hCarrier (e y)
  exact ⟨a, e.injective ha⟩

/-- Public type-safe compact surjectivity criterion. -/
theorem surjective_principalUnitProdiscreteLimit_of_surjective_coordinates
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {A : Type w} [TopologicalSpace A] [CompactSpace A]
    (g : A → PrincipalUnitProdiscreteLimit F)
    (hg : Continuous g)
    (hsur : ∀ n, Function.Surjective fun a : A =>
      PrincipalUnitProdiscreteLimit.coordinate F n (g a)) :
    Function.Surjective g :=
  Internal.surjective_principalUnitProdiscreteLimit_of_surjective_coordinates
    F g hg hsur

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
