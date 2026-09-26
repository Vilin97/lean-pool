/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Derivative
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Leibniz
import Mathlib.Tactic.Abel

/-!
# Boundary estimates for Cantor–Bendixson degrees of truncations

The cofactor construction multiplies a pointwise-bounded cofactor by a homogeneous representative
of its assigned degree and proper-truncation bounds. The translated truncation of that product
differs from
the cofactor truncation times the full representative only below a prescribed separated degree.
-/

public noncomputable section

open Set Filter Topology
open scoped NatOrdinal

universe u v

namespace HahnSeries.Nonpositive

variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CommRing R] [NoZeroDivisors R] [CharZero R]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := R))

/-- A product of a factor of degree at most `ρ` with a factor of degree strictly below `σ` has
degree strictly below every bound `τ` separated from `ρ` by `σ`. -/
theorem degree_mul_lt_of_le_of_lt_of_separated
    (a b : Nonpositive G R) (ρ σ τ : NatOrdinal.{u})
    (ha : ν a ≤ ρ) (hb : ν b < σ)
    (hsep : ∀ θ, θ < σ → ρ + θ < τ) :
    ν (a * b) < τ := by
  have hmul := (ν).map_mul_le_add a b
  cases hdegree : ν b using WithBot.recBotCoe with
  | bot =>
      rw [hdegree, WithBot.add_bot] at hmul
      exact hmul.trans_lt (WithBot.bot_lt_coe τ)
  | coe θ =>
      have hθ : θ < σ := by simpa only [hdegree, WithBot.coe_lt_coe] using hb
      apply hmul.trans_lt
      rw [hdegree]
      calc
        ν a + (θ : WithBot NatOrdinal) ≤ (ρ : WithBot NatOrdinal) + θ :=
          by simpa only [add_comm] using add_le_add_right ha θ
        _ = ((ρ + θ : NatOrdinal) : WithBot NatOrdinal) := (WithBot.coe_add ρ θ).symm
        _ < (τ : WithBot NatOrdinal) := by
          simpa only [WithBot.coe_lt_coe] using hsep θ hθ

/-- Under the separation inequality, the nonboundary convolution terms and the truncation of the
second factor are strictly below `τ`. Hence only the first boundary term survives at degree at
least `τ`. -/
theorem degree_translatedTruncLE_mul_sub_mul_lt_of_pointwise_bounds
    (a b : Nonpositive G R) (ρ σ τ : NatOrdinal.{u})
    (ha : ν a ≤ ρ)
    (hat : ∀ x : G, x < 0 → ν (translatedTruncLE x a) ≤ ρ)
    (hbt : ∀ x : G, x < 0 → ν (translatedTruncLE x b) < σ)
    (hsep : ∀ θ, θ < σ → ρ + θ < τ)
    {γ : G} (hγ : γ < 0) :
    ν (translatedTruncLE γ (a * b) - translatedTruncLE γ a * b) < τ := by
  have hremValue := HahnSeries.cantorBendixsonValue_leibnizRemainder_lt_of_forall
    (a : HahnSeries G R) (b : HahnSeries G R) a.property b.property hγ
    (ρ := (ω^ τ).val) (NatOrdinal.wpow_pos τ) (fun x y _ hx _ hy _ ↦ by
      have hprod := degree_mul_lt_of_le_of_lt_of_separated
        (translatedTruncLE x a) (translatedTruncLE y b) ρ σ τ
        (hat x hx) (hbt y hy) hsep
      rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
        NatOrdinal.cantorDegree_lt_coe_iff] at hprod
      exact NatOrdinal.of.lt_iff_lt.mp
        (by simpa only [coe_translatedTruncLE, Subring.coe_mul, NatOrdinal.of_val] using hprod))
  have hrem : ν (translatedTruncLE γ (a * b) - translatedTruncLE γ a * b -
      a * translatedTruncLE γ b) < τ := by
    rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
      NatOrdinal.cantorDegree_lt_coe_iff]
    change NatOrdinal.of (((translatedTruncLE γ (a * b) : HahnSeries G R) -
      (translatedTruncLE γ a : HahnSeries G R) * b -
      (a : HahnSeries G R) * translatedTruncLE γ b).cantorBendixsonValue) < ω^ τ
    exact NatOrdinal.of.lt_iff_lt.mpr (by
      simpa only [coe_translatedTruncLE, Subring.coe_mul, NatOrdinal.val_wpow] using hremValue)
  have hlast : ν (a * translatedTruncLE γ b) < τ :=
    degree_mul_lt_of_le_of_lt_of_separated a (translatedTruncLE γ b)
      ρ σ τ ha (hbt γ hγ) hsep
  have heq : translatedTruncLE γ (a * b) - translatedTruncLE γ a * b =
      (translatedTruncLE γ (a * b) - translatedTruncLE γ a * b -
        a * translatedTruncLE γ b) + a * translatedTruncLE γ b := by
    abel
  rw [heq]
  exact ((ν).map_add_le_max _ _).trans_lt (max_lt hrem hlast)

end HahnSeries.Nonpositive
