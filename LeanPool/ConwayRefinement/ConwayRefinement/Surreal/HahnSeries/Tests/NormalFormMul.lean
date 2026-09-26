/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.NormalFormMul

/-!
# Checks for Conway normal-form multiplication options

These checks exercise the public multiplication-option and truncation-cofinality interface without
unfolding the Conway normal-form or surreal Hahn-series definitions.
-/

open Order Set

public noncomputable section

namespace Tests

open SurrealHahnSeries

/-- Integer casts use the public constant-singleton representation. -/
example (n : ℤ) :
    (n : SurrealHahnSeries) = single 0 (n : ℝ) :=
  intCast_eq_single_zero n

/-- Arbitrary Conway normal forms preserve multiplication by integer constants. -/
example (n : ℤ) (x : Surreal) :
    ((n : Surreal) * x).toHahnSeries =
      single 0 (n : ℝ) * x.toHahnSeries :=
  Surreal.toHahnSeries_intCast_mul n x

/-- Arbitrary normal forms preserve multiplication by rational constants. -/
example (q : ℚ) (x : SurrealHahnSeries) :
    (single 0 (q : ℝ) * x).toSurreal = (q : Surreal) * x.toSurreal :=
  toSurreal_single_zero_ratCast_mul q x

/-- Arbitrary normal forms preserve multiplication by every real constant. -/
example (r : ℝ) (x : SurrealHahnSeries) :
    (single 0 r * x).toSurreal = (r : Surreal) * x.toSurreal :=
  toSurreal_single_zero_mul r x

/-- Arbitrary normal forms preserve multiplication by every singleton normal form. -/
example (p : Surreal) (r : ℝ) (x : SurrealHahnSeries) :
    (single p r * x).toSurreal = (single p r).toSurreal * x.toSurreal :=
  toSurreal_single_mul p r x

/-- Singleton multiplication is available without exposing the underlying Hahn-series subtype. -/
example (p q : Surreal) (r s : ℝ) :
    single p r * single q s = single (p + q) (r * s) :=
  single_mul_single p q r s

/-- Singleton multiplication translates arbitrary coefficients and truncation cutoffs. -/
example (p q k : Surreal) (r : ℝ) (y : SurrealHahnSeries) :
    (single p r * y).coeff k = r * y.coeff (k - p) ∧
      (single p r * y).trunc (p + q) = single p r * y.trunc q :=
  ⟨coeff_single_mul p r y k, trunc_single_mul p q r y⟩

/-- Product truncations expose exact source truncation options with the expected sign reversal. -/
example {p : Surreal} {r : ℝ} {y t : SurrealHahnSeries} :
    (t ∈ truncLT (single p r * y) →
      (0 < r ∧ ∃ b ∈ truncLT y, single p r * b = t) ∨
        (r < 0 ∧ ∃ b ∈ truncGT y, single p r * b = t)) ∧
    (t ∈ truncGT (single p r * y) →
      (0 < r ∧ ∃ b ∈ truncGT y, single p r * b = t) ∨
        (r < 0 ∧ ∃ b ∈ truncLT y, single p r * b = t)) :=
  ⟨exists_eq_single_mul_of_mem_truncLT, exists_eq_single_mul_of_mem_truncGT⟩

/-- The public option value evaluates to its defining ring expression without unfolding. -/
example (x y a b : SurrealHahnSeries) :
    mulOptionValue x y a b = a * y + x * b - a * b :=
  mulOptionValue_eq x y a b

/-- Formal and Conway multiplication agree on the leading normal-form term. -/
example (x y : SurrealHahnSeries) :
    (x * y).toSurreal.leadingTerm = (x.toSurreal * y.toSurreal).leadingTerm :=
  leadingTerm_toSurreal_mul x y

/-- A nonzero product coefficient publicly yields a contributing pair of source exponents. -/
example {x y : SurrealHahnSeries} {k : Surreal} (hk : k ∈ (x * y).support) :
    ∃ p ∈ x.support, ∃ q ∈ y.support, p + q = k :=
  exists_add_eq_of_mem_support_mul hk

/-- Nonnegative support and integer-part constant coefficients are stable under multiplication. -/
example {x y : SurrealHahnSeries}
    (hx : x.support ⊆ Set.Ici 0) (hy : y.support ⊆ Set.Ici 0) :
    (x * y).support ⊆ Set.Ici 0 ∧
      (x * y).coeff 0 = x.coeff 0 * y.coeff 0 :=
  ⟨support_mul_subset_Ici hx hy, coeff_zero_mul_of_support_subset_Ici hx hy⟩

/-- Every left truncation of a product is dominated by a genuine left product option. -/
example {x y t : SurrealHahnSeries} (ht : t ∈ truncLT (x * y)) :
    ∃ a ∈ truncLT x, ∃ b ∈ truncLT y,
      t < mulOptionValue x y a b ∧ mulOptionValue x y a b < x * y :=
  exists_mulOptionValue_between_of_mem_truncLT ht

/-- Every right truncation of a product dominates a genuine right product option. -/
example {x y t : SurrealHahnSeries} (ht : t ∈ truncGT (x * y)) :
    ∃ a ∈ truncLT x, ∃ b ∈ truncGT y,
      x * y < mulOptionValue x y a b ∧ mulOptionValue x y a b < t :=
  exists_mulOptionValue_between_of_mem_truncGT ht

/-- The limit-by-limit step consumes multiplication only for strictly shorter recursive inputs. -/
example {x y : SurrealHahnSeries}
    (hx : IsSuccPrelimit x.length) (hy : IsSuccPrelimit y.length)
    (hmul : ∀ a b : SurrealHahnSeries,
      a.length ≤ x.length → b.length ≤ y.length →
      (a.length < x.length ∨ b.length < y.length) →
      (a * b).toSurreal = a.toSurreal * b.toSurreal) :
    (x * y).toSurreal = x.toSurreal * y.toSurreal :=
  toSurreal_mul_of_isSuccPrelimit hx hy hmul

/-- The exact recursive limit step accepts the left and right length axes independently. -/
example {x y : SurrealHahnSeries}
    (hx : IsSuccPrelimit x.length) (hy : IsSuccPrelimit y.length)
    (hmulLeft : ∀ a b : SurrealHahnSeries,
      a.length < x.length → b.length ≤ y.length →
      (a * b).toSurreal = a.toSurreal * b.toSurreal)
    (hmulRight : ∀ b : SurrealHahnSeries, b.length < y.length →
      (x * b).toSurreal = x.toSurreal * b.toSurreal) :
    (x * y).toSurreal = x.toSurreal * y.toSurreal :=
  toSurreal_mul_of_isSuccPrelimit_of_axes hx hy hmulLeft hmulRight

/-- The Conway normal-form map preserves arbitrary Hahn-series products. -/
example (x y : SurrealHahnSeries) :
    (x * y).toSurreal = x.toSurreal * y.toSurreal :=
  toSurreal_mul x y

/-- The inverse Conway normal-form map preserves arbitrary surreal products. -/
example (x y : Surreal) :
    (x * y).toHahnSeries = x.toHahnSeries * y.toHahnSeries :=
  Surreal.toHahnSeries_mul x y

end Tests
