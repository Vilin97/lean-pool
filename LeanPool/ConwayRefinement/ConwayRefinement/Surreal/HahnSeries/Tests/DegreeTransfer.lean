/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.DegreeTransfer

/-!
# Checks for Conway-to-Hahn degree transfer

The two-term example `ω + 1` has distinct nonzero exponents, so it excludes the zero and
single-monomial degeneracies. Its finite support gives degree zero on both sides of the full Hahn
embedding, while the generic equality gives degree preservation for every surreal number.
-/

universe u

public noncomputable section

namespace Tests

open Surreal

/-- The nondegenerate two-term surreal used by the degree-transfer check. -/
def twoTermDegreeSurreal : Surreal.{u} :=
  ω^ (1 : Surreal.{u}) + ((1 : ℝ) : Surreal.{u})

private theorem twoTermDegreeSurreal_support_finite :
    ((twoTermDegreeSurreal : Surreal.{u}).support).Finite := by
  rw [twoTermDegreeSurreal]
  have hwpow : (support (ω^ (1 : Surreal.{u}))).Finite := by
    rw [support_wpow]
    exact Set.finite_singleton _
  exact (hwpow.union (support_realCast_finite (1 : ℝ))).subset support_add_subset

private theorem twoTermDegreeSurreal_ne_zero :
    (twoTermDegreeSurreal : Surreal.{u}) ≠ 0 := by
  rw [twoTermDegreeSurreal]
  exact (add_pos (Surreal.wpow_pos _) (by norm_num)).ne'

/-- The public full Hahn embedding preserves degree for an arbitrary surreal. -/
theorem surrealFullHahn_supportDegree (x : Surreal.{u}) :
    x.toFullHahnSeries.degree = x.supportDegree :=
  supportDegree_toFullHahnSeries x

/-- The nondegenerate two-term Conway normal form has degree zero. -/
theorem twoTermDegreeSurreal_supportDegree :
    (twoTermDegreeSurreal : Surreal.{u}).supportDegree = 0 := by
  rw [← supportDegree_toFullHahnSeries, HahnSeries.degree_eq_zero]
  constructor
  · intro hzero
    apply twoTermDegreeSurreal_ne_zero
    apply toFullHahnSeries_injective
    rw [hzero, toFullHahnSeries_zero]
  · have himage :
        (twoTermDegreeSurreal : Surreal.{u}).toFullHahnSeries.support ⊆
          OrderDual.toDual '' (twoTermDegreeSurreal : Surreal.{u}).support := by
      intro i hi
      exact ⟨i.ofDual, mem_support_toFullHahnSeries.mp hi, by simp⟩
    exact (twoTermDegreeSurreal_support_finite.image OrderDual.toDual).subset himage

end Tests
