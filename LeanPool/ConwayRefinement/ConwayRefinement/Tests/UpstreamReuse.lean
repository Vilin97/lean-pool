/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.MonoidAlgebra.ToDirectSum
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.HahnSeries.Cardinal
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Hom.Set
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.SetTheory.Cardinal.Cofinality.Basic
import Mathlib.SetTheory.ZFC.Class
import Mathlib.SetTheory.Ordinal.Family
import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Pow
import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.HahnSeries.Basic
import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Ordinal

/-!
# Upstream reuse checks

This module pins the availability and compiler-visible signatures of selected upstream interfaces.
It intentionally declares no mathematical API. The hash-command linter is disabled here because
the module consists precisely of checked signature fixtures.
-/
universe u v w
  (@Ordinal.isPrincipal_add_iff_zero_or_omega0_opow :
    {o : Ordinal.{u}} →
      Ordinal.IsPrincipal (· + ·) o ↔
        o = 0 ∨ o ∈ Set.range fun e : Ordinal.{u} ↦ Ordinal.omega0 ^ e)
  (@Ordinal.sub_omega0_opow_log_lt :
    {o : Ordinal.{u}} →
      o ≠ 0 → o - Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 o < o)
  (@HahnSeries.cardSuppLTSubring :
    (Γ : Type u) →
      (R : Type v) →
        (κ : Cardinal.{u}) →
          [PartialOrder Γ] →
            [AddCommMonoid Γ] →
              [IsOrderedCancelAddMonoid Γ] →
                [Ring R] → [Fact (Cardinal.aleph0 ≤ κ)] → Subring (HahnSeries Γ R))
  (@HahnSeries.cardSuppLTSubfield :
    (Γ : Type u) →
      (R : Type v) →
        (κ : Cardinal.{u}) →
          [LinearOrder Γ] →
            [AddCommGroup Γ] →
              [IsOrderedAddMonoid Γ] →
                [Field R] → [Fact (Cardinal.aleph0 < κ)] → Subfield (HahnSeries Γ R))
  (@Order.le_cof_iff :
    ∀ {α : Type u} [Preorder α] {c : Cardinal.{u}},
      c ≤ Order.cof α ↔ ∀ s : Set α, IsCofinal s → c ≤ Cardinal.mk ↥s)
  (@not_isCofinal_iff :
    ∀ {α : Type u} [LinearOrder α] {s : Set α},
      ¬ IsCofinal s ↔ ∃ x, ∀ y ∈ s, y < x)
  (@HahnSeries.cardSupp_single_mul_le :
    ∀ {Γ : Type u} {R : Type v} [PartialOrder Γ] [AddCommMonoid Γ]
      [IsOrderedCancelAddMonoid Γ] [NonUnitalNonAssocSemiring R]
      (x : HahnSeries Γ R) (a : Γ) (r : R),
        (HahnSeries.single a r * x).cardSupp ≤ x.cardSupp)
  (@HahnSeries.iterateEquiv :
    {Γ : Type u} →
      {Γ' : Type v} →
        {R : Type w} →
          [PartialOrder Γ] →
            [Zero R] →
              [PartialOrder Γ'] →
                HahnSeries Γ (HahnSeries Γ' R) ≃ HahnSeries (Lex (Γ × Γ')) R)
  (@HahnSeries.truncLT :
    {Γ : Type u} →
      {R : Type v} →
        [Zero R] →
          [PartialOrder Γ] →
            [DecidableLT Γ] → Γ → ZeroHom (HahnSeries Γ R) (HahnSeries Γ R))
  (@HahnSeries.embDomain :
    {Γ : Type u} →
      {Γ' : Type v} →
        {R : Type w} →
          [PartialOrder Γ] →
            [Zero R] →
              [PartialOrder Γ'] →
                (Γ ↪o Γ') → HahnSeries Γ R → HahnSeries Γ' R)
  (@HahnSeries.support_embDomain_subset :
    {Γ : Type u} →
      {Γ' : Type v} →
        {R : Type w} →
          [PartialOrder Γ] →
            [Zero R] →
              [PartialOrder Γ'] →
                {f : Γ ↪o Γ'} →
                  {x : HahnSeries Γ R} →
                    (HahnSeries.embDomain f x).support ⊆ f '' x.support)
  (@WithBot.coe_sSup' :
    {α : Type u} →
      [Preorder α] →
        [SupSet α] →
          {s : Set α} →
            s.Nonempty →
              BddAbove s →
                ((sSup s : α) : WithBot α) =
                  sSup ((fun a : α ↦ (a : WithBot α)) '' s))
  (@SurrealHahnSeries.type_support :
    ∀ x : SurrealHahnSeries.{u},
      Ordinal.type (α := x.support) (· > ·) = Ordinal.lift.{u + 1} x.length)
  (@not_injective_of_ordinal :
    ∀ {α : Type v} [Small.{u} α] (f : Ordinal.{u} → α), ¬Function.Injective f)
