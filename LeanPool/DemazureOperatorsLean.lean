/-
Copyright (c) 2026 Óscar Álvarez Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Óscar Álvarez Sánchez
-/
module

public import LeanPool.DemazureOperatorsLean.Demazure
public import LeanPool.DemazureOperatorsLean.DemazureAux
public import LeanPool.DemazureOperatorsLean.DemazureRelations
public import LeanPool.DemazureOperatorsLean.DemazureAuxRelations
public import LeanPool.DemazureOperatorsLean.StrongExchange
public import LeanPool.DemazureOperatorsLean.Matsumoto

/-!
# Demazure Operators and Lean

Source: doi:10.1070/RM1973v028n03ABEH001557
Authors: Óscar Álvarez Sánchez
Status: verified
Main declarations: `Demazure.Dem`, `CoxeterSystem.strongExchangeProperty`
Tags: algebraic-combinatorics, demazure-operators, polynomials, representation-theory
MSC: 05E05, 13P10, 20F55
-/

@[expose] public section

/-!
The Demazure-operator declarations are sourced to the BGG Schubert-cells paper
listed in the project card. The strong-exchange declaration is included as
supporting Coxeter theory with source metadata from Humphreys' *Reflection Groups
and Coxeter Groups*. The Matsumoto development is retained as conditional
auxiliary infrastructure because `CoxeterSystem.matsumoto_reduced` assumes the
extra `MatsumotoCondition` hypothesis.
-/
