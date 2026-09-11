/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.CencovPetz.Basic
public import LeanPool.CencovPetz.CencovFinite
public import LeanPool.CencovPetz.CencovSplitPoint
public import LeanPool.CencovPetz.ContinuousExtension
public import LeanPool.CencovPetz.FisherContinuity
public import LeanPool.CencovPetz.LeftInverseIsometry
public import LeanPool.CencovPetz.MarkovMorphism
public import LeanPool.CencovPetz.MonotoneMetric
public import LeanPool.CencovPetz.PermutationInvariance
public import LeanPool.CencovPetz.PermutationInvariantBilinForm
public import LeanPool.CencovPetz.RationalDensity
public import LeanPool.CencovPetz.RationalPoint
public import LeanPool.CencovPetz.Replication
public import LeanPool.CencovPetz.ReplicationInvariance
public import LeanPool.CencovPetz.Simplex
public import LeanPool.CencovPetz.SimplexTopology
public import LeanPool.CencovPetz.Splitting
public import LeanPool.CencovPetz.SplittingInvariance
public import LeanPool.CencovPetz.SplittingUniform
public import LeanPool.CencovPetz.SufficientStatistic
public import LeanPool.CencovPetz.Uniform
public import LeanPool.CencovPetz.UniformScalarConstant
public import LeanPool.CencovPetz.UniformScalarMultiple
public import LeanPool.CencovPetz.UniformSimplex
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Finite Čencov-Petz Uniqueness

Source: url:https://bookstore.ams.org/mmono-53
Authors: Adam Benenson
Status: verified
Main declarations: `LeanPool.CencovPetz.MonotoneMetricFamily.eq_smul_fisher_of_continuous`
Tags: information-geometry, fisher-information, markov-morphisms, finite-simplex
MSC: 62B10, 53C21
-/

@[expose] public section

/-!
This project formalizes the finite/discrete Čencov-Petz uniqueness theorem:
every continuous monotone metric family on finite probability simplexes is a
scalar multiple of the Fisher information metric. The imported declarations
are placed under `LeanPool.CencovPetz`.
-/
