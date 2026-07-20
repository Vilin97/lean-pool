/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.CencovPetz.Basic
import LeanPool.CencovPetz.CencovFinite
import LeanPool.CencovPetz.CencovSplitPoint
import LeanPool.CencovPetz.ContinuousExtension
import LeanPool.CencovPetz.FisherContinuity
import LeanPool.CencovPetz.LeftInverseIsometry
import LeanPool.CencovPetz.MarkovMorphism
import LeanPool.CencovPetz.MonotoneMetric
import LeanPool.CencovPetz.PermutationInvariance
import LeanPool.CencovPetz.PermutationInvariantBilinForm
import LeanPool.CencovPetz.RationalDensity
import LeanPool.CencovPetz.RationalPoint
import LeanPool.CencovPetz.Replication
import LeanPool.CencovPetz.ReplicationInvariance
import LeanPool.CencovPetz.Simplex
import LeanPool.CencovPetz.SimplexTopology
import LeanPool.CencovPetz.Splitting
import LeanPool.CencovPetz.SplittingInvariance
import LeanPool.CencovPetz.SplittingUniform
import LeanPool.CencovPetz.SufficientStatistic
import LeanPool.CencovPetz.Uniform
import LeanPool.CencovPetz.UniformScalarConstant
import LeanPool.CencovPetz.UniformScalarMultiple
import LeanPool.CencovPetz.UniformSimplex

/-!
# Finite Čencov-Petz Uniqueness

Source: url:https://bookstore.ams.org/mmono-53
Authors: Adam Benenson
Status: verified
Main declarations: `LeanPool.CencovPetz.MonotoneMetricFamily.eq_smul_fisher_of_continuous`
Tags: information-geometry, fisher-information, markov-morphisms, finite-simplex
MSC: 62B10, 53C21
-/

/-!
This project formalizes the finite/discrete Čencov-Petz uniqueness theorem:
every continuous monotone metric family on finite probability simplexes is a
scalar multiple of the Fisher information metric. The imported declarations
are placed under `LeanPool.CencovPetz`.
-/
