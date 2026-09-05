/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/

import LeanPool.LinearModel.Ols.Assumptions
import LeanPool.LinearModel.Ols.ConvergenceInProbability
import LeanPool.LinearModel.Ols.Gram
import LeanPool.LinearModel.Ols.HCSandwichConsistency
import LeanPool.LinearModel.Ols.Leverage
import LeanPool.LinearModel.Ols.Optimality
import LeanPool.LinearModel.Ols.ProjectionCLT
import LeanPool.LinearModel.Ols.QuadForm
import LeanPool.LinearModel.Ols.TTest
import LeanPool.LinearModel.Ols.Welch

/-!
# Ordinary least squares and model-robust inference

This directory develops fixed-design OLS geometry, central limit theory,
heteroscedasticity-consistent sandwich estimators, conservative p-values, and
the two-sample identification with Welch's statistic.
-/
