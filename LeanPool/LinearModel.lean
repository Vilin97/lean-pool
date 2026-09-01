/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/

import LeanPool.LinearModel.Clt
import LeanPool.LinearModel.Ols

/-!
# Model-robust linear regression and heteroscedasticity-consistent inference

Source: url:https://github.com/lean-statistics/linear-model-lean
Authors: Patrick Rubin-Delanchy, Andrew Jones
Status: verified
Main declarations: `LeanPool.LinearModel.hcGram_pvalue_conservative_of_level`
Tags: linear-regression, central-limit-theorem, heteroscedasticity, robust-inference
MSC: 62J05, 62F03, 62E20, 60F05
-/

/-!
The development formalizes ordinary least squares without assuming that the
conditional mean is a correctly specified linear model. Its main chain of
results proves a Lindeberg central limit theorem, derives asymptotic normality
of scalar projections of the OLS estimator, establishes consistency of the
HC0--HC3 sandwich estimators, and proves conservative robust tests and p-values
under heteroscedasticity and misspecification. It also shows that HC2 applied to
the two-sample cell-means regression reproduces Welch's t-statistic exactly.
-/
