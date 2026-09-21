/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.SeveralComplexVariables.AnalyticUniqueness
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Basic
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.CauchyCoefficients
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.CauchyDerivatives
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.CauchyEstimates
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.CauchyIntegral
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.CauchyRiemann
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.CauchySeries
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.ContourIntegral
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Derivatives
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.PolynomialDerivatives
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.DominatedIntegral
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.FunctionSpace
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.LocallyBounded
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.LocallyUniform
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Montel
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Osgood
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.ParametricIntegral
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Polydisc
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.PolydiscTaylor
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Reindex

/-!
# Several-complex-variables infrastructure

This umbrella imports finite-dimensional complex analyticity, polydisc Cauchy formulas and
series, locally bounded Osgood, coordinate derivatives and Cauchy–Riemann equations, locally
uniform limits and their derivatives, compact-open holomorphic function spaces, Montel's theorem,
and analytic parameter-dependent integrals. Taylor coefficients, convergence and remainder
estimates allow separate radii in each coordinate.
The modules are independent of the simplex-measure and Carlson developments. See `COVERAGE.md`
for the Mathlib inventory, proved textbook coverage, and remaining work.
-/
