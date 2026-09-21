/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.R.Basic
public import LeanPool.CarlsonFunctions.Carlson.R.Integral
public import LeanPool.CarlsonFunctions.Carlson.R.Continuation
public import LeanPool.CarlsonFunctions.Carlson.R.Deriv
public import LeanPool.CarlsonFunctions.Carlson.R.Exponent
public import LeanPool.CarlsonFunctions.Carlson.R.Relations
public import LeanPool.CarlsonFunctions.Carlson.R.JointParameter
public import LeanPool.CarlsonFunctions.Carlson.R.Confluence
public import LeanPool.CarlsonFunctions.Carlson.R.Laplace
public import LeanPool.CarlsonFunctions.Carlson.R.SlitPlane
public import LeanPool.CarlsonFunctions.Carlson.R.SingleIntegral
public import LeanPool.CarlsonFunctions.Carlson.R.SingleIntegralAnalytic
public import LeanPool.CarlsonFunctions.Carlson.R.SlitContinuation
public import LeanPool.CarlsonFunctions.Carlson.R.SlitJointAnalytic
public import LeanPool.CarlsonFunctions.Carlson.R.SlitIntegral
public import LeanPool.CarlsonFunctions.Carlson.R.RayKernel
public import LeanPool.CarlsonFunctions.Carlson.R.Contour
public import LeanPool.CarlsonFunctions.Carlson.R.EulerTransform
public import LeanPool.CarlsonFunctions.Carlson.R.IntegralEvaluation
public import LeanPool.CarlsonFunctions.Carlson.R.SmallVariable
public import LeanPool.CarlsonFunctions.Carlson.R.AssociatedRecurrence
public import LeanPool.CarlsonFunctions.Carlson.R.ContinuedRecurrence
public import LeanPool.CarlsonFunctions.Carlson.R.ZeroParameter
public import LeanPool.CarlsonFunctions.Carlson.R.IntegerParameters
public import LeanPool.CarlsonFunctions.Carlson.R.AssociatedDependence
public import LeanPool.CarlsonFunctions.Carlson.R.SlitAssociated
public import LeanPool.CarlsonFunctions.Carlson.R.SlitDeriv
public import LeanPool.CarlsonFunctions.Carlson.R.SlitRelations
public import LeanPool.CarlsonFunctions.Carlson.R.EulerPoisson
public import LeanPool.CarlsonFunctions.Carlson.R.JointRecurrence

/-!
# Carlson's multivariate R-function

Umbrella import for the native integral, continuation interface, differentiation kernel,
associated-function theory, confluence, and Laplace representation of Carlson's `R_t`.
The regularized slit-plane function is jointly entire in the exponent and Dirichlet
parameters and holomorphic in all nodes off the nonpositive real axis.
Node differentiation, the homogeneity recurrence, and polynomial dependence of
associated functions are available on this full slit domain. See `Carlson/R/Coverage.md`
for implemented results and known remaining work.
-/
