/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.L.Basic
public import LeanPool.CarlsonFunctions.Carlson.L.Continuation
public import LeanPool.CarlsonFunctions.Carlson.L.Relations
public import LeanPool.CarlsonFunctions.Carlson.L.Properties
public import LeanPool.CarlsonFunctions.Carlson.L.Deriv
public import LeanPool.CarlsonFunctions.Carlson.L.Series
public import LeanPool.CarlsonFunctions.Carlson.L.Associated
public import LeanPool.CarlsonFunctions.Carlson.L.SlitContinuation
public import LeanPool.CarlsonFunctions.Carlson.L.SlitIntegral
public import LeanPool.CarlsonFunctions.Carlson.L.SlitRelations
public import LeanPool.CarlsonFunctions.Carlson.L.SlitProperties
public import LeanPool.CarlsonFunctions.Carlson.L.SlitDeriv
public import LeanPool.CarlsonFunctions.Carlson.L.EulerPoisson
public import LeanPool.CarlsonFunctions.Carlson.L.JointRecurrence

/-!
# Carlson's Dirichlet averages of the power-logarithm kernel

The `regCarlsonLSlit` interface is jointly holomorphic in all complex exponents and
Dirichlet parameters and all slit-plane nodes. It extends the original right-half-plane
interface, which remains available. See `Carlson/L/Coverage.md` for the paper correspondence.
-/
