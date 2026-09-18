/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
module

public import LeanPool.Vlasov.Base
public import LeanPool.Vlasov.ForMathlib
public import LeanPool.Vlasov.OT

/-!
# Mean-field derivation and well-posedness of the Vlasov equation

Source: arxiv:2607.08986
Authors: Joseph K. Miller
Status: verified
Main declarations: `Vlasov.vlasovWellPosedness`, `Vlasov.dobrushin`, `Vlasov.meanFieldLimit`
Tags: kinetic-theory, mean-field-limit, optimal-transport, wasserstein-distance, pde
MSC: 35Q83, 82C22, 49Q22
-/

@[expose] public section
