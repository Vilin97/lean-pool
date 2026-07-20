/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/

import LeanPool.SingularModuli.QuadraticOrder.Basic
import LeanPool.SingularModuli.QuadraticOrder.Norm
import LeanPool.SingularModuli.QuadraticOrder.Discriminant
import LeanPool.SingularModuli.QuadraticOrder.Verification
import LeanPool.SingularModuli.QuadraticOrder.RootCounting
import LeanPool.SingularModuli.QuadraticOrder.Prime
import LeanPool.SingularModuli.QuadraticOrder.CanonicalForm

/-!
# Quadratic-order prime classification

Source: url:https://github.com/ElodinLaarz/lean-thesis
Authors: Caleb L. Geiger
Status: verified
Main declarations: `QuadraticOrder.prime_inert_iff`, `QuadraticOrder.prime_split_iff`
Tags: algebraic-number-theory, quadratic-orders, legendre-symbol
MSC: 11R11, 11R29, 11A15
-/
