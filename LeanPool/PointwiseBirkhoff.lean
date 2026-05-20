/-
Copyright (c) 2026 Lua Viana Reis, Oliver Butterley, Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis, Oliver Butterley, Pietro Monticone
-/

import LeanPool.PointwiseBirkhoff.Main

/-!
# Pointwise Birkhoff Ergodic Theorem

Source: url:https://doi.org/10.1017/CBO9780511608728
Authors: Lua Viana Reis, Oliver Butterley, Pietro Monticone
Status: verified
Main declarations: `LeanPool.PointwiseBirkhoff.birkhoffErgodicTheorem'`
Tags: ergodic-theory, measure-theory, probability
MSC: 37A30, 28D05
-/

/-!
## Mathematical overview

Formalizes the pointwise Birkhoff ergodic theorem for an integrable real-valued
observable on a probability space with a measure-preserving transformation. The
limit is expressed as the conditional expectation onto the invariant
measurable space, and the final theorem removes an explicit measurability
assumption on the observable.
-/
