/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Aristotle
-/

import LeanPool.ForwardEuler.Main

/-!
# Forward Euler Method

Source: url:https://github.com/Vilin97/forward_euler
Authors: Vasily Ilin, Aristotle
Status: verified
Main declarations: `ODE.EulerMethod.dist_path_le`, `ODE.EulerMethod.tendsto_path`
Tags: numerical-analysis, ordinary-differential-equations, numerical-methods
MSC: 65L05, 34A45
-/

/-!
## Mathematical overview

A formal proof of convergence of the forward Euler method for ordinary
differential equations.

Given an ODE `y'(t) = v(t, y(t))` with `y(t₀) = y₀`, where
`v : ℝ × E → E` is a vector field on a normed space `E`, this project
defines the Euler approximation and proves that it converges to the true
solution as the step size `h → 0⁺`.

## Main results

- `ODE.EulerMethod.dist_deriv_le` — the Euler derivative is uniformly close
  to the vector field along the path:
  `dist(deriv(t), v(t, path(t))) ≤ h * (L + K * M)`.
- `ODE.EulerMethod.dist_path_le` — Grönwall bound on the distance between
  the Euler path and the true solution.
- `ODE.EulerMethod.tendsto_path` — `path(v, h, t₀, y₀, t) → sol(t)` as
  `h → 0⁺`.
-/
