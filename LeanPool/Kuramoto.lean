/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Cassie
-/

import LeanPool.Kuramoto.OrderParameter
import LeanPool.Kuramoto.GradientFlow
import LeanPool.Kuramoto.Contraction
import LeanPool.Kuramoto.Weighted
import LeanPool.Kuramoto.Hebbian
import LeanPool.Kuramoto.Connections
import LeanPool.Kuramoto.WitnessGeometry
import LeanPool.Kuramoto.Frontier

/-!
# Finite-N Kuramoto Synchronization

Source: url:https://github.com/velvetmonkey/kuramoto-lean
Authors: Ben Cassie
Status: verified
Main declarations: `kuramotoR_norm_le_one`, `weighted_lyapunov_descent`
Tags: dynamical-systems, synchronization, kuramoto
MSC: 34D06
-/
