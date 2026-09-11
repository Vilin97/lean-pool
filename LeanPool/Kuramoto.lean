/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Cassie
-/
module

public import LeanPool.Kuramoto.OrderParameter
public import LeanPool.Kuramoto.GradientFlow
public import LeanPool.Kuramoto.Contraction
public import LeanPool.Kuramoto.Weighted
public import LeanPool.Kuramoto.Hebbian
public import LeanPool.Kuramoto.Connections
public import LeanPool.Kuramoto.WitnessGeometry
public import LeanPool.Kuramoto.Frontier

/-!
# Finite-N Kuramoto Synchronization

Source: url:https://github.com/velvetmonkey/kuramoto-lean
Authors: Ben Cassie
Status: verified
Main declarations: `kuramotoR_norm_le_one`, `weighted_lyapunov_descent`
Tags: dynamical-systems, synchronization, kuramoto
MSC: 34D06
-/

@[expose] public section
