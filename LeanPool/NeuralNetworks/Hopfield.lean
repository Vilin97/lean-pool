/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LeanPool.NeuralNetworks.Hopfield.Basic
import LeanPool.NeuralNetworks.Hopfield.Energy
import LeanPool.NeuralNetworks.Hopfield.Convergence

/-!
# Hopfield Networks

Formalization of finite Hopfield networks: spin states, network structure,
energy function, monotonic energy decrease during zero-threshold updates, and
existence of a finite update path to a fixed point.
-/
