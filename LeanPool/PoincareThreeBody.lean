/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Analytic
import LeanPool.PoincareThreeBody.Averaging
import LeanPool.PoincareThreeBody.Core
import LeanPool.PoincareThreeBody.Delaunay
import LeanPool.PoincareThreeBody.GeneratingFunction
import LeanPool.PoincareThreeBody.KeplerOrbit
import LeanPool.PoincareThreeBody.Perturbation
import LeanPool.PoincareThreeBody.Polar
import LeanPool.PoincareThreeBody.Resonance
import LeanPool.PoincareThreeBody.ResonantOrbit
import LeanPool.PoincareThreeBody.RotatingEllipse

/-!
# Poincaré's Nonintegrability Theorem for the Restricted Three-Body Problem

Source: arxiv:2111.11031, doi:10.1063/5.0266087, url:https://arxiv.org/abs/2111.11031
Authors: Gershon Bialer
Status: verified
Main declarations: `LeanPool.PoincareThreeBody.delaunayHomological_obstruction`
Tags: dynamical-systems, celestial-mechanics, hamiltonian-systems, nonintegrability
MSC: 70F07, 37J30, 37J40
-/

/-!
# Poincaré's theorem for the planar restricted three-body problem

This project formalizes the analytic and perturbative ingredients of Poincaré's classical
nonintegrability theorem for the planar circular restricted three-body problem.
-/
