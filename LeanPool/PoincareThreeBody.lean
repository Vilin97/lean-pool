/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import LeanPool.PoincareThreeBody.Analytic
public import LeanPool.PoincareThreeBody.AnalyticNormalization
public import LeanPool.PoincareThreeBody.AnalyticMinors
public import LeanPool.PoincareThreeBody.ActionFactorization
public import LeanPool.PoincareThreeBody.ActionPoisson
public import LeanPool.PoincareThreeBody.Averaging
public import LeanPool.PoincareThreeBody.Core
public import LeanPool.PoincareThreeBody.CoefficientNormalization
public import LeanPool.PoincareThreeBody.CertifiedPoincareSet
public import LeanPool.PoincareThreeBody.Delaunay
public import LeanPool.PoincareThreeBody.DelaunayActions
public import LeanPool.PoincareThreeBody.DelaunayAnchorChart
public import LeanPool.PoincareThreeBody.DelaunayChart
public import LeanPool.PoincareThreeBody.DelaunayFlow
public import LeanPool.PoincareThreeBody.DelaunaySection
public import LeanPool.PoincareThreeBody.DenseResonantObstruction
public import LeanPool.PoincareThreeBody.DifferentialDependence
public import LeanPool.PoincareThreeBody.DisturbingCertificate
public import LeanPool.PoincareThreeBody.DisturbingFunction
public import LeanPool.PoincareThreeBody.EnergyLeafObstruction
public import LeanPool.PoincareThreeBody.GeneratingFunction
public import LeanPool.PoincareThreeBody.GlobalEnergySection
public import LeanPool.PoincareThreeBody.HamiltonianMixedPartials
public import LeanPool.PoincareThreeBody.HomologicalEquation
public import LeanPool.PoincareThreeBody.IrrationalTorusFlow
public import LeanPool.PoincareThreeBody.KeplerOrbit
public import LeanPool.PoincareThreeBody.KeplerPhaseOrbit
public import LeanPool.PoincareThreeBody.KeplerFlow
public import LeanPool.PoincareThreeBody.KeplerHamiltonian
public import LeanPool.PoincareThreeBody.LeadingObstruction
public import LeanPool.PoincareThreeBody.LocalEnergyLeaf
public import LeanPool.PoincareThreeBody.MixedPartials
public import LeanPool.PoincareThreeBody.NormalizationInduction
public import LeanPool.PoincareThreeBody.NormalizationClosure
public import LeanPool.PoincareThreeBody.OneTwoResonance
public import LeanPool.PoincareThreeBody.OrbitHomologicalEquation
public import LeanPool.PoincareThreeBody.ParameterDomainTopology
public import LeanPool.PoincareThreeBody.ParameterizedAnalyticDivision
public import LeanPool.PoincareThreeBody.Perturbation
public import LeanPool.PoincareThreeBody.PoincareSet
public import LeanPool.PoincareThreeBody.PoissonNormalization
public import LeanPool.PoincareThreeBody.Polar
public import LeanPool.PoincareThreeBody.Resonance
public import LeanPool.PoincareThreeBody.ResonantActionObstruction
public import LeanPool.PoincareThreeBody.ResonantOrbit
public import LeanPool.PoincareThreeBody.RotatingEllipse
public import LeanPool.PoincareThreeBody.ValidatedQuadrature

/-!
# Poincaré's Nonintegrability Theorem for the Restricted Three-Body Problem

Source: arxiv:2111.11031, doi:10.1063/5.0266087, url:https://arxiv.org/abs/2111.11031
Authors: Gershon Bialer
Status: verified
Main declarations: `LeanPool.PoincareThreeBody.nonintegrability_of_collisionBand`
Tags: dynamical-systems, celestial-mechanics, hamiltonian-systems, nonintegrability
MSC: 70F07, 37J30, 37J40
-/

@[expose] public section

/-!
# Poincaré's theorem for the planar restricted three-body problem

This project formalizes the analytic and perturbative ingredients of Poincaré's classical
nonintegrability theorem for the planar circular restricted three-body problem.

The source states the classical planar result as Theorem 1.1 on page 2 of arXiv:2111.11031v2
and gives its precise local meromorphic resonant-orbit obstruction in Theorem 3.1 on page 8.
The final Lean theorem is the fixed-coordinate, global uniform-domain special case: a global
real-analytic family restricts and complexifies on the local neighborhoods used by the source.
-/
