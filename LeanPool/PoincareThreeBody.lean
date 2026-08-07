/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Analytic
import LeanPool.PoincareThreeBody.AnalyticNormalization
import LeanPool.PoincareThreeBody.AnalyticMinors
import LeanPool.PoincareThreeBody.ActionFactorization
import LeanPool.PoincareThreeBody.ActionPoisson
import LeanPool.PoincareThreeBody.Averaging
import LeanPool.PoincareThreeBody.Core
import LeanPool.PoincareThreeBody.CoefficientNormalization
import LeanPool.PoincareThreeBody.CertifiedPoincareSet
import LeanPool.PoincareThreeBody.ChapterVI
import LeanPool.PoincareThreeBody.ChapterVIContour
import LeanPool.PoincareThreeBody.ChapterVIDarboux
import LeanPool.PoincareThreeBody.ChapterVILatticeReduction
import LeanPool.PoincareThreeBody.Delaunay
import LeanPool.PoincareThreeBody.DelaunayActions
import LeanPool.PoincareThreeBody.DelaunayAnchorChart
import LeanPool.PoincareThreeBody.DelaunayChart
import LeanPool.PoincareThreeBody.DelaunayFlow
import LeanPool.PoincareThreeBody.DelaunaySection
import LeanPool.PoincareThreeBody.DenseResonantObstruction
import LeanPool.PoincareThreeBody.DifferentialDependence
import LeanPool.PoincareThreeBody.DisturbingCertificate
import LeanPool.PoincareThreeBody.DisturbingFunction
import LeanPool.PoincareThreeBody.EnergyLeafObstruction
import LeanPool.PoincareThreeBody.GeneratingFunction
import LeanPool.PoincareThreeBody.GlobalEnergySection
import LeanPool.PoincareThreeBody.HamiltonianMixedPartials
import LeanPool.PoincareThreeBody.HomologicalEquation
import LeanPool.PoincareThreeBody.IrrationalTorusFlow
import LeanPool.PoincareThreeBody.KeplerOrbit
import LeanPool.PoincareThreeBody.KeplerPhaseOrbit
import LeanPool.PoincareThreeBody.KeplerFlow
import LeanPool.PoincareThreeBody.KeplerHamiltonian
import LeanPool.PoincareThreeBody.LeadingObstruction
import LeanPool.PoincareThreeBody.LocalEnergyLeaf
import LeanPool.PoincareThreeBody.MixedPartials
import LeanPool.PoincareThreeBody.NormalizationInduction
import LeanPool.PoincareThreeBody.NormalizationClosure
import LeanPool.PoincareThreeBody.OneTwoResonance
import LeanPool.PoincareThreeBody.OrbitHomologicalEquation
import LeanPool.PoincareThreeBody.ParameterDomainTopology
import LeanPool.PoincareThreeBody.ParameterizedAnalyticDivision
import LeanPool.PoincareThreeBody.Perturbation
import LeanPool.PoincareThreeBody.PoincareSet
import LeanPool.PoincareThreeBody.PoissonNormalization
import LeanPool.PoincareThreeBody.Polar
import LeanPool.PoincareThreeBody.Resonance
import LeanPool.PoincareThreeBody.ResonantActionObstruction
import LeanPool.PoincareThreeBody.ResonantOrbit
import LeanPool.PoincareThreeBody.RotatingEllipse
import LeanPool.PoincareThreeBody.ValidatedQuadrature

/-!
# A Restricted Three-Body Nonintegrability Theorem

Sources: Poincaré, *Les méthodes nouvelles de la mécanique céleste*, Volume I, Chapter VI;
arxiv:2111.11031, doi:10.1063/5.0266087, url:https://arxiv.org/abs/2111.11031
Authors: Gershon Bialer
Status: verified
Main declarations: `LeanPool.PoincareThreeBody.nonintegrability_of_collisionBand`,
`LeanPool.PoincareThreeBody.nonintegrability_of_chapterVI_asymptotics`
Tags: dynamical-systems, celestial-mechanics, hamiltonian-systems, nonintegrability
MSC: 70F07, 37J30, 37J40
-/

/-!
# A nonintegrability theorem for the planar restricted three-body problem

This project proves a parameter-analytic nonintegrability theorem for the planar circular
restricted three-body problem.  Its unconditional proof is a modern modification of Poincaré's
argument: real logarithmic collision blow-up and analytic continuation replace the complex
singularity classification and Darboux coefficient estimates in §§93--101 of Chapter VI.

The source states the classical planar result as Theorem 1.1 on page 2 of arXiv:2111.11031v2
and gives its precise local meromorphic resonant-orbit obstruction in Theorem 3.1 on page 8.
The final Lean theorem is the fixed-coordinate, global uniform-domain special case: a global
real-analytic family restricts and complexifies on the local neighborhoods used by the source.

`ChapterVILatticeReduction` verifies the finite two-variable coefficient reduction in §94 and
its unimodular reindexing for arbitrary summable double series. `ChapterVIContour` verifies
coefficient extraction by normalized circle integration for the resulting finite Laurent sums.
`ChapterVIDarboux` proves that a Darboux-type asymptotic with nonzero leading model forces
eventual coefficient nonvanishing, as used in §§99--102.  `ChapterVI` connects these results to
the restricted resonant Fourier coefficient and final theorem. The analytic passage from a
summable coefficient family to Poincaré's holomorphic infinite Laurent series, complex
singularity/admissibility analysis, and derivation of the Darboux asymptotics are not yet
formalized. Thus the project must not be cited as a complete verification of Poincaré's original
Chapter VI calculations.
-/
