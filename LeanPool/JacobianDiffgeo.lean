/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Init
import LeanPool.JacobianDiffgeo.Surface
import LeanPool.JacobianDiffgeo.LocalMultiplicity
import LeanPool.JacobianDiffgeo.Forms
import LeanPool.JacobianDiffgeo.MappingDegree
import LeanPool.JacobianDiffgeo.ProjectiveLine
import LeanPool.JacobianDiffgeo.ResidueCalculus
import LeanPool.JacobianDiffgeo.Meromorphic
import LeanPool.JacobianDiffgeo.Path
import LeanPool.JacobianDiffgeo.SphereTopology
import LeanPool.JacobianDiffgeo.MeromorphicTrace
import LeanPool.JacobianDiffgeo.ProperDegree
import LeanPool.JacobianDiffgeo.JacobianConstruction
import LeanPool.JacobianDiffgeo.Cech
import LeanPool.JacobianDiffgeo.Finiteness
import LeanPool.JacobianDiffgeo.Dbar
import LeanPool.JacobianDiffgeo.Monodromy
import LeanPool.JacobianDiffgeo.FormTrace
import LeanPool.JacobianDiffgeo.PlanarStokes
import LeanPool.JacobianDiffgeo.SerrePairing
import LeanPool.JacobianDiffgeo.AbelWeak
import LeanPool.JacobianDiffgeo.DolbeaultComparison
import LeanPool.JacobianDiffgeo.ResidueTheorem
import LeanPool.JacobianDiffgeo.CanonicalForms
import LeanPool.JacobianDiffgeo.LaurentTail
import LeanPool.JacobianDiffgeo.JacFunctorial
import LeanPool.JacobianDiffgeo.Abel
import LeanPool.JacobianDiffgeo.TailDuality
import LeanPool.JacobianDiffgeo.H1Genus
import LeanPool.JacobianDiffgeo.RiemannRoch
import LeanPool.JacobianDiffgeo.GenusSphereHeadline
import LeanPool.JacobianDiffgeo.PeriodLattice
import LeanPool.JacobianDiffgeo.CechCount
import LeanPool.JacobianDiffgeo.Challenge

/-!
# The Jacobian of a Compact Riemann Surface

Source: url:https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9
Authors: Rado Kirov
Status: verified
Main declarations: `JacobianChallenge.genus_eq_zero_iff_homeo`
Tags: riemann-surfaces, complex-geometry, abel-jacobi, riemann-roch, serre-duality
MSC: 14H40, 30F30, 32G20
-/
