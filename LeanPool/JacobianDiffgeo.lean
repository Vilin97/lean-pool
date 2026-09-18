/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import LeanPool.JacobianDiffgeo.Init
public import LeanPool.JacobianDiffgeo.Surface
public import LeanPool.JacobianDiffgeo.LocalMultiplicity
public import LeanPool.JacobianDiffgeo.Forms
public import LeanPool.JacobianDiffgeo.MappingDegree
public import LeanPool.JacobianDiffgeo.ProjectiveLine
public import LeanPool.JacobianDiffgeo.ResidueCalculus
public import LeanPool.JacobianDiffgeo.Meromorphic
public import LeanPool.JacobianDiffgeo.Path
public import LeanPool.JacobianDiffgeo.SphereTopology
public import LeanPool.JacobianDiffgeo.MeromorphicTrace
public import LeanPool.JacobianDiffgeo.ProperDegree
public import LeanPool.JacobianDiffgeo.JacobianConstruction
public import LeanPool.JacobianDiffgeo.Cech
public import LeanPool.JacobianDiffgeo.Finiteness
public import LeanPool.JacobianDiffgeo.Dbar
public import LeanPool.JacobianDiffgeo.Monodromy
public import LeanPool.JacobianDiffgeo.FormTrace
public import LeanPool.JacobianDiffgeo.PlanarStokes
public import LeanPool.JacobianDiffgeo.SerrePairing
public import LeanPool.JacobianDiffgeo.AbelWeak
public import LeanPool.JacobianDiffgeo.DolbeaultComparison
public import LeanPool.JacobianDiffgeo.ResidueTheorem
public import LeanPool.JacobianDiffgeo.CanonicalForms
public import LeanPool.JacobianDiffgeo.LaurentTail
public import LeanPool.JacobianDiffgeo.JacFunctorial
public import LeanPool.JacobianDiffgeo.Abel
public import LeanPool.JacobianDiffgeo.TailDuality
public import LeanPool.JacobianDiffgeo.H1Genus
public import LeanPool.JacobianDiffgeo.RiemannRoch
public import LeanPool.JacobianDiffgeo.GenusSphereHeadline
public import LeanPool.JacobianDiffgeo.PeriodLattice
public import LeanPool.JacobianDiffgeo.CechCount
public import LeanPool.JacobianDiffgeo.Challenge
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# The Jacobian of a Compact Riemann Surface

Source: url:https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9
Authors: Rado Kirov
Status: verified
Main declarations: `genus_eq_zero_iff_homeo`, `Jacobian.ofCurve_inj`
Tags: riemann-surfaces, complex-geometry, abel-jacobi, riemann-roch, serre-duality
MSC: 14H40, 30F30, 32G20
-/

@[expose] public section
