/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

/-!
# Caffarelli–Kohn–Nirenberg partial regularity

Source: url:https://github.com/scottnarmstrong/CaffarelliKohnNirenberg/tree/635fa6376aa3d46ae5251cb1d276a8589163f332
Authors: Scott Armstrong, Vlad Vicol
Status: verified
Main declarations: `CKN.epsilonRegularityL3`, `CKN.epsilonRegularityGradient`, `CKN.caffarelliKohnNirenberg`, `CKN.isSuitableWeakSolution_iff_integrable`, `CKN.isSuitableWeakSolutionIntegrable_shearFlow`
Tags: partial differential equations, Navier–Stokes, regularity, harmonic analysis, geometric measure theory
MSC: 35Q30, 35B65, 42B20, 28A78
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.TheoremA
public import LeanPool.CaffarelliKohnNirenberg.Statements.TheoremB
public import LeanPool.CaffarelliKohnNirenberg.Statements.TheoremC
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearFlowSuitable
public import LeanPool.CaffarelliKohnNirenberg.Witnesses.TrivialSolution

/-!
# Caffarelli–Kohn–Nirenberg partial regularity

Imported from Scott Armstrong and Vlad Vicol, upstream commit
`635fa6376aa3d46ae5251cb1d276a8589163f332`, Apache-2.0.
-/
