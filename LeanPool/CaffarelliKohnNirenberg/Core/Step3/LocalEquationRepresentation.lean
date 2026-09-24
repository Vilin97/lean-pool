/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.SubordinatedCampanato
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian

/-!
# Local Equation Representation

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric


noncomputable section

namespace CKN.Core.Step3

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential

/-!
# Localized equation and heat-potential representation

The cutoff-tested S3 identity is the distribution-free entry point for the
local equation.  The source terms below are the paper's displayed formulas.
The pressure representation is recorded as a structural decomposition, while
the pointwise estimate is proved directly from the explicit heat kernels.
-/

def localizedVelocity (φ : ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z => φ z • u z

def localizedConvection (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) : ParabolicPoint → Vec3 :=
  fun z i => ∑ j, u z j * Du z i j

def localizedEquationG (φ : ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (f : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z => fun i =>
    timePartial φ z * u z i +
      spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i -
      φ z * localizedConvection u Du z i + φ z * f z i

def localizedEquationH (φ : ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) : Fin 3 → ParabolicPoint → Vec3 :=
  fun i z => (-2 * spatialPartial φ i z) • u z









end CKN.Core.Step3
