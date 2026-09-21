/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarsePoincareRHS
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.WeakFluxRHS
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseFluxResponseRHS
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.EnergyRHS

/-! # Inhomogeneous -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Section 3.2: Inhomogeneous equations

This file bundles the public contract packages for all of Chapter 3.2.

## Audit tag

Claim: provide the single Chapter 3.2 aggregate package by bundling the
canonical inhomogeneous theorem packages.

Downstream target: Ch5 and other note-facing consumers that need the whole
inhomogeneous toolkit.  This file should only assemble listed component
packages, not introduce alternate component theories.
-/

/-- Public aggregate package for the inhomogeneous estimates of Chapter 3.2. -/
structure InhomogeneousEquationsTheory (d : ℕ) [NeZero d] : Prop where
  coarsePoincareRHS : CoarsePoincareRHSTheory d
  coarseCaccioppoliRHS : CoarseCaccioppoliRHSTheory d
  weakFluxRHS : WeakFluxRHSTheory d
  coarseFluxResponseRHS : CoarseFluxResponseRHSTheory d
  energyConsequencesRHS : EnergyConsequencesRHSTheory d

/-- Assemble the Chapter 3.2 aggregate package from its component theorem
packages. -/
private theorem inhomogeneousEquationsTheory_of_components
    {d : ℕ} [NeZero d]
    (coarsePoincareRHS : CoarsePoincareRHSTheory d)
    (coarseCaccioppoliRHS : CoarseCaccioppoliRHSTheory d)
    (weakFluxRHS : WeakFluxRHSTheory d)
    (coarseFluxResponseRHS : CoarseFluxResponseRHSTheory d)
    (energyConsequencesRHS : EnergyConsequencesRHSTheory d) :
    InhomogeneousEquationsTheory d where
  coarsePoincareRHS := coarsePoincareRHS
  coarseCaccioppoliRHS := coarseCaccioppoliRHS
  weakFluxRHS := weakFluxRHS
  coarseFluxResponseRHS := coarseFluxResponseRHS
  energyConsequencesRHS := energyConsequencesRHS

/-- Public Chapter 3.2 aggregate package. -/
theorem inhomogeneousEquationsTheory
    {d : ℕ} [NeZero d] :
    InhomogeneousEquationsTheory d :=
  inhomogeneousEquationsTheory_of_components
    coarsePoincareRHSTheory
    coarseCaccioppoliRHSTheory
    weakFluxRHSTheory
    coarseFluxResponseRHSTheory
    energyConsequencesRHSTheory

end Ch03
end Book
end Homogenization
