/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceLaw
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.RestrictionLaw

/-!
# Canonical Chapter 4 source laws

Unprefixed Chapter 4 law names denote the exact coarse-source, integral-local
semantics. The separate pointwise-restriction/sup-metric engineering lane is
exposed through the `Restriction*` names imported from `RestrictionLaw`.
-/

@[expose] public section

namespace Homogenization.Book.Ch04

/-- A canonical Chapter 4 law on the exact coarse source carrier. -/
abbrev CoeffLaw (d : ℕ) := SourceCoeffLaw d

/-- The canonical coarse-source stationarity assumption. -/
abbrev StationaryLaw {d : ℕ} (P : CoeffLaw d) := SourceStationaryLaw P

/-- The canonical coarse-source Euclidean unit-range assumption. -/
abbrev UnitRangeDependentLaw {d : ℕ} (P : CoeffLaw d) := SourceUnitRangeDependentLaw P

/-- The canonical coarse-source joint isotropy and adjoint-invariance assumption. -/
abbrev IsotropicAndAdjointInvariantLaw {d : ℕ} (P : CoeffLaw d) :=
  SourceIsotropicAndAdjointInvariantLaw P

/-- The canonical coarse-source structural law assumptions. -/
abbrev StructuralLaw {d : ℕ} (P : CoeffLaw d) := SourceStructuralLaw P

namespace StructuralLaw

/-- Access the canonical stationarity field. -/
theorem stationary {d : ℕ} {P : CoeffLaw d} (hP : StructuralLaw P) :
    StationaryLaw P :=
  SourceStructuralLaw.stationary hP

/-- Access the canonical unit-range field. -/
theorem unit_range {d : ℕ} {P : CoeffLaw d} (hP : StructuralLaw P) :
    UnitRangeDependentLaw P :=
  SourceStructuralLaw.unit_range hP

/-- Access the canonical joint isotropy and adjoint-invariance field. -/
theorem isotropic_and_adjoint_invariant {d : ℕ} {P : CoeffLaw d} (hP : StructuralLaw P) :
    IsotropicAndAdjointInvariantLaw P :=
  SourceStructuralLaw.isotropic_and_adjoint_invariant hP

end StructuralLaw

end Homogenization.Book.Ch04
