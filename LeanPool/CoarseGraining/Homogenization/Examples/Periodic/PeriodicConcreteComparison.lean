/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Examples.Periodic.MField

/-!
# Concrete periodic comparison corollary

**Proves.** `periodicConcrete_comparison` — the periodic comparison estimate for
the *explicit* scalar field `a(x) = m(x) • I`, where
`m(x) = d + 2 + ∑ i, cos (2 * π * x i)` (defined and shown periodic, isotropic,
adjoint-invariant, and uniformly elliptic with `λ = 2`, `Λ = 2d + 2` in `MField`).
It instantiates `periodicGeneral_comparison` at this field.

**Comparator.** `Audit/PeriodicConcrete` checks a Mathlib-only restatement of this
theorem against the proof below.  See `Audit/README.md` for the comparator map.

**Progression.** abstract theorem (`Audit/QuenchedComparison`) → general periodic
(`PeriodicGeneralComparison`, `Audit/PeriodicGeneral`) → *explicit field (this
file)* → classical data (`PeriodicSmoothComparison`, `Audit/PeriodicSmooth`).
-/

namespace Homogenization
namespace Examples
namespace Periodic

open MeasureTheory
open scoped ENNReal

noncomputable section

/--
Fixed-exponent quenched homogenization comparison for the explicit periodic
coefficient field `mFieldCoeff`.  The constants are chosen before the dimension
data and before the deterministic Dirac setup.
-/
theorem periodicConcrete_comparison {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ (two_le_dim : 2 ≤ d),
        let Lam : ℝ := 2 * (d : ℝ) + 2
        let S : Book.MainResults.Setup d :=
          periodicSetup two_le_dim (mFieldReg (d := d)) 2 Lam
            mFieldCoeff_periodic mFieldCoeff_isotropic mFieldCoeff_adjointInvariant
            (by norm_num)
            (by
              nlinarith [show 0 ≤ (d : ℝ) by exact_mod_cast Nat.zero_le d])
            (fun Q => mFieldReg_aeeEllipticOn (measurableSet_openCubeSet Q))
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : RegCoeffField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ aω ∂S.P,
              ∀ (ha : Book.Ch04.AELocallyUniformlyEllipticField aω)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : S.ComparisonPair aω ha m g),
                X aω ≤ (3 : ℝ) ^ m →
                Book.Ch03.Legacy.ForceSobolevRegularity
                  (Book.MainResults.originCube d m) Book.MainResults.fixedComparisonS g →
                S.comparisonDefect Book.MainResults.fixedComparisonS pair ≤
                  C * ((3 : ℝ) ^ m / X aω) ^ (-alpha) *
                    S.comparisonData Book.MainResults.fixedComparisonS pair := by
  obtain ⟨C, alpha, Cscale, hC, halpha, hCscale, hmain⟩ :=
    periodicGeneral_comparison (d := d)
  refine ⟨C, alpha, Cscale, hC, halpha, hCscale, ?_⟩
  intro two_le_dim
  exact hmain two_le_dim (mFieldReg (d := d)) 2 (2 * (d : ℝ) + 2)
    mFieldCoeff_periodic mFieldCoeff_isotropic mFieldCoeff_adjointInvariant
    (by norm_num)
    (by
      nlinarith [show 0 ≤ (d : ℝ) by exact_mod_cast Nat.zero_le d])
    (fun Q => mFieldReg_aeeEllipticOn (measurableSet_openCubeSet Q))

end

end Periodic
end Examples
end Homogenization
