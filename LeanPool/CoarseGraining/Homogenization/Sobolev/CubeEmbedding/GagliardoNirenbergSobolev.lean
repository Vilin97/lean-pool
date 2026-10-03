/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import LeanPool.CoarseGraining.Homogenization.Ambient.Basic

/-! # Gagliardo Nirenberg Sobolev -/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal NNReal

/-!
# Gagliardo–Nirenberg–Sobolev at the ambient `Vec d`

Instantiates mathlib's Gagliardo–Nirenberg–Sobolev inequality
(`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`) at the ambient
`Vec d = Fin d → ℝ` with Lebesgue `volume`, codomain `ℝ`, `p = 2`, and target
the critical exponent `2* = 2d/(d−2)`.  It records that `Vec d` carries every
typeclass the inequality needs (finite-dimensional, Borel, Haar `volume`)
without any detour through `EuclideanSpace`/`PiLp`, that
`Module.finrank ℝ (Vec d) = d`, and the exponent bookkeeping
`1/2* = 1/2 − 1/d` for `d ≥ 3`.

This is the form fed to each smooth compactly supported approximant in the cube
Sobolev embedding.
-/

noncomputable section

/-- The critical Sobolev exponent `2* = 2d/(d−2)`, as an `ℝ≥0`.
For `d ≥ 3` this is a genuine exponent `> 2`. -/
def twoStar (d : ℕ) : ℝ≥0 := (2 * d) / (d - 2)

/-- `Vec d` has finite rank `d` (sanity fact used to discharge the GNS
finrank side-conditions). -/
theorem finrank_vec (d : ℕ) : Module.finrank ℝ (Homogenization.Vec d) = d := by
  simp [Homogenization.Vec]

/-- **Gagliardo–Nirenberg–Sobolev at `Vec d`.**
For `d ≥ 3` and a `C¹`, compactly supported real function `u` on `Vec d`, the
`L^{2*}` norm of `u` (w.r.t. Lebesgue `volume`) is controlled by the `L²` norm
of its Fréchet derivative, with the mathlib GNS constant.

This is the form invoked on each smooth compactly supported approximant in the
reflection route.  It certifies the exponent arithmetic `1/2* = 1/2 − 1/d` and
that `Vec d` satisfies every hypothesis of `eLpNorm_le_eLpNorm_fderiv_of_eq`
with no `EuclideanSpace` routing. -/
theorem gns_contDiff_compactSupport
    {d : ℕ} (hd : 3 ≤ d) {u : Homogenization.Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u) :
    eLpNorm u (twoStar d) (volume : Measure (Homogenization.Vec d))
      ≤ SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Homogenization.Vec d)) (2 : ℝ≥0)
        * eLpNorm (fderiv ℝ u) 2 (volume : Measure (Homogenization.Vec d)) := by
  have hfr : Module.finrank ℝ (Homogenization.Vec d) = d := finrank_vec d
  refine eLpNorm_le_eLpNorm_fderiv_of_eq volume hu h2u (p := 2) (p' := twoStar d)
    (by norm_num) (by rw [hfr]; omega) ?_
  rw [hfr]
  -- exponent bookkeeping: (2*)⁻¹ = 2⁻¹ − d⁻¹
  have hdle : (2 : ℝ≥0) ≤ (d : ℝ≥0) := by exact_mod_cast (by omega : 2 ≤ d)
  have hd3 : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 3 ≤ d)
  have hpos : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  rw [twoStar, NNReal.coe_inv, NNReal.coe_div, NNReal.coe_sub hdle]
  push_cast
  field_simp

end

end Homogenization
