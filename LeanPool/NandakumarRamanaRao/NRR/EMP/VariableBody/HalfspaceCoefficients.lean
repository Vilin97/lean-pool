/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Basic
import LeanPool.NandakumarRamanaRao.NRR.PowerDiagram.CellAreaContinuityWeights
import LeanPool.NandakumarRamanaRao.NRR.ConfigurationSpace

/-!
# `NRR.EMP.VariableBody.HalfspaceCoefficients` — moving halfspace coefficients

For a variable planar body `C : BodySpace K A`, a configuration of sites `s : Config n`, and a
weight vector `w : Fin n → ℝ`, the restricted power cell of site `i` is the body `C` intersected
with finitely many closed lower halfspaces. The `j`‑th halfspace has

* normal `sepNormal s i j = 2 • (sⱼ - sᵢ)`, depending only on the sites, and
* offset `sepOffset s w i j = ‖sⱼ‖² - ‖sᵢ‖² - wⱼ + wᵢ`, depending affinely on sites and weights.

These are thin wrappers over the fixed-site coefficients `PowerDiagram.sepNormal` and
`PowerDiagram.sepOffset` evaluated at `s.pts`. Their continuity in the configuration (for the
normal) and jointly in configuration and weights (for the offset) follows from continuity of the
site map `Config.continuous_pts`. The off-diagonal normals are nonzero by injectivity of the sites.

The cell-algebra identities re-express `cellSet hA C s w i` as the parent body `C.body`
intersected with the intersection of these halfspaces, both over all `j` and over the off-diagonal
`j ≠ i` (the diagonal term is the whole plane and drops out). Keeping the parent as `C.body` lets
later indicator-convergence arguments apply the subbody membership-stability theorem directly.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody
open scoped RealInnerProductSpace

namespace NRR.EMP.VariableBody

variable {K : Geometry.ConvexBody Plane} {A : ℝ} {n : ℕ} (hA : 0 < A)

/-- The **separating normal** of the pair `(i, j)` for a configuration `s`, as the fixed-site
separating normal `PowerDiagram.sepNormal` evaluated at the sites `s.pts`. -/
noncomputable def sepNormal (s : Config n) (i j : Fin n) : Plane :=
  PowerDiagram.sepNormal s.pts i j

/-- The **separating offset** of the pair `(i, j)` for a configuration `s` and weights `w`, as the
fixed-site separating offset `PowerDiagram.sepOffset` evaluated at the sites `s.pts`. -/
noncomputable def sepOffset (s : Config n) (w : Fin n → ℝ) (i j : Fin n) : ℝ :=
  PowerDiagram.sepOffset s.pts w i j

/-- The separating normal varies continuously with the configuration. -/
theorem continuous_sepNormal (i j : Fin n) :
    Continuous fun s : Config n => sepNormal s i j := by
  unfold sepNormal PowerDiagram.sepNormal
  have hj : Continuous fun s : Config n => s.pts j :=
    (continuous_apply j).comp Config.continuous_pts
  have hi : Continuous fun s : Config n => s.pts i :=
    (continuous_apply i).comp Config.continuous_pts
  exact (hj.sub hi).const_smul (2 : ℝ)

/-- The separating offset varies continuously with the configuration and the weights jointly. -/
theorem continuous_sepOffset (i j : Fin n) :
    Continuous fun z : Config n × (Fin n → ℝ) =>
      sepOffset z.1 z.2 i j := by
  unfold sepOffset PowerDiagram.sepOffset
  have hpts : Continuous fun z : Config n × (Fin n → ℝ) => z.1.pts :=
    Config.continuous_pts.comp continuous_fst
  have hj : Continuous fun z : Config n × (Fin n → ℝ) => z.1.pts j :=
    (continuous_apply j).comp hpts
  have hi : Continuous fun z : Config n × (Fin n → ℝ) => z.1.pts i :=
    (continuous_apply i).comp hpts
  have hwj : Continuous fun z : Config n × (Fin n → ℝ) => z.2 j :=
    (continuous_apply j).comp continuous_snd
  have hwi : Continuous fun z : Config n × (Fin n → ℝ) => z.2 i :=
    (continuous_apply i).comp continuous_snd
  exact (((hj.norm.pow 2).sub (hi.norm.pow 2)).sub hwj).add hwi

/-- Off-diagonal separating normals are nonzero, from injectivity of the sites. -/
theorem sepNormal_ne_zero
    (s : Config n) {i j : Fin n} (hij : i ≠ j) :
    sepNormal s i j ≠ 0 :=
  PowerDiagram.sepNormal_ne_zero_of_injective s.pts s.injective_pts hij

/-- **Full halfspace representation.** The restricted power cell of site `i` inside the variable
body `C` equals the parent body `C.body` intersected with the closed lower halfspaces over all
`j`. -/
theorem cellSet_eq_iInter_halfspace
    (C : BodySpace K A) (s : Config n)
    (w : Fin n → ℝ) (i : Fin n) :
    cellSet hA C s w i =
      (C.body : Set Plane) ∩
        ⋂ j, Geometry.lowerClosedHalfspace
          (sepNormal s i j) (sepOffset s w i j) := by
  simp only [cellSet_def, PowerDiagram.bodyCellSet_eq_finiteHalfspaceIntersection,
    finiteHalfspaceIntersection, solidBody_carrier, sepNormal, sepOffset]

/-- **Off-diagonal halfspace representation.** The diagonal term `j = i` is the whole plane, so it
can be dropped, leaving the intersection over `j ≠ i`. -/
theorem cellSet_eq_offDiag_halfspaces
    (C : BodySpace K A) (s : Config n)
    (w : Fin n → ℝ) (i : Fin n) :
    cellSet hA C s w i =
      (C.body : Set Plane) ∩
        ⋂ j : {j : Fin n // j ≠ i},
          Geometry.lowerClosedHalfspace
            (sepNormal s i j.1) (sepOffset s w i j.1) := by
  simp only [cellSet_def, PowerDiagram.bodyCellSet_eq_finiteHalfspaceIntersection_offDiag,
    finiteHalfspaceIntersection, solidBody_carrier, sepNormal, sepOffset]

end NRR.EMP.VariableBody
