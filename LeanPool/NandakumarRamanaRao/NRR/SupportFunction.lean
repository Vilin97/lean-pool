/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunction
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionBasic
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionContinuity
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionTransform
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Width
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.WidthContinuity
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.WidthIdentities
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarCircle

/-!
# `NRR.SupportFunction` — public support-function and width API

This compatibility module re-exports the implemented convex-body support function and width under
stable public names. All substantive proofs live under `NRR.Geometry.ConvexBody`.
-/

open scoped RealInnerProductSpace

namespace NRR.Geometry.ConvexBody

/-- **Support function** (compatibility alias). `supportFn K u = h_K(u) = ⨆ x ∈ K, ⟪x, u⟫`. -/
noncomputable def supportFn (K : ConvexBody Plane) (u : Plane) : ℝ :=
  supportFunction K u

/-- **Width** (compatibility alias). `width K u = w_K(u) = h_K(u) + h_K(-u)`. -/
noncomputable def width (K : ConvexBody Plane) (u : Plane) : ℝ :=
  widthFunction K u

/-- Unfolding lemma for the `supportFn` alias. -/
theorem supportFn_eq (K : ConvexBody Plane) (u : Plane) :
    K.supportFn u = supportFunction K u := rfl

/-- Unfolding lemma for the `width` alias. -/
theorem width_eq (K : ConvexBody Plane) (u : Plane) :
    K.width u = widthFunction K u := rfl

/-- The supremum defining `supportFn` is attained on the compact body. -/
theorem exists_supportFn_eq (K : ConvexBody Plane) (u : Plane) :
    ∃ x ∈ (K : Set Plane), K.supportFn u = ⟪x, u⟫ := by
  obtain ⟨x, hx, hxeq⟩ := K.exists_supportPoint u
  exact ⟨x, hx, hxeq.symm⟩

/-- Positive homogeneity of the support function. -/
theorem supportFn_smul (K : ConvexBody Plane) {c : ℝ} (hc : 0 ≤ c) (u : Plane) :
    K.supportFn (c • u) = c * K.supportFn u :=
  K.supportFunction_smul_direction_of_nonneg hc u

/-- Subadditivity of the support function. -/
theorem supportFn_add_le (K : ConvexBody Plane) (u v : Plane) :
    K.supportFn (u + v) ≤ K.supportFn u + K.supportFn v :=
  K.supportFunction_add_direction_le u v

/-- The support function is convex in the direction `u`
(from positive homogeneity and subadditivity). -/
theorem convexOn_supportFn (K : ConvexBody Plane) :
    ConvexOn ℝ Set.univ K.supportFn := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb _ => ?_⟩
  calc K.supportFn (a • u + b • v)
      ≤ K.supportFn (a • u) + K.supportFn (b • v) := K.supportFn_add_le _ _
    _ = a • K.supportFn u + b • K.supportFn v := by
        rw [K.supportFn_smul ha, K.supportFn_smul hb, smul_eq_mul, smul_eq_mul]

/-- The support function is continuous in the direction `u`. -/
theorem continuous_supportFn (K : ConvexBody Plane) : Continuous K.supportFn :=
  K.continuous_supportFunction

/-- Monotonicity of the support function under inclusion of bodies. -/
theorem supportFn_mono {K L : ConvexBody Plane} (h : (K : Set Plane) ⊆ (L : Set Plane))
    (u : Plane) :
    K.supportFn u ≤ L.supportFn u :=
  supportFunction_mono h u

/-- **Half-space inclusion.** `K` is contained in the intersection of all its supporting
half-spaces. (The reverse inclusion, i.e. exact reconstruction, requires a separation theorem
and is not claimed here.) -/
theorem subset_iInter_support_halfspace (K : ConvexBody Plane) :
    (K : Set Plane) ⊆ ⋂ u : Plane, {x : Plane | ⟪x, u⟫ ≤ K.supportFn u} := by
  intro x hx
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  intro u
  exact K.inner_le_supportFunction hx

/-- The width functional is continuous in the direction. -/
theorem continuous_width (K : ConvexBody Plane) : Continuous K.width :=
  K.continuous_widthFunction

/-- The width is nonnegative. -/
theorem width_nonneg (K : ConvexBody Plane) (u : Plane) : 0 ≤ K.width u :=
  K.widthFunction_nonneg u

/-- Width is monotone under inclusion of bodies. -/
theorem width_mono {K L : ConvexBody Plane} (h : (K : Set Plane) ⊆ (L : Set Plane)) (u : Plane) :
    K.width u ≤ L.width u :=
  widthFunction_mono h u

-- The stronger equality statement
-- `eq_iInter_halfspace : (K : Set E2) = ⋂ u, {x | ⟪u, x⟫ ≤ K.supportFn u}`.
-- That equality is the exact reconstruction of `K` as the intersection of its supporting
-- half-spaces; the reverse inclusion `⋂ … ⊆ K` needs the separating-hyperplane theorem, which
-- is not yet available in this layer. In this compatibility layer we only assert the easy
-- inclusion `subset_iInter_support_halfspace` above, and do not claim the equality.

end NRR.Geometry.ConvexBody
