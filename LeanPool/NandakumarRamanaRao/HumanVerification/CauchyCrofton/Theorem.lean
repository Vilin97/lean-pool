/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCrofton.PolygonCauchy
import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCrofton.PolygonApproximation
import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCrofton.HausdorffMonotonicity
import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCroftonStatement

/-!
# The Cauchy–Crofton bridge

Combining

* the polygon identity `hPerimeter P = cPerimeter P` for inscribed cyclic polygons,
* monotonicity of both perimeters,
* their common behaviour under dilations,
* and the inscribed approximation `r⁻¹ • K ⊆ P ⊆ K`,

a squeeze as `r ↓ 1` gives the Cauchy–Crofton identity

```
μH[1] (frontier K) = ENNReal.ofReal (perimeter K)
```

for every planar compact convex body with nonempty interior.
-/

open Set MeasureTheory NRR.Geometry
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace HumanVerification.CauchyCrofton

/-- The bridge, for a body containing the origin in its interior. -/
theorem hausdorffPerimeter_eq_cauchyPerimeter_of_zero_mem
    (K : Body) (h0 : (0 : Point2) ∈ interior (K : Set Point2)) :
    hPerimeter K = cPerimeter K := by
  have hkey : ∀ r : ℝ, 1 < r →
      hPerimeter K ≤ ENNReal.ofReal r * cPerimeter K ∧
      cPerimeter K ≤ ENNReal.ofReal r * hPerimeter K := by
    intro r hr
    have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
    obtain ⟨A, hA⟩ := exists_polygon_sandwich K h0 hr
    set P : Body := polyBody K A h0 with hP
    have hPK : (P : Set Point2) ⊆ (K : Set Point2) := by
      rw [hP, polyBody_carrier]
      exact polySet_subset (interior_subset h0)
    have hKrP : (K : Set Point2) ⊆ ((P.scalePos r hr0 : Body) : Set Point2) := by
      intro x hx
      rw [NRR.Geometry.ConvexBody.scalePos_carrier]
      refine ⟨r⁻¹ • x, ?_, ?_⟩
      · rw [hP, polyBody_carrier]
        exact hA ⟨x, hx, rfl⟩
      · show r • r⁻¹ • x = x
        rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    have hpoly : hPerimeter P = cPerimeter P := polygon_hPerimeter_eq_cPerimeter h0
    constructor
    · calc hPerimeter K ≤ hPerimeter (P.scalePos r hr0) := hPerimeter_mono hKrP
        _ = ENNReal.ofReal r * hPerimeter P := hPerimeter_scalePos P hr0
        _ = ENNReal.ofReal r * cPerimeter P := by rw [hpoly]
        _ ≤ ENNReal.ofReal r * cPerimeter K := mul_le_mul_right (cPerimeter_mono hPK) _
    · calc cPerimeter K ≤ cPerimeter (P.scalePos r hr0) := cPerimeter_mono hKrP
        _ = ENNReal.ofReal r * cPerimeter P := cPerimeter_scalePos P hr0
        _ = ENNReal.ofReal r * hPerimeter P := by rw [hpoly]
        _ ≤ ENNReal.ofReal r * hPerimeter K := mul_le_mul_right (hPerimeter_mono hPK) _
  have hfin : hPerimeter K ≠ ⊤ := by
    have h2 := (hkey 2 (by norm_num)).1
    refine ne_top_of_le_ne_top ?_ h2
    simp [ENNReal.mul_eq_top, cPerimeter_ne_top K]
  exact eq_of_forall_one_lt_mul hfin (cPerimeter_ne_top K)
    (fun r hr => (hkey r hr).1) (fun r hr => (hkey r hr).2)

/-- **Cauchy–Crofton**, in terms of the two perimeter functionals. -/
theorem hPerimeter_eq_cPerimeter (K : Body) :
    hPerimeter K = cPerimeter K := by
  obtain ⟨c, hc⟩ := K.interior_nonempty
  set K' : Body := K.translate (-c) with hK'
  have h0 : (0 : Point2) ∈ interior ((K' : Set Point2)) := by
    have himg : (fun x : Point2 => -c + x) '' interior (K : Set Point2)
        = interior ((fun x : Point2 => -c + x) '' (K : Set Point2)) := by
      simpa using (Homeomorph.addLeft (-c)).image_interior (K : Set Point2)
    rw [hK', NRR.Geometry.ConvexBody.translate_carrier, ← himg]
    exact ⟨c, hc, by abel_nf⟩
  have h1 : hPerimeter K' = cPerimeter K' :=
    hausdorffPerimeter_eq_cauchyPerimeter_of_zero_mem K' h0
  rwa [hK', hPerimeter_translate, cPerimeter_translate] at h1

/-- **Cauchy–Crofton.** The one-dimensional Hausdorff measure of the boundary of a planar
compact convex body with nonempty interior equals its Cauchy width-integral perimeter. -/
theorem hausdorffPerimeter_eq_cauchyPerimeter (K : NRR.Geometry.ConvexBody Point2) :
    (μH[1] : Measure Point2) (frontier (K : Set Point2))
      = ENNReal.ofReal (NRR.Geometry.ConvexBody.perimeter K) :=
  hPerimeter_eq_cPerimeter K

/-- Proposition-level form used by the human-verification transfer. -/
theorem cauchyCroftonStatement : HumanVerification.CauchyCroftonStatement := by
  intro K
  exact hausdorffPerimeter_eq_cauchyPerimeter K

end HumanVerification.CauchyCrofton
