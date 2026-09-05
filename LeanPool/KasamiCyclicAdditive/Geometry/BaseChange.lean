/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Geometry.PointFrobenius
import LeanPool.KasamiCyclicAdditive.Geometry.IsogenyFactor

/-!
# Base change of points along a field extension

`basePt K F : E(K) →+ E(F)` is the group homomorphism induced by `algebraMap K F`
on points of the Fermat cubic, built the same way as `frobPt` (via
`WeierstrassCurve.Affine.Point.baseChange` and `curveCast`). It commutes with
`frobPt` (`basePt_frobPt`), which is exactly the naturality needed to transport
the `G`-preimage identity from `E(K)` to `E(F) = E(AlgebraicClosure K)`.
-/

namespace KasamiCyclicAdditive.PointFrobenius

open WeierstrassCurve KasamiCyclicAdditive.FermatCubic

variable {K F : Type*} [Field K] [DecidableEq K] [CharP K 2]
  [Field F] [DecidableEq F] [CharP F 2] [Algebra K F]

/-- The group homomorphism `E(K) →+ E(F)` induced by `algebraMap K F`. -/
noncomputable def basePt (K F : Type*) [Field K] [DecidableEq K]
    [Field F] [DecidableEq F] [Algebra K F] :
    (fer K).toAffine.Point →+ (fer F).toAffine.Point :=
  (curveCast (ferZ_baseChange (K := F))).toAddMonoidHom.comp
    ((WeierstrassCurve.Affine.Point.baseChange (W' := ferZ) K F).comp
      (curveCast (ferZ_baseChange (K := K))).symm.toAddMonoidHom)

omit [CharP K 2] [CharP F 2] in
/-- `basePt` sends an affine point to the point with base-changed coordinates. -/
lemma basePt_some {x y : K} (hns : (fer K).toAffine.Nonsingular x y)
    (hns2 : (fer F).toAffine.Nonsingular (algebraMap K F x) (algebraMap K F y)) :
    basePt K F (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns2 := by
  rw [basePt]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    curveCast_symm_some]
  rw [show WeierstrassCurve.Affine.Point.baseChange (W' := ferZ) K F
      = WeierstrassCurve.Affine.Point.map (Algebra.ofId K F) from rfl,
    WeierstrassCurve.Affine.Point.map_some, curveCast_some]
  simp only [Algebra.ofId_apply]

/-- `basePt` maps affine Fermat points to affine Fermat points. -/
lemma basePt_pt {w t : K} (h : w ^ 3 + t ^ 3 = 1) :
    basePt K F (pt w t h) = pt (algebraMap K F w) (algebraMap K F t)
      (by rw [← map_pow, ← map_pow, ← map_add, h, map_one]) := by
  have hx : algebraMap K F ((w + t)⁻¹) = (algebraMap K F w + algebraMap K F t)⁻¹ := by
    rw [map_inv₀, map_add]
  have hy :
      algebraMap K F (w * (w + t)⁻¹) =
        algebraMap K F w * (algebraMap K F w + algebraMap K F t)⁻¹ := by
    rw [map_mul, hx]
  have hns2 :
      (fer F).toAffine.Nonsingular (algebraMap K F ((w + t)⁻¹))
          (algebraMap K F (w * (w + t)⁻¹)) := by
    rw [hx, hy]
    exact chart_nonsingular (by rw [← map_pow, ← map_pow, ← map_add, h, map_one])
  rw [pt, basePt_some (chart_nonsingular h) hns2, pt]
  refine some_eq_some _ _ ?_ ?_ <;> simp [hx, hy]

/-- `basePt` maps points at infinity to points at infinity. -/
lemma basePt_ptInf {a : K} (ha : a ^ 3 = 1) :
    basePt K F (ptInf a ha) = ptInf (algebraMap K F a) (by rw [← map_pow, ha, map_one]) := by
  by_cases ha1 : a = 1
  · subst ha1
    simp [ptInf, map_one]
  · have ha1' : algebraMap K F a ≠ 1 := by
      intro hc
      exact ha1 ((algebraMap K F).injective (by rw [hc, map_one]))
    have hns2 : (fer F).toAffine.Nonsingular (algebraMap K F (0 : K)) (algebraMap K F a) := by
      rw [map_zero]
      exact inf_nonsingular (K := F)
        (cube_root_rel (a := algebraMap K F a) (by rw [← map_pow, ha, map_one]) ha1')
    rw [ptInf_ne_one ha ha1, basePt_some (inf_nonsingular (cube_root_rel ha ha1)) hns2,
      ptInf_ne_one _ ha1']
    exact some_eq_some _ _ (map_zero (algebraMap K F)) rfl

/-- **Naturality of `basePt` with respect to Frobenius.** -/
theorem basePt_frobPt (x : (fer K).toAffine.Point) :
    basePt K F (frobPt K x) = frobPt F (basePt K F x) := by
  rcases point_repr x with rfl | ⟨a, ha, rfl⟩ | ⟨w, t, h, rfl⟩
  · simp
  · rw [frobPt_ptInf ha, basePt_ptInf, basePt_ptInf,
      frobPt_ptInf (by rw [← map_pow, ha, map_one])]
    congr 1
    rw [map_pow]
  · rw [frobPt_pt h, basePt_pt, basePt_pt,
      frobPt_pt (by rw [← map_pow, ← map_pow, ← map_add, h, map_one])]
    refine pt_congr _ _ ?_ ?_ <;> rw [map_pow]

/-- **Naturality of `basePt` with respect to `gMap`.** -/
theorem basePt_gMap (a b : ℤ) (x : (fer K).toAffine.Point) :
    basePt K F (Isogeny.gMap (frobPt K) a b x)
      = Isogeny.gMap (frobPt F) a b (basePt K F x) := by
  simp only [Isogeny.gMap, map_sub, map_zsmul, basePt_frobPt]

/-- `basePt` commutes with `t3`. -/
theorem basePt_t3 : basePt K F (t3 K) = t3 F := by
  rw [t3, t3, basePt_pt]
  refine pt_congr _ _ ?_ ?_ <;> simp

end KasamiCyclicAdditive.PointFrobenius
