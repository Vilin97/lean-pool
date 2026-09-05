/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.IncidenceChart
import LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.RationalKernel

/-!
# Frobenius as a group endomorphism of the Fermat cubic, and its kernel

This file supplies the two pieces of infrastructure that the geometric
bridging statements of `Assembly/GeometricChain.lean` need but that no other
module provides.

1. **Frobenius as an endomorphism.**  `frobPt` is the squaring map `π` on
   `(fer K).toAffine.Point`, packaged as an `AddMonoidHom`.  It is obtained from
   Mathlib's `WeierstrassCurve.Affine.Point.map` applied to the Frobenius
   `x ↦ x ^ 2`, viewed as a `ℤ`-algebra map (every ring hom is one), together
   with the transport along `ferZ.baseChange K = fer K`.  The computation rules
   `frobPt_pt` and `frobPt_ptInf` say that `π` squares the coordinates in both
   charts of `FermatCubic`.

2. **The kernel dictionary.**  `isKernelPoint_iff` identifies
   `KasamiCyclicAdditive.FermatCubicFrobenius.IsKernelPoint` of
   `Geometry/FermatCubic/RationalKernel.lean` — a condition on homogeneous
   triples — with the group-theoretic condition `π^k P = -P`.  Combined with
   `KasamiCyclicAdditive.FermatCubicFrobenius.rational_kernel_odd` this gives
   `kernel_trivial_odd`: for odd `n` the map `1 + π^k` is injective on `E(K)`.

`point_repr` classifies the points of `E(K)`: every one is the origin, a point
at infinity `ptInf a`, or an affine Fermat point `pt w t`.  This is what lets
the two charts of `FermatCubic` be used exhaustively.
-/

namespace KasamiCyclicAdditive.PointFrobenius

open WeierstrassCurve KasamiCyclicAdditive.FermatCubic

/-! ## The Frobenius endomorphism -/

/-- The Fermat cubic in Weierstrass form over `ℤ`; `fer K` is its base change. -/
def ferZ : WeierstrassCurve ℤ := ⟨0, 0, 1, 0, 1⟩

variable {K : Type*} [Field K] [DecidableEq K] [CharP K 2]

omit [DecidableEq K] [CharP K 2] in
/-- `fer K` is the base change of `ferZ` along `ℤ → K`. -/
lemma ferZ_baseChange : ferZ.baseChange K = fer K := by
  simp [ferZ, fer, WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- Transport points along an equality of curves. -/
def curveCast {W W' : WeierstrassCurve K} (h : W = W') :
    W.toAffine.Point ≃+ W'.toAffine.Point := by
  subst h; exact AddEquiv.refl _

omit [CharP K 2] in
/-- `curveCast` leaves the coordinates of an affine point unchanged. -/
lemma curveCast_some {W W' : WeierstrassCurve K} (h : W = W') {x y : K}
    (hns : W.toAffine.Nonsingular x y) :
    curveCast h (Affine.Point.some _ _ hns) = Affine.Point.some _ _ (h ▸ hns) := by
  subst h; rfl

omit [CharP K 2] in
/-- The inverse of `curveCast` likewise leaves the coordinates unchanged. -/
lemma curveCast_symm_some {W W' : WeierstrassCurve K} (h : W = W') {x y : K}
    (hns : W'.toAffine.Nonsingular x y) :
    (curveCast h).symm (Affine.Point.some _ _ hns) = Affine.Point.some _ _ (h ▸ hns) := by
  subst h; rfl

/-- The Frobenius `x ↦ x ^ 2`, as a `ℤ`-algebra map. -/
private noncomputable def frobAlg (K : Type*) [Field K] [CharP K 2] : K →ₐ[ℤ] K :=
  (frobenius K 2).toIntAlgHom

omit [DecidableEq K] in
/-- `frobAlg` squares its argument. -/
private lemma frobAlg_apply (x : K) : frobAlg K x = x ^ 2 := rfl

/-- **Frobenius as a group endomorphism of `E(K)`.** -/
noncomputable def frobPt (K : Type*) [Field K] [DecidableEq K] [CharP K 2] :
    (fer K).toAffine.Point →+ (fer K).toAffine.Point :=
  (curveCast (ferZ_baseChange (K := K))).toAddMonoidHom.comp
    ((Affine.Point.map (W' := ferZ) (frobAlg K)).comp
      (curveCast (ferZ_baseChange (K := K))).symm.toAddMonoidHom)

/-- `π` squares both Weierstrass coordinates. -/
private lemma frobPt_some {x y : K} (hns : (fer K).toAffine.Nonsingular x y)
    (hns2 : (fer K).toAffine.Nonsingular (x ^ 2) (y ^ 2)) :
    frobPt K (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns2 := by
  rw [frobPt]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    curveCast_symm_some, Affine.Point.map_some, curveCast_some, frobAlg_apply]

/-- `π` squares both Fermat coordinates. -/
lemma frobPt_pt {w t : K} (h : w ^ 3 + t ^ 3 = 1) :
    frobPt K (pt w t h) = pt (w ^ 2) (t ^ 2) (frob_fermat h 1) := by
  have hsq : (w + t) ^ 2 = w ^ 2 + t ^ 2 := by
    linear_combination (w * t) * CharTwo.two_eq_zero (R := K)
  have hx : ((w + t)⁻¹) ^ 2 = (w ^ 2 + t ^ 2)⁻¹ := by rw [inv_pow, hsq]
  have hy : (w * (w + t)⁻¹) ^ 2 = w ^ 2 * (w ^ 2 + t ^ 2)⁻¹ := by rw [mul_pow, hx]
  have hns2 : (fer K).toAffine.Nonsingular (((w + t)⁻¹) ^ 2) ((w * (w + t)⁻¹) ^ 2) := by
    rw [hx, hy]
    simpa using chart_nonsingular (frob_fermat h 1)
  rw [pt, frobPt_some (chart_nonsingular h) hns2, pt]
  refine some_eq_some _ _ ?_ ?_ <;> simpa using ‹_›

/-- `π` squares the parameter of a point at infinity. -/
lemma frobPt_ptInf {a : K} (ha : a ^ 3 = 1) :
    frobPt K (ptInf a ha) = ptInf (a ^ 2) (by linear_combination (a ^ 3 + 1) * ha) := by
  by_cases ha1 : a = 1
  · subst ha1
    simp [ptInf, map_zero]
  · have ha21 : a ^ 2 ≠ 1 := by
      intro hc
      exact ha1 (by linear_combination ha - a * hc)
    have hns2 : (fer K).toAffine.Nonsingular ((0 : K) ^ 2) (a ^ 2) := by
      simpa using inf_nonsingular (cube_root_rel (by linear_combination (a ^ 3 + 1) * ha) ha21)
    rw [ptInf_ne_one ha ha1, ptInf_ne_one _ ha21,
      frobPt_some (inf_nonsingular (cube_root_rel ha ha1)) hns2]
    exact some_eq_some _ _ (by norm_num) rfl

omit [DecidableEq K] in
/-- Frobenius preserves the Weierstrass equation of `fer`. -/
private lemma weierstrass_eq_sq {x y : K} (h : y ^ 2 + y = x ^ 3 + 1) :
    (y ^ 2) ^ 2 + y ^ 2 = (x ^ 2) ^ 3 + 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (y ^ 2 + y + x ^ 3 + 1) * h + (x ^ 3 - y ^ 3) * h2

/-- **The CM relation.**  `fer` is defined over `𝔽₂`, where it has exactly three
points, so its trace of Frobenius is `a = 2 + 1 - 3 = 0` and `π² + 2 = 0` in the
endomorphism ring. -/
theorem frobPt_frobPt (P : (fer K).toAffine.Point) :
    frobPt K (frobPt K P) = (-2 : ℤ) • P := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rcases P with _ | @⟨x, y, hns⟩
  · rw [show (Affine.Point.zero : (fer K).toAffine.Point) = 0 from rfl]
    simp
  · have hxy : y ^ 2 + y = x ^ 3 + 1 := eq_of_nonsingular hns
    have hxy2 := weierstrass_eq_sq hxy
    have hns2 : (fer K).toAffine.Nonsingular (x ^ 2) (y ^ 2) := nonsingular_of_eq hxy2
    have hxy4 := weierstrass_eq_sq hxy2
    have hns4 : (fer K).toAffine.Nonsingular ((x ^ 2) ^ 2) ((y ^ 2) ^ 2) :=
      nonsingular_of_eq hxy4
    have hxy' : ¬(x = x ∧ y = (fer K).toAffine.negY x y) := fun h => Y_ne_negY x y h.2
    rw [frobPt_some hns hns2, frobPt_some hns2 hns4,
      show (-2 : ℤ) • (Affine.Point.some _ _ hns) =
          -(Affine.Point.some _ _ hns + Affine.Point.some _ _ hns) by
        rw [neg_smul, two_zsmul],
      Affine.Point.add_some hxy', Affine.Point.neg_some]
    refine some_eq_some _ _ ?_ ?_
    · rw [slope_self, addX_eq]
      linear_combination (-x) * h2
    · rw [negY_eq, addY_eq, slope_self, addX_eq]
      linear_combination (y ^ 2 + y + x ^ 3) * hxy + (-y ^ 3 - x ^ 3 - 1) * h2

/-! ## Iterated Frobenius -/

/-- `π` as an element of the endomorphism monoid, so that `π ^ k` is available. -/
noncomputable def frobEnd (K : Type*) [Field K] [DecidableEq K] [CharP K 2] :
    AddMonoid.End ((fer K).toAffine.Point) := frobPt K

/-- One step of the recursion for `π ^ k`. -/
private lemma frobEnd_pow_succ (k : ℕ) (P : (fer K).toAffine.Point) :
    (frobEnd K ^ (k + 1)) P = (frobEnd K ^ k) (frobPt K P) := by
  rw [pow_succ]
  rfl

/-- `π ^ k` raises both Fermat coordinates to the `2 ^ k`. -/
lemma frobEnd_pow_pt (k : ℕ) {w t : K} (h : w ^ 3 + t ^ 3 = 1) :
    (frobEnd K ^ k) (pt w t h) = pt (w ^ 2 ^ k) (t ^ 2 ^ k) (frob_fermat h k) := by
  induction k generalizing w t with
  | zero => simp
  | succ k ih =>
      rw [frobEnd_pow_succ, frobPt_pt h, ih]
      refine pt_congr _ _ ?_ ?_ <;> rw [← pow_mul, pow_succ']

/-- `π ^ k` raises the parameter of a point at infinity to the `2 ^ k`. -/
lemma frobEnd_pow_ptInf (k : ℕ) {a : K} (ha : a ^ 3 = 1) :
    (frobEnd K ^ k) (ptInf a ha) = ptInf (a ^ 2 ^ k) (by
      rw [← pow_mul, Nat.mul_comm, pow_mul, ha, one_pow]) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
      rw [frobEnd_pow_succ, frobPt_ptInf ha, ih]
      congr 1
      rw [← pow_mul, pow_succ']

/-! ## Classification of the points of `E(K)`

Every point is the origin, a point at infinity, or an affine Fermat point.  This
is what makes the two charts of `FermatCubic` exhaustive. -/

omit [DecidableEq K] in
/-- The affine Weierstrass chart produces a Fermat point away from `x = 0`. -/
private lemma fermat_of_weierstrass {x y : K} (hx : x ≠ 0)
    (h : y ^ 2 + y = x ^ 3 + 1) :
    (y / x) ^ 3 + ((y + 1) / x) ^ 3 = 1 := by
  rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 3 hx)]
  linear_combination h + (y ^ 3 + y ^ 2 + y + 1) * CharTwo.two_eq_zero (R := K)

/-- The two charts of `FermatCubic` cover `E(K)`. -/
theorem point_repr (P : (fer K).toAffine.Point) :
    P = 0 ∨ (∃ (a : K) (ha : a ^ 3 = 1), P = ptInf a ha) ∨
      (∃ (w t : K) (h : w ^ 3 + t ^ 3 = 1), P = pt w t h) := by
  induction P with
  | zero => exact Or.inl rfl
  | some x y hns =>
      have heq : y ^ 2 + y = x ^ 3 + 1 := eq_of_nonsingular hns
      by_cases hx : x = 0
      · subst hx
        have hy2 : y ^ 2 + y + 1 = 0 := by linear_combination heq + CharTwo.two_eq_zero (R := K)
        have hy3 : y ^ 3 = 1 := cube_root_of_rel hy2
        have hy1 : y ≠ 1 := by
          rintro rfl
          have hzz : (1 : K) = 0 := by linear_combination hy2 - CharTwo.two_eq_zero (R := K)
          exact one_ne_zero hzz
        refine Or.inr (Or.inl ⟨y, hy3, ?_⟩)
        rw [ptInf_ne_one hy3 hy1]
      · have hsum : y / x + (y + 1) / x = x⁻¹ := by
          rw [← add_div,
            show y + (y + 1) = 1 by linear_combination y * CharTwo.two_eq_zero (R := K), one_div]
        have hcurve := fermat_of_weierstrass hx heq
        refine Or.inr (Or.inr ⟨y / x, (y + 1) / x, hcurve, ?_⟩)
        rw [pt]
        refine some_eq_some _ _ ?_ ?_
        · rw [hsum, inv_inv]
        · rw [hsum, inv_inv]
          field_simp

/-- `E(K)` is finite when `K` is. -/
instance instFinitePoint [Finite K] : Finite ((fer K).toAffine.Point) := by
  refine Finite.of_injective
    (fun P => match P with
      | 0 => (none : Option (K × K))
      | @Affine.Point.some _ _ _ x y _ => some (x, y)) ?_
  rintro (_ | @⟨x₁, y₁, h₁⟩) (_ | @⟨x₂, y₂, h₂⟩) hEq
  all_goals simp_all

/-! ## The kernel of `1 + π^k`

`KasamiCyclicAdditive.FermatCubicFrobenius.IsKernelPoint` of
`Geometry/FermatCubic/RationalKernel.lean` is a statement about homogeneous
triples; on the affine chart it is exactly `π^k P = -P`. -/

/-- **The dictionary.**  For an affine Fermat point,
`Geometry/FermatCubic/RationalKernel.lean`'s triple condition
`IsKernelPoint k W T 1` is the group-theoretic statement `π^k P = -P`. -/
theorem isKernelPoint_iff {k : ℕ} {w t : K} (h : w ^ 3 + t ^ 3 = 1) :
    KasamiCyclicAdditive.FermatCubicFrobenius.IsKernelPoint k w t 1 ↔
      (frobEnd K ^ k) (pt w t h) = -(pt w t h) := by
  rw [neg_pt, frobEnd_pow_pt]
  constructor
  · rintro ⟨c, -, hw, ht, hc⟩
    rw [one_pow, mul_one] at hc
    subst hc
    exact pt_congr _ _ (by rw [hw, one_mul]) (by rw [ht, one_mul])
  · intro hEq
    obtain ⟨hw, ht⟩ := pt_inj hEq
    exact ⟨1, one_ne_zero, by rw [hw, one_mul], by rw [ht, one_mul], by norm_num⟩

/-- **Trivial rational kernel for odd `n`.**  The map `1 + π^k` is injective on
`E(K)`: its only zero is the origin.  This is
`KasamiCyclicAdditive.FermatCubicFrobenius.rational_kernel_odd` transported through the
dictionary. -/
theorem kernel_trivial_odd [Fintype K] {n k : ℕ} (hn : Odd n) (hkn : Nat.Coprime k n)
    (hcard : Fintype.card K = 2 ^ n) {P : (fer K).toAffine.Point}
    (hP : (frobEnd K ^ k) P + P = 0) : P = 0 := by
  rcases point_repr P with rfl | ⟨a, ha, rfl⟩ | ⟨w, t, h, rfl⟩
  · rfl
  · have ha1 : a = 1 :=
      KasamiCyclicAdditive.FermatCubicFrobenius.cube_root_eq_one_of_odd hn hcard ha
    subst ha1
    simp [ptInf]
  · exfalso
    have hneg : (frobEnd K ^ k) (pt w t h) = -(pt w t h) :=
      eq_neg_of_add_eq_zero_left hP
    have hker : KasamiCyclicAdditive.FermatCubicFrobenius.IsKernelPoint k w t 1 :=
      (isKernelPoint_iff h).mpr hneg
    have hpt : KasamiCyclicAdditive.FermatCubicFrobenius.IsPoint w t (1 : K) := by
      refine ⟨?_, by linear_combination h⟩
      rintro ⟨-, -, hc⟩
      exact one_ne_zero hc
    have := (KasamiCyclicAdditive.FermatCubicFrobenius.rational_kernel_odd hn hkn hcard hpt).mp hker
    exact one_ne_zero this.1

end KasamiCyclicAdditive.PointFrobenius
