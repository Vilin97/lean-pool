/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspSmoothMembership

/-!
# Algebraic carrier for smooth Euclidean fractional-Sobolev tests

This module supplies the pointwise real vector-space structure on globally
smooth test fields.  The subsequent completed-dual graph will map this carrier
to two `L^p` components once the separate diagonal-singularity integrability
lemma establishes that every smooth test has finite Gagliardo seminorm.
-/

@[expose] public section

namespace Homogenization

noncomputable section

namespace CubeEuclideanWspSmoothTest

/-- Smooth test fields are determined by their pointwise vector fields. -/
@[ext]
theorem ext {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} {h k : CubeEuclideanWspSmoothTest Q s p}
    (hfield : h.toField = k.toField) : h = k := by
  cases h
  cases k
  cases hfield
  rfl

instance {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} : Zero (CubeEuclideanWspSmoothTest Q s p) where
  zero :=
    { toField := 0
      contDiff := contDiff_const }

instance {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} : Add (CubeEuclideanWspSmoothTest Q s p) where
  add h k :=
    { toField := h.toField + k.toField
      contDiff := h.contDiff.add k.contDiff }

instance {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} : Neg (CubeEuclideanWspSmoothTest Q s p) where
  neg h :=
    { toField := -h.toField
      contDiff := h.contDiff.neg }

instance {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} : Sub (CubeEuclideanWspSmoothTest Q s p) where
  sub h k := h + -k

instance {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} : AddCommGroup (CubeEuclideanWspSmoothTest Q s p) where
  add_assoc h k l := by
    apply ext
    funext x
    exact add_assoc _ _ _
  zero_add h := by
    apply ext
    funext x
    exact zero_add _
  add_zero h := by
    apply ext
    funext x
    exact add_zero _
  neg_add_cancel h := by
    apply ext
    funext x
    exact neg_add_cancel _
  add_comm h k := by
    apply ext
    funext x
    exact add_comm _ _
  sub_eq_add_neg h k := rfl
  nsmul := nsmulRec
  nsmul_zero := by intro h; rfl
  nsmul_succ := by intro n h; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intro h; rfl
  zsmul_succ' := by intro n h; rfl
  zsmul_neg' := by intro n h; rfl

instance {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} : SMul ℝ (CubeEuclideanWspSmoothTest Q s p) where
  smul c h :=
    { toField := c • h.toField
      contDiff := h.contDiff.const_smul c }

instance {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} : Module ℝ (CubeEuclideanWspSmoothTest Q s p) where
  one_smul h := by
    apply ext
    funext x
    exact one_smul ℝ (h.toField x)
  mul_smul c d h := by
    apply ext
    funext x
    exact mul_smul c d (h.toField x)
  smul_zero c := by
    apply ext
    funext x
    exact smul_zero c
  smul_add c h k := by
    apply ext
    funext x
    exact smul_add c (h.toField x) (k.toField x)
  add_smul c d h := by
    apply ext
    funext x
    exact add_smul c d (h.toField x)
  zero_smul h := by
    apply ext
    funext x
    exact zero_smul ℝ (h.toField x)

@[simp]
theorem toField_zero {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} :
    ((0 : CubeEuclideanWspSmoothTest Q s p).toField) = 0 := rfl

@[simp]
theorem toField_add {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} (h k : CubeEuclideanWspSmoothTest Q s p) :
    (h + k).toField = h.toField + k.toField := rfl

@[simp]
theorem toField_neg {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} (h : CubeEuclideanWspSmoothTest Q s p) :
    (-h).toField = -h.toField := rfl

@[simp]
theorem toField_smul {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} (c : ℝ) (h : CubeEuclideanWspSmoothTest Q s p) :
    (c • h).toField = c • h.toField := rfl

/-- The exact fractional-Sobolev field represented by a smooth test.

This is the source-facing graph map: it changes neither the pointwise field nor
either constituent of the approved full `W^(s,p)` norm.  Completion and dual
identification remain deliberately outside this module. -/
noncomputable def toCubeEuclideanWspField {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) : CubeEuclideanWspField Q s p where
  toField := h.toField
  euclideanMemLp := euclideanMemLp_of_continuous Q p.exponent h.contDiff.continuous
  euclideanMemWsp := h.memCubeEuclideanWsp

@[simp]
theorem toCubeEuclideanWspField_toField {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    h.toCubeEuclideanWspField.toField = h.toField := rfl

/-- The graph representative has exactly the original Gagliardo seminorm. -/
theorem toCubeEuclideanWspField_eSeminorm_eq {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    cubeEuclideanWspESeminorm Q s p h.toCubeEuclideanWspField.toField =
      cubeEuclideanWspESeminorm Q s p h.toField := rfl

/-- The graph representative has exactly the approved full `W^(s,p)` norm. -/
theorem toCubeEuclideanWspField_fullENorm_eq {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    cubeEuclideanWspFullENorm Q s p h.toCubeEuclideanWspField.toField =
      cubeEuclideanWspFullENorm Q s p h.toField := rfl

end CubeEuclideanWspSmoothTest

end

end Homogenization
