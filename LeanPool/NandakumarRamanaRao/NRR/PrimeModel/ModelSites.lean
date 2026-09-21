/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.Model

/-!
# Site family and explicit parameter actions

The body and signed-interval coordinates are fixed; only the model point is moved by the prime
symmetry group. Named maps are used instead of global product-action instances.
-/

namespace NRR

open Geometry

variable {p : ℕ} {hp : Nat.Prime p}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}

namespace PrimeConfigurationModel

/-- The model configuration map as the compact site family used by the variable-body partition construction. -/
def sites (M : PrimeConfigurationModel hp) :
    EMP.VariableBody.SiteFamily M.Point p := M.toConfig

@[simp] theorem sites_apply (M : PrimeConfigurationModel hp) (x : M.Point) :
    M.sites x = M.toConfig x := rfl

 theorem sites_equivariant (M : PrimeConfigurationModel hp) :
    IsPrimeEquivariant (hp := hp) M.sites :=
  M.toConfig_equivariant

/-- Action on a body/model-point parameter, fixing the body. -/
def smulBodyPoint
    (M : PrimeConfigurationModel hp)
    (g : PrimeSymmetry hp)
    (z : BodySpace K A × M.Point) : BodySpace K A × M.Point :=
  (z.1, g • z.2)

/-- Action on a body/model-point/interval parameter, fixing body and interval. -/
def smulBodyPointInterval
    (M : PrimeConfigurationModel hp)
    (g : PrimeSymmetry hp)
    (z : (BodySpace K A × M.Point) × SignedInterval) :
    (BodySpace K A × M.Point) × SignedInterval :=
  ((z.1.1, g • z.1.2), z.2)

@[simp] theorem smulBodyPoint_one
    (M : PrimeConfigurationModel hp)
    (z : BodySpace K A × M.Point) :
    M.smulBodyPoint (1 : PrimeSymmetry hp) z = z := by
  ext <;> simp [smulBodyPoint]

 theorem smulBodyPoint_mul
    (M : PrimeConfigurationModel hp)
    (g h : PrimeSymmetry hp)
    (z : BodySpace K A × M.Point) :
    M.smulBodyPoint (g * h) z = M.smulBodyPoint g (M.smulBodyPoint h z) := by
  ext <;> simp [smulBodyPoint, mul_smul]

@[simp] theorem smulBodyPointInterval_one
    (M : PrimeConfigurationModel hp)
    (z : (BodySpace K A × M.Point) × SignedInterval) :
    M.smulBodyPointInterval (1 : PrimeSymmetry hp) z = z := by
  rcases z with ⟨⟨C, x⟩, t⟩
  simp [smulBodyPointInterval]

 theorem smulBodyPointInterval_mul
    (M : PrimeConfigurationModel hp)
    (g h : PrimeSymmetry hp)
    (z : (BodySpace K A × M.Point) × SignedInterval) :
    M.smulBodyPointInterval (g * h) z =
      M.smulBodyPointInterval g (M.smulBodyPointInterval h z) := by
  rcases z with ⟨⟨C, x⟩, t⟩
  simp [smulBodyPointInterval, mul_smul]

 theorem continuous_smulBodyPoint
    (M : PrimeConfigurationModel hp) (g : PrimeSymmetry hp) :
    Continuous (M.smulBodyPoint (K := K) (A := A) g) :=
  continuous_fst.prodMk ((M.continuous_smul g).comp continuous_snd)

 theorem continuous_smulBodyPointInterval
    (M : PrimeConfigurationModel hp) (g : PrimeSymmetry hp) :
    Continuous (M.smulBodyPointInterval (K := K) (A := A) g) :=
  ((continuous_fst.comp continuous_fst).prodMk
      ((M.continuous_smul g).comp (continuous_snd.comp continuous_fst))).prodMk
    continuous_snd

end PrimeConfigurationModel

end NRR
