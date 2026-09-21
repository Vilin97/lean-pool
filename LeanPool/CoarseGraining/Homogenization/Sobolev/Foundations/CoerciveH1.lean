/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.MeanZero
import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient

/-! # Coercive H1 -/

namespace Homogenization

/-!
# Coercive `H¹` Scaffolding

This file packages the first reusable coercive layer above the witness-based
`H1Function` API.

The key objects are:

- a gauge-fixed mean-zero carrier `H1MeanZeroFunction U`;
- typed `L²(U)` and `L²(U; ℝ^d)` realizations of `u` and `∇u`;
- a bundled coercive estimate on the mean-zero carrier.

The future bounded-open-convex Poincare theorem should produce
`H1CoerciveEstimate U` data, and the future Hodge proof should consume that
coercive layer rather than the raw witness structures directly.
-/

/-- Mean-zero `H¹(U)` functions, represented by a chosen `H¹` witness together
with the zero-average condition. -/
structure H1MeanZeroFunction {d : ℕ} (U : Set (Vec d)) where
  toH1Function : H1Function U
  meanZero : MeanZeroOn U toH1Function.toFun

namespace H1MeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)}

instance : Coe (H1MeanZeroFunction U) (H1Function U) where
  coe u := u.toH1Function

instance : CoeFun (H1MeanZeroFunction U) (fun _ => Vec d → ℝ) where
  coe u := u.toH1Function

@[simp] theorem coe_mk (u : H1Function U) (hmean : MeanZeroOn U u.toFun) :
    ((⟨u, hmean⟩ : H1MeanZeroFunction U) : H1Function U) = u :=
  rfl

@[ext] theorem ext {u v : H1MeanZeroFunction U}
    (htoH1 : u.toH1Function = v.toH1Function) : u = v := by
  cases u
  cases v
  cases htoH1
  rfl

variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

instance : Zero (H1MeanZeroFunction U) where
  zero :=
    { toH1Function := 0
      meanZero := by
        change ∫ x in U, (0 : ℝ) ∂MeasureTheory.volume = 0
        simp }

instance : Add (H1MeanZeroFunction U) where
  add u v :=
    { toH1Function := u.toH1Function + v.toH1Function
      meanZero := by
        have huInt : MeasureTheory.IntegrableOn u.toH1Function U := u.toH1Function.integrableOn
        have hvInt : MeasureTheory.IntegrableOn v.toH1Function U := v.toH1Function.integrableOn
        change ∫ x in U, (u.toH1Function + v.toH1Function) x ∂MeasureTheory.volume = 0
        rw [show (fun x => (u.toH1Function + v.toH1Function) x) =
            fun x => u x + v x by rfl]
        rw [MeasureTheory.integral_add huInt.integrable hvInt.integrable, u.meanZero, v.meanZero]
        ring }

instance : SMul ℝ (H1MeanZeroFunction U) where
  smul c u :=
    { toH1Function := c • u.toH1Function
      meanZero := by
        change ∫ x in U, (c • u.toH1Function) x ∂MeasureTheory.volume = 0
        rw [show (fun x => (c • u.toH1Function) x) = fun x => c * u x by rfl]
        rw [MeasureTheory.integral_const_mul, u.meanZero]
        simp }

instance : Neg (H1MeanZeroFunction U) where
  neg u := (-1 : ℝ) • u

instance : Sub (H1MeanZeroFunction U) where
  sub u v := u + (-v)

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
@[simp] theorem toH1Function_zero :
    ((0 : H1MeanZeroFunction U) : H1Function U) = 0 :=
  rfl

@[simp] theorem toH1Function_add
    (u v : H1MeanZeroFunction U) :
    ((u + v : H1MeanZeroFunction U) : H1Function U) = (u : H1Function U) + (v : H1Function U) :=
  rfl

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
@[simp] theorem toH1Function_smul
    (c : ℝ) (u : H1MeanZeroFunction U) :
    ((c • u : H1MeanZeroFunction U) : H1Function U) = c • (u : H1Function U) :=
  rfl

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
@[simp] theorem toH1Function_neg
    (u : H1MeanZeroFunction U) :
    ((-u : H1MeanZeroFunction U) : H1Function U) = -(u : H1Function U) :=
  rfl

@[simp] theorem toH1Function_sub
    (u v : H1MeanZeroFunction U) :
    ((u - v : H1MeanZeroFunction U) : H1Function U) = (u : H1Function U) - (v : H1Function U) :=
  rfl

instance : SMul ℕ (H1MeanZeroFunction U) where
  smul n u := (n : ℝ) • u

instance : SMul ℤ (H1MeanZeroFunction U) where
  smul n u := (n : ℝ) • u

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem toH1Function_injective :
    Function.Injective (fun u : H1MeanZeroFunction U => (u : H1Function U)) := by
  intro u v h
  exact H1MeanZeroFunction.ext h

instance : AddCommGroup (H1MeanZeroFunction U) :=
  Function.Injective.addCommGroup
    (fun u : H1MeanZeroFunction U => (u : H1Function U))
    toH1Function_injective
    rfl
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ => rfl)
    (fun u n => by
      change ((n : ℝ) • (u : H1Function U)) = n • (u : H1Function U)
      rfl)
    (fun u n => by
      change ((n : ℝ) • (u : H1Function U)) = n • (u : H1Function U)
      rfl)

noncomputable def toH1FunctionAddMonoidHom :
    H1MeanZeroFunction U →+ H1Function U where
  toFun := fun u => u.toH1Function
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance : Module ℝ (H1MeanZeroFunction U) :=
  Function.Injective.module ℝ
    toH1FunctionAddMonoidHom
    toH1Function_injective
    (fun _ _ => rfl)

end H1MeanZeroFunction

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- The scalar `L²(U)` realization of an `H¹` function. -/
noncomputable def toScalarL2 (u : H1Function U) : ScalarL2 U :=
  Homogenization.toScalarL2 u.memL2

/-- The vector `L²(U; ℝ^d)` realization of the weak gradient. -/
noncomputable def gradToVectorL2 (u : H1Function U) : VectorL2 U :=
  Homogenization.toVectorL2 u.grad_memVectorL2

/-- The Hilbert-vector `L²(U; ℝ^d)` realization of the weak gradient. -/
noncomputable def gradToHilbertVectorL2 (u : H1Function U) : HilbertVectorL2 U :=
  Homogenization.toHilbertVectorL2OfVecField u.grad_memVectorL2

/-- The `i`th scalar `L²(U)` realization of the weak gradient. -/
noncomputable def gradCoordToScalarL2 (u : H1Function U) (i : Fin d) : ScalarL2 U :=
  Homogenization.toScalarL2 (u.grad_memL2 i)

/-- The sum of the scalar `L²` norms of the gradient coordinates. -/
noncomputable def gradientCoordL2NormSum (u : H1Function U) : ℝ :=
  ∑ i, ‖u.gradCoordToScalarL2 i‖

theorem coeFn_toScalarL2 (u : H1Function U) :
    u.toScalarL2 =ᵐ[volumeMeasureOn U] u :=
  Homogenization.coeFn_toScalarL2 u.memL2

theorem coeFn_gradToVectorL2 (u : H1Function U) :
    u.gradToVectorL2 =ᵐ[volumeMeasureOn U] u.grad :=
  Homogenization.coeFn_toVectorL2 u.grad_memVectorL2

theorem coeFn_gradToHilbertVectorL2 (u : H1Function U) :
    u.gradToHilbertVectorL2 =ᵐ[volumeMeasureOn U] hilbertifyVecField u.grad :=
  Homogenization.coeFn_toHilbertVectorL2OfVecField u.grad_memVectorL2

theorem coeFn_gradCoordToScalarL2 (u : H1Function U) (i : Fin d) :
    u.gradCoordToScalarL2 i =ᵐ[volumeMeasureOn U] fun x => u.grad x i :=
  Homogenization.coeFn_toScalarL2 (u.grad_memL2 i)

theorem toScalarL2_add (u v : H1Function U) :
    (u + v).toScalarL2 = u.toScalarL2 + v.toScalarL2 := by
  simpa [H1Function.toScalarL2] using! MeasureTheory.MemLp.toLp_add u.memL2 v.memL2

theorem toScalarL2_smul (c : ℝ) (u : H1Function U) :
    (c • u).toScalarL2 = c • u.toScalarL2 := by
  simpa [H1Function.toScalarL2] using! MeasureTheory.MemLp.toLp_const_smul c u.memL2

theorem gradToVectorL2_add (u v : H1Function U) :
    (u + v).gradToVectorL2 = u.gradToVectorL2 + v.gradToVectorL2 := by
  simpa [H1Function.gradToVectorL2] using!
    MeasureTheory.MemLp.toLp_add u.grad_memVectorL2 v.grad_memVectorL2

theorem gradToVectorL2_smul (c : ℝ) (u : H1Function U) :
    (c • u).gradToVectorL2 = c • u.gradToVectorL2 := by
  simpa [H1Function.gradToVectorL2] using!
    MeasureTheory.MemLp.toLp_const_smul c u.grad_memVectorL2

theorem gradToHilbertVectorL2_add (u v : H1Function U) :
    (u + v).gradToHilbertVectorL2 = u.gradToHilbertVectorL2 + v.gradToHilbertVectorL2 := by
  let hu : MemHilbertVectorL2 U (hilbertifyVecField u.grad) :=
    Homogenization.memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2
  let hv : MemHilbertVectorL2 U (hilbertifyVecField v.grad) :=
    Homogenization.memHilbertVectorL2_hilbertifyVecField v.grad_memVectorL2
  simpa [H1Function.gradToHilbertVectorL2, hilbertifyVecField] using!
    MeasureTheory.MemLp.toLp_add hu hv

theorem gradToHilbertVectorL2_smul (c : ℝ) (u : H1Function U) :
    (c • u).gradToHilbertVectorL2 = c • u.gradToHilbertVectorL2 := by
  let hu : MemHilbertVectorL2 U (hilbertifyVecField u.grad) :=
    Homogenization.memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2
  simpa [H1Function.gradToHilbertVectorL2, hilbertifyVecField] using!
    MeasureTheory.MemLp.toLp_const_smul c hu

theorem gradCoordToScalarL2_add (u v : H1Function U) (i : Fin d) :
    (u + v).gradCoordToScalarL2 i = u.gradCoordToScalarL2 i + v.gradCoordToScalarL2 i := by
  simpa [H1Function.gradCoordToScalarL2] using!
    MeasureTheory.MemLp.toLp_add (u.grad_memL2 i) (v.grad_memL2 i)

theorem gradCoordToScalarL2_smul (c : ℝ) (u : H1Function U) (i : Fin d) :
    (c • u).gradCoordToScalarL2 i = c • u.gradCoordToScalarL2 i := by
  simpa [H1Function.gradCoordToScalarL2] using!
    MeasureTheory.MemLp.toLp_const_smul c (u.grad_memL2 i)

theorem norm_gradCoordToScalarL2_le (u : H1Function U) (i : Fin d) :
    ‖u.gradCoordToScalarL2 i‖ ≤ ‖u.gradToVectorL2‖ := by
  refine MeasureTheory.Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [coeFn_gradCoordToScalarL2 u i, coeFn_gradToVectorL2 u] with x hcoord hvec
  rw [hcoord, hvec]
  exact norm_le_pi_norm (u.grad x) i

theorem gradientCoordL2NormSum_nonneg (u : H1Function U) :
    0 ≤ u.gradientCoordL2NormSum := by
  exact Finset.sum_nonneg fun i _ => norm_nonneg _

theorem gradientCoordL2NormSum_le (u : H1Function U) :
    u.gradientCoordL2NormSum ≤ d * ‖u.gradToVectorL2‖ := by
  have hcoord :
      ∀ i : Fin d, ‖u.gradCoordToScalarL2 i‖ ≤ ‖u.gradToVectorL2‖ :=
    norm_gradCoordToScalarL2_le u
  calc
    u.gradientCoordL2NormSum
        = ∑ i : Fin d, ‖u.gradCoordToScalarL2 i‖ := rfl
    _ ≤ ∑ _i : Fin d, ‖u.gradToVectorL2‖ := by
          exact Finset.sum_le_sum fun i _ => hcoord i
    _ = d * ‖u.gradToVectorL2‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Normalize an `H¹` function to its mean-zero representative by subtracting
the average. -/
noncomputable def toMeanZero
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) : H1MeanZeroFunction U :=
  ⟨u.subAverage, u.meanZeroOn_subAverage⟩

/-- Alias for `toMeanZero`, matching the existing harmonic normalization API. -/
noncomputable def normalizeMeanZero
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) : H1MeanZeroFunction U :=
  u.toMeanZero

@[simp] theorem toMeanZero_toH1Function
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) :
    u.toMeanZero.toH1Function = u.subAverage :=
  rfl

@[simp] theorem normalizeMeanZero_toH1Function
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) :
    u.normalizeMeanZero.toH1Function = u.subAverage :=
  rfl

@[simp] theorem toMeanZero_apply
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) (x : Vec d) :
    u.toMeanZero x = u x - integralAverage U u := by
  simp [H1Function.toMeanZero]

@[simp] theorem toMeanZero_grad
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) (x : Vec d) :
    u.toMeanZero.toH1Function.grad x = u.grad x := by
  exact u.grad_subAverage x

theorem gradToVectorL2_subAverage_eq
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) :
    u.subAverage.gradToVectorL2 = u.gradToVectorL2 := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_gradToVectorL2 u.subAverage, coeFn_gradToVectorL2 u]
    with x hsub hu
  rw [hsub, hu]
  exact u.grad_subAverage x

/-- Pair a vector `L²` field with the weak gradient in the Hilbert `L²`
ambient space. -/
noncomputable def gradientHilbertPairing {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (u : H1Function U) : ℝ :=
  inner ℝ (Homogenization.toHilbertVectorL2OfVecField hf) u.gradToHilbertVectorL2

theorem gradientHilbertPairing_eq_integral {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (u : H1Function U) :
    u.gradientHilbertPairing hf =
      ∫ x in U, vecDot (f x) (u.grad x) ∂MeasureTheory.volume := by
  unfold H1Function.gradientHilbertPairing H1Function.gradToHilbertVectorL2
  rw [MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards
      [Homogenization.coeFn_toHilbertVectorL2OfVecField hf,
        Homogenization.coeFn_toHilbertVectorL2OfVecField u.grad_memVectorL2]
    with x hfx hux
  rw [hfx, hux]
  simp [hilbertifyVecField, HilbertVec.inner_def]

theorem abs_gradientHilbertPairing_le {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (u : H1Function U) :
    |u.gradientHilbertPairing hf| ≤
      ‖Homogenization.toHilbertVectorL2OfVecField hf‖ * ‖u.gradToHilbertVectorL2‖ := by
  exact abs_real_inner_le_norm (Homogenization.toHilbertVectorL2OfVecField hf) u.gradToHilbertVectorL2

theorem norm_gradToHilbertVectorL2_le (u : H1Function U) :
    ‖u.gradToHilbertVectorL2‖ ≤ (d : ℝ) * ‖u.gradToVectorL2‖ := by
  exact Homogenization.norm_toHilbertVectorL2OfVecField_le
    (U := U) (f := u.grad) u.grad_memVectorL2

theorem norm_gradToVectorL2_le_norm_gradToHilbertVectorL2 (u : H1Function U) :
    ‖u.gradToVectorL2‖ ≤ ‖u.gradToHilbertVectorL2‖ := by
  exact Homogenization.norm_toVectorL2_le_toHilbertVectorL2OfVecField
    (U := U) (f := u.grad) u.grad_memVectorL2

end H1Function

namespace H1MeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)}

/-- The scalar `L²(U)` realization of a mean-zero `H¹` function. -/
noncomputable def toScalarL2 (u : H1MeanZeroFunction U) : ScalarL2 U :=
  u.toH1Function.toScalarL2

/-- The vector `L²(U; ℝ^d)` realization of the weak gradient. -/
noncomputable def gradToVectorL2 (u : H1MeanZeroFunction U) : VectorL2 U :=
  u.toH1Function.gradToVectorL2

/-- The Hilbert-vector `L²(U; ℝ^d)` realization of a mean-zero `H¹`
function's weak gradient. -/
noncomputable def gradToHilbertVectorL2 (u : H1MeanZeroFunction U) : HilbertVectorL2 U :=
  u.toH1Function.gradToHilbertVectorL2

theorem toScalarL2_add [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u v : H1MeanZeroFunction U) :
    (u + v).toScalarL2 = u.toScalarL2 + v.toScalarL2 := by
  simpa [H1MeanZeroFunction.toScalarL2] using
    H1Function.toScalarL2_add u.toH1Function v.toH1Function

theorem toScalarL2_smul [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (c : ℝ) (u : H1MeanZeroFunction U) :
    (c • u).toScalarL2 = c • u.toScalarL2 := by
  simpa [H1MeanZeroFunction.toScalarL2] using
    H1Function.toScalarL2_smul c u.toH1Function

theorem gradToVectorL2_add [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u v : H1MeanZeroFunction U) :
    (u + v).gradToVectorL2 = u.gradToVectorL2 + v.gradToVectorL2 := by
  simpa [H1MeanZeroFunction.gradToVectorL2] using
    H1Function.gradToVectorL2_add u.toH1Function v.toH1Function

theorem gradToVectorL2_smul [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (c : ℝ) (u : H1MeanZeroFunction U) :
    (c • u).gradToVectorL2 = c • u.gradToVectorL2 := by
  simpa [H1MeanZeroFunction.gradToVectorL2] using
    H1Function.gradToVectorL2_smul c u.toH1Function

theorem gradToHilbertVectorL2_add [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u v : H1MeanZeroFunction U) :
    (u + v).gradToHilbertVectorL2 = u.gradToHilbertVectorL2 + v.gradToHilbertVectorL2 := by
  simpa [H1MeanZeroFunction.gradToHilbertVectorL2] using
    H1Function.gradToHilbertVectorL2_add u.toH1Function v.toH1Function

theorem gradToHilbertVectorL2_smul [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (c : ℝ) (u : H1MeanZeroFunction U) :
    (c • u).gradToHilbertVectorL2 = c • u.gradToHilbertVectorL2 := by
  simpa [H1MeanZeroFunction.gradToHilbertVectorL2] using
    H1Function.gradToHilbertVectorL2_smul c u.toH1Function

end H1MeanZeroFunction

namespace H1MeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)}

/-- The scalar `L²` norm of a mean-zero `H¹` function. -/
noncomputable def valueL2Norm (u : H1MeanZeroFunction U) : ℝ :=
  ‖u.toScalarL2‖

/-- The gradient-only `L²` norm which is the future coercive norm on the
mean-zero layer. -/
noncomputable def gradientL2Norm (u : H1MeanZeroFunction U) : ℝ :=
  ‖u.gradToVectorL2‖

noncomputable instance [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    Norm (H1MeanZeroFunction U) where
  norm u := u.gradientL2Norm

@[simp] theorem norm_eq_gradientL2Norm
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (u : H1MeanZeroFunction U) :
    ‖u‖ = u.gradientL2Norm :=
  rfl

theorem seminormedSpaceCore [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    SeminormedSpace.Core ℝ (H1MeanZeroFunction U) where
  norm_nonneg u := by
    show 0 ≤ u.gradientL2Norm
    exact norm_nonneg u.gradToVectorL2
  norm_smul c u := by
    change ‖(c • u).gradToVectorL2‖ = ‖c‖ * ‖u.gradToVectorL2‖
    rw [H1MeanZeroFunction.gradToVectorL2_smul, norm_smul]
  norm_triangle u v := by
    change ‖(u + v).gradToVectorL2‖ ≤ ‖u.gradToVectorL2‖ + ‖v.gradToVectorL2‖
    rw [H1MeanZeroFunction.gradToVectorL2_add]
    exact norm_add_le u.gradToVectorL2 v.gradToVectorL2

noncomputable instance [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    SeminormedAddCommGroup (H1MeanZeroFunction U) :=
  SeminormedAddCommGroup.ofCore (𝕜 := ℝ) seminormedSpaceCore

noncomputable instance [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    NormedSpace ℝ (H1MeanZeroFunction U) where
  norm_smul_le c u := by
    rw [(seminormedSpaceCore (U := U)).norm_smul c u]

/-- The gradient realization as a linear map into the Hilbert `L²` ambient
space. -/
noncomputable def gradToHilbertVectorL2Linear [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    H1MeanZeroFunction U →ₗ[ℝ] HilbertVectorL2 U where
  toFun := gradToHilbertVectorL2
  map_add' := gradToHilbertVectorL2_add
  map_smul' := gradToHilbertVectorL2_smul

@[simp] theorem gradToHilbertVectorL2Linear_apply
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (u : H1MeanZeroFunction U) :
    gradToHilbertVectorL2Linear (U := U) u = u.gradToHilbertVectorL2 :=
  rfl

/-- The gradient realization as a continuous linear map for the gradient-only
seminorm on the mean-zero coercive layer. -/
noncomputable def gradToHilbertVectorL2CLM [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    H1MeanZeroFunction U →L[ℝ] HilbertVectorL2 U :=
  (gradToHilbertVectorL2Linear (U := U)).mkContinuous (d : ℝ)
    (fun u => by
      change ‖u.toH1Function.gradToHilbertVectorL2‖ ≤
        (d : ℝ) * ‖u.toH1Function.gradToVectorL2‖
      exact H1Function.norm_gradToHilbertVectorL2_le (U := U) u.toH1Function)

@[simp] theorem gradToHilbertVectorL2CLM_apply
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (u : H1MeanZeroFunction U) :
    gradToHilbertVectorL2CLM (d := d) (U := U) u = u.gradToHilbertVectorL2 := by
  rw [gradToHilbertVectorL2CLM, LinearMap.mkContinuous_apply]
  rfl

/-- The gradient pairing of a mean-zero `H¹` function against an `L²` vector
field, realized through the Hilbert `L²` ambient space. -/
noncomputable def gradientPairing {f : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hf : MemVectorL2 U f) (u : H1MeanZeroFunction U) : ℝ :=
  inner ℝ (Homogenization.toHilbertVectorL2OfVecField hf) u.gradToHilbertVectorL2

theorem gradientPairing_eq_integral {f : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hf : MemVectorL2 U f) (u : H1MeanZeroFunction U) :
    gradientPairing hf u =
      ∫ x in U, vecDot (f x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
  exact H1Function.gradientHilbertPairing_eq_integral (hf := hf) (u := u.toH1Function)

theorem gradientPairing_add {f : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hf : MemVectorL2 U f) (u v : H1MeanZeroFunction U) :
    gradientPairing hf (u + v) = gradientPairing hf u + gradientPairing hf v := by
  rw [H1MeanZeroFunction.gradientPairing, H1MeanZeroFunction.gradientPairing,
    H1MeanZeroFunction.gradientPairing, H1MeanZeroFunction.gradToHilbertVectorL2_add,
    inner_add_right]

theorem gradientPairing_smul {f : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hf : MemVectorL2 U f) (c : ℝ) (u : H1MeanZeroFunction U) :
    gradientPairing hf (c • u) = c * gradientPairing hf u := by
  simpa [H1MeanZeroFunction.gradientPairing, H1MeanZeroFunction.gradToHilbertVectorL2_smul] using
    inner_smul_right (Homogenization.toHilbertVectorL2OfVecField hf) u.gradToHilbertVectorL2 c

/-- The gradient pairing, packaged as a linear functional on the mean-zero
coercive `H¹` layer. -/
noncomputable def gradientPairingLinear {f : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hf : MemVectorL2 U f) : H1MeanZeroFunction U →ₗ[ℝ] ℝ where
  toFun := gradientPairing hf
  map_add' := gradientPairing_add hf
  map_smul' c u := by
    simpa using gradientPairing_smul hf c u

@[simp] theorem gradientPairingLinear_apply {f : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hf : MemVectorL2 U f) (u : H1MeanZeroFunction U) :
    gradientPairingLinear hf u = gradientPairing hf u :=
  rfl

theorem abs_gradientPairing_le {f : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hf : MemVectorL2 U f) (u : H1MeanZeroFunction U) :
    |gradientPairing hf u| ≤
      ‖Homogenization.toHilbertVectorL2OfVecField hf‖ * ‖u.gradToHilbertVectorL2‖ := by
  exact abs_real_inner_le_norm (Homogenization.toHilbertVectorL2OfVecField hf) u.gradToHilbertVectorL2

theorem norm_gradToHilbertVectorL2_le (u : H1MeanZeroFunction U) :
    ‖u.gradToHilbertVectorL2‖ ≤ (d : ℝ) * u.gradientL2Norm := by
  exact H1Function.norm_gradToHilbertVectorL2_le (U := U) u.toH1Function

theorem gradientL2Norm_le_norm_gradToHilbertVectorL2 (u : H1MeanZeroFunction U) :
    u.gradientL2Norm ≤ ‖u.gradToHilbertVectorL2‖ := by
  exact H1Function.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2 (U := U) u.toH1Function

theorem abs_gradientPairing_le_gradientL2Norm {f : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hf : MemVectorL2 U f) (u : H1MeanZeroFunction U) :
    |gradientPairing hf u| ≤
      ((d : ℝ) * ‖Homogenization.toHilbertVectorL2OfVecField hf‖) * u.gradientL2Norm := by
  calc
    |gradientPairing hf u| ≤
        ‖Homogenization.toHilbertVectorL2OfVecField hf‖ * ‖u.gradToHilbertVectorL2‖ :=
      abs_gradientPairing_le hf u
    _ ≤ ‖Homogenization.toHilbertVectorL2OfVecField hf‖ * ((d : ℝ) * u.gradientL2Norm) := by
          exact mul_le_mul_of_nonneg_left (norm_gradToHilbertVectorL2_le (d := d) u) (norm_nonneg _)
    _ = ((d : ℝ) * ‖Homogenization.toHilbertVectorL2OfVecField hf‖) * u.gradientL2Norm := by
          ring

theorem norm_gradientPairingLinear_apply_le {f : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hf : MemVectorL2 U f) (u : H1MeanZeroFunction U) :
    ‖gradientPairingLinear hf u‖ ≤
      ((d : ℝ) * ‖Homogenization.toHilbertVectorL2OfVecField hf‖) * u.gradientL2Norm := by
  change ‖gradientPairing hf u‖ ≤
    ((d : ℝ) * ‖Homogenization.toHilbertVectorL2OfVecField hf‖) * u.gradientL2Norm
  simpa only [Real.norm_eq_abs] using abs_gradientPairing_le_gradientL2Norm (d := d) hf u

/-- The gradient pairing as a continuous linear functional for the
gradient-only seminorm on the mean-zero coercive layer. -/
noncomputable def gradientPairingCLM {f : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hf : MemVectorL2 U f) : H1MeanZeroFunction U →L[ℝ] ℝ := by
  letI : AddCommGroup (H1MeanZeroFunction U) :=
    (show SeminormedAddCommGroup (H1MeanZeroFunction U) from inferInstance).toAddCommGroup
  letI : Module ℝ (H1MeanZeroFunction U) := inferInstance
  exact (gradientPairingLinear hf).mkContinuous
    (((d : ℝ) * ‖Homogenization.toHilbertVectorL2OfVecField hf‖))
    (fun u => by
      change ‖gradientPairingLinear hf u‖ ≤
        ((d : ℝ) * ‖Homogenization.toHilbertVectorL2OfVecField hf‖) * u.gradientL2Norm
      exact norm_gradientPairingLinear_apply_le (d := d) hf u)

@[simp] theorem gradientPairingCLM_apply {f : Vec d → Vec d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hf : MemVectorL2 U f) (u : H1MeanZeroFunction U) :
    gradientPairingCLM hf u = gradientPairing hf u := by
  let : AddCommGroup (H1MeanZeroFunction U) :=
    (show SeminormedAddCommGroup (H1MeanZeroFunction U) from inferInstance).toAddCommGroup
  let : Module ℝ (H1MeanZeroFunction U) := inferInstance
  show (gradientPairingLinear hf).mkContinuous
      (((d : ℝ) * ‖Homogenization.toHilbertVectorL2OfVecField hf‖))
      (fun u => by
        change ‖gradientPairingLinear hf u‖ ≤
          ((d : ℝ) * ‖Homogenization.toHilbertVectorL2OfVecField hf‖) * u.gradientL2Norm
        exact norm_gradientPairingLinear_apply_le (d := d) hf u) u = gradientPairing hf u
  rw [LinearMap.mkContinuous_apply]
  rfl

end H1MeanZeroFunction

/-- Bundled coercive estimate on the mean-zero `H¹` layer. -/
structure H1CoerciveEstimate {d : ℕ} (U : Set (Vec d)) where
  fixedValue : ℝ
  constant_nonneg : 0 ≤ fixedValue
  bound :
    ∀ u : H1MeanZeroFunction U,
      u.valueL2Norm ≤ fixedValue * u.gradientL2Norm

namespace H1CoerciveEstimate

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

theorem bound_subAverage (hC : H1CoerciveEstimate U) (u : H1Function U) :
    (u.toMeanZero).valueL2Norm ≤ hC.fixedValue * ‖u.gradToVectorL2‖ := by
  calc
    (u.toMeanZero).valueL2Norm ≤ hC.fixedValue * (u.toMeanZero).gradientL2Norm :=
      hC.bound u.toMeanZero
    _ = hC.fixedValue * ‖u.gradToVectorL2‖ := by
      rw [H1MeanZeroFunction.gradientL2Norm, H1MeanZeroFunction.gradToVectorL2,
        H1Function.toMeanZero_toH1Function, H1Function.gradToVectorL2_subAverage_eq]

end H1CoerciveEstimate

namespace H1MeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

/-- The value realization as a linear map into scalar `L²(U)`. -/
noncomputable def toScalarL2Linear : H1MeanZeroFunction U →ₗ[ℝ] ScalarL2 U where
  toFun := toScalarL2
  map_add' := toScalarL2_add
  map_smul' := toScalarL2_smul

@[simp] theorem toScalarL2Linear_apply (u : H1MeanZeroFunction U) :
    toScalarL2Linear (U := U) u = u.toScalarL2 :=
  rfl

theorem norm_toScalarL2Linear_apply_le (hC : H1CoerciveEstimate U) (u : H1MeanZeroFunction U) :
    ‖toScalarL2Linear (U := U) u‖ ≤ hC.fixedValue * ‖u‖ := by
  change ‖u.toScalarL2‖ ≤ hC.fixedValue * u.gradientL2Norm
  exact hC.bound u

/-- The value realization as a continuous linear map once a coercive estimate
controls `‖u‖_{L²}` by the gradient-only seminorm. -/
noncomputable def toScalarL2CLM (hC : H1CoerciveEstimate U) :
    H1MeanZeroFunction U →L[ℝ] ScalarL2 U :=
  (toScalarL2Linear (U := U)).mkContinuous hC.fixedValue
    (norm_toScalarL2Linear_apply_le (U := U) hC)

@[simp] theorem toScalarL2CLM_apply (hC : H1CoerciveEstimate U) (u : H1MeanZeroFunction U) :
    toScalarL2CLM (U := U) hC u = u.toScalarL2 := by
  show (toScalarL2Linear (U := U)).mkContinuous hC.fixedValue
      (norm_toScalarL2Linear_apply_le (U := U) hC) u = u.toScalarL2
  rw [LinearMap.mkContinuous_apply]
  rfl

/-- The mean-zero coercive layer packaged in the Hilbert product
`L²(U) × L²(U; ℝᵈ)`. -/
noncomputable def toHilbertProductLinear :
    H1MeanZeroFunction U →ₗ[ℝ] (ScalarL2 U × HilbertVectorL2 U) where
  toFun u := (u.toScalarL2, u.gradToHilbertVectorL2)
  map_add' u v := by
    ext <;> simp [toScalarL2_add, gradToHilbertVectorL2_add]
  map_smul' c u := by
    ext <;> simp [toScalarL2_smul, gradToHilbertVectorL2_smul]

@[simp] theorem toHilbertProductLinear_apply (u : H1MeanZeroFunction U) :
    toHilbertProductLinear (U := U) u = (u.toScalarL2, u.gradToHilbertVectorL2) :=
  rfl

theorem norm_le_norm_toHilbertProductLinear_apply (u : H1MeanZeroFunction U) :
    ‖u‖ ≤ ‖toHilbertProductLinear (d := d) (U := U) u‖ := by
  calc
    ‖u‖ = u.gradientL2Norm := by
          rfl
    _ ≤ ‖u.gradToHilbertVectorL2‖ := gradientL2Norm_le_norm_gradToHilbertVectorL2 (d := d) u
    _ ≤ ‖(u.toScalarL2, u.gradToHilbertVectorL2)‖ := by
          exact le_max_right ‖u.toScalarL2‖ ‖u.gradToHilbertVectorL2‖
    _ = ‖toHilbertProductLinear (d := d) (U := U) u‖ := by
          rw [toHilbertProductLinear_apply]

theorem norm_toHilbertProductLinear_apply_le
    (hC : H1CoerciveEstimate U) (u : H1MeanZeroFunction U) :
    ‖toHilbertProductLinear (d := d) (U := U) u‖ ≤ max hC.fixedValue (d : ℝ) * ‖u‖ := by
  rw [toHilbertProductLinear_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · calc
      ‖u.toScalarL2‖ ≤ hC.fixedValue * ‖u‖ :=
        norm_toScalarL2Linear_apply_le (U := U) hC u
      _ ≤ max hC.fixedValue (d : ℝ) * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · calc
      ‖u.gradToHilbertVectorL2‖ ≤ (d : ℝ) * ‖u‖ := by
        change ‖u.toH1Function.gradToHilbertVectorL2‖ ≤
          (d : ℝ) * ‖u.toH1Function.gradToVectorL2‖
        exact H1Function.norm_gradToHilbertVectorL2_le (U := U) u.toH1Function
      _ ≤ max hC.fixedValue (d : ℝ) * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- The mean-zero coercive layer as a continuous linear map into
`L²(U) × L²(U; ℝᵈ)` once a coercive estimate is available. -/
noncomputable def toHilbertProductCLM (hC : H1CoerciveEstimate U) :
    H1MeanZeroFunction U →L[ℝ] (ScalarL2 U × HilbertVectorL2 U) :=
  (toHilbertProductLinear (U := U)).mkContinuous (max hC.fixedValue (d : ℝ))
    (norm_toHilbertProductLinear_apply_le (d := d) (U := U) hC)

@[simp] theorem toHilbertProductCLM_apply
    (hC : H1CoerciveEstimate U) (u : H1MeanZeroFunction U) :
    toHilbertProductCLM (d := d) (U := U) hC u = (u.toScalarL2, u.gradToHilbertVectorL2) := by
  show (toHilbertProductLinear (U := U)).mkContinuous (max hC.fixedValue (d : ℝ))
      (norm_toHilbertProductLinear_apply_le (d := d) (U := U) hC) u =
      (u.toScalarL2, u.gradToHilbertVectorL2)
  rw [LinearMap.mkContinuous_apply]
  rfl

theorem norm_le_norm_toHilbertProductCLM_apply
    (hC : H1CoerciveEstimate U) (u : H1MeanZeroFunction U) :
    ‖u‖ ≤ ‖toHilbertProductCLM (d := d) (U := U) hC u‖ := by
  rw [toHilbertProductCLM_apply]
  exact norm_le_norm_toHilbertProductLinear_apply (d := d) (U := U) u

end H1MeanZeroFunction

end Homogenization
