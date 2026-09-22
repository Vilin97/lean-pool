/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Banach spaces carried by rectangular symmetric ideals

A complete `TauCeti.SymmetricOperatorIdealFamily` already contains exactly the
analytic data needed to regard its members as a Banach space in the ideal gauge.
This file packages that observation once and for all.

The resulting type has three uses.

* Its norm is the family gauge, not the ambient operator norm.
* The forgetful map to bounded operators is contractive.
* Bochner integration in the ideal norm automatically produces an ideal member,
  and forgetting the integral agrees with integrating the underlying operators.

The construction is completely generic.  Once the rectangular Hilbert--Schmidt,
trace, or Schatten family has been supplied, no additional completeness or
integration argument is needed for that family.
-/

namespace TauCeti
namespace DavisKahan
namespace OperatorIdeal
namespace UnitarilyInvariant

open scoped InnerProductSpace
open Filter Topology MeasureTheory

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The linear subspace of members of a rectangular symmetric ideal. -/
noncomputable def idealSubmodule
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜) :
    Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {A | N.Mem A}
  zero_mem' := N.zero_mem
  add_mem' := fun hA hB => N.add_mem hA hB
  smul_mem' := fun c _A hA => N.smul_mem c hA

/-- A member of a rectangular symmetric ideal, bundled with the ideal gauge as
its norm.  This is a fresh type synonym so it does not inherit the ambient
operator norm from the submodule subtype. -/
def IdealOperator
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
     : Type _ :=
  ↥(idealSubmodule (E := E) (F := F) N)

namespace IdealOperator

variable (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]

/-- Additive group structure, inherited from the ideal submodule. -/
instance instAddCommGroup : AddCommGroup (IdealOperator (E := E) (F := F) N) :=
  inferInstanceAs (AddCommGroup ↥(idealSubmodule (E := E) (F := F) N))

/-- Scalar multiplication, inherited from the ideal submodule. -/
instance instModule : Module 𝕜 (IdealOperator (E := E) (F := F) N) :=
  inferInstanceAs (Module 𝕜 ↥(idealSubmodule (E := E) (F := F) N))

/-- Forget the ideal membership witness. -/
def toOp (A : IdealOperator (E := E) (F := F) N) : E →L[𝕜] F :=
  (A : ↥(idealSubmodule (E := E) (F := F) N)).1

omit [N.IsComplete] in
/-- The underlying operator belongs to the ideal. -/
theorem mem (A : IdealOperator (E := E) (F := F) N) : N.Mem A.toOp :=
  (A : ↥(idealSubmodule (E := E) (F := F) N)).2

/-- Bundle a member of the ideal. -/
def ofMem (A : E →L[𝕜] F) (hA : N.Mem A) :
    IdealOperator (E := E) (F := F) N := ⟨A, hA⟩

omit [N.IsComplete] in
/-- Bundling a member and forgetting the witness is the identity. -/
@[simp] theorem toOp_ofMem (A : E →L[𝕜] F) (hA : N.Mem A) :
    (ofMem N A hA).toOp = A := rfl

omit [N.IsComplete] in
/-- The zero ideal member is the zero operator. -/
@[simp] theorem toOp_zero :
    (0 : IdealOperator (E := E) (F := F) N).toOp = 0 := rfl

omit [N.IsComplete] in
/-- Addition of ideal members is addition of the underlying operators. -/
@[simp] theorem toOp_add
    (A B : IdealOperator (E := E) (F := F) N) :
    (A + B).toOp = A.toOp + B.toOp := rfl

omit [N.IsComplete] in
/-- Scaling an ideal member scales the underlying operator. -/
@[simp] theorem toOp_smul
    (c : 𝕜) (A : IdealOperator (E := E) (F := F) N) :
    (c • A).toOp = c • A.toOp := rfl

omit [N.IsComplete] in
/-- Negation of an ideal member negates the underlying operator. -/
@[simp] theorem toOp_neg
    (A : IdealOperator (E := E) (F := F) N) :
    (-A).toOp = -A.toOp := rfl

omit [N.IsComplete] in
/-- Subtraction of ideal members subtracts the underlying operators. -/
@[simp] theorem toOp_sub
    (A B : IdealOperator (E := E) (F := F) N) :
    (A - B).toOp = A.toOp - B.toOp := rfl

omit [N.IsComplete] in
/-- The anonymous-constructor form also forgets to the underlying operator. -/
@[simp] theorem toOp_mk
    (A : E →L[𝕜] F) (hA : N.Mem A) :
    (show IdealOperator (E := E) (F := F) N from ⟨A, hA⟩).toOp = A := rfl

omit [N.IsComplete] in
/-- Ideal members are equal when their underlying bounded operators agree. -/
@[ext] theorem ext
    {A B : IdealOperator (E := E) (F := F) N}
    (h : A.toOp = B.toOp) : A = B :=
  show (A : ↥(idealSubmodule (E := E) (F := F) N)) =
      (B : ↥(idealSubmodule (E := E) (F := F) N)) from Subtype.ext h

/-- The ideal gauge is the norm on bundled ideal operators. -/
noncomputable instance instNorm :
    Norm (IdealOperator (E := E) (F := F) N) :=
  ⟨fun A => N.gaugeReal A.toOp⟩

omit [N.IsComplete] in
/-- The norm on the ideal is the ideal gauge of the underlying operator. -/
@[simp] theorem norm_def
    (A : IdealOperator (E := E) (F := F) N) :
    ‖A‖ = N.gaugeReal A.toOp := rfl

/-- Norm laws supplied directly by the rectangular ideal fields. -/
theorem core : NormedSpace.Core 𝕜 (IdealOperator (E := E) (F := F) N) where
  norm_nonneg A := N.gaugeReal_nonneg A.mem
  norm_smul c A := by
    change N.gaugeReal (c • A.toOp) = ‖c‖ * N.gaugeReal A.toOp
    exact N.gaugeReal_smul c A.mem
  norm_triangle A B := by
    change N.gaugeReal (A.toOp + B.toOp) ≤ N.gaugeReal A.toOp + N.gaugeReal B.toOp
    exact N.gaugeReal_add_le A.mem B.mem
  norm_eq_zero_iff A := by
    change N.gaugeReal A.toOp = 0 ↔ A = 0
    constructor
    · intro hzero
      apply IdealOperator.ext N
      exact N.gaugeReal_eq_zero A.mem hzero
    · intro hzero
      rw [hzero]
      exact N.gaugeReal_zero

/-- The ideal is a normed additive group for the gauge, via `core`. -/
noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (IdealOperator (E := E) (F := F) N) :=
  NormedAddCommGroup.ofCore (core (E := E) (F := F) N)

/-- The ideal is a normed `𝕜`-space for the gauge, via `core`. -/
noncomputable instance instNormedSpace :
    NormedSpace 𝕜 (IdealOperator (E := E) (F := F) N) :=
  NormedSpace.ofCore (core (E := E) (F := F) N)

/-- Forgetting to the bounded-operator space is contractive. -/
theorem norm_toOp_le
    (A : IdealOperator (E := E) (F := F) N) :
    ‖A.toOp‖ ≤ ‖A‖ := by
  change ‖A.toOp‖ ≤ N.gaugeReal A.toOp
  exact N.opNorm_le_gaugeReal A.mem

/-- The forgetful linear map from the ideal Banach space to bounded operators. -/
noncomputable def toOpL :
    IdealOperator (E := E) (F := F) N →L[𝕜] (E →L[𝕜] F) :=
  LinearMap.mkContinuous
    { toFun := toOp N
      map_add' := fun A B => toOp_add N A B
      map_smul' := fun c A => toOp_smul N c A }
    1 (fun A => by
      rw [one_mul]
      exact norm_toOp_le N A)

/-- The contractive inclusion acts by forgetting the membership witness. -/
@[simp] theorem toOpL_apply
    (A : IdealOperator (E := E) (F := F) N) :
    toOpL (E := E) (F := F) N A = A.toOp := rfl

/-- Left composition by a fixed bounded operator, acting continuously in the
ideal norm. -/
noncomputable def compLeftL
    {G : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (L : F →L[𝕜] G) :
    IdealOperator (E := E) (F := F) N →L[𝕜]
      IdealOperator (E := E) (F := G) N := by
  let M : IdealOperator (E := E) (F := F) N →ₗ[𝕜]
      IdealOperator (E := E) (F := G) N :=
    { toFun := fun A => ofMem N (L ∘L A.toOp) (N.comp_left_mem L A.mem)
      map_add' := by
        intro A B
        apply IdealOperator.ext N
        simp [ContinuousLinearMap.comp_add]
      map_smul' := by
        intro c A
        apply IdealOperator.ext N
        simp }
  exact M.mkContinuous ‖L‖ fun A => by
    change N.gaugeReal (L ∘L A.toOp) ≤ ‖L‖ * N.gaugeReal A.toOp
    exact N.gaugeReal_comp_left_le_mul L A.mem

/-- Left composition acts on the underlying operator by left composition. -/
@[simp] theorem compLeftL_toOp
    {G : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (L : F →L[𝕜] G)
    (A : IdealOperator (E := E) (F := F) N) :
    (compLeftL N L A).toOp = L ∘L A.toOp := rfl

/-- Right composition by a fixed bounded operator, acting continuously in the
ideal norm. -/
noncomputable def compRightL
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (R : H →L[𝕜] E) :
    IdealOperator (E := E) (F := F) N →L[𝕜]
      IdealOperator (E := H) (F := F) N := by
  let M : IdealOperator (E := E) (F := F) N →ₗ[𝕜]
      IdealOperator (E := H) (F := F) N :=
    { toFun := fun A => ofMem N (A.toOp ∘L R) (N.comp_right_mem R A.mem)
      map_add' := by
        intro A B
        apply IdealOperator.ext N
        simp [ContinuousLinearMap.add_comp]
      map_smul' := by
        intro c A
        apply IdealOperator.ext N
        simp [ContinuousLinearMap.smul_comp] }
  exact M.mkContinuous ‖R‖ fun A => by
    change N.gaugeReal (A.toOp ∘L R) ≤ ‖R‖ * N.gaugeReal A.toOp
    have h := N.gaugeReal_comp_right_le_mul R A.mem
    simpa [mul_comm] using h

/-- Right composition acts on the underlying operator by right composition. -/
@[simp] theorem compRightL_toOp
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (R : H →L[𝕜] E)
    (A : IdealOperator (E := E) (F := F) N) :
    (compRightL N R A).toOp = A.toOp ∘L R := rfl

/-- Two-sided bounded composition as a continuous linear map in the ideal
norm. -/
noncomputable def compBothL
    {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) (R : H →L[𝕜] E) :
    IdealOperator (E := E) (F := F) N →L[𝕜]
      IdealOperator (E := H) (F := G) N := by
  let M : IdealOperator (E := E) (F := F) N →ₗ[𝕜]
      IdealOperator (E := H) (F := G) N :=
    { toFun := fun A => ofMem N (L ∘L A.toOp ∘L R) (N.comp_mem L R A.mem)
      map_add' := by
        intro A B
        apply IdealOperator.ext N
        simp [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
      map_smul' := by
        intro c A
        apply IdealOperator.ext N
        simp [ContinuousLinearMap.smul_comp] }
  exact M.mkContinuous (‖L‖ * ‖R‖) fun A => by
    change N.gaugeReal (L ∘L A.toOp ∘L R) ≤
      (‖L‖ * ‖R‖) * N.gaugeReal A.toOp
    calc
      N.gaugeReal (L ∘L A.toOp ∘L R)
          ≤ ‖L‖ * N.gaugeReal A.toOp * ‖R‖ := N.gaugeReal_comp_le L R A.mem
      _ = (‖L‖ * ‖R‖) * N.gaugeReal A.toOp := by ring

/-- Two-sided composition acts on the underlying operator on both sides. -/
@[simp] theorem compBothL_toOp
    {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) (R : H →L[𝕜] E)
    (A : IdealOperator (E := E) (F := F) N) :
    (compBothL N L R A).toOp = L ∘L A.toOp ∘L R := rfl

/-- The ideal gauge completeness field produces an actual `CompleteSpace`
instance on the bundled ideal. -/
noncomputable instance instCompleteSpace :
    CompleteSpace (IdealOperator (E := E) (F := F) N) := by
  refine Metric.complete_of_cauchySeq_tendsto fun A hA => ?_
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m n,
      M ≤ m → M ≤ n → N.gaugeReal ((A m).toOp - (A n).toOp) < ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.1 hA ε hε
    refine ⟨M, ?_⟩
    intro m n hm hn
    have hdist := hM m hm n hn
    simpa only [dist_eq_norm, norm_def, toOp_sub] using hdist
  obtain ⟨L, hL, hconv⟩ := N.gaugeReal_complete
    (fun n => (A n).toOp) (fun n => (A n).mem) hcauchy
  refine ⟨ofMem N L hL, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := hconv ε hε
  refine ⟨M, ?_⟩
  intro n hn
  have h := hM n hn
  simpa only [dist_eq_norm, norm_def, toOp_sub, toOp_ofMem] using h

/-- Real scalars act on the ideal Banach space by restriction along
`ℝ → 𝕜`; this is what Bochner integration needs. -/
noncomputable instance instNormedSpaceReal :
    NormedSpace ℝ (IdealOperator (E := E) (F := F) N) :=
  NormedSpace.restrictScalars ℝ 𝕜 _

/-- The forgetful map commutes with Bochner integration in the ideal norm.

The ambient operator space of a general `RCLike` scalar has no canonical real
normed-space structure, so it is taken as an instance argument; at `ℝ` and `ℂ`
it is found automatically. -/
theorem toOp_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedSpace ℝ (E →L[𝕜] F)]
    (f : α → IdealOperator (E := E) (F := F) N)
    (hf : Integrable f μ) :
    (∫ a, f a ∂μ).toOp = ∫ a, (f a).toOp ∂μ := by
  have h := (toOpL (E := E) (F := F) N).integral_comp_comm hf
  simpa only [toOpL_apply] using h.symm

/-- The Bochner integral of an ideal-valued integrable function is an ideal
member after forgetting to bounded operators. -/
theorem mem_integral_toOp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedSpace ℝ (E →L[𝕜] F)]
    (f : α → IdealOperator (E := E) (F := F) N)
    (hf : Integrable f μ) :
    N.Mem (∫ a, (f a).toOp ∂μ) := by
  rw [← toOp_integral N f hf]
  exact (∫ a, f a ∂μ).mem

/-- The ideal gauge of the underlying integral is bounded by the integral of
pointwise ideal norms. -/
theorem gauge_integral_toOp_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedSpace ℝ (E →L[𝕜] F)]
    (f : α → IdealOperator (E := E) (F := F) N)
    (hf : Integrable f μ) :
    N.gaugeReal (∫ a, (f a).toOp ∂μ) ≤ ∫ a, ‖f a‖ ∂μ := by
  rw [← toOp_integral N f hf]
  change ‖∫ a, f a ∂μ‖ ≤ ∫ a, ‖f a‖ ∂μ
  exact norm_integral_le_integral_norm f

/-- A pointwise ideal-valued raw operator field can be integrated by bundling
its membership witnesses. -/
theorem mem_integral_of_integrable_lift
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedSpace ℝ (E →L[𝕜] F)]
    (f : α → E →L[𝕜] F)
    (hmem : ∀ a, N.Mem (f a))
    (hlift : Integrable (fun a => ofMem N (f a) (hmem a)) μ) :
    N.Mem (∫ a, f a ∂μ) := by
  simpa using mem_integral_toOp N (fun a => ofMem N (f a) (hmem a)) hlift

/-- Gauge estimate for a raw operator field with an integrable ideal-valued
lift. -/
theorem gauge_integral_of_integrable_lift_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedSpace ℝ (E →L[𝕜] F)]
    (f : α → E →L[𝕜] F)
    (hmem : ∀ a, N.Mem (f a))
    (hlift : Integrable (fun a => ofMem N (f a) (hmem a)) μ) :
    N.gaugeReal (∫ a, f a ∂μ) ≤ ∫ a, N.gaugeReal (f a) ∂μ := by
  simpa only [norm_def, toOp_ofMem] using
    gauge_integral_toOp_le N (fun a => ofMem N (f a) (hmem a)) hlift

end IdealOperator

end

end UnitarilyInvariant
end OperatorIdeal
end DavisKahan
end TauCeti
