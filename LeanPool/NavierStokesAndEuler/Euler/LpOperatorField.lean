/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSupportedSubspace
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.NormNum.GCD

/-!
# Rectangular coefficient fields acting on actual spatial L²

Bounded continuous fields of operators E→F act on genuine Bochner L²
classes, with their literal pointwise representatives. The action restricts
to the closed supported spaces, where its norm needs a bound only on the
support region. This supplies the physical frame and projected forcing maps.
-/

@[expose] public section


noncomputable section

namespace EulerLpOperatorField

open Set MeasureTheory ContinuousLinearMap EulerLpSupportedSubspace
open scoped BoundedContinuousFunction

variable {α E F : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] (μ : Measure α)
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instLpOperatorField1 : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instLpOperatorField2 : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ (E →L[ℝ] F))` instance to shorten typeclass
synthesis. -/
local instance instLpOperatorField3 : NormedAddCommGroup (α →ᵇ (E →L[ℝ] F)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ (E →L[ℝ] F))` instance to shorten typeclass
synthesis. -/
local instance instLpOperatorField4 : NormedSpace ℝ (α →ᵇ (E →L[ℝ] F)) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Lp E 2 μ)` instance to shorten typeclass synthesis. -/
local instance instLpOperatorField5 : NormedAddCommGroup (Lp E 2 μ) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Lp E 2 μ)` instance to shorten typeclass synthesis. -/
local instance instLpOperatorField6 : NormedSpace ℝ (Lp E 2 μ) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Lp F 2 μ)` instance to shorten typeclass synthesis. -/
local instance instLpOperatorField7 : NormedAddCommGroup (Lp F 2 μ) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Lp F 2 μ)` instance to shorten typeclass synthesis. -/
local instance instLpOperatorField8 : NormedSpace ℝ (Lp F 2 μ) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Lp E 2 μ →L[ℝ] Lp F 2 μ)` instance to shorten
typeclass synthesis. -/
local instance instLpOperatorField9 : NormedAddCommGroup (Lp E 2 μ →L[ℝ] Lp F 2 μ) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Lp E 2 μ →L[ℝ] Lp F 2 μ)` instance to shorten typeclass
synthesis. -/
local instance instLpOperatorField10 : NormedSpace ℝ (Lp E 2 μ →L[ℝ] Lp F 2 μ) := inferInstance

/-- Literal coefficient application is genuinely square integrable. -/
theorem apply_memLp (A : α →ᵇ (E →L[ℝ] F)) (u : Lp E 2 μ) :
    MemLp (fun x => A x (u x)) 2 μ := by
  apply (Lp.memLp u).of_le_mul (c := ‖A‖)
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (A.continuous.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable u))
  · exact Filter.Eventually.of_forall (fun x => ((A x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm x) (norm_nonneg _)))

/-- Actual application to a Bochner L² class. -/
def applyField (A : α →ᵇ (E →L[ℝ] F)) (u : Lp E 2 μ) : Lp F 2 μ :=
  (apply_memLp μ A u).toLp (fun x => A x (u x))

theorem applyField_ae (A : α →ᵇ (E →L[ℝ] F)) (u : Lp E 2 μ) :
    applyField μ A u =ᵐ[μ] fun x => A x (u x) := (apply_memLp μ A u).coeFn_toLp

/-- Full linear, bundling `toFun`, `map_add`, `map_smul`. -/
def fullLinear (A : α →ᵇ (E →L[ℝ] F)) : Lp E 2 μ →ₗ[ℝ] Lp F 2 μ where
  toFun := applyField μ A
  map_add' u v := by
    apply Lp.ext
    filter_upwards [applyField_ae μ A (u+v), applyField_ae μ A u, applyField_ae μ A v,
      Lp.coeFn_add u v, Lp.coeFn_add (applyField μ A u) (applyField μ A v)] with x huv hu hv hsum
          hout
    simp only [Pi.add_apply] at hsum hout
    rw [huv,hout,hu,hv,hsum,map_add]
  map_smul' r u := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [applyField_ae μ A (r • u), applyField_ae μ A u,
      Lp.coeFn_smul r u, Lp.coeFn_smul r (applyField μ A u)] with x hru hu hin hout
    simp only [Pi.smul_apply] at hin hout
    rw [hru,hout,hu,hin,map_smul]

theorem applyField_norm (A : α →ᵇ (E →L[ℝ] F)) (u : Lp E 2 μ) :
    ‖applyField μ A u‖ ≤ ‖A‖*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [applyField_ae μ A u] with x hx
  rw [hx]
  exact ((A x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm x) (norm_nonneg _))

/-- The actual bounded rectangular multiplier on full spatial L². -/
def full (A : α →ᵇ (E →L[ℝ] F)) : Lp E 2 μ →L[ℝ] Lp F 2 μ :=
  (fullLinear μ A).mkContinuous ‖A‖ (applyField_norm μ A)

theorem full_ae (A : α →ᵇ (E →L[ℝ] F)) (u : Lp E 2 μ) :
    full μ A u =ᵐ[μ] fun x => A x (u x) := applyField_ae μ A u

theorem full_norm (A : α →ᵇ (E →L[ℝ] F)) : ‖full μ A‖ ≤ ‖A‖ :=
  opNorm_le_bound _ (norm_nonneg A) (applyField_norm μ A)

theorem full_add (A B : α →ᵇ (E →L[ℝ] F)) : full μ (A+B) = full μ A+full μ B := by
  apply ContinuousLinearMap.ext
  intro u
  change full μ (A+B) u = full μ A u+full μ B u
  apply Lp.ext
  filter_upwards [full_ae μ (A+B) u, full_ae μ A u, full_ae μ B u,
    Lp.coeFn_add (full μ A u) (full μ B u)] with x hab ha hb hout
  simp only [Pi.add_apply] at hout
  rw [hab,hout,ha,hb]
  rfl

theorem full_smul (r : ℝ) (A : α →ᵇ (E →L[ℝ] F)) : full μ (r • A) = r • full μ A := by
  apply ContinuousLinearMap.ext
  intro u
  change full μ (r • A) u = r • full μ A u
  apply Lp.ext
  filter_upwards [full_ae μ (r • A) u, full_ae μ A u, Lp.coeFn_smul r (full μ A u)] with x hr ha
      hout
  simp only [Pi.smul_apply] at hout
  rw [hr,hout,ha]
  rfl

/-- Rectangular multiplier formation is itself a linear contraction. -/
def fullMap : (α →ᵇ (E →L[ℝ] F)) →L[ℝ] (Lp E 2 μ →L[ℝ] Lp F 2 μ) where
  toLinearMap := { toFun := full μ, map_add' := full_add μ, map_smul' := full_smul μ }
  cont := AddMonoidHomClass.continuous_of_bound
    ({ toFun := full μ, map_add' := full_add μ, map_smul' := full_smul μ } :
      (α →ᵇ (E →L[ℝ] F)) →ₗ[ℝ] (Lp E 2 μ →L[ℝ] Lp F 2 μ)) 1
    (fun A => by
      change ‖full μ A‖ ≤ (1 : ℝ)*‖A‖
      simpa only [one_mul] using full_norm μ A)

theorem fullMap_norm : ‖fullMap (E := E) (F := F) μ‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  change ‖full μ A‖ ≤ (1 : ℝ)*‖A‖
  simpa only [one_mul] using full_norm μ A

end EulerLpOperatorField

namespace EulerLpOperatorField

open Set MeasureTheory ContinuousLinearMap EulerLpSupportedSubspace
open scoped BoundedContinuousFunction

variable {α E F : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] (μ : Measure α)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (S : Set α) (hS : MeasurableSet S)

theorem full_mem (A : α →ᵇ (E →L[ℝ] F)) (u : supportedSpace (V := E) μ S hS) :
    full μ A (u : Lp E 2 μ) ∈ supportedSpace μ S hS := by
  apply (mem_supportedSpace_ae μ S hS _).2
  filter_upwards [full_ae μ A (u : Lp E 2 μ),
    (mem_supportedSpace_ae μ S hS (u : Lp E 2 μ)).1 u.property] with x ha hu hx
  rw [ha,hu hx,map_zero]

/-- The genuine rectangular multiplier between the supported Hilbert spaces. -/
def supported (A : α →ᵇ (E →L[ℝ] F)) :
    supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V := F) μ S hS :=
  ((full μ A).comp (supportedSpace μ S hS).subtypeL).codRestrict
    (supportedSpace μ S hS) (full_mem μ S hS A)

theorem supported_ae (A : α →ᵇ (E →L[ℝ] F)) (u : supportedSpace (V := E) μ S hS) :
    ((supported μ S hS A u : supportedSpace (V := F) μ S hS) : Lp F 2 μ) =ᵐ[μ]
      fun x => A x ((u : Lp E 2 μ) x) := full_ae μ A u

/-- Only values on the supporting region enter the actual operator norm. -/
theorem supported_norm (A : α →ᵇ (E →L[ℝ] F)) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x ∈ S, ‖A x‖ ≤ C) : ‖supported μ S hS A‖ ≤ C := by
  apply opNorm_le_bound _ hC
  intro u
  change ‖full μ A (u : Lp E 2 μ)‖ ≤ C*‖(u : Lp E 2 μ)‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [full_ae μ A (u : Lp E 2 μ),
    (mem_supportedSpace_ae μ S hS (u : Lp E 2 μ)).1 u.property] with x ha hu
  rw [ha]
  by_cases hx : x ∈ S
  · exact ((A x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA x hx) (norm_nonneg _))
  · simp only [hu hx,map_zero,norm_zero,mul_zero,le_refl]

/-- A pointwise lower frame bound becomes the actual spatial-L² lower frame bound. -/
theorem supported_norm_sq_lower (A : α →ᵇ (E →L[ℝ] F)) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ x ∈ S, ∀ v : E, c*‖v‖^2 ≤ ‖A x v‖^2)
    (u : supportedSpace (V := E) μ S hS) :
    c*‖u‖^2 ≤ ‖supported μ S hS A u‖^2 := by
  have hroot : (Real.sqrt c)^2 = c := Real.sq_sqrt hc
  have h : ‖Real.sqrt c • (u : Lp E 2 μ)‖ ≤ ‖full μ A (u : Lp E 2 μ)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [full_ae μ A (u : Lp E 2 μ), Lp.coeFn_smul (Real.sqrt c) (u : Lp E 2 μ),
      (mem_supportedSpace_ae μ S hS (u : Lp E 2 μ)).1 u.property] with x ha hs hu
    rw [ha,hs,Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg c)]
    by_cases hx : x ∈ S
    · apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg _)) (norm_nonneg _)).1
      rw [mul_pow,hroot]
      exact hA x hx _
    · simp only [hu hx,map_zero,norm_zero,mul_zero,le_refl]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg c)] at h
  have hs := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg _)) (norm_nonneg _)).2 h
  change c*‖(u : Lp E 2 μ)‖^2 ≤ ‖full μ A (u : Lp E 2 μ)‖^2
  simpa only [mul_pow,hroot] using hs

end EulerLpOperatorField
