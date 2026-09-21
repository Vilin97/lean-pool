/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-! # Hilbert Minimization -/

namespace Homogenization

/-!
This file records the abstract Hilbert-space minimization step behind the
construction of the doubled `\mu`-minimizers in the coarse-graining notes.

The setup is a real Hilbert space `V`, a coercive continuous bilinear form
`B : V →L[ℝ] V →L[ℝ] ℝ`, and a closed subspace `K`. For each affine shift
`x : V`, we build the unique correction `k(x) ∈ K` such that
`x + k(x)` is stationary against variations in `K`. Under symmetry of `B`, this
stationary point minimizes the quadratic energy on the affine space `x + K`.
-/

noncomputable section

open ContinuousLinearMap
open Filter
open scoped RealInnerProductSpace
open scoped Topology

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

instance closedSubmodule_completeSpace (K : ClosedSubmodule ℝ V) : CompleteSpace K.toSubmodule :=
  K.isClosed.completeSpace_coe

/-- The quadratic energy attached to a continuous bilinear form. -/
def quadraticEnergy (B : V →L[ℝ] V →L[ℝ] ℝ) (u : V) : ℝ :=
  (1 / 2 : ℝ) * B u u

omit [CompleteSpace V] in
theorem quadraticEnergy_nonneg {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B) (u : V) :
    0 ≤ quadraticEnergy B u := by
  rcases hB with ⟨C, hC_pos, hcoer⟩
  have h_nonneg : 0 ≤ B u u := by
    calc
      0 ≤ C * ‖u‖ * ‖u‖ := by positivity
      _ ≤ B u u := hcoer u
  unfold quadraticEnergy
  nlinarith

omit [CompleteSpace V] in
theorem quadraticEnergy_add {B : V →L[ℝ] V →L[ℝ] ℝ}
    (h_symm : ∀ u v : V, B u v = B v u) (u v : V) :
    quadraticEnergy B (u + v) = quadraticEnergy B u + B u v + quadraticEnergy B v := by
  unfold quadraticEnergy
  have h_expand : B (u + v) (u + v) = B u u + B u v + B v u + B v v := by
    rw [B.map_add₂ u v (u + v), (B u).map_add, (B v).map_add]
    ring
  rw [h_expand, h_symm v u]
  ring

omit [CompleteSpace V] in
theorem quadraticEnergy_continuous (B : V →L[ℝ] V →L[ℝ] ℝ) :
    Continuous (quadraticEnergy B) := by
  have h_apply : Continuous fun u : V => B u u :=
    Continuous.clm_apply B.continuous continuous_id
  unfold quadraticEnergy
  exact continuous_const.mul h_apply

/-- The concave quadratic response `ℓ(u) - 1 / 2 B(u,u)` attached to a
continuous linear functional and a coercive bilinear form. -/
def linearQuadraticResponse (B : V →L[ℝ] V →L[ℝ] ℝ) (ℓ : V →L[ℝ] ℝ)
    (u : V) : ℝ :=
  ℓ u - quadraticEnergy B u

omit [CompleteSpace V] in
theorem linearQuadraticResponse_le_of_firstVariation {B : V →L[ℝ] V →L[ℝ] ℝ}
    {ℓ : V →L[ℝ] ℝ} (hB : IsCoercive B)
    (h_symm : ∀ u v : V, B u v = B v u) {u v : V}
    (hfirst : ∀ w : V, B u w = ℓ w) :
    linearQuadraticResponse B ℓ v ≤ linearQuadraticResponse B ℓ u := by
  let w : V := v - u
  have hv : v = u + w := by
    simp [w]
  have hlin : ℓ w = B u w := (hfirst w).symm
  have hresp :
      linearQuadraticResponse B ℓ v =
        linearQuadraticResponse B ℓ u - quadraticEnergy B w := by
    rw [hv]
    rw [linearQuadraticResponse, linearQuadraticResponse, quadraticEnergy_add h_symm]
    rw [map_add]
    rw [hlin]
    ring
  rw [hresp]
  exact sub_le_self _ (quadraticEnergy_nonneg hB w)

/-- The Riesz representative of a continuous linear functional. -/
noncomputable def rieszRep (ℓ : V →L[ℝ] ℝ) : V :=
  (InnerProductSpace.toDual ℝ V).symm ℓ

@[simp] theorem inner_rieszRep_apply (ℓ : V →L[ℝ] ℝ) (w : V) :
    inner ℝ (rieszRep ℓ) w = ℓ w := by
  change inner ℝ (((InnerProductSpace.toDual ℝ V).symm) ℓ) w = ℓ w
  exact
    InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ)
      (E := V)
      (x := w)
      (y := (ℓ : StrongDual ℝ V))

/-- The unique stationary point for the concave quadratic response associated
to a coercive bilinear form. -/
noncomputable def linearQuadraticResponseMaximizer
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ℓ : V →L[ℝ] ℝ) : V :=
  hB.continuousLinearEquivOfBilin.symm (rieszRep ℓ)

theorem linearQuadraticResponseMaximizer_firstVariation
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ℓ : V →L[ℝ] ℝ) (w : V) :
    B (linearQuadraticResponseMaximizer B hB ℓ) w = ℓ w := by
  let e : V ≃L[ℝ] V := hB.continuousLinearEquivOfBilin
  calc
    B (linearQuadraticResponseMaximizer B hB ℓ) w
        = inner ℝ (e (linearQuadraticResponseMaximizer B hB ℓ)) w := by
            symm
            exact hB.continuousLinearEquivOfBilin_apply
              (linearQuadraticResponseMaximizer B hB ℓ) w
    _ = inner ℝ (rieszRep ℓ) w := by
          simp [linearQuadraticResponseMaximizer, e]
    _ = ℓ w := by
          exact inner_rieszRep_apply ℓ w

theorem linearQuadraticResponse_le_maximizer {B : V →L[ℝ] V →L[ℝ] ℝ}
    (hB : IsCoercive B) (h_symm : ∀ u v : V, B u v = B v u)
    (ℓ : V →L[ℝ] ℝ) (v : V) :
    linearQuadraticResponse B ℓ v ≤
      linearQuadraticResponse B ℓ (linearQuadraticResponseMaximizer B hB ℓ) :=
  linearQuadraticResponse_le_of_firstVariation hB h_symm
    (fun w => linearQuadraticResponseMaximizer_firstVariation B hB ℓ w)

omit [CompleteSpace V] in
theorem isBoundedBilinearMap_restrict {B : V →L[ℝ] V →L[ℝ] ℝ}
    (K : ClosedSubmodule ℝ V) :
    IsBoundedBilinearMap ℝ (fun p : K.toSubmodule × K.toSubmodule => B p.1 p.2) where
  add_left x₁ x₂ y := by
    exact B.map_add₂ x₁ x₂ y
  smul_left c x y := by
    exact B.map_smul₂ c x y
  add_right x y₁ y₂ := by
    exact (B x).map_add y₁ y₂
  smul_right c x y := by
    exact (B x).map_smul c y
  bound := by
    refine ⟨max ‖B‖ 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
    intro x y
    calc
      ‖B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := B.le_opNorm₂ x y
      _ ≤ max ‖B‖ 1 * ‖x‖ * ‖y‖ := by
        gcongr
        exact le_max_left _ _

/-- Restrict a continuous bilinear form to a closed subspace. -/
noncomputable def restrictBilin (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    K.toSubmodule →L[ℝ] K.toSubmodule →L[ℝ] ℝ :=
  IsBoundedBilinearMap.toContinuousLinearMap
    (f := fun p : K.toSubmodule × K.toSubmodule => B p.1 p.2)
    (isBoundedBilinearMap_restrict (B := B) K)

omit [CompleteSpace V] in
@[simp] theorem restrictBilin_apply (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (u w : K.toSubmodule) :
    restrictBilin K B u w = B u w := by
  simp [restrictBilin]

omit [CompleteSpace V] in
theorem isCoercive_restrictBilin {B : V →L[ℝ] V →L[ℝ] ℝ}
    (K : ClosedSubmodule ℝ V) (hB : IsCoercive B) :
    IsCoercive (restrictBilin K B) := by
  rcases hB with ⟨C, hC_pos, hcoer⟩
  refine ⟨C, hC_pos, ?_⟩
  intro u
  simpa [restrictBilin_apply] using hcoer (u : V)

omit [CompleteSpace V] in
theorem isBoundedBilinearMap_subspaceRhs {B : V →L[ℝ] V →L[ℝ] ℝ}
    (K : ClosedSubmodule ℝ V) :
    IsBoundedBilinearMap ℝ (fun p : V × K.toSubmodule => -B p.1 p.2) where
  add_left x₁ x₂ y := by
    change -(B (x₁ + x₂) y) = -B x₁ y + -B x₂ y
    rw [B.map_add₂]
    ring
  smul_left c x y := by
    change -(B (c • x) y) = c • -B x y
    rw [B.map_smul₂]
    simp
  add_right x y₁ y₂ := by
    change -(B x (y₁ + y₂)) = -B x y₁ + -B x y₂
    rw [(B x).map_add]
    ring
  smul_right c x y := by
    change -(B x (c • y)) = c • -B x y
    rw [(B x).map_smul]
    simp
  bound := by
    refine ⟨max ‖B‖ 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
    intro x y
    calc
      ‖-B x y‖ = ‖B x y‖ := by simp
      _ ≤ ‖B‖ * ‖x‖ * ‖y‖ := B.le_opNorm₂ x y
      _ ≤ max ‖B‖ 1 * ‖x‖ * ‖y‖ := by
        gcongr
        exact le_max_left _ _

/-- The continuous family of linear functionals `w ↦ -B x w` on the closed subspace `K`. -/
noncomputable def subspaceRhsBilin (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    V →L[ℝ] K.toSubmodule →L[ℝ] ℝ :=
  IsBoundedBilinearMap.toContinuousLinearMap
    (f := fun p : V × K.toSubmodule => -B p.1 p.2)
    (isBoundedBilinearMap_subspaceRhs (B := B) K)

omit [CompleteSpace V] in
@[simp] theorem subspaceRhsBilin_apply (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (x : V) (w : K.toSubmodule) :
    subspaceRhsBilin K B x w = -B x w := by
  rfl

/-- Riesz representation on the closed subspace `K`. -/
noncomputable def subspaceRieszMap (K : ClosedSubmodule ℝ V) :
    (K.toSubmodule →L[ℝ] ℝ) →L[ℝ] K.toSubmodule :=
  (InnerProductSpace.toDual ℝ K.toSubmodule).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem inner_subspaceRieszMap_apply (K : ClosedSubmodule ℝ V)
    (ℓ : K.toSubmodule →L[ℝ] ℝ) (w : K.toSubmodule) :
    inner ℝ (subspaceRieszMap K ℓ) w = ℓ w := by
  change inner ℝ (((InnerProductSpace.toDual ℝ K.toSubmodule).symm) ℓ) w = ℓ w
  exact
    (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := K.toSubmodule) (x := w) (y := ℓ))

/-- The Riesz representatives of the functionals `w ↦ -B x w` on `K`. -/
noncomputable def subspaceRhs (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    V →L[ℝ] K.toSubmodule :=
  (subspaceRieszMap K).comp (subspaceRhsBilin K B)

@[simp] theorem inner_subspaceRhs_apply (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (x : V) (w : K.toSubmodule) :
    inner ℝ (subspaceRhs K B x) w = -B x w := by
  change inner ℝ (subspaceRieszMap K (subspaceRhsBilin K B x)) w = -B x w
  rw [inner_subspaceRieszMap_apply]
  simp [subspaceRhsBilin_apply]

/-- The unique correction in `K` solving the affine first-variation equation. -/
noncomputable def correctionMap (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) :
    V →L[ℝ] K.toSubmodule :=
  ((isCoercive_restrictBilin K hB).continuousLinearEquivOfBilin).symm.toContinuousLinearMap.comp
    (subspaceRhs K B)

theorem restrictBilin_correctionMap_apply (K : ClosedSubmodule ℝ V)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (x : V) (w : K.toSubmodule) :
    restrictBilin K B (correctionMap K B hB x) w = -B x w := by
  let hK : IsCoercive (restrictBilin K B) := isCoercive_restrictBilin K hB
  calc
    restrictBilin K B (correctionMap K B hB x) w
      = inner ℝ (hK.continuousLinearEquivOfBilin (correctionMap K B hB x)) w := by
          symm
          exact hK.continuousLinearEquivOfBilin_apply (correctionMap K B hB x) w
    _ = inner ℝ (subspaceRhs K B x) w := by
          simp [correctionMap]
    _ = -B x w := by
          exact inner_subspaceRhs_apply K B x w

/-- The affine stationary point `x + k(x)` in the affine space `x + K`. -/
noncomputable def affineMinimizerMap (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) :
    V →L[ℝ] V :=
  ContinuousLinearMap.id ℝ V + (K.toSubmodule.subtypeL.comp (correctionMap K B hB))

@[simp] theorem affineMinimizerMap_apply (K : ClosedSubmodule ℝ V)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (x : V) :
    affineMinimizerMap K B hB x = x + correctionMap K B hB x :=
  rfl

theorem sub_affineMinimizerMap_apply_mem (K : ClosedSubmodule ℝ V)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (x : V) :
    affineMinimizerMap K B hB x - x ∈ K := by
  change affineMinimizerMap K B hB x - x ∈ K.toSubmodule
  have h_eq : affineMinimizerMap K B hB x - x = (correctionMap K B hB x : V) := by
    simp [affineMinimizerMap]
  rw [h_eq]
  exact (correctionMap K B hB x).2

theorem affineMinimizerMap_firstVariation (K : ClosedSubmodule ℝ V)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (x : V) (w : K.toSubmodule) :
    B (affineMinimizerMap K B hB x) w = 0 := by
  calc
    B (affineMinimizerMap K B hB x) w
      = B x w + B (correctionMap K B hB x) w := by
          simp [affineMinimizerMap, map_add]
    _ = B x w + restrictBilin K B (correctionMap K B hB x) w := by
          rw [restrictBilin_apply]
    _ = B x w + (-B x w) := by
          rw [restrictBilin_correctionMap_apply K B hB x w]
    _ = 0 := by ring

theorem affineMinimizerMap_minimizes_quadraticEnergy (K : ClosedSubmodule ℝ V)
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (h_symm : ∀ u v : V, B u v = B v u) (x y : V)
    (hy : y - x ∈ K) :
    quadraticEnergy B (affineMinimizerMap K B hB x) ≤ quadraticEnergy B y := by
  let m := affineMinimizerMap K B hB x
  have hm : m - x ∈ K := sub_affineMinimizerMap_apply_mem K B hB x
  have hdiff : y - m ∈ K := by
    have : y - m = (y - x) - (m - x) := by abel
    rw [this]
    exact K.toSubmodule.sub_mem hy hm
  let w : K.toSubmodule := ⟨y - m, hdiff⟩
  have hy_eq : y = m + w := by
    change y = m + (y - m)
    abel
  rw [hy_eq, quadraticEnergy_add h_symm]
  have hfirst : B m w = 0 := by
    change B (affineMinimizerMap K B hB x) w = 0
    exact affineMinimizerMap_firstVariation K B hB x w
  rw [hfirst, add_zero]
  exact le_add_of_nonneg_right (quadraticEnergy_nonneg hB w)

/-- The affine minimizer is the unique point in the affine subspace whose
quadratic energy is no larger than the canonical minimized energy. -/
theorem eq_affineMinimizerMap_of_quadraticEnergy_le (K : ClosedSubmodule ℝ V)
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (h_symm : ∀ u v : V, B u v = B v u) (x y : V)
    (hy : y - x ∈ K)
    (hle : quadraticEnergy B y ≤ quadraticEnergy B (affineMinimizerMap K B hB x)) :
    y = affineMinimizerMap K B hB x := by
  let m := affineMinimizerMap K B hB x
  have hm : m - x ∈ K := sub_affineMinimizerMap_apply_mem K B hB x
  have hdiff : y - m ∈ K := by
    have : y - m = (y - x) - (m - x) := by abel
    rw [this]
    exact K.toSubmodule.sub_mem hy hm
  let w : K.toSubmodule := ⟨y - m, hdiff⟩
  have hy_eq : y = m + w := by
    change y = m + (y - m)
    abel
  have hfirst : B m w = 0 := by
    change B (affineMinimizerMap K B hB x) w = 0
    exact affineMinimizerMap_firstVariation K B hB x w
  have henergy :
      quadraticEnergy B y = quadraticEnergy B m + quadraticEnergy B (w : V) := by
    rw [hy_eq, quadraticEnergy_add h_symm, hfirst]
    ring
  have hnonneg : 0 ≤ quadraticEnergy B (w : V) :=
    quadraticEnergy_nonneg hB (w : V)
  have hle_zero : quadraticEnergy B (w : V) ≤ 0 := by
    nlinarith
  have hqzero : quadraticEnergy B (w : V) = 0 :=
    le_antisymm hle_zero hnonneg
  have hBww : B (w : V) (w : V) = 0 := by
    unfold quadraticEnergy at hqzero
    nlinarith
  rcases hB with ⟨C, hC_pos, hcoer⟩
  have hnorm_nonneg : 0 ≤ ‖(w : V)‖ := norm_nonneg _
  have hnorm_zero : ‖(w : V)‖ = 0 := by
    have hcoer_w := hcoer (w : V)
    rw [hBww] at hcoer_w
    by_contra hne
    have hnorm_pos : 0 < ‖(w : V)‖ := by
      exact lt_of_le_of_ne (norm_nonneg _) (fun hzero => hne hzero.symm)
    have hprod_pos : 0 < C * ‖(w : V)‖ * ‖(w : V)‖ := by positivity
    linarith
  have hw_zero : (w : V) = 0 := norm_eq_zero.mp hnorm_zero
  calc
    y = m + w := hy_eq
    _ = m := by rw [hw_zero, add_zero]

/-- The quadratic energy splits into the minimized affine energy plus the
energy of the displacement from the affine minimizer. -/
theorem quadraticEnergy_eq_affineMinimizerMap_add_diff (K : ClosedSubmodule ℝ V)
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (h_symm : ∀ u v : V, B u v = B v u) (x y : V) (hy : y - x ∈ K) :
    quadraticEnergy B y =
      quadraticEnergy B (affineMinimizerMap K B hB x) +
        quadraticEnergy B (y - affineMinimizerMap K B hB x) := by
  let m := affineMinimizerMap K B hB x
  have hm : m - x ∈ K := sub_affineMinimizerMap_apply_mem K B hB x
  have hdiff : y - m ∈ K := by
    have : y - m = (y - x) - (m - x) := by abel
    rw [this]
    exact K.toSubmodule.sub_mem hy hm
  let w : K.toSubmodule := ⟨y - m, hdiff⟩
  have hy_eq : y = m + w := by
    change y = m + (y - m)
    abel
  have hfirst : B m w = 0 := by
    change B (affineMinimizerMap K B hB x) w = 0
    exact affineMinimizerMap_firstVariation K B hB x w
  calc
    quadraticEnergy B y = quadraticEnergy B (m + w) := by rw [hy_eq]
    _ = quadraticEnergy B m + B m w + quadraticEnergy B (w : V) := by
          rw [quadraticEnergy_add h_symm]
    _ = quadraticEnergy B m + quadraticEnergy B (w : V) := by
          rw [hfirst]
          ring

/-- Deterministic Galerkin/Cea convergence: if approximate minimizers in the
affine space have energy no larger than admissible comparison points converging
to the true Hilbert minimizer, then the approximate minimizers converge to the
true minimizer. -/
theorem tendsto_galerkin_of_quadraticEnergy_le_approximants
    (K : ClosedSubmodule ℝ V) {B : V →L[ℝ] V →L[ℝ] ℝ}
    (hB : IsCoercive B) (h_symm : ∀ u v : V, B u v = B v u)
    (x : V) {u v : ℕ → V}
    (hu_mem : ∀ n, u n - x ∈ K) (hv_mem : ∀ n, v n - x ∈ K)
    (hEnergy : ∀ n, quadraticEnergy B (u n) ≤ quadraticEnergy B (v n))
    (hv : Tendsto v atTop (𝓝 (affineMinimizerMap K B hB x))) :
    Tendsto u atTop (𝓝 (affineMinimizerMap K B hB x)) := by
  let m := affineMinimizerMap K B hB x
  let hBcopy := hB
  rcases hBcopy with ⟨C, hC_pos, hcoer⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hvdiff : Tendsto (fun n : ℕ => v n - m) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => m) atTop (𝓝 m) := tendsto_const_nhds
    simpa [m] using hv.sub hconst
  have hqv :
      Tendsto (fun n : ℕ => quadraticEnergy B (v n - m)) atTop (𝓝 0) := by
    have hcont := (quadraticEnergy_continuous B).tendsto (0 : V)
    simpa [Function.comp_def, quadraticEnergy] using hcont.comp hvdiff
  have hupper :
      Tendsto
        (fun n : ℕ => Real.sqrt ((2 / C) * quadraticEnergy B (v n - m)))
        atTop (𝓝 0) := by
    have hmul : Tendsto (fun n : ℕ => (2 / C) * quadraticEnergy B (v n - m))
        atTop (𝓝 ((2 / C) * 0)) :=
      hqv.const_mul (2 / C)
    have hsqrt := hmul.sqrt
    simpa using hsqrt
  refine squeeze_zero (fun n : ℕ => norm_nonneg (u n - m)) ?_ hupper
  intro n
  have hu_split :=
    quadraticEnergy_eq_affineMinimizerMap_add_diff K hB h_symm x (u n) (hu_mem n)
  have hv_split :=
    quadraticEnergy_eq_affineMinimizerMap_add_diff K hB h_symm x (v n) (hv_mem n)
  have hqle_raw :
      quadraticEnergy B (u n - affineMinimizerMap K B hB x) ≤
        quadraticEnergy B (v n - affineMinimizerMap K B hB x) := by
    nlinarith [hEnergy n, hu_split, hv_split]
  have hqle : quadraticEnergy B (u n - m) ≤ quadraticEnergy B (v n - m) := by
    change
      quadraticEnergy B (u n - affineMinimizerMap K B hB x) ≤
        quadraticEnergy B (v n - affineMinimizerMap K B hB x)
    exact hqle_raw
  have hcoer_u := hcoer (u n - m)
  have hsq : ‖u n - m‖ ^ 2 ≤ (2 / C) * quadraticEnergy B (v n - m) := by
    unfold quadraticEnergy at hqle
    have hpow : ‖u n - m‖ ^ 2 = ‖u n - m‖ * ‖u n - m‖ := by ring
    unfold quadraticEnergy
    rw [hpow]
    field_simp [ne_of_gt hC_pos]
    nlinarith [hcoer_u, hqle, hC_pos]
  exact Real.le_sqrt_of_sq_le hsq

/-- Deterministic convergence from near-minimal energy.  If points in the
affine correction space have quadratic energy within `ε n` of the selected
Hilbert minimizer and `ε n → 0`, then the points converge to that minimizer. -/
theorem tendsto_of_quadraticEnergy_le_min_add_eps
    (K : ClosedSubmodule ℝ V) {B : V →L[ℝ] V →L[ℝ] ℝ}
    (hB : IsCoercive B) (h_symm : ∀ u v : V, B u v = B v u)
    (x : V) {u : ℕ → V} {ε : ℕ → ℝ}
    (hu_mem : ∀ n, u n - x ∈ K)
    (hε_tendsto : Tendsto ε atTop (𝓝 0))
    (hEnergy :
      ∀ n,
        quadraticEnergy B (u n) ≤
          quadraticEnergy B (affineMinimizerMap K B hB x) + ε n) :
    Tendsto u atTop (𝓝 (affineMinimizerMap K B hB x)) := by
  let m := affineMinimizerMap K B hB x
  let hBcopy := hB
  rcases hBcopy with ⟨C, hC_pos, hcoer⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hupper :
      Tendsto (fun n : ℕ => Real.sqrt ((2 / C) * ε n)) atTop (𝓝 0) := by
    have hmul : Tendsto (fun n : ℕ => (2 / C) * ε n) atTop (𝓝 ((2 / C) * 0)) :=
      hε_tendsto.const_mul (2 / C)
    simpa using hmul.sqrt
  refine squeeze_zero (fun n : ℕ => norm_nonneg (u n - m)) ?_ hupper
  intro n
  have hu_split :=
    quadraticEnergy_eq_affineMinimizerMap_add_diff K hB h_symm x (u n) (hu_mem n)
  have hqle_raw : quadraticEnergy B (u n - affineMinimizerMap K B hB x) ≤ ε n := by
    nlinarith [hEnergy n, hu_split]
  have hqle : quadraticEnergy B (u n - m) ≤ ε n := by
    change quadraticEnergy B (u n - affineMinimizerMap K B hB x) ≤ ε n
    exact hqle_raw
  have hcoer_u := hcoer (u n - m)
  have hsq : ‖u n - m‖ ^ 2 ≤ (2 / C) * ε n := by
    unfold quadraticEnergy at hqle
    have hpow : ‖u n - m‖ ^ 2 = ‖u n - m‖ * ‖u n - m‖ := by ring
    rw [hpow]
    field_simp [ne_of_gt hC_pos]
    nlinarith [hcoer_u, hqle, hC_pos]
  exact Real.le_sqrt_of_sq_le hsq

section Parameterized

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine minimizer map pulled back along a continuous linear parameter map. -/
noncomputable def parameterAffineMinimizerMap (K : ClosedSubmodule ℝ V)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ι : E →L[ℝ] V) :
    E →L[ℝ] V :=
  (affineMinimizerMap K B hB).comp ι

@[simp] theorem parameterAffineMinimizerMap_apply (K : ClosedSubmodule ℝ V)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ι : E →L[ℝ] V) (p : E) :
    parameterAffineMinimizerMap K B hB ι p = affineMinimizerMap K B hB (ι p) :=
  rfl

theorem sub_parameterAffineMinimizerMap_apply_mem (K : ClosedSubmodule ℝ V)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ι : E →L[ℝ] V) (p : E) :
    parameterAffineMinimizerMap K B hB ι p - ι p ∈ K := by
  change affineMinimizerMap K B hB (ι p) - ι p ∈ K
  exact sub_affineMinimizerMap_apply_mem K B hB (ι p)

theorem parameterAffineMinimizerMap_firstVariation (K : ClosedSubmodule ℝ V)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ι : E →L[ℝ] V)
    (p : E) (w : K.toSubmodule) :
    B (parameterAffineMinimizerMap K B hB ι p) w = 0 := by
  simpa [parameterAffineMinimizerMap] using
    affineMinimizerMap_firstVariation K B hB (ι p) w

theorem parameterAffineMinimizerMap_minimizes_quadraticEnergy (K : ClosedSubmodule ℝ V)
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (h_symm : ∀ u v : V, B u v = B v u) (ι : E →L[ℝ] V) (p : E) (y : V)
    (hy : y - ι p ∈ K) :
    quadraticEnergy B (parameterAffineMinimizerMap K B hB ι p) ≤ quadraticEnergy B y := by
  simpa [parameterAffineMinimizerMap] using
    affineMinimizerMap_minimizes_quadraticEnergy K hB h_symm (ι p) y hy

end Parameterized

end Abstract

end

end Homogenization
