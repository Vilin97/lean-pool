/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.InvariantSubsetQuotient
public import LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.Foundations.InvariantSubsetQuotient
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint

/-!
# Hopf problem: toric · toric space 2

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem ToricSpace.factors_continuous (s : ToricFan.Triangle) : Continuous (factors s) := by
  apply continuous_pi
  intro i
  change Continuous (fun u : ActingTorus => ∏ j, (u j : ℂ) ^ s.dual i j)
  exact
    continuous_finsetProd _
      (fun j _ =>
        (Units.continuous_val.comp (continuous_apply j)).zpow₀ _ (fun u => Or.inl (u j).ne_zero))

private theorem ToricSpace.torusAction_joint_continuous :
    Continuous (fun p : ActingTorus × Space => torusAction p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨u, x⟩
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  have hlocal :
    Continuous
      (fun p : ActingTorus × ToricCharts.CoordinateSpace 3 =>
        ToricSpace.inclusion s (scale s p.1 p.2)) :=
    (inclusion_openEmbedding s).continuous.comp
      (((factors_continuous s).comp continuous_fst).mul continuous_snd)
  apply
    (((Topology.IsOpenEmbedding.id (X := ActingTorus)).prodMap
            (inclusion_openEmbedding s)).continuousAt_iff
        (g := fun p : ActingTorus × Space => torusAction p.1 p.2) (x := (u, z))).mp
  change
    ContinuousAt
      (fun p : ActingTorus × ToricCharts.CoordinateSpace 3 =>
        torusAction p.1 (ToricSpace.inclusion s p.2))
      (u, z)
  simpa only [torusAction_inclusion] using hlocal.continuousAt (x := (u, z))

private theorem ToricSpace.fibreMultiplier_continuous : Continuous fibreMultiplier := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_const

private def ToricSpace.displacementMatrix (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -1, 0] + (Real.log ‖t‖)⁻¹ • driftMatrix C t

private theorem ToricSpace.displacementMatrix_mulVec (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ)
    (y : Fin 2 → ℝ) : displacementMatrix C t *ᵥ y = displacement C t y := by
  rw [displacementMatrix, Matrix.add_mulVec, Matrix.smul_mulVec]
  change
    !![(0 : ℝ), 1; -1, 0] *ᵥ y + (Real.log ‖t‖)⁻¹ • (driftMatrix C t *ᵥ y) =
      realCuspVector y + (Real.log ‖t‖)⁻¹ • (driftMatrix C t *ᵥ y)
  congr 1
  ext i
  fin_cases i <;> simp [realCuspVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private def ToricSpace.inverseDisplacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  (displacementMatrix C t)⁻¹.mulVecLin

@[simp]
private theorem ToricSpace.inverseDisplacement_add (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ)
    (y z : Fin 2 → ℝ) :
    inverseDisplacement C t (y + z) = inverseDisplacement C t y + inverseDisplacement C t z :=
  map_add _ _ _

private theorem ToricSpace.displacementMatrix_isUnit (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) :
    IsUnit (displacementMatrix C t) := by
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  intro y
  obtain ⟨z, hz⟩ := (displacement_bijective C ht hR).surjective y
  exact ⟨z, (displacementMatrix_mulVec C t z).trans hz⟩

private theorem ToricSpace.displacementMatrix_det_ne_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) :
    (displacementMatrix C t).det ≠ 0 :=
  isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (displacementMatrix_isUnit C ht hR))

private theorem
    ToricSpace.inverseDisplacement_displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (y : Fin 2 → ℝ) : inverseDisplacement C t (displacement C t y) = y := by
  change (displacementMatrix C t)⁻¹ *ᵥ displacement C t y = y
  rw [← displacementMatrix_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (displacementMatrix_det_ne_zero C ht hR)),
    Matrix.one_mulVec]

private theorem
    ToricSpace.displacement_inverseDisplacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (y : Fin 2 → ℝ) : displacement C t (inverseDisplacement C t y) = y := by
  rw [← displacementMatrix_mulVec]
  change displacementMatrix C t *ᵥ ((displacementMatrix C t)⁻¹ *ᵥ y) = y
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (displacementMatrix_det_ne_zero C ht hR)),
    Matrix.one_mulVec]

private theorem ToricSpace.inverseDisplacement_norm_le (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (y : Fin 2 → ℝ) : ‖inverseDisplacement C t y‖ ≤ 2 * ‖y‖ := by
  have h := displacement_lower_bound C ht hR (inverseDisplacement C t y)
  rwa [displacement_inverseDisplacement C ht hR y] at h

private theorem
    ToricSpace.displacementMatrix_continuousAt (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (hC : ∀ i j, ContinuousAt (fun s => C s i j) t) (ht0 : t ≠ 0) (htlog : Real.log ‖t‖ ≠ 0) :
    ContinuousAt (displacementMatrix C) t := by
  have hlog : ContinuousAt (fun s : ℂ => (Real.log ‖s‖)⁻¹) t :=
    ((Real.continuousAt_log (norm_ne_zero_iff.mpr ht0)).comp continuous_norm.continuousAt).inv₀
      htlog
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  change
    ContinuousAt
      (fun s : ℂ => !![(0 : ℝ), 1; -1, 0] i j + (Real.log ‖s‖)⁻¹ * (-2 * Real.pi * (C s i j).im))
      t
  exact
    continuousAt_const.add
      (hlog.mul (continuousAt_const.mul (Complex.continuous_im.continuousAt.comp (hC i j))))

private theorem ToricSpace.inverseDisplacement_continuousAt_of_det_ne_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ} (hC : ∀ i j, ContinuousAt (fun s => C s i j) t)
    (ht0 : t ≠ 0) (htlog : Real.log ‖t‖ ≠ 0) (hdet : (displacementMatrix C t).det ≠ 0)
    (y : Fin 2 → ℝ) :
    ContinuousAt (fun p : ℂ × (Fin 2 → ℝ) => inverseDisplacement C p.1 p.2) (t, y) := by
  have hi : ContinuousAt (fun s : ℂ => (displacementMatrix C s)⁻¹) t :=
    (continuousAt_matrix_inv (displacementMatrix C t)
          (by simpa only [Ring.inverse_eq_inv'] using ContinuousInv₀.continuousAt_inv₀ hdet)).comp
      (displacementMatrix_continuousAt C hC ht0 htlog)
  have hm : Continuous (fun p : Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hp : ContinuousAt (fun p : ℂ × (Fin 2 → ℝ) => (displacementMatrix C p.1)⁻¹) (t, y) :=
    ContinuousAt.comp (f := fun p : ℂ × (Fin 2 → ℝ) => p.1) (g := fun s : ℂ =>
      (displacementMatrix C s)⁻¹) hi continuous_fst.continuousAt
  exact hm.continuousAt.comp (hp.prodMk continuous_snd.continuousAt)

private theorem
    ToricSpace.inverseDisplacement_continuousAt (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (hC : ∀ i j, ContinuousAt (fun s => C s i j) t) (ht : Real.log ‖t‖ < 0)
    (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) (y : Fin 2 → ℝ) :
    ContinuousAt (fun p : ℂ × (Fin 2 → ℝ) => inverseDisplacement C p.1 p.2) (t, y) := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  exact
    inverseDisplacement_continuousAt_of_det_ne_zero C hC ht0 ht.ne
      (displacementMatrix_det_ne_zero C ht hR) y

private theorem ToricSpace.position_continuousAt {x : Space} (hx : time x ≠ 0)
    (hlog : Real.log ‖time x‖ ≠ 0) : ContinuousAt position x := by
  have hxT : x ∈ openTorus := (mem_openTorus_iff x).mpr hx
  have hc : ContinuousAt torusCoordinates x :=
    torusCoordinates_holomorphic.continuousOn.continuousAt (openTorus_isOpen.mem_nhds hxT)
  have ht : ContinuousAt (fun y : Space => Real.log ‖time y‖) x :=
    ContinuousAt.comp (f := fun y : Space => ‖time y‖) (g := Real.log)
      (Real.continuousAt_log (norm_ne_zero_iff.mpr hx))
      time_holomorphic.continuous.continuousAt.norm
  apply continuousAt_pi.mpr
  intro i
  have hi : ContinuousAt (fun y : Space => torusCoordinates y i.castSucc) x :=
    (continuous_apply i.castSucc).continuousAt.comp hc
  have hli : ContinuousAt (fun y : Space => Real.log ‖torusCoordinates y i.castSucc‖) x :=
    ContinuousAt.comp (f := fun y : Space => ‖torusCoordinates y i.castSucc‖) (g := Real.log)
      (Real.continuousAt_log (norm_ne_zero_iff.mpr (torusCoordinates_nonzero hxT i.castSucc)))
      hi.norm
  exact hli.div ht hlog

private theorem ToricSpace.position_norm_le_on_chartNeighbourhood {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {s : ToricFan.Triangle} {n : ℕ} {x : Space} (hx : x ∈ chartNeighbourhood s n ε) :
    ‖position x‖ ≤ Max.max 0 (positionBound s ((n : ℝ) + 2) ε) := by
  by_cases ht : time x = 0
  · have hp : position x = 0 := by
      ext i
      simp [position, ht]
    rw [hp, norm_zero]
    exact le_max_left _ _
  · obtain ⟨z, hz, rfl⟩ := hx
    have hzT : z ∈ ToricCharts.torus := by
      rw [← inclusion_preimage_openTorus s]
      exact (mem_openTorus_iff _).mpr ht
    have hS : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith
    exact
      (position_norm_bound s hzT hS hε hε1 hz.2 (fun j => (hz.1 j).le)).trans (le_max_right _ _)

private theorem ToricSpace.position_locally_bounded {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {x : Space}
    (ht : ‖time x‖ < ε) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ y in 𝓝 x, ‖time y‖ < ε ∧ ‖position y‖ ≤ B := by
  obtain ⟨s, n, hx⟩ := chartNeighbourhood_cover ht
  refine ⟨Max.max 0 (positionBound s ((n : ℝ) + 2) ε), le_max_left _ _, ?_⟩
  filter_upwards [(chartNeighbourhood_open s n ε).mem_nhds hx] with y hy
  exact ⟨chartNeighbourhood_time hy, position_norm_le_on_chartNeighbourhood hε hε1 hy⟩

private def
    ToricCharts.coordinateModulus {d : ℕ} (z : CoordinateSpace d) : CoordinateSpace d := fun i =>
  (‖z i‖ : ℂ)

@[simp]
private theorem ToricCharts.coordinateModulus_apply {d : ℕ} (z : CoordinateSpace d) (i : Fin d) :
    coordinateModulus z i = (‖z i‖ : ℂ) :=
  rfl

private theorem ToricCharts.coordinateModulus_continuous {d : ℕ} :
    Continuous (coordinateModulus : CoordinateSpace d → CoordinateSpace d) := by
  exact continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i).norm

@[simp]
private theorem ToricCharts.coordinateModulus_idempotent {d : ℕ} (z : CoordinateSpace d) :
    coordinateModulus (coordinateModulus z) = coordinateModulus z := by
  funext i
  simp [coordinateModulus]

@[simp]
private theorem ToricCharts.coordinateModulus_mem_domain_iff {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (z : CoordinateSpace d) : coordinateModulus z ∈ domain A ↔ z ∈ domain A := by simp [domain]

@[simp]
private theorem ToricCharts.coordinateModulus_mem_torus_iff {d : ℕ} (z : CoordinateSpace d) :
    coordinateModulus z ∈ torus ↔ z ∈ torus := by simp [torus]

private theorem ToricCharts.monomial_coordinateModulus {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (z : CoordinateSpace d) :
    monomial A (coordinateModulus z) = coordinateModulus (monomial A z) := by
  funext i
  simp [monomial, coordinateModulus, norm_prod, norm_zpow]

private def ToricCharts.nonnegativeCoordinates {d : ℕ} : Set (CoordinateSpace d) :=
  {z | ∃ r : Fin d → ℝ, (∀ i, 0 ≤ r i) ∧ z = fun i => (r i : ℂ)}

private theorem ToricCharts.coordinateModulus_eq_self_iff {d : ℕ} (z : CoordinateSpace d) :
    coordinateModulus z = z ↔ z ∈ nonnegativeCoordinates := by
  constructor
  · intro hz
    exact ⟨fun i => ‖z i‖, fun i => norm_nonneg _, hz.symm⟩
  · rintro ⟨r, hr, rfl⟩
    funext i
    exact congrArg Complex.ofReal (Complex.norm_of_nonneg (hr i))

private theorem ToricSpace.chartChange_coordinateModulus (s t : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricFan.Triangle.chartChange s t (ToricCharts.coordinateModulus z) =
      ToricCharts.coordinateModulus (ToricFan.Triangle.chartChange s t z) :=
  ToricCharts.monomial_coordinateModulus (ToricFan.Triangle.transition s t) z

private theorem ToricSpace.coordinateModulus_overlap (s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ (ToricFan.Triangle.chartChange s t).source) :
    ToricSpace.inclusion t (ToricCharts.coordinateModulus (ToricFan.Triangle.chartChange s t z)) =
      ToricSpace.inclusion s (ToricCharts.coordinateModulus z) := by
  symm
  apply (inclusion_eq_iff s t _ _).mpr
  refine ⟨?_, chartChange_coordinateModulus s t z⟩
  simpa only [ToricFan.Triangle.chartChange_source,
    ToricCharts.coordinateModulus_mem_domain_iff] using hz

private def ToricSpace.modulus : Space → Space :=
  descend fun s z => ToricSpace.inclusion s (ToricCharts.coordinateModulus z)

@[simp]
private theorem
    ToricSpace.modulus_inclusion (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    modulus (ToricSpace.inclusion s z) =
      ToricSpace.inclusion s (ToricCharts.coordinateModulus z) :=
  descend_inclusion _ (fun s t _z hz => coordinateModulus_overlap s t hz) s z

private theorem ToricSpace.modulus_continuous : Continuous modulus := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  apply
    ((parametrization s).continuousAt_iff_continuousAt_comp_right
        (show ToricSpace.inclusion s z ∈ (parametrization s).target by simp)).mpr
  have h : modulus ∘ parametrization s = ToricSpace.inclusion s ∘ ToricCharts.coordinateModulus :=
    by
    funext w
    exact modulus_inclusion s w
  rw [h]
  exact
    ((inclusion_openEmbedding s).continuous.comp
        ToricCharts.coordinateModulus_continuous).continuousAt

@[simp]
private theorem ToricSpace.modulus_idempotent (x : Space) : modulus (modulus x) = modulus x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp only [modulus_inclusion, ToricCharts.coordinateModulus_idempotent]

@[simp]
private theorem ToricSpace.time_modulus (x : Space) : time (modulus x) = (‖time x‖ : ℂ) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [ToricFan.Triangle.time]

private def ToricSpace.positivePart : Set Space :=
  {x | modulus x = x}

private abbrev ToricSpace.PositivePart :=
  positivePart

private theorem ToricSpace.positivePart_isClosed : IsClosed positivePart :=
  isClosed_eq modulus_continuous continuous_id

@[simp]
private theorem ToricSpace.inclusion_mem_positivePart_iff (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricSpace.inclusion s z ∈ positivePart ↔ z ∈ ToricCharts.nonnegativeCoordinates := by
  change modulus (ToricSpace.inclusion s z) = ToricSpace.inclusion s z ↔ _
  rw [modulus_inclusion, (inclusion_openEmbedding s).injective.eq_iff,
    ToricCharts.coordinateModulus_eq_self_iff]

@[simp]
private theorem ToricSpace.modulus_mem_positivePart (x : Space) : modulus x ∈ positivePart :=
  modulus_idempotent x

private def ToricSpace.modulusRetraction (x : Space) : PositivePart :=
  ⟨modulus x, modulus_mem_positivePart x⟩

@[simp]
private theorem ToricSpace.modulusRetraction_coe (x : Space) :
    (modulusRetraction x : Space) = modulus x :=
  rfl

private abbrev ToricSpace.CompactTorus :=
  Fin 3 → Circle

private def ToricSpace.compactTorusUnits : CompactTorus →* ActingTorus
    where
  toFun u i := Circle.toUnits (u i)
  map_one' := by
    funext i
    exact Circle.toUnits.map_one
  map_mul' u
    v := by
    funext i
    exact Circle.toUnits.map_mul (u i) (v i)

@[simp]
private theorem ToricSpace.compactTorusUnits_apply (u : CompactTorus) (i : Fin 3) :
    (compactTorusUnits u i : ℂ) = (u i : ℂ) :=
  rfl

private theorem ToricSpace.compactTorusUnits_continuous : Continuous compactTorusUnits := by
  apply continuous_pi
  intro i
  apply Units.continuous_iff.mpr
  have h : Continuous (fun u : CompactTorus => (u i : ℂ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  exact ⟨h, h.inv₀ (fun u => (u i).coe_ne_zero)⟩

private def ToricSpace.compactTorusAction (u : CompactTorus) (x : Space) : Space :=
  torusAction (compactTorusUnits u) x

@[simp]
private theorem ToricSpace.compactTorusAction_one (x : Space) : compactTorusAction 1 x = x := by
  simp [compactTorusAction]

private theorem ToricSpace.compactTorusAction_mul (u v : CompactTorus) (x : Space) :
    compactTorusAction u (compactTorusAction v x) = compactTorusAction (u * v) x := by
  simp [compactTorusAction, torusAction_mul]

private instance ToricSpace.compactTorusMulAction : MulAction CompactTorus Space
    where
  smul := compactTorusAction
  one_smul := compactTorusAction_one
  mul_smul u v x := (compactTorusAction_mul u v x).symm

private theorem ToricSpace.compactTorusAction_continuous :
    Continuous (fun p : CompactTorus × Space => compactTorusAction p.1 p.2) := by
  have h : Continuous (fun p : CompactTorus × Space => (compactTorusUnits p.1, p.2)) :=
    (compactTorusUnits_continuous.comp continuous_fst).prodMk continuous_snd
  change
    Continuous
      ((fun p : ActingTorus × Space => torusAction p.1 p.2) ∘
        (fun p : CompactTorus × Space => (compactTorusUnits p.1, p.2)))
  exact torusAction_joint_continuous.comp h

private instance ToricSpace.compactTorusContinuousSMul : ContinuousSMul CompactTorus Space :=
  ⟨compactTorusAction_continuous⟩

@[simp]
private theorem ToricSpace.norm_factors_compactTorusUnits (s : ToricFan.Triangle) (u : CompactTorus)
    (i : Fin 3) : ‖factors s (compactTorusUnits u) i‖ = 1 := by
  simp [factors, ToricCharts.monomial, norm_prod, norm_zpow, Circle.norm_coe]

private theorem ToricSpace.coordinateModulus_scale_compactTorusUnits (s : ToricFan.Triangle)
    (u : CompactTorus) (z : ToricCharts.CoordinateSpace 3) :
    ToricCharts.coordinateModulus (scale s (compactTorusUnits u) z) =
      ToricCharts.coordinateModulus z := by
  funext i
  change (‖factors s (compactTorusUnits u) i * z i‖ : ℂ) = (‖z i‖ : ℂ)
  rw [norm_mul, norm_factors_compactTorusUnits, one_mul]

@[simp]
private theorem ToricSpace.modulus_compactTorusAction (u : CompactTorus) (x : Space) :
    modulus (compactTorusAction u x) = modulus x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [compactTorusAction, coordinateModulus_scale_compactTorusUnits]

@[simp]
private theorem ToricSpace.norm_time_compactTorusAction (u : CompactTorus) (x : Space) :
    ‖time (compactTorusAction u x)‖ = ‖time x‖ := by
  simp [compactTorusAction, time_torusAction, Circle.norm_coe]

private theorem ToricSpace.exists_unitNorm_scale_modulus (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ∃ u : ActingTorus, (∀ i, ‖(u i : ℂ)‖ = 1) ∧ scale s u (ToricCharts.coordinateModulus z) = z :=
  by
  classical
  have hphase (c : ℂ) : ∃ w : ℂ, ‖w‖ = 1 ∧ w * (‖c‖ : ℂ) = c := by
    by_cases hc : c = 0
    · exact ⟨1, NormOneClass.norm_one, by simp [hc]⟩
    · refine ⟨c / (‖c‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hc)]
      · exact
          div_mul_cancel₀ _ (by simpa only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero] using hc)
  choose w hw hmul using fun i => hphase (z i)
  have hw0 : w ∈ ToricCharts.torus := by
    intro i hi
    have h := hw i
    rw [hi, norm_zero] at h
    exact zero_ne_one h
  let u : ActingTorus := fun i =>
    Units.mk0 (ToricCharts.monomial s.rays w i) (ToricCharts.monomial_mapsTo_torus s.rays hw0 i)
  have hu : ∀ i, ‖(u i : ℂ)‖ = 1 := by
    intro i
    change ‖ToricCharts.monomial s.rays w i‖ = 1
    simp only [ToricCharts.monomial, norm_prod, norm_zpow, hw, one_zpow, Finset.prod_const_one]
  refine ⟨u, hu, ?_⟩
  have hf : factors s u = w := by
    change ToricCharts.monomial s.dual (ToricCharts.monomial s.rays w) = w
    rw [ToricCharts.monomial_mul_on_torus _ _ hw0, ToricFan.Triangle.dual_rays,
      ToricCharts.monomial_one]
  ext i
  change factors s u i * (‖z i‖ : ℂ) = z i
  rw [hf]
  exact hmul i

private theorem ToricSpace.exists_compactTorus_scale_modulus (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ∃ u : CompactTorus, scale s (compactTorusUnits u) (ToricCharts.coordinateModulus z) = z := by
  obtain ⟨u, hu, hz⟩ := exists_unitNorm_scale_modulus s z
  let v : CompactTorus := fun i => ⟨(u i : ℂ), mem_sphere_zero_iff_norm.mpr (hu i)⟩
  refine ⟨v, ?_⟩
  have hv : compactTorusUnits v = u := by
    funext i
    apply Units.ext
    rfl
  rw [hv]
  exact hz

private theorem ToricSpace.exists_compactTorusAction_modulus (x : Space) :
    ∃ u : CompactTorus, compactTorusAction u (modulus x) = x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨u, hu⟩ := exists_compactTorus_scale_modulus s z
  refine ⟨u, ?_⟩
  change
    torusAction (compactTorusUnits u) (modulus (ToricSpace.inclusion s z)) =
      ToricSpace.inclusion s z
  rw [modulus_inclusion, torusAction_inclusion, hu]

private def ToricSpace.polarMultiplication (p : CompactTorus × PositivePart) : Space :=
  compactTorusAction p.1 p.2

private theorem ToricSpace.polarMultiplication_continuous : Continuous polarMultiplication := by
  have h : Continuous (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  change
    Continuous
      ((fun p : CompactTorus × Space => compactTorusAction p.1 p.2) ∘
        (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))))
  exact compactTorusAction_continuous.comp h

private theorem
    ToricSpace.polarMultiplication_surjective : Function.Surjective polarMultiplication := by
  intro x
  obtain ⟨u, hu⟩ := exists_compactTorusAction_modulus x
  exact ⟨(u, modulusRetraction x), hu⟩

private theorem
    ToricSpace.compactTorusAction_injective_of_time_ne_zero {x : Space} (hx : time x ≠ 0) :
    Function.Injective (fun u : CompactTorus => compactTorusAction u x) := by
  intro u v huv
  have hxt : x ∈ openTorus := (mem_openTorus_iff x).mpr hx
  have he := congrArg torusCoordinates huv
  change
    torusCoordinates (torusAction (compactTorusUnits u) x) =
      torusCoordinates (torusAction (compactTorusUnits v) x) at he
  rw [torusCoordinates_action _ hxt, torusCoordinates_action _ hxt] at he
  funext i
  apply Circle.ext
  exact mul_right_cancel₀ (torusCoordinates_nonzero hxt i) (congrFun he i)

private def ToricSpace.compactTorusActionShear : CompactTorus × Space ≃ₜ CompactTorus × Space
    where
  toFun p := (p.1, p.1 • p.2)
  invFun p := (p.1, p.1⁻¹ • p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk ContinuousSMul.continuous_smul
  continuous_invFun := continuous_fst.prodMk (continuous_fst.inv.smul continuous_snd)

private theorem ToricSpace.compactTorusAction_isClosedMap :
    IsClosedMap (fun p : CompactTorus × Space => compactTorusAction p.1 p.2) :=
  isClosedMap_snd_of_compactSpace.comp compactTorusActionShear.isClosedMap

private theorem ToricSpace.polarMultiplication_isClosedMap : IsClosedMap polarMultiplication := by
  have h : IsClosedMap (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))) :=
    ((Homeomorph.refl CompactTorus).isClosedEmbedding.prodMap
        positivePart_isClosed.isClosedEmbedding_subtypeVal).isClosedMap
  change
    IsClosedMap
      ((fun p : CompactTorus × Space => compactTorusAction p.1 p.2) ∘
        (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))))
  exact compactTorusAction_isClosedMap.comp h

private abbrev ToricSpace.ClosedPositiveTube (η : ℝ) :=
  { x : PositivePart // ‖time (x : Space)‖ ≤ η }

private theorem ToricSpace.closedPolarMap_mem_iff (η : ℝ) (p : CompactTorus × PositivePart) :
    polarMultiplication p ∈ {x : Space | ‖time x‖ ≤ η} ↔
      p.2 ∈ {x : PositivePart | ‖time (x : Space)‖ ≤ η} := by
  change ‖time (compactTorusAction p.1 p.2)‖ ≤ η ↔ ‖time (p.2 : Space)‖ ≤ η
  rw [norm_time_compactTorusAction]

private def ToricSpace.closedPolarMap (η : ℝ) :
    CompactTorus × ClosedPositiveTube η → { x : Space // ‖time x‖ ≤ η } :=
  ProductRestriction.productRestriction polarMultiplication
    {x : PositivePart | ‖time (x : Space)‖ ≤ η} {x : Space | ‖time x‖ ≤ η}
    (closedPolarMap_mem_iff η)

@[simp]
private theorem ToricSpace.closedPolarMap_coe (η : ℝ) (p : CompactTorus × ClosedPositiveTube η) :
    (closedPolarMap η p : Space) = compactTorusAction p.1 (p.2.1 : Space) :=
  rfl

private theorem ToricSpace.closedPolarMap_continuous (η : ℝ) : Continuous (closedPolarMap η) :=
  ProductRestriction.productRestriction_continuous _ _ _ _ polarMultiplication_continuous

private theorem ToricSpace.closedPolarMap_isClosedMap (η : ℝ) : IsClosedMap (closedPolarMap η) :=
  ProductRestriction.productRestriction_isClosedMap _ _ _ _ polarMultiplication_isClosedMap

private theorem
    ToricSpace.closedPolarMap_surjective (η : ℝ) : Function.Surjective (closedPolarMap η) :=
  ProductRestriction.productRestriction_surjective _ _ _ _ polarMultiplication_surjective

private theorem ToricSpace.closedPolarMap_isQuotientMap (η : ℝ) :
    Topology.IsQuotientMap (closedPolarMap η) :=
  (closedPolarMap_isClosedMap η).isQuotientMap (closedPolarMap_continuous η)
    (closedPolarMap_surjective η)

private def ToricSpace.closedModulusRetraction (η : ℝ) (x : { x : Space // ‖time x‖ ≤ η }) :
    ClosedPositiveTube η :=
  ⟨modulusRetraction x, by
    change ‖time (modulus (x : Space))‖ ≤ η
    simpa only [time_modulus, Complex.norm_real, norm_norm] using x.property⟩

@[simp]
private theorem ToricSpace.closedModulusRetraction_closedPolarMap (η : ℝ)
    (p : CompactTorus × ClosedPositiveTube η) :
    closedModulusRetraction η (closedPolarMap η p) = p.2 := by
  apply Subtype.ext
  apply Subtype.ext
  change modulus (compactTorusAction p.1 (p.2.1 : Space)) = (p.2.1 : Space)
  rw [modulus_compactTorusAction]
  exact p.2.1.property

private def ToricSpace.phaseShear (v : Fin 2 → ℤ) (u : CompactTorus) : CompactTorus :=
  ![u 0 * u 2 ^ v 0, u 1 * u 2 ^ v 1, u 2]

private theorem ToricSpace.phaseShear_coe (v : Fin 2 → ℤ) (u : CompactTorus) :
    (fun j => (phaseShear v u j : ℂ)) =
      ToricCharts.monomial (ToricFan.Triangle.shear v) (fun j => (u j : ℂ)) := by
  funext i
  fin_cases i <;>
    simp [phaseShear, ToricCharts.monomial, ToricFan.Triangle.shear, Fin.prod_univ_succ]

private theorem ToricSpace.factors_shift_phaseShear (s : ToricFan.Triangle) (v : Fin 2 → ℤ)
    (u : CompactTorus) :
    factors (s.shift v) (compactTorusUnits (phaseShear v u)) = factors s (compactTorusUnits u) := by
  change
    ToricCharts.monomial (s.shift v).dual (fun j => (phaseShear v u j : ℂ)) =
      ToricCharts.monomial s.dual (fun j => (u j : ℂ))
  rw [ToricFan.Triangle.dual_shift, phaseShear_coe,
    ToricCharts.monomial_mul_on_torus _ _ (fun j => (u j).coe_ne_zero), Matrix.mul_assoc,
    ToricFan.Triangle.shear_add]
  simp

private theorem
    ToricSpace.translate_compactTorusAction (v : Fin 2 → ℤ) (u : CompactTorus) (x : Space) :
    ToricSpace.translate v (compactTorusAction u x) =
      compactTorusAction (phaseShear v u) (ToricSpace.translate v x) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [compactTorusAction, scale, factors_shift_phaseShear]

private abbrev CuspHoneycombTiling.Plane :=
  Fin 2 → ℝ

private abbrev CuspHoneycombTiling.Lattice :=
  Fin 2 → ℤ

private def CuspHoneycombTiling.latticePoint (v : CuspHoneycombTiling.Lattice) : Plane := fun i =>
  (v i : ℝ)

@[simp]
private theorem
    CuspHoneycombTiling.latticePoint_apply (v : CuspHoneycombTiling.Lattice) (i : Fin 2) :
    latticePoint v i = (v i : ℝ) :=
  rfl

@[simp]
private theorem CuspHoneycombTiling.latticePoint_zero : latticePoint 0 = 0 := by
  funext i
  simp [latticePoint]

@[simp]
private theorem CuspHoneycombTiling.latticePoint_add (v w : CuspHoneycombTiling.Lattice) :
    latticePoint (v + w) = latticePoint v + latticePoint w := by
  funext i
  simp [latticePoint]

@[simp]
private theorem CuspHoneycombTiling.latticePoint_neg (v : CuspHoneycombTiling.Lattice) :
    latticePoint (-v) = -latticePoint v := by
  funext i
  simp [latticePoint]

private def CuspHoneycombTiling.baseCell : Set Plane :=
  {x | |2 * x 0 + x 1| ≤ 1 ∧ |x 0 - x 1| ≤ 1 ∧ |x 0 + 2 * x 1| ≤ 1}

private def CuspHoneycombTiling.cell (v : CuspHoneycombTiling.Lattice) : Set Plane :=
  {x | x - latticePoint v ∈ baseCell}

@[simp]
private theorem CuspHoneycombTiling.mem_baseCell (x : Plane) :
    x ∈ baseCell ↔ |2 * x 0 + x 1| ≤ 1 ∧ |x 0 - x 1| ≤ 1 ∧ |x 0 + 2 * x 1| ≤ 1 :=
  Iff.rfl

@[simp]
private theorem CuspHoneycombTiling.mem_cell (v : CuspHoneycombTiling.Lattice) (x : Plane) :
    x ∈ cell v ↔ x - latticePoint v ∈ baseCell :=
  Iff.rfl

@[simp]
private theorem CuspHoneycombTiling.cell_zero : cell 0 = baseCell := by
  ext x
  simp only [mem_cell, latticePoint_zero, sub_zero]

private theorem CuspHoneycombTiling.baseCell_coordinate_bound_sharp {x : Plane} (hx : x ∈ baseCell)
    (i : Fin 2) : |x i| ≤ (2 / 3 : ℝ) := by
  obtain ⟨h0, h1, h2⟩ := hx
  have h0' := abs_le.mp h0
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  fin_cases i
  · change |x 0| ≤ (2 / 3 : ℝ)
    exact abs_le.mpr ⟨by linarith [h0'.1, h1'.1], by linarith [h0'.2, h1'.2]⟩
  · change |x 1| ≤ (2 / 3 : ℝ)
    exact abs_le.mpr ⟨by linarith [h2'.1, h1'.2], by linarith [h2'.2, h1'.1]⟩

private theorem CuspHoneycombTiling.baseCell_coordinate_bound {x : Plane} (hx : x ∈ baseCell)
    (i : Fin 2) : |x i| ≤ 1 :=
  (baseCell_coordinate_bound_sharp hx i).trans (by norm_num)

private theorem
    CuspHoneycombTiling.cell_coordinate_bound {v : CuspHoneycombTiling.Lattice} {x : Plane}
    (hx : x ∈ cell v) (i : Fin 2) : |x i - (v i : ℝ)| ≤ 1 :=
  baseCell_coordinate_bound hx i

private theorem
    CuspHoneycombTiling.add_latticePoint_mem_cell_iff (v w : CuspHoneycombTiling.Lattice)
    (x : Plane) : x + latticePoint w ∈ cell (v + w) ↔ x ∈ cell v := by
  simp only [mem_cell, latticePoint_add, add_sub_add_right_eq_sub]

private def CuspHoneycombTiling.squareCenter (p q : ℝ) : CuspHoneycombTiling.Lattice :=
  if q ≤ p then if 2 * p + q ≤ 1 then 0 else if 2 ≤ p + 2 * q then 1 else ![1, 0]
  else if p + 2 * q ≤ 1 then 0 else if 2 ≤ 2 * p + q then 1 else ![0, 1]

private theorem CuspHoneycombTiling.mem_cell_squareCenter (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : (![p, q] : Plane) ∈ cell (squareCenter p q) := by
  unfold squareCenter
  split_ifs
  all_goals
    simp only [mem_cell, mem_baseCell, Pi.sub_apply, latticePoint_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply, Pi.one_apply, Int.cast_zero,
      Int.cast_one, sub_zero, abs_le]
  all_goals repeat' apply And.intro
  all_goals linarith

private def CuspHoneycombTiling.floorCenter (x : Plane) : CuspHoneycombTiling.Lattice := fun i =>
  ⌊x i⌋ + squareCenter (Int.fract (x 0)) (Int.fract (x 1)) i

private theorem CuspHoneycombTiling.sub_latticePoint_floorCenter (x : Plane) :
    x - latticePoint (floorCenter x) =
      (![Int.fract (x 0), Int.fract (x 1)] : Plane) -
        latticePoint (squareCenter (Int.fract (x 0)) (Int.fract (x 1))) := by
  funext i
  simp only [Pi.sub_apply, latticePoint, floorCenter, Int.cast_add, sub_add_eq_sub_sub]
  rw [Int.self_sub_floor]
  fin_cases i <;> rfl

private theorem
    CuspHoneycombTiling.mem_cell_floorCenter (x : Plane) : x ∈ cell (floorCenter x) := by
  change x - latticePoint (floorCenter x) ∈ baseCell
  rw [sub_latticePoint_floorCenter]
  exact
    mem_cell_squareCenter _ _ (Int.fract_nonneg _) (Int.fract_lt_one _).le (Int.fract_nonneg _)
      (Int.fract_lt_one _).le

private theorem CuspHoneycombTiling.exists_mem_cell (x : Plane) :
    ∃ v : CuspHoneycombTiling.Lattice, x ∈ cell v :=
  ⟨floorCenter x, mem_cell_floorCenter x⟩

private theorem CuspHoneycombTiling.iUnion_cell :
    (⋃ v : CuspHoneycombTiling.Lattice, cell v) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact exists_mem_cell x

private theorem CuspHoneycombTiling.baseCell_isClosed : IsClosed baseCell := by
  have h0 : IsClosed {x : Plane | |2 * x 0 + x 1| ≤ 1} :=
    isClosed_le ((continuous_const.mul (continuous_apply 0)).add (continuous_apply 1)).abs
      continuous_const
  have h1 : IsClosed {x : Plane | |x 0 - x 1| ≤ 1} :=
    isClosed_le ((continuous_apply 0).sub (continuous_apply 1)).abs continuous_const
  have h2 : IsClosed {x : Plane | |x 0 + 2 * x 1| ≤ 1} :=
    isClosed_le ((continuous_apply 0).add (continuous_const.mul (continuous_apply 1))).abs
      continuous_const
  exact h0.inter (h1.inter h2)

private theorem CuspHoneycombTiling.baseCell_isCompact : IsCompact baseCell := by
  apply
    (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc (-1 : Plane) 1)).of_isClosed_subset
      baseCell_isClosed
  intro x hx
  exact
    ⟨fun i => (abs_le.mp (baseCell_coordinate_bound hx i)).1, fun i =>
      (abs_le.mp (baseCell_coordinate_bound hx i)).2⟩

private theorem
    CuspHoneycombTiling.cell_isClosed (v : CuspHoneycombTiling.Lattice) : IsClosed (cell v) :=
  baseCell_isClosed.preimage (continuous_id.sub continuous_const)

private theorem CuspHoneycombTiling.cell_finite_inter_ball (x : Plane) :
    {v : CuspHoneycombTiling.Lattice | (cell v ∩ Metric.ball x 1).Nonempty}.Finite := by
  have hbox : {v : CuspHoneycombTiling.Lattice | ∀ i, v i ∈ Set.Icc ⌈x i - 2⌉ ⌊x i + 2⌋}.Finite :=
    Set.Finite.pi' (fun i => Set.finite_Icc ⌈x i - 2⌉ ⌊x i + 2⌋)
  apply hbox.subset
  rintro v ⟨y, hyv, hyx⟩ i
  have hcoord := abs_le.mp (cell_coordinate_bound hyv i)
  have hdist : |y i - x i| < 1 := by
    simpa only [Real.dist_eq] using (dist_le_pi_dist y x i).trans_lt (Metric.mem_ball.mp hyx)
  have hnear := abs_lt.mp hdist
  constructor
  · apply Int.ceil_le.mpr
    linarith [hcoord.2, hnear.1]
  · apply Int.le_floor.mpr
    linarith [hcoord.1, hnear.2]

private theorem CuspHoneycombTiling.cell_locallyFinite : LocallyFinite cell := by
  intro x
  exact ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), cell_finite_inter_ball x⟩

private theorem
    CuspHoneycombTiling.baseCell_inter_cell_nonempty_iff (v : CuspHoneycombTiling.Lattice) :
    (baseCell ∩ cell v).Nonempty ↔
      v = 0 ∨
        v = ![1, 0] ∨ v = ![0, 1] ∨ v = ![1, -1] ∨ v = ![-1, 0] ∨ v = ![0, -1] ∨ v = ![-1, 1] := by
  constructor
  · rintro ⟨x, hx, hxv⟩
    have hcoord (i : Fin 2) : -1 ≤ v i ∧ v i ≤ 1 := by
      have hbase := abs_le.mp (baseCell_coordinate_bound_sharp hx i)
      have hshift := abs_le.mp (baseCell_coordinate_bound_sharp hxv i)
      change -(2 / 3 : ℝ) ≤ x i - (v i : ℝ) ∧ x i - (v i : ℝ) ≤ 2 / 3 at hshift
      have hlo : (-2 : ℝ) < (v i : ℝ) := by linarith [hbase.1, hshift.2]
      have hhi : (v i : ℝ) < (2 : ℝ) := by linarith [hbase.2, hshift.1]
      have hlo' : (-2 : ℤ) < v i := by exact_mod_cast hlo
      have hhi' : v i < (2 : ℤ) := by exact_mod_cast hhi
      omega
    have hbase := abs_le.mp hx.1
    have hshift := abs_le.mp hxv.1
    change
      (-1 : ℝ) ≤ 2 * (x 0 - (v 0 : ℝ)) + (x 1 - (v 1 : ℝ)) ∧
        2 * (x 0 - (v 0 : ℝ)) + (x 1 - (v 1 : ℝ)) ≤ 1 at hshift
    have hlinear : (-2 : ℝ) ≤ 2 * (v 0 : ℝ) + (v 1 : ℝ) ∧ 2 * (v 0 : ℝ) + (v 1 : ℝ) ≤ 2 := by
      constructor <;> linarith [hbase.1, hbase.2, hshift.1, hshift.2]
    have hlinear' : (-2 : ℤ) ≤ 2 * v 0 + v 1 ∧ 2 * v 0 + v 1 ≤ 2 := by exact_mod_cast hlinear
    have h0 := hcoord 0
    have h1 := hcoord 1
    simp only [funext_iff, Fin.forall_fin_two, Pi.zero_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    omega
  · intro hv
    refine ⟨fun i => (v i : ℝ) / 2, ?_, ?_⟩
    · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [baseCell]
    · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [cell, baseCell, latticePoint]

private theorem CuspHoneycombTiling.cell_inter_cell_nonempty_iff_baseCell
    (v w : CuspHoneycombTiling.Lattice) :
    (cell v ∩ cell w).Nonempty ↔ (baseCell ∩ cell (w - v)).Nonempty := by
  constructor
  · rintro ⟨x, hxv, hxw⟩
    refine ⟨x - latticePoint v, hxv, ?_⟩
    apply (add_latticePoint_mem_cell_iff (w - v) v (x - latticePoint v)).mp
    simpa only [sub_add_cancel] using hxw
  · rintro ⟨x, hx, hxwv⟩
    refine ⟨x + latticePoint v, ?_, ?_⟩
    · have h := (add_latticePoint_mem_cell_iff 0 v x).mpr (by simpa only [cell_zero] using hx)
      simpa only [zero_add] using h
    · simpa only [sub_add_cancel] using (add_latticePoint_mem_cell_iff (w - v) v x).mpr hxwv

private abbrev CuspHoneycombHexagon.Plane :=
  Fin 2 → ℝ

private abbrev CuspHoneycombHexagon.Square :=
  { p : Plane // ∀ i, p i ∈ Set.Icc (0 : ℝ) 1 }

private theorem CuspHoneycombHexagon.square_isCompact :
    IsCompact {p : Plane | ∀ i, p i ∈ Set.Icc (0 : ℝ) 1} :=
  isCompact_pi_infinite (fun _ => CompactIccSpace.isCompact_Icc)

private instance CuspHoneycombHexagon.square_compactSpace : CompactSpace Square :=
  isCompact_iff_compactSpace.mp square_isCompact

private def CuspHoneycombHexagon.SquareRel (i j : Fin 6) (p q : Square) : Prop :=
  (i = j ∧ p = q) ∨
    (j = i + 1 ∧ p.1 0 = 1 ∧ q.1 1 = 1 ∧ q.1 0 = p.1 1) ∨
      (i = j + 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = p.1 0) ∨ ((∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1))

private theorem CuspHoneycombHexagon.square_eq_of_all_one (p q : Square) (hp : ∀ k, p.1 k = 1)
    (hq : ∀ k, q.1 k = 1) : p = q := by
  apply Subtype.ext
  funext k
  exact (hp k).trans (hq k).symm

@[simp]
private theorem CuspHoneycombHexagon.squareRel_self (i : Fin 6) (p q : Square) :
    SquareRel i i p q ↔ p = q := by
  have hne : i ≠ i + 1 := (show ∀ i : Fin 6, i ≠ i + 1 by decide) i
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨hp, hq⟩)
    · exact h
    · exact (hne h).elim
    · exact (hne h).elim
    · exact square_eq_of_all_one p q hp hq
  · exact fun h => Or.inl ⟨rfl, h⟩

@[simp]
private theorem CuspHoneycombHexagon.squareRel_next (i : Fin 6) (p q : Square) :
    SquareRel i (i + 1) p q ↔ p.1 0 = 1 ∧ q.1 1 = 1 ∧ q.1 0 = p.1 1 := by
  have hne : i ≠ i + 1 := (show ∀ i : Fin 6, i ≠ i + 1 by decide) i
  have hne₂ : i ≠ (i + 1) + 1 := (show ∀ i : Fin 6, i ≠ (i + 1) + 1 by decide) i
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨hp, hq⟩)
    · exact (hne h).elim
    · exact h
    · exact (hne₂ h).elim
    · exact ⟨hp 0, hq 1, (hq 0).trans (hp 1).symm⟩
  · exact fun h => Or.inr (Or.inl ⟨rfl, h⟩)

@[simp]
private theorem CuspHoneycombHexagon.squareRel_prev (i : Fin 6) (p q : Square) :
    SquareRel i (i + 5) p q ↔ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = p.1 0 := by
  have hne : i ≠ i + 5 := (show ∀ i : Fin 6, i ≠ i + 5 by decide) i
  have hnext : i + 5 ≠ i + 1 := (show ∀ i : Fin 6, i + 5 ≠ i + 1 by decide) i
  have hprev : i = (i + 5) + 1 := (show ∀ i : Fin 6, i = (i + 5) + 1 by decide) i
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨hp, hq⟩)
    · exact (hne h).elim
    · exact (hnext h).elim
    · exact h
    · exact ⟨hp 1, hq 0, (hq 1).trans (hp 0).symm⟩
  · exact fun h => Or.inr (Or.inr (Or.inl ⟨hprev, h⟩))

private theorem
    CuspHoneycombHexagon.squareRel_nonadjacent (i j : Fin 6) (p q : Square) (hij : i ≠ j)
    (hnext : j ≠ i + 1) (hprev : i ≠ j + 1) :
    SquareRel i j p q ↔ (∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1) := by
  simp only [SquareRel, hij, hnext, hprev, false_and, false_or]

@[simp]
private theorem CuspHoneycombHexagon.squareRel_add_two (i : Fin 6) (p q : Square) :
    SquareRel i (i + 2) p q ↔ (∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1) :=
  squareRel_nonadjacent i (i + 2) p q ((show ∀ i : Fin 6, i ≠ i + 2 by decide) i)
    ((show ∀ i : Fin 6, i + 2 ≠ i + 1 by decide) i)
    ((show ∀ i : Fin 6, i ≠ (i + 2) + 1 by decide) i)

@[simp]
private theorem CuspHoneycombHexagon.squareRel_add_three (i : Fin 6) (p q : Square) :
    SquareRel i (i + 3) p q ↔ (∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1) :=
  squareRel_nonadjacent i (i + 3) p q ((show ∀ i : Fin 6, i ≠ i + 3 by decide) i)
    ((show ∀ i : Fin 6, i + 3 ≠ i + 1 by decide) i)
    ((show ∀ i : Fin 6, i ≠ (i + 3) + 1 by decide) i)

@[simp]
private theorem CuspHoneycombHexagon.squareRel_add_four (i : Fin 6) (p q : Square) :
    SquareRel i (i + 4) p q ↔ (∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1) :=
  squareRel_nonadjacent i (i + 4) p q ((show ∀ i : Fin 6, i ≠ i + 4 by decide) i)
    ((show ∀ i : Fin 6, i + 4 ≠ i + 1 by decide) i)
    ((show ∀ i : Fin 6, i ≠ (i + 4) + 1 by decide) i)

private def ToricCharts.zeroCount (z : CoordinateSpace 3) : ℕ :=
  Nat.card { j : Fin 3 // z j = 0 }

private def ToricCharts.vanishingIndices (z : CoordinateSpace 3) : Finset (Fin 3) := by
  classical exact Finset.univ.filter (fun j => z j = 0)

@[simp]
private theorem ToricCharts.mem_vanishingIndices (z : CoordinateSpace 3) (j : Fin 3) :
    j ∈ vanishingIndices z ↔ z j = 0 := by classical simp [vanishingIndices]

private theorem ToricCharts.vanishingIndices_card (z : CoordinateSpace 3) :
    (vanishingIndices z).card = zeroCount z := by
  classical
  rw [zeroCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

private theorem ToricCharts.vanishingIndices_nonempty (z : CoordinateSpace 3) :
    (vanishingIndices z).Nonempty ↔ ToricFan.Triangle.time z = 0 := by
  constructor
  · rintro ⟨j, hj⟩
    have hp : ∏ k, z k = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) ((mem_vanishingIndices z j).mp hj)
    simpa [ToricFan.Triangle.time, Fin.prod_univ_succ, mul_assoc] using hp
  · intro hz
    obtain h | h | h := (ToricFan.Triangle.central_fibre z).mp hz
    · exact ⟨0, (mem_vanishingIndices z 0).mpr h⟩
    · exact ⟨1, (mem_vanishingIndices z 1).mpr h⟩
    · exact ⟨2, (mem_vanishingIndices z 2).mpr h⟩

private theorem ToricCharts.zeroCount_pos_iff (z : CoordinateSpace 3) :
    0 < zeroCount z ↔ ToricFan.Triangle.time z = 0 := by
  rw [← vanishingIndices_card, Finset.card_pos, vanishingIndices_nonempty]

@[simp]
private theorem ToricCharts.zeroCount_zero : zeroCount (0 : CoordinateSpace 3) = 3 := by
  classical simp [zeroCount, Nat.card_eq_fintype_card]

public
theorem ToricCharts.equal_columns_of_left_inverse {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hBA : B * A = 1) {j k : Fin 3} (hcol : ∀ i, A i j = A i k) : j = k := by
  have he : (B * A) j j = (B * A) j k := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun c => B j i * c) (hcol i))
  rw [hBA] at he
  by_contra hne
  simp [hne] at he

private theorem
    ToricCharts.zeroCount_le_monomial {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A)
    (hBA : B * A = 1) {z : CoordinateSpace 3} (hz : z ∈ domain A) :
    zeroCount z ≤ zeroCount (monomial A z) := by
  have hcol (j : { j : Fin 3 // z j = 0 }) : ∃ k : Fin 3, ∀ i, A i j = if i = k then 1 else 0 :=
    column_single_of_zero hA hz j.2
  choose f hf using hcol
  let g : { j : Fin 3 // z j = 0 } → { k : Fin 3 // monomial A z k = 0 } := fun j =>
    ⟨f j, monomial_zero_of_column_single j.2 (hf j)⟩
  apply Nat.card_le_card_of_injective g
  intro j k h
  have hfk : f j = f k := congrArg Subtype.val h
  apply Subtype.ext
  apply equal_columns_of_left_inverse hBA
  intro i
  rw [hf j i, hf k i, hfk]

private theorem ToricCharts.zeroCount_monomial {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A)
    (hB : HeightOne B) (hAB : A * B = 1) (hBA : B * A = 1) {z : CoordinateSpace 3}
    (hz : z ∈ domain A) : zeroCount (monomial A z) = zeroCount z := by
  have hw := inverse_mapsTo_domain hA hBA hz
  have he : monomial B (monomial A z) = z := monomial_inverse_on_overlap A B hBA ⟨hz, hw⟩
  have hle := zeroCount_le_monomial hB hAB hw
  rw [he] at hle
  exact le_antisymm hle (zeroCount_le_monomial hA hBA hz)

private theorem ToricCharts.zeroCount_mul (u z : CoordinateSpace 3) (hu : ∀ j, u j ≠ 0) :
    zeroCount (u * z) = zeroCount z := by
  apply Nat.card_congr
  exact
    Equiv.subtypeEquivRight (fun j => by simp only [Pi.mul_apply, mul_eq_zero, hu j, false_or])

private theorem ToricFan.Triangle.zeroCount_chartChange (s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ (chartChange s t).source) :
    ToricCharts.zeroCount (chartChange s t z) = ToricCharts.zeroCount z := by
  apply
    ToricCharts.zeroCount_monomial (transition_heightOne s t) (transition_heightOne t s)
      (by rw [transition_mul, transition_self]) (by rw [transition_mul, transition_self])
  simpa only [chartChange_source] using hz

private theorem ToricFan.Triangle.origin_mem_chartChange_source (s t : ToricFan.Triangle) :
    (0 : ToricCharts.CoordinateSpace 3) ∈ (chartChange s t).source ↔ s = t := by
  constructor
  · intro hz
    rw [chartChange_source] at hz
    have hn (i j : Fin 3) : 0 ≤ transition s t i j := by
      by_contra h
      exact hz i j (lt_of_not_ge h) rfl
    have h00 := hn 0 0
    have h01 := hn 0 1
    have h02 := hn 0 2
    have h10 := hn 1 0
    have h11 := hn 1 1
    have h12 := hn 1 2
    have h20 := hn 2 0
    have h21 := hn 2 1
    have h22 := hn 2 2
    cases hs : s.upper <;> cases ht : t.upper
    all_goals
      simp [transition, dual, rays, hs, ht, Matrix.mul_apply,
        Fin.sum_univ_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h22
    all_goals
      first
      | omega
      | apply ToricFan.Triangle.ext
        · omega
        · omega
        · simp [hs, ht]
  · rintro rfl
    rw [chartChange_self_source]
    exact Set.mem_univ _

private def ToricSpace.branchCount (x : Space) : ℕ :=
  ToricCharts.zeroCount ((parametrization (preferredTriangle x)).symm x)

private theorem ToricSpace.branchCount_inclusion (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    branchCount (ToricSpace.inclusion s z) = ToricCharts.zeroCount z := by
  have he :=
    parametrization_transition s (preferredTriangle (ToricSpace.inclusion s z))
      (preferred_mem (ToricSpace.inclusion s z))
  unfold branchCount
  rw [he.2]
  exact ToricFan.Triangle.zeroCount_chartChange s _ he.1

private theorem ToricSpace.branchCount_pos_iff (x : Space) : 0 < branchCount x ↔ time x = 0 := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [branchCount_inclusion, ToricCharts.zeroCount_pos_iff, time_inclusion]

private theorem ToricSpace.inclusion_origin_injective (s t : ToricFan.Triangle) :
    ToricSpace.inclusion s 0 = ToricSpace.inclusion t 0 ↔ s = t := by
  constructor
  · intro he
    exact
      (ToricFan.Triangle.origin_mem_chartChange_source s t).mp
        ((inclusion_eq_iff s t 0 0).mp he).1
  · rintro rfl
    rfl

private theorem
    ToricSpace.twistedTranslate_origin (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (s : ToricFan.Triangle) :
    twistedTranslate C v (ToricSpace.inclusion s 0) =
      ToricSpace.inclusion (s.shift (cuspVector v)) 0 := by
  simp [twistedTranslate, translate_inclusion, variableMultiplier, scale]

@[simp]
private theorem ToricSpace.branchCount_translate (v : Fin 2 → ℤ) (x : Space) :
    branchCount (ToricSpace.translate v x) = branchCount x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [translate_inclusion, branchCount_inclusion, branchCount_inclusion]

@[simp]
private theorem ToricSpace.branchCount_torusAction (u : ActingTorus) (x : Space) :
    branchCount (torusAction u x) = branchCount x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [torusAction_inclusion, branchCount_inclusion, branchCount_inclusion]
  exact ToricCharts.zeroCount_mul (factors s u) z (factors_nonzero s u)

@[simp]
private theorem
    ToricSpace.branchCount_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (x : Space) : branchCount (twistedTranslate C v x) = branchCount x := by
  simp [twistedTranslate, variableMultiplier]

private def ToricFan.Triangle.vertex (s : ToricFan.Triangle) (j : Fin 3) : Fin 2 → ℤ := fun i =>
  s.rays i.castSucc j

private theorem ToricFan.Triangle.vertex_eq_iff (s t : ToricFan.Triangle) (j k : Fin 3) :
    s.vertex j = t.vertex k ↔ ∀ i, s.rays i j = t.rays i k := by
  constructor
  · intro h i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
    · simp
  · intro h
    funext i
    exact h i.castSucc

private theorem ToricFan.Triangle.vertex_injective (s : ToricFan.Triangle) :
    Function.Injective s.vertex := by
  intro j k h
  exact ToricCharts.equal_columns_of_left_inverse s.dual_rays ((vertex_eq_iff s s j k).mp h)

private theorem
    ToricFan.Triangle.transition_column_iff_vertex (s t : ToricFan.Triangle) (j k : Fin 3) :
    (∀ i, transition s t i j = if i = k then 1 else 0) ↔ s.vertex j = t.vertex k := by
  rw [vertex_eq_iff]
  constructor
  · intro h i
    have hc := congrFun (congrFun (transition_covariance s t) i) j
    simpa only [Matrix.mul_apply, h, mul_ite, mul_one, MulZeroClass.mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using hc.symm
  · intro h i
    have hc := congrFun (congrFun t.dual_rays i) k
    simpa only [transition, Matrix.mul_apply, h, Matrix.one_apply] using hc

@[simp]
private theorem ToricFan.Triangle.vertex_shift (s : ToricFan.Triangle) (v : Fin 2 → ℤ) (j : Fin 3) :
    (s.shift v).vertex j = s.vertex j + v := by
  ext i
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;> simp [vertex, shift, rays, hs] <;> ring

private def
    ToricFan.Triangle.chartBranches (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    Set (Fin 2 → ℤ) :=
  s.vertex '' {j | z j = 0}

private theorem ToricFan.Triangle.chartBranches_finite (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) : (chartBranches s z).Finite :=
  (Set.toFinite _).image _

private theorem ToricFan.Triangle.chartBranches_ncard (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) : (chartBranches s z).ncard = ToricCharts.zeroCount z := by
  rw [chartBranches, Set.ncard_image_of_injective _ (vertex_injective s)]
  rfl

private theorem ToricFan.Triangle.chartBranches_subset_change (s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ (chartChange s t).source) :
    chartBranches s z ⊆ chartBranches t (chartChange s t z) := by
  rintro v ⟨j, hj, rfl⟩
  obtain ⟨k, hk⟩ :=
    ToricCharts.column_single_of_zero (transition_heightOne s t)
      (by simpa only [chartChange_source] using hz) hj
  refine ⟨k, ToricCharts.monomial_zero_of_column_single hj hk, ?_⟩
  exact ((transition_column_iff_vertex s t j k).mp hk).symm

private theorem ToricFan.Triangle.chartBranches_change (s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ (chartChange s t).source) :
    chartBranches t (chartChange s t z) = chartBranches s z := by
  apply subset_antisymm
  · have h := chartBranches_subset_change t s ((chartChange s t).map_source hz)
    have hi : chartChange t s (chartChange s t z) = z := (chartChange s t).left_inv hz
    rwa [hi] at h
  · exact chartBranches_subset_change s t hz

private theorem ToricFan.Triangle.chartBranches_mul (s : ToricFan.Triangle)
    (u z : ToricCharts.CoordinateSpace 3) (hu : ∀ j, u j ≠ 0) :
    chartBranches s (u * z) = chartBranches s z := by
  unfold chartBranches
  congr 1
  ext j
  simp [hu]

private theorem ToricFan.Triangle.chartBranches_shift (s : ToricFan.Triangle) (v : Fin 2 → ℤ)
    (z : ToricCharts.CoordinateSpace 3) :
    chartBranches (s.shift v) z = (fun w => w + v) '' chartBranches s z := by
  simp only [chartBranches, Set.image_image, vertex_shift]

private def ToricSpace.branchVertices : Space → Set (Fin 2 → ℤ) :=
  descend ToricFan.Triangle.chartBranches

@[simp]
private theorem ToricSpace.branchVertices_inclusion (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    branchVertices (ToricSpace.inclusion s z) = ToricFan.Triangle.chartBranches s z :=
  descend_inclusion ToricFan.Triangle.chartBranches
    (fun s t _ hz => ToricFan.Triangle.chartBranches_change s t hz) s z

private theorem ToricSpace.branchVertices_finite (x : Space) : (branchVertices x).Finite :=
  ToricFan.Triangle.chartBranches_finite _ _

private theorem
    ToricSpace.branchVertices_ncard (x : Space) : (branchVertices x).ncard = branchCount x :=
  ToricFan.Triangle.chartBranches_ncard _ _

private theorem ToricSpace.branchVertices_nonempty (x : Space) :
    (branchVertices x).Nonempty ↔ time x = 0 := by
  rw [← Set.ncard_pos (branchVertices_finite x), branchVertices_ncard, branchCount_pos_iff]

private def ToricSpace.rayDivisor (v : Fin 2 → ℤ) : Set Space :=
  {x | v ∈ branchVertices x}

private theorem ToricSpace.mem_rayDivisor_inclusion (v : Fin 2 → ℤ) (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricSpace.inclusion s z ∈ rayDivisor v ↔ ∃ j, z j = 0 ∧ s.vertex j = v := by
  change v ∈ branchVertices (ToricSpace.inclusion s z) ↔ _
  rw [branchVertices_inclusion]
  rfl

private theorem ToricSpace.mem_rayDivisor_vertex (s : ToricFan.Triangle) (j : Fin 3)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricSpace.inclusion s z ∈ rayDivisor (s.vertex j) ↔ z j = 0 := by
  rw [mem_rayDivisor_inclusion]
  constructor
  · rintro ⟨k, hk, he⟩
    rwa [(ToricFan.Triangle.vertex_injective s) he] at hk
  · intro hj
    exact ⟨j, hj, rfl⟩

private theorem ToricSpace.preimage_rayDivisor (v : Fin 2 → ℤ) (s : ToricFan.Triangle) :
    ToricSpace.inclusion s ⁻¹' rayDivisor v = ⋃ j : Fin 3, {z | z j = 0 ∧ s.vertex j = v} := by
  ext z
  simp only [Set.mem_preimage, mem_rayDivisor_inclusion, Set.mem_iUnion, Set.mem_ofPred_eq]

private theorem ToricSpace.rayDivisor_isClosed (v : Fin 2 → ℤ) : IsClosed (rayDivisor v) := by
  rw [← isOpen_compl_iff, gluing.isOpen_iff]
  change ∀ s : ToricFan.Triangle, IsOpen (ToricSpace.inclusion s ⁻¹' (rayDivisor v)ᶜ)
  intro s
  rw [Set.preimage_compl, isOpen_compl_iff, preimage_rayDivisor]
  apply isClosed_iUnion_of_finite
  intro j
  exact (isClosed_eq (continuous_apply j) continuous_const).inter isClosed_const

private theorem ToricSpace.time_eq_zero_of_mem_rayDivisor {v : Fin 2 → ℤ} {x : Space}
    (hx : x ∈ rayDivisor v) : time x = 0 :=
  (branchVertices_nonempty x).mp ⟨v, hx⟩

private theorem
    ToricSpace.central_fibre_eq_rayDivisors : time ⁻¹' {0} = ⋃ v : Fin 2 → ℤ, rayDivisor v := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, rayDivisor,
    Set.mem_ofPred_eq, ← branchVertices_nonempty, Set.nonempty_def]

private theorem ToricSpace.branchVertices_translate (v : Fin 2 → ℤ) (x : Space) :
    branchVertices (ToricSpace.translate v x) = (fun w => w + v) '' branchVertices x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [translate_inclusion, branchVertices_inclusion, branchVertices_inclusion,
    ToricFan.Triangle.chartBranches_shift]

private theorem ToricSpace.branchVertices_torusAction (u : ActingTorus) (x : Space) :
    branchVertices (torusAction u x) = branchVertices x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [torusAction_inclusion, branchVertices_inclusion, branchVertices_inclusion]
  exact ToricFan.Triangle.chartBranches_mul s (factors s u) z (factors_nonzero s u)

private theorem ToricSpace.branchVertices_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : Space) :
    branchVertices (twistedTranslate C v x) = (fun w => w + cuspVector v) '' branchVertices x := by
  simp only [twistedTranslate, variableMultiplier, branchVertices_torusAction,
    branchVertices_translate]

private theorem ToricSpace.twistedTranslate_mem_rayDivisor (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v w : Fin 2 → ℤ) (x : Space) :
    twistedTranslate C v x ∈ rayDivisor w ↔ x ∈ rayDivisor (w - cuspVector v) := by
  change w ∈ branchVertices (twistedTranslate C v x) ↔ _
  rw [branchVertices_twistedTranslate]
  constructor
  · rintro ⟨u, hu, he⟩
    have : u = w - cuspVector v := eq_sub_iff_add_eq.mpr he
    rwa [← this]
  · intro hx
    exact ⟨w - cuspVector v, hx, sub_add_cancel _ _⟩

private def ToricComponent.insertZero (j : Fin 3) (z : ToricCharts.CoordinateSpace 2) :
    ToricCharts.CoordinateSpace 3 :=
  Fin.insertNth j 0 z

private def ToricComponent.removeCoordinate (j : Fin 3) (z : ToricCharts.CoordinateSpace 3) :
    ToricCharts.CoordinateSpace 2 :=
  Fin.removeNth j z

@[simp]
private theorem ToricComponent.insertZero_at (j : Fin 3) (z : ToricCharts.CoordinateSpace 2) :
    insertZero j z j = 0 :=
  Fin.insertNth_apply_same (α := fun _ : Fin 3 => ℂ) j 0 z

@[simp]
private theorem ToricComponent.removeCoordinate_insertZero (j : Fin 3)
    (z : ToricCharts.CoordinateSpace 2) : removeCoordinate j (insertZero j z) = z :=
  Fin.removeNth_insertNth (α := fun _ : Fin 3 => ℂ) j 0 z

private theorem
    ToricComponent.insertZero_removeCoordinate (j : Fin 3) (z : ToricCharts.CoordinateSpace 3)
    (hz : z j = 0) : insertZero j (removeCoordinate j z) = z :=
  Fin.insertNth_eq_iff.mpr ⟨hz.symm, rfl⟩

private theorem
    ToricComponent.insertZero_holomorphic (j : Fin 3) : ContDiff ℂ ω (insertZero j) := by
  apply contDiff_pi.mpr
  intro k
  obtain rfl | ⟨l, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
  · simpa only [insertZero_at] using
      (contDiff_const : ContDiff ℂ ω (fun _ : ToricCharts.CoordinateSpace 2 => (0 : ℂ)))
  · simpa only [insertZero, Fin.insertNth_apply_succAbove] using (contDiff_apply ℂ ℂ l)

private theorem ToricComponent.removeCoordinate_holomorphic (j : Fin 3) :
    ContDiff ℂ ω (removeCoordinate j) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_apply ℂ ℂ (j.succAbove i)

private structure ToricComponent.ChartIndex (v : Fin 2 → ℤ) where
  triangle : ToricFan.Triangle
  coordinate : Fin 3
  vertex_eq : triangle.vertex coordinate = v

private theorem ToricComponent.insertZero_mem {v : Fin 2 → ℤ} (c : ChartIndex v)
    (z : ToricCharts.CoordinateSpace 2) :
    ToricSpace.inclusion c.triangle (insertZero c.coordinate z) ∈ ToricSpace.rayDivisor v := by
  have h :=
    (ToricSpace.mem_rayDivisor_vertex c.triangle c.coordinate (insertZero c.coordinate z)).mpr
      (insertZero_at c.coordinate z)
  simpa only [c.vertex_eq] using h

private def ToricComponent.planeHomeomorph {v : Fin 2 → ℤ} (c : ChartIndex v) :
    ToricCharts.CoordinateSpace 2 ≃ₜ
      ToricSpace.inclusion c.triangle ⁻¹' ToricSpace.rayDivisor v := by
  refine
    { toFun := fun z => ⟨insertZero c.coordinate z, insertZero_mem c z⟩
      invFun := fun w => removeCoordinate c.coordinate w
      left_inv := fun z => removeCoordinate_insertZero c.coordinate z
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro w
    apply Subtype.ext
    apply insertZero_removeCoordinate
    have hw :
      ToricSpace.inclusion c.triangle (w : ToricCharts.CoordinateSpace 3) ∈
        ToricSpace.rayDivisor v :=
      w.2
    exact
      (ToricSpace.mem_rayDivisor_vertex c.triangle c.coordinate w).mp
        (by simpa only [c.vertex_eq] using hw)
  · exact (insertZero_holomorphic c.coordinate).continuous.subtype_mk _
  · exact (removeCoordinate_holomorphic c.coordinate).continuous.comp continuous_subtype_val

private def ToricComponent.affineInclusion {v : Fin 2 → ℤ} (c : ChartIndex v)
    (z : ToricCharts.CoordinateSpace 2) : ToricSpace.rayDivisor v :=
  ⟨ToricSpace.inclusion c.triangle (insertZero c.coordinate z), insertZero_mem c z⟩

private theorem ToricComponent.affineInclusion_openEmbedding {v : Fin 2 → ℤ} (c : ChartIndex v) :
    Topology.IsOpenEmbedding (affineInclusion c) :=
  ((ToricSpace.inclusion_openEmbedding c.triangle).restrictPreimage
        (ToricSpace.rayDivisor v)).comp
    (planeHomeomorph c).isOpenEmbedding

private theorem ToricComponent.affineInclusion_jointly_surjective {v : Fin 2 → ℤ}
    (x : ToricSpace.rayDivisor v) :
    ∃ c : ChartIndex v, ∃ z : ToricCharts.CoordinateSpace 2, affineInclusion c z = x := by
  obtain ⟨s, z, hz⟩ := ToricSpace.inclusion_jointly_surjective (x : ToricSpace.Space)
  have hx : ToricSpace.inclusion s z ∈ ToricSpace.rayDivisor v := by rw [hz]; exact x.2
  obtain ⟨j, hj, hv⟩ := (ToricSpace.mem_rayDivisor_inclusion v s z).mp hx
  refine ⟨⟨s, j, hv⟩, removeCoordinate j z, ?_⟩
  apply Subtype.ext
  change ToricSpace.inclusion s (insertZero j (removeCoordinate j z)) = (x : ToricSpace.Space)
  rw [insertZero_removeCoordinate j z hj]
  exact hz

private def
    CuspQuotient.branchCount (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) : QuotientSpace C ε → ℕ :=
  Quotient.lift
    (fun x : ToricSpace.Tube (disc ε) => ToricSpace.branchCount (x : ToricSpace.Space))
    (by
      let := ToricSpace.tubeAction C (disc ε)
      intro x y h
      change x ∈ MulAction.orbit LatticeGroup y at h
      obtain ⟨g, rfl⟩ := h
      exact ToricSpace.branchCount_twistedTranslate C g.toAdd y)

private theorem
    CuspQuotient.centralChartMap_origin_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (s t : ToricFan.Triangle) :
    centralChartMap C ε hε s centralOrigin = centralChartMap C ε hε t centralOrigin ↔
      s.upper = t.upper := by
  let := ToricSpace.tubeAction C (disc ε)
  constructor
  · intro he
    have horb := Quotient.exact he
    change
      centralLift ε hε s centralOrigin ∈
        MulAction.orbit LatticeGroup (centralLift ε hε t centralOrigin) at horb
    obtain ⟨g, hg⟩ := horb
    have he' :
      ToricSpace.twistedTranslate C g.toAdd (ToricSpace.inclusion t 0) =
        ToricSpace.inclusion s 0 :=
      congrArg Subtype.val hg
    rw [ToricSpace.twistedTranslate_origin] at he'
    have hst := (ToricSpace.inclusion_origin_injective _ _).mp he'
    exact (congrArg ToricFan.Triangle.upper hst).symm
  · intro hst
    rw [centralChartMap_origin_reference C ε hε s, centralChartMap_origin_reference C ε hε t, hst]

@[simp]
private theorem ToricSpace.cuspVector_neg (v : Fin 2 → ℤ) : cuspVector (-v) = -cuspVector v := by
  ext i
  fin_cases i <;> simp [cuspVector]

@[simp]
private theorem
    ToricSpace.cuspVector_cuspVector (v : Fin 2 → ℤ) : cuspVector (cuspVector v) = -v := by
  ext i
  fin_cases i <;> simp [cuspVector]

private theorem ToricSpace.cuspVector_injective : Function.Injective cuspVector := by
  intro v w h
  have h' := congrArg cuspVector h
  simpa only [cuspVector_cuspVector, neg_inj] using h'

private def CuspQuotient.componentLift (ε : ℝ) (hε : 0 < ε) (x : ToricSpace.rayDivisor 0) :
    ToricSpace.Tube (disc ε) :=
  ⟨x, by
    change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
    rw [ToricSpace.time_eq_zero_of_mem_rayDivisor x.2]
    simpa using hε⟩

private theorem ToricSpace.rayDivisors_locallyFinite : LocallyFinite rayDivisor := by
  intro x
  let s := preferredTriangle x
  refine
    ⟨Set.range (ToricSpace.inclusion s),
      (inclusion_openEmbedding s).isOpen_range.mem_nhds (preferred_mem x), ?_⟩
  apply (Set.finite_range s.vertex).subset
  rintro v ⟨y, hy, ⟨z, rfl⟩⟩
  obtain ⟨j, _, hj⟩ := (mem_rayDivisor_inclusion v s z).mp hy
  exact ⟨j, hj⟩

private def
    ToricSpace.centralTranslationHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    Space ≃ₜ Space :=
  (translationHomeomorph (cuspVector v)).trans
    (torusHomeomorph (fibreMultiplier (exponentialMultiplier C v 0)))

private def ToricComponent.zeroTriangle : Fin 6 → ToricFan.Triangle :=
  ![⟨0, 0, Bool.false⟩, ⟨-1, 0, Bool.true⟩, ⟨-1, 0, Bool.false⟩, ⟨-1, -1, Bool.true⟩,
    ⟨0, -1, Bool.false⟩, ⟨0, -1, Bool.true⟩]

private def ToricComponent.zeroCoordinate : Fin 6 → Fin 3 :=
  ![0, 0, 1, 2, 2, 1]

private theorem ToricComponent.zeroTriangle_vertex (i : Fin 6) :
    (zeroTriangle i).vertex (zeroCoordinate i) = 0 := by fin_cases i <;> decide

private def ToricComponent.zeroChart (i : Fin 6) : ChartIndex 0 :=
  ⟨zeroTriangle i, zeroCoordinate i, zeroTriangle_vertex i⟩

private theorem ToricComponent.zeroChart_surjective : Function.Surjective zeroChart := by
  rintro ⟨⟨a, b, u⟩, j, hj⟩
  have h0 := congrFun hj 0
  have h1 := congrFun hj 1
  cases u <;> fin_cases j
  · change a = 0 at h0
    change b = 0 at h1
    subst a b
    exact ⟨0, rfl⟩
  · change a + 1 = 0 at h0
    change b = 0 at h1
    have ha : a = -1 := by omega
    subst a b
    exact ⟨2, rfl⟩
  · change a = 0 at h0
    change b + 1 = 0 at h1
    have hb : b = -1 := by omega
    subst a b
    exact ⟨4, rfl⟩
  · change a + 1 = 0 at h0
    change b = 0 at h1
    have ha : a = -1 := by omega
    subst a b
    exact ⟨1, rfl⟩
  · change a = 0 at h0
    change b + 1 = 0 at h1
    have hb : b = -1 := by omega
    subst a b
    exact ⟨5, rfl⟩
  · change a + 1 = 0 at h0
    change b + 1 = 0 at h1
    have ha : a = -1 := by omega
    have hb : b = -1 := by omega
    subst a b
    exact ⟨3, rfl⟩

private def ToricComponent.hexagonRay : Fin 6 → (Fin 2 → ℤ) :=
  ![![1, 0], ![0, 1], ![-1, 1], ![-1, 0], ![0, -1], ![1, -1] ]

private theorem ToricComponent.hexagonRay_injective : Function.Injective hexagonRay := by decide

private theorem ToricComponent.hexagonRay_ne_zero (i : Fin 6) : hexagonRay i ≠ 0 := by
  fin_cases i <;> decide

private theorem
    ToricComponent.hexagonRay_opposite (i : Fin 6) : hexagonRay (i + 3) = -hexagonRay i := by
  fin_cases i <;> decide

private def CuspHoneycombHexagon.vertex (i : Fin 6) : Plane := fun k =>
  (ToricComponent.hexagonRay i k : ℝ)

private def CuspHoneycombHexagon.midpoint (i : Fin 6) : Plane :=
  (1 / 2 : ℝ) • (vertex (i - 1) + vertex i)

private def CuspHoneycombHexagon.Hexagon : Set Plane :=
  {x | |x 0| ≤ 1 ∧ |x 1| ≤ 1 ∧ |x 0 + x 1| ≤ 1}

private def CuspHoneycombHexagon.sideFunctional (k : Fin 6) (x : Plane) : ℝ :=
  ![x 0, x 0 + x 1, x 1, -x 0, -x 0 - x 1, -x 1] k

private def CuspHoneycombHexagon.side (k : Fin 6) : Set Plane :=
  {x | x ∈ Hexagon ∧ sideFunctional k x = 1}

@[simp]
private theorem CuspHoneycombHexagon.sideFunctional_zero (x : Plane) : sideFunctional 0 x = x 0 :=
  rfl

@[simp]
private theorem
    CuspHoneycombHexagon.sideFunctional_one (x : Plane) : sideFunctional 1 x = x 0 + x 1 :=
  rfl

@[simp]
private theorem CuspHoneycombHexagon.sideFunctional_two (x : Plane) : sideFunctional 2 x = x 1 :=
  rfl

@[simp]
private theorem CuspHoneycombHexagon.sideFunctional_three (x : Plane) : sideFunctional 3 x = -x 0 :=
  rfl

@[simp]
private theorem
    CuspHoneycombHexagon.sideFunctional_four (x : Plane) : sideFunctional 4 x = -x 0 - x 1 :=
  rfl

@[simp]
private theorem CuspHoneycombHexagon.sideFunctional_five (x : Plane) : sideFunctional 5 x = -x 1 :=
  rfl

private def CuspHoneycombHexagon.cornerZero : Square :=
  ⟨fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩⟩

private def CuspHoneycombHexagon.cornerOne : Square :=
  ⟨fun _ => 1, fun _ => ⟨zero_le_one, le_rfl⟩⟩

private def CuspHoneycombHexagon.tile (i : Fin 6) (p : Square) : Plane :=
  (1 - Max.max (p.1 0) (p.1 1)) • vertex i +
      Max.max (p.1 1 - p.1 0) 0 • CuspHoneycombHexagon.midpoint i +
    Max.max (p.1 0 - p.1 1) 0 • CuspHoneycombHexagon.midpoint (i + 1)

private theorem CuspHoneycombHexagon.tile_continuous (i : Fin 6) : Continuous (tile i) := by
  have h0 : Continuous (fun p : Square => p.1 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous (fun p : Square => p.1 1) :=
    (continuous_apply 1).comp continuous_subtype_val
  exact
    (((continuous_const.sub (h0.max h1)).smul continuous_const).add
          (((h1.sub h0).max continuous_const).smul continuous_const)).add
      (((h0.sub h1).max continuous_const).smul continuous_const)

private theorem CuspHoneycombHexagon.tile_of_le (i : Fin 6) (p : Square) (hp : p.1 0 ≤ p.1 1) :
    tile i p = (1 - p.1 1) • vertex i + (p.1 1 - p.1 0) • CuspHoneycombHexagon.midpoint i := by
  simp only [tile, max_eq_right hp, max_eq_left (sub_nonneg.mpr hp),
    max_eq_right (sub_nonpos.mpr hp), zero_smul, add_zero]

private theorem CuspHoneycombHexagon.tile_of_ge (i : Fin 6) (p : Square) (hp : p.1 1 ≤ p.1 0) :
    tile i p = (1 - p.1 0) • vertex i + (p.1 0 - p.1 1) • CuspHoneycombHexagon.midpoint (i + 1) :=
  by
  simp only [tile, max_eq_left hp, max_eq_right (sub_nonpos.mpr hp),
    max_eq_left (sub_nonneg.mpr hp), zero_smul, add_zero]

private theorem CuspHoneycombHexagon.tile_fst_one (i : Fin 6) (p : Square) (hp : p.1 0 = 1) :
    tile i p = (1 - p.1 1) • CuspHoneycombHexagon.midpoint (i + 1) := by
  rw [tile_of_ge i p (by simpa only [hp] using (p.2 1).2)]
  simp only [hp, sub_self, zero_smul, zero_add]

private theorem CuspHoneycombHexagon.tile_fst_zero (i : Fin 6) (p : Square) (hp : p.1 0 = 0) :
    tile i p = (1 - p.1 1) • vertex i + p.1 1 • CuspHoneycombHexagon.midpoint i := by
  rw [tile_of_le i p (by simpa only [hp] using (p.2 1).1)]
  simp only [hp, sub_zero]

@[simp]
private theorem
    CuspHoneycombHexagon.tile_cornerZero (i : Fin 6) : tile i cornerZero = vertex i := by
  rw [tile_fst_zero i cornerZero rfl]
  simp only [cornerZero, sub_zero, one_smul, zero_smul, add_zero]

@[simp]
private theorem CuspHoneycombHexagon.tile_cornerOne (i : Fin 6) : tile i cornerOne = 0 := by
  rw [tile_fst_one i cornerOne rfl]
  simp only [cornerOne, sub_self, zero_smul]

@[simp]
private theorem CuspHoneycombHexagon.vertex_zero : vertex 0 = ![1, 0] := by
  funext k
  fin_cases k
  · change ((1 : ℤ) : ℝ) = 1
    norm_num
  · change ((0 : ℤ) : ℝ) = 0
    norm_num

@[simp]
private theorem CuspHoneycombHexagon.vertex_one : vertex 1 = ![0, 1] := by
  funext k
  fin_cases k
  · change ((0 : ℤ) : ℝ) = 0
    norm_num
  · change ((1 : ℤ) : ℝ) = 1
    norm_num

@[simp]
private theorem CuspHoneycombHexagon.vertex_two : vertex 2 = ![-1, 1] := by
  funext k
  fin_cases k
  · change ((-1 : ℤ) : ℝ) = -1
    norm_num
  · change ((1 : ℤ) : ℝ) = 1
    norm_num

@[simp]
private theorem CuspHoneycombHexagon.vertex_three : vertex 3 = ![-1, 0] := by
  funext k
  fin_cases k
  · change ((-1 : ℤ) : ℝ) = -1
    norm_num
  · change ((0 : ℤ) : ℝ) = 0
    norm_num

@[simp]
private theorem CuspHoneycombHexagon.vertex_four : vertex 4 = ![0, -1] := by
  funext k
  fin_cases k
  · change ((0 : ℤ) : ℝ) = 0
    norm_num
  · change ((-1 : ℤ) : ℝ) = -1
    norm_num

@[simp]
private theorem CuspHoneycombHexagon.vertex_five : vertex 5 = ![1, -1] := by
  funext k
  fin_cases k
  · change ((1 : ℤ) : ℝ) = 1
    norm_num
  · change ((-1 : ℤ) : ℝ) = -1
    norm_num

private def CuspHoneycombHexagon.rotate : Plane ≃ₗ[ℝ] Plane
    where
  toFun x := ![-x 1, x 0 + x 1]
  invFun x := ![x 0 + x 1, -x 0]
  left_inv
    x := by
    funext k
    fin_cases k <;> simp
  right_inv
    x := by
    funext k
    fin_cases k <;> simp
  map_add' x
    y := by
    funext k
    fin_cases k <;> simp <;> ring
  map_smul' r
    x := by
    funext k
    fin_cases k <;> simp; ring

@[simp]
private theorem
    CuspHoneycombHexagon.rotate_vertex (i : Fin 6) : rotate (vertex i) = vertex (i + 1) := by
  have hr :
    ∀ i : Fin 6,
      ToricComponent.hexagonRay (i + 1) 0 = -ToricComponent.hexagonRay i 1 ∧
        ToricComponent.hexagonRay (i + 1) 1 =
          ToricComponent.hexagonRay i 0 + ToricComponent.hexagonRay i 1 := by decide
  funext k
  fin_cases k
  · change -(ToricComponent.hexagonRay i 1 : ℝ) = (ToricComponent.hexagonRay (i + 1) 0 : ℝ)
    rw [(hr i).1, Int.cast_neg]
  · change
      (ToricComponent.hexagonRay i 0 : ℝ) + (ToricComponent.hexagonRay i 1 : ℝ) =
        (ToricComponent.hexagonRay (i + 1) 1 : ℝ)
    rw [(hr i).2, Int.cast_add]

@[simp]
private theorem CuspHoneycombHexagon.rotate_midpoint (i : Fin 6) :
    rotate (CuspHoneycombHexagon.midpoint i) = CuspHoneycombHexagon.midpoint (i + 1) := by
  simp only [CuspHoneycombHexagon.midpoint, map_smul, map_add, rotate_vertex, sub_add_cancel,
    add_sub_cancel_right]

@[simp]
private theorem CuspHoneycombHexagon.rotate_tile (i : Fin 6) (p : Square) :
    rotate (tile i p) = tile (i + 1) p := by
  simp only [tile, map_add, map_smul, rotate_vertex, rotate_midpoint]

private theorem CuspHoneycombHexagon.sector_formula_0 (α β : ℝ) :
    α • vertex 0 + β • vertex (0 + 1) = ![α, β] := by
  ext k
  fin_cases k
  · change α * ((1 : ℤ) : ℝ) + β * ((0 : ℤ) : ℝ) = α
    norm_num [sub_eq_add_neg]
  · change α * ((0 : ℤ) : ℝ) + β * ((1 : ℤ) : ℝ) = β
    norm_num [sub_eq_add_neg]

private theorem CuspHoneycombHexagon.sector_formula_1 (α β : ℝ) :
    α • vertex 1 + β • vertex (1 + 1) = ![-β, α + β] := by
  ext k
  fin_cases k
  · change α * ((0 : ℤ) : ℝ) + β * ((-1 : ℤ) : ℝ) = -β
    norm_num [sub_eq_add_neg]
  · change α * ((1 : ℤ) : ℝ) + β * ((1 : ℤ) : ℝ) = α + β
    norm_num [sub_eq_add_neg]

private theorem CuspHoneycombHexagon.sector_formula_2 (α β : ℝ) :
    α • vertex 2 + β • vertex (2 + 1) = ![-α - β, α] := by
  ext k
  fin_cases k
  · change α * ((-1 : ℤ) : ℝ) + β * ((-1 : ℤ) : ℝ) = -α - β
    norm_num [sub_eq_add_neg]
  · change α * ((1 : ℤ) : ℝ) + β * ((0 : ℤ) : ℝ) = α
    norm_num [sub_eq_add_neg]

private theorem CuspHoneycombHexagon.sector_formula_3 (α β : ℝ) :
    α • vertex 3 + β • vertex (3 + 1) = ![-α, -β] := by
  ext k
  fin_cases k
  · change α * ((-1 : ℤ) : ℝ) + β * ((0 : ℤ) : ℝ) = -α
    norm_num [sub_eq_add_neg]
  · change α * ((0 : ℤ) : ℝ) + β * ((-1 : ℤ) : ℝ) = -β
    norm_num [sub_eq_add_neg]

private theorem CuspHoneycombHexagon.sector_formula_4 (α β : ℝ) :
    α • vertex 4 + β • vertex (4 + 1) = ![β, -α - β] := by
  ext k
  fin_cases k
  · change α * ((0 : ℤ) : ℝ) + β * ((1 : ℤ) : ℝ) = β
    norm_num [sub_eq_add_neg]
  · change α * ((-1 : ℤ) : ℝ) + β * ((-1 : ℤ) : ℝ) = -α - β
    norm_num [sub_eq_add_neg]

private theorem CuspHoneycombHexagon.sector_formula_5 (α β : ℝ) :
    α • vertex 5 + β • vertex (5 + 1) = ![α + β, -α] := by
  ext k
  fin_cases k
  · change α * ((1 : ℤ) : ℝ) + β * ((1 : ℤ) : ℝ) = α + β
    norm_num [sub_eq_add_neg]
  · change α * ((-1 : ℤ) : ℝ) + β * ((0 : ℤ) : ℝ) = -α
    norm_num [sub_eq_add_neg]

private theorem CuspHoneycombHexagon.sector_decomposition {x : Plane} (hx : x ∈ Hexagon) :
    ∃ i : Fin 6, ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α + β ≤ 1 ∧ x = α • vertex i + β • vertex (i + 1) := by
  obtain ⟨h0, h1, h01⟩ := hx
  obtain ⟨h0l, h0u⟩ := abs_le.mp h0
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  obtain ⟨h01l, h01u⟩ := abs_le.mp h01
  by_cases ha : 0 ≤ x 0
  · by_cases hb : 0 ≤ x 1
    · refine ⟨0, x 0, x 1, ha, hb, h01u, ?_⟩
      rw [sector_formula_0]
      exact funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
    · by_cases hab : 0 ≤ x 0 + x 1
      · refine ⟨5, -x 1, x 0 + x 1, ?_, hab, ?_, ?_⟩
        · linarith
        · linarith
        · rw [sector_formula_5]
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
            ring
      · refine ⟨4, -(x 0 + x 1), x 0, ?_, ha, ?_, ?_⟩
        · linarith
        · linarith
        · rw [sector_formula_4]
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one];
          ring
  · by_cases hb : 0 ≤ x 1
    · by_cases hab : 0 ≤ x 0 + x 1
      · refine ⟨1, x 0 + x 1, -x 0, hab, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · rw [sector_formula_1]
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
            ring
      · refine ⟨2, x 1, -(x 0 + x 1), hb, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · rw [sector_formula_2]
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one];
          ring
    · refine ⟨3, -x 0, -x 1, ?_, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · linarith
      · rw [sector_formula_3]
        refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
          ring

private theorem
    CuspHoneycombHexagon.sector_mem_hexagon (i : Fin 6) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + β ≤ 1) : α • vertex i + β • vertex (i + 1) ∈ Hexagon := by
  fin_cases i
  · change α • vertex 0 + β • vertex (0 + 1) ∈ Hexagon
    rw [sector_formula_0]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 1 + β • vertex (1 + 1) ∈ Hexagon
    rw [sector_formula_1]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 2 + β • vertex (2 + 1) ∈ Hexagon
    rw [sector_formula_2]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 3 + β • vertex (3 + 1) ∈ Hexagon
    rw [sector_formula_3]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 4 + β • vertex (4 + 1) ∈ Hexagon
    rw [sector_formula_4]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 5 + β • vertex (5 + 1) ∈ Hexagon
    rw [sector_formula_5]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

private theorem CuspHoneycombHexagon.tile_zero_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 0 p = ![1 - p.1 0, (p.1 0 - p.1 1) / 2] := by
  rw [tile_of_le 0 p h]
  have hindex : (0 : Fin 6) - 1 = 5 := by decide
  rw [CuspHoneycombHexagon.midpoint, hindex, vertex_five, vertex_zero]
  ext k
  fin_cases k <;> norm_num; ring

private theorem CuspHoneycombHexagon.tile_zero_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 0 p = ![1 - (p.1 0 + p.1 1) / 2, (p.1 0 - p.1 1) / 2] := by
  rw [tile_of_ge 0 p h]
  have hadd : (0 : Fin 6) + 1 = 1 := by decide
  have hindex : (1 : Fin 6) - 1 = 0 := by decide
  rw [hadd, CuspHoneycombHexagon.midpoint, hindex, vertex_zero, vertex_one]
  ext k
  fin_cases k <;> norm_num <;> ring

private theorem CuspHoneycombHexagon.tile_one_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 1 p = ![(p.1 1 - p.1 0) / 2, 1 - (p.1 0 + p.1 1) / 2] := by
  rw [tile_of_le 1 p h]
  have hindex : (1 : Fin 6) - 1 = 0 := by decide
  rw [CuspHoneycombHexagon.midpoint, hindex, vertex_zero, vertex_one]
  ext k
  fin_cases k <;> norm_num <;> ring

private theorem CuspHoneycombHexagon.tile_one_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 1 p = ![(p.1 1 - p.1 0) / 2, 1 - p.1 1] := by
  rw [tile_of_ge 1 p h]
  have hadd : (1 : Fin 6) + 1 = 2 := by decide
  have hindex : (2 : Fin 6) - 1 = 1 := by decide
  rw [hadd, CuspHoneycombHexagon.midpoint, hindex, vertex_one, vertex_two]
  ext k
  fin_cases k <;> norm_num; ring

private theorem CuspHoneycombHexagon.tile_two_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 2 p = ![(p.1 0 + p.1 1) / 2 - 1, 1 - p.1 0] := by
  rw [tile_of_le 2 p h]
  have hindex : (2 : Fin 6) - 1 = 1 := by decide
  rw [CuspHoneycombHexagon.midpoint, hindex, vertex_one, vertex_two]
  ext k
  fin_cases k <;> norm_num; ring

private theorem CuspHoneycombHexagon.tile_two_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 2 p = ![p.1 1 - 1, 1 - (p.1 0 + p.1 1) / 2] := by
  rw [tile_of_ge 2 p h]
  have hadd : (2 : Fin 6) + 1 = 3 := by decide
  have hindex : (3 : Fin 6) - 1 = 2 := by decide
  rw [hadd, CuspHoneycombHexagon.midpoint, hindex, vertex_two, vertex_three]
  ext k
  fin_cases k <;> norm_num; ring

private theorem CuspHoneycombHexagon.tile_three_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 3 p = ![p.1 0 - 1, (p.1 1 - p.1 0) / 2] := by
  rw [tile_of_le 3 p h]
  have hindex : (3 : Fin 6) - 1 = 2 := by decide
  rw [CuspHoneycombHexagon.midpoint, hindex, vertex_two, vertex_three]
  ext k
  fin_cases k <;> norm_num; ring

private theorem CuspHoneycombHexagon.tile_three_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 3 p = ![(p.1 0 + p.1 1) / 2 - 1, (p.1 1 - p.1 0) / 2] := by
  rw [tile_of_ge 3 p h]
  have hadd : (3 : Fin 6) + 1 = 4 := by decide
  have hindex : (4 : Fin 6) - 1 = 3 := by decide
  rw [hadd, CuspHoneycombHexagon.midpoint, hindex, vertex_three, vertex_four]
  ext k
  fin_cases k <;> norm_num <;> ring

private theorem CuspHoneycombHexagon.tile_four_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 4 p = ![(p.1 0 - p.1 1) / 2, (p.1 0 + p.1 1) / 2 - 1] := by
  rw [tile_of_le 4 p h]
  have hindex : (4 : Fin 6) - 1 = 3 := by decide
  rw [CuspHoneycombHexagon.midpoint, hindex, vertex_three, vertex_four]
  ext k
  fin_cases k <;> norm_num <;> ring

private theorem CuspHoneycombHexagon.tile_four_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 4 p = ![(p.1 0 - p.1 1) / 2, p.1 1 - 1] := by
  rw [tile_of_ge 4 p h]
  have hadd : (4 : Fin 6) + 1 = 5 := by decide
  have hindex : (5 : Fin 6) - 1 = 4 := by decide
  rw [hadd, CuspHoneycombHexagon.midpoint, hindex, vertex_four, vertex_five]
  ext k
  fin_cases k <;> norm_num; ring

private theorem CuspHoneycombHexagon.tile_five_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 5 p = ![1 - (p.1 0 + p.1 1) / 2, p.1 0 - 1] := by
  rw [tile_of_le 5 p h]
  have hindex : (5 : Fin 6) - 1 = 4 := by decide
  rw [CuspHoneycombHexagon.midpoint, hindex, vertex_four, vertex_five]
  ext k
  fin_cases k <;> norm_num; ring

private theorem CuspHoneycombHexagon.tile_five_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 5 p = ![1 - p.1 1, (p.1 0 + p.1 1) / 2 - 1] := by
  rw [tile_of_ge 5 p h]
  have hadd : (5 : Fin 6) + 1 = 0 := by decide
  have hindex : (0 : Fin 6) - 1 = 5 := by decide
  rw [hadd, CuspHoneycombHexagon.midpoint, hindex, vertex_five, vertex_zero]
  ext k
  fin_cases k <;> norm_num; ring

private theorem CuspHoneycombHexagon.eq_cornerOne_iff (p : Square) :
    p = cornerOne ↔ p.1 0 = 1 ∧ p.1 1 = 1 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    apply Subtype.ext
    ext k
    fin_cases k <;> assumption

private theorem CuspHoneycombHexagon.tile_zero_eq_one_iff (p q : Square) :
    tile 0 p = tile 1 q ↔ p.1 0 = 1 ∧ q.1 1 = 1 ∧ q.1 0 = p.1 1 := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;> rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [tile_zero_le p hp] at h
      | rw [tile_zero_ge p hp] at h
      first
      | rw [tile_one_le q hq] at h
      | rw [tile_one_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨?_, ?_, ?_⟩ <;> linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨hp, hq, hqp⟩
    have hp' : p.1 1 ≤ p.1 0 := by simpa only [hp] using (p.property 1).2
    have hq' : q.1 0 ≤ q.1 1 := by simpa only [hq] using (q.property 0).2
    rw [tile_zero_ge p hp', tile_one_le q hq']
    ext k
    fin_cases k <;> simp [hp, hq, hqp] <;> ring

private theorem CuspHoneycombHexagon.tile_zero_eq_five_iff (p q : Square) :
    tile 0 p = tile 5 q ↔ p.1 1 = 1 ∧ q.1 0 = 1 ∧ p.1 0 = q.1 1 := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;> rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [tile_zero_le p hp] at h
      | rw [tile_zero_ge p hp] at h
      first
      | rw [tile_five_le q hq] at h
      | rw [tile_five_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨?_, ?_, ?_⟩ <;> linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨hp, hq, hpq⟩
    have hp' : p.1 0 ≤ p.1 1 := by simpa only [hp] using (p.property 0).2
    have hq' : q.1 1 ≤ q.1 0 := by simpa only [hq] using (q.property 1).2
    rw [tile_zero_le p hp', tile_five_ge q hq']
    ext k
    fin_cases k <;> simp [hp, hq, hpq]; ring

private theorem CuspHoneycombHexagon.tile_zero_eq_two_iff (p q : Square) :
    tile 0 p = tile 2 q ↔ p = cornerOne ∧ q = cornerOne := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rw [eq_cornerOne_iff, eq_cornerOne_iff]
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;> rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [tile_zero_le p hp] at h
      | rw [tile_zero_ge p hp] at h
      first
      | rw [tile_two_le q hq] at h
      | rw [tile_two_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨rfl, rfl⟩
    simp

private theorem CuspHoneycombHexagon.tile_zero_eq_three_iff (p q : Square) :
    tile 0 p = tile 3 q ↔ p = cornerOne ∧ q = cornerOne := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rw [eq_cornerOne_iff, eq_cornerOne_iff]
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;> rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [tile_zero_le p hp] at h
      | rw [tile_zero_ge p hp] at h
      first
      | rw [tile_three_le q hq] at h
      | rw [tile_three_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨rfl, rfl⟩
    simp

private theorem CuspHoneycombHexagon.tile_zero_eq_four_iff (p q : Square) :
    tile 0 p = tile 4 q ↔ p = cornerOne ∧ q = cornerOne := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rw [eq_cornerOne_iff, eq_cornerOne_iff]
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;> rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [tile_zero_le p hp] at h
      | rw [tile_zero_ge p hp] at h
      first
      | rw [tile_four_le q hq] at h
      | rw [tile_four_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨rfl, rfl⟩
    simp

private theorem CuspHoneycombHexagon.tile_zero_injective : Function.Injective (tile 0) := by
  intro p q h
  apply Subtype.ext
  rcases le_total (p.1 0) (p.1 1) with hp | hp <;> rcases le_total (q.1 0) (q.1 1) with hq | hq
  all_goals
    first
    | rw [tile_zero_le p hp] at h
    | rw [tile_zero_ge p hp] at h
    first
    | rw [tile_zero_le q hq] at h
    | rw [tile_zero_ge q hq] at h
    have hx := congrFun h 0
    have hy := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
    ext k
    fin_cases k
    · change p.1 0 = q.1 0
      linarith only [hp, hq, hx, hy]
    · change p.1 1 = q.1 1
      linarith only [hp, hq, hx, hy]

private theorem CuspHoneycombHexagon.rotate_iterate_tile (n : ℕ) (i : Fin 6) (p : Square) :
    (rotate : Plane → Plane)^[n] (tile i p) = tile (i + (n : Fin 6)) p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, rotate_tile]
    congr 1
    simp only [Nat.cast_succ, add_assoc]

private theorem CuspHoneycombHexagon.tile_eq_iff_sub (i j : Fin 6) (p q : Square) :
    tile i p = tile j q ↔ tile 0 p = tile (j - i) q := by
  have hp : (rotate : Plane → Plane)^[i.val] (tile 0 p) = tile i p := by
    rw [rotate_iterate_tile]
    simp only [Fin.cast_val_eq_self, zero_add]
  have hq : (rotate : Plane → Plane)^[i.val] (tile (j - i) q) = tile j q := by
    rw [rotate_iterate_tile]
    simp only [Fin.cast_val_eq_self, sub_add_cancel]
  rw [← hp, ← hq]
  exact (rotate.injective.iterate i.val).eq_iff

private theorem CuspHoneycombHexagon.squareRel_sub (i j : Fin 6) (p q : Square) :
    SquareRel 0 (j - i) p q ↔ SquareRel i j p q := by
  have h0 : (0 : Fin 6) = j - i ↔ i = j := by rw [eq_sub_iff_add_eq, zero_add]
  have h1 : j - i = (0 : Fin 6) + 1 ↔ j = i + 1 := by
    rw [zero_add, sub_eq_iff_eq_add, add_comm (1 : Fin 6) i]
  have h2 : (0 : Fin 6) = (j - i) + 1 ↔ i = j + 1 := by
    have he : j - i + 1 = (j + 1) - i := by abel
    rw [he, eq_sub_iff_add_eq, zero_add]
  simp only [SquareRel, h0, h1, h2]

private theorem
    CuspHoneycombHexagon.eq_cornerOne_iff_all (p : Square) : p = cornerOne ↔ ∀ k, p.1 k = 1 :=
  by
  constructor
  · rintro rfl
    exact fun _ => rfl
  · intro hp
    exact square_eq_of_all_one p cornerOne hp (fun _ => rfl)

private theorem CuspHoneycombHexagon.tile_zero_eq_iff (j : Fin 6) (p q : Square) :
    tile 0 p = tile j q ↔ SquareRel 0 j p q := by
  fin_cases j
  · change tile 0 p = tile 0 q ↔ SquareRel 0 0 p q
    rw [squareRel_self]
    exact tile_zero_injective.eq_iff
  · change tile 0 p = tile 1 q ↔ SquareRel 0 (0 + 1) p q
    rw [squareRel_next]
    exact tile_zero_eq_one_iff p q
  · change tile 0 p = tile 2 q ↔ SquareRel 0 (0 + 2) p q
    rw [squareRel_add_two, tile_zero_eq_two_iff, eq_cornerOne_iff_all, eq_cornerOne_iff_all]
  · change tile 0 p = tile 3 q ↔ SquareRel 0 (0 + 3) p q
    rw [squareRel_add_three, tile_zero_eq_three_iff, eq_cornerOne_iff_all, eq_cornerOne_iff_all]
  · change tile 0 p = tile 4 q ↔ SquareRel 0 (0 + 4) p q
    rw [squareRel_add_four, tile_zero_eq_four_iff, eq_cornerOne_iff_all, eq_cornerOne_iff_all]
  · change tile 0 p = tile 5 q ↔ SquareRel 0 (0 + 5) p q
    rw [squareRel_prev, tile_zero_eq_five_iff]
    constructor <;> rintro ⟨h0, h1, h2⟩
    · exact ⟨h0, h1, h2.symm⟩
    · exact ⟨h0, h1, h2.symm⟩

private theorem CuspHoneycombHexagon.tile_eq_iff (i j : Fin 6) (p q : Square) :
    tile i p = tile j q ↔ SquareRel i j p q :=
  (tile_eq_iff_sub i j p q).trans ((tile_zero_eq_iff (j - i) p q).trans (squareRel_sub i j p q))

private theorem
    CuspHoneycombHexagon.tile_sector_of_le (i : Fin 6) (p : Square) (hp : p.1 0 ≤ p.1 1) :
    tile i p =
      ((p.1 1 - p.1 0) / 2) • vertex (i - 1) + (1 - (p.1 0 + p.1 1) / 2) • vertex ((i - 1) + 1) :=
  by
  rw [tile_of_le i p hp, CuspHoneycombHexagon.midpoint, sub_add_cancel]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem
    CuspHoneycombHexagon.tile_sector_of_ge (i : Fin 6) (p : Square) (hp : p.1 1 ≤ p.1 0) :
    tile i p = (1 - (p.1 0 + p.1 1) / 2) • vertex i + ((p.1 0 - p.1 1) / 2) • vertex (i + 1) := by
  rw [tile_of_ge i p hp, CuspHoneycombHexagon.midpoint, add_sub_cancel_right]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem
    CuspHoneycombHexagon.tile_mem_hexagon (i : Fin 6) (p : Square) : tile i p ∈ Hexagon := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_sector_of_le i p hp]
    apply sector_mem_hexagon (i - 1) <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · rw [tile_sector_of_ge i p hp]
    apply sector_mem_hexagon i <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]

private theorem
    CuspHoneycombHexagon.exists_tile_of_sector (i : Fin 6) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + β ≤ 1) : ∃ j : Fin 6, ∃ p : Square, tile j p = α • vertex i + β • vertex (i + 1) :=
  by
  rcases le_total β α with h | h
  · let p : Square :=
      ⟨![1 - α + β, 1 - α - β], by
        intro k
        fin_cases k
        · change 0 ≤ 1 - α + β ∧ 1 - α + β ≤ 1
          constructor <;> linarith
        · change 0 ≤ 1 - α - β ∧ 1 - α - β ≤ 1
          constructor <;> linarith⟩
    have hp : p.1 1 ≤ p.1 0 := by
      change 1 - α - β ≤ 1 - α + β
      linarith
    refine ⟨i, p, ?_⟩
    rw [tile_sector_of_ge i p hp]
    ext k
    simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · let p : Square :=
      ⟨![1 - α - β, 1 + α - β], by
        intro k
        fin_cases k
        · change 0 ≤ 1 - α - β ∧ 1 - α - β ≤ 1
          constructor <;> linarith
        · change 0 ≤ 1 + α - β ∧ 1 + α - β ≤ 1
          constructor <;> linarith⟩
    have hp : p.1 0 ≤ p.1 1 := by
      change 1 - α - β ≤ 1 + α - β
      linarith
    refine ⟨i + 1, p, ?_⟩
    rw [tile_sector_of_le (i + 1) p hp, add_sub_cancel_right]
    ext k
    simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

private theorem CuspHoneycombHexagon.tile_jointly_surjective (x : Hexagon) :
    ∃ i : Fin 6, ∃ p : Square, tile i p = x.val := by
  obtain ⟨i, α, β, hα, hβ, hαβ, hx⟩ := sector_decomposition x.2
  obtain ⟨j, p, hp⟩ := exists_tile_of_sector i α β hα hβ hαβ
  exact ⟨j, p, hp.trans hx.symm⟩

private theorem CuspHoneycombHexagon.tile_zero_side_zero_eq_one_iff (p : Square) :
    sideFunctional 0 (tile 0 p) = 1 ↔ p.1 0 = 0 := by
  rw [sideFunctional_zero]
  have hp0 := (p.property 0).1
  have hp1 := (p.property 1).1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_zero]
    constructor <;> intro h <;> linarith only [hp, hp0, hp1, h]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_zero]
    constructor <;> intro h <;> linarith only [hp, hp0, hp1, h]

private theorem CuspHoneycombHexagon.tile_zero_side_one_eq_one_iff (p : Square) :
    sideFunctional 1 (tile 0 p) = 1 ↔ p.1 1 = 0 := by
  rw [sideFunctional_one]
  have hp0 := (p.property 0).1
  have hp1 := (p.property 1).1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> intro h <;> linarith only [hp, hp0, hp1, h]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> intro h <;> linarith only [hp, hp0, hp1, h]

private theorem CuspHoneycombHexagon.tile_zero_side_two_lt_one (p : Square) :
    sideFunctional 2 (tile 0 p) < 1 := by
  rw [sideFunctional_two]
  have hp0 := (p.property 0).2
  have hp1 := (p.property 1).1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith only [hp0, hp1]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith only [hp0, hp1]

private theorem CuspHoneycombHexagon.tile_zero_side_three_lt_one (p : Square) :
    sideFunctional 3 (tile 0 p) < 1 := by
  rw [sideFunctional_three]
  have hp0 := (p.property 0).2
  have hp1 := (p.property 1).2
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_zero]
    linarith only [hp0, hp1]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_zero]
    linarith only [hp0, hp1]

private theorem CuspHoneycombHexagon.tile_zero_side_four_lt_one (p : Square) :
    sideFunctional 4 (tile 0 p) < 1 := by
  rw [sideFunctional_four]
  have hp0 := (p.property 0).2
  have hp1 := (p.property 1).2
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith only [hp0, hp1]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith only [hp0, hp1]

private theorem CuspHoneycombHexagon.tile_zero_side_five_lt_one (p : Square) :
    sideFunctional 5 (tile 0 p) < 1 := by
  rw [sideFunctional_five]
  have hp0 := (p.property 0).1
  have hp1 := (p.property 1).2
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith only [hp0, hp1]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith only [hp0, hp1]

private theorem CuspHoneycombHexagon.tile_zero_side_eq_one_iff (p : Square) (k : Fin 6) :
    sideFunctional k (tile 0 p) = 1 ↔ (k = 0 ∧ p.1 0 = 0) ∨ (k = 1 ∧ p.1 1 = 0) := by
  fin_cases k
  · simpa only [Fin.zero_eta, true_and, or_false,
      show (0 : Fin 6) = 0 ↔ True from iff_true_intro rfl,
      show (0 : Fin 6) = 1 ↔ False from iff_false_intro (by decide), false_and] using
      tile_zero_side_zero_eq_one_iff p
  · simpa only [Fin.mk_one, false_and, false_or, true_and,
      show (1 : Fin 6) = 0 ↔ False from iff_false_intro (by decide),
      show (1 : Fin 6) = 1 ↔ True from iff_true_intro rfl] using tile_zero_side_one_eq_one_iff p
  · constructor
    · intro h
      exact ((tile_zero_side_two_lt_one p).ne h).elim
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ((show (2 : Fin 6) ≠ 0 by decide) h).elim
      · exact ((show (2 : Fin 6) ≠ 1 by decide) h).elim
  · constructor
    · intro h
      exact ((tile_zero_side_three_lt_one p).ne h).elim
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ((show (3 : Fin 6) ≠ 0 by decide) h).elim
      · exact ((show (3 : Fin 6) ≠ 1 by decide) h).elim
  · constructor
    · intro h
      exact ((tile_zero_side_four_lt_one p).ne h).elim
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ((show (4 : Fin 6) ≠ 0 by decide) h).elim
      · exact ((show (4 : Fin 6) ≠ 1 by decide) h).elim
  · constructor
    · intro h
      exact ((tile_zero_side_five_lt_one p).ne h).elim
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ((show (5 : Fin 6) ≠ 0 by decide) h).elim
      · exact ((show (5 : Fin 6) ≠ 1 by decide) h).elim

private theorem CuspHoneycombHexagon.sideFunctional_rotate (k : Fin 6) (x : Plane) :
    sideFunctional (k + 1) (rotate x) = sideFunctional k x := by
  fin_cases k
  · change -x 1 + (x 0 + x 1) = x 0
    ring
  · change x 0 + x 1 = x 0 + x 1
    rfl
  · change -(-x 1) = x 1
    ring
  · change -(-x 1) - (x 0 + x 1) = -x 0
    ring
  · change -(x 0 + x 1) = -x 0 - x 1
    ring
  · change -x 1 = -x 1
    rfl

private theorem CuspHoneycombHexagon.sideFunctional_iterate (n : ℕ) (k : Fin 6) (x : Plane) :
    sideFunctional (k + (n : Fin 6)) ((rotate : Plane → Plane)^[n] x) = sideFunctional k x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Function.iterate_succ_apply', sideFunctional_rotate, ih]

private theorem CuspHoneycombHexagon.sideFunctional_tile_sub (i k : Fin 6) (p : Square) :
    sideFunctional k (tile i p) = sideFunctional (k - i) (tile 0 p) := by
  have h := sideFunctional_iterate i.val (k - i) (tile 0 p)
  simpa only [rotate_iterate_tile, Fin.cast_val_eq_self, sub_add_cancel, zero_add] using h

private theorem CuspHoneycombHexagon.tile_mem_side_iff (i k : Fin 6) (p : Square) :
    tile i p ∈ side k ↔ (k = i ∧ p.1 0 = 0) ∨ (k = i + 1 ∧ p.1 1 = 0) := by
  have h1 : k - i = (1 : Fin 6) ↔ k = i + 1 := by rw [sub_eq_iff_eq_add, add_comm (1 : Fin 6) i]
  change (tile i p ∈ Hexagon ∧ sideFunctional k (tile i p) = 1) ↔ _
  rw [sideFunctional_tile_sub]
  simp only [tile_mem_hexagon i p, true_and, tile_zero_side_eq_one_iff, sub_eq_zero, h1]

private def CuspHoneycombTiling.dualStandardLinearEquiv : Plane ≃ₗ[ℝ] Plane
    where
  toFun x := ![2 * x 0 + x 1, x 1 - x 0]
  invFun y := ![(y 0 - y 1) / 3, (y 0 + 2 * y 1) / 3]
  left_inv
    x := by
    funext i
    fin_cases i
    · change ((2 * x 0 + x 1) - (x 1 - x 0)) / 3 = x 0
      ring
    · change ((2 * x 0 + x 1) + 2 * (x 1 - x 0)) / 3 = x 1
      ring
  right_inv
    y := by
    funext i
    fin_cases i
    · change 2 * ((y 0 - y 1) / 3) + (y 0 + 2 * y 1) / 3 = y 0
      ring
    · change (y 0 + 2 * y 1) / 3 - (y 0 - y 1) / 3 = y 1
      ring
  map_add' x
    y := by
    funext i
    fin_cases i
    · change 2 * (x 0 + y 0) + (x 1 + y 1) = (2 * x 0 + x 1) + (2 * y 0 + y 1)
      ring
    · change (x 1 + y 1) - (x 0 + y 0) = (x 1 - x 0) + (y 1 - y 0)
      ring
  map_smul' a
    x := by
    funext i
    fin_cases i
    · change 2 * (a * x 0) + a * x 1 = a * (2 * x 0 + x 1)
      ring
    · change a * x 1 - a * x 0 = a * (x 1 - x 0)
      ring

private def CuspHoneycombTiling.dualStandardPlaneHomeomorph : Plane ≃ₜ Plane
    where
  toEquiv := dualStandardLinearEquiv.toEquiv
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_const.mul (continuous_apply 0)).add (continuous_apply 1)
    · exact (continuous_apply 1).sub (continuous_apply 0)
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact ((continuous_apply 0).sub (continuous_apply 1)).div_const 3
    · exact ((continuous_apply 0).add (continuous_const.mul (continuous_apply 1))).div_const 3

@[simp]
private theorem CuspHoneycombTiling.dualStandardPlaneHomeomorph_apply (x : Plane) :
    dualStandardPlaneHomeomorph x = ![2 * x 0 + x 1, x 1 - x 0] :=
  rfl

private theorem CuspHoneycombTiling.dualStandardPlaneHomeomorph_mem_hexagon (x : Plane) :
    dualStandardPlaneHomeomorph x ∈ CuspHoneycombHexagon.Hexagon ↔ x ∈ baseCell := by
  change (|2 * x 0 + x 1| ≤ 1 ∧ |x 1 - x 0| ≤ 1 ∧ |2 * x 0 + x 1 + (x 1 - x 0)| ≤ 1) ↔ _
  have he : 2 * x 0 + x 1 + (x 1 - x 0) = x 0 + 2 * x 1 := by ring
  rw [he, abs_sub_comm (x 1) (x 0)]
  rfl

private theorem CuspHoneycombTiling.dualStandardPlaneHomeomorph_symm_mem_baseCell (y : Plane) :
    dualStandardPlaneHomeomorph.symm y ∈ baseCell ↔ y ∈ CuspHoneycombHexagon.Hexagon := by
  simpa only [Homeomorph.apply_symm_apply] using
    (dualStandardPlaneHomeomorph_mem_hexagon (dualStandardPlaneHomeomorph.symm y)).symm

private def
    CuspHoneycombTiling.standardHexagonDualHomeomorph : CuspHoneycombHexagon.Hexagon ≃ₜ baseCell
    where
  toFun
    y :=
    ⟨dualStandardPlaneHomeomorph.symm y,
      (dualStandardPlaneHomeomorph_symm_mem_baseCell y).mpr y.2⟩
  invFun x := ⟨dualStandardPlaneHomeomorph x, (dualStandardPlaneHomeomorph_mem_hexagon x).mpr x.2⟩
  left_inv y := Subtype.ext (dualStandardPlaneHomeomorph.apply_symm_apply y)
  right_inv x := Subtype.ext (dualStandardPlaneHomeomorph.symm_apply_apply x)
  continuous_toFun :=
    (dualStandardPlaneHomeomorph.symm.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (dualStandardPlaneHomeomorph.continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
private theorem
    CuspHoneycombTiling.standardHexagonDualHomeomorph_coe (y : CuspHoneycombHexagon.Hexagon) :
    (standardHexagonDualHomeomorph y : Plane) = dualStandardPlaneHomeomorph.symm y :=
  rfl

private def CuspHoneycombTiling.triangleBarycenter (s : ToricFan.Triangle) : Plane := fun i =>
  ((s.vertex 0 i : ℝ) + (s.vertex 1 i : ℝ) + (s.vertex 2 i : ℝ)) / 3

private theorem CuspHoneycombTiling.triangleBarycenter_zeroTriangle (i : Fin 6) :
    triangleBarycenter (ToricComponent.zeroTriangle i) = fun j =>
      ((ToricComponent.hexagonRay i j : ℝ) + (ToricComponent.hexagonRay (i + 1) j : ℝ)) / 3 := by
  have hs :
    (ToricComponent.zeroTriangle i).vertex 0 + (ToricComponent.zeroTriangle i).vertex 1 +
        (ToricComponent.zeroTriangle i).vertex 2 =
      ToricComponent.hexagonRay i + ToricComponent.hexagonRay (i + 1) := by fin_cases i <;> decide
  funext j
  have hj :
    (ToricComponent.zeroTriangle i).vertex 0 j + (ToricComponent.zeroTriangle i).vertex 1 j +
        (ToricComponent.zeroTriangle i).vertex 2 j =
      ToricComponent.hexagonRay i j + ToricComponent.hexagonRay (i + 1) j :=
    congrFun hs j
  have hreal :
    ((ToricComponent.zeroTriangle i).vertex 0 j : ℝ) +
          ((ToricComponent.zeroTriangle i).vertex 1 j : ℝ) +
        ((ToricComponent.zeroTriangle i).vertex 2 j : ℝ) =
      (ToricComponent.hexagonRay i j : ℝ) + (ToricComponent.hexagonRay (i + 1) j : ℝ) := by
    exact_mod_cast hj
  exact congrArg (fun r : ℝ => r / 3) hreal

private theorem CuspHoneycombTiling.dual_standard_vertex (i : Fin 6) :
    dualStandardPlaneHomeomorph.symm (CuspHoneycombHexagon.vertex i) =
      triangleBarycenter (ToricComponent.zeroTriangle i) := by
  have hr :
    ∀ i : Fin 6,
      ToricComponent.hexagonRay (i + 1) 0 = -ToricComponent.hexagonRay i 1 ∧
        ToricComponent.hexagonRay (i + 1) 1 =
          ToricComponent.hexagonRay i 0 + ToricComponent.hexagonRay i 1 := by decide
  rw [triangleBarycenter_zeroTriangle]
  funext j
  fin_cases j
  · change
      ((ToricComponent.hexagonRay i 0 : ℝ) - (ToricComponent.hexagonRay i 1 : ℝ)) / 3 =
        ((ToricComponent.hexagonRay i 0 : ℝ) + (ToricComponent.hexagonRay (i + 1) 0 : ℝ)) / 3
    rw [(hr i).1, Int.cast_neg]
    ring
  · change
      ((ToricComponent.hexagonRay i 0 : ℝ) + 2 * (ToricComponent.hexagonRay i 1 : ℝ)) / 3 =
        ((ToricComponent.hexagonRay i 1 : ℝ) + (ToricComponent.hexagonRay (i + 1) 1 : ℝ)) / 3
    rw [(hr i).2, Int.cast_add]
    ring

private theorem CuspHoneycombTiling.mem_neighbor_cell_iff_sideFunctional (k : Fin 6) (x : Plane)
    (hx : x ∈ baseCell) :
    x ∈ cell (ToricComponent.hexagonRay k) ↔
      CuspHoneycombHexagon.sideFunctional k (dualStandardPlaneHomeomorph x) = 1 := by
  have h0 := abs_le.mp hx.1
  have h1 := abs_le.mp hx.2.1
  have h2 := abs_le.mp hx.2.2
  fin_cases k <;>
    norm_num [cell, baseCell, latticePoint, ToricComponent.hexagonRay,
      CuspHoneycombHexagon.sideFunctional, dualStandardPlaneHomeomorph_apply, abs_le]
  all_goals
    constructor
    · intro h
      linarith
    · intro h
      repeat' apply And.intro
      all_goals linarith

private theorem CuspHoneycombTiling.dual_image_side (k : Fin 6) :
    dualStandardPlaneHomeomorph.symm '' CuspHoneycombHexagon.side k =
      baseCell ∩ cell (ToricComponent.hexagonRay k) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hx : dualStandardPlaneHomeomorph.symm y ∈ baseCell :=
      (dualStandardPlaneHomeomorph_symm_mem_baseCell y).mpr hy.1
    refine ⟨hx, (mem_neighbor_cell_iff_sideFunctional k _ hx).mpr ?_⟩
    simpa only [Homeomorph.apply_symm_apply] using hy.2
  · intro hx
    refine ⟨dualStandardPlaneHomeomorph x, ?_, dualStandardPlaneHomeomorph.symm_apply_apply x⟩
    exact
      ⟨(dualStandardPlaneHomeomorph_mem_hexagon x).mpr hx.1,
        (mem_neighbor_cell_iff_sideFunctional k x hx.1).mp hx.2⟩

private theorem CuspHoneycombTiling.standardHexagonDualHomeomorph_mem_cell_iff_side (k : Fin 6)
    (x : CuspHoneycombHexagon.Hexagon) :
    (standardHexagonDualHomeomorph x : Plane) ∈ cell (ToricComponent.hexagonRay k) ↔
      (x : Plane) ∈ CuspHoneycombHexagon.side k := by
  have h :=
    mem_neighbor_cell_iff_sideFunctional k (standardHexagonDualHomeomorph x)
      (standardHexagonDualHomeomorph x).property
  simpa only [standardHexagonDualHomeomorph_coe, Homeomorph.apply_symm_apply,
    CuspHoneycombHexagon.side, Set.mem_ofPred_eq, x.property, true_and] using h

private def CuspHoneycombHexagon.segmentIntervalHomeomorph {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] [T2Space E] (a b : E)
    (hab : a ≠ b) : unitInterval ≃ₜ segment ℝ a b :=
  ((Path.segment a b).continuous.isClosedEmbedding
        (Path.segment_injective_of_ne hab)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (Path.range_segment a b))

@[simp]
private theorem CuspHoneycombHexagon.segmentIntervalHomeomorph_apply {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] [T2Space E] (a b : E)
    (hab : a ≠ b) (t : unitInterval) :
    (segmentIntervalHomeomorph a b hab t : E) = (1 - (t : ℝ)) • a + (t : ℝ) • b := by
  change AffineMap.lineMap a b (t : ℝ) = _
  exact AffineMap.lineMap_apply_module _ _ _

private theorem CuspHoneycombHexagon.vertex_injective : Function.Injective vertex := by
  intro i j hij
  apply ToricComponent.hexagonRay_injective
  funext k
  have h := congrFun hij k
  change (ToricComponent.hexagonRay i k : ℝ) = (ToricComponent.hexagonRay j k : ℝ) at h
  exact_mod_cast h

private theorem CuspHoneycombHexagon.vertex_prev_ne (k : Fin 6) : vertex (k - 1) ≠ vertex k := by
  intro h
  exact (show ∀ k : Fin 6, k - 1 ≠ k by decide) k (vertex_injective h)

private theorem CuspHoneycombHexagon.side_eq_segment (k : Fin 6) :
    side k = segment ℝ (vertex (k - 1)) (vertex k) := by
  have hpred :
    ∀ k : Fin 6,
      k - 1 =
        ![⟨5, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
            ⟨4, by decide⟩]
          k := by decide
  rw [hpred k, segment_eq_image]
  ext x
  constructor
  · rintro ⟨⟨h0, h1, h01⟩, hk⟩
    obtain ⟨h0l, h0u⟩ := abs_le.mp h0
    obtain ⟨h1l, h1u⟩ := abs_le.mp h1
    obtain ⟨h01l, h01u⟩ := abs_le.mp h01
    refine ⟨![x 1 + 1, x 1, -x 0, 1 - x 1, -x 1, x 0] k, ?_, ?_⟩
    · fin_cases k <;> norm_num [sideFunctional] at hk ⊢ <;> constructor <;> linarith
    · funext j
      fin_cases k <;> fin_cases j <;>
          norm_num [sideFunctional, vertex, ToricComponent.hexagonRay, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul] at hk ⊢ <;>
        linarith
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    fin_cases k <;>
          norm_num [side, Hexagon, sideFunctional, vertex, ToricComponent.hexagonRay,
            Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, smul_eq_mul, abs_le] <;>
        (repeat' constructor) <;>
      linarith

private def CuspHoneycombHexagon.sideIntervalHomeomorph (k : Fin 6) : unitInterval ≃ₜ side k :=
  (segmentIntervalHomeomorph (vertex (k - 1)) (vertex k) (vertex_prev_ne k)).trans
    (Homeomorph.setCongr (side_eq_segment k).symm)

@[simp]
private theorem CuspHoneycombHexagon.sideIntervalHomeomorph_apply (k : Fin 6) (t : unitInterval) :
    (sideIntervalHomeomorph k t : Plane) = (1 - (t : ℝ)) • vertex (k - 1) + (t : ℝ) • vertex k := by
  change (segmentIntervalHomeomorph (vertex (k - 1)) (vertex k) (vertex_prev_ne k) t : Plane) = _
  exact segmentIntervalHomeomorph_apply _ _ _ _

private theorem CuspHoneycombHexagon.sideIntervalHomeomorph_one (k : Fin 6) :
    (sideIntervalHomeomorph k 1 : Plane) = vertex k := by simp

private theorem CuspHoneycombHexagon.eq_vertex_of_consecutive_sideFunctional (k : Fin 6) (x : Plane)
    (h0 : sideFunctional k x = 1) (h1 : sideFunctional (k + 1) x = 1) : x = vertex k := by
  fin_cases k <;> ext l <;> fin_cases l <;>
      norm_num [sideFunctional, vertex, ToricComponent.hexagonRay, Fin.add_def, Matrix.cons_val,
        Matrix.vecHead, Matrix.vecTail] at h0 h1 ⊢ <;>
    linarith

private theorem CuspHoneycombHexagon.vertex_mem_side_self (k : Fin 6) : vertex k ∈ side k := by
  fin_cases k <;>
    norm_num [side, Hexagon, sideFunctional, vertex, ToricComponent.hexagonRay, Fin.add_def,
      Matrix.cons_val, Matrix.vecHead, Matrix.vecTail]

private theorem
    CuspHoneycombHexagon.vertex_mem_side_next (k : Fin 6) : vertex k ∈ side (k + 1) := by
  fin_cases k <;>
    norm_num [side, Hexagon, sideFunctional, vertex, ToricComponent.hexagonRay, Fin.add_def,
      Matrix.cons_val, Matrix.vecHead, Matrix.vecTail]

private theorem
    CuspHoneycombHexagon.side_inter_next (k : Fin 6) : side k ∩ side (k + 1) = {vertex k} := by
  ext x
  constructor
  · intro hx
    exact eq_vertex_of_consecutive_sideFunctional k x hx.1.2 hx.2.2
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨vertex_mem_side_self k, vertex_mem_side_next k⟩

private theorem CuspHoneycombHexagon.side_disjoint_add_two (k : Fin 6) :
    Disjoint (side k) (side (k + 2)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨h0l, h0u⟩ := abs_le.mp hx.1.1
  obtain ⟨h1l, h1u⟩ := abs_le.mp hx.1.2.1
  obtain ⟨h01l, h01u⟩ := abs_le.mp hx.1.2.2
  have h0 := hx.2
  have h2 := hy.2
  fin_cases k <;>
      norm_num [sideFunctional, Fin.add_def, Matrix.cons_val, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h0 h2 <;>
    linarith only [h0, h2, h0l, h0u, h1l, h1u, h01l, h01u]

private theorem CuspHoneycombHexagon.side_disjoint_add_three (k : Fin 6) :
    Disjoint (side k) (side (k + 3)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h0 := hx.2
  have h3 := hy.2
  fin_cases k <;>
      norm_num [sideFunctional, Fin.add_def, Matrix.cons_val, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h0 h3 <;>
    linarith only [h0, h3]

private theorem CuspHoneycombHexagon.side_disjoint_add_four (k : Fin 6) :
    Disjoint (side k) (side (k + 4)) := by
  have hi : (k + 4) + 2 = k := by
    rw [add_assoc]
    change k + 0 = k
    exact add_zero k
  simpa only [hi] using (side_disjoint_add_two (k + 4)).symm

private theorem CuspHoneycombHexagon.side_disjoint_nonadjacent {i j : Fin 6} (hij : i ≠ j)
    (hnext : j ≠ i + 1) (hprev : i ≠ j + 1) : Disjoint (side i) (side j) := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin 6, j = i + k := ⟨j - i, by rw [add_comm i (j - i), sub_add_cancel]⟩
  fin_cases k
  · exact (hij (by change i = i + 0; simp)).elim
  · exact (hnext rfl).elim
  · change Disjoint (side i) (side (i + 2))
    exact side_disjoint_add_two i
  · change Disjoint (side i) (side (i + 3))
    exact side_disjoint_add_three i
  · change Disjoint (side i) (side (i + 4))
    exact side_disjoint_add_four i
  · apply False.elim
    apply hprev
    change i = (i + 5) + 1
    rw [add_assoc]
    change i = i + 0
    exact (add_zero i).symm

private theorem CuspHoneycombTiling.standard_vertex_opposite (k : Fin 6) :
    CuspHoneycombHexagon.vertex (k + 3) = -CuspHoneycombHexagon.vertex k := by
  funext i
  change (ToricComponent.hexagonRay (k + 3) i : ℝ) = -(ToricComponent.hexagonRay k i : ℝ)
  rw [ToricComponent.hexagonRay_opposite]
  simp only [Pi.neg_apply, Int.cast_neg]

private theorem CuspHoneycombTiling.dual_latticePoint_ray (k : Fin 6) :
    dualStandardLinearEquiv (latticePoint (ToricComponent.hexagonRay k)) =
      CuspHoneycombHexagon.vertex (k - 1) + CuspHoneycombHexagon.vertex k := by
  have h :
    ∀ k : Fin 6,
      ToricComponent.hexagonRay (k - 1) 0 + ToricComponent.hexagonRay k 0 =
          2 * ToricComponent.hexagonRay k 0 + ToricComponent.hexagonRay k 1 ∧
        ToricComponent.hexagonRay (k - 1) 1 + ToricComponent.hexagonRay k 1 =
          ToricComponent.hexagonRay k 1 - ToricComponent.hexagonRay k 0 := by decide
  funext i
  fin_cases i
  · change
      2 * (ToricComponent.hexagonRay k 0 : ℝ) + (ToricComponent.hexagonRay k 1 : ℝ) =
        (ToricComponent.hexagonRay (k - 1) 0 : ℝ) + (ToricComponent.hexagonRay k 0 : ℝ)
    exact_mod_cast (h k).1.symm
  · change
      (ToricComponent.hexagonRay k 1 : ℝ) - (ToricComponent.hexagonRay k 0 : ℝ) =
        (ToricComponent.hexagonRay (k - 1) 1 : ℝ) + (ToricComponent.hexagonRay k 1 : ℝ)
    exact_mod_cast (h k).2.symm

private theorem CuspHoneycombTiling.dual_sideInterval_opposite (k : Fin 6) (t : unitInterval) :
    dualStandardPlaneHomeomorph.symm
        (CuspHoneycombHexagon.sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane) =
      dualStandardPlaneHomeomorph.symm (CuspHoneycombHexagon.sideIntervalHomeomorph k t : Plane) -
        latticePoint (ToricComponent.hexagonRay k) := by
  change
    dualStandardLinearEquiv.symm
        (CuspHoneycombHexagon.sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane) =
      dualStandardLinearEquiv.symm (CuspHoneycombHexagon.sideIntervalHomeomorph k t : Plane) -
        latticePoint (ToricComponent.hexagonRay k)
  apply dualStandardLinearEquiv.injective
  simp only [map_sub, LinearEquiv.apply_symm_apply, dual_latticePoint_ray]
  have hidx : ∀ k : Fin 6, k + 3 - 1 = (k - 1) + 3 := by decide
  simp only [CuspHoneycombHexagon.sideIntervalHomeomorph_apply, unitInterval.coe_symm_eq, hidx,
    standard_vertex_opposite]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  ring

private theorem
    CuspHoneycombTiling.sub_latticePoint_mem_cell_iff (v w : CuspHoneycombTiling.Lattice)
    (x : Plane) : x - latticePoint v ∈ cell w ↔ x ∈ cell (v + w) := by
  simp only [mem_cell, latticePoint_add, sub_sub]

private def CuspHoneycombTiling.cellTranslationHomeomorph (v : CuspHoneycombTiling.Lattice) :
    baseCell ≃ₜ cell v
    where
  toFun
    x := ⟨(x : Plane) + latticePoint v, by simpa only [mem_cell, add_sub_cancel_right] using x.2⟩
  invFun y := ⟨(y : Plane) - latticePoint v, y.2⟩
  left_inv x := Subtype.ext (add_sub_cancel_right (x : Plane) (latticePoint v))
  right_inv y := Subtype.ext (sub_add_cancel (y : Plane) (latticePoint v))
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

private def CuspHoneycombTiling.cellShiftHomeomorph (v w : CuspHoneycombTiling.Lattice) :
    cell v ≃ₜ cell (v + w)
    where
  toFun x := ⟨(x : Plane) + latticePoint w, (add_latticePoint_mem_cell_iff v w x).mpr x.2⟩
  invFun
    y :=
    ⟨(y : Plane) - latticePoint w,
      (sub_latticePoint_mem_cell_iff w v y).mpr (by simpa only [add_comm w v] using y.2)⟩
  left_inv x := Subtype.ext (add_sub_cancel_right (x : Plane) (latticePoint w))
  right_inv y := Subtype.ext (sub_add_cancel (y : Plane) (latticePoint w))
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

@[simp]
private theorem CuspHoneycombTiling.cellShiftHomeomorph_coe (v w : CuspHoneycombTiling.Lattice)
    (x : cell v) : (cellShiftHomeomorph v w x : Plane) = (x : Plane) + latticePoint w :=
  rfl

private theorem CuspHoneycombTiling.triangleBarycenter_shift (s : ToricFan.Triangle)
    (v : CuspHoneycombTiling.Lattice) :
    triangleBarycenter (s.shift v) = triangleBarycenter s + latticePoint v := by
  funext i
  simp only [triangleBarycenter, ToricFan.Triangle.vertex_shift, Pi.add_apply, Int.cast_add,
    latticePoint_apply]
  ring

private abbrev ToricSpace.CompactFibreTorus :=
  Fin 2 → Circle

private def ToricSpace.compactFibreUnits : CompactFibreTorus →* (Fin 2 → ℂˣ)
    where
  toFun u i := Circle.toUnits (u i)
  map_one' := by
    funext i
    exact Circle.toUnits.map_one
  map_mul' u
    v := by
    funext i
    exact Circle.toUnits.map_mul (u i) (v i)

private def ToricSpace.compactFibrePhase (u : CompactFibreTorus) : CompactTorus :=
  ![u 0, u 1, 1]

private theorem ToricSpace.compactFibrePhase_continuous : Continuous compactFibrePhase := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_const

private theorem ToricSpace.compactTorusUnits_compactFibrePhase (u : CompactFibreTorus) :
    compactTorusUnits (compactFibrePhase u) = fibreMultiplier (compactFibreUnits u) := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact Circle.toUnits.map_one

private def ToricSpace.compactFibreAction (u : CompactFibreTorus) (x : Space) : Space :=
  torusAction (fibreMultiplier (compactFibreUnits u)) x

private theorem ToricSpace.compactFibreAction_eq_compact (u : CompactFibreTorus) (x : Space) :
    compactFibreAction u x = compactTorusAction (compactFibrePhase u) x := by
  rw [compactTorusAction, compactTorusUnits_compactFibrePhase]
  rfl

@[simp]
private theorem ToricSpace.compactFibreAction_one (x : Space) : compactFibreAction 1 x = x := by
  simp only [compactFibreAction, map_one, fibreMultiplier_one, torusAction_one]

private theorem ToricSpace.compactFibreAction_mul (u v : CompactFibreTorus) (x : Space) :
    compactFibreAction u (compactFibreAction v x) = compactFibreAction (u * v) x := by
  simp only [compactFibreAction, map_mul, fibreMultiplier_mul, torusAction_mul]

private instance ToricSpace.compactFibreMulAction : MulAction CompactFibreTorus Space
    where
  smul := compactFibreAction
  one_smul := compactFibreAction_one
  mul_smul u v x := (compactFibreAction_mul u v x).symm

private theorem ToricSpace.compactFibreAction_continuous :
    Continuous (fun p : CompactFibreTorus × Space => compactFibreAction p.1 p.2) := by
  have h :=
    compactTorusAction_continuous.comp
      ((compactFibrePhase_continuous.comp continuous_fst).prodMk continuous_snd)
  exact h.congr (fun _ => (compactFibreAction_eq_compact _ _).symm)

private instance ToricSpace.compactFibreContinuousSMul : ContinuousSMul CompactFibreTorus Space :=
  ⟨compactFibreAction_continuous⟩

@[simp]
private theorem ToricSpace.time_compactFibreAction (u : CompactFibreTorus) (x : Space) :
    time (compactFibreAction u x) = time x :=
  time_fibreMultiplier _ x

@[simp]
private theorem ToricSpace.modulus_compactFibreAction (u : CompactFibreTorus) (x : Space) :
    modulus (compactFibreAction u x) = modulus x := by
  rw [compactFibreAction_eq_compact, modulus_compactTorusAction]

private def
    ToricSpace.compactFibreActionShear : CompactFibreTorus × Space ≃ₜ CompactFibreTorus × Space
    where
  toFun p := (p.1, p.1 • p.2)
  invFun p := (p.1, p.1⁻¹ • p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk ContinuousSMul.continuous_smul
  continuous_invFun := continuous_fst.prodMk (continuous_fst.inv.smul continuous_snd)

private theorem ToricSpace.compactFibreAction_isProperMap :
    IsProperMap (fun p : CompactFibreTorus × Space => compactFibreAction p.1 p.2) :=
  isProperMap_snd_of_compactSpace.comp compactFibreActionShear.isProperMap

private theorem
    ToricSpace.torusAction_inclusion_eq_self_iff (u : ActingTorus) (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    torusAction u (ToricSpace.inclusion s z) = ToricSpace.inclusion s z ↔
      ∀ i, z i ≠ 0 → factors s u i = 1 := by
  rw [torusAction_inclusion, (inclusion_openEmbedding s).injective.eq_iff]
  constructor
  · intro h i hi
    apply mul_right_cancel₀ hi
    simpa only [scale, Pi.mul_apply, one_mul] using congrFun h i
  · intro h
    funext i
    change factors s u i * z i = z i
    by_cases hi : z i = 0
    · simp only [hi, MulZeroClass.mul_zero]
    · rw [h i hi, one_mul]

private theorem ToricSpace.compactTorusAction_inclusion_eq_self_iff (u : CompactTorus)
    (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    compactTorusAction u (ToricSpace.inclusion s z) = ToricSpace.inclusion s z ↔
      ∀ i, z i ≠ 0 → factors s (compactTorusUnits u) i = 1 :=
  torusAction_inclusion_eq_self_iff (compactTorusUnits u) s z

private def ToricSpace.rayCompactPhase (v : Fin 2 → ℤ) (a : Circle) : CompactTorus :=
  ![a ^ v 0, a ^ v 1, a]

@[simp]
private theorem
    ToricSpace.rayCompactPhase_two (v : Fin 2 → ℤ) (a : Circle) : rayCompactPhase v a 2 = a :=
  rfl

private theorem
    ToricSpace.rayCompactPhase_vertex_coe (s : ToricFan.Triangle) (j : Fin 3) (a : Circle) :
    (fun i => (rayCompactPhase (s.vertex j) a i : ℂ)) = fun i => (a : ℂ) ^ s.rays i j := by
  funext i
  fin_cases i <;> simp [rayCompactPhase, ToricFan.Triangle.vertex]

private theorem
    ToricSpace.monomial_single_coordinate_phase (A : Matrix (Fin 3) (Fin 3) ℤ) (j : Fin 3)
    (a : ℂ) : ToricCharts.monomial A (fun k => if k = j then a else 1) = fun i => a ^ A i j := by
  funext i
  change (∏ k, (if k = j then a else 1) ^ A i k) = _
  calc
    (∏ k, (if k = j then a else 1) ^ A i k) = ∏ k, if k = j then a ^ A i k else 1 := by
      apply Finset.prod_congr rfl
      intro k _
      split_ifs <;> simp
    _ = a ^ A i j := by simp

private theorem ToricSpace.factors_rayCompactPhase_vertex (s : ToricFan.Triangle) (j : Fin 3)
    (a : Circle) :
    factors s (compactTorusUnits (rayCompactPhase (s.vertex j) a)) = fun i =>
      if i = j then (a : ℂ) else 1 := by
  let w : ToricCharts.CoordinateSpace 3 := fun i => if i = j then (a : ℂ) else 1
  have hw : w ∈ ToricCharts.torus := by
    intro i
    dsimp [w]
    split_ifs
    · exact a.coe_ne_zero
    · exact one_ne_zero
  have hv : (fun i => (rayCompactPhase (s.vertex j) a i : ℂ)) = ToricCharts.monomial s.rays w := by
    rw [rayCompactPhase_vertex_coe]
    exact (monomial_single_coordinate_phase s.rays j a).symm
  change ToricCharts.monomial s.dual (fun i => (rayCompactPhase (s.vertex j) a i : ℂ)) = _
  rw [hv, ToricCharts.monomial_mul_on_torus _ _ hw, ToricFan.Triangle.dual_rays,
    ToricCharts.monomial_one]

private theorem ToricSpace.rayCompactPhase_fixes_of_mem_rayDivisor (v : Fin 2 → ℤ) (a : Circle)
    {x : Space} (hx : x ∈ rayDivisor v) : compactTorusAction (rayCompactPhase v a) x = x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨j, hj, rfl⟩ := (mem_rayDivisor_inclusion v s z).mp hx
  apply (compactTorusAction_inclusion_eq_self_iff _ s z).mpr
  intro i hi
  have hij : i ≠ j := by
    intro h
    subst i
    exact hi hj
  rw [factors_rayCompactPhase_vertex]
  exact ite_eq_right hij

private def
    CuspHoneycombHexagon.positiveComponentSet (v : Fin 2 → ℤ) : Set (ToricSpace.rayDivisor v) :=
  Subtype.val ⁻¹' ToricSpace.positivePart

private abbrev CuspHoneycombHexagon.PositiveComponent (v : Fin 2 → ℤ) :=
  positiveComponentSet v

private abbrev CuspHoneycombHexagon.PositiveE0 :=
  PositiveComponent 0

private theorem CuspHoneycombHexagon.coordinateModulus_insertZero (j : Fin 3)
    (z : ToricCharts.CoordinateSpace 2) :
    ToricCharts.coordinateModulus (ToricComponent.insertZero j z) =
      ToricComponent.insertZero j (ToricCharts.coordinateModulus z) := by
  funext k
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
  · simp [ToricCharts.coordinateModulus]
  · simp [ToricCharts.coordinateModulus, ToricComponent.insertZero, Fin.insertNth_apply_succAbove]

private theorem CuspHoneycombHexagon.affineInclusion_mem_positive_iff {v : Fin 2 → ℤ}
    (c : ToricComponent.ChartIndex v) (z : ToricCharts.CoordinateSpace 2) :
    ToricComponent.affineInclusion c z ∈ positiveComponentSet v ↔
      z ∈ ToricCharts.nonnegativeCoordinates := by
  change
    ToricSpace.modulus
          (ToricSpace.inclusion c.triangle (ToricComponent.insertZero c.coordinate z)) =
        ToricSpace.inclusion c.triangle (ToricComponent.insertZero c.coordinate z) ↔
      _
  rw [ToricSpace.modulus_inclusion, coordinateModulus_insertZero,
    (ToricSpace.inclusion_openEmbedding c.triangle).injective.eq_iff, ←
    ToricCharts.coordinateModulus_eq_self_iff]
  constructor
  · intro h
    simpa only [ToricComponent.removeCoordinate_insertZero] using
      congrArg (ToricComponent.removeCoordinate c.coordinate) h
  · intro h
    exact congrArg (ToricComponent.insertZero c.coordinate) h

private abbrev CuspHoneycombHexagon.PositiveQuadrant :=
  { r : Fin 2 → ℝ // ∀ i, 0 ≤ r i }

private def
    CuspHoneycombHexagon.positiveAffineInclusion {v : Fin 2 → ℤ} (c : ToricComponent.ChartIndex v)
    (r : PositiveQuadrant) : PositiveComponent v :=
  ⟨ToricComponent.affineInclusion c (fun i => (r.1 i : ℂ)),
    (affineInclusion_mem_positive_iff c _).mpr ⟨r.1, r.2, rfl⟩⟩

private theorem CuspHoneycombHexagon.twistedTranslate_zero_correction (v : Fin 2 → ℤ)
    (x : ToricSpace.Space) :
    ToricSpace.twistedTranslate (fun _ => 0) v x =
      ToricSpace.translate (ToricSpace.cuspVector v) x := by
  have he : ToricSpace.exponentialMultiplier (fun _ => 0) v = fun _ => 1 := by
    funext t
    ext i
    simp [ToricSpace.exponentialMultiplier]
  simp [ToricSpace.twistedTranslate, he]

private theorem CuspHoneycombHexagon.zeroComponent_bounded_chart (x : ToricSpace.rayDivisor 0) :
    ∃ (i : Fin 6) (z : ToricCharts.CoordinateSpace 2),
      ‖z‖ ≤ 1 ∧ ToricComponent.affineInclusion (ToricComponent.zeroChart i) z = x := by
  let C : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun _ => 0
  have hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 (1 : ℝ)) := fun _ _ =>
    contDiffOn_const
  obtain ⟨ε, hε, _, hε1, hR, hCε⟩ := CuspQuotient.exists_admissible_radius C (by norm_num) hC
  let a : ToricSpace.Tube (CuspQuotient.disc ε) := CuspQuotient.componentLift ε hε x
  have ha0 : ToricSpace.time (a : ToricSpace.Space) = 0 :=
    ToricSpace.time_eq_zero_of_mem_rayDivisor x.2
  have hrep :=
    CuspQuotient.mem_quotientRepresentatives C ε hε hε1 hCε hR (half_pos hε) (half_lt_self hε)
      (x := a)
      (by
        rw [ha0, norm_zero]
        exact (half_pos hε).le)
  obtain ⟨b, hb, hba⟩ := hrep
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  have horb := Quotient.exact hba
  change b ∈ MulAction.orbit CuspQuotient.LatticeGroup a at horb
  obtain ⟨g, hg⟩ := horb
  have hgb :
    ToricSpace.translate (ToricSpace.cuspVector g.toAdd) (x : ToricSpace.Space) =
      (b : ToricSpace.Space) := by
    have h := congrArg Subtype.val hg
    change
      ToricSpace.twistedTranslate C g.toAdd (x : ToricSpace.Space) = (b : ToricSpace.Space) at h
    rwa [show C = (fun _ => 0) from rfl, twistedTranslate_zero_correction] at h
  change (b : ToricSpace.Space) ∈ CuspQuotient.compactRepresentatives (ε / 2) at hb
  obtain ⟨s, _hs, z, hz, hzb⟩ := Set.mem_iUnion₂.mp hb
  have hx :
    ToricSpace.inclusion (s.shift (-ToricSpace.cuspVector g.toAdd)) z = (x : ToricSpace.Space) := by
    rw [← ToricSpace.translate_inclusion, hzb, ← hgb, ToricSpace.translate_add]
    simp
  obtain ⟨j, hj, hv⟩ := (ToricSpace.mem_rayDivisor_inclusion 0 _ z).mp (hx.symm ▸ x.2)
  let c : ToricComponent.ChartIndex 0 := ⟨s.shift (-ToricSpace.cuspVector g.toAdd), j, hv⟩
  obtain ⟨i, hi⟩ := ToricComponent.zeroChart_surjective c
  refine ⟨i, ToricComponent.removeCoordinate j z, ?_, ?_⟩
  · have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro k
    exact (norm_le_pi_norm z (j.succAbove k)).trans hz1
  · rw [hi]
    apply Subtype.ext
    change
      ToricSpace.inclusion (s.shift (-ToricSpace.cuspVector g.toAdd))
          (ToricComponent.insertZero j (ToricComponent.removeCoordinate j z)) =
        (x : ToricSpace.Space)
    rw [ToricComponent.insertZero_removeCoordinate j z hj]
    exact hx

private theorem CuspHoneycombHexagon.positiveE0_bounded_chart (x : PositiveE0) :
    ∃ (i : Fin 6) (r : PositiveQuadrant),
      (∀ k, r.1 k ≤ 1) ∧ positiveAffineInclusion (ToricComponent.zeroChart i) r = x := by
  obtain ⟨i, z, hz, he⟩ := zeroComponent_bounded_chart x.1
  have hp :
    ToricComponent.affineInclusion (ToricComponent.zeroChart i) z ∈ positiveComponentSet 0 :=
    he.symm ▸ x.2
  obtain ⟨r, hr, hzr⟩ := (affineInclusion_mem_positive_iff (ToricComponent.zeroChart i) z).mp hp
  refine ⟨i, ⟨r, hr⟩, ?_, Subtype.ext ?_⟩
  · intro k
    have hk := (norm_le_pi_norm z k).trans hz
    rwa [hzr, Complex.norm_of_nonneg (hr k)] at hk
  · change ToricComponent.affineInclusion (ToricComponent.zeroChart i) (fun k => (r k : ℂ)) = x.1
    rw [← hzr]
    exact he

private def ToricFan.edgeDirection : Fin 3 → (Fin 2 → ℤ) :=
  ![![1, 0], ![0, 1], ![1, -1] ]

private def ToricFan.AreAdjacent (v w : Fin 2 → ℤ) : Prop :=
  ∃ i : Fin 3, w - v = edgeDirection i ∨ w - v = -edgeDirection i

private theorem
    ToricFan.Triangle.vertices_adjacent (s : ToricFan.Triangle) {j k : Fin 3} (hjk : j ≠ k) :
    ToricFan.AreAdjacent (s.vertex j) (s.vertex k) := by
  cases hs : s.upper <;> fin_cases j <;> fin_cases k <;>
    simp_all [ToricFan.AreAdjacent, vertex, rays, ToricFan.edgeDirection, funext_iff,
      Fin.exists_fin_succ, Fin.forall_fin_succ]

private theorem ToricFan.Triangle.triangle_for_edge (v : Fin 2 → ℤ) (i : Fin 3) :
    ∃ s : ToricFan.Triangle,
      ∃ j k : Fin 3, s.vertex j = v ∧ s.vertex k = v + ToricFan.edgeDirection i := by
  fin_cases i
  · refine ⟨⟨v 0, v 1, Bool.false⟩, 0, 1, ?_, ?_⟩
    all_goals ext a; fin_cases a <;> simp [vertex, rays, ToricFan.edgeDirection]
  · refine ⟨⟨v 0, v 1, Bool.false⟩, 0, 2, ?_, ?_⟩
    all_goals ext a; fin_cases a <;> simp [vertex, rays, ToricFan.edgeDirection]
  · refine ⟨⟨v 0, v 1 - 1, Bool.false⟩, 2, 1, ?_, ?_⟩
    all_goals ext a; fin_cases a <;> simp [vertex, rays, ToricFan.edgeDirection, sub_eq_add_neg]

private theorem ToricFan.Triangle.exists_triangle_of_adjacent {v w : Fin 2 → ℤ}
    (h : ToricFan.AreAdjacent v w) :
    ∃ s : ToricFan.Triangle, ∃ j k : Fin 3, s.vertex j = v ∧ s.vertex k = w := by
  obtain ⟨i, hi | hi⟩ := h
  · have hw : w = v + ToricFan.edgeDirection i := by
      exact (sub_eq_iff_eq_add.mp hi).trans (add_comm _ _)
    obtain ⟨s, j, k, hj, hk⟩ := triangle_for_edge v i
    exact ⟨s, j, k, hj, hk.trans hw.symm⟩
  · have hv : v = w + ToricFan.edgeDirection i := by
      ext a
      have h := congrFun hi a
      change w a - v a = -ToricFan.edgeDirection i a at h
      change v a = w a + ToricFan.edgeDirection i a
      omega
    obtain ⟨s, j, k, hj, hk⟩ := triangle_for_edge w i
    exact ⟨s, k, j, hk.trans hv.symm, hj⟩

private theorem ToricSpace.rayDivisor_inter_nonempty_iff_vertices (v w : Fin 2 → ℤ) :
    (rayDivisor v ∩ rayDivisor w).Nonempty ↔
      ∃ s : ToricFan.Triangle, ∃ j k : Fin 3, s.vertex j = v ∧ s.vertex k = w := by
  constructor
  · rintro ⟨x, hxv, hxw⟩
    obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
    obtain ⟨j, _, hj⟩ := (mem_rayDivisor_inclusion v s z).mp hxv
    obtain ⟨k, _, hk⟩ := (mem_rayDivisor_inclusion w s z).mp hxw
    exact ⟨s, j, k, hj, hk⟩
  · rintro ⟨s, j, k, rfl, rfl⟩
    exact
      ⟨ToricSpace.inclusion s 0, (mem_rayDivisor_vertex s j 0).mpr rfl,
        (mem_rayDivisor_vertex s k 0).mpr rfl⟩

private theorem ToricSpace.rayDivisor_inter_nonempty_iff (v w : Fin 2 → ℤ) (hvw : v ≠ w) :
    (rayDivisor v ∩ rayDivisor w).Nonempty ↔ ToricFan.AreAdjacent v w := by
  rw [rayDivisor_inter_nonempty_iff_vertices]
  constructor
  · rintro ⟨s, j, k, rfl, rfl⟩
    exact ToricFan.Triangle.vertices_adjacent s (fun h => hvw (congrArg s.vertex h))
  · exact ToricFan.Triangle.exists_triangle_of_adjacent

end Mathoverflow1973

end
