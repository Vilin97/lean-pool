/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceCoefficient
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceExponents
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.VelocityAverage
public import LeanPool.CaffarelliKohnNirenberg.Core.Parameters

/-!
# Uniform closed-half-cylinder control from concrete heat sources

Finite numerical bounds on the source Morrey norms control the Hölder
seminorm. The original small-data condition controls the velocity average.
Together they give a quantitative representative with constants chosen
before the solution. Construction of the heat sources is a separate step.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential


noncomputable section

namespace CKN.Core.Endgame

/-- The uniform half-cylinder norm bound determined by the source norm
bounds and the small-data threshold. -/
def uniformHalfCylinderHolderBound (q ε₀ : ℝ) (KF KG : ℝ≥0∞) : ℝ :=
  2 * uniformVectorHeatHolderCoefficient (stepGamma₀ q)
    (stepTheta₀ (stepGamma₀ q)) (stepTheta₁ (stepGamma₀ q)) (6 / 5) KF KG +
      ((volume (parabolicCylinder 0 0 (1 / 2))).toReal⁻¹ * ε₀) ^ (1 / 3 : ℝ)

/-- The numerical half-cylinder bound is nonnegative. -/
theorem uniformHalfCylinderHolderBound_nonneg
    (q ε₀ : ℝ) (KF KG : ℝ≥0∞) (hε₀ : 0 ≤ ε₀) :
    0 ≤ uniformHalfCylinderHolderBound q ε₀ KF KG := by
  unfold uniformHalfCylinderHolderBound
  exact add_nonneg
    (mul_nonneg (by norm_num) (uniformVectorHeatHolderCoefficient_nonneg _ _ _ _ _ _))
    (Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) hε₀) _)

/-- Concrete heat sources with uniform finite Morrey bounds, an a.e.
representation on the half-cylinder, and the original small-data hypothesis
give the quantitative closed-half-cylinder representative and its interior
regular points. All numerical bounds are fixed before the solution. -/
theorem uniform_halfCylinder_representative_of_heat_sources
    (q ε₀ : ℝ) (KF KG : ℝ≥0∞)
    (hq : 5 / 2 < q) (hε₀ : 0 ≤ ε₀) (hKF : KF < ⊤) (hKG : KG < ⊤)
    {Ω : Set Vec3} {I : Set ℝ}
    {u F : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {G : Fin 3 → ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ z in parabolicCylinder 0 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (hF : ∀ i, AEMeasurable (fun x => F x i) volume)
    (hG : ∀ j i, AEMeasurable (fun x => G j x i) volume)
    (hNF : ∀ i, morreyNorm (6 / 5) (stepTheta₀ (stepGamma₀ q))
      (fun x => F x i) ≤ KF)
    (hNG : ∀ j i, morreyNorm (6 / 5) (stepTheta₁ (stepGamma₀ q))
      (fun x => G j x i) ≤ KG)
    (hSupportF : ∀ i, HasCompactSupport (fun x => F x i))
    (hSupportG : ∀ j i, HasCompactSupport (fun x => G j x i))
    (hrep : u =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))]
      (fun x i => heatPotential (fun y => F y i) (fun j y => G j y i) x)) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
      ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
        w (stepGamma₀ q) (uniformHalfCylinderHolderBound q ε₀ KF KG) ∧
      ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
        IsRegularPoint Ω I u z := by
  have hγ := stepGamma₀_pos hq
  have hγ1 := stepGamma₀_lt_one q
  have hθ₀ := stepTheta₀_gt_half hγ hγ1
  have hθ₁ := stepTheta₁_gt_five hγ hγ1
  obtain ⟨w, hwu, hnorm, hreg⟩ := halfCylinder_representative_of_heat_sources_of_small_data
    hε₀ hsol hdom hsmall hγ hγ1 (stepTheta₀_inv _) (stepTheta₁_inv _)
    (by norm_num : (1 : ℝ) ≤ 6 / 5)
    (by linarith only [hθ₀]) (by linarith only [hθ₁]) hF hG
    (fun i => (hNF i).trans_lt hKF) (fun j i => (hNG j i).trans_lt hKG)
    hSupportF hSupportG hrep
  refine ⟨w, hwu, ?_, hreg⟩
  have hcoef := vectorHeatHolderCoefficient_le_of_source_bounds
    (stepGamma₀ q) (stepTheta₀ (stepGamma₀ q)) (stepTheta₁ (stepGamma₀ q))
    (6 / 5) KF KG hKF hKG hNF hNG
  obtain ⟨B, K, hB, hK, hBK, hb, hk⟩ := hnorm
  refine ⟨B, K, hB, hK, hBK.trans ?_, hb, hk⟩
  exact add_le_add
    (mul_le_mul_of_nonneg_left hcoef (show (0 : ℝ) ≤ 2 by norm_num)) le_rfl

private theorem hasCompactSupport_of_unitCylinder_support
    {g : ParabolicPoint → ℝ}
    (hsupp : ∀ x ∉ parabolicCylinder (0 : Vec3) 0 1, g x = 0) :
    HasCompactSupport g := by
  have hspace : IsCompact {x : Vec3 | vec3EuclideanNorm (x - 0) ≤ 1} := by
    have hcompact := vec3Homeomorph.isCompact_preimage.mpr
      (isCompact_closedBall (vec3Homeomorph (0 : Vec3)) 1)
    convert hcompact using 1
    ext x
    simp only [mem_ofPred_eq, mem_preimage, Metric.mem_closedBall,
      vec3Homeomorph_apply, dist_eq_norm, ← WithLp.toLp_sub,
      ← vec3EuclideanNorm_eq_l2]
  have hcompact : IsCompact (closure (parabolicCylinder (0 : Vec3) 0 1)) := by
    apply parabolicHomeomorph.symm.isCompact_preimage.mp
    rw [closure_parabolicCylinder one_pos]
    exact hspace.prod isCompact_Icc
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro x hx
  apply subset_closure
  by_contra hnot
  exact hx (hsupp x hnot)

/-- Unit-cylinder-supported sources at the paper's exponents give the same
uniform closed-half-cylinder norm. Compact support and the heat exponents
are derived without increasing the numerical source bounds. -/
theorem uniform_halfCylinder_representative_of_paper_source_bounds
    (q ε₀ : ℝ) (KF KG : ℝ≥0∞)
    (hq : 5 / 2 < q) (hε₀ : 0 ≤ ε₀) (hKF : KF < ⊤) (hKG : KG < ⊤)
    {Ω : Set Vec3} {I : Set ℝ}
    {u F : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {G : Fin 3 → ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ z in parabolicCylinder 0 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (hF : ∀ i, AEMeasurable (fun x => F x i) volume)
    (hG : ∀ j i, AEMeasurable (fun x => G j x i) volume)
    (hNF : ∀ i, morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
      (fun x => F x i) ≤ KF)
    (hNG : ∀ j i, morreyNorm (6 / 5) (25 / 3 : ℝ)
      (fun x => G j x i) ≤ KG)
    (hSupportF : ∀ i, ∀ x ∉ parabolicCylinder (0 : Vec3) 0 1, F x i = 0)
    (hSupportG : ∀ j i, ∀ x ∉ parabolicCylinder (0 : Vec3) 0 1, G j x i = 0)
    (hrep : u =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))]
      (fun x i => heatPotential (fun y => F y i) (fun j y => G j y i) x)) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
      ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
        w (stepGamma₀ q) (uniformHalfCylinderHolderBound q ε₀ KF KG) ∧
      ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
        IsRegularPoint Ω I u z := by
  obtain ⟨hNF', hNG'⟩ := source_norm_bounds_at_holder_exponents_unit
    q KF KG hq hNF hNG hSupportG
  exact uniform_halfCylinder_representative_of_heat_sources
    q ε₀ KF KG hq hε₀ hKF hKG hsol hdom hsmall hF hG hNF' hNG'
    (fun i => hasCompactSupport_of_unitCylinder_support (hSupportF i))
    (fun j i => hasCompactSupport_of_unitCylinder_support (hSupportG j i)) hrep

end CKN.Core.Endgame
