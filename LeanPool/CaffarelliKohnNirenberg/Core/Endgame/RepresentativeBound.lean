/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.HeatRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-! # Reanchoring a Hölder representative by velocity averages

The absolute value of a representative is controlled by averaging its
oscillation against the original velocity. No average of the heat potential
outside the region of almost-everywhere agreement is required.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- A Hölder seminorm and an `L³` average on a positive finite-measure set
control the full norm on any set at bounded distance from it. -/
theorem holder_norm_of_seminorm_of_ae_eq
    {S T : Set ParabolicPoint} {u w : ParabolicPoint → Vec3} {γ K D : ℝ}
    (hS : MeasurableSet S) (hSpos : 0 < volume S) (hStop : volume S < ∞)
    (hγ : 0 ≤ γ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hdist : ∀ x ∈ T, ∀ y ∈ S, parabolicDist x y ≤ D)
    (hsemi : ∀ x y, vec3EuclideanNorm (w x - w y) ≤ K * parabolicDist x y ^ γ)
    (hrep : w =ᵐ[volume.restrict S] u)
    (hu : IntegrableOn (fun x => vec3EuclideanNorm (u x)) S)
    (hu3 : IntegrableOn (fun x => vec3EuclideanNorm (u x) ^ (3 : ℝ)) S) :
    ParabolicHolderVecNormLE T w γ
      (K * D ^ γ + (⨍ x in S, vec3EuclideanNorm (u x) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) + K) := by
  have haverage : 0 ≤ ⨍ x in S, vec3EuclideanNorm (u x) ^ (3 : ℝ) :=
    Integration.setAverage_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (vec3EuclideanNorm_nonneg _) _)
  have hroot : 0 ≤ (⨍ x in S, vec3EuclideanNorm (u x) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg haverage _
  refine ⟨K * D ^ γ + (⨍ x in S, vec3EuclideanNorm (u x) ^ (3 : ℝ)) ^ (1 / 3 : ℝ),
    K, add_nonneg (mul_nonneg hK (Real.rpow_nonneg hD γ)) hroot, hK, le_rfl, ?_,
    fun x _ y _ => hsemi x y⟩
  intro x hx
  have hpoint : ∀ᵐ y ∂volume.restrict S,
      vec3EuclideanNorm (w x) ≤ K * D ^ γ + vec3EuclideanNorm (u y) := by
    filter_upwards [hrep, ae_restrict_mem hS] with y hy hys
    have htri : vec3EuclideanNorm (w x) ≤
        vec3EuclideanNorm (w x - w y) + vec3EuclideanNorm (w y) := by
      rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
        WithLp.toLp_sub]
      have h := norm_add_le (WithLp.toLp 2 (w x - w y)) (WithLp.toLp 2 (w y))
      simpa only [WithLp.toLp_sub, sub_add_cancel] using h
    have hdiff := (hsemi x y).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (parabolicDist_nonneg x y) (hdist x hx y hys) hγ) hK)
    exact htri.trans (add_le_add hdiff (by rw [hy]))
  have hmean : vec3EuclideanNorm (w x) ≤ K * D ^ γ +
      ⨍ y in S, vec3EuclideanNorm (u y) := by
    have hav := Integration.setAverage_mono_of_ae
      (integrableOn_const hStop.ne) ((integrableOn_const hStop.ne).add hu) hpoint
    rw [Integration.setAverage_add_of_integrableOn
      (f := fun _ : ParabolicPoint => K * D ^ γ)
      (integrableOn_const hStop.ne) hu,
      Integration.setAverage_const_of_pos_of_lt_top hSpos hStop,
      Integration.setAverage_const_of_pos_of_lt_top hSpos hStop] at hav
    exact hav
  have hmean3 : (⨍ y in S, vec3EuclideanNorm (u y)) ≤
      (⨍ y in S, vec3EuclideanNorm (u y) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
    have hu3' : IntegrableOn (fun x => |vec3EuclideanNorm (u x)| ^ (3 : ℝ)) S := by
      simpa only [abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using hu3
    have h := Integration.setAverage_abs_rpow_norm_mono
      (f := fun x => vec3EuclideanNorm (u x)) (q := 1) (p := 3)
      (by norm_num) (by norm_num) hSpos hStop hu hu3'
    simpa only [abs_of_nonneg (vec3EuclideanNorm_nonneg _), Real.rpow_one,
      inv_one, one_div] using h
  exact hmean.trans (add_le_add_right hmean3 _)

private theorem closed_halfCylinder_subset_half_closedBall :
    closure (parabolicCylinder 0 0 (1 / 2)) ⊆
      Metric.closedBall ((0, 0) : ParabolicPoint) (1 / 2) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  exact (parabolicCylinder_subset_metricBall_sameCenter
    ((0, 0) : ParabolicPoint) (by norm_num : (0 : ℝ) < 1 / 2)).trans
      Metric.ball_subset_closedBall

/-- Reanchoring on the half-cylinder gives the full closed-cylinder norm
`2 K + (average |u|³)^(1/3)` from the global seminorm `K`. -/
theorem halfCylinder_holder_norm_of_seminorm
    {u w : ParabolicPoint → Vec3} {γ K : ℝ}
    (hγ : 0 ≤ γ) (hK : 0 ≤ K)
    (hsemi : ∀ x y, vec3EuclideanNorm (w x - w y) ≤ K * parabolicDist x y ^ γ)
    (hrep : w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u)
    (hu : IntegrableOn (fun x => vec3EuclideanNorm (u x))
      (parabolicCylinder 0 0 (1 / 2)))
    (hu3 : IntegrableOn (fun x => vec3EuclideanNorm (u x) ^ (3 : ℝ))
      (parabolicCylinder 0 0 (1 / 2))) :
    ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2))) w γ
      (2 * K + (⨍ x in parabolicCylinder 0 0 (1 / 2),
        vec3EuclideanNorm (u x) ^ (3 : ℝ)) ^ (1 / 3 : ℝ)) := by
  have hdist : ∀ x ∈ closure (parabolicCylinder 0 0 (1 / 2)),
      ∀ y ∈ parabolicCylinder 0 0 (1 / 2), parabolicDist x y ≤ 1 := by
    intro x hx y hy
    let c : ParabolicPoint := (0, 0)
    have hx' := Metric.mem_closedBall.mp (closed_halfCylinder_subset_half_closedBall hx)
    have hy' := Metric.mem_closedBall.mp
      (closed_halfCylinder_subset_half_closedBall (subset_closure hy))
    rw [← dist_eq_parabolicDist]
    calc
      dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) + 1 / 2 := add_le_add hx' (by rw [dist_comm]; exact hy')
      _ = 1 := by norm_num
  have h := holder_norm_of_seminorm_of_ae_eq
    (show MeasurableSet (parabolicCylinder 0 0 (1 / 2)) from
      (vec3Ball_measurable 0 (1 / 2)).prod measurableSet_Ioc)
    (Integration.volume_parabolicCylinder_pos (by norm_num : (0 : ℝ) < 1 / 2))
    Integration.volume_parabolicCylinder_lt_top hγ hK (by norm_num : (0 : ℝ) ≤ 1)
    hdist hsemi hrep hu hu3
  simpa only [Real.one_rpow, mul_one, show ∀ A : ℝ, K + A + K = 2 * K + A by
    intro A; ring] using h

/-- The heat estimate reanchored entirely inside the velocity cylinder. Its
constant depends on the actual source norms and the velocity `L³` average,
not on values of the potential at future times. -/
theorem halfCylinder_reanchored_heat_representative
    {u F : ParabolicPoint → Vec3} {G : Fin 3 → ParabolicPoint → Vec3}
    {γ θ₀ θ₁ P : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5) (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : ∀ i, AEMeasurable (fun x => F x i) volume)
    (hG : ∀ j i, AEMeasurable (fun x => G j x i) volume)
    (hNF : ∀ i, morreyNorm P θ₀ (fun x => F x i) < ∞)
    (hNG : ∀ j i, morreyNorm P θ₁ (fun x => G j x i) < ∞)
    (hSupportF : ∀ i, HasCompactSupport (fun x => F x i))
    (hSupportG : ∀ j i, HasCompactSupport (fun x => G j x i))
    (hrep : u =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))]
      (fun x i => heatPotential (fun y => F y i) (fun j y => G j y i) x))
    (hu : IntegrableOn (fun x => vec3EuclideanNorm (u x))
      (parabolicCylinder 0 0 (1 / 2)))
    (hu3 : IntegrableOn (fun x => vec3EuclideanNorm (u x) ^ (3 : ℝ))
      (parabolicCylinder 0 0 (1 / 2))) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
      ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2))) w γ
        (2 * vectorHeatHolderCoefficient F G γ θ₀ θ₁ P +
          (⨍ x in parabolicCylinder 0 0 (1 / 2),
            vec3EuclideanNorm (u x) ^ (3 : ℝ)) ^ (1 / 3 : ℝ)) := by
  obtain ⟨w, hw, hsemi, _hlocal⟩ := vector_heat_representative_and_seminorm_of_morrey
    hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ hF hG hNF hNG hSupportF hSupportG
  have hwlocal : w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))]
      (fun x i => heatPotential (fun y => F y i) (fun j y => G j y i) x) :=
    ae_restrict_of_ae hw
  have hwu := hwlocal.trans hrep.symm
  exact ⟨w, hwu, halfCylinder_holder_norm_of_seminorm hγ.le
    (Finset.sum_nonneg fun i _ => abs_nonneg _) hsemi hwu hu hu3⟩

end CKN.Core.Endgame
