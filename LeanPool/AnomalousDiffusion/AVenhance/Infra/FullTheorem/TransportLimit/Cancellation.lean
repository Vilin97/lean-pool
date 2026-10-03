/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyStatic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergySmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra

/-!
# Slice transport identity against smooth periodic tests

For a bounded measurable periodic divergence-free field `b` and a periodic `H¹` function `u`,
`∫_cell (b·Du) φ = -∫_cell u (b·∇φ)` for every smooth periodic `φ`.  It follows by
polarising the static cancellation `∫ (b·Dv) v = 0` for `v = u - φ`, `u`, `φ`.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

noncomputable section

namespace AVenhance.Infra.FullTheorem.TransportLimit

open AVenhance.Infra.Parabolic.WeakUniqueness
open AVenhance.Infra.Section5.RelativeError

local instance cancellationFiniteUnitCube : IsFiniteMeasure (volume.restrict unitCube) := by
  refine ⟨?_⟩
  unfold unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

theorem unitCube_measurableSet' : MeasurableSet unitCube := by
  unfold unitCube
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

/-- Coordinates of a bounded measurable field are essentially bounded on the cell. -/
theorem bcoord_memLp_top {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) (i : Fin 2) :
    MemLp (fun x => b x i) ⊤ (volume.restrict unitCube) := by
  obtain ⟨C, -, hCb⟩ := hbBound
  have hbi : AEStronglyMeasurable (fun x => b x i) (volume.restrict unitCube) :=
    (continuous_apply i).comp_aestronglyMeasurable
      (hbMeas.mono_measure Measure.restrict_le_self)
  apply MemLp.of_bound hbi C
  filter_upwards with x
  exact (norm_le_pi_norm (b x) i).trans (hCb x)

/-- The transport pairing of a bounded field with an `L²` gradient is `L²`. -/
theorem drift_memL2 {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) {D : Vec 2 → Vec 2}
    (hD : GradMemL2On unitCube D) :
    MemL2On unitCube (fun x => vecDot (b x) (D x)) := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      MemLp (fun x => b x i * D x i) 2 (volume.restrict unitCube) := fun i _ =>
    (bcoord_memLp_top hbMeas hbBound i).mul (hD i)
  have := memLp_finsetSum (Finset.univ : Finset (Fin 2)) h
  simpa [vecDot] using this

theorem slice_transport_identity {b : Vec 2 → Vec 2}
    (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) (hbPer : IsZ2Periodic b)
    (hDiv : ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b x) (spaceGrad φ x) = 0)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2} (hu : IsPeriodicH1With u Du)
    {φ : Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφp : IsZ2Periodic φ) :
    ∫ x in unitCube, vecDot (b x) (Du x) * φ x =
      -∫ x in unitCube, u x * vecDot (b x) (spaceGrad φ x) := by
  have hcell : ∀ f : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → IsZ2Periodic f →
      ∫ x in AVenhance.Infra.Torus.unitCell 2, vecDot (b x) (spaceGrad f x) = 0 :=
    fun f hf hfp => AVenhance.Infra.Parabolic.WeakUniqueness.isDivFree_integral_periodic_smooth_test
      hbMeas hbBound hbPer hDiv hf hfp
  have hstatic : ∀ {v : Vec 2 → ℝ} {Dv : Vec 2 → Vec 2}, IsPeriodicH1With v Dv →
      ∫ x in unitCube, vecDot (b x) (Dv x) * v x = 0 := by
    intro v Dv hv
    have := static_divFree_h1_cancellation hbMeas hbBound hcell hv
    rwa [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube] at this
  have hφH : IsPeriodicH1With φ (fun x => spaceGrad φ x) :=
    isPeriodicH1With_of_contDiff (hφ.of_le (by simp)) hφp
  have hwH := isPeriodicH1With_sub hu hφH
  have h1 := hstatic hu
  have h4 := hstatic hφH
  have h5 := hstatic hwH
  have hA := drift_memL2 hbMeas hbBound hu.2.2.2.1
  have hB := drift_memL2 hbMeas hbBound hφH.2.2.2.1
  have hu2 : MemL2On unitCube u := hu.2.2.1
  have hφ2 : MemL2On unitCube φ := hφH.2.2.1
  have iAu := weak_product_integrable_cell hA hu2
  have iAφ := weak_product_integrable_cell hA hφ2
  have iBu := weak_product_integrable_cell hB hu2
  have iBφ := weak_product_integrable_cell hB hφ2
  have hexp : (fun x => vecDot (b x) (Du x - spaceGrad φ x) * (u x - φ x)) =
      fun x => ((vecDot (b x) (Du x) * u x - vecDot (b x) (Du x) * φ x) -
        vecDot (b x) (spaceGrad φ x) * u x) + vecDot (b x) (spaceGrad φ x) * φ x := by
    funext x
    simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_mul]
    ring
  have h5' : ∫ x in unitCube, vecDot (b x) (Du x - spaceGrad φ x) * (u x - φ x) = 0 := h5
  rw [hexp] at h5'
  have s1 := integral_sub (μ := volume.restrict unitCube) iAu iAφ
  have s2 := integral_sub (μ := volume.restrict unitCube) (iAu.sub iAφ) iBu
  have s3 := integral_add (μ := volume.restrict unitCube) ((iAu.sub iAφ).sub iBu) iBφ
  simp only [Pi.sub_apply] at s2 s3
  rw [s3, s2, s1] at h5'
  have e : ∫ x in unitCube, u x * vecDot (b x) (spaceGrad φ x) =
      ∫ x in unitCube, vecDot (b x) (spaceGrad φ x) * u x := by
    congr 1; funext x; ring
  rw [e]
  linarith

end AVenhance.Infra.FullTheorem.TransportLimit
