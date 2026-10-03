/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.BaseEnergyIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.TimeCube
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.UnitCube

/-! # the energy identity in the carriers

Translates the cell-integral identities of `BaseEnergyIdentity` into `l2NormSq`, `gradNormSq`
(over `unitCube`) and `spaceTimeGradNormSq` (over `timeCube`), and adds the mean-zero Poincaré
inequality along the solution.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Torus
open AVenhance.Infra.Classical
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

variable {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {g : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}

theorem l2NormSq_eq_cell (f : Vec 2 → ℝ) :
    l2NormSq f = ∫ x in unitCell 2, f x ^ 2 := by
  unfold l2NormSq
  exact (integral_unitCell_eq_unitCube _).symm

theorem gradNormSq_spaceGrad_eq_cellGrad (f : ℝ → Vec 2 → ℝ) (s : ℝ) :
    gradNormSq (spaceGrad (f s)) = cellGrad f s := by
  unfold gradNormSq cellGrad
  exact (integral_unitCell_eq_unitCube _).symm

theorem classical_energy_hasDerivAt (hφ : IsAdmissibleStream φ)
    (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g θ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in unitCell 2, (θ s x) ^ 2) (-(2 * κ) * cellGrad θ t) t := by
  simpa [cellGrad] using classical_shift_hasDerivAt φ hφ hsol 0 ht

/-- The integrated energy identity in cell form. -/
theorem classical_cell_energy_identity (hφ : IsAdmissibleStream φ)
    (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g θ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ x in unitCell 2, (θ T x) ^ 2) - (∫ x in unitCell 2, (g x) ^ 2) =
      ∫ s in (0 : ℝ)..T, -(2 * κ) * cellGrad θ s := by
  have hcont : ContinuousOn (fun s => ∫ x in unitCell 2, (θ s x) ^ 2) (Set.Icc 0 T) := by
    simpa using shift_energy_continuousOn hsol 0 hT
  have hint : IntervalIntegrable (fun s => -(2 * κ) * cellGrad θ s) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact continuousOn_const.mul (cellGrad_continuousOn hsol hT)
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hcont
    (f' := fun s => -(2 * κ) * cellGrad θ s)
    (fun s hs => (classical_energy_hasDerivAt hφ hsol hs.1).hasDerivWithinAt) hint
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [hsol.2.2.1 x]

/-- The integrated energy identity in the carriers, for every `t ≥ 0`. -/
theorem classical_energy_identity_frozen (hφ : IsAdmissibleStream φ)
    (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g θ) {t : ℝ} (ht : 0 ≤ t) :
    l2NormSq (θ t) + 2 * κ * ∫ s in (0 : ℝ)..t, gradNormSq (spaceGrad (θ s)) = l2NormSq g := by
  have h := classical_cell_energy_identity hφ hsol ht
  rw [intervalIntegral.integral_const_mul] at h
  rw [l2NormSq_eq_cell, l2NormSq_eq_cell]
  simp only [gradNormSq_spaceGrad_eq_cellGrad]
  linarith

theorem gradNormSq_continuousOn (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g θ)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun s => gradNormSq (spaceGrad (θ s))) (Set.Icc 0 T) := by
  simp only [gradNormSq_spaceGrad_eq_cellGrad]
  exact cellGrad_continuousOn hsol hT

theorem gradNormSq_nonneg' (f : Vec 2 → ℝ) : 0 ≤ gradNormSq (spaceGrad f) :=
  integral_nonneg fun x => by
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- Fubini: the space-time gradient norm is the time integral of the slice norms. -/
theorem spaceTimeGradNormSq_eq_intervalIntegral
    (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g θ) :
    spaceTimeGradNormSq (fun t x => spaceGrad (θ t) x) =
      ∫ s in (0 : ℝ)..1, gradNormSq (spaceGrad (θ s)) := by
  let h : ℝ × Vec 2 → ℝ := fun p => vecNormSq (spaceGrad (θ p.1) p.2)
  have hcomp (i : Fin 2) : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (θ p.1) p.2 i)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (spaceGrad_component_contDiffOn hsol i).continuousOn
  have hcont : ContinuousOn h (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    have : h = fun p => spaceGrad (θ p.1) p.2 0 * spaceGrad (θ p.1) p.2 0 +
        spaceGrad (θ p.1) p.2 1 * spaceGrad (θ p.1) p.2 1 := by
      funext p
      simp [h, vecNormSq, vecDot, Fin.sum_univ_two]
    rw [this]
    exact ((hcomp 0).mul (hcomp 0)).add ((hcomp 1).mul (hcomp 1))
  let K : Set (ℝ × Vec 2) := Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 :
      ℝ) 1)
  have hKc : IsCompact K :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hKs : K ⊆ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
    rintro ⟨t, x⟩ ⟨ht, _⟩
    exact ⟨ht.1, Set.mem_univ _⟩
  have hTK : timeCube ⊆ K := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨⟨ht.1.le, ht.2.le⟩, ?_⟩
    intro i _
    have := hx i (Set.mem_univ i)
    exact ⟨this.1.le, this.2.le⟩
  have hint : IntegrableOn h timeCube :=
    ((hcont.mono hKs).integrableOn_compact hKc).mono_set hTK
  unfold spaceTimeGradNormSq
  change ∫ p in timeCube, h p = _
  unfold timeCube at hint ⊢
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [setIntegral_prod h hint]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rfl

end AVenhance.Infra.Section5.RelativeError
