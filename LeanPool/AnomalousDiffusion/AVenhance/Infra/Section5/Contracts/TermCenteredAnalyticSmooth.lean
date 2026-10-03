/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsCentered
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalyticJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermFluxesSlice
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialPeriodicity

/-! # Smoothness and `ℤ²`-periodicity of the slow factors

The slow factors `section5SlowChoice2`, `section5SlowChoice3` are `ξ_{m,k}(t)` (a constant in `x`)
times finite sums of products of entries of `∇X⁻¹ - I` (respectively `I - (∇X∘X⁻¹)ᵀ`) and of
`∇G_l`, each smooth and `ℤ²`-periodic. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

theorem sds_isZPeriodic_of_isZ2Periodic {α : Type*} {f : Vec 2 → α} (h : IsZ2Periodic f) :
    Infra.Ergodic.IsZPeriodic f := fun x k => h k x

theorem sds_isZ2Periodic_mul {f g : Vec 2 → ℝ} (hf : IsZ2Periodic f) (hg : IsZ2Periodic g) :
    IsZ2Periodic (fun x => f x * g x) := by
  intro n x
  simp only [hf n x, hg n x]

theorem sds_isZ2Periodic_sum {ι : Type*} (s : Finset ι) {f : ι → Vec 2 → ℝ}
    (hf : ∀ i ∈ s, IsZ2Periodic (f i)) : IsZ2Periodic (fun x => ∑ i ∈ s, f i x) := by
  intro n x
  exact Finset.sum_congr rfl fun i hi => hf i hi n x

theorem sds_isZ2Periodic_const_mul (c : ℝ) {f : Vec 2 → ℝ} (hf : IsZ2Periodic f) :
    IsZ2Periodic (fun x => c * f x) := by
  intro n x
  simp only [hf n x]

/-- Entries of `∇F` are periodic for a differentiable lattice-equivariant `F`. -/
theorem sds_gradMatrix_entry_periodic {F : Vec 2 → Vec 2} (hF : Differentiable ℝ F)
    (he : ∀ k x, F (x + latticeShift k) = F x + latticeShift k) (i j : Fin 2) :
    IsZ2Periodic (fun x => gradMatrix F x i j) := by
  have hp := Infra.Section4.amnr_fderiv_periodic_of_equivariant hF he
  intro k x
  change fderiv ℝ (fun y => F y j) (x + latticeShift k) (basisVec i) =
    fderiv ℝ (fun y => F y j) x (basisVec i)
  rw [fderiv_apply (hF _) j, fderiv_apply (hF _) j, hp k x]

section Slow

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem sds_invGrad_sub_one_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ)
    (i j : Fin 2) :
    IsZ2Periodic (fun x => (gradMatrix (fun z => I.xFlowInv hΦ m l t z) x - 1) i j) := by
  have hdiff : Differentiable ℝ (fun z => I.xFlowInv hΦ m l t z) :=
    (RelativeError.contDiff_xFlowInv_slice I hΦ m l t).differentiable (by simp)
  have hp := sds_gradMatrix_entry_periodic hdiff
    (fun k x => Infra.Section4.amnr_xFlowInv_lattice_equivariant I hΦ m l t k x) i j
  intro n x
  have h := hp n x
  simp only at h
  simp only [Matrix.sub_apply]
  rw [h]

theorem sds_flowGrad_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (i j : Fin 2) :
    IsZ2Periodic (fun x => I.flowGrad hΦ m l t x i j) :=
  Infra.Section4.amnr_flowGrad_spatial_periodic I hΦ m l t i j

theorem sds_contDiff_Y_entry (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (i a : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (1 - (I.flowGrad hΦ m l t x).transpose) i a) := by
  have h := (contDiff_const (c := (1 : Matrix (Fin 2) (Fin 2) ℝ) i a)).sub
    (sdj_contDiff_flowGrad_entry (I := I) hΦ m l t a i)
  simpa only [Matrix.sub_apply, Matrix.transpose_apply,
    show (1 : Matrix (Fin 2) (Fin 2) ℝ) i a = (1 : Matrix (Fin 2) (Fin 2) ℝ) a i by
      simp [Matrix.one_apply, eq_comm]] using h

theorem sds_Y_entry_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (i a : Fin 2) :
    IsZ2Periodic (fun x => (1 - (I.flowGrad hΦ m l t x).transpose) i a) := by
  intro n x
  have h := sds_flowGrad_periodic I hΦ m l t a i n x
  simp only at h
  simp only [Matrix.sub_apply, Matrix.transpose_apply]
  rw [h]

theorem sds_slow2 (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) {t : ℝ}
    (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hTp : IsZ2Periodic (T t)) (k : ℤ) (a j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (section5SlowChoice2 I hΦ m κm T k t a j) ∧
      IsZ2Periodic (section5SlowChoice2 I hΦ m κm T k t a j) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => I.xiMK m k t * κm * ∑ i : Fin 2,
      (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x - 1) i a *
        gradG I hΦ m T (lIdx β I.Λ m k) t x i j) ∧
    IsZ2Periodic (fun x => I.xiMK m k t * κm * ∑ i : Fin 2,
      (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x - 1) i a *
        gradG I hΦ m T (lIdx β I.Λ m k) t x i j)
  refine ⟨contDiff_const.mul (ContDiff.sum fun i _ => ?_),
    sds_isZ2Periodic_const_mul _ (sds_isZ2Periodic_sum _ fun i _ => ?_)⟩
  · exact (sdj_contDiff_invGrad_sub_one_entry hΦ m _ t i a).mul
      (tf_gradG_slice_contDiff I hΦ m T t _ hTt i j)
  · exact sds_isZ2Periodic_mul (sds_invGrad_sub_one_periodic I hΦ m _ t i a)
      (tf_gradG_slice_periodic I hΦ m T t _ hTp i j)

theorem sds_slow3 (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) {t : ℝ}
    (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hTp : IsZ2Periodic (T t)) (k : ℤ) (a j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (section5SlowChoice3 I hΦ m T k t a j) ∧
      IsZ2Periodic (section5SlowChoice3 I hΦ m T k t a j) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => I.xiMK m k t * ∑ i : Fin 2,
      (1 - (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose) i a *
        gradG I hΦ m T (lIdx β I.Λ m k) t x i j) ∧
    IsZ2Periodic (fun x => I.xiMK m k t * ∑ i : Fin 2,
      (1 - (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose) i a *
        gradG I hΦ m T (lIdx β I.Λ m k) t x i j)
  refine ⟨contDiff_const.mul (ContDiff.sum fun i _ => ?_),
    sds_isZ2Periodic_const_mul _ (sds_isZ2Periodic_sum _ fun i _ => ?_)⟩
  · exact (sds_contDiff_Y_entry I hΦ m _ t i a).mul
      (tf_gradG_slice_contDiff I hΦ m T t _ hTt i j)
  · exact sds_isZ2Periodic_mul (sds_Y_entry_periodic I hΦ m _ t i a)
      (tf_gradG_slice_periodic I hΦ m T t _ hTp i j)

end Slow

end AVenhance.Infra.Section5.Contracts
end
