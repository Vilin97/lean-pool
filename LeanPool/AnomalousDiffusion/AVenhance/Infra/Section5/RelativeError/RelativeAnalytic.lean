/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativePositiveComposition
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.Bridge

/-! Positive-temperature-jet quadratic bridge. No zeroth temperature norm is used. -/

@[expose] public section

noncomputable section
open scoped ContDiff
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section5.RelativeError
open AVenhance AVenhance.FaaDiBruno AVenhance.Infra.Section5.AnalyticBridge

/-- Positive spatial jets with an arbitrary amplitude on the actual T. -/
def PositiveTemperatureJets (A ρ S : ℝ) (T : ℝ → Vec 2 → ℝ) : Prop :=
  ∀ n : ℕ, ∀ i : Fin n → Fin 2, 0 < n → ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ n (T t) x
      (fun j => basisVec (i j)))) ≤ A * S * n.factorial * (A / ρ) ^ n

theorem fderiv_eq_zero_of_amplitude_zero {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : IsZ2Periodic f) {a : ℝ} (ha : 1 ≤ a)
    (hreg : ∀ (n : ℕ) (i : Fin n → Fin 2), 0 < n →
      Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j)))) ≤
        0 * n.factorial * a ^ n) (v : Fin 2) (x : Vec 2) :
    fderiv ℝ f x (basisVec v) = 0 := by
  have h := abs_iteratedFDeriv_fderiv_le hf hp le_rfl ha hreg 0 (fun j => Fin.elim0 j) v x
  simp only [zero_mul, mul_zero, abs_nonpos_iff, iteratedFDeriv_zero_apply] at h
  exact h

/-- **Route A bridge**: `e.Tm.reg.upgrade` (all orders, `L²_x`), `H² ⊂ L∞`, `l.product`,
proposition 10528 and `e.flow.for.ergodic` give the composed `L¹` analyticity required by
`l.flow.averages`.  Amplitude `A' ρ^{-6} ‖θ₀‖²` (so `p = 6`), radius `ρ / A'`. -/
theorem relative_hasCoordinateAnalyticL1Bounds_of_bounds (A : ℝ) (hA : 1 ≤ A) :
    ∃ A' : ℝ, 1 ≤ A' ∧ ∀ (S : ℝ) (T : ℝ → Vec 2 → ℝ) (ρ e : ℝ) (X : Vec 2 → Vec 2),
      0 ≤ S → 0 < ρ → ρ ≤ e → e ≤ 1 →
      PositiveTemperatureJets A ρ S T → FlowForErgodicBound A e X → ContDiff ℝ (⊤ : ℕ∞) X →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ContDiff ℝ (⊤ : ℕ∞) (T t) → IsZ2Periodic (T t) →
      ∀ i j : Fin 2,
        Infra.Ergodic.HasCoordinateAnalyticL1Bounds
          (fun y => ((spaceGrad (T t) (X y) i * spaceGrad (T t) (X y) j : ℝ) : ℂ))
          (A' * ρ ^ (-6 : ℤ) * S ^ 2) (ρ / A') := by
  obtain ⟨K, hK1, hK⟩ := exists_poly_le_two_pow
  refine ⟨bridgeConst K A, one_le_bridgeConst hK1 hA, ?_⟩
  intro S T ρ e X hS hρ hρe he1 hT hX hXs t ht hTs hTp i j i' n hn
  have hTs' : ContDiff ℝ ∞ (T t) := hTs
  have hXs' : ContDiff ℝ ∞ X := hXs
  have hreg := fun (m : ℕ) (w : Fin m → Fin 2) (hm : 0 < m) => hT m w hm t
      (Set.Ioo_subset_Icc_self ht)
  set N : ℝ := S with hNdef
  have hN2 : N ^ 2 = S ^ 2 := rfl
  have hA'1 := one_le_bridgeConst hK1 hA
  have hA'0 : 0 < bridgeConst K A := lt_of_lt_of_le one_pos hA'1
  have hM0 : 0 ≤ (bridgeConst K A * ρ ^ (-6 : ℤ) * S ^ 2) * n.factorial /
      (ρ / bridgeConst K A) ^ n := by
    have := sq_nonneg S
    positivity
  have hFs : ContDiff ℝ ∞ ((fun y => fderiv ℝ (T t) y (basisVec i) * fderiv ℝ (T t) y (basisVec
      j)) ∘ X) :=
    (((contDiff_fderiv_apply_basis hTs' i).mul (contDiff_fderiv_apply_basis hTs' j))).comp hXs'
  have hfun : (fun y => ((spaceGrad (T t) (X y) i * spaceGrad (T t) (X y) j : ℝ) : ℂ)) =
      fun x => ((((fun y => fderiv ℝ (T t) y (basisVec i) * fderiv ℝ (T t) y (basisVec j)) ∘ X) x
          : ℝ) : ℂ) :=
    rfl
  rw [hfun]
  refine integral_norm_unitCell_le hM0 fun x => ?_
  rw [norm_coordDerivIter_ofReal hFs]
  rcases hS.eq_or_lt with hN0 | hNpos
  · -- Zero amplitude still controls every gradient.
    have hreg0 : ∀ (m : ℕ) (w : Fin m → Fin 2), 0 < m →
        Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ m (T t) x (fun j => basisVec (w j)))) ≤
          0 * m.factorial * (A / ρ) ^ m := by
      intro m w hm
      have := hreg m w hm
      have hN0' : N = 0 := hN0.symm
      rwa [hN0', mul_zero] at this
    have ha1 : 1 ≤ A / ρ := by
      rw [le_div_iff₀ hρ]; linarith
    have hzero : ((fun y => fderiv ℝ (T t) y (basisVec i) * fderiv ℝ (T t) y (basisVec j)) ∘ X)
        = fun _ => (0 : ℝ) := by
      funext y
      simp [fderiv_eq_zero_of_amplitude_zero hTs' hTp ha1 hreg0 i,
        fderiv_eq_zero_of_amplitude_zero hTs' hTp ha1 hreg0 j]
    rw [hzero, orderedPartial_eq_iteratedFDeriv contDiff_const,
      iteratedFDeriv_const_of_ne hn.ne']
    simpa using hM0
  · have hNpos' : 0 < N := hNpos
    have hreg' : ∀ (m : ℕ) (w : Fin m → Fin 2), 0 < m →
        Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ m (T t) x (fun j => basisVec (w j)))) ≤
          (A * N) * m.factorial * (A / ρ) ^ m := hreg
    have hpt := orderedPartial_comp_le hK1 hK hA hρ hρe he1 hNpos' hTs' hTp hreg' hX hXs' i j n x
      (fun _ => i')
    refine hpt.trans ?_
    have := combine_bound (N := N) hK1 hA hρ hρe n
    rwa [hN2] at this

end AVenhance.Infra.Section5.RelativeError
