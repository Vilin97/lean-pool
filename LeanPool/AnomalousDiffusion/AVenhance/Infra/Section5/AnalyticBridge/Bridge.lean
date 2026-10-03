/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.CompBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic

/-! # The `L²_x → L¹` composed-analyticity bridge (route A)

`e.Tm.reg.upgrade` (all orders, `L²_x`) + `H² ⊂ L∞` + `l.product` + proposition 10528 +
`e.flow.for.ergodic` give the averaged coordinate-derivative bounds for `∂_iT ∂_jT ∘ X` required by
`l.flow.averages`.  The constant is `A' ρ^{-6} ‖θ₀‖²` with radius `ρ / A'`.
-/

@[expose] public section

noncomputable section

open scoped ContDiff
open Homogenization MeasureTheory

namespace AVenhance.Infra.Section5.AnalyticBridge

open AVenhance AVenhance.FaaDiBruno

/-- The bridge constant `A' = 4 (3 sc K)² A⁸ + (2 + 8K) A²`. -/
def bridgeConst (K A : ℝ) : ℝ :=
  4 * (3 * sobolevConst * K) ^ 2 * A ^ 8 + (2 + 8 * K) * A ^ 2

theorem one_le_bridgeConst {K A : ℝ} (hK : 1 ≤ K) (hA : 1 ≤ A) : 1 ≤ bridgeConst K A := by
  unfold bridgeConst
  have h1 : (1 : ℝ) ≤ A ^ 2 := one_le_pow₀ hA
  have h2 : 0 ≤ 4 * (3 * sobolevConst * K) ^ 2 * A ^ 8 := by positivity
  nlinarith

/-- The composed radius is at most `A' / ρ`. -/
theorem radius_le_bridgeConst {K A ρ e : ℝ} (hK : 1 ≤ K) (hA : 1 ≤ A) (hρ : 0 < ρ)
    (hρe : ρ ≤ e) :
    (2 * A / e) * (1 + ((2 : ℕ) : ℝ) * (K * e) * (2 * (A / ρ))) ≤ bridgeConst K A / ρ := by
  have he : 0 < e := lt_of_lt_of_le hρ hρe
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have heq : (2 * A / e) * (1 + ((2 : ℕ) : ℝ) * (K * e) * (2 * (A / ρ))) =
      2 * A / e + 8 * K * A ^ 2 / ρ := by
    push_cast
    field_simp
    ring
  rw [heq]
  have h1 : 2 * A / e ≤ 2 * A / ρ := div_le_div_of_nonneg_left (by positivity) hρ hρe
  have hA2 : A ≤ A ^ 2 := by nlinarith
  have h3 : 2 * A / ρ + 8 * K * A ^ 2 / ρ ≤ bridgeConst K A / ρ := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hρ.le
    unfold bridgeConst
    have h2 : 0 ≤ 4 * (3 * sobolevConst * K) ^ 2 * A ^ 8 := by positivity
    nlinarith
  linarith

/-- The composed amplitude is at most `A' ρ^{-6} N²`. -/
theorem amplitude_le_bridgeConst {K A ρ N : ℝ} (hK : 1 ≤ K) (hA : 1 ≤ A) (hρ : 0 < ρ) :
    4 * (3 * sobolevConst * (A * N) * K * (A / ρ) ^ 3) ^ 2 ≤
      bridgeConst K A * ρ ^ (-6 : ℤ) * N ^ 2 := by
  have hz : ρ ^ (-6 : ℤ) = (ρ ^ 6)⁻¹ := by
    rw [zpow_neg]; norm_cast
  have heq : 4 * (3 * sobolevConst * (A * N) * K * (A / ρ) ^ 3) ^ 2 =
      (4 * (3 * sobolevConst * K) ^ 2 * A ^ 8) * ρ ^ (-6 : ℤ) * N ^ 2 := by
    rw [hz]
    field_simp
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold bridgeConst
  have : 0 ≤ (2 + 8 * K) * A ^ 2 := by
    have : 0 ≤ K := by linarith
    positivity
  linarith

/-- Abstract-real combination of amplitude and radius bounds into the target shape. -/
theorem combine_bound {K A ρ N : ℝ} (hK : 1 ≤ K) (hA : 1 ≤ A) (hρ : 0 < ρ) {e : ℝ}
    (hρe : ρ ≤ e) (n : ℕ) :
    (4 * (3 * sobolevConst * (A * N) * K * (A / ρ) ^ 3) ^ 2) * n.factorial *
        ((2 * A / e) * (1 + ((2 : ℕ) : ℝ) * (K * e) * (2 * (A / ρ)))) ^ n ≤
      (bridgeConst K A * ρ ^ (-6 : ℤ) * N ^ 2) * n.factorial /
        (ρ / bridgeConst K A) ^ n := by
  have hA' : 1 ≤ bridgeConst K A := one_le_bridgeConst hK hA
  have hA'0 : 0 < bridgeConst K A := lt_of_lt_of_le one_pos hA'
  have hamp := amplitude_le_bridgeConst (N := N) hK hA hρ
  have hrad := radius_le_bridgeConst hK hA hρ hρe
  have hhe : 0 < e := lt_of_lt_of_le hρ hρe
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  have hR0 : 0 ≤ (2 * A / e) * (1 + ((2 : ℕ) : ℝ) * (K * e) * (2 * (A / ρ))) := by
    have : 0 < A := lt_of_lt_of_le one_pos hA
    positivity
  have hpow := pow_le_pow_left₀ hR0 hrad n
  have hdiv : (bridgeConst K A / ρ) ^ n = 1 / (ρ / bridgeConst K A) ^ n := by
    rw [one_div, ← inv_pow, inv_div]
  have hfac : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  have hC0 : 0 ≤ bridgeConst K A * ρ ^ (-6 : ℤ) * N ^ 2 := by positivity
  calc (4 * (3 * sobolevConst * (A * N) * K * (A / ρ) ^ 3) ^ 2) * n.factorial *
        ((2 * A / e) * (1 + ((2 : ℕ) : ℝ) * (K * e) * (2 * (A / ρ)))) ^ n
      ≤ (bridgeConst K A * ρ ^ (-6 : ℤ) * N ^ 2) * n.factorial * (bridgeConst K A / ρ) ^ n := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hamp hfac) hpow (by positivity)
        positivity
    _ = _ := by rw [hdiv]; ring

/-! ### Integration over the unit cell and the main theorem -/

/-- The half-open unit cell has volume at most one. -/
theorem volume_unitCell_le_one : (volume : Measure (Vec 2)) (Infra.Torus.unitCell 2) ≤ 1 := by
  have hsub : Infra.Torus.unitCell 2 ⊆ Set.Icc (0 : Vec 2) 1 := by
    intro x hx
    simp only [Infra.Torus.unitCell, Infra.Torus.unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
    refine ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩
  refine (measure_mono hsub).trans ?_
  rw [Real.volume_Icc_pi]
  simp

/-- A pointwise bound gives the same bound for the unit-cell average of the norm. -/
theorem integral_norm_unitCell_le {g : Vec 2 → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x, ‖g x‖ ≤ M) : (∫ x in Infra.Torus.unitCell 2, ‖g x‖) ≤ M := by
  have hfin : (volume : Measure (Vec 2)) (Infra.Torus.unitCell 2) < ⊤ :=
    lt_of_le_of_lt volume_unitCell_le_one ENNReal.one_lt_top
  have h1 := norm_setIntegral_le_of_norm_le_const (f := fun x => ‖g x‖) hfin
    (fun x _ => by simpa using h x)
  have h2 : (volume : Measure (Vec 2)).real (Infra.Torus.unitCell 2) ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top volume_unitCell_le_one
    simpa [Measure.real] using this
  calc (∫ x in Infra.Torus.unitCell 2, ‖g x‖)
      ≤ ‖∫ x in Infra.Torus.unitCell 2, ‖g x‖‖ := le_abs_self _
    _ ≤ M * (volume : Measure (Vec 2)).real (Infra.Torus.unitCell 2) := h1
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left h2 hM
    _ = M := mul_one M

theorem nonneg_l2NormSq (f : Vec 2 → ℝ) : 0 ≤ l2NormSq f :=
  setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun x => sq_nonneg (f x))

/-- If `θ₀ = 0` in `L²`, the gradient of every admissible `T(t)` vanishes. -/
theorem fderiv_eq_zero_of_amplitude_zero {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : IsZ2Periodic f) {a : ℝ} (ha : 1 ≤ a)
    (hreg : ∀ (n : ℕ) (i : Fin n → Fin 2),
      Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j)))) ≤
        0 * n.factorial * a ^ n) (v : Fin 2) (x : Vec 2) :
    fderiv ℝ f x (basisVec v) = 0 := by
  have h := abs_iteratedFDeriv_fderiv_le hf hp le_rfl ha hreg 0 (fun j => Fin.elim0 j) v x
  simp only [zero_mul, mul_zero, abs_nonpos_iff, iteratedFDeriv_zero_apply] at h
  exact h

/-- **Route A bridge**: `e.Tm.reg.upgrade` (all orders, `L²_x`), `H² ⊂ L∞`, `l.product`,
proposition 10528 and `e.flow.for.ergodic` give the composed `L¹` analyticity required by
`l.flow.averages`.  Amplitude `A' ρ^{-6} ‖θ₀‖²` (so `p = 6`), radius `ρ / A'`. -/
theorem hasCoordinateAnalyticL1Bounds_of_bounds (A : ℝ) (hA : 1 ≤ A) :
    ∃ A' : ℝ, 1 ≤ A' ∧ ∀ (θ₀ : Vec 2 → ℝ) (T : ℝ → Vec 2 → ℝ) (ρ e : ℝ) (X : Vec 2 → Vec 2),
      0 < ρ → ρ ≤ e → e ≤ 1 →
      TmRegUpgradeLinfL2 A ρ θ₀ T → FlowForErgodicBound A e X → ContDiff ℝ (⊤ : ℕ∞) X →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ContDiff ℝ (⊤ : ℕ∞) (T t) → IsZ2Periodic (T t) →
      ∀ i j : Fin 2,
        Infra.Ergodic.HasCoordinateAnalyticL1Bounds
          (fun y => ((spaceGrad (T t) (X y) i * spaceGrad (T t) (X y) j : ℝ) : ℂ))
          (A' * ρ ^ (-6 : ℤ) * l2NormSq θ₀) (ρ / A') := by
  obtain ⟨K, hK1, hK⟩ := exists_poly_le_two_pow
  refine ⟨bridgeConst K A, one_le_bridgeConst hK1 hA, ?_⟩
  intro θ₀ T ρ e X hρ hρe he1 hT hX hXs t ht hTs hTp i j i' n hn
  have hTs' : ContDiff ℝ ∞ (T t) := hTs
  have hXs' : ContDiff ℝ ∞ X := hXs
  have hreg := fun (m : ℕ) (w : Fin m → Fin 2) => hT m w t (Set.Ioo_subset_Icc_self ht)
  set N : ℝ := Real.sqrt (l2NormSq θ₀) with hNdef
  have hN2 : N ^ 2 = l2NormSq θ₀ := Real.sq_sqrt (nonneg_l2NormSq θ₀)
  have hA'1 := one_le_bridgeConst hK1 hA
  have hA'0 : 0 < bridgeConst K A := lt_of_lt_of_le one_pos hA'1
  have hM0 : 0 ≤ (bridgeConst K A * ρ ^ (-6 : ℤ) * l2NormSq θ₀) * n.factorial /
      (ρ / bridgeConst K A) ^ n := by
    have := nonneg_l2NormSq θ₀
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
  rcases (Real.sqrt_nonneg (l2NormSq θ₀)).eq_or_lt with hN0 | hNpos
  · -- degenerate case `θ₀ = 0`
    have hreg0 : ∀ (m : ℕ) (w : Fin m → Fin 2),
        Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ m (T t) x (fun j => basisVec (w j)))) ≤
          0 * m.factorial * (A / ρ) ^ m := by
      intro m w
      have := hreg m w
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
    have hreg' : ∀ (m : ℕ) (w : Fin m → Fin 2),
        Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ m (T t) x (fun j => basisVec (w j)))) ≤
          (A * N) * m.factorial * (A / ρ) ^ m := hreg
    have hpt := orderedPartial_comp_le hK1 hK hA hρ hρe he1 hNpos' hTs' hTp hreg' hX hXs' i j n x
      (fun _ => i')
    refine hpt.trans ?_
    have := combine_bound (N := N) hK1 hA hρ hρe n
    rwa [hN2] at this

end AVenhance.Infra.Section5.AnalyticBridge

end
