/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.NoSelectionInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionInputs.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitSeries
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamRegularity

/-! # `VelGradContract`: the gradient of the stream drift is `O(ε_m^{β-2})`

`∂_j (streamVel (Φ_m))_i = ± ∂_j ∂_{i'} Φ_m`, and `Φ_m = ∑_{k ≤ m}` increments, whose second
derivatives are `≲ ε_k^{β-2}` (stream-regularity estimates).  The scales `ε_k^{β-2}` grow
    geometrically with ratio at
least `128^{2-β}`, so the sum is `≲ ε_m^{β-2}`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSelectionInputs

open AVenhance AVenhance.Infra.Construction

/-- Second derivative `∂_j ∂_i f`. -/
def hess2 (f : Vec 2 → ℝ) (i j : Fin 2) (x : Vec 2) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ f y (basisVec i)) x (basisVec j)

theorem hess2_add {f g : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 2) (x : Vec 2) : hess2 (f + g) i j x = hess2 f i j x + hess2 g i j x := by
  have e : (fun y => fderiv ℝ (f + g) y (basisVec i)) =
      fun y => fderiv ℝ f y (basisVec i) + fderiv ℝ g y (basisVec i) := by
    funext y
    rw [fderiv_add (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
    rfl
  unfold hess2
  rw [e]
  rw [fderiv_fun_add ((smoothPartial hf _).differentiable (by simp) x)
    ((smoothPartial hg _).differentiable (by simp) x)]
  rfl

theorem hess2_eq_iterated {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 2) (x : Vec 2) :
    hess2 f i j x = iteratedFDeriv ℝ 2 f x (fun k => basisVec (if k = 0 then j else i)) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp)) x
  have hc : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec i) x := differentiableAt_const _
  have h := fderiv_clm_apply hdf hc
  unfold hess2
  rw [h]
  simp [iteratedFDeriv_two_apply]

theorem slice_contDiff {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (m : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) :=
  (streamSeq_isAdmissible hseq m).1.comp (contDiff_const.prodMk contDiff_id)

/-- Second derivative of an increment. -/
theorem hess2_increment_le {β C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (t : ℝ) (x : Vec 2) (i j : Fin 2) :
    |hess2 (Φ m t - Φ (m - 1) t) i j x| ≤ 2 ^ 16 * epsilon β I.Λ m ^ (β - 2) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (Φ m t - Φ (m - 1) t) :=
    (slice_contDiff hseq m t).sub (slice_contDiff hseq (m - 1) t)
  rw [hess2_eq_iterated hf]
  have := streamIncrement_secondCoordinate_le hseq hreg hm t x
    (fun k => if k = 0 then j else i)
  simpa [Real.norm_eq_abs] using this

/-- Abstract inversion step. -/
theorem inv_step {a b q : ℝ} (ha : 0 < a) (hb : 0 < b) (h : b ≤ a * q) : a⁻¹ ≤ q * b⁻¹ := by
  calc a⁻¹ = (a * b)⁻¹ * b := by field_simp
    _ ≤ (a * b)⁻¹ * (a * q) := by gcongr
    _ = q * b⁻¹ := by field_simp

theorem eps_neg_step {β : ℝ} (I : Ingredients β) (m : ℕ) :
    epsilon β I.Λ m ^ (β - 2) ≤
      (I.Λ : ℝ) ^ (-(2 - β)) * epsilon β I.Λ (m + 1) ^ (β - 2) := by
  have hs : 0 < 2 - β := by linarith [I.beta_lt]
  have h0 := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have h1 := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m + 1)
  have hstep := epsilon_rpow_step_le I hs m
  have e : β - 2 = -(2 - β) := by ring
  rw [e, Real.rpow_neg h0.le, Real.rpow_neg h1.le]
  exact inv_step (Real.rpow_pos_of_pos h0 _) (Real.rpow_pos_of_pos h1 _) hstep

/-- Partial sums of the Hessian. -/
theorem hess2_partial_le {β C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ) {c q : ℝ}
    (hq1 : q < 1) (hqΛ : (I.Λ : ℝ) ^ (-(2 - β)) ≤ q) (hc : 2 ^ 16 ≤ c * (1 - q))
    (t : ℝ) (x : Vec 2) (i j : Fin 2) (n : ℕ) :
    |hess2 (Φ n t) i j x| ≤ c * epsilon β I.Λ n ^ (β - 2) := by
  have hc0 : 0 ≤ c := by
    by_contra hneg
    replace hneg := not_le.1 hneg
    nlinarith [mul_neg_of_neg_of_pos hneg (sub_pos.2 hq1)]
  induction n with
  | zero =>
    have h0 : Φ 0 t = fun _ => 0 := by rw [hseq.1]
    have : hess2 (Φ 0 t) i j x = 0 := by
      rw [h0]; simp [hess2]
    rw [this]
    have := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := 0)
    simpa using mul_nonneg hc0 (Real.rpow_nonneg this.le (β - 2))
  | succ n ih =>
    have hinc := hess2_increment_le hseq hreg (m := n + 1) (by omega) t x i j
    simp only [Nat.add_sub_cancel] at hinc
    have hsplit : Φ (n + 1) t = Φ n t + (Φ (n + 1) t - Φ n t) := by abel
    have hadd : hess2 (Φ n t + (Φ (n + 1) t - Φ n t)) i j x =
        hess2 (Φ n t) i j x + hess2 (Φ (n + 1) t - Φ n t) i j x :=
      hess2_add (slice_contDiff hseq n t)
        ((slice_contDiff hseq (n + 1) t).sub (slice_contDiff hseq n t)) i j x
    rw [← hsplit] at hadd
    rw [hadd]
    have hstep := eps_neg_step I n
    have hp : 0 ≤ epsilon β I.Λ (n + 1) ^ (β - 2) :=
      Real.rpow_nonneg (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
        (m := n + 1)).le _
    calc |hess2 (Φ n t) i j x + hess2 (Φ (n + 1) t - Φ n t) i j x|
        ≤ |hess2 (Φ n t) i j x| + |hess2 (Φ (n + 1) t - Φ n t) i j x| := abs_add_le _ _
      _ ≤ c * epsilon β I.Λ n ^ (β - 2) + 2 ^ 16 * epsilon β I.Λ (n + 1) ^ (β - 2) :=
          add_le_add ih hinc
      _ ≤ c * (q * epsilon β I.Λ (n + 1) ^ (β - 2)) + 2 ^ 16 * epsilon β I.Λ (n + 1) ^ (β - 2) := by
          have : epsilon β I.Λ n ^ (β - 2) ≤ q * epsilon β I.Λ (n + 1) ^ (β - 2) :=
            hstep.trans (mul_le_mul_of_nonneg_right hqΛ hp)
          gcongr
      _ ≤ c * epsilon β I.Λ (n + 1) ^ (β - 2) := by
          have : (c * q + 2 ^ 16) * epsilon β I.Λ (n + 1) ^ (β - 2) ≤
              c * epsilon β I.Λ (n + 1) ^ (β - 2) := by
            gcongr
            linarith
          linarith

theorem abs_spaceGrad_streamVel_le {ψ : ℝ → Vec 2 → ℝ} (t : ℝ)
    {B : ℝ} (hB : ∀ a b : Fin 2, ∀ x, |hess2 (ψ t) a b x| ≤ B) (x : Vec 2) (i j : Fin 2) :
    |spaceGrad (fun y => streamVel ψ t y i) x j| ≤ B := by
  fin_cases i
  · have hfun : (fun y => streamVel ψ t y 0) = fun y => -(fderiv ℝ (ψ t) y (basisVec 1)) := by
      funext y
      simp [streamVel, spaceGrad, sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have : spaceGrad (fun y => streamVel ψ t y 0) x j = -hess2 (ψ t) 1 j x := by
      rw [hfun]
      simp only [spaceGrad, hess2]
      rw [fderiv_fun_neg]
      rfl
    change |spaceGrad (fun y => streamVel ψ t y 0) x j| ≤ B
    rw [this, abs_neg]
    exact hB _ _ _
  · have hfun : (fun y => streamVel ψ t y 1) = fun y => fderiv ℝ (ψ t) y (basisVec 0) := by
      funext y
      simp [streamVel, spaceGrad, sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have : spaceGrad (fun y => streamVel ψ t y 1) x j = hess2 (ψ t) 0 j x := by
      rw [hfun]
      rfl
    change |spaceGrad (fun y => streamVel ψ t y 1) x j| ≤ B
    rw [this]
    exact hB _ _ _

theorem velGrad (β C₀ : ℝ) : VelGradContract β C₀ := by
  by_cases hβ : β < 2
  swap
  · refine ⟨0, le_refl _, fun I => ?_⟩
    exact absurd (lt_trans I.beta_lt (by norm_num)) hβ
  have hs : 0 < 2 - β := by linarith
  set q₀ : ℝ := (128 : ℝ) ^ (-(2 - β)) with hq₀
  have hq₀1 : q₀ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < 1 - q₀ := by linarith
  obtain ⟨Ct, -, hCt⟩ := stream_regularity β
  refine ⟨2 ^ 16 / (1 - q₀), by positivity, ?_⟩
  intro I _ _ _ Φ hΦ m hm t _ x i j
  have hreg : StreamRegularityBounds Ct I Φ := fun m hm t => hCt I Φ hΦ m hm t
  have hΛ : (128 : ℝ) ≤ I.Λ := by exact_mod_cast I.two_pow_seven_le
  have hqle : (I.Λ : ℝ) ^ (-(2 - β)) ≤ q₀ := by
    rw [hq₀, Real.rpow_neg (by positivity), Real.rpow_neg (by norm_num)]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hΛ hs.le)
  have hq1 : (I.Λ : ℝ) ^ (-(2 - β)) < 1 := inverse_lambda_rpow_lt_one I hs
  have hc : (2 : ℝ) ^ 16 ≤ 2 ^ 16 / (1 - q₀) * (1 - (I.Λ : ℝ) ^ (-(2 - β))) := by
    have e : 2 ^ 16 / (1 - q₀) * (1 - q₀) = (2 : ℝ) ^ 16 := by field_simp
    have hc0 : 0 ≤ (2 : ℝ) ^ 16 / (1 - q₀) := by positivity
    calc (2 : ℝ) ^ 16 = 2 ^ 16 / (1 - q₀) * (1 - q₀) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hc0
  refine abs_spaceGrad_streamVel_le t (B := _) ?_ x i j
  intro a b y
  exact hess2_partial_le hΦ hreg (c := 2 ^ 16 / (1 - q₀)) (q := (I.Λ : ℝ) ^ (-(2 - β)))
    hq1 le_rfl hc t y a b m

end AVenhance.Infra.FullTheorem.NoSelectionInputs
