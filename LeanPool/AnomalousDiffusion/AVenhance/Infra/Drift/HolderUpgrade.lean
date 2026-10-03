/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsContinuousIntoHolder

/-!
# Lowering the Hölder exponent of a drift

If `b` lies in `IsHolderClass a` and `0 < α < a`, then `b` lies in `IsHolderClass α`, and
`t ↦ b(t,·)` is continuous into the spatial `C^{0,α}` seminorm. The second statement is the
interpolation `min(A, B) ≤ A^{1-θ} B^θ` with `θ = α / a`, applied to the two bounds
`|g(x) - g(y)| ≤ 2C|t - s|^a` and `|g(x) - g(y)| ≤ 2C'|x - y|^a` for `g = b(t,·) - b(s,·)`.
-/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Drift

/-- `min(P, Q) ≤ P^{1-θ} Q^θ` for `P, Q ≥ 0` and `θ ∈ [0,1]`. -/
theorem le_rpow_mul_rpow_of_le_of_le {z P Q θ : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hzP : z ≤ P) (hzQ : z ≤ Q) :
    z ≤ P ^ (1 - θ) * Q ^ θ := by
  rcases le_total P Q with hPQ | hQP
  · calc z ≤ P := hzP
      _ = P ^ (1 - θ) * P ^ θ := by
          rw [← Real.rpow_add' hP (by norm_num : (1 - θ) + θ ≠ 0)]; simp
      _ ≤ P ^ (1 - θ) * Q ^ θ := by
          gcongr
  · calc z ≤ Q := hzQ
      _ = Q ^ (1 - θ) * Q ^ θ := by
          rw [← Real.rpow_add' hQ (by norm_num : (1 - θ) + θ ≠ 0)]; simp
      _ ≤ P ^ (1 - θ) * Q ^ θ := by
          gcongr

/-- `(p u^a)^{1-θ} (q v^a)^θ = p^{1-θ} q^θ u^{a(1-θ)} v^{aθ}` for nonnegative `p, q, u, v`. -/
theorem rpow_interp_eq {p q u v a θ : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hu : 0 ≤ u)
    (hv : 0 ≤ v) :
    (p * u ^ a) ^ (1 - θ) * (q * v ^ a) ^ θ =
      p ^ (1 - θ) * q ^ θ * (u ^ (a * (1 - θ)) * v ^ (a * θ)) := by
  rw [Real.mul_rpow hp (Real.rpow_nonneg hu _), Real.mul_rpow hq (Real.rpow_nonneg hv _),
    ← Real.rpow_mul hu, ← Real.rpow_mul hv]
  ring

/-- On `[0,1]`, a larger exponent gives a smaller power. -/
theorem rpow_le_rpow_of_le_one {x α a : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hα : 0 ≤ α)
    (hαa : α ≤ a) : x ^ a ≤ x ^ α :=
  Real.rpow_le_rpow_of_exponent_ge' hx₀ hx₁ hα hαa

theorem abs_sub_le_one_of_mem_Icc {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : |s - t| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- Lowering the exponent of the drift class. -/
theorem isHolderClass_mono {a α : ℝ} {b : ℝ → Vec 2 → Vec 2} (hb : IsHolderClass a b)
    (hα : 0 < α) (hαa : α ≤ a) : IsHolderClass α b := by
  obtain ⟨hper, hcont, ⟨M, hM⟩, ⟨Cx, hCx⟩, ⟨Ct, hCt⟩⟩ := hb
  refine ⟨hper, hcont, ⟨M, hM⟩, ⟨max Cx 0 + 2 * max M 0, ?_⟩, ⟨max Ct 0, ?_⟩⟩
  · intro t ht x y
    have hd0 : 0 ≤ ‖x - y‖ := norm_nonneg _
    have hpowα : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg hd0 _
    rcases le_total ‖x - y‖ 1 with hd1 | hd1
    · have h1 := hCx t ht x y
      have h2 : ‖x - y‖ ^ a ≤ ‖x - y‖ ^ α := rpow_le_rpow_of_le_one hd0 hd1 hα.le hαa
      have h3 : Cx * ‖x - y‖ ^ a ≤ max Cx 0 * ‖x - y‖ ^ α :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hd0 _)).trans
          (mul_le_mul_of_nonneg_left h2 (le_max_right _ _))
      have hM0 : 0 ≤ 2 * max M 0 * ‖x - y‖ ^ α :=
        mul_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) hpowα
      calc ‖b t x - b t y‖ ≤ Cx * ‖x - y‖ ^ a := h1
        _ ≤ max Cx 0 * ‖x - y‖ ^ α := h3
        _ ≤ (max Cx 0 + 2 * max M 0) * ‖x - y‖ ^ α := by
            rw [add_mul]; exact le_add_of_nonneg_right hM0
    · have hone : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow hd1 hα.le
      have hxy : ‖b t x - b t y‖ ≤ 2 * max M 0 := by
        calc ‖b t x - b t y‖ ≤ ‖b t x‖ + ‖b t y‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (hM t ht x) (hM t ht y)
          _ ≤ 2 * max M 0 := by linarith [le_max_left M 0]
      have hM0 : 0 ≤ max M 0 := le_max_right _ _
      have hCx0 : 0 ≤ max Cx 0 := le_max_right _ _
      calc ‖b t x - b t y‖ ≤ 2 * max M 0 := hxy
        _ ≤ 2 * max M 0 * ‖x - y‖ ^ α := le_mul_of_one_le_right (by positivity) hone
        _ ≤ (max Cx 0 + 2 * max M 0) * ‖x - y‖ ^ α := by
            rw [add_mul]; exact le_add_of_nonneg_left (mul_nonneg hCx0 hpowα)
  · intro s hs t ht x
    have hd0 : 0 ≤ |s - t| := abs_nonneg _
    have h2 : |s - t| ^ a ≤ |s - t| ^ α :=
      rpow_le_rpow_of_le_one hd0 (abs_sub_le_one_of_mem_Icc hs ht) hα.le hαa
    calc ‖b s x - b t x‖ ≤ Ct * |s - t| ^ a := hCt s hs t ht x
      _ ≤ max Ct 0 * |s - t| ^ a :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hd0 _)
      _ ≤ max Ct 0 * |s - t| ^ α := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)

/-- A drift of class `IsHolderClass a` is continuous in time into the spatial `C^{0,α}`
seminorm for every `0 < α < a`. -/
theorem isContinuousIntoHolder_of_lt {a α : ℝ} {b : ℝ → Vec 2 → Vec 2}
    (hb : IsHolderClass a b) (hα : 0 < α) (hαa : α < a) : IsContinuousIntoHolder α b := by
  obtain ⟨-, -, -, ⟨Cx, hCx⟩, ⟨Ct, hCt⟩⟩ := hb
  have ha : 0 < a := hα.trans hαa
  set θ : ℝ := α / a with hθdef
  have hθ₀ : 0 ≤ θ := div_nonneg hα.le ha.le
  have hθ₁ : θ ≤ 1 := (div_le_one ha).2 hαa.le
  have haθ : a * θ = α := by rw [hθdef]; field_simp
  have hgap : 0 < a * (1 - θ) := by
    have : a * (1 - θ) = a - α := by rw [mul_sub, haθ, mul_one]
    rw [this]; linarith
  set p : ℝ := 2 * max Ct 0
  set q : ℝ := 2 * max Cx 0
  have hp : 0 ≤ p := by positivity
  have hq : 0 ≤ q := by positivity
  set K : ℝ := p ^ (1 - θ) * q ^ θ
  have hK : 0 ≤ K := mul_nonneg (Real.rpow_nonneg hp _) (Real.rpow_nonneg hq _)
  intro s hs ε hε
  set δ : ℝ := (ε / (K + 1)) ^ (1 / (a * (1 - θ)))
  have hεK : 0 < ε / (K + 1) := div_pos hε (by linarith)
  refine ⟨δ, Real.rpow_pos_of_pos hεK _, ?_⟩
  intro t ht hts x y
  have hd0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hτ0 : 0 ≤ |t - s| := abs_nonneg _
  -- the two bounds
  have hA : ‖(b t x - b s x) - (b t y - b s y)‖ ≤ p * |t - s| ^ a := by
    have h1 := hCt t ht s hs x
    have h2 := hCt t ht s hs y
    have hm : Ct * |t - s| ^ a ≤ max Ct 0 * |t - s| ^ a :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hτ0 _)
    calc ‖(b t x - b s x) - (b t y - b s y)‖ ≤ ‖b t x - b s x‖ + ‖b t y - b s y‖ :=
          norm_sub_le _ _
      _ ≤ p * |t - s| ^ a := by simp only [p]; linarith
  have hB : ‖(b t x - b s x) - (b t y - b s y)‖ ≤ q * ‖x - y‖ ^ a := by
    have h1 := hCx t ht x y
    have h2 := hCx s hs x y
    have hm : Cx * ‖x - y‖ ^ a ≤ max Cx 0 * ‖x - y‖ ^ a :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hd0 _)
    have heq : (b t x - b s x) - (b t y - b s y) = (b t x - b t y) - (b s x - b s y) := by
      abel
    calc ‖(b t x - b s x) - (b t y - b s y)‖ = ‖(b t x - b t y) - (b s x - b s y)‖ := by
          rw [heq]
      _ ≤ ‖b t x - b t y‖ + ‖b s x - b s y‖ := norm_sub_le _ _
      _ ≤ q * ‖x - y‖ ^ a := by simp only [q]; linarith
  have hint := le_rpow_mul_rpow_of_le_of_le (mul_nonneg hp (Real.rpow_nonneg hτ0 _))
    (mul_nonneg hq (Real.rpow_nonneg hd0 _)) hθ₀ hθ₁ hA hB
  rw [rpow_interp_eq hp hq hτ0 hd0, haθ] at hint
  -- the time factor is small
  have hsmall : |t - s| ^ (a * (1 - θ)) ≤ ε / (K + 1) := by
    have h1 : |t - s| ^ (a * (1 - θ)) ≤ δ ^ (a * (1 - θ)) :=
      Real.rpow_le_rpow hτ0 hts.le hgap.le
    have h2 : δ ^ (a * (1 - θ)) = ε / (K + 1) := by
      simp only [δ]
      rw [← Real.rpow_mul hεK.le, one_div, inv_mul_cancel₀ hgap.ne', Real.rpow_one]
    linarith
  have hKε : K * |t - s| ^ (a * (1 - θ)) ≤ ε := by
    calc K * |t - s| ^ (a * (1 - θ)) ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hsmall hK
      _ ≤ ε := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by linarith)]
          calc K * ε ≤ K * ε + ε := le_add_of_nonneg_right hε.le
            _ = ε * (K + 1) := by ring
  have hpowα : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg hd0 _
  calc ‖(b t x - b s x) - (b t y - b s y)‖
      ≤ K * (|t - s| ^ (a * (1 - θ)) * ‖x - y‖ ^ α) := hint
    _ = (K * |t - s| ^ (a * (1 - θ))) * ‖x - y‖ ^ α := by ring
    _ ≤ ε * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_right hKε hpowα

end AVenhance.Infra.Drift
