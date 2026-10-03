/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.BoundedParabolicUniqueness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ChiMKCorrector
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.IsCorrectorSol

/-! Proof of the Section 3 corrector existence and uniqueness statement. -/

@[expose] public section

noncomputable section

namespace AVenhance.Proofs.Ingredients

open MeasureTheory Homogenization
open AVenhance.Infra.Section3
open AVenhance

theorem chiMK_isUniqueSolution {β : ℝ} (I : AVenhance.Ingredients β)
    (κ : ℝ) (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) (k : ℤ) (j : Fin 2) :
    let sol : ℝ → Vec 2 → ℝ := fun t x => I.chiMK κ m k t x j
    (ContDiff ℝ 2 (fun p : ℝ × Vec 2 => sol p.1 p.2) ∧
      (∃ B : ℝ, ∀ t x, |sol t x| ≤ B) ∧
        I.IsCorrectorSol κ m k (basisVec j) sol) ∧
      ∀ χ : ℝ → Vec 2 → ℝ,
        ContDiff ℝ 2 (fun p : ℝ × Vec 2 => χ p.1 p.2) →
        (∃ B : ℝ, ∀ t x, |χ t x| ≤ B) →
        I.IsCorrectorSol κ m k (basisVec j) χ → χ = sol := by
  let sol : ℝ → Vec 2 → ℝ := fun t x => I.chiMK κ m k t x j
  have hsol := AVenhance.Infra.Section3.chiMK_component_isBoundedCorrectorSol
    I hm κ hκ k j
  refine ⟨?_, ?_⟩
  · simpa [sol] using hsol
  · intro χ hχC hχBound hχSol
    obtain ⟨Bχ, hχBound⟩ := hχBound
    let Bsol : ℝ :=
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ *
        |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m|
    have hsolBound (t : ℝ) (x : Vec 2) : |sol t x| ≤ Bsol := by
      simpa [sol, Bsol] using
        AVenhance.Infra.Section3.chiMK_component_abs_le I hm κ hκ k t x j
    have hBχnonneg : 0 ≤ Bχ :=
      le_trans (abs_nonneg (χ 0 0)) (hχBound 0 0)
    have hBsolnonneg : 0 ≤ Bsol := by
      dsimp [Bsol]
      positivity
    let M : ℝ := Bχ + Bsol
    have hM : 0 ≤ M := by dsimp [M]; positivity
    let w : ℝ → Vec 2 → ℝ := fun t x => χ t x - sol t x
    have hwBound : ∀ t x, |w t x| ≤ M := by
      intro t x
      calc
        |w t x| = |χ t x - sol t x| := rfl
        _ = |χ t x + (-(sol t x))| := rfl
        _ ≤ |χ t x| + |-(sol t x)| := abs_add_le _ _
        _ = |χ t x| + |sol t x| := by rw [abs_neg]
        _ ≤ M := by
          dsimp [M]
          exact add_le_add (hχBound t x) (hsolBound t x)
    have hsolC : ContDiff ℝ 2 (fun p : ℝ × Vec 2 => sol p.1 p.2) := by
      simpa [sol] using AVenhance.Infra.Section3.chiMK_component_contDiff_two
        I κ k j
    have hwC : ContDiff ℝ 2 (fun p : ℝ × Vec 2 => w p.1 p.2) := by
      dsimp [w]
      exact hχC.sub hsolC
    have hsolCorrect : I.IsCorrectorSol κ m k (basisVec j) sol := by
      simpa [sol] using
        AVenhance.Infra.Section3.chiMK_isCorrectorSol I κ m k j
    let b : ℝ → Vec 2 → Fin 2 → ℝ := fun t x i =>
      I.zetaProd m k t * uShear β I.Λ m k x i
    have hbBound : ∀ t x i,
        |b t x i| ≤ |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m| := by
      intro t x i
      change |I.zetaProd m k t * uShear β I.Λ m k x i| ≤ _
      rw [abs_mul]
      have hz := AVenhance.Infra.Section3.zetaProd_mem_Icc I hm k t
      have hza : |I.zetaProd m k t| ≤ 1 := by
        rw [abs_of_nonneg hz.1]
        exact hz.2
      have hu := AVenhance.Infra.Section3.uShear_component_abs_le
        (β := β) (Λ := I.Λ) (m := m) k x i
      calc
        |I.zetaProd m k t| * |uShear β I.Λ m k x i| ≤
            |I.zetaProd m k t| *
              |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m| :=
          mul_le_mul_of_nonneg_left hu (abs_nonneg _)
        _ ≤ 1 * |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m| :=
          mul_le_mul_of_nonneg_right hza (abs_nonneg _)
        _ = |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m| := one_mul _
    have hzero : ∀ t, t < (-(2 / 3) + (k : ℝ)) * tau β I.Λ m →
        ∀ x, w t x = 0 := by
      intro t ht x
      have hχ0 := hχSol.2 t x ht
      have hsol0 := hsolCorrect.2 t x ht
      dsimp [w]
      rw [hχ0, hsol0]
      simp
    have hPDE : ∀ t x,
        deriv (fun s => w s x) t =
          κ * spaceLap (w t) x -
            ∑ i : Fin 2, b t x i * spaceGrad (w t) x i := by
      intro t x
      have hχSpace : ContDiff ℝ 2 (fun y : Vec 2 => χ t y) :=
        hχC.comp (contDiff_const.prodMk contDiff_id)
      have hsolSpace : ContDiff ℝ 2 (fun y : Vec 2 => sol t y) :=
        hsolC.comp (contDiff_const.prodMk contDiff_id)
      have hLap := spaceLap_sub hχSpace hsolSpace (x := x)
      have hGrad (i : Fin 2) :=
        spaceGrad_sub i
          (hχSpace.differentiable (by norm_num) x)
          (hsolSpace.differentiable (by norm_num) x)
      have hχderiv := (hχSol.1 t x).deriv
      have hsolderiv := (hsolCorrect.1 t x).deriv
      have hsubderiv : deriv (fun s => w s x) t =
          deriv (fun s => χ s x) t - deriv (fun s => sol s x) t := by
        change deriv (fun s : ℝ => χ s x - sol s x) t = _
        exact deriv_fun_sub
          ((hχSol.1 t x).differentiableAt)
          ((hsolCorrect.1 t x).differentiableAt)
      rw [hsubderiv, hχderiv, hsolderiv, hLap]
      simp only [Fin.sum_univ_two]
      rw [hGrad 0, hGrad 1]
      simp only [b]
      ring
    have hwzero := AVenhance.Infra.Section3.boundedParabolic_eq_zero
      (κ := κ) (D := |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m|)
      (M := M) (t₀ := (-(2 / 3) + (k : ℝ)) * tau β I.Λ m)
      (u := w) (b := b) hκ hM hwBound hbBound hwC hzero hPDE
    funext t
    funext x
    have hz := hwzero t x
    dsimp [w] at hz
    exact sub_eq_zero.mp hz

end AVenhance.Proofs.Ingredients
