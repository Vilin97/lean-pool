/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.SubordinatedFar

/-!
# Subordinated Assembly

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
private lemma heatPotential_far_shell_profile_hF_1 :
    ∀ {F : ParabolicPoint → ℝ} {r γ θ₀ P : ℝ},
      (0 : ℝ) < r →
        let V : ℝ :=
          ENNReal.toReal
            ((volume : Set ParabolicPoint → ℝ≥0∞) (parabolicCylinder (0 : Vec3) (0 : ℝ) (1 : ℝ)));
        let BF : ℝ := V ^ ((1 : ℝ) - (1 : ℝ) / P) * (morreyNorm P θ₀ F).toReal;
        let a₀ : ℝ := (5 : ℝ) * ((1 : ℝ) - (1 : ℝ) / θ₀);
        a₀ = (3 : ℝ) + γ →
          (∀ (j : ℕ), (2 : ℝ) ^ ((↑j : ℝ) * (γ - (2 : ℝ))) ≤ (2 : ℝ) ^ ((↑j : ℝ) * (γ - (1 : ℝ)))) →
            ∀ (j : ℕ),
              (2 : ℝ) * r * ((900000 : ℝ) / ((2 : ℝ) ^ ((↑j : ℝ) + (4 : ℝ)) * r) ^ (4 : ℕ)) *
                    ((2 : ℝ) * ((2 : ℝ) ^ ((↑((↑j : ℤ) + (6 : ℤ)) : ℝ) + (1 : ℝ)) * r)) ^ a₀ =
                  (1800000 : ℝ) * (2 : ℝ) ^ ((8 : ℝ) * a₀ - (16 : ℝ)) *
                      (2 : ℝ) ^ ((↑j : ℝ) * (a₀ - (4 : ℝ))) *
                    r ^ (a₀ + (1 : ℝ) - (4 : ℝ)) →
                (2 : ℝ) * r *
                        ((2 : ℝ) * r *
                          ((10000000 : ℝ) / ((2 : ℝ) ^ ((↑j : ℝ) + (4 : ℝ)) * r) ^ (5 : ℕ))) *
                      ((2 : ℝ) * ((2 : ℝ) ^ ((↑((↑j : ℤ) + (6 : ℤ)) : ℝ) + (1 : ℝ)) * r)) ^ a₀ =
                    (40000000 : ℝ) * (2 : ℝ) ^ ((8 : ℝ) * a₀ - (20 : ℝ)) *
                        (2 : ℝ) ^ ((↑j : ℝ) * (a₀ - (5 : ℝ))) *
                      r ^ (a₀ + (2 : ℝ) - (5 : ℝ)) →
                  (2 : ℝ) * r *
                        ((900000 : ℝ) / ((2 : ℝ) ^ ((↑j : ℝ) + (4 : ℝ)) * r) ^ (4 : ℕ) +
                          (2 : ℝ) * r *
                            ((10000000 : ℝ) / ((2 : ℝ) ^ ((↑j : ℝ) + (4 : ℝ)) * r) ^ (5 : ℕ))) *
                      (((2 : ℝ) * ((2 : ℝ) ^ ((↑((↑j : ℤ) + (6 : ℤ)) : ℝ) + (1 : ℝ)) * r)) ^ a₀ *
                        BF) ≤
                    ((1800000 : ℝ) * (2 : ℝ) ^ ((8 : ℝ) * a₀ - (16 : ℝ)) +
                            (40000000 : ℝ) * (2 : ℝ) ^ ((8 : ℝ) * a₀ - (20 : ℝ))) *
                          BF *
                        (2 : ℝ) ^ ((↑j : ℝ) * (γ - (1 : ℝ))) *
                      r ^ γ
    := by
  intro F r γ θ₀ P hr V BF a₀ ha₀ hj j hFfirst hFsecond
  have hBF : 0 ≤ BF := by
    dsimp [BF]
    positivity
  have hbase :
      (1800000 * (2 : ℝ) ^ (8 * a₀ - 16) *
          (2 : ℝ) ^ ((j : ℝ) * (a₀ - 4)) * r ^ (a₀ + 1 - 4) +
        40000000 * (2 : ℝ) ^ (8 * a₀ - 20) *
          (2 : ℝ) ^ ((j : ℝ) * (a₀ - 5)) * r ^ (a₀ + 2 - 5)) ≤
      (1800000 * (2 : ℝ) ^ (8 * a₀ - 16) +
        40000000 * (2 : ℝ) ^ (8 * a₀ - 20)) *
        (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
    rw [ha₀]
    have hsecond :
        40000000 * (2 : ℝ) ^ (8 * (3 + γ) - 20) *
            (2 : ℝ) ^ ((j : ℝ) * (3 + γ - 5)) * r ^ (3 + γ + 2 - 5) ≤
          40000000 * (2 : ℝ) ^ (8 * (3 + γ) - 20) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
      calc
        _ = (40000000 * (2 : ℝ) ^ (8 * (3 + γ) - 20) * r ^ γ) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 2)) := by ring_nf
        _ ≤ (40000000 * (2 : ℝ) ^ (8 * (3 + γ) - 20) * r ^ γ) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) := by
          exact mul_le_mul_of_nonneg_left (hj j) (by positivity)
        _ = _ := by ring_nf
    calc
      _ ≤ (1800000 * (2 : ℝ) ^ (8 * (3 + γ) - 16) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ) +
          40000000 * (2 : ℝ) ^ (8 * (3 + γ) - 20) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
        apply add_le_add
        · apply le_of_eq
          ring_nf
        · exact hsecond
      _ = _ := by ring
  calc
    _ = (2 * r * (900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) *
        (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^ a₀ +
      2 * r * (2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5)) *
        (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^ a₀) * BF := by ring
    _ = ((1800000 * (2 : ℝ) ^ (8 * a₀ - 16) *
          (2 : ℝ) ^ ((j : ℝ) * (a₀ - 4)) * r ^ (a₀ + 1 - 4)) +
        (40000000 * (2 : ℝ) ^ (8 * a₀ - 20) *
          (2 : ℝ) ^ ((j : ℝ) * (a₀ - 5)) * r ^ (a₀ + 2 - 5))) * BF := by
      rw [hFfirst, hFsecond]
    _ ≤ _ := by
      exact (mul_le_mul_of_nonneg_right hbase hBF).trans_eq (by ring)

private lemma heatPotential_far_shell_profile_hG_2 :
    ∀ {G : Fin (3 : ℕ) → ParabolicPoint → ℝ} {r γ θ₁ P : ℝ},
      (0 : ℝ) < r →
        let V : ℝ :=
          ENNReal.toReal
            ((volume : Set ParabolicPoint → ℝ≥0∞) (parabolicCylinder (0 : Vec3) (0 : ℝ) (1 : ℝ)));
        let BG : Fin (3 : ℕ) → ℝ := fun (i : Fin (3 : ℕ)) =>
          V ^ ((1 : ℝ) - (1 : ℝ) / P) * (morreyNorm P θ₁ (G i)).toReal;
        let a₁ : ℝ := (5 : ℝ) * ((1 : ℝ) - (1 : ℝ) / θ₁);
        a₁ = (4 : ℝ) + γ →
          (∀ (j : ℕ), (2 : ℝ) ^ ((↑j : ℝ) * (γ - (2 : ℝ))) ≤ (2 : ℝ) ^ ((↑j : ℝ) * (γ - (1 : ℝ)))) →
            ∀ (j : ℕ),
              (∀ (_ : Fin (3 : ℕ)),
                  (2 : ℝ) * r * ((60000000 : ℝ) / ((2 : ℝ) ^ ((↑j : ℝ) + (4 : ℝ)) * r) ^ (5 : ℕ)) *
                      ((2 : ℝ) * ((2 : ℝ) ^ ((↑((↑j : ℤ) + (6 : ℤ)) : ℝ) + (1 : ℝ)) * r)) ^ a₁ =
                    (120000000 : ℝ) * (2 : ℝ) ^ ((8 : ℝ) * a₁ - (20 : ℝ)) *
                        (2 : ℝ) ^ ((↑j : ℝ) * (a₁ - (5 : ℝ))) *
                      r ^ (a₁ + (1 : ℝ) - (5 : ℝ))) →
                (∀ (_ : Fin (3 : ℕ)),
                    (2 : ℝ) * r *
                          ((2 : ℝ) * r *
                            ((30000000000 : ℝ) / ((2 : ℝ) ^ ((↑j : ℝ) + (4 : ℝ)) * r) ^ (6 : ℕ))) *
                        ((2 : ℝ) * ((2 : ℝ) ^ ((↑((↑j : ℤ) + (6 : ℤ)) : ℝ) + (1 : ℝ)) * r)) ^ a₁ =
                      (120000000000 : ℝ) * (2 : ℝ) ^ ((8 : ℝ) * a₁ - (24 : ℝ)) *
                          (2 : ℝ) ^ ((↑j : ℝ) * (a₁ - (6 : ℝ))) *
                        r ^ (a₁ + (2 : ℝ) - (6 : ℝ))) →
                  ∀ (i : Fin (3 : ℕ)),
                    (2 : ℝ) * r *
                          ((60000000 : ℝ) / ((2 : ℝ) ^ ((↑j : ℝ) + (4 : ℝ)) * r) ^ (5 : ℕ) +
                            (2 : ℝ) * r *
                              ((30000000000 : ℝ) /
                                ((2 : ℝ) ^ ((↑j : ℝ) + (4 : ℝ)) * r) ^ (6 : ℕ))) *
                        (((2 : ℝ) * ((2 : ℝ) ^ ((↑((↑j : ℤ) + (6 : ℤ)) : ℝ) + (1 : ℝ)) * r)) ^ a₁ *
                          BG i) ≤
                      ((120000000 : ℝ) * (2 : ℝ) ^ ((8 : ℝ) * a₁ - (20 : ℝ)) +
                              (120000000000 : ℝ) * (2 : ℝ) ^ ((8 : ℝ) * a₁ - (24 : ℝ))) *
                            BG i *
                          (2 : ℝ) ^ ((↑j : ℝ) * (γ - (1 : ℝ))) *
                        r ^ γ
    := by
  intro G r γ θ₁ P hr V BG a₁ ha₁ hj j hGfirst hGsecond i
  have hBG : 0 ≤ BG i := by
    dsimp [BG]
    positivity
  have hbase :
      (120000000 * (2 : ℝ) ^ (8 * a₁ - 20) *
          (2 : ℝ) ^ ((j : ℝ) * (a₁ - 5)) * r ^ (a₁ + 1 - 5) +
        120000000000 * (2 : ℝ) ^ (8 * a₁ - 24) *
          (2 : ℝ) ^ ((j : ℝ) * (a₁ - 6)) * r ^ (a₁ + 2 - 6)) ≤
      (120000000 * (2 : ℝ) ^ (8 * a₁ - 20) +
        120000000000 * (2 : ℝ) ^ (8 * a₁ - 24)) *
        (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
    rw [ha₁]
    have hsecond :
        120000000000 * (2 : ℝ) ^ (8 * (4 + γ) - 24) *
            (2 : ℝ) ^ ((j : ℝ) * (4 + γ - 6)) * r ^ (4 + γ + 2 - 6) ≤
          120000000000 * (2 : ℝ) ^ (8 * (4 + γ) - 24) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
      calc
        _ = (120000000000 * (2 : ℝ) ^ (8 * (4 + γ) - 24) * r ^ γ) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 2)) := by ring_nf
        _ ≤ (120000000000 * (2 : ℝ) ^ (8 * (4 + γ) - 24) * r ^ γ) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) := by
          exact mul_le_mul_of_nonneg_left (hj j) (by positivity)
        _ = _ := by ring
    calc
      _ ≤ (120000000 * (2 : ℝ) ^ (8 * (4 + γ) - 20) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ) +
          120000000000 * (2 : ℝ) ^ (8 * (4 + γ) - 24) *
            (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
        apply add_le_add
        · apply le_of_eq
          ring_nf
        · exact hsecond
      _ = _ := by ring
  calc
    _ = (2 * r * (60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) *
        (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^ a₁ +
      2 * r * (2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6)) *
        (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^ a₁) * BG i := by ring
    _ = ((120000000 * (2 : ℝ) ^ (8 * a₁ - 20) *
          (2 : ℝ) ^ ((j : ℝ) * (a₁ - 5)) * r ^ (a₁ + 1 - 5)) +
        (120000000000 * (2 : ℝ) ^ (8 * a₁ - 24) *
          (2 : ℝ) ^ ((j : ℝ) * (a₁ - 6)) * r ^ (a₁ + 2 - 6))) * BG i := by
      rw [hGfirst i, hGsecond i]
    _ ≤ _ := by
      exact (mul_le_mul_of_nonneg_right hbase hBG).trans_eq (by ring)

lemma heatPotential_far_shell_profile_of_morrey
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {r γ θ₀ θ₁ P : ℝ}
    (hr : 0 < r) (_ : 0 < γ)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5)
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (_ : 1 ≤ P) (_ : P ≤ θ₀) (_ : P ≤ θ₁)
    (_ : morreyNorm P θ₀ F < ∞)
    (_ : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞) :
    let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
    let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
    let BG : Fin 3 → ℝ := fun i =>
      V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
    let A : ℕ → ℝ := fun j =>
      (2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
        2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5))) *
        ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
          (5 * (1 - 1 / θ₀)) * BF) +
      ∑ i, (2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
        2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6))) *
        ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
          (5 * (1 - 1 / θ₁)) * BG i)
    let C : ℝ :=
      (1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
        40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) * BF +
      ∑ i, (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
        120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) * BG i
    (∀ j : ℕ, 0 ≤ A j) ∧
      (∀ j : ℕ, A j ≤ C * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ) := by
  dsimp
  let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
  let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
  let BG : Fin 3 → ℝ := fun i =>
    V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
  let a₀ : ℝ := 5 * (1 - 1 / θ₀)
  let a₁ : ℝ := 5 * (1 - 1 / θ₁)
  let A : ℕ → ℝ := fun j =>
    (2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
      2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5))) *
      ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^ a₀ * BF) +
    ∑ i, (2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
      2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6))) *
      ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^ a₁ * BG i)
  let C : ℝ :=
    (1800000 * (2 : ℝ) ^ (8 * a₀ - 16) +
      40000000 * (2 : ℝ) ^ (8 * a₀ - 20)) * BF +
    ∑ i, (120000000 * (2 : ℝ) ^ (8 * a₁ - 20) +
      120000000000 * (2 : ℝ) ^ (8 * a₁ - 24)) * BG i
  have hA : ∀ j : ℕ, 0 ≤ A j := by
    intro j
    dsimp [A, BF, BG]
    positivity
  have ha₀ : a₀ = 3 + γ := by
    dsimp [a₀]
    rw [hθ₀]
    ring
  have ha₁ : a₁ = 4 + γ := by
    dsimp [a₁]
    rw [hθ₁]
    ring
  have hj : ∀ j : ℕ,
      (2 : ℝ) ^ ((j : ℝ) * (γ - 2)) ≤
        (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) := by
    intro j
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hj0 : 0 ≤ (j : ℝ) := by positivity
    nlinarith only [hj0]
  have hAj : ∀ j : ℕ,
      A j ≤ C * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
    intro j
    have hFfirst :
        2 * r * (900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) *
            (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^ a₀ =
          (1800000 * (2 : ℝ) ^ (8 * a₀ - 16) *
            (2 : ℝ) ^ ((j : ℝ) * (a₀ - 4)) * r ^ (a₀ + 1 - 4)) := by
      have hshift :
          (2 : ℝ) * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r) =
            2 * ((2 : ℝ) ^ ((j : ℝ) + 7) * r) := by
        have he : (((j + 6 : ℤ) : ℝ) + 1) = (j : ℝ) + 7 := by
          norm_num [Int.cast_add]
          ring
        rw [he]
      rw [hshift]
      convert (heatPotential_far_scale_first (a := a₀) (c := 900000)
        (m := 4) (j := j) hr) using 1; norm_num
    have hFsecond :
        2 * r * (2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5)) *
            (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^ a₀ =
          (40000000 * (2 : ℝ) ^ (8 * a₀ - 20) *
            (2 : ℝ) ^ ((j : ℝ) * (a₀ - 5)) * r ^ (a₀ + 2 - 5)) := by
      have hshift :
          (2 : ℝ) * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r) =
            2 * ((2 : ℝ) ^ ((j : ℝ) + 7) * r) := by
        have he : (((j + 6 : ℤ) : ℝ) + 1) = (j : ℝ) + 7 := by
          norm_num [Int.cast_add]
          ring
        rw [he]
      rw [hshift]
      convert (heatPotential_far_scale_second (a := a₀) (c := 10000000)
        (m := 5) (j := j) hr) using 1; norm_num
    have hGfirst (i : Fin 3) :
        2 * r * (60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) *
            (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^ a₁ =
          (120000000 * (2 : ℝ) ^ (8 * a₁ - 20) *
            (2 : ℝ) ^ ((j : ℝ) * (a₁ - 5)) * r ^ (a₁ + 1 - 5)) := by
      have hshift :
          (2 : ℝ) * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r) =
            2 * ((2 : ℝ) ^ ((j : ℝ) + 7) * r) := by
        have he : (((j + 6 : ℤ) : ℝ) + 1) = (j : ℝ) + 7 := by
          norm_num [Int.cast_add]
          ring
        rw [he]
      rw [hshift]
      convert (heatPotential_far_scale_first (a := a₁) (c := 60000000)
        (m := 5) (j := j) hr) using 1; norm_num
    have hGsecond (i : Fin 3) :
        2 * r * (2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6)) *
            (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^ a₁ =
          (120000000000 * (2 : ℝ) ^ (8 * a₁ - 24) *
            (2 : ℝ) ^ ((j : ℝ) * (a₁ - 6)) * r ^ (a₁ + 2 - 6)) := by
      have hshift :
          (2 : ℝ) * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r) =
            2 * ((2 : ℝ) ^ ((j : ℝ) + 7) * r) := by
        have he : (((j + 6 : ℤ) : ℝ) + 1) = (j : ℝ) + 7 := by
          norm_num [Int.cast_add]
          ring
        rw [he]
      rw [hshift]
      convert (heatPotential_far_scale_second (a := a₁) (c := 30000000000)
        (m := 6) (j := j) hr) using 1; norm_num
    have hF := @heatPotential_far_shell_profile_hF_1 F r γ θ₀ P hr ha₀ hj j hFfirst hFsecond
    have hG := @heatPotential_far_shell_profile_hG_2 G r γ θ₁ P hr ha₁ hj j hGfirst hGsecond
    dsimp [A, C]
    calc
      _ ≤ ((1800000 * (2 : ℝ) ^ (8 * a₀ - 16) +
          40000000 * (2 : ℝ) ^ (8 * a₀ - 20)) * BF) *
          (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ +
        ∑ i, ((120000000 * (2 : ℝ) ^ (8 * a₁ - 20) +
          120000000000 * (2 : ℝ) ^ (8 * a₁ - 24)) * BG i) *
          (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
        exact add_le_add hF
          (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hG i))
      _ = C * (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ := by
        dsimp [C]
        calc
          _ = ((1800000 * (2 : ℝ) ^ (8 * a₀ - 16) +
              40000000 * (2 : ℝ) ^ (8 * a₀ - 20)) * BF) *
              ((2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ) +
            ∑ i, ((120000000 * (2 : ℝ) ^ (8 * a₁ - 20) +
              120000000000 * (2 : ℝ) ^ (8 * a₁ - 24)) * BG i) *
              ((2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ) := by
            apply congrArg₂ (· + ·)
            · ring
            · apply Finset.sum_congr rfl
              intro i hi
              ring
          _ = ((1800000 * (2 : ℝ) ^ (8 * a₀ - 16) +
              40000000 * (2 : ℝ) ^ (8 * a₀ - 20)) * BF +
            ∑ i, (120000000 * (2 : ℝ) ^ (8 * a₁ - 20) +
              120000000000 * (2 : ℝ) ^ (8 * a₁ - 24)) * BG i) *
              ((2 : ℝ) ^ ((j : ℝ) * (γ - 1)) * r ^ γ) := by
            rw [add_mul, ← Finset.sum_mul]
            ring
          _ = _ := by ring
  exact ⟨hA, hAj⟩

lemma heatPotential_far_shell_value_bound_of_morrey
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {z p p' : ParabolicPoint} {r γ θ₀ θ₁ P : ℝ}
    (hr : 0 < r) (_ : 0 < γ)
    (_ : 1 / θ₀ = (2 - γ) / 5)
    (_ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : AEMeasurable F volume) (hG : ∀ i : Fin 3, AEMeasurable (G i) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
    let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
    let BG : Fin 3 → ℝ := fun i =>
      V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
    let A : ℕ → ℝ := fun j =>
      (2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
        2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5))) *
        ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
          (5 * (1 - 1 / θ₀)) * BF) +
      ∑ i, (2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
        2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6))) *
        ((2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
          (5 * (1 - 1 / θ₁)) * BG i)
    ∀ j : ℕ,
      |heatPotentialShellValue F G (heatPotentialFarShellSet z r j) p -
          heatPotentialShellValue F G (heatPotentialFarShellSet z r j) p'| ≤ A j := by
  dsimp
  intro j
  have h := heatPotential_far_shell_oscillation_bound_of_morrey
    (z := z) (p := p) (p' := p') (r := r) (P := P)
    (θ₀ := θ₀) (θ₁ := θ₁) (j := j) hr hP hPθ₀ hPθ₁ hF hG hNF hNG hp hp'
  have hFfactor := heatPotential_far_shell_source_factor_toReal
    (r := r) (P := P) (θ := θ₀) hr hF hNF j
  have hGfactor : ∀ i : Fin 3,
      ((ENNReal.ofReal
          (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r))) ^
          (5 * (1 - 1 / θ₁)) *
        (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
          morreyNorm P θ₁ (G i)).toReal =
        (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
          (5 * (1 - 1 / θ₁)) *
        (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
          (morreyNorm P θ₁ (G i)).toReal := by
    intro i
    exact heatPotential_far_shell_source_factor_toReal
      (r := r) (P := P) (θ := θ₁) hr (hG i) (hNG i) j
  rw [hFfactor] at h
  simp_rw [hGfactor] at h
  convert h using 1; ring_nf


lemma heatPotential_series_difference_bound
    {h : ParabolicPoint → ℝ} {s : ℕ → ParabolicPoint → ℝ}
    {p p' : ParabolicPoint} {Anear : ℝ} {A : ℕ → ℝ}
    {n : ParabolicPoint → ℝ}
    (hsplitp : h p = n p + ∑' j : ℕ, s j p)
    (hsplitp' : h p' = n p' + ∑' j : ℕ, s j p')
    (hsump : Summable (fun j : ℕ => s j p))
    (hsump' : Summable (fun j : ℕ => s j p'))
    (hnear : |n p - n p'| ≤ Anear)
    (hAsum : Summable A)
    (hfar : ∀ j : ℕ, |s j p - s j p'| ≤ A j) :
    |h p - h p'| ≤ Anear + ∑' j : ℕ, A j := by
  let sp : ℕ → ℝ := fun j => s j p
  let sp' : ℕ → ℝ := fun j => s j p'
  have hdiffnorm : ∀ j : ℕ, ‖sp j - sp' j‖ ≤ A j := by
    intro j
    rw [Real.norm_eq_abs]
    simpa only [sp, sp'] using hfar j
  have hdiffsum : Summable (fun j : ℕ => sp j - sp' j) := by
    exact Summable.of_norm_bounded hAsum hdiffnorm
  have htsum : (∑' j : ℕ, sp j) - ∑' j : ℕ, sp' j =
      ∑' j : ℕ, (sp j - sp' j) := by
    symm
    exact hsump.tsum_sub hsump'
  have hdiff_le : |∑' j : ℕ, (sp j - sp' j)| ≤ ∑' j : ℕ, A j := by
    calc
      |∑' j : ℕ, (sp j - sp' j)| ≤ ∑' j : ℕ, |sp j - sp' j| := by
        change ‖∑' j : ℕ, (sp j - sp' j)‖ ≤
          ∑' j : ℕ, ‖sp j - sp' j‖
        exact norm_tsum_le_tsum_norm hdiffsum.norm
      _ ≤ ∑' j : ℕ, A j := hdiffsum.norm.tsum_le_tsum hdiffnorm hAsum
  calc
    |h p - h p'| =
        |(n p - n p') +
          ((∑' j : ℕ, sp j) - ∑' j : ℕ, sp' j)| := by
      rw [hsplitp, hsplitp']
      congr 1
      ring
    _ = |(n p - n p') +
          ∑' j : ℕ, (sp j - sp' j)| := by rw [htsum]
    _ ≤ |n p - n p'| +
        |∑' j : ℕ, (sp j - sp' j)| := abs_add_le _ _
    _ ≤ Anear + ∑' j : ℕ, A j := add_le_add hnear hdiff_le


end CKN.Core.HeatPotential
