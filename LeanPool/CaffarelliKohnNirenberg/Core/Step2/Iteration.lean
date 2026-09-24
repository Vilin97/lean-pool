/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import LeanPool.CaffarelliKohnNirenberg.Core.Parameters
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Statements.Theta

/-!
# Iteration

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

private lemma iteration_radius_pos {κ r₅ : ℝ} (hκ : 0 < κ) (hr₅ : 0 < r₅)
    (n : ℕ) : 0 < κ ^ n * r₅ := by positivity

private lemma iteration_radius_le {κ r₅ : ℝ} (hκ : 0 < κ) (hκle : κ ≤ 1)
    (hr₅ : 0 < r₅) (n : ℕ) : κ ^ n * r₅ ≤ r₅ := by
  have hpow : κ ^ n ≤ 1 := by exact pow_le_one₀ hκ.le hκle
  simpa using mul_le_mul_of_nonneg_right hpow hr₅.le

private lemma iteration_young_eighth {a b : ℝ} :
    a * b ≤ (1 / 8 : ℝ) * a ^ 2 + 2 * b ^ 2 := by
  nlinarith only [sq_nonneg (a - 4 * b)]

private lemma iteration_lambda_decay
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) {z : ParabolicPoint}
    {κ r₅ : ℝ} (hκ : 0 < κ) (hκle : κ ≤ 1) (hr₅ : 0 < r₅)
    (hz : closure (parabolicCylinder z.1 z.2 r₅) ⊆ spaceTimeSet Ω I)
    (n : ℕ) :
    0 ≤ lambda q f z (κ ^ n * r₅) ∧
      lambda q f z (κ ^ n * r₅) ≤
        κ ^ ((n : ℝ) * stepSigma q) * lambda q f z r₅ := by
  have hρ : 0 < κ ^ n * r₅ := iteration_radius_pos hκ hr₅ n
  have hρr : κ ^ n * r₅ ≤ r₅ := iteration_radius_le hκ hκle hr₅ n
  have hmono := lambda_mono_radius_of_sws hsol z hρ hρr hz
  have hratio : (κ ^ n * r₅) / r₅ = κ ^ n := by
    field_simp
  have hpow : (κ ^ n) ^ stepSigma q = κ ^ ((n : ℝ) * stepSigma q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
  have hnonneg : 0 ≤ lambda q f z (κ ^ n * r₅) := by
    unfold lambda
    positivity
  refine ⟨hnonneg, ?_⟩
  rw [hratio, show (3 - 5 / q : ℝ) = stepSigma q by rfl, hpow] at hmono
  exact hmono

private lemma exists_iteration_index {κ r r₅ : ℝ}
    (hκ : 0 < κ) (hκlt : κ < 1)
    (hr : 0 < r) (hrr : r ≤ r₅) :
    ∃ n : ℕ, κ ^ (n + 1) * r₅ < r ∧ r ≤ κ ^ n * r₅ := by
  let p : ℕ → Prop := fun n => κ ^ (n + 1) * r₅ < r
  have hp_tendsto : Tendsto (fun n : ℕ => κ ^ n * r₅) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hκ.le hκlt).mul_const r₅
  have hp_eventually : ∀ᶠ n : ℕ in atTop, p n := by
    have h := (tendsto_order.1 hp_tendsto).2 r hr
    rcases (eventually_atTop.1 h) with ⟨N, hN⟩
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    exact hN (n + 1) (by omega)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hp_eventually)
  have hex : ∃ n, p n := ⟨N, hN N le_rfl⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · exact Nat.find_spec hex
  · by_cases hzero : Nat.find hex = 0
    · simpa [hzero] using hrr
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hnot : ¬p m := by
        apply Nat.find_min hex
        rw [hm]
        exact Nat.lt_succ_self m
      dsimp [p] at hnot ⊢
      rw [hm]
      exact le_of_not_gt hnot

/-! The paper proposition is exposed conditionally until the analytic one-step
estimate is available. -/

private lemma iteration_hraw_1 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {r₅ C₂₇ C₂₈ : ℝ},
      (0 : ℝ) < C₂₇ →
        (0 : ℝ) < C₂₈ →
          (0 : ℝ) < r₅ →
            closure (parabolicCylinder z.1 z.2 r₅) ⊆ spaceTimeSet Ω I →
              theta (iterationKappa C₂₇) u Du p z r₅ ≤ iterationEta C₂₇ →
                (∀ {w : ParabolicPoint} {ρ : ℝ},
                    (0 : ℝ) < ρ →
                      closure (parabolicCylinder w.1 w.2 ρ) ⊆ spaceTimeSet Ω I →
                        theta (iterationKappa C₂₇) u Du p w (iterationKappa C₂₇ * ρ) ≤
                            C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
                                    theta (iterationKappa C₂₇) u Du p w ρ +
                                  C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                                      (beta u Du w ρ ^ (1 / 2 : ℝ) + beta u Du w ρ) *
                                    theta (iterationKappa C₂₇) u Du p w ρ +
                                C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                                    theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                                  lambda q f w ρ ^ (1 / 2 : ℝ) +
                              C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f w ρ ∧
                          (theta (iterationKappa C₂₇) u Du p w ρ ≤ (1 : ℝ) →
                            theta (iterationKappa C₂₇) u Du p w (iterationKappa C₂₇ * ρ) ≤
                              C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
                                      theta (iterationKappa C₂₇) u Du p w ρ +
                                    (2 : ℝ) * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                                        theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                                      theta (iterationKappa C₂₇) u Du p w ρ +
                                  C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                                      theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                                    lambda q f w ρ ^ (1 / 2 : ℝ) +
                                C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f w ρ)) →
                  let κ : ℝ := iterationKappa C₂₇;
                  let η : ℝ := iterationEta C₂₇;
                  let _ : ℝ := iterationEpsilon;
                  let Λ₀ : ℝ := iterationLambda₀ C₂₇ C₂₈;
                  let C₂₉ : ℝ := iterationC₂₉ C₂₇ C₂₈;
                  let Θ : ℕ → ℝ := fun (n : ℕ) => theta κ u Du p z (κ ^ n * r₅);
                  let Lraw : ℕ → ℝ := fun (n : ℕ) => lambda q f z (κ ^ n * r₅);
                  (0 : ℝ) < κ →
                    κ ≤ (1 : ℝ) →
                      (0 : ℝ) < η →
                        η ≤ (1 : ℝ) →
                          (0 : ℝ) < C₂₉ →
                            C₂₉ * Λ₀ = η / (2 : ℝ) →
                              (∀ (n : ℕ), (0 : ℝ) ≤ Θ n) →
                                (∀ (n : ℕ),
                                    (0 : ℝ) ≤ Lraw n ∧
                                      Lraw n ≤ κ ^ ((↑n : ℝ) * stepSigma q) * Lraw (0 : ℕ)) →
                                  (∀ (n : ℕ), Lraw n ≤ Λ₀) → ∀ (n : ℕ), Θ n ≤ η
    := by
  intro Ω I q u Du p f z r₅ C₂₇ C₂₈ hC₂₇ hC₂₈ hr₅ hz hθ₅ hThetaDecay κ η ε Λ₀ C₂₉ Θ Lraw hκ hκle
    hη hηle hC₂₉ hΛ
    hθ_nonneg hLamDecay hLrawle n
  induction n with
  | zero => simpa [Θ] using hθ₅
  | succ n ih =>
      have hρ : 0 < κ ^ n * r₅ := iteration_radius_pos hκ hr₅ n
      have hρsub : closure (parabolicCylinder z.1 z.2 (κ ^ n * r₅)) ⊆
          spaceTimeSet Ω I := by
        exact (closure_parabolicCylinder_mono hρ.le
          (iteration_radius_le hκ hκle hr₅ n)).trans hz
      have hsmall := (hThetaDecay hρ hρsub).2 (ih.trans hηle)
      have hLamN : Lraw n ≤ Λ₀ := hLrawle n
      have hfirst : C₂₇ * κ ^ (2 / 3 : ℝ) * Θ n ≤ (1 / 8 : ℝ) * Θ n := by
        have hA := iterationKappa_prop₁ hC₂₇
        have hκpow : κ ^ (2 / 3 : ℝ) ≤ κ ^ (2 / 3 - ε) :=
          Real.rpow_le_rpow_of_exponent_ge hκ hκle
            (by norm_num [ε, iterationEpsilon])
        have hcoef : C₂₇ * κ ^ (2 / 3 : ℝ) ≤ (1 / 8 : ℝ) :=
          (mul_le_mul_of_nonneg_left hκpow hC₂₇.le).trans hA
        exact mul_le_mul_of_nonneg_right hcoef (hθ_nonneg n)
      have hsecond : 2 * C₂₇ * κ ^ (-5 : ℝ) * Θ n ^ (1 / 2 : ℝ) * Θ n ≤
          (1 / 8 : ℝ) * Θ n := by
        have hB := iterationKappa_prop₂ hC₂₇
        have hsqrt : Θ n ^ (1 / 2 : ℝ) ≤ η ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (hθ_nonneg n) ih (by norm_num)
        have hκpow : κ ^ (-5 : ℝ) ≤ κ ^ (-5 - ε) :=
          Real.rpow_le_rpow_of_exponent_ge hκ hκle
            (by norm_num [ε, iterationEpsilon])
        have hcoef : 2 * C₂₇ * κ ^ (-5 : ℝ) * Θ n ^ (1 / 2 : ℝ) ≤
            2 * C₂₇ * κ ^ (-5 - ε) * η ^ (1 / 2 : ℝ) := by
          calc
            2 * C₂₇ * κ ^ (-5 : ℝ) * Θ n ^ (1 / 2 : ℝ) ≤
                2 * C₂₇ * κ ^ (-5 : ℝ) * η ^ (1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_left hsqrt (by positivity)
            _ ≤ 2 * C₂₇ * κ ^ (-5 - ε) * η ^ (1 / 2 : ℝ) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hκpow (by positivity)) (by positivity)
        exact (mul_le_mul_of_nonneg_right hcoef (hθ_nonneg n)).trans
          (mul_le_mul_of_nonneg_right hB (hθ_nonneg n))
      have hyoung := iteration_young_eighth
        (a := Θ n ^ (1 / 2 : ℝ))
        (b := C₂₈ * κ ^ (-1 / 2 : ℝ) * Lraw n ^ (1 / 2 : ℝ))
      have hforce : C₂₈ * κ ^ (-1 / 2 : ℝ) * Θ n ^ (1 / 2 : ℝ) * Lraw n ^ (1 / 2 : ℝ)
          + C₂₈ * κ ^ (-3 : ℝ) * Lraw n ≤ (1 / 8 : ℝ) * Θ n + η / 2 := by
        have hκpow1 : κ ^ (-1 : ℝ) ≤ κ ^ (-1 - 2 * ε) := by
          exact Real.rpow_le_rpow_of_exponent_ge hκ hκle
            (by norm_num [ε, iterationEpsilon])
        have hκpow2 : κ ^ (-3 : ℝ) ≤ κ ^ (-3 - ε) := by
          exact Real.rpow_le_rpow_of_exponent_ge hκ hκle
            (by norm_num [ε, iterationEpsilon])
        have hsq : (Lraw n ^ (1 / 2 : ℝ)) ^ 2 = Lraw n := by
          rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (hLamDecay n).1]
        have hyoung' : C₂₈ * κ ^ (-1 / 2 : ℝ) * Θ n ^ (1 / 2 : ℝ) *
            Lraw n ^ (1 / 2 : ℝ) ≤
            (1 / 8 : ℝ) * Θ n + 2 * C₂₈ ^ 2 * κ ^ (-1 : ℝ) * Lraw n := by
          calc
            C₂₈ * κ ^ (-1 / 2 : ℝ) * Θ n ^ (1 / 2 : ℝ) * Lraw n ^ (1 / 2 : ℝ) =
                Θ n ^ (1 / 2 : ℝ) *
                  (C₂₈ * κ ^ (-1 / 2 : ℝ) * Lraw n ^ (1 / 2 : ℝ)) := by ring_nf
            _ ≤ (1 / 8 : ℝ) * (Θ n ^ (1 / 2 : ℝ)) ^ 2 +
                  2 * (C₂₈ * κ ^ (-1 / 2 : ℝ) * Lraw n ^ (1 / 2 : ℝ)) ^ 2 := hyoung
            _ = (1 / 8 : ℝ) * Θ n + 2 * C₂₈ ^ 2 * κ ^ (-1 : ℝ) * Lraw n := by
              have hThetaSq : (Θ n ^ (1 / 2 : ℝ)) ^ 2 = Θ n := by
                rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (hθ_nonneg n)]
              rw [hThetaSq]
              have hκhalf : (κ ^ (-1 / 2 : ℝ)) ^ 2 = κ ^ (-1 : ℝ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
                congr 1; ring_nf
              simp only [mul_pow, hsq, hκhalf]
              ring_nf
        have hlast : C₂₈ * κ ^ (-3 : ℝ) * Lraw n ≤
            C₂₈ * κ ^ (-3 - ε) * Lraw n := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hκpow2 hC₂₈.le) (hLamDecay n).1
        have hmid : 2 * C₂₈ ^ 2 * κ ^ (-1 : ℝ) * Lraw n +
            C₂₈ * κ ^ (-3 : ℝ) * Lraw n ≤
            2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε) * Lraw n +
              C₂₈ * κ ^ (-3 - ε) * Lraw n := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hκpow1 (by positivity)) (hLamDecay n).1)
            hlast
        have hC29eq : 2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε) * Lraw n +
            C₂₈ * κ ^ (-3 - ε) * Lraw n = C₂₉ * Lraw n := by
          rw [show C₂₉ = 2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε) +
            C₂₈ * κ ^ (-3 - ε) by rfl]
          ring_nf
        calc
          C₂₈ * κ ^ (-1 / 2 : ℝ) * Θ n ^ (1 / 2 : ℝ) * Lraw n ^ (1 / 2 : ℝ) +
              C₂₈ * κ ^ (-3 : ℝ) * Lraw n ≤
              (1 / 8 : ℝ) * Θ n + 2 * C₂₈ ^ 2 * κ ^ (-1 : ℝ) * Lraw n +
                C₂₈ * κ ^ (-3 : ℝ) * Lraw n := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hyoung' (C₂₈ * κ ^ (-3 : ℝ) * Lraw n)
          _ = (1 / 8 : ℝ) * Θ n +
              (2 * C₂₈ ^ 2 * κ ^ (-1 : ℝ) * Lraw n +
                C₂₈ * κ ^ (-3 : ℝ) * Lraw n) := by ring_nf
          _ ≤ (1 / 8 : ℝ) * Θ n +
              (2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε) * Lraw n +
                C₂₈ * κ ^ (-3 - ε) * Lraw n) :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hmid ((1 / 8 : ℝ) * Θ n)
          _ = (1 / 8 : ℝ) * Θ n + C₂₉ * Lraw n := by rw [hC29eq]
          _ ≤ (1 / 8 : ℝ) * Θ n + η / 2 := by
            simpa [add_comm] using add_le_add_left
              ((mul_le_mul_of_nonneg_left (hLrawle n) hC₂₉.le).trans_eq hΛ)
              ((1 / 8 : ℝ) * Θ n)
      have hnextTheta : Θ (n + 1) =
          theta κ u Du p z (κ * (κ ^ n * r₅)) := by
        dsimp [Θ]
        congr 1
        rw [pow_succ]
        ring_nf
      rw [hnextTheta]
      have hsmall' : Θ (n + 1) ≤
          C₂₇ * κ ^ (2 / 3 : ℝ) * Θ n +
            2 * C₂₇ * κ ^ (-5 : ℝ) * Θ n ^ (1 / 2 : ℝ) * Θ n +
            C₂₈ * κ ^ (-1 / 2 : ℝ) * Θ n ^ (1 / 2 : ℝ) * Lraw n ^ (1 / 2 : ℝ) +
            C₂₈ * κ ^ (-3 : ℝ) * Lraw n := by
        have harg : κ ^ (n + 1) * r₅ = κ * (κ ^ n * r₅) := by
          rw [pow_succ]
          ring_nf
        rw [show Θ (n + 1) = theta κ u Du p z (κ ^ (n + 1) * r₅) by rfl]
        rw [harg]
        simpa [Θ, κ] using hsmall
      have hsmall'' : theta κ u Du p z (κ * (κ ^ n * r₅)) ≤
          C₂₇ * κ ^ (2 / 3 : ℝ) * Θ n +
            2 * C₂₇ * κ ^ (-5 : ℝ) * Θ n ^ (1 / 2 : ℝ) * Θ n +
            C₂₈ * κ ^ (-1 / 2 : ℝ) * Θ n ^ (1 / 2 : ℝ) * Lraw n ^ (1 / 2 : ℝ) +
            C₂₈ * κ ^ (-3 : ℝ) * Lraw n := by
        rw [← hnextTheta]
        exact hsmall'
      nlinarith only [hsmall'', hfirst, hsecond, hforce, ih, hη]

private lemma iteration_hrec_2 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {r₅ C₂₇ C₂₈ : ℝ},
      (0 : ℝ) < r₅ →
        closure (parabolicCylinder z.1 z.2 r₅) ⊆ spaceTimeSet Ω I →
          (∀ {w : ParabolicPoint} {ρ : ℝ},
              (0 : ℝ) < ρ →
                closure (parabolicCylinder w.1 w.2 ρ) ⊆ spaceTimeSet Ω I →
                  theta (iterationKappa C₂₇) u Du p w (iterationKappa C₂₇ * ρ) ≤
                      C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
                              theta (iterationKappa C₂₇) u Du p w ρ +
                            C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                                (beta u Du w ρ ^ (1 / 2 : ℝ) + beta u Du w ρ) *
                              theta (iterationKappa C₂₇) u Du p w ρ +
                          C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                              theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                            lambda q f w ρ ^ (1 / 2 : ℝ) +
                        C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f w ρ ∧
                    (theta (iterationKappa C₂₇) u Du p w ρ ≤ (1 : ℝ) →
                      theta (iterationKappa C₂₇) u Du p w (iterationKappa C₂₇ * ρ) ≤
                        C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
                                theta (iterationKappa C₂₇) u Du p w ρ +
                              (2 : ℝ) * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                                  theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                                theta (iterationKappa C₂₇) u Du p w ρ +
                            C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                                theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                              lambda q f w ρ ^ (1 / 2 : ℝ) +
                          C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f w ρ)) →
            let κ : ℝ := iterationKappa C₂₇;
            let η : ℝ := iterationEta C₂₇;
            let ε : ℝ := iterationEpsilon;
            let Θ : ℕ → ℝ := fun (n : ℕ) => theta κ u Du p z (κ ^ n * r₅);
            let Lraw : ℕ → ℝ := fun (n : ℕ) => lambda q f z (κ ^ n * r₅);
            let L : ℕ → ℝ := fun (n : ℕ) => Lraw n / κ ^ ((↑n : ℝ) * ε);
            let T : ℕ → ℝ := fun (n : ℕ) => Θ n / κ ^ ((↑n : ℝ) * ε);
            (0 : ℝ) < κ →
              κ ≤ (1 : ℝ) →
                η ≤ (1 : ℝ) →
                  (∀ (n : ℕ), (0 : ℝ) ≤ L n) →
                    (∀ (n : ℕ), (0 : ℝ) ≤ T n) →
                      (∀ (n : ℕ), Θ n ≤ η) →
                        ∀ (n : ℕ),
                          T (n + (1 : ℕ)) ≤
                            C₂₇ * κ ^ ((2 / 3 : ℝ) - ε) * T n +
                                  (2 : ℝ) * C₂₇ * κ ^ ((-5 : ℝ) - ε) * Θ n ^ (1 / 2 : ℝ) * T n +
                                C₂₈ * κ ^ ((-1 / 2 : ℝ) - ε) * T n ^ (1 / 2 : ℝ) *
                                  L n ^ (1 / 2 : ℝ) +
                              C₂₈ * κ ^ ((-3 : ℝ) - ε) * L n
    := by
  intro Ω I q u Du p f z r₅ C₂₇ C₂₈ hr₅ hz hThetaDecay κ η ε Θ Lraw L T hκ hκle hηle hLnonneg
    hTnonneg hΘle n
  have hρ : 0 < κ ^ n * r₅ := iteration_radius_pos hκ hr₅ n
  have hρsub : closure (parabolicCylinder z.1 z.2 (κ ^ n * r₅)) ⊆
      spaceTimeSet Ω I := by
    exact (closure_parabolicCylinder_mono hρ.le
      (iteration_radius_le hκ hκle hr₅ n)).trans hz
  have hdec := (hThetaDecay hρ hρsub).2 ((hΘle n).trans hηle)
  have hscale : ∀ m, Θ m = T m * κ ^ ((m : ℝ) * ε) := by
    intro m
    dsimp [T]
    field_simp
  have hnext : κ ^ (n + 1) * r₅ = κ * (κ ^ n * r₅) := by
    rw [pow_succ]
    ring_nf
  have hpow : κ ^ (((n + 1 : ℕ) : ℝ) * ε) =
      κ ^ ((n : ℝ) * ε) * κ ^ ε := by
    rw [← Real.rpow_add hκ]
    congr 1
    push_cast
    ring_nf
  have hnextTheta : Θ (n + 1) = theta κ u Du p z (κ * (κ ^ n * r₅)) := by
    dsimp [Θ]
    rw [hnext]
  have hdec' : theta κ u Du p z (κ * (κ ^ n * r₅)) ≤
      C₂₇ * κ ^ (2 / 3 : ℝ) * Θ n +
        2 * C₂₇ * κ ^ (-5 : ℝ) * Θ n ^ (1 / 2 : ℝ) * Θ n +
        C₂₈ * κ ^ (-1 / 2 : ℝ) * Θ n ^ (1 / 2 : ℝ) * Lraw n ^ (1 / 2 : ℝ) +
        C₂₈ * κ ^ (-3 : ℝ) * Lraw n := by
    simpa [κ, Θ, Lraw] using hdec
  rw [show T (n + 1) = Θ (n + 1) /
    κ ^ (((n + 1 : ℕ) : ℝ) * ε) by rfl, hnextTheta]
  rw [hscale n] at hdec'
  have hLrawscale : Lraw n = L n * κ ^ ((n : ℝ) * ε) := by
    dsimp [L]
    field_simp
  rw [hLrawscale] at hdec'
  have hΘpow : (T n * κ ^ ((n : ℝ) * ε)) ^ (1 / 2 : ℝ) =
      T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2) := by
    rw [Real.mul_rpow (hTnonneg n) (Real.rpow_nonneg hκ.le _)]
    congr 1
    rw [← Real.rpow_mul hκ.le]
    ring_nf
  rw [hΘpow] at hdec'
  have hLpow : (L n * κ ^ ((n : ℝ) * ε)) ^ (1 / 2 : ℝ) =
      L n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2) := by
    rw [Real.mul_rpow (hLnonneg n) (Real.rpow_nonneg hκ.le _)]
    congr 1
    rw [← Real.rpow_mul hκ.le]
    ring_nf
  rw [hLpow] at hdec'
  have hdiv : 0 < κ ^ (((n + 1 : ℕ) : ℝ) * ε) := by positivity
  apply (div_le_iff₀ hdiv).2
  rw [hpow]
  have hThetaSqrt : Θ n ^ (1 / 2 : ℝ) =
      T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2) := by
    rw [hscale n, hΘpow]
  have hhalf : (κ ^ ((n : ℝ) * ε / 2)) ^ 2 =
      κ ^ ((n : ℝ) * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
    congr 1
    ring_nf
  have hhalf' : (κ ^ ((n : ℝ) * ε * (1 / 2 : ℝ))) ^ 2 =
      κ ^ ((n : ℝ) * ε) := by
    convert hhalf using 1; ring_nf
  have hkah : κ ^ ((n : ℝ) * ε / 2) *
      κ ^ ((n : ℝ) * ε / 2) = κ ^ ((n : ℝ) * ε) := by
    calc
      κ ^ ((n : ℝ) * ε / 2) * κ ^ ((n : ℝ) * ε / 2) =
          (κ ^ ((n : ℝ) * ε / 2)) ^ 2 := by ring_nf
      _ = κ ^ ((n : ℝ) * ε) := hhalf
  have hkah' : κ ^ ((n : ℝ) * ε * (1 / 2 : ℝ)) *
      κ ^ ((n : ℝ) * ε * (1 / 2 : ℝ)) = κ ^ ((n : ℝ) * ε) := by
    calc
      κ ^ ((n : ℝ) * ε * (1 / 2 : ℝ)) *
          κ ^ ((n : ℝ) * ε * (1 / 2 : ℝ)) =
          (κ ^ ((n : ℝ) * ε * (1 / 2 : ℝ))) ^ 2 := by ring_nf
      _ = κ ^ ((n : ℝ) * ε) := hhalf'
  have h₁ : κ ^ (2 / 3 - ε : ℝ) * κ ^ ε = κ ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hκ]
    congr 1
    ring_nf
  have h₂ : κ ^ (-5 - ε : ℝ) * κ ^ ε = κ ^ (-5 : ℝ) := by
    rw [← Real.rpow_add hκ]
    congr 1
    ring_nf
  have h₃ : κ ^ (-1 / 2 - ε : ℝ) * κ ^ ε = κ ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_add hκ]
    congr 1
    ring_nf
  have h₄ : κ ^ (-3 - ε : ℝ) * κ ^ ε = κ ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hκ]
    congr 1
    ring_nf
  have hdec'' : theta κ u Du p z (κ * (κ ^ n * r₅)) ≤
      C₂₇ * κ ^ (2 / 3 : ℝ) * (T n * κ ^ ((n : ℝ) * ε)) +
        2 * C₂₇ * κ ^ (-5 : ℝ) *
          (T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) *
            (T n * κ ^ ((n : ℝ) * ε)) +
        C₂₈ * κ ^ (-1 / 2 : ℝ) *
          (T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) *
            (L n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) +
        C₂₈ * κ ^ (-3 : ℝ) * (L n * κ ^ ((n : ℝ) * ε)) := by
    exact hdec'
  have hscaled :
      (C₂₇ * κ ^ (2 / 3 - ε : ℝ) * T n +
        2 * C₂₇ * κ ^ (-5 - ε : ℝ) * Θ n ^ (1 / 2 : ℝ) * T n +
        C₂₈ * κ ^ (-1 / 2 - ε : ℝ) * T n ^ (1 / 2 : ℝ) *
          L n ^ (1 / 2 : ℝ) +
        C₂₈ * κ ^ (-3 - ε : ℝ) * L n) *
          (κ ^ ((n : ℝ) * ε) * κ ^ ε) =
      C₂₇ * κ ^ (2 / 3 : ℝ) * (T n * κ ^ ((n : ℝ) * ε)) +
        2 * C₂₇ * κ ^ (-5 : ℝ) *
          (T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) *
            (T n * κ ^ ((n : ℝ) * ε)) +
        C₂₈ * κ ^ (-1 / 2 : ℝ) *
          (T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) *
            (L n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) +
        C₂₈ * κ ^ (-3 : ℝ) * (L n * κ ^ ((n : ℝ) * ε)) := by
    rw [hThetaSqrt]
    calc
      _ = (κ ^ (2 / 3 - ε : ℝ) * κ ^ ε) *
            (C₂₇ * T n * κ ^ ((n : ℝ) * ε)) +
          (κ ^ (-5 - ε : ℝ) * κ ^ ε) *
            (2 * C₂₇ * (T n ^ (1 / 2 : ℝ) *
              κ ^ ((n : ℝ) * ε / 2)) * T n * κ ^ ((n : ℝ) * ε)) +
          (κ ^ (-1 / 2 - ε : ℝ) * κ ^ ε) *
            (C₂₈ * T n ^ (1 / 2 : ℝ) * L n ^ (1 / 2 : ℝ) *
              κ ^ ((n : ℝ) * ε)) +
          (κ ^ (-3 - ε : ℝ) * κ ^ ε) *
            (C₂₈ * L n * κ ^ ((n : ℝ) * ε)) := by ring_nf
      _ = C₂₇ * κ ^ (2 / 3 : ℝ) *
            (T n * κ ^ ((n : ℝ) * ε)) +
          2 * C₂₇ * κ ^ (-5 : ℝ) *
            (T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) *
              (T n * κ ^ ((n : ℝ) * ε)) +
          C₂₈ * κ ^ (-1 / 2 : ℝ) *
            (T n ^ (1 / 2 : ℝ) * L n ^ (1 / 2 : ℝ) *
              κ ^ ((n : ℝ) * ε)) +
          C₂₈ * κ ^ (-3 : ℝ) *
            (L n * κ ^ ((n : ℝ) * ε)) := by
        rw [h₁, h₂, h₃, h₄]
        ring_nf
      _ = _ := by
        rw [show κ ^ ((n : ℝ) * ε) =
          κ ^ ((n : ℝ) * ε * (1 / 2 : ℝ)) *
            κ ^ ((n : ℝ) * ε * (1 / 2 : ℝ)) by exact hkah'.symm]
        ring_nf
  calc
    theta κ u Du p z (κ * (κ ^ n * r₅)) ≤
        C₂₇ * κ ^ (2 / 3 : ℝ) * (T n * κ ^ ((n : ℝ) * ε)) +
          2 * C₂₇ * κ ^ (-5 : ℝ) *
            (T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) *
              (T n * κ ^ ((n : ℝ) * ε)) +
          C₂₈ * κ ^ (-1 / 2 : ℝ) *
            (T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) *
              (L n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) +
          C₂₈ * κ ^ (-3 : ℝ) * (L n * κ ^ ((n : ℝ) * ε)) := hdec''
    _ = _ := hscaled.symm

/-- Conditional form of `prop:iteration`, consuming the two inequalities of
`lem:theta-decay` as its only additional analytic input. -/
theorem iteration_of_thetaDecay
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r₅ C₂₇ C₂₈ : ℝ}
    (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈) (hr₅ : 0 < r₅)
    (hz : closure (parabolicCylinder z.1 z.2 r₅) ⊆ spaceTimeSet Ω I)
    (hθ₅ : theta (iterationKappa C₂₇) u Du p z r₅ ≤ iterationEta C₂₇)
    (hLam₅ : lambda q f z r₅ ≤ iterationLambda₀ C₂₇ C₂₈)
    (hThetaDecay : ∀ {w : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
      closure (parabolicCylinder w.1 w.2 ρ) ⊆ spaceTimeSet Ω I →
      theta (iterationKappa C₂₇) u Du p w (iterationKappa C₂₇ * ρ) ≤
        C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) * theta (iterationKappa C₂₇) u Du p w ρ +
          C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
            (beta u Du w ρ ^ (1 / 2 : ℝ) + beta u Du w ρ) *
              theta (iterationKappa C₂₇) u Du p w ρ +
          C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
            theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
              lambda q f w ρ ^ (1 / 2 : ℝ) +
          C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f w ρ ∧
      (theta (iterationKappa C₂₇) u Du p w ρ ≤ 1 →
        theta (iterationKappa C₂₇) u Du p w (iterationKappa C₂₇ * ρ) ≤
          C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
              theta (iterationKappa C₂₇) u Du p w ρ +
            2 * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
              theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                theta (iterationKappa C₂₇) u Du p w ρ +
            C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
              theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                lambda q f w ρ ^ (1 / 2 : ℝ) +
            C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f w ρ)) :
    (∀ n : ℕ, theta (iterationKappa C₂₇) u Du p z
        (iterationKappa C₂₇ ^ n * r₅) ≤
      iterationEta C₂₇ * iterationKappa C₂₇ ^ ((n : ℝ) * iterationEpsilon)) ∧
    (∀ r : ℝ, 0 < r → r ≤ r₅ →
      theta (iterationKappa C₂₇) u Du p z r ≤
        iterationKappa C₂₇ ^ (-4 / 3 - iterationEpsilon) *
          iterationEta C₂₇ * r₅ ^ (-iterationEpsilon) * r ^ iterationEpsilon) := by
  let κ := iterationKappa C₂₇
  let η := iterationEta C₂₇
  let ε := iterationEpsilon
  let Λ₀ := iterationLambda₀ C₂₇ C₂₈
  let C₂₉ := iterationC₂₉ C₂₇ C₂₈
  let Θ : ℕ → ℝ := fun n => theta κ u Du p z (κ ^ n * r₅)
  let Lraw : ℕ → ℝ := fun n => lambda q f z (κ ^ n * r₅)
  let L : ℕ → ℝ := fun n => Lraw n / κ ^ ((n : ℝ) * ε)
  let T : ℕ → ℝ := fun n => Θ n / κ ^ ((n : ℝ) * ε)
  have hκ : 0 < κ := iterationKappa_pos hC₂₇
  have hκle : κ ≤ 1 := by linarith only [iterationKappa_le_half C₂₇]
  have hη : 0 < η := iterationEta_pos hC₂₇
  have hηle : η ≤ 1 := iterationEta_le_one C₂₇
  have hC₂₉ : 0 < C₂₉ := iterationC₂₉_pos hC₂₇ hC₂₈
  have hΛ : C₂₉ * Λ₀ = η / 2 := by
    exact iterationC₂₉_mul_Lambda₀ hC₂₇ hC₂₈
  have hσ : ε ≤ stepSigma q := by
    exact le_of_lt (by simpa [ε] using (iterationEpsilon_lt_stepSigma hsol.2.2.2.1))
  have hθ_nonneg : ∀ n, 0 ≤ Θ n := by
    intro n
    dsimp [Θ]
    unfold theta
    unfold alpha beta delta
    positivity
  have hLamDecay : ∀ n, 0 ≤ Lraw n ∧ Lraw n ≤
      κ ^ ((n : ℝ) * stepSigma q) * Lraw 0 := by
    intro n
    have h := iteration_lambda_decay hsol hκ hκle hr₅ hz n
    simpa [Lraw] using h
  have hLrawzero : 0 ≤ Lraw 0 := (hLamDecay 0).1
  have hLrawzeroΛ : Lraw 0 ≤ Λ₀ := by simpa [Lraw] using hLam₅
  have hL : ∀ n, L n ≤ Λ₀ := by
    intro n
    dsimp [L]
    exact force_normalized_bound hκ hκle hσ hLrawzero hLrawzeroΛ hLamDecay n
  have hLrawle : ∀ n, Lraw n ≤ Λ₀ := by
    intro n
    have hden : 0 < κ ^ ((n : ℝ) * ε) := by positivity
    have hdenle : κ ^ ((n : ℝ) * ε) ≤ 1 := by
      have heps : 0 ≤ ε := by norm_num [ε, iterationEpsilon]
      exact Real.rpow_le_one hκ.le hκle
        (mul_nonneg (Nat.cast_nonneg n) heps)
    have hmul := mul_le_mul_of_nonneg_right (hL n) hden.le
    calc
      Lraw n = L n * κ ^ ((n : ℝ) * ε) := by
        dsimp [L]
        field_simp
      _ ≤ Λ₀ * κ ^ ((n : ℝ) * ε) := hmul
      _ ≤ Λ₀ := by
        have hΛnonneg : 0 ≤ Λ₀ := hLrawzero.trans hLrawzeroΛ
        exact mul_le_of_le_one_right hΛnonneg hdenle
  have hLle : ∀ n, L n ≤ Λ₀ := hL
  have hLnonneg : ∀ n, 0 ≤ L n := by
    intro n
    dsimp [L]
    exact div_nonneg (hLamDecay n).1 (by positivity)
  have hraw := @iteration_hraw_1 Ω I q u Du p f z r₅ C₂₇ C₂₈ hC₂₇ hC₂₈ hr₅ hz hθ₅ hThetaDecay hκ
    hκle hη hηle hC₂₉ hΛ hθ_nonneg hLamDecay hLrawle
  have hTnonneg : ∀ n, 0 ≤ T n := by
    intro n
    dsimp [T]
    exact div_nonneg (hθ_nonneg n) (by positivity)
  have hTzero : T 0 ≤ η := by simpa [T, Θ] using hθ₅
  have hΘle : ∀ n, Θ n ≤ η := hraw
  have hrec := @iteration_hrec_2 Ω I q u Du p f z r₅ C₂₇ C₂₈ hr₅ hz hThetaDecay hκ hκle hηle
    hLnonneg hTnonneg hΘle
  have hTbound := iteration_normalized_bound (T := T) (L := L) (Θ := Θ)
    hκ hη (by linarith only [hC₂₇.le]) (by linarith only [hC₂₈.le])
    (iterationKappa_prop₁ hC₂₇) (iterationKappa_prop₂ hC₂₇)
    (by rfl) hC₂₉.le (by rw [hΛ]) hTzero hTnonneg
    (fun n => hθ_nonneg n) hΘle
      hLnonneg hLle hrec
  constructor
  · intro n
    have hdisc := theta_iteration_bound (θ := Θ) (T := T) (κ := κ)
      (ε := ε) (η := η) hκ (fun m => by
        dsimp [T]
        field_simp) hTbound n
    simpa [Θ, κ, η, ε] using hdisc
  · intro r hr hrr
    have hκlt : κ < 1 := lt_of_le_of_lt (iterationKappa_le_half C₂₇) (by norm_num)
    obtain ⟨n, hn₁, hn₂⟩ := exists_iteration_index hκ hκlt hr hrr
    have hdisc' := theta_iteration_bound (θ := Θ) (T := T) (κ := κ)
      (ε := ε) (η := η) hκ (fun m => by
        dsimp [T]
        field_simp) hTbound n
    have hdisc : theta (iterationKappa C₂₇) u Du p z
        (iterationKappa C₂₇ ^ n * r₅) ≤
        iterationEta C₂₇ * iterationKappa C₂₇ ^ ((n : ℝ) * iterationEpsilon) := by
      simpa [Θ, κ, η, ε] using hdisc'
    have hinterp := theta_intermediate_scale_bound κ ε η r₅ r u Du p z hκ hκle
      (show 0 < ε by norm_num [ε, iterationEpsilon]) hη.le hr₅ hr
      (by simpa [div_lt_iff₀ (mul_pos hκ hr₅)] using hn₁)
      (by simpa [div_le_iff₀ hr₅] using hn₂) hdisc
      (sws_timeSliceEnergyEssSup_ne_top hsol
        (iteration_radius_pos hκ hr₅ n) ((closure_parabolicCylinder_mono
          (iteration_radius_pos hκ hr₅ n).le (iteration_radius_le hκ hκle hr₅ n)).trans hz))
      (ne_of_lt (sws_gradient_integral_lt_top hsol
        (iteration_radius_pos hκ hr₅ n) ((closure_parabolicCylinder_mono
          (iteration_radius_pos hκ hr₅ n).le (iteration_radius_le hκ hκle hr₅ n)).trans hz)))
      (ne_of_lt (sws_pressure_integral_lt_top hsol
        (iteration_radius_pos hκ hr₅ n) ((closure_parabolicCylinder_mono
          (iteration_radius_pos hκ hr₅ n).le (iteration_radius_le hκ hκle hr₅ n)).trans hz)))
    simpa [κ, η, ε] using hinterp.2

-- Final node once the analytic lemma is available:
-- theorem iteration ... := iteration_of_thetaDecay ... thetaDecay

end CKN
