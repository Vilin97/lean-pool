/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Representation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.CutoffAverage
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowAverageSourceBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowAverage

/-! Exact flow-average form of the actual temperature forcing coefficient. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Matrix entry of the temperature coefficient after subtracting the previous diffusivity. -/
def amnrTemperatureCoefficient {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κm κprev : ℝ) (i j : Fin 2) (z : AmnrSpace) : ℝ :=
  (I.Kmat κm m z.1 - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
    I.sMat hΦ m κm z.1 z.2) i j

/-- The quadratic part of the left-Jacobian temperature coefficient, expressed
through the mixed two-flow averages used in the source estimates. -/
def amnrTemperatureQuadraticAverage {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κm : ℝ) (i j : Fin 2) (z : AmnrSpace) : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 2,
    (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
      (amnrFlowAverageA0Plus I hΦ m a b i j z -
      (if i = a then 1 else 0) * amnrFlowAverage I hΦ m b j z)

/-- The finite cutoff average preserves subtraction of a scalar constant. -/
theorem amnr_hatXi_average_sub_const {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (f : ℤ → ℝ) (d : ℝ) :
    (∑' l : ℤ, I.hatXiML m l t * (f l - d)) =
      (∑' l : ℤ, I.hatXiML m l t * f l) - d := by
  classical
  let s := (I.hatXiML_support_finite hm t).toFinset
  have hz (l : ℤ) (hl : l ∉ s) : I.hatXiML m l t = 0 := by
    by_contra hh
    exact hl ((Set.Finite.mem_toFinset _).mpr hh)
  have hs (g : ℤ → ℝ) : (∑' l, I.hatXiML m l t * g l) =
      ∑ l ∈ s, I.hatXiML m l t * g l :=
    tsum_eq_sum (fun l hl => by rw [hz l hl, zero_mul])
  have hweights : ∑ l ∈ s, I.hatXiML m l t = 1 := by
    have he : (∑' l : ℤ, I.hatXiML m l t) = ∑ l ∈ s, I.hatXiML m l t :=
      tsum_eq_sum (fun l hl => hz l hl)
    rw [← he]
    exact AVenhance.Infra.Ingredients.hatXiML_partition I hm t
  rw [hs, hs]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hweights, one_mul]

/-- The left-Jacobian quadratic window equals its contraction against the
two-flow cutoff averages. -/
theorem TemperatureCoefficientIdentity.amnr_temperature_quadratic_window_eq_average {β : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    (κm : ℝ) (i j : Fin 2) (z : AmnrSpace) :
    (∑' l : ℤ, I.hatXiML m l z.1 *
      (((I.flowGrad hΦ m l z.1 z.2).transpose - 1) *
        (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        I.flowGrad hΦ m l z.1 z.2) i j) =
      amnrTemperatureQuadraticAverage I hΦ m κm i j z := by
  classical
  let s := (I.hatXiML_support_finite hm z.1).toFinset
  have hz (l : ℤ) (hl : l ∉ s) : I.hatXiML m l z.1 = 0 := by
    by_contra hh
    exact hl ((Set.Finite.mem_toFinset _).mpr hh)
  have hsum (g : ℤ → ℝ) : (∑' l : ℤ, I.hatXiML m l z.1 * g l) =
      ∑ l ∈ s, I.hatXiML m l z.1 * g l :=
    tsum_eq_sum (fun l hl => by rw [hz l hl, zero_mul])
  have hweighted (f g : ℤ → ℝ) (d : ℝ) :
      (∑' l : ℤ, I.hatXiML m l z.1 * (f l * g l - d * g l)) =
        (∑' l : ℤ, I.hatXiML m l z.1 * (f l * g l)) -
          d * (∑' l : ℤ, I.hatXiML m l z.1 * g l) := by
    rw [hsum, hsum, hsum]
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hpoint (l : ℤ) :
      (((I.flowGrad hΦ m l z.1 z.2).transpose - 1) *
        (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        I.flowGrad hΦ m l z.1 z.2) i j =
      ∑ a : Fin 2, ∑ b : Fin 2,
        (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
          (I.flowGrad hΦ m l z.1 z.2 a i * I.flowGrad hΦ m l z.1 z.2 b j -
            (if i = a then 1 else 0) * I.flowGrad hΦ m l z.1 z.2 b j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply,
      Matrix.one_apply]
    calc
      _ = ∑ b : Fin 2, ∑ a : Fin 2,
          (I.flowGrad hΦ m l z.1 z.2 a i - (if i = a then 1 else 0)) *
            (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
            I.flowGrad hΦ m l z.1 z.2 b j := by
        apply Finset.sum_congr rfl
        intro b hb
        exact Finset.sum_mul Finset.univ
          (fun a : Fin 2 =>
            (I.flowGrad hΦ m l z.1 z.2 a i - (if i = a then 1 else 0)) *
              (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b)
          (I.flowGrad hΦ m l z.1 z.2 b j)
      _ = ∑ a : Fin 2, ∑ b : Fin 2,
          (I.flowGrad hΦ m l z.1 z.2 a i - (if i = a then 1 else 0)) *
            (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
            I.flowGrad hΦ m l z.1 z.2 b j := by
        rw [Finset.sum_comm]
      _ = ∑ a : Fin 2, ∑ b : Fin 2,
          (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
            (I.flowGrad hΦ m l z.1 z.2 a i * I.flowGrad hΦ m l z.1 z.2 b j -
              (if i = a then 1 else 0) * I.flowGrad hΦ m l z.1 z.2 b j) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
  rw [hsum]
  simp_rw [hpoint]
  unfold amnrTemperatureQuadraticAverage
  have hcontract :
      (∑ l ∈ s, I.hatXiML m l z.1 *
        (∑ a : Fin 2, ∑ b : Fin 2,
          (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
            (I.flowGrad hΦ m l z.1 z.2 a i * I.flowGrad hΦ m l z.1 z.2 b j -
              (if i = a then 1 else 0) * I.flowGrad hΦ m l z.1 z.2 b j))) =
      ∑ a : Fin 2, ∑ b : Fin 2,
        (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
          (amnrFlowAverageA0Plus I hΦ m a b i j z -
            (if i = a then 1 else 0) * amnrFlowAverage I hΦ m b j z) := by
    calc
      _ = ∑ l ∈ s, ∑ a : Fin 2, ∑ b : Fin 2,
          I.hatXiML m l z.1 *
            ((I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
              (I.flowGrad hΦ m l z.1 z.2 a i * I.flowGrad hΦ m l z.1 z.2 b j -
                (if i = a then 1 else 0) * I.flowGrad hΦ m l z.1 z.2 b j)) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
      _ = ∑ a : Fin 2, ∑ l ∈ s, ∑ b : Fin 2,
          I.hatXiML m l z.1 *
            ((I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
              (I.flowGrad hΦ m l z.1 z.2 a i * I.flowGrad hΦ m l z.1 z.2 b j -
                (if i = a then 1 else 0) * I.flowGrad hΦ m l z.1 z.2 b j)) := by
        rw [Finset.sum_comm]
      _ = ∑ a : Fin 2, ∑ b : Fin 2, ∑ l ∈ s,
          I.hatXiML m l z.1 *
            ((I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
              (I.flowGrad hΦ m l z.1 z.2 a i * I.flowGrad hΦ m l z.1 z.2 b j -
                (if i = a then 1 else 0) * I.flowGrad hΦ m l z.1 z.2 b j)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
      _ = ∑ a : Fin 2, ∑ b : Fin 2,
          (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
            (amnrFlowAverageA0Plus I hΦ m a b i j z -
              (if i = a then 1 else 0) * amnrFlowAverage I hΦ m b j z) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        have hterm := hweighted
          (fun l => I.flowGrad hΦ m l z.1 z.2 a i)
          (fun l => I.flowGrad hΦ m l z.1 z.2 b j)
          (if i = a then 1 else 0)
        have hfinite :
            (∑ l ∈ s, I.hatXiML m l z.1 *
              (I.flowGrad hΦ m l z.1 z.2 a i * I.flowGrad hΦ m l z.1 z.2 b j -
                (if i = a then 1 else 0) * I.flowGrad hΦ m l z.1 z.2 b j)) =
              amnrFlowAverageA0Plus I hΦ m a b i j z -
                (if i = a then 1 else 0) * amnrFlowAverage I hΦ m b j z := by
          rw [← hsum, hterm]
          simp only [amnrFlowAverageA0Plus, amnrFlowAverageGen, amnrFlowAverage]
        calc
          (∑ l ∈ s, I.hatXiML m l z.1 *
              ((I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
                (I.flowGrad hΦ m l z.1 z.2 a i * I.flowGrad hΦ m l z.1 z.2 b j -
                  (if i = a then 1 else 0) * I.flowGrad hΦ m l z.1 z.2 b j))) =
              (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
                ∑ l ∈ s, I.hatXiML m l z.1 *
                  (I.flowGrad hΦ m l z.1 z.2 a i * I.flowGrad hΦ m l z.1 z.2 b j -
                    (if i = a then 1 else 0) * I.flowGrad hΦ m l z.1 z.2 b j) := by
            calc
              _ = ∑ l ∈ s,
                  (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a b *
                    (I.hatXiML m l z.1 *
                      (I.flowGrad hΦ m l z.1 z.2 a i * I.flowGrad hΦ m l z.1 z.2 b j -
                        (if i = a then 1 else 0) * I.flowGrad hΦ m l z.1 z.2 b j)) := by
                apply Finset.sum_congr rfl
                intro l hl
                ring
              _ = _ := by rw [Finset.mul_sum]
          _ = _ := by rw [hfinite]
  exact hcontract

/-- The actual coefficient is the K-flow average plus the complete quadratic
left-Jacobian contribution, minus the preceding diffusivity. -/
theorem amnrTemperatureCoefficient_eq_average {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κm κprev : ℝ) (i j : Fin 2) (z : AmnrSpace) :
    amnrTemperatureCoefficient I hΦ m κm κprev i j z =
      (∑ p : Fin 2, I.Kmat κm m z.1 i p * amnrFlowAverage I hΦ m p j z) -
        κprev * (if i = j then 1 else 0) +
          amnrTemperatureQuadraticAverage I hΦ m κm i j z := by
  classical
  let s := (I.hatXiML_support_finite hm z.1).toFinset
  have hz (l : ℤ) (hl : l ∉ s) : I.hatXiML m l z.1 = 0 := by
    by_contra hh
    exact hl ((Set.Finite.mem_toFinset _).mpr hh)
  have hsum (g : ℤ → ℝ) : (∑' l : ℤ, I.hatXiML m l z.1 * g l) =
      ∑ l ∈ s, I.hatXiML m l z.1 * g l :=
    tsum_eq_sum (fun l hl => by rw [hz l hl, zero_mul])
  have hlin (p : Fin 2) :
      (∑ l ∈ s, I.hatXiML m l z.1 *
        (I.flowGrad hΦ m l z.1 z.2 p j - (if p = j then 1 else 0))) =
        amnrFlowAverage I hΦ m p j z - (if p = j then 1 else 0) := by
    rw [← hsum]
    exact amnr_hatXi_average_sub_const I hm z.1
      (fun l => I.flowGrad hΦ m l z.1 z.2 p j) (if p = j then 1 else 0)
  have hquad := TemperatureCoefficientIdentity.amnr_temperature_quadratic_window_eq_average I hΦ
      hm κm i j z
  have hmatrix (g : ℤ → Matrix (Fin 2) (Fin 2) ℝ) :
      (∑' l : ℤ, I.hatXiML m l z.1 • g l) =
        ∑ l ∈ s, I.hatXiML m l z.1 • g l :=
    tsum_eq_sum (fun l hl => by rw [hz l hl, zero_smul])
  have hquadFinite :
      (∑ l ∈ s, I.hatXiML m l z.1 *
        (((I.flowGrad hΦ m l z.1 z.2).transpose - 1) *
          (I.Kmat κm m z.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          I.flowGrad hΦ m l z.1 z.2) i j) =
        amnrTemperatureQuadraticAverage I hΦ m κm i j z := by
    rw [← hsum, hquad]
  unfold amnrTemperatureCoefficient
  rw [sMat_eq_coarseCoeffWindow]
  unfold coarseCoeffWindow
  rw [hmatrix, hmatrix]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, Matrix.sum_apply]
  rw [hquadFinite]
  simp only [Matrix.mul_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
  simp_rw [hlin]
  simp only [one_mul, mul_sub, Finset.sum_sub_distrib]
  have hcancel :
      ∑ p : Fin 2, I.Kmat κm m z.1 i p * (if p = j then 1 else 0) =
        I.Kmat κm m z.1 i j := by
    calc
      _ = ∑ p : Fin 2, if p = j then I.Kmat κm m z.1 i p else 0 := by
        simp only [mul_ite, mul_one, mul_zero]
      _ = I.Kmat κm m z.1 i j := by
        simp
  rw [hcancel]
  ring

end AVenhance.Infra.Section4
