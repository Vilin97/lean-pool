/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportHighOrder
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Transport

/-! # Transport Sharp Estimate

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped ContDiff NNReal Topology

noncomputable section

namespace AVenhance.FaaDiBruno

/-- Coefficient of a lower-order term in the sharp transport majorant. -/
def transportSharpLowerCoefficient (n k : ℕ) (C_f C_g R : ℝ) : ℝ :=
  (n.choose k : ℝ) *
    (C_f * (n - k).factorial * R ^ (n - k) /
      (n - k + 1 : ℝ) ^ 2) *
    (16 * C_g * (k + 1).factorial / (k + 2 : ℝ) ^ 2)

/-- Time-dependent integrand for a lower-order sharp transport contribution. -/
def transportSharpLowerIntegrand (n k : ℕ) (C_f C_g R : ℝ) (s : ℝ) : ℝ :=
  transportSharpLowerCoefficient n k C_f C_g R *
    (s * transportShiftRadius C_f R s ^ (k + 1))

/-- Scalar majorant for the source term in the sharp transport estimate. -/
def transportSharpSourceMajorant (n : ℕ) (C_f C_g R S s : ℝ) : ℝ :=
  C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
    ((n : ℝ) * C_f * R / 2) *
      (S * s * n.factorial * transportShiftRadius C_f R s ^ n /
        (n + 1 : ℝ) ^ 2) +
    2 * (∑ k ∈ Finset.range (n - 1 : ℕ),
      transportSharpLowerIntegrand n k C_f C_g R s)

theorem TransportSharpEstimate.choose_factorials_succ_product {n k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℝ) * (n - k).factorial * (k + 1).factorial =
      n.factorial * (k + 1 : ℝ) := by
  have hchoose := Nat.choose_mul_factorial_mul_factorial hk
  have hchoose' : (n.choose k : ℝ) * k.factorial * (n - k).factorial =
      n.factorial := by exact_mod_cast hchoose
  have hsucc : ((k + 1).factorial : ℝ) = (k + 1 : ℝ) * k.factorial := by
    exact_mod_cast Nat.factorial_succ k
  rw [hsucc]
  nlinarith [hchoose']

theorem TransportSharpEstimate.transportLowerIntegralTerm_bound {n k : ℕ}
    (hk : k < n - 1) {C_f C_g R ρ t : ℝ}
    (hCf : 0 < C_f) (hCg : 0 ≤ C_g) (hR : 0 < R)
    (ht : 0 ≤ t) (hρ : R ≤ ρ) :
    2 * ((n.choose k : ℝ) *
      (C_f * (n - k).factorial * R ^ (n - k) /
        (n - k + 1 : ℝ) ^ 2) *
      (16 * C_g * (k + 1).factorial / (k + 2 : ℝ) ^ 2) *
      (t * ρ ^ (k + 2) /
        (8 * C_f * R ^ 2 * (k + 2 : ℝ)))) ≤
      t * (n.factorial * ρ ^ n / (n + 1 : ℝ) ^ 2) *
        (4 * C_g * (n + 1 : ℝ) ^ 2 /
          ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) := by
  have hk' : k ≤ n := by omega
  have hrho : 0 < ρ := lt_of_lt_of_le hR hρ
  have hpow : R ^ (n - k - 2) ≤ ρ ^ (n - k - 2) :=
    pow_le_pow_left₀ hR.le hρ (n - k - 2)
  have hpowerProd : R ^ (n - k - 2) * ρ ^ (k + 2) ≤ ρ ^ n := by
    calc
      R ^ (n - k - 2) * ρ ^ (k + 2) ≤
          ρ ^ (n - k - 2) * ρ ^ (k + 2) :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = ρ ^ n := by
        rw [← pow_add]
        congr 1
        omega
  have hratio : (k + 1 : ℝ) / (k + 2 : ℝ) ≤ 1 := by
    rw [div_le_one₀ (by positivity : 0 < (k + 2 : ℝ))]
    exact_mod_cast Nat.le_succ (k + 1)
  have hfac := TransportSharpEstimate.choose_factorials_succ_product hk'
  have hpowcast : n - k = (n - k - 2) + 2 := by omega
  have hRpow : R ^ (n - k) = R ^ (n - k - 2) * R ^ 2 := by
    calc
      R ^ (n - k) = R ^ ((n - k - 2) + 2) := congrArg (fun j : ℕ => R ^ j) hpowcast
      _ = R ^ (n - k - 2) * R ^ 2 := by rw [pow_add]
  have hD1 : 0 < (n - k + 1 : ℝ) := by
    have hnk : (k : ℝ) ≤ n := by exact_mod_cast hk'
    linarith
  have hD2 : 0 < (k + 2 : ℝ) := by positivity
  have hEq :
      2 * ((n.choose k : ℝ) *
        (C_f * (n - k).factorial * R ^ (n - k) /
          (n - k + 1 : ℝ) ^ 2) *
        (16 * C_g * (k + 1).factorial / (k + 2 : ℝ) ^ 2) *
        (t * ρ ^ (k + 2) /
          (8 * C_f * R ^ 2 * (k + 2 : ℝ)))) =
      (4 * C_g * t * n.factorial /
        ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) *
        (R ^ (n - k - 2) * ρ ^ (k + 2)) *
        ((k + 1 : ℝ) / (k + 2 : ℝ)) := by
    have hCfne : C_f ≠ 0 := ne_of_gt hCf
    have hRne : R ≠ 0 := ne_of_gt hR
    have hfactor :
        2 * ((n.choose k : ℝ) *
          (C_f * (n - k).factorial * R ^ (n - k) /
            (n - k + 1 : ℝ) ^ 2) *
          (16 * C_g * (k + 1).factorial / (k + 2 : ℝ) ^ 2) *
          (t * ρ ^ (k + 2) /
            (8 * C_f * R ^ 2 * (k + 2 : ℝ)))) =
        (4 * C_g * t * R ^ (n - k - 2) * ρ ^ (k + 2) /
          ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 3)) *
          ((n.choose k : ℝ) * (n - k).factorial * (k + 1).factorial) := by
      rw [hRpow]
      field_simp [hCfne, hRne, hD1.ne', hD2.ne']
      ring
    calc
      _ = (4 * C_g * t * R ^ (n - k - 2) * ρ ^ (k + 2) /
            ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 3)) *
            ((n.choose k : ℝ) * (n - k).factorial * (k + 1).factorial) := hfactor
      _ = (4 * C_g * t * R ^ (n - k - 2) * ρ ^ (k + 2) /
            ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 3)) *
            (n.factorial * (k + 1 : ℝ)) := by rw [hfac]
      _ = _ := by field_simp [hD1.ne', hD2.ne']
  rw [hEq]
  have hratio0 : 0 ≤ (k + 1 : ℝ) / (k + 2 : ℝ) := by positivity
  have hcoef0 : 0 ≤ (4 * C_g * t * n.factorial /
      ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) := by positivity
  calc
    _ ≤ (4 * C_g * t * n.factorial /
          ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) *
          ρ ^ n * 1 := by
        gcongr
      _ = t * (n.factorial * ρ ^ n / (n + 1 : ℝ) ^ 2) *
          (4 * C_g * (n + 1 : ℝ) ^ 2 /
            ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) := by
        field_simp [hD1.ne', hD2.ne']

private theorem transportSharpSourceMajorant_integral_bound_lowerBound1 :
  ∀ {n : ℕ},
    (2 : ℕ) ≤ n →
      ∀ {C_f C_g R t : ℝ},
        (0 : ℝ) ≤ C_g →
          (0 : ℝ) ≤ t →
            let ρ : ℝ := transportShiftRadius C_f R t;
            let scale : ℝ := (↑n.factorial : ℝ) * ρ ^ n / ((↑n : ℝ) + (1 : ℝ)) ^ (2 : ℕ);
            let lower : ℝ → ℝ := fun (s : ℝ) =>
              (2 : ℝ) * ∑ k ∈ Finset.range (n - (1 : ℕ)), transportSharpLowerIntegrand n k C_f C_g
                  R s;
            (0 : ℝ) ≤ scale →
              ∫ (s : ℝ) in (0 : ℝ)..t, lower s =
                  (2 : ℝ) *
                    ∑ k ∈ Finset.range (n - (1 : ℕ)),
                      ∫ (s : ℝ) in (0 : ℝ)..t, transportSharpLowerIntegrand n k C_f C_g R s →
                (∀ k ∈ Finset.range (n - (1 : ℕ)),
                    (2 : ℝ) * ∫ (s : ℝ) in (0 : ℝ)..t, transportSharpLowerIntegrand n k C_f C_g R
                        s ≤
                      t * scale *
                        ((4 : ℝ) * C_g * ((↑n : ℝ) + (1 : ℝ)) ^ (2 : ℕ) /
                          (((↑n : ℝ) - (↑k : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * ((↑k : ℝ) + (2 : ℝ)) ^ (2 :
                              ℕ)))) →
                  ∑ k ∈ Finset.range (n - (1 : ℕ)),
                        ((↑n : ℝ) + (1 : ℝ)) ^ (2 : ℕ) /
                          (((↑n : ℝ) - (↑k : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * ((↑k : ℝ) + (2 : ℝ)) ^ (2 :
                              ℕ)) ≤
                      (3 / 2 : ℝ) →
                    ∫ (s : ℝ) in (0 : ℝ)..t, lower s ≤ t * scale * ((6 : ℝ) * C_g)
    := by
  intro n hn C_f C_g R t hCg ht ρ scale lower hscale hlowerEq hlowerTerm hshiftedSum
  rw [hlowerEq]
  have hsumTerms := Finset.sum_le_sum fun k hk => hlowerTerm k hk
  have hsumNonneg : 0 ≤ ∑ k ∈ Finset.range (n - 1 : ℕ),
      (n + 1 : ℝ) ^ 2 /
        ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2) :=
    Finset.sum_nonneg fun k hk => by positivity
  calc
    2 * (∑ k ∈ Finset.range (n - 1 : ℕ),
        ∫ s in 0..t, transportSharpLowerIntegrand n k C_f C_g R s) ≤
      ∑ k ∈ Finset.range (n - 1 : ℕ),
        t * scale * (4 * C_g * (n + 1 : ℝ) ^ 2 /
          ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) := by
        have hsumTerm' :
            (∑ k ∈ Finset.range (n - 1 : ℕ),
              2 * (∫ s in 0..t, transportSharpLowerIntegrand n k C_f C_g R s)) ≤ _ :=
          hsumTerms
        rw [Finset.mul_sum]
        exact hsumTerm'
    _ = t * scale * (4 * C_g *
        (∑ k ∈ Finset.range (n - 1 : ℕ),
          (n + 1 : ℝ) ^ 2 /
            ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2))) := by
        calc
          _ = (t * scale * (4 * C_g)) *
              (∑ k ∈ Finset.range (n - 1 : ℕ),
                (n + 1 : ℝ) ^ 2 /
                  ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = _ := by ring
    _ ≤ t * scale * (6 * C_g) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg ht hscale)
        calc
          4 * C_g * (∑ k ∈ Finset.range (n - 1 : ℕ),
              (n + 1 : ℝ) ^ 2 /
                ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) ≤
            4 * C_g * (3 / 2) := mul_le_mul_of_nonneg_left hshiftedSum
              (by positivity)
          _ = 6 * C_g := by ring

private theorem transportSharpSourceMajorant_integral_bound_lowerTerm2 :
  ∀ {n : ℕ} {C_f C_g R t : ℝ},
    (0 : ℝ) < C_f →
      (0 : ℝ) ≤ C_g →
        (0 : ℝ) < R →
          (0 : ℝ) ≤ t →
            let ρ : ℝ := transportShiftRadius C_f R t;
            let scale : ℝ := (↑n.factorial : ℝ) * ρ ^ n / ((↑n : ℝ) + (1 : ℝ)) ^ (2 : ℕ);
            (∀ (k : ℕ),
                ∫ (s : ℝ) in (0 : ℝ)..t, s * transportShiftRadius C_f R s ^ (k + (1 : ℕ)) ≤
                  t * ρ ^ (k + (2 : ℕ)) / ((8 : ℝ) * C_f * R ^ (2 : ℕ) * ((↑k : ℝ) + (2 : ℝ)))) →
              ∀ k ∈ Finset.range (n - (1 : ℕ)),
                (2 : ℝ) * ∫ (s : ℝ) in (0 : ℝ)..t, transportSharpLowerIntegrand n k C_f C_g R s ≤
                  t * scale *
                    ((4 : ℝ) * C_g * ((↑n : ℝ) + (1 : ℝ)) ^ (2 : ℕ) /
                      (((↑n : ℝ) - (↑k : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * ((↑k : ℝ) + (2 : ℝ)) ^ (2 : ℕ)))
    := by
  intro n C_f C_g R t hCf hCg hR ht ρ scale hρintegral k hk
  have hklt : k < n - 1 := Finset.mem_range.mp hk
  have hrad := hρintegral k
  have hc : 0 ≤ transportSharpLowerCoefficient n k C_f C_g R := by
    simp only [transportSharpLowerCoefficient]
    positivity
  have hleft :
      2 * (∫ s in 0..t, transportSharpLowerIntegrand n k C_f C_g R s) =
        2 * transportSharpLowerCoefficient n k C_f C_g R *
          (∫ s in 0..t, s * transportShiftRadius C_f R s ^ (k + 1)) := by
    simp only [transportSharpLowerIntegrand]
    rw [intervalIntegral.integral_const_mul]
    ring
  have hle :
      2 * transportSharpLowerCoefficient n k C_f C_g R *
        (∫ s in 0..t, s * transportShiftRadius C_f R s ^ (k + 1)) ≤
      2 * transportSharpLowerCoefficient n k C_f C_g R *
        (t * ρ ^ (k + 2) /
          (8 * C_f * R ^ 2 * (k + 2 : ℝ))) := by
    exact mul_le_mul_of_nonneg_left hrad (mul_nonneg (by norm_num) hc)
  rw [hleft]
  calc
    _ ≤ 2 * ((n.choose k : ℝ) *
          (C_f * (n - k).factorial * R ^ (n - k) /
            (n - k + 1 : ℝ) ^ 2) *
          (16 * C_g * (k + 1).factorial / (k + 2 : ℝ) ^ 2) *
          (t * ρ ^ (k + 2) /
            (8 * C_f * R ^ 2 * (k + 2 : ℝ)))) := by
      simpa [transportSharpLowerCoefficient, mul_assoc] using hle
    _ ≤ t * (n.factorial * ρ ^ n / (n + 1 : ℝ) ^ 2) *
        (4 * C_g * (n + 1 : ℝ) ^ 2 /
          ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) := by
      simpa [scale, ρ] using TransportSharpEstimate.transportLowerIntegralTerm_bound hklt
        hCf hCg hR ht (transportShiftRadius_lower ht hCf.le)

/-- Integrating the sharp source majorant over a characteristic gives the
equal-radius feedback coefficient and the corrected shifted convolution. -/
theorem transportSharpSourceMajorant_integral_bound {n : ℕ} (hn : 2 ≤ n)
    {C_f C_g R S t : ℝ} (hCf : 0 < C_f) (hCg : 0 ≤ C_g)
    (hR : 0 < R) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (hT : t ≤ 1 / (8 * C_f * R)) :
    (∫ s in 0..t, transportSharpSourceMajorant n C_f C_g R S s) ≤
      t * (n.factorial * transportShiftRadius C_f R t ^ n /
        (n + 1 : ℝ) ^ 2) * (C_g + S / 8 + 12 * C_g) := by
  let ρ : ℝ := transportShiftRadius C_f R t
  let scale : ℝ := n.factorial * ρ ^ n / (n + 1 : ℝ) ^ 2
  let base : ℝ := C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2
  let top : ℝ → ℝ := fun s => ((n : ℝ) * C_f * R / 2) *
    (S * s * n.factorial * transportShiftRadius C_f R s ^ n /
      (n + 1 : ℝ) ^ 2)
  let lower : ℝ → ℝ := fun s =>
    2 * (∑ k ∈ Finset.range (n - 1 : ℕ),
      transportSharpLowerIntegrand n k C_f C_g R s)
  have hρ : R ≤ ρ := by
    dsimp [ρ]
    exact transportShiftRadius_lower ht hCf.le
  have hρpos : 0 < ρ := lt_of_lt_of_le hR hρ
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hscaleR : R ^ n ≤ ρ ^ n := pow_le_pow_left₀ hR.le hρ n
  have hbase : t * base ≤ t * scale * C_g := by
    dsimp [base, scale]
    calc
      t * (C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) =
          (t * C_g * n.factorial / (n + 1 : ℝ) ^ 2) * R ^ n := by ring
      _ ≤ (t * C_g * n.factorial / (n + 1 : ℝ) ^ 2) * ρ ^ n :=
        mul_le_mul_of_nonneg_left hscaleR (by positivity)
      _ = t * (n.factorial * ρ ^ n / (n + 1 : ℝ) ^ 2) * C_g := by ring
  have htopRadiusRaw := transportRadiusIntegral_bound
    (j := n) (d := (2 : ℝ)) (by norm_num) hCf hR hR.le ht
  have htopRadius :
      (∫ s in 0..t, s * transportShiftRadius C_f R s ^ n) ≤
        t * ρ ^ (n + 1) /
          (8 * C_f * R ^ 2 * (n + 1 : ℝ)) := by
    have hrad (s : ℝ) :
        R + (4 * (2 : ℝ) * C_f * R ^ 2) * s = transportShiftRadius C_f R s := by
      dsimp [transportShiftRadius]
      ring
    have hden : (4 * (2 : ℝ) * C_f * R ^ 2) * (n + 1 : ℝ) =
        8 * C_f * R ^ 2 * (n + 1 : ℝ) := by ring
    rw [show (fun s => s * (R +
          (4 * (2 : ℝ) * C_f * R ^ 2) * s) ^ n) =
        (fun s => s * transportShiftRadius C_f R s ^ n) from by
          funext s
          rw [hrad]] at htopRadiusRaw
    rw [hrad t, hden] at htopRadiusRaw
    exact htopRadiusRaw
  have htopEq : (∫ s in 0..t, top s) =
      (((n : ℝ) * C_f * R / 2) * (S * n.factorial /
        (n + 1 : ℝ) ^ 2)) *
        (∫ s in 0..t, s * transportShiftRadius C_f R s ^ n) := by
    have hfun : (fun s => top s) = (fun s =>
        (((n : ℝ) * C_f * R / 2) * (S * n.factorial /
          (n + 1 : ℝ) ^ 2)) *
          (s * transportShiftRadius C_f R s ^ n)) := by
      funext s
      dsimp [top]
      ring
    rw [hfun, intervalIntegral.integral_const_mul]
  have htopCoeff : 0 ≤ ((n : ℝ) * C_f * R / 2) *
      (S * n.factorial / (n + 1 : ℝ) ^ 2) := by positivity
  have htopBound : (∫ s in 0..t, top s) ≤
      t * scale * (S *
        ((n : ℝ) * ρ / (16 * (n + 1 : ℝ) * R))) := by
    rw [htopEq]
    calc
      _ ≤ (((n : ℝ) * C_f * R / 2) *
            (S * n.factorial / (n + 1 : ℝ) ^ 2)) *
            (t * ρ ^ (n + 1) /
              (8 * C_f * R ^ 2 * (n + 1 : ℝ))) :=
        mul_le_mul_of_nonneg_left htopRadius htopCoeff
      _ = t * scale * (S *
            ((n : ℝ) * ρ / (16 * (n + 1 : ℝ) * R))) := by
        dsimp [scale, ρ]
        have hCfne : C_f ≠ 0 := ne_of_gt hCf
        have hRne : R ≠ 0 := ne_of_gt hR
        field_simp [hCfne, hRne]
        ring
  have htimeE18 : t ≤ 1 / (4 * (2 : ℝ) * C_f * R) := by
    have hden : 4 * (2 : ℝ) * C_f * R = 8 * C_f * R := by ring
    rw [hden]
    exact hT
  have hE18 := transportE18_equalRadius_le_eighth (n := n) (d := (2 : ℝ))
    (by norm_num) hCf hR ht htimeE18
  have hE18' : (n : ℝ) * ρ / (16 * (n + 1 : ℝ) * R) ≤ 1 / 8 := by
    have hrad : R + 4 * t * (2 : ℝ) * C_f * R ^ 2 = ρ := by
      dsimp [ρ, transportShiftRadius]
      ring
    rw [← hrad]
    exact hE18
  have htopFinal : (∫ s in 0..t, top s) ≤ t * scale * (S / 8) := by
    exact htopBound.trans <| by
      have hS : S * ((n : ℝ) * ρ / (16 * (n + 1 : ℝ) * R)) ≤ S / 8 := by
        calc
          _ ≤ S * (1 / 8) := mul_le_mul_of_nonneg_left hE18' hS
          _ = S / 8 := by ring
      exact mul_le_mul_of_nonneg_left hS (mul_nonneg ht hscale)
  have hlowerCont (k : ℕ) :
      Continuous (fun s => transportSharpLowerIntegrand n k C_f C_g R s) := by
    simp only [transportSharpLowerIntegrand, transportSharpLowerCoefficient,
      transportShiftRadius]
    fun_prop
  have hlowerInt (k : ℕ) :
      IntervalIntegrable (fun s => transportSharpLowerIntegrand n k C_f C_g R s)
        volume 0 t := (hlowerCont k).intervalIntegrable 0 t
  have hlowerEq : (∫ s in 0..t, lower s) =
      2 * (∑ k ∈ Finset.range (n - 1 : ℕ),
        ∫ s in 0..t, transportSharpLowerIntegrand n k C_f C_g R s) := by
    dsimp [lower]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_finsetSum (fun k hk => hlowerInt k)]
  have hρintegral (k : ℕ) :
      (∫ s in 0..t, s * transportShiftRadius C_f R s ^ (k + 1)) ≤
        t * ρ ^ (k + 2) /
          (8 * C_f * R ^ 2 * (k + 2 : ℝ)) := by
    have h := transportRadiusIntegral_bound
      (j := k + 1) (d := (2 : ℝ)) (by norm_num) hCf hR hR.le ht
    have hrad (s : ℝ) :
        R + (4 * (2 : ℝ) * C_f * R ^ 2) * s = transportShiftRadius C_f R s := by
      dsimp [transportShiftRadius]
      ring
    have hden : (4 * (2 : ℝ) * C_f * R ^ 2) * ((k + 1 : ℝ) + 1) =
        8 * C_f * R ^ 2 * (k + 2 : ℝ) := by ring
    have hexp : k + 1 + 1 = k + 2 := by omega
    rw [show (fun s => s * (R +
          (4 * (2 : ℝ) * C_f * R ^ 2) * s) ^ (k + 1)) =
        (fun s => s * transportShiftRadius C_f R s ^ (k + 1)) from by
          funext s
          rw [hrad]] at h
    rw [hrad t] at h
    push_cast at h
    rw [hexp, hden] at h
    exact h
  have hlowerTerm (k : ℕ) (hk : k ∈ Finset.range (n - 1 : ℕ)) :
      2 * (∫ s in 0..t, transportSharpLowerIntegrand n k C_f C_g R s) ≤
        t * scale * (4 * C_g * (n + 1 : ℝ) ^ 2 /
          ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) := by
    exact @transportSharpSourceMajorant_integral_bound_lowerTerm2 n C_f C_g R t hCf hCg hR ht
        hρintegral k hk
  have hshiftedSum :
      (∑ k ∈ Finset.range (n - 1 : ℕ),
        (n + 1 : ℝ) ^ 2 /
          ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) ≤ 3 / 2 := by
    have hcastEq (k : ℕ) (hk : k ∈ Finset.range (n - 1 : ℕ)) :
        ((n - k + 1 : ℕ) : ℝ) = (n - k + 1 : ℝ) := by
      have hklt : k < n - 1 := Finset.mem_range.mp hk
      have hkLE : k ≤ n := by omega
      rw [Nat.cast_add, Nat.cast_sub hkLE, Nat.cast_one]
    have hsumEq :
        (∑ k ∈ Finset.range (n - 1 : ℕ),
          (n + 1 : ℝ) ^ 2 /
            ((n - k + 1 : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) =
        (∑ k ∈ Finset.range (n - 1 : ℕ),
          (n + 1 : ℝ) ^ 2 /
            (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcastEq k hk]
    rw [hsumEq]
    exact transportE22_shifted_sum_le_three_halves n
  have hlowerBound : (∫ s in 0..t, lower s) ≤ t * scale * (6 * C_g) := by
    exact @transportSharpSourceMajorant_integral_bound_lowerBound1 n hn C_f C_g R t hCg ht hscale
        hlowerEq hlowerTerm hshiftedSum
  have hbaseInt : IntervalIntegrable (fun _ : ℝ => base) volume 0 t :=
    intervalIntegrable_const
  have htopCont : Continuous top := by
    dsimp [top]
    fun_prop [transportShiftRadius]
  have htopInt : IntervalIntegrable top volume 0 t := htopCont.intervalIntegrable 0 t
  have hlowerCont : Continuous lower := by
    dsimp [lower, transportSharpLowerIntegrand, transportSharpLowerCoefficient]
    fun_prop [transportShiftRadius]
  have hlowerInt' : IntervalIntegrable lower volume 0 t := hlowerCont.intervalIntegrable 0 t
  have hsplit :
      (∫ s in 0..t, transportSharpSourceMajorant n C_f C_g R S s) =
        t * base + (∫ s in 0..t, top s) + (∫ s in 0..t, lower s) := by
    change (∫ s in 0..t, (base + top s) + lower s) = _
    rw [intervalIntegral.integral_add (hbaseInt.add htopInt) hlowerInt']
    rw [intervalIntegral.integral_add hbaseInt htopInt]
    rw [intervalIntegral.integral_const]
    simp
  rw [hsplit]
  have hlowerWeak : t * scale * (6 * C_g) ≤ t * scale * (12 * C_g) := by
    exact mul_le_mul_of_nonneg_left (by nlinarith [hCg]) (mul_nonneg ht hscale)
  calc
    t * base + (∫ s in 0..t, top s) + (∫ s in 0..t, lower s) ≤
        t * scale * C_g + t * scale * (S / 8) + t * scale * (12 * C_g) :=
      add_le_add (add_le_add hbase htopFinal) (hlowerBound.trans hlowerWeak)
    _ = t * scale * (C_g + S / 8 + 12 * C_g) := by ring

private theorem transportSolution_snorm_order_equalRadius_majorantBound1 :
  ∀ {n : ℕ},
    (2 : ℕ) ≤ n →
      ∀ {b g Y : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)},
        IsClassicalTransportSolution b g Y →
          ContDiff ℝ ∞ (Function.uncurry b) →
            ContDiff ℝ ∞ (Function.uncurry g) →
              ∀ {X : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ)},
                IsFlow b X →
                  ∀ {C_f C_g R : ℝ},
                    (0 : ℝ) < C_f →
                      (0 : ℝ) ≤ C_g →
                        (0 : ℝ) < R →
                          (∀ (t : ℝ) (m : ℕ), (1 : ℕ) ≤ m → m ≤ n → snorm (b t) m R ≤
                              ENNReal.ofReal C_f) →
                            (∀ (t : ℝ), snorm (g t) n R ≤ ENNReal.ofReal C_g) →
                              (∀ (k : ℕ),
                                  (1 : ℕ) ≤ k →
                                    k < n →
                                      ∀ (t : ℝ),
                                        |t| ≤ (1 : ℝ) / ((8 : ℝ) * C_f * R) →
                                          snorm (Y t) k (transportShiftRadius C_f R |t|) ≤
                                            ENNReal.ofReal ((16 : ℝ) * C_g * |t|)) →
                                let T : ℝ := 1 / (8 * C_f * R);
                                ∀ (L : ℝ),
                                  (∀ (t : ℝ) (x y : Vec (2 : ℕ)), ‖b t x - b t y‖ ≤ L * ‖x - y‖) →
                                    (0 : ℕ) < n →
                                      let S : ℝ := sSup (transportJetRatioSet (n := n) Y C_f R T);
                                      (0 : ℝ) ≤ S →
                                        (∀ (t : ℝ),
                                            |t| ≤ T →
                                              ∀ (I : Fin n → Fin (2 : ℕ)) (x : Vec (2 : ℕ)),
                                                ‖orderedPartial n (Y t) x I‖ ≤
                                                  S *
                                                    (|t| *
                                                      ((↑n.factorial : ℝ) * transportShiftRadius
                                                          C_f R |t| ^ n /
                                                        ((↑n : ℝ) + (1 : ℝ)) ^ (2 : ℕ)))) →
                                          ∀ z ∈ transportJetRatioSet (n := n) Y C_f R T, z ≤ C_g +
                                              S / (8 : ℝ) + (12 : ℝ) * C_g
    := by
  intro n hn b g Y hY hb hg X hX C_f C_g R hCf hCg hR hB hG hLower T L hLip hnpos S hSnonneg
      hpartialS z hz
  rcases hz with ⟨t, htpos, htT, I, x, rfl⟩
  let B : ℝ → ℝ := fun s => transportSharpSourceMajorant n C_f C_g R S s
  have hBcont : Continuous B := by
    dsimp [B]
    unfold transportSharpSourceMajorant transportSharpLowerIntegrand
      transportSharpLowerCoefficient
    fun_prop [transportShiftRadius]
  have hsourceSharp : ∀ r, |r| ≤ T → ∀ J : Fin n → Fin 2, ∀ y,
      ‖transportSourceJet (List.ofFn fun j => coordinateVector 2 (J j))
        b g Y (r, y)‖ ≤ B |r| := by
    intro r hr J y
    have hU : ∀ Q : Fin n → Fin 2,
        ‖orderedPartial n (Y r) y Q‖ ≤
          S * (|r| * (n.factorial * transportShiftRadius C_f R |r| ^ n /
            (n + 1 : ℝ) ^ 2)) := by
      intro Q
      exact hpartialS r hr Q y
    have hsharp := transportSourceJet_norm_le_sharp hn J hY hb hg
      hCf hCg hR hB hG
      (by simpa [T] using hLower) r hr y hU
    have hlowEq :
        (∑ k ∈ Finset.range (n - 1 : ℕ),
          (n.choose k : ℝ) *
            (C_f * (n - k).factorial * R ^ (n - k) /
              (n - k + 1 : ℝ) ^ 2 *
              (16 * C_g * |r| * (k + 1).factorial *
                transportShiftRadius C_f R |r| ^ (k + 1) /
                (k + 2 : ℝ) ^ 2))) =
        (∑ k ∈ Finset.range (n - 1 : ℕ),
          transportSharpLowerCoefficient n k C_f C_g R *
            (|r| * transportShiftRadius C_f R |r| ^ (k + 1))) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [transportSharpLowerCoefficient]
      ring
    have hRHS :
        C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
          ((n : ℝ) * C_f * R / 2) *
            (S * (|r| * (n.factorial *
              transportShiftRadius C_f R |r| ^ n / (n + 1 : ℝ) ^ 2))) +
          2 * (∑ k ∈ Finset.range (n - 1 : ℕ),
            (n.choose k : ℝ) *
              (C_f * (n - k).factorial * R ^ (n - k) /
                (n - k + 1 : ℝ) ^ 2 *
                (16 * C_g * |r| * (k + 1).factorial *
                  transportShiftRadius C_f R |r| ^ (k + 1) /
                  (k + 2 : ℝ) ^ 2))) = B |r| := by
      dsimp [B, transportSharpSourceMajorant, transportSharpLowerIntegrand]
      rw [← hlowEq]
      ring
    exact hsharp.trans_eq hRHS
  have hpartialInt := transportOrderedPartial_norm_le_integrated_source_bound
    hnpos hY hb hg hX ⟨L, hLip⟩ htT B hBcont hsourceSharp I x
  have hInt := transportSharpSourceMajorant_integral_bound hn hCf hCg hR
    hSnonneg (abs_nonneg t) htT
  have hscale : 0 < n.factorial *
      transportShiftRadius C_f R |t| ^ n / (n + 1 : ℝ) ^ 2 := by
    dsimp [transportShiftRadius]
    positivity
  have hden : 0 < |t| *
      (n.factorial * transportShiftRadius C_f R |t| ^ n /
        (n + 1 : ℝ) ^ 2) := mul_pos htpos hscale
  have hnum :
      ‖orderedPartial n (Y t) x I‖ ≤
        (|t| * (n.factorial * transportShiftRadius C_f R |t| ^ n /
          (n + 1 : ℝ) ^ 2)) * (C_g + S / 8 + 12 * C_g) := by
    exact hpartialInt.trans (by simpa [B] using hInt)
  exact (div_le_iff₀ hden).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hnum)

/-- The corrected equal-radius, dimension-two form of Lemma 10577 at order
`n ≥ 2`. The lower orders are the induction hypotheses on the same shifted
radius, and the top-order feedback is absorbed with the corrected factor. -/
theorem transportSolution_snorm_order_equalRadius
    {n : ℕ} (hn : 2 ≤ n) {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {C_f C_g R : ℝ} (hCf : 0 < C_f) (hCg : 0 ≤ C_g) (hR : 0 < R)
    (hB : ∀ t m, 1 ≤ m → m ≤ n →
      snorm (b t) m R ≤ ENNReal.ofReal C_f)
    (hG : ∀ t, snorm (g t) n R ≤ ENNReal.ofReal C_g)
    (hLower : ∀ k, 1 ≤ k → k < n → ∀ t,
      |t| ≤ 1 / (8 * C_f * R) →
      snorm (Y t) k (transportShiftRadius C_f R |t|) ≤
        ENNReal.ofReal (16 * C_g * |t|)) :
    ∀ t, |t| ≤ 1 / (8 * C_f * R) →
      snorm (Y t) n (transportShiftRadius C_f R |t|) ≤
        ENNReal.ofReal (16 * C_g * |t|) := by
  let T : ℝ := 1 / (8 * C_f * R)
  let K : ℝ := (n : ℝ) * C_f * R / 2
  let F : ℝ := C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
    2 * transportLowerAllocationMajorant n C_f C_g R (2 * R) T
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hTnonneg : 0 ≤ T := hTpos.le
  have hTmax : T ≤ 1 / (8 * C_f * R) := le_rfl
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hF : 0 ≤ F := by
    dsimp [F]
    apply add_nonneg
    · positivity
    · exact mul_nonneg (by norm_num) <| transportLowerAllocationMajorant_nonneg
        hCf.le hCg hR.le (by positivity) hTnonneg
  obtain ⟨M, hMnonneg, hM⟩ := transportJetArray_coarse_bound hn
    hY hb hg hX hCf hCg hR hTnonneg hTmax hB hG
    (by simpa [T] using hLower)
  have hsourceArray := transportSourceArray_norm_le_of_lower_bounds hn
    hY hb hg hCf hCg hR hTnonneg hTmax hB hG (by simpa [T] using hLower)
  have hLipExist := transportField_lipschitz_of_snorm_one hb hCf.le hR
    (fun r => hB r 1 (by omega) (by omega))
  rcases hLipExist with ⟨L, hLnonneg, hLip⟩
  let D : ℝ := K * M + F
  have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
  have hsource : ∀ r, |r| ≤ T → ∀ I : Fin n → Fin 2, ∀ x,
      ‖transportSourceJet (List.ofFn fun j => coordinateVector 2 (I j))
        b g Y (r, x)‖ ≤ D := by
    intro r hr I x
    have harr := hsourceArray r hr x
    have hcomponent :
        ‖transportSourceJet (List.ofFn fun j => coordinateVector 2 (I j))
            b g Y (r, x)‖ ≤ ‖transportSpatialSourceArray n b g Y r x‖ := by
      change ‖transportSpatialSourceArray n b g Y r x I‖ ≤ _
      exact norm_le_pi_norm _ I
    have hjet := hM r hr x
    calc
      _ ≤ ‖transportSpatialSourceArray n b g Y r x‖ := hcomponent
      _ ≤ K * ‖orderedSpatialJetArray n (Y r) x‖ + F := by
        simpa [K, F] using harr
      _ ≤ K * M + F := add_le_add
        (mul_le_mul_of_nonneg_left hjet hK) le_rfl
  have hnpos : 0 < n := by omega
  have hpartialCoarse : ∀ t, |t| ≤ T → ∀ I : Fin n → Fin 2, ∀ x,
      ‖orderedPartial n (Y t) x I‖ ≤ |t| * D := by
    intro t ht I x
    exact transportOrderedPartial_norm_le_symmetric_source_bound hnpos
      hY hb hg hX ⟨L, hLip⟩ hsource ht I x
  have hratioBdd := transportJetRatioSet_bddAbove Y hCf.le hR hDnonneg
    hpartialCoarse
  have hratioNonempty : (transportJetRatioSet (n := n) Y C_f R T).Nonempty := by
    refine ⟨‖orderedPartial n (Y T) 0 (fun _ => 0)‖ /
      (T * (n.factorial * transportShiftRadius C_f R T ^ n /
        (n + 1 : ℝ) ^ 2)), T, ?_, ?_, fun _ => 0, 0, ?_⟩
    · simpa [abs_of_pos hTpos] using hTpos
    · simp [abs_of_pos hTpos]
    · simp [abs_of_pos hTpos]
  let S : ℝ := sSup (transportJetRatioSet (n := n) Y C_f R T)
  have hSnonneg : 0 ≤ S := by
    rcases hratioNonempty with ⟨z, hz⟩
    have hznonneg : 0 ≤ z := by
      rcases hz with ⟨t, htpos, htT, I, x, hzeq⟩
      rw [hzeq]
      have hscale : 0 < n.factorial *
          transportShiftRadius C_f R |t| ^ n / (n + 1 : ℝ) ^ 2 := by
        dsimp [transportShiftRadius]
        positivity
      positivity
    exact hznonneg.trans (le_csSup hratioBdd hz)
  have hpartialS : ∀ t, |t| ≤ T → ∀ I : Fin n → Fin 2, ∀ x,
      ‖orderedPartial n (Y t) x I‖ ≤
        S * (|t| * (n.factorial * transportShiftRadius C_f R |t| ^ n /
          (n + 1 : ℝ) ^ 2)) := by
    intro t ht I x
    by_cases htzero : t = 0
    · subst t
      have hinit := orderedSpatialJetArray_initial_zero hnpos hY x
      have hcoord : orderedPartial n (Y 0) x I = 0 := by
        simpa [orderedSpatialJetArray] using congrFun hinit I
      simp [hcoord]
    · have htpos : 0 < |t| := abs_pos.mpr htzero
      have hmem :
          (‖orderedPartial n (Y t) x I‖ /
            (|t| * (n.factorial * transportShiftRadius C_f R |t| ^ n /
              (n + 1 : ℝ) ^ 2))) ∈
          transportJetRatioSet (n := n) Y C_f R T :=
        ⟨t, htpos, ht, I, x, rfl⟩
      have hscale : 0 < n.factorial *
          transportShiftRadius C_f R |t| ^ n / (n + 1 : ℝ) ^ 2 := by
        dsimp [transportShiftRadius]
        positivity
      have hden : 0 < |t| *
          (n.factorial * transportShiftRadius C_f R |t| ^ n /
            (n + 1 : ℝ) ^ 2) := mul_pos htpos hscale
      have hsup := le_csSup hratioBdd hmem
      exact (div_le_iff₀ hden).mp hsup
  have hmajorantBound : ∀ z ∈ transportJetRatioSet (n := n) Y C_f R T,
      z ≤ C_g + S / 8 + 12 * C_g := by
    exact @transportSolution_snorm_order_equalRadius_majorantBound1 n hn b g Y hY hb hg X hX C_f
        C_g R hCf hCg hR hB hG hLower L hLip hnpos hSnonneg hpartialS
  have hSupper : S ≤ C_g + S / 8 + 12 * C_g :=
    csSup_le hratioNonempty hmajorantBound
  have hSabs : S ≤ C_g + S / 8 + 6 * (2 : ℝ) * C_g := by
    nlinarith [hSupper]
  have hSfinal : S ≤ 16 * C_g := by
    have h := transportE18_equalRadius_absorption (d := (2 : ℝ))
      (by norm_num) hCg hSabs
    nlinarith [h]
  intro t ht
  let ρt : ℝ := transportShiftRadius C_f R |t|
  have hρt : 0 < ρt := by dsimp [ρt, transportShiftRadius]; positivity
  have hpoint : ∀ I : Fin n → Fin 2, ∀ x,
      ‖orderedPartial n (Y t) x I‖ ≤
        (16 * C_g * |t|) * (n.factorial * ρt ^ n / (n + 1 : ℝ) ^ 2) := by
    intro I x
    have hpt := hpartialS t (by simpa [T] using ht) I x
    have hfactor : 0 ≤ |t| *
        (n.factorial * ρt ^ n / (n + 1 : ℝ) ^ 2) := by positivity
    calc
      _ ≤ S * (|t| * (n.factorial * ρt ^ n / (n + 1 : ℝ) ^ 2)) := by
        simpa [ρt] using hpt
      _ ≤ (16 * C_g) * (|t| *
            (n.factorial * ρt ^ n / (n + 1 : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hSfinal hfactor
      _ = (16 * C_g * |t|) *
            (n.factorial * ρt ^ n / (n + 1 : ℝ) ^ 2) := by ring
  have hDsup := derivativeSup_le_of_orderedPartial_pointwise (Y t) hpoint
  have hDsup' : derivativeSup n (Y t) ≤ ENNReal.ofReal
      ((16 * C_g * |t|) * ρt ^ n * n.factorial / (n + 1 : ℝ) ^ 2) := by
    have hreal :
        (16 * C_g * |t|) * (n.factorial * ρt ^ n / (n + 1 : ℝ) ^ 2) =
          (16 * C_g * |t|) * ρt ^ n * n.factorial / (n + 1 : ℝ) ^ 2 := by ring
    rw [hreal] at hDsup
    exact hDsup
  have hsnorm := snorm_le_of_derivativeSup_le (Y t) hρt hDsup'
  simpa [ρt] using hsnorm

/-- The order-one base case with finite-order coefficient bounds. -/
theorem transportSolution_snorm_equalRadius_one
    {N : ℕ} (hN : 1 ≤ N)
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {C_f C_g R : ℝ} (hCf : 0 < C_f) (hCg : 0 ≤ C_g) (hR : 0 < R)
    (hB : ∀ t m, 1 ≤ m → m ≤ N →
      snorm (b t) m R ≤ ENNReal.ofReal C_f)
    (hG : ∀ t m, 1 ≤ m → m ≤ N →
      snorm (g t) m R ≤ ENNReal.ofReal C_g)
    {t : ℝ} (ht : |t| ≤ 1 / (8 * C_f * R)) :
    snorm (Y t) 1 (transportShiftRadius C_f R |t|) ≤
      ENNReal.ofReal (16 * C_g * |t|) := by
  have hbase := @transportSolution_snorm_one_equalRadius
    b g Y hY hb hg X hX C_f C_g R hCf hCg hR
    (fun r => hB r 1 (by omega) hN)
    (fun r => hG r 1 (by omega) hN) t ht
  rw [show transportShiftRadius C_f R |t| =
    R * (1 + 8 * |t| * C_f * R) by unfold transportShiftRadius; ring]
  exact hbase

/-- The induction step in Lemma 10577, isolated so each high-order estimate
elaborates under Lean's default heartbeat budget. -/
theorem transportSolution_snorm_equalRadius_step
    {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N)
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {C_f C_g R : ℝ} (hCf : 0 < C_f) (hCg : 0 ≤ C_g) (hR : 0 < R)
    (hB : ∀ t m, 1 ≤ m → m ≤ N →
      snorm (b t) m R ≤ ENNReal.ofReal C_f)
    (hG : ∀ t m, 1 ≤ m → m ≤ N →
      snorm (g t) m R ≤ ENNReal.ofReal C_g)
    (hLower : ∀ k, 1 ≤ k → k < n → ∀ t,
      |t| ≤ 1 / (8 * C_f * R) →
      snorm (Y t) k (transportShiftRadius C_f R |t|) ≤
        ENNReal.ofReal (16 * C_g * |t|))
    {t : ℝ} (ht : |t| ≤ 1 / (8 * C_f * R)) :
    snorm (Y t) n (transportShiftRadius C_f R |t|) ≤
      ENNReal.ofReal (16 * C_g * |t|) := by
  exact @transportSolution_snorm_order_equalRadius n hn b g Y hY hb hg X hX
    C_f C_g R hCf hCg hR
    (fun r m hm hmn => hB r m hm (le_trans hmn hnN))
    (fun r => hG r n (by omega) hnN) hLower t ht

/-- All positive spatial orders through the paper's finite cutoff in the
corrected equal-radius form of Lemma 10577. The induction hypotheses use the
shifted radius at each time, so the lower-order terms in the differentiated
equation are exactly those absorbed by the corrections. -/
theorem transportSolution_snorm_equalRadius_all
    {N : ℕ}
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {C_f C_g R : ℝ} (hCf : 0 < C_f) (hCg : 0 ≤ C_g) (hR : 0 < R)
    (hB : ∀ t m, 1 ≤ m → m ≤ N →
      snorm (b t) m R ≤ ENNReal.ofReal C_f)
    (hG : ∀ t m, 1 ≤ m → m ≤ N →
      snorm (g t) m R ≤ ENNReal.ofReal C_g) :
    ∀ n, 1 ≤ n → n ≤ N → ∀ t, |t| ≤ 1 / (8 * C_f * R) →
      snorm (Y t) n (transportShiftRadius C_f R |t|) ≤
        ENNReal.ofReal (16 * C_g * |t|) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn hnN t ht
      by_cases hn_one : n = 1
      · subst n
        exact transportSolution_snorm_equalRadius_one hnN hY hb hg hX
          hCf hCg hR hB hG ht
      · have hn_two : 2 ≤ n := by omega
        exact transportSolution_snorm_equalRadius_step hn_two hnN hY hb hg hX
          hCf hCg hR hB hG
          (by
            intro k hk hklt r hr
            exact ih k (by omega) hk (by omega) r hr)
          ht

/-- The consumed finite-order, equal-radius form of Corollary 10670. The
coordinate matrix gradient is controlled through order `n` by Lemma 10577 at
order `n+1`; this includes the separate `n=0` endpoint. -/
theorem transportSolution_gradient_snorm_equalRadius
    {N n : ℕ} (hn : n + 1 ≤ N)
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {C_f C_g R : ℝ} (hCf : 0 < C_f) (hCg : 0 ≤ C_g) (hR : 0 < R)
    (hB : ∀ t m, 1 ≤ m → m ≤ N →
      snorm (b t) m R ≤ ENNReal.ofReal C_f)
    (hG : ∀ t m, 1 ≤ m → m ≤ N →
      snorm (g t) m R ≤ ENNReal.ofReal C_g)
    {t : ℝ} (ht : |t| ≤ 1 / (8 * C_f * R)) :
    snorm (spatialGradientMatrix (Y t)) n
        (R * (1 + 8 * |t| * C_f * R) ^ 2) ≤
      ENNReal.ofReal (8 * C_g / C_f) := by
  have hnext := transportSolution_snorm_equalRadius_all hY hb hg hX
    hCf hCg hR hB hG (n + 1) (by omega) hn t ht
  have hnext' : snorm (Y t) (n + 1)
      (R * (1 + 8 * |t| * C_f * R)) ≤
      ENNReal.ofReal (16 * C_g * |t|) := by
    have hradius : transportShiftRadius C_f R |t| =
        R * (1 + 8 * |t| * C_f * R) := by
      unfold transportShiftRadius
      ring
    rw [← hradius]
    exact hnext
  have hslice : ContDiff ℝ ∞ (Y t) := by
    have hpair : ContDiff ℝ ∞ (fun x : Vec 2 => (t, x)) := by fun_prop
    simpa [Function.uncurry, Function.comp_def] using hY.smooth.comp hpair
  exact spatialGradientMatrix_snorm_le_of_nextOrder (Y t) hslice n
    hCf hCg hR (abs_nonneg t) ht hnext'

end AVenhance.FaaDiBruno

end
