/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaPrime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermittedInterval

/-! Normalized coordinates for the auxiliary diffusivity recurrence. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance

/-- The exponents in the normalized recurrence satisfy the balance used in
the source's scale conversion. -/
theorem q_gamma_balance {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    q β * (β - gamma β) = β + gamma β := by
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ hβ'
  unfold gamma
  field_simp [ne_of_gt (by linarith : 0 < q β + 1)]
  ring

/-- A supergeometric ratio raised to the exponent `β−γ` stays within a
linear error. The proof keeps the real-power estimates separate from the
polynomial inequalities. -/
theorem rpow_ratio_control {e x r A : ℝ}
    (he : 0 ≤ e) (he128 : e ≤ 1 / 128) (hA : 0 ≤ A)
    (hlo : 1 - 10 * e ≤ x) (hhi : x ≤ 1 + A * e)
    (hr : 0 < r) (hr2 : r ≤ 2) :
    x ^ r ≤ 1 + (2 * A + A ^ 2 / 128) * e ∧
      (x ^ r)⁻¹ ≤ 1 + 50 * e := by
  have hu : 0 ≤ 10 * e := by positivity
  have hu4 : 10 * e ≤ 1 / 4 := by nlinarith [he128]
  have hloPos : 0 < 1 - 10 * e := by nlinarith [he128]
  have hxPos : 0 < x := lt_of_lt_of_le hloPos hlo
  have hhiPos : 0 < 1 + A * e := by positivity
  have hhiOne : 1 ≤ 1 + A * e := by nlinarith [mul_nonneg hA he]
  have hrNonneg : 0 ≤ r := hr.le
  have hxPow : x ^ r ≤ (1 + A * e) ^ r :=
    Real.rpow_le_rpow hxPos.le hhi hrNonneg
  have hPowTwo : (1 + A * e) ^ r ≤ (1 + A * e) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hhiOne hr2
  have hUpperAlgebra : (1 + A * e) ^ 2 ≤
      1 + (2 * A + A ^ 2 / 128) * e := by
    have he2 : e ^ 2 ≤ e / 128 := by nlinarith [he128, sq_nonneg e]
    nlinarith [mul_nonneg (sq_nonneg A) he]
  have hInvBase : 1 / x ≤ 1 / (1 - 10 * e) :=
    one_div_le_one_div_of_le hloPos hlo
  have hInvPow : (1 / x) ^ r ≤ (1 / (1 - 10 * e)) ^ r := by
    apply Real.rpow_le_rpow
    · positivity
    · exact hInvBase
    · exact hrNonneg
  have hInvBaseOne : 1 ≤ 1 / (1 - 10 * e) := by
    apply (le_div_iff₀ hloPos).2
    nlinarith [hu]
  have hInvPowTwo : (1 / (1 - 10 * e)) ^ r ≤
      (1 / (1 - 10 * e)) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hInvBaseOne hr2
  have hReciprocalAlgebra :
      (1 / (1 - 10 * e)) ^ 2 ≤ 1 + 50 * e := by
    have hInvLin : 1 / (1 - 10 * e) ≤ 1 + 20 * e := by
      apply (div_le_iff₀ hloPos).2
      nlinarith [mul_nonneg hu (by nlinarith [he128] : 0 ≤ 1 - 20 * e)]
    have hInvLinNonneg : 0 ≤ 1 / (1 - 10 * e) := by positivity
    have hSq : (1 / (1 - 10 * e)) ^ 2 ≤ (1 + 20 * e) ^ 2 :=
      pow_le_pow_left₀ hInvLinNonneg hInvLin 2
    have hSqUpper : (1 + 20 * e) ^ 2 ≤ 1 + 50 * e := by
      nlinarith [he128, sq_nonneg e]
    exact le_trans hSq hSqUpper
  have hDivPow : (1 / x) ^ r = (x ^ r)⁻¹ := by
    rw [Real.div_rpow (by norm_num) hxPos.le]
    simp
  constructor
  · exact hxPow.trans (hPowTwo.trans (by
      calc
        (1 + A * e) ^ (2 : ℝ) = (1 + A * e) ^ 2 :=
          Real.rpow_natCast (1 + A * e) 2
        _ ≤ 1 + (2 * A + A ^ 2 / 128) * e := hUpperAlgebra))
  · rw [← hDivPow]
    exact hInvPow.trans (hInvPowTwo.trans (by
      calc
        (1 / (1 - 10 * e)) ^ (2 : ℝ) =
            (1 / (1 - 10 * e)) ^ 2 :=
              Real.rpow_natCast (1 / (1 - 10 * e)) 2
        _ ≤ 1 + 50 * e := hReciprocalAlgebra))

/-- The corrected supergeometric estimate controls the exact normalized
recurrence factor by `1 + C(β) ε_m`. This uses exponent `β−γ`; the source's
display at `e.bound.some.stuff` writes `β` there, while the exact balance is
`q(β−γ)=β+γ`. -/
theorem kappaPrime_ratio_factor_bounds {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    let R := (epsilon β Λ (m + 1) / epsilon β Λ m ^ q β) ^
      (β - gamma β)
    R ≤ 1 + (2 * Infra.Ingredients.supergeoConstant β +
        Infra.Ingredients.supergeoConstant β ^ 2 / 128) *
        epsilon β Λ m ∧
      R⁻¹ ≤ 1 + 50 * epsilon β Λ m := by
  let e := epsilon β Λ m
  let x := epsilon β Λ (m + 1) / epsilon β Λ m ^ q β
  let r := β - gamma β
  let A := Infra.Ingredients.supergeoConstant β
  let R := (epsilon β Λ (m + 1) / epsilon β Λ m ^ q β) ^
    (β - gamma β)
  have hePos : 0 < e := by
    dsimp [e]
    exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have he : 0 ≤ e := hePos.le
  have he128 : e ≤ 1 / 128 := by
    have hε := Infra.Ingredients.epsilon_le_lambda_pow hβ hβ' hΛ (m := m)
    have hΛpos : 0 < (Λ : ℝ) := by positivity
    have hΛone : 1 ≤ (Λ : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2 ^ 7) hΛ)
    have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hExp : -(m : ℝ) ≤ (-1 : ℝ) := by linarith
    have hpow : (Λ : ℝ) ^ (-(m : ℝ)) ≤ (Λ : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hΛone hExp
    have hΛ128 : (128 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
    have hInv : (Λ : ℝ)⁻¹ ≤ (128 : ℝ)⁻¹ := by
      simpa [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 128) hΛ128)
    have hInvRpow : (Λ : ℝ) ^ (-1 : ℝ) = (Λ : ℝ)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hΛpos), Real.rpow_one]
    calc
      e ≤ (Λ : ℝ) ^ (-(m : ℝ)) := by simpa [e] using hε
      _ ≤ (Λ : ℝ) ^ (-1 : ℝ) := hpow
      _ ≤ (128 : ℝ)⁻¹ := by rw [hInvRpow]; exact hInv
      _ = 1 / 128 := by norm_num
  have hqPow : 0 < epsilon β Λ m ^ q β :=
    Real.rpow_pos_of_pos hePos _
  have hsg := Infra.Ingredients.epsilon_supergeo hβ hβ' hΛ hm
  have hxlo : 1 - 10 * e ≤ x := by
    dsimp [e, x]
    exact (le_div_iff₀ hqPow).2 hsg.1
  have hxhi : x ≤ 1 + A * e := by
    dsimp [e, x, A]
    exact (div_le_iff₀ hqPow).2 hsg.2
  have hrPos : 0 < r := by
    dsimp [r]
    apply sub_pos.mpr
    unfold gamma
    have hden : 0 < q β + 1 := by
      have hq := Infra.Ingredients.one_lt_q hβ hβ'
      linarith
    apply (div_lt_iff₀ hden).2
    have hβpos : 0 < β := by linarith
    nlinarith [mul_pos hβpos (by norm_num : (0 : ℝ) < 2)]
  have hrTwo : r ≤ 2 := by
    dsimp [r]
    have hg : 0 < gamma β := Infra.Ingredients.gamma_pos hβ hβ'
    nlinarith [hβ']
  have hA : 0 ≤ A := by
    have hq : 0 < q β := by
      have := Infra.Ingredients.one_lt_q hβ hβ'
      linarith
    dsimp [A, Infra.Ingredients.supergeoConstant]
    positivity
  have hcontrol := rpow_ratio_control he he128 hA hxlo hxhi hrPos hrTwo
  change R ≤ 1 + (2 * Infra.Ingredients.supergeoConstant β +
      Infra.Ingredients.supergeoConstant β ^ 2 / 128) *
        epsilon β Λ m ∧ R⁻¹ ≤ 1 + 50 * epsilon β Λ m
  simpa [R, x, e, r, A] using hcontrol

/-- The auxiliary recurrence in coordinates normalized by
`ε_m^(β+γ)`. The forcing term is `9/80`; scaling the diffusivity by
`sqrt(80/9)` would instead make that term one. -/
def kappaPrimeNormalized (β : ℝ) (Λ : ℕ) (κ : ℝ) (m d : ℕ) : ℝ :=
  kappaPrimeAt β Λ κ m d /
    epsilon β Λ m ^ (β + gamma β)

/-- Exact one-step normalized recurrence. It uses exponent `β−γ` on the
supergeometric ratio, as follows from `q(β−γ)=β+γ`. -/
theorem kappaPrimeNormalized_step {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (hκ : 0 < κ) (m d : ℕ) :
    kappaPrimeNormalized β Λ κ m (d + 1) =
      (epsilon β Λ (m + 1) /
        epsilon β Λ m ^ q β) ^ (β - gamma β) *
        (epsilon β Λ (m + 1) ^ (2 * gamma β) *
          kappaPrimeNormalized β Λ κ (m + 1) d +
          (9 / 80) /
            kappaPrimeNormalized β Λ κ (m + 1) d) := by
  have he : 0 < epsilon β Λ m := Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hen : 0 < epsilon β Λ (m + 1) := Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hK : 0 < kappaPrimeAt β Λ κ (m + 1) d :=
    kappaPrimeAt_pos hβ hβ' hΛ hκ (m + 1) d
  have hgamma : q β * (β - gamma β) = β + gamma β :=
    q_gamma_balance hβ hβ'
  have hterm : a β Λ (m + 1) ^ 2 * epsilon β Λ (m + 1) ^ 4 =
      epsilon β Λ (m + 1) ^ (2 * β) := by
    change (epsilon β Λ (m + 1) ^ (β - 2)) ^ 2 *
      epsilon β Λ (m + 1) ^ 4 = _
    calc
      (epsilon β Λ (m + 1) ^ (β - 2)) ^ 2 *
          epsilon β Λ (m + 1) ^ 4 =
        epsilon β Λ (m + 1) ^ ((β - 2) * 2) *
          epsilon β Λ (m + 1) ^ (4 : ℝ) := by
            rw [← Real.rpow_natCast (epsilon β Λ (m + 1) ^ (β - 2)) 2,
              ← Real.rpow_natCast (epsilon β Λ (m + 1)) 4,
              ← Real.rpow_mul hen.le]
            rw [show (β - 2) * (↑(2 : ℕ) : ℝ) = (β - 2) * 2 by norm_num,
              show (↑(4 : ℕ) : ℝ) = (4 : ℝ) by norm_num]
      _ = epsilon β Λ (m + 1) ^ ((β - 2) * 2 + 4) := by
        rw [← Real.rpow_add hen]
      _ = epsilon β Λ (m + 1) ^ (2 * β) := by
        congr 1
        ring
  let e := epsilon β Λ m
  let v := epsilon β Λ (m + 1)
  let K := kappaPrimeAt β Λ κ (m + 1) d
  let p := β + gamma β
  have he' : 0 < e := by dsimp [e]; exact he
  have hv' : 0 < v := by dsimp [v]; exact hen
  have hK' : 0 < K := by dsimp [K]; exact hK
  have hrec : kappaPrimeAt β Λ κ m (d + 1) =
      K + (9 / 80) * v ^ (2 * β) / K := by
    rw [kappaPrimeAt]
    change K + 9 * a β Λ (m + 1) ^ 2 * epsilon β Λ (m + 1) ^ 4 /
        (80 * K) = K + (9 / 80) * v ^ (2 * β) / K
    calc
      K + 9 * a β Λ (m + 1) ^ 2 * epsilon β Λ (m + 1) ^ 4 /
          (80 * K) =
        K + (9 / 80) *
          (a β Λ (m + 1) ^ 2 * epsilon β Λ (m + 1) ^ 4) / K := by ring
      _ = K + (9 / 80) * v ^ (2 * β) / K := by
        dsimp [v]
        rw [hterm]
  have hratio : (v / e ^ q β) ^ (β - gamma β) =
      v ^ (β - gamma β) / e ^ p := by
    dsimp [e, v, p]
    rw [Real.div_rpow hen.le (Real.rpow_nonneg he.le (q β)),
      ← Real.rpow_mul he.le, hgamma]
  change kappaPrimeAt β Λ κ m (d + 1) /
      epsilon β Λ m ^ p =
    (epsilon β Λ (m + 1) / epsilon β Λ m ^ q β) ^ (β - gamma β) *
      (epsilon β Λ (m + 1) ^ (2 * gamma β) *
        kappaPrimeNormalized β Λ κ (m + 1) d +
        (9 / 80) / kappaPrimeNormalized β Λ κ (m + 1) d)
  simp only [kappaPrimeNormalized]
  rw [hrec]
  change (K + (9 / 80) * v ^ (2 * β) / K) / e ^ p =
    (v / e ^ q β) ^ (β - gamma β) *
      (v ^ (2 * gamma β) * (K / v ^ p) + (9 / 80) / (K / v ^ p))
  rw [hratio]
  rw [show (9 : ℝ) / 80 / (K / v ^ p) =
      (9 / 80) * v ^ p / K by field_simp [ne_of_gt hK', ne_of_gt hv']]
  field_simp [ne_of_gt he', ne_of_gt hv', ne_of_gt hK']
  have hfirst : v ^ (β - gamma β) * v ^ (2 * gamma β) = v ^ p := by
    rw [← Real.rpow_add hv']
    congr 1
    dsimp [p]
    ring
  have hvsq : (v ^ p) ^ 2 = v ^ (2 * p) := by
    rw [← Real.rpow_natCast (v ^ p) 2, ← Real.rpow_mul hv'.le]
    congr 1
    norm_num1
    ring
  have hsecond : v ^ (β - gamma β) * (v ^ p) ^ 2 =
      v ^ (2 * β) * v ^ p := by
    rw [hvsq]
    calc
      v ^ (β - gamma β) * v ^ (2 * p) =
          v ^ ((β - gamma β) + 2 * p) := by rw [← Real.rpow_add hv']
      _ = v ^ (2 * β + p) := by
        congr 1
        dsimp [p]
        ring
      _ = v ^ (2 * β) * v ^ p := by rw [← Real.rpow_add hv']
  calc
    (K ^ 2 * 80 + 9 * v ^ (2 * β)) * v ^ p =
        80 * K ^ 2 * (v ^ (β - gamma β) * v ^ (2 * gamma β)) +
          9 * (v ^ (β - gamma β) * (v ^ p) ^ 2) := by
            rw [hfirst, hsecond]
            ring
    _ = v ^ (β - gamma β) *
        (K ^ 2 * 80 * v ^ (2 * gamma β) + 9 * (v ^ p) ^ 2) := by ring_nf

/-- A reciprocal-symmetric size that is invariant under the limiting map
`s ↦ (9/80)/s`. -/
def kappaPrimeNormalizedSize (β : ℝ) (Λ : ℕ) (κ : ℝ) (m d : ℕ) : ℝ :=
  max (kappaPrimeNormalized β Λ κ m d)
    ((9 / 80) / kappaPrimeNormalized β Λ κ m d)

/-- The multiplicative factor in one step of the normalized size estimate. -/
def kappaPrimeNormalizedStepFactor (β : ℝ) (Λ m : ℕ) : ℝ :=
  max ((epsilon β Λ (m + 1) / epsilon β Λ m ^ q β) ^
        (β - gamma β))
      (((epsilon β Λ (m + 1) / epsilon β Λ m ^ q β) ^
        (β - gamma β))⁻¹) *
    (1 + epsilon β Λ (m + 1) ^ (2 * gamma β))

theorem kappaPrimeNormalized_pos {β : ℝ} {Λ : ℕ} {κ : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hκ : 0 < κ)
    (m d : ℕ) : 0 < kappaPrimeNormalized β Λ κ m d := by
  unfold kappaPrimeNormalized
  exact div_pos (kappaPrimeAt_pos hβ hβ' hΛ hκ m d)
    (Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos hβ hβ' hΛ) _)

/-- One normalized recurrence step grows the reciprocal-symmetric size by
the scale-ratio factor and an `ε^(2γ)` perturbation. -/
theorem kappaPrimeNormalizedSize_step {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (hκ : 0 < κ) (m d : ℕ) :
    kappaPrimeNormalizedSize β Λ κ m (d + 1) ≤
      max ((epsilon β Λ (m + 1) / epsilon β Λ m ^ q β) ^
          (β - gamma β))
        (((epsilon β Λ (m + 1) / epsilon β Λ m ^ q β) ^
          (β - gamma β))⁻¹) *
        (1 + epsilon β Λ (m + 1) ^ (2 * gamma β)) *
        kappaPrimeNormalizedSize β Λ κ (m + 1) d := by
  let s := kappaPrimeNormalized β Λ κ (m + 1) d
  let u := epsilon β Λ (m + 1) ^ (2 * gamma β)
  let c : ℝ := 9 / 80
  let R := (epsilon β Λ (m + 1) / epsilon β Λ m ^ q β) ^
    (β - gamma β)
  let T := u * s + c / s
  let F := max R R⁻¹
  let Y := max s (c / s)
  have hs : 0 < s := by
    dsimp [s]
    exact kappaPrimeNormalized_pos hβ hβ' hΛ hκ (m + 1) d
  have hu : 0 ≤ u := by
    dsimp [u]
    exact Real.rpow_nonneg
      (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le _
  have hc : 0 < c := by norm_num [c]
  have hR : 0 < R := by
    dsimp [R]
    exact Real.rpow_pos_of_pos
      (div_pos (Infra.Cutoff.epsilon_pos hβ hβ' hΛ)
        (Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos hβ hβ' hΛ) _)) _
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hrec := kappaPrimeNormalized_step hβ hβ' hΛ hκ m d
  have hcur : kappaPrimeNormalized β Λ κ m (d + 1) = R * T := by
    dsimp [R, T, u, s, c]
    exact hrec
  have hYnonneg : 0 ≤ Y := by dsimp [Y]; positivity
  have hFnonneg : 0 ≤ F := by dsimp [F]; positivity
  have hsY : s ≤ Y := le_max_left _ _
  have hcsY : c / s ≤ Y := le_max_right _ _
  have hTupper : T ≤ (1 + u) * Y := by
    dsimp [T]
    calc
      u * s + c / s ≤ u * Y + Y :=
        add_le_add (mul_le_mul_of_nonneg_left hsY hu) hcsY
      _ = (1 + u) * Y := by ring
  have hTlower : c ≤ s * T := by
    dsimp [T]
    have hnonneg : 0 ≤ u * s ^ 2 := mul_nonneg hu (sq_nonneg s)
    have hsc : 0 < s := hs
    dsimp [c]
    field_simp [ne_of_gt hsc]
    nlinarith [hnonneg]
  have hcT : c / T ≤ s := (div_le_iff₀ hT).2 hTlower
  have hF_R : R ≤ F := le_max_left _ _
  have hF_inv : R⁻¹ ≤ F := le_max_right _ _
  have hfirst : R * T ≤ (F * (1 + u)) * Y := by
    calc
      R * T ≤ F * ((1 + u) * Y) :=
        mul_le_mul hF_R hTupper (by positivity) (by positivity)
      _ = (F * (1 + u)) * Y := by ring
  have hinvEq : c / (R * T) = R⁻¹ * (c / T) := by
    field_simp [ne_of_gt hR, ne_of_gt hT]
  have hsecond : c / (R * T) ≤ (F * (1 + u)) * Y := by
    rw [hinvEq]
    calc
      R⁻¹ * (c / T) ≤ F * Y :=
        mul_le_mul hF_inv (le_trans hcT hsY) (by positivity) (by positivity)
      _ ≤ (F * (1 + u)) * Y := by
        have hOne : 1 ≤ 1 + u := by linarith
        have hFone : F ≤ F * (1 + u) := by
          calc
            F = F * 1 := by ring
            _ ≤ F * (1 + u) := mul_le_mul_of_nonneg_left hOne hFnonneg
        exact mul_le_mul_of_nonneg_right hFone hYnonneg
  have hsize : kappaPrimeNormalizedSize β Λ κ m (d + 1) =
      max (R * T) (c / (R * T)) := by
    simp [kappaPrimeNormalizedSize, hcur, c]
  calc
    kappaPrimeNormalizedSize β Λ κ m (d + 1) =
        max (R * T) (c / (R * T)) := hsize
    _ ≤ (F * (1 + u)) * Y := max_le hfirst hsecond
    _ = max ((epsilon β Λ (m + 1) / epsilon β Λ m ^ q β) ^
          (β - gamma β))
        (((epsilon β Λ (m + 1) / epsilon β Λ m ^ q β) ^
          (β - gamma β))⁻¹) *
        (1 + epsilon β Λ (m + 1) ^ (2 * gamma β)) *
        kappaPrimeNormalizedSize β Λ κ (m + 1) d := by
          dsimp [F, u, Y, R, c, kappaPrimeNormalizedSize, s]

end AVenhance.Infra.Section3

end
