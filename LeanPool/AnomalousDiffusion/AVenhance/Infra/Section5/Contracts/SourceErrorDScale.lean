/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyExponent
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.DmFlowTgrad
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPairingAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SourceErrors

/-! # `SourceErrorDContract`: scale bookkeeping

The cutoff exponent budget `2δ + qβ ≤ δ Jcut / 2`, the `2δ` first-term scale at the terminal step,
the assembly of the `d_m` bound in paper-scale form, and the final conversion to
`ε_{m-1}^{2δ} √κ_m` (`e.monster.est.11.a.d`, `enhance.tex` 7860-7880). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section4

/-- Abstract-real core of the cutoff exponent budget: `10 δ + 16 q/3 ≤ δ N` for the `δ =
    (q-1)²/(4(q+1)(4q-1))` and `N ≥ 500/δ + 128 q²(q-1)`. -/
theorem sed_budget_core {q δ N : ℝ} (hq : 1 < q)
    (hδ : δ = (q - 1) ^ 2 / (4 * (q + 1) * (4 * q - 1)))
    (hN : 500 / δ + 128 * q ^ 2 * (q - 1) ≤ N) :
    10 * δ + 16 * q / 3 ≤ δ * N := by
  have hq1 : 0 < q - 1 := by linarith
  have hden : 0 < 4 * (q + 1) * (4 * q - 1) := by
    have : 0 < 4 * q - 1 := by linarith
    positivity
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hmul := mul_le_mul_of_nonneg_left hN hδpos.le
  have h500 : δ * (500 / δ) = 500 := by field_simp
  have hmain : 500 + δ * (128 * q ^ 2 * (q - 1)) ≤ δ * N := by
    calc 500 + δ * (128 * q ^ 2 * (q - 1)) = δ * (500 / δ + 128 * q ^ 2 * (q - 1)) := by
          rw [mul_add, h500]
      _ ≤ δ * N := hmul
  have hnn : 0 ≤ δ * (128 * q ^ 2 * (q - 1)) := by positivity
  have hδle : δ ≤ 1 / 16 := by
    rw [hδ, div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  by_cases hsmall : q ≤ 93
  · have : 16 * q / 3 ≤ 496 := by linarith
    linarith
  · replace hsmall := not_le.mp hsmall
    have hδ20 : 1 / 20 ≤ δ := by
      rw [hδ, div_le_div_iff₀ (by norm_num) hden]
      nlinarith
    have hpos : 0 ≤ 128 * q ^ 2 * (q - 1) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hδ20 hpos
    have h2 : 16 * q / 3 + 1 ≤ 1 / 20 * (128 * q ^ 2 * (q - 1)) := by nlinarith
    linarith

/-- The cutoff absorbs the lower bound `ε_m ≳ ε_{m-1}^q` and the extra `ε^{2δ}`:
`2δ + qβ ≤ δ J / 2`. -/
theorem sed_jcut_budget {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    2 * delta β + q β * β ≤ delta β * (Jcut β : ℝ) / 2 := by
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  have hd := Infra.Ingredients.delta_pos hβ hβ'
  have hδ := Infra.Ingredients.delta_eq_q_fraction hβ hβ'
  have hN1 := Infra.Ingredients.Nstar_ge_defining_real hβ hβ'
  have hN2 := Infra.Ingredients.Nstar_ge_eight_add_mul hβ hβ'
  have hsq : 0 ≤ 1 / (delta β) ^ 2 := by positivity
  have hN : 500 / delta β + 128 * q β ^ 2 * (q β - 1) ≤ (Nstar β : ℝ) := by
    obtain ⟨h1, h2, h3⟩ := Infra.Ingredients.Nstar_corrections_nonneg hβ hβ'
    rw [Infra.Ingredients.Nstar_eq_ceil]
    refine le_trans ?_ (Nat.le_ceil _)
    linarith
  have hcore := sed_budget_core hq hδ hN
  have hJ : (Nstar β : ℝ) ≤ 2 * (Jcut β : ℝ) + 2 := by
    have : Nstar β ≤ 2 * Jcut β + 2 := by unfold Jcut; omega
    exact_mod_cast this
  have hqb : q β * β ≤ 4 * q β / 3 := by
    have : 0 < q β := by linarith
    nlinarith
  have hmulJ := mul_le_mul_of_nonneg_left hJ hd.le
  nlinarith

/-- The first `d_m` term at the `2δ` exprat rate (the bound at the terminal step `m = M`,
where the `4δ` of the interior diffusivity display is not available). -/
theorem sed_first_scale
    {N : ℕ} {E δ Czeta Cprod Cexprat Cg Theta κprev B R G Khalf x : ℝ}
    (hE : 0 < E)
    (hCzeta : 0 ≤ Czeta) (hCprod : 0 ≤ Cprod)
    (hCg : 0 ≤ Cg) (hTheta : 0 ≤ Theta) (hκprev : 0 < κprev)
    (hRnonneg : 0 ≤ R) (hGnonneg : 0 ≤ G)
    (hKhalf : Khalf = Real.sqrt κprev * Theta)
    (hx : x = E ^ (δ / 2))
    (hProduct : B ≤ Cprod * κprev)
    (hExprat : R ≤ Cexprat * E ^ (2 * δ))
    (hG : G ≤ Cg * Theta / Real.sqrt κprev) :
    2 * ((4 * Real.pi ^ 2 * Czeta * (N : ℝ) * 2 ^ N) * B * R ^ N) * G ≤
      (2 * (4 * Real.pi ^ 2 * Czeta * (N : ℝ) * 2 ^ N) * Cprod * Cg) *
        Khalf * (Cexprat * x ^ 4) ^ N := by
  have hκ : 0 < Real.sqrt κprev := Real.sqrt_pos.2 hκprev
  have hKhalf0 : 0 ≤ Khalf := by rw [hKhalf]; positivity
  have hBG : B * G ≤ Cprod * Cg * Khalf := by
    calc
      B * G ≤ (Cprod * κprev) * G :=
        mul_le_mul_of_nonneg_right hProduct hGnonneg
      _ ≤ (Cprod * κprev) * (Cg * Theta / Real.sqrt κprev) :=
        mul_le_mul_of_nonneg_left hG (mul_nonneg hCprod hκprev.le)
      _ = Cprod * Cg * Khalf := by
        rw [hKhalf]
        field_simp [ne_of_gt hκ]
        rw [Real.sq_sqrt hκprev.le]
        ring
  have hpow4 : (E ^ (δ / 2)) ^ 4 = E ^ (2 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le]
    congr 1
    ring
  have hpow : R ^ N ≤ (Cexprat * x ^ 4) ^ N := by
    rw [hx, hpow4]
    exact pow_le_pow_left₀ hRnonneg hExprat N
  have hcoef : 0 ≤ 2 * (4 * Real.pi ^ 2 * Czeta * (N : ℝ) * 2 ^ N) := by
    positivity
  calc
    _ = (2 * (4 * Real.pi ^ 2 * Czeta * (N : ℝ) * 2 ^ N)) *
        (B * G) * R ^ N := by ring
    _ ≤ (2 * (4 * Real.pi ^ 2 * Czeta * (N : ℝ) * 2 ^ N)) *
        ((Cprod * Cg * Khalf) *
          (Cexprat * x ^ 4) ^ N) := by
      have hboth := mul_le_mul hBG hpow (pow_nonneg hRnonneg N)
        (mul_nonneg (mul_nonneg hCprod hCg) hKhalf0)
      calc
        _ = (2 * (4 * Real.pi ^ 2 * Czeta * (N : ℝ) * 2 ^ N)) *
            (B * G * R ^ N) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hboth hcoef
    _ = _ := by ring

/-- Assembly of the `d_m` bound from the pulled-gradient bound `G`, the tail tensor bound
`A`, and the scale data (product rate, `2δ` exprat rate, time ratio), in the paper-scale form
`C (√κ_{m-1} Θ) (C' ε_{m-1}^{δ/2})^{Jcut}`. -/
theorem sed_eLpNorm_le
    {β C₀ Csrc Cprod Cexpr Θ κprev A : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (hcutoff : I.Czeta ≤ C₀) (hκ : 0 < κ) (hκprev : 0 < κprev)
    (hC₀ : 0 ≤ C₀) (hCsrc : 0 ≤ Csrc) (hCprod : 0 ≤ Cprod)
    (hCexpr : 1 ≤ Cexpr) (hCzeta : 0 ≤ I.Czeta) (hΘ : 0 ≤ Θ)
    (hProduct : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ ≤ Cprod * κprev)
    (hExprat : epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) ≤
      Cexpr * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hTimeRatio : tau β I.Λ m / tauP β I.Λ m ≤
      (1 / 4) * epsilon β I.Λ (m - 1) ^ delta β)
    (hA : 0 ≤ A ∧ A ≤ Csrc * Θ *
      (epsilon β I.Λ m ^ 2 / κ) * (Real.sqrt κprev)⁻¹ *
      epsilon β I.Λ (m - 1) ^ (-(2 + gamma β)) *
      (tauP β I.Λ m)⁻¹ ^ Jcut β)
    (hflow : ∀ z : ℝ × Vec 2, ∀ l : ℤ, I.hatXiML m l z.1 ≠ 0 →
      ‖I.flowGrad hΦ m l z.1 z.2‖ ≤ 2)
    (hTgrad : eLpNorm (fun z : ℝ × Vec 2 => AVenhance.spaceGrad (T z.1) z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal (Θ / Real.sqrt κprev))
    (hfirstMeas : AEStronglyMeasurable
      (dmFrozenFluxFirst I hΦ m κ T)
      (volume.restrict AVenhance.timeCube))
    (hAmnr : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      eLpNorm (fun z : ℝ × Vec 2 =>
        I.Amnr hΦ m κ n T (AVenhance.Jcut β) z.1 z.2) 2
          (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal A)
    (hAentryMeas : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2,
        AEStronglyMeasurable (fun z : ℝ × Vec 2 =>
          I.Amnr hΦ m κ n T (AVenhance.Jcut β) z.1 z.2 i j k)
          (volume.restrict AVenhance.timeCube))
    (hCoordinateMeas : ∀ n ∈ Finset.range (AVenhance.Nstar β),
      ∀ i j k : Fin 2,
        AEStronglyMeasurable
          (dmFrozenTailCoordinateTerm I hΦ m κ T n i j k)
          (volume.restrict AVenhance.timeCube))
    (hratio : epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) ≤ 1)
    (hcut : 2 ≤ AVenhance.Jcut β) :
    eLpNorm (fun z : ℝ × Vec 2 => AVenhance.Infra.Section5.sourceErrorD I hΦ m κ T z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal
        (((2 * (4 * Real.pi ^ 2 * I.Czeta * (AVenhance.Nstar β : ℝ) *
              2 ^ AVenhance.Nstar β) * Cprod * 16) +
          (AVenhance.Nstar β : ℝ) * (8 * (4 * Real.pi ^ 2 * C₀) * Csrc * Cprod)) *
          (Real.sqrt κprev * Θ) *
          ((Cexpr ^ 3 + 2 + 1) * epsilon β I.Λ (m - 1) ^ (delta β / 2)) ^
            AVenhance.Jcut β) := by
  let E := epsilon β I.Λ (m - 1)
  let epsm := epsilon β I.Λ m
  let tauVal := AVenhance.tau β I.Λ m
  let tauPVal := AVenhance.tauP β I.Λ m
  let x := E ^ (delta β / 2)
  let Khalf := Real.sqrt κprev * Θ
  let G := 16 * Θ / Real.sqrt κprev
  let Couter := 2 * (4 * Real.pi ^ 2 * I.Czeta * (AVenhance.Nstar β : ℝ) *
    2 ^ AVenhance.Nstar β) * Cprod * 16
  let CA := 8 * (4 * Real.pi ^ 2 * C₀) * Csrc * Cprod
  have hE : 0 < E := by
    dsimp [E]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
      (m := m - 1)
  have hE1 : E ≤ 1 := by
    dsimp [E]
    exact Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m - 1)
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hγ : 0 ≤ gamma β :=
    (Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt).le
  have hepsm : 0 < epsm := by
    dsimp [epsm]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have htau : 0 < tauVal := by
    dsimp [tauVal]
    exact Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have htauP : 0 < tauPVal := by
    dsimp [tauPVal]
    exact Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hGnonneg : 0 ≤ G := by dsimp [G]; positivity
  have hGL : 4 * (2 : ℝ) ^ 2 * (Θ / Real.sqrt κprev) ≤ G := by
    dsimp [G]; apply le_of_eq; ring
  have hKhalf : Khalf = Real.sqrt κprev * Θ := rfl
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg hE.le _
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact Real.rpow_le_one hE.le hE1 (by positivity)
  have hRnonneg : 0 ≤ epsm ^ 2 / (κ * tauVal) := by positivity
  have hpower' := hm_dm_jcut_power_budget I.one_lt_beta I.beta_lt
  have hfirstScale := sed_first_scale
    (N := AVenhance.Nstar β) (E := E) (δ := delta β)
    (Czeta := I.Czeta) (Cprod := Cprod) (Cexprat := Cexpr)
    (Cg := 16) (Theta := Θ) (κprev := κprev)
    (B := a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ)
    (R := epsm ^ 2 / (κ * tauVal)) (G := G) (Khalf := Khalf) (x := x)
    hE hCzeta hCprod (by norm_num)
    hΘ hκprev hRnonneg hGnonneg hKhalf rfl hProduct
    (by simpa [epsm, tauVal, E] using hExprat) le_rfl
  have hAfac : 0 ≤ (2 : ℝ) := by norm_num
  have htailScale := dm_tail_scale_from_rate_bounds I m (AVenhance.Jcut β)
    (E := E) (δ := delta β) (γ := gamma β) (C₀ := C₀) (Csrc := Csrc)
    (Cprod := Cprod) (Theta := Θ) (κm := κ) (κprev := κprev)
    (epsm := epsm) (tau := tauVal) (tauP := tauPVal) (A := A)
    (Khalf := Khalf) (Afac := 2) (x := x)
    hE hE1 hδ hγ hC₀ hCsrc hCprod hΘ hκ hκprev hepsm htau htauP
    hKhalf rfl rfl hProduct (by simpa [tauVal, tauPVal, E] using hTimeRatio)
    hpower' hA
  have hCouter : 0 ≤ Couter := by dsimp [Couter]; positivity
  have hCA : 0 ≤ CA := by dsimp [CA]; positivity
  have hK : 0 ≤ Khalf := by dsimp [Khalf]; positivity
  have hAmnrA : 0 ≤ A := hA.1
  have hpaper := dm_frozenSource_paper_scale
    (C₀ := C₀) (A := A) (G := G) (Cexpr := Cexpr) (Couter := Couter)
    (Afac := 2) (CA := CA) (x := x) (Khalf := Khalf)
    I hΦ m κ T hcutoff hm hκ hAmnrA hGnonneg hratio
    hfirstMeas (by norm_num : (0 : ℝ) ≤ 2) hflow hTgrad hGL hAmnr hAentryMeas hCoordinateMeas hCexpr
    hCouter hAfac hCA hx0 hx1 hK hcut hfirstScale
    (by simpa [CA, Khalf, x, E] using htailScale)
  have hsource := sourceErrorD_eLpNorm_le_of_dmFrozenSource
    I hΦ m κ T hpaper
  simpa [Couter, CA, Khalf, x, E] using hsource

/-- Abstract-real final scale: the `Jcut`-th power of `C x^{δ/2}` times `√κ_{m-1} Θ` is at most a
constant times `x^{2δ} √κ_m`. -/
theorem sed_final_scale {x εm κm κp K Θ Cb δ q β : ℝ} {J : ℕ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hεm : 0 < εm) (hκm : 0 < κm) (hκp : 0 < κp) (hK : 1 ≤ K)
    (hκpK : κp ≤ K) (hβ : 0 < β) (hpow : x ^ q ≤ 2 * εm) (hε : εm ^ (2 * β) ≤ K * κp * κm)
    (hE : 2 * δ + q * β ≤ δ * (J : ℝ) / 2) (hΘ : 0 ≤ Θ) (hCb : 0 ≤ Cb) :
    Real.sqrt κp * Θ * (Cb * x ^ (δ / 2)) ^ J ≤
      (Θ * Cb ^ J * 2 ^ β * K * Real.sqrt K) * x ^ (2 * δ) * Real.sqrt κm := by
  have hxJ : (x ^ (δ / 2)) ^ J = x ^ (δ * (J : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  have hY : 0 ≤ Θ * Cb ^ J := by positivity
  have hZ := sc_Z_core hx0 hx1 hεm hκm hκp hK hκpK hβ hpow hε hE hY
  calc Real.sqrt κp * Θ * (Cb * x ^ (δ / 2)) ^ J
      = Real.sqrt κp * ((Θ * Cb ^ J) * x ^ (δ * (J : ℝ) / 2)) := by
        rw [mul_pow, hxJ]; ring
    _ ≤ _ := hZ

end AVenhance.Infra.Section5.Contracts

end
