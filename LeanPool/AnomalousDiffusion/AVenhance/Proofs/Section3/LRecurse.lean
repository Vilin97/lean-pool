/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaAtPrimeScaleComparison

/-! Proof of the statement for the corrected of `l_recurse`. -/

@[expose] public section

noncomputable section

namespace AVenhance.Proofs

open AVenhance

theorem LRecurse.kappaPrimeUniformConstant_ge_one {β : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) :
    1 ≤ Infra.Section3.kappaPrimeUniformConstant β := by
  have hsuper : 0 ≤ Infra.Ingredients.supergeoConstant β := by
    dsimp [Infra.Ingredients.supergeoConstant]
    have hq := Infra.Ingredients.one_lt_q hβ hβ'
    positivity
  have herr : 0 ≤ Infra.Section3.kappaPrimeRatioError β := by
    unfold Infra.Section3.kappaPrimeRatioError
    exact add_nonneg (mul_nonneg (by norm_num) hsuper)
      (div_nonneg (sq_nonneg _) (by norm_num))
  have hend : 2 ≤ Infra.Section3.kappaPrimeEndpointConstant β := by
    unfold Infra.Section3.kappaPrimeEndpointConstant
    apply le_trans _ (le_max_left _ _)
    nlinarith [herr]
  have hγ := Infra.Ingredients.gamma_pos hβ hβ'
  have hr : (128 : ℝ) ^ (-2 * gamma β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
  have hden : 0 < 1 - (128 : ℝ) ^ (-2 * gamma β) := sub_pos.mpr hr
  have harg : 0 ≤ max (Infra.Section3.kappaPrimeRatioError β) 50 *
      (128 / 127) + 1 / (1 - (128 : ℝ) ^ (-2 * gamma β)) := by
    positivity
  have hexp : 1 ≤ Real.exp
      (max (Infra.Section3.kappaPrimeRatioError β) 50 *
        (128 / 127) + 1 / (1 - (128 : ℝ) ^ (-2 * gamma β))) :=
    Real.one_le_exp_iff.mpr harg
  unfold Infra.Section3.kappaPrimeUniformConstant
  calc
    1 ≤ 2 := by norm_num
    _ ≤ Infra.Section3.kappaPrimeEndpointConstant β := hend
    _ ≤ Infra.Section3.kappaPrimeEndpointConstant β *
        Real.exp (max (Infra.Section3.kappaPrimeRatioError β) 50 *
          (128 / 127) + 1 / (1 - (128 : ℝ) ^ (-2 * gamma β))) :=
      calc
        Infra.Section3.kappaPrimeEndpointConstant β =
            1 * Infra.Section3.kappaPrimeEndpointConstant β := by ring
        _ ≤ Real.exp (max (Infra.Section3.kappaPrimeRatioError β) 50 *
              (128 / 127) + 1 / (1 - (128 : ℝ) ^ (-2 * gamma β))) *
            Infra.Section3.kappaPrimeEndpointConstant β :=
          mul_le_mul_of_nonneg_right hexp (by linarith)
        _ = Infra.Section3.kappaPrimeEndpointConstant β *
            Real.exp (max (Infra.Section3.kappaPrimeRatioError β) 50 *
              (128 / 127) + 1 / (1 - (128 : ℝ) ^ (-2 * gamma β))) := by ring

private theorem l_recurse_branch1 :
  ∀ (β C₀ R : ℝ), (∀ (I : Ingredients β), I.Czeta ≤ C₀ → I.Chat ≤ C₀ → ∀ (κ : ℝ), (0 : ℝ) < κ →
    ∀ (M : ℕ), (1 : ℕ) ≤ M → κ ∈ permittedInterval β I.Λ M → ∀ (m : ℕ), (1 : ℕ) ≤ m → m ≤ M →
    max (I.kappaAt κ m (M - m) / Infra.Section3.kappaPrimeAt β I.Λ κ m (M - m))
    (Infra.Section3.kappaPrimeAt β I.Λ κ m (M - m) / I.kappaAt κ m (M - m)) ≤ R) →
  let U : ℝ := Infra.Section3.kappaPrimeUniformConstant β;
  let clo : ℝ := (1 / 2 : ℝ) ^ ((2 : ℝ) - β - gamma β) / (U * (2 : ℝ) ^ (-28 : ℤ));
  let chi : ℝ := ((1 : ℝ) + Infra.Ingredients.supergeoConstant β / (128 : ℝ)) ^ ((2 : ℝ) - β -
    gamma β) / ((9 / 80 : ℝ) / U * (2 : ℝ) ^ (-33 : ℤ));
  let cScale : ℝ := (9 / 80 : ℝ) / U / R;
  let cExprat : ℝ := clo / R;
  let c : ℝ := min cScale cExprat;
  let C : ℝ := max (R * U) (R * chi);
  (0 : ℝ) < R → ∀ (I : Ingredients β), I.Czeta ≤ C₀ → I.Chat ≤ C₀ → ∀ (κ : ℝ) (M : ℕ), (1 : ℕ) ≤
    M → κ ∈ permittedInterval β I.Λ M → (0 : ℝ) < κ → (∀ (m : ℕ), (0 : ℝ) < I.kappaAt κ m (M -
    m)) → ∀ (m : ℕ), (2 : ℕ) ≤ m → m < M → c * epsilon β I.Λ (m - (1 : ℕ)) ^ ((4 : ℝ) * delta β)
    ≤ epsilon β I.Λ m ^ (2 : ℕ) / (I.kappaAt κ m (M - m) * tau β I.Λ m) ∧ epsilon β I.Λ m ^ (2 :
    ℕ) / (I.kappaAt κ m (M - m) * tau β I.Λ m) ≤ C * epsilon β I.Λ (m - (1 : ℕ)) ^ ((4 : ℝ) *
    delta β)
    := by
  intro β C₀ R hratio U clo chi cScale cExprat c C hRpos I hCz hCh κ M hM hpermitted hκ hκatPos m
      hm hmM
  let k := I.kappaAt κ m (M - m)
  let kp := Infra.Section3.kappaPrimeAt β I.Λ κ m (M - m)
  let ep := epsilon β I.Λ (m - 1)
  let e := epsilon β I.Λ m
  let t := tau β I.Λ m
  let F := ep ^ (4 * delta β)
  let xp := e ^ 2 / (kp * t)
  let x := e ^ 2 / (k * t)
  have hkpos : 0 < k := by dsimp [k]; exact hκatPos m
  have hkpPos : 0 < kp := by
    dsimp [kp]
    exact Infra.Section3.kappaPrimeAt_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le hκ m (M - m)
  have hep : 0 < ep := by
    dsimp [ep]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he : 0 < e := by
    dsimp [e]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ht : 0 < t := I.tau_pos' m
  have hF : 0 < F := by dsimp [F]; exact Real.rpow_pos_of_pos hep _
  have hxp : 0 < xp := by dsimp [xp]; positivity
  have hcomp := hratio I hCz hCh κ hκ M hM hpermitted m
    (by omega : 1 ≤ m) (by omega : m ≤ M)
  have hactualOverPrime' := (max_le_iff.mp hcomp).1
  have hprimeOverActual' := (max_le_iff.mp hcomp).2
  have hpexpr := Infra.Section3.kappaPrimeAt_exprat_bounds
    I.one_lt_beta I.beta_lt I.two_pow_seven_le hκ hpermitted hm
      (by omega : m < M)
  have hpexpr' : clo * F ≤ xp ∧ xp ≤ chi * F := by
    simpa [clo, chi, U, ep, e, t, kp, xp, F] using hpexpr
  have hfactorLo : 1 / R ≤ kp / k := by
    have h := one_div_le_one_div_of_le (div_pos hkpos hkpPos)
      hactualOverPrime'
    calc
      1 / R ≤ 1 / (k / kp) := h
      _ = kp / k := by field_simp
  have hidentity : x = xp * (kp / k) := by
    dsimp [x, xp, e, kp, k]
    field_simp [ne_of_gt hkpos, ne_of_gt hkpPos, ne_of_gt ht]
    apply (div_eq_div_iff (ne_of_gt hkpos)
      (mul_ne_zero (ne_of_gt hkpos) (ne_of_gt hkpPos))).2
    ring
  constructor
  · calc
      c * F ≤ cExprat * F :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hF.le
      _ = (clo * F) / R := by dsimp [cExprat]; ring
      _ ≤ xp / R := div_le_div_of_nonneg_right hpexpr'.1 hRpos.le
      _ = xp * (1 / R) := by ring
      _ ≤ xp * (kp / k) := mul_le_mul_of_nonneg_left hfactorLo hxp.le
      _ = x := hidentity.symm
  · have hfactorHi : kp / k ≤ R := hprimeOverActual'
    calc
      x = xp * (kp / k) := hidentity
      _ ≤ xp * R := mul_le_mul_of_nonneg_left hfactorHi hxp.le
      _ ≤ (R * chi) * F := by
        calc
          xp * R ≤ (chi * F) * R :=
            mul_le_mul_of_nonneg_right hpexpr'.2 hRpos.le
          _ = (R * chi) * F := by ring
      _ ≤ C * F :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hF.le

/-- The theorem with the corrected `4δ` exprat exponent. -/
theorem l_recurse (β C₀ : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
        ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
        ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
          (∀ m : ℕ, 1 ≤ m → m < M →
            c * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β)) ≤
                I.kappaAt κ m (M - m) ∧
            I.kappaAt κ m (M - m) ≤
                C * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β))) ∧
          (∀ m : ℕ, 2 ≤ m → m < M →
            c * epsilon β I.Λ (m - 1) ^ (4 * delta β) ≤
              epsilon β I.Λ m ^ 2 /
                (I.kappaAt κ m (M - m) * tau β I.Λ m) ∧
            epsilon β I.Λ m ^ 2 /
                (I.kappaAt κ m (M - m) * tau β I.Λ m) ≤
              C * epsilon β I.Λ (m - 1) ^ (4 * delta β)) := by
  classical
  by_cases hfeasible : ∃ I : Ingredients β,
      I.Czeta ≤ C₀ ∧ I.Cxi ≤ C₀ ∧ I.Chat ≤ C₀
  · obtain ⟨I₀, hCz₀, hCxi₀, hCh₀⟩ := hfeasible
    have hβ := I₀.one_lt_beta
    have hβ' := I₀.beta_lt
    have hC₀ : 0 ≤ C₀ :=
      le_trans (by linarith [I₀.one_le_Czeta]) hCz₀
    obtain ⟨R, hR, hratio⟩ :=
      Infra.Section3.kappaAt_kappaPrime_uniform_ratio_bound hβ hβ' hC₀
    let U := Infra.Section3.kappaPrimeUniformConstant β
    let clo := ((1 / 2 : ℝ) ^ (2 - β - gamma β)) /
      (U * (2 : ℝ) ^ (-28 : ℤ))
    let chi := (1 + Infra.Ingredients.supergeoConstant β / 128) ^
      (2 - β - gamma β) /
      ((9 / 80 / U) * (2 : ℝ) ^ (-33 : ℤ))
    let cScale := (9 / 80 / U) / R
    let cExprat := clo / R
    let c := min cScale cExprat
    let C := max (R * U) (R * chi)
    have hUpos : 0 < U :=
      Infra.Section3.kappaPrimeUniformConstant_pos hβ hβ'
    have hUge : 1 ≤ U := by simpa [U] using
      LRecurse.kappaPrimeUniformConstant_ge_one hβ hβ'
    have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
    have hsuper : 0 ≤ Infra.Ingredients.supergeoConstant β := by
      dsimp [Infra.Ingredients.supergeoConstant]
      have hq := Infra.Ingredients.one_lt_q hβ hβ'
      positivity
    have hclo : 0 < clo := by
      dsimp [clo]
      apply div_pos
      · exact Real.rpow_pos_of_pos (by norm_num) _
      · positivity
    have hchi : 0 < chi := by
      dsimp [chi]
      apply div_pos
      · exact Real.rpow_pos_of_pos (by positivity) _
      · positivity
    have hcScale : 0 < cScale := by
      dsimp [cScale]
      positivity
    have hcExprat : 0 < cExprat := by
      dsimp [cExprat]
      exact div_pos hclo hRpos
    have hc : 0 < c := by
      dsimp [c]
      exact lt_min hcScale hcExprat
    have hUtwo : 2 ≤ U := by
      have herr : 0 ≤ Infra.Section3.kappaPrimeRatioError β := by
        unfold Infra.Section3.kappaPrimeRatioError
        exact add_nonneg (mul_nonneg (by norm_num) hsuper)
          (div_nonneg (sq_nonneg _) (by norm_num))
      have hend : 2 ≤ Infra.Section3.kappaPrimeEndpointConstant β := by
        unfold Infra.Section3.kappaPrimeEndpointConstant
        apply le_trans _ (le_max_left _ _)
        nlinarith [herr]
      have hγ := Infra.Ingredients.gamma_pos hβ hβ'
      have hr : (128 : ℝ) ^ (-2 * gamma β) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
      have hden : 0 < 1 - (128 : ℝ) ^ (-2 * gamma β) := sub_pos.mpr hr
      have harg : 0 ≤ max (Infra.Section3.kappaPrimeRatioError β) 50 *
          (128 / 127) + 1 / (1 - (128 : ℝ) ^ (-2 * gamma β)) := by
        positivity
      have hexp : 1 ≤ Real.exp
          (max (Infra.Section3.kappaPrimeRatioError β) 50 *
            (128 / 127) + 1 / (1 - (128 : ℝ) ^ (-2 * gamma β))) :=
        Real.one_le_exp_iff.mpr harg
      dsimp [U, Infra.Section3.kappaPrimeUniformConstant]
      calc
        2 ≤ Infra.Section3.kappaPrimeEndpointConstant β := hend
        _ ≤ Real.exp (max (Infra.Section3.kappaPrimeRatioError β) 50 *
              (128 / 127) + 1 / (1 - (128 : ℝ) ^ (-2 * gamma β))) *
            Infra.Section3.kappaPrimeEndpointConstant β :=
          calc
            Infra.Section3.kappaPrimeEndpointConstant β =
                1 * Infra.Section3.kappaPrimeEndpointConstant β := by ring
            _ ≤ Real.exp (max (Infra.Section3.kappaPrimeRatioError β) 50 *
                  (128 / 127) + 1 / (1 - (128 : ℝ) ^ (-2 * gamma β))) *
                Infra.Section3.kappaPrimeEndpointConstant β :=
              mul_le_mul_of_nonneg_right hexp (by linarith)
        _ = Infra.Section3.kappaPrimeEndpointConstant β *
            Real.exp (max (Infra.Section3.kappaPrimeRatioError β) 50 *
              (128 / 127) + 1 / (1 - (128 : ℝ) ^ (-2 * gamma β))) := by ring
    have hUR : 1 ≤ U * R := by
      have hdiff : 0 ≤ (U - 1) * (R - 1) :=
        mul_nonneg (sub_nonneg.mpr hUge) (sub_nonneg.mpr hR)
      nlinarith
    have hcScaleSmall : cScale ≤ 9 / 80 := by
      have heq : cScale = (9 / 80 : ℝ) / (U * R) := by
        dsimp [cScale]
        ring
      rw [heq]
      apply (div_le_iff₀ (by positivity : 0 < U * R)).2
      nlinarith [hUR]
    have hCge : 2 ≤ C := by
      have hRU : 2 ≤ R * U := by
        calc
          2 ≤ U := hUtwo
          _ ≤ R * U := by
            calc
              U = 1 * U := by ring
              _ ≤ R * U := mul_le_mul_of_nonneg_right hR hUpos.le
      exact le_trans hRU (le_max_left _ _)
    have hcC : c < C := by
      have hcsmall : c ≤ 9 / 80 := by
        dsimp [c]
        exact (min_le_left _ _).trans hcScaleSmall
      linarith
    refine ⟨c, C, hc, hcC, ?_⟩
    intro I hCz hCxi hCh κ _hPerm M hM hpermitted
    have hκ : 0 < κ := by
      have hε : 0 < epsilon β I.Λ M :=
        Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
      have hq : 0 < q β :=
        lt_trans (by norm_num) (Infra.Ingredients.one_lt_q I.one_lt_beta I.beta_lt)
      have hexp : 0 < 2 * β / (q β + 1) := by positivity
      have hleft : 0 < (1 / 2 : ℝ) *
          epsilon β I.Λ M ^ (2 * β / (q β + 1)) := by positivity
      exact lt_of_lt_of_le hleft hpermitted.1
    have hκatPos (m : ℕ) : 0 < I.kappaAt κ m (M - m) :=
      Infra.Section3.kappaAt_pos I hκ m (M - m)
    constructor
    · intro m hm hmM
      let k := I.kappaAt κ m (M - m)
      let kp := Infra.Section3.kappaPrimeAt β I.Λ κ m (M - m)
      let s := a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β)
      have hkpos : 0 < k := by dsimp [k]; exact hκatPos m
      have hkpPos : 0 < kp := by
        dsimp [kp]
        exact Infra.Section3.kappaPrimeAt_pos I.one_lt_beta I.beta_lt
          I.two_pow_seven_le hκ m (M - m)
      have hs : 0 < s := by
        dsimp [s]
        exact mul_pos
          (Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
          (Real.rpow_pos_of_pos
            (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) _)
      have hscale := Infra.Section3.kappaPrimeAt_uniform_bounds
        I.one_lt_beta I.beta_lt I.two_pow_seven_le hκ hpermitted hm
          (by omega : m < M)
      have hcomp := hratio I hCz hCh κ hκ M hM hpermitted m hm
        (by omega : m ≤ M)
      have hactualOverPrime' := (max_le_iff.mp hcomp).1
      have hprimeOverActual' := (max_le_iff.mp hcomp).2
      constructor
      · calc
          c * s ≤ cScale * s :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le
          _ = ((9 / 80 / U) * s) / R := by dsimp [cScale]; ring
          _ ≤ kp / R := div_le_div_of_nonneg_right hscale.1 hRpos.le
          _ ≤ k := by
            apply (div_le_iff₀ hRpos).2
            simpa [mul_comm] using (div_le_iff₀ hkpos).1 hprimeOverActual'
      · calc
          k ≤ R * kp := (div_le_iff₀ hkpPos).1 hactualOverPrime'
          _ ≤ R * (U * s) := mul_le_mul_of_nonneg_left hscale.2 hRpos.le
          _ = (R * U) * s := by ring
          _ ≤ C * s :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hs.le
    · exact @l_recurse_branch1 β C₀ R hratio hRpos I hCz hCh κ M hM hpermitted hκ hκatPos
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    intro I hCz hCxi hCh κ _hPerm M hM hpermitted
    exfalso
    exact hfeasible ⟨I, hCz, hCxi, hCh⟩

end AVenhance.Proofs

end
