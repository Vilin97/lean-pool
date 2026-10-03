/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaAtPrimeBootstrap

/-! Uniform comparison of the κ chain with κ′.  The high scales use
the summable averaging loss; only the finitely many lower scales use the
coarse flux cap. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance

theorem KappaAtPrimeScaleComparison.kappaAtPrime_ratio_high {β C₀ : ℝ}
    (I : Ingredients β) (hCz : I.Czeta ≤ C₀) (hCh : I.Chat ≤ C₀)
    {κ : ℝ} (hκ : 0 < κ) {M N : ℕ}
    (hpermitted : κ ∈ permittedInterval β I.Λ M)
    (hN : 1 ≤ N)
    (hTail : kappaAtBootstrapTail β
      (kappaAtBootstrapErrorCoefficient β C₀ 2) N ≤ 1 / 2) :
    ∀ m d, m + d = M → N ≤ m →
      max (I.kappaAt κ m d / kappaPrimeAt β I.Λ κ m d)
        (kappaPrimeAt β I.Λ κ m d / I.kappaAt κ m d) ≤
          (1 - kappaAtBootstrapTail β
            (kappaAtBootstrapErrorCoefficient β C₀ 2) m)⁻¹ := by
  have hC₀ : 0 ≤ C₀ := le_trans (by linarith [I.one_le_Czeta]) hCz
  have hE : 0 < kappaAtBootstrapErrorCoefficient β C₀ 2 :=
    kappaAtBootstrapErrorCoefficient_pos I.one_lt_beta I.beta_lt hC₀
      (by norm_num)
  have hden : 0 < 1 - (128 : ℝ) ^ (-delta β) := by
    have hδ := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
    have hr : (128 : ℝ) ^ (-delta β) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact sub_pos.mpr hr
  intro m d
  induction d generalizing m with
  | zero =>
      intro hmD hmN
      have hmM : m = M := by omega
      subst M
      have htail := kappaAtBootstrapTail_le_half_of_index I.one_lt_beta
        I.beta_lt hE hTail hmN
      have htail0 := kappaAtBootstrapTail_nonneg I.one_lt_beta I.beta_lt hE.le m
      have hinv : 1 ≤
          (1 - kappaAtBootstrapTail β
            (kappaAtBootstrapErrorCoefficient β C₀ 2) m)⁻¹ := by
        have hdenm : 0 < 1 - kappaAtBootstrapTail β
            (kappaAtBootstrapErrorCoefficient β C₀ 2) m := by linarith
        rw [← one_div]
        apply (le_div_iff₀ hdenm).2
        linarith
      simpa [Ingredients.kappaAt, kappaPrimeAt, hκ.ne'] using hinv
  | succ d ih =>
      intro hmD hmN
      let j := m + 1
      let R := (1 - kappaAtBootstrapTail β
        (kappaAtBootstrapErrorCoefficient β C₀ 2) j)⁻¹
      have hjN : N ≤ j := by dsimp [j]; omega
      have hprev := ih j (by dsimp [j]; omega) hjN
      have htailm := kappaAtBootstrapTail_le_half_of_index I.one_lt_beta
        I.beta_lt hE hTail hmN
      have htailj := kappaAtBootstrapTail_le_half_of_index I.one_lt_beta
        I.beta_lt hE hTail hjN
      have htailm0 := kappaAtBootstrapTail_nonneg I.one_lt_beta I.beta_lt hE.le m
      have htailj0 := kappaAtBootstrapTail_nonneg I.one_lt_beta I.beta_lt hE.le j
      have hRpos : 0 < R := by
        dsimp [R]
        have hdenj : 0 < 1 - kappaAtBootstrapTail β
            (kappaAtBootstrapErrorCoefficient β C₀ 2) j := by linarith
        positivity
      have hRge : 1 ≤ R := by
        dsimp [R]
        have hdenj : 0 < 1 - kappaAtBootstrapTail β
            (kappaAtBootstrapErrorCoefficient β C₀ 2) j := by linarith
        rw [← one_div]
        apply (le_div_iff₀ hdenj).2
        linarith
      have hRle : R ≤ 2 := by
        dsimp [R]
        have hdenj : 0 < 1 - kappaAtBootstrapTail β
            (kappaAtBootstrapErrorCoefficient β C₀ 2) j := by linarith
        rw [← one_div]
        apply (div_le_iff₀ hdenj).2
        linarith
      have hprev' :
          max (I.kappaAt κ j (M - j) /
              kappaPrimeAt β I.Λ κ j (M - j))
            (kappaPrimeAt β I.Λ κ j (M - j) /
              I.kappaAt κ j (M - j)) ≤ R := by
        have hd : M - j = d := by dsimp [j]; omega
        simpa [R, hd] using hprev
      have hcoef : kappaAtBootstrapErrorCoefficient β C₀ R ≤
          kappaAtBootstrapErrorCoefficient β C₀ 2 :=
        kappaAtBootstrap_errorCoefficient_mono I.one_lt_beta I.beta_lt hC₀ hRle
      have hε := epsilon_delta_le_geometric I.one_lt_beta I.beta_lt
        I.two_pow_seven_le m
      have hη : kappaAtBootstrapErrorCoefficient β C₀ R *
          epsilon β I.Λ m ^ delta β ≤
        kappaAtBootstrapErrorCoefficient β C₀ 2 *
          ((128 : ℝ) ^ (-delta β)) ^ m := by
        calc
          kappaAtBootstrapErrorCoefficient β C₀ R *
              epsilon β I.Λ m ^ delta β ≤
          kappaAtBootstrapErrorCoefficient β C₀ 2 *
              epsilon β I.Λ m ^ delta β :=
                mul_le_mul_of_nonneg_right hcoef
                  (Real.rpow_nonneg
                    (le_of_lt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
                      I.two_pow_seven_le)) _)
          _ ≤ _ := mul_le_mul_of_nonneg_left hε hE.le
      have hηtail : kappaAtBootstrapErrorCoefficient β C₀ R *
          epsilon β I.Λ m ^ delta β ≤
          kappaAtBootstrapTail β
            (kappaAtBootstrapErrorCoefficient β C₀ 2) m := by
        let x := kappaAtBootstrapErrorCoefficient β C₀ 2 *
          ((128 : ℝ) ^ (-delta β)) ^ m
        have hx : 0 ≤ x := by dsimp [x]; positivity
        have hr0 : 0 ≤ (128 : ℝ) ^ (-delta β) := by positivity
        have hfrac : x ≤ x / (1 - (128 : ℝ) ^ (-delta β)) := by
          apply (le_div_iff₀ hden).2
          nlinarith [mul_nonneg hx hr0]
        change kappaAtBootstrapErrorCoefficient β C₀ R *
            epsilon β I.Λ m ^ delta β ≤
          x / (1 - (128 : ℝ) ^ (-delta β))
        exact hη.trans hfrac
      have hηlt : kappaAtBootstrapErrorCoefficient β C₀ R *
          epsilon β I.Λ m ^ delta β < 1 := by
        have hsmall := hηtail.trans htailm
        linarith
      have hstep := kappaAtBootstrap_averaged_step I hCz hCh hκ
        hpermitted (by dsimp [j]; omega) (by dsimp [j]; omega)
        hRge hprev' hηlt
      have hd : M - j = d := by dsimp [j]; omega
      have hstep' :
          max (I.KhomScalar (I.kappaAt κ j d) j /
              (kappaPrimeAt β I.Λ κ j d +
                (9 / 80 : ℝ) *
                  (a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4) /
                    kappaPrimeAt β I.Λ κ j d))
            ((kappaPrimeAt β I.Λ κ j d +
                (9 / 80 : ℝ) *
                  (a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4) /
                    kappaPrimeAt β I.Λ κ j d) /
              I.KhomScalar (I.kappaAt κ j d) j) ≤
            R / (1 - kappaAtBootstrapErrorCoefficient β C₀ R *
              epsilon β I.Λ m ^ delta β) := by
        simpa [j, hd] using hstep
      have hactualRec : I.kappaAt κ m (d + 1) =
          I.KhomScalar (I.kappaAt κ j d) j := by
        dsimp [j]
        rw [Ingredients.kappaAt]
      have hprimeRec : kappaPrimeAt β I.Λ κ m (d + 1) =
          kappaPrimeAt β I.Λ κ j d +
            (9 / 80 : ℝ) *
              (a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4) /
                kappaPrimeAt β I.Λ κ j d := by
        dsimp [j]
        rw [kappaPrimeAt]
        ring
      have hcoefPos := kappaAtBootstrapErrorCoefficient_pos I.one_lt_beta I.beta_lt
        hC₀ hRge
      have hη0 : 0 ≤ kappaAtBootstrapErrorCoefficient β C₀ R *
          epsilon β I.Λ m ^ delta β :=
        mul_nonneg hcoefPos.le (Real.rpow_nonneg
          (le_of_lt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
            I.two_pow_seven_le)) _)
      have htailStep := kappaAtBootstrapTail_step_bound I.one_lt_beta I.beta_lt
        hE htailm hη0 hη
      calc
        max (I.kappaAt κ m (d + 1) / kappaPrimeAt β I.Λ κ m (d + 1))
            (kappaPrimeAt β I.Λ κ m (d + 1) / I.kappaAt κ m (d + 1)) ≤
          R / (1 - kappaAtBootstrapErrorCoefficient β C₀ R *
              epsilon β I.Λ m ^ delta β) := by
                rw [hactualRec, hprimeRec]
                exact hstep'
        _ ≤ (1 - kappaAtBootstrapTail β
            (kappaAtBootstrapErrorCoefficient β C₀ 2) m)⁻¹ := by
              simpa [R] using htailStep

theorem KappaAtPrimeScaleComparison.kappaAtPrime_ratio_low_segment {β C₀ : ℝ}
    (I : Ingredients β) (hCz : I.Czeta ≤ C₀) (hCh : I.Chat ≤ C₀)
    {κ : ℝ} (hκ : 0 < κ) {M base : ℕ}
    (hpermitted : κ ∈ permittedInterval β I.Λ M)
    (hbaseM : base ≤ M)
    (hbaseRatio : max
      (I.kappaAt κ base (M - base) /
        kappaPrimeAt β I.Λ κ base (M - base))
      (kappaPrimeAt β I.Λ κ base (M - base) /
        I.kappaAt κ base (M - base)) ≤ 2) :
    ∀ m k, m + k = base → 1 ≤ m →
      max (I.kappaAt κ m (M - m) / kappaPrimeAt β I.Λ κ m (M - m))
        (kappaPrimeAt β I.Λ κ m (M - m) / I.kappaAt κ m (M - m)) ≤
          kappaAtBootstrapIteratedBound β C₀ k := by
  intro m k
  induction k generalizing m with
  | zero =>
      intro hmk hm
      have hmEq : m = base := by omega
      subst m
      simpa [kappaAtBootstrapIteratedBound] using hbaseRatio
  | succ k ih =>
      intro hmk hm
      let j := m + 1
      let R := kappaAtBootstrapIteratedBound β C₀ k
      have hjk : j + k = base := by dsimp [j]; omega
      have hj : 1 ≤ j := by dsimp [j]; omega
      have hj2 : 2 ≤ j := by dsimp [j]; omega
      have hjM : j ≤ M := by dsimp [j]; omega
      have hprev := ih j hjk hj
      have hR : 1 ≤ R := by
        dsimp [R]
        exact le_trans (by norm_num : (1 : ℝ) ≤ 2)
          (kappaAtBootstrapIteratedBound_ge_two (β := β) (C₀ := C₀) k)
      have hstep := kappaAtBootstrap_one_step I hCz hCh hκ hpermitted
        hj2 hjM hR hprev
      have hd : M - j + 1 = M - m := by dsimp [j]; omega
      have hactualRec : I.kappaAt κ m (M - m) =
          I.KhomScalar (I.kappaAt κ j (M - j)) j := by
        rw [← hd, Ingredients.kappaAt]
      have hprimeRec : kappaPrimeAt β I.Λ κ m (M - m) =
          kappaPrimeAt β I.Λ κ j (M - j) +
            (9 / 80 : ℝ) *
              (a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4) /
                kappaPrimeAt β I.Λ κ j (M - j) := by
        rw [← hd, kappaPrimeAt]
        simp [j]
        ring
      have hstep' : max
          (I.KhomScalar (I.kappaAt κ j (M - j)) j /
            (kappaPrimeAt β I.Λ κ j (M - j) +
              (9 / 80 : ℝ) *
                (a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4) /
                  kappaPrimeAt β I.Λ κ j (M - j)))
          ((kappaPrimeAt β I.Λ κ j (M - j) +
              (9 / 80 : ℝ) *
                (a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4) /
                  kappaPrimeAt β I.Λ κ j (M - j)) /
            I.KhomScalar (I.kappaAt κ j (M - j)) j) ≤
          R * kappaAtBootstrapStepFactor β C₀ R := by
        simpa [R] using hstep
      have hboundEq : kappaAtBootstrapIteratedBound β C₀ (k + 1) =
          R * kappaAtBootstrapStepFactor β C₀ R := by
        rfl
      calc
        max (I.kappaAt κ m (M - m) / kappaPrimeAt β I.Λ κ m (M - m))
            (kappaPrimeAt β I.Λ κ m (M - m) / I.kappaAt κ m (M - m)) ≤
          R * kappaAtBootstrapStepFactor β C₀ R := by
            rw [hactualRec, hprimeRec]
            exact hstep'
        _ = kappaAtBootstrapIteratedBound β C₀ (k + 1) := hboundEq.symm

/-- An unconditional factor comparing the and auxiliary κ chains on
all scales `1 ≤ m ≤ M`.  The cutoff and the finite low-scale product depend
only on `β` and `C₀`. -/
theorem kappaAt_kappaPrime_uniform_ratio_bound {β C₀ : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hC₀ : 0 ≤ C₀) :
    ∃ R : ℝ, 1 ≤ R ∧
      ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Chat ≤ C₀ →
        ∀ κ : ℝ, 0 < κ → ∀ M : ℕ, 1 ≤ M →
          κ ∈ permittedInterval β I.Λ M →
          ∀ m : ℕ, 1 ≤ m → m ≤ M →
            max (I.kappaAt κ m (M - m) /
                kappaPrimeAt β I.Λ κ m (M - m))
              (kappaPrimeAt β I.Λ κ m (M - m) /
                I.kappaAt κ m (M - m)) ≤ R := by
  have hE : 0 < kappaAtBootstrapErrorCoefficient β C₀ 2 :=
    kappaAtBootstrapErrorCoefficient_pos hβ hβ' hC₀ (by norm_num)
  obtain ⟨N, hN, hTail⟩ := exists_kappaAtBootstrap_cutoff hβ hβ' hE
  let R := kappaAtBootstrapIteratedBound β C₀ N
  refine ⟨R, ?_, ?_⟩
  · dsimp [R]
    exact le_trans (by norm_num : (1 : ℝ) ≤ 2)
      (kappaAtBootstrapIteratedBound_ge_two (β := β) (C₀ := C₀) N)
  · intro I hCz hCh κ hκ M hM hpermitted m hm hmM
    have hC₀I : 0 ≤ C₀ := hC₀
    let base := min M N
    have hbaseM : base ≤ M := Nat.min_le_left _ _
    have hbaseN : base ≤ N := Nat.min_le_right _ _
    have hbasePos : 1 ≤ base := by dsimp [base]; omega
    have hbaseRatio : max
        (I.kappaAt κ base (M - base) /
          kappaPrimeAt β I.Λ κ base (M - base))
        (kappaPrimeAt β I.Λ κ base (M - base) /
          I.kappaAt κ base (M - base)) ≤ 2 := by
      by_cases hMN : M ≤ N
      · have hbaseEq : base = M := min_eq_left hMN
        rw [hbaseEq]
        simp [Ingredients.kappaAt, kappaPrimeAt, hκ.ne']
      · have hNM : N ≤ M := by omega
        have hhigh := KappaAtPrimeScaleComparison.kappaAtPrime_ratio_high I hCz hCh hκ hpermitted
          hN hTail N (M - N) (by omega) (by omega)
        have hbaseEq : base = N := min_eq_right hNM
        rw [hbaseEq]
        have htailN := hTail
        have hdenN : 0 < 1 - kappaAtBootstrapTail β
            (kappaAtBootstrapErrorCoefficient β C₀ 2) N := by linarith
        have hinvN :
            (1 - kappaAtBootstrapTail β
              (kappaAtBootstrapErrorCoefficient β C₀ 2) N)⁻¹ ≤ 2 := by
          rw [← one_div]
          apply (div_le_iff₀ hdenN).2
          linarith
        exact hhigh.trans hinvN
    by_cases hmBase : m ≤ base
    · have hlow : max (I.kappaAt κ m (M - m) /
          kappaPrimeAt β I.Λ κ m (M - m))
          (kappaPrimeAt β I.Λ κ m (M - m) /
            I.kappaAt κ m (M - m)) ≤
          kappaAtBootstrapIteratedBound β C₀ (base - m) := by
        have hsegment := KappaAtPrimeScaleComparison.kappaAtPrime_ratio_low_segment I hCz hCh hκ
          hpermitted hbaseM hbaseRatio m (base - m)
          (by dsimp [base]; omega) hm
        exact hsegment
      calc
        max (I.kappaAt κ m (M - m) /
            kappaPrimeAt β I.Λ κ m (M - m))
          (kappaPrimeAt β I.Λ κ m (M - m) /
            I.kappaAt κ m (M - m)) ≤
            kappaAtBootstrapIteratedBound β C₀ (base - m) := hlow
        _ ≤ R := by
          dsimp [R]
          exact kappaAtBootstrapIteratedBound_mono (by dsimp [base]; omega)
    · have hNm : N ≤ m := by
        by_contra hnot
        have hmN : m < N := by omega
        exact hmBase ((Nat.le_min).2 ⟨hmM, Nat.le_of_lt hmN⟩)
      have hhigh := KappaAtPrimeScaleComparison.kappaAtPrime_ratio_high I hCz hCh hκ hpermitted
        hN hTail m (M - m) (by omega) hNm
      have htailm := kappaAtBootstrapTail_le_half_of_index hβ hβ' hE hTail hNm
      have hdenm : 0 < 1 - kappaAtBootstrapTail β
          (kappaAtBootstrapErrorCoefficient β C₀ 2) m := by linarith
      have hinvm :
          (1 - kappaAtBootstrapTail β
            (kappaAtBootstrapErrorCoefficient β C₀ 2) m)⁻¹ ≤ 2 := by
        rw [← one_div]
        apply (div_le_iff₀ hdenm).2
        linarith
      exact hhigh.trans (hinvm.trans
        (kappaAtBootstrapIteratedBound_ge_two N))

end AVenhance.Infra.Section3

end
