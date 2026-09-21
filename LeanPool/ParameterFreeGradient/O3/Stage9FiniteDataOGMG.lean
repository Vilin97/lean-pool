/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Stage9Execution
import LeanPool.ParameterFreeGradient.O3.Stage9Pairing
import LeanPool.ParameterFreeGradient.O3.Stage9Certificate

/-!
# Stage 9: finite-data OGM-G terminal-gradient certificate

This module connects the source-exact execution and its observable guards to
the native finite algebraic certificate.  In particular, the certificate is
proved from the actual recursion; it is not an input field or hypothesis.
-/

open scoped BigOperators

namespace O3

noncomputable def stage9ActualPsi (cfg : OGMGExecutionConfig d)
    (fstar : ℝ) (i : ℕ) : ℝ :=
  Stage9Certificate.ogmgPsi cfg.M fstar
    (ogmgFunctionValue cfg) (ogmgGradientSq cfg) i

noncomputable def stage9ActualI (cfg : OGMGExecutionConfig d)
    (fstar : ℝ) (i j : ℕ) : ℝ :=
  Stage9Certificate.ogmgI (stage9ActualPsi cfg fstar)
    (ogmgPairTerm cfg) i j

theorem pairing_symm {d : ℕ} (x y : Vec d) : pairing x y = pairing y x := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The algebraic `I_ij` is exactly the observable interpolation margin. -/
theorem stage9ActualI_eq_interpolationMargin
    (cfg : OGMGExecutionConfig d) (fstar : ℝ) (hM : cfg.M ≠ 0)
    (i j : ℕ) :
    stage9ActualI cfg fstar i j =
      ogmgFunctionValue cfg i - ogmgFunctionValue cfg j -
        pairing (ogmgGradient cfg j)
          ((ogmgState cfg i).current - (ogmgState cfg j).current) -
        (lpNorm 2 (ogmgGradient cfg i - ogmgGradient cfg j)) ^ (2 : ℕ) /
          (2 * cfg.M) := by
  let gi := ogmgGradient cfg i
  let gj := ogmgGradient cfg j
  let ui := (ogmgState cfg i).current
  let uj := (ogmgState cfg j).current
  have hnorm : (lpNorm 2 (gi - gj)) ^ (2 : ℕ) =
      (lpNorm 2 gi) ^ (2 : ℕ) - 2 * pairing gj gi +
        (lpNorm 2 gj) ^ (2 : ℕ) := by
    simp_rw [Stage2RouteC.lpNorm_two_sq]
    unfold pairing
    calc
      (∑ x, (gi - gj) x ^ 2) =
          ∑ x, (gi x ^ 2 - 2 * (gj x * gi x) + gj x ^ 2) := by
            apply Finset.sum_congr rfl
            intro x _
            simp only [Pi.sub_apply]
            ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum]
  have hpair : pairing gj
      ((ui - cfg.M⁻¹ • gi) - (uj - cfg.M⁻¹ • gj)) =
      pairing gj (ui - uj) - cfg.M⁻¹ * (pairing gj gi - pairing gj gj) := by
    unfold pairing
    calc
      (∑ x, gj x * ((ui x - cfg.M⁻¹ * gi x) -
          (uj x - cfg.M⁻¹ * gj x))) =
          ∑ x, (gj x * (ui x - uj x) -
            cfg.M⁻¹ * (gj x * gi x - gj x * gj x)) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
      _ = (∑ x, gj x * (ui x - uj x)) -
          cfg.M⁻¹ * ((∑ x, gj x * gi x) - ∑ x, gj x * gj x) := by
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  change ogmgFunctionValue cfg i - fstar -
        (lpNorm 2 gi) ^ (2 : ℕ) / (2 * cfg.M) -
      (ogmgFunctionValue cfg j - fstar -
        (lpNorm 2 gj) ^ (2 : ℕ) / (2 * cfg.M)) -
      pairing gj ((ui - cfg.M⁻¹ • gi) - (uj - cfg.M⁻¹ • gj)) = _
  change _ = ogmgFunctionValue cfg i - ogmgFunctionValue cfg j -
      pairing gj (ui - uj) - (lpNorm 2 (gi - gj)) ^ (2 : ℕ) / (2 * cfg.M)
  rw [hnorm, hpair, lpNorm_two_sq_eq_pairing, lpNorm_two_sq_eq_pairing]
  field_simp [hM]
  ring

theorem stage9InterpolationCheck_iff_actualI_nonneg
    (cfg : OGMGExecutionConfig d) (fstar : ℝ) (hM : cfg.M ≠ 0)
    (i j : Fin (cfg.horizon + 1)) :
    (ogmgInterpolationCheck cfg i j).Holds ↔
      0 ≤ stage9ActualI cfg fstar i j := by
  rw [stage9ActualI_eq_interpolationMargin cfg fstar hM i j]
  rfl

/-- The terminal descent query and the proof-side lower bound imply
`psi_n ≥ 0` with the exact `1/(2M)` coefficient. -/
theorem stage9ActualPsi_terminal_nonneg
    (cfg : OGMGExecutionConfig d) (fstar : ℝ) (hM : 0 < cfg.M)
    (hterminal : (ogmgTerminalDescentCheck cfg).Holds)
    (hlower : fstar ≤ (ogmgTerminalObservation cfg).value) :
    0 ≤ stage9ActualPsi cfg fstar cfg.horizon := by
  have hdescent := (ogmgTerminalDescentCheck_source_iff cfg hM).mp hterminal
  unfold stage9ActualPsi Stage9Certificate.ogmgPsi ogmgFunctionValue
    ogmgGradientSq
  linarith

/-- The exact source identity instantiated by the actual oracle data and the
actual recursive OGM-G execution. -/
theorem stage9Actual_certificate_identity
    (n : ℕ) (hn : 1 ≤ n) (oracle : PairOracle d) (M : ℝ) (U : Vec d)
    (fstar : ℝ) (hM : M ≠ 0) :
    let cfg := stage9ExecutionConfig n oracle M U
    ogmgFunctionValue cfg 0 - fstar -
        (stage9Theta n 0) ^ 2 / (2 * M) * ogmgGradientSq cfg n =
      Stage9Certificate.ogmgCertificateRhs n (stage9Kappa n)
        (stage9ActualPsi cfg fstar) (ogmgPairTerm cfg) := by
  dsimp only
  apply Stage9Certificate.ogmgCertificate_identity_of_pairing_balance
    n M (stage9Theta n 0) fstar
    (ogmgFunctionValue (stage9ExecutionConfig n oracle M U))
    (ogmgGradientSq (stage9ExecutionConfig n oracle M U))
    (stage9Kappa n) (ogmgPairTerm (stage9ExecutionConfig n oracle M U))
    hM (stage9Kappa_zero n)
  have hvelocity : ∀ k, 1 ≤ k → k ≤ n →
      M • (ogmgV (stage9ExecutionConfig n oracle M U) k -
        ogmgV (stage9ExecutionConfig n oracle M U) (k - 1)) =
        (-stage9Theta n k) •
          (stage9P (stage9Theta n)
              (ogmgGradient (stage9ExecutionConfig n oracle M U)) k +
            stage9P (stage9Theta n)
              (ogmgGradient (stage9ExecutionConfig n oracle M U)) (k + 1)) := by
    intro k hk _
    have h := stage9Execution_velocity_p_relation n oracle M U hM k
    dsimp only at h
    rw [show (ogmgState (stage9ExecutionConfig n oracle M U) k).previousV =
        ogmgV (stage9ExecutionConfig n oracle M U) (k - 1) by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      simp] at h
    exact h
  change Stage9Certificate.ogmgPairingAggregate n (stage9Kappa n)
      (stage9PairTerm
        (ogmgGradient (stage9ExecutionConfig n oracle M U))
        (ogmgV (stage9ExecutionConfig n oracle M U))) = _
  exact stage9_pairing_balance n hn M hM
      (ogmgGradient (stage9ExecutionConfig n oracle M U))
      (ogmgV (stage9ExecutionConfig n oracle M U)) hvelocity

/-- Exact actual-execution audit at horizon `n=1`. -/
theorem stage9Actual_certificate_audit_n1
    (oracle : PairOracle d) (M : ℝ) (U : Vec d) (fstar : ℝ) (hM : M ≠ 0) :
    let cfg := stage9ExecutionConfig 1 oracle M U
    ogmgFunctionValue cfg 0 - fstar -
        (stage9Theta 1 0) ^ 2 / (2 * M) * ogmgGradientSq cfg 1 =
      Stage9Certificate.ogmgCertificateRhs 1 (stage9Kappa 1)
        (stage9ActualPsi cfg fstar) (ogmgPairTerm cfg) :=
  stage9Actual_certificate_identity 1 (by omega) oracle M U fstar hM

/-- Exact actual-execution audit at horizon `n=2`. -/
theorem stage9Actual_certificate_audit_n2
    (oracle : PairOracle d) (M : ℝ) (U : Vec d) (fstar : ℝ) (hM : M ≠ 0) :
    let cfg := stage9ExecutionConfig 2 oracle M U
    ogmgFunctionValue cfg 0 - fstar -
        (stage9Theta 2 0) ^ 2 / (2 * M) * ogmgGradientSq cfg 2 =
      Stage9Certificate.ogmgCertificateRhs 2 (stage9Kappa 2)
        (stage9ActualPsi cfg fstar) (ogmgPairTerm cfg) :=
  stage9Actual_certificate_identity 2 (by omega) oracle M U fstar hM

/-- Exact actual-execution audit at horizon `n=3`. -/
theorem stage9Actual_certificate_audit_n3
    (oracle : PairOracle d) (M : ℝ) (U : Vec d) (fstar : ℝ) (hM : M ≠ 0) :
    let cfg := stage9ExecutionConfig 3 oracle M U
    ogmgFunctionValue cfg 0 - fstar -
        (stage9Theta 3 0) ^ 2 / (2 * M) * ogmgGradientSq cfg 3 =
      Stage9Certificate.ogmgCertificateRhs 3 (stage9Kappa 3)
        (stage9ActualPsi cfg fstar) (ogmgPairTerm cfg) :=
  stage9Actual_certificate_identity 3 (by omega) oracle M U fstar hM

/-- Exact source-level proposition carrier.  The oracle and all method data
precede the proof-only lower bound; no certificate is supplied by the caller. -/
def FiniteDataOGMGStatement : Prop :=
  ∀ (d : ℕ) (oracle : PairOracle d) (U : Vec d) (M fstar : ℝ) (n : ℕ),
    0 < M → 1 ≤ n →
    let cfg := stage9ExecutionConfig n oracle M U
    OGMGAllInterpolationGuardsHold cfg →
    (ogmgTerminalDescentCheck cfg).Holds →
    fstar ≤ (ogmgTerminalObservation cfg).value →
    (lpNorm 2 (ogmgGradient cfg n)) ^ (2 : ℕ) ≤
        2 * M * (ogmgFunctionValue cfg 0 - fstar) /
          (stage9Theta n 0) ^ (2 : ℕ) ∧
      (n + 1 : ℝ) / Real.sqrt 2 ≤ stage9Theta n 0

/-- Native finite-data OGM-G terminal-gradient certificate. -/
theorem finiteDataOGMG : FiniteDataOGMGStatement := by
  intro d oracle U M fstar n hM hn
  dsimp only
  intro hall hterminal hlower
  let cfg := stage9ExecutionConfig n oracle M U
  have hcfg : cfg.horizon = n := rfl
  have hMne : M ≠ 0 := ne_of_gt hM
  have hidentity := stage9Actual_certificate_identity n hn oracle M U fstar hMne
  have hall' := (ogmgAllInterpolationGuardsHold_iff cfg).mp hall
  have hfirst : 0 ≤ ∑ i ∈ Finset.range n,
      stage9Kappa n (i + 1) * stage9ActualI cfg fstar i (i + 1) := by
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (stage9Kappa_nonneg n (i + 1))
    have hii : i < n := Finset.mem_range.mp hi
    let ii : Fin (cfg.horizon + 1) := ⟨i, by rw [hcfg]; omega⟩
    let is : Fin (cfg.horizon + 1) := ⟨i + 1, by rw [hcfg]; omega⟩
    exact (stage9InterpolationCheck_iff_actualI_nonneg cfg fstar hMne
      ii is).mp (hall' ii is)
  have hsecond : 0 ≤ ∑ i ∈ Finset.range n,
      Stage9Certificate.ogmgDelta (stage9Kappa n) i *
        stage9ActualI cfg fstar n i := by
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · have hd : 0 ≤ stage9Delta n i :=
        stage9Delta_nonneg (Finset.mem_range.mp hi)
      simpa only [stage9Delta, Stage9Certificate.ogmgDelta] using hd
    have hii : i < n := Finset.mem_range.mp hi
    let nn : Fin (cfg.horizon + 1) := ⟨n, by rw [hcfg]; omega⟩
    let ii : Fin (cfg.horizon + 1) := ⟨i, by rw [hcfg]; omega⟩
    exact (stage9InterpolationCheck_iff_actualI_nonneg cfg fstar hMne
      nn ii).mp (hall' nn ii)
  have hpsi := stage9ActualPsi_terminal_nonneg cfg fstar hM hterminal hlower
  rw [hcfg] at hpsi
  have hrhs : 0 ≤ Stage9Certificate.ogmgCertificateRhs n (stage9Kappa n)
      (stage9ActualPsi cfg fstar) (ogmgPairTerm cfg) := by
    have hfirst' : 0 ≤ ∑ i ∈ Finset.range n,
        stage9Kappa n (i + 1) *
          Stage9Certificate.ogmgI (stage9ActualPsi cfg fstar)
            (ogmgPairTerm cfg) i (i + 1) := by
      simpa only [stage9ActualI] using hfirst
    have hsecond' : 0 ≤ ∑ i ∈ Finset.range n,
        Stage9Certificate.ogmgDelta (stage9Kappa n) i *
          Stage9Certificate.ogmgI (stage9ActualPsi cfg fstar)
            (ogmgPairTerm cfg) n i := by
      simpa only [stage9ActualI] using hsecond
    unfold Stage9Certificate.ogmgCertificateRhs
    exact add_nonneg (add_nonneg hfirst' hsecond') hpsi
  have hraw : 0 ≤ ogmgFunctionValue cfg 0 - fstar -
      (stage9Theta n 0) ^ 2 / (2 * M) * ogmgGradientSq cfg n := by
    dsimp only at hidentity
    rw [hidentity]
    exact hrhs
  constructor
  · have htheta : 0 < (stage9Theta n 0) ^ (2 : ℕ) := sq_pos_of_pos (stage9Theta_pos n 0)
    have hraw' : 0 ≤ ogmgFunctionValue (stage9ExecutionConfig n oracle M U) 0 - fstar -
        (stage9Theta n 0) ^ 2 / (2 * M) *
          (lpNorm 2 (ogmgGradient (stage9ExecutionConfig n oracle M U) n)) ^ (2 : ℕ) := by
      simpa [cfg, ogmgGradientSq] using hraw
    apply (le_div_iff₀ htheta).2
    field_simp [hMne] at hraw'
    nlinarith
  · exact stage9Theta_zero_lower hn

end O3
