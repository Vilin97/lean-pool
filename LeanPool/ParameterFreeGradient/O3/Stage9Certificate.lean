/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Stage9Theta

/-!
# Stage 9: exact finite-data OGM-G algebraic certificate

This file isolates the algebraic heart of the finite-data OGM-G argument.
The main result below is horizon-generic: it expands the two certificate sums,
proves that every function-value coefficient telescopes to `psi 0`, and
reduces the remaining equality to the exact signed inner-product balance.

The final section contains a literal source-recurrence audit at `n = 1`,
explicit coefficient-theorem specializations at `n = 2, 3`, and separate
endpoint audits at all three horizons.  They are theorem statements rather
than floating-point examples: all coefficients remain symbolic and the
special equation `theta_0^2-theta_0=2 theta_1^2` is used exactly.  The actual
vector recurrence supplies the pairing-balance premise in `Stage9Pairing`.
-/

namespace O3
namespace Stage9Certificate

/-- The source quantity
`psi_i = f_i - f^* - ||g_i||^2/(2M)`.  The squared gradient is an explicit
scalar input so that the coefficient algebra is independent of a particular
vector representation. -/
noncomputable def ogmgPsi (M fstar : ℝ) (fval gradSq : ℕ → ℝ) (i : ℕ) : ℝ :=
  fval i - fstar - gradSq i / (2 * M)

/-- The source interpolation remainder
`I_ij = psi_i - psi_j - <g_j,v_i-v_j>`. -/
def ogmgI (psi : ℕ → ℝ) (pairTerm : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  psi i - psi j - pairTerm i j

/-- `delta_i = kappa_(i+1) - kappa_i`. -/
def ogmgDelta (kappa : ℕ → ℝ) (i : ℕ) : ℝ :=
  kappa (i + 1) - kappa i

/-- The literal right side of the frozen OGM-G certificate. -/
def ogmgCertificateRhs (n : ℕ) (kappa psi : ℕ → ℝ)
    (pairTerm : ℕ → ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, kappa (i + 1) * ogmgI psi pairTerm i (i + 1)) +
    (∑ i ∈ Finset.range n,
      ogmgDelta kappa i * ogmgI psi pairTerm n i) + psi n

/-- The unsigned collection of pairing terms subtracted by the certificate. -/
def ogmgPairingAggregate (n : ℕ) (kappa : ℕ → ℝ)
    (pairTerm : ℕ → ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, kappa (i + 1) * pairTerm i (i + 1)) +
    ∑ i ∈ Finset.range n, ogmgDelta kappa i * pairTerm n i

/-- Exact telescoping of the function-value coefficients.  No monotonicity or
theta equation is needed: only the source normalization `kappa_0 = 1`. -/
theorem ogmg_value_coefficients_telescope (n : ℕ) (kappa psi : ℕ → ℝ)
    (hkappa0 : kappa 0 = 1) :
    (∑ i ∈ Finset.range n,
        kappa (i + 1) * (psi i - psi (i + 1))) +
      (∑ i ∈ Finset.range n,
        ogmgDelta kappa i * (psi n - psi i)) + psi n = psi 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hdelta :
          (∑ i ∈ Finset.range n, ogmgDelta kappa i) = kappa n - 1 := by
        rw [show (∑ i ∈ Finset.range n, ogmgDelta kappa i) =
            ∑ i ∈ Finset.range n, (kappa (i + 1) - kappa i) by rfl]
        rw [Finset.sum_range_sub, hkappa0]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hrewrite :
          (∑ i ∈ Finset.range n,
              ogmgDelta kappa i * (psi (n + 1) - psi i)) =
            (∑ i ∈ Finset.range n,
              ogmgDelta kappa i * (psi n - psi i)) +
              (kappa n - 1) * (psi (n + 1) - psi n) := by
        calc
          (∑ i ∈ Finset.range n,
              ogmgDelta kappa i * (psi (n + 1) - psi i)) =
              ∑ i ∈ Finset.range n,
                (ogmgDelta kappa i * (psi n - psi i) +
                  ogmgDelta kappa i * (psi (n + 1) - psi n)) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
          _ = (∑ i ∈ Finset.range n,
                ogmgDelta kappa i * (psi n - psi i)) +
              ∑ i ∈ Finset.range n,
                ogmgDelta kappa i * (psi (n + 1) - psi n) := by
                  rw [Finset.sum_add_distrib]
          _ = (∑ i ∈ Finset.range n,
                ogmgDelta kappa i * (psi n - psi i)) +
              (kappa n - 1) * (psi (n + 1) - psi n) := by
                  rw [← Finset.sum_mul, hdelta]
      rw [hrewrite]
      rw [show ogmgDelta kappa n = kappa (n + 1) - kappa n by
        simp [ogmgDelta]]
      calc
        (∑ i ∈ Finset.range n,
              kappa (i + 1) * (psi i - psi (i + 1))) +
            kappa (n + 1) * (psi n - psi (n + 1)) +
          ((∑ i ∈ Finset.range n,
                ogmgDelta kappa i * (psi n - psi i)) +
              (kappa n - 1) * (psi (n + 1) - psi n) +
            (kappa (n + 1) - kappa n) *
              (psi (n + 1) - psi n)) +
          psi (n + 1) =
            ((∑ i ∈ Finset.range n,
                kappa (i + 1) * (psi i - psi (i + 1))) +
              (∑ i ∈ Finset.range n,
                ogmgDelta kappa i * (psi n - psi i)) + psi n) := by ring
        _ = psi 0 := ih

/-- Fully expanded arbitrary-horizon certificate: the value coefficients
collapse exactly, leaving only the two signed pairing sums. -/
theorem ogmgCertificateRhs_eq (n : ℕ) (kappa psi : ℕ → ℝ)
    (pairTerm : ℕ → ℕ → ℝ) (hkappa0 : kappa 0 = 1) :
    ogmgCertificateRhs n kappa psi pairTerm =
      psi 0 - ogmgPairingAggregate n kappa pairTerm := by
  have hvalue := ogmg_value_coefficients_telescope n kappa psi hkappa0
  have hvalue' :
      (∑ i ∈ Finset.range n, kappa (i + 1) * psi i) -
          (∑ i ∈ Finset.range n, kappa (i + 1) * psi (i + 1)) +
        ((∑ i ∈ Finset.range n, ogmgDelta kappa i * psi n) -
          (∑ i ∈ Finset.range n, ogmgDelta kappa i * psi i)) + psi n = psi 0 := by
    simpa only [mul_sub, Finset.sum_sub_distrib] using hvalue
  unfold ogmgCertificateRhs ogmgPairingAggregate ogmgI
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  linear_combination hvalue'

/-- The exact source identity follows once the OGM-G recurrence supplies its
quadratic pairing balance.  This lemma is the interface between the actual
iterate proof and the coefficient certificate; the balance is not stored in
the final finite-data statement. -/
theorem ogmgCertificate_identity_of_pairing_balance
    (n : ℕ) (M theta0 fstar : ℝ) (fval gradSq : ℕ → ℝ)
    (kappa : ℕ → ℝ) (pairTerm : ℕ → ℕ → ℝ)
    (hM : M ≠ 0) (hkappa0 : kappa 0 = 1)
    (hpair :
      ogmgPairingAggregate n kappa pairTerm =
        (theta0 ^ 2 * gradSq n - gradSq 0) / (2 * M)) :
    fval 0 - fstar - theta0 ^ 2 / (2 * M) * gradSq n =
      ogmgCertificateRhs n kappa (ogmgPsi M fstar fval gradSq) pairTerm := by
  rw [ogmgCertificateRhs_eq n kappa _ pairTerm hkappa0, hpair]
  unfold ogmgPsi
  field_simp [hM]
  ring

/-- Discrete change-of-order identity behind the second pairing sum. -/
theorem weighted_terminal_displacement (n : ℕ) (w v : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, w i * (v n - v i)) =
      ∑ k ∈ Finset.range n,
        (∑ i ∈ Finset.range (k + 1), w i) * (v (k + 1) - v k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hsplit :
          (∑ i ∈ Finset.range n, w i * (v (n + 1) - v i)) =
            (∑ i ∈ Finset.range n, w i * (v n - v i)) +
              (∑ i ∈ Finset.range n, w i) * (v (n + 1) - v n) := by
        calc
          _ = ∑ i ∈ Finset.range n,
              (w i * (v n - v i) + w i * (v (n + 1) - v n)) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
          _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [hsplit, ih, Finset.sum_range_succ]
      ring

/-- The source scalar OGM-G recurrence, used only for the independent
small-horizon coefficient audits below. -/
noncomputable def scalarOgmgNext (theta thetaNext u v vPrev : ℝ) : ℝ :=
  v + ((theta - 1) * (2 * thetaNext - 1) /
      (theta * (2 * theta - 1))) * (v - vPrev) +
    ((2 * thetaNext - 1) / (2 * theta - 1)) * (v - u)

def auditTwo (x0 x1 : ℝ) : ℕ → ℝ
  | 0 => x0
  | 1 => x1
  | _ => 0

/-- Independent exact audit at the smallest legal horizon.  This unfolds the
literal source recurrence with `v_{-1}=U`, the terminal `v_1`, and the special
theta equation; no convergence theorem is used. -/
theorem ogmg_certificate_audit_n1
    (M U fstar f0 f1 g0 g1 : ℝ) (hM : M ≠ 0) :
    let theta := stage9Theta 1
    let kappa := stage9Kappa 1
    let v0 := U - g0 / M
    let u1 := scalarOgmgNext (theta 0) (theta 1) U v0 U
    let v1 := u1 - g1 / M
    let fval := auditTwo f0 f1
    let grad := auditTwo g0 g1
    let vel := auditTwo v0 v1
    let gradSq := fun i => (grad i) ^ 2
    let pairTerm := fun i j => grad j * (vel i - vel j)
    f0 - fstar - (theta 0) ^ 2 / (2 * M) * g1 ^ 2 =
      ogmgCertificateRhs 1 kappa (ogmgPsi M fstar fval gradSq) pairTerm := by
  dsimp only
  apply ogmgCertificate_identity_of_pairing_balance 1 M (stage9Theta 1 0)
    fstar (auditTwo f0 f1) (fun i => (auditTwo g0 g1 i) ^ 2)
    (stage9Kappa 1)
    (fun i j => auditTwo g0 g1 j *
      (auditTwo (U - g0 / M)
        (scalarOgmgNext (stage9Theta 1 0) (stage9Theta 1 1) U
          (U - g0 / M) U - g1 / M) i -
       auditTwo (U - g0 / M)
        (scalarOgmgNext (stage9Theta 1 0) (stage9Theta 1 1) U
          (U - g0 / M) U - g1 / M) j)) hM (stage9Kappa_zero 1)
  norm_num [ogmgPairingAggregate, ogmgDelta, auditTwo]
  have hs : (ogmgThetaZero 1) ^ 2 - ogmgThetaZero 1 = 2 := by
    simpa using (stage9Theta_special_equation (by omega : 1 ≤ (1 : ℕ)))
  have ht0 := stage9Theta_ne_zero 1 0
  have hd0 := stage9_two_mul_theta_sub_one_ne_zero 1 0
  rw [stage9Kappa_of_pos (by omega : 0 < (1 : ℕ))]
  simp only [stage9Theta_zero,
    stage9Theta_endpoint (by omega : 1 ≤ (1 : ℕ))] at ht0 hd0 ⊢
  have hd0' : ogmgThetaZero 1 * 2 - 1 ≠ 0 := by
    intro h
    apply hd0
    nlinarith
  unfold scalarOgmgNext
  field_simp [hM, ht0, hd0, hd0']
  ring_nf
  linear_combination
    (-g0 * (2 * ogmgThetaZero 1 - 1) *
      (ogmgThetaZero 1 * g1 + g0)) * hs

/-- The p-sequence used in the TeX verification, specialized to the exact
source theta array. -/
noncomputable def auditP (n : ℕ) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (1 - 1 / stage9Theta n k) * auditP n g k +
      (1 / stage9Theta n k) * g k

/-- The endpoint `p_(n+1)=g_n` is derived from `theta_n=1`; it is not an
extra certificate input. -/
theorem auditP_terminal {n : ℕ} (hn : 1 ≤ n) (g : ℕ → ℝ) :
    auditP n g (n + 1) = g n := by
  rw [auditP, stage9Theta_endpoint hn]
  ring

/-- Exact source endpoint audit at `n=1`. -/
theorem ogmg_endpoint_audit_n1 (g : ℕ → ℝ) :
    stage9Theta 1 1 = 1 ∧
      stage9Theta 1 0 ^ 2 - stage9Theta 1 0 =
        2 * stage9Theta 1 1 ^ 2 ∧
      auditP 1 g 2 = g 1 := by
  exact ⟨stage9Theta_endpoint (by omega),
    stage9Theta_special_equation (by omega), auditP_terminal (by omega) g⟩

/-- Exact source endpoint and ordinary-coefficient audit at `n=2`. -/
theorem ogmg_endpoint_audit_n2 (g : ℕ → ℝ) :
    stage9Theta 2 2 = 1 ∧
      stage9Theta 2 0 ^ 2 - stage9Theta 2 0 =
        2 * stage9Theta 2 1 ^ 2 ∧
      stage9Theta 2 1 ^ 2 - stage9Theta 2 1 = stage9Theta 2 2 ^ 2 ∧
      auditP 2 g 3 = g 2 := by
  exact ⟨stage9Theta_endpoint (by omega),
    stage9Theta_special_equation (by omega),
    stage9Theta_ordinary_equation (by omega) (by omega),
    auditP_terminal (by omega) g⟩

/-- Exact source endpoint and both ordinary-coefficient audits at `n=3`. -/
theorem ogmg_endpoint_audit_n3 (g : ℕ → ℝ) :
    stage9Theta 3 3 = 1 ∧
      stage9Theta 3 0 ^ 2 - stage9Theta 3 0 =
        2 * stage9Theta 3 1 ^ 2 ∧
      stage9Theta 3 1 ^ 2 - stage9Theta 3 1 = stage9Theta 3 2 ^ 2 ∧
      stage9Theta 3 2 ^ 2 - stage9Theta 3 2 = stage9Theta 3 3 ^ 2 ∧
      auditP 3 g 4 = g 3 := by
  exact ⟨stage9Theta_endpoint (by omega),
    stage9Theta_special_equation (by omega),
    stage9Theta_ordinary_equation (by omega) (by omega),
    stage9Theta_ordinary_equation (by omega) (by omega),
    auditP_terminal (by omega) g⟩

/-- Explicit horizon-2 specialization of the native arbitrary-horizon
coefficient theorem.  The execution audit supplies the exact pairing balance
after expanding the two literal source recurrence steps. -/
theorem ogmg_certificate_coefficients_audit_n2
    (M fstar : ℝ) (fval gradSq : ℕ → ℝ) (pairTerm : ℕ → ℕ → ℝ)
    (hM : M ≠ 0)
    (hpair : ogmgPairingAggregate 2 (stage9Kappa 2) pairTerm =
      ((stage9Theta 2 0) ^ 2 * gradSq 2 - gradSq 0) / (2 * M)) :
    fval 0 - fstar - (stage9Theta 2 0) ^ 2 / (2 * M) * gradSq 2 =
      ogmgCertificateRhs 2 (stage9Kappa 2)
        (ogmgPsi M fstar fval gradSq) pairTerm :=
  ogmgCertificate_identity_of_pairing_balance 2 M (stage9Theta 2 0)
    fstar fval gradSq (stage9Kappa 2) pairTerm hM (stage9Kappa_zero 2) hpair

/-- Explicit horizon-3 specialization of the native arbitrary-horizon
coefficient theorem. -/
theorem ogmg_certificate_coefficients_audit_n3
    (M fstar : ℝ) (fval gradSq : ℕ → ℝ) (pairTerm : ℕ → ℕ → ℝ)
    (hM : M ≠ 0)
    (hpair : ogmgPairingAggregate 3 (stage9Kappa 3) pairTerm =
      ((stage9Theta 3 0) ^ 2 * gradSq 3 - gradSq 0) / (2 * M)) :
    fval 0 - fstar - (stage9Theta 3 0) ^ 2 / (2 * M) * gradSq 3 =
      ogmgCertificateRhs 3 (stage9Kappa 3)
        (ogmgPsi M fstar fval gradSq) pairTerm :=
  ogmgCertificate_identity_of_pairing_balance 3 M (stage9Theta 3 0)
    fstar fval gradSq (stage9Kappa 3) pairTerm hM (stage9Kappa_zero 3) hpair

end Stage9Certificate
end O3
