/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import Mathlib.Topology.MetricSpace.Sequences
import LeanPool.PhaseRetrieval.DimdPoly.Internal.FiniteBaseAnnulusEstimate
import LeanPool.PhaseRetrieval.DimdPoly.Internal.ExactModulusRecovery

/-! # CoefficientLimitRigidity -/


open scoped BigOperators

noncomputable section

namespace DimdPolyLEAN

/-!
# CoefficientLimitRigidity

Compactness bridge scaffold whose only public downstream output is a finite
coefficient-threshold theorem.
-/

private theorem norm_sq_eq_sum_coeff_wip
    {d : Nat} {kappa : MultiIndex d} (H : Pkappa d kappa) :
    ‖H‖ ^ 2 = Finset.sum H.support (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
  unfold coeffPkappa
  change (Real.sqrt (Finset.sum H.support (fun alpha => ‖H alpha‖ ^ 2))) ^ 2 = _
  rw [Real.sq_sqrt]
  positivity

private theorem norm_nonneg_pkappa_coeff_wip
    {d : Nat} {kappa : MultiIndex d} (H : Pkappa d kappa) :
    0 <= ‖H‖ := by
  change 0 <= Real.sqrt (Finset.sum H.support (fun alpha => ‖H alpha‖ ^ 2))
  exact Real.sqrt_nonneg _

private theorem toFun_ofPkappa_wip
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    toFun kappa (ofPkappa kappa F) = evalPkappa kappa F := by
  ext z
  rw [toFun, evalPkappa, Finsupp.sum]
  have hzero :
      ∀ alpha ∉ F.support,
        coeffSkappa (ofPkappa kappa F) alpha * Phi kappa alpha z = 0 := by
    intro alpha halpha
    simp [coeffSkappa, ofPkappa, Finsupp.notMem_support_iff.mp halpha]
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [coeffSkappa, ofPkappa]

private theorem summable_skappa_eval_mul_of_phi_sq_wip
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (z : Cd d)
    (hPhi : Summable (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2)) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha * Phi kappa alpha z) := by
  have hU : Summable (fun alpha : Idx d => ‖coeffSkappa U alpha‖ ^ 2) := by
    simpa [coeffSkappa] using U.summable_norm_sq
  refine Summable.of_norm_bounded
    (g := fun alpha : Idx d =>
      (‖coeffSkappa U alpha‖ ^ 2 + ‖Phi kappa alpha z‖ ^ 2) / 2)
    ((hU.add hPhi).div_const 2) ?_
  intro alpha
  have hmul :
      ‖coeffSkappa U alpha * Phi kappa alpha z‖ <=
        ‖coeffSkappa U alpha‖ * ‖Phi kappa alpha z‖ :=
    norm_mul_le _ _
  have hsq :
      ‖coeffSkappa U alpha‖ * ‖Phi kappa alpha z‖ <=
        (‖coeffSkappa U alpha‖ ^ 2 + ‖Phi kappa alpha z‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖coeffSkappa U alpha‖ - ‖Phi kappa alpha z‖)]
  exact le_trans hmul hsq

private theorem finite_eval_sum_tendsto_wip
    {d : Nat} {kappa : MultiIndex d}
    {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha)))
    (E : Finset (Idx d)) (z : Cd d) :
    Filter.Tendsto
      (fun m => Finset.sum E
        (fun alpha => coeffPkappa (H m) alpha * Phi kappa alpha z))
      Filter.atTop
      (nhds (Finset.sum E
        (fun alpha => coeffSkappa U alpha * Phi kappa alpha z))) := by
  apply tendsto_finsetSum
  intro alpha halpha
  exact (hcoeff alpha).mul tendsto_const_nhds

private theorem phi1D_eq_oneDimPhi_wip
    (k n : Nat) (z : ℂ) :
    phi1D k n z = Hermite1DimdLEAN.oneDimPhi k n z := by
  unfold phi1D complexHermite Hermite1DimdLEAN.oneDimPhi
  congr 1
  · simp [one_div, mul_comm]
  · rw [Nat.min_comm k n]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj' : j <= min n k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjn : j <= n := le_trans hj' (Nat.min_le_left _ _)
    have hfac_ne : (Nat.factorial (n - j) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - j)
    have hfactor : (Nat.factorial j : ℂ) * (Nat.choose n j : ℂ) =
        (Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) := by
      apply mul_right_cancel₀ hfac_ne
      calc
        ((Nat.factorial j : ℂ) * (Nat.choose n j : ℂ)) *
            (Nat.factorial (n - j) : ℂ)
            = (Nat.choose n j : ℂ) * (Nat.factorial j : ℂ) *
                (Nat.factorial (n - j) : ℂ) := by ring
        _ = (Nat.factorial n : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
        _ = ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
              (Nat.factorial (n - j) : ℂ) := by field_simp [hfac_ne]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      congrArg
        (fun x : ℂ =>
          ((-1 : ℂ) ^ j) * x * (Nat.choose k j : ℂ) *
            z ^ (n - j) * (star z) ^ (k - j))
        hfactor

private theorem summable_sq_hermite_phi_eval_wip
    (k : Nat) (z : ℂ) :
    Summable (fun n : Nat => ‖HermitekLEAN.Phi k n z‖ ^ 2) := by
  obtain ⟨C, hC_nonneg, hC⟩ := HermitekLEAN.point_eval_bounded (k := k) z
  apply summable_of_sum_range_le (c := C ^ 2) (fun n => sq_nonneg _)
  intro J
  let a' : Fin J -> ℂ := fun n => star (HermitekLEAN.Phi k n.1 z)
  have hNS :
      HermitekLEAN.weightedNormSq (HermitekLEAN.finiteHermiteSum k a') =
        Finset.sum Finset.univ (fun n : Fin J => ‖HermitekLEAN.Phi k n.1 z‖ ^ 2) := by
    rw [HermitekLEAN.finiteHermiteSum_normSq]
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [a']
  let S : ℝ := Finset.sum Finset.univ
    (fun n : Fin J => ‖HermitekLEAN.Phi k n.1 z‖ ^ 2)
  have hS_nonneg : 0 <= S := by
    dsimp [S]
    exact Finset.sum_nonneg fun n hn => sq_nonneg _
  have hWN :
      HermitekLEAN.weightedNorm (HermitekLEAN.finiteHermiteSum k a') =
        Real.sqrt S := by
    change Real.sqrt (HermitekLEAN.weightedNormSq (HermitekLEAN.finiteHermiteSum k a')) =
      Real.sqrt S
    rw [hNS]
  have hFz : HermitekLEAN.finiteHermiteSum k a' z = (S : ℂ) := by
    simp only [HermitekLEAN.finiteHermiteSum, a', S]
    push_cast
    congr 1
    ext1 n
    calc
      star (HermitekLEAN.Phi k n.1 z) * HermitekLEAN.Phi k n.1 z
          = HermitekLEAN.Phi k n.1 z * star (HermitekLEAN.Phi k n.1 z) := by ring
      _ = (‖HermitekLEAN.Phi k n.1 z‖ ^ 2 : ℂ) := by
        simpa [Complex.normSq_eq_norm_sq] using
          Complex.mul_conj (HermitekLEAN.Phi k n.1 z)
  have hev :
      ‖HermitekLEAN.finiteHermiteSum k a' z‖ <=
        C * HermitekLEAN.weightedNorm (HermitekLEAN.finiteHermiteSum k a') :=
    hC (HermitekLEAN.finiteHermiteSum_mem_Hk k a')
  have hFz_bound : S <= ‖HermitekLEAN.finiteHermiteSum k a' z‖ := by
    calc
      S <= |S| := le_abs_self S
      _ = ‖(S : ℂ)‖ := (Complex.norm_real S).symm
      _ = ‖HermitekLEAN.finiteHermiteSum k a' z‖ := by rw [hFz]
  have hSle : S <= C ^ 2 := by
    have hev' : ‖HermitekLEAN.finiteHermiteSum k a' z‖ <= C * Real.sqrt S := by
      simpa [hWN] using hev
    nlinarith [Real.sq_sqrt hS_nonneg, sq_nonneg (Real.sqrt S - C), hFz_bound,
      hev', hC_nonneg]
  calc
    Finset.sum (Finset.range J) (fun n => ‖HermitekLEAN.Phi k n z‖ ^ 2)
        = S := (Fin.sum_univ_eq_sum_range (fun n : Nat => ‖HermitekLEAN.Phi k n z‖ ^ 2) J).symm
    _ <= C ^ 2 := hSle

private theorem summable_sq_phi1D_eval_wip
    (k : Nat) (z : ℂ) :
    Summable (fun m : Nat => ‖phi1D k m z‖ ^ 2) := by
  have hEq :
      (fun m : Nat => ‖phi1D k m z‖ ^ 2) =
        fun m : Nat => ‖HermitekLEAN.Phi k m z‖ ^ 2 := by
    funext m
    have hphi : phi1D k m z = HermitekLEAN.Phi k m z :=
      phi1D_eq_oneDimPhi_wip k m z
    simp [hphi]
  simpa [hEq] using
    summable_sq_hermite_phi_eval_wip k z

private theorem Phi_norm_sq_eq_prod_wip
    {d : Nat} (kappa alpha : MultiIndex d) (z : Cd d) :
    ‖Phi kappa alpha z‖ ^ 2 =
      Finset.prod Finset.univ
        (fun q : Fin d => ‖phi1D (kappa q) (alpha q) (z q)‖ ^ 2) := by
  simp [Phi, norm_prod, Finset.prod_pow]

private theorem summable_sq_Phi_eval_wip
    {d : Nat} (kappa : MultiIndex d) (z : Cd d) :
    Summable (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2) := by
  refine summable_of_sum_le
    (c := Finset.prod Finset.univ
      (fun q : Fin d => ∑' n : Nat, ‖phi1D (kappa q) n (z q)‖ ^ 2))
    (fun alpha : Idx d => sq_nonneg _) ?_
  intro E
  let J : Fin d -> Nat := fun q => Finset.sup E (fun alpha : Idx d => alpha q)
  let B : Finset (Idx d) := Fintype.piFinset fun q : Fin d => Finset.range (J q + 1)
  have hE_subset : E ⊆ B := by
    intro alpha halpha
    dsimp [B]
    rw [Fintype.mem_piFinset]
    intro q
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (s := E) (f := fun beta : Idx d => beta q) halpha
  have hsum_E_le_B :
      Finset.sum E (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2) <=
        Finset.sum B (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hE_subset
      (by intro alpha hB hnot; exact sq_nonneg _)
  have hbox_eq :
      Finset.sum B (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2) =
        Finset.prod Finset.univ
          (fun q : Fin d =>
            Finset.sum (Finset.range (J q + 1))
              (fun n : Nat => ‖phi1D (kappa q) n (z q)‖ ^ 2)) := by
    dsimp [B]
    symm
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    exact (Phi_norm_sq_eq_prod_wip kappa alpha z).symm
  have hprod_le :
      Finset.prod Finset.univ
          (fun q : Fin d =>
            Finset.sum (Finset.range (J q + 1))
              (fun n : Nat => ‖phi1D (kappa q) n (z q)‖ ^ 2)) <=
        Finset.prod Finset.univ
          (fun q : Fin d =>
            ∑' n : Nat, ‖phi1D (kappa q) n (z q)‖ ^ 2) := Finset.prod_le_prod
      (by
        intro q hq
        exact Finset.sum_nonneg fun n hn => sq_nonneg _)
      (by
        intro q hq
        exact (summable_sq_phi1D_eval_wip (kappa q) (z q)).sum_le_tsum
          (Finset.range (J q + 1)) (fun n hn => sq_nonneg _))
  exact le_trans hsum_E_le_B (by rw [hbox_eq]; exact hprod_le)

private theorem summable_skappa_eval_mul_wip
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (z : Cd d) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha * Phi kappa alpha z) :=
  summable_skappa_eval_mul_of_phi_sq_wip kappa U z
    (summable_sq_Phi_eval_wip kappa z)

private theorem summable_pkappa_eval_mul_wip
    {d : Nat} (kappa : MultiIndex d) (H : Pkappa d kappa) (z : Cd d) :
    Summable (fun alpha : Idx d => coeffPkappa H alpha * Phi kappa alpha z) := by
  have h := summable_skappa_eval_mul_wip kappa (ofPkappa kappa H) z
  refine h.congr ?_
  intro alpha
  rfl

private theorem evalPkappa_eq_tsum_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (H : Pkappa d kappa) (z : Cd d) :
    evalPkappa kappa H z =
      ∑' alpha : Idx d, coeffPkappa H alpha * Phi kappa alpha z := by
  have h := congrFun (toFun_ofPkappa_wip kappa H) z
  exact h.symm

private theorem evalPkappa_sub_toFun_eq_tsum_diff_wip
    {d : Nat} (kappa : MultiIndex d) (H : Pkappa d kappa)
    (U : Skappa d kappa) (z : Cd d) :
    evalPkappa kappa H z - toFun kappa U z =
      ∑' alpha : Idx d,
        (coeffPkappa H alpha - coeffSkappa U alpha) * Phi kappa alpha z := by
  have hHsum := summable_pkappa_eval_mul_wip kappa H z
  have hUsum := summable_skappa_eval_mul_wip kappa U z
  rw [evalPkappa_eq_tsum_coeff_wip, toFun]
  have hsub := hHsum.tsum_sub hUsum
  have hdiff_eq :
      (∑' alpha : Idx d,
        (coeffPkappa H alpha - coeffSkappa U alpha) * Phi kappa alpha z) =
        ∑' alpha : Idx d,
          (coeffPkappa H alpha * Phi kappa alpha z -
            coeffSkappa U alpha * Phi kappa alpha z) := tsum_congr fun alpha => by ring
  rw [hdiff_eq, hsub]

private theorem evalPkappa_add_apply_wip
    {d : Nat} (kappa : MultiIndex d)
    (F G : Pkappa d kappa) (z : Cd d) :
    evalPkappa kappa (F + G) z = evalPkappa kappa F z + evalPkappa kappa G z := by
  unfold evalPkappa
  rw [Finsupp.sum_add_index'] <;> simp [add_mul]

private theorem evalPkappa_smul_real_wip
    {d : Nat} (kappa : MultiIndex d) (t : ℝ) (H : Pkappa d kappa) :
    evalPkappa kappa (t • H) = fun z => (t : ℂ) * evalPkappa kappa H z := by
  ext z
  by_cases ht : t = 0
  · subst t
    simp [evalPkappa]
  · unfold evalPkappa
    rw [Finsupp.sum, Finsupp.sum, Finsupp.support_smul_eq ht, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    rw [Finsupp.smul_apply]
    change ((t : ℂ) * H alpha) * Phi kappa alpha z =
      (t : ℂ) * (H alpha * Phi kappa alpha z)
    ring

private theorem finite_eval_sum_norm_le_wip
    {d : Nat} (kappa : MultiIndex d) (E : Finset (Idx d))
    (a : Idx d -> ℂ) (z : Cd d) :
    ‖Finset.sum E (fun alpha => a alpha * Phi kappa alpha z)‖ <=
      Real.sqrt (Finset.sum E (fun alpha => ‖a alpha‖ ^ 2)) *
        Real.sqrt (Finset.sum E (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) := by
  calc
    ‖Finset.sum E (fun alpha => a alpha * Phi kappa alpha z)‖
        <= Finset.sum E (fun alpha => ‖a alpha * Phi kappa alpha z‖) :=
          norm_sum_le E (fun alpha => a alpha * Phi kappa alpha z)
    _ = Finset.sum E (fun alpha => ‖a alpha‖ * ‖Phi kappa alpha z‖) := by
          refine Finset.sum_congr rfl ?_
          intro alpha halpha
          rw [norm_mul]
    _ <= Real.sqrt (Finset.sum E (fun alpha => ‖a alpha‖ ^ 2)) *
        Real.sqrt (Finset.sum E (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) := by
          simpa using
            Real.sum_mul_le_sqrt_mul_sqrt E
              (fun alpha => ‖a alpha‖) (fun alpha => ‖Phi kappa alpha z‖)

private theorem evalPkappa_norm_le_kernel_sqrt_wip
    {d : Nat} (kappa : MultiIndex d) (H : Pkappa d kappa)
    (hH_norm : ‖H‖ = 1) (z : Cd d) :
    ‖evalPkappa kappa H z‖ <=
      Real.sqrt (∑' alpha : Idx d, ‖Phi kappa alpha z‖ ^ 2) := by
  have hfinite :=
    finite_eval_sum_norm_le_wip kappa H.support (coeffPkappa H) z
  have hcoeff_sqrt :
      Real.sqrt (Finset.sum H.support
        (fun alpha => ‖coeffPkappa H alpha‖ ^ 2)) = 1 := by
    have hnorm_sq := norm_sq_eq_sum_coeff_wip H
    have hsum_eq_one :
        Finset.sum H.support (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) = 1 := by
      nlinarith [hH_norm, hnorm_sq]
    rw [hsum_eq_one]
    simp
  have hphi_le :
      Finset.sum H.support (fun alpha => ‖Phi kappa alpha z‖ ^ 2) <=
        ∑' alpha : Idx d, ‖Phi kappa alpha z‖ ^ 2 := by
    exact (summable_sq_Phi_eval_wip kappa z).sum_le_tsum _
      (fun alpha halpha => sq_nonneg _)
  have hsqrt_le := Real.sqrt_le_sqrt hphi_le
  calc
    ‖evalPkappa kappa H z‖
        = ‖Finset.sum H.support
            (fun alpha => coeffPkappa H alpha * Phi kappa alpha z)‖ := by rfl
    _ <= Real.sqrt (Finset.sum H.support
          (fun alpha => ‖coeffPkappa H alpha‖ ^ 2)) *
        Real.sqrt (Finset.sum H.support
          (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) := hfinite
    _ = Real.sqrt (Finset.sum H.support
          (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) := by rw [hcoeff_sqrt, one_mul]
    _ <= Real.sqrt (∑' alpha : Idx d, ‖Phi kappa alpha z‖ ^ 2) := hsqrt_le

private theorem finite_coeff_sum_le_norm_sq_wip
    {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d)) (H : Pkappa d kappa) :
    Finset.sum E (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) <= ‖H‖ ^ 2 := by
  classical
  rw [norm_sq_eq_sum_coeff_wip H]
  have hsum_eq :
      Finset.sum E (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) =
        Finset.sum (E ∩ H.support) (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
    symm
    refine Finset.sum_subset (by intro alpha h; exact (Finset.mem_inter.mp h).1) ?_
    intro alpha hE hnot
    have hnot_support : alpha ∉ H.support := by
      intro hs
      exact hnot (Finset.mem_inter.mpr ⟨hE, hs⟩)
    simp [coeffPkappa, Finsupp.notMem_support_iff.mp hnot_support]
  rw [hsum_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro alpha h; exact (Finset.mem_inter.mp h).2)
    (by intro alpha hsupport hnot; positivity)

private theorem finite_coeff_diff_sq_sum_le_four_wip
    {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d))
    {H : Pkappa d kappa} {U : Skappa d kappa}
    (hH_norm : ‖H‖ = 1)
    (hU_partial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1) :
    Finset.sum E (fun alpha => ‖coeffPkappa H alpha - coeffSkappa U alpha‖ ^ 2) <= 4 := by
  have hterm :
      ∀ alpha : Idx d,
        ‖coeffPkappa H alpha - coeffSkappa U alpha‖ ^ 2 <=
          (2 : ℝ) * (‖coeffPkappa H alpha‖ ^ 2 + ‖coeffSkappa U alpha‖ ^ 2) := by
    intro alpha
    have hsub :
        ‖coeffPkappa H alpha - coeffSkappa U alpha‖ <=
          ‖coeffPkappa H alpha‖ + ‖coeffSkappa U alpha‖ := norm_sub_le _ _
    have hsq :
        ‖coeffPkappa H alpha - coeffSkappa U alpha‖ ^ 2 <=
          (‖coeffPkappa H alpha‖ + ‖coeffSkappa U alpha‖) ^ 2 := by
      nlinarith [hsub, norm_nonneg (coeffPkappa H alpha - coeffSkappa U alpha),
        norm_nonneg (coeffPkappa H alpha), norm_nonneg (coeffSkappa U alpha)]
    have ham :
        (‖coeffPkappa H alpha‖ + ‖coeffSkappa U alpha‖) ^ 2 <=
          2 * (‖coeffPkappa H alpha‖ ^ 2 + ‖coeffSkappa U alpha‖ ^ 2) := by
      nlinarith [sq_nonneg (‖coeffPkappa H alpha‖ - ‖coeffSkappa U alpha‖)]
    exact le_trans hsq ham
  calc
    Finset.sum E (fun alpha => ‖coeffPkappa H alpha - coeffSkappa U alpha‖ ^ 2)
        <= Finset.sum E
          (fun alpha => (2 : ℝ) *
            (‖coeffPkappa H alpha‖ ^ 2 + ‖coeffSkappa U alpha‖ ^ 2)) :=
          Finset.sum_le_sum fun alpha halpha => hterm alpha
    _ = Finset.sum E
          (fun alpha => 2 * ‖coeffPkappa H alpha‖ ^ 2 +
            2 * ‖coeffSkappa U alpha‖ ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro alpha halpha
          ring
    _ = 2 * Finset.sum E (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) +
          2 * Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ <= 2 * 1 + 2 * 1 := by
          have hH_le : Finset.sum E (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) <= 1 := by
            have hle := finite_coeff_sum_le_norm_sq_wip E H
            have hH_sq : ‖H‖ ^ 2 = 1 := by nlinarith [hH_norm]
            nlinarith
          have hU_le := hU_partial E
          nlinarith
    _ = 4 := by ring

private theorem finite_eval_diff_sum_norm_le_wip
    {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d))
    {H : Pkappa d kappa} {U : Skappa d kappa}
    (hH_norm : ‖H‖ = 1)
    (hU_partial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1)
    (z : Cd d) :
    ‖Finset.sum E
      (fun alpha => (coeffPkappa H alpha - coeffSkappa U alpha) * Phi kappa alpha z)‖ <=
      2 * Real.sqrt (Finset.sum E (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) := by
  have hcs := finite_eval_sum_norm_le_wip kappa E
    (fun alpha => coeffPkappa H alpha - coeffSkappa U alpha) z
  have hdiff := finite_coeff_diff_sq_sum_le_four_wip E hH_norm hU_partial
  have hsqrt_le_two :
      Real.sqrt (Finset.sum E
        (fun alpha => ‖coeffPkappa H alpha - coeffSkappa U alpha‖ ^ 2)) <= 2 := by
    calc
      Real.sqrt (Finset.sum E
        (fun alpha => ‖coeffPkappa H alpha - coeffSkappa U alpha‖ ^ 2))
          <= Real.sqrt 4 := Real.sqrt_le_sqrt hdiff
      _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
  have hphi_nonneg :
      0 <= Real.sqrt (Finset.sum E (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) :=
    Real.sqrt_nonneg _
  exact le_trans hcs (by nlinarith)

private theorem phi_sq_finite_tail_small_wip
    {d : Nat} (kappa : MultiIndex d) (z : Cd d) {eps : ℝ} (heps : 0 < eps) :
    ∃ E : Finset (Idx d), ∀ T : Finset (Idx d),
      Disjoint T E ->
        Finset.sum T (fun alpha => ‖Phi kappa alpha z‖ ^ 2) < eps := by
  obtain ⟨E, hE⟩ :=
    (summable_iff_vanishing_norm.mp (summable_sq_Phi_eval_wip kappa z)) eps heps
  refine ⟨E, ?_⟩
  intro T hdis
  have h := hE T hdis
  have hnonneg : 0 <= Finset.sum T (fun alpha => ‖Phi kappa alpha z‖ ^ 2) :=
    Finset.sum_nonneg fun alpha halpha => sq_nonneg _
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using h

private theorem finite_eval_diff_tail_small_wip
    {d : Nat} (kappa : MultiIndex d) (z : Cd d) {eps : ℝ} (heps : 0 < eps) :
    ∃ E : Finset (Idx d), ∀ T : Finset (Idx d),
      Disjoint T E ->
      ∀ {H : Pkappa d kappa} {U : Skappa d kappa},
        ‖H‖ = 1 ->
        (∀ E : Finset (Idx d),
          Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1) ->
        ‖Finset.sum T
          (fun alpha => (coeffPkappa H alpha - coeffSkappa U alpha) *
            Phi kappa alpha z)‖ < eps := by
  obtain ⟨E, hE⟩ :=
    phi_sq_finite_tail_small_wip kappa z
      (by positivity : 0 < (eps / 2) ^ 2)
  refine ⟨E, ?_⟩
  intro T hdis H U hH_norm hU_partial
  have htail := hE T hdis
  have htail_nonneg :
      0 <= Finset.sum T (fun alpha => ‖Phi kappa alpha z‖ ^ 2) :=
    Finset.sum_nonneg fun alpha halpha => sq_nonneg _
  have hsqrt_lt :
      Real.sqrt (Finset.sum T (fun alpha => ‖Phi kappa alpha z‖ ^ 2)) < eps / 2 := by
    rw [← Real.sqrt_sq (by linarith : 0 <= eps / 2)]
    exact Real.sqrt_lt_sqrt htail_nonneg htail
  have hbound := finite_eval_diff_sum_norm_le_wip T hH_norm hU_partial z
  nlinarith

private theorem norm_tsum_subtype_compl_le_of_finset_bound_wip
    {ι : Type*} (E : Finset ι) {f : ι -> ℂ} {C : ℝ}
    (hf : Summable (fun alpha : {alpha // alpha ∉ (E : Set ι)} => f alpha))
    (hC : ∀ T : Finset ι, Disjoint T E -> ‖Finset.sum T f‖ <= C) :
    ‖∑' alpha : {alpha // alpha ∉ (E : Set ι)}, f alpha‖ <= C := by
  classical
  have hlim :
      Filter.Tendsto
        (fun T : Finset {alpha // alpha ∉ (E : Set ι)} =>
          ‖Finset.sum T (fun alpha => f alpha)‖)
        Filter.atTop
        (nhds (‖∑' alpha : {alpha // alpha ∉ (E : Set ι)}, f alpha‖)) := by
    simpa [HasSum] using hf.hasSum.norm
  refine le_of_tendsto hlim (Filter.Eventually.of_forall ?_)
  intro T
  let T' : Finset ι := T.map ⟨Subtype.val, Subtype.coe_injective⟩
  have hdis : Disjoint T' E := by
    rw [Finset.disjoint_left]
    intro alpha halpha hE
    rcases Finset.mem_map.mp halpha with ⟨beta, hbeta, rfl⟩
    exact beta.2 hE
  have hsum :
      Finset.sum T (fun alpha : {alpha // alpha ∉ (E : Set ι)} => f alpha) =
        Finset.sum T' f := by simp [T']
  have hnorm :
      ‖Finset.sum T (fun alpha : {alpha // alpha ∉ (E : Set ι)} => f alpha)‖ =
        ‖Finset.sum T' f‖ := by rw [hsum]
  exact hnorm.trans_le (hC T' hdis)

private theorem evalPkappa_tendsto_toFun_of_coeff_tendsto_wip
    {d : Nat} {kappa : MultiIndex d}
    {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha)))
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hU_partial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1)
    (z : Cd d) :
    Filter.Tendsto (fun m => evalPkappa kappa (H m) z) Filter.atTop
      (nhds (toFun kappa U z)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨E, hE⟩ :=
    finite_eval_diff_tail_small_wip kappa z (by linarith : 0 < eps / 3)
  have hhead :
      Filter.Tendsto
        (fun m => Finset.sum E
          (fun alpha =>
            (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z))
        Filter.atTop (nhds 0) := by
    have hsum := finite_eval_sum_tendsto_wip hcoeff E z
    have hsub :
        Filter.Tendsto
          (fun m =>
            Finset.sum E (fun alpha => coeffPkappa (H m) alpha * Phi kappa alpha z) -
              Finset.sum E (fun alpha => coeffSkappa U alpha * Phi kappa alpha z))
          Filter.atTop
          (nhds
            (Finset.sum E (fun alpha => coeffSkappa U alpha * Phi kappa alpha z) -
              Finset.sum E (fun alpha => coeffSkappa U alpha * Phi kappa alpha z))) :=
      hsum.sub tendsto_const_nhds
    convert hsub using 1
    · ext m
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro alpha halpha
      ring
    · simp
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hhead) (eps / 3) (by linarith)
  refine ⟨M, ?_⟩
  intro m hm
  rw [dist_eq_norm]
  have hdiff_summ :
      Summable (fun alpha : Idx d =>
        (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z) := by
    have hHsum := summable_pkappa_eval_mul_wip kappa (H m) z
    have hUsum := summable_skappa_eval_mul_wip kappa U z
    exact (hHsum.sub hUsum).congr fun alpha => by ring
  have htail_le :
      ‖∑' alpha : {alpha // alpha ∉ (E : Set (Idx d))},
        (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z‖ <=
        eps / 3 := by
    refine norm_tsum_subtype_compl_le_of_finset_bound_wip
      (E := E)
      (f := fun alpha : Idx d =>
        (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z)
      (hf := hdiff_summ.subtype _) ?_
    intro T hdis
    exact le_of_lt (hE T hdis (hH_norm m) hU_partial)
  have hsplit := hdiff_summ.sum_add_tsum_subtype_compl E
  have hdiff_eval := evalPkappa_sub_toFun_eq_tsum_diff_wip kappa (H m) U z
  rw [hdiff_eval, ← hsplit]
  have hhead_lt :
      ‖Finset.sum E
        (fun alpha =>
          (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z)‖ <
        eps / 3 := by simpa [dist_eq_norm] using hM m hm
  have hsum_norm :=
    norm_add_le
      (Finset.sum E
        (fun alpha =>
          (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z))
      (∑' alpha : {alpha // alpha ∉ (E : Set (Idx d))},
        (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z)
  calc
    ‖Finset.sum E
        (fun alpha =>
          (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z) +
        ∑' alpha : {alpha // alpha ∉ (E : Set (Idx d))},
          (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z‖
        <=
        ‖Finset.sum E
          (fun alpha =>
            (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z)‖ +
          ‖∑' alpha : {alpha // alpha ∉ (E : Set (Idx d))},
            (coeffPkappa (H m) alpha - coeffSkappa U alpha) * Phi kappa alpha z‖ :=
          hsum_norm
    _ < eps / 3 + eps / 3 := add_lt_add_of_lt_of_le hhead_lt htail_le
    _ < eps := by linarith

private theorem evalPkappa_add_smul_tendsto_toFun_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa)
    {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    {t : ℕ -> ℝ} {T : ℝ}
    (ht : Filter.Tendsto t Filter.atTop (nhds T))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha)))
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hU_partial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1)
    (z : Cd d) :
    Filter.Tendsto
      (fun m => evalPkappa kappa (F + t m • H m) z)
      Filter.atTop
      (nhds (evalPkappa kappa F z + (T : ℂ) * toFun kappa U z)) := by
  have hH_eval :=
    evalPkappa_tendsto_toFun_of_coeff_tendsto_wip hcoeff hH_norm hU_partial z
  have ht_complex :
      Filter.Tendsto (fun m => (t m : ℂ)) Filter.atTop (nhds (T : ℂ)) :=
    (Complex.continuous_ofReal.tendsto T).comp ht
  have hscaled :
      Filter.Tendsto
        (fun m => (t m : ℂ) * evalPkappa kappa (H m) z)
        Filter.atTop
        (nhds ((T : ℂ) * toFun kappa U z)) :=
    ht_complex.mul hH_eval
  have hconst :
      Filter.Tendsto (fun _ : ℕ => evalPkappa kappa F z) Filter.atTop
        (nhds (evalPkappa kappa F z)) :=
    tendsto_const_nhds
  have hsum := hconst.add hscaled
  convert hsum using 1
  ext m
  rw [evalPkappa_add_apply_wip, congrFun (evalPkappa_smul_real_wip kappa (t m) (H m)) z]

private theorem ae_norm_eq_of_tendsto_defect_wip
    {d : Nat} {base : Cd d -> ℂ}
    {v : ℕ -> Cd d -> ℂ} {limit : Cd d -> ℂ}
    (hpointwise :
      ∀ᵐ z ∂ gammaD d, Filter.Tendsto (fun m => v m z) Filter.atTop (nhds (limit z)))
    (hdefect :
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m => |‖v m z‖ - ‖base z‖|)
          Filter.atTop (nhds 0)) :
    (fun z => ‖limit z‖) =ᵐ[gammaD d] fun z => ‖base z‖ := by
  filter_upwards [hpointwise, hdefect] with z hzpoint hzdef
  let φ : ℂ -> ℝ := fun w => |‖w‖ - ‖base z‖|
  have hφ : Continuous φ := by
    unfold φ
    exact (continuous_norm.sub continuous_const).abs
  have hlim :
      Filter.Tendsto
        (fun m => |‖v m z‖ - ‖base z‖|)
        Filter.atTop
        (nhds (|‖limit z‖ - ‖base z‖|)) := by
    change Filter.Tendsto (φ ∘ fun m => v m z) Filter.atTop (nhds (φ (limit z)))
    exact (hφ.tendsto (limit z)).comp hzpoint
  have hzero : |‖limit z‖ - ‖base z‖| = 0 :=
    tendsto_nhds_unique hlim hzdef
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

private theorem ae_real_part_eq_zero_of_tendsto_wip
    {d : Nat} {base : Cd d -> ℂ}
    {u : ℕ -> Cd d -> ℂ} {limit : Cd d -> ℂ}
    (hpointwise :
      ∀ᵐ z ∂ gammaD d, Filter.Tendsto (fun m => u m z) Filter.atTop (nhds (limit z)))
    (hreal :
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m => Complex.re (u m z * star (base z)))
          Filter.atTop (nhds 0)) :
    (fun z => Complex.re (limit z * star (base z))) =ᵐ[gammaD d] fun _ => 0 := by
  filter_upwards [hpointwise, hreal] with z hzpoint hzreal
  let φ : ℂ -> ℝ := fun w => Complex.re (w * star (base z))
  have hφ : Continuous φ := by
    unfold φ
    exact Complex.continuous_re.comp (continuous_id.mul continuous_const)
  have hlim :
      Filter.Tendsto
        (fun m => Complex.re (u m z * star (base z)))
        Filter.atTop
        (nhds (Complex.re (limit z * star (base z)))) := by
    change Filter.Tendsto (φ ∘ fun m => u m z) Filter.atTop (nhds (φ (limit z)))
    exact (hφ.tendsto (limit z)).comp hzpoint
  exact tendsto_nhds_unique hlim hzreal

private theorem pkappaInner_eq_sum_right_support_wip
    {d : Nat} {kappa : MultiIndex d} (G F : Pkappa d kappa) :
    pkappaInner G F = Finset.sum F.support (fun alpha => G alpha * star (F alpha)) := by
  classical
  unfold pkappaInner
  rw [Finsupp.sum]
  have hleft :
      Finset.sum G.support (fun alpha => G alpha * star (F alpha)) =
        Finset.sum (G.support ∩ F.support) (fun alpha => G alpha * star (F alpha)) := by
    symm
    refine Finset.sum_subset (by intro alpha h; exact (Finset.mem_inter.mp h).1) ?_
    intro alpha hG hnot
    have hnotF : alpha ∉ F.support := by
      intro hF
      exact hnot (Finset.mem_inter.mpr ⟨hG, hF⟩)
    simp [Finsupp.notMem_support_iff.mp hnotF]
  have hright :
      Finset.sum F.support (fun alpha => G alpha * star (F alpha)) =
        Finset.sum (G.support ∩ F.support) (fun alpha => G alpha * star (F alpha)) := by
    symm
    refine Finset.sum_subset (by intro alpha h; exact (Finset.mem_inter.mp h).2) ?_
    intro alpha hF hnot
    have hnotG : alpha ∉ G.support := by
      intro hG
      exact hnot (Finset.mem_inter.mpr ⟨hG, hF⟩)
    simp [Finsupp.notMem_support_iff.mp hnotG]
  exact hleft.trans hright.symm

private theorem pkappaInner_add_left_wip
    {d : Nat} {kappa : MultiIndex d} (G H F : Pkappa d kappa) :
    pkappaInner (G + H) F = pkappaInner G F + pkappaInner H F := by
  rw [pkappaInner_eq_sum_right_support_wip, pkappaInner_eq_sum_right_support_wip,
    pkappaInner_eq_sum_right_support_wip]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [Finsupp.add_apply, add_mul]

private theorem pkappaInner_smul_left_complex_wip
    {d : Nat} {kappa : MultiIndex d} (c : ℂ) (G F : Pkappa d kappa) :
    pkappaInner (c • G) F = c * pkappaInner G F := by
  rw [pkappaInner_eq_sum_right_support_wip, pkappaInner_eq_sum_right_support_wip,
    Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [Finsupp.smul_apply, mul_assoc]

private theorem pkappaInner_smul_left_real_wip
    {d : Nat} {kappa : MultiIndex d} (t : ℝ) (G F : Pkappa d kappa) :
    pkappaInner (t • G) F = (t : ℂ) * pkappaInner G F := by
  change pkappaInner (((t : ℂ) • G)) F = (t : ℂ) * pkappaInner G F
  exact pkappaInner_smul_left_complex_wip (t : ℂ) G F

private theorem pkappaInner_self_of_norm_one_wip
    {d : Nat} {kappa : MultiIndex d} {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1) :
    pkappaInner F F = 1 := by
  rw [pkappaInner_eq_sum_right_support_wip]
  have hsum :
      Finset.sum F.support (fun alpha => F alpha * star (F alpha)) =
        ((Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) : ℝ) : ℂ) := by
    norm_num
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj (F alpha)
  have hnorm_sq := norm_sq_eq_sum_coeff_wip F
  have hsum_one : Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) = 1 := by
    simpa [coeffPkappa] using hnorm_sq.symm.trans (by rw [hF_norm]; norm_num)
  rw [hsum]
  exact_mod_cast hsum_one

private theorem skappaInnerAgainstPk_tendsto_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha))) :
    Filter.Tendsto
      (fun m => pkappaInner (H m) F)
      Filter.atTop
      (nhds (Finset.sum F.support
        (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha)))) := by
  rw [show (fun m => pkappaInner (H m) F) =
      fun m => Finset.sum F.support
        (fun alpha => coeffPkappa (H m) alpha * star (coeffPkappa F alpha)) by
    funext m
    rw [pkappaInner_eq_sum_right_support_wip]
    simp [coeffPkappa]]
  apply tendsto_finsetSum
  intro alpha halpha
  exact (hcoeff alpha).mul tendsto_const_nhds

private def coefficientControlSet_wip
    {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d)) (F : Pkappa d kappa) :
    Finset (Idx d) :=
  E ∪ F.support

private theorem norm_smul_pkappa_complex_wip
    {d : Nat} {kappa : MultiIndex d} (c : ℂ) (F : Pkappa d kappa) :
    ‖c • F‖ = ‖c‖ * ‖F‖ := by
  classical
  by_cases hc : c = 0
  · subst c
    rw [zero_smul]
    change Real.sqrt (Finset.sum (0 : Pkappa d kappa).support
      (fun alpha => ‖(0 : Pkappa d kappa) alpha‖ ^ 2)) = ‖(0 : ℂ)‖ * ‖F‖
    simp
  · change
      Real.sqrt (Finset.sum (c • F).support (fun alpha => ‖(c • F) alpha‖ ^ 2)) =
        ‖c‖ * Real.sqrt (Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2))
    rw [Finsupp.support_smul_eq hc]
    have hsum :
        Finset.sum F.support (fun alpha => ‖(c • F) alpha‖ ^ 2) =
          ‖c‖ ^ 2 * Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro alpha halpha
      simp [Finsupp.smul_apply, mul_pow]
    rw [hsum, Real.sqrt_mul (sq_nonneg ‖c‖), Real.sqrt_sq_eq_abs]
    simp [abs_of_nonneg (norm_nonneg _)]

private def orthogonalToSkappa_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa) (U : Skappa d kappa) : Prop :=
  Finset.sum F.support
    (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha)) = 0

private theorem orthogonalToSkappa_of_coeff_tendsto_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    (horth : ∀ m, orthogonalToPk F (H m))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha))) :
    orthogonalToSkappa_wip F U := by
  have hsum_tendsto :
      Filter.Tendsto
        (fun m =>
          Finset.sum F.support
            (fun alpha => coeffPkappa (H m) alpha * star (coeffPkappa F alpha)))
        Filter.atTop
        (nhds (Finset.sum F.support
          (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha)))) := by
    apply tendsto_finsetSum
    intro alpha halpha
    exact (hcoeff alpha).mul tendsto_const_nhds
  have hsum_zero :
      (fun m =>
          Finset.sum F.support
            (fun alpha => coeffPkappa (H m) alpha * star (coeffPkappa F alpha))) =
        fun _ : ℕ => (0 : ℂ) := by
    funext m
    have hm := horth m
    dsimp [orthogonalToPk] at hm
    simpa [coeffPkappa, pkappaInner_eq_sum_right_support_wip (H m) F] using hm
  have hzero_tendsto :
      Filter.Tendsto
        (fun m =>
          Finset.sum F.support
            (fun alpha => coeffPkappa (H m) alpha * star (coeffPkappa F alpha)))
        Filter.atTop (nhds (0 : ℂ)) := by
    rw [hsum_zero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hsum_tendsto hzero_tendsto

private theorem scalar_multiple_eq_zero_of_orthogonalToSkappa_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1)
    {U : Skappa d kappa} {c : ℂ}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = c * coeffPkappa F alpha)
    (horth : orthogonalToSkappa_wip F U) :
    c = 0 := by
  have hinner :
      Finset.sum F.support
          (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha)) =
        c * ((Finset.sum F.support
          (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) : ℝ) : ℂ) := by
    calc
      Finset.sum F.support
          (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha))
          = Finset.sum F.support
            (fun alpha => (c * coeffPkappa F alpha) * star (coeffPkappa F alpha)) := by
              refine Finset.sum_congr rfl ?_
              intro alpha halpha
              rw [hcoeff alpha]
      _ = c * Finset.sum F.support
            (fun alpha => coeffPkappa F alpha * star (coeffPkappa F alpha)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro alpha halpha
              ring
      _ = c * ((Finset.sum F.support
            (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) : ℝ) : ℂ) := by
              congr 1
              norm_num
              refine Finset.sum_congr rfl ?_
              intro alpha halpha
              simpa [Complex.normSq_eq_norm_sq] using
                Complex.mul_conj (coeffPkappa F alpha)
  have hsum_one :
      ((Finset.sum F.support (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) : ℝ) : ℂ) = 1 := by
    have hnorm_sq := norm_sq_eq_sum_coeff_wip F
    have hF_sq : ‖F‖ ^ 2 = 1 := by nlinarith [hF_norm]
    norm_num
    exact_mod_cast hnorm_sq.symm.trans hF_sq
  have hzero : c * ((Finset.sum F.support
      (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) : ℝ) : ℂ) = 0 := by rw [← hinner, horth]
  simpa [hsum_one] using hzero

private theorem coeff_zero_of_scalar_multiple_orthogonalToSkappa_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1)
    {U : Skappa d kappa} {c : ℂ}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = c * coeffPkappa F alpha)
    (horth : orthogonalToSkappa_wip F U) :
    ∀ alpha, coeffSkappa U alpha = 0 := by
  have hc : c = 0 :=
    scalar_multiple_eq_zero_of_orthogonalToSkappa_wip hF_norm hcoeff horth
  intro alpha
  simp [hcoeff alpha, hc]

private theorem finite_coeff_sq_tendsto_wip
    {d : Nat} {kappa : MultiIndex d}
    {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha)))
    (E : Finset (Idx d)) :
    Filter.Tendsto
      (fun m => Finset.sum E (fun alpha => ‖coeffPkappa (H m) alpha‖ ^ 2))
      Filter.atTop
      (nhds (Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2))) := by
  apply tendsto_finsetSum
  intro alpha halpha
  exact ((continuous_pow 2).tendsto _).comp ((hcoeff alpha).norm)

private theorem finite_coeff_sq_limit_ge_of_forall_le_wip
    {d : Nat} {kappa : MultiIndex d}
    {H : ℕ -> Pkappa d kappa} {U : Skappa d kappa}
    {rho : ℝ} (E : Finset (Idx d))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H m) alpha) Filter.atTop
      (nhds (coeffSkappa U alpha)))
    (hmass : ∀ m, rho <=
      Finset.sum E (fun alpha => ‖coeffPkappa (H m) alpha‖ ^ 2)) :
    rho <= Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) := by
  exact ge_of_tendsto (finite_coeff_sq_tendsto_wip hcoeff E)
    (Filter.Eventually.of_forall hmass)

private def skappaOfCoeffBound_wip
    {d : Nat} (kappa : MultiIndex d) (u : Idx d -> ℂ)
    (hpartial :
      ∀ E : Finset (Idx d), Finset.sum E (fun alpha => ‖u alpha‖ ^ 2) <= 1) :
    Skappa d kappa :=
  { coeff := u
    summable_norm_sq := by exact summable_of_sum_le (fun alpha => sq_nonneg (‖u alpha‖)) hpartial }

private theorem coeff_limit_subseq_with_head_mass_wip
    {d : Nat} (kappa : MultiIndex d)
    (K : Finset (Idx d)) {rho : ℝ}
    (H : ℕ -> Pkappa d kappa)
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hmass : ∀ m, rho <=
      Finset.sum K (fun alpha => ‖coeffPkappa (H m) alpha‖ ^ 2)) :
    ∃ U : Skappa d kappa, ∃ φ : ℕ -> ℕ,
      StrictMono φ ∧
      (∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha) Filter.atTop
        (nhds (coeffSkappa U alpha))) ∧
      (∀ E : Finset (Idx d),
        Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1) ∧
      rho <= Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) := by
  let S : Set (Idx d -> ℂ) :=
    {x | ∀ alpha, x alpha ∈ Metric.closedBall (0 : ℂ) 1}
  have hcoeff_le_one : ∀ m alpha, ‖coeffPkappa (H m) alpha‖ <= 1 := by
    intro m alpha
    have hle :=
      finite_coeff_sum_le_norm_sq_wip ({alpha} : Finset (Idx d)) (H m)
    simp only [Finset.sum_singleton] at hle
    have hH_sq : ‖H m‖ ^ 2 = 1 := by nlinarith [hH_norm m]
    have hnonneg : 0 <= ‖coeffPkappa (H m) alpha‖ := norm_nonneg _
    nlinarith
  have hseq_mem : ∀ m, (fun alpha => coeffPkappa (H m) alpha) ∈ S := by
    intro m alpha
    simpa only [S, Metric.mem_closedBall, dist_zero_right] using hcoeff_le_one m alpha
  have hS_compact : IsCompact S := by
    dsimp [S]
    exact isCompact_pi_infinite
      (fun _ : Idx d => ProperSpace.isCompact_closedBall (0 : ℂ) 1)
  have hS_seqcompact : IsSeqCompact S := hS_compact.isSeqCompact
  obtain ⟨u, _hu_mem, φ, hφ_strict, hφ_tendsto⟩ :=
    hS_seqcompact (fun m => hseq_mem m)
  have hcoeff_raw :
      ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
        Filter.atTop (nhds (u alpha)) := by
    intro alpha
    exact (continuous_apply alpha |>.tendsto u).comp hφ_tendsto
  have hfinite_tendsto :
      ∀ E : Finset (Idx d),
        Filter.Tendsto
          (fun m => Finset.sum E (fun alpha => ‖coeffPkappa (H (φ m)) alpha‖ ^ 2))
          Filter.atTop
          (nhds (Finset.sum E (fun alpha => ‖u alpha‖ ^ 2))) := by
    intro E
    apply tendsto_finsetSum
    intro alpha halpha
    exact ((continuous_pow 2).tendsto _).comp ((hcoeff_raw alpha).norm)
  have hpartial :
      ∀ E : Finset (Idx d), Finset.sum E (fun alpha => ‖u alpha‖ ^ 2) <= 1 := by
    intro E
    refine le_of_tendsto (hfinite_tendsto E) (Filter.Eventually.of_forall ?_)
    intro m
    have hle := finite_coeff_sum_le_norm_sq_wip E (H (φ m))
    have hH_sq : ‖H (φ m)‖ ^ 2 = 1 := by nlinarith [hH_norm (φ m)]
    nlinarith
  let U : Skappa d kappa := skappaOfCoeffBound_wip kappa u hpartial
  have hcoeff :
      ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
        Filter.atTop (nhds (coeffSkappa U alpha)) := by
    intro alpha
    simpa [U, skappaOfCoeffBound_wip, coeffSkappa] using hcoeff_raw alpha
  have hpartial_U :
      ∀ E : Finset (Idx d),
        Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1 := by
    intro E
    simpa [U, skappaOfCoeffBound_wip, coeffSkappa] using hpartial E
  have hmass_U : rho <=
      Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) := by
    exact finite_coeff_sq_limit_ge_of_forall_le_wip K hcoeff
      (fun m => hmass (φ m))
  exact ⟨U, φ, hφ_strict, hcoeff, hpartial_U, hmass_U⟩

private theorem scalar_coeff_limit_subseq_with_head_mass_wip
    {d : Nat} (kappa : MultiIndex d)
    (K : Finset (Idx d)) {rho : ℝ}
    (H : ℕ -> Pkappa d kappa) (t : ℕ -> ℝ)
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hmass : ∀ m, rho <=
      Finset.sum K (fun alpha => ‖coeffPkappa (H m) alpha‖ ^ 2))
    (ht_mem : ∀ m, t m ∈ Set.Icc (0 : ℝ) 4) :
    ∃ T : ℝ, ∃ U : Skappa d kappa, ∃ φ : ℕ -> ℕ,
      T ∈ Set.Icc (0 : ℝ) 4 ∧
      StrictMono φ ∧
      Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds T) ∧
      (∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha) Filter.atTop
        (nhds (coeffSkappa U alpha))) ∧
      (∀ E : Finset (Idx d),
        Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1) ∧
      rho <= Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) := by
  obtain ⟨T, hT_closure, ψ, hψ_strict, hψ_tendsto⟩ :=
    tendsto_subseq_of_bounded
      (s := Set.Icc (0 : ℝ) 4)
      (Metric.isBounded_Icc (0 : ℝ) 4)
      ht_mem
  have hT_mem : T ∈ Set.Icc (0 : ℝ) 4 := by simpa [closure_Icc] using hT_closure
  obtain ⟨U, φ, hφ_strict, hcoeff, hpartial, hmass_U⟩ :=
    coeff_limit_subseq_with_head_mass_wip kappa K
      (fun m => H (ψ m))
      (fun m => hH_norm (ψ m))
      (fun m => hmass (ψ m))
  let σ : ℕ -> ℕ := fun m => ψ (φ m)
  have hσ_strict : StrictMono σ := by exact hψ_strict.comp hφ_strict
  have hσ_t_tendsto :
      Filter.Tendsto (fun m => t (σ m)) Filter.atTop (nhds T) :=
    hψ_tendsto.comp hφ_strict.tendsto_atTop
  have hσ_coeff :
      ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (σ m)) alpha)
        Filter.atTop (nhds (coeffSkappa U alpha)) := by
    intro alpha
    simpa [σ] using hcoeff alpha
  exact ⟨T, U, σ, hT_mem, hσ_strict, hσ_t_tendsto, hσ_coeff, hpartial, hmass_U⟩

private theorem finite_head_mass_contradiction_of_coeff_zero_wip
    {d : Nat} {kappa : MultiIndex d} (K : Finset (Idx d)) {rho : ℝ}
    (h_rho : 0 < rho) {U : Skappa d kappa}
    (hmass : rho <= Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2))
    (hzero : ∀ alpha, coeffSkappa U alpha = 0) :
    False := by
  have hsum_zero :
      Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) = 0 := by simp [hzero]
  nlinarith

private theorem bad_sequence_of_no_finite_head_lower_bound_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa) (K : Finset (Idx d)) (rho : ℝ)
    (hbad :
      ¬ ∃ delta : ℝ, 0 < delta ∧
        ∀ {H : Pkappa d kappa} {t : ℝ},
          orthogonalToPk F H ->
          ‖H‖ = 1 ->
          rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ->
          0 < t ->
          t <= 4 ->
          delta * t <= defect F (t • H)) :
    ∀ n : ℕ, ∃ H : Pkappa d kappa, ∃ t : ℝ,
      orthogonalToPk F H ∧
      ‖H‖ = 1 ∧
      rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ∧
      0 < t ∧
      t <= 4 ∧
      defect F (t • H) < (1 / ((n + 1 : Nat) : ℝ)) * t := by
  intro n
  let delta : ℝ := 1 / ((n + 1 : Nat) : ℝ)
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    positivity
  by_contra hno
  apply hbad
  refine ⟨delta, hdelta_pos, ?_⟩
  intro H t horth hH_norm hmass ht_pos ht_le_four
  by_contra hnot
  have hlt : defect F (t • H) < delta * t := lt_of_not_ge hnot
  exact hno ⟨H, t, horth, hH_norm, hmass, ht_pos, ht_le_four, hlt⟩

private theorem finite_head_bad_limit_data_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa) (K : Finset (Idx d)) {rho : ℝ}
    (hbad :
      ¬ ∃ delta : ℝ, 0 < delta ∧
        ∀ {H : Pkappa d kappa} {t : ℝ},
          orthogonalToPk F H ->
          ‖H‖ = 1 ->
          rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ->
          0 < t ->
          t <= 4 ->
          delta * t <= defect F (t • H)) :
    ∃ H : ℕ -> Pkappa d kappa, ∃ t : ℕ -> ℝ,
      ∃ T : ℝ, ∃ U : Skappa d kappa, ∃ φ : ℕ -> ℕ,
        T ∈ Set.Icc (0 : ℝ) 4 ∧
        StrictMono φ ∧
        Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds T) ∧
        (∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
          Filter.atTop (nhds (coeffSkappa U alpha))) ∧
        (∀ E : Finset (Idx d),
          Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1) ∧
        rho <= Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) ∧
        (∀ m, orthogonalToPk F (H m)) ∧
        (∀ m, ‖H m‖ = 1) ∧
        (∀ m, rho <= Finset.sum K (fun alpha => ‖coeffPkappa (H m) alpha‖ ^ 2)) ∧
        (∀ m, 0 < t m) ∧
        (∀ m, t m <= 4) ∧
        (∀ m, defect F (t m • H m) <
          (1 / ((m + 1 : Nat) : ℝ)) * t m) ∧
        orthogonalToSkappa_wip F U := by
  have hseq := bad_sequence_of_no_finite_head_lower_bound_wip F K rho hbad
  choose H t horth hH_norm hmass ht_pos ht_le hdef using hseq
  have ht_mem : ∀ m, t m ∈ Set.Icc (0 : ℝ) 4 := by
    intro m
    exact Set.mem_Icc.mpr ⟨le_of_lt (ht_pos m), ht_le m⟩
  obtain ⟨T, U, φ, hT_mem, hφ_strict, ht_tendsto, hcoeff, hpartial, hmass_U⟩ :=
    scalar_coeff_limit_subseq_with_head_mass_wip kappa K H t hH_norm hmass ht_mem
  have horth_U : orthogonalToSkappa_wip F U := by
    exact orthogonalToSkappa_of_coeff_tendsto_wip
      (F := F) (H := fun m => H (φ m)) (U := U)
      (fun m => horth (φ m)) hcoeff
  exact
    ⟨H, t, T, U, φ, hT_mem, hφ_strict, ht_tendsto, hcoeff, hpartial,
      hmass_U, horth, hH_norm, hmass, ht_pos, ht_le, hdef, horth_U⟩

private theorem bad_sequence_of_no_finite_head_lower_bound_positiveGauge_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa) (K : Finset (Idx d)) (rho : ℝ)
    (hbad :
      ¬ ∃ delta : ℝ, 0 < delta ∧
        ∀ {H : Pkappa d kappa} {t : ℝ},
          positivePhaseGauge F (F + t • H) ->
          ‖H‖ = 1 ->
          rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ->
          0 < t ->
          t <= 4 ->
          delta * t <= defect F (t • H)) :
    ∀ n : ℕ, ∃ H : Pkappa d kappa, ∃ t : ℝ,
      positivePhaseGauge F (F + t • H) ∧
      ‖H‖ = 1 ∧
      rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ∧
      0 < t ∧
      t <= 4 ∧
      defect F (t • H) < (1 / ((n + 1 : Nat) : ℝ)) * t := by
  intro n
  let delta : ℝ := 1 / ((n + 1 : Nat) : ℝ)
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    positivity
  by_contra hno
  apply hbad
  refine ⟨delta, hdelta_pos, ?_⟩
  intro H t hpos hH_norm hmass ht_pos ht_le_four
  by_contra hnot
  have hlt : defect F (t • H) < delta * t := lt_of_not_ge hnot
  exact hno ⟨H, t, hpos, hH_norm, hmass, ht_pos, ht_le_four, hlt⟩

private theorem finite_head_bad_limit_data_positiveGauge_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa) (K : Finset (Idx d)) {rho : ℝ}
    (hbad :
      ¬ ∃ delta : ℝ, 0 < delta ∧
        ∀ {H : Pkappa d kappa} {t : ℝ},
          positivePhaseGauge F (F + t • H) ->
          ‖H‖ = 1 ->
          rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ->
          0 < t ->
          t <= 4 ->
          delta * t <= defect F (t • H)) :
    ∃ H : ℕ -> Pkappa d kappa, ∃ t : ℕ -> ℝ,
      ∃ T : ℝ, ∃ U : Skappa d kappa, ∃ φ : ℕ -> ℕ,
        T ∈ Set.Icc (0 : ℝ) 4 ∧
        StrictMono φ ∧
        Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds T) ∧
        (∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
          Filter.atTop (nhds (coeffSkappa U alpha))) ∧
        (∀ E : Finset (Idx d),
          Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1) ∧
        rho <= Finset.sum K (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) ∧
        (∀ m, positivePhaseGauge F (F + t m • H m)) ∧
        (∀ m, ‖H m‖ = 1) ∧
        (∀ m, rho <= Finset.sum K (fun alpha => ‖coeffPkappa (H m) alpha‖ ^ 2)) ∧
        (∀ m, 0 < t m) ∧
        (∀ m, t m <= 4) ∧
        (∀ m, defect F (t m • H m) <
          (1 / ((m + 1 : Nat) : ℝ)) * t m) := by
  have hseq := bad_sequence_of_no_finite_head_lower_bound_positiveGauge_wip F K rho hbad
  choose H t hpos hH_norm hmass ht_pos ht_le hdef using hseq
  have ht_mem : ∀ m, t m ∈ Set.Icc (0 : ℝ) 4 := by
    intro m
    exact Set.mem_Icc.mpr ⟨le_of_lt (ht_pos m), ht_le m⟩
  obtain ⟨T, U, φ, hT_mem, hφ_strict, ht_tendsto, hcoeff, hpartial, hmass_U⟩ :=
    scalar_coeff_limit_subseq_with_head_mass_wip kappa K H t hH_norm hmass ht_mem
  exact
    ⟨H, t, T, U, φ, hT_mem, hφ_strict, ht_tendsto, hcoeff, hpartial,
      hmass_U, hpos, hH_norm, hmass, ht_pos, ht_le, hdef⟩

private theorem positiveGauge_im_inner_normed_perturbation_wip
    {d : Nat} {kappa : MultiIndex d}
    {F H : Pkappa d kappa} (hF_norm : ‖F‖ = 1)
    {t : ℝ} (ht_pos : 0 < t)
    (hpos : positivePhaseGauge F (F + t • H)) :
    (pkappaInner H F).im = 0 := by
  have him := hpos.1
  rw [pkappaInner_add_left_wip, pkappaInner_smul_left_real_wip,
    pkappaInner_self_of_norm_one_wip hF_norm] at him
  have htim : t * (pkappaInner H F).im = 0 := by simpa using him
  exact (mul_eq_zero.mp htim).resolve_left ht_pos.ne'

private theorem positiveGauge_limit_inner_im_zero_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1)
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ} {U : Skappa d kappa} {φ : ℕ -> ℕ}
    (hpos : ∀ m, positivePhaseGauge F (F + t m • H m))
    (ht_pos : ∀ m, 0 < t m)
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
      Filter.atTop (nhds (coeffSkappa U alpha))) :
    (Finset.sum F.support
      (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha))).im = 0 := by
  have hlim := skappaInnerAgainstPk_tendsto_wip (F := F) (H := fun m => H (φ m))
    (U := U) hcoeff
  have hlim_im :
      Filter.Tendsto
        (fun m => (pkappaInner (H (φ m)) F).im)
        Filter.atTop
        (nhds (Finset.sum F.support
          (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha))).im) :=
    Complex.continuous_im.tendsto _ |>.comp hlim
  have hzero :
      (fun m => (pkappaInner (H (φ m)) F).im) = fun _ : ℕ => (0 : ℝ) := by
    funext m
    exact positiveGauge_im_inner_normed_perturbation_wip hF_norm
      (ht_pos (φ m)) (hpos (φ m))
  have hzero_lim :
      Filter.Tendsto
        (fun m => (pkappaInner (H (φ m)) F).im)
        Filter.atTop (nhds (0 : ℝ)) := by
    rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim_im hzero_lim

private theorem unit_complex_of_real_nonneg_wip {w : ℂ}
    (hw : ‖w‖ = 1) (him : w.im = 0) (hre : 0 ≤ w.re) :
    w = 1 := by
  apply Complex.ext
  · have hnormsq : w.re * w.re + w.im * w.im = 1 := by
      calc
        w.re * w.re + w.im * w.im = Complex.normSq w := (Complex.normSq_apply w).symm
        _ = ‖w‖ ^ 2 := Complex.normSq_eq_norm_sq w
        _ = 1 := by rw [hw]; norm_num
    have hsq : w.re ^ 2 = (1 : ℝ) ^ 2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · simpa using h
    · nlinarith
  · simpa using him

private theorem positiveGauge_limit_affine_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa}
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ} {T : ℝ} {U : Skappa d kappa}
    {φ : ℕ -> ℕ}
    (hpos : ∀ m, positivePhaseGauge F (F + t m • H m))
    (ht_tendsto : Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds T))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
      Filter.atTop (nhds (coeffSkappa U alpha))) :
    let L : ℂ :=
      Finset.sum F.support
        (fun alpha =>
          (coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha) *
            star (coeffPkappa F alpha))
    L.im = 0 ∧ 0 ≤ L.re := by
  let L : ℂ :=
    Finset.sum F.support
      (fun alpha =>
        (coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha) *
          star (coeffPkappa F alpha))
  have hlim_H := skappaInnerAgainstPk_tendsto_wip (F := F) (H := fun m => H (φ m))
    (U := U) hcoeff
  have ht_complex :
      Filter.Tendsto (fun m => ((t (φ m) : ℝ) : ℂ)) Filter.atTop (nhds (T : ℂ)) :=
    Complex.continuous_ofReal.tendsto T |>.comp ht_tendsto
  have hlim :
      Filter.Tendsto
        (fun m => pkappaInner (F + t (φ m) • H (φ m)) F)
        Filter.atTop (nhds L) := by
    have hsum :
        Filter.Tendsto
          (fun m => pkappaInner F F + (t (φ m) : ℂ) * pkappaInner (H (φ m)) F)
          Filter.atTop
          (nhds
            (pkappaInner F F +
              (T : ℂ) *
                Finset.sum F.support
                  (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha)))) :=
      tendsto_const_nhds.add (ht_complex.mul hlim_H)
    have htarget :
        pkappaInner F F +
            (T : ℂ) *
              Finset.sum F.support
                (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha)) =
          L := by
      rw [pkappaInner_eq_sum_right_support_wip]
      dsimp [L]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro alpha halpha
      simp [coeffPkappa]
      ring
    have hseq_eq :
        (fun m => pkappaInner (F + t (φ m) • H (φ m)) F) =
          fun m => pkappaInner F F + (t (φ m) : ℂ) * pkappaInner (H (φ m)) F := by
      funext m
      rw [pkappaInner_add_left_wip, pkappaInner_smul_left_real_wip]
    simpa [hseq_eq, ← htarget] using hsum
  have him_lim :
      Filter.Tendsto
        (fun m => (pkappaInner (F + t (φ m) • H (φ m)) F).im)
        Filter.atTop (nhds L.im) :=
    Complex.continuous_im.tendsto _ |>.comp hlim
  have him_zero_lim :
      Filter.Tendsto
        (fun m => (pkappaInner (F + t (φ m) • H (φ m)) F).im)
        Filter.atTop (nhds (0 : ℝ)) := by
    rw [show
        (fun m => (pkappaInner (F + t (φ m) • H (φ m)) F).im) =
          fun _ : ℕ => (0 : ℝ) by
      funext m
      exact (hpos (φ m)).1]
    exact tendsto_const_nhds
  have hL_im : L.im = 0 := tendsto_nhds_unique him_lim him_zero_lim
  have hre_lim :
      Filter.Tendsto
        (fun m => (pkappaInner (F + t (φ m) • H (φ m)) F).re)
        Filter.atTop (nhds L.re) :=
    Complex.continuous_re.tendsto _ |>.comp hlim
  have hL_re : 0 ≤ L.re :=
    ge_of_tendsto hre_lim (Filter.Eventually.of_forall fun m => (hpos (φ m)).2)
  exact ⟨hL_im, hL_re⟩

private theorem defect_nonneg_wip
    {d : Nat} {kappa : MultiIndex d}
    (F G : Pkappa d kappa) :
    0 <= defect F G := Real.sqrt_nonneg _

private lemma continuous_Phi_coeff_wip
    {d : Nat} (kappa alpha : MultiIndex d) :
    Continuous (Phi kappa alpha) := by
  unfold Phi phi1D complexHermite
  continuity

private lemma continuous_evalPkappa_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    Continuous (evalPkappa kappa F) := by
  unfold evalPkappa
  refine continuous_finsetSum _ ?_
  intro alpha halpha
  exact continuous_const.mul (continuous_Phi_coeff_wip kappa alpha)

private def defectFunctionPkappa_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    Cd d -> ℝ :=
  fun z => |‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖|

private lemma norm_sq_add_real_smul_wip (a w : ℂ) (t : ℝ) :
    ‖a + (t : ℂ) * w‖ ^ 2 =
      ‖a‖ ^ 2 + t ^ 2 * ‖w‖ ^ 2 + 2 * t * Complex.re (w * star a) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, ← Complex.normSq_eq_norm_sq]
  have hsq : Complex.normSq ((t : ℂ) * w) = t ^ 2 * ‖w‖ ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
    ring
  rw [hsq]
  have hre :
      Complex.re (a * star ((t : ℂ) * w)) = t * Complex.re (w * star a) := by
    have hstar : star ((t : ℂ) * w) = (t : ℂ) * star w := by simp
    rw [hstar]
    have hmul : a * ((t : ℂ) * star w) = (a * star w) * (t : ℂ) := by ring
    rw [hmul, Complex.re_mul_ofReal]
    have hre' : Complex.re (a * star w) = Complex.re (w * star a) := by
      simp [Complex.mul_re, sub_eq_add_neg, mul_comm]
    rw [hre']
    ring
  have hre' :
      (a * (starRingEnd ℂ) ((t : ℂ) * w)).re =
        t * Complex.re (w * star a) := by simpa using hre
  rw [hre']
  ring

private lemma defectFunction_div_eq_abs_linearization_wip
    (a w : ℂ) {t : ℝ} (ht : 0 < t) :
    |‖a + (t : ℂ) * w‖ - ‖a‖| / t *
        (‖a + (t : ℂ) * w‖ + ‖a‖) =
      |2 * Complex.re (w * star a) + t * ‖w‖ ^ 2| := by
  have hmul :
      |‖a + (t : ℂ) * w‖ - ‖a‖| *
          (‖a + (t : ℂ) * w‖ + ‖a‖) =
        |2 * t * Complex.re (w * star a) + t ^ 2 * ‖w‖ ^ 2| := by
    have hnonneg : 0 <= ‖a + (t : ℂ) * w‖ + ‖a‖ := by positivity
    rw [← abs_of_nonneg hnonneg, ← abs_mul]
    have hsq := norm_sq_add_real_smul_wip a w t
    have hprod :
        (‖a + (t : ℂ) * w‖ - ‖a‖) *
            (‖a + (t : ℂ) * w‖ + ‖a‖) =
          2 * t * Complex.re (w * star a) + t ^ 2 * ‖w‖ ^ 2 := by nlinarith
    exact congrArg abs hprod
  have ht0 : t ≠ 0 := ne_of_gt ht
  calc
    |‖a + (t : ℂ) * w‖ - ‖a‖| / t *
        (‖a + (t : ℂ) * w‖ + ‖a‖)
        = (|‖a + (t : ℂ) * w‖ - ‖a‖| *
            (‖a + (t : ℂ) * w‖ + ‖a‖)) / t := by field_simp [ht0]
    _ = |2 * t * Complex.re (w * star a) + t ^ 2 * ‖w‖ ^ 2| / t := by rw [hmul]
    _ = |t * (2 * Complex.re (w * star a) + t * ‖w‖ ^ 2)| / t := by
          congr 1
          ring_nf
    _ = |t| * |2 * Complex.re (w * star a) + t * ‖w‖ ^ 2| / t := by rw [abs_mul]
    _ = |2 * Complex.re (w * star a) + t * ‖w‖ ^ 2| := by
          rw [abs_of_pos ht, mul_div_cancel_left₀ _ ht0]

private lemma continuous_defectFunctionPkappa_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    Continuous (defectFunctionPkappa_coeff_wip kappa F G) := by
  unfold defectFunctionPkappa_coeff_wip
  exact (((continuous_evalPkappa_coeff_wip kappa (F + G)).norm.sub
    (continuous_evalPkappa_coeff_wip kappa F).norm).abs)

private theorem pkappa_eq_zero_of_norm_eq_zero_coeff_wip
    {d : Nat} {kappa : MultiIndex d} {F : Pkappa d kappa}
    (hnorm : ‖F‖ = 0) :
    F = 0 := by
  ext alpha
  by_contra hne
  have hmem : alpha ∈ F.support := Finsupp.mem_support_iff.mpr hne
  have hterm_pos : 0 < ‖F alpha‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  have hle :
      ‖F alpha‖ ^ 2 <= Finset.sum F.support (fun beta => ‖coeffPkappa F beta‖ ^ 2) := by
    simpa [coeffPkappa] using
      (Finset.single_le_sum
        (f := fun beta : Idx d => ‖F beta‖ ^ 2) (s := F.support) (a := alpha)
        (fun beta _ => by positivity) hmem)
  have hsum_pos : 0 < Finset.sum F.support (fun beta => ‖coeffPkappa F beta‖ ^ 2) :=
    lt_of_lt_of_le hterm_pos hle
  have hnorm_sq := norm_sq_eq_sum_coeff_wip F
  nlinarith

private theorem norm_ne_zero_of_ne_zero_pkappa_coeff_wip
    {d : Nat} {kappa : MultiIndex d} {F : Pkappa d kappa}
    (hF : F ≠ 0) :
    ‖F‖ ≠ 0 := by
  intro hnorm
  exact hF (pkappa_eq_zero_of_norm_eq_zero_coeff_wip hnorm)

private theorem integrable_evalPkappa_sq_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.Integrable
      (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) := by
  by_cases hF : F = 0
  · subst hF
    simp [evalPkappa]
  · have hmeas :
        MeasureTheory.AEStronglyMeasurable (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2)
          (gammaD d) :=
      ((continuous_evalPkappa_coeff_wip kappa F).norm.pow 2).stronglyMeasurable.aestronglyMeasurable
    by_contra hInt
    have hundef :
        (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = 0 :=
      MeasureTheory.integral_undef hInt
    have hmass :
        (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = ‖F‖ ^ 2 :=
      evalPkappa_total_mass hd kappa F
    have hnorm_ne : ‖F‖ ≠ 0 := norm_ne_zero_of_ne_zero_pkappa_coeff_wip hF
    have hnorm_pos : 0 < ‖F‖ := lt_of_le_of_ne (Real.sqrt_nonneg _) hnorm_ne.symm
    nlinarith

private theorem gaussianL2Norm_eq_lpNorm_coeff_wip
    {d : Nat} {α : Type*} [NormedAddCommGroup α] [MeasurableSpace α] [NormedSpace ℝ α]
    [BorelSpace α] (F : Cd d -> α)
    (hF : MeasureTheory.AEStronglyMeasurable F (gammaD d)) :
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      MeasureTheory.lpNorm F 2 (gammaD d) := by
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := gammaD d) (p := (2 : NNReal)) (f := F) htwo hF
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      MeasureTheory.lpNorm F (↑(2 : NNReal)) (gammaD d)
  rw [hlp]
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) ^ ((2 : ℝ)⁻¹)
  rw [Real.sqrt_eq_rpow]
  norm_num

private theorem memLp_two_evalPkappa_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.MemLp (evalPkappa kappa F) 2 (gammaD d) := by
  let _ := hd
  have hmeas :
      MeasureTheory.AEStronglyMeasurable (evalPkappa kappa F) (gammaD d) :=
    (continuous_evalPkappa_coeff_wip kappa F).stronglyMeasurable.aestronglyMeasurable
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).2
      (integrable_evalPkappa_sq_coeff_wip hd kappa F)

private theorem evalPkappa_lpNorm_eq_norm_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.lpNorm (evalPkappa kappa F) 2 (gammaD d) = ‖F‖ := by
  have hpow :
      (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ (2 : ℝ) ∂ gammaD d) =
        ∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d := by
    congr 1
    ext z
    exact Real.rpow_natCast ‖evalPkappa kappa F z‖ 2
  calc
    MeasureTheory.lpNorm (evalPkappa kappa F) 2 (gammaD d)
        = Real.sqrt
            (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ (2 : ℝ) ∂ gammaD d) := by
          symm
          exact gaussianL2Norm_eq_lpNorm_coeff_wip (evalPkappa kappa F)
            (memLp_two_evalPkappa_coeff_wip hd kappa F).1
    _ = Real.sqrt
          (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) := by rw [hpow]
    _ = ‖F‖ := by
          rw [evalPkappa_total_mass hd kappa F, Real.sqrt_sq_eq_abs]
          exact abs_of_nonneg (Real.sqrt_nonneg _)

private theorem memLp_two_defectFunctionPkappa_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    MeasureTheory.MemLp (defectFunctionPkappa_coeff_wip kappa F G) 2 (gammaD d) := by
  let _ := hd
  have hmeas :
      MeasureTheory.AEStronglyMeasurable (defectFunctionPkappa_coeff_wip kappa F G) (gammaD d) :=
    (continuous_defectFunctionPkappa_coeff_wip kappa F G).stronglyMeasurable.aestronglyMeasurable
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hplus_int :
      MeasureTheory.Integrable
        (fun z : Cd d => 2 * ‖evalPkappa kappa (F + G) z‖ ^ 2) (gammaD d) :=
    (integrable_evalPkappa_sq_coeff_wip hd kappa (F + G)).const_mul 2
  have hbase_int :
      MeasureTheory.Integrable
        (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) :=
    (integrable_evalPkappa_sq_coeff_wip hd kappa F).const_mul 2
  have hsq :
      MeasureTheory.Integrable
        (fun z : Cd d =>
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2)
        (gammaD d) := hplus_int.add hbase_int
  have hmeasSq :
      MeasureTheory.AEStronglyMeasurable
        (fun z : Cd d => defectFunctionPkappa_coeff_wip kappa F G z ^ 2) (gammaD d) :=
    (continuous_defectFunctionPkappa_coeff_wip kappa F G).pow 2
      |>.stronglyMeasurable.aestronglyMeasurable
  have hbound :
      ∀ᵐ z ∂ gammaD d,
        ‖defectFunctionPkappa_coeff_wip kappa F G z ^ 2‖ <=
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2 := by
    filter_upwards with z
    have hsqz :
        defectFunctionPkappa_coeff_wip kappa F G z ^ 2 <=
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2 := by
      unfold defectFunctionPkappa_coeff_wip
      have : (‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖) ^ 2 <=
          2 * ‖evalPkappa kappa (F + G) z‖ ^ 2 + 2 * ‖evalPkappa kappa F z‖ ^ 2 := by
        nlinarith [sq_nonneg (‖evalPkappa kappa (F + G) z‖ + ‖evalPkappa kappa F z‖)]
      simpa [sq_abs] using this
    have hnonneg : 0 <= defectFunctionPkappa_coeff_wip kappa F G z ^ 2 := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hsqz
  simpa [Real.norm_eq_abs, abs_of_nonneg] using
    MeasureTheory.Integrable.mono' hsq hmeasSq hbound

private theorem defect_lpNorm_eq_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    defect F G =
      MeasureTheory.lpNorm (defectFunctionPkappa_coeff_wip kappa F G) 2 (gammaD d) := by
  let _ := hd
  simpa [defect, defectFunctionPkappa_coeff_wip, Real.norm_eq_abs, sq_abs] using
    gaussianL2Norm_eq_lpNorm_coeff_wip (defectFunctionPkappa_coeff_wip kappa F G)
      (memLp_two_defectFunctionPkappa_coeff_wip hd kappa F G).1

private theorem finite_head_bad_limit_eval_tendsto_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa)
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ}
    {T : ℝ} {U : Skappa d kappa} {φ : ℕ -> ℕ}
    (ht_tendsto : Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds T))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
      Filter.atTop (nhds (coeffSkappa U alpha)))
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hpartial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1)
    (z : Cd d) :
    Filter.Tendsto
      (fun m => evalPkappa kappa (F + t (φ m) • H (φ m)) z)
      Filter.atTop
      (nhds (evalPkappa kappa F z + (T : ℂ) * toFun kappa U z)) := by
  exact evalPkappa_add_smul_tendsto_toFun_wip
    (kappa := kappa) F
    (H := fun m => H (φ m)) (U := U)
    (t := fun m => t (φ m)) (T := T)
    ht_tendsto hcoeff (fun m => hH_norm (φ m)) hpartial z

private theorem finite_head_bad_limit_defect_tendsto_zero_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa}
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ} {φ : ℕ -> ℕ}
    (hφ_strict : StrictMono φ)
    (ht_le : ∀ m, t m <= 4)
    (hdef : ∀ m, defect F (t m • H m) <
      (1 / ((m + 1 : Nat) : ℝ)) * t m) :
    Filter.Tendsto
      (fun m => defect F (t (φ m) • H (φ m)))
      Filter.atTop (nhds 0) := by
  refine squeeze_zero
    (f := fun m => defect F (t (φ m) • H (φ m)))
    (g := fun m : ℕ => 4 * (1 / (((m + 1 : Nat) : ℝ))))
    (fun m => defect_nonneg_wip F (t (φ m) • H (φ m))) ?_ ?_
  · intro m
    have hφ_ge : m <= φ m := hφ_strict.id_le m
    have hden :
        (((m + 1 : Nat) : ℝ)) <= (((φ m + 1 : Nat) : ℝ)) := by exact_mod_cast Nat.succ_le_succ hφ_ge
    have hrecip :
        (1 / (((φ m + 1 : Nat) : ℝ))) <=
          (1 / (((m + 1 : Nat) : ℝ))) := one_div_le_one_div_of_le (by positivity) hden
    have hupper :
        (1 / (((φ m + 1 : Nat) : ℝ))) * t (φ m) <=
          4 * (1 / (((m + 1 : Nat) : ℝ))) := by
      calc
        (1 / (((φ m + 1 : Nat) : ℝ))) * t (φ m)
            <= (1 / (((φ m + 1 : Nat) : ℝ))) * 4 :=
              mul_le_mul_of_nonneg_left (ht_le (φ m)) (by positivity)
        _ <= (1 / (((m + 1 : Nat) : ℝ))) * 4 := mul_le_mul_of_nonneg_right hrecip (by norm_num)
        _ = 4 * (1 / (((m + 1 : Nat) : ℝ))) := by ring
    exact le_trans (le_of_lt (hdef (φ m))) hupper
  · have hbase :
        Filter.Tendsto
          (fun m : ℕ => (1 / (((m + 1 : Nat) : ℝ))))
          Filter.atTop (nhds 0) := by
      convert
        (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
          (fun m : ℕ => (1 / ((m : ℝ) + 1)))
          Filter.atTop (nhds 0)) using 1
      ext m
      norm_num
    have hmul :
        Filter.Tendsto
          (fun m : ℕ => 4 * (1 / (((m + 1 : Nat) : ℝ))))
          Filter.atTop (nhds (4 * 0)) :=
      tendsto_const_nhds.mul hbase
    simpa using hmul

private theorem finite_head_bad_limit_defect_ae_tendsto_zero_wip
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    {F : Pkappa d kappa}
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ} {φ : ℕ -> ℕ}
    (hφ_strict : StrictMono φ)
    (ht_le : ∀ m, t m <= 4)
    (hdef : ∀ m, defect F (t m • H m) <
      (1 / ((m + 1 : Nat) : ℝ)) * t m) :
    ∃ ψ : ℕ -> ℕ, StrictMono ψ ∧
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m =>
            defectFunctionPkappa_coeff_wip kappa F
              (t (φ (ψ m)) • H (φ (ψ m))) z)
          Filter.atTop (nhds 0) := by
  let f : ℕ -> Cd d -> ℝ := fun m =>
    defectFunctionPkappa_coeff_wip kappa F (t (φ m) • H (φ m))
  have hdef_tendsto :
      Filter.Tendsto
        (fun m => defect F (t (φ m) • H (φ m)))
        Filter.atTop (nhds 0) :=
    finite_head_bad_limit_defect_tendsto_zero_wip hφ_strict ht_le hdef
  have hf_meas :
      ∀ m, MeasureTheory.AEStronglyMeasurable (f m) (gammaD d) := by
    intro m
    exact (continuous_defectFunctionPkappa_coeff_wip kappa F
      (t (φ m) • H (φ m))).stronglyMeasurable.aestronglyMeasurable
  have hf_mem :
      ∀ m, MeasureTheory.MemLp (f m) 2 (gammaD d) := by
    intro m
    exact memLp_two_defectFunctionPkappa_coeff_wip hd kappa F
      (t (φ m) • H (φ m))
  have heLp_eq :
      ∀ m,
        MeasureTheory.eLpNorm (f m - fun _ : Cd d => (0 : ℝ)) 2 (gammaD d) =
          ENNReal.ofReal (defect F (t (φ m) • H (φ m))) := by
    intro m
    have hsub : (f m - fun _ : Cd d => (0 : ℝ)) = f m := by
      funext z
      simp
    rw [hsub,
      ← MeasureTheory.ofReal_lpNorm (hf_mem m),
      ← defect_lpNorm_eq_coeff_wip hd kappa F (t (φ m) • H (φ m))]
  have heLp_tendsto :
      Filter.Tendsto
        (fun m =>
          MeasureTheory.eLpNorm (f m - fun _ : Cd d => (0 : ℝ)) 2 (gammaD d))
        Filter.atTop (nhds 0) := by
    have hfun :
        (fun m =>
          MeasureTheory.eLpNorm (f m - fun _ : Cd d => (0 : ℝ)) 2 (gammaD d)) =
        fun m => ENNReal.ofReal (defect F (t (φ m) • H (φ m)) : ℝ) := by
      funext m
      exact heLp_eq m
    rw [hfun]
    simpa using ENNReal.tendsto_ofReal hdef_tendsto
  have hzero_meas :
      MeasureTheory.AEStronglyMeasurable (fun _ : Cd d => (0 : ℝ)) (gammaD d) :=
    (continuous_const : Continuous (fun _ : Cd d => (0 : ℝ)))
      |>.stronglyMeasurable.aestronglyMeasurable
  have hInMeasure :
      MeasureTheory.TendstoInMeasure (gammaD d) f Filter.atTop (fun _ : Cd d => (0 : ℝ)) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (p := (2 : ENNReal)) (μ := gammaD d)
      (f := f) (g := fun _ : Cd d => (0 : ℝ))
      (by norm_num) hf_meas hzero_meas heLp_tendsto
  obtain ⟨ψ, hψ_strict, hψ_ae⟩ := hInMeasure.exists_seq_tendsto_ae
  refine ⟨ψ, hψ_strict, ?_⟩
  filter_upwards [hψ_ae] with z hz
  simpa [f] using hz

private theorem finite_head_bad_limit_defect_quotient_ae_tendsto_zero_wip
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    {F : Pkappa d kappa}
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ} {φ : ℕ -> ℕ}
    (hφ_strict : StrictMono φ)
    (ht_pos : ∀ m, 0 < t m)
    (hdef : ∀ m, defect F (t m • H m) <
      (1 / ((m + 1 : Nat) : ℝ)) * t m) :
    ∃ ψ : ℕ -> ℕ, StrictMono ψ ∧
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m =>
            defectFunctionPkappa_coeff_wip kappa F
              (t (φ (ψ m)) • H (φ (ψ m))) z / t (φ (ψ m)))
          Filter.atTop (nhds 0) := by
  let f : ℕ -> Cd d -> ℝ := fun m z =>
    defectFunctionPkappa_coeff_wip kappa F (t (φ m) • H (φ m)) z / t (φ m)
  have hf_eq :
      ∀ m,
        f m =
          ((t (φ m))⁻¹ : ℝ) •
            defectFunctionPkappa_coeff_wip kappa F (t (φ m) • H (φ m)) := by
    intro m
    funext z
    simp [f, Pi.smul_apply, div_eq_mul_inv, mul_comm]
  have hf_meas :
      ∀ m, MeasureTheory.AEStronglyMeasurable (f m) (gammaD d) := by
    intro m
    change MeasureTheory.AEStronglyMeasurable
      (fun z : Cd d =>
        defectFunctionPkappa_coeff_wip kappa F (t (φ m) • H (φ m)) z / t (φ m))
      (gammaD d)
    exact ((continuous_defectFunctionPkappa_coeff_wip kappa F
      (t (φ m) • H (φ m))).div_const (t (φ m))).stronglyMeasurable.aestronglyMeasurable
  have hf_mem :
      ∀ m, MeasureTheory.MemLp (f m) 2 (gammaD d) := by
    intro m
    rw [hf_eq m]
    exact (memLp_two_defectFunctionPkappa_coeff_wip hd kappa F
      (t (φ m) • H (φ m))).const_smul ((t (φ m))⁻¹ : ℝ)
  have hbound :
      ∀ m,
        MeasureTheory.eLpNorm (f m) 2 (gammaD d) <=
          ENNReal.ofReal (1 / ((m + 1 : Nat) : ℝ)) := by
    intro m
    have hf_mem_m := hf_mem m
    have hfin : MeasureTheory.eLpNorm (f m) 2 (gammaD d) ≠ ⊤ := by simpa using hf_mem_m.2.ne
    refine (ENNReal.le_ofReal_iff_toReal_le hfin (by positivity)).2 ?_
    rw [MeasureTheory.toReal_eLpNorm hf_mem_m.1, hf_eq m,
      MeasureTheory.lpNorm_const_smul]
    rw [← defect_lpNorm_eq_coeff_wip hd kappa F (t (φ m) • H (φ m))]
    have hratio :
        defect F (t (φ m) • H (φ m)) / t (φ m) <
          1 / (((φ m + 1 : Nat) : ℝ)) := by
      have hdiv :=
        div_lt_div_of_pos_right (hdef (φ m)) (ht_pos (φ m))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
        (ht_pos (φ m)).ne'] using hdiv
    have hφ_ge : m <= φ m := hφ_strict.id_le m
    have hden :
        (((m + 1 : Nat) : ℝ)) <= (((φ m + 1 : Nat) : ℝ)) := by exact_mod_cast Nat.succ_le_succ hφ_ge
    have hfinal :
        defect F (t (φ m) • H (φ m)) / t (φ m) <=
          1 / (((m + 1 : Nat) : ℝ)) := (le_of_lt hratio).trans
        (one_div_le_one_div_of_le (by positivity) hden)
    simpa [Real.norm_eq_abs, abs_of_pos (ht_pos (φ m)), div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hfinal
  have htarget :
      Filter.Tendsto
        (fun m : ℕ => ENNReal.ofReal (1 / ((m + 1 : Nat) : ℝ)))
        Filter.atTop (nhds 0) := by
    have hbase :
        Filter.Tendsto
          (fun m : ℕ => (1 / ((m + 1 : Nat) : ℝ)))
          Filter.atTop (nhds 0) := by
      convert
        (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
          (fun m : ℕ => (1 / ((m : ℝ) + 1)))
          Filter.atTop (nhds 0)) using 1
      ext m
      norm_num
    simpa using ENNReal.tendsto_ofReal hbase
  have heLp_tendsto :
      Filter.Tendsto
        (fun m =>
          MeasureTheory.eLpNorm (f m - fun _ : Cd d => (0 : ℝ)) 2 (gammaD d))
        Filter.atTop (nhds 0) := by
    have hfun :
        (fun m =>
          MeasureTheory.eLpNorm (f m - fun _ : Cd d => (0 : ℝ)) 2 (gammaD d)) =
        fun m => MeasureTheory.eLpNorm (f m) 2 (gammaD d) := by
      funext m
      congr 1
      funext z
      simp
    rw [hfun, ENNReal.tendsto_nhds_zero]
    intro eps heps
    filter_upwards [(ENNReal.tendsto_nhds_zero.mp htarget) eps heps] with m hm
    exact le_trans (hbound m) hm
  have hzero_meas :
      MeasureTheory.AEStronglyMeasurable (fun _ : Cd d => (0 : ℝ)) (gammaD d) :=
    (continuous_const : Continuous (fun _ : Cd d => (0 : ℝ)))
      |>.stronglyMeasurable.aestronglyMeasurable
  have hInMeasure :
      MeasureTheory.TendstoInMeasure (gammaD d) f Filter.atTop (fun _ : Cd d => (0 : ℝ)) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (p := (2 : ENNReal)) (μ := gammaD d)
      (f := f) (g := fun _ : Cd d => (0 : ℝ))
      (by norm_num) hf_meas hzero_meas heLp_tendsto
  obtain ⟨ψ, hψ_strict, hψ_ae⟩ := hInMeasure.exists_seq_tendsto_ae
  refine ⟨ψ, hψ_strict, ?_⟩
  filter_upwards [hψ_ae] with z hz
  simpa [f] using hz

private theorem finite_head_bad_limit_real_part_ae_wip
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (F : Pkappa d kappa)
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ}
    {U : Skappa d kappa} {φ : ℕ -> ℕ}
    (hφ_strict : StrictMono φ)
    (ht_tendsto_zero :
      Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds 0))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
      Filter.atTop (nhds (coeffSkappa U alpha)))
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hpartial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1)
    (ht_pos : ∀ m, 0 < t m)
    (ht_le : ∀ m, t m <= 4)
    (hdef : ∀ m, defect F (t m • H m) <
      (1 / ((m + 1 : Nat) : ℝ)) * t m) :
    (fun z => Complex.re (toFun kappa U z * star (evalPkappa kappa F z)))
      =ᵐ[gammaD d] fun _ => 0 := by
  obtain ⟨ψ, hψ_strict, hquot_ae⟩ :=
    finite_head_bad_limit_defect_quotient_ae_tendsto_zero_wip
      (hd := hd) (kappa := kappa) (F := F) (H := H) (t := t) (φ := φ)
      hφ_strict ht_pos hdef
  have ht_sub_tendsto_zero :
      Filter.Tendsto (fun m => t (φ (ψ m))) Filter.atTop (nhds 0) :=
    ht_tendsto_zero.comp hψ_strict.tendsto_atTop
  have hpointwise :
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m => evalPkappa kappa (H (φ (ψ m))) z)
          Filter.atTop
          (nhds (toFun kappa U z)) := by
    filter_upwards with z
    have hz :=
      evalPkappa_tendsto_toFun_of_coeff_tendsto_wip
        (kappa := kappa) (H := fun m => H (φ m)) (U := U)
        hcoeff (fun m => hH_norm (φ m)) hpartial z
    exact hz.comp hψ_strict.tendsto_atTop
  have hreal :
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m =>
            Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
              star (evalPkappa kappa F z)))
          Filter.atTop (nhds 0) := by
    filter_upwards [hquot_ae] with z hzquot
    let Cz : ℝ := Real.sqrt (∑' alpha : Idx d, ‖Phi kappa alpha z‖ ^ 2)
    have hCz_nn : 0 <= Cz := by
      dsimp [Cz]
      exact Real.sqrt_nonneg _
    have hw_bound :
        ∀ m : ℕ, ‖evalPkappa kappa (H (φ (ψ m))) z‖ <= Cz := by
      intro m
      exact evalPkappa_norm_le_kernel_sqrt_wip kappa (H (φ (ψ m)))
        (hH_norm (φ (ψ m))) z
    have hR_nonneg :
        ∀ m : ℕ,
          0 <=
            defectFunctionPkappa_coeff_wip kappa F
              (t (φ (ψ m)) • H (φ (ψ m))) z / t (φ (ψ m)) := by
      intro m
      exact div_nonneg (abs_nonneg _) (le_of_lt (ht_pos (φ (ψ m))))
    have hlin_eq :
        ∀ m : ℕ,
          defectFunctionPkappa_coeff_wip kappa F
              (t (φ (ψ m)) • H (φ (ψ m))) z / t (φ (ψ m)) *
              (‖evalPkappa kappa F z +
                  (t (φ (ψ m)) : ℂ) * evalPkappa kappa (H (φ (ψ m))) z‖ +
                ‖evalPkappa kappa F z‖) =
            |2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
                  star (evalPkappa kappa F z)) +
                t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2| := by
      intro m
      simpa [defectFunctionPkappa_coeff_wip, evalPkappa_add_apply_wip,
        evalPkappa_smul_real_wip] using
        (defectFunction_div_eq_abs_linearization_wip
          (evalPkappa kappa F z)
          (evalPkappa kappa (H (φ (ψ m))) z)
          (ht_pos (φ (ψ m))))
    have hfactor_bound :
        ∀ m : ℕ,
          ‖evalPkappa kappa F z +
              (t (φ (ψ m)) : ℂ) * evalPkappa kappa (H (φ (ψ m))) z‖ +
              ‖evalPkappa kappa F z‖ <=
            2 * ‖evalPkappa kappa F z‖ + 4 * Cz := by
      intro m
      have htm_nonneg : 0 <= t (φ (ψ m)) := le_of_lt (ht_pos (φ (ψ m)))
      calc
        ‖evalPkappa kappa F z +
            (t (φ (ψ m)) : ℂ) * evalPkappa kappa (H (φ (ψ m))) z‖ +
            ‖evalPkappa kappa F z‖
            <= (‖evalPkappa kappa F z‖ +
                ‖(t (φ (ψ m)) : ℂ) * evalPkappa kappa (H (φ (ψ m))) z‖) +
                ‖evalPkappa kappa F z‖ := by
              gcongr
              exact norm_add_le _ _
        _ = 2 * ‖evalPkappa kappa F z‖ +
              ‖(t (φ (ψ m)) : ℂ) * evalPkappa kappa (H (φ (ψ m))) z‖ := by ring_nf
        _ = 2 * ‖evalPkappa kappa F z‖ +
              t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htm_nonneg]
        _ <= 2 * ‖evalPkappa kappa F z‖ +
              4 * ‖evalPkappa kappa (H (φ (ψ m))) z‖ := by
              gcongr
              exact ht_le (φ (ψ m))
        _ <= 2 * ‖evalPkappa kappa F z‖ + 4 * Cz := by
              gcongr
              exact hw_bound m
    have hprod :
        Filter.Tendsto
          (fun m =>
            (defectFunctionPkappa_coeff_wip kappa F
                (t (φ (ψ m)) • H (φ (ψ m))) z / t (φ (ψ m))) *
              (2 * ‖evalPkappa kappa F z‖ + 4 * Cz))
          Filter.atTop (nhds 0) := by simpa using hzquot.mul tendsto_const_nhds
    have habs :
        Filter.Tendsto
          (fun m =>
            |2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
                  star (evalPkappa kappa F z)) +
                t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2|)
          Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun m => abs_nonneg _) ?_ hprod
      intro m
      rw [← hlin_eq m]
      exact mul_le_mul_of_nonneg_left (hfactor_bound m) (hR_nonneg m)
    have hlin :
        Filter.Tendsto
          (fun m =>
            2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
                  star (evalPkappa kappa F z)) +
                t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2)
          Filter.atTop (nhds 0) :=
      (tendsto_zero_iff_abs_tendsto_zero _).2 habs
    have herror :
        Filter.Tendsto
          (fun m =>
            t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2)
          Filter.atTop (nhds 0) := by
      have hbound_err :
          ∀ m : ℕ,
            t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2 <=
              (Cz ^ 2) * t (φ (ψ m)) := by
        intro m
        have hsq :
            ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2 <= Cz ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hCz_nn).2 (hw_bound m)
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hsq (le_of_lt (ht_pos (φ (ψ m))))
      have hczsq :
          Filter.Tendsto (fun m => (Cz ^ 2) * t (φ (ψ m))) Filter.atTop (nhds 0) := by
        have htmp :
            Filter.Tendsto (fun m => (Cz ^ 2) * t (φ (ψ m)))
              Filter.atTop (nhds ((Cz ^ 2) * 0)) :=
          tendsto_const_nhds.mul ht_sub_tendsto_zero
        simpa using htmp
      refine squeeze_zero
        (fun m => mul_nonneg (le_of_lt (ht_pos (φ (ψ m)))) (sq_nonneg _))
        hbound_err hczsq
    have htwo :
        Filter.Tendsto
          (fun m =>
            2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
              star (evalPkappa kappa F z)))
          Filter.atTop (nhds 0) := by
      have hsub := hlin.sub herror
      have htwo_eq :
          (fun m =>
            2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
              star (evalPkappa kappa F z))) =
          fun m =>
            2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
              star (evalPkappa kappa F z)) +
              t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2 -
                t (φ (ψ m)) * ‖evalPkappa kappa (H (φ (ψ m))) z‖ ^ 2 := by
        funext m
        ring
      simpa [htwo_eq] using hsub
    have hhalf :
        Filter.Tendsto
          (fun m =>
            (1 / 2 : ℝ) *
              (2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
                star (evalPkappa kappa F z))))
          Filter.atTop (nhds ((1 / 2 : ℝ) * 0)) :=
      tendsto_const_nhds.mul htwo
    have hhalf_eq :
        (fun m =>
          Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
            star (evalPkappa kappa F z))) =
        fun m =>
          (1 / 2 : ℝ) *
            (2 * Complex.re (evalPkappa kappa (H (φ (ψ m))) z *
              star (evalPkappa kappa F z))) := by
      funext m
      ring
    simpa [hhalf_eq] using hhalf
  exact
    ae_real_part_eq_zero_of_tendsto_wip
      (base := evalPkappa kappa F)
      (u := fun m z => evalPkappa kappa (H (φ (ψ m))) z)
      (limit := toFun kappa U)
      hpointwise hreal

private theorem finite_head_bad_limit_modulus_ae_wip
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (F : Pkappa d kappa)
    {H : ℕ -> Pkappa d kappa} {t : ℕ -> ℝ}
    {T : ℝ} {U : Skappa d kappa} {φ : ℕ -> ℕ}
    (hφ_strict : StrictMono φ)
    (ht_tendsto : Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds T))
    (hcoeff : ∀ alpha, Filter.Tendsto (fun m => coeffPkappa (H (φ m)) alpha)
      Filter.atTop (nhds (coeffSkappa U alpha)))
    (hH_norm : ∀ m, ‖H m‖ = 1)
    (hpartial : ∀ E : Finset (Idx d),
      Finset.sum E (fun alpha => ‖coeffSkappa U alpha‖ ^ 2) <= 1)
    (ht_le : ∀ m, t m <= 4)
    (hdef : ∀ m, defect F (t m • H m) <
      (1 / ((m + 1 : Nat) : ℝ)) * t m) :
    (fun z => ‖evalPkappa kappa F z + (T : ℂ) * toFun kappa U z‖)
      =ᵐ[gammaD d] fun z => ‖evalPkappa kappa F z‖ := by
  obtain ⟨ψ, hψ_strict, hdef_ae⟩ :=
    finite_head_bad_limit_defect_ae_tendsto_zero_wip
      (hd := hd) (kappa := kappa) (F := F) (H := H) (t := t) (φ := φ)
      hφ_strict ht_le hdef
  have hpointwise :
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m => evalPkappa kappa (F + t (φ (ψ m)) • H (φ (ψ m))) z)
          Filter.atTop
          (nhds (evalPkappa kappa F z + (T : ℂ) * toFun kappa U z)) := by
    filter_upwards with z
    have hz :=
      finite_head_bad_limit_eval_tendsto_wip
        (kappa := kappa) F ht_tendsto hcoeff hH_norm hpartial z
    exact hz.comp hψ_strict.tendsto_atTop
  have hdefect :
      ∀ᵐ z ∂ gammaD d,
        Filter.Tendsto
          (fun m =>
            |‖evalPkappa kappa (F + t (φ (ψ m)) • H (φ (ψ m))) z‖ -
              ‖evalPkappa kappa F z‖|)
          Filter.atTop (nhds 0) := by
    filter_upwards [hdef_ae] with z hz
    simpa [defectFunctionPkappa_coeff_wip] using hz
  exact ae_norm_eq_of_tendsto_defect_wip hpointwise hdefect

private def skappaAffinePkappa_wip
    {d : Nat} (kappa : MultiIndex d)
    (F : Pkappa d kappa) (U : Skappa d kappa) (a b : ℂ) :
    Skappa d kappa where
  coeff := fun alpha => a * coeffPkappa F alpha + b * coeffSkappa U alpha
  summable_norm_sq := by
    classical
    let f : Idx d -> ℝ := fun alpha => ‖a * coeffPkappa F alpha‖ ^ 2
    let g : Idx d -> ℝ := fun alpha => ‖b * coeffSkappa U alpha‖ ^ 2
    have hf : Summable f := by
      dsimp [f, coeffPkappa]
      refine summable_of_hasFiniteSupport ?_
      refine Set.Finite.subset F.support.finite_toSet ?_
      intro alpha hnonzero
      have haF_ne : a * F alpha ≠ 0 := by
        intro hzero
        apply hnonzero
        simp [hzero]
      have hF_ne : F alpha ≠ 0 := by
        intro hzero
        exact haF_ne (by simp [hzero])
      exact F.mem_support_iff.mpr hF_ne
    have hg : Summable g := by
      have hg_eq :
          g = fun alpha => (‖b‖ ^ 2) * (‖coeffSkappa U alpha‖ ^ 2) := by
        funext alpha
        dsimp [g]
        rw [norm_mul, mul_pow]
      rw [hg_eq]
      exact U.summable_norm_sq.mul_left (‖b‖ ^ 2)
    have hsum : Summable (fun alpha => 2 * f alpha + 2 * g alpha) :=
      (hf.mul_left 2).add (hg.mul_left 2)
    refine hsum.of_nonneg_of_le (fun alpha => sq_nonneg _) ?_
    intro alpha
    dsimp [f, g]
    let x : ℂ := a * coeffPkappa F alpha
    let y : ℂ := b * coeffSkappa U alpha
    have hnorm : ‖x + y‖ <= ‖x‖ + ‖y‖ := norm_add_le x y
    have hsq :
        ‖x + y‖ ^ 2 <= (‖x‖ + ‖y‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
    have hquad : (‖x‖ + ‖y‖) ^ 2 <= 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
    have hfinal := le_trans hsq hquad
    simpa [x, y] using hfinal

private theorem coeff_skappaAffinePkappa_wip
    {d : Nat} (kappa : MultiIndex d)
    (F : Pkappa d kappa) (U : Skappa d kappa) (a b : ℂ) (alpha : Idx d) :
    coeffSkappa (skappaAffinePkappa_wip kappa F U a b) alpha =
      a * coeffPkappa F alpha + b * coeffSkappa U alpha := by rfl

private theorem toFun_skappaAffinePkappa_wip
    {d : Nat} (kappa : MultiIndex d)
    (F : Pkappa d kappa) (U : Skappa d kappa) (a b : ℂ) :
    toFun kappa (skappaAffinePkappa_wip kappa F U a b) =
      fun z => a * evalPkappa kappa F z + b * toFun kappa U z := by
  ext z
  have hFsum := summable_pkappa_eval_mul_wip kappa F z
  have hUsum := summable_skappa_eval_mul_wip kappa U z
  have hFsum' :
      Summable (fun alpha : Idx d => a * (coeffPkappa F alpha * Phi kappa alpha z)) :=
    hFsum.mul_left a
  have hUsum' :
      Summable (fun alpha : Idx d => b * (coeffSkappa U alpha * Phi kappa alpha z)) :=
    hUsum.mul_left b
  unfold toFun
  calc
    ∑' alpha : Idx d,
        coeffSkappa (skappaAffinePkappa_wip kappa F U a b) alpha * Phi kappa alpha z
        = (∑' alpha : Idx d,
            (a * (coeffPkappa F alpha * Phi kappa alpha z) +
              b * (coeffSkappa U alpha * Phi kappa alpha z))) := tsum_congr fun alpha => by
            change
              (a * coeffPkappa F alpha + b * coeffSkappa U alpha) *
                  Phi kappa alpha z =
                a * (coeffPkappa F alpha * Phi kappa alpha z) +
                  b * (coeffSkappa U alpha * Phi kappa alpha z)
            ring
    _ = (∑' alpha : Idx d, a * (coeffPkappa F alpha * Phi kappa alpha z)) +
          ∑' alpha : Idx d, b * (coeffSkappa U alpha * Phi kappa alpha z) := hFsum'.tsum_add hUsum'
    _ = a * (∑' alpha : Idx d, coeffPkappa F alpha * Phi kappa alpha z) +
          b * (∑' alpha : Idx d, coeffSkappa U alpha * Phi kappa alpha z) := by
          rw [hFsum.tsum_mul_left, hUsum.tsum_mul_left]
    _ = a * evalPkappa kappa F z + b * (∑' alpha : Idx d,
          coeffSkappa U alpha * Phi kappa alpha z) := by rw [evalPkappa_eq_tsum_coeff_wip kappa F z]

private theorem skappa_exact_modulus_affine_relation_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (U : Skappa d kappa)
    (a b c e : ℂ)
    (hmod :
      (fun z => ‖c * evalPkappa kappa F z + e * toFun kappa U z‖)
        =ᵐ[gammaD d]
      fun z => ‖a * evalPkappa kappa F z + b * toFun kappa U z‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      ∀ alpha,
        c * coeffPkappa F alpha + e * coeffSkappa U alpha =
          w * (a * coeffPkappa F alpha + b * coeffSkappa U alpha) := by
  let X : Skappa d kappa := skappaAffinePkappa_wip kappa F U a b
  let Y : Skappa d kappa := skappaAffinePkappa_wip kappa F U c e
  have hmodXY :
      (fun z => ‖toFun kappa X z‖) =ᵐ[gammaD d]
        fun z => ‖toFun kappa Y z‖ := by
    filter_upwards [hmod] with z hz
    simpa [X, Y, toFun_skappaAffinePkappa_wip] using hz.symm
  obtain ⟨w, hw, hYX⟩ :=
    exact_modulus_recovery_skappa_ae hd kappa hmodXY
  refine ⟨w, hw, ?_⟩
  intro alpha
  have hcoeff := congrArg (fun S : Skappa d kappa => coeffSkappa S alpha) hYX
  simp only [X, Y] at hcoeff
  have hsmul :
      coeffSkappa (w • skappaAffinePkappa_wip kappa F U a b) alpha
        = w * coeffSkappa (skappaAffinePkappa_wip kappa F U a b) alpha := rfl
  rw [coeff_skappaAffinePkappa_wip, hsmul, coeff_skappaAffinePkappa_wip] at hcoeff
  exact hcoeff

private theorem skappa_modulus_phase_relation_against_pkappa_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0)
    {T : ℝ} (hT_pos : 0 < T) (U : Skappa d kappa)
    (hmod :
      (fun z => ‖evalPkappa kappa F z + (T : ℂ) * toFun kappa U z‖)
        =ᵐ[gammaD d] fun z => ‖evalPkappa kappa F z‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      ∀ alpha,
        coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha =
          w * coeffPkappa F alpha := by
  let _ := hF_ne
  let _ := hT_pos
  have hmod' :
      (fun z => ‖(1 : ℂ) * evalPkappa kappa F z + (T : ℂ) * toFun kappa U z‖)
        =ᵐ[gammaD d]
      fun z => ‖(1 : ℂ) * evalPkappa kappa F z + (0 : ℂ) * toFun kappa U z‖ := by
    filter_upwards [hmod] with z hz
    simpa using hz
  obtain ⟨w, hw, hrel⟩ :=
    skappa_exact_modulus_affine_relation_wip
      hd kappa F U (1 : ℂ) (0 : ℂ) (1 : ℂ) (T : ℂ) hmod'
  refine ⟨w, hw, ?_⟩
  intro alpha
  simpa using hrel alpha

private theorem skappa_real_part_scalar_relation_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (U : Skappa d kappa)
    (hreal :
      (fun z => Complex.re (toFun kappa U z * star (evalPkappa kappa F z)))
        =ᵐ[gammaD d] fun _ => 0) :
    ∃ c : ℂ, ∀ alpha, coeffSkappa U alpha = c * coeffPkappa F alpha := by
  have hmod :
      (fun z => ‖(1 : ℂ) * evalPkappa kappa F z + (1 : ℂ) * toFun kappa U z‖)
        =ᵐ[gammaD d]
      fun z => ‖(1 : ℂ) * evalPkappa kappa F z + (-1 : ℂ) * toFun kappa U z‖ := by
    filter_upwards [hreal] with z hz
    let f : ℂ := evalPkappa kappa F z
    let u : ℂ := toFun kappa U z
    have hsq :
        ‖f + u‖ ^ 2 = ‖f + (-1 : ℂ) * u‖ ^ 2 := by
      have hplus := norm_sq_add_real_smul_wip f u 1
      have hminus := norm_sq_add_real_smul_wip f u (-1)
      have hplus' :
          ‖f + u‖ ^ 2 =
            ‖f‖ ^ 2 + 1 ^ 2 * ‖u‖ ^ 2 + 2 * 1 * Complex.re (u * star f) := by simpa using hplus
      have hminus' :
          ‖f + (-1 : ℂ) * u‖ ^ 2 =
            ‖f‖ ^ 2 + (-1 : ℝ) ^ 2 * ‖u‖ ^ 2 +
              2 * (-1 : ℝ) * Complex.re (u * star f) := by simpa using hminus
      have hz' : Complex.re (u * star f) = 0 := by simpa [f, u] using hz
      nlinarith
    have hnorm : ‖f + u‖ = ‖f + (-1 : ℂ) * u‖ := by
      have hcases := (sq_eq_sq_iff_eq_or_eq_neg.mp hsq)
      rcases hcases with h | h
      · exact h
      · have hleft_nonneg : 0 <= ‖f + u‖ := norm_nonneg _
        have hright_nonneg : 0 <= ‖f + (-1 : ℂ) * u‖ := norm_nonneg _
        nlinarith
    simpa [f, u] using hnorm
  obtain ⟨w, hw, hrel⟩ :=
    skappa_exact_modulus_affine_relation_wip
      hd kappa F U (1 : ℂ) (-1 : ℂ) (1 : ℂ) (1 : ℂ) hmod
  by_cases hw_neg : w = -1
  · exfalso
    apply hF_ne
    ext alpha
    have h :
        coeffPkappa F alpha + coeffSkappa U alpha =
          w * (coeffPkappa F alpha + (-1 : ℂ) * coeffSkappa U alpha) := by simpa using hrel alpha
    rw [hw_neg] at h
    have htwo :
        (2 : ℂ) * coeffPkappa F alpha = 0 := by
      calc
        (2 : ℂ) * coeffPkappa F alpha
            =
              (coeffPkappa F alpha + coeffSkappa U alpha) -
                ((-1 : ℂ) *
                  (coeffPkappa F alpha + (-1 : ℂ) * coeffSkappa U alpha)) := by ring
        _ = 0 := by rw [h]; ring
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  · have hw_add_ne : (1 : ℂ) + w ≠ 0 := by
      intro hsum
      apply hw_neg
      have hsum' : w + 1 = 0 := by simpa [add_comm] using hsum
      exact eq_neg_iff_add_eq_zero.mpr hsum'
    let c : ℂ := (w - 1) / ((1 : ℂ) + w)
    refine ⟨c, ?_⟩
    intro alpha
    have h :
        coeffPkappa F alpha + coeffSkappa U alpha =
          w * (coeffPkappa F alpha + (-1 : ℂ) * coeffSkappa U alpha) := by simpa using hrel alpha
    have hlin :
        ((1 : ℂ) + w) * coeffSkappa U alpha =
          (w - 1) * coeffPkappa F alpha := by
      calc
        ((1 : ℂ) + w) * coeffSkappa U alpha
            =
              (coeffPkappa F alpha + coeffSkappa U alpha) +
                w * coeffSkappa U alpha - coeffPkappa F alpha := by ring
        _ =
              w * (coeffPkappa F alpha + (-1 : ℂ) * coeffSkappa U alpha) +
                w * coeffSkappa U alpha - coeffPkappa F alpha := by rw [h]
        _ = (w - 1) * coeffPkappa F alpha := by ring
    calc
      coeffSkappa U alpha
          = (((1 : ℂ) + w)⁻¹) * (((1 : ℂ) + w) * coeffSkappa U alpha) := by field_simp [hw_add_ne]
      _ = (((1 : ℂ) + w)⁻¹) * ((w - 1) * coeffPkappa F alpha) := by rw [hlin]
      _ = c * coeffPkappa F alpha := by
            dsimp [c]
            field_simp [hw_add_ne]

private theorem cayley_re_eq_zero_of_norm_eq_one_wip {w : ℂ}
    (hw : ‖w‖ = 1) (hw_add_ne : (1 : ℂ) + w ≠ 0) :
    (((w - 1) / ((1 : ℂ) + w)).re = 0) := by
  let c : ℂ := (w - 1) / ((1 : ℂ) + w)
  have hw_conj : w * (starRingEnd ℂ) w = 1 := by simpa [hw] using (RCLike.mul_conj w)
  have hden_star : (1 : ℂ) + (starRingEnd ℂ) w ≠ 0 := by
    simpa [map_add] using (star_ne_zero.mpr hw_add_ne :
      (starRingEnd ℂ) (1 + w) ≠ 0)
  have hc_add : c + star c = 0 := by
    dsimp [c]
    rw [map_div₀, map_sub, map_add]
    simp only [map_one]
    field_simp [hw_add_ne, hden_star]
    ring_nf
    rw [hw_conj]
    field_simp [hden_star]
    ring
  have hre : (c + star c).re = 0 := by
    rw [hc_add]
    simp
  have hre' : 2 * c.re = 0 := by simpa [Complex.add_re, Complex.conj_re, two_mul] using hre
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  exact mul_eq_zero.mp hre' |>.resolve_left htwo

private theorem skappa_real_part_pure_imag_scalar_relation_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (U : Skappa d kappa)
    (hreal :
      (fun z => Complex.re (toFun kappa U z * star (evalPkappa kappa F z)))
        =ᵐ[gammaD d] fun _ => 0) :
    ∃ c : ℂ, c.re = 0 ∧ ∀ alpha, coeffSkappa U alpha = c * coeffPkappa F alpha := by
  have hmod :
      (fun z => ‖(1 : ℂ) * evalPkappa kappa F z + (1 : ℂ) * toFun kappa U z‖)
        =ᵐ[gammaD d]
      fun z => ‖(1 : ℂ) * evalPkappa kappa F z + (-1 : ℂ) * toFun kappa U z‖ := by
    filter_upwards [hreal] with z hz
    let f : ℂ := evalPkappa kappa F z
    let u : ℂ := toFun kappa U z
    have hsq :
        ‖f + u‖ ^ 2 = ‖f + (-1 : ℂ) * u‖ ^ 2 := by
      have hplus := norm_sq_add_real_smul_wip f u 1
      have hminus := norm_sq_add_real_smul_wip f u (-1)
      have hplus' :
          ‖f + u‖ ^ 2 =
            ‖f‖ ^ 2 + 1 ^ 2 * ‖u‖ ^ 2 + 2 * 1 * Complex.re (u * star f) := by simpa using hplus
      have hminus' :
          ‖f + (-1 : ℂ) * u‖ ^ 2 =
            ‖f‖ ^ 2 + (-1 : ℝ) ^ 2 * ‖u‖ ^ 2 +
              2 * (-1 : ℝ) * Complex.re (u * star f) := by simpa using hminus
      have hz' : Complex.re (u * star f) = 0 := by simpa [f, u] using hz
      nlinarith
    have hnorm : ‖f + u‖ = ‖f + (-1 : ℂ) * u‖ := by
      have hcases := (sq_eq_sq_iff_eq_or_eq_neg.mp hsq)
      rcases hcases with h | h
      · exact h
      · have hleft_nonneg : 0 <= ‖f + u‖ := norm_nonneg _
        have hright_nonneg : 0 <= ‖f + (-1 : ℂ) * u‖ := norm_nonneg _
        nlinarith
    simpa [f, u] using hnorm
  obtain ⟨w, hw, hrel⟩ :=
    skappa_exact_modulus_affine_relation_wip
      hd kappa F U (1 : ℂ) (-1 : ℂ) (1 : ℂ) (1 : ℂ) hmod
  by_cases hw_neg : w = -1
  · exfalso
    apply hF_ne
    ext alpha
    have h :
        coeffPkappa F alpha + coeffSkappa U alpha =
          w * (coeffPkappa F alpha + (-1 : ℂ) * coeffSkappa U alpha) := by simpa using hrel alpha
    rw [hw_neg] at h
    have htwo :
        (2 : ℂ) * coeffPkappa F alpha = 0 := by
      calc
        (2 : ℂ) * coeffPkappa F alpha
            =
              (coeffPkappa F alpha + coeffSkappa U alpha) -
                ((-1 : ℂ) *
                  (coeffPkappa F alpha + (-1 : ℂ) * coeffSkappa U alpha)) := by ring
        _ = 0 := by rw [h]; ring
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  · have hw_add_ne : (1 : ℂ) + w ≠ 0 := by
      intro hsum
      apply hw_neg
      have hsum' : w + 1 = 0 := by simpa [add_comm] using hsum
      exact eq_neg_iff_add_eq_zero.mpr hsum'
    let c : ℂ := (w - 1) / ((1 : ℂ) + w)
    refine ⟨c, cayley_re_eq_zero_of_norm_eq_one_wip hw hw_add_ne, ?_⟩
    intro alpha
    have h :
        coeffPkappa F alpha + coeffSkappa U alpha =
          w * (coeffPkappa F alpha + (-1 : ℂ) * coeffSkappa U alpha) := by simpa using hrel alpha
    have hlin :
        ((1 : ℂ) + w) * coeffSkappa U alpha =
          (w - 1) * coeffPkappa F alpha := by
      calc
        ((1 : ℂ) + w) * coeffSkappa U alpha
            =
              (coeffPkappa F alpha + coeffSkappa U alpha) +
                w * coeffSkappa U alpha - coeffPkappa F alpha := by ring
        _ =
              w * (coeffPkappa F alpha + (-1 : ℂ) * coeffSkappa U alpha) +
                w * coeffSkappa U alpha - coeffPkappa F alpha := by rw [h]
        _ = (w - 1) * coeffPkappa F alpha := by ring
    calc
      coeffSkappa U alpha
          = (((1 : ℂ) + w)⁻¹) * (((1 : ℂ) + w) * coeffSkappa U alpha) := by field_simp [hw_add_ne]
      _ = (((1 : ℂ) + w)⁻¹) * ((w - 1) * coeffPkappa F alpha) := by rw [hlin]
      _ = c * coeffPkappa F alpha := by
            dsimp [c]
            field_simp [hw_add_ne]

private theorem coeff_zero_of_modulus_phase_relation_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1)
    {T : ℝ} (hT_pos : 0 < T) {U : Skappa d kappa} {w : ℂ}
    (hrel : ∀ alpha,
      coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha =
        w * coeffPkappa F alpha)
    (horth : orthogonalToSkappa_wip F U) :
    ∀ alpha, coeffSkappa U alpha = 0 := by
  have hT_ne : (T : ℂ) ≠ 0 := by exact_mod_cast hT_pos.ne'
  have hcoeff :
      ∀ alpha,
        coeffSkappa U alpha =
          (((T : ℂ)⁻¹ * (w - 1)) * coeffPkappa F alpha) := by
    intro alpha
    have hTU :
        (T : ℂ) * coeffSkappa U alpha =
          (w - 1) * coeffPkappa F alpha := by
      calc
        (T : ℂ) * coeffSkappa U alpha
            = (coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha) -
                coeffPkappa F alpha := by ring
        _ = w * coeffPkappa F alpha - coeffPkappa F alpha := by rw [hrel alpha]
        _ = (w - 1) * coeffPkappa F alpha := by ring
    calc
      coeffSkappa U alpha
          = (T : ℂ)⁻¹ * ((T : ℂ) * coeffSkappa U alpha) := by field_simp [hT_ne]
      _ = (T : ℂ)⁻¹ * ((w - 1) * coeffPkappa F alpha) := by rw [hTU]
      _ = (((T : ℂ)⁻¹ * (w - 1)) * coeffPkappa F alpha) := by ring
  exact coeff_zero_of_scalar_multiple_orthogonalToSkappa_wip hF_norm hcoeff horth

private theorem coeff_zero_of_real_part_scalar_relation_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1)
    {U : Skappa d kappa} {c : ℂ}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = c * coeffPkappa F alpha)
    (horth : orthogonalToSkappa_wip F U) :
    ∀ alpha, coeffSkappa U alpha = 0 :=
  coeff_zero_of_scalar_multiple_orthogonalToSkappa_wip hF_norm hcoeff horth

private theorem bad_limit_coeff_zero_from_exact_rigidity_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1)
    {T : ℝ} {U : Skappa d kappa}
    (hT_mem : T ∈ Set.Icc (0 : ℝ) 4)
    (horth : orthogonalToSkappa_wip F U)
    (hreal :
      T = 0 ->
        (fun z => Complex.re (toFun kappa U z * star (evalPkappa kappa F z)))
          =ᵐ[gammaD d] fun _ => 0)
    (hmod :
      0 < T ->
        (fun z => ‖evalPkappa kappa F z + (T : ℂ) * toFun kappa U z‖)
          =ᵐ[gammaD d] fun z => ‖evalPkappa kappa F z‖) :
    ∀ alpha, coeffSkappa U alpha = 0 := by
  by_cases hT_zero : T = 0
  · obtain ⟨c, hc⟩ :=
      skappa_real_part_scalar_relation_wip hd kappa F hF_ne U (hreal hT_zero)
    exact coeff_zero_of_real_part_scalar_relation_wip hF_norm hc horth
  · have hT_pos : 0 < T := lt_of_le_of_ne hT_mem.1 (Ne.symm hT_zero)
    obtain ⟨w, hw, hrel⟩ :=
      skappa_modulus_phase_relation_against_pkappa_wip
        hd kappa F hF_ne hT_pos U (hmod hT_pos)
    exact coeff_zero_of_modulus_phase_relation_wip hF_norm hT_pos hrel horth

private theorem coeff_zero_of_pure_imag_scalar_positiveGauge_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1)
    {U : Skappa d kappa} {c : ℂ}
    (hc_re : c.re = 0)
    (hcoeff : ∀ alpha, coeffSkappa U alpha = c * coeffPkappa F alpha)
    (him :
      (Finset.sum F.support
        (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha))).im = 0) :
    ∀ alpha, coeffSkappa U alpha = 0 := by
  have hinner :
      Finset.sum F.support
          (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha)) =
        c := by
    calc
      Finset.sum F.support
          (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha))
          = Finset.sum F.support
            (fun alpha => (c * coeffPkappa F alpha) * star (coeffPkappa F alpha)) := by
              refine Finset.sum_congr rfl ?_
              intro alpha halpha
              rw [hcoeff alpha]
      _ = c * Finset.sum F.support
            (fun alpha => coeffPkappa F alpha * star (coeffPkappa F alpha)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro alpha halpha
              ring
      _ = c * ((Finset.sum F.support
            (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) : ℝ) : ℂ) := by
              congr 1
              norm_num
              refine Finset.sum_congr rfl ?_
              intro alpha halpha
              simpa [Complex.normSq_eq_norm_sq] using
                Complex.mul_conj (coeffPkappa F alpha)
      _ = c := by
              have hnorm_sq := norm_sq_eq_sum_coeff_wip F
              have hsum_one :
                  ((Finset.sum F.support
                    (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) : ℝ) : ℂ) = 1 := by
                have hsum_real :
                    Finset.sum F.support (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) = 1 := by
                  simpa using hnorm_sq.symm.trans (by rw [hF_norm]; norm_num)
                exact_mod_cast hsum_real
              rw [hsum_one, mul_one]
  have hc_im : c.im = 0 := by
    rw [hinner] at him
    exact him
  have hc : c = 0 := by
    apply Complex.ext
    · simpa using hc_re
    · simpa using hc_im
  intro alpha
  simp [hcoeff alpha, hc]

private theorem coeff_zero_of_modulus_phase_relation_positiveGauge_wip
    {d : Nat} {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1)
    {T : ℝ} (hT_pos : 0 < T) {U : Skappa d kappa} {w : ℂ}
    (hw : ‖w‖ = 1)
    (hrel : ∀ alpha,
      coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha =
        w * coeffPkappa F alpha)
    (hlimit :
      let L : ℂ :=
        Finset.sum F.support
          (fun alpha =>
            (coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha) *
              star (coeffPkappa F alpha))
      L.im = 0 ∧ 0 ≤ L.re) :
    ∀ alpha, coeffSkappa U alpha = 0 := by
  let L : ℂ :=
    Finset.sum F.support
      (fun alpha =>
        (coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha) *
          star (coeffPkappa F alpha))
  have hL_eq_w : L = w := by
    dsimp [L]
    calc
      Finset.sum F.support
          (fun alpha =>
            (coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha) *
              star (coeffPkappa F alpha))
          = Finset.sum F.support
            (fun alpha => (w * coeffPkappa F alpha) * star (coeffPkappa F alpha)) := by
              refine Finset.sum_congr rfl ?_
              intro alpha halpha
              rw [hrel alpha]
      _ = w * Finset.sum F.support
            (fun alpha => coeffPkappa F alpha * star (coeffPkappa F alpha)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro alpha halpha
              ring
      _ = w * ((Finset.sum F.support
            (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) : ℝ) : ℂ) := by
              congr 1
              norm_num
              refine Finset.sum_congr rfl ?_
              intro alpha halpha
              simpa [Complex.normSq_eq_norm_sq] using
                Complex.mul_conj (coeffPkappa F alpha)
      _ = w := by
              have hnorm_sq := norm_sq_eq_sum_coeff_wip F
              have hsum_one :
                  ((Finset.sum F.support
                    (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) : ℝ) : ℂ) = 1 := by
                have hsum_real :
                    Finset.sum F.support (fun alpha => ‖coeffPkappa F alpha‖ ^ 2) = 1 := by
                  simpa using hnorm_sq.symm.trans (by rw [hF_norm]; norm_num)
                exact_mod_cast hsum_real
              rw [hsum_one, mul_one]
  have hL_im : L.im = 0 := hlimit.1
  have hL_re : 0 ≤ L.re := hlimit.2
  have hw_im : w.im = 0 := by simpa [hL_eq_w] using hL_im
  have hw_re : 0 ≤ w.re := by simpa [hL_eq_w] using hL_re
  have hw_one : w = 1 := unit_complex_of_real_nonneg_wip hw hw_im hw_re
  have hT_ne : (T : ℂ) ≠ 0 := by exact_mod_cast hT_pos.ne'
  intro alpha
  have hTU : (T : ℂ) * coeffSkappa U alpha = 0 := by
    calc
      (T : ℂ) * coeffSkappa U alpha
          =
            (coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha) -
              coeffPkappa F alpha := by ring
      _ = w * coeffPkappa F alpha - coeffPkappa F alpha := by rw [hrel alpha]
      _ = 0 := by rw [hw_one]; ring
  exact (mul_eq_zero.mp hTU).resolve_left hT_ne

private theorem bad_limit_coeff_zero_from_exact_rigidity_positiveGauge_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1)
    {T : ℝ} {U : Skappa d kappa}
    (hT_mem : T ∈ Set.Icc (0 : ℝ) 4)
    (hinner_im :
      (Finset.sum F.support
        (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha))).im = 0)
    (hlimit :
      let L : ℂ :=
        Finset.sum F.support
          (fun alpha =>
            (coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha) *
              star (coeffPkappa F alpha))
      L.im = 0 ∧ 0 ≤ L.re)
    (hreal :
      T = 0 ->
        (fun z => Complex.re (toFun kappa U z * star (evalPkappa kappa F z)))
          =ᵐ[gammaD d] fun _ => 0)
    (hmod :
      0 < T ->
        (fun z => ‖evalPkappa kappa F z + (T : ℂ) * toFun kappa U z‖)
          =ᵐ[gammaD d] fun z => ‖evalPkappa kappa F z‖) :
    ∀ alpha, coeffSkappa U alpha = 0 := by
  by_cases hT_zero : T = 0
  · obtain ⟨c, hc_re, hc⟩ :=
      skappa_real_part_pure_imag_scalar_relation_wip hd kappa F hF_ne U (hreal hT_zero)
    exact coeff_zero_of_pure_imag_scalar_positiveGauge_wip hF_norm hc_re hc hinner_im
  · have hT_pos : 0 < T := lt_of_le_of_ne hT_mem.1 (Ne.symm hT_zero)
    obtain ⟨w, hw, hrel⟩ :=
      skappa_modulus_phase_relation_against_pkappa_wip
        hd kappa F hF_ne hT_pos U (hmod hT_pos)
    exact coeff_zero_of_modulus_phase_relation_positiveGauge_wip hF_norm hT_pos hw hrel hlimit

private theorem finite_head_defect_lower_bound_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1)
    (K : Finset (Idx d)) (rho : ℝ) (h_rho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        orthogonalToPk F H ->
        ‖H‖ = 1 ->
        rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ->
        0 < t ->
        t <= 4 ->
        delta * t <= defect F (t • H) := by
  by_contra hbad
  obtain
    ⟨H, t, T, U, φ, hT_mem, hφ_strict, ht_tendsto, hcoeff, hpartial,
      hmass_U, horth, hH_norm, hmass, ht_pos, ht_le, hdef, horth_U⟩ :=
    finite_head_bad_limit_data_wip F K (rho := rho) hbad
  have hzero : ∀ alpha, coeffSkappa U alpha = 0 := by
    refine
      bad_limit_coeff_zero_from_exact_rigidity_wip
        hd kappa F hF_ne hF_norm hT_mem horth_U ?_ ?_
    · intro hT_zero
      have ht_tendsto_zero :
          Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds 0) := by
        simpa [hT_zero] using ht_tendsto
      exact
        finite_head_bad_limit_real_part_ae_wip
          (hd := hd) (kappa := kappa) F hφ_strict ht_tendsto_zero
          hcoeff hH_norm hpartial ht_pos ht_le hdef
    · intro hT_pos
      exact
        finite_head_bad_limit_modulus_ae_wip
          (hd := hd) (kappa := kappa) F hφ_strict ht_tendsto
          hcoeff hH_norm hpartial ht_le hdef
  exact finite_head_mass_contradiction_of_coeff_zero_wip K h_rho hmass_U hzero

private theorem finite_head_defect_lower_bound_positiveGauge_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1)
    (K : Finset (Idx d)) (rho : ℝ) (h_rho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        positivePhaseGauge F (F + t • H) ->
        ‖H‖ = 1 ->
        rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ->
        0 < t ->
        t <= 4 ->
        delta * t <= defect F (t • H) := by
  by_contra hbad
  obtain
    ⟨H, t, T, U, φ, hT_mem, hφ_strict, ht_tendsto, hcoeff, hpartial,
      hmass_U, hpos, hH_norm, hmass, ht_pos, ht_le, hdef⟩ :=
    finite_head_bad_limit_data_positiveGauge_wip F K (rho := rho) hbad
  have him_inner :
      (Finset.sum F.support
        (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha))).im = 0 :=
    positiveGauge_limit_inner_im_zero_wip hF_norm hpos ht_pos hcoeff
  have hlimit :
      let L : ℂ :=
        Finset.sum F.support
          (fun alpha =>
            (coeffPkappa F alpha + (T : ℂ) * coeffSkappa U alpha) *
              star (coeffPkappa F alpha))
      L.im = 0 ∧ 0 ≤ L.re :=
    positiveGauge_limit_affine_wip hpos ht_tendsto hcoeff
  have hzero : ∀ alpha, coeffSkappa U alpha = 0 := by
    refine
      bad_limit_coeff_zero_from_exact_rigidity_positiveGauge_wip
        hd kappa F hF_ne hF_norm hT_mem him_inner hlimit ?_ ?_
    · intro hT_zero
      have ht_tendsto_zero :
          Filter.Tendsto (fun m => t (φ m)) Filter.atTop (nhds 0) := by
        simpa [hT_zero] using ht_tendsto
      exact
        finite_head_bad_limit_real_part_ae_wip
          (hd := hd) (kappa := kappa) F hφ_strict ht_tendsto_zero
          hcoeff hH_norm hpartial ht_pos ht_le hdef
    · intro hT_pos
      exact
        finite_head_bad_limit_modulus_ae_wip
          (hd := hd) (kappa := kappa) F hφ_strict ht_tendsto
          hcoeff hH_norm hpartial ht_le hdef
  exact finite_head_mass_contradiction_of_coeff_zero_wip K h_rho hmass_U hzero

private lemma evalPkappa_pointwise_bound_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) (z : Cd d) :
    ‖evalPkappa kappa G z‖ ≤
      defectFunctionPkappa_coeff_wip kappa F G z + 2 * ‖evalPkappa kappa F z‖ := by
  have hsub :
      evalPkappa kappa G z = evalPkappa kappa (F + G) z - evalPkappa kappa F z := by
    rw [evalPkappa_add_apply_wip kappa F G z, add_sub_cancel_left]
  have haux :
      ‖evalPkappa kappa (F + G) z‖ ≤
        defectFunctionPkappa_coeff_wip kappa F G z + ‖evalPkappa kappa F z‖ := by
    unfold defectFunctionPkappa_coeff_wip
    exact sub_le_iff_le_add.mp (le_abs_self _)
  calc
    ‖evalPkappa kappa G z‖ = ‖evalPkappa kappa (F + G) z - evalPkappa kappa F z‖ := by rw [hsub]
    _ ≤ ‖evalPkappa kappa (F + G) z‖ + ‖evalPkappa kappa F z‖ := norm_sub_le _ _
    _ ≤ defectFunctionPkappa_coeff_wip kappa F G z +
          ‖evalPkappa kappa F z‖ + ‖evalPkappa kappa F z‖ := by linarith
    _ = defectFunctionPkappa_coeff_wip kappa F G z + 2 * ‖evalPkappa kappa F z‖ := by ring

private theorem norm_le_defect_add_two_coeff_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) (hF_norm : ‖F‖ = 1) :
    ‖G‖ ≤ defect F G + 2 := by
  have hdef_mem := memLp_two_defectFunctionPkappa_coeff_wip hd kappa F G
  have htwoF_mem :
      MeasureTheory.MemLp (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖) 2 (gammaD d) :=
    (memLp_two_evalPkappa_coeff_wip hd kappa F).norm.const_smul (2 : ℝ)
  have hsum_mem :
      MeasureTheory.MemLp
        (defectFunctionPkappa_coeff_wip kappa F G + fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
        2 (gammaD d) := hdef_mem.add htwoF_mem
  have hmono :
      MeasureTheory.lpNorm (evalPkappa kappa G) 2 (gammaD d) ≤
        MeasureTheory.lpNorm
          (defectFunctionPkappa_coeff_wip kappa F G +
            fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
          2 (gammaD d) := by
    refine MeasureTheory.lpNorm_mono_real hsum_mem ?_
    intro z
    simpa using evalPkappa_pointwise_bound_coeff_wip kappa F G z
  have htri :
      MeasureTheory.lpNorm
          (defectFunctionPkappa_coeff_wip kappa F G +
            fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
          2 (gammaD d)
        ≤ MeasureTheory.lpNorm (defectFunctionPkappa_coeff_wip kappa F G) 2 (gammaD d) +
            MeasureTheory.lpNorm (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖) 2
              (gammaD d) := MeasureTheory.lpNorm_add_le hdef_mem
      (g := fun z : Cd d => 2 * ‖evalPkappa kappa F z‖) (by norm_num)
  have hnormEq :
      MeasureTheory.lpNorm (fun z : Cd d => ‖evalPkappa kappa F z‖) 2 (gammaD d) =
        MeasureTheory.lpNorm (evalPkappa kappa F) 2 (gammaD d) := by
    simpa using
      (MeasureTheory.lpNorm_norm (μ := gammaD d) (p := (2 : ENNReal))
        (memLp_two_evalPkappa_coeff_wip hd kappa F).aestronglyMeasurable)
  have htwoF_norm :
      MeasureTheory.lpNorm (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
        2 (gammaD d) = 2 := by
    calc
      MeasureTheory.lpNorm (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
          2 (gammaD d)
          = MeasureTheory.lpNorm
              ((2 : ℝ) • fun z : Cd d => ‖evalPkappa kappa F z‖) 2 (gammaD d) := by rfl
      _ = ‖(2 : ℝ)‖ *
            MeasureTheory.lpNorm (fun z : Cd d => ‖evalPkappa kappa F z‖) 2
              (gammaD d) := by
            rw [MeasureTheory.lpNorm_const_smul]
            norm_num
      _ = 2 * MeasureTheory.lpNorm (evalPkappa kappa F) 2 (gammaD d) := by
            rw [hnormEq]
            norm_num
      _ = 2 * ‖F‖ := by rw [evalPkappa_lpNorm_eq_norm_coeff_wip hd kappa F]
      _ = 2 := by simp [hF_norm]
  calc
    ‖G‖ = MeasureTheory.lpNorm (evalPkappa kappa G) 2 (gammaD d) := by
          symm
          exact evalPkappa_lpNorm_eq_norm_coeff_wip hd kappa G
    _ ≤ MeasureTheory.lpNorm
          (defectFunctionPkappa_coeff_wip kappa F G +
            fun z : Cd d => 2 * ‖evalPkappa kappa F z‖)
          2 (gammaD d) := hmono
    _ ≤ MeasureTheory.lpNorm (defectFunctionPkappa_coeff_wip kappa F G) 2 (gammaD d) +
          MeasureTheory.lpNorm (fun z : Cd d => 2 * ‖evalPkappa kappa F z‖) 2
            (gammaD d) := htri
    _ = defect F G + 2 := by rw [← defect_lpNorm_eq_coeff_wip hd kappa F G, htwoF_norm]

private theorem coefficient_head_mass_of_highAnnulus_small_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (E : Finset (Idx d)) (J : Nat) :
    ∃ Kextra : Finset (Idx d), ∃ rho_head : ℝ, 0 < rho_head ∧
      ∀ {H : Pkappa d kappa},
        ‖H‖ = 1 ->
        highAnnulusMass J (ofPkappa kappa H) <= 1 / 4 ->
        rho_head <=
          Finset.sum (coefficientControlSet_wip E F ∪ Kextra)
            (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
  obtain ⟨Kextra, rho_head, hrho_head_pos, hlow⟩ :=
    lowAnnulusProjection hd kappa J
  refine ⟨Kextra, rho_head, hrho_head_pos, ?_⟩
  intro H hH_norm hhigh
  have hpartition := annulusMassPartition hd kappa J H
  have hH_sq : ‖H‖ ^ 2 = 1 := by nlinarith
  have hlow_lower : 1 / 4 < lowAnnulusMass J (ofPkappa kappa H) := by nlinarith
  have hKextra_mass_gt :
      rho_head < Finset.sum Kextra (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
    by_contra hnot
    have hmass_le :
        Finset.sum Kextra (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) <= rho_head :=
      le_of_not_gt hnot
    have hlow_upper : lowAnnulusMass J (ofPkappa kappa H) <= 1 / 4 :=
      hlow hH_norm hmass_le
    linarith
  have hKextra_subset : Kextra ⊆ coefficientControlSet_wip E F ∪ Kextra := by
    intro alpha halpha
    exact Finset.mem_union.mpr (Or.inr halpha)
  have hsum_le_union :
      Finset.sum Kextra (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) <=
        Finset.sum (coefficientControlSet_wip E F ∪ Kextra)
          (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hKextra_subset
      (by intro alpha halpha hnot; positivity)
  exact le_trans (le_of_lt hKextra_mass_gt) hsum_le_union

private theorem highAnnulusControl_eps_noOrth_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1)
    {eps : ℝ} (h_eps : 0 < eps) :
    ∃ J : Nat, ∃ delta_high : ℝ, 0 < delta_high ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        ‖H‖ = 1 ->
        0 < t ->
        t <= 4 ->
        defect F (t • H) <= delta_high * t ->
        highAnnulusMass J (ofPkappa kappa H) <= eps := by
  obtain ⟨J, C, hC_pos, hann⟩ :=
    finite_base_annulus_estimate hd kappa F ⟨hF_ne, hF_norm⟩
      (eps / 2) (by linarith)
  let delta_high : ℝ := min 1 (eps / (2 * C))
  have hdelta_high_pos : 0 < delta_high := by
    dsimp [delta_high]
    exact lt_min zero_lt_one (div_pos h_eps (mul_pos (by norm_num) hC_pos))
  refine ⟨J, delta_high, hdelta_high_pos, ?_⟩
  intro H t hH_norm ht_pos ht_le_four hdefect
  have hdelta_nonneg : 0 <= delta_high := le_of_lt hdelta_high_pos
  have hdelta_le_one : delta_high <= 1 := by
    dsimp [delta_high]
    exact min_le_left _ _
  have hdelta_le : delta_high <= eps / (2 * C) := by
    dsimp [delta_high]
    exact min_le_right _ _
  have hCdelta_le : C * delta_high <= eps / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hdelta_le (le_of_lt hC_pos)
    have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    have hcalc : C * (eps / (2 * C)) = eps / 2 := by field_simp [hC_ne]
    nlinarith
  have hdelta_sq_le : delta_high ^ 2 <= delta_high := by nlinarith [sq_nonneg delta_high]
  have hCdelta_sq_le : C * delta_high ^ 2 <= eps / 2 := by
    calc
      C * delta_high ^ 2 <= C * delta_high :=
        mul_le_mul_of_nonneg_left hdelta_sq_le (le_of_lt hC_pos)
      _ <= eps / 2 := hCdelta_le
  have hhigh :
      highAnnulusMass J (ofPkappa kappa H) <= C * delta_high ^ 2 + eps / 2 :=
    hann hH_norm ht_pos ht_le_four hdelta_nonneg hdefect
  linarith

theorem positiveGauge_coercivity
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ G : Pkappa d kappa,
        positivePhaseGauge F (F + G) ->
          ‖G‖ <= C_F * defect F G := by
  obtain ⟨J, delta_high, hdelta_high_pos, hhigh⟩ :=
    highAnnulusControl_eps_noOrth_wip hd kappa F hF_ne hF_norm
      (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨Kextra, rho_head, hrho_head_pos, hhead⟩ :=
    coefficient_head_mass_of_highAnnulus_small_wip hd kappa F (∅ : Finset (Idx d)) J
  let K : Finset (Idx d) := coefficientControlSet_wip (∅ : Finset (Idx d)) F ∪ Kextra
  obtain ⟨delta_head, hdelta_head_pos, hhead_lower⟩ :=
    finite_head_defect_lower_bound_positiveGauge_wip
      hd kappa F hF_ne hF_norm K rho_head hrho_head_pos
  let delta : ℝ := min delta_high (delta_head / 2)
  let C_F : ℝ := max 2 delta⁻¹
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min hdelta_high_pos (by positivity)
  have hC_F_pos : 0 < C_F := by
    dsimp [C_F]
    exact lt_of_lt_of_le zero_lt_two (le_max_left _ _)
  refine ⟨C_F, hC_F_pos, ?_⟩
  intro G hposG
  by_cases hG : G = 0
  · subst G
    have hzero :
        ‖(0 : Pkappa d kappa)‖ = 0 := by
      change Real.sqrt (Finset.sum (0 : Pkappa d kappa).support
        (fun alpha => ‖(0 : Pkappa d kappa) alpha‖ ^ 2)) = 0
      simp
    rw [hzero]
    exact mul_nonneg (le_of_lt hC_F_pos) (Real.sqrt_nonneg _)
  · let t : ℝ := ‖G‖
    let H : Pkappa d kappa := (((t : ℂ)⁻¹) : ℂ) • G
    have ht_ne : t ≠ 0 := norm_ne_zero_of_ne_zero_pkappa_coeff_wip hG
    have ht_pos : 0 < t := lt_of_le_of_ne (norm_nonneg_pkappa_coeff_wip G) ht_ne.symm
    have hH_norm : ‖H‖ = 1 := by
      dsimp [H, t]
      rw [norm_smul_pkappa_complex_wip]
      have htinv : ‖(t : ℂ)⁻¹‖ * ‖G‖ = 1 := by
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
        have hGnorm_ne : ‖G‖ ≠ 0 := by simpa [t] using ht_ne
        dsimp [t]
        field_simp [hGnorm_ne]
      simpa [t] using htinv
    have hG_eq : G = t • H := by
      ext alpha
      change G alpha = ((t : ℂ) * (((t : ℂ)⁻¹) * G alpha))
      field_simp [ht_ne]
    have hposH : positivePhaseGauge F (F + t • H) := by simpa [hG_eq] using hposG
    have hlarge_bridge : t ≤ defect F G + 2 := by
      simpa [t] using norm_le_defect_add_two_coeff_wip hd kappa F G hF_norm
    by_cases hlt4 : t < 4
    · by_cases hsmall : defect F G ≤ delta * t
      · have hdelta_le_high : delta ≤ delta_high := by
          dsimp [delta]
          exact min_le_left _ _
        have hdelta_le_head_half : delta ≤ delta_head / 2 := by
          dsimp [delta]
          exact min_le_right _ _
        have hdefect_high : defect F (t • H) ≤ delta_high * t := by
          have hstep : defect F G ≤ delta_high * t := by
            refine le_trans hsmall ?_
            exact mul_le_mul_of_nonneg_right hdelta_le_high (le_of_lt ht_pos)
          simpa [hG_eq] using hstep
        have hhigh_mass : highAnnulusMass J (ofPkappa kappa H) ≤ 1 / 4 :=
          hhigh hH_norm ht_pos (le_of_lt hlt4) hdefect_high
        have hmass :
            rho_head <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
          dsimp [K]
          exact hhead hH_norm hhigh_mass
        have hlower : delta_head * t <= defect F (t • H) :=
          hhead_lower hposH hH_norm hmass ht_pos (le_of_lt hlt4)
        have hupper : defect F (t • H) <= (delta_head / 2) * t := by
          have hstep : defect F G ≤ (delta_head / 2) * t := by
            refine le_trans hsmall ?_
            exact mul_le_mul_of_nonneg_right hdelta_le_head_half (le_of_lt ht_pos)
          simpa [hG_eq] using hstep
        exfalso
        nlinarith [hdelta_head_pos, ht_pos, hlower, hupper]
      · have hdelta_inv_le : delta⁻¹ ≤ C_F := by
          dsimp [C_F]
          exact le_max_right _ _
        have hstrict : delta * t < defect F G := lt_of_not_ge hsmall
        have ht_le_delta : t ≤ delta⁻¹ * defect F G := by
          have haux : t ≤ defect F G / delta := by
            rw [le_div_iff₀ hdelta_pos]
            exact le_of_lt (by simpa [mul_comm] using hstrict)
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using haux
        calc
          ‖G‖ = t := rfl
          _ ≤ delta⁻¹ * defect F G := ht_le_delta
          _ ≤ C_F * defect F G := mul_le_mul_of_nonneg_right hdelta_inv_le (Real.sqrt_nonneg _)
    · have hge4 : 4 ≤ t := le_of_not_gt hlt4
      have htwo_defect : t ≤ 2 * defect F G := by
        nlinarith [(Real.sqrt_nonneg _ : (0:ℝ) ≤ defect F G)]
      have htwo_le_C : 2 ≤ C_F := by
        dsimp [C_F]
        exact le_max_left _ _
      calc
        ‖G‖ = t := rfl
        _ ≤ 2 * defect F G := htwo_defect
        _ ≤ C_F * defect F G := by exact mul_le_mul_of_nonneg_right htwo_le_C (Real.sqrt_nonneg _)

private theorem lowAnnulusDefectControl_of_finite_head_lower_bound_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (J : Nat)
    (hhead_lower :
      ∀ (K : Finset (Idx d)) (rho : ℝ), 0 < rho ->
        ∃ delta : ℝ, 0 < delta ∧
          ∀ {H : Pkappa d kappa} {t : ℝ},
            orthogonalToPk F H ->
            ‖H‖ = 1 ->
            rho <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) ->
            0 < t ->
            t <= 4 ->
            delta * t <= defect F (t • H)) :
    ∃ delta_low : ℝ, 0 < delta_low ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        orthogonalToPk F H ->
        ‖H‖ = 1 ->
        0 < t ->
        t <= 4 ->
        highAnnulusMass J (ofPkappa kappa H) <= 1 / 4 ->
        defect F (t • H) <= delta_low * t ->
        lowAnnulusMass J (ofPkappa kappa H) <= 1 / 4 := by
  let E0 : Finset (Idx d) := ∅
  obtain ⟨Kextra, rho_head, hrho_head_pos, hhead⟩ :=
    coefficient_head_mass_of_highAnnulus_small_wip hd kappa F E0 J
  let K : Finset (Idx d) := coefficientControlSet_wip E0 F ∪ Kextra
  obtain ⟨delta_head, hdelta_head_pos, hdefect_lower⟩ :=
    hhead_lower K rho_head hrho_head_pos
  refine ⟨delta_head / 2, by positivity, ?_⟩
  intro H t horth hH_norm ht_pos ht_le_four hhigh hdefect
  have hmass :
      rho_head <= Finset.sum K (fun alpha => ‖coeffPkappa H alpha‖ ^ 2) := by
    dsimp [K]
    exact hhead hH_norm hhigh
  have hlower : delta_head * t <= defect F (t • H) :=
    hdefect_lower horth hH_norm hmass ht_pos ht_le_four
  have hupper : defect F (t • H) <= (delta_head / 2) * t := hdefect
  exfalso
  nlinarith [hdelta_head_pos, ht_pos, hlower, hupper]

private theorem finite_window_lowAnnulusDefectControl_core_wip
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1)
    (J : Nat) :
    ∃ delta_low : ℝ, 0 < delta_low ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        orthogonalToPk F H ->
        ‖H‖ = 1 ->
        0 < t ->
        t <= 4 ->
        highAnnulusMass J (ofPkappa kappa H) <= 1 / 4 ->
        defect F (t • H) <= delta_low * t ->
        lowAnnulusMass J (ofPkappa kappa H) <= 1 / 4 := by
  exact
    lowAnnulusDefectControl_of_finite_head_lower_bound_wip hd kappa F J
      (fun K rho h_rho =>
        finite_head_defect_lower_bound_wip hd kappa F hF_ne hF_norm K rho h_rho)

theorem lowAnnulusDefectControl
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F : Pkappa d kappa) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1)
    (J : Nat) :
    ∃ delta_low : ℝ, 0 < delta_low ∧
      ∀ {H : Pkappa d kappa} {t : ℝ},
        orthogonalToPk F H ->
        ‖H‖ = 1 ->
        0 < t ->
        t <= 4 ->
        highAnnulusMass J (ofPkappa kappa H) <= 1 / 4 ->
        defect F (t • H) <= delta_low * t ->
        lowAnnulusMass J (ofPkappa kappa H) <= 1 / 4 := by
  let _ := hd
  let _ := hF_ne
  let _ := hF_norm
  /-
  Assembly-specific compactness/no-escape output:
  small defect, after the high-annulus estimate has localized the normalized
  perturbation, must force the low-annulus mass small. This is weaker than the
  previous arbitrary finite-coefficient statement and is exactly the bridge used
  by `orthogonal_coercivity`.
  -/
  by_cases hJ : J = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro H t horth hH_norm ht_pos ht_le_four hhigh hdefect
    subst J
    have hnonempty : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    have hempty : lowAnnuli d 0 = ∅ := by simp [lowAnnuli]
    simp [lowAnnulusMass, hempty]
  · exact finite_window_lowAnnulusDefectControl_core_wip hd kappa F hF_ne hF_norm J

end DimdPolyLEAN
