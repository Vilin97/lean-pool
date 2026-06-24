/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.ImportedAnalyticInputs
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ProductBasisAndAnnuli

/-! # TensorBasis -/


open scoped BigOperators

noncomputable section

namespace DimdPolyLEAN

/-!
# TensorBasis

Statement-first scaffold for the frozen coefficient model and realization maps
for the fixed-dimension polyanalytic Fock basis.
-/

theorem coeff_ofPkappa
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) (alpha : Idx d) :
    coeffSkappa (ofPkappa kappa F) alpha = coeffPkappa F alpha := by
  let _ := hd
  simp [coeffSkappa, coeffPkappa, ofPkappa]

theorem evalPkappa_zero
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    evalPkappa kappa (0 : Pkappa d kappa) = 0 := by
  let _ := hd
  ext z
  simp [evalPkappa]

theorem evalPkappa_add
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    evalPkappa kappa (F + G) = fun z => evalPkappa kappa F z + evalPkappa kappa G z := by
  let _ := hd
  ext z
  simp [evalPkappa, Finsupp.sum_add_index, add_mul]

theorem evalPkappa_smul
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (c : ℂ) (F : Pkappa d kappa) :
    evalPkappa kappa (c • F) = fun z => c * evalPkappa kappa F z := by
  let _ := hd
  ext z
  by_cases hc : c = 0
  · subst c
    simp [evalPkappa]
  · unfold evalPkappa
    rw [Finsupp.sum, Finsupp.sum, Finsupp.support_smul_eq hc, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    rw [Finsupp.smul_apply]
    simp [mul_left_comm, mul_comm]

theorem evalPkappa_sub
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    evalPkappa kappa (F - G) = fun z => evalPkappa kappa F z - evalPkappa kappa G z := by
  let _ := hd
  have hneg : -G = (-1 : ℂ) • G := by
    ext alpha
    simp
  rw [sub_eq_add_neg, hneg, evalPkappa_add hd kappa F ((-1 : ℂ) • G),
    evalPkappa_smul hd kappa (-1 : ℂ) G]
  ext z
  simp [sub_eq_add_neg]

theorem projFinset_idempotent
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (E : Finset (Idx d)) (F : Pkappa d kappa) :
    projFinset E (projFinset E F) = projFinset E F := by
  let _ := hd
  ext alpha
  by_cases h : alpha ∈ E
  · simp [projFinset, h]
  · simp [projFinset, h]

theorem exact_truncate_coeff_energy
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d}
    (E : Finset (Idx d)) (F : Skappa d kappa) :
    ‖truncateFinset E F‖ ^ 2 = Finset.sum E (fun alpha => ‖coeffSkappa F alpha‖ ^ 2) := by
  let _ := hd
  classical
  have hcoeff :
      ∀ alpha : Idx d, truncateFinset E F alpha = if alpha ∈ E then coeffSkappa F alpha else 0 := by
    intro alpha
    have hsum :
        truncateFinset E F alpha =
          (∑ beta ∈ E, Finsupp.single beta (coeffSkappa F beta)) alpha := by rfl
    rw [hsum]
    by_cases h : alpha ∈ E
    · simp [h, Finsupp.single_apply]
    · simp [h, Finsupp.single_apply]
  have hsupp : (truncateFinset E F).support ⊆ E := by
    intro alpha halpha
    by_contra hnot
    have hzero : truncateFinset E F alpha = 0 := by simp [hcoeff alpha, hnot]
    exact (Finsupp.mem_support_iff.mp halpha) hzero
  change
    (Real.sqrt (Finset.sum (truncateFinset E F).support
      (fun alpha => ‖truncateFinset E F alpha‖ ^ 2))) ^ 2 =
      Finset.sum E (fun alpha => ‖coeffSkappa F alpha‖ ^ 2)
  rw [Real.sq_sqrt]
  · calc
      Finset.sum (truncateFinset E F).support
          (fun alpha => ‖truncateFinset E F alpha‖ ^ 2)
          = Finset.sum E (fun alpha => ‖truncateFinset E F alpha‖ ^ 2) := by
            exact Finset.sum_subset hsupp fun alpha _E hsupport => by
              have hzero : truncateFinset E F alpha = 0 :=
                Finsupp.notMem_support_iff.mp hsupport
              simp [hzero]
      _ = Finset.sum E (fun alpha => ‖coeffSkappa F alpha‖ ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro alpha halpha
            simp [hcoeff alpha, halpha]
  · positivity

private theorem phi1D_eq_oneDimPhi
    (k n : Nat) (z : ℂ) :
    phi1D k n z = Hermite1DimdLEAN.oneDimPhi k n z := by
  unfold phi1D complexHermite Hermite1DimdLEAN.oneDimPhi
  congr 1
  · simp [one_div, mul_comm]
  · rw [Nat.min_comm k n]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj' : j ≤ min n k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjn : j ≤ n := le_trans hj' (Nat.min_le_left _ _)
    have hfac_ne : (Nat.factorial (n - j) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - j)
    have hfactor : (Nat.factorial j : ℂ) * (Nat.choose n j : ℂ) =
        (Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) := by
      apply mul_right_cancel₀ hfac_ne
      calc
        ((Nat.factorial j : ℂ) * (Nat.choose n j : ℂ)) * (Nat.factorial (n - j) : ℂ)
            = (Nat.choose n j : ℂ) * (Nat.factorial j : ℂ) * (Nat.factorial (n - j) : ℂ) := by ring
        _ = (Nat.factorial n : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
        _ = ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
              (Nat.factorial (n - j) : ℂ) := by field_simp [hfac_ne]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      congrArg
        (fun x : ℂ => ((-1 : ℂ) ^ j) * x * (Nat.choose k j : ℂ) * z ^ (n - j) * (star z) ^ (k - j))
        hfactor

private theorem Phi_eq_PhiKappaAlpha
    {d : Nat} (kappa alpha : MultiIndex d) (z : Cd d) :
    Phi kappa alpha z = Hermite1DimdLEAN.PhiKappaAlpha kappa alpha z := by
  unfold Phi Hermite1DimdLEAN.PhiKappaAlpha
  refine Finset.prod_congr rfl ?_
  intro q hq
  exact phi1D_eq_oneDimPhi (kappa q) (alpha q) (z q)

private lemma oneDimPhi_phaseLaw
    (k n : Nat) (t : ℝ) (z : ℂ) :
    Hermite1DimdLEAN.oneDimPhi k n (Complex.exp (Complex.I * t) * z) =
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
        Hermite1DimdLEAN.oneDimPhi k n z := by
  obtain ⟨radial, hradial⟩ := Hermite1DimdLEAN.oneVariableAngularFactorization k n
  have hz : ((‖z‖ : ℂ) * Complex.exp (Complex.I * z.arg)) = z := by
    simp [mul_comm Complex.I (z.arg : ℂ), Complex.norm_mul_exp_arg_mul_I z]
  have hrot :
      Complex.exp (Complex.I * t) * z =
        ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by
    calc
      Complex.exp (Complex.I * t) * z =
          Complex.exp (Complex.I * t) * ((‖z‖ : ℂ) * Complex.exp (Complex.I * z.arg)) := by rw [hz]
      _ = ((‖z‖ : ℂ) * Complex.exp (Complex.I * t)) * Complex.exp (Complex.I * z.arg) := by ring_nf
      _ = (‖z‖ : ℂ) * (Complex.exp (Complex.I * t) * Complex.exp (Complex.I * z.arg)) := by
            rw [mul_assoc]
      _ = ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by
            rw [← Complex.exp_add]
            congr 1
            ring_nf
  have hleft :
      Hermite1DimdLEAN.oneDimPhi k n ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by simpa using hradial ‖z‖ (t + z.arg)
  have hright :
      Hermite1DimdLEAN.oneDimPhi k n z =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by simpa [hz] using hradial ‖z‖ z.arg
  have hexp :
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
          Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) := by
    rw [show Complex.I * ((((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) =
        Complex.I * ((((n : ℤ) - (k : ℤ) : ℂ) * t)) +
          Complex.I * ((((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) by ring_nf]
    rw [Complex.exp_add]
  calc
    Hermite1DimdLEAN.oneDimPhi k n (Complex.exp (Complex.I * t) * z) =
        Hermite1DimdLEAN.oneDimPhi k n
          ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by rw [hrot]
    _ = Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := hleft
    _ = Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
          Hermite1DimdLEAN.oneDimPhi k n z := by
          rw [hexp, hright]
          ring_nf

theorem Phi_rotate_one_exp
    {d : Nat} (kappa alpha : MultiIndex d) (q0 : Fin d) (t : ℝ) (z : Cd d) :
    Phi kappa alpha (Function.update z q0 (Complex.exp (Complex.I * t) * z q0)) =
      Complex.exp (Complex.I * (((alpha q0 : ℤ) - (kappa q0 : ℤ) : ℂ) * t)) *
        Phi kappa alpha z := by
  classical
  rw [Phi_eq_PhiKappaAlpha, Phi_eq_PhiKappaAlpha]
  unfold Hermite1DimdLEAN.PhiKappaAlpha
  have hupdate :
      (fun q : Fin d =>
        Hermite1DimdLEAN.oneDimPhi (kappa q) (alpha q)
          (Function.update z q0 (Complex.exp (Complex.I * t) * z q0) q)) =
        Function.update
          (fun q : Fin d => Hermite1DimdLEAN.oneDimPhi (kappa q) (alpha q) (z q))
          q0
          (Hermite1DimdLEAN.oneDimPhi (kappa q0) (alpha q0)
            (Complex.exp (Complex.I * t) * z q0)) := by
    funext q
    by_cases hq : q = q0
    · subst hq
      simp
    · simp [Function.update, hq]
  rw [hupdate, Finset.prod_update_of_mem (s := Finset.univ) (i := q0) (by simp), oneDimPhi_phaseLaw]
  conv_rhs =>
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (s := Finset.univ) (i := q0) (by simp)]
  ring_nf

private lemma fourier_mk_eq_exp
    (n : ℤ) (θ : ℝ) :
    (fourier n (QuotientAddGroup.mk θ : Circle) : ℂ) =
      Complex.exp (Complex.I * (n : ℂ) * θ) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem Phi_rotateCoord_circle_phase
    {d : Nat} (kappa alpha : MultiIndex d) (q0 : Fin d)
    (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      Phi kappa alpha
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
    (fourier ((alpha q0 : Nat) : Int) x : ℂ) *
      Phi kappa alpha z := by
  induction x using Quotient.inductionOn with
  | h θ =>
      rw [fourier_mk_eq_exp ((kappa q0 : Nat) : Int) θ,
        fourier_mk_eq_exp ((alpha q0 : Nat) : Int) θ,
        fourier_mk_eq_exp (1 : Int) θ]
      have hone :
        Complex.exp (Complex.I * ((1 : ℤ) : ℂ) * θ) =
            Complex.exp (Complex.I * θ) := by
        congr 1
        ring_nf
      rw [hone, Phi_rotate_one_exp]
      have hphase :
          Complex.exp (Complex.I * (((kappa q0 : Nat) : Int) : ℂ) * θ) *
              (Complex.exp
                (Complex.I * (((alpha q0 : ℤ) - (kappa q0 : ℤ) : ℂ) * θ)) *
                Phi kappa alpha z) =
            Complex.exp (Complex.I * (((alpha q0 : Nat) : Int) : ℂ) * θ) *
              Phi kappa alpha z := by
        rw [← mul_assoc, ← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
      exact hphase

theorem evalPkappa_rotateCoord_circle_phase_sum
    {d : Nat} (kappa : MultiIndex d) (q0 : Fin d)
    (F : Pkappa d kappa) (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      evalPkappa kappa F
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
      ∑ alpha ∈ F.support,
        F alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
  classical
  unfold evalPkappa
  rw [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  have hphase :=
    Phi_rotateCoord_circle_phase
      (kappa := kappa) (alpha := alpha) (q0 := q0) x z
  have hchar : circleChar (alpha q0) x = (fourier ((alpha q0 : Nat) : Int) x : ℂ) :=
    circleChar_eq_fourier_nat (alpha q0) x
  calc
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
        (F alpha *
          Phi kappa alpha
            (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)))
      = F alpha *
          ((fourier ((kappa q0 : Nat) : Int) x : ℂ) *
            Phi kappa alpha
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) := by ring_nf
    _ = F alpha * ((fourier ((alpha q0 : Nat) : Int) x : ℂ) * Phi kappa alpha z) := by rw [hphase]
    _ = F alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
          rw [hchar]
          ring_nf

private theorem evalPkappa_eq_evalHermiteSum
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    evalPkappa kappa F = Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩ := by
  ext z
  unfold evalPkappa Hermite1DimdLEAN.evalHermiteSum Hermite1DimdLEAN.FiniteHermiteSum.support
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [Phi_eq_PhiKappaAlpha]

theorem evalPkappa_total_mass
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    (∫ z, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = ‖F‖ ^ 2 := by
  let _ := hd
  have hparseval :
      Hermite1DimdLEAN.hermiteNormSq kappa ⟨F⟩ =
        Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) :=
    Hermite1DimdLEAN.finiteParseval kappa ⟨F⟩
  have hparseval' :
      (∫ z, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) =
        Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) := by
    simp only [Hermite1DimdLEAN.hermiteNormSq, Hermite1DimdLEAN.gaussianL2NormSq] at hparseval
    simp only [evalPkappa_eq_evalHermiteSum kappa F]
    exact hparseval
  rw [hparseval']
  change Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) =
    (Real.sqrt (Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2))) ^ 2
  symm
  rw [Real.sq_sqrt]
  positivity

theorem toFun_ofPkappa
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

private theorem summable_sq_hermite_phi_eval
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

private theorem summable_sq_phi1D_eval
    (k : Nat) (z : ℂ) :
    Summable (fun m : Nat => ‖phi1D k m z‖ ^ 2) := by
  have hEq :
      (fun m : Nat => ‖phi1D k m z‖ ^ 2) =
        fun m : Nat => ‖HermitekLEAN.Phi k m z‖ ^ 2 := by
    funext m
    have hphi : phi1D k m z = HermitekLEAN.Phi k m z :=
      phi1D_eq_oneDimPhi k m z
    simp [hphi]
  simpa [hEq] using summable_sq_hermite_phi_eval k z

private theorem Phi_norm_sq_eq_prod
    {d : Nat} (kappa alpha : MultiIndex d) (z : Cd d) :
    ‖Phi kappa alpha z‖ ^ 2 =
      Finset.prod Finset.univ
        (fun q : Fin d => ‖phi1D (kappa q) (alpha q) (z q)‖ ^ 2) := by
  simp [Phi, norm_prod, Finset.prod_pow]

theorem summable_sq_Phi_eval
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
        Finset.sum B (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hE_subset (fun alpha _ _ => sq_nonneg _)
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
    exact (Phi_norm_sq_eq_prod kappa alpha z).symm
  have hprod_le :
      Finset.prod Finset.univ
          (fun q : Fin d =>
            Finset.sum (Finset.range (J q + 1))
              (fun n : Nat => ‖phi1D (kappa q) n (z q)‖ ^ 2)) <=
        Finset.prod Finset.univ
          (fun q : Fin d =>
            ∑' n : Nat, ‖phi1D (kappa q) n (z q)‖ ^ 2) :=
    Finset.prod_le_prod
      (fun q _ => Finset.sum_nonneg fun n _ => sq_nonneg _)
      (fun q _ => (summable_sq_phi1D_eval (kappa q) (z q)).sum_le_tsum
          (Finset.range (J q + 1)) (fun n _ => sq_nonneg _))
  exact le_trans hsum_E_le_B (by rw [hbox_eq]; exact hprod_le)

theorem summable_skappa_eval_mul_of_phi_sq
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

theorem summable_skappa_eval_mul
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (z : Cd d) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha * Phi kappa alpha z) :=
  summable_skappa_eval_mul_of_phi_sq kappa U z (summable_sq_Phi_eval kappa z)

theorem toFun_rotateCoord_circle_phase_tsum
    {d : Nat} (kappa : MultiIndex d) (q0 : Fin d)
    (U : Skappa d kappa) (x : Circle) (z : Cd d) :
    (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
      toFun kappa U
        (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)) =
      ∑' alpha : Idx d,
        coeffSkappa U alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
  classical
  let zrot : Cd d :=
    Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)
  let cκ : ℂ := fourier ((kappa q0 : Nat) : Int) x
  have hsum_rot : Summable (fun alpha : Idx d => coeffSkappa U alpha * Phi kappa alpha zrot) :=
    summable_skappa_eval_mul kappa U zrot
  unfold toFun
  change cκ * (∑' alpha : Idx d, coeffSkappa U alpha * Phi kappa alpha zrot) =
    ∑' alpha : Idx d, coeffSkappa U alpha * Phi kappa alpha z * circleChar (alpha q0) x
  rw [← hsum_rot.tsum_mul_left cκ]
  exact tsum_congr fun alpha => by
    have hphase :=
      Phi_rotateCoord_circle_phase (kappa := kappa) (alpha := alpha) (q0 := q0) x z
    have hchar : circleChar (alpha q0) x = (fourier ((alpha q0 : Nat) : Int) x : ℂ) :=
      circleChar_eq_fourier_nat (alpha q0) x
    dsimp [cκ, zrot]
    calc
      (fourier ((kappa q0 : Nat) : Int) x : ℂ) *
          (coeffSkappa U alpha *
            Phi kappa alpha
              (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0)))
        = coeffSkappa U alpha *
            ((fourier ((kappa q0 : Nat) : Int) x : ℂ) *
              Phi kappa alpha
                (Function.update z q0 ((fourier (1 : Int) x : ℂ) * z q0))) := by ring
      _ = coeffSkappa U alpha *
            ((fourier ((alpha q0 : Nat) : Int) x : ℂ) * Phi kappa alpha z) := by rw [hphase]
      _ = coeffSkappa U alpha * Phi kappa alpha z * circleChar (alpha q0) x := by
            rw [hchar]
            ring

theorem box_subset_box
    {d : Nat} {J K : MultiIndex d} (hJK : J ≤ K) :
    box J ⊆ box K := by
  intro alpha halpha
  rw [box, Fintype.mem_piFinset] at halpha ⊢
  intro q
  have hq := halpha q
  rw [Finset.mem_range] at hq ⊢
  exact Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp hq) (hJK q))

theorem finite_subset_box
    {d : Nat} (E : Finset (Idx d)) :
    ∃ J : MultiIndex d, E ⊆ box J := by
  refine ⟨fun q => Finset.sup E (fun alpha : Idx d => alpha q), ?_⟩
  intro alpha halpha
  rw [box, Fintype.mem_piFinset]
  intro q
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact Finset.le_sup (s := E) (f := fun beta : Idx d => beta q) halpha

theorem tendsto_box_atTop
    {d : Nat} :
    Filter.Tendsto (fun J : MultiIndex d => box J) Filter.atTop Filter.atTop := by
  refine (show Monotone (fun J : MultiIndex d => box J) from ?_).tendsto_atTop_finset ?_
  · intro J K hJK
    exact box_subset_box hJK
  · intro alpha
    refine ⟨alpha, ?_⟩
    rw [box, Fintype.mem_piFinset]
    intro q
    rw [Finset.mem_range]
    exact Nat.lt_succ_self (alpha q)

/-!
## Representative bridge stubs

These are the `Skappa` realization facts needed by the phase-space exact
modulus recovery file.  They are declaration-shaped stubs for the
locally-uniform/L2 representative package described in the tensor-basis

-/

/-- `partialSum`: partial Sum. -/
def partialSum
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (J : MultiIndex d) :
    Cd d -> ℂ :=
  fun z => Finset.sum (box J) fun alpha => coeffSkappa U alpha * Phi kappa alpha z

theorem partialSum_tendsto_toFun_pointwise
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (z : Cd d) :
    Filter.Tendsto (fun J : MultiIndex d => partialSum kappa U J z)
      Filter.atTop (nhds (toFun kappa U z)) := by
  simpa [partialSum, toFun, HasSum, SummationFilter.unconditional, Function.comp_def] using
    ((summable_skappa_eval_mul kappa U z).hasSum.comp (tendsto_box_atTop (d := d)))

/-- `evalPkappaL2`: eval Pkappa L2. -/
def evalPkappaL2 {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    L2Tensor d :=
  toL2 kappa (ofPkappa kappa F)

/-- `PhiL2`: Phi L2. -/
def PhiL2 {d : Nat} (kappa : MultiIndex d) (alpha : Idx d) : L2Tensor d :=
  evalPkappaL2 kappa (Finsupp.single alpha 1)

/-- `BoxPartialSumsLocallyUniformTo`: Box Partial Sums Locally Uniform To. -/
def BoxPartialSumsLocallyUniformTo
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (f : Cd d -> ℂ) : Prop :=
  TendstoLocallyUniformly (fun J : MultiIndex d => partialSum kappa U J) f Filter.atTop

/-- `BoxPartialSumsLocallyUniformCauchy`: Box Partial Sums Locally Uniform Cauchy. -/
def BoxPartialSumsLocallyUniformCauchy
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) : Prop :=
  (∀ K : Set (Cd d), IsCompact K ->
    UniformCauchySeqOn (fun J : MultiIndex d => partialSum kappa U J) Filter.atTop K) ∧
  BoxPartialSumsLocallyUniformTo kappa U (toFun kappa U)

/-- `IsTensorL2Rep`: Is Tensor L2 Rep. -/
def IsTensorL2Rep {d : Nat} (F : L2Tensor d) (f : Cd d -> ℂ) : Prop :=
  ∃ hf_mem : MeasureTheory.MemLp f 2 (gammaD d), hf_mem.toLp f = F

/-- `L2BoxPartialSumsTendTo`: L2 Box Partial Sums Tend To. -/
def L2BoxPartialSumsTendTo
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (F : L2Tensor d) : Prop :=
  Filter.Tendsto (fun J : MultiIndex d => evalPkappaL2 kappa (truncateFinset (box J) U))
    Filter.atTop (nhds F) ∧
  IsTensorL2Rep F (toFun kappa U)

theorem continuous_Phi
    {d : Nat} (kappa alpha : MultiIndex d) :
    Continuous (Phi kappa alpha) := by
  unfold Phi phi1D complexHermite
  continuity

theorem continuous_evalPkappa
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    Continuous (evalPkappa kappa F) := by
  unfold evalPkappa
  refine continuous_finsetSum _ ?_
  intro alpha halpha
  exact continuous_const.mul (continuous_Phi kappa alpha)

theorem integrable_evalPkappa_sq
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.Integrable
      (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) := by
  by_cases hF : F = 0
  · subst hF
    simp [evalPkappa]
  · have hmeas :
        MeasureTheory.AEStronglyMeasurable (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2)
          (gammaD d) :=
      ((continuous_evalPkappa kappa F).norm.pow 2).stronglyMeasurable.aestronglyMeasurable
    by_contra hInt
    have hundef :
        (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = 0 :=
      MeasureTheory.integral_undef hInt
    have hmass :
        (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = ‖F‖ ^ 2 :=
      evalPkappa_total_mass hd kappa F
    have hnorm_ne : ‖F‖ ≠ 0 := by
      intro hnorm
      apply hF
      ext alpha
      by_contra hne
      have hmem : alpha ∈ F.support := Finsupp.mem_support_iff.mpr hne
      have hterm_pos : 0 < ‖F alpha‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
      have hle :
          ‖F alpha‖ ^ 2 <= Finset.sum F.support (fun beta => ‖F beta‖ ^ 2) := Finset.single_le_sum
          (f := fun beta : Idx d => ‖F beta‖ ^ 2) (s := F.support) (a := alpha)
          (fun beta _ => by positivity) hmem
      have hsum_pos : 0 < Finset.sum F.support (fun beta => ‖F beta‖ ^ 2) :=
        lt_of_lt_of_le hterm_pos hle
      change (Real.sqrt (Finset.sum F.support (fun beta => ‖F beta‖ ^ 2))) = 0 at hnorm
      have hsum_zero : Finset.sum F.support (fun beta => ‖F beta‖ ^ 2) = 0 :=
        (Real.sqrt_eq_zero (by positivity)).mp hnorm
      nlinarith
    have hnorm_pos : 0 < ‖F‖ := lt_of_le_of_ne (Real.sqrt_nonneg _) hnorm_ne.symm
    nlinarith

theorem memLp_two_evalPkappa
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.MemLp (evalPkappa kappa F) 2 (gammaD d) := by
  have hmeas :
      MeasureTheory.AEStronglyMeasurable (evalPkappa kappa F) (gammaD d) :=
    (continuous_evalPkappa kappa F).stronglyMeasurable.aestronglyMeasurable
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).2
      (integrable_evalPkappa_sq hd kappa F)

theorem evalPkappaL2_eq_toLp
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    evalPkappaL2 kappa F =
      (memLp_two_evalPkappa hd kappa F).toLp (evalPkappa kappa F) := by
  unfold evalPkappaL2 toL2
  rw [toFun_ofPkappa kappa F]
  simp [memLp_two_evalPkappa hd kappa F]

theorem evalPkappaL2_add
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    evalPkappaL2 kappa (F + G) = evalPkappaL2 kappa F + evalPkappaL2 kappa G := by
  let hF := memLp_two_evalPkappa hd kappa F
  let hG := memLp_two_evalPkappa hd kappa G
  rw [evalPkappaL2_eq_toLp hd kappa (F + G)]
  calc
    (memLp_two_evalPkappa hd kappa (F + G)).toLp (evalPkappa kappa (F + G))
        = (hF.add hG).toLp (evalPkappa kappa F + evalPkappa kappa G) := by
          apply MeasureTheory.MemLp.toLp_congr
          exact Filter.Eventually.of_forall fun z => by
            rw [congrFun (evalPkappa_add hd kappa F G) z]
            rfl
    _ = hF.toLp (evalPkappa kappa F) + hG.toLp (evalPkappa kappa G) :=
          hF.toLp_add hG
    _ = evalPkappaL2 kappa F + evalPkappaL2 kappa G := by
          rw [← evalPkappaL2_eq_toLp hd kappa F, ← evalPkappaL2_eq_toLp hd kappa G]

theorem evalPkappaL2_smul
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (c : ℂ) (F : Pkappa d kappa) :
    evalPkappaL2 kappa (c • F) = c • evalPkappaL2 kappa F := by
  let hF := memLp_two_evalPkappa hd kappa F
  rw [evalPkappaL2_eq_toLp hd kappa (c • F)]
  calc
    (memLp_two_evalPkappa hd kappa (c • F)).toLp (evalPkappa kappa (c • F))
        = (hF.const_smul c).toLp (c • evalPkappa kappa F) := by
          apply MeasureTheory.MemLp.toLp_congr
          exact Filter.Eventually.of_forall fun z => by
            rw [congrFun (evalPkappa_smul hd kappa c F) z]
            rfl
    _ = c • hF.toLp (evalPkappa kappa F) := hF.toLp_const_smul c
    _ = c • evalPkappaL2 kappa F := by rw [← evalPkappaL2_eq_toLp hd kappa F]

theorem evalPkappaL2_zero
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    evalPkappaL2 kappa (0 : Pkappa d kappa) = 0 := by
  simpa using evalPkappaL2_smul hd kappa (0 : ℂ) (0 : Pkappa d kappa)

theorem PhiL2_orthonormal
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (alpha beta : Idx d) :
    inner ℂ (PhiL2 kappa alpha) (PhiL2 kappa beta) =
      if alpha = beta then (1 : ℂ) else 0 := by
  rw [PhiL2, PhiL2, evalPkappaL2_eq_toLp hd kappa (Finsupp.single alpha 1),
    evalPkappaL2_eq_toLp hd kappa (Finsupp.single beta 1), MeasureTheory.L2.inner_def]
  have hcoe_alpha :=
    (memLp_two_evalPkappa hd kappa (Finsupp.single alpha 1)).coeFn_toLp
  have hcoe_beta :=
    (memLp_two_evalPkappa hd kappa (Finsupp.single beta 1)).coeFn_toLp
  trans ∫ z : Cd d, Phi kappa beta z * star (Phi kappa alpha z) ∂ gammaD d
  · apply MeasureTheory.integral_congr_ae
    filter_upwards [hcoe_alpha, hcoe_beta] with z hα hβ
    rw [hα, hβ]
    simp [evalPkappa, mul_comm]
  · have horth :=
      Hermite1DimdLEAN.productBasisOrthonormal (κ := kappa) (α := beta) (β := alpha)
    simp only [Hermite1DimdLEAN.gaussianInner] at horth
    simp only [Phi_eq_PhiKappaAlpha]
    rw [show (if alpha = beta then (1 : ℂ) else 0) = if beta = alpha then 1 else 0 from
      if_congr eq_comm rfl rfl]
    exact horth

theorem evalPkappaL2_single
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (alpha : Idx d) (c : ℂ) :
    evalPkappaL2 kappa (Finsupp.single alpha c : Pkappa d kappa) = c • PhiL2 kappa alpha := by
  have hsingle :
      (Finsupp.single alpha c : Pkappa d kappa) =
        c • (Finsupp.single alpha 1 : Pkappa d kappa) := by
    ext beta
    by_cases h : beta = alpha
    · subst h
      simp
    · simp [Finsupp.single_eq_of_ne h]
  rw [hsingle, evalPkappaL2_smul hd kappa c]
  rfl

theorem finite_coeff_recovery
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa)
    (beta : Idx d) :
    coeffPkappa F beta = inner ℂ (PhiL2 kappa beta) (evalPkappaL2 kappa F) := by
  classical
  induction F using Finsupp.induction with
  | zero =>
      rw [coeffPkappa, evalPkappaL2_zero hd kappa]
      simp
  | single_add alpha c F halpha hc hF =>
      rw [evalPkappaL2_add hd kappa (Finsupp.single alpha c : Pkappa d kappa) F,
        evalPkappaL2_single hd kappa alpha c, inner_add_right, ← hF]
      by_cases hβα : beta = alpha
      · subst hβα
        rw [inner_smul_right, PhiL2_orthonormal hd kappa beta beta]
        simp [coeffPkappa]
      · simp [coeffPkappa, hβα, Finsupp.single_eq_of_ne hβα, inner_smul_right,
          PhiL2_orthonormal hd kappa]

theorem PhiL2_orthonormal_family
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    Orthonormal ℂ (fun alpha : Idx d => PhiL2 kappa alpha) := by
  classical
  rw [orthonormal_iff_ite]
  intro alpha beta
  exact PhiL2_orthonormal hd kappa alpha beta

theorem summable_PhiL2_coeff_smul
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha • PhiL2 kappa alpha) := by
  classical
  let hOrthonormal := PhiL2_orthonormal_family hd kappa
  have hOrthogonalFamily := hOrthonormal.orthogonalFamily
  have hcoeff : Summable (fun alpha : Idx d => ‖coeffSkappa U alpha‖ ^ 2) := by
    simpa [coeffSkappa] using U.summable_norm_sq
  simpa using
    (hOrthogonalFamily.summable_iff_norm_sq_summable
      (fun alpha : Idx d => coeffSkappa U alpha)).2 hcoeff

theorem evalPkappaL2_truncateFinset
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    (E : Finset (Idx d)) :
    evalPkappaL2 kappa (truncateFinset E U) =
      ∑ alpha ∈ E, coeffSkappa U alpha • PhiL2 kappa alpha := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      simp [truncateFinset, evalPkappaL2_zero hd kappa]
  | insert alpha E hnot hE =>
      have hE' :
          evalPkappaL2 kappa (∑ beta ∈ E, Finsupp.single beta (coeffSkappa U beta)) =
            ∑ beta ∈ E, coeffSkappa U beta • PhiL2 kappa beta := by simpa [truncateFinset] using hE
      simp [truncateFinset, Finset.sum_insert hnot, evalPkappaL2_add hd kappa,
        evalPkappaL2_single hd kappa, hE']

theorem evalPkappaL2_box_tendsto_tsum
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    Filter.Tendsto (fun J : MultiIndex d =>
        evalPkappaL2 kappa (truncateFinset (box J) U))
      Filter.atTop
      (nhds (∑' alpha : Idx d, coeffSkappa U alpha • PhiL2 kappa alpha)) := by
  have hsummable := summable_PhiL2_coeff_smul hd kappa U
  simpa [HasSum, SummationFilter.unconditional, evalPkappaL2_truncateFinset hd kappa U,
    Function.comp_def] using
    hsummable.hasSum.comp (tendsto_box_atTop (d := d))

theorem evalPkappa_truncateFinset
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    (E : Finset (Idx d)) :
    evalPkappa kappa (truncateFinset E U) =
      fun z : Cd d => ∑ alpha ∈ E, coeffSkappa U alpha * Phi kappa alpha z := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      ext z
      simp [truncateFinset, evalPkappa]
  | insert alpha E hnot hE =>
      ext z
      have hE' :
          Finsupp.sum (∑ beta ∈ E, Finsupp.single beta (coeffSkappa U beta))
              (fun beta c => c * Phi kappa beta z) =
            ∑ beta ∈ E, coeffSkappa U beta * Phi kappa beta z := by
        simpa [truncateFinset, evalPkappa] using congrFun hE z
      rw [show truncateFinset (insert alpha E) U =
          Finsupp.single alpha (coeffSkappa U alpha) +
            (∑ beta ∈ E, Finsupp.single beta (coeffSkappa U beta)) by
        simp [truncateFinset, Finset.sum_insert hnot]]
      rw [congrFun
        (evalPkappa_add hd kappa (Finsupp.single alpha (coeffSkappa U alpha))
          (∑ beta ∈ E, Finsupp.single beta (coeffSkappa U beta))) z]
      rw [Finset.sum_insert hnot]
      simp [evalPkappa, hE']

private lemma factorial_ratio_le_pow_succ
    {n k j : ℕ} (hjn : j ≤ n) (hjk : j ≤ k) :
    (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) ≤ (n + 1 : ℝ) ^ k := by
  have hnat : n.descFactorial j ≤ (n + 1) ^ k := by
    calc
      n.descFactorial j ≤ n ^ j := Nat.descFactorial_le_pow _ _
      _ ≤ (n + 1) ^ j := Nat.pow_le_pow_left n.le_succ _
      _ ≤ (n + 1) ^ k := Nat.pow_le_pow_right (Nat.succ_pos _) hjk
  have hdiv_nat : n.descFactorial j = n.factorial / (n - j).factorial := by
    rw [Nat.descFactorial_eq_div hjn]
  have hdiv :
      (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) = n.descFactorial j := by
    rw [hdiv_nat, Nat.cast_div (Nat.factorial_dvd_factorial (Nat.sub_le n j))]
    positivity
  rw [hdiv]
  exact_mod_cast hnat

private lemma choose_partial_sum_le_pow_two (k n : ℕ) :
    Finset.sum (Finset.range (min k n + 1)) (fun j => (Nat.choose k j : ℝ)) ≤
      (2 : ℝ) ^ k := by
  calc
    Finset.sum (Finset.range (min k n + 1)) (fun j => (Nat.choose k j : ℝ))
        ≤ Finset.sum (Finset.range (k + 1)) (fun j => (Nat.choose k j : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp at hx ⊢
            omega
          · intro j _ _
            positivity
    _ = (2 : ℝ) ^ k := by exact_mod_cast Nat.sum_range_choose k

private lemma summable_nat_pow_mul_pow_div_factorial_nonneg
    (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => ((n + 1 : ℝ) ^ m) * x ^ n / (Nat.factorial n : ℝ)) := by
  let f : ℕ → ℝ := fun n => ((n + 1 : ℝ) ^ m) * x ^ n / (Nat.factorial n : ℝ)
  rw [← @summable_nat_add_iff ℝ _ _ _ _ m]
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ =>
      ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ))) ?_ ?_ ?_
  · intro n
    positivity
  · intro n
    have hdesc_nat : (n + 1) ^ m ≤ (n + m).descFactorial m := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.pow_sub_le_descFactorial (n + m) m)
    have hpow_real :
        ((n + m + 1 : ℝ) ^ m) ≤
          (m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ) := by
      have hdesc :
          ((n + 1 : ℝ) ^ m) ≤ (((n + m).descFactorial m : ℕ) : ℝ) := by exact_mod_cast hdesc_nat
      calc
        ((n + m + 1 : ℝ) ^ m) ≤ (((m + 1 : ℝ) * (n + 1)) ^ m) := by
          gcongr
          nlinarith
        _ = (m + 1 : ℝ) ^ m * (n + 1 : ℝ) ^ m := by rw [mul_pow]
        _ ≤ (m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ) := by gcongr
    have hfact :
        (Nat.factorial n : ℝ) * (((n + m).descFactorial m : ℕ) : ℝ) =
          (Nat.factorial (n + m) : ℝ) := by
      have hfact_nat : n.factorial * (n + m).descFactorial m = (n + m).factorial := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.factorial_mul_descFactorial (show m ≤ n + m by omega))
      exact_mod_cast hfact_nat
    have hcalc :
        (((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) * x ^ (n + m)) /
            (Nat.factorial (n + m) : ℝ) =
          ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ)) := by
      rw [pow_add, ← hfact]
      have hnfact : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have hndesc_nat : (n + m).descFactorial m ≠ 0 :=
        Nat.ne_of_gt (Nat.descFactorial_pos.mpr (show m ≤ n + m by omega))
      have hndesc : (((n + m).descFactorial m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hndesc_nat
      field_simp [hnfact, hndesc]
    calc
      f (n + m) =
          ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) /
            (Nat.factorial (n + m) : ℝ) := by simp [f]
      _ ≤ (((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) *
              x ^ (n + m)) / (Nat.factorial (n + m) : ℝ) := by
            have hpowx :
                ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) ≤
                  ((m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ)) *
                    x ^ (n + m) := mul_le_mul_of_nonneg_right hpow_real (pow_nonneg hx _)
            have hfacpos : 0 < (Nat.factorial (n + m) : ℝ) := by positivity
            rw [div_le_iff₀ hfacpos]
            calc
              ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) ≤
                  ((m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ)) *
                    x ^ (n + m) := hpowx
              _ =
                  ((((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) *
                      x ^ (n + m)) / (Nat.factorial (n + m) : ℝ)) *
                    (Nat.factorial (n + m) : ℝ) := by
                    have hfacne : (Nat.factorial (n + m) : ℝ) ≠ 0 := by positivity
                    field_simp [hfacne]
      _ = ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ)) := hcalc
  · simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using
      (Real.summable_pow_div_factorial x).mul_left ((m + 1 : ℝ) ^ m * x ^ m)

private def phiMajorant (k n : Nat) (R : ℝ) : ℝ :=
  ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
    Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))

private lemma phiMajorant_nonneg
    {k n : Nat} {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ phiMajorant k n R := by
  unfold phiMajorant
  positivity

private lemma summable_phiMajorant_sq
    (k : Nat) {R : ℝ} (hR : 1 ≤ R) :
    Summable (fun n : Nat => phiMajorant k n R ^ 2) := by
  let C : ℝ := (((2 : ℝ) ^ k) ^ 2 * (R ^ k) ^ 2) / (Nat.factorial k : ℝ)
  have hbase0 :
      Summable
        (fun n : ℕ =>
          ((n + 1 : ℝ) ^ (2 * k)) * (R ^ 2) ^ n / (Nat.factorial n : ℝ)) := by
    apply summable_nat_pow_mul_pow_div_factorial_nonneg
    positivity
  have hbase :
      Summable
        (fun n : ℕ => (((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) /
          (Nat.factorial n : ℝ)) := by
    refine hbase0.congr ?_
    intro n
    rw [← pow_mul, ← pow_mul]
    simp [pow_mul, Nat.mul_comm]
  have hmajorant :
      Summable
        (fun n : ℕ =>
          C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ))) := hbase.mul_left C
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg (phiMajorant k n R)) ?_ hmajorant
  intro n
  have hsqrt_ne :
      Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) ≠ 0 := by positivity
  have : phiMajorant k n R ^ 2 =
      C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)) := by
    dsimp [phiMajorant, C]
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt (by positivity)]
  exact this.le

private lemma phi1D_norm_le_majorant
    {k n : ℕ} {R : ℝ} (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖phi1D k n z‖ ≤ phiMajorant k n R := by
  let S := Finset.range (min k n + 1)
  let term : ℕ → ℂ := fun j =>
    (-1 : ℂ) ^ j * ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) *
      z ^ (n - j) * star z ^ (k - j)
  let common : ℝ := ((n + 1 : ℝ) ^ k) * R ^ k * R ^ n
  have hphi : phi1D k n z = HermitekLEAN.Phi k n z := by
    simpa [Hermite1DimdLEAN.oneDimPhi, HermitekLEAN.Phi] using phi1D_eq_oneDimPhi k n z
  rw [hphi, HermitekLEAN.phi_explicit]
  have hsum_norm : ‖Finset.sum S term‖ ≤ Finset.sum S (fun j => ‖term j‖) :=
    norm_sum_le _ _
  have hterm_bound : ∀ j ∈ S, ‖term j‖ ≤ (Nat.choose k j : ℝ) * common := by
    intro j hj
    have hjk : j ≤ k := by
      simp [S] at hj
      omega
    have hjn : j ≤ n := by
      simp [S] at hj
      omega
    have hratio := factorial_ratio_le_pow_succ hjn hjk
    have hz1 : ‖z‖ ^ (n - j) ≤ R ^ n :=
      le_trans (pow_le_pow_left₀ (norm_nonneg _) hz _) (pow_le_pow_right₀ hR (Nat.sub_le _ _))
    have hz2 : ‖z‖ ^ (k - j) ≤ R ^ k :=
      le_trans (pow_le_pow_left₀ (norm_nonneg _) hz _) (pow_le_pow_right₀ hR (Nat.sub_le _ _))
    calc
      ‖term j‖ =
          (Nat.choose k j : ℝ) *
            ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
              ‖z‖ ^ (n - j) * ‖z‖ ^ (k - j) := by
            dsimp [term]
            simp [norm_pow]
      _ ≤ (Nat.choose k j : ℝ) * ((n + 1 : ℝ) ^ k) * R ^ n * R ^ k := by gcongr
      _ = (Nat.choose k j : ℝ) * common := by
            dsimp [common]
            ring
  have hsum_bound :
      Finset.sum S (fun j => ‖term j‖) ≤
        Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) :=
    Finset.sum_le_sum (fun j hj => hterm_bound j hj)
  have hsum_factor :
      Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) =
        (Finset.sum S (fun j => (Nat.choose k j : ℝ))) * common := by rw [Finset.sum_mul]
  have hfront_nonneg :
      0 ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ :=
    norm_nonneg _
  have hfront :
      ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ =
        ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) := by
    rw [one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), one_div]
  calc
    ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
        Finset.sum S term‖
        ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ *
            Finset.sum S (fun j => ‖term j‖) := le_trans (norm_mul_le _ _) <|
            mul_le_mul_of_nonneg_left hsum_norm (norm_nonneg _)
    _ ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ *
            Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) :=
          mul_le_mul_of_nonneg_left hsum_bound hfront_nonneg
    _ = ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
            Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) := by rw [hfront]
    _ = ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
            ((Finset.sum S (fun j => (Nat.choose k j : ℝ))) * common) := by rw [hsum_factor]
    _ ≤ ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
            (((2 : ℝ) ^ k) * common) := by
          gcongr
          simpa [S] using choose_partial_sum_le_pow_two k n
    _ = phiMajorant k n R := by
          dsimp [phiMajorant, common]
          rw [div_eq_mul_inv]
          ring

private lemma phiMajorant_multi_sq_summable
    {d : Nat} (kappa : MultiIndex d) {R : ℝ} (hR : 1 ≤ R) :
    Summable
      (fun alpha : Idx d =>
        (Finset.prod Finset.univ fun q : Fin d => phiMajorant (kappa q) (alpha q) R) ^ 2) := by
  classical
  refine summable_of_sum_le
    (c := Finset.prod Finset.univ
      (fun q : Fin d => ∑' n : Nat, phiMajorant (kappa q) n R ^ 2))
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
      Finset.sum E
          (fun alpha : Idx d =>
            (Finset.prod Finset.univ fun q : Fin d =>
              phiMajorant (kappa q) (alpha q) R) ^ 2) ≤
        Finset.sum B
          (fun alpha : Idx d =>
            (Finset.prod Finset.univ fun q : Fin d =>
              phiMajorant (kappa q) (alpha q) R) ^ 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hE_subset
      (by intro alpha _ _; exact sq_nonneg _)
  have hbox_eq :
      Finset.sum B
          (fun alpha : Idx d =>
            (Finset.prod Finset.univ fun q : Fin d =>
              phiMajorant (kappa q) (alpha q) R) ^ 2) =
        Finset.prod Finset.univ
          (fun q : Fin d =>
            Finset.sum (Finset.range (J q + 1))
              (fun n : Nat => phiMajorant (kappa q) n R ^ 2)) := by
    dsimp [B]
    symm
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    simp [Finset.prod_pow]
  have hprod_le :
      Finset.prod Finset.univ
          (fun q : Fin d =>
            Finset.sum (Finset.range (J q + 1))
              (fun n : Nat => phiMajorant (kappa q) n R ^ 2)) ≤
        Finset.prod Finset.univ
          (fun q : Fin d => ∑' n : Nat, phiMajorant (kappa q) n R ^ 2) :=
    Finset.prod_le_prod
      (fun q _ => Finset.sum_nonneg fun n _ => sq_nonneg _)
      (fun q _ => (summable_phiMajorant_sq (kappa q) hR).sum_le_tsum
          (Finset.range (J q + 1)) (fun n _ => sq_nonneg _))
  exact le_trans hsum_E_le_B (by rw [hbox_eq]; exact hprod_le)

private theorem uniformCauchySeqOn_of_summable_bound
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) {K : Set (Cd d)}
    {M : Idx d -> ℝ} (hM : Summable M)
    (hbound : ∀ alpha : Idx d, ∀ z ∈ K,
      ‖coeffSkappa U alpha * Phi kappa alpha z‖ ≤ M alpha) :
    UniformCauchySeqOn (fun J : MultiIndex d => partialSum kappa U J) Filter.atTop K := by
  classical
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  rcases (summable_iff_vanishing_norm.mp hM) (ε / 2) hε2 with ⟨E0, hE0⟩
  rcases finite_subset_box E0 with ⟨J0, hE0J0⟩
  refine ⟨J0, ?_⟩
  intro J hJ L hL z hzK
  let term : Idx d -> ℂ := fun alpha => coeffSkappa U alpha * Phi kappa alpha z
  have tail_bound (N : MultiIndex d) (hN : J0 ≤ N) :
      dist (partialSum kappa U N z) (partialSum kappa U J0 z) < ε / 2 := by
    have hsubset : box J0 ⊆ box N := box_subset_box hN
    have htail_eq :
        partialSum kappa U N z - partialSum kappa U J0 z =
          ∑ alpha ∈ box N \ box J0, term alpha := by
      unfold partialSum
      have hsum :=
        Finset.sum_sdiff (s₁ := box J0) (s₂ := box N) (f := term) hsubset
      dsimp [term] at hsum ⊢
      rw [← hsum]
      abel
    have hdisj : Disjoint (box N \ box J0) E0 := by
      rw [Finset.disjoint_left]
      intro alpha halpha hαE0
      exact (Finset.mem_sdiff.mp halpha).2 (hE0J0 hαE0)
    have htail_lt : ‖∑ alpha ∈ box N \ box J0, M alpha‖ < ε / 2 := hE0 _ hdisj
    rw [dist_eq_norm, htail_eq]
    calc
      ‖∑ alpha ∈ box N \ box J0, term alpha‖
          ≤ ∑ alpha ∈ box N \ box J0, ‖term alpha‖ := norm_sum_le _ _
      _ ≤ ∑ alpha ∈ box N \ box J0, M alpha := by
            refine Finset.sum_le_sum ?_
            intro alpha halpha
            exact hbound alpha z hzK
      _ = ‖∑ alpha ∈ box N \ box J0, M alpha‖ := by
            rw [Real.norm_eq_abs]
            exact (abs_of_nonneg (Finset.sum_nonneg fun alpha halpha =>
              le_trans (norm_nonneg _) (hbound alpha z hzK))).symm
      _ < ε / 2 := htail_lt
  have hJtail := tail_bound J hJ
  have hLtail := tail_bound L hL
  calc
    dist (partialSum kappa U J z) (partialSum kappa U L z)
        ≤ dist (partialSum kappa U J z) (partialSum kappa U J0 z) +
            dist (partialSum kappa U J0 z) (partialSum kappa U L z) :=
          dist_triangle _ _ _
    _ = dist (partialSum kappa U J z) (partialSum kappa U J0 z) +
          dist (partialSum kappa U L z) (partialSum kappa U J0 z) := by
          rw [dist_comm (partialSum kappa U J0 z) (partialSum kappa U L z)]
    _ < ε := by linarith

private lemma compact_exists_coord_bound
    {d : Nat} {K : Set (Cd d)} (hK : IsCompact K) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ z ∈ K, ∀ q : Fin d, ‖z q‖ ≤ R := by
  rcases hK.isBounded.subset_closedBall (0 : Cd d) with ⟨r, hr⟩
  refine ⟨max 1 r, le_max_left _ _, ?_⟩
  intro z hz q
  have hzball := hr hz
  have hznorm : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
  exact le_trans (norm_le_pi_norm z q) (le_trans hznorm (le_max_right _ _))

private lemma partialSum_uniformCauchy_on_compact
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) {K : Set (Cd d)}
    (hK : IsCompact K) :
    UniformCauchySeqOn (fun J : MultiIndex d => partialSum kappa U J) Filter.atTop K := by
  classical
  rcases compact_exists_coord_bound hK with ⟨R, hR, hcoord⟩
  let Bprod : Idx d -> ℝ := fun alpha =>
    Finset.prod Finset.univ fun q : Fin d => phiMajorant (kappa q) (alpha q) R
  let M : Idx d -> ℝ := fun alpha => ‖coeffSkappa U alpha‖ * Bprod alpha
  have hR_nonneg : 0 ≤ R := le_trans zero_le_one hR
  have hBprod_nonneg : ∀ alpha : Idx d, 0 ≤ Bprod alpha := by
    intro alpha
    dsimp [Bprod]
    exact Finset.prod_nonneg fun q _ => phiMajorant_nonneg hR_nonneg
  have hM_summable : Summable M := by
    have hcoeff : Summable (fun alpha : Idx d => ‖coeffSkappa U alpha‖ ^ 2) := by
      simpa [coeffSkappa] using U.summable_norm_sq
    have hBsq : Summable (fun alpha : Idx d => Bprod alpha ^ 2) := by
      simpa [Bprod] using phiMajorant_multi_sq_summable kappa hR
    refine Summable.of_nonneg_of_le (fun alpha => ?_) ?_ ((hcoeff.add hBsq).div_const 2)
    · exact mul_nonneg (norm_nonneg _) (hBprod_nonneg alpha)
    · intro alpha
      dsimp [M]
      nlinarith [sq_nonneg (‖coeffSkappa U alpha‖ - Bprod alpha)]
  refine uniformCauchySeqOn_of_summable_bound kappa U hM_summable ?_
  intro alpha z hzK
  have hPhi : ‖Phi kappa alpha z‖ ≤ Bprod alpha := by
    rw [show ‖Phi kappa alpha z‖ =
        Finset.prod Finset.univ
          (fun q : Fin d => ‖phi1D (kappa q) (alpha q) (z q)‖) by
      simp [Phi, norm_prod]]
    exact Finset.prod_le_prod
      (by intro q _; exact norm_nonneg _)
      (by intro q _; exact phi1D_norm_le_majorant hR (hcoord z hzK q))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hPhi (norm_nonneg _)

theorem l2_tsum_represents_toFun
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    IsTensorL2Rep
      (∑' alpha : Idx d, coeffSkappa U alpha • PhiL2 kappa alpha)
      (toFun kappa U) := by
  classical
  let S : L2Tensor d := ∑' alpha : Idx d, coeffSkappa U alpha • PhiL2 kappa alpha
  have hL2 :
      Filter.Tendsto (fun J : MultiIndex d =>
          evalPkappaL2 kappa (truncateFinset (box J) U))
        Filter.atTop (nhds S) := by simpa [S] using evalPkappaL2_box_tendsto_tsum hd kappa U
  have hInMeasure := MeasureTheory.tendstoInMeasure_of_tendsto_Lp hL2
  obtain ⟨ns, hns, hns_ae⟩ := hInMeasure.exists_seq_tendsto_ae'
  have hpartial_ae :
      ∀ᵐ z ∂ gammaD d, ∀ n : ℕ,
        ((evalPkappaL2 kappa (truncateFinset (box (ns n)) U) : L2Tensor d) :
            Cd d -> ℂ) z =
          partialSum kappa U (ns n) z := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    have hcoe_eval :
        ((evalPkappaL2 kappa (truncateFinset (box (ns n)) U) : L2Tensor d) :
            Cd d -> ℂ) =ᵐ[gammaD d]
          evalPkappa kappa (truncateFinset (box (ns n)) U) := by
      rw [evalPkappaL2_eq_toLp hd]
      exact (memLp_two_evalPkappa hd kappa (truncateFinset (box (ns n)) U)).coeFn_toLp
    filter_upwards [hcoe_eval] with z hz
    rw [hz, congrFun (evalPkappa_truncateFinset hd kappa U (box (ns n))) z]
    rfl
  have hS_ae :
      (S : Cd d -> ℂ) =ᵐ[gammaD d] toFun kappa U := by
    filter_upwards [hns_ae, hpartial_ae] with z hSlim hpartial
    have hpartial_lim_S :
        Filter.Tendsto (fun n : ℕ => partialSum kappa U (ns n) z) Filter.atTop
          (nhds (S z)) := by
      convert hSlim using 1
      funext n
      exact (hpartial n).symm
    have hpartial_lim_toFun :
        Filter.Tendsto (fun n : ℕ => partialSum kappa U (ns n) z) Filter.atTop
          (nhds (toFun kappa U z)) :=
      (partialSum_tendsto_toFun_pointwise kappa U z).comp hns
    exact tendsto_nhds_unique hpartial_lim_S hpartial_lim_toFun
  have hmem : MeasureTheory.MemLp (toFun kappa U) 2 (gammaD d) :=
    (MeasureTheory.memLp_congr_ae hS_ae).1 (MeasureTheory.Lp.memLp S)
  have htoLp : hmem.toLp (toFun kappa U) = S := by
    apply MeasureTheory.Lp.ext
    exact hmem.coeFn_toLp.trans hS_ae.symm
  exact ⟨hmem, by simpa [S] using htoLp⟩

theorem partialSum_continuous
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    (J : MultiIndex d) :
    Continuous (partialSum kappa U J) := by
  let _ := hd
  unfold partialSum
  refine continuous_finsetSum _ ?_
  intro alpha halpha
  exact continuous_const.mul (continuous_Phi kappa alpha)

theorem partialSum_locallyUniform
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    BoxPartialSumsLocallyUniformCauchy kappa U := by
  let _ := hd
  have hCauchy : ∀ K : Set (Cd d), IsCompact K ->
      UniformCauchySeqOn (fun J : MultiIndex d => partialSum kappa U J) Filter.atTop K := by
    intro K hK
    exact partialSum_uniformCauchy_on_compact kappa U hK
  refine ⟨hCauchy, ?_⟩
  change TendstoLocallyUniformly
    (fun J : MultiIndex d => partialSum kappa U J) (toFun kappa U) Filter.atTop
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  exact (hCauchy K hK).tendstoUniformlyOn_of_tendsto fun z _ =>
    partialSum_tendsto_toFun_pointwise kappa U z

theorem toFun_eq_boxLimit
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    BoxPartialSumsLocallyUniformTo kappa U (toFun kappa U) := by
  let _ := hd
  exact (partialSum_locallyUniform hd kappa U).2

theorem toL2_eq_boxLimit
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    L2BoxPartialSumsTendTo kappa U (toL2 kappa U) := by
  classical
  let S : L2Tensor d := ∑' alpha : Idx d, coeffSkappa U alpha • PhiL2 kappa alpha
  have hL2 :
      Filter.Tendsto (fun J : MultiIndex d =>
          evalPkappaL2 kappa (truncateFinset (box J) U))
        Filter.atTop (nhds S) := by simpa [S] using evalPkappaL2_box_tendsto_tsum hd kappa U
  have hrepS : IsTensorL2Rep S (toFun kappa U) := by
    simpa [S] using l2_tsum_represents_toFun hd kappa U
  rcases hrepS with ⟨hmem, htoLp⟩
  have htoL2 : toL2 kappa U = S := by
    unfold toL2
    simp [hmem, htoLp]
  constructor
  · simpa [htoL2] using hL2
  · exact ⟨hmem, by simpa [htoL2] using htoLp⟩

theorem continuous_limit_of_locallyUniform_boxPartialSums
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    {f : Cd d -> ℂ}
    (hlim : BoxPartialSumsLocallyUniformTo kappa U f) :
    Continuous f := by
  let _ := hd
  exact hlim.continuous <| Filter.Frequently.of_forall fun J =>
    partialSum_continuous hd kappa U J

theorem toFun_as_L2_eq_boxLimit
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    IsTensorL2Rep (toL2 kappa U) (toFun kappa U) := by
  let _ := hd
  let _ := toFun_eq_boxLimit hd kappa U
  exact (toL2_eq_boxLimit hd kappa U).2

theorem toFun_represents_toL2
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    IsTensorL2Rep (toL2 kappa U) (toFun kappa U) :=
  toFun_as_L2_eq_boxLimit hd kappa U

theorem coeff_recovery
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    (beta : Idx d) :
    coeffSkappa U beta = inner ℂ (PhiL2 kappa beta) (toL2 kappa U) := by
  let _ := hd
  let Φ : L2Tensor d := PhiL2 kappa beta
  have hlimL2 := (toL2_eq_boxLimit hd kappa U).1
  have hinner_cont : Continuous (fun F : L2Tensor d => inner ℂ Φ F) := by fun_prop
  have hlim_inner :
      Filter.Tendsto
        (fun J : MultiIndex d =>
          inner ℂ Φ (evalPkappaL2 kappa (truncateFinset (box J) U)))
        Filter.atTop (nhds (inner ℂ Φ (toL2 kappa U))) :=
    hinner_cont.continuousAt.tendsto.comp hlimL2
  have hbeta_eventually :
      ∀ᶠ J : MultiIndex d in Filter.atTop, beta ∈ box J := by
    filter_upwards [Filter.eventually_atTop.2 ⟨beta, fun J hJ => hJ⟩] with J hJ
    rw [box, Fintype.mem_piFinset]
    intro q
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hJ q)
  have hseq_coeff :
      ∀ᶠ J : MultiIndex d in Filter.atTop,
        inner ℂ Φ (evalPkappaL2 kappa (truncateFinset (box J) U)) =
          coeffSkappa U beta := by
    filter_upwards [hbeta_eventually] with J hbetaJ
    calc
      inner ℂ Φ (evalPkappaL2 kappa (truncateFinset (box J) U))
          = coeffPkappa (truncateFinset (box J) U) beta := by
            simpa [Φ] using (finite_coeff_recovery hd kappa (truncateFinset (box J) U) beta).symm
      _ = coeffSkappa U beta := by
            simp only [coeffPkappa, coeffSkappa, truncateFinset]
            rw [Finsupp.finsetSum_apply, Finset.sum_eq_single beta]
            · simp
            · intro alpha halpha hne
              simp [Finsupp.single_eq_of_ne hne.symm]
            · intro hnot
              exact False.elim (hnot hbetaJ)
  have hlim_coeff :
      Filter.Tendsto
        (fun J : MultiIndex d =>
          inner ℂ Φ (evalPkappaL2 kappa (truncateFinset (box J) U)))
        Filter.atTop (nhds (coeffSkappa U beta)) :=
    tendsto_nhds_of_eventually_eq hseq_coeff
  exact (tendsto_nhds_unique hlim_inner hlim_coeff).symm

theorem toL2_eq_of_toFun_eq
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d} {U V : Skappa d kappa}
    (h : ∀ z, toFun kappa U z = toFun kappa V z) :
    toL2 kappa U = toL2 kappa V := by
  let _ := hd
  have hfun : toFun kappa U = toFun kappa V := funext h
  unfold toL2
  rw [hfun]

theorem skappa_ext_of_coeff_eq
    {d : Nat} {kappa : MultiIndex d} {U V : Skappa d kappa}
    (hcoeff : ∀ alpha, coeffSkappa U alpha = coeffSkappa V alpha) :
    U = V := by
  cases U
  cases V
  simp only [coeffSkappa] at hcoeff
  congr
  funext alpha
  exact hcoeff alpha

theorem continuous_toFun
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    Continuous (toFun kappa U) :=
  continuous_limit_of_locallyUniform_boxPartialSums hd kappa U (toFun_eq_boxLimit hd kappa U)

theorem toFun_smul_complex
    {d : Nat} (kappa : MultiIndex d) (w : ℂ) (U : Skappa d kappa) :
    toFun kappa (w • U) = fun z => w * toFun kappa U z := by
  funext z
  calc
    (∑' alpha : Idx d, (w • U).coeff alpha * Phi kappa alpha z) =
        ∑' alpha : Idx d, w * (U.coeff alpha * Phi kappa alpha z) :=
          tsum_congr fun alpha => mul_assoc w (U.coeff alpha) (Phi kappa alpha z)
    _ = w * ∑' alpha : Idx d, U.coeff alpha * Phi kappa alpha z := by rw [tsum_mul_left]

theorem skappa_ext_of_toFun_eq
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d} {U V : Skappa d kappa}
    (h : ∀ z, toFun kappa U z = toFun kappa V z) :
    U = V := by
  apply skappa_ext_of_coeff_eq
  intro beta
  calc
    coeffSkappa U beta = inner ℂ (PhiL2 kappa beta) (toL2 kappa U) := coeff_recovery hd kappa U beta
    _ = inner ℂ (PhiL2 kappa beta) (toL2 kappa V) := by rw [toL2_eq_of_toFun_eq hd h]
    _ = coeffSkappa V beta := (coeff_recovery hd kappa V beta).symm

end DimdPolyLEAN
