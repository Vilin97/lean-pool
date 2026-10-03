/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.BarNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatXiML
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Product
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.DerivativeBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Explicit estimates for the construction seminorm and time cutoffs. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Construction

/-- The Appendix B seminorm uses the same coordinate derivatives as the norm. -/
theorem barNorm_eq_snorm (f : Vec 2 → ℝ) (n : ℕ) (R : ℝ)
    (hf : ContDiff ℝ n f) :
    AVenhance.barNorm n R f = FaaDiBruno.snorm f n R := by
  have hp (x : Vec 2) (i : Fin n → Fin 2) :
      FaaDiBruno.orderedPartial n f x i =
        iteratedFDeriv ℝ n f x (fun j => basisVec (i j)) := by
    unfold FaaDiBruno.orderedPartial FaaDiBruno.liftVecOne
    change iteratedFDeriv ℝ n (f ∘ (FaaDiBruno.vecOneEquiv 2).toContinuousLinearMap)
      (WithLp.toLp 1 x) (fun j => FaaDiBruno.coordinateVectorOne 2 (i j)) = _
    rw [(FaaDiBruno.vecOneEquiv 2).toContinuousLinearMap.iteratedFDeriv_comp_right hf
      (WithLp.toLp 1 x) le_rfl]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      FaaDiBruno.vecOneEquiv, FaaDiBruno.coordinateVectorOne, basisVec,
      PiLp.coe_continuousLinearEquiv]
  unfold AVenhance.barNorm FaaDiBruno.snorm FaaDiBruno.derivativeSup
    FaaDiBruno.partialSup
  simp_rw [hp]
  have hm (i : Fin n → Fin 2) : AEStronglyMeasurable
      (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j))) volume :=
    by
      have hc := hf.continuous_iteratedFDeriv'
      have hh : Continuous (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j))) := by
        fun_prop
      exact hh.aestronglyMeasurable
  simp_rw [eLpNorm_exponent_top (hm _)]
  rfl

/-- The small cutoff scaling cancels its derivative factor exactly. -/
theorem scaledCutoff_deriv_le {f : ℝ → ℝ} {N : ℕ} {C τ : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hb : ∀ j : ℕ, j ≤ N → ∀ t, |iteratedDeriv j f t| ≤ C)
    (hτ : 0 < τ) (k : ℤ) {j : ℕ} (hj : j ≤ N) (t : ℝ) :
    τ ^ j * |iteratedDeriv j (AVenhance.scaledCutoff f τ k) t| ≤ C := by
  have heq : AVenhance.scaledCutoff f τ k = fun t => f (t / τ - k) := by
    funext t
    unfold AVenhance.scaledCutoff
    congr 1
    field_simp
  rw [heq]
  exact Cutoff.scaled_translate_iteratedDeriv_bound hf hb hτ hj

/-- `e.zeta.mk`, with the original ingredient constant. -/
theorem zetaMK_deriv_le {β : ℝ} (I : AVenhance.Ingredients β)
    (m : ℕ) (k : ℤ) {j : ℕ} (hj : j ≤ AVenhance.Nstar β) (t : ℝ) :
    AVenhance.tau β I.Λ m ^ j * |iteratedDeriv j (I.zetaMK m k) t| ≤ I.Czeta := by
  exact scaledCutoff_deriv_le I.zeta_smooth I.zeta_deriv_le
    (Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) k hj t

lemma ExplicitBarNorm.factorial_coefficient_le_five (n : ℕ) :
    ((n + 1 : ℝ) ^ 2) / (Nat.factorial n : ℝ) ≤ 5 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hfaccast : (Nat.factorial (n + 1) : ℝ) =
        (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by norm_cast
    rw [hfaccast]
    by_cases hn0 : n = 0
    · subst n
      norm_num
    by_cases hn1 : n = 1
    · subst n
      norm_num
    have hn : 2 ≤ n := by omega
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnum : ((n + 2 : ℝ) ^ 2) ≤ (n + 1 : ℝ) ^ 3 := by
      have hn0r : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hprod := mul_nonneg (sub_nonneg.mpr hnr) (sq_nonneg (n : ℝ))
      nlinarith [hprod, hn0r]
    have hstep : ((n + 2 : ℝ) ^ 2) /
          ((n + 1 : ℝ) * (Nat.factorial n : ℝ)) ≤
        ((n + 1 : ℝ) ^ 2) / (Nat.factorial n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hm := mul_le_mul_of_nonneg_right hnum
        (show 0 ≤ (Nat.factorial n : ℝ) from Nat.cast_nonneg _)
      nlinarith [hm]
    have hnumEq : ((↑(n + 1) + 1 : ℝ) ^ 2) = (↑n + 2) ^ 2 := by
      norm_cast
    calc
      ((↑(n + 1) + 1 : ℝ) ^ 2) /
          ((n + 1 : ℝ) * (Nat.factorial n : ℝ)) =
        ((↑n + 2 : ℝ) ^ 2) /
          ((n + 1 : ℝ) * (Nat.factorial n : ℝ)) := by rw [hnumEq]
      _ ≤ ((n + 1 : ℝ) ^ 2) / (Nat.factorial n : ℝ) := hstep
      _ ≤ 5 := ih

/-- A coordinate sine has no dimension loss in the derivative bound. -/
theorem sine_coordinate_partial_le (A ω : ℝ) (hA : 0 ≤ A) (hω : 0 ≤ ω)
    (i : Fin 2) (n : ℕ) (x : Vec 2) (J : Fin n → Fin 2) :
    ‖iteratedFDeriv ℝ n (fun y : Vec 2 => A * Real.sin (ω * y i)) x
      (fun j => basisVec (J j))‖ ≤ A * ω ^ n := by
  let L : Vec 2 →L[ℝ] ℝ := ω • ContinuousLinearMap.proj i
  have hs : ContDiff ℝ n (fun y : Vec 2 => Real.sin (L y)) :=
    Real.contDiff_sin.comp L.contDiff
  have heq : (fun y : Vec 2 => A * Real.sin (ω * y i)) =
      fun y => A • Real.sin (L y) := by rfl
  rw [heq, iteratedFDeriv_const_smul_apply' hs.contDiffAt]
  change ‖A * (iteratedFDeriv ℝ n (Real.sin ∘ L) x
    (fun j => basisVec (J j)))‖ ≤ _
  have hsin : ContDiff ℝ n Real.sin := Real.contDiff_sin
  rw [L.iteratedFDeriv_comp_right hsin x le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hA]
  apply mul_le_mul_of_nonneg_left _ hA
  calc
    ‖(∏ j, L (basisVec (J j))) * iteratedDeriv n Real.sin (L x)‖ =
        (∏ j, ‖L (basisVec (J j))‖) * |iteratedDeriv n Real.sin (L x)| := by
          rw [norm_mul, norm_prod, Real.norm_eq_abs]
    _ ≤ (∏ _j : Fin n, ω) * 1 := by
      apply mul_le_mul _ (Real.abs_iteratedDeriv_sin_le_one n _) (abs_nonneg _)
          (Finset.prod_nonneg (fun _ _ => hω))
      apply Finset.prod_le_prod₀
      · intro j hj; positivity
      · intro j hj
        simp only [L, smul_apply, ContinuousLinearMap.proj_apply,
          smul_eq_mul, basisVec, Pi.single_apply]
        split_ifs <;> simp [abs_of_nonneg hω, hω]
    _ = ω ^ n := by simp

/-- Turning pointwise coordinate derivative bounds into the seminorm. -/
theorem barNorm_le_of_partial_le (f : Vec 2 → ℝ) (n : ℕ) (R B : ℝ)
    (hf : ContDiff ℝ n f)
    (hb : ∀ x (J : Fin n → Fin 2),
      ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ ≤ B) :
    AVenhance.barNorm n R f ≤
      ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
        (ENNReal.ofReal R)⁻¹ ^ n * ENNReal.ofReal B := by
  unfold AVenhance.barNorm
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply iSup_le
  intro J
  rw [eLpNorm_exponent_top (show AEStronglyMeasurable
      (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (J j))) volume from by
    have hc := hf.continuous_iteratedFDeriv'
    have hh : Continuous (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (J j))) := by
      fun_prop
    exact hh.aestronglyMeasurable)]
  exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall (fun x => hb x J))

/-- A geometric derivative bound yields the source constant five at every order. -/
theorem barNorm_le_five_of_partial_le (f : Vec 2 → ℝ) (n : ℕ) {R A : ℝ}
    (hf : ContDiff ℝ n f) (hR : 0 < R) (hA : 0 ≤ A)
    (hb : ∀ x (J : Fin n → Fin 2),
      ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ ≤ A * R ^ n) :
    AVenhance.barNorm n R f ≤ ENNReal.ofReal (5 * A) := by
  refine (barNorm_le_of_partial_le f n R (A * R ^ n) hf hb).trans ?_
  rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_pow hR.le]
  have hcancel : (ENNReal.ofReal R)⁻¹ ^ n * ENNReal.ofReal R ^ n = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by simp [hR]) ENNReal.ofReal_ne_top, one_pow]
  calc
    ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
        (ENNReal.ofReal R)⁻¹ ^ n * (ENNReal.ofReal A * ENNReal.ofReal R ^ n) =
        ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) * ENNReal.ofReal A := by
          calc
            _ = ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
              ENNReal.ofReal A * ((ENNReal.ofReal R)⁻¹ ^ n * ENNReal.ofReal R ^ n) := by ring
            _ = _ := by rw [hcancel, mul_one]
    _ ≤ ENNReal.ofReal 5 * ENNReal.ofReal A := by
      gcongr
      exact ExplicitBarNorm.factorial_coefficient_le_five n
    _ = ENNReal.ofReal (5 * A) := (ENNReal.ofReal_mul (by norm_num)).symm

/-- Explicit barred norm for an arbitrary coordinate sine and a larger radius. -/
theorem barNorm_sine_le (A ω : ℝ) (hA : 0 ≤ A) (hω : 0 ≤ ω)
    (i : Fin 2) (n : ℕ) {R : ℝ} (hR : 0 < R) (hωR : ω ≤ R) :
    AVenhance.barNorm n R (fun x : Vec 2 => A * Real.sin (ω * x i)) ≤
      ENNReal.ofReal (5 * A) := by
  apply barNorm_le_five_of_partial_le _ n (by fun_prop) hR hA
  intro x J
  exact (sine_coordinate_partial_le A ω hA hω i n x J).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hω hωR n) hA)

lemma ExplicitBarNorm.psi_sine_form {β : ℝ} {Λ m : ℕ} (k : ℤ) (x : Vec 2) :
  AVenhance.psi β Λ m k x =
      AVenhance.a β Λ m * AVenhance.epsilon β Λ m ^ 2 *
        (if k % 4 = 1 then
          Real.sin ((2 * Real.pi / AVenhance.epsilon β Λ m) * x 0)
        else if k % 4 = 3 then
          Real.sin ((2 * Real.pi / AVenhance.epsilon β Λ m) * x 1)
        else 0) := by
  unfold AVenhance.psi AVenhance.psi0
  have hcoord (i : Fin 2) :
      2 * Real.pi * ((AVenhance.epsilon β Λ m)⁻¹ * x i) =
        (2 * Real.pi / AVenhance.epsilon β Λ m) * x i := by
    rw [div_eq_mul_inv]
    ring
  by_cases h1 : k % 4 = 1
  · simp only [ite_eq_left h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    simp only [hcoord 0]
  · by_cases h3 : k % 4 = 3
    · simp only [ite_eq_right h1, ite_eq_left h3]
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [hcoord 1]
    · simp only [ite_eq_right h1, ite_eq_right h3]

/-- `e.psimk.snorm`, on the norm, for every derivative order and larger radii. -/
theorem psi_barNorm_le_of_parameters {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (m : ℕ) (k : ℤ) (n : ℕ) {R : ℝ}
    (hR : 2 * Real.pi / AVenhance.epsilon β Λ m ≤ R) :
    AVenhance.barNorm n R (AVenhance.psi β Λ m k) ≤
      ENNReal.ofReal (5 * AVenhance.a β Λ m * AVenhance.epsilon β Λ m ^ 2) := by
  have hε := Cutoff.epsilon_pos (m := m) hβ hβ' hΛ
  have ha := Cutoff.a_pos (m := m) hβ hβ' hΛ
  have hω : 0 < 2 * Real.pi / AVenhance.epsilon β Λ m := by positivity
  have hA : 0 ≤ AVenhance.a β Λ m * AVenhance.epsilon β Λ m ^ 2 := by positivity
  have heq : AVenhance.psi β Λ m k = fun x =>
      AVenhance.a β Λ m * AVenhance.epsilon β Λ m ^ 2 *
      (if k % 4 = 1 then Real.sin ((2 * Real.pi / AVenhance.epsilon β Λ m) * x 0)
       else if k % 4 = 3 then Real.sin ((2 * Real.pi / AVenhance.epsilon β Λ m) * x 1)
       else 0) := funext (ExplicitBarNorm.psi_sine_form k)
  rw [heq]
  by_cases h1 : k % 4 = 1
  · simp only [h1, ite_true]
    simpa only [mul_assoc] using barNorm_sine_le _ _ hA hω.le 0 n (hω.trans_le hR) hR
  · by_cases h3 : k % 4 = 3
    · simp only [ite_eq_right h1, ite_eq_left h3]
      simpa only [mul_assoc] using barNorm_sine_le _ _ hA hω.le 1 n (hω.trans_le hR) hR
    · simp only [h1, ite_false, h3, mul_zero]
      simp [AVenhance.barNorm]

/-- Ingredient-package specialization of the scalar shear estimate. -/
theorem psi_barNorm_le {β : ℝ} (I : AVenhance.Ingredients β)
    (m : ℕ) (k : ℤ) (n : ℕ) {R : ℝ}
    (hR : 2 * Real.pi / AVenhance.epsilon β I.Λ m ≤ R) :
    AVenhance.barNorm n R (AVenhance.psi β I.Λ m k) ≤
      ENNReal.ofReal (5 * AVenhance.a β I.Λ m * AVenhance.epsilon β I.Λ m ^ 2) :=
  psi_barNorm_le_of_parameters I.one_lt_beta I.beta_lt I.two_pow_seven_le m k n hR

/-- Continuous derivatives allow the essential supremum to be evaluated pointwise. -/
theorem continuous_eLpNorm_top_eq_iSup (f : Vec 2 → ℝ) (hf : Continuous f) :
    eLpNorm f ⊤ volume = ⨆ x, ‖f x‖ₑ := by
  rw [eLpNorm_exponent_top hf.aestronglyMeasurable, eLpNormEssSup_eq_essSup_enorm]
  apply le_antisymm essSup_le_iSup
  apply iSup_le
  intro x
  have hae := ae_le_essSup (f := fun y : Vec 2 => ‖f y‖ₑ) (μ := volume)
  have heq : (fun y => min ‖f y‖ₑ (essSup (fun z => ‖f z‖ₑ) volume)) =
      fun y => ‖f y‖ₑ := by
    apply Measure.eq_of_ae_eq (hae.mono (fun y hy => min_eq_left hy))
    · exact hf.enorm.min continuous_const
    · exact hf.enorm
  have hx := congrFun heq x
  exact (min_eq_left_iff).mp hx

/-- A pointwise presentation of the exact norm. -/
theorem barNorm_eq_pointwise (f : Vec 2 → ℝ) (n : ℕ) (R : ℝ)
    (hf : ContDiff ℝ n f) :
    AVenhance.barNorm n R f =
      ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
        (ENNReal.ofReal R)⁻¹ ^ n *
          ⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
            ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ := by
  unfold AVenhance.barNorm
  congr 2
  funext J
  apply continuous_eLpNorm_top_eq_iSup
  have hc := hf.continuous_iteratedFDeriv'
  fun_prop

/-- Addition on the seminorm has constant one. -/
theorem barNorm_add_le (f g : Vec 2 → ℝ) (n : ℕ) (R : ℝ)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    AVenhance.barNorm n R (f + g) ≤ AVenhance.barNorm n R f + AVenhance.barNorm n R g := by
  have hfg : ContDiff ℝ n (f + g) := hf.add hg
  rw [barNorm_eq_pointwise (f + g) n R hfg, barNorm_eq_pointwise _ _ _ hf,
    barNorm_eq_pointwise _ _ _ hg, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply iSup_le
  intro J
  apply iSup_le
  intro x
  rw [iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt,
    add_apply]
  exact (enorm_add_le _ _).trans (add_le_add
    (le_iSup_of_le J (le_iSup_of_le x le_rfl))
    (le_iSup_of_le J (le_iSup_of_le x le_rfl)))

/-- Leibniz with geometric derivative bounds; the rates add exactly. -/
theorem timeProduct_deriv_le {f g : ℝ → ℝ} {N : ℕ} {C D s r : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hC : 0 ≤ C) (_hD : 0 ≤ D) (hs : 0 ≤ s) (_hr : 0 ≤ r)
    (hbF : ∀ i : ℕ, i ≤ N → ∀ t, |iteratedDeriv i f t| ≤ C * s ^ i)
    (hbG : ∀ i : ℕ, i ≤ N → ∀ t, |iteratedDeriv i g t| ≤ D * r ^ i)
    {j : ℕ} (hj : j ≤ N) (t : ℝ) :
    |iteratedDeriv j (f * g) t| ≤ C * D * (s + r) ^ j := by
  rw [iteratedDeriv_mul (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
  calc
    |∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * iteratedDeriv i f t * iteratedDeriv (j - i) g t| ≤
        ∑ i ∈ Finset.range (j + 1),
          |(j.choose i : ℝ) * iteratedDeriv i f t * iteratedDeriv (j - i) g t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        C * D * (s ^ i * r ^ (j - i) * (j.choose i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i ≤ N := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        _ ≤ (j.choose i : ℝ) * (C * s ^ i) * (D * r ^ (j - i)) := by
          gcongr
          · exact hbF i hiN t
          · exact hbG (j - i) ((Nat.sub_le _ _).trans hj) t
        _ = _ := by ring
    _ = C * D * (s + r) ^ j := by rw [add_pow, Finset.mul_sum]

/-- A weighted derivative estimate is equivalently an inverse-rate envelope. -/
theorem derivative_envelope {f : ℝ → ℝ} {τ C : ℝ} (hτ : 0 < τ) (j : ℕ)
    (hb : ∀ t, τ ^ j * |iteratedDeriv j f t| ≤ C) (t : ℝ) :
    |iteratedDeriv j f t| ≤ C * (τ⁻¹) ^ j := by
  have hh := mul_le_mul_of_nonneg_left (hb t) (pow_nonneg (inv_nonneg.mpr hτ.le) j)
  simpa only [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hτ.ne', one_pow, one_mul,
    mul_comm ((τ⁻¹) ^ j) C] using hh

/-- The product bound in time is uniform through `Nstar`, with explicit constants. -/
theorem scaled_timeProduct_deriv_le {f g : ℝ → ℝ} {N : ℕ} {C D τ σ : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hτ : 0 < τ) (hσ : 0 < σ)
    (hbF : ∀ i : ℕ, i ≤ N → ∀ t, τ ^ i * |iteratedDeriv i f t| ≤ C)
    (hbG : ∀ i : ℕ, i ≤ N → ∀ t, σ ^ i * |iteratedDeriv i g t| ≤ D)
    {j : ℕ} (hj : j ≤ N) (t : ℝ) :
    |iteratedDeriv j (f * g) t| ≤ C * D * (τ⁻¹ + σ⁻¹) ^ j := by
  exact timeProduct_deriv_le hf hg hC hD (inv_nonneg.mpr hτ.le) (inv_nonneg.mpr hσ.le)
    (fun i hi t => derivative_envelope hτ i (hbF i hi) t)
    (fun i hi t => derivative_envelope hσ i (hbG i hi) t) hj t

/-- Construction cutoff product, with exact small and large transition rates. -/
theorem zetaMK_hatZetaML_product_deriv_le {β : ℝ} (I : AVenhance.Ingredients β)
    (m : ℕ) (hm : 1 ≤ m) (k l : ℤ) {j : ℕ} (hj : j ≤ AVenhance.Nstar β) (t : ℝ) :
    |iteratedDeriv j (I.zetaMK m k * I.hatZetaML m l) t| ≤
      I.Czeta * I.Chat *
        ((AVenhance.tau β I.Λ m)⁻¹ + (AVenhance.tauP β I.Λ m)⁻¹) ^ j := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (I.zetaMK m k) := by
    unfold AVenhance.Ingredients.zetaMK AVenhance.scaledCutoff
    exact I.zeta_smooth.comp (by fun_prop)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (I.hatZetaML m l) := by
    unfold AVenhance.Ingredients.hatZetaML AVenhance.shiftCutoff
    exact (I.hatZeta_smooth m).comp (by fun_prop)
  exact scaled_timeProduct_deriv_le hf hg (by linarith [I.one_le_Czeta])
    (by linarith [I.one_le_Chat])
    (Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
    (Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
    (fun i hi t => zetaMK_deriv_le I m k hi t)
    (fun i hi t => I.hatZeta_deriv_le m hm l i hi t) hj t

/-- Finite sums retain constant one, as needed after time-cutoff localization. -/
theorem barNorm_sum_le {ι : Type*} (S : Finset ι) (f : ι → Vec 2 → ℝ)
    (n : ℕ) (R : ℝ) (hf : ∀ i ∈ S, ContDiff ℝ n (f i)) :
    AVenhance.barNorm n R (∑ i ∈ S, f i) ≤ ∑ i ∈ S, AVenhance.barNorm n R (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [AVenhance.barNorm]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hS : ∀ k ∈ S, ContDiff ℝ n (f k) := fun k hk => hf k (Finset.mem_insert_of_mem hk)
    have hsum : ContDiff ℝ n (∑ k ∈ S, f k) := by
      convert ContDiff.sum hS using 1
      ext x
      simp
    exact (barNorm_add_le _ _ n R (hf i (Finset.mem_insert_self i S)) hsum).trans
      (add_le_add le_rfl (ih hS))

end AVenhance.Infra.Construction
