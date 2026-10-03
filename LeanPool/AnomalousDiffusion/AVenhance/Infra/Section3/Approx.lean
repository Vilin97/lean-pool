/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.CutoffMemory
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.MatrixBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.QMNRChar
public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Analysis.Calculus.Taylor
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Overlap
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxTimeRegularity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Section 3.3 estimates. Repeated mean-zero periodic primitives have
geometric bounds, rather than the printed factorial gain (E21e). -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section3
open AVenhance

theorem Approx.periodic_primitive_bound {f : ℝ → ℝ} {P B : ℝ}
    (hP : 0 < P) (hB : 0 ≤ B) (hf : Continuous f) (hp : Function.Periodic f P)
    (hz : (∫ t in (0 : ℝ)..P, f t) = 0)
    (hb : ∀ t, |f t| ≤ B) (t : ℝ) :
    |-(∫ s in (0 : ℝ)..t, f s) + ∫ u in (0 : ℝ)..1, ∫ s in (0 : ℝ)..u, f s| ≤
      2 * P * B := by
  let F : ℝ → ℝ := fun u => ∫ s in (0 : ℝ)..u, f s
  have hper : Function.Periodic F P := by
    intro u
    have hcell : (∫ s in u..u + P, f s) = 0 := by
      rw [hp.intervalIntegral_add_eq u 0]
      simpa using hz
    dsimp [F]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 u) (hf.intervalIntegrable u (u + P)), hcell, add_zero]
  have hcellbound : ∀ u ∈ Set.Icc 0 P, |F u| ≤ P * B := by
    intro u hu
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := u) (f := f)
      (fun s _ => by simpa only [Real.norm_eq_abs] using hb s)
    have huabs : |u - 0| = u := by simp [abs_of_nonneg hu.1]
    rw [huabs, Real.norm_eq_abs] at h
    exact h.trans (by nlinarith only [hu.2, hB])
  have hglobal : ∀ u, |F u| ≤ P * B := by
    intro u
    obtain ⟨v, hv, heq⟩ := hper.exists_mem_Ico₀ hP u
    rw [heq]
    exact hcellbound v ⟨hv.1, hv.2.le⟩
  have hmean : |∫ u in (0 : ℝ)..1, F u| ≤ P * B := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (f := F)
      (fun u _ => by simpa only [Real.norm_eq_abs] using hglobal u)
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
  change |-F t + ∫ u in (0 : ℝ)..1, F u| ≤ _
  calc
    _ ≤ |F t| + |∫ u in (0 : ℝ)..1, F u| := by
      simpa only [abs_neg] using abs_add_le (-F t) (∫ u in (0 : ℝ)..1, F u)
    _ ≤ P * B + P * B := add_le_add (hglobal t) hmean
    _ = _ := by ring

/-- Corrected geometric bound for the actual mean-zero primitives.
The factorial in the printed `e.qmnr.bounds` is not used. -/
theorem qMNR_entry_abs_le_geometric {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (hn : n ≤ Nstar β)
    (r : ℕ) (t : ℝ) (i j : Fin 2) :
    |I.qMNR κ m n r t i j| ≤
      2 * ((2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
        (n.factorial : ℝ) * (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
        (I.Czeta / tau β I.Λ m ^ n)) * (8 * tau β I.Λ m) ^ r := by
  let B := (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
      (n.factorial : ℝ) * (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
      (I.Czeta / tau β I.Λ m ^ n)
  have hC : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hτ := I.tau_pos' m
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hP : 0 < 4 * tau β I.Λ m := by positivity
  have hchar := I.qMNR_char κ hκ m hm n
  suffices ∀ r t, |I.qMNR κ m n r t i j| ≤ 2 * B * (8 * tau β I.Λ m) ^ r from this r t
  intro r
  induction r with
  | zero =>
    intro t
    change |I.jMN κ m n t i j - timeAvgMat (I.jMN κ m n) i j| ≤ _
    calc
      _ ≤ |I.jMN κ m n t i j| + |timeAvgMat (I.jMN κ m n) i j| := abs_sub _ _
      _ ≤ B + B := add_le_add (jMN_entry_abs_le I m hn hκ t i j)
        (jMN_average_entry_abs_le I m hn hκ i j)
      _ = _ := by simp; ring
  | succ r ih =>
    intro t
    have hp : Function.Periodic (fun u => I.qMNR κ m n r u i j) (4 * tau β I.Λ m) :=
      fun u => congrFun (congrFun (hchar.2.1 r u) i) j
    have hz := (qMNR_periodic_and_period_mean_zero I κ (n := n) hm r).2 i j
    have hb : 0 ≤ 2 * B * (8 * tau β I.Λ m) ^ r := by positivity
    have h := Approx.periodic_primitive_bound hP hb (qMNR_entry_continuous I κ m n r i j)
      hp hz ih t
    change |-(∫ s in (0 : ℝ)..t, I.qMNR κ m n r s i j) +
      ∫ u in (0 : ℝ)..1, ∫ s in (0 : ℝ)..u, I.qMNR κ m n r s i j| ≤ _
    apply h.trans_eq
    rw [pow_succ]
    ring

/-- Corrected `e.qmnr.bounds`: a geometric gain in r, with a constant
uniform in m,n,r after the cutoff constant is bounded. -/
theorem qMNR_entry_paper_bound {β C₀ : ℝ} (I : Ingredients β)
    (hcutoff : I.Czeta ≤ C₀) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    {n : ℕ} (hn : n ≤ Nstar β) (r : ℕ) (t : ℝ) (i j : Fin 2) :
    |I.qMNR κ m n r t i j| ≤ 4 * Real.pi ^ 2 * C₀ *
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
      (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ n * (8 * tau β I.Λ m) ^ r := by
  have hτ := I.tau_pos' m
  have hC : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hC₀ : 0 ≤ C₀ := hC.trans hcutoff
  have hfact : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hf : 2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
      (n.factorial : ℝ) ≤ 2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 :=
    div_le_self (by positivity) hfact
  have hq : epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ) ≤ epsilon β I.Λ m ^ 2 / κ := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) hκ
    have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith
  calc
    _ ≤ 2 * ((2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
        (n.factorial : ℝ) * (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
        (I.Czeta / tau β I.Λ m ^ n)) * (8 * tau β I.Λ m) ^ r :=
      qMNR_entry_abs_le_geometric I hm hκ hn r t i j
    _ ≤ 2 * ((2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        (epsilon β I.Λ m ^ 2 / κ) ^ n) * (C₀ / tau β I.Λ m ^ n)) *
        (8 * tau β I.Λ m) ^ r := by gcongr
    _ = _ := by
      simp only [div_pow, mul_pow]
      ring

/-- Supremum matrix norm version of the corrected geometric bound. -/
theorem qMNR_norm_paper_bound {β C₀ : ℝ} (I : Ingredients β)
    (hcutoff : I.Czeta ≤ C₀) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    {n : ℕ} (hn : n ≤ Nstar β) (r : ℕ) (t : ℝ) :
    ‖I.qMNR κ m n r t‖ ≤ 4 * Real.pi ^ 2 * C₀ *
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
      (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ n * (8 * tau β I.Λ m) ^ r := by
  have hC₀ : 0 ≤ C₀ := by linarith [I.one_le_Czeta, hcutoff]
  have hτ := I.tau_pos' m
  have hB : 0 ≤ 4 * Real.pi ^ 2 * C₀ * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
      (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ n * (8 * tau β I.Λ m) ^ r := by positivity
  apply (pi_norm_le_iff_of_nonneg hB).2
  intro i
  apply (pi_norm_le_iff_of_nonneg hB).2
  intro j
  simpa only [Real.norm_eq_abs] using qMNR_entry_paper_bound I hcutoff hm hκ hn r t i j

/-- Backward Taylor remainder, with an explicit derivative bound.
The extra factor `(N-1)!` is harmless for the fixed cutoff budget. -/
theorem backward_taylor_remainder {f : ℝ → ℝ} {B s t : ℝ} (k : ℕ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hst : s ≤ t)
    (hb : ∀ u, |iteratedDeriv (k + 1) f u| ≤ B) :
    |f s - ∑ j ∈ Finset.range (k + 1),
        ((j.factorial : ℝ)⁻¹ * (s - t) ^ j) * iteratedDeriv j f t| ≤
      B * (t - s) ^ (k + 1) / (k.factorial : ℝ) := by
  classical
  by_cases heq : s = t
  · subst s
    have hsum : (∑ j ∈ Finset.range (k + 1),
        ((j.factorial : ℝ)⁻¹ * (t - t) ^ j) * iteratedDeriv j f t) = f t := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    rw [hsum]
    simp
  have hu : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hst heq)
  let g : ℝ → ℝ := fun x => f (t - x)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (by fun_prop)
  have hwithin : ∀ j x, x ∈ Set.Icc 0 (t - s) →
      iteratedDerivWithin j g (Set.Icc 0 (t - s)) x = iteratedDeriv j g x := by
    intro j x hx
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu)
      (hg.of_le (by simp)).contDiffAt hx
  have hderiv : ∀ j x, iteratedDeriv j g x = (-1 : ℝ) ^ j * iteratedDeriv j f (t - x) := by
    intro j x
    exact congrFun (iteratedDeriv_comp_const_sub (n := j) (f := f) (s := t)) x
  have hbound : ∀ x ∈ Set.Icc 0 (t - s),
      ‖iteratedDerivWithin (k + 1) g (Set.Icc 0 (t - s)) x‖ ≤ B := by
    intro x hx
    rw [hwithin _ _ hx, hderiv, Real.norm_eq_abs, abs_mul, abs_pow]
    simpa using hb (t - x)
  have htaylor : taylorWithinEval g k (Set.Icc 0 (t - s)) 0 (t - s) =
      ∑ j ∈ Finset.range (k + 1),
        ((j.factorial : ℝ)⁻¹ * (s - t) ^ j) * iteratedDeriv j f t := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hwithin j 0 ⟨le_refl 0, hu.le⟩, hderiv]
    simp only [sub_zero, smul_eq_mul]
    rw [show (j.factorial : ℝ)⁻¹ * (t - s) ^ j *
        ((-1 : ℝ) ^ j * iteratedDeriv j f t) =
      (j.factorial : ℝ)⁻¹ * ((t - s) ^ j * (-1 : ℝ) ^ j) * iteratedDeriv j f t by ring,
      ← mul_pow, show (t - s) * (-1 : ℝ) = s - t by ring]
  have h := taylor_mean_remainder_bound (n := k) (a := (0 : ℝ)) (b := t - s)
    (x := t - s) (C := B) hu.le (hg.of_le (by simp)).contDiffOn
    ⟨hu.le, le_refl _⟩ hbound
  rw [htaylor, Real.norm_eq_abs] at h
  simpa [g] using h

theorem Approx.taylor_remainder_exp_bound {f : ℝ → ℝ} {B ρ s t : ℝ} (k : ℕ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hB : 0 ≤ B) (hρ : 0 < ρ) (hst : s ≤ t)
    (hb : ∀ u, |iteratedDeriv (k + 1) f u| ≤ B) :
    |f s - ∑ j ∈ Finset.range (k + 1),
        ((j.factorial : ℝ)⁻¹ * (s - t) ^ j) * iteratedDeriv j f t| * Real.exp (ρ * (s - t)) ≤
      (B * (k + 1 : ℕ) * 2 ^ (k + 1) / ρ ^ (k + 1)) * Real.exp (ρ / 2 * (s - t)) := by
  have hpoly := polynomial_exp_abs_le (k + 1)
    (mul_nonpos_of_nonneg_of_nonpos hρ.le (sub_nonpos.mpr hst))
  rw [abs_mul, abs_pow, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hρ.le
    (sub_nonpos.mpr hst)), abs_of_pos (Real.exp_pos _),
    show -(ρ * (s - t)) = ρ * (t - s) by ring, mul_pow] at hpoly
  have hkernel : (t - s) ^ (k + 1) * Real.exp (ρ * (s - t)) ≤
      ((k + 1).factorial : ℝ) * 2 ^ (k + 1) / ρ ^ (k + 1) *
        Real.exp (ρ / 2 * (s - t)) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hρ (k + 1))).2
    rw [show ρ * (s - t) / 2 = ρ / 2 * (s - t) by ring] at hpoly
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hpoly
  calc
    _ ≤ (B * (t - s) ^ (k + 1) / (k.factorial : ℝ)) * Real.exp (ρ * (s - t)) :=
      mul_le_mul_of_nonneg_right (backward_taylor_remainder k hf hst hb) (Real.exp_nonneg _)
    _ = (B / (k.factorial : ℝ)) * ((t - s) ^ (k + 1) * Real.exp (ρ * (s - t))) := by ring
    _ ≤ (B / (k.factorial : ℝ)) * (((k + 1).factorial : ℝ) * 2 ^ (k + 1) /
        ρ ^ (k + 1) * Real.exp (ρ / 2 * (s - t))) :=
      mul_le_mul_of_nonneg_left hkernel (by positivity)
    _ = _ := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp

/-- Exponentially weighted Taylor remainder on a half-line. The cutoff h
need only be bounded; the integral estimate assumes no integrability premise. -/
theorem taylor_memory_remainder_bound {f h : ℝ → ℝ} {B ρ t : ℝ} (k : ℕ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hb : ∀ u, |iteratedDeriv (k + 1) f u| ≤ B) (hh : ∀ u, |h u| ≤ 1) :
    |∫ s in Set.Iic t, h s * (f s - ∑ j ∈ Finset.range (k + 1),
        ((j.factorial : ℝ)⁻¹ * (s - t) ^ j) * iteratedDeriv j f t) * Real.exp (ρ * (s - t))| ≤
      (B * (k + 1 : ℕ) * 2 ^ (k + 1) / ρ ^ (k + 1)) * (ρ / 2)⁻¹ := by
  let D := B * (k + 1 : ℕ) * 2 ^ (k + 1) / ρ ^ (k + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound : ∀ s ∈ Set.Iic t,
      ‖h s * (f s - ∑ j ∈ Finset.range (k + 1),
        ((j.factorial : ℝ)⁻¹ * (s - t) ^ j) * iteratedDeriv j f t) * Real.exp (ρ * (s - t))‖ ≤
        D * Real.exp (ρ / 2 * (s - t)) := by
    intro s hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ 1 * |f s - ∑ j ∈ Finset.range (k + 1),
          ((j.factorial : ℝ)⁻¹ * (s - t) ^ j) * iteratedDeriv j f t| * Real.exp (ρ * (s - t)) := by
        gcongr
        exact hh s
      _ ≤ _ := by simpa [D] using Approx.taylor_remainder_exp_bound k hf hB hρ hs hb
  have hExp : IntegrableOn (fun s => Real.exp (ρ / 2 * (s - t))) (Set.Iic t) := by
    have heq : (fun s => Real.exp (ρ / 2 * (s - t))) =
        fun s => Real.exp (-ρ / 2 * t) * Real.exp (ρ / 2 * s) := by
      funext s
      rw [show ρ / 2 * (s - t) = -ρ / 2 * t + ρ / 2 * s by ring, Real.exp_add]
    rw [heq]
    exact (integrableOn_exp_mul_Iic (by positivity) t).const_mul _
  have h := norm_integral_le_of_norm_le (hExp.const_mul D)
    (ae_restrict_mem measurableSet_Iic |>.mono (fun s hs => hbound s hs))
  rw [integral_const_mul] at h
  have hExpInt : (∫ s in Set.Iic t, Real.exp (ρ / 2 * (s - t))) = (ρ / 2)⁻¹ := by
    rw [show (fun s => Real.exp (ρ / 2 * (s - t))) =
      fun s => Real.exp (-ρ / 2 * t) * Real.exp (ρ / 2 * s) by
        funext s
        rw [show ρ / 2 * (s - t) = -ρ / 2 * t + ρ / 2 * s by ring, Real.exp_add],
      integral_const_mul, integral_exp_mul_Iic (by positivity) t]
    rw [show Real.exp (-ρ / 2 * t) * (Real.exp (ρ / 2 * t) / (ρ / 2)) =
      (Real.exp (-ρ / 2 * t) * Real.exp (ρ / 2 * t)) / (ρ / 2) by ring,
      ← Real.exp_add, show -ρ / 2 * t + ρ / 2 * t = 0 by ring, Real.exp_zero]
    exact one_div _
  rw [hExpInt] at h
  exact h

/-- The weighted remainder for the small cutoff and a large cutoff.
This is the analytic remainder needed before identifying the flux expansion. -/
theorem zetaMK_memory_remainder_bound {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (k l : ℤ) {N : ℕ} (hN : 1 ≤ N) (hbudget : N ≤ Nstar β)
    {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    |∫ s in Set.Iic t, I.hatZetaML m l s *
      (I.zetaMK m k s - ∑ j ∈ Finset.range N,
        ((j.factorial : ℝ)⁻¹ * (s - t) ^ j) * iteratedDeriv j (I.zetaMK m k) t) *
      Real.exp (ρ * (s - t))| ≤
      ((I.Czeta / tau β I.Λ m ^ N) * N * 2 ^ N / ρ ^ N) * (ρ / 2)⁻¹ := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hf : ContDiff ℝ (⊤ : ℕ∞) (I.zetaMK m k) := by
    unfold Ingredients.zetaMK scaledCutoff
    exact I.zeta_smooth.comp (by fun_prop)
  apply taylor_memory_remainder_bound r hf
    (div_nonneg (by linarith [I.one_le_Czeta]) (pow_nonneg (I.tau_pos' m).le _)) hρ
    (fun u => zetaMK_derivative_abs_le I m k hbudget u)
  intro u
  have hu := hatZetaML_mem_Icc I hm l u
  rw [abs_of_nonneg hu.1]
  exact hu.2

/-- The cutoff memory remainder with the physical decay rate. This controls
one Taylor remainder; it does not by itself identify the flux minus Jhat. -/
theorem zetaMK_physical_memory_remainder_bound {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (k l : ℤ) {N : ℕ}
    (hN : 1 ≤ N) (hbudget : N ≤ Nstar β) (t : ℝ) :
    |∫ s in Set.Iic t, I.hatZetaML m l s *
      (I.zetaMK m k s - ∑ j ∈ Finset.range N,
        ((j.factorial : ℝ)⁻¹ * (s - t) ^ j) * iteratedDeriv j (I.zetaMK m k) t) *
      Real.exp ((4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * (s - t))| ≤
      (2 * I.Czeta * N * 2 ^ N) * (epsilon β I.Λ m ^ 2 / κ) *
        (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ N := by
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  have he : 0 < epsilon β I.Λ m ^ 2 := sq_pos_of_pos (Infra.Cutoff.epsilon_pos I.one_lt_beta
      I.beta_lt I.two_pow_seven_le (m := m))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hτ := I.tau_pos' m
  have hC : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hrate : κ / epsilon β I.Λ m ^ 2 ≤ ρ := by
    dsimp [ρ]
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith
  have hrinv : ρ⁻¹ ≤ epsilon β I.Λ m ^ 2 / κ := by
    calc
      _ ≤ (κ / epsilon β I.Λ m ^ 2)⁻¹ := inv_anti₀ (div_pos hκ he) hrate
      _ = _ := by rw [inv_div]
  have h := zetaMK_memory_remainder_bound I hm k l hN hbudget hρ t
  calc
    _ ≤ ((I.Czeta / tau β I.Λ m ^ N) * N * 2 ^ N / ρ ^ N) * (ρ / 2)⁻¹ := h
    _ = (2 * I.Czeta * N * 2 ^ N / tau β I.Λ m ^ N) * ρ⁻¹ * (ρ⁻¹) ^ N := by
      simp only [div_eq_mul_inv, inv_pow]
      ring
    _ ≤ (2 * I.Czeta * N * 2 ^ N / tau β I.Λ m ^ N) *
        (epsilon β I.Λ m ^ 2 / κ) * (epsilon β I.Λ m ^ 2 / κ) ^ N := by
      gcongr
    _ = _ := by
      simp only [div_pow, mul_pow]
      ring

/-- Coordinate-axis matrix selected by the shear index modulo four. -/
def Approx.shearAxis (k : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (if k % 4 = 1 then !![0, 0; 0, 1] else 0) +
    (if k % 4 = 3 then !![1, 0; 0, 0] else 0)

theorem Approx.other_odd_zero {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {k l : ℤ} (hk : Odd k) (hl : Odd l) (hne : l ≠ k)
    {t : ℝ} (hz : I.zetaMK m k t ≠ 0) : I.zetaMK m l t = 0 := by
  by_contra h
  have h0 := xiMK_eq_zero_of_zetaMK_ne_zero_of_odd_ne I hm hk hl hne t hz
  have h1 := xiMK_eq_one_of_zetaMK_ne_zero I hm l t h
  rw [h0] at h1
  norm_num at h1

theorem Approx.shearAxis_active {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) {k : ℤ} (hk : Odd k) {t : ℝ}
    (hz : I.zetaMK m k t ≠ 0) :
    I.flux κ m t = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t) • Approx.shearAxis k := by
  have hmod : k % 4 = 1 ∨ k % 4 = 3 := by
    obtain ⟨z, hz⟩ := hk
    have := Int.emod_nonneg k (by norm_num : (4 : ℤ) ≠ 0)
    have := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 4)
    omega
  rcases hmod with hk1 | hk3
  · rw [flux_active_one I hm κ k t hk1 hz]
    congr 2
    simp only [Approx.shearAxis, hk1, ↓reduceIte]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.single]
  · rw [flux_active_three I hm κ k t hk3 hz]
    congr 2
    simp only [Approx.shearAxis, hk3, ↓reduceIte]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.single]

/-- The always-valid odd-mode formula for the actual flux.
It applies also near the ends of even nominal time windows. -/
theorem flux_eq_odd_mode_sum {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ t : ℝ) :
    I.flux κ m t = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      ∑' k : {k : ℤ // Odd k},
        (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
          I.zetaProd m k t * I.corrTime κ m k t) •
          ((if (k : ℤ) % 4 = 1 then !![0, 0; 0, 1] else 0) +
            (if (k : ℤ) % 4 = 3 then !![1, 0; 0, 0] else 0)) := by
  classical
  by_cases h : ∃ k : ℤ, Odd k ∧ I.zetaMK m k t ≠ 0
  · obtain ⟨k, hk, hz⟩ := h
    rw [tsum_eq_single ⟨k, hk⟩]
    · exact Approx.shearAxis_active I hm κ hk hz
    · intro l hl
      have hne : l.val ≠ k := fun h => hl (Subtype.ext h)
      have hzero := Approx.other_odd_zero I hm hk l.property hne hz
      simp [Ingredients.zetaProd, hzero]
  · have hz : ∀ k : ℤ, Odd k → I.zetaMK m k t = 0 := by
      intro k hk
      by_contra hne
      exact h ⟨k, hk, hne⟩
    rw [flux_eq_kappa_of_no_odd_active I hm κ t hz]
    have hsum : (∑' k : {k : ℤ // Odd k},
        (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
          I.zetaProd m k t * I.corrTime κ m k t) • Approx.shearAxis k) = 0 := by
      have hterms : (fun k : {k : ℤ // Odd k} =>
          (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
            I.zetaProd m k t * I.corrTime κ m k t) • Approx.shearAxis k) = fun _ => 0 := by
        funext k
        simp only [Ingredients.zetaProd, hz k.val k.property, mul_zero, zero_mul, zero_smul]
      rw [hterms]
      simp only [tsum_zero]
    simpa only [Approx.shearAxis, hsum, add_zero] using
      (congrArg (fun X => κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + X) hsum).symm

theorem Approx.jMN_active {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (n : ℕ) {k : ℤ} (hk : Odd k) {t : ℝ}
    (hz : I.zetaMK m k t ≠ 0) :
    I.jMN κ m n t =
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
        (n.factorial : ℝ) * (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) •
      ((I.zetaMK m k t * iteratedDeriv n (I.zetaMK m k) t) • Approx.shearAxis k) := by
  classical
  unfold Ingredients.jMN
  rw [tsum_eq_single ⟨k, hk⟩]
  · rfl
  · intro l hl
    have hzero := Approx.other_odd_zero I hm hk l.property
      (fun h => hl (Subtype.ext h)) hz
    simp [hzero]

theorem Approx.LMN_active {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (n : ℕ) {k : ℤ} {t : ℝ}
    (hz : I.zetaMK m k t ≠ 0) :
    I.LMN κ m n t = I.hatZetaML m (lIdx β I.Λ m k) t *
      ∫ s in Set.Iic t, I.hatZetaML m (lIdx β I.Λ m k) s *
        (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
        Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t)) := by
  unfold Ingredients.LMN
  apply tsum_eq_single
  intro l hl
  have hzero := Infra.Ingredients.cutoff_overlaps I hm k l hl t
  have hh : I.hatZetaML m l t = 0 := (mul_eq_zero.mp hzero).resolve_right hz
  rw [hh, zero_mul]

theorem Approx.exp_shift_integrable {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    IntegrableOn (fun s => Real.exp (ρ * (s - t))) (Set.Iic t) := by
  have heq : (fun s => Real.exp (ρ * (s - t))) =
      fun s => Real.exp (-ρ * t) * Real.exp (ρ * s) := by
    funext s
    rw [show ρ * (s - t) = -ρ * t + ρ * s by ring, Real.exp_add]
  rw [heq]
  exact (integrableOn_exp_mul_Iic hρ t).const_mul _

theorem Approx.polynomial_memory_integrable {h : ℝ → ℝ} (hc : Continuous h)
    (hh : ∀ s, |h s| ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) (t : ℝ) :
    IntegrableOn (fun s => h s * (s - t) ^ n * Real.exp (ρ * (s - t))) (Set.Iic t) := by
  let D := (n.factorial : ℝ) * 2 ^ n / ρ ^ n
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hg := (Approx.exp_shift_integrable (by positivity : 0 < ρ / 2) t).const_mul D
  apply hg.mono' ((hc.mul ((continuous_id.sub continuous_const).pow n)).mul
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_id.sub continuous_const)))).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
  have hp := polynomial_exp_abs_le n
    (mul_nonpos_of_nonneg_of_nonpos hρ.le (sub_nonpos.mpr hs))
  have heq : |(s - t) ^ n * Real.exp (ρ * (s - t))| ≤
      D * Real.exp (ρ / 2 * (s - t)) := by
    rw [abs_mul, abs_pow, abs_mul, abs_of_pos hρ,
      abs_of_pos (Real.exp_pos _), mul_pow] at hp
    rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    dsimp [D]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hρ n)).2
    rw [show ρ * (s - t) / 2 = ρ / 2 * (s - t) by ring] at hp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hp
  change ‖h s * (s - t) ^ n * Real.exp (ρ * (s - t))‖ ≤ _
  rw [Real.norm_eq_abs, mul_assoc, abs_mul]
  calc
    _ ≤ 1 * |(s - t) ^ n * Real.exp (ρ * (s - t))| :=
      mul_le_mul_of_nonneg_right (hh s) (abs_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using heq

/-- Past-time exponential moment of an enlarged cutoff, of a specified polynomial order. -/
def Approx.cutoffMoment {β : ℝ} (I : Ingredients β) (κ : ℝ) (m : ℕ)
    (l : ℤ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ s in Set.Iic t, I.hatZetaML m l s * (s - t) ^ n *
    Real.exp ((4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * (s - t))

theorem Approx.cutoffMoment_integrable {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (l : ℤ) (n : ℕ) (t : ℝ) :
    IntegrableOn (fun s => I.hatZetaML m l s * (s - t) ^ n *
      Real.exp ((4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * (s - t))) (Set.Iic t) := by
  apply Approx.polynomial_memory_integrable
  · unfold Ingredients.hatZetaML shiftCutoff
    exact (I.hatZeta_smooth m).continuous.comp (continuous_id.sub continuous_const)
  · intro s
    rw [abs_of_nonneg (hatZetaML_mem_Icc I hm l s).1]
    exact (hatZetaML_mem_Icc I hm l s).2
  · have hε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    positivity

theorem Approx.memory_taylor_identity {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (k : ℤ) (N : ℕ) (t : ℝ) :
    I.corrTime κ m k t - ∑ n ∈ Finset.range N,
      ((n.factorial : ℝ)⁻¹ * iteratedDeriv n (I.zetaMK m k) t) *
        Approx.cutoffMoment I κ m (lIdx β I.Λ m k) n t =
    ∫ s in Set.Iic t, I.hatZetaML m (lIdx β I.Λ m k) s *
      (I.zetaMK m k s - ∑ n ∈ Finset.range N,
        ((n.factorial : ℝ)⁻¹ * (s - t) ^ n) * iteratedDeriv n (I.zetaMK m k) t) *
      Real.exp ((4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * (s - t)) := by
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let H := I.hatZetaML m (lIdx β I.Λ m k)
  let term := fun n s => ((n.factorial : ℝ)⁻¹ * iteratedDeriv n (I.zetaMK m k) t) *
    (H s * (s - t) ^ n * Real.exp (ρ * (s - t)))
  have hterm : ∀ n, IntegrableOn (term n) (Set.Iic t) := by
    intro n
    exact (Approx.cutoffMoment_integrable I hm hκ _ n t).const_mul _
  have hforce : IntegrableOn (fun s => H s * I.zetaMK m k s * Real.exp (ρ * (s - t)))
      (Set.Iic t) := by
    have hc := zetaProd_exp_continuous_compactSupport I (m := m) κ k
    have hi := hc.1.integrable_of_hasCompactSupport (μ := volume) hc.2
    have heq : (fun s => H s * I.zetaMK m k s * Real.exp (ρ * (s - t))) =
        fun s => Real.exp (-ρ * t) * (I.zetaProd m k s * Real.exp (ρ * s)) := by
      funext s
      rw [show ρ * (s - t) = -ρ * t + ρ * s by ring, Real.exp_add]
      dsimp [H, Ingredients.zetaProd]
      ring
    rw [heq]
    exact hi.integrableOn.const_mul _
  have heq : (fun s => H s * (I.zetaMK m k s - ∑ n ∈ Finset.range N,
        ((n.factorial : ℝ)⁻¹ * (s - t) ^ n) * iteratedDeriv n (I.zetaMK m k) t) *
        Real.exp (ρ * (s - t))) =
      fun s => H s * I.zetaMK m k s * Real.exp (ρ * (s - t)) -
        ∑ n ∈ Finset.range N, term n s := by
    funext s
    dsimp [term]
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    ring
  change _ = ∫ s in Set.Iic t, H s * _ * Real.exp (ρ * (s - t))
  rw [heq, integral_sub hforce (integrable_finsetSum _ (fun n _ => hterm n)),
    integral_finsetSum _ (fun n _ => hterm n)]
  unfold Ingredients.corrTime Approx.cutoffMoment
  dsimp [term, H, ρ]
  simp_rw [integral_const_mul]
  rfl

theorem Approx.LMN_active_moment {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (n : ℕ) {k : ℤ} {t : ℝ}
    (hz : I.zetaMK m k t ≠ 0) :
    I.LMN κ m n t = I.hatZetaML m (lIdx β I.Λ m k) t *
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) ^ n *
        Approx.cutoffMoment I κ m (lIdx β I.Λ m k) n t := by
  rw [Approx.LMN_active I hm κ n hz]
  unfold Approx.cutoffMoment
  rw [show (fun s => I.hatZetaML m (lIdx β I.Λ m k) s *
      (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
        Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t))) =
      fun s => (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) ^ n *
        (I.hatZetaML m (lIdx β I.Λ m k) s * (s - t) ^ n *
          Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t))) by
    funext s
    rw [show 4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2 =
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * (s - t) by ring, mul_pow]
    ring, integral_const_mul]
  ring

theorem Approx.Jhat_active {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) {k : ℤ} (hk : Odd k) {t : ℝ}
    (hz : I.zetaMK m k t ≠ 0) :
    I.Jhat κ m t = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * (∑ n ∈ Finset.range (Nstar β),
          ((n.factorial : ℝ)⁻¹ * iteratedDeriv n (I.zetaMK m k) t) *
            Approx.cutoffMoment I κ m (lIdx β I.Λ m k) n t)) • Approx.shearAxis k := by
  classical
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  ext i j
  unfold Ingredients.Jhat
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [Approx.jMN_active I hm κ n hk hz, Approx.LMN_active_moment I hm κ n hz]
  simp only [Matrix.smul_apply, smul_eq_mul, Ingredients.zetaProd]
  have hr : (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n *
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) ^ n = 1 := by
    rw [← mul_pow]
    have hbase : epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ) *
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) = 1 := by
      field_simp
    rw [hbase, one_pow]
  calc
    _ = (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        (I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t) *
        (((n.factorial : ℝ)⁻¹ * iteratedDeriv n (I.zetaMK m k) t) *
          Approx.cutoffMoment I κ m (lIdx β I.Λ m k) n t) * Approx.shearAxis k i j) *
        ((epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n *
          (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) ^ n) := by ring
    _ = _ := by rw [hr, mul_one]

theorem Approx.flux_sub_Jhat_active {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) {k : ℤ} (hk : Odd k) {t : ℝ}
    (hz : I.zetaMK m k t ≠ 0) :
    I.flux κ m t - I.Jhat κ m t =
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * (∫ s in Set.Iic t,
          I.hatZetaML m (lIdx β I.Λ m k) s *
            (I.zetaMK m k s - ∑ n ∈ Finset.range (Nstar β),
              ((n.factorial : ℝ)⁻¹ * (s - t) ^ n) * iteratedDeriv n (I.zetaMK m k) t) *
            Real.exp ((4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * (s - t)))) •
        Approx.shearAxis k := by
  rw [Approx.shearAxis_active I hm κ hk hz, Approx.Jhat_active I hm hκ hk hz,
    add_sub_add_left_eq_sub, ← sub_smul, ← mul_sub,
    Approx.memory_taylor_identity I hm hκ k (Nstar β) t]

theorem Approx.shearAxis_entry_abs_le (k : ℤ) (i j : Fin 2) :
    |Approx.shearAxis k i j| ≤ 1 := by
  by_cases h1 : k % 4 = 1
  · simp only [Approx.shearAxis, h1, ↓reduceIte]
    fin_cases i <;> fin_cases j <;> norm_num
  · by_cases h3 : k % 4 = 3
    · simp only [Approx.shearAxis, h3, ↓reduceIte]
      fin_cases i <;> fin_cases j <;> norm_num
    · simp only [Approx.shearAxis, h1, h3, ↓reduceIte, add_zero, Matrix.zero_apply, abs_zero]
      norm_num

theorem Approx.Jhat_eq_kappa_of_no_odd_active {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m : ℕ) (t : ℝ) (hz : ∀ k : ℤ, Odd k → I.zetaMK m k t = 0) :
    I.Jhat κ m t = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  classical
  have hj : ∀ n, I.jMN κ m n t = 0 := by
    intro n
    unfold Ingredients.jMN
    have hterms : (fun k : {k : ℤ // Odd k} =>
      (I.zetaMK m k t * iteratedDeriv n (I.zetaMK m k) t) • Approx.shearAxis k) =
        fun _ => 0 := by
      funext k
      rw [hz k.val k.property, zero_mul, zero_smul]
    change _ • (∑' k : {k : ℤ // Odd k},
      (I.zetaMK m k t * iteratedDeriv n (I.zetaMK m k) t) • Approx.shearAxis k) = 0
    rw [hterms, tsum_zero, smul_zero]
  simp only [Ingredients.Jhat, hj, smul_zero, Finset.sum_const_zero, add_zero]

/-- Entrywise `e.JJhat` for the actual flux and Jhat. -/
theorem flux_sub_Jhat_entry_abs_le {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (t : ℝ) (i j : Fin 2) :
    |(I.flux κ m t - I.Jhat κ m t) i j| ≤
      (4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
        (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β := by
  classical
  have hC : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hτ := I.tau_pos' m
  by_cases h : ∃ k : ℤ, Odd k ∧ I.zetaMK m k t ≠ 0
  · obtain ⟨k, hk, hz⟩ := h
    have hN : 1 ≤ Nstar β := by
      have := Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
      omega
    have hR := zetaMK_physical_memory_remainder_bound I hm hκ k
      (lIdx β I.Λ m k) hN (le_refl (Nstar β)) t
    rw [Approx.flux_sub_Jhat_active I hm hκ hk hz, Matrix.smul_apply, smul_eq_mul,
      abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (by positivity)
        (zetaProd_mem_Icc I hm k t).1)]
    calc
      _ ≤ (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 * 1) *
          ((2 * I.Czeta * Nstar β * 2 ^ Nstar β) * (epsilon β I.Λ m ^ 2 / κ) *
            (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β) * 1 := by
        gcongr
        · exact (zetaProd_mem_Icc I hm k t).2
        · exact Approx.shearAxis_entry_abs_le k i j
      _ = _ := by ring
  · have hz : ∀ k : ℤ, Odd k → I.zetaMK m k t = 0 := by
      intro k hk
      by_contra hne
      exact h ⟨k, hk, hne⟩
    rw [flux_eq_kappa_of_no_odd_active I hm κ t hz,
      Approx.Jhat_eq_kappa_of_no_odd_active I κ m t hz, sub_self, Matrix.zero_apply, abs_zero]
    positivity

/-- `e.JJhat`, in the elementwise supremum matrix norm, with an explicit
constant depending only on the cutoff constant and the fixed Taylor budget. -/
theorem flux_sub_Jhat_norm_le {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (t : ℝ) :
    ‖I.flux κ m t - I.Jhat κ m t‖ ≤
      (4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
        (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β := by
  have hC : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hτ := I.tau_pos' m
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  simpa only [Real.norm_eq_abs] using flux_sub_Jhat_entry_abs_le I hm hκ t i j

theorem Approx.halfline_translate (t T : ℝ) (f : ℝ → ℝ) :
    (∫ s in Set.Iic (t + T), f s) = ∫ s in Set.Iic t, f (s + T) := by
  have h := (measurePreserving_add_right volume T).setIntegral_preimage_emb
    (MeasurableEquiv.addRight T).measurableEmbedding f (Set.Iic (t + T))
  have hset : (fun s : ℝ => s + T) ⁻¹' Set.Iic (t + T) = Set.Iic t := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Iic, add_le_add_iff_right]
  rw [hset] at h
  exact h.symm

/-- The large memory coefficient has its actual large-cell period. -/
theorem LMN_periodic {β : ℝ} (I : Ingredients β) (κ : ℝ) (m n : ℕ) :
    Function.Periodic (I.LMN κ m n) (tauPP β I.Λ m) := by
  intro t
  let T := tauPP β I.Λ m
  have hhat (l : ℤ) (s : ℝ) : I.hatZetaML m (l + 1) (s + T) = I.hatZetaML m l s := by
    unfold Ingredients.hatZetaML shiftCutoff
    congr 1
    push_cast
    dsimp [T]
    ring
  unfold Ingredients.LMN
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
  apply tsum_congr
  intro l
  change I.hatZetaML m (l + 1) (t + T) * _ = I.hatZetaML m l t * _
  rw [hhat, Approx.halfline_translate t T]
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro s _
  change I.hatZetaML m (l + 1) (s + T) *
      (4 * Real.pi ^ 2 * κ * (s + T - (t + T)) / epsilon β I.Λ m ^ 2) ^ n *
      Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s + T - (t + T))) = _
  rw [hhat, show s + T - (t + T) = s - t by ring]

theorem Approx.periodic_iteratedDeriv {f : ℝ → ℝ} {P : ℝ}
    (hp : Function.Periodic f P) (r : ℕ) : Function.Periodic (iteratedDeriv r f) P := by
  have hfun : (fun s => f (s + P)) = f := funext hp
  intro t
  have h := congrFun (iteratedDeriv_comp_add_const (n := r) (f := f) (s := P)) t
  rw [hfun] at h
  exact h.symm

theorem Approx.LMN_unit_periodic {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (n : ℕ) : Function.Periodic (I.LMN κ m n) 1 := by
  obtain ⟨k, hk⟩ := Infra.Ingredients.tauPP_reciprocal_multiple_four
    I.one_lt_beta I.beta_lt I.two_pow_seven_le hm
  have hT := I.tauPP_pos' m
  have hmul : ((4 * k : ℕ) : ℝ) * tauPP β I.Λ m = 1 := by
    have heq : 1 / tauPP β I.Λ m = ((4 * k : ℕ) : ℝ) := by exact_mod_cast hk
    exact ((div_eq_iff hT.ne').mp heq).symm
  have h := (LMN_periodic I κ m n).nat_mul (4 * k)
  simpa only [hmul] using h

theorem Approx.qMNR_unit_periodic {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (n r : ℕ) (i j : Fin 2) :
    Function.Periodic (fun t => I.qMNR κ m n r t i j) 1 := by
  obtain ⟨k, hk⟩ := four_tau_reciprocal_nat I hm
  have hp := (qMNR_periodic I κ (n := n) hm r).nat_mul k
  rw [hk] at hp
  exact fun t => congrFun (congrFun (hp t) i) j

theorem Approx.periodic_primitive_pairing {f : ℝ → ℝ} {q : ℕ → ℝ → ℝ} (N : ℕ)
    (hf : ContDiff ℝ (N : ℕ∞) f) (hp : Function.Periodic f 1)
    (hq : ∀ r, Continuous (q r)) (hqp : ∀ r, Function.Periodic (q r) 1)
    (hqd : ∀ r t, HasDerivAt (q (r + 1)) (-q r t) t) :
    (∫ t in (0 : ℝ)..1, f t * q 0 t) =
      ∫ t in (0 : ℝ)..1, iteratedDeriv N f t * q N t := by
  have hstep : ∀ r < N,
      (∫ t in (0 : ℝ)..1, iteratedDeriv r f t * q r t) =
        ∫ t in (0 : ℝ)..1, iteratedDeriv (r + 1) f t * q (r + 1) t := by
    intro r hr
    have hfc := hf.continuous_iteratedDeriv r (by exact_mod_cast hr.le)
    have hfd := hf.differentiable_iteratedDeriv r (by exact_mod_cast hr)
    have hnext := hf.continuous_iteratedDeriv (r + 1) (by exact_mod_cast Nat.succ_le_of_lt hr)
    have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hfc.continuousOn (hq (r + 1)).continuousOn
      (fun t _ => by simpa only [iteratedDeriv_succ] using (hfd t).hasDerivAt)
      (fun t _ => hqd r t) (hnext.intervalIntegrable 0 1)
      ((hq r).neg.intervalIntegrable 0 1)
    have hfp := Approx.periodic_iteratedDeriv hp r 0
    have hqq := hqp (r + 1) 0
    simp only [zero_add] at hfp hqq
    rw [hfp, hqq, sub_self, zero_sub] at hi
    simp only [mul_neg, intervalIntegral.integral_neg] at hi
    exact neg_injective hi
  have hchain : ∀ r ≤ N,
      (∫ t in (0 : ℝ)..1, f t * q 0 t) =
        ∫ t in (0 : ℝ)..1, iteratedDeriv r f t * q r t := by
    intro r
    induction r with
    | zero => intro _; simp only [iteratedDeriv_zero]
    | succ r ih =>
      intro hr
      exact (ih (by omega)).trans (hstep r (by omega))
  exact hchain N le_rfl

/-- Finite-regularity averaging of an actual jMN oscillation against LMN.
The small factor is the ratio of the two cutoff time scales. -/
theorem LMN_jMN_covariance_abs_le {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m / 2)
    {n : ℕ} (hn : n ≤ Nstar β) (i j : Fin 2) :
    |∫ t in (0 : ℝ)..1, I.LMN κ m n t *
      (I.jMN κ m n t i j - timeAvgMat (I.jMN κ m n) i j)| ≤
      (2 * I.Czeta * ((Nstar β).factorial : ℝ) *
        2 ^ Nstar β * 2 ^ Nstar β * I.Chat ^ 2 * 8 ^ Nstar β) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
        (tau β I.Λ m / tauP β I.Λ m) ^ Nstar β := by
  let N := Nstar β
  have hτ := I.tau_pos' m
  have hτP := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hC : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hH : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  have hR : epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos hκ hτ)).2
    linarith only [hcondition, (mul_pos hκ hτ)]
  have hqbound (t : ℝ) : |I.qMNR κ m n N t i j| ≤
      4 * Real.pi ^ 2 * I.Czeta * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
        (8 * tau β I.Λ m) ^ N := by
    have h := qMNR_entry_paper_bound I le_rfl hm hκ hn N t i j
    calc
      _ ≤ 4 * Real.pi ^ 2 * I.Czeta * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ n *
          (8 * tau β I.Λ m) ^ N := h
      _ ≤ _ := by
        have hp := pow_le_one₀ (n := n) (by positivity : 0 ≤ epsilon β I.Λ m ^ 2 /
          (κ * tau β I.Λ m)) hR
        calc
          _ ≤ 4 * Real.pi ^ 2 * I.Czeta * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
              1 * (8 * tau β I.Λ m) ^ N := by gcongr
          _ = _ := by ring
  have hpair := Approx.periodic_primitive_pairing N (LMN_contDiff I hm hκ n)
    (Approx.LMN_unit_periodic I hm κ n)
    (fun r => qMNR_entry_continuous I κ m n r i j)
    (fun r => Approx.qMNR_unit_periodic I hm κ n r i j)
    (fun r t => qMNR_hasDerivAt I κ m n r t i j)
  change (∫ t in (0 : ℝ)..1, I.LMN κ m n t * I.qMNR κ m n 0 t i j) = _ at hpair
  rw [show (fun t => I.LMN κ m n t *
      (I.jMN κ m n t i j - timeAvgMat (I.jMN κ m n) i j)) =
      (fun t => I.LMN κ m n t * I.qMNR κ m n 0 t i j) by
        funext t; rfl, hpair]
  have hb (t : ℝ) : |iteratedDeriv N (I.LMN κ m n) t * I.qMNR κ m n N t i j| ≤
      ((((N.factorial : ℝ) * 2 ^ N * 2 ^ N * I.Chat ^ 2 / (2 * Real.pi ^ 2)) *
        (epsilon β I.Λ m ^ 2 / κ) / tauP β I.Λ m ^ N) *
        (4 * Real.pi ^ 2 * I.Czeta * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
          (8 * tau β I.Λ m) ^ N)) := by
    rw [abs_mul]
    exact mul_le_mul (LMN_derivative_paper_bound I le_rfl hm hκ hn le_rfl t)
      (hqbound t) (abs_nonneg _) (by positivity)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (f := fun t => iteratedDeriv N (I.LMN κ m n) t * I.qMNR κ m n N t i j)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hb t)
  simp only [Real.norm_eq_abs, sub_zero, abs_one] at hint
  calc
    _ ≤ _ := hint
    _ = _ := by
      dsimp [N]
      simp only [div_pow, mul_pow]
      field_simp
      ring

theorem Approx.Jhat_entry_continuous {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (i j : Fin 2) :
    Continuous (fun t => I.Jhat κ m t i j) := by
  unfold Ingredients.Jhat
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply continuous_const.add
  apply continuous_finsetSum
  intro n _
  exact (LMN_contDiff I hm hκ n).continuous.mul
    ((continuous_apply j).comp ((continuous_apply i).comp (jMN_continuous I m n κ)))

theorem Approx.Kmat_entry_continuous {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (i j : Fin 2) :
    Continuous (fun t => I.Kmat κ m t i j) := by
  unfold Ingredients.Kmat
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply continuous_const.add
  apply continuous_finsetSum
  intro n _
  exact (LMN_contDiff I hm hκ n).continuous.mul continuous_const

theorem Approx.timeAvgMat_sub_entry_eq_integral {F G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (i j : Fin 2) (hf : Continuous (fun t => F t i j))
    (hg : Continuous (fun t => G t i j)) :
    (timeAvgMat F - timeAvgMat G) i j = ∫ t in (0 : ℝ)..1, (F t - G t) i j := by
  simp only [timeAvgMat, Matrix.sub_apply, Matrix.of_apply]
  exact (intervalIntegral.integral_sub (hf.intervalIntegrable 0 1)
    (hg.intervalIntegrable 0 1)).symm

/-- Averaging preserves the proved flux approximation error. -/
theorem Jhat_average_sub_Khom_norm_le {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) :
    ‖timeAvgMat (I.Jhat κ m) - I.Khom κ m‖ ≤
      (4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
        (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β := by
  have hC : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hτ := I.tau_pos' m
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  unfold Ingredients.Khom
  rw [Approx.timeAvgMat_sub_entry_eq_integral i j (Approx.Jhat_entry_continuous I hm hκ i j)
    (flux_entry_time_continuous I hm κ i j)]
  have hb (t : ℝ) := flux_sub_Jhat_entry_abs_le I hm hκ t i j
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun t => (I.Jhat κ m t - I.flux κ m t) i j)
    (fun t _ => by
      rw [Real.norm_eq_abs, Matrix.sub_apply, abs_sub_comm]
      simpa only [Matrix.sub_apply] using hb t)
  simpa only [sub_zero, abs_one, mul_one] using hint

/-- The oscillatory part of Jhat contributes a finite-regularity averaging
error, with the actual time-scale ratio rather than an assumed analytic rate. -/
theorem Kmat_average_sub_Jhat_entry_abs_le {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m / 2) (i j : Fin 2) :
    |(timeAvgMat (I.Kmat κ m) - timeAvgMat (I.Jhat κ m)) i j| ≤
      (2 * Nstar β * I.Czeta * ((Nstar β).factorial : ℝ) *
        2 ^ Nstar β * 2 ^ Nstar β * I.Chat ^ 2 * 8 ^ Nstar β) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
        (tau β I.Λ m / tauP β I.Λ m) ^ Nstar β := by
  classical
  rw [Approx.timeAvgMat_sub_entry_eq_integral i j (Approx.Kmat_entry_continuous I hm hκ i j)
    (Approx.Jhat_entry_continuous I hm hκ i j)]
  let F := fun n t => I.LMN κ m n t *
    (I.jMN κ m n t i j - timeAvgMat (I.jMN κ m n) i j)
  have hc (n : ℕ) : Continuous (F n) :=
    (LMN_contDiff I hm hκ n).continuous.mul
      (((continuous_apply j).comp ((continuous_apply i).comp (jMN_continuous I m n κ))).sub
          continuous_const)
  have heq : (fun t => (I.Kmat κ m t - I.Jhat κ m t) i j) =
      fun t => -(∑ n ∈ Finset.range (Nstar β), F n t) := by
    funext t
    unfold Ingredients.Kmat Ingredients.Jhat
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    dsimp [F]
    congr 1
    funext n
    ring
  rw [heq, intervalIntegral.integral_neg,
    intervalIntegral.integral_finsetSum (fun n _ => (hc n).intervalIntegrable 0 1), abs_neg]
  calc
    _ ≤ ∑ n ∈ Finset.range (Nstar β), |∫ t in (0 : ℝ)..1, F n t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (Nstar β),
        (2 * I.Czeta * ((Nstar β).factorial : ℝ) *
          2 ^ Nstar β * 2 ^ Nstar β * I.Chat ^ 2 * 8 ^ Nstar β) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (tau β I.Λ m / tauP β I.Λ m) ^ Nstar β := by
      apply Finset.sum_le_sum
      intro n hn
      exact LMN_jMN_covariance_abs_le I hm hκ hcondition
        (Finset.mem_range.mp hn).le i j
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- A finite-regularity version of the average comparison, retaining both
justified errors. No analytic averaging premise is silently added. -/
theorem Kmat_average_sub_Khom_norm_le_finite {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m / 2) :
    ‖timeAvgMat (I.Kmat κ m) - I.Khom κ m‖ ≤
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
      ((4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β +
        (2 * Nstar β * I.Czeta * ((Nstar β).factorial : ℝ) *
          2 ^ Nstar β * 2 ^ Nstar β * I.Chat ^ 2 * 8 ^ Nstar β) *
          (tau β I.Λ m / tauP β I.Λ m) ^ Nstar β) := by
  have hC : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hH : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  have hτ := I.tau_pos' m
  have hτP := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hnorm := Jhat_average_sub_Khom_norm_le I hm hκ
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  have hb := Kmat_average_sub_Jhat_entry_abs_le I hm hκ hcondition i j
  have hj : |(timeAvgMat (I.Jhat κ m) - I.Khom κ m) i j| ≤
      (4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
        (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β := by
    exact (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans hnorm)
  rw [Real.norm_eq_abs, Matrix.sub_apply]
  have htri := abs_sub_le (timeAvgMat (I.Kmat κ m) i j)
    (timeAvgMat (I.Jhat κ m) i j) (I.Khom κ m i j)
  simp only [Matrix.sub_apply] at hb hj
  calc
    _ ≤ |timeAvgMat (I.Kmat κ m) i j - timeAvgMat (I.Jhat κ m) i j| +
        |timeAvgMat (I.Jhat κ m) i j - I.Khom κ m i j| := htri
    _ ≤ _ := add_le_add hb hj
    _ = _ := by ring

end AVenhance.Infra.Section3
