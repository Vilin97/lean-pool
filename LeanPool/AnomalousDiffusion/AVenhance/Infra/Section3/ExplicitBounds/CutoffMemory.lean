/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.JMNRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.DerivativeBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.JHat
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.Integral

/-! Explicit cutoff factors in the Section 3 coefficient estimates.

The cutoff derivative budget is `Nstar β`; derivative estimates of a product
containing `∂ⁿζ` therefore require `n + ℓ ≤ Nstar β`. Constants are displayed
rather than hidden in a β-dependent `C`. The memory integrals are differentiated
on a fixed half-line after translation, with an integrable exponential
majorant for every derivative. The matrix estimates include order zero and
all orders through `Nstar β`; the physical diffusivity comparison is conditional
on the internal-index κ bounds from the diffusivity-recursion estimates.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section3
open AVenhance

/-- The cutoff bound after rescaling to the small time scale. -/
theorem zetaMK_scaled_derivative_bound {β : ℝ} (I : Ingredients β)
    (m : ℕ) (k : ℤ) {j : ℕ} (hj : j ≤ Nstar β) (t : ℝ) :
    tau β I.Λ m ^ j * |iteratedDeriv j (I.zetaMK m k) t| ≤ I.Czeta := by
  have hτ := I.tau_pos' m
  have hfun : I.zetaMK m k =
      fun t => I.zeta (t / tau β I.Λ m - (k : ℝ)) := by
    funext t
    simp only [Ingredients.zetaMK, scaledCutoff]
    congr 1
    field_simp
  rw [hfun]
  exact Infra.Cutoff.scaled_translate_iteratedDeriv_bound
    I.zeta_smooth I.zeta_deriv_le hτ hj

/-- Unweighted form of the rescaled cutoff estimate. -/
theorem zetaMK_derivative_abs_le {β : ℝ} (I : Ingredients β)
    (m : ℕ) (k : ℤ) {j : ℕ} (hj : j ≤ Nstar β) (t : ℝ) :
    |iteratedDeriv j (I.zetaMK m k) t| ≤ I.Czeta / tau β I.Λ m ^ j := by
  apply (le_div_iff₀ (pow_pos (I.tau_pos' m) j)).2
  simpa [mul_comm] using zetaMK_scaled_derivative_bound I m k hj t

/-- The large-scale bound is already part of the ingredients. -/
theorem hatZetaML_derivative_abs_le {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) {j : ℕ} (hj : j ≤ Nstar β) (t : ℝ) :
    |iteratedDeriv j (I.hatZetaML m l) t| ≤ I.Chat / tauP β I.Λ m ^ j := by
  apply (le_div_iff₀ (pow_pos (Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le) j)).2
  simpa [Ingredients.hatZetaML, mul_comm] using I.hatZeta_deriv_le m hm l j hj t

theorem CutoffMemory.zetaMK_smooth {β : ℝ} (I : Ingredients β) (m : ℕ) (k : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (I.zetaMK m k) := by
  unfold Ingredients.zetaMK scaledCutoff
  exact I.zeta_smooth.comp (by fun_prop)

theorem CutoffMemory.iteratedDeriv_iteratedDeriv (f : ℝ → ℝ) (i n : ℕ) :
    iteratedDeriv i (iteratedDeriv n f) = iteratedDeriv (i + n) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

/-- Diagonal coordinate projector associated with a shear mode. -/
def CutoffMemory.modeMatrix (k : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (if k % 4 = 1 then !![0, 0; 0, 1] else 0) +
    (if k % 4 = 3 then !![1, 0; 0, 0] else 0)

theorem CutoffMemory.modeMatrix_entry_abs_le (k : ℤ) (i j : Fin 2) :
    |CutoffMemory.modeMatrix k i j| ≤ 1 := by
  by_cases h1 : k % 4 = 1
  · have h3 : k % 4 ≠ 3 := by omega
    fin_cases i <;> fin_cases j <;> norm_num [CutoffMemory.modeMatrix, h1, h3]
  · by_cases h3 : k % 4 = 3
    · fin_cases i <;> fin_cases j <;> norm_num [CutoffMemory.modeMatrix, h1, h3]
    · simp [CutoffMemory.modeMatrix, h1, h3]

theorem CutoffMemory.zetaMK_partition {β : ℝ} (I : Ingredients β) (m : ℕ) (t : ℝ) :
    ∑' k : ℤ, I.zetaMK m k t = 1 := by
  convert I.zeta_partition (t / tau β I.Λ m) using 1
  congr 1
  funext k
  unfold Ingredients.zetaMK scaledCutoff
  congr 1
  field_simp [(I.tau_pos' m).ne']

/-- Entrywise version of `e.jmn.bound`, with an explicit constant and no
hidden cutoff normalization. This is the printed (zeroth derivative) bound. -/
theorem jMN_entry_abs_le {β : ℝ} (I : Ingredients β) (m : ℕ)
    {n : ℕ} (hn : n ≤ Nstar β) {κ : ℝ} (hκ : 0 < κ)
    (t : ℝ) (i j : Fin 2) :
    |I.jMN κ m n t i j| ≤
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
        (n.factorial : ℝ) *
        (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
        (I.Czeta / tau β I.Λ m ^ n) := by
  classical
  let S : Finset {k : ℤ // Odd k} :=
    ((I.zetaMK_support_finite m t).preimage (fun _ _ _ _ h => Subtype.ext h)).toFinset
  let c := 2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
      (n.factorial : ℝ) * (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hB : 0 ≤ I.Czeta / tau β I.Λ m ^ n := by
    exact div_nonneg (by linarith [I.one_le_Czeta]) (pow_nonneg (I.tau_pos' m).le _)
  have hsum : (∑' k : {k : ℤ // Odd k},
      (I.zetaMK m k t * iteratedDeriv n (I.zetaMK m k) t) • CutoffMemory.modeMatrix k) =
      ∑ k ∈ S, (I.zetaMK m k t * iteratedDeriv n (I.zetaMK m k) t) •
        CutoffMemory.modeMatrix k := by
    apply tsum_eq_sum
    intro k hk
    have hz : I.zetaMK m k t = 0 := by
      by_contra hne
      apply hk
      exact (Set.Finite.mem_toFinset _).2 hne
    simp [hz]
  have hzsum : (∑ k ∈ S, I.zetaMK m k t) ≤ 1 := by
    have hint : Summable (fun k : ℤ => I.zetaMK m k t) :=
      summable_of_hasFiniteSupport (I.zetaMK_support_finite m t)
    have hle := hint.sum_le_tsum (S.image Subtype.val)
      (fun k _ => (zetaMK_mem_Icc I k t).1)
    rw [CutoffMemory.zetaMK_partition] at hle
    rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)] at hle
    exact hle
  have hentry : I.jMN κ m n t i j = c *
      ∑ k ∈ S, I.zetaMK m k t * iteratedDeriv n (I.zetaMK m k) t *
        CutoffMemory.modeMatrix k i j := by
    unfold Ingredients.jMN
    change (c • (∑' k : {k : ℤ // Odd k},
      (I.zetaMK m k t * iteratedDeriv n (I.zetaMK m k) t) • CutoffMemory.modeMatrix k)) i j = _
    rw [hsum]
    simp only [Matrix.smul_apply, smul_eq_mul]
    congr 1
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rfl
  rw [hentry, abs_mul, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  calc
    |∑ k ∈ S, I.zetaMK m k t * iteratedDeriv n (I.zetaMK m k) t *
        CutoffMemory.modeMatrix k i j| ≤
      ∑ k ∈ S, |I.zetaMK m k t * iteratedDeriv n (I.zetaMK m k) t *
        CutoffMemory.modeMatrix k i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ S, I.zetaMK m k t * (I.Czeta / tau β I.Λ m ^ n) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_mul, abs_of_nonneg (zetaMK_mem_Icc I k t).1]
      calc
        I.zetaMK m k t * |iteratedDeriv n (I.zetaMK m k) t| *
            |CutoffMemory.modeMatrix k i j| ≤
          (I.zetaMK m k t * (I.Czeta / tau β I.Λ m ^ n)) * 1 := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left
                (zetaMK_derivative_abs_le I m k hn t) (zetaMK_mem_Icc I k t).1
            · exact CutoffMemory.modeMatrix_entry_abs_le k i j
            · exact abs_nonneg _
            · exact mul_nonneg (zetaMK_mem_Icc I k t).1 hB
        _ = _ := mul_one _
    _ ≤ I.Czeta / tau β I.Λ m ^ n := by
      rw [← Finset.sum_mul]
      simpa using mul_le_mul_of_nonneg_right hzsum hB

theorem CutoffMemory.iteratedDeriv_congr_nhds {f g : ℝ → ℝ} {t : ℝ}
    (h : f =ᶠ[nhds t] g) (ℓ : ℕ) : iteratedDeriv ℓ f t = iteratedDeriv ℓ g t := by
  have he : ∀ ℓ, iteratedDeriv ℓ f =ᶠ[nhds t] iteratedDeriv ℓ g := by
    intro ℓ
    induction ℓ with
    | zero => simpa only [iteratedDeriv_zero] using h
    | succ ℓ ih => simpa only [iteratedDeriv_succ] using ih.deriv
  exact (he ℓ).eq_of_nhds

theorem CutoffMemory.odd_mode_cutoffs_locally_single {β : ℝ} (I : Ingredients β)
    (m : ℕ) (t : ℝ) : ∃ k : ℤ, ∃ hk : Odd k,
      ∀ᶠ s in nhds t, ∀ k' : {k : ℤ // Odd k},
        k' ≠ ⟨k, hk⟩ → I.zetaMK m k' s = 0 := by
  classical
  let τ := tau β I.Λ m
  have hτ : 0 < τ := I.tau_pos' m
  let z : ℤ := ⌊t / τ / 2⌋
  let k : ℤ := 2 * z + 1
  have hk : Odd k := ⟨z, by dsimp [k]⟩
  have htlo : ((k : ℝ) - 1) * τ ≤ t := by
    have h := Int.floor_le (t / τ / 2)
    change (z : ℝ) ≤ t / τ / 2 at h
    have h' : 2 * (z : ℝ) ≤ t / τ := by linarith
    have := (le_div_iff₀ hτ).mp h'
    dsimp [k]
    push_cast
    nlinarith
  have hthi : t < ((k : ℝ) + 1) * τ := by
    have h := Int.lt_floor_add_one (t / τ / 2)
    change t / τ / 2 < (z : ℝ) + 1 at h
    have h' : t / τ < 2 * (z : ℝ) + 2 := by linarith
    have := (div_lt_iff₀ hτ).mp h'
    dsimp [k]
    push_cast
    nlinarith
  refine ⟨k, hk, ?_⟩
  filter_upwards [Ioo_mem_nhds (by linarith : t - τ / 6 < t)
    (by linarith : t < t + τ / 6)] with s hs
  intro k' hne
  have hne' : k'.val ≠ k := by intro h; exact hne (Subtype.ext h)
  obtain ⟨z', hz'⟩ := k'.property
  have hsep : k'.val ≤ k - 2 ∨ k + 2 ≤ k'.val := by
    change k'.val ≤ (2 * z + 1) - 2 ∨ (2 * z + 1) + 2 ≤ k'.val
    change k'.val ≠ 2 * z + 1 at hne'
    omega
  have hnot : (s - (k' : ℝ) * τ) / τ ∉ Set.Icc (-(2 / 3 : ℝ)) (2 / 3) := by
    intro hmem
    have hlow := (le_div_iff₀ hτ).mp hmem.1
    have hhigh := (div_le_iff₀ hτ).mp hmem.2
    rcases hsep with hlo | hhi
    · have hlo' : (k' : ℝ) ≤ (k : ℝ) - 2 := by exact_mod_cast hlo
      nlinarith [hs.1, mul_le_mul_of_nonneg_right hlo' hτ.le]
    · have hhi' : (k : ℝ) + 2 ≤ (k' : ℝ) := by exact_mod_cast hhi
      nlinarith [hs.2, mul_le_mul_of_nonneg_right hhi' hτ.le]
  have hle := I.zeta_le_ind ((s - (k' : ℝ) * τ) / τ)
  rw [indIcc_eq_zero_of_not_mem hnot] at hle
  exact le_antisymm hle (I.zeta_nonneg _)

/-- An odd mode can be chosen so that all other odd cutoffs vanish on a
neighborhood of the given time. The gap between odd supports is essential. -/
theorem CutoffMemory.jMN_locally_single_mode {β : ℝ} (I : Ingredients β)
    (m n : ℕ) (κ t : ℝ) (i j : Fin 2) :
    ∃ k : ℤ, Odd k ∧ (fun s => I.jMN κ m n s i j) =ᶠ[nhds t]
      (fun s =>
        (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
          (n.factorial : ℝ) * (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
        (I.zetaMK m k s * iteratedDeriv n (I.zetaMK m k) s) * CutoffMemory.modeMatrix k i j) := by
  classical
  obtain ⟨k, hk, hzero⟩ := CutoffMemory.odd_mode_cutoffs_locally_single I m t
  refine ⟨k, hk, ?_⟩
  filter_upwards [hzero] with s hzero
  have hsum : (∑' k' : {k : ℤ // Odd k},
      (I.zetaMK m k' s * iteratedDeriv n (I.zetaMK m k') s) • CutoffMemory.modeMatrix k') =
      (I.zetaMK m k s * iteratedDeriv n (I.zetaMK m k) s) • CutoffMemory.modeMatrix k := by
    refine tsum_eq_single (f := fun k' : {k : ℤ // Odd k} =>
      (I.zetaMK m k' s * iteratedDeriv n (I.zetaMK m k') s) •
        CutoffMemory.modeMatrix k') ⟨k, hk⟩ ?_
    intro k' hne
    simp [hzero k' hne]
  unfold Ingredients.jMN
  change (_ • (∑' k' : {k : ℤ // Odd k},
    (I.zetaMK m k' s * iteratedDeriv n (I.zetaMK m k') s) • CutoffMemory.modeMatrix k')) i j = _
  rw [hsum]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- A convenient exponential majorant for every polynomial memory kernel.
The factor two sacrifices sharpness and avoids an improper gamma integral. -/
theorem polynomial_exp_abs_le (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    |x ^ n * Real.exp x| ≤
      (n.factorial : ℝ) * 2 ^ n * Real.exp (x / 2) := by
  have hn : 0 < (n.factorial : ℝ) := by positivity
  have hpow := (div_le_iff₀ hn).mp
    (Real.pow_div_factorial_le_exp (-x / 2) (by linarith : 0 ≤ -x / 2) n)
  rw [abs_mul, abs_pow, abs_of_nonpos hx, abs_of_pos (Real.exp_pos _)]
  calc
    (-x) ^ n * Real.exp x =
        (2 : ℝ) ^ n * (-x / 2) ^ n * Real.exp x := by
          rw [← mul_pow]
          congr 2
          ring
    _ ≤ 2 ^ n * (Real.exp (-x / 2) * (n.factorial : ℝ)) * Real.exp x := by
      gcongr
    _ = (n.factorial : ℝ) * 2 ^ n * Real.exp (x / 2) := by
      rw [show 2 ^ n * (Real.exp (-x / 2) * (n.factorial : ℝ)) * Real.exp x =
        (n.factorial : ℝ) * 2 ^ n * (Real.exp (-x / 2) * Real.exp x) by ring,
        ← Real.exp_add, show -x / 2 + x = x / 2 by ring]

theorem CutoffMemory.exp_memory_integrable {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (ρ * (s - t))) (Set.Iic t) := by
  have heq : (fun s : ℝ => Real.exp (ρ * (s - t))) =
      fun s => Real.exp (-ρ * t) * Real.exp (ρ * s) := by
    funext s
    rw [show ρ * (s - t) = -ρ * t + ρ * s by ring, Real.exp_add]
  rw [heq]
  exact (integrableOn_exp_mul_Iic hρ t).const_mul _

theorem CutoffMemory.exp_memory_integral {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    (∫ s in Set.Iic t, Real.exp (ρ * (s - t))) = ρ⁻¹ := by
  rw [show (fun s : ℝ => Real.exp (ρ * (s - t))) =
      fun s => Real.exp (-ρ * t) * Real.exp (ρ * s) by
    funext s
    rw [show ρ * (s - t) = -ρ * t + ρ * s by ring, Real.exp_add],
    integral_const_mul, integral_exp_mul_Iic hρ t, div_eq_mul_inv, ← mul_assoc,
    ← Real.exp_add, show -ρ * t + ρ * t = 0 by ring, Real.exp_zero, one_mul]

/-- Each memory integral has an explicit factorial bound. No
integrability premise is assumed: an integrable exponential majorant suffices. -/
theorem LMN_memory_integral_abs_le {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (l : ℤ) (t : ℝ) :
    |∫ s in Set.Iic t, I.hatZetaML m l s *
        (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
        Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t))| ≤
      (n.factorial : ℝ) * 2 ^ n *
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹ := by
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have hε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
      (m := m)
    positivity
  let B := (n.factorial : ℝ) * 2 ^ n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg : IntegrableOn (fun s : ℝ => B * Real.exp ((ρ / 2) * (s - t)))
      (Set.Iic t) := (CutoffMemory.exp_memory_integrable (by linarith : 0 < ρ / 2) t).const_mul B
  have hle : ∀ s ∈ Set.Iic t,
      ‖I.hatZetaML m l s * (4 * Real.pi ^ 2 * κ * (s - t) /
        epsilon β I.Λ m ^ 2) ^ n * Real.exp (ρ * (s - t))‖ ≤
        B * Real.exp ((ρ / 2) * (s - t)) := by
    intro s hs
    have hx : ρ * (s - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ.le (sub_nonpos.mpr hs)
    rw [Real.norm_eq_abs, show 4 * Real.pi ^ 2 * κ * (s - t) /
      epsilon β I.Λ m ^ 2 = ρ * (s - t) by dsimp [ρ]; ring,
      mul_assoc, abs_mul, abs_of_nonneg (hatZetaML_mem_Icc I hm l s).1]
    calc
      I.hatZetaML m l s * |(ρ * (s - t)) ^ n * Real.exp (ρ * (s - t))| ≤
          1 * |(ρ * (s - t)) ^ n * Real.exp (ρ * (s - t))| :=
            mul_le_mul_of_nonneg_right (hatZetaML_mem_Icc I hm l s).2 (abs_nonneg _)
      _ ≤ B * Real.exp ((ρ / 2) * (s - t)) := by
        simpa [B, show ρ * (s - t) / 2 = (ρ / 2) * (s - t) by ring] using
          polynomial_exp_abs_le n hx
  have hint := norm_integral_le_of_norm_le hg
    (ae_restrict_mem measurableSet_Iic |>.mono (fun s hs => hle s hs))
  rw [integral_const_mul, CutoffMemory.exp_memory_integral (by linarith : 0 < ρ / 2) t] at hint
  exact hint

/-- Product of a time cutoff and its translate by a fixed lag. -/
def CutoffMemory.cutoffPair (f : ℝ → ℝ) (u : ℝ) : ℝ → ℝ :=
  fun t => f t * f (t + u)

theorem CutoffMemory.cutoffPair_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (u : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (CutoffMemory.cutoffPair f u) :=
  hf.mul (hf.comp (by fun_prop))

theorem CutoffMemory.cutoffPair_derivative_bound {f : ℝ → ℝ} {N j : ℕ} {B τ : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hB : 0 ≤ B) (hτ : 0 < τ)
    (hb : ∀ j ≤ N, ∀ t, |iteratedDeriv j f t| ≤ B / τ ^ j)
    (hj : j ≤ N) (u t : ℝ) :
    |iteratedDeriv j (CutoffMemory.cutoffPair f u) t| ≤ 2 ^ j * B ^ 2 / τ ^ j := by
  have hshift : ContDiff ℝ (j : ℕ∞) (fun t => f (t + u)) :=
    (hf.comp (by fun_prop)).of_le (by simp)
  change |iteratedDeriv j (f * (fun t => f (t + u))) t| ≤ _
  rw [iteratedDeriv_mul (hf.of_le (by simp)).contDiffAt hshift.contDiffAt]
  simp_rw [iteratedDeriv_comp_add_const]
  calc
    |∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        iteratedDeriv i f t * iteratedDeriv (j - i) f (t + u)| ≤
      ∑ i ∈ Finset.range (j + 1), |(j.choose i : ℝ) *
        iteratedDeriv i f t * iteratedDeriv (j - i) f (t + u)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (B ^ 2 / τ ^ j) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        (j.choose i : ℝ) * |iteratedDeriv i f t| * |iteratedDeriv (j - i) f (t + u)| ≤
          (j.choose i : ℝ) * (B / τ ^ i) * (B / τ ^ (j - i)) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left (hb i (by omega) t) (Nat.cast_nonneg _)
            · exact hb (j - i) (by omega) (t + u)
            · exact abs_nonneg _
            · positivity
        _ = _ := by
          rw [mul_assoc, div_mul_div_comm, ← pow_add, Nat.add_sub_of_le hi']
          ring
    _ = _ := by
      rw [← Finset.sum_mul]
      have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [hchoose]
      ring

theorem CutoffMemory.cutoffPair_derivative_continuous_shift {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : ℕ) (t : ℝ) :
    Continuous (fun u => iteratedDeriv j (CutoffMemory.cutoffPair f u) t) := by
  have heq : (fun u => iteratedDeriv j (CutoffMemory.cutoffPair f u) t) =
      fun u => ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        iteratedDeriv i f t * iteratedDeriv (j - i) f (t + u) := by
    funext u
    change iteratedDeriv j (f * (fun t => f (t + u))) t = _
    have hshift : ContDiff ℝ (j : ℕ∞) (fun t => f (t + u)) :=
      (hf.comp (by fun_prop)).of_le (by simp)
    rw [iteratedDeriv_mul (hf.of_le (by simp)).contDiffAt hshift.contDiffAt]
    simp_rw [iteratedDeriv_comp_add_const]
  rw [heq]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul
    ((hf.continuous_iteratedDeriv (j - i) (by simp)).comp (by fun_prop)))

/-- Past-lag exponential memory integral of a derivative of a cutoff pair. -/
def CutoffMemory.pairMemory (f : ℝ → ℝ) (ρ : ℝ) (n j : ℕ) (t : ℝ) : ℝ :=
  ∫ u in Set.Iic (0 : ℝ), iteratedDeriv j (CutoffMemory.cutoffPair f u) t *
    ((ρ * u) ^ n * Real.exp (ρ * u))

theorem CutoffMemory.pairMemory_integrand_bound {f : ℝ → ℝ} {N j n : ℕ} {B τ ρ : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hB : 0 ≤ B) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hb : ∀ j ≤ N, ∀ t, |iteratedDeriv j f t| ≤ B / τ ^ j)
    (hj : j ≤ N) (t : ℝ) {u : ℝ} (hu : u ≤ 0) :
    ‖iteratedDeriv j (CutoffMemory.cutoffPair f u) t * ((ρ * u) ^ n * Real.exp (ρ * u))‖ ≤
      (2 ^ j * B ^ 2 / τ ^ j) * ((n.factorial : ℝ) * 2 ^ n) *
        Real.exp (ρ / 2 * u) := by
  rw [Real.norm_eq_abs, abs_mul]
  have hpoly := polynomial_exp_abs_le n (mul_nonpos_of_nonneg_of_nonpos hρ.le hu)
  have hpair := CutoffMemory.cutoffPair_derivative_bound hf hB hτ hb hj u t
  calc
    _ ≤ (2 ^ j * B ^ 2 / τ ^ j) *
        ((n.factorial : ℝ) * 2 ^ n * Real.exp (ρ * u / 2)) := by
      apply mul_le_mul hpair hpoly (abs_nonneg _)
      positivity
    _ = _ := by rw [show ρ * u / 2 = ρ / 2 * u by ring]; ring

theorem CutoffMemory.pairMemory_integrand_continuous {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ρ : ℝ) (n j : ℕ) (t : ℝ) :
    Continuous (fun u => iteratedDeriv j (CutoffMemory.cutoffPair f u) t *
      ((ρ * u) ^ n * Real.exp (ρ * u))) :=
  (CutoffMemory.cutoffPair_derivative_continuous_shift hf j t).mul (by fun_prop)

theorem CutoffMemory.pairMemory_integrable {f : ℝ → ℝ} {N j n : ℕ} {B τ ρ : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hB : 0 ≤ B) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hb : ∀ j ≤ N, ∀ t, |iteratedDeriv j f t| ≤ B / τ ^ j)
    (hj : j ≤ N) (t : ℝ) :
    IntegrableOn (fun u => iteratedDeriv j (CutoffMemory.cutoffPair f u) t *
      ((ρ * u) ^ n * Real.exp (ρ * u))) (Set.Iic (0 : ℝ)) := by
  refine ((integrableOn_exp_mul_Iic (by linarith : 0 < ρ / 2) 0).const_mul
    ((2 ^ j * B ^ 2 / τ ^ j) * ((n.factorial : ℝ) * 2 ^ n))).mono'
      (CutoffMemory.pairMemory_integrand_continuous hf ρ n j t).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
  exact CutoffMemory.pairMemory_integrand_bound hf hB hτ hρ hb hj t hu

theorem CutoffMemory.pairMemory_hasDerivAt {f : ℝ → ℝ} {N j n : ℕ} {B τ ρ : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hB : 0 ≤ B) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hb : ∀ j ≤ N, ∀ t, |iteratedDeriv j f t| ≤ B / τ ^ j)
    (hj : j < N) (t : ℝ) :
    HasDerivAt (CutoffMemory.pairMemory f ρ n j) (CutoffMemory.pairMemory f ρ n (j + 1) t) t := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (μ := volume.restrict (Set.Iic (0 : ℝ)))
    (bound := fun u => (2 ^ (j + 1) * B ^ 2 / τ ^ (j + 1)) *
      ((n.factorial : ℝ) * 2 ^ n) * Real.exp (ρ / 2 * u))
    (F := fun t u => iteratedDeriv j (CutoffMemory.cutoffPair f u) t *
      ((ρ * u) ^ n * Real.exp (ρ * u)))
    (F' := fun t u => iteratedDeriv (j + 1) (CutoffMemory.cutoffPair f u) t *
      ((ρ * u) ^ n * Real.exp (ρ * u)))
    (Filter.univ_mem)
    (Filter.Eventually.of_forall (fun x =>
      (CutoffMemory.pairMemory_integrand_continuous hf ρ n j x).aestronglyMeasurable))
    (CutoffMemory.pairMemory_integrable hf hB hτ hρ hb (by omega) t)
    (CutoffMemory.pairMemory_integrand_continuous hf ρ n (j + 1) t).aestronglyMeasurable
    ?_ ((integrableOn_exp_mul_Iic (by linarith : 0 < ρ / 2) 0).const_mul _)
    ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    intro x _
    exact CutoffMemory.pairMemory_integrand_bound hf hB hτ hρ hb (by omega) x hu
  · apply Filter.Eventually.of_forall
    intro u x _
    have hd := ((CutoffMemory.cutoffPair_smooth hf u).differentiable_iteratedDeriv j
      (by norm_cast; exact ENat.natCast_lt_top _)).differentiableAt (x := x) |>.hasDerivAt
    rw [← iteratedDeriv_succ] at hd
    exact hd.mul_const _

theorem CutoffMemory.pairMemory_derivative {f : ℝ → ℝ} {N j n : ℕ} {B τ ρ : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hB : 0 ≤ B) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hb : ∀ j ≤ N, ∀ t, |iteratedDeriv j f t| ≤ B / τ ^ j)
    (hj : j ≤ N) : iteratedDeriv j (CutoffMemory.pairMemory f ρ n 0) = CutoffMemory.pairMemory f ρ
        n j := by
  induction j with
  | zero => exact iteratedDeriv_zero
  | succ j ih =>
    rw [iteratedDeriv_succ, ih (by omega)]
    funext t
    exact (CutoffMemory.pairMemory_hasDerivAt hf hB hτ hρ hb (by omega) t).deriv

theorem CutoffMemory.pairMemory_abs_le {f : ℝ → ℝ} {N j n : ℕ} {B τ ρ : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hB : 0 ≤ B) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hb : ∀ j ≤ N, ∀ t, |iteratedDeriv j f t| ≤ B / τ ^ j)
    (hj : j ≤ N) (t : ℝ) :
    |CutoffMemory.pairMemory f ρ n j t| ≤ (2 ^ j * B ^ 2 / τ ^ j) *
      ((n.factorial : ℝ) * 2 ^ n) * (ρ / 2)⁻¹ := by
  have hint := norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Iic (by linarith : 0 < ρ / 2) 0).const_mul
      ((2 ^ j * B ^ 2 / τ ^ j) * ((n.factorial : ℝ) * 2 ^ n)))
    (ae_restrict_mem measurableSet_Iic |>.mono (fun u hu =>
      CutoffMemory.pairMemory_integrand_bound hf hB hτ hρ hb hj t hu))
  rw [integral_const_mul, integral_exp_mul_Iic (by linarith : 0 < ρ / 2) 0] at hint
  simpa [CutoffMemory.pairMemory, Real.norm_eq_abs, div_eq_mul_inv] using hint

theorem CutoffMemory.pairMemory_continuous {f : ℝ → ℝ} {N j n : ℕ} {B τ ρ : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hB : 0 ≤ B) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hb : ∀ j ≤ N, ∀ t, |iteratedDeriv j f t| ≤ B / τ ^ j)
    (hj : j ≤ N) : Continuous (CutoffMemory.pairMemory f ρ n j) := by
  apply continuous_of_dominated
    (bound := fun u => (2 ^ j * B ^ 2 / τ ^ j) * ((n.factorial : ℝ) * 2 ^ n) *
      Real.exp (ρ / 2 * u))
  · intro t
    exact (CutoffMemory.pairMemory_integrand_continuous hf ρ n j t).aestronglyMeasurable
  · intro t
    filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    exact CutoffMemory.pairMemory_integrand_bound hf hB hτ hρ hb hj t hu
  · exact (integrableOn_exp_mul_Iic (by linarith : 0 < ρ / 2) 0).const_mul _
  · apply Filter.Eventually.of_forall
    intro u
    exact ((CutoffMemory.cutoffPair_smooth hf u).continuous_iteratedDeriv j (by simp)).mul
        continuous_const

theorem CutoffMemory.pairMemory_contDiff {f : ℝ → ℝ} {N n : ℕ} {B τ ρ : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hB : 0 ≤ B) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hb : ∀ j ≤ N, ∀ t, |iteratedDeriv j f t| ≤ B / τ ^ j) :
    ContDiff ℝ (N : ℕ∞) (CutoffMemory.pairMemory f ρ n 0) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro j hj
    rw [CutoffMemory.pairMemory_derivative hf hB hτ hρ hb hj]
    exact CutoffMemory.pairMemory_continuous hf hB hτ hρ hb hj
  · intro j hj
    rw [CutoffMemory.pairMemory_derivative hf hB hτ hρ hb hj.le]
    intro t
    exact (CutoffMemory.pairMemory_hasDerivAt hf hB hτ hρ hb hj t).differentiableAt

theorem CutoffMemory.memory_pair_translation (f : ℝ → ℝ) (ρ : ℝ) (n : ℕ) (t : ℝ) :
    f t * (∫ s in Set.Iic t, f s * ((ρ * (s - t)) ^ n * Real.exp (ρ * (s - t)))) =
      CutoffMemory.pairMemory f ρ n 0 t := by
  have h := (measurePreserving_add_right volume t).setIntegral_preimage_emb
    (MeasurableEquiv.addRight t).measurableEmbedding
    (fun s => f t * (f s * ((ρ * (s - t)) ^ n * Real.exp (ρ * (s - t))))) (Set.Iic t)
  have hset : (fun u : ℝ => u + t) ⁻¹' Set.Iic t = Set.Iic 0 := by
    ext u
    simp
  rw [hset] at h
  rw [integral_const_mul] at h
  simpa [CutoffMemory.pairMemory, iteratedDeriv_zero, CutoffMemory.cutoffPair, add_comm,
      mul_assoc, integral_const_mul] using h.symm

theorem CutoffMemory.hat_mode_cutoffs_locally_single {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) : ∃ l : ℤ,
      ∀ᶠ s in nhds t, ∀ l' : ℤ, l' ≠ l → I.hatZetaML m l' s = 0 := by
  let T := tauPP β I.Λ m
  let τ := tauP β I.Λ m
  have hT : 0 < T := I.tauPP_pos' m
  have hτ : 0 < τ := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  let l : ℤ := ⌊t / T + 1 / 2⌋
  have hlo : ((l : ℝ) - 1 / 2) * T ≤ t := by
    have h : (l : ℝ) ≤ t / T + 1 / 2 := Int.floor_le _
    have h' : (l : ℝ) - 1 / 2 ≤ t / T := by linarith only [h]
    exact (le_div_iff₀ hT).mp h'
  have hhi : t < ((l : ℝ) + 1 / 2) * T := by
    have h : t / T + 1 / 2 < (l : ℝ) + 1 := Int.lt_floor_add_one _
    have h' : t / T < (l : ℝ) + 1 / 2 := by linarith only [h]
    exact (div_lt_iff₀ hT).mp h'
  refine ⟨l, ?_⟩
  filter_upwards [Ioo_mem_nhds (by linarith : t - τ / 2 < t)
    (by linarith : t < t + τ / 2)] with s hs
  intro l' hne
  have hnot : s ∉ Set.Icc (((l' : ℝ) - 1 / 2) * T + τ)
      (((l' : ℝ) + 1 / 2) * T - τ) := by
    intro hmem
    have hsep : l' ≤ l - 1 ∨ l + 1 ≤ l' := by omega
    rcases hsep with hsep | hsep
    · have hcast : (l' : ℝ) ≤ (l : ℝ) - 1 := by exact_mod_cast hsep
      have hmul := mul_le_mul_of_nonneg_right hcast hT.le
      nlinarith only [hs.1, hlo, hτ, hmem.2, hmul]
    · have hcast : (l : ℝ) + 1 ≤ (l' : ℝ) := by exact_mod_cast hsep
      have hmul := mul_le_mul_of_nonneg_right hcast hT.le
      nlinarith only [hs.2, hhi, hτ, hmem.1, hmul]
  have hle := I.hatZeta_le m hm l' s
  rw [indIcc_eq_zero_of_not_mem hnot] at hle
  exact le_antisymm hle (hatZetaML_mem_Icc I hm l' s).1

theorem CutoffMemory.LMN_locally_pairMemory {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (n : ℕ) (t : ℝ) : ∃ l : ℤ,
    I.LMN κ m n =ᶠ[nhds t] CutoffMemory.pairMemory (I.hatZetaML m l)
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) n 0 := by
  classical
  obtain ⟨l, hzero⟩ := CutoffMemory.hat_mode_cutoffs_locally_single I hm t
  refine ⟨l, ?_⟩
  filter_upwards [hzero] with s hs
  unfold Ingredients.LMN
  rw [tsum_eq_single l (fun l' hne => by rw [hs l' hne, zero_mul])]
  rw [← CutoffMemory.memory_pair_translation]
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro u _
  dsimp only
  rw [show 4 * Real.pi ^ 2 * κ * (u - s) / epsilon β I.Λ m ^ 2 =
    (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * (u - s) by ring]
  ring

/-- `e.Lmn.bound` for the actual memory sum, including every positive
order allowed by the cutoff budget. Constants retain the factorial
and Leibniz factors explicitly. -/
theorem LMN_derivative_abs_le {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) {ℓ : ℕ}
    (hℓ : ℓ ≤ Nstar β) (t : ℝ) :
    |iteratedDeriv ℓ (I.LMN κ m n) t| ≤
      (2 ^ ℓ * I.Chat ^ 2 / tauP β I.Λ m ^ ℓ) *
        ((n.factorial : ℝ) * 2 ^ n) *
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹ := by
  obtain ⟨l, hlocal⟩ := CutoffMemory.LMN_locally_pairMemory I hm κ n t
  have hf : ContDiff ℝ (⊤ : ℕ∞) (I.hatZetaML m l) := by
    unfold Ingredients.hatZetaML shiftCutoff
    exact (I.hatZeta_smooth m).comp (by fun_prop)
  have hB : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  have hτ := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hρ : 0 < 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 := by
    have hε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    positivity
  have hb : ∀ j ≤ Nstar β, ∀ s, |iteratedDeriv j (I.hatZetaML m l) s| ≤
      I.Chat / tauP β I.Λ m ^ j := fun j hj s => hatZetaML_derivative_abs_le I hm l hj s
  rw [CutoffMemory.iteratedDeriv_congr_nhds hlocal ℓ, CutoffMemory.pairMemory_derivative hf hB hτ
      hρ hb hℓ]
  exact CutoffMemory.pairMemory_abs_le hf hB hτ hρ hb hℓ t

/-- The paper-size bound with one constant uniform in both indices.
Only `I.Chat ≤ C₀` is needed for the memory coefficient. -/
theorem LMN_derivative_paper_bound {β C₀ : ℝ} (I : Ingredients β)
    (hcutoff : I.Chat ≤ C₀) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    {n ℓ : ℕ} (hn : n ≤ Nstar β) (hℓ : ℓ ≤ Nstar β) (t : ℝ) :
    |iteratedDeriv ℓ (I.LMN κ m n) t| ≤
      ((Nstar β).factorial : ℝ) * 2 ^ Nstar β * 2 ^ Nstar β * C₀ ^ 2 /
        (2 * Real.pi ^ 2) * (epsilon β I.Λ m ^ 2 / κ) / tauP β I.Λ m ^ ℓ := by
  have hC : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  have hC₀ : 0 ≤ C₀ := hC.trans hcutoff
  have hτ := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hπ := Real.pi_pos
  have hnfac : (n.factorial : ℝ) ≤ ((Nstar β).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hn
  have hn2 : (2 : ℝ) ^ n ≤ 2 ^ Nstar β := pow_le_pow_right₀ (by norm_num) hn
  have hℓ2 : (2 : ℝ) ^ ℓ ≤ 2 ^ Nstar β := pow_le_pow_right₀ (by norm_num) hℓ
  calc
    _ ≤ (2 ^ ℓ * I.Chat ^ 2 / tauP β I.Λ m ^ ℓ) *
        ((n.factorial : ℝ) * 2 ^ n) *
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹ :=
          LMN_derivative_abs_le I hm hκ n hℓ t
    _ ≤ (2 ^ Nstar β * C₀ ^ 2 / tauP β I.Λ m ^ ℓ) *
        (((Nstar β).factorial : ℝ) * 2 ^ Nstar β) *
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹ := by gcongr
    _ = _ := by
      simp only [inv_div]
      field_simp
      ring

/-- The memory coefficient is `C^{N_*}` in time. -/
theorem LMN_contDiff {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m)
    {κ : ℝ} (hκ : 0 < κ) (n : ℕ) : ContDiff ℝ (Nstar β : ℕ∞) (I.LMN κ m n) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  obtain ⟨l, hlocal⟩ := CutoffMemory.LMN_locally_pairMemory I hm κ n t
  have hf : ContDiff ℝ (⊤ : ℕ∞) (I.hatZetaML m l) := by
    unfold Ingredients.hatZetaML shiftCutoff
    exact (I.hatZeta_smooth m).comp (by fun_prop)
  have hB : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  have hτ := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hρ : 0 < 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 := by
    have hε := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    positivity
  have hb : ∀ j ≤ Nstar β, ∀ s, |iteratedDeriv j (I.hatZetaML m l) s| ≤
      I.Chat / tauP β I.Λ m ^ j := fun j hj s => hatZetaML_derivative_abs_le I hm l hj s
  exact (CutoffMemory.pairMemory_contDiff hf hB hτ hρ hb).contDiffAt.congr_of_eventuallyEq hlocal

end AVenhance.Infra.Section3
