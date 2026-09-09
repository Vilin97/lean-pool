/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyGeneratingComposition

@[expose] public section

/-! The finite generating sum for genuine derivatives.  This file derives
the identity-map contribution and the composition estimate needed by the
flow bootstrap from actual derivatives, including the exact Faà di Bruno
formula. -/

noncomputable section

open scoped BigOperators ContDiff

namespace EulerGevreyGeneratingDerivatives

open EulerGevreyGeneratingComposition

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def derivativeSum (f : E → F) (N : ℕ) (z : ℝ) (x : E) : ℝ :=
  generatingSum (ftaylorSeries ℝ f x) N z

theorem derivativeSum_nonneg (f : E → F) (N : ℕ) (z : ℝ) (x : E)
    (hz : 0 ≤ z) : 0 ≤ derivativeSum f N z x :=
  generatingSum_nonneg _ _ _ hz

theorem derivativeSum_add_le (f g : E → F) (N : ℕ) (z : ℝ) (x : E)
    (hf : ContDiffAt ℝ N f x) (hg : ContDiffAt ℝ N g x) (hz : 0 ≤ z) :
    derivativeSum (f+g) N z x ≤ derivativeSum f N z x+derivativeSum g N z x := by
  unfold derivativeSum generatingSum normalizedJet ftaylorSeries
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  have hnN : (n : ℕ∞ω) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  rw [iteratedFDeriv_add_apply (hf.of_le hnN) (hg.of_le hnN)]
  calc
    _ ≤ ((‖iteratedFDeriv ℝ n f x‖+‖iteratedFDeriv ℝ n g x‖)/(n.factorial : ℝ)^2)*z^n := by
      gcongr
      exact norm_add_le _ _
    _ = _ := by ring

theorem norm_iteratedFDeriv_id_le (n : ℕ) (hn : 0 < n) (x : E) :
    ‖iteratedFDeriv ℝ n (id : E → E) x‖ ≤ if n = 1 then 1 else 0 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  by_cases hm : m = 0
  · subst m
    change ‖iteratedFDeriv ℝ 1 (id : E → E) x‖ ≤ (1 : ℝ)
    rw [norm_iteratedFDeriv_one, fderiv_id]
    exact ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
  · have hm1 : m+1 ≠ 1 := by omega
    have hid : fderiv ℝ (id : E → E) = fun _ : E => ContinuousLinearMap.id ℝ E := by
      funext y
      exact fderiv_id
    rw [Nat.succ_eq_add_one, ite_eq_right hm1, ← norm_iteratedFDeriv_fderiv]
    simp [hid, iteratedFDeriv_const_of_ne hm]

theorem derivativeSum_id_le (N : ℕ) (z : ℝ) (x : E) (hz : 0 ≤ z) :
    derivativeSum (id : E → E) N z x ≤ z := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, if n = 1 then z else 0 := by
      unfold derivativeSum generatingSum
      apply Finset.sum_le_sum
      intro n hn
      have hnorm := norm_iteratedFDeriv_id_le n (Finset.mem_Icc.mp hn).1 x
      change ‖iteratedFDeriv ℝ n (id : E → E) x‖/(n.factorial : ℝ)^2*z^n ≤ _
      by_cases hn1 : n = 1
      · subst n
        simp only [ite_true, Nat.factorial_one, Nat.cast_one,
          one_pow, div_one, pow_one] at hnorm ⊢
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm hz
      · simp only [ite_eq_right hn1] at hnorm ⊢
        have hz0 : ‖iteratedFDeriv ℝ n (id : E → E) x‖ = 0 :=
          le_antisymm hnorm (norm_nonneg _)
        rw [hz0, zero_div, zero_mul]
    _ ≤ z := by
      simp only [Finset.sum_ite_eq', Finset.mem_Icc, le_refl, true_and]
      split_ifs
      · exact le_rfl
      · exact hz

theorem derivativeSum_id_add_le (f : E → E) (N : ℕ) (z : ℝ) (x : E)
    (hf : ContDiffAt ℝ N f x) (hz : 0 ≤ z) :
    derivativeSum (id+f) N z x ≤ z+derivativeSum f N z x :=
  (derivativeSum_add_le id f N z x contDiffAt_id hf hz).trans
    (add_le_add (derivativeSum_id_le N z x hz) le_rfl)

theorem derivativeSum_comp_le (f : E → F) (g : F → G) (N : ℕ)
    (z B R : ℝ) (x : E) (hz : 0 ≤ z) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hf : ContDiffAt ℝ N f x) (hg : ContDiffAt ℝ N g (f x))
    (hgj : ∀ j ∈ Finset.Icc 1 N,
      ‖iteratedFDeriv ℝ j g (f x)‖ ≤ B*R^j*(j.factorial : ℝ)^2)
    (hsmall : R*derivativeSum f N z x < 1) :
    derivativeSum (g ∘ f) N z x ≤
      B*(R*derivativeSum f N z x)/(1-R*derivativeSum f N z x) := by
  have he := generatingSum_taylorComp_le (ftaylorSeries ℝ f x)
    (ftaylorSeries ℝ g (f x)) N B R z hB hR hz hgj hsmall
  refine le_trans (le_of_eq ?_) he
  unfold derivativeSum generatingSum normalizedJet
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : (n : ℕ∞ω) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  rw [show ftaylorSeries ℝ (g ∘ f) x n =
    (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeries ℝ f x) n from
    iteratedFDeriv_comp hg hf hnN]

theorem rational_fraction_mono (B x y : ℝ) (hB : 0 ≤ B)
    (hxy : x ≤ y) (hy : y < 1) :
    B*x/(1-x) ≤ B*y/(1-y) := by
  have hx : 0 < 1-x := by linarith
  have hy' : 0 < 1-y := by linarith
  apply (div_le_div_iff₀ hx hy').2
  nlinarith [mul_le_mul_of_nonneg_left hxy hB]

/-- The identity part of a flow costs exactly z in its generating sum. -/
theorem derivativeSum_comp_id_add_le (f : E → E) (g : E → F) (N : ℕ)
    (z B R : ℝ) (x : E) (hz : 0 ≤ z) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hf : ContDiffAt ℝ N f x) (hg : ContDiffAt ℝ N g (x+f x))
    (hgj : ∀ j ∈ Finset.Icc 1 N,
      ‖iteratedFDeriv ℝ j g (x+f x)‖ ≤ B*R^j*(j.factorial : ℝ)^2)
    (hsmall : R*(z+derivativeSum f N z x) < 1) :
    derivativeSum (g ∘ (id+f)) N z x ≤
      EulerGevreyFlowBootstrap.rationalRate B R z (derivativeSum f N z x) := by
  have hsum := mul_le_mul_of_nonneg_left (derivativeSum_id_add_le f N z x hf hz) hR
  have he := derivativeSum_comp_le (id+f) g N z B R x hz hB hR
    (contDiffAt_id.add hf) hg
    (by simpa only [Pi.add_apply, id_eq] using hgj) (hsum.trans_lt hsmall)
  exact he.trans (rational_fraction_mono B _ _ hB hsum hsmall)

end EulerGevreyGeneratingDerivatives
