/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: residue-calculus. Taylor-coefficient extractor via iterated `dslope`.
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic

/-!
# Taylor coefficients via iterated difference quotients (residue-calculus)

`RS.taylorCoeffAt g z₀ j` is the `j`-th Taylor coefficient of `g` at `z₀`, extracted by the
iterated `dslope` operator — no `iteratedDeriv`, no factorials. For `g` analytic at `z₀` with
power series `p` it equals `p.coeff j` (`RS.HasFPowerSeriesAt.taylorCoeffAt_eq`).

Main exports:
* `RS.taylorCoeffAt_congr` — dependence on the `𝓝 z₀`-germ only;
* `RS.taylorCoeffAt_add` / `_const_mul` / `_sub` / `_fun_sum` — ℂ-linearity on analytic germs;
* `RS.taylorCoeffAt_sub_pow_mul`, `RS.taylorCoeffAt_monomial` — the monomial shift workhorse;
* `RS.AnalyticAt.exists_taylor_remainder` — exact, pointwise Taylor remainder factorization.
-/

open Filter Topology Metric Function

namespace RS

variable {f g F : ℂ → ℂ} {z₀ : ℂ}

/-- The `j`-th Taylor coefficient of `g` at `z₀`, extracted by iterated difference quotients.
For `g` analytic at `z₀` with power series `p` this equals `p.coeff j`. Junk for non-smooth
`g` (whatever the iterated `dslope` evaluates to). -/
noncomputable def taylorCoeffAt (g : ℂ → ℂ) (z₀ : ℂ) (j : ℕ) : ℂ :=
  (Function.swap dslope z₀)^[j] g z₀

@[simp] theorem taylorCoeffAt_zero_apply : taylorCoeffAt g z₀ 0 = g z₀ := rfl

theorem taylorCoeffAt_succ (j : ℕ) :
    taylorCoeffAt g z₀ (j + 1) = taylorCoeffAt (dslope g z₀) z₀ j := rfl

/-- `dslope` iterates of analytic germs are analytic. -/
theorem AnalyticAt.iterate_dslope (hg : AnalyticAt ℂ g z₀) (j : ℕ) :
    AnalyticAt ℂ ((Function.swap dslope z₀)^[j] g) z₀ := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨_, hp.has_fpower_series_iterate_dslope_fslope j⟩

/-- Bridge to power series (for consumers that hold a `HasFPowerSeriesAt`; not used
internally). -/
theorem HasFPowerSeriesAt.taylorCoeffAt_eq {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt g p z₀) (j : ℕ) : taylorCoeffAt g z₀ j = p.coeff j := by
  have h := (hp.has_fpower_series_iterate_dslope_fslope j).coeff_zero 1
  calc taylorCoeffAt g z₀ j = (FormalMultilinearSeries.fslope^[j] p).coeff 0 := h.symm
    _ = p.coeff j := by rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add]

/-- `dslope` respects `𝓝 z₀`-germs. -/
theorem Filter.EventuallyEq.dslope_eq (hfg : f =ᶠ[𝓝 z₀] g) :
    dslope f z₀ =ᶠ[𝓝 z₀] dslope g z₀ := by
  have hz : f z₀ = g z₀ := hfg.eq_of_nhds
  filter_upwards [hfg] with b hb
  rcases eq_or_ne b z₀ with rfl | hbz
  · simp only [dslope_same, hfg.deriv_eq]
  · rw [dslope_of_ne _ hbz, dslope_of_ne _ hbz, slope_def_field, slope_def_field, hb, hz]

/-- Germ invariance: `taylorCoeffAt` only depends on the `𝓝 z₀`-germ. -/
theorem taylorCoeffAt_congr (hfg : f =ᶠ[𝓝 z₀] g) (j : ℕ) :
    taylorCoeffAt f z₀ j = taylorCoeffAt g z₀ j := by
  induction j generalizing f g with
  | zero => exact hfg.eq_of_nhds
  | succ j ih =>
    rw [taylorCoeffAt_succ, taylorCoeffAt_succ]
    exact ih (Filter.EventuallyEq.dslope_eq hfg)

theorem dslope_const_mul (c : ℂ) (g : ℂ → ℂ) (z₀ : ℂ) :
    dslope (fun z => c * g z) z₀ = fun b => c * dslope g z₀ b := by
  funext b
  rcases eq_or_ne b z₀ with rfl | hbz
  · simp only [dslope_same, deriv_const_mul_field]
  · rw [dslope_of_ne _ hbz, dslope_of_ne _ hbz, slope_def_field, slope_def_field]
    ring

theorem dslope_const (c : ℂ) (z₀ : ℂ) : dslope (fun _ => c) z₀ = fun _ => 0 := by
  funext b
  rcases eq_or_ne b z₀ with rfl | hbz
  · simp
  · rw [dslope_of_ne _ hbz, slope_def_field]
    simp

theorem taylorCoeffAt_const_mul (c : ℂ) (j : ℕ) :
    taylorCoeffAt (fun z => c * g z) z₀ j = c * taylorCoeffAt g z₀ j := by
  induction j generalizing g with
  | zero => rfl
  | succ j ih =>
    rw [taylorCoeffAt_succ, taylorCoeffAt_succ, dslope_const_mul]
    exact ih

theorem taylorCoeffAt_zero_fun (j : ℕ) : taylorCoeffAt (fun _ => (0 : ℂ)) z₀ j = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [taylorCoeffAt_succ, dslope_const]; exact ih

@[simp] theorem taylorCoeffAt_const (c : ℂ) (j : ℕ) :
    taylorCoeffAt (fun _ => c) z₀ j = if j = 0 then c else 0 := by
  cases j with
  | zero => rfl
  | succ j => rw [taylorCoeffAt_succ, dslope_const, taylorCoeffAt_zero_fun]; simp

theorem taylorCoeffAt_neg (j : ℕ) :
    taylorCoeffAt (fun z => -g z) z₀ j = -taylorCoeffAt g z₀ j := by
  simpa [neg_one_mul] using taylorCoeffAt_const_mul (g := g) (z₀ := z₀) (-1) j

/-- ℂ-additivity of Taylor coefficients on analytic germs. -/
theorem taylorCoeffAt_add (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀) (j : ℕ) :
    taylorCoeffAt (f + g) z₀ j = taylorCoeffAt f z₀ j + taylorCoeffAt g z₀ j := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  rw [HasFPowerSeriesAt.taylorCoeffAt_eq (hp.add hq) j,
    HasFPowerSeriesAt.taylorCoeffAt_eq hp j, HasFPowerSeriesAt.taylorCoeffAt_eq hq j]
  rfl

theorem taylorCoeffAt_fun_add (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀) (j : ℕ) :
    taylorCoeffAt (fun z => f z + g z) z₀ j = taylorCoeffAt f z₀ j + taylorCoeffAt g z₀ j :=
  taylorCoeffAt_add hf hg j

theorem taylorCoeffAt_sub (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀) (j : ℕ) :
    taylorCoeffAt (fun z => f z - g z) z₀ j = taylorCoeffAt f z₀ j - taylorCoeffAt g z₀ j := by
  have hneg : AnalyticAt ℂ (fun z => -g z) z₀ := by fun_prop
  have h2 := taylorCoeffAt_fun_add (g := fun z => -g z) hf hneg j
  rw [taylorCoeffAt_neg] at h2
  have h1 : (fun z => f z - g z) = fun z => f z + -g z := by funext z; ring
  rw [h1, h2, sub_eq_add_neg]

theorem taylorCoeffAt_fun_sum {ι : Type*} {s : Finset ι} {G : ι → ℂ → ℂ}
    (hG : ∀ i ∈ s, AnalyticAt ℂ (G i) z₀) (j : ℕ) :
    taylorCoeffAt (fun z => ∑ i ∈ s, G i z) z₀ j = ∑ i ∈ s, taylorCoeffAt (G i) z₀ j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hstep : (fun z => ∑ i ∈ insert a s, G i z)
        = fun z => G a z + ∑ i ∈ s, G i z := by
      funext z; rw [Finset.sum_insert ha]
    rw [hstep, Finset.sum_insert ha,
      taylorCoeffAt_fun_add (hG a (Finset.mem_insert_self a s))
        (Finset.analyticAt_fun_sum s fun i hi => hG i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hG i (Finset.mem_insert_of_mem hi)]

theorem dslope_sub_mul (hF : DifferentiableAt ℂ F z₀) :
    dslope (fun z => (z - z₀) * F z) z₀ = F := by
  funext b
  rcases eq_or_ne b z₀ with rfl | hbz
  · rw [dslope_same]
    have h1 : HasDerivAt (fun z => (z - b) * F z)
        (1 * F b + (b - b) * deriv F b) b :=
      ((hasDerivAt_id b).sub_const b).mul hF.hasDerivAt
    simpa using h1.deriv
  · have h2 := dslope_sub_smul_of_ne F hbz
    simpa only [smul_eq_mul] using h2

/-- Shift: prepending a monomial factor shifts Taylor coefficients. THE workhorse identity. -/
theorem taylorCoeffAt_sub_pow_mul (hg : AnalyticAt ℂ g z₀) (d j : ℕ) :
    taylorCoeffAt (fun z => (z - z₀) ^ d * g z) z₀ j
      = if j < d then 0 else taylorCoeffAt g z₀ (j - d) := by
  induction d generalizing j with
  | zero => simp only [pow_zero, one_mul, Nat.not_lt_zero, if_false, Nat.sub_zero]
  | succ d ih =>
    cases j with
    | zero =>
      simp only [taylorCoeffAt_zero_apply, sub_self, zero_pow (Nat.succ_ne_zero d), zero_mul,
        Nat.zero_lt_succ, if_true]
    | succ j =>
      have hfun : (fun z => (z - z₀) ^ (d + 1) * g z)
          = fun z => (z - z₀) * ((z - z₀) ^ d * g z) := by
        funext z; ring
      have hg' : DifferentiableAt ℂ g z₀ := hg.differentiableAt
      have hdiff : DifferentiableAt ℂ (fun z => (z - z₀) ^ d * g z) z₀ := by fun_prop
      rw [hfun, taylorCoeffAt_succ, dslope_sub_mul hdiff, ih j]
      simp only [Nat.succ_lt_succ_iff, Nat.succ_sub_succ]

@[simp] theorem taylorCoeffAt_monomial (d j : ℕ) :
    taylorCoeffAt (fun z => (z - z₀) ^ d) z₀ j = if j = d then 1 else 0 := by
  have h := taylorCoeffAt_sub_pow_mul (g := fun _ => (1 : ℂ)) (z₀ := z₀) analyticAt_const d j
  simp only [mul_one] at h
  rw [h, taylorCoeffAt_const]
  split_ifs <;> first | rfl | omega

/-- Taylor remainder factorization, EXACT (pointwise): subtracting the degree-`< m` Taylor
polynomial leaves an honest `(z - z₀) ^ m`-divisible function with analytic quotient. -/
theorem AnalyticAt.exists_taylor_remainder (hg : AnalyticAt ℂ g z₀) (m : ℕ) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r z₀ ∧
      (∀ j, taylorCoeffAt r z₀ j = taylorCoeffAt g z₀ (j + m)) ∧
      ∀ z, g z = (∑ d ∈ Finset.range m, taylorCoeffAt g z₀ d * (z - z₀) ^ d)
        + (z - z₀) ^ m * r z := by
  classical
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ,
      G = fun z => g z - ∑ d ∈ Finset.range m, taylorCoeffAt g z₀ d * (z - z₀) ^ d := ⟨_, rfl⟩
  have hPan : AnalyticAt ℂ
      (fun z => ∑ d ∈ Finset.range m, taylorCoeffAt g z₀ d * (z - z₀) ^ d) z₀ :=
    Finset.analyticAt_fun_sum _ fun d _ => by fun_prop
  have hGan : AnalyticAt ℂ G z₀ := by rw [hGdef]; exact hg.sub hPan
  -- Taylor coefficients of `G` vanish below `m`.
  have hGcoeff : ∀ j, taylorCoeffAt G z₀ j
      = taylorCoeffAt g z₀ j - (if j < m then taylorCoeffAt g z₀ j else 0) := by
    intro j
    rw [hGdef, taylorCoeffAt_sub hg hPan]
    congr 1
    rw [taylorCoeffAt_fun_sum (fun d _ => by fun_prop) j]
    have hterm : ∀ d ∈ Finset.range m,
        taylorCoeffAt (fun z => taylorCoeffAt g z₀ d * (z - z₀) ^ d) z₀ j
          = if j = d then taylorCoeffAt g z₀ d else 0 := by
      intro d _
      rw [taylorCoeffAt_const_mul, taylorCoeffAt_monomial]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    simp only [Finset.mem_range]
  have hzero : ∀ k < m, (Function.swap dslope z₀)^[k] G z₀ = 0 := by
    intro k hk
    have h0 := hGcoeff k
    rw [if_pos hk, sub_self] at h0
    exact h0
  have h1 : (fun z => (z - z₀) ^ m * (Function.swap dslope z₀)^[m] G z) = G := by
    funext z
    have hpt := pow_sub_smul_iterate_dslope_of_zero (f := G) (a := z₀) m hzero z
    rwa [smul_eq_mul] at hpt
  refine ⟨(Function.swap dslope z₀)^[m] G, AnalyticAt.iterate_dslope hGan m, ?_, ?_⟩
  · intro j
    have h2 := taylorCoeffAt_sub_pow_mul (AnalyticAt.iterate_dslope hGan m) m (j + m)
    rw [h1, hGcoeff (j + m)] at h2
    simp only [if_neg (show ¬ j + m < m by omega), sub_zero, Nat.add_sub_cancel] at h2
    exact h2.symm
  · intro z
    have hpt := congrFun h1 z
    rw [hpt]
    simp only [hGdef]
    ring

end RS
