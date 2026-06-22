/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.CoulombConcreteTheorem42

/-!
# Non-vacuousness of the Coulomb Concrete Theorem

Proves that the equilibrium Maxwellian satisfies all 13 hypotheses of
`CoulombConcreteTheorem42`, demonstrating the theorem is non-vacuous.

Also provides helper lemmas about the equilibrium Maxwellian:
- `fderiv_equilibriumMaxwellian`: directional derivative formula
- `equilibriumMaxwellian_schwartz_decay`: Schwartz-class decay
- `equilibriumMaxwellian_log_bound`: polynomial log growth
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section

namespace VML

/-- The directional derivative of the equilibrium Maxwellian:
    ∂(eM)/∂vᵢ = -(vᵢ/T) · eM(v).
    Proof: eM = C · exp(-normSq/(2T)), chain rule gives
    fderiv(eM) v eᵢ = C · exp(…) · (-2vᵢ/(2T)) = eM(v) · (-vᵢ/T). -/
lemma fderiv_equilibriumMaxwellian (ρ T : ℝ) (_hT : 0 < T) (v : Fin 3 → ℝ) (i : Fin 3) :
    fderiv ℝ (equilibriumMaxwellian ρ T) v (Pi.single i 1) =
    -(v i / T) * equilibriumMaxwellian ρ T v := by
  have hq_smooth : ContDiff ℝ ⊤ (fun w : Fin 3 → ℝ => -(normSq w) / (2 * T)) :=
    contDiff_negNormSq_div T
  have hq_diff : Differentiable ℝ (fun w : Fin 3 → ℝ => -(normSq w) / (2 * T)) :=
    hq_smooth.differentiable WithTop.top_ne_zero
  -- eM = pf • (exp ∘ q)
  have heM_eq : equilibriumMaxwellian ρ T =
      (ρ / (2 * π * T) ^ ((3:ℝ)/2)) •
      (Real.exp ∘ (fun w : Fin 3 → ℝ => -(normSq w) / (2 * T))) := by
    ext w; simp [equilibriumMaxwellian, Pi.smul_apply, smul_eq_mul]
  rw [heM_eq]
  set pf := ρ / (2 * π * T) ^ ((3:ℝ)/2)
  set q : (Fin 3 → ℝ) → ℝ := fun w => -(normSq w) / (2 * T)
  set expq : (Fin 3 → ℝ) → ℝ := Real.exp ∘ q
  -- fderiv (pf • expq) = pf • fderiv expq
  have hexpq_diff : DifferentiableAt ℝ expq v :=
    (Real.differentiable_exp.comp hq_diff).differentiableAt
  rw [show (pf • expq : (Fin 3 → ℝ) → ℝ) = fun w => pf * expq w from by
    ext w; simp [Pi.smul_apply, smul_eq_mul]]
  rw [fderiv_const_mul hexpq_diff pf, _root_.smul_apply, smul_eq_mul]
  -- fderiv expq = exp(q v) • fderiv q by chain rule
  rw [show expq = fun w => Real.exp (q w) from rfl,
    fderiv_exp_comp_always q v, _root_.smul_apply, smul_eq_mul]
  -- Compute fderiv of q at v applied to e_i
  have h_comp_diff : ∀ j : Fin 3, DifferentiableAt ℝ (fun w : Fin 3 → ℝ => w j * w j) v :=
    fun j => (differentiableAt_apply j v).mul (differentiableAt_apply j v)
  have h_sum_diff : DifferentiableAt ℝ (fun w : Fin 3 → ℝ => ∑ j : Fin 3, w j * w j) v :=
    DifferentiableAt.fun_sum fun j _ => h_comp_diff j
  -- q = fun w => (-1/(2*T)) * normSq w, so fderiv q = (-1/(2T)) • fderiv normSq
  have hq_eq : q = fun w => (-1/(2*T)) * (normSq w) := by
    ext w; simp only [q]; unfold normSq dotProduct; ring
  rw [hq_eq, fderiv_const_mul (by unfold normSq dotProduct; exact h_sum_diff) (-1/(2*T)),
    _root_.smul_apply, smul_eq_mul]
  unfold normSq dotProduct
  rw [fderiv_fun_sum (fun j _ => h_comp_diff j), _root_.sum_apply]
  -- Each fderiv (w_j * w_j) at v applied to e_i = 2 * v j * δ_{ij}
  have hfderiv_sq : ∀ j : Fin 3,
      (fderiv ℝ (fun w : Fin 3 → ℝ => w j * w j) v) (Pi.single i 1) =
      2 * v j * if j = i then 1 else 0 := by
    intro j
    have hd1 : DifferentiableAt ℝ (fun w : Fin 3 → ℝ => w j) v :=
      differentiableAt_apply j v
    have hd_proj : fderiv ℝ (fun w : Fin 3 → ℝ => w j) v (Pi.single i 1) =
        if j = i then 1 else 0 := by
      rw [show (fun w : Fin 3 → ℝ => w j) =
        (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ) from rfl,
        ContinuousLinearMap.fderiv]
      simp [ContinuousLinearMap.proj_apply, Pi.single_apply]
    rw [fderiv_fun_mul hd1 hd1]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hd_proj]
    ring
  simp only [hfderiv_sq, Fin.sum_univ_three]
  fin_cases i <;> simp <;> ring

/-- Exponential decay lower bound for equilibrium Maxwellian:
    exp(-C(1+‖v‖)²) ≤ eM(v) for suitable C. Uses normSq v ≤ 3(1+‖v‖)² (sup norm). -/
private lemma equilibriumMaxwellian_exp_lower_bound (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T) :
    ∃ (C : ℝ) (K : ℕ), ∀ v : Fin 3 → ℝ,
    Real.exp (-C * (1 + ‖v‖) ^ (K : ℕ)) ≤ equilibriumMaxwellian ρ T v := by
  have hpf : 0 < ρ / (2 * π * T) ^ ((3 : ℝ) / 2) :=
    div_pos hρ (rpow_pos_of_pos (by positivity) _)
  refine ⟨3 / (2 * T) + max 0 (-Real.log (ρ / (2 * π * T) ^ ((3:ℝ)/2))), 2, fun v => ?_⟩
  unfold equilibriumMaxwellian
  set pf := ρ / (2 * π * T) ^ ((3 : ℝ) / 2)
  set M := max (0 : ℝ) (-Real.log pf)
  -- Key: normSq v ≤ 3(1+‖v‖)²
  have h_normSq : normSq v ≤ 3 * (1 + ‖v‖) ^ 2 := by
    unfold normSq dotProduct; simp only [Fin.sum_univ_three]
    have h : ∀ j : Fin 3, v j * v j ≤ ‖v‖ * ‖v‖ := fun j => by
      have : |v j| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v j
      calc v j * v j = |v j| * |v j| := (abs_mul_abs_self _).symm
        _ ≤ ‖v‖ * ‖v‖ := mul_self_le_mul_self (abs_nonneg _) this
    nlinarith [h 0, h 1, h 2, norm_nonneg v]
  have h_s1 : (1 : ℝ) ≤ (1 + ‖v‖) ^ 2 := by nlinarith [norm_nonneg v]
  have hM_nn : 0 ≤ M := le_max_left 0 _
  -- Factor: exp(-(3/(2T)+M)*s) = exp(-M*s) * exp(-3s/(2T))
  have h_split : -(3 / (2 * T) + M) * (1 + ‖v‖) ^ 2 =
      -M * (1 + ‖v‖) ^ 2 + -(3 * (1 + ‖v‖) ^ 2 / (2 * T)) := by ring
  rw [h_split, Real.exp_add]
  apply mul_le_mul
  -- exp(-M*s) ≤ pf: from M ≥ -log(pf) and s ≥ 1
  · rw [← Real.exp_log hpf]
    exact Real.exp_le_exp.mpr
      (by nlinarith [le_max_right (0:ℝ) (-Real.log pf), le_mul_of_one_le_right hM_nn h_s1])
  -- exp(-3s/(2T)) ≤ exp(-normSq/(2T)): from normSq ≤ 3s
  · apply Real.exp_le_exp.mpr
    have hT2 : (0 : ℝ) < 2 * T := by linarith
    have h_div : normSq v / (2 * T) ≤ 3 * (1 + ‖v‖) ^ 2 / (2 * T) :=
      div_le_div_of_nonneg_right h_normSq hT2.le
    have : -(3 * (1 + ‖v‖) ^ 2 / (2 * T)) = -(3 * (1 + ‖v‖) ^ 2) / (2 * T) := by ring
    rw [this]
    exact div_le_div_of_nonneg_right (neg_le_neg h_normSq) hT2.le
  · exact Real.exp_nonneg _
  · exact hpf.le

/-- Bound x^M * exp(-ax) ≤ M!/a^M via the Taylor expansion of exp. -/
private lemma pow_mul_exp_neg_le (M : ℕ) (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) :
    x ^ M * Real.exp (-a * x) ≤ M.factorial / a ^ M := by
  have hax : 0 ≤ a * x := mul_nonneg ha.le hx
  have h1 : (a * x) ^ M / M.factorial ≤ Real.exp (a * x) := by
    have := Real.sum_le_exp_of_nonneg hax (M + 1)
    calc (a * x) ^ M / ↑M.factorial
        = ∑ i ∈ Finset.range (M + 1),
            if i = M then (a * x) ^ i / ↑i.factorial else 0 := by
          simp [Finset.sum_ite_eq']
      _ ≤ ∑ i ∈ Finset.range (M + 1), (a * x) ^ i / ↑i.factorial := by
          gcongr with i hi; split_ifs with h
          · exact le_refl _
          · exact div_nonneg (pow_nonneg hax _) (Nat.cast_nonneg _)
      _ ≤ Real.exp (a * x) := this
  have h2 : (a * x) ^ M ≤ M.factorial * Real.exp (a * x) := by
    have := (div_le_iff₀ (Nat.cast_pos.mpr M.factorial_pos)).mp h1; linarith
  have h3 : x ^ M * Real.exp (-a * x) * a ^ M ≤ M.factorial := by
    calc x ^ M * Real.exp (-a * x) * a ^ M
        = (a * x) ^ M * Real.exp (-a * x) := by rw [mul_pow]; ring
      _ ≤ M.factorial * Real.exp (a * x) * Real.exp (-a * x) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ = M.factorial * (Real.exp (a * x) * Real.exp (-a * x)) := by ring
      _ = M.factorial * Real.exp (a * x + (-a * x)) := by rw [← Real.exp_add]
      _ = M.factorial := by simp
  rwa [le_div_iff₀ (pow_pos ha M)]

/-- Polynomial times Gaussian is bounded: (1+u)^M * exp(-au²) ≤ C for all u ≥ 0. -/
private lemma poly_mul_gaussian_le (M : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u → (1 + u) ^ M * Real.exp (-a * u ^ 2) ≤ C := by
  refine ⟨2 ^ M * (1 + M.factorial / a ^ M), by positivity, fun u hu => ?_⟩
  by_cases h : u ≤ 1
  · calc (1 + u) ^ M * Real.exp (-a * u ^ 2)
        ≤ 2 ^ M * 1 := by
          apply mul_le_mul
          · exact pow_le_pow_left₀ (by linarith) (by linarith) M
          · rw [← Real.exp_zero]; exact Real.exp_le_exp_of_le (by nlinarith)
          · exact Real.exp_nonneg _
          · positivity
      _ ≤ 2 ^ M * (1 + M.factorial / a ^ M) := by
          gcongr
          linarith [div_nonneg (Nat.cast_nonneg M.factorial) (pow_nonneg ha.le M)]
  · push Not at h
    have hu1 : 1 ≤ u := h.le
    have h_sq : u ≤ u ^ 2 := le_self_pow₀ hu1 two_ne_zero
    calc (1 + u) ^ M * Real.exp (-a * u ^ 2)
        ≤ (2 * u) ^ M * Real.exp (-a * u) := by
          apply mul_le_mul
          · exact pow_le_pow_left₀ (by linarith) (by linarith) M
          · exact Real.exp_le_exp_of_le (by nlinarith)
          · exact Real.exp_nonneg _
          · positivity
      _ = 2 ^ M * (u ^ M * Real.exp (-a * u)) := by ring_nf
      _ ≤ 2 ^ M * (M.factorial / a ^ M) := by
          gcongr; exact pow_mul_exp_neg_le M a ha u hu
      _ ≤ 2 ^ M * (1 + M.factorial / a ^ M) := by gcongr; linarith

/-- The equilibrium Maxwellian has Schwartz decay: all iterated velocity derivatives
    decay faster than any polynomial. Uses `norm_iteratedFDeriv_comp_le` (Faà di Bruno bound)
    with exp(q(v)) where q = -normSq/(2T) is quadratic, combined with the
    polynomial-times-Gaussian bound. -/
lemma equilibriumMaxwellian_schwartz_decay (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T) :
    ∀ (N k : ℕ), ∃ C > 0, ∀ (v : Fin 3 → ℝ),
      ‖iteratedFDeriv ℝ k (equilibriumMaxwellian ρ T) v‖ * (1 + ‖v‖) ^ N ≤ C := by
  intro N k
  set pf := ρ / (2 * π * T) ^ ((3 : ℝ) / 2)
  set q := fun v : Fin 3 → ℝ => -(normSq v) / (2 * T)
  have hpf_pos : 0 < pf := div_pos hρ (rpow_pos_of_pos (by positivity) _)
  have hq_smooth : ContDiff ℝ ⊤ q := contDiff_negNormSq_div T
  have hexpq_smooth : ContDiff ℝ ⊤ (Real.exp ∘ q) := contDiff_exp.comp hq_smooth
  have heM_eq : equilibriumMaxwellian ρ T = fun v => pf * (Real.exp ∘ q) v := by
    ext w
    unfold equilibriumMaxwellian
    rfl
  -- Step 1: Pull constant pf out of iteratedFDeriv
  have h_norm : ∀ v, ‖iteratedFDeriv ℝ k (equilibriumMaxwellian ρ T) v‖ =
      pf * ‖iteratedFDeriv ℝ k (Real.exp ∘ q) v‖ := by
    intro v
    rw [heM_eq, show (fun v => pf * (Real.exp ∘ q) v) = pf • (Real.exp ∘ q) from by
      ext w; simp [Pi.smul_apply, smul_eq_mul]]
    rw [iteratedFDeriv_const_smul_apply (hexpq_smooth.contDiffAt.of_le le_top)]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpf_pos]
  -- Step 2: Derivative bound for q (quadratic form)
  obtain ⟨c, hc_pos, hc⟩ := quadratic_iteratedFDeriv_bound T hT k
  -- Step 3: Apply norm_iteratedFDeriv_comp_le (Faà di Bruno)
  have h_comp_bound : ∀ v, ‖iteratedFDeriv ℝ k (Real.exp ∘ q) v‖ ≤
      k.factorial * Real.exp (q v) * (c * (1 + ‖v‖)) ^ k := by
    intro v
    apply norm_iteratedFDeriv_comp_le contDiff_exp hq_smooth le_top v
    · -- exp derivatives: ‖iteratedFDeriv i exp y‖ = exp(y)
      intro i _
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        show Real.exp = fun s => Real.exp (1 * s) from by ext s; simp,
        iteratedDeriv_exp_const_mul]
      simp only [one_pow, one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact le_refl _
    · exact fun i hi1 hi2 => hc v i hi1 hi2
  -- Step 4: q(v) ≤ -‖v‖²/(2T) since normSq v ≥ ‖v‖²
  have h_q_ub : ∀ v, q v ≤ -(1/(2*T)) * ‖v‖ ^ 2 := by
    intro v; simp only [q]
    rw [show -(1 / (2 * T)) * ‖v‖ ^ 2 = -(‖v‖ ^ 2 / (2 * T)) from by ring, neg_div]
    exact neg_le_neg
      (div_le_div_of_nonneg_right (norm_sq_le_normSq v) (by positivity : (0:ℝ) ≤ 2*T))
  -- Step 5: Polynomial × Gaussian bound
  obtain ⟨Cg, hCg_pos, hCg⟩ := poly_mul_gaussian_le (k + N) (1/(2*T)) (by positivity)
  refine ⟨pf * k.factorial * c ^ k * Cg, by positivity, fun v => ?_⟩
  have hv_nn : 0 ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
  rw [h_norm v]
  -- Chain the inequalities
  have step1 : pf * ‖iteratedFDeriv ℝ k (Real.exp ∘ q) v‖ * (1 + ‖v‖) ^ N ≤
      pf * (k.factorial * Real.exp (q v) * (c * (1 + ‖v‖)) ^ k) * (1 + ‖v‖) ^ N := by
    gcongr; exact h_comp_bound v
  have step2 : pf * (k.factorial * Real.exp (q v) * (c * (1 + ‖v‖)) ^ k) *
      (1 + ‖v‖) ^ N =
      pf * k.factorial * c ^ k * (Real.exp (q v) * (1 + ‖v‖) ^ (k + N)) := by
    rw [mul_pow]; ring
  have step3 : Real.exp (q v) * (1 + ‖v‖) ^ (k + N) ≤
      (1 + ‖v‖) ^ (k + N) * Real.exp (-(1/(2*T)) * ‖v‖ ^ 2) :=
    calc Real.exp (q v) * (1 + ‖v‖) ^ (k + N)
        ≤ Real.exp (-(1/(2*T)) * ‖v‖ ^ 2) * (1 + ‖v‖) ^ (k + N) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp_of_le (h_q_ub v)) (pow_nonneg hv_nn _)
      _ = (1 + ‖v‖) ^ (k + N) * Real.exp (-(1/(2*T)) * ‖v‖ ^ 2) := by ring
  have step4 : (1 + ‖v‖) ^ (k + N) * Real.exp (-(1/(2*T)) * ‖v‖ ^ 2) ≤ Cg :=
    hCg ‖v‖ (norm_nonneg v)
  linarith [mul_le_mul_of_nonneg_left (le_trans step3 step4)
    (by positivity : (0:ℝ) ≤ pf * k.factorial * c ^ k)]

/-- Polynomial log growth bound for equilibrium Maxwellian:
    |log(eM(v))| ≤ C*(1+‖v‖)² for suitable C. -/
lemma equilibriumMaxwellian_log_bound (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T) :
    ∃ (C_log : ℝ) (K_log : ℕ), ∀ v : Fin 3 → ℝ,
    |Real.log (equilibriumMaxwellian ρ T v)| ≤ C_log * (1 + ‖v‖) ^ K_log := by
  obtain ⟨C_log, K_log, hbound⟩ := schwartz_log_bound
    (fun _ v => equilibriumMaxwellian_pos ρ T hρ hT v)
    ⟨fun N {k} _ => (equilibriumMaxwellian_schwartz_decay ρ T hρ hT N k).imp
      fun C hC => ⟨hC.1, fun _ v => hC.2 v⟩,
     fun N i => ⟨1, one_pos, fun x v => by
      simp only [torusGradX, periodicLift]
      have : (fun y => equilibriumMaxwellian ρ T v) ∘ torusMk =
          fun _ => equilibriumMaxwellian ρ T v := by ext; rfl
      rw [this]; simp⟩⟩
    ((equilibriumMaxwellian_exp_lower_bound ρ T hρ hT).imp
      fun C hC => hC.imp fun K hCK => fun _ => hCK)
  exact ⟨C_log, K_log, fun v => hbound default v⟩

/-- Integral of vᵢ * equilibriumMaxwellian is 0 by odd symmetry. -/
lemma integral_coord_mul_equilibriumMaxwellian_eq_zero (ρ T : ℝ) (i : Fin 3) :
    ∫ v : Fin 3 → ℝ, v i * equilibriumMaxwellian ρ T v = 0 := by
  have h_odd : ∀ v : Fin 3 → ℝ, (-v) i * equilibriumMaxwellian ρ T (-v) =
      -(v i * equilibriumMaxwellian ρ T v) := by
    intro v; simp [Pi.neg_apply, equilibriumMaxwellian, normSq, dotProduct]
  have h_neg : (fun v : Fin 3 → ℝ => (-v) i * equilibriumMaxwellian ρ T (-v)) =
      (fun v => -(v i * equilibriumMaxwellian ρ T v)) := funext h_odd
  have h := MeasureTheory.integral_neg_eq_self
    (fun v : Fin 3 → ℝ => v i * equilibriumMaxwellian ρ T v)
    (μ := MeasureTheory.MeasureSpace.volume)
  rw [h_neg, MeasureTheory.integral_neg] at h
  linarith

/-- The integral of the equilibrium Maxwellian equals the density ρ:
    ∫ ρ/(2πT)^{3/2} exp(-|v|²/(2T)) dv = ρ.
    Proof: factor exp as product of 1D Gaussians, apply Fubini, then
    integral_gaussian gives √(2πT) per coordinate, so the product is (2πT)^{3/2}
    which cancels the prefactor. -/
lemma integral_equilibriumMaxwellian (ρ T : ℝ) (hT : 0 < T) :
    ∫ v : Fin 3 → ℝ, equilibriumMaxwellian ρ T v = ρ := by
  unfold equilibriumMaxwellian
  rw [integral_const_mul]
  -- Factor the exponential as a product
  have h_factor : (fun v : Fin 3 → ℝ => exp (-(normSq v) / (2 * T))) =
      (fun v => ∏ i : Fin 3, exp (-(1/(2*T)) * (v i)^2)) := by
    ext v; rw [← exp_sum]; congr 1
    simp only [normSq, dotProduct, Fin.sum_univ_three, sq]; ring
  rw [h_factor]
  -- Apply Fubini: ∫ ∏ fᵢ(vᵢ) = ∏ ∫ fᵢ
  have h_fubini : ∫ v : Fin 3 → ℝ, ∏ i : Fin 3, exp (-(1/(2*T)) * (v i)^2) =
      ∏ i : Fin 3, ∫ x : ℝ, exp (-(1/(2*T)) * x^2) := by
    erw [← MeasureTheory.integral_fintype_prod_eq_prod]; rfl
  rw [h_fubini]
  -- Each 1D integral: ∫ exp(-bx²) = √(π/b) with b = 1/(2T)
  have h_gauss : ∫ x : ℝ, exp (-(1/(2*T)) * x^2) = sqrt (π / (1/(2*T))) :=
    integral_gaussian _
  simp only [Fin.prod_univ_three, h_gauss]
  -- Simplify π / (1/(2T)) = 2πT
  have h_simp : π / (1/(2*T)) = 2 * π * T := by field_simp
  rw [h_simp]
  -- √(2πT)³ = (2πT)^(3/2)
  have h2piT_pos : (0:ℝ) < 2 * π * T := by positivity
  have h_sqrt_cube : sqrt (2 * π * T) * sqrt (2 * π * T) * sqrt (2 * π * T) =
      (2 * π * T) ^ ((3:ℝ)/2) := by
    rw [show (3:ℝ)/2 = 1/2 + 1/2 + 1/2 from by ring]
    rw [rpow_add h2piT_pos, rpow_add h2piT_pos]
    simp [sqrt_eq_rpow]
  rw [h_sqrt_cube]
  exact div_mul_cancel₀ ρ (ne_of_gt (rpow_pos_of_pos h2piT_pos _))

/-- **Non-vacuousness of CoulombConcreteTheorem42.**

    The equilibrium Maxwellian f(v) = ρ/(2πT)^{3/2} exp(-|v|²/(2T)) with
    E = 0, B = 0 satisfies all 13 hypotheses of the main theorem. This
    proves the theorem is non-vacuous: at least one instance exists.

    **Proof status: all 10 non-trivial goals fully proved. 0 sorry's.**

    Why each hypothesis holds for the equilibrium:
    - (3) hf_pos: ρ/(2πT)^{3/2} > 0 and exp > 0 ⇒ f > 0  ✓
    - (4) hf_smooth_v: composition of smooth functions (const, exp, polynomial)  ✓
    - (5) hf_smooth_x: f is spatially constant ⇒ periodicLift is constant ⇒ C^∞  ✓
    - (6) hB_smooth: B = 0, same argument as (5)  ✓
    - (7) hSchwartz: Gaussian is Schwartz class via Faà di Bruno + poly×Gaussian bound  ✓
    - (8) hGradBound: ∂eM/∂vᵢ = -(vᵢ/T)·eM, bound |vᵢ| ≤ 1+‖v‖  ✓
    - (9) hVlasov: A(z)·z = 0 (projection annihilation) ⇒ integrand vanishes  ✓
    - (10) hAmpere: ∇×0 = 0, ∫ vᵢ eM dv = 0 by odd symmetry  ✓
    - (11) hGauss: ∇·0 = 0 = ∫eM - ρIon (simp closes)  ✓
    - (12) hDivB: ∇·0 = 0  ✓ -/
theorem CoulombConcreteTheorem42_nonvacuous (ν T ρIon : ℝ)
    (_hν : 0 < ν) (hT : 0 < T) (hρ_ion : 0 < ρIon) :
    ∃ (f : Torus3 → (Fin 3 → ℝ) → ℝ) (E B : Torus3 → Fin 3 → ℝ),
    (∀ x v, 0 < f x v) ∧                                                  -- (3)
    (∀ x, ContDiff ℝ 3 (f x)) ∧                                           -- (4)
    (∀ v, ContDiff ℝ 2 (periodicLift (fun x => f x v))) ∧                 -- (5)
    (∀ i, ContDiff ℝ 2 (periodicLift (fun x => B x i))) ∧                 -- (6)
    UniformSchwartzDecay f ∧                                                -- (7)
    (∃ Cg Kg, ∀ x v i,
      |fderiv ℝ (f x) v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f x v) ∧ -- (8)
    (∀ x v, dotProduct v (torusGradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator coulombKernel (f x) v) ∧                         -- (9)
    (∀ x, torusCurlX B x = fun i => ∫ v, v i * f x v) ∧                  -- (10)
    (∀ x, torusDivX E x = (∫ v, f x v) - ρIon) ∧                        -- (11)
    (∀ x, torusDivX B x = 0) := by                                        -- (12)
  refine ⟨fun _ => equilibriumMaxwellian ρIon T,
         fun _ => 0, fun _ => 0,
         fun _ v => equilibriumMaxwellian_pos ρIon T hρ_ion hT v,  -- (3) ✓
         ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (4) hf_smooth_v: equilibriumMaxwellian is C^∞
  · intro _
    unfold equilibriumMaxwellian
    apply ContDiff.mul contDiff_const
    apply ContDiff.exp
    apply ContDiff.div_const
    apply ContDiff.neg
    unfold normSq dotProduct
    exact ContDiff.sum fun i _ =>
      (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)
  -- (5) hf_smooth_x: periodicLift of constant is C^∞
  · intro v
    simp only [periodicLift]
    exact contDiff_const
  -- (6) hB_smooth: periodicLift of zero is C^∞
  · intro i
    simp only [periodicLift, Pi.zero_apply]
    exact contDiff_const
  -- (7) hSchwartz: Gaussian is UniformSchwartzDecay
  · constructor
    · -- hDecay: ‖iteratedFDeriv ℝ k eM v‖ * (1+‖v‖)^N ≤ C
      intro N k hk_le
      obtain ⟨C, hC, hbound⟩ :=
        equilibriumMaxwellian_schwartz_decay ρIon T hρ_ion hT N k
      exact ⟨C, hC, fun _ v => hbound v⟩
    · -- hGradDecay: spatial gradient of constant function is 0
      intro N i
      refine ⟨1, one_pos, fun x v => ?_⟩
      simp only [torusGradX, periodicLift]
      have : (fun y => equilibriumMaxwellian ρIon T v) ∘ torusMk =
          fun _ => equilibriumMaxwellian ρIon T v := by ext; rfl
      rw [this]; simp
  -- (8) hGradBound: |∂eM/∂vᵢ| = |vᵢ/T| · eM ≤ (1+‖v‖)/T · eM
  · refine ⟨1 / T, 1, fun _ v i => ?_⟩
    rw [fderiv_equilibriumMaxwellian ρIon T hT v i]
    have hpos := equilibriumMaxwellian_pos ρIon T hρ_ion hT v
    rw [abs_mul, abs_neg, abs_div, abs_of_pos hT, abs_of_pos hpos, pow_one]
    have hvi : |v i| ≤ 1 + ‖v‖ :=
      le_trans (norm_le_pi_norm v i) (le_add_of_nonneg_left (by norm_num))
    calc |v i| / T * equilibriumMaxwellian ρIon T v
        ≤ (1 + ‖v‖) / T * equilibriumMaxwellian ρIon T v := by
          apply mul_le_mul_of_nonneg_right
          · exact div_le_div_of_nonneg_right hvi hT.le
          · exact hpos.le
      _ = 1 / T * (1 + ‖v‖) * equilibriumMaxwellian ρIon T v := by ring
  -- (9) hVlasov: Vlasov equation (Maxwellian in kernel of Landau operator)
  · intro x v
    -- Spatial gradient of constant is 0
    have hgrad_zero : ∀ i : Fin 3,
        torusGradX (fun y => equilibriumMaxwellian ρIon T v) x i = 0 := by
      intro i; simp only [torusGradX, periodicLift]
      have : (fun y => equilibriumMaxwellian ρIon T v) ∘ torusMk =
          fun _ => equilibriumMaxwellian ρIon T v := by ext; rfl
      rw [this]; simp
    -- LandauOperator eM v = 0 because integrand vanishes
    suffices h : LandauOperator coulombKernel (equilibriumMaxwellian ρIon T) v = 0 by
      have hd : v ⬝ᵥ (fun i => torusGradX (fun y =>
          equilibriumMaxwellian ρIon T v) x i) = 0 := by
        simp only [dotProduct, hgrad_zero, mul_zero, Finset.sum_const_zero]
      simp only [hd, h, mul_zero, zero_add]
      unfold cross; simp [dotProduct, vGrad, Fin.sum_univ_three, mul_zero,
        zero_mul, sub_self]
    -- The integrand is 0 for all w: A(v-w) · (eM(w)·∇eM(v) - eM(v)·∇eM(w)) = 0
    -- because the vector argument is proportional to (v-w) and A(z)·z = 0
    unfold LandauOperator vDiv
    -- Show the flux function is identically 0
    have hflux_zero : ∀ v', (∫ w, mulVec (landauMatrix coulombKernel (v' - w))
        (equilibriumMaxwellian ρIon T w • vGrad (equilibriumMaxwellian ρIon T) v' -
         equilibriumMaxwellian ρIon T v' • vGrad (equilibriumMaxwellian ρIon T) w)) = 0 := by
      intro v'
      -- Show integrand is 0 pointwise
      have h_integrand : ∀ w, mulVec (landauMatrix coulombKernel (v' - w))
          (equilibriumMaxwellian ρIon T w • vGrad (equilibriumMaxwellian ρIon T) v' -
           equilibriumMaxwellian ρIon T v' • vGrad (equilibriumMaxwellian ρIon T) w) = 0 := by
        intro w
        -- The bracket vector = (-eM(v')*eM(w)/T) • (v' - w)
        have hbracket : equilibriumMaxwellian ρIon T w • vGrad (equilibriumMaxwellian ρIon T) v' -
            equilibriumMaxwellian ρIon T v' • vGrad (equilibriumMaxwellian ρIon T) w =
            (-(equilibriumMaxwellian ρIon T v' * equilibriumMaxwellian ρIon T w / T)) •
              (v' - w) := by
          ext i
          simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, vGrad,
            fderiv_equilibriumMaxwellian ρIon T hT v' i,
            fderiv_equilibriumMaxwellian ρIon T hT w i]
          ring
        rw [hbracket, Matrix.mulVec_smul, landauMatrix_mulVec_self, smul_zero]
      simp [h_integrand]
    -- vDiv of zero function = 0
    have : ∀ i, fderiv ℝ (fun w => (0 : Fin 3 → ℝ) i) v (Pi.single i 1) = 0 := by
      intro i; simp
    conv => arg 2; rw [show (0:ℝ) = ν * 0 from by ring]
    simp only [hflux_zero]
    simp
  -- (10) hAmpere: Ampere's law (curl 0 = ∫ vᵢ eM dv)
  · intro x
    ext i
    simp only [torusCurlX, periodicLift, Pi.zero_apply]
    -- fderiv of (fun z => 0) ∘ torusMk = fderiv of constant = 0
    have hzero : ∀ (j : Fin 3) (p : Fin 3 → ℝ),
        fderiv ℝ (fun y => ((fun _ : Torus3 => (0 : ℝ)) ∘ torusMk) y) p (Pi.single j 1) = 0 := by
      intro j p
      have : ((fun _ : Torus3 => (0 : ℝ)) ∘ torusMk) = fun _ => (0 : ℝ) := by ext; rfl
      rw [show (fun y => ((fun _ : Torus3 => (0 : ℝ)) ∘ torusMk) y) =
          (fun _ => (0 : ℝ)) from by ext; rfl]
      simp
    simp only [hzero, sub_self]
    -- ∫ vᵢ * eM = 0 by odd symmetry of Gaussian
    have hint := integral_coord_mul_equilibriumMaxwellian_eq_zero ρIon T i
    fin_cases i <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- (11) hGauss: Gauss's law
  · intro x
    simp only [torusDivX, periodicLift]
    -- Each summand: fderiv of (fun z => 0 i) ∘ torusMk = 0
    have hzero : ∀ j : Fin 3,
        fderiv ℝ (fun y => ((fun z : Torus3 => (0 : Fin 3 → ℝ) j) ∘ torusMk) y)
          (torusMk_surjective x).choose (Pi.single j 1) = 0 := by
      intro j
      rw [show (fun y => ((fun z : Torus3 => (0 : Fin 3 → ℝ) j) ∘ torusMk) y) =
          (fun _ => (0 : ℝ)) from by ext; simp]
      simp
    simp only [hzero, Finset.sum_const_zero]
    -- ∫ eM(v) dv = ρIon (Gaussian normalization)
    linarith [integral_equilibriumMaxwellian ρIon T hT]
  -- (12) hDivB: divergence of B = 0
  · intro x
    simp only [torusDivX, periodicLift]
    have hzero : ∀ j : Fin 3,
        fderiv ℝ (fun y => ((fun z : Torus3 => (0 : Fin 3 → ℝ) j) ∘ torusMk) y)
          (torusMk_surjective x).choose (Pi.single j 1) = 0 := by
      intro j
      rw [show (fun y => ((fun z : Torus3 => (0 : Fin 3 → ℝ) j) ∘ torusMk) y) =
          (fun _ => (0 : ℝ)) from by ext; simp]
      simp
    simp only [hzero, Finset.sum_const_zero]

/-- **Full round-trip for CoulombConcreteTheorem42.**

    Not only are the 13 hypotheses simultaneously satisfiable
    (`CoulombConcreteTheorem42_nonvacuous`), but applying the main theorem
    to the equilibrium Maxwellian witnesses produces the expected
    conclusion: f is a global Maxwellian, E = 0, B = const, with unique
    equilibrium temperature.

    This closes the loop: the theorem is non-vacuous AND the conclusion
    actually holds for a concrete physical configuration. -/
theorem CoulombConcreteTheorem42_roundtrip (ν T ρIon : ℝ)
    (hν : 0 < ν) (hT : 0 < T) (hρ_ion : 0 < ρIon) :
    ∃ (f : Torus3 → (Fin 3 → ℝ) → ℝ) (E B : Torus3 → Fin 3 → ℝ),
    ∃ (T_eq : ℝ) (B₀ : Fin 3 → ℝ), 0 < T_eq ∧
    (∀ x v, f x v = equilibriumMaxwellian ρIon T_eq v) ∧
    (∀ x, E x = 0) ∧
    (∀ x, B x = B₀) ∧
    (∀ T', 0 < T' →
      (∀ v, equilibriumMaxwellian ρIon T' v =
        equilibriumMaxwellian ρIon T_eq v) →
      T' = T_eq) := by
  obtain ⟨f, E, B, hf_pos, hf_sv, hf_sx, hB_s, hSch, hGrad,
         hVlasov, hAmpere, hGauss, hDivB⟩ :=
    CoulombConcreteTheorem42_nonvacuous ν T ρIon hν hT hρ_ion
  obtain ⟨T_eq, B₀, hT_pos, hf_eq, hE_zero, hB_const⟩ :=
    CoulombConcreteTheorem42 f E B ν ρIon hν hρ_ion hf_pos hf_sv hf_sx
      hB_s hSch hGrad hVlasov hAmpere hGauss hDivB
  exact ⟨f, E, B, T_eq, B₀, hT_pos, hf_eq, hE_zero, hB_const,
    fun T' hT' h_eq =>
      equilibriumMaxwellian_T_injective ρIon T' T_eq hρ_ion hT' hT_pos h_eq⟩

end VML
