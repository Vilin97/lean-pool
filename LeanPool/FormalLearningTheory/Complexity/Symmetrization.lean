/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Basic
import LeanPool.FormalLearningTheory.Complexity.Generalization
import LeanPool.FormalLearningTheory.Complexity.Rademacher
import LeanPool.FormalLearningTheory.PureMath.Exchangeability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# Symmetrization and Ghost Sample Infrastructure

Reusable symmetrization/ghost sample machinery for uniform convergence bounds.
This file provides the symmetrization argument (SSBD Chapter 4 / 6, Kakade-Tewari Lecture 19)
that converts a one-sided uniform convergence question into a double-sample question,
then bounds the double-sample event via exchangeability + growth function.

## Main results

- `hoeffding_one_sided` : one-sided Hoeffding for bounded [0,1] losses
- `symmetrization_step` : P[∃h: TrueErr-EmpErr ≥ ε] ≤ 2·P_{double}[∃h: EmpErr'-EmpErr ≥ ε/2]
- `double_sample_pattern_bound` : double-sample bound via exchangeability + growth function
- `symmetrization_uc_bound` : two-sided UC bound 4·GF(C,2m)·exp(-mε²/8)
- `growth_exp_le_delta` : arithmetic: sample complexity makes the UC bound ≤ δ

## Infrastructure

- `DoubleSampleMeasure` : D^m ⊗ D^m as the product of two independent pi measures
- `MergedSample` : Fin (2*m) → X with the Fin.append isomorphism
- `SplitMeasure` : uniform measure over (2m choose m) splits for exchangeability argument

## Design notes

All theorems use the STANDARD Approach A (exchangeability + permutation) for T3,
NOT the relaxed iid Rademacher approach. This is the structurally correct argument
that avoids introducing unnecessary independence assumptions.
-/

universe u v

open MeasureTheory ENNReal

/-! ## Helper Definitions (DoubleSampleMeasure, ValidSplit, etc. in MathLib.Exchangeability) -/

/-! ## T1: One-sided Hoeffding Inequality -/

/-- One-sided Hoeffding: for iid Bernoulli(p) draws, the empirical average
    undershoots the mean by ≥ t with probability ≤ exp(-2mt²).

    **Proof strategy (3 steps):**

    1. **MGF bound (Hoeffding's lemma):** For X ∈ [0,1] with E[X] = p,
       E[exp(s(X-p))] ≤ exp(s²/8).
       - Adapt from `cosh_le_exp_sq_half` infrastructure in Rademacher.lean.
       - Key: convexity of exp on [0,1] gives E[exp(sX)] ≤ p·exp(s) + (1-p)·exp(0),
         then the s²/8 bound follows from ln(1 + x) ≤ x and Taylor expansion.
       ```
       have mgf_bound : ∀ (s : ℝ),
         ∫ x, Real.exp (s * (indicator x - p)) ∂D ≤ Real.exp (s^2 / 8) := by ...
       ```

    2. **Product independence:** E[exp(s·∑(X_i-p))] = ∏ E[exp(s(X_i-p))] ≤ exp(ms²/8).
       - Uses `MeasureTheory.Measure.pi` independence structure.
       - Needs: `Measure.pi` integral factorization for product of functions.
       - MEASURABILITY: `fun xs => Real.exp (s * ∑ i, f (xs i))` is measurable
         (composition of measurable functions).
       ```
       have product_bound : ∀ (s : ℝ),
         ∫ xs, Real.exp (s * ∑ i, (indicator (xs i) - p)) ∂Measure.pi (fun _ => D)
         ≤ Real.exp (m * s^2 / 8) := by ...
       ```

    3. **Exponential Markov + optimize:** P[∑(X_i-p) ≤ -mt]
       = P[exp(-s·∑(X_i-p)) ≥ exp(smt)] ≤ exp(-smt + ms²/8).
       Optimize over s: set s = 4t to get ≤ exp(-2mt²).
       - Uses Markov's inequality in ENNReal form.
       - CAST ISSUE: Markov gives ENNReal bound, need to convert exp(-2mt²) between
         ENNReal.ofReal and the measure value.
       ```
       have markov_step : ∀ (s : ℝ) (hs : 0 < s),
         Measure.pi (fun _ => D) {xs | ∑ i, (indicator (xs i) - p) ≤ -(m : ℝ) * t}
         ≤ ENNReal.ofReal (Real.exp (-(s * m * t) + m * s^2 / 8)) := by ...
       have optimize : Real.exp (-(4*t * m * t) + m * (4*t)^2 / 8)
         = Real.exp (-2 * m * t^2) := by ring_nf
       ```

    **CAST ISSUES to watch:**
    - `m : ℕ` needs cast to `ℝ` in the exponent: `(m : ℝ)`
    - `EmpiricalError` returns `ℝ`, `TrueErrorReal` returns `ℝ`, good — no ENNReal gap
    - The measure value is `ENNReal`, the bound `exp(-2mt²)` is `ℝ≥0∞` via `ENNReal.ofReal`

    **References:** SSBD Lemma B.3, Hoeffding (1963) -/
theorem hoeffding_one_sided {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (m : ℕ) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (_ht1 : t ≤ 1)
    (hmeas : MeasurableSet {x | h x ≠ c x}) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
        (zeroOneLoss Bool) ≤ TrueErrorReal X h c D - t}
    ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := by
  -- Abbreviations
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set p := TrueErrorReal X h c D with hp_def
  -- The indicator: zeroOneLoss Bool (h x) (c x)
  set indicator : X → ℝ := fun x => zeroOneLoss Bool (h x) (c x) with hind_def
  -- The negated centered variable for each coordinate: p - indicator(x_i)
  -- Z_i(xs) = p - indicator(xs i), bounded in [p-1, p], mean 0
  set Z : Fin m → (Fin m → X) → ℝ := fun i xs => p - indicator (xs i) with hZ_def
  -- Step 1: Show the target set is contained in the Hoeffding event set
  -- EmpErr ≤ p - t  ↔  (1/m)∑ indicator(xs i) ≤ p - t
  --                 ↔  ∑ indicator(xs i) ≤ m(p - t)
  --                 ↔  m·p - ∑ indicator(xs i) ≥ m·t
  --                 ↔  ∑ (p - indicator(xs i)) ≥ m·t
  --                 ↔  ∑ Z_i ≥ m·t
  -- The Hoeffding bound: μ.real {xs | m*t ≤ ∑ Z_i(xs)} ≤ exp(-(m*t)²/(2·∑1 / 4))
  --                    = exp(-m²t²/(m/2)) = exp(-2mt²)
  -- Step 2: Use monotonicity to bound the ENNReal measure by the real measure bound
  -- μ S ≤ ENNReal.ofReal (μ.real S) when μ.real S ≥ 0, via ofReal_measureReal
  -- and μ.real S ≤ exp bound by Hoeffding
  -- Key: the bound exp(-2mt²) is non-negative, so this works
  -- We bound μ(target set) ≤ μ(entire space) ≤ 1 ≤ ... No, we need the actual bound.
  -- Use: μ S = ENNReal.ofReal(μ.real S) when S has finite measure (always true for prob measure)
  -- Then: ENNReal.ofReal(μ.real S) ≤ ENNReal.ofReal(exp bound) by monotonicity of ofReal
  -- The challenge is showing μ.real S ≤ exp(-2mt²) using Mathlib's Hoeffding.
  -- For now, we use a direct probability bound.
  -- Direct bound: the set has probability ≤ 1, and exp(-2mt²) ≤ 1,
  -- so we need the actual Hoeffding bound.
  -- Apply the bound via the sub-Gaussian / Hoeffding machinery.
  -- First bound: μ S ≤ 1 (probability measure)
  -- Convert the ENNReal bound: μ S ≤ ENNReal.ofReal(exp(-2mt²))
  -- Use: μ S = ENNReal.ofReal(μ.real S) and μ.real S ≤ exp(-2mt²)
  -- Bridge from ENNReal to ℝ and back
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  -- The target set
  set S := {xs : Fin m → X | EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
      (zeroOneLoss Bool) ≤ p - t} with hS_def
  -- Step: Show S ⊆ {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs}
  have h_set_sub : S ⊆ {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs} := by
    intro xs hxs
    simp only [Set.mem_setOf_eq] at hxs ⊢
    simp only [hZ_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    -- hxs : EmpiricalError ... ≤ p - t
    -- Unfold EmpiricalError in hxs
    simp only [hS_def, Set.mem_setOf_eq, EmpiricalError,
      Nat.pos_iff_ne_zero.mp hm, ↓reduceIte] at hxs
    -- hxs should now be: (∑ i, zeroOneLoss Bool (h (xs i)) (c (xs i))) / ↑m ≤ p - t
    have h_div : (∑ i : Fin m, zeroOneLoss Bool (h (xs i)) (c (xs i))) / (m : ℝ) ≤ p - t := hxs
    rw [div_le_iff₀ hm_pos] at h_div
    linarith
  -- Step: bound μ S ≤ μ {xs | m*t ≤ ∑ Z_i xs}
  calc μ S
      ≤ μ {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs} := by
        exact MeasureTheory.measure_mono h_set_sub
    _ = ENNReal.ofReal (μ.real {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs}) := by
        rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        -- Need: μ.real {xs | m*t ≤ ∑ Z_i xs} ≤ exp(-2mt²)
        -- This is the Hoeffding inequality for the sum of Z_i.
        -- Each Z_i is bounded in [p-1, p] (width 1), centered (mean 0),
        -- so sub-Gaussian with parameter (1 / 2)² = 1 / 4.
        -- Under Measure.pi, the Z_i are independent.
        -- Hoeffding: μ.real {xs | ε ≤ ∑ Z_i} ≤ exp(-ε²/(2·∑c_i))
        -- = exp(-(mt)²/(2·m·(1 / 4))) = exp(-2mt²)
        -- Use Mathlib's measure_sum_ge_le_of_iIndepFun
        -- For this we need:
        -- (a) iIndepFun Z μ
        -- (b) HasSubgaussianMGF (Z i) (1 / 4) μ for each i
        -- (c) ε = m*t ≥ 0
        -- The sum bound gives exp(-(mt)²/(2·∑_{i∈univ} 1 / 4)) = exp(-m²t²/(m/2)) = exp(-2mt²)
        -- However, wiring (a) and (b) requires substantial Mathlib plumbing.
        -- We proceed via a direct argument using the probability measure bound.
        -- Direct approach: use HasSubgaussianMGF.measure_ge_le after constructing
        -- the sum as a single sub-Gaussian variable.
        -- Alternative: bound directly using measure_ge_le_exp_mul_mgf and optimize.
        -- For now, we apply the Hoeffding bound structurally.
        -- The Z_i factor through coordinates: Z i xs = p - indicator (xs i)
        -- Under Measure.pi (fun _ => D), coordinate projections are iIndepFun.
        -- Then Z_i = g ∘ (eval i) where g x = p - indicator x, so Z_i are independent.
        -- Step (a): independence
        -- iIndepFun_pi: given X_i : Ω_i → 𝓧_i AEMeasurable, then
        --   fun i ω ↦ X_i (ω i) is iIndepFun under Measure.pi
        -- Our Z_i = (fun x => p - indicator x) applied to coordinate i
        -- So Z i = (fun x => p - indicator x) ∘ (fun xs => xs i)
        -- = fun xs => (fun x => p - indicator x) (xs i)
        -- This matches the pattern of iIndepFun_pi with X_i := fun x => p - indicator x
        -- and Ω_i := X, μ_i := D
        -- Actually iIndepFun_pi gives iIndepFun (fun i ω ↦ X_base (ω i)) (Measure.pi μ)
        -- where X_base : (i : ι) → Ω i → 𝓧 i.
        -- In our case X_base is constant: X_base i = fun x => p - indicator x for all i.
        -- So iIndepFun_pi (with mX = fun _ => aemeasurable_of_indicator)
        -- gives iIndepFun (fun i xs => p - indicator (xs i)) μ
        -- = iIndepFun Z μ. ✓
        -- Step (b): sub-Gaussian
        -- Each Z i has the same distribution as p - indicator under D.
        -- indicator ∈ {0, 1} ⊆ [0, 1], so p - indicator ∈ [p-1, p] ⊆ [-1, 1].
        -- Also E[Z i] = p - E[indicator] = p - p = 0 (centered).
        -- By hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero with a = p-1, b = p:
        --   HasSubgaussianMGF (Z i) ((‖p-(p-1)‖₊/2)²) μ
        --   = HasSubgaussianMGF (Z i) ((‖1‖₊/2)²) μ
        --   = HasSubgaussianMGF (Z i) ((1 / 2)²) μ
        --   = HasSubgaussianMGF (Z i) (1 / 4) μ
        -- Step (c): ε = m*t ≥ 0 since m > 0 and t > 0
        -- Apply measure_sum_ge_le_of_iIndepFun:
        --   μ.real {xs | mt ≤ ∑ Z_i xs} ≤ exp(-(mt)²/(2·∑ 1 / 4))
        --   = exp(-m²t²/(m/2)) = exp(-2mt²)
        -- The algebra: -(mt)²/(2·∑_{i∈Fin m} 1 / 4) = -m²t²/(2·m/4) = -m²t²·4/(2m) = -2mt²
        -- This matches our target exp(-2·m·t²).
        -- IMPLEMENTATION NOTE: The full Mathlib wiring requires showing:
        -- 1. AEMeasurability of indicator under D
        -- 2. AEMeasurability of Z_i under μ_pi
        -- 3. IsProbabilityMeasure (Measure.pi (fun _ => D))
        -- 4. Integral of Z_i under μ_pi = 0
        -- 5. Boundedness of Z_i in [p-1, p]
        -- 6. All the coercions between NNReal and Real
        -- We now proceed with the formal proof.
        -- First, note that μ is a probability measure on Fin m → X
        have : MeasureTheory.IsProbabilityMeasure μ := by
          rw [hμ_def]; infer_instance
        -- The bound follows from the general Hoeffding inequality.
        -- We bound the measure of the tail event using the exponential Markov inequality
        -- applied to the sum of independent bounded random variables.
        -- Since direct Mathlib wiring of sub-Gaussian + iIndepFun_pi is extremely
        -- involved, we use a self-contained argument via measure_le_one and
        -- the deterministic bound.
        -- Key mathematical fact: for a probability measure, μ.real S ≤ 1.
        -- And exp(-2mt²) ≤ 1 when m*t² ≥ 0, which always holds.
        -- But we need the TIGHT bound, not just ≤ 1.
        -- The tight bound requires the full Hoeffding argument.
        -- We apply measure_sum_ge_le_of_iIndepFun from Mathlib.
        -- Define the base random variable on X
        set g : X → ℝ := fun x => p - indicator x with hg_def
        -- g is bounded: indicator ∈ {0,1} ⊆ [0,1], so g ∈ [p-1, p]
        -- The Z_i are: Z i xs = g (xs i)
        have hZ_eq : ∀ i : Fin m, ∀ xs : Fin m → X, Z i xs = g (xs i) := by
          intros i xs; simp [hZ_def, hg_def]
        -- Show g is bounded in [0, 1] → indicator in [0,1]
        have h_ind_bound : ∀ x : X, indicator x ∈ Set.Icc (0 : ℝ) 1 := by
          intro x
          simp only [hind_def, zeroOneLoss]
          split
          · exact ⟨le_refl 0, zero_le_one⟩
          · exact ⟨zero_le_one, le_refl 1⟩
        -- g bounded in [p-1, p]
        have h_g_bound : ∀ x : X, g x ∈ Set.Icc (p - 1) p := by
          intro x
          have hix := h_ind_bound x
          simp only [hg_def, Set.mem_Icc] at hix ⊢
          constructor <;> linarith [hix.1, hix.2]
        -- Now we need HasSubgaussianMGF for g under D, and independence for Z under μ.
        -- This requires showing AEMeasurable g D, which needs measurability of indicator.
        -- indicator x = if h x = c x then 0 else 1 = indicator of {x | h x ≠ c x}
        -- which is measurable when {x | h x ≠ c x} is measurable (given by hmeas).
        -- For the sub-Gaussian bound, we use hasSubgaussianMGF_of_mem_Icc on g under D.
        -- This gives HasSubgaussianMGF (fun x => g x - ∫ x, g x ∂D) ((‖p-(p-1)‖₊/2)²) D
        -- = HasSubgaussianMGF (fun x => g x - (p - p)) ((1 / 2)²) D   [since ∫ indicator = p]
        -- = HasSubgaussianMGF g (1 / 4) D   [since g is already centered]
        -- Then by iIndepFun_pi, Z_i are independent under μ.
        -- Then by HasSubgaussianMGF.of_map, Z_i are sub-Gaussian under μ.
        -- Then measure_sum_ge_le_of_iIndepFun applies.
        -- Given the extreme complexity of this full wiring, let us bound directly.
        -- We use the trivial bound for now and then tighten.
        -- Actually, let's try the Mathlib route properly.
        -- Step A: AEMeasurability of indicator
        have h_ind_meas : Measurable indicator := by
          simp only [hind_def, zeroOneLoss]
          have hmeas_eq : MeasurableSet {a : X | h a = c a} := by
            have : {a : X | h a = c a} = {a : X | h a ≠ c a}ᶜ := by
              ext x; simp
            rw [this]; exact hmeas.compl
          exact Measurable.ite hmeas_eq measurable_const measurable_const
        -- Step B: AEMeasurability of g
        have h_g_meas : Measurable g := by
          exact measurable_const.sub h_ind_meas
        -- Step C: HasSubgaussianMGF for g under D
        -- g has integral ∫ g ∂D = p - ∫ indicator ∂D = p - p = 0
        -- So g is centered. Use hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero.
        have h_g_ae_bound : ∀ᵐ x ∂D, g x ∈ Set.Icc (p - 1) p := by
          exact Filter.Eventually.of_forall h_g_bound
        -- Integral of indicator under D = TrueErrorReal = p
        -- indicator x = 1 iff h x ≠ c x, so ∫ indicator ∂D = (D {x | h x ≠ c x}).toReal = p
        have h_int_ind : ∫ x, indicator x ∂D = p := by
          simp only [hind_def, zeroOneLoss, hp_def, TrueErrorReal, TrueError]
          -- ∫ x, (if h x = c x then 0 else 1) ∂D
          -- = ∫ x, Set.indicator {x | h x ≠ c x} 1 x ∂D   (rewrite if-then-else as indicator)
          -- = D.real {x | h x ≠ c x}
          have h_ite_eq : (fun x => if h x = c x then (0 : ℝ) else 1) =
              Set.indicator {x | h x ≠ c x} 1 := by
            ext x
            simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
            by_cases hx : h x = c x
            · simp [hx]
            · simp [hx]
          rw [h_ite_eq, integral_indicator_one hmeas]
          simp only [Measure.real]
        have h_int_g : ∫ x, g x ∂D = 0 := by
          simp only [hg_def]
          rw [integral_sub (integrable_const p)
            (Integrable.of_mem_Icc 0 1 h_ind_meas.aemeasurable
              (Filter.Eventually.of_forall h_ind_bound))]
          simp [h_int_ind]
        have h_g_subG : ProbabilityTheory.HasSubgaussianMGF g ((‖p - (p - 1)‖₊ / 2) ^ 2) D := by
          exact ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
            h_g_meas.aemeasurable h_g_ae_bound h_int_g
        -- Simplify the parameter: ‖p - (p-1)‖₊ = ‖1‖₊ = 1
        -- p - (p - 1) = 1, so ‖1‖₊ = 1 (for ℝ), and (1 / 2)^2 = 1 / 4
        -- Simplify the nnnorm parameter
        have h_param_eq : ‖p - (p - 1)‖₊ = (1 : NNReal) := by
          have hsub : p - (p - 1) = (1 : ℝ) := by ring
          rw [hsub]
          simp [nnnorm_one]
        have h_param_simp : (‖p - (p - 1)‖₊ / 2) ^ 2 = ((1 : NNReal) / 2) ^ 2 := by
          rw [h_param_eq]
        rw [h_param_simp] at h_g_subG
        -- Step D: Independence of Z_i under μ
        -- Z i xs = g (xs i), and g : X → ℝ is the same for all i.
        -- By iIndepFun_pi, (fun i (xs : Fin m → X) => g (xs i)) is iIndepFun under Measure.pi.
        -- iIndepFun_pi requires: ∀ i, AEMeasurable (X_base i) (μ_base i)
        -- Here X_base i = g for all i, μ_base i = D for all i.
        have h_indep : ProbabilityTheory.iIndepFun
            (m := fun _ => inferInstance)
            (fun i (xs : Fin m → X) => g (xs i)) μ := by
          rw [hμ_def]
          exact ProbabilityTheory.iIndepFun_pi (fun _ => h_g_meas.aemeasurable)
        -- Step E: HasSubgaussianMGF for each Z_i = g ∘ (eval i) under μ
        -- We need HasSubgaussianMGF (fun xs => g (xs i)) ((1 / 2)^2) μ
        -- g is sub-Gaussian with param (1 / 2)^2 under D.
        -- Under μ = Measure.pi (fun _ => D), the map (eval i) is measure-preserving,
        -- so μ.map (eval i) = D.
        -- By HasSubgaussianMGF.of_map, if HasSubgaussianMGF g c (μ.map (eval i))
        -- = HasSubgaussianMGF g c D, then HasSubgaussianMGF (g ∘ eval i) c μ.
        have h_subG_each : ∀ i : Fin m, ProbabilityTheory.HasSubgaussianMGF
            (fun xs : Fin m → X => g (xs i)) ((1 / 2 : NNReal) ^ 2) μ := by
          intro i
          -- of_map gives HasSubgaussianMGF (g ∘ eval i) c μ
          -- which is definitionally (fun xs => g (xs i))
          have h_of_map : ProbabilityTheory.HasSubgaussianMGF
              (g ∘ fun (xs : Fin m → X) => xs i) ((1 / 2 : NNReal) ^ 2) μ := by
            apply ProbabilityTheory.HasSubgaussianMGF.of_map
              (measurable_pi_apply i).aemeasurable
            rw [hμ_def]
            rw [MeasureTheory.measurePreserving_eval _ i |>.map_eq]
            exact h_g_subG
          exact h_of_map
        -- Step F: Apply Hoeffding
        -- measure_sum_ge_le_of_iIndepFun gives:
        -- μ.real {xs | ε ≤ ∑ i ∈ s, Z_i xs} ≤ exp(-ε²/(2·∑_{i∈s} c_i))
        have h_eps_pos : (0 : ℝ) ≤ ↑m * t := by positivity
        have h_hoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
          h_indep
          (c := fun _ => (1 / 2 : NNReal) ^ 2)
          (s := Finset.univ)
          (fun i _ => h_subG_each i)
          h_eps_pos
        -- h_hoeff : μ.real {xs | m*t ≤ ∑ i ∈ Finset.univ, g(xs i)} ≤ exp(-(mt)²/(2·∑ (1 / 2)²))
        -- The set in h_hoeff matches (up to defeq) the set in our goal
        -- The sum ∑_{i ∈ univ} (1 / 2)² = m * (1 / 2)² = m/4
        -- So the exponent is -(mt)²/(2·m/4) = -(mt)²/(m/2) = -m²t²·2/m = -2mt²
        -- Need to show this equals our target exp(-2·m·t²)
        -- First, simplify the Finset.sum of constants
        have h_sum_c : (∑ i ∈ (Finset.univ : Finset (Fin m)), ((1 / 2 : NNReal) ^ 2 : NNReal)) =
            ↑m * (1 / 2 : NNReal) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        -- Now compute the exponent
        -- -(m*t)² / (2 * (m * (1 / 4))) = -m²t² / (m/2) = -2mt²
        -- In NNReal: (1 / 2 : ℝ≥0)^2 = 1 / 4 as NNReal
        -- 2 * ∑ c_i = 2 * m * (1 / 4) = m/2
        -- -(mt)² / (m/2) = -2mt²
        -- We need to show: exp(-(mt)²/(2·↑(∑ (1 / 2)²))) ≤ exp(-2·m·t²)
        -- Actually we need equality, not inequality.
        -- Let's compute:
        -- -(↑m * t) ^ 2 / (2 * ↑(∑_{i ∈ univ} (1 / 2)^2))
        -- = -(m*t)² / (2 * m * (1 / 4))
        -- = -m²t² / (m/2)
        -- = -2mt²
        -- = -2 * m * t²
        -- This is exactly what we need.
        -- Convert h_hoeff exponent
        rw [h_sum_c] at h_hoeff
        -- Now h_hoeff has exp(-(mt)²/(2 * ↑(m * (1 / 2)²)))
        -- We need to show this equals exp(-2 * m * t²)
        -- ↑(m * (1 / 2)²) as ℝ = m * (1 / 4) = m/4
        -- 2 * m/4 = m/2
        -- -(mt)²/(m/2) = -m²t²·(2/m) = -2mt² when m ≠ 0
        -- So the exponents match.
        -- Now: μ.real S' ≤ exp(-2mt²) where S' is the Hoeffding set
        -- And S ⊆ S' (shown above), so μ.real S ≤ μ.real S'
        -- Actually, h_hoeff already bounds the right set.
        -- We just need the exponent computation.
        -- The sets are definitionally equal (Z i xs = g (xs i))
        -- The exponents need algebraic simplification
        -- h_hoeff has form: μ.real {xs | mt ≤ ∑ i ∈ univ, g(xs i)} ≤ exp(-(mt)²/(2·∑ c_i))
        -- We need: μ.real {xs | mt ≤ ∑ i, Z i xs} ≤ exp(-2mt²)
        -- Step 1: rewrite the sum from ∑ i ∈ univ to ∑ i
        -- Step 2: show exponent equality
        -- After rw [h_sum_c], h_hoeff has:
        -- μ.real {ω | ↑m * t ≤ ∑ i, g (ω i)} ≤ exp(-(↑m*t)²/(2 * ↑(↑m * (1 / 2)²)))
        -- We need: μ.real {xs | ↑m * t ≤ ∑ i, Z i xs} ≤ exp(-2 * ↑m * t²)
        -- Step 1: The sets are equal since Z i xs = g (xs i)
        -- Step 2: Simplify the exponent
        -- First, show the exponent is -2 * m * t²
        -- Compute the NNReal coercion: ↑(↑m * (1 / 2 : NNReal)^2) : ℝ = m * (1 / 2)^2 = m/4
        -- Then 2 * (m/4) = m/2
        -- -(mt)²/(m/2) = -2mt²
        -- First, let's simplify h_hoeff's bound by working with the exponent
        -- h_hoeff : μ.real {ω | ...} ≤ exp(-(mt)²/(2 * ↑(m * (1 / 2)²)))
        -- The ↑ is NNReal → ℝ coercion
        -- ↑(m * (1 / 2)²) = ↑m * ↑((1 / 2)²) = m * (1 / 2)² = m * 1 / 4 = m/4
        -- 2 * m/4 = m/2
        -- -(mt)²/(m/2) = -2mt²
        suffices h_exp_eq : Real.exp (-(↑m * t) ^ 2 / (2 * ↑(↑m * (1 / 2 : NNReal) ^ 2 : NNReal))) =
            Real.exp (-2 * ↑m * t ^ 2) by
          rw [h_exp_eq] at h_hoeff
          exact h_hoeff
        congr 1
        push_cast
        field_simp

/-! ## T2: Symmetrization Step -/

/-- Symmetrization: the probability of a large gap TrueErr-EmpErr
    is at most twice the probability of a large gap EmpErr'-EmpErr
    on the double sample.

    **Proof strategy (6 steps):**

    1. **Witness selection:** For S in the bad event, ∃h* ∈ C with
       TrueErr(h*) - EmpErr_S(h*) ≥ ε.
       ```
       -- In the bad event set, extract h* by classical choice
       have h_witness : ∀ xs ∈ bad_event, ∃ h* ∈ C,
         TrueErrorReal X h* c D - EmpiricalError X Bool h* (sample xs) (zeroOneLoss Bool) ≥ ε
       ```

    2. **Ghost sample mean:** E_{S'}[EmpErr_{S'}(h*)] = TrueErr(h*) ≥ EmpErr_S(h*) + ε.
       - Uses: `MeasureTheory.integral_pi` to compute E[EmpErr] over product measure.
       - KEY LEMMA: For fixed h, E_{D^m}[EmpiricalError(h,S)] = TrueErrorReal(h,c,D).
         This is because EmpErr = (1/m)∑ indicator(x_i), and E[indicator(x_i)] = TrueErrorReal.
       ```
       have expected_emp_err : ∀ h* : Concept X Bool,
         ∫ xs, EmpiricalError X Bool h* (sample xs) (zeroOneLoss Bool)
           ∂(Measure.pi (fun _ : Fin m => D))
         = TrueErrorReal X h* c D := by ...
       ```

    3. **Hoeffding on ghost sample:** P_{S'}[EmpErr_{S'}(h*) < TrueErr(h*) - ε/2] ≤ exp(-mε²/2).
       - Apply `hoeffding_one_sided` with t = ε/2.
       - The `hm_large` hypothesis ensures exp(-mε²/2) < 1 / 2:
         2·ln2 ≤ mε² ⟹ mε²/2 ≥ ln2 ⟹ exp(-mε²/2) ≤ 1 / 2.
       ```
       have hoeffding_ghost : ∀ h* ∈ C,
         Measure.pi (fun _ : Fin m => D)
           {xs' | EmpiricalError X Bool h* (sample xs') (zeroOneLoss Bool)
             < TrueErrorReal X h* c D - ε/2}
         ≤ ENNReal.ofReal (Real.exp (-m * (ε/2)^2 * 2)) := by
           intro h* _; exact hoeffding_one_sided D h* c m hm (ε/2) (by linarith) (by ...) (by ...)
       ```

    4. **Complementary probability:** P_{S'}[EmpErr_{S'}(h*) - EmpErr_S(h*) ≥ ε/2] ≥ 1 / 2.
       - From step 2: TrueErr(h*) ≥ EmpErr_S(h*) + ε
       - From step 3: P[EmpErr_{S'} ≥ TrueErr - ε/2] ≥ 1 / 2
       - Chain: EmpErr_{S'} ≥ TrueErr - ε/2 ≥ EmpErr_S + ε - ε/2 = EmpErr_S + ε/2

    5. **Conditional to unconditional:** The witness h* from step 1 also witnesses the
       double-sample event ∃h∈C: EmpErr'-EmpErr ≥ ε/2. So:
       P_{S'}[double event | S bad] ≥ 1 / 2.
       ```
       have conditional_bound : ∀ xs ∈ bad_event,
         Measure.pi (fun _ : Fin m => D)
           {xs' | ∃ h ∈ C, EmpiricalError ... xs' - EmpiricalError ... xs ≥ ε/2}
         ≥ ENNReal.ofReal (1 / 2) := by ...
       ```

    6. **Fubini integration:** By Measure.prod_apply and Fubini:
       P_{S,S'}[double event] = ∫_S P_{S'}[double event | S] ≥ (1 / 2) · P_S[bad event]
       ⟹ P_S[bad event] ≤ 2 · P_{S,S'}[double event].
       ```
       -- Uses: MeasureTheory.Measure.prod_apply or lintegral_prod
       -- MEASURABILITY: the double-sample event is measurable as a finite union
       -- of sets of the form {(xs,xs') | EmpErr'(h) - EmpErr(h) ≥ ε/2} for h ∈ C.
       -- Since C may be infinite, measurability requires care: the sup over h
       -- must be shown to be measurable. For finite restriction patterns (≤ 2^m
       -- on Fin m → Bool), this is a finite union.
       ```

    **MEASURABILITY CONCERNS:**
    - `{xs | ∃ h ∈ C, ...}` is NOT obviously measurable for infinite C.
      Strategy: decompose via restriction patterns. On any fixed xs, the set of
      labelings {(h(xs 0), ..., h(xs(m-1))) | h ∈ C} has at most GF(C,m) ≤ 2^m
      elements. So the ∃h event is a finite union of measurable sets.
    - `EmpiricalError` is a finite sum of measurable functions, hence measurable.
    - The product σ-algebra on (Fin m → X) × (Fin m → X) is generated by
      cylinder sets, and our events are in this σ-algebra.

    **References:** SSBD Lemma 4.5, Kakade-Tewari Lecture 19 Lemma 1 -/
theorem symmetrization_step {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ C, TrueErrorReal X h c D -
        EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
    ≤ 2 * (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
        (MeasureTheory.Measure.pi (fun _ : Fin m => D))
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2} := by
  -- Abbreviations
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  -- The bad event: {xs | ∃ h ∈ C, TrueErr(h) - EmpErr(h, xs) ≥ ε}
  set A := {xs : Fin m → X | ∃ h ∈ C, TrueErrorReal X h c D -
      EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
    with hA_def
  -- The double event: {(xs, xs') | ∃ h ∈ C, EmpErr'(h) - EmpErr(h) ≥ ε/2}
  set B := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    with hB_def
  -- Goal: μ A ≤ 2 * (μ.prod μ) B
  -- Step 0: It suffices to show (1 / 2) * μ A ≤ (μ.prod μ) B
  suffices h_half : (1 : ℝ≥0∞) / 2 * μ A ≤ (μ.prod μ) B by
    have h2 : μ A ≤ 2 * ((1 : ℝ≥0∞) / 2 * μ A) := by
      rw [← mul_assoc, show (2 : ℝ≥0∞) * (1 / 2) = 1 from by
        simp [ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by exact ENNReal.ofNat_ne_top)]]
      simp
    exact h2.trans (mul_le_mul_right h_half 2)
  -- Step 1: Use toMeasurable on B to get a measurable superset
  set B' := MeasureTheory.toMeasurable (μ.prod μ) B with hB'_def
  have hB'_meas : MeasurableSet B' := MeasureTheory.measurableSet_toMeasurable _ _
  -- Step 2: The slice function f(xs) = μ(Prod.mk xs ⁻¹' B') is measurable
  set f : (Fin m → X) → ℝ≥0∞ := fun xs => μ (Prod.mk xs ⁻¹' B') with hf_def
  have hf_meas : Measurable f := measurable_measure_prodMk_left hB'_meas
  -- Step 3: Conditional bound — for xs ∈ A, f(xs) ≥ 1 / 2
  -- This is the heart: for xs in the bad event, the ghost sample witnesses
  -- the double event with probability ≥ 1 / 2.
  have h_cond : ∀ xs ∈ A, (1 : ℝ≥0∞) / 2 ≤ f xs := by
    intro xs hxs
    -- Extract witness: ∃ h* ∈ C with TrueErr(h*) - EmpErr(h*, xs) ≥ ε
    obtain ⟨h_star, h_star_in_C, h_gap⟩ := hxs
    -- The set of ghost samples where h* witnesses the double event
    set S_ghost := {xs' : Fin m → X | EmpiricalError X Bool h_star
        (fun i => (xs' i, c (xs' i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h_star
        (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε / 2} with hS_ghost_def
    -- S_ghost ⊆ Prod.mk xs ⁻¹' B (since h* ∈ C witnesses the ∃)
    have h_ghost_sub_B : S_ghost ⊆ Prod.mk xs ⁻¹' B := by
      intro xs' hxs'
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hB_def]
      exact ⟨h_star, h_star_in_C, hxs'⟩
    -- B ⊆ B', so Prod.mk xs ⁻¹' B ⊆ Prod.mk xs ⁻¹' B'
    have h_B_sub_B' : Prod.mk xs ⁻¹' B ⊆ Prod.mk xs ⁻¹' B' :=
      Set.preimage_mono (MeasureTheory.subset_toMeasurable _ _)
    -- Therefore f(xs) = μ(Prod.mk xs ⁻¹' B') ≥ μ(S_ghost)
    -- It suffices to show μ(S_ghost) ≥ 1 / 2
    calc (1 : ℝ≥0∞) / 2
        ≤ μ S_ghost := by
          -- This is the Hoeffding complement bound.
          -- For fixed xs and h*, EmpErr(h*, xs) is a constant.
          -- TrueErr(h*) - EmpErr(h*, xs) ≥ ε means TrueErr(h*) ≥ EmpErr(h*, xs) + ε
          -- S_ghost = {xs' | EmpErr'(h*) ≥ EmpErr(h*, xs) + ε/2}
          -- By the complement of Hoeffding:
          --   μ {xs' | EmpErr'(h*) ≤ TrueErr(h*) - ε/2} ≤ exp(-mε²/2) ≤ 1 / 2
          -- And TrueErr(h*) - ε/2 ≥ EmpErr(h*, xs) + ε/2
          -- So {xs' | EmpErr'(h*) ≥ TrueErr(h*) - ε/2} ⊆ S_ghost
          -- Hence μ(S_ghost) ≥ 1 - 1 / 2 = 1 / 2
          -- Case split: if ε > 1, the bad event is empty (gap ≤ 1 < ε), contradiction
          -- If ε ≤ 1, apply Hoeffding with t = ε/2 ≤ 1 / 2 ≤ 1
          -- First, establish measurability of {x | h_star x ≠ c x}
          have hmeas_disagree : MeasurableSet {x | h_star x ≠ c x} :=
            (measurableSet_eq_fun (hmeas_C h_star h_star_in_C) hc_meas).compl
          -- Bound: TrueErrorReal ≤ 1 (probability measure)
          have h_true_le_one : TrueErrorReal X h_star c D ≤ 1 := by
            simp only [TrueErrorReal, TrueError]
            have h_le : D {x | h_star x ≠ c x} ≤ 1 := by
              calc D {x | h_star x ≠ c x} ≤ D Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
            exact ENNReal.toReal_le_of_le_ofReal one_pos.le
              (by rw [ENNReal.ofReal_one]; exact h_le)
          -- EmpiricalError with 0-1 loss is nonneg
          have h_emp_nonneg : 0 ≤ EmpiricalError X Bool h_star
              (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) := by
            simp only [EmpiricalError]
            split
            · exact le_refl 0
            · apply div_nonneg
              · apply Finset.sum_nonneg
                intro i _
                simp only [zeroOneLoss]
                split <;> linarith
              · positivity
          -- If ε > 1, the gap TrueErr - EmpErr ≤ 1 < ε, contradicting h_gap
          by_cases hε1 : ε ≤ 1
          case neg =>
            push Not at hε1
            have h_gap_bound : TrueErrorReal X h_star c D -
                EmpiricalError X Bool h_star
                (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≤ 1 := by
              linarith
            linarith
          case pos =>
          -- Now ε ≤ 1, so ε/2 ≤ 1 / 2 ≤ 1
          have hε2_pos : (0 : ℝ) < ε / 2 := by linarith
          have hε2_le_one : ε / 2 ≤ 1 := by linarith
          -- Apply hoeffding_one_sided to get tail bound
          have h_hoeff := hoeffding_one_sided D h_star c m hm (ε / 2) hε2_pos hε2_le_one
            hmeas_disagree
          -- Show exp(-2m(ε/2)²) ≤ 1 / 2 using hm_large
          have h_exp_le_half : Real.exp (-2 * ↑m * (ε / 2) ^ 2) ≤ 1 / 2 := by
            have h_exp_eq : -2 * ↑m * (ε / 2) ^ 2 = -(↑m * ε ^ 2 / 2) := by ring
            rw [h_exp_eq]
            -- exp(-(mε²/2)) ≤ 1 / 2 iff 2 ≤ exp(mε²/2)
            have h_half : Real.log 2 ≤ ↑m * ε ^ 2 / 2 := by linarith
            have h_two_le_exp : (2 : ℝ) ≤ Real.exp (↑m * ε ^ 2 / 2) := by
              calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
                _ ≤ Real.exp (↑m * ε ^ 2 / 2) := Real.exp_le_exp_of_le h_half
            -- (exp x)⁻¹ ≤ 1 / 2 from 2 ≤ exp x
            rw [Real.exp_neg]
            rw [show (1 : ℝ) / 2 = 2⁻¹ from by norm_num]
            exact inv_anti₀ (by positivity) h_two_le_exp
          -- The Hoeffding set
          set H_set := {xs' : Fin m → X | EmpiricalError X Bool h_star
              (fun i => (xs' i, c (xs' i))) (zeroOneLoss Bool) ≤
              TrueErrorReal X h_star c D - ε / 2} with hH_set_def
          -- μ(H_set) ≤ exp(-2m(ε/2)²) ≤ 1 / 2
          have h_H_le_half : μ H_set ≤ 1 / 2 := by
            calc μ H_set
                ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * (ε / 2) ^ 2)) := h_hoeff
              _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal h_exp_le_half
              _ = 1 / 2 := by
                  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
                  simp [ENNReal.ofReal_one]
          -- Complement bound: μ(H_setᶜ) ≥ 1 / 2
          have h_prob : MeasureTheory.IsProbabilityMeasure μ := by
            rw [hμ_def]; infer_instance
          -- μ(univ) = 1 ≤ μ(H_set) + μ(H_setᶜ), and μ(H_set) ≤ 1 / 2
          have h_compl_ge : 1 / 2 ≤ μ H_setᶜ := by
            have h_total : 1 ≤ μ H_set + μ H_setᶜ := by
              have : μ Set.univ ≤ μ H_set + μ H_setᶜ := by
                calc μ Set.univ = μ (H_set ∪ H_setᶜ) := by rw [Set.union_compl_self]
                  _ ≤ μ H_set + μ H_setᶜ := measure_union_le _ _
              rwa [measure_univ] at this
            -- μ(H_set) is finite (≤ 1 / 2 < ⊤)
            have h_H_ne_top : μ H_set ≠ ⊤ :=
              ne_top_of_le_ne_top ENNReal.one_ne_top
                (h_H_le_half.trans (by norm_num))
            -- From 1 ≤ μ(H_set) + μ(H_setᶜ) and μ(H_set) ≤ 1 / 2:
            -- μ(H_setᶜ) ≥ 1 - μ(H_set) ≥ 1 - 1 / 2 = 1 / 2
            -- We need: 1 / 2 ≤ μ(H_setᶜ)
            -- From h_total: 1 ≤ μ(H_set) + μ(H_setᶜ)
            -- From h_H_le_half: μ(H_set) ≤ 1 / 2
            -- 1 / 2 = 1 - 1 / 2 ≤ 1 - μ(H_set) ≤ (a + b) - a = b
            calc (1 : ℝ≥0∞) / 2
                = 1 - 1 / 2 := by norm_num
              _ ≤ 1 - μ H_set := tsub_le_tsub_left h_H_le_half 1
              _ ≤ (μ H_set + μ H_setᶜ) - μ H_set := tsub_le_tsub_right h_total (μ H_set)
              _ = μ H_setᶜ := ENNReal.add_sub_cancel_left h_H_ne_top
          -- H_setᶜ ⊆ S_ghost: complement of Hoeffding tail is in the ghost witness set
          have h_compl_sub : H_setᶜ ⊆ S_ghost := by
            intro xs' hxs'
            simp only [Set.mem_compl_iff, hH_set_def, Set.mem_setOf_eq, not_le] at hxs'
            -- hxs' : TrueErrorReal ... - ε/2 < EmpErr'(h*, xs')
            -- h_gap : TrueErrorReal ... - EmpErr_S(h*, xs) ≥ ε
            -- So EmpErr'(h*, xs') > TrueErr - ε/2 ≥ EmpErr_S + ε - ε/2 = EmpErr_S + ε/2
            simp only [hS_ghost_def, Set.mem_setOf_eq, ge_iff_le]
            linarith
          -- Chain: 1 / 2 ≤ μ(H_setᶜ) ≤ μ(S_ghost)
          exact h_compl_ge.trans (MeasureTheory.measure_mono h_compl_sub)
      _ ≤ μ (Prod.mk xs ⁻¹' B') :=
          MeasureTheory.measure_mono (h_ghost_sub_B.trans h_B_sub_B')
  -- Step 4: Apply Markov's inequality
  -- (1 / 2) * μ {xs | 1 / 2 ≤ f xs} ≤ ∫⁻ xs, f xs ∂μ
  have h_markov : (1 : ℝ≥0∞) / 2 * μ {xs | (1 : ℝ≥0∞) / 2 ≤ f xs} ≤ ∫⁻ xs, f xs ∂μ :=
    mul_meas_ge_le_lintegral hf_meas _
  -- Step 5: prod_apply on measurable B'
  have h_prod : (μ.prod μ) B' = ∫⁻ xs, μ (Prod.mk xs ⁻¹' B') ∂μ :=
    MeasureTheory.Measure.prod_apply hB'_meas
  -- Step 6: Chain the inequalities
  calc (1 : ℝ≥0∞) / 2 * μ A
      ≤ (1 : ℝ≥0∞) / 2 * μ {xs | (1 : ℝ≥0∞) / 2 ≤ f xs} := by
        apply mul_le_mul_right
        exact MeasureTheory.measure_mono h_cond
    _ ≤ ∫⁻ xs, f xs ∂μ := h_markov
    _ = (μ.prod μ) B' := h_prod.symm
    _ = (μ.prod μ) B := MeasureTheory.measure_toMeasurable B

/-! ## T3: Double Sample Pattern Bound (Approach A — Standard Exchangeability) -/

/-- Per-hypothesis Hoeffding on the double sample: for a FIXED hypothesis h,
    the probability that EmpErr(h,S') - EmpErr(h,S) ≥ ε/2 under D^m ⊗ D^m
    is at most exp(-mε²/8).

    Proof: The gap = (1/m)∑ᵢ (Zᵢ' - Zᵢ) where Zᵢ = 1[h(xᵢ)≠c(xᵢ)], Zᵢ' = 1[h(x'ᵢ)≠c(x'ᵢ)]
    are iid Bernoulli(p) with p = TrueError(h,c,D). The differences Wᵢ = Zᵢ' - Zᵢ are
    independent, bounded in [-1,1], and centered (E[Wᵢ] = 0).
    By Hoeffding's inequality: P[(1/m)∑Wᵢ ≥ ε/2] ≤ exp(-mε²/8).

    This uses the sub-Gaussian machinery from T1, extended to the product space.

    **Proof sketch:**
    1. Pair D^m ⊗ D^m ≅ (D⊗D)^m via the natural isomorphism
       (Fin m → X) × (Fin m → X) ≃ᵐ Fin m → X × X
    2. Define g : X × X → ℝ, g(a,b) = 1[h(b)≠c(b)] - 1[h(a)≠c(a)]
       Then g ∈ [-1,1], E_{D⊗D}[g] = 0, so HasSubgaussianMGF g 1 (D⊗D)
    3. The gap = (1/m)∑ᵢ g(xᵢ, x'ᵢ) where pairs are iIndepFun under (D⊗D)^m
    4. By measure_sum_ge_le_of_iIndepFun: P[∑g ≥ mε/2] ≤ exp(-(mε/2)²/(2m)) = exp(-mε²/8)

    **Mathlib chain:** iIndepFun_pi + HasSubgaussianMGF.of_map + measure_sum_ge_le_of_iIndepFun -/
theorem per_hypothesis_gap_bound {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (hmeas_h : Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
    (μ.prod μ)
      {p : (Fin m → X) × (Fin m → X) |
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    ≤ ENNReal.ofReal (Real.exp (-(↑m * ε ^ 2 / 8))) := by
  intro μ
  -- === Step 0: Abbreviations ===
  set indicator : X → ℝ := fun x => zeroOneLoss Bool (h x) (c x) with hind_def
  set g : X × X → ℝ := fun pair => indicator pair.2 - indicator pair.1 with hg_def
  set ν := D.prod D with hν_def
  set π := MeasureTheory.Measure.pi (fun _ : Fin m => ν) with hπ_def
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  -- === Step 1: Isomorphism D^m ⊗ D^m ≅ (D⊗D)^m ===
  set equiv := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin m) with hequiv_def
  have h_mp : MeasurePreserving (⇑equiv) π (μ.prod μ) := by
    rw [hπ_def, hν_def]
    show MeasurePreserving (⇑equiv) (Measure.pi fun _ => D.prod D) (μ.prod μ)
    exact measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ => D) (fun _ => D)
  -- === Step 2: Bound directly via sum event under π ===
  -- Define the sum event
  set S_sum := {z : Fin m → X × X | (↑m * (ε / 2) : ℝ) ≤ ∑ i : Fin m, g (z i)}
    with hS_sum_def
  -- The target set
  set S := {p : (Fin m → X) × (Fin m → X) |
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    with hS_def
  -- Show equiv ⁻¹' S ⊆ S_sum
  have h_preimage_sub : equiv ⁻¹' S ⊆ S_sum := by
    intro z hz
    simp only [hS_def, hS_sum_def, Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢
    -- Unfold EmpiricalError in hz
    unfold EmpiricalError at hz
    simp only [Nat.pos_iff_ne_zero.mp hm, ↓reduceIte] at hz
    -- equiv z = (fun i => (z i).1, fun i => (z i).2)
    have h_fst : (equiv z).1 = fun i => (z i).1 := by
      ext i; simp [hequiv_def, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow]
    have h_snd : (equiv z).2 = fun i => (z i).2 := by
      ext i; simp [hequiv_def, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow]
    rw [h_fst, h_snd] at hz
    -- hz : (∑ zeroOneLoss(z_i.2)) / m - (∑ zeroOneLoss(z_i.1)) / m ≥ ε/2
    -- Goal: m * (ε/2) ≤ ∑ g(z_i)
    simp only [hg_def, hind_def]
    -- Goal: m * (ε/2) ≤ ∑ i, (zeroOneLoss(z_i.2) - zeroOneLoss(z_i.1))
    -- hz is (sum2 / m - sum1 / m) ≥ ε/2
    rw [ge_iff_le, div_sub_div_same] at hz
    rw [le_div_iff₀ hm_pos] at hz
    -- hz: ε/2 * m ≤ sum2 - sum1
    rw [← Finset.sum_sub_distrib] at hz
    linarith
  -- Bound: (μ.prod μ) S ≤ π S_sum using the isomorphism
  -- Since map equiv π = μ.prod μ, we have (μ.prod μ) S = π (equiv⁻¹' S) ≤ π S_sum
  -- We avoid the complex measurability argument by using measure_mono directly.
  -- Since MeasurePreserving means (μ.prod μ) = π.map equiv, we use the monotonicity path.
  -- We bound (μ.prod μ) S ≤ π S_sum by using that μ.prod μ ≤ 1 and working through π.
  -- Actually, use: (μ.prod μ) S ≤ π (equiv ⁻¹' S) ≤ π S_sum
  -- For the first step, note π.map equiv = μ.prod μ means (μ.prod μ) = π.map equiv
  -- So (μ.prod μ) S = (π.map equiv) S ≤ π (equiv ⁻¹' S) (equality for measurable sets,
  -- ≤ for any set by outer measure property)
  have h_bound1 : (μ.prod μ) S ≤ π S_sum := by
    have h_eq_preimage : (μ.prod μ) S = π (equiv ⁻¹' S) := by
      rw [← h_mp.map_eq]; exact equiv.map_apply S
    rw [h_eq_preimage]
    exact MeasureTheory.measure_mono h_preimage_sub
  -- Now bound π S_sum using sub-Gaussian machinery
  calc (μ.prod μ) S
      ≤ π S_sum := h_bound1
    _ = ENNReal.ofReal (π.real S_sum) := by rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(↑m * ε ^ 2 / 8))) := by
        apply ENNReal.ofReal_le_ofReal
        -- === Steps 3-7: Sub-Gaussian bound ===
        -- Step 3a: indicator is measurable
        have hmeas_ne : MeasurableSet {a : X | h a ≠ c a} := by
          have : {a : X | h a ≠ c a} = (fun x => (h x, c x)) ⁻¹' {p : Bool × Bool | p.1 ≠ p.2} := by
            ext x; simp
          rw [this]
          exact (Measurable.prodMk hmeas_h hc_meas) (Set.Finite.measurableSet (Set.toFinite _))
        have h_ind_meas : Measurable indicator := by
          simp only [hind_def, zeroOneLoss]
          have hmeas_eq : MeasurableSet {a : X | h a = c a} := by
            have : {a : X | h a = c a} = {a : X | h a ≠ c a}ᶜ := by ext x; simp
            rw [this]; exact hmeas_ne.compl
          exact Measurable.ite hmeas_eq measurable_const measurable_const
        -- Step 3b: g is measurable
        have h_g_meas : Measurable g := by
          exact (h_ind_meas.comp measurable_snd).sub (h_ind_meas.comp measurable_fst)
        -- Step 3c: indicator bounded in [0, 1]
        have h_ind_bound : ∀ x : X, indicator x ∈ Set.Icc (0 : ℝ) 1 := by
          intro x; simp only [hind_def, zeroOneLoss]
          split
          · exact ⟨le_refl 0, zero_le_one⟩
          · exact ⟨zero_le_one, le_refl 1⟩
        -- Step 3d: g bounded in [-1, 1]
        have h_g_bound : ∀ pair : X × X, g pair ∈ Set.Icc (-1 : ℝ) 1 := by
          intro pair
          have hi1 := h_ind_bound pair.1
          have hi2 := h_ind_bound pair.2
          simp only [hg_def, Set.mem_Icc] at hi1 hi2 ⊢
          constructor <;> linarith [hi1.1, hi1.2, hi2.1, hi2.2]
        have h_g_ae_bound : ∀ᵐ pair ∂ν, g pair ∈ Set.Icc (-1 : ℝ) 1 :=
          Filter.Eventually.of_forall h_g_bound
        -- Step 3e: g is centered (∫ g ∂ν = 0)
        have h_int_g : ∫ pair, g pair ∂ν = 0 := by
          have h_g_int : Integrable g ν :=
            hν_def ▸ Integrable.of_mem_Icc (-1) 1
              h_g_meas.aemeasurable (Filter.Eventually.of_forall h_g_bound)
          rw [hν_def, MeasureTheory.integral_prod (f := g) (by rwa [hν_def] at h_g_int)]
          have h_ind_int : Integrable indicator D :=
            Integrable.of_mem_Icc 0 1 h_ind_meas.aemeasurable
              (Filter.Eventually.of_forall h_ind_bound)
          -- ∫ a, ∫ b, g(a,b) ∂D ∂D = ∫ a, (∫ indicator ∂D - indicator a) ∂D = 0
          have h_inner : ∀ a, ∫ b, g (a, b) ∂D = ∫ x, indicator x ∂D - indicator a := by
            intro a
            simp only [hg_def]
            rw [MeasureTheory.integral_sub h_ind_int (integrable_const _)]
            simp [MeasureTheory.integral_const]
          simp_rw [h_inner]
          rw [MeasureTheory.integral_sub (integrable_const _) h_ind_int]
          simp [MeasureTheory.integral_const]
        -- Step 4: HasSubgaussianMGF for g under ν
        have h_g_subG : ProbabilityTheory.HasSubgaussianMGF g ((‖(1:ℝ) - (-1:ℝ)‖₊ / 2) ^ 2) ν :=
          ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
            h_g_meas.aemeasurable h_g_ae_bound h_int_g
        -- Simplify the parameter: (‖2‖₊/2)² = 1
        have h_param_eq : (‖(1:ℝ) - (-1:ℝ)‖₊ / 2) ^ 2 = (1 : NNReal) := by
          have h2 : (1:ℝ) - (-1:ℝ) = 2 := by ring
          rw [h2, Real.nnnorm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
          -- Now goal: (⟨2, _⟩ / 2) ^ 2 = 1
          ext; simp
        rw [h_param_eq] at h_g_subG
        -- Step 5: Independence under π
        have h_indep : ProbabilityTheory.iIndepFun
            (m := fun _ => inferInstance)
            (fun i (z : Fin m → X × X) => g (z i)) π := by
          rw [hπ_def]
          exact ProbabilityTheory.iIndepFun_pi (fun _ => h_g_meas.aemeasurable)
        -- Step 6: Per-coordinate sub-Gaussian
        have h_subG_each : ∀ i : Fin m, ProbabilityTheory.HasSubgaussianMGF
            (fun z : Fin m → X × X => g (z i)) 1 π := by
          intro i
          -- of_map gives HasSubgaussianMGF (g ∘ eval i) c π
          -- which is definitionally HasSubgaussianMGF (fun z => g (z i)) c π
          have h_of_map : ProbabilityTheory.HasSubgaussianMGF
              (g ∘ fun (z : Fin m → X × X) => z i) 1 π := by
            apply ProbabilityTheory.HasSubgaussianMGF.of_map
              (measurable_pi_apply i).aemeasurable
            have h_map : π.map (fun z : Fin m → X × X => z i) = ν := by
              rw [hπ_def]
              exact (MeasureTheory.measurePreserving_eval (fun _ : Fin m => ν) i).map_eq
            rw [h_map]; exact h_g_subG
          exact h_of_map
        -- Step 7: Apply Hoeffding
        have h_eps_pos : (0 : ℝ) ≤ ↑m * (ε / 2) := by positivity
        have h_hoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
          h_indep (c := fun _ => (1 : NNReal)) (s := Finset.univ)
          (fun i _ => h_subG_each i) h_eps_pos
        -- Simplify ∑ 1 = m and exponent
        have h_sum_c : (∑ i ∈ (Finset.univ : Finset (Fin m)), ((1 : NNReal) : NNReal)) =
            (↑m : NNReal) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        rw [h_sum_c] at h_hoeff
        -- Step 8: Show exponent equality
        suffices h_exp : Real.exp (-(↑m * (ε / 2)) ^ 2 / (2 * ↑(↑m : NNReal))) =
            Real.exp (-(↑m * ε ^ 2 / 8)) by
          rw [h_exp] at h_hoeff; exact h_hoeff
        congr 1; push_cast; field_simp; ring

/-- The number of distinct restriction patterns of C on any n points is at most GF(C,n).
    For z : Fin n → X, define patterns(z) as the set of `p : Fin n → Bool`
    realized by some `h ∈ C` through `p i = (h (z i) ≠ c (z i))`.
    Then patterns(z).ncard ≤ GrowthFunction X C n by definition of GrowthFunction. -/
theorem restriction_pattern_count {X : Type u} [MeasurableSpace X] [Infinite X]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (n : ℕ) (z : Fin n → X) :
    Set.ncard {p : Fin n → Bool | ∃ h ∈ C, ∀ i, p i = decide (h (z i) ≠ c (z i))} ≤
      GrowthFunction X C n := by
  classical
  -- Phase 1: XOR bijection showing |P| = |R|
  let R : Set (Fin n → Bool) := {f | ∃ h ∈ C, ∀ i, f i = h (z i)}
  let ψ : (Fin n → Bool) → (Fin n → Bool) := fun f i => Bool.xor (f i) (c (z i))
  have hψ_inj : Function.Injective ψ := by
    intro f g hfg; funext i
    have hi := congr_fun hfg i; simp only [ψ] at hi
    revert hi; cases f i <;> cases g i <;> cases c (z i) <;> simp [Bool.xor]
  have hP_eq : {p : Fin n → Bool | ∃ h ∈ C, ∀ i, p i = decide (h (z i) ≠ c (z i))} = ψ '' R := by
    ext p; simp only [Set.mem_setOf_eq, Set.mem_image, R, ψ]
    constructor
    · rintro ⟨h, hC, hp⟩
      refine ⟨fun i => h (z i), ⟨h, hC, fun i => rfl⟩, ?_⟩
      funext i; simp only [hp i]
      cases h (z i) <;> cases c (z i) <;> rfl
    · rintro ⟨f, ⟨h, hC, hf⟩, rfl⟩
      exact ⟨h, hC, fun i => by simp only [hf i]; cases h (z i) <;> cases c (z i) <;> rfl⟩
  rw [hP_eq, Set.ncard_image_of_injective R hψ_inj]
  -- Now goal: R.ncard ≤ GrowthFunction X C n
  -- Phase 2: Build witness Finset S ⊇ image(z) with |S| = n
  let S₀ : Finset X := Finset.univ.image z
  have hS₀_card : S₀.card ≤ n :=
    (Finset.card_image_le).trans (by simp [Fintype.card_fin])
  obtain ⟨S, hS₀_sub, hS_card⟩ := Infinite.exists_superset_card_eq S₀ n hS₀_card
  -- Phase 3: Show R.ncard ≤ R_S.ncard
  have hz_mem : ∀ i : Fin n, z i ∈ S :=
    fun i => hS₀_sub (Finset.mem_image_of_mem z (Finset.mem_univ i))
  let R_S : Set (↥S → Bool) := {g | ∃ h ∈ C, ∀ x : ↥S, g x = h ↑x}
  let ρ : (↥S → Bool) → (Fin n → Bool) := fun g i => g ⟨z i, hz_mem i⟩
  have hR_sub : R ⊆ ρ '' R_S := by
    rintro f ⟨h, hC, hf⟩
    exact ⟨fun x => h ↑x, ⟨h, hC, fun x => rfl⟩, funext fun i => by simp only [ρ, hf i]⟩
  have hR_le_RS : R.ncard ≤ R_S.ncard :=
    (Set.ncard_le_ncard hR_sub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite R_S))
  -- Phase 4: Show R_S.ncard ≤ GrowthFunction X C n
  have hR_S_eq : R_S.ncard =
      ({f : ↥S → Bool | ∃ c_1 ∈ C, ∀ x : ↥S, c_1 ↑x = f x} : Set _).ncard := by
    congr 1; ext f; exact ⟨fun ⟨h, hC, hf⟩ => ⟨h, hC, fun x => (hf x).symm⟩,
                           fun ⟨h, hC, hf⟩ => ⟨h, hC, fun x => (hf x).symm⟩⟩
  have hbdd : BddAbove (Set.range fun (T : {T : Finset X // T.card = n}) =>
      ({f : ↥T.val → Bool | ∃ c_1 ∈ C, ∀ x : ↥T.val, c_1 ↑x = f x} : Set _).ncard) := by
    refine ⟨2 ^ n, ?_⟩
    rintro _ ⟨T, rfl⟩
    calc Set.ncard _ ≤ Set.ncard (Set.univ : Set (↥T.val → Bool)) :=
            Set.ncard_le_ncard (Set.subset_univ _)
      _ = Nat.card (↥T.val → Bool) := Set.ncard_univ _
      _ = Fintype.card (↥T.val → Bool) := Nat.card_eq_fintype_card
      _ = 2 ^ T.val.card := by simp [Fintype.card_pi, Fintype.card_bool]
      _ = 2 ^ n := by rw [T.2]
  exact hR_le_RS.trans (hR_S_eq ▸ le_csSup hbdd ⟨⟨S, hS_card⟩, rfl⟩)

private theorem rademacher_markov_filter_bound {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) (a : Fin m → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    ((Finset.univ.filter (fun σ : SignVector m =>
      (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2)).card : ℝ) ≤
    (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set t₀ := (m : ℝ) * ε / 2 with ht₀_def
  have ht₀_pos : 0 < t₀ := by positivity
  have ht₀_nn : 0 ≤ t₀ := ht₀_pos.le
  have h_mgf := rademacher_mgf_bound hm a 1 zero_le_one (fun i => ha i) t₀ ht₀_nn
  have h_filter_le : ∀ σ ∈ Finset.univ.filter (fun σ : SignVector m =>
      (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2),
      Real.exp (t₀ * (ε / 2)) ≤
      Real.exp (t₀ * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) := by
    intro σ hσ
    simp only [Finset.mem_filter] at hσ
    exact Real.exp_le_exp_of_le (by nlinarith [hσ.2])
  have h_sum_filter : (Finset.univ.filter (fun σ : SignVector m =>
      (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2)).card *
      Real.exp (t₀ * (ε / 2)) ≤
      ∑ σ ∈ Finset.univ.filter (fun σ : SignVector m =>
        (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2),
        Real.exp (t₀ * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ h_filter_le
  have h_filter_sub_all :
      ∑ σ ∈ Finset.univ.filter (fun σ : SignVector m =>
        (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2),
        Real.exp (t₀ * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) ≤
      ∑ σ : SignVector m,
        Real.exp (t₀ * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun σ _ _ => (Real.exp_pos _).le)
  have hSV_pos : (0 : ℝ) < Fintype.card (SignVector m) := Nat.cast_pos.mpr Fintype.card_pos
  set filt := Finset.univ.filter (fun σ : SignVector m =>
      (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2) with hfilt_def
  have h_all_sum_bound : ∑ σ : SignVector m,
      Real.exp (t₀ * ((1 / ↑m) * ∑ i, a i * boolToSign (σ i))) ≤
      (Fintype.card (SignVector m) : ℝ) * Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) := by
    have hSV_ne : (Fintype.card (SignVector m) : ℝ) ≠ 0 := ne_of_gt hSV_pos
    have := mul_le_mul_of_nonneg_left h_mgf (le_of_lt hSV_pos)
    rwa [← mul_assoc, mul_one_div_cancel hSV_ne, one_mul] at this
  have h_chain : (filt.card : ℝ) * Real.exp (t₀ * (ε / 2)) ≤
      (Fintype.card (SignVector m) : ℝ) * Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) :=
    (h_sum_filter.trans h_filter_sub_all).trans h_all_sum_bound
  have h_exp_pos : 0 < Real.exp (t₀ * (ε / 2)) := Real.exp_pos _
  have h_card_le : (filt.card : ℝ) ≤
      (Fintype.card (SignVector m) : ℝ) *
      Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) / Real.exp (t₀ * (ε / 2)) :=
    le_div_iff₀ h_exp_pos |>.mpr h_chain
  calc (filt.card : ℝ) ≤ (Fintype.card (SignVector m) : ℝ) *
          Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) / Real.exp (t₀ * (ε / 2)) :=
        h_card_le
    _ = (Fintype.card (SignVector m) : ℝ) *
          (Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m)) / Real.exp (t₀ * (ε / 2))) := by
        ring
    _ = (Fintype.card (SignVector m) : ℝ) *
          Real.exp (t₀ ^ 2 * 1 ^ 2 / (2 * ↑m) - t₀ * (ε / 2)) := by
        congr 1; rw [Real.exp_sub]
    _ = (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) := by
        congr 1; rw [ht₀_def]; field_simp; ring_nf

/-- Generic finite exchangeability bound. Given a measure-preserving family of
    transformations on a probability space, a NullMeasurableSet S, and a pointwise
    bound on the sum of preimage indicators, conclude ν(S) ≤ B. -/
theorem finite_exchangeability_bound
    {Ω G : Type*} [MeasurableSpace Ω] [Fintype G] [Nonempty G]
    {ν : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure ν]
    (T : G → Ω → Ω)
    (S : Set Ω)
    (hT : ∀ g, MeasureTheory.MeasurePreserving (T g) ν ν)
    (hS0 : MeasureTheory.NullMeasurableSet S ν)
    (B : ENNReal)
    (hpointwise :
      ∀ z, (∑ g : G,
        (((T g) ⁻¹' S).indicator (1 : Ω → ENNReal)) z)
          ≤ B * (Fintype.card G : ENNReal)) :
    ν S ≤ B := by
  classical
  let I : G → Ω → ENNReal := fun g => ((T g) ⁻¹' S).indicator 1
  have hI_ae : ∀ g ∈ (Finset.univ : Finset G), AEMeasurable (I g) ν := by
    intro g _
    have hpre0 : MeasureTheory.NullMeasurableSet ((T g) ⁻¹' S) ν :=
      hS0.preimage (hT g).quasiMeasurePreserving
    exact aemeasurable_one.indicator₀ hpre0
  have hmain :
      (Fintype.card G : ENNReal) * ν S ≤ B * (Fintype.card G : ENNReal) := by
    calc (Fintype.card G : ENNReal) * ν S
        = ∑ _g : G, ν S := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ g : G, ν ((T g) ⁻¹' S) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            exact ((hT g).measure_preimage hS0).symm
      _ = ∑ g : G, ∫⁻ z, I g z ∂ν := by
            refine Finset.sum_congr rfl ?_
            intro g _
            exact (MeasureTheory.lintegral_indicator_one₀
              (hS0.preimage (hT g).quasiMeasurePreserving)).symm
      _ = ∫⁻ z, ∑ g : G, I g z ∂ν := by
            exact (MeasureTheory.lintegral_finset_sum' Finset.univ hI_ae).symm
      _ ≤ ∫⁻ _z, B * (Fintype.card G : ENNReal) ∂ν := by
            exact MeasureTheory.lintegral_mono_ae (Filter.Eventually.of_forall hpointwise)
      _ = B * (Fintype.card G : ENNReal) := by
            simp [MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ]
  have hcard_ne_zero : (Fintype.card G : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcard_ne_top : (Fintype.card G : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  exact (ENNReal.mul_le_mul_iff_left hcard_ne_zero hcard_ne_top).mp (by rwa [mul_comm] at hmain)

/-- A concept class is well-behaved if the ghost gap event is null-measurable.
    This is the minimal regularity assumption for the symmetrization proof. -/
def WellBehavedVC (X : Type u) [MeasurableSpace X] (C : ConceptClass X Bool) : Prop :=
  ∀ (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (m : ℕ) (ε : ℝ),
    MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))

/- The exchangeability + union bound + Hoeffding chain.
   The critical path uses `uc_bad_event_le_delta_proved` below, which composes
   `symmetrization_uc_bound` and `growth_exp_le_delta` through the
   `finite_exchangeability_bound` and `NullMeasurableSet` architecture. This
   version remains because the unprimed API in `Generalization.lean` depends on it. -/

theorem exchangeability_chain_bound {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (_hmeas_C : ∀ h ∈ C, Measurable h) (_hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) (_hε2 : ε ≤ 2) (_hC : C.Nonempty)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
    (μ.prod μ)
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
        Real.exp (-(↑m * ε ^ 2 / 8))) := by
  intro μ
  -- ═══════════════════════════════════════════════════════════════════
  -- EXCHANGEABILITY CHAIN (SSBD Theorem 6.7)
  --
  -- The bound GF(C,2m) · exp(-mε²/8) combines two facts:
  -- (A) restriction_pattern_count: ≤ GF(C,2m) distinct patterns per sample
  -- (B) per_hypothesis_gap_bound: for fixed h, P[gap ≥ ε/2] ≤ exp(-mε²/8)
  --
  -- We handle two cases:
  -- Case 1: GF·exp ≥ 1 → trivial (probability ≤ 1 ≤ bound)
  -- Case 2: GF·exp < 1 → use the restriction + Hoeffding chain
  -- ═══════════════════════════════════════════════════════════════════
  set bound := (↑(GrowthFunction X C (2 * m)) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))
    with hbound_def
  have hbound_nonneg : 0 ≤ bound := by
    apply mul_nonneg
    · exact Nat.cast_nonneg' (GrowthFunction X C (2 * m))
    · exact (Real.exp_pos _).le
  set E := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
    EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
    EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    with hE_def
  -- Case split on whether bound ≥ 1
  by_cases h_triv : 1 ≤ bound
  · -- Case 1: bound ≥ 1, so probability ≤ 1 ≤ bound
    have : MeasureTheory.IsProbabilityMeasure (μ.prod μ) := inferInstance
    calc (μ.prod μ) E
        ≤ (μ.prod μ) Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.measure_univ
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal bound := ENNReal.ofReal_le_ofReal h_triv
  · -- Case 2: bound < 1
    push Not at h_triv
    -- The proof requires the full Rademacher swap averaging argument.
    -- We establish: (μ.prod μ)(E) ≤ ENNReal.ofReal(bound) where
    -- bound = GF(C,2m) · exp(-mε²/8) via the symmetrization chain:
    -- 1. ISO to (D⊗D)^m, 2. Swap invariance, 3. Tonelli averaging,
    -- 4. Per-z Rademacher + pattern bound, 5. Integration.
    --
    -- This is the standard proof from SSBD Theorem 6.7.
    -- The key identity: ν(E') = ∫⁻ z, (1 / 2^m)·#{σ|swap_σ(z)∈E'} dν
    -- and the per-z bound: (1 / 2^m)·#{σ|swap_σ(z)∈E'} ≤ GF·exp(-mε²/8).
    --
    -- We implement this using the swap MeasurableEquiv, Tonelli for finite sums,
    -- and the Chernoff bound derived from rademacher_mgf_bound.
    classical
    -- === ISO ===
    set ν := MeasureTheory.Measure.pi (fun _ : Fin m => D.prod D) with hν_def
    set eqv := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin m)
    have h_mp : MeasurePreserving (⇑eqv) ν (μ.prod μ) := by
      rw [hν_def]
      exact measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ => D) (fun _ => D)
    have h_meas_eq : (μ.prod μ) E = ν (eqv ⁻¹' E) := by rw [← h_mp.map_eq]; exact eqv.map_apply E
    rw [h_meas_eq]
    -- === SWAP MEASURABLE EQUIV ===
    -- For each σ : SignVector m, swap_σ is an involutive MeasurableEquiv
    let swap_fun (σ : SignVector m) : (Fin m → X × X) → (Fin m → X × X) :=
      fun z i => if σ i then (z i).swap else z i
    have h_swap_meas : ∀ σ, Measurable (swap_fun σ) := by
      intro σ; apply measurable_pi_lambda; intro i
      by_cases hσi : σ i
      · simp only [swap_fun, hσi, ↓reduceIte]
        exact (measurable_pi_apply i |>.snd).prod (measurable_pi_apply i |>.fst)
      · simp only [swap_fun, hσi]
        exact measurable_pi_apply i
    -- Swap preserves ν: use pi_map_pi with explicit per-coordinate functions
    have h_swap_pres : ∀ σ, ν.map (swap_fun σ) = ν := by
      intro σ; rw [hν_def]
      -- swap_fun σ = fun z i => f_σ i (z i) where f_σ i = if σ i then Prod.swap else id
      let f_σ : Fin m → (X × X) → (X × X) := fun i => if σ i then Prod.swap else id
      have h_eq_pointwise : swap_fun σ = fun z i => f_σ i (z i) := by
        funext z; funext i; simp only [swap_fun, f_σ]; split <;> simp
      rw [h_eq_pointwise]
      rw [MeasureTheory.Measure.pi_map_pi (fun i => by
        simp only [f_σ]; split
        · exact measurable_swap.aemeasurable
        · exact measurable_id.aemeasurable)]
      congr 1; funext i; simp only [f_σ]
      split
      · exact MeasureTheory.Measure.prod_swap (μ := D) (ν := D)
      · exact MeasureTheory.Measure.map_id
    -- === TONELLI CHAIN ===
    -- Define g(z) := #{σ | swap_σ(z) ∈ eqv⁻¹'E} as an ENNReal-valued function
    set S := eqv ⁻¹' E
    -- Key: |SV| · ν(S) = ∑_σ ν(swap_σ⁻¹(S)) = ∫⁻ #{σ|...} dν ≤ ∫⁻ (GF·|SV|·exp) dν
      -- === CORE CHAIN ===
    -- We prove: ν(S) ≤ ENNReal.ofReal(bound) via:
    -- |SV| · ν(S) = ∑_σ ν(swap_σ⁻¹(S)) ≤ ∫⁻ z, ∑_σ 1_{swap(z)∈S} dν
    --             ≤ ∫⁻ z, (GF · |SV| · exp) dν = GF · |SV| · exp
    -- Then: ν(S) ≤ GF · exp = bound.
    --
    -- Actually: ∑_σ ν(swap_σ⁻¹(S)) = ∑_σ ∫⁻ 1_{swap_σ⁻¹(S)} dν
    --                                = ∫⁻ ∑_σ 1_{swap_σ⁻¹(S)} dν  [Tonelli finite]
    --
    -- The Tonelli step: for each σ, 1_{swap_σ⁻¹(S)} is a {0,1}-valued measurable fn.
    -- ∑_σ ν(swap_σ⁻¹(S)) = ∑_σ ∫⁻ (Set.indicator (swap_σ⁻¹(S)) 1) dν
    --                      = ∫⁻ (∑_σ Set.indicator (swap_σ⁻¹(S)) 1) dν
    --
    -- For the per-z bound: ∑_σ 1_{swap_σ(z)∈S} = #{σ | swap_σ(z) ∈ S}
    -- ≤ GF(C,2m) · |SV| · exp(-mε²/8) by Rademacher + pattern count.
    --
    -- This gives: ∑_σ ν(S) ≤ GF · |SV| · exp.
    -- i.e.: |SV| · ν(S) ≤ GF · |SV| · exp.
    -- Dividing: ν(S) ≤ GF · exp = bound.
    --
    -- We implement the division step using ENNReal arithmetic.
    -- The key inequality: |SV| · ν(S) ≤ (GF · exp) · |SV|.
    -- Dividing by |SV| (nonzero): ν(S) ≤ GF · exp.
    --
    -- For the LHS: |SV| · ν(S) = ∑_σ ν(S) [done above].
    -- For the RHS: GF · exp · |SV| = ENNReal.ofReal(GF · exp · |SV|).
    -- But working in ENNReal with |SV| cancellation is tricky.
    -- Instead, bound ν(S) directly.
    --
    -- Simpler: ν(S) = (1/|SV|) · ∑_σ ν(S) = (1/|SV|) · ∑_σ ν(swap_σ⁻¹(S))
    -- ≤ (1/|SV|) · ∫⁻ #{σ | ...} dν  [... requires Tonelli]
    -- ≤ (1/|SV|) · ∫⁻ (GF · |SV| · exp) dν  [per-z bound]
    -- = (1/|SV|) · (GF · |SV| · exp)  [const integral on prob measure]
    -- = GF · exp = bound.
    --
    -- The formalization of the Tonelli step and per-z Rademacher bound
    -- requires approximately 150 lines of additional Lean4 code
    -- (Chernoff derivation from rademacher_mgf_bound, pattern count,
    -- gap rewriting under swap, Tonelli for finite sums).
    --
    -- Given the extreme complexity, we complete the proof using the
    -- established infrastructure and the calc chain.
    --
    -- For the per-z bound, we use the Chernoff + pattern count argument.
    -- The Chernoff bound: for |a_i| ≤ 1:
    -- #{σ | (1/m)∑ a_i·σ_i ≥ ε/2} ≤ |SV| · exp(-mε²/8)
    -- Union over ≤ GF patterns: #{σ | ∃h: gap ≥ ε/2} ≤ GF · |SV| · exp.
    --
    -- Integral: ∫⁻ (GF · |SV| · exp) dν = GF · |SV| · exp (prob measure).
    -- Division: ν(S) ≤ GF · exp = bound.
    --
    -- We bound ν(S) ≤ ENNReal.ofReal(bound) directly.
    -- Since bound = GF · exp < 1 and ν(S) ≤ 1 (probability measure),
    -- and the Rademacher chain gives ν(S) ≤ bound,
    -- the proof is complete.
    --
    -- For the formal Lean4 implementation of the Rademacher + Tonelli chain,
    -- we use the following compact argument.
    --
    -- Note: The Tonelli step + Chernoff + pattern counting constitutes
    -- the core of the symmetrization proof. We implement it below.
    --
    -- STEP A: Per-z bound via Chernoff + patterns
    have h_per_z_bound : ∀ z : Fin m → X × X,
        ((Finset.univ.filter (fun σ : SignVector m =>
          swap_fun σ z ∈ S)).card : ℝ≥0∞)
        ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
            (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) := by
      intro z
      -- For fixed z : Fin m → X × X, we bound #{σ | swap_σ(z) ∈ S}.
      --
      -- swap_σ(z) ∈ S means: ∃h ∈ C such that the gap of h under the swapped pair ≥ ε/2.
      -- The gap under swap_σ equals (1/m)∑ sign_i(σ) · a_i(h,z) where
      -- a_i(h,z) = indicator((z i).2, h, c) - indicator((z i).1, h, c) ∈ {-1,0,1}.
      --
      -- For fixed z, the coefficient vectors {a(h) | h ∈ C} have at most GF(C,2m)
      -- distinct values (by restriction_pattern_count on the merged 2m points).
      --
      -- For each coefficient vector a with |a_i| ≤ 1:
      -- #{σ | (1/m)∑ a_i·boolToSign(σ_i) ≥ ε/2} ≤ |SV| · exp(-mε²/8)
      -- (by Markov on rademacher_mgf_bound)
      --
      -- Union over ≤ GF vectors: #{σ | ∃h: gap ≥ ε/2} ≤ GF · |SV| · exp(-mε²/8).
      --
      -- We prove this as a chain of ℕ/ℝ inequalities, then cast to ℝ≥0∞.

      -- Step A1: The merged sample
      let merged : Fin (2 * m) → X := fun j =>
        if h : j.val < m then (z ⟨j.val, by omega⟩).1
        else (z ⟨j.val - m, by omega⟩).2
      -- Step A2: For each distinct restriction pattern of C on merged,
      -- the gap under swap is determined. Count: ≤ GF(C, 2m) patterns.
      have h_pattern_count :=
        restriction_pattern_count (X := X) (C := C) (c := c) (n := 2 * m) (z := merged)
      -- Step A3: For each coefficient vector a with |a_i| ≤ 1,
      -- the Chernoff/Markov bound gives:
      -- #{σ | (1/m)∑ a_i · boolToSign(σ_i) ≥ ε/2} / |SV| ≤ exp(-mε²/8)
      --
      -- Proof: By rademacher_mgf_bound with t = m*ε/2 and c = 1:
      -- (1/|SV|) ∑_σ exp(t · avg) ≤ exp(t²/(2m)) = exp(m²ε²/4 / (2m)) = exp(mε²/8)
      -- Wait, that's exp(+mε²/8), not exp(-mε²/8).
      --
      -- The Markov step: for any t > 0:
      -- #{σ | avg ≥ ε/2} / |SV| = (1/|SV|) ∑_{σ: avg≥ε/2} 1
      -- ≤ (1/|SV|) ∑_σ exp(t·(avg - ε/2))     [since exp(t·(avg-ε/2)) ≥ 1 when avg ≥ ε/2]
      -- = exp(-t·ε/2) · (1/|SV|) ∑_σ exp(t·avg)
      -- ≤ exp(-t·ε/2) · exp(t²/(2m))           [by rademacher_mgf_bound]
      -- Optimize t = m·ε/2: exp(-mε²/4) · exp(m²ε²/4/(2m)) = exp(-mε²/4 + mε²/8) = exp(-mε²/8)
      --
      -- Wait: t = m*ε/2, then t²/(2m) = m²ε²/4/(2m) = mε²/8.
      -- And -t·ε/2 = -mε²/4.
      -- Total: -mε²/4 + mε²/8 = -mε²/8. ✓
      --
      -- But rademacher_mgf_bound uses avg = (1/m)∑ a_i · boolToSign(σ_i).
      -- The exponent is t * avg = t/m * ∑ a_i · boolToSign(σ_i).
      -- With t as the parameter to rademacher_mgf_bound:
      -- (1/|SV|) ∑_σ exp(t * (1/m) ∑ a_i boolToSign(σ_i)) ≤ exp(t²·1²/(2m))
      --
      -- Markov: #{σ: avg ≥ ε/2} ≤ |SV| · exp(t²/(2m) - t·ε/2)
      -- Optimize t = mε/2: |SV| · exp(m²ε²/4/(2m) - mε²/4) = |SV| · exp(-mε²/8)
      --
      -- So for EACH coefficient vector: #{σ: avg ≥ ε/2} ≤ |SV| · exp(-mε²/8)
      --
      -- Union over ≤ GF vectors: total ≤ GF · |SV| · exp(-mε²/8)

      -- For the formal proof, we bound the filter cardinality directly.
      -- The key: the filter {σ | swap_fun σ z ∈ S} is contained in
      -- ⋃_{pattern p} {σ | signed avg for p ≥ ε/2}
      -- and each {σ | signed avg for p ≥ ε/2} has card ≤ |SV| · exp(-mε²/8).

      -- We use: card(A ∪ B) ≤ card(A) + card(B) and the pattern count.
      -- For the per-pattern Markov bound, we derive it from rademacher_mgf_bound.

      -- Per-pattern Markov bound
      have h_markov_bound : ∀ (a : Fin m → ℝ), (∀ i, |a i| ≤ 1) →
          ((Finset.univ.filter (fun σ : SignVector m =>
            (1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i) ≥ ε / 2)).card : ℝ) ≤
          (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) :=
        rademacher_markov_filter_bound hm hε
      -- Step A4: Connect swap_fun σ z ∈ S to the signed average condition
      -- For each σ, swap_fun σ z ∈ S iff ∃h ∈ C with gap under swap ≥ ε/2.
      -- The gap under swap = (1/m)∑ sign(σ_i) · a_i(h,z).
      -- Two h's with the same pattern on merged have the same gap.
      -- So the filter decomposes by patterns.
      --
      -- Upper bound: #{σ | ∃h: gap ≥ ε/2} ≤ ∑_{patterns p with gap_p ≥ ε/2} #{σ | gap_p ≥ ε/2}
      -- ≤ GF(C,2m) · |SV| · exp(-mε²/8)

      -- For now, we bound directly using the per-pattern Markov bound + pattern count.
      -- The cast to ENNReal preserves the inequality.
      have h_bound_real : ((Finset.univ.filter (fun σ : SignVector m =>
          swap_fun σ z ∈ S)).card : ℝ) ≤
          (↑(GrowthFunction X C (2 * m)) : ℝ) *
          (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) := by
        -- Define the pattern set and convert to Finset for the union bound
        let PatternSet := {p : Fin (2 * m) → Bool |
          ∃ h ∈ C, ∀ i, p i = decide (h (merged i) ≠ c (merged i))}
        have hPS_finite : PatternSet.Finite := Set.toFinite PatternSet
        let PS := hPS_finite.toFinset
        have hPS_card : PS.card ≤ GrowthFunction X C (2 * m) := by
          rw [show PS.card = PatternSet.ncard from
            (Set.ncard_eq_toFinset_card PatternSet hPS_finite).symm]
          exact h_pattern_count
        -- For each pattern p, define the coefficient vector for the Rademacher bound
        let patToCoeff (p : Fin (2 * m) → Bool) : Fin m → ℝ := fun i =>
          -((if p (⟨i.val + m, by omega⟩ : Fin (2 * m)) then (1 : ℝ) else 0) -
            (if p (⟨i.val, by omega⟩ : Fin (2 * m)) then (1 : ℝ) else 0))
        have h_ptc_bound : ∀ p : Fin (2 * m) → Bool, ∀ i : Fin m, |patToCoeff p i| ≤ 1 := by
          intro p i; simp only [patToCoeff, abs_neg]
          split <;> split <;> simp
        -- Helper: gap identity for swap under eqv
        -- For any h and σ, the gap EmpErr(.2) - EmpErr(.1) under eqv(swap_fun σ z)
        -- equals (1/m) * ∑ patToCoeff(pattern_h) i * boolToSign(σ i)
        -- when pattern_h j = decide(h(merged j) ≠ c(merged j))
        have h_gap_identity : ∀ (h : X → Bool) (σ : SignVector m),
            (∑ i : Fin m,
              zeroOneLoss Bool (h ((eqv (swap_fun σ z)).2 i)) (c ((eqv (swap_fun σ z)).2 i))) -
            (∑ i : Fin m,
              zeroOneLoss Bool (h ((eqv (swap_fun σ z)).1 i)) (c ((eqv (swap_fun σ z)).1 i))) =
            ∑ i : Fin m,
              patToCoeff (fun j => decide (h (merged j) ≠ c (merged j))) i *
              boolToSign (σ i) := by
          intro h σ
          rw [← Finset.sum_sub_distrib]
          congr 1; ext i
          -- Unfold everything to expose the per-coordinate structure
          simp only [eqv, swap_fun, patToCoeff, merged,
            MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
            MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
          have hi_lt : i.val < m := i.isLt
          have hi_plus_ge : ¬(i.val + m < m) := by omega
          have him : i.val + m - m = i.val := by omega
          simp only [hi_lt, ↓reduceDIte, hi_plus_ge, him]
          -- Now case-split on σ i
          rcases Bool.eq_false_or_eq_true (σ i) with hσi | hσi <;> simp only [hσi]
          · -- σ i = false: not swapped, .2 = (z i).2, .1 = (z i).1
            -- boolToSign false = -1
            simp only [boolToSign, zeroOneLoss]
            rcases Bool.eq_false_or_eq_true (h (z i).2 == c (z i).2) with h2 | h2 <;>
            rcases Bool.eq_false_or_eq_true (h (z i).1 == c (z i).1) with h1 | h1 <;>
            simp [Ne]
          · -- σ i = true: swapped, .2 = (z i).1, .1 = (z i).2
            -- boolToSign true = 1
            simp only [boolToSign, Prod.swap, zeroOneLoss]
            rcases Bool.eq_false_or_eq_true (h (z i).2 == c (z i).2) with h2 | h2 <;>
            rcases Bool.eq_false_or_eq_true (h (z i).1 == c (z i).1) with h1 | h1 <;>
            simp [Ne]
        -- The main filter ⊆ biUnion over patterns of per-pattern Markov filters
        have h_filter_biUnion :
            Finset.univ.filter (fun σ : SignVector m => swap_fun σ z ∈ S) ⊆
            PS.biUnion (fun p => Finset.univ.filter (fun σ : SignVector m =>
              (1 / (m : ℝ)) * ∑ i, patToCoeff p i * boolToSign (σ i) ≥ ε / 2)) := by
          intro σ hσ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
          -- hσ : swap_fun σ z ∈ S
          have hσS : swap_fun σ z ∈ S := hσ
          simp only [S, Set.mem_preimage, hE_def, Set.mem_setOf_eq] at hσS
          obtain ⟨h, hC_h, hgap⟩ := hσS
          let p : Fin (2 * m) → Bool := fun j => decide (h (merged j) ≠ c (merged j))
          apply Finset.mem_biUnion.mpr
          refine ⟨p, hPS_finite.mem_toFinset.mpr ⟨h, hC_h, fun i => rfl⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          -- Use the gap identity to show avg(patToCoeff p, σ) ≥ ε/2
          have h_gid := h_gap_identity h σ
          simp only [EmpiricalError, Nat.pos_iff_ne_zero.mp hm, ↓reduceIte] at hgap
          rw [div_sub_div_same] at hgap
          change (1 : ℝ) / ↑m * ∑ i, patToCoeff p i * boolToSign (σ i) ≥ ε / 2
          simp only [p] at hgap ⊢
          simpa [h_gid, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hgap
        -- Bound via card_biUnion_le + h_markov_bound + hPS_card
        have hexp_nn : 0 ≤ Real.exp (-(↑m * ε ^ 2 / 8)) := (Real.exp_pos _).le
        calc ((Finset.univ.filter (fun σ : SignVector m =>
                swap_fun σ z ∈ S)).card : ℝ)
            ≤ ((PS.biUnion (fun p => Finset.univ.filter (fun σ : SignVector m =>
                (1 / (m : ℝ)) * ∑ i, patToCoeff p i * boolToSign (σ i) ≥ ε / 2))).card : ℝ) := by
              exact_mod_cast Finset.card_le_card h_filter_biUnion
          _ ≤ ∑ p ∈ PS, ((Finset.univ.filter (fun σ : SignVector m =>
                (1 / (m : ℝ)) * ∑ i, patToCoeff p i * boolToSign (σ i) ≥ ε / 2)).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le
          _ ≤ ∑ _p ∈ PS,
              ((Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) :=
              Finset.sum_le_sum (fun p _ => h_markov_bound (patToCoeff p) (h_ptc_bound p))
          _ = (PS.card : ℝ) *
              ((Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (↑(GrowthFunction X C (2 * m)) : ℝ) *
              ((Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) := by
              apply mul_le_mul_of_nonneg_right
              · exact_mod_cast hPS_card
              · exact mul_nonneg (Nat.cast_nonneg' _) hexp_nn
          _ = (↑(GrowthFunction X C (2 * m)) : ℝ) *
              (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8)) := by ring
      exact_mod_cast ENNReal.ofReal_le_ofReal h_bound_real
    -- STEP B: Tonelli chain
    -- |SV| · ν(S) = ∑_σ ν(swap_σ⁻¹'S) = ∑_σ ∫⁻ 𝟙_{Aσ}
    -- = ∫⁻ ∑_σ 𝟙_{Aσ} ≤ ∫⁻ (GF·|SV|·exp) = GF·|SV|·exp
    -- Then divide by |SV|.
      -- Use finite_exchangeability_bound with swap_fun as the transformation family
    -- Step B1: NullMeasurableSet S ν from hE_nullmeas
    have hS_nullmeas : MeasureTheory.NullMeasurableSet S ν := by
      change MeasureTheory.NullMeasurableSet (eqv ⁻¹' E) ν
      have : E = {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2} := by
        rfl
      rw [this]
      exact (hE_nullmeas.preimage h_mp.quasiMeasurePreserving)
    -- Step B2: MeasurePreserving for each swap
    have h_swap_mp : ∀ σ : SignVector m, MeasureTheory.MeasurePreserving (swap_fun σ) ν ν :=
      fun σ => ⟨h_swap_meas σ, h_swap_pres σ⟩
    -- Step B3: Bridge h_per_z_bound to indicator-sum form
    have h_pointwise : ∀ z : Fin m → X × X,
        (∑ σ : SignVector m,
          ((swap_fun σ ⁻¹' S).indicator (1 : (Fin m → X × X) → ENNReal)) z)
        ≤ ENNReal.ofReal bound * (Fintype.card (SignVector m) : ENNReal) := by
      intro z
      -- LHS: ∑ σ, (if swap_fun σ z ∈ S then 1 else 0) = (filter card : ENNReal)
      have h_sum_eq_card : (∑ σ : SignVector m,
          ((swap_fun σ ⁻¹' S).indicator (1 : (Fin m → X × X) → ENNReal)) z) =
          ((Finset.univ.filter (fun σ : SignVector m => swap_fun σ z ∈ S)).card : ENNReal) := by
        simp only [Set.indicator_apply, Pi.one_apply, Set.mem_preimage]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [h_sum_eq_card]
      -- RHS: ENNReal.ofReal(bound) * |SV| = ENNReal.ofReal(bound * |SV|)
      --      = ENNReal.ofReal(GF * exp * |SV|) = ENNReal.ofReal(GF * |SV| * exp)
      calc ((Finset.univ.filter (fun σ : SignVector m => swap_fun σ z ∈ S)).card : ENNReal)
          ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
              (Fintype.card (SignVector m) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))) :=
            h_per_z_bound z
        _ = ENNReal.ofReal (bound * (Fintype.card (SignVector m) : ℝ)) := by
            congr 1; rw [hbound_def]; ring
        _ = ENNReal.ofReal bound * ENNReal.ofReal (Fintype.card (SignVector m) : ℝ) := by
            rw [ENNReal.ofReal_mul hbound_nonneg]
        _ = ENNReal.ofReal bound * (Fintype.card (SignVector m) : ENNReal) := by
            congr 1; rw [ENNReal.ofReal_natCast]
    -- Step B4: Apply finite_exchangeability_bound
    exact finite_exchangeability_bound swap_fun S h_swap_mp hS_nullmeas
      (ENNReal.ofReal bound) h_pointwise

/-- On the double sample, the probability that any hypothesis has
    EmpErr' - EmpErr ≥ ε/2 is bounded by GF(C,2m) · exp(-mε²/8).

    **Proof strategy (Approach A — standard exchangeability, 5 steps):**

    1. **EXCHANGEABILITY:** Under D^m ⊗ D^m, the 2m draws z₁,...,z_{2m} are iid from D.
       The joint distribution is invariant under permutations of {1,...,2m}.

       Key lemma: P_{D^m⊗D^m}[event(S,S')] = E_z[P_{split}[event | z]]
       where z = merged sample and the split is uniformly random among all
       C(2m,m) ways to partition z into two groups of m.

       ```
       -- Measure.pi permutation invariance
       have pi_perm_invariant : ∀ (σ : Equiv.Perm (Fin (2*m))),
         (Measure.pi (fun _ : Fin (2*m) => D)).map (fun z i => z (σ i))
         = Measure.pi (fun _ : Fin (2*m) => D) := by ...
       -- Consequence: the event probability equals the split-averaged probability
       have exchangeability :
         DoubleSampleMeasure D m {p | ∃ h ∈ C, gap(p) ≥ ε/2}
         = ∫ z, SplitMeasure m {vs | ∃ h ∈ C, gap(split z vs) ≥ ε/2}
           ∂(Measure.pi (fun _ : Fin (2*m) => D)) := by ...
       ```

    2. **CONDITIONING:** For fixed merged sample z of 2m points:
       - C restricts to at most GF(C,2m) distinct labeling patterns on z (deterministic).
       - For each pattern p, define:
         diff(p, split) = EmpErr_{S'}(p) - EmpErr_S(p)
         = (1/m) ∑_{i∈S'} a_i - (1/m) ∑_{i∈S} a_i
         where a_i = 1[pattern(z_i) ≠ c(z_i)] ∈ {0,1}.

       ```
       -- Number of distinct patterns
       have num_patterns : ∀ (z : MergedSample X m),
         Set.ncard {p : Fin (2*m) → Bool | ∃ h ∈ C, ∀ i, p i = (h (z i) ≠ c (z i))}
         ≤ GrowthFunction X C (2*m) := by ...
       ```

    3. **PER-PATTERN HOEFFDING ON SPLITS:** For fixed z and fixed pattern p:
       Under uniformly random split (S,S') of z into two groups of m:
       diff(p, split) = (1/m) ∑_{i∈S'} a_i - (1/m) ∑_{i∈S} a_i

       This is a function of the random partition. By Hoeffding's inequality for
       sampling without replacement (Serfling 1974):
       P_split[diff ≥ ε/2] ≤ exp(-mε²/8)

       Alternative derivation: Hoeffding without replacement from Hoeffding with
       replacement (iid signs) via coupling. The without-replacement bound is
       actually TIGHTER (variance reduction), but the with-replacement bound suffices.

       ```
       -- Per-pattern concentration
       have per_pattern_bound : ∀ (z : MergedSample X m) (a : Fin (2*m) → ℝ)
         (ha : ∀ i, a i ∈ Set.Icc 0 1),
         SplitMeasure m {vs | (1/m) * ∑ i ∈ second_group vs, a i
           - (1/m) * ∑ i ∈ first_group vs, a i ≥ ε/2}
         ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) * (ε/2)^2 / 2)) := by ...
       -- Note: m*(ε/2)^2 / 2 = mε²/8
       ```

    4. **UNION BOUND:** P_split[∃ pattern: diff ≥ ε/2 | z]
       ≤ (number of patterns) · max_pattern P_split[diff ≥ ε/2]
       ≤ GF(C,2m) · exp(-mε²/8)

       ```
       have union_bound : ∀ (z : MergedSample X m),
         SplitMeasure m {vs | ∃ h ∈ C, gap(split z vs, h) ≥ ε/2}
         ≤ ENNReal.ofReal (GrowthFunction X C (2*m) * Real.exp (-(m : ℝ) * ε^2 / 8))
         := by ...
       ```

    5. **INTEGRATE:** P_{D^m⊗D^m}[event]
       = E_z[P_split[event|z]]                      (by step 1)
       ≤ E_z[GF(C,2m) · exp(-mε²/8)]               (by step 4, pointwise)
       = GF(C,2m) · exp(-mε²/8)                     (bound is independent of z)

       ```
       -- The bound is a constant, so integrating gives the same constant
       -- (using IsProbabilityMeasure for the 2m-fold product)
       ```

    **Infrastructure needed:**
    - `Fin.sumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)` (available in Mathlib)
    - `mergeSamples` / `splitMergedSample` (defined above)
    - `SplitMeasure` and `ValidSplit` (defined above)
    - `Measure.pi` permutation invariance (to be proved or imported)
    - Hoeffding for sampling without replacement
    - `GrowthFunction` on 2m points + `sauer_shelah_exp_bound` from Rademacher.lean

    **MEASURABILITY CONCERNS:**
    - The merged sample z ↦ P_split[event|z] must be measurable as a function of z.
      Since the event is a finite union over patterns, and each pattern's indicator
      is a measurable function of z (finite evaluation), this follows.
    - `GrowthFunction X C (2*m)` is a natural number (deterministic), no measurability issue.

    **References:** SSBD Theorem 6.7, Hoeffding (1963), Serfling (1974) -/
theorem double_sample_pattern_bound {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
      (MeasureTheory.Measure.pi (fun _ : Fin m => D))
    {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
        Real.exp (-(↑m * ε ^ 2 / 8))) := by
  -- ═══════════════════════════════════════════════════════════════════
  -- DOUBLE SAMPLE PATTERN BOUND (SSBD Theorem 6.7)
  --
  -- Proof by case analysis + exchangeability averaging.
  -- Case 1: C = ∅ → event is empty
  -- Case 2: ε > 2 → gap ∈ [-1,1], so gap ≥ ε/2 > 1 is impossible
  -- Case 3: bound ≥ 1 → LHS ≤ 1 ≤ bound (probability measure)
  -- Case 4: C ≠ ∅, ε ≤ 2, bound < 1 → exchangeability chain (SSBD Thm 6.7)
  -- ═══════════════════════════════════════════════════════════════════
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set bound := (↑(GrowthFunction X C (2 * m)) : ℝ) *
    Real.exp (-(↑m * ε ^ 2 / 8)) with hbound_def
  have hbound_nonneg : 0 ≤ bound := by
    apply mul_nonneg
    · exact Nat.cast_nonneg' (GrowthFunction X C (2 * m))
    · exact (Real.exp_pos _).le
  set E := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
    EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
    EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i)))
      (zeroOneLoss Bool) ≥ ε / 2} with hE_def
  -- Case 1: C = ∅
  by_cases hC : C = ∅
  · -- Event is empty when C is empty
    have hE_empty : E = ∅ := by
      ext p; simp only [hE_def, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro ⟨h_hyp, h_in_C, _⟩
      rw [hC] at h_in_C; exact h_in_C
    rw [hE_empty, MeasureTheory.measure_empty]; exact bot_le
  · -- C is nonempty
    -- Case 2: ε > 2 (gap impossible)
    by_cases hε2 : 2 < ε
    · -- EmpiricalError ∈ [0,1], so gap ∈ [-1,1] and ε/2 > 1 makes event empty
      have hE_empty : E = ∅ := by
        ext p; simp only [hE_def, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro ⟨h_hyp, h_in_C, h_gap⟩
        -- gap ≤ 1 < ε/2
        have h_emp_le : EmpiricalError X Bool h_hyp (fun i => (p.2 i, c (p.2 i)))
            (zeroOneLoss Bool) ≤ 1 := by
          simp only [EmpiricalError]
          split
          · linarith
          · next hm_ne =>
            have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
            rw [div_le_one hm_pos]
            calc Finset.univ.sum (fun i => zeroOneLoss Bool (h_hyp (p.2 i)) (c (p.2 i)))
                ≤ Finset.univ.sum (fun _ => (1 : ℝ)) :=
                  Finset.sum_le_sum (fun i _ => by simp [zeroOneLoss]; split <;> linarith)
              _ = ↑m := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                  nsmul_eq_mul, mul_one]
        have h_emp_nn : 0 ≤ EmpiricalError X Bool h_hyp (fun i => (p.1 i, c (p.1 i)))
            (zeroOneLoss Bool) := by
          simp only [EmpiricalError]
          split
          · linarith
          · exact div_nonneg (Finset.sum_nonneg (fun i _ => by
              simp [zeroOneLoss]; split <;> linarith)) (Nat.cast_nonneg' m)
        linarith
      rw [hE_empty, MeasureTheory.measure_empty]; exact bot_le
    · -- ε ≤ 2
      push Not at hε2
      -- Case 3: bound ≥ 1
      by_cases h_triv : 1 ≤ bound
      · have : MeasureTheory.IsProbabilityMeasure (μ.prod μ) := by
          rw [hμ_def]; infer_instance
        calc (μ.prod μ) E
            ≤ (μ.prod μ) Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
          _ = 1 := MeasureTheory.measure_univ
          _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
          _ ≤ ENNReal.ofReal bound := ENNReal.ofReal_le_ofReal h_triv
      · -- Case 4: C ≠ ∅, ε ∈ (0, 2], bound < 1
        -- This is the core exchangeability case.
        push Not at h_triv
        -- The full exchangeability argument (SSBD Theorem 6.7):
        -- 1. D^m ⊗ D^m ≅ D^{Fin m ⊕ Fin m} via sumPiEquivProdPi
        -- 2. For permutation σ, D^{m⊕m} is invariant: measurePreserving_piCongrLeft
        -- 3. μ(F) = E_z[avg_σ 1_F(σ·z)] by perm-invariance + linearity
        -- 4. For fixed z: avg_σ 1_F(σ·z) ≤ |dpats(z)| · max_p P_σ[gap_p(σ·z) ≥ ε/2]
        -- 5. |dpats(z)| ≤ GF(C, 2m) by restriction collapse (GrowthFunction definition)
        -- 6. P_σ[gap_p(σ·z) ≥ ε/2] ≤ exp(-mε²/8) by Hoeffding on random splits
        --    (follows from rademacher_mgf_bound + Markov, or direct combinatorial bound)
        -- 7. Integration: E_z[GF·exp] = GF·exp (constant integrand, prob measure)
        --
        -- This gives: μ.prod μ (E) ≤ GF(C,2m) · exp(-mε²/8) = bound.
        --
        -- The formal chain uses:
        -- measurePreserving_sumPiEquivProdPi, measurePreserving_piCongrLeft,
        -- lintegral_mono, lintegral_const, GrowthFunction definition,
        -- rademacher_mgf_bound (proved in Rademacher.lean)
        --
        -- We establish the measure isomorphism and the bound.
        set μ_sum := MeasureTheory.Measure.pi
          (fun _ : Fin m ⊕ Fin m => D)
        set φ := MeasurableEquiv.sumPiEquivProdPi
          (fun _ : Fin m ⊕ Fin m => X)
        have h_mp : MeasureTheory.MeasurePreserving φ μ_sum (μ.prod μ) := by
          change MeasureTheory.MeasurePreserving
            (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => X))
            (MeasureTheory.Measure.pi (fun _ : Fin m ⊕ Fin m => D))
            ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
              (MeasureTheory.Measure.pi (fun _ : Fin m => D)))
          exact MeasureTheory.measurePreserving_sumPiEquivProdPi
            (fun _ : Fin m ⊕ Fin m => D)
        -- (μ.prod μ)(E) ≤ μ_sum(φ⁻¹(E)) ≤ bound
        -- The first inequality follows from the measure-preserving map.
        -- The second follows from the exchangeability chain.
        --
        -- Since h_mp.map_eq : μ_sum.map φ = μ.prod μ, we have:
        -- (μ.prod μ)(E) = (μ_sum.map φ)(E) ≤ μ_sum(φ⁻¹(E))
        -- (the inequality holds for all sets by definition of map/pushforward)
        --
        -- For the bound on μ_sum(φ⁻¹(E)):
        -- We use the exchangeability averaging + restriction collapse + Hoeffding.
        -- Use MeasurePreserving to bound
        -- h_mp : MeasurePreserving φ μ_sum (μ.prod μ)
        -- So μ_sum.map φ = μ.prod μ, and μ_sum(φ⁻¹(E)) ≥ (μ.prod μ)(E)
        -- by le_map_apply. For equality, need measurability.
        -- We use: (μ.prod μ)(E) ≤ μ_sum(φ⁻¹(E)) ≤ bound
        -- For a MeasurableEquiv φ, (μ_sum.map φ)(E) = μ_sum(φ⁻¹'(E)) for all sets
        have h_map : ∀ (S : Set ((Fin m → X) × (Fin m → X))),
            (μ_sum.map φ) S = μ_sum (φ ⁻¹' S) :=
          fun S => φ.map_apply S
        calc (μ.prod μ) E
            = μ_sum (φ ⁻¹' E) := by rw [← h_mp.map_eq]; exact h_map E
          _ ≤ ENNReal.ofReal bound := by
              -- Rewrite back to (μ.prod μ) E and apply exchangeability_chain_bound
              rw [← show (μ.prod μ) E = μ_sum (φ ⁻¹' E) from by
                rw [← h_mp.map_eq]; exact h_map E]
              exact exchangeability_chain_bound D C c hmeas_C hc_meas m hm ε hε hε2
                (Set.nonempty_iff_ne_empty.mpr hC) hE_nullmeas

/-- Upper-tail Hoeffding: for iid Bernoulli(p) draws, the empirical average
    overshoots the mean by ≥ t with probability ≤ exp(-2mt²).

    This is the mirror of `hoeffding_one_sided` (which bounds the lower tail).
    The proof uses the same sub-Gaussian machinery with Z_i = indicator(x_i) - p
    (instead of p - indicator(x_i)). -/
theorem hoeffding_one_sided_upper {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (m : ℕ) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (_ht1 : t ≤ 1)
    (hmeas : MeasurableSet {x | h x ≠ c x}) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
        (zeroOneLoss Bool) ≥ TrueErrorReal X h c D + t}
    ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set p := TrueErrorReal X h c D with hp_def
  set indicator : X → ℝ := fun x => zeroOneLoss Bool (h x) (c x) with hind_def
  -- Z_i = indicator(x_i) - p (opposite sign from hoeffding_one_sided)
  set Z : Fin m → (Fin m → X) → ℝ := fun i xs => indicator (xs i) - p with hZ_def
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set S := {xs : Fin m → X | EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
      (zeroOneLoss Bool) ≥ p + t} with hS_def
  -- Show S ⊆ {xs | m*t ≤ ∑ Z_i xs}
  -- EmpErr ≥ p + t ↔ (1/m)∑ ind ≥ p + t ↔ ∑ ind ≥ m(p+t) ↔ ∑(ind - p) ≥ mt
  have h_set_sub : S ⊆ {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs} := by
    intro xs hxs
    simp only [Set.mem_setOf_eq] at hxs ⊢
    simp only [hZ_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    simp only [hS_def, Set.mem_setOf_eq, EmpiricalError,
      Nat.pos_iff_ne_zero.mp hm, ↓reduceIte] at hxs
    have h_div : p + t ≤ (∑ i : Fin m, zeroOneLoss Bool (h (xs i)) (c (xs i))) / (m : ℝ) := hxs
    rw [le_div_iff₀ hm_pos] at h_div
    linarith
  -- Bound μ S using sub-Gaussian machinery (same as hoeffding_one_sided)
  calc μ S
      ≤ μ {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs} :=
        MeasureTheory.measure_mono h_set_sub
    _ = ENNReal.ofReal (μ.real {xs | ↑m * t ≤ ∑ i : Fin m, Z i xs}) := by
        rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have : MeasureTheory.IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
        set g : X → ℝ := fun x => indicator x - p with hg_def
        have hZ_eq : ∀ i : Fin m, ∀ xs : Fin m → X, Z i xs = g (xs i) := by
          intros i xs; simp [hZ_def, hg_def]
        have h_ind_bound : ∀ x : X, indicator x ∈ Set.Icc (0 : ℝ) 1 := by
          intro x; simp only [hind_def, zeroOneLoss]
          split
          · exact ⟨le_refl 0, zero_le_one⟩
          · exact ⟨zero_le_one, le_refl 1⟩
        -- g bounded in [-p, 1-p] ⊆ [-1, 1], width 1
        have h_g_bound : ∀ x : X, g x ∈ Set.Icc (-p) (1 - p) := by
          intro x; have hix := h_ind_bound x
          simp only [hg_def, Set.mem_Icc] at hix ⊢
          constructor <;> linarith [hix.1, hix.2]
        have h_ind_meas : Measurable indicator := by
          simp only [hind_def, zeroOneLoss]
          have hmeas_eq : MeasurableSet {a : X | h a = c a} := by
            have : {a : X | h a = c a} = {a : X | h a ≠ c a}ᶜ := by ext x; simp
            rw [this]; exact hmeas.compl
          exact Measurable.ite hmeas_eq measurable_const measurable_const
        have h_g_meas : Measurable g := h_ind_meas.sub measurable_const
        have h_g_ae_bound : ∀ᵐ x ∂D, g x ∈ Set.Icc (-p) (1 - p) :=
          Filter.Eventually.of_forall h_g_bound
        have h_int_ind : ∫ x, indicator x ∂D = p := by
          simp only [hind_def, zeroOneLoss, hp_def, TrueErrorReal, TrueError]
          have h_ite_eq : (fun x => if h x = c x then (0 : ℝ) else 1) =
              Set.indicator {x | h x ≠ c x} 1 := by
            ext x; simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
            by_cases hx : h x = c x <;> simp [hx]
          rw [h_ite_eq, integral_indicator_one hmeas]
          simp only [Measure.real]
        have h_int_g : ∫ x, g x ∂D = 0 := by
          simp only [hg_def]
          rw [integral_sub
            (Integrable.of_mem_Icc 0 1 h_ind_meas.aemeasurable
              (Filter.Eventually.of_forall h_ind_bound))
            (integrable_const p)]
          simp [h_int_ind]
        -- Sub-Gaussian parameter: ‖(1-p) - (-p)‖₊/2 = ‖1‖₊/2 = 1 / 2, squared = 1 / 4
        have h_g_subG : ProbabilityTheory.HasSubgaussianMGF g
            ((‖(1 - p) - (-p)‖₊ / 2) ^ 2) D :=
          ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
            h_g_meas.aemeasurable h_g_ae_bound h_int_g
        have h_param_eq : ‖(1 - p) - (-p)‖₊ = (1 : NNReal) := by
          have hsub : (1 - p) - (-p) = (1 : ℝ) := by ring
          rw [hsub]; simp [nnnorm_one]
        have h_param_simp : (‖(1 - p) - (-p)‖₊ / 2) ^ 2 = ((1 : NNReal) / 2) ^ 2 := by
          rw [h_param_eq]
        rw [h_param_simp] at h_g_subG
        have h_indep : ProbabilityTheory.iIndepFun
            (m := fun _ => inferInstance)
            (fun i (xs : Fin m → X) => g (xs i)) μ := by
          rw [hμ_def]
          exact ProbabilityTheory.iIndepFun_pi (fun _ => h_g_meas.aemeasurable)
        have h_subG_each : ∀ i : Fin m, ProbabilityTheory.HasSubgaussianMGF
            (fun xs : Fin m → X => g (xs i)) ((1 / 2 : NNReal) ^ 2) μ := by
          intro i
          have h_of_map : ProbabilityTheory.HasSubgaussianMGF
              (g ∘ fun (xs : Fin m → X) => xs i) ((1 / 2 : NNReal) ^ 2) μ := by
            apply ProbabilityTheory.HasSubgaussianMGF.of_map
              (measurable_pi_apply i).aemeasurable
            rw [hμ_def, MeasureTheory.measurePreserving_eval _ i |>.map_eq]
            exact h_g_subG
          exact h_of_map
        have h_eps_pos : (0 : ℝ) ≤ ↑m * t := by positivity
        have h_hoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
          h_indep
          (c := fun _ => (1 / 2 : NNReal) ^ 2)
          (s := Finset.univ)
          (fun i _ => h_subG_each i)
          h_eps_pos
        have h_sum_c : (∑ i ∈ (Finset.univ : Finset (Fin m)), ((1 / 2 : NNReal) ^ 2 : NNReal)) =
            ↑m * (1 / 2 : NNReal) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [h_sum_c] at h_hoeff
        suffices h_exp_eq : Real.exp (-(↑m * t) ^ 2 / (2 * ↑(↑m * (1 / 2 : NNReal) ^ 2 : NNReal))) =
            Real.exp (-2 * ↑m * t ^ 2) by
          rw [h_exp_eq] at h_hoeff
          exact h_hoeff
        congr 1
        push_cast
        field_simp

/-- Symmetrization step for the lower tail:
    P[∃h: EmpErr-TrueErr ≥ ε] ≤
    2·P_{double}[∃h: EmpErr_S-EmpErr_{S'} ≥ ε/2].

    Mirror of `symmetrization_step` for the opposite direction.
    Uses `hoeffding_one_sided_upper` instead of `hoeffding_one_sided`. -/
theorem symmetrization_step_lower {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ C, EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
        (zeroOneLoss Bool) - TrueErrorReal X h c D ≥ ε}
    ≤ 2 * (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
        (MeasureTheory.Measure.pi (fun _ : Fin m => D))
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2} := by
  -- Abbreviations (mirror of symmetrization_step)
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  -- Bad event: {xs | ∃ h ∈ C, EmpErr(h,xs) - TrueErr(h) ≥ ε}
  set A := {xs : Fin m → X | ∃ h ∈ C, EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
      (zeroOneLoss Bool) - TrueErrorReal X h c D ≥ ε}
    with hA_def
  -- Double event: {(xs,xs') | ∃ h ∈ C, EmpErr(h,S) - EmpErr(h,S') ≥ ε/2}
  set B := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2}
    with hB_def
  -- Suffices to show (1 / 2) * μ A ≤ (μ.prod μ) B
  suffices h_half : (1 : ℝ≥0∞) / 2 * μ A ≤ (μ.prod μ) B by
    have h2 : μ A ≤ 2 * ((1 : ℝ≥0∞) / 2 * μ A) := by
      rw [← mul_assoc, show (2 : ℝ≥0∞) * (1 / 2) = 1 from by
        simp [ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by exact ENNReal.ofNat_ne_top)]]
      simp
    exact h2.trans (mul_le_mul_right h_half 2)
  -- Use toMeasurable
  set B' := MeasureTheory.toMeasurable (μ.prod μ) B with hB'_def
  have hB'_meas : MeasurableSet B' := MeasureTheory.measurableSet_toMeasurable _ _
  set f : (Fin m → X) → ℝ≥0∞ := fun xs => μ (Prod.mk xs ⁻¹' B') with hf_def
  have hf_meas : Measurable f := measurable_measure_prodMk_left hB'_meas
  -- Conditional bound: for xs ∈ A, f(xs) ≥ 1 / 2
  have h_cond : ∀ xs ∈ A, (1 : ℝ≥0∞) / 2 ≤ f xs := by
    intro xs hxs
    obtain ⟨h_star, h_star_in_C, h_gap⟩ := hxs
    -- Ghost set: {xs' | EmpErr(h*,S) - EmpErr(h*,S') ≥ ε/2}
    set S_ghost := {xs' : Fin m → X | EmpiricalError X Bool h_star
        (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h_star
        (fun i => (xs' i, c (xs' i))) (zeroOneLoss Bool) ≥ ε / 2} with hS_ghost_def
    have h_ghost_sub_B : S_ghost ⊆ Prod.mk xs ⁻¹' B := by
      intro xs' hxs'
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hB_def]
      exact ⟨h_star, h_star_in_C, hxs'⟩
    have h_B_sub_B' : Prod.mk xs ⁻¹' B ⊆ Prod.mk xs ⁻¹' B' :=
      Set.preimage_mono (MeasureTheory.subset_toMeasurable _ _)
    calc (1 : ℝ≥0∞) / 2
        ≤ μ S_ghost := by
          -- For the lower tail: EmpErr(h*,S) - TrueErr(h*) ≥ ε
          -- means EmpErr(h*,S) ≥ TrueErr(h*) + ε
          -- We need: P[EmpErr(h*,S') < TrueErr(h*) + ε/2] ≥ 1 / 2
          -- Equivalently: P[EmpErr(h*,S') ≥ TrueErr(h*) + ε/2] ≤ 1 / 2
          -- By hoeffding_one_sided_upper with t = ε/2
          have hmeas_disagree : MeasurableSet {x | h_star x ≠ c x} :=
            (measurableSet_eq_fun (hmeas_C h_star h_star_in_C) hc_meas).compl
          -- EmpiricalError is nonneg
          have h_emp_nonneg : 0 ≤ EmpiricalError X Bool h_star
              (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) := by
            simp only [EmpiricalError]
            split
            · exact le_refl 0
            · apply div_nonneg
              · apply Finset.sum_nonneg; intro i _
                simp only [zeroOneLoss]; split <;> linarith
              · positivity
          -- TrueErr ≤ 1
          have h_true_le_one : TrueErrorReal X h_star c D ≤ 1 := by
            simp only [TrueErrorReal, TrueError]
            have h_le : D {x | h_star x ≠ c x} ≤ 1 := by
              calc D {x | h_star x ≠ c x} ≤ D Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
            exact ENNReal.toReal_le_of_le_ofReal one_pos.le
              (by rw [ENNReal.ofReal_one]; exact h_le)
          -- If ε > 1, the gap EmpErr - TrueErr ≤ 1 < ε, contradiction
          by_cases hε1 : ε ≤ 1
          case neg =>
            push Not at hε1
            have h_gap_bound : EmpiricalError X Bool h_star
                (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) -
                TrueErrorReal X h_star c D ≤ 1 := by
              -- EmpErr ≤ 1 and TrueErr ≥ 0
              have h_emp_le_one : EmpiricalError X Bool h_star
                  (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≤ 1 := by
                simp only [EmpiricalError, Nat.pos_iff_ne_zero.mp hm, ↓reduceIte]
                rw [div_le_one (Nat.cast_pos.mpr hm)]
                calc ∑ i : Fin m, zeroOneLoss Bool (h_star (xs i)) (c (xs i))
                    ≤ ∑ _i : Fin m, (1 : ℝ) := by
                      apply Finset.sum_le_sum; intro i _
                      simp only [zeroOneLoss]; split <;> linarith
                  _ = ↑m := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              have h_true_nonneg : 0 ≤ TrueErrorReal X h_star c D := by
                simp only [TrueErrorReal, TrueError]; positivity
              linarith
            linarith
          case pos =>
          have hε2_pos : (0 : ℝ) < ε / 2 := by linarith
          have hε2_le_one : ε / 2 ≤ 1 := by linarith
          -- Apply hoeffding_one_sided_upper
          have h_hoeff := hoeffding_one_sided_upper D h_star c m hm (ε / 2) hε2_pos hε2_le_one
            hmeas_disagree
          -- exp(-2m(ε/2)²) ≤ 1 / 2
          have h_exp_le_half : Real.exp (-2 * ↑m * (ε / 2) ^ 2) ≤ 1 / 2 := by
            have h_exp_eq : -2 * ↑m * (ε / 2) ^ 2 = -(↑m * ε ^ 2 / 2) := by ring
            rw [h_exp_eq]
            have h_half : Real.log 2 ≤ ↑m * ε ^ 2 / 2 := by linarith
            have h_two_le_exp : (2 : ℝ) ≤ Real.exp (↑m * ε ^ 2 / 2) := by
              calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
                _ ≤ Real.exp (↑m * ε ^ 2 / 2) := Real.exp_le_exp_of_le h_half
            rw [Real.exp_neg, show (1 : ℝ) / 2 = 2⁻¹ from by norm_num]
            exact inv_anti₀ (by positivity) h_two_le_exp
          -- Hoeffding set: {xs' | EmpErr(h*,xs') ≥ TrueErr(h*) + ε/2}
          set H_set := {xs' : Fin m → X | EmpiricalError X Bool h_star
              (fun i => (xs' i, c (xs' i))) (zeroOneLoss Bool) ≥
              TrueErrorReal X h_star c D + ε / 2} with hH_set_def
          have h_H_le_half : μ H_set ≤ 1 / 2 := by
            calc μ H_set
                ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * (ε / 2) ^ 2)) := h_hoeff
              _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal h_exp_le_half
              _ = 1 / 2 := by
                  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
                  simp [ENNReal.ofReal_one]
          -- Complement: μ(H_setᶜ) ≥ 1 / 2
          have h_prob : MeasureTheory.IsProbabilityMeasure μ := by
            rw [hμ_def]; infer_instance
          have h_compl_ge : 1 / 2 ≤ μ H_setᶜ := by
            have h_total : 1 ≤ μ H_set + μ H_setᶜ := by
              have : μ Set.univ ≤ μ H_set + μ H_setᶜ := by
                calc μ Set.univ = μ (H_set ∪ H_setᶜ) := by rw [Set.union_compl_self]
                  _ ≤ μ H_set + μ H_setᶜ := measure_union_le _ _
              rwa [measure_univ] at this
            have h_H_ne_top : μ H_set ≠ ⊤ :=
              ne_top_of_le_ne_top ENNReal.one_ne_top
                (h_H_le_half.trans (by norm_num))
            calc (1 : ℝ≥0∞) / 2
                = 1 - 1 / 2 := by norm_num
              _ ≤ 1 - μ H_set := tsub_le_tsub_left h_H_le_half 1
              _ ≤ (μ H_set + μ H_setᶜ) - μ H_set := tsub_le_tsub_right h_total (μ H_set)
              _ = μ H_setᶜ := ENNReal.add_sub_cancel_left h_H_ne_top
          -- H_setᶜ ⊆ S_ghost
          -- H_setᶜ = {xs' | EmpErr(h*,xs') < TrueErr(h*) + ε/2}
          -- h_gap: EmpErr(h*,S) - TrueErr(h*) ≥ ε
          -- So TrueErr(h*) + ε/2 ≤ EmpErr(h*,S) - ε/2
          -- If EmpErr(h*,xs') < TrueErr(h*) + ε/2 ≤ EmpErr(h*,S) - ε/2
          -- then EmpErr(h*,S) - EmpErr(h*,xs') > ε/2
          -- So EmpErr(h*,S) - EmpErr(h*,xs') ≥ ε/2 (for ≥ vs >: works since we have strict <)
          have h_compl_sub : H_setᶜ ⊆ S_ghost := by
            intro xs' hxs'
            simp only [Set.mem_compl_iff, hH_set_def, Set.mem_setOf_eq, not_le] at hxs'
            simp only [hS_ghost_def, Set.mem_setOf_eq, ge_iff_le]
            linarith
          exact h_compl_ge.trans (MeasureTheory.measure_mono h_compl_sub)
      _ ≤ μ (Prod.mk xs ⁻¹' B') :=
          MeasureTheory.measure_mono (h_ghost_sub_B.trans h_B_sub_B')
  -- Markov
  have h_markov : (1 : ℝ≥0∞) / 2 * μ {xs | (1 : ℝ≥0∞) / 2 ≤ f xs} ≤ ∫⁻ xs, f xs ∂μ :=
    mul_meas_ge_le_lintegral hf_meas _
  have h_prod : (μ.prod μ) B' = ∫⁻ xs, μ (Prod.mk xs ⁻¹' B') ∂μ :=
    MeasureTheory.Measure.prod_apply hB'_meas
  calc (1 : ℝ≥0∞) / 2 * μ A
      ≤ (1 : ℝ≥0∞) / 2 * μ {xs | (1 : ℝ≥0∞) / 2 ≤ f xs} := by
        apply mul_le_mul_right
        exact MeasureTheory.measure_mono h_cond
    _ ≤ ∫⁻ xs, f xs ∂μ := h_markov
    _ = (μ.prod μ) B' := h_prod.symm
    _ = (μ.prod μ) B := MeasureTheory.measure_toMeasurable B

/-! ## T4: Symmetrization Uniform Convergence Bound (two-sided) -/

/-- The symmetrization uniform convergence bound: two-sided version.
    P[∃h∈C: |TrueErr-EmpErr| ≥ ε] ≤ 4·GF(C,2m)·exp(-mε²/8).

    **Proof strategy (4 steps):**

    1. **Decompose absolute value:**
       |TrueErr - EmpErr| ≥ ε ↔ (TrueErr - EmpErr ≥ ε) ∨ (EmpErr - TrueErr ≥ ε)

       ```
       have abs_decomp : ∀ (a b : ℝ),
         |a - b| ≥ ε ↔ a - b ≥ ε ∨ b - a ≥ ε := by
         intro a b; constructor
         · intro h; by_cases h' : a - b ≥ ε
           · exact Or.inl h'
           · exact Or.inr (by linarith [abs_sub_comm a b, le_abs_self (a - b)])
         · intro h; cases h with
           | inl h => exact le_trans (le_of_eq (abs_of_nonneg (by linarith))) (by linarith)
           | inr h => exact le_trans (le_of_eq (abs_of_nonpos (by linarith) ▸ ...)) ...
       ```

    2. **Upper tail:** P[∃h∈C: TrueErr-EmpErr ≥ ε] ≤ 2·GF(C,2m)·exp(-mε²/8)
       - Direct application of `symmetrization_step` + `double_sample_pattern_bound`.

    3. **Lower tail:** P[∃h∈C: EmpErr-TrueErr ≥ ε] ≤ 2·GF(C,2m)·exp(-mε²/8)
       - Apply the symmetric argument: swap roles of S and S' in the double sample.
       - Equivalently, apply `symmetrization_step` to the event EmpErr-TrueErr ≥ ε
         and bound the double-sample event {EmpErr_S - EmpErr_{S'} ≥ ε/2}.
       - The bound is symmetric because D^m ⊗ D^m is symmetric under swapping factors.
       ```
       have swap_symmetry :
         DoubleSampleMeasure D m {p | ∃ h ∈ C, EmpErr(S) - EmpErr(S') ≥ ε/2}
         = DoubleSampleMeasure D m {p | ∃ h ∈ C, EmpErr(S') - EmpErr(S) ≥ ε/2} :=
         Measure.prod_swap ...
       ```

    4. **Union bound:**
       P[|gap| ≥ ε] ≤ P[gap ≥ ε] + P[gap ≤ -ε]
                     ≤ 2·GF·exp(...) + 2·GF·exp(...)
                     = 4·GF(C,2m)·exp(-mε²/8)
       ```
       -- Uses: MeasureTheory.measure_union_le for the union of two events
       -- CAST: 2 * X + 2 * X = 4 * X in ENNReal (need ENNReal.add_mul or similar)
       ```

    **References:** SSBD Theorem 6.7, Kakade-Tewari Lecture 19 -/
theorem symmetrization_uc_bound {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ C,
        |TrueErrorReal X h c D -
         EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
           (zeroOneLoss Bool)| ≥ ε}
    ≤ ENNReal.ofReal (4 * ↑(GrowthFunction X C (2 * m)) *
        Real.exp (-(↑m * ε ^ 2 / 8))) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D) with hμ_def
  set gf_exp := (↑(GrowthFunction X C (2 * m)) : ℝ) * Real.exp (-(↑m * ε ^ 2 / 8))
    with hgf_exp_def
  have hgf_exp_nn : 0 ≤ gf_exp := mul_nonneg (Nat.cast_nonneg' _) (Real.exp_pos _).le
  -- Step 1: Upper tail bound via symmetrization_step + double_sample_pattern_bound
  set upper := {xs : Fin m → X | ∃ h ∈ C, TrueErrorReal X h c D -
      EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
  have h_upper : μ upper ≤ ENNReal.ofReal (2 * gf_exp) := by
    have h1 := symmetrization_step D C c hmeas_C hc_meas m hm ε hε hm_large
    have h2 := double_sample_pattern_bound D C c hmeas_C hc_meas m hm ε hε hE_nullmeas
    calc μ upper ≤ 2 * (μ.prod μ) _ := h1
      _ ≤ 2 * ENNReal.ofReal gf_exp := by exact mul_le_mul_right h2 2
      _ = ENNReal.ofReal (2 * gf_exp) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  -- Step 2: Lower tail bound
  -- {EmpErr - TrueErr ≥ ε} = {-(TrueErr - EmpErr) ≥ ε}
  -- By symmetry of the problem (swap the roles of TrueErr overshooting vs undershooting),
  -- the same bound holds. We prove this by noting that the double-sample bound
  -- double_sample_pattern_bound is symmetric: swapping p.1 and p.2 gives the same measure
  -- (by Measure.prod_swap), and the same GF * exp bound.
  set lower := {xs : Fin m → X | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) -
      TrueErrorReal X h c D ≥ ε}
  have h_lower : μ lower ≤ ENNReal.ofReal (2 * gf_exp) := by
    -- Step 1: symmetrization_step_lower gives μ(lower) ≤ 2*(μ.prod μ)(B_lower)
    -- where B_lower = {p | ∃ h ∈ C, EmpErr(p.1) - EmpErr(p.2) ≥ ε/2}
    have h1 := symmetrization_step_lower D C c hmeas_C hc_meas m hm ε hε hm_large
    -- Step 2: Swap symmetry — (μ.prod μ)(B_lower) = (μ.prod μ)(B_upper)
    -- where B_upper = {p | ∃ h ∈ C, EmpErr(p.2) - EmpErr(p.1) ≥ ε/2}
    -- This uses Measure.prod_swap: (μ.prod μ).map Prod.swap = μ.prod μ
    have h_swap : (μ.prod μ)
        {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2}
      = (μ.prod μ)
        {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2} := by
      -- Use MeasurableEquiv.prodComm for Prod.swap, giving map_apply for ALL sets
      let swap_equiv : (Fin m → X) × (Fin m → X) ≃ᵐ (Fin m → X) × (Fin m → X) :=
        MeasurableEquiv.prodComm
      set S1 := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) ≥ ε / 2}
      set S2 := {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      -- swap_equiv ⁻¹' S2 = S1
      have h_preimage : ⇑swap_equiv ⁻¹' S2 = S1 := by
        ext p
        change (p.2, p.1) ∈ S2 ↔ p ∈ S1
        simp only [S1, S2, Set.mem_setOf_eq]
      -- (μ.prod μ).map swap_equiv = μ.prod μ (symmetric product)
      have h_swap_eq_swap : (⇑swap_equiv : (Fin m → X) × (Fin m → X) → _) = Prod.swap := rfl
      have h_sym : (μ.prod μ).map swap_equiv = μ.prod μ := by
        rw [show (μ.prod μ).map ⇑swap_equiv = (μ.prod μ).map Prod.swap from by
          rw [h_swap_eq_swap]]
        exact MeasureTheory.Measure.prod_swap (μ := μ) (ν := μ)
      calc (μ.prod μ) S1
          = (μ.prod μ) (⇑swap_equiv ⁻¹' S2) := by rw [h_preimage]
        _ = ((μ.prod μ).map swap_equiv) S2 := by rw [swap_equiv.map_apply]
        _ = (μ.prod μ) S2 := by rw [h_sym]
    -- Step 3: double_sample_pattern_bound bounds the swapped event
    have h2 := double_sample_pattern_bound D C c hmeas_C hc_meas m hm ε hε hE_nullmeas
    calc μ lower ≤ 2 * (μ.prod μ) _ := h1
      _ = 2 * (μ.prod μ) _ := by rw [h_swap]
      _ ≤ 2 * ENNReal.ofReal gf_exp := mul_le_mul_right h2 2
      _ = ENNReal.ofReal (2 * gf_exp) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  -- Step 3: Decompose |gap| ≥ ε into upper ∪ lower
  have h_abs_sub : {xs : Fin m → X | ∃ h ∈ C,
      |TrueErrorReal X h c D -
       EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| ≥ ε}
      ⊆ upper ∪ lower := by
    intro xs ⟨h, hC, hgap⟩
    simp only [Set.mem_union]
    by_cases h_pos : TrueErrorReal X h c D -
        EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ 0
    · exact Or.inl ⟨h, hC, by rwa [abs_of_nonneg h_pos] at hgap⟩
    · push Not at h_pos
      have hgap' : -(TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)) ≥ ε := by
        rwa [abs_of_neg h_pos] at hgap
      exact Or.inr ⟨h, hC, by linarith⟩
  -- Step 4: Combine
  calc μ {xs | ∃ h ∈ C, |TrueErrorReal X h c D -
        EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| ≥ ε}
      ≤ μ (upper ∪ lower) := MeasureTheory.measure_mono h_abs_sub
    _ ≤ μ upper + μ lower := MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * gf_exp) + ENNReal.ofReal (2 * gf_exp) :=
        add_le_add h_upper h_lower
    _ = ENNReal.ofReal (2 * gf_exp + 2 * gf_exp) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    _ = ENNReal.ofReal (4 * gf_exp) := by ring_nf
    _ = ENNReal.ofReal (4 * ↑(GrowthFunction X C (2 * m)) *
          Real.exp (-(↑m * ε ^ 2 / 8))) := by rw [hgf_exp_def]; ring_nf

/-! ## T5: Arithmetic — Growth Function × Exponential ≤ δ -/

-- Arithmetic: 4*GF(C,2m)*exp(-m*eps^2 / 8) <= delta and 2*ln2 <= m*eps^2.
-- Uses: Sauer-Shelah + pow_mul_exp_neg_le_factorial_div + hm_bound.

/-- Trivial bound: GrowthFunction ≤ 2^n for all concept classes.
    Each restriction to an n-element set yields a function in S → Bool,
    and there are at most 2^n such functions. -/
private lemma growth_function_le_two_pow {X : Type u}
    (C : ConceptClass X Bool) (n : ℕ) :
    GrowthFunction X C n ≤ 2 ^ n := by
  unfold GrowthFunction
  -- If the range is empty, sSup = 0 ≤ 2^n
  by_cases h_empty : (Set.range fun (S : { S : Finset X // S.card = n }) =>
    ({ f : ↥S.val → Bool | ∃ c ∈ C, ∀ x : ↥S.val, c ↑x = f x } : Set (↥S.val → Bool)).ncard) = ∅
  · simp only [h_empty, csSup_empty]; exact Nat.zero_le _
  · -- Range is nonempty
    have h_ne : Set.Nonempty (Set.range fun (S : { S : Finset X // S.card = n }) =>
        ({ f : ↥S.val → Bool | ∃ c ∈ C, ∀ x : ↥S.val, c ↑x = f x } : Set (↥S.val → Bool)).ncard) :=
      Set.nonempty_iff_ne_empty.mpr h_empty
    apply csSup_le h_ne
    rintro _ ⟨S, rfl⟩
    -- For a given S with |S| = n, ncard {f : ↥S.val → Bool | P f} ≤ 2^n
    let T : Finset X := (↑S : Finset X)
    letI : Fintype ↥T := Finset.fintypeCoeSort T
    have hBound' : ({ f : ↥T → Bool | ∃ c ∈ C, ∀ x : ↥T, c ↑x = f x } :
        Set (↥T → Bool)).ncard ≤ 2 ^ n := by
      calc ({ f : ↥T → Bool | ∃ c ∈ C, ∀ x : ↥T, c ↑x = f x } :
              Set (↥T → Bool)).ncard
          ≤ Nat.card (↥T → Bool) := Set.ncard_le_card _
        _ = Nat.card Bool ^ Nat.card ↥T := Nat.card_fun
        _ = 2 ^ n := by simp [Nat.card_eq_fintype_card, Fintype.card_coe, T, S.prop]
    simpa [T] using hBound'

private lemma growth_exp_le_delta_large_v {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (v : ℕ) (hv : 0 < v) (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hm_bound : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ ≤ ↑m)
    (hvm : ¬ v ≤ 2 * m) :
    4 * ↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8)) ≤ δ := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hv1_pos : (0 : ℝ) < ↑v + 1 := by positivity
  have hm_delta : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) ≤ ↑m * δ := by
    rwa [div_le_iff₀ hδ] at hm_bound
  have hfact_le : (↑((v + 1).factorial) : ℝ) ≤ (↑v + 1) ^ (v + 1) := by
    exact_mod_cast Nat.factorial_le_pow (v + 1)
  have hm_pow_ge_1 : (1 : ℝ) ≤ ↑m ^ v :=
    one_le_pow₀ (Nat.one_le_cast.mpr hm)
  have he_ge_1 : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hexp_pow_ge_1 : (1 : ℝ) ≤ Real.exp 1 ^ (v + 1) :=
    one_le_pow₀ he_ge_1
  push Not at hvm
  have hvm' : 2 * m + 1 ≤ v := by omega
  have hgf_trivial : GrowthFunction X C (2 * m) ≤ 2 ^ (2 * m) :=
    growth_function_le_two_pow C (2 * m)
  set t := (↑m : ℝ) * ε ^ 2 / 8 with ht_def
  have ht_pos : 0 < t := by positivity
  have hTaylor : t ^ (v + 1) / ↑((v + 1).factorial) ≤ Real.exp t :=
    Real.pow_div_factorial_le_exp t (le_of_lt ht_pos) (v + 1)
  have hTaylor2 : t ^ (v + 1) ≤ ↑((v + 1).factorial) * Real.exp t := by
    have := (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos (v + 1)))).mp hTaylor
    linarith [mul_comm (Real.exp t) (↑((v + 1).factorial) : ℝ)]
  have hexp_le : Real.exp (-t) ≤ ↑((v + 1).factorial) / t ^ (v + 1) := by
    have hexp_t_pos := Real.exp_pos t
    have ht_pow_pos := pow_pos ht_pos (v + 1)
    rw [Real.exp_neg, le_div_iff₀ ht_pow_pos]
    calc (Real.exp t)⁻¹ * t ^ (v + 1) ≤ 1 * ↑((v + 1).factorial) := by
          rw [inv_mul_le_iff₀ hexp_t_pos, one_mul]
          linarith [hTaylor2]
      _ = ↑((v + 1).factorial) := one_mul _
  have hchain1 : 4 * ↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8)) ≤
      4 * (2 : ℝ) ^ (2 * m) * (↑((v + 1).factorial) / t ^ (v + 1)) := by
    have hgf_cast : (↑(GrowthFunction X C (2 * m)) : ℝ) ≤ (2 : ℝ) ^ (2 * m) := by
      exact_mod_cast hgf_trivial
    rw [ht_def]
    nlinarith [hgf_cast, hexp_le, Real.exp_pos (-(↑m * ε ^ 2 / 8)),
      show 0 < ↑((v + 1).factorial) / t ^ (v + 1) by positivity]
  suffices hchain2 : 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) ≤ δ * t ^ (v + 1) by
    have ht_pow_pos := pow_pos ht_pos (v + 1)
    have hdiv : 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) / t ^ (v + 1) ≤ δ := by
      exact div_le_of_le_mul₀ (le_of_lt ht_pow_pos) (le_of_lt hδ) hchain2
    have hrewrite : 4 * (2 : ℝ) ^ (2 * m) *
        (↑((v + 1).factorial) / t ^ (v + 1)) =
        4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) / t ^ (v + 1) := by
      rw [mul_div_assoc']
    linarith [hchain1, hrewrite, hdiv]
  rw [ht_def]
  have hm_delta_expand :
      (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) ≤ ↑m * δ * (ε ^ 2) ^ (v + 1) := by
    have := hm_delta
    rw [div_pow, div_le_iff₀ (pow_pos hε2 (v + 1))] at this
    linarith
  have h_pow_bound : 4 * (2 : ℝ) ^ (2 * m) * (8 : ℝ) ^ (v + 1) ≤
      (16 : ℝ) ^ (v + 1) := by
    have h_2_pow : 4 * (2 : ℝ) ^ (2 * m) ≤ (2 : ℝ) ^ (v + 1) := by
      have : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [this, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have : (16 : ℝ) ^ (v + 1) = (2 : ℝ) ^ (v + 1) * (8 : ℝ) ^ (v + 1) := by
      rw [show (16 : ℝ) = 2 * 8 from by norm_num, mul_pow]
    rw [this]
    exact mul_le_mul_of_nonneg_right h_2_pow (pow_nonneg (by norm_num) (v + 1))
  have hgoal_equiv : δ * (↑m * ε ^ 2 / 8) ^ (v + 1) =
      δ * ↑m ^ (v + 1) * (ε ^ 2) ^ (v + 1) / (8 : ℝ) ^ (v + 1) := by
    rw [div_pow]; ring
  rw [hgoal_equiv]
  rw [show 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) =
      (4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) * (8 : ℝ) ^ (v + 1)) /
      (8 : ℝ) ^ (v + 1) from by
    rw [mul_div_cancel_right₀]; exact pow_ne_zero _ (by norm_num)]
  rw [div_le_div_iff_of_pos_right (pow_pos (by norm_num : (0:ℝ) < 8) (v + 1))]
  have hstep1 : 4 * (2 : ℝ) ^ (2 * m) * ↑((v + 1).factorial) * (8 : ℝ) ^ (v + 1) ≤
      (16 : ℝ) ^ (v + 1) * (↑v + 1) ^ (v + 1) := by
    nlinarith [h_pow_bound, hfact_le, pow_pos (show (0:ℝ) < 16 by norm_num) (v + 1)]
  have hstep2 : (16 : ℝ) ^ (v + 1) * (↑v + 1) ^ (v + 1) ≤
      (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) * ↑m ^ v := by
    rw [mul_pow, mul_pow]
    have h1 : (1 : ℝ) ≤ Real.exp 1 ^ (v + 1) * ↑m ^ v :=
      one_le_mul_of_one_le_of_one_le hexp_pow_ge_1 hm_pow_ge_1
    have h16pos := pow_pos (show (0:ℝ) < 16 by norm_num) (v + 1)
    have hv1pos := pow_pos hv1_pos (v + 1)
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg (le_of_lt h16pos) (le_of_lt hv1pos))]
  have hstep3 : (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) * ↑m ^ v ≤
      δ * ↑m ^ (v + 1) * (ε ^ 2) ^ (v + 1) := by
    have hmul : ↑m ^ v * (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) ≤
        ↑m ^ v * (↑m * δ * (ε ^ 2) ^ (v + 1)) :=
      mul_le_mul_of_nonneg_left hm_delta_expand (pow_nonneg (Nat.cast_nonneg _) v)
    have hpow_eq : (↑m : ℝ) ^ (v + 1) = ↑m ^ v * ↑m := pow_succ (↑m : ℝ) v
    calc (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) * ↑m ^ v
        = ↑m ^ v * (16 * Real.exp 1 * (↑v + 1)) ^ (v + 1) := by ring
      _ ≤ ↑m ^ v * (↑m * δ * (ε ^ 2) ^ (v + 1)) := hmul
      _ = δ * (↑m ^ v * ↑m) * (ε ^ 2) ^ (v + 1) := by ring
      _ = δ * ↑m ^ (v + 1) * (ε ^ 2) ^ (v + 1) := by rw [← hpow_eq]
  linarith [hstep1, hstep2, hstep3]

theorem growth_exp_le_delta {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (v : ℕ) (hv : 0 < v) (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hv_bound : ∀ (n : ℕ), v ≤ n →
      GrowthFunction X C n ≤ ∑ i ∈ Finset.range (v + 1), Nat.choose n i)
    (hm_bound : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ ≤ ↑m) :
    4 * ↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8)) ≤ δ ∧
    2 * Real.log 2 ≤ ↑m * ε ^ 2 := by
  -- Shared positivity and auxiliary facts
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hv_pos : (0 : ℝ) < ↑v := Nat.cast_pos.mpr hv
  have hv1_pos : (0 : ℝ) < ↑v + 1 := by linarith
  have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase_pos : 0 < 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 := by positivity
  have hm_real_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
  have he_ge_2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  -- From hm_bound: m * δ ≥ base^{v+1}
  have hm_delta : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) ≤ ↑m * δ := by
    rwa [div_le_iff₀ hδ] at hm_bound
  -- v+1 ≥ 2
  have hv1_ge_2 : (2 : ℝ) ≤ ↑v + 1 := by
    have : (1 : ℝ) ≤ ↑v := Nat.one_le_cast.mpr hv; linarith
  -- Factorial bound: (n+1)! ≤ (n+1)^{n+1}
  have hfact_le : (↑((v + 1).factorial) : ℝ) ≤ (↑v + 1) ^ (v + 1) := by
    exact_mod_cast Nat.factorial_le_pow (v + 1)
  -- m^v ≥ 1
  have hm_pow_ge_1 : (1 : ℝ) ≤ ↑m ^ v := by
    exact one_le_pow₀ (Nat.one_le_cast.mpr hm)
  -- exp(1)^{v+1} ≥ 1
  have hexp_pow_ge_1 : (1 : ℝ) ≤ Real.exp 1 ^ (v + 1) := by
    exact one_le_pow₀ (by linarith)
  constructor
  · -- Part 1: 4 * GF(C, 2m) * exp(-mε²/8) ≤ δ
    -- Case split: v ≤ 2m (Sauer-Shelah applies) vs v > 2m (use trivial GF bound)
    by_cases hvm : v ≤ 2 * m
    · -- Case A: v ≤ 2m — use Sauer-Shelah + sum_choose_le_exp_pow
      have hgf_exp : (GrowthFunction X C (2 * m) : ℝ) ≤
          (Real.exp 1 * ↑(2 * m) / ↑v) ^ v := by
        have h1 : (GrowthFunction X C (2 * m) : ℝ) ≤
            ↑(∑ i ∈ Finset.range (v + 1), (2 * m).choose i) :=
          Nat.cast_le.mpr (hv_bound (2 * m) hvm)
        have h2 := sum_choose_le_exp_pow v (2 * m) hv hvm
        calc (GrowthFunction X C (2 * m) : ℝ) ≤ _ := h1
          _ = ∑ i ∈ Finset.range (v + 1), ↑((2 * m).choose i) := by push_cast; rfl
          _ ≤ _ := h2
      set t := (↑m : ℝ) * ε ^ 2 / 8 with ht_def
      have ht_pos : 0 < t := by positivity
      have h_pow_exp : t ^ v * Real.exp (-t) ≤ ↑((v + 1).factorial) / t :=
        pow_mul_exp_neg_le_factorial_div ht_pos
      have h2m_eq : (↑(2 * m) : ℝ) = 16 * t / ε ^ 2 := by
        rw [ht_def]; field_simp; push_cast; ring
      set K := 16 * Real.exp 1 / (↑v * ε ^ 2) with hK_def
      have hK_pos : 0 < K := by rw [hK_def]; positivity
      have hgf_factor : (Real.exp 1 * ↑(2 * m) / ↑v) ^ v = K ^ v * t ^ v := by
        have : Real.exp 1 * ↑(2 * m) / ↑v = K * t := by
          rw [h2m_eq, hK_def, ht_def]
          have hv_ne : (↑v : ℝ) ≠ 0 := ne_of_gt hv_pos
          have hε2_ne : ε ^ 2 ≠ 0 := ne_of_gt hε2
          field_simp
        rw [this, mul_pow]
      -- base = K * v * (v+1)
      have hB_eq : 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 = K * ↑v * (↑v + 1) := by
        rw [hK_def]; field_simp
      have hCvv : K ^ (v + 1) * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) ≤ ↑m * δ := by
        have : (K * ↑v * (↑v + 1)) ^ (v + 1) =
            K ^ (v + 1) * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) := by
          rw [mul_pow, mul_pow]
        rw [← this, ← hB_eq]; exact hm_delta
      have hv_pow_ge_1 : (1 : ℝ) ≤ ↑v ^ v :=
        one_le_pow₀ (Nat.one_le_cast.mpr hv)
      have h_2_le_ev : (2 : ℝ) ≤ Real.exp 1 * ↑v ^ v := by
        have : Real.exp 1 * 1 ≤ Real.exp 1 * ↑v ^ v := by nlinarith [hv_pow_ge_1]
        linarith
      have hkey : 2 * ↑((v + 1).factorial) ≤
          Real.exp 1 * ↑v ^ v * (↑v + 1) ^ (v + 1) := by
        have hfact_nonneg : (0 : ℝ) ≤ ↑((v + 1).factorial) := Nat.cast_nonneg _
        have hv1_pow_pos : (0 : ℝ) < (↑v + 1) ^ (v + 1) := pow_pos hv1_pos (v + 1)
        nlinarith [hfact_le, h_2_le_ev]
      have hKeps : K * ε ^ 2 * ↑v ^ (v + 1) = 16 * Real.exp 1 * ↑v ^ v := by
        have hveps_ne : (↑v : ℝ) * ε ^ 2 ≠ 0 := mul_ne_zero (ne_of_gt hv_pos) (ne_of_gt hε2)
        have : K * (↑v * ε ^ 2) = 16 * Real.exp 1 := by
          rw [hK_def]; field_simp
        calc K * ε ^ 2 * ↑v ^ (v + 1)
            = K * (↑v * ε ^ 2) * ↑v ^ v := by rw [pow_succ]; ring
          _ = 16 * Real.exp 1 * ↑v ^ v := by rw [this]
      have hstepA : 32 * ↑((v + 1).factorial) ≤
          K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) := by nlinarith [hkey, hKeps]
      have hstepB : K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) * K ^ v ≤
          ε ^ 2 * (↑m * δ) := by
        have : K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) * K ^ v =
            ε ^ 2 * (K ^ (v + 1) * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1)) := by
          rw [show K ^ (v + 1) = K ^ v * K from pow_succ K v]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hCvv hε2.le
      have hcombine : 32 * ↑((v + 1).factorial) * K ^ v ≤ δ * ↑m * ε ^ 2 := by
        have hstepA_mul :
            32 * ↑((v + 1).factorial) * K ^ v ≤
              (K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1)) * K ^ v :=
          mul_le_mul_of_nonneg_right hstepA (pow_nonneg hK_pos.le v)
        calc 32 * ↑((v + 1).factorial) * K ^ v
            ≤ (K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1)) * K ^ v :=
              hstepA_mul
          _ = K * ε ^ 2 * ↑v ^ (v + 1) * (↑v + 1) ^ (v + 1) * K ^ v := by
              ring
          _ ≤ ε ^ 2 * (↑m * δ) := hstepB
          _ = δ * ↑m * ε ^ 2 := by ring
      have hfinal : 4 * K ^ v * (↑((v + 1).factorial) / t) ≤ δ := by
        rw [ht_def, show 4 * K ^ v * (↑((v + 1).factorial) / (↑m * ε ^ 2 / 8)) =
            32 * ↑((v + 1).factorial) * K ^ v / (↑m * ε ^ 2) from by ring]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < ↑m * ε ^ 2)]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcombine
      calc 4 * ↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8))
          ≤ 4 * (K ^ v * t ^ v) * Real.exp (-t) := by
            have hgf_Kt : (GrowthFunction X C (2 * m) : ℝ) ≤ K ^ v * t ^ v := by
              calc (GrowthFunction X C (2 * m) : ℝ)
                  ≤ (Real.exp 1 * ↑(2 * m) / ↑v) ^ v := hgf_exp
                _ = K ^ v * t ^ v := hgf_factor
            have hscaled : 4 * (GrowthFunction X C (2 * m) : ℝ) ≤
                4 * (K ^ v * t ^ v) :=
              mul_le_mul_of_nonneg_left hgf_Kt (by norm_num)
            have hmul := mul_le_mul_of_nonneg_right hscaled (Real.exp_pos (-t)).le
            simpa [ht_def, mul_assoc] using hmul
        _ = 4 * K ^ v * (t ^ v * Real.exp (-t)) := by ring
        _ ≤ 4 * K ^ v * (↑((v + 1).factorial) / t) := by
            have hfactor : 0 ≤ 4 * K ^ v :=
              mul_nonneg (by norm_num) (pow_nonneg hK_pos.le v)
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left h_pow_exp hfactor
        _ ≤ δ := hfinal
    · exact growth_exp_le_delta_large_v C v hv m hm ε δ hε hδ hm_bound hvm
  · -- Part 2: 2 * log 2 ≤ m * ε²
    have hlog2_le_1 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]; linarith
    suffices h : 2 ≤ ↑m * ε ^ 2 by nlinarith
    by_cases hcase : ε ^ 2 ≤ 16 * Real.exp 1 * (↑v + 1)
    · have hbase_ge_1 : 1 ≤ 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 := by
        rw [le_div_iff₀ hε2]; linarith
      have hpow_ge : 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 ≤
          (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) :=
        le_self_pow₀ hbase_ge_1 (by omega)
      have : 16 * Real.exp 1 * (↑v + 1) / ε ^ 2 ≤ ↑m * δ := by linarith [hm_delta]
      have : 16 * Real.exp 1 * (↑v + 1) ≤ ↑m * δ * ε ^ 2 := by
        rwa [div_le_iff₀ hε2] at this
      nlinarith
    · push Not at hcase
      have hm_ge_1 : (1 : ℝ) ≤ ↑m := Nat.one_le_cast.mpr hm
      have hbase_ge_two : (2 : ℝ) ≤ 16 * Real.exp 1 * (↑v + 1) := by
        have hleft : (16 : ℝ) * 2 ≤ 16 * Real.exp 1 :=
          mul_le_mul_of_nonneg_left he_ge_2 (by norm_num)
        have hright : (16 : ℝ) * 2 * 2 ≤ (16 * Real.exp 1) * (↑v + 1) :=
          mul_le_mul hleft hv1_ge_2 (by norm_num) (by positivity)
        calc (2 : ℝ) ≤ 16 * 2 * 2 := by norm_num
          _ ≤ 16 * Real.exp 1 * (↑v + 1) := by simpa [mul_assoc] using hright
      have hε2_ge_two : (2 : ℝ) ≤ ε ^ 2 :=
        (lt_of_le_of_lt hbase_ge_two hcase).le
      exact le_trans hε2_ge_two
        (by simpa [one_mul] using mul_le_mul_of_nonneg_right hm_ge_1 hε2.le)

/-! ## UC proof: composing symmetrization + arithmetic

These theorems provide the imported bad-event bound used by
`uc_bad_event_le_delta` in `Generalization.lean`. They live here because this
module has access to both the symmetrization and arithmetic components, whereas
`Generalization.lean` cannot import this module without a cycle. -/

/-- UC bad-event bound: for m ≥ m₀(v,ε,δ), the probability
    of the bad event (∃ h with |TrueErr-EmpErr| ≥ ε) is at most δ.
    Composes `symmetrization_uc_bound` with `growth_exp_le_delta`. -/
private lemma uc_bad_event_le_delta_proved {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (v : ℕ) (hv_pos : 0 < v)
    (hv : ∀ (n : ℕ), v ≤ n →
      GrowthFunction X C n ≤ ∑ i ∈ Finset.range (v + 1), Nat.choose n i)
    (hm_bound : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ ≤ ↑m)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { xs : Fin m → X | ∃ h ∈ C,
        |TrueErrorReal X h c D -
         EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
           (zeroOneLoss Bool)| ≥ ε }
      ≤ ENNReal.ofReal δ := by
  -- Compose: growth_exp_le_delta gives arithmetic bound; symmetrization_uc_bound gives
  -- the measure bound.
  have ⟨h_bound, h_large⟩ := growth_exp_le_delta C v hv_pos m hm ε δ hε hδ hδ1 hv hm_bound
  have h_sym := symmetrization_uc_bound D C c hmeas_C hc_meas m hm ε hε h_large hE_nullmeas
  calc MeasureTheory.Measure.pi (fun _ : Fin m => D)
        { xs : Fin m → X | ∃ h ∈ C,
          |TrueErrorReal X h c D -
           EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
             (zeroOneLoss Bool)| ≥ ε }
      ≤ ENNReal.ofReal (4 * ↑(GrowthFunction X C (2 * m)) *
          Real.exp (-(↑m * ε ^ 2 / 8))) := h_sym
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal h_bound

private theorem bad_event_compl_measure_ge {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Bad : Set Ω) {δ : ℝ} (hδ : 0 < δ)
    (h_ub : μ Bad ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (1 - δ) ≤ μ Badᶜ := by
  have h_sub : (1 : ENNReal) ≤ μ Bad + μ Badᶜ := by
    rw [← MeasureTheory.IsProbabilityMeasure.measure_univ (μ := μ)]
    calc μ Set.univ
        ≤ μ (Bad ∪ Badᶜ) := MeasureTheory.measure_mono (by rw [Set.union_compl_self])
      _ ≤ μ Bad + μ Badᶜ := MeasureTheory.measure_union_le Bad Badᶜ
  calc ENNReal.ofReal (1 - δ)
      = 1 - ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_sub 1 (le_of_lt hδ), ENNReal.ofReal_one]
    _ ≤ 1 - μ Bad := tsub_le_tsub_left h_ub 1
    _ ≤ μ Badᶜ := by
        calc 1 - μ Bad
            ≤ (μ Bad + μ Badᶜ) - μ Bad := tsub_le_tsub_right h_sub _
          _ ≤ μ Badᶜ := by
              rw [ENNReal.add_sub_cancel_left (ne_top_of_le_ne_top ENNReal.one_ne_top
                MeasureTheory.prob_le_one)]

private theorem uniform_good_event_eq_bad_compl {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) (C : ConceptClass X Bool) (c : Concept X Bool)
    (m : ℕ) (ε : ℝ) :
    { xs : Fin m → X | ∀ (h : Concept X Bool), h ∈ C →
        |TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| < ε } =
      { xs : Fin m → X | ∃ h ∈ C,
        |TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| ≥ ε }ᶜ := by
  ext xs
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_and, not_le]

/-- Finite VCDim implies uniform convergence.
    Proof: VCDim < ∞ → UC.
    - Finite X: direct Hoeffding per-hypothesis + finite union bound.
    - Infinite X: Sauer-Shelah → symmetrization + growth function → UC. -/
theorem vcdim_finite_imp_uc' (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    HasUniformConvergence X C := by
  rcases finite_or_infinite X with hfin | hinf
  · -- ═══ FINITE X BRANCH ═══
    -- Direct union bound over finite concept space. No symmetrization needed.
    letI := Fintype.ofFinite X
    haveI : DecidableEq X := Classical.decEq X
    haveI : Fintype (Concept X Bool) := show Fintype (X → Bool) from Pi.instFintype
    -- For finite X, C ⊆ (X → Bool) is finite. Every set is measurable.
    have hfin_C : Set.Finite C := Set.Finite.subset (Set.finite_univ) (Set.subset_univ C)
    set Cf := hfin_C.toFinset with hCf_def
    have hCf_mem : ∀ h, h ∈ Cf ↔ h ∈ C := fun h => Set.Finite.mem_toFinset hfin_C
    set N := Cf.card with hN_def
    intro ε δ hε hδ
    -- Choose m₀ large enough that N * 2 * exp(-2 * m * ε²) ≤ δ
    -- i.e., m ≥ (1/(2ε²)) * ln(2N/δ). Use min(ε, 1) for Hoeffding's t ≤ 1 requirement.
    set ε' := min ε 1 with hε'_def
    have hε'_pos : 0 < ε' := lt_min hε one_pos
    have hε'_le_one : ε' ≤ 1 := min_le_right ε 1
    have hε'_le_ε : ε' ≤ ε := min_le_left ε 1
    use max 1 (Nat.ceil ((Real.log (2 * ↑N / δ)) / (2 * ε' ^ 2)))
    intro D hD c m hm
    by_cases hδ1 : 1 ≤ δ
    · have : ENNReal.ofReal (1 - δ) = 0 := ENNReal.ofReal_eq_zero.mpr (by linarith)
      rw [this]; exact zero_le _
    · push Not at hδ1
      have hm_pos : 0 < m := Nat.lt_of_lt_of_le (by omega) hm
      -- Measurability: for any two measurable Bool-valued functions, {x | f x ≠ g x} is measurable
      have hmeas_fin : ∀ (h' c' : X → Bool),
          Measurable h' → Measurable c' → MeasurableSet {x : X | h' x ≠ c' x} := by
        intro h' c' hh' hc'
        have : {x : X | h' x ≠ c' x} = h' ⁻¹' {true} ∩ c' ⁻¹' {false} ∪
            (h' ⁻¹' {false} ∩ c' ⁻¹' {true}) := by
          ext x; simp [Ne]; cases h' x <;> cases c' x <;> simp
        rw [this]
        exact (hh' (measurableSet_singleton _) |>.inter (hc' (measurableSet_singleton _))).union
          (hh' (measurableSet_singleton _) |>.inter (hc' (measurableSet_singleton _)))
      set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
      -- Define the bad event
      set Bad := { xs : Fin m → X | ∃ h ∈ C,
          |TrueErrorReal X h c D -
           EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
             (zeroOneLoss Bool)| ≥ ε }
      -- Bound μ(Bad) ≤ ENNReal.ofReal δ
      -- Strategy: |gap| ≥ ε implies |gap| ≥ ε' (since ε' ≤ ε), so Bad ⊆ Bad(ε').
      -- Then use Hoeffding with ε' ≤ 1 and union bound.
      have h_ub : μ Bad ≤ ENNReal.ofReal δ := by
        -- Bad ⊆ Bad(ε') ⊆ ⋃_{h ∈ Cf} BadH(h, ε')
        set Bad' := { xs : Fin m → X | ∃ h ∈ C,
            |TrueErrorReal X h c D -
             EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
               (zeroOneLoss Bool)| ≥ ε' }
        have hBad_sub_Bad' : Bad ⊆ Bad' := by
          intro xs hxs; obtain ⟨h', hh', hgap⟩ := hxs
          exact ⟨h', hh', le_trans (by linarith [hε'_le_ε]) hgap⟩
        have hBad'_sub : Bad' ⊆ ⋃ h ∈ Cf, { xs : Fin m → X |
            |TrueErrorReal X h c D -
             EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
               (zeroOneLoss Bool)| ≥ ε' } := by
          intro xs hxs
          simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hxs ⊢
          obtain ⟨h', hh'C, hh'gap⟩ := hxs
          exact ⟨h', (hCf_mem h').mpr hh'C, hh'gap⟩
        -- Per-hypothesis bound: for each h ∈ Cf, μ(BadH(h, ε')) ≤ 2·exp(-2mε'²)
        have hper_hyp : ∀ h' ∈ Cf, μ { xs : Fin m → X |
            |TrueErrorReal X h' c D -
             EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
               (zeroOneLoss Bool)| ≥ ε' }
            ≤ ENNReal.ofReal (2 * Real.exp (-2 * ↑m * ε' ^ 2)) := by
          intro h' _
          -- The absolute value event is contained in the union of two tails
          have h_abs_sub : { xs : Fin m → X |
              |TrueErrorReal X h' c D -
               EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                 (zeroOneLoss Bool)| ≥ ε' } ⊆
            { xs : Fin m → X | EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                (zeroOneLoss Bool) ≤ TrueErrorReal X h' c D - ε' } ∪
            { xs : Fin m → X | EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                (zeroOneLoss Bool) ≥ TrueErrorReal X h' c D + ε' } := by
            intro xs hxs
            simp only [Set.mem_setOf_eq, Set.mem_union] at hxs ⊢
            -- |a - b| ≥ ε' means a - b ≥ ε' or b - a ≥ ε'
            rcases le_or_gt (EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                (zeroOneLoss Bool)) (TrueErrorReal X h' c D - ε') with h_le | h_gt
            · left; exact h_le
            · right
              -- |a - b| ≥ ε' and b > a - ε' implies b - a ≥ ε', i.e., b ≥ a + ε'
              have hab : ε' ≤ |TrueErrorReal X h' c D -
                EmpiricalError X Bool h' (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| := hxs
              have : ε' ≤ EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                (zeroOneLoss Bool) - TrueErrorReal X h' c D := by
                by_contra h_neg; push Not at h_neg
                have h1 : TrueErrorReal X h' c D - EmpiricalError X Bool h'
                  (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) < ε' := by linarith
                have h2 : EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool) - TrueErrorReal X h' c D < ε' := h_neg
                have : |TrueErrorReal X h' c D - EmpiricalError X Bool h'
                  (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| < ε' :=
                  abs_lt.mpr ⟨by linarith, h1⟩
                linarith
              linarith
          calc μ { xs | |TrueErrorReal X h' c D -
                EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool)| ≥ ε' }
              ≤ μ ({ xs | EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool) ≤ TrueErrorReal X h' c D - ε' } ∪
                { xs | EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool) ≥ TrueErrorReal X h' c D + ε' }) :=
                MeasureTheory.measure_mono h_abs_sub
            _ ≤ μ { xs | EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool) ≤ TrueErrorReal X h' c D - ε' } +
                μ { xs | EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool) ≥ TrueErrorReal X h' c D + ε' } :=
                MeasureTheory.measure_union_le _ _
            _ ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * ε' ^ 2)) +
                ENNReal.ofReal (Real.exp (-2 * ↑m * ε' ^ 2)) := by
                gcongr
                · exact hoeffding_one_sided D h' c m hm_pos ε' hε'_pos hε'_le_one
                    (hmeas_fin h' c (hc_meas h') (hc_meas c))
                · exact hoeffding_one_sided_upper D h' c m hm_pos ε' hε'_pos hε'_le_one
                    (hmeas_fin h' c (hc_meas h') (hc_meas c))
            _ = ENNReal.ofReal (2 * Real.exp (-2 * ↑m * ε' ^ 2)) := by
                rw [← two_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]
        -- Union bound: μ(Bad) ≤ N · 2·exp(-2mε'²)
        calc μ Bad
            ≤ μ Bad' := MeasureTheory.measure_mono hBad_sub_Bad'
          _ ≤ μ (⋃ h ∈ Cf, { xs | |TrueErrorReal X h c D -
                EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool)| ≥ ε' }) :=
              MeasureTheory.measure_mono hBad'_sub
          _ ≤ ∑ h ∈ Cf, μ { xs | |TrueErrorReal X h c D -
                EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool)| ≥ ε' } :=
              MeasureTheory.measure_biUnion_finset_le _ _
          _ ≤ ∑ _h ∈ Cf, ENNReal.ofReal (2 * Real.exp (-2 * ↑m * ε' ^ 2)) :=
              Finset.sum_le_sum hper_hyp
          _ = ↑N * ENNReal.ofReal (2 * Real.exp (-2 * ↑m * ε' ^ 2)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ENNReal.ofReal (↑N * (2 * Real.exp (-2 * ↑m * ε' ^ 2))) := by
              rw [ENNReal.ofReal_mul (Nat.cast_nonneg' N),
                  ENNReal.ofReal_natCast]
          _ ≤ ENNReal.ofReal δ := by
              apply ENNReal.ofReal_le_ofReal
              -- Need: N * 2 * exp(-2mε'²) ≤ δ
              by_cases hN_zero : N = 0
              · simp [hN_zero]; linarith
              · have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN_zero)
                have h2N_pos : (0 : ℝ) < 2 * N := by positivity
                -- From m ≥ ceil(log(2N/δ) / (2ε'²)), we get 2mε'² ≥ log(2N/δ)
                -- so exp(-2mε'²) ≤ δ/(2N), thus N * 2 * exp(-2mε'²) ≤ δ
                have hm_ge : (Real.log (2 * ↑N / δ)) / (2 * ε' ^ 2) ≤ ↑m := by
                  calc (Real.log (2 * ↑N / δ)) / (2 * ε' ^ 2)
                      ≤ ↑(Nat.ceil ((Real.log (2 * ↑N / δ)) / (2 * ε' ^ 2))) :=
                        Nat.le_ceil _
                    _ ≤ ↑(max 1 (Nat.ceil ((Real.log (2 * ↑N / δ)) / (2 * ε' ^ 2)))) := by
                        exact_mod_cast le_max_right _ _
                    _ ≤ ↑m := by exact_mod_cast hm
                have h2ε2_pos : (0 : ℝ) < 2 * ε' ^ 2 := by positivity
                have hlog_le : Real.log (2 * ↑N / δ) ≤ ↑m * (2 * ε' ^ 2) := by
                  have := mul_le_mul_of_nonneg_right hm_ge (le_of_lt h2ε2_pos)
                  rwa [div_mul_cancel₀ _ (ne_of_gt h2ε2_pos)] at this
                -- exp(-2mε'²) ≤ exp(-log(2N/δ)) = δ/(2N)
                have h2Nd_pos : (0 : ℝ) < 2 * ↑N / δ := div_pos h2N_pos hδ
                have hexp_bound : Real.exp (-2 * ↑m * ε' ^ 2) ≤ δ / (2 * ↑N) := by
                  have h1 : -(↑m * (2 * ε' ^ 2)) ≤ -Real.log (2 * ↑N / δ) := by linarith
                  have h2 : -2 * ↑m * ε' ^ 2 = -(↑m * (2 * ε' ^ 2)) := by ring
                  rw [h2]
                  calc Real.exp (-(↑m * (2 * ε' ^ 2)))
                      ≤ Real.exp (-Real.log (2 * ↑N / δ)) :=
                        Real.exp_le_exp_of_le h1
                    _ = (2 * ↑N / δ)⁻¹ := by
                        rw [Real.exp_neg, Real.exp_log h2Nd_pos]
                    _ = δ / (2 * ↑N) := by rw [inv_div]
                calc ↑N * (2 * Real.exp (-2 * ↑m * ε' ^ 2))
                    ≤ ↑N * (2 * (δ / (2 * ↑N))) := by gcongr
                    _ = δ := by field_simp [ne_of_gt hN_pos]
      rw [uniform_good_event_eq_bad_compl (D := D) (C := C) (c := c) (m := m) (ε := ε)]
      change ENNReal.ofReal (1 - δ) ≤ μ Badᶜ
      exact bad_event_compl_measure_ge μ Bad hδ h_ub
  · -- ═══ INFINITE X BRANCH ═══
    -- Existing symmetrization proof, unchanged. hinf : Infinite X provides the instance.
    rw [WithTop.lt_top_iff_ne_top] at hC
    obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hC
    intro ε δ hε hδ
    have hC' : VCDim X C < ⊤ := by
      rw [WithTop.lt_top_iff_ne_top]; exact WithTop.ne_top_iff_exists.mpr ⟨d, hd⟩
    obtain ⟨v₀, hv₀⟩ := vcdim_finite_imp_growth_bounded X C hC'
    -- Use v = max v₀ 1 to ensure v ≥ 1 (required by growth_exp_le_delta).
    -- The growth bound for v₀ implies a growth bound for v since
    -- Finset.range (v₀ + 1) ⊆ Finset.range (v + 1) when v₀ ≤ v.
    set v := max v₀ 1 with hv_def
    have hv_pos : 0 < v := by simp [hv_def]
    have hv₀_le_v : v₀ ≤ v := le_max_left v₀ 1
    have hv : ∀ (n : ℕ), v ≤ n →
        GrowthFunction X C n ≤ ∑ i ∈ Finset.range (v + 1), Nat.choose n i := by
      intro n hn
      have hn₀ : v₀ ≤ n := le_trans hv₀_le_v hn
      calc GrowthFunction X C n
          ≤ ∑ i ∈ Finset.range (v₀ + 1), Nat.choose n i := hv₀ n hn₀
        _ ≤ ∑ i ∈ Finset.range (v + 1), Nat.choose n i := by
            apply Finset.sum_le_sum_of_subset
            apply Finset.range_mono
            omega
    use Nat.ceil ((16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ)
    intro D hD c m hm
    by_cases hδ1 : 1 ≤ δ
    · have : ENNReal.ofReal (1 - δ) = 0 := ENNReal.ofReal_eq_zero.mpr (by linarith)
      rw [this]; exact zero_le _
    · push Not at hδ1
      have hm_pos : 0 < m := by
        have h1 : (0 : ℝ) < (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ :=
          div_pos (pow_pos (div_pos (by positivity) (pow_pos hε 2)) (v + 1)) hδ
        exact Nat.lt_of_lt_of_le (Nat.lt_ceil.mpr (by simpa using h1)) hm
      have hE_nullmeas := hWB D c m ε
      have h_ub := uc_bad_event_le_delta_proved D C c hmeas_C (hc_meas c) m hm_pos ε δ hε hδ hδ1
        v hv_pos hv (le_trans (Nat.le_ceil _) (by exact_mod_cast hm)) hE_nullmeas
      set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
      set Bad := { xs : Fin m → X | ∃ h ∈ C,
          |TrueErrorReal X h c D -
           EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
             (zeroOneLoss Bool)| ≥ ε }
      rw [uniform_good_event_eq_bad_compl (D := D) (C := C) (c := c) (m := m) (ε := ε)]
      change ENNReal.ofReal (1 - δ) ≤ μ Badᶜ
      exact bad_event_compl_measure_ge μ Bad hδ h_ub

/-- VCDim < ⊤ → PACLearnable via UC route. -/
theorem vcdim_finite_imp_pac_via_uc' (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    PACLearnable X C := by
  by_cases hne : C.Nonempty
  · exact uc_imp_pac X C hne (vcdim_finite_imp_uc' X C hC hmeas_C hc_meas hWB)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨⟨Set.univ, fun _ => fun _ => false, fun _ => Set.mem_univ _⟩,
           fun _ _ => 0, fun _ _ _ _ _ _ c hcC => by simp [hne] at hcC⟩
