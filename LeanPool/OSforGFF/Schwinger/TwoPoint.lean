/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Schwinger.Defs

/-!
## Schwinger Two-Point Function

This file defines the two-point Schwinger function S₂(x) = ⟨φ(x)φ(0)⟩ as the limit
of smeared correlations as the smearing functions approach Dirac deltas.

For mollifiers φ_ε (smooth, nonnegative, integral 1, support shrinking to 0):
  S₂(x) := lim_{ε→0} SchwingerFunction₂ dμ (φ_ε(·-x)) (φ_ε)
         = lim_{ε→0} ∫∫ φ_ε(u-x) ⟨φ(u)φ(v)⟩ φ_ε(v) du dv

For the GFF with covariance kernel C, this equals C(x) by `double_mollifier_convergence`.
-/

open MeasureTheory
open scoped MeasureTheory

noncomputable section

/-- If f(n+1) → L, then f(n) → L. This is because atTop is shift-invariant. -/
private lemma tendsto_of_tendsto_succ {α : Type*} {f : ℕ → α} {L : Filter α}
    (h : Filter.Tendsto (fun n => f (n + 1)) Filter.atTop L) :
    Filter.Tendsto f Filter.atTop L := (Filter.tendsto_add_atTop_iff_nat 1).mp h

/-! ### Two-Point Schwinger Function Infrastructure -/

/-- Convert a ContDiffBump centered at 0 to a normalized Schwartz function.
    This produces the L¹-normalized version φ.normed volume, which integrates to 1.
    Bump functions have compact support and are smooth, so they are Schwartz.
-/
noncomputable def bumpToSchwartz (φ : ContDiffBump (0 : SpaceTime)) : TestFunction :=
  -- The normed bump has compact support and is C^∞, hence Schwartz
  (φ.hasCompactSupport_normed (μ := volume)).toSchwartzMap φ.contDiff_normed

/-- bumpToSchwartz produces the L¹-normalized bump function. -/
@[simp]
theorem bumpToSchwartz_apply (φ : ContDiffBump (0 : SpaceTime)) (x : SpaceTime) :
    bumpToSchwartz φ x = φ.normed volume x := rfl

/-- Translate a Schwartz function by a vector.
    This is an alias for `SchwartzMap.translate` specialized to SpaceTime.

    Translation preserves smoothness and decay properties.
    See `SchwartzMap.translate` in FunctionalAnalysis.lean for the general version.
-/
noncomputable def translateSchwartz (f : TestFunction) (a : SpaceTime) : TestFunction :=
  f.translate a

/-- The smeared two-point function using a bump function.
    This is well-defined (modulo bumpToSchwartz) and converges to the
    pointwise value as the bump width → 0.

    SmearedTwoPointFunction dμ φ x = ∫∫ φ(u-x) ⟨φ(u)φ(v)⟩ φ(v) du dv
-/
noncomputable def SmearedTwoPointFunction (dμ_config : ProbabilityMeasure FieldConfiguration)
    (φ : ContDiffBump (0 : SpaceTime)) (x : SpaceTime) : ℝ :=
  SchwingerFunction₂ dμ_config
    (translateSchwartz (bumpToSchwartz φ) x)
    (bumpToSchwartz φ)

/-- A canonical sequence of bump functions with rOut → 0.
    We use rOut = 1/n for n ∈ ℕ⁺.
-/
noncomputable def standardBumpSequence (n : ℕ) (hn : n ≠ 0) : ContDiffBump (0 : SpaceTime) :=
  -- Create a bump with rOut = 1/n and rIn = 1/(2n)
  { rIn := 1 / (2 * n)
    rOut := 1 / n
    rIn_pos := by positivity
    rIn_lt_rOut := by
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have h2n : (0 : ℝ) < 2 * n := by positivity
      have : (2 * (n : ℝ))⁻¹ < (n : ℝ)⁻¹ := inv_strictAnti₀ hn' (by linarith)
      simp only [one_div]
      exact this }

/-- Two-point correlation function defined as the limit of smeared correlations.

    **Definition**: S₂(x) := lim_{n→∞} SmearedTwoPointFunction dμ (φ_{1/n}) x

    where φ_ε is a standard bump function with outer radius ε.

    This replaces the old DiracDelta-based definition, which was conceptually correct
    but used sorry since delta functions are distributions, not test functions.

    **Regularization at coincident points**: At x = 0, the two-point function is
    mathematically undefined (it would be infinite for most QFTs). We regularize
    by setting S₂(0) = 0, which is consistent with the convention used in
    freeCovarianceKernel and makes the decay bounds hold trivially at x = 0.

    For the GFF, this limit equals freeCovarianceKernel(x) by `double_mollifier_convergence`.
-/
noncomputable def SchwingerTwoPointFunction
    (dμ_config : ProbabilityMeasure FieldConfiguration) (x : SpaceTime) : ℝ :=
  -- Regularize at coincident points: S₂(0) = 0
  if x = 0 then 0
  else
    -- Use the filter limit along the sequence of bump functions
    -- The limit exists for "good" measures (those with continuous covariance kernels away from 0)
    Filter.limUnder Filter.atTop
      (fun n : ℕ => if hn : n = 0 then 0 else SmearedTwoPointFunction dμ_config
         (standardBumpSequence n hn) x)

/-- SchwingerTwoPointFunction vanishes at coincident points by definition. -/
@[simp]
theorem schwingerTwoPointFunction_zero
    (dμ_config : ProbabilityMeasure FieldConfiguration) :
    SchwingerTwoPointFunction dμ_config 0 = 0 := by
  unfold SchwingerTwoPointFunction
  simp only [ite_true]

/-- The smeared two-point function converges to SchwingerTwoPointFunction as bump width → 0.

    This justifies the limit-based definition of SchwingerTwoPointFunction.
    For measures with continuous covariance kernels (like the GFF), the limit exists
    and equals the kernel value.

    **Key hypothesis**: We assume there exists a continuous (away from 0) kernel C
    such that SchwingerFunction₂ computes the double integral against C.
    This holds for Gaussian measures where C is the covariance kernel.

    The proof uses `double_mollifier_convergence` from FunctionalAnalysis.lean.
-/
theorem smearedTwoPoint_tendsto_schwingerTwoPoint
    (dμ_config : ProbabilityMeasure FieldConfiguration) (x : SpaceTime) (hx : x ≠ 0)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (φ : ι → ContDiffBump (0 : SpaceTime))
    (hφ : Filter.Tendsto (fun i => (φ i).rOut) l (nhds 0))
    -- Key hypothesis: there exists an underlying continuous kernel
    (C : SpaceTime → ℝ)
    (hC : ContinuousOn C {y | y ≠ 0})
    -- The SchwingerFunction₂ computes the double integral against C
    (hS₂ : ∀ (f g : TestFunction),
      SchwingerFunction₂ dμ_config f g = ∫ u, ∫ v, f u * C (u - v) * g v) :
    Filter.Tendsto (fun i => SmearedTwoPointFunction dμ_config (φ i) x)
      l (nhds (C x)) := by
  -- The SmearedTwoPointFunction is SchwingerFunction₂ with mollifiers
  -- By hS₂, this equals ∫∫ φ(u-x) C(u-v) φ(v) du dv
  -- By double_mollifier_convergence, this → C(x)
  simp only [SmearedTwoPointFunction]
  -- Rewrite using hS₂
  have h_eq : ∀ i, SchwingerFunction₂ dμ_config (translateSchwartz (bumpToSchwartz (φ i)) x)
    (bumpToSchwartz (φ i)) =
      ∫ u, ∫ v, (translateSchwartz (bumpToSchwartz (φ i)) x) u * C (u - v) * (bumpToSchwartz (φ i))
        v := by
    intro i
    exact hS₂ _ _
  simp_rw [h_eq]
  -- bumpToSchwartz produces the normed bump, so we can directly apply double_mollifier_convergence
  -- translateSchwartz is SchwartzMap.translate, which shifts by x
  simp only [translateSchwartz, SchwartzMap.translate_apply, bumpToSchwartz_apply]
  -- Now apply double_mollifier_convergence with the Schwartz functions
  exact double_mollifier_convergence C hC x hx φ hφ

/-- For measures with a continuous kernel C, the SchwingerTwoPointFunction equals C(x).

    This is the key result: if the measure has an underlying continuous covariance kernel,
    then the limit-based definition of SchwingerTwoPointFunction evaluates to that kernel.

    Note: For x = 0, the SchwingerTwoPointFunction is defined to be 0 by regularization,
    so this theorem requires x ≠ 0.
-/
theorem schwingerTwoPointFunction_eq_kernel
    (dμ_config : ProbabilityMeasure FieldConfiguration) (x : SpaceTime) (hx : x ≠ 0)
    (C : SpaceTime → ℝ)
    (hC : ContinuousOn C {y | y ≠ 0})
    (hS₂ : ∀ (f g : TestFunction),
      SchwingerFunction₂ dμ_config f g = ∫ u, ∫ v, f u * C (u - v) * g v) :
    SchwingerTwoPointFunction dμ_config x = C x := by
  unfold SchwingerTwoPointFunction
  simp only [hx, ↓reduceIte]  -- unfold the if x = 0 case
  -- By smearedTwoPoint_tendsto_schwingerTwoPoint, the sequence converges to C x
  have h_tendsto : Filter.Tendsto
      (fun n : ℕ => if hn : n = 0 then 0 else SmearedTwoPointFunction dμ_config
         (standardBumpSequence n hn) x)
      Filter.atTop (nhds (C x)) := by
    -- For n ≥ 1, apply smearedTwoPoint_tendsto_schwingerTwoPoint
    -- standardBumpSequence n has rOut = 1/n → 0
    -- Define φ indexed by ℕ+ using (n+1) to avoid the n=0 issue
    -- φ n = standardBumpSequence (n+1) _, so φ n has rOut = 1/(n+1)
    let φ : ℕ → ContDiffBump (0 : SpaceTime) := fun n => standardBumpSequence (n + 1)
      (Nat.succ_ne_zero n)
    -- The rOut of this sequence tends to 0: 1/(n+1) → 0
    have hφ_rOut : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) := by
      simp only [φ, standardBumpSequence]
      have h1 : ∀ n : ℕ, (1 : ℝ) / ↑(n + 1) = 1 / (↑n + 1) := fun n => by norm_cast
      simp_rw [h1]
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    -- Apply smearedTwoPoint_tendsto_schwingerTwoPoint to φ
    have h_smeared : Filter.Tendsto (fun n => SmearedTwoPointFunction dμ_config (φ n) x)
        Filter.atTop (nhds (C x)) :=
      smearedTwoPoint_tendsto_schwingerTwoPoint dμ_config x hx φ hφ_rOut C hC hS₂
    -- Key observation: for n ≥ 1, the original sequence at n equals φ(n-1)
    -- original(n) = SmearedTwo (standardBumpSequence n) = SmearedTwo (φ (n-1)) when n ≥ 1
    -- Since φ(n-1) = standardBumpSequence n for n ≥ 1
    -- We use Filter.tendsto_atTop_add_const_nat:
    -- If Tendsto f atTop L, then Tendsto (f ∘ (· + k)) atTop L
    -- Equivalently: Tendsto (fun n => f (n + k)) atTop L
    -- We have h_smeared: Tendsto (fun n => SmearedTwo (φ n)) atTop (nhds (C x))
    -- This means: Tendsto (fun n => SmearedTwo (standardBumpSequence (n+1))) atTop (nhds (C x))
    -- The original sequence for n ≥ 1 is: SmearedTwo (standardBumpSequence n)
    -- Let f(n) = original(n+1) = SmearedTwo (standardBumpSequence (n+1)) = SmearedTwo (φ n)
    -- So h_smeared says f → C(x)
    -- Now original = f ∘ pred (for n ≥ 1), i.e., original(n) = f(n-1) for n ≥ 1
    -- Since atTop is cofinal under (·-1) for n ≥ 1, original → C(x)
    -- Use tendsto_of_tendsto_succ: if f(n+1) → L then f(n) → L
    -- We show that original(n+1) = (SmearedTwo ∘ φ)(n), so original(n+1) → C(x)
    -- Then by tendsto_of_tendsto_succ, original(n) → C(x)
    apply tendsto_of_tendsto_succ
    -- Goal: Tendsto (fun n => original(n+1)) atTop (nhds (C x))
    -- original(n+1) = if (n+1)=0 then 0 else SmearedTwo (standardBumpSequence (n+1))
    --              = SmearedTwo (standardBumpSequence (n+1))  [since n+1 ≠ 0]
    --              = SmearedTwo (φ n)
    simpa only [Nat.succ_ne_zero, dite_false] using h_smeared
  -- In Hausdorff spaces, limUnder equals the limit when it exists
  exact Filter.Tendsto.limUnder_eq h_tendsto

end
