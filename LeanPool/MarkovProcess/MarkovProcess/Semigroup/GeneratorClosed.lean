/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Generator


/-!
# The generator is closed

If vectors `u i` of the generator domain of a strongly continuous contraction semigroup `S`
converge to `f` and their generators `S.generator (u i)` converge to `g`, then `f` lies in the
domain and `S.generator f = g` (`mem_generatorDomain_of_tendsto_generator`,
`generator_eq_of_tendsto_generator`).  The proof passes to the limit in the fundamental identity
`S t (u i) - u i = ∫₀ᵗ S s (S.generator (u i)) ds`, using that the orbit integral over `[0, t]`
is `t`-Lipschitz in the vector (`norm_orbitIntegral_le`), and reads the generator of `f` off the
limit identity through the time averages `t⁻¹ ∫₀ᵗ S s g ds → g`.

Main results: `orbitIntegral_sub`, `norm_orbitIntegral_le`, `tendsto_orbitIntegral`,
`operator_sub_eq_orbitIntegral_of_tendsto_generator`, `mem_generatorDomain_of_tendsto_generator`,
`generator_eq_of_tendsto_generator`.

Nothing is asserted about the domain beyond closedness of the graph; density is proved in
`Semigroup/Generator.lean`.
-/

@[expose] public section

open Filter Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)

/-- The orbit integral is additive in the vector. -/
theorem orbitIntegral_sub (f g : E) (u : ℝ) :
    S.orbitIntegral f u - S.orbitIntegral g u = S.orbitIntegral (f - g) u := by
  simp only [orbitIntegral_apply, map_sub]
  exact (intervalIntegral.integral_sub ((S.continuous_operator_toNNReal f).intervalIntegrable _ _)
    ((S.continuous_operator_toNNReal g).intervalIntegrable _ _)).symm

/-- The orbit integral over `[0, t]` is bounded by `t` times the norm of the vector. -/
theorem norm_orbitIntegral_le (f : E) (t : NNReal) : ‖S.orbitIntegral f t‖ ≤ ‖f‖ * t := by
  rw [orbitIntegral_apply]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
    (C := ‖f‖) (f := fun s : ℝ ↦ S (Real.toNNReal s) f) (fun s _ ↦ S.norm_apply_le _ f)
  rwa [sub_zero, abs_of_nonneg t.coe_nonneg] at h

/-- The orbit integral over `[0, t]` is continuous in the vector. -/
theorem tendsto_orbitIntegral {ι : Type*} {l : Filter ι} {v : ι → E} {g : E}
    (hv : Tendsto v l (𝓝 g)) (t : NNReal) :
    Tendsto (fun i ↦ S.orbitIntegral (v i) t) l (𝓝 (S.orbitIntegral g t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun i ↦ ‖v i - g‖ * (t : ℝ)) (fun i ↦ norm_nonneg _) (fun i ↦ ?_) ?_
  · rw [S.orbitIntegral_sub]
    exact S.norm_orbitIntegral_le _ t
  · simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hv).mul_const (t : ℝ)

section Closed

variable [CompleteSpace E]
variable {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → S.generatorDomain} {f g : E}

/-- Passing to the limit in the fundamental identity of the generator. -/
theorem operator_sub_eq_orbitIntegral_of_tendsto_generator
    (hu : Tendsto (fun i ↦ (u i : E)) l (𝓝 f))
    (hL : Tendsto (fun i ↦ S.generator (u i)) l (𝓝 g)) (t : NNReal) :
    S t f - f = S.orbitIntegral g t := by
  have h1 : Tendsto (fun i ↦ S t (u i : E) - (u i : E)) l (𝓝 (S t f - f)) :=
    (((S t).continuous.tendsto f).comp hu).sub hu
  have h2 : Tendsto (fun i ↦ S t (u i : E) - (u i : E)) l (𝓝 (S.orbitIntegral g t)) := by
    refine (S.tendsto_orbitIntegral hL t).congr fun i ↦ ?_
    rw [orbitIntegral_apply]
    exact (S.operator_sub_eq_integral (u i) t).symm
  exact tendsto_nhds_unique h1 h2

/-- The difference quotients of the limit vector converge to the limit of the generators. -/
theorem tendsto_differenceQuotient_of_tendsto_generator
    (hu : Tendsto (fun i ↦ (u i : E)) l (𝓝 f))
    (hL : Tendsto (fun i ↦ S.generator (u i)) l (𝓝 g)) :
    Tendsto (fun t : NNReal ↦ (t : ℝ)⁻¹ • (S t f - f)) (𝓝[>] 0) (𝓝 g) := by
  refine (S.tendsto_inv_smul_orbitIntegral g).congr fun t ↦ ?_
  rw [S.operator_sub_eq_orbitIntegral_of_tendsto_generator hu hL t]

/-- **The generator is closed**: the limit of domain vectors whose generators converge lies in
the domain. -/
theorem mem_generatorDomain_of_tendsto_generator
    (hu : Tendsto (fun i ↦ (u i : E)) l (𝓝 f))
    (hL : Tendsto (fun i ↦ S.generator (u i)) l (𝓝 g)) : f ∈ S.generatorDomain :=
  S.mem_generatorDomain_of_tendsto (S.tendsto_differenceQuotient_of_tendsto_generator hu hL)

/-- **The generator is closed**: its value at the limit is the limit of the generators. -/
theorem generator_eq_of_tendsto_generator
    (hu : Tendsto (fun i ↦ (u i : E)) l (𝓝 f))
    (hL : Tendsto (fun i ↦ S.generator (u i)) l (𝓝 g)) :
    S.generator ⟨f, S.mem_generatorDomain_of_tendsto_generator hu hL⟩ = g :=
  S.generator_eq_of_tendsto _ (S.tendsto_differenceQuotient_of_tendsto_generator hu hL)

end Closed

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
