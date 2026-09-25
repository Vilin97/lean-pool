/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.Operator

/-!
# The Borel calculus is a homomorphism

Three facts complete the bounded Borel functional calculus of a normal operator:

* `borelCalculus_of_continuous` — it extends the continuous functional calculus;
* `inner_borelCalculus_self` — its diagonal matrix elements are the integrals
  against the diagonal measures, `⟪ξ, borelCalculus f ξ⟫ = ∫ f ∂(diagMeasure ξ)`;
* `borelCalculus_mul` — it is multiplicative.

Multiplicativity is the only step that needs the transport argument twice, and
in a specific order: the continuous approximant `p` of `f` is chosen first, and
the tolerance for the approximant `q` of `g` is then taken to be `ε / (1 + ‖p‖)`.
There is no uniform chooseBound on the approximants, so the second tolerance genuinely
has to depend on the first approximant.

## Sources

Multiplicativity of the bounded Borel calculus, by the same transport argument as
the rest of the chain; see
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean` for the
sources of the construction as a whole (the classical spectral theorem for normal
operators, and the Spectra-removal plan for the route comparison).

## Provenance

*New*; see `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean`.
-/

@[expose] public section

open scoped InnerProductSpace ENNReal CompactlySupported
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

namespace IsBddMeasurable

variable {f g : spectrum ℂ a → ℂ}

/-- Continuous symbols are admissible. -/
theorem of_continuous (g : C(spectrum ℂ a, ℂ)) : IsBddMeasurable (fun x => g x) :=
  ⟨g.continuous.measurable, ‖g‖, norm_nonneg _, fun x => g.norm_coe_le_norm x⟩

omit [CompleteSpace H] in
/-- Products of admissible symbols are admissible. -/
theorem mul (hf : IsBddMeasurable f) (hg : IsBddMeasurable g) :
    IsBddMeasurable (fun x => f x * g x) := by
  refine ⟨hf.measurable.mul hg.measurable, hf.chooseBound * hg.chooseBound, ?_, fun x => ?_⟩
  · have := hf.chooseBound_nonneg; have := hg.chooseBound_nonneg; positivity
  · rw [norm_mul]
    exact mul_le_mul (hf.norm_le_chooseBound x) (hg.norm_le_chooseBound x) (norm_nonneg _)
      hf.chooseBound_nonneg

omit [CompleteSpace H] in
/-- Admissible symbols are integrable against every finite measure on the
spectrum. -/
theorem integrable (hf : IsBddMeasurable f) (ν : Measure (spectrum ℂ a))
    [IsFiniteMeasure ν] : Integrable f ν :=
  integrable_of_bounded hf.measurable hf.norm_le_chooseBound ν

omit [CompleteSpace H] in
/-- Conjugates of admissible symbols are admissible. -/
theorem conj (hf : IsBddMeasurable f) :
    IsBddMeasurable (fun x => (starRingEnd ℂ) (f x)) :=
  ⟨Complex.continuous_conj.measurable.comp hf.measurable, hf.chooseBound, hf.chooseBound_nonneg,
    fun x => by rw [RCLike.norm_conj]; exact hf.norm_le_chooseBound x⟩

end IsBddMeasurable

section Diagonal

variable (ha : IsStarNormal a) {f : spectrum ℂ a → ℂ}

/-- The diagonal of the polarised integral is the integral against the diagonal
measure. -/
theorem pair_self_eq_integral (hfm : Measurable f) {M : ℝ} (hfb : ∀ x, ‖f x‖ ≤ M)
    (ξ : H) : pair ha f ξ ξ = ∫ x, f x ∂(diagMeasure ha ξ) := by
  refine eq_of_forall_norm_sub_le (C := 2) (by norm_num) fun ε hε => ?_
  have : IsFiniteMeasure (∑ k : Fin 4, diagMeasure ha (pairVectors ξ ξ k)) :=
    isFiniteMeasure_sum_diagMeasure ha _
  set ν : Measure (spectrum ℂ a) :=
    (∑ k : Fin 4, diagMeasure ha (pairVectors ξ ξ k)) + diagMeasure ha ξ with hν
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hfi : Integrable f ν := integrable_of_bounded hfm hfb ν
  obtain ⟨g, hgi, hgle⟩ := exists_continuous_integral_norm_sub_le ν hfi hε
  have hdom : ∀ k : Fin 4, diagMeasure ha (pairVectors ξ ξ k) ≤ ν := fun k =>
    Measure.le_add_right (diagMeasure_le_sum ha (pairVectors ξ ξ) k)
  have hdomξ : diagMeasure ha ξ ≤ ν := Measure.le_add_left le_rfl
  have h1 : ‖pair ha f ξ ξ - pair ha (fun x => g x) ξ ξ‖ ≤ ε :=
    le_trans (norm_pair_sub_pair_le ha ν ξ ξ hdom hfi hgi) hgle
  have h2 : ‖(∫ x, f x ∂(diagMeasure ha ξ)) - (∫ x, g x ∂(diagMeasure ha ξ))‖ ≤ ε :=
    le_trans (norm_integral_sub_integral_le hdomξ hfi hgi) hgle
  have hgeq : pair ha (fun x => g x) ξ ξ = ∫ x, g x ∂(diagMeasure ha ξ) := by
    rw [pair_of_continuous ha g, integral_diagMeasure]
  have key : pair ha f ξ ξ - ∫ x, f x ∂(diagMeasure ha ξ)
      = (pair ha f ξ ξ - pair ha (fun x => g x) ξ ξ)
        - ((∫ x, f x ∂(diagMeasure ha ξ)) - (∫ x, g x ∂(diagMeasure ha ξ))) := by
    rw [hgeq]; ring
  rw [key]
  refine le_trans (norm_sub_le _ _) ?_
  linarith

/-- **The diagonal matrix elements of the Borel calculus.** -/
theorem inner_borelCalculus_self (hf : IsBddMeasurable f) (ξ : H) :
    ⟪ξ, borelCalculus ha hf ξ⟫_ℂ = ∫ x, f x ∂(diagMeasure ha ξ) := by
  rw [inner_borelCalculus, pair_self_eq_integral ha hf.measurable hf.norm_le_chooseBound]

end Diagonal

section Continuous

variable (ha : IsStarNormal a)

/-- The Borel calculus extends the continuous functional calculus. -/
theorem borelCalculus_of_continuous (g : C(spectrum ℂ a, ℂ))
    (hg : IsBddMeasurable (fun x => g x)) :
    borelCalculus ha hg = cfcHom ha g := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  rw [inner_borelCalculus, pair_of_continuous]

/-- The Borel calculus is unital. -/
theorem borelCalculus_one (h1 : IsBddMeasurable (fun _ : spectrum ℂ a => (1 : ℂ))) :
    borelCalculus ha h1 = 1 := by
  have h := borelCalculus_of_continuous ha (1 : C(spectrum ℂ a, ℂ)) h1
  exact h.trans (map_one _)

/-- The Borel calculus kills the zero symbol. -/
theorem borelCalculus_zero (h0 : IsBddMeasurable (fun _ : spectrum ℂ a => (0 : ℂ))) :
    borelCalculus ha h0 = 0 := by
  have h := borelCalculus_of_continuous ha (0 : C(spectrum ℂ a, ℂ)) h0
  exact h.trans (map_zero _)

end Continuous

section Multiplicative

variable (ha : IsStarNormal a) {f g : spectrum ℂ a → ℂ}

/-- Pointwise product estimate: replacing both factors costs each factor's bound times the
other's error.  Split as `P * Q - F * G = P * (Q - G) + (P - F) * G`. -/
private theorem norm_mul_sub_mul_le {P Q F G : ℂ} {cP cG : ℝ}
    (hP : ‖P‖ ≤ cP) (hG : ‖G‖ ≤ cG) :
    ‖P * Q - F * G‖ ≤ cP * ‖Q - G‖ + cG * ‖P - F‖ := by
  have hsplit : P * Q - F * G = P * (Q - G) + (P - F) * G := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mul]
  have e1 : ‖P‖ * ‖Q - G‖ ≤ cP * ‖Q - G‖ :=
    mul_le_mul_of_nonneg_right hP (norm_nonneg _)
  have e2 : ‖P - F‖ * ‖G‖ ≤ cG * ‖P - F‖ := by
    rw [mul_comm ‖P - F‖ ‖G‖]
    exact mul_le_mul_of_nonneg_right hG (norm_nonneg _)
  linarith

/-- An `L¹` error measured against a smaller measure is bounded by the same error against a
larger one.  Used once per approximant, and the `norm_sub_rev` flip is what makes the two
directions match. -/
private theorem integral_norm_sub_le_of_measure_le {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} (hμν : μ ≤ ν)
    {u v : α → ℂ} (h : Integrable (fun x => v x - u x) ν) :
    ∫ x, ‖u x - v x‖ ∂μ ≤ ∫ x, ‖v x - u x‖ ∂ν := by
  have hrev : ∀ x, ‖u x - v x‖ = ‖v x - u x‖ := fun x => norm_sub_rev _ _
  simp only [hrev]
  exact integral_mono_measure hμν
    (Filter.Eventually.of_forall fun _ => norm_nonneg _) h.norm

/-- **The `L¹` half of step 5.**  If `u` approximates `F` and `v` approximates `G`, each against
its own dominating measure, the product `u * v` approximates `F * G` against the smaller measure
with the two errors weighted by the opposite factor's bound.

Stated separately because it is the only genuinely quantitative step of
`pair_mul_eq_inner_comp`: everything around it is bookkeeping about which measure dominates
which. -/
private theorem integral_norm_mul_sub_mul_le {α : Type*} [MeasurableSpace α]
    {μ ν₁ ν₂ : Measure α} (h₁ : μ ≤ ν₁) (h₂ : μ ≤ ν₂)
    {u v F G : α → ℂ} {cu cG δ₁ δ₂ : ℝ}
    (hcu : ∀ x, ‖u x‖ ≤ cu) (hcG : ∀ x, ‖G x‖ ≤ cG) (hcu0 : 0 ≤ cu) (hcG0 : 0 ≤ cG)
    (huv : Integrable (fun x => u x * v x - F x * G x) μ)
    (hvG : Integrable (fun x => v x - G x) μ) (huF : Integrable (fun x => u x - F x) μ)
    (hvG₂ : Integrable (fun x => G x - v x) ν₂) (huF₁ : Integrable (fun x => F x - u x) ν₁)
    (hδ₂ : ∫ x, ‖G x - v x‖ ∂ν₂ ≤ δ₂) (hδ₁ : ∫ x, ‖F x - u x‖ ∂ν₁ ≤ δ₁) :
    ∫ x, ‖u x * v x - F x * G x‖ ∂μ ≤ cu * δ₂ + cG * δ₁ := by
  calc ∫ x, ‖u x * v x - F x * G x‖ ∂μ
      ≤ ∫ x, (cu * ‖v x - G x‖ + cG * ‖u x - F x‖) ∂μ :=
        integral_mono huv.norm
          ((hvG.norm.const_mul cu).add (huF.norm.const_mul cG))
          (fun x => norm_mul_sub_mul_le (hcu x) (hcG x))
    _ = cu * (∫ x, ‖v x - G x‖ ∂μ) + cG * (∫ x, ‖u x - F x‖ ∂μ) := by
        rw [integral_add (hvG.norm.const_mul cu) (huF.norm.const_mul cG),
          integral_const_mul, integral_const_mul]
    _ ≤ cu * δ₂ + cG * δ₁ := by
        have hv' : ∫ x, ‖v x - G x‖ ∂μ ≤ δ₂ :=
          le_trans (integral_norm_sub_le_of_measure_le h₂ hvG₂) hδ₂
        have hu' : ∫ x, ‖u x - F x‖ ∂μ ≤ δ₁ :=
          le_trans (integral_norm_sub_le_of_measure_le h₁ huF₁) hδ₁
        have t1 := mul_le_mul_of_nonneg_left hv' hcu0
        have t2 := mul_le_mul_of_nonneg_left hu' hcG0
        linarith

/-- **Replacing a bounded measurable symbol by a continuous approximant, at one pair.**

Steps 1 and 3 of `pair_mul_eq_inner_comp` are this lemma at `(ψ, η)` and `(ζ, ξ)`; extracting it
is what keeps the two from being the same six lines twice. -/
private theorem norm_pair_sub_cfcHom_le (ha : IsStarNormal a) {u : spectrum ℂ a → ℂ}
    (hu : IsBddMeasurable u) (ν : Measure (spectrum ℂ a)) [IsFiniteMeasure ν] (ψ ξ : H)
    (hdom : ∀ k : Fin 4, diagMeasure ha (pairVectors ψ ξ k) ≤ ν)
    (r : C(spectrum ℂ a, ℂ)) (hri : Integrable (fun x => (r : spectrum ℂ a → ℂ) x) ν)
    {δ : ℝ} (hrle : ∫ x, ‖u x - r x‖ ∂ν ≤ δ) :
    ‖pair ha u ψ ξ - ⟪ψ, cfcHom ha r ξ⟫_ℂ‖ ≤ δ := by
  rw [← pair_of_continuous ha r ψ ξ]
  exact le_trans (norm_pair_sub_pair_le ha ν ψ ξ hdom (hu.integrable ν) hri) hrle

/-- **Multiplicativity of the Borel calculus, in matrix-element form.**

The proof is an `ε`-argument in five steps, and what remains inline after the four preliminary
lemmas above is the scaffolding they cannot absorb: three measures, each needing its own
`IsFiniteMeasure` instance, and two applications of `exists_continuous_integral_norm_sub_le`
whose outputs (`p`, `q`) every later step mentions.

1. replace `f` by a continuous `p` at the pair `(ψ, η)` — `norm_pair_sub_cfcHom_le`;
2. move `p` to the left slot, turning `(ψ, η)` into `(ζ, ξ)` with `ζ = p⋆ ψ`;
3. replace `g` by a continuous `q` at `(ζ, ξ)` — the same lemma again;
4. recombine `p` and `q` into the single continuous symbol `p * q`;
5. replace the continuous product by the Borel one — `integral_norm_mul_sub_mul_le`, which is
   where the quantitative content lives.

The `ε'` of step 3 is `ε / (1 + ‖p‖)`, chosen after `p` is known so that step 5's `‖p‖ * ε'`
term is bounded by `ε` regardless of how large `‖p‖` turned out to be. -/
theorem pair_mul_eq_inner_comp (hf : IsBddMeasurable f) (hg : IsBddMeasurable g)
    (ψ ξ : H) :
    pair ha (fun x => f x * g x) ψ ξ
      = ⟪ψ, borelCalculus ha hf (borelCalculus ha hg ξ)⟫_ℂ := by
  set η := borelCalculus ha hg ξ with hη
  refine eq_of_forall_norm_sub_le (C := 3 + hg.chooseBound)
    (by have := hg.chooseBound_nonneg; linarith) fun ε hε => ?_
  -- the measure attached to the target pair `(ψ, ξ)`, common to all steps
  have : IsFiniteMeasure (∑ k : Fin 4, diagMeasure ha (pairVectors ψ ξ k)) :=
    isFiniteMeasure_sum_diagMeasure ha _
  set νP : Measure (spectrum ℂ a) := ∑ k : Fin 4, diagMeasure ha (pairVectors ψ ξ k) with hνP
  have : IsFiniteMeasure (∑ k : Fin 4, diagMeasure ha (pairVectors ψ η k)) :=
    isFiniteMeasure_sum_diagMeasure ha _
  set ν₁ : Measure (spectrum ℂ a) :=
    νP + ∑ k : Fin 4, diagMeasure ha (pairVectors ψ η k) with hν₁
  have : IsFiniteMeasure ν₁ := by rw [hν₁]; infer_instance
  -- choose the approximant of `f` first
  obtain ⟨p, hpi, hple⟩ :=
    exists_continuous_integral_norm_sub_le ν₁ (hf.integrable ν₁) hε
  have hpnn : (0 : ℝ) < 1 + ‖p‖ := by positivity
  set ε' : ℝ := ε / (1 + ‖p‖) with hε'
  have hε'pos : 0 < ε' := div_pos hε hpnn
  have hε'le : ε' ≤ ε := by
    rw [hε']
    exact div_le_self hε.le (le_add_of_nonneg_right (norm_nonneg p))
  -- the vector against which `g` will be tested
  set ζ := (cfcHom ha (star p)) ψ with hζ
  have : IsFiniteMeasure (∑ k : Fin 4, diagMeasure ha (pairVectors ζ ξ k)) :=
    isFiniteMeasure_sum_diagMeasure ha _
  set ν₂ : Measure (spectrum ℂ a) :=
    νP + ∑ k : Fin 4, diagMeasure ha (pairVectors ζ ξ k) with hν₂
  have : IsFiniteMeasure ν₂ := by rw [hν₂]; infer_instance
  obtain ⟨q, hqi, hqle⟩ :=
    exists_continuous_integral_norm_sub_le ν₂ (hg.integrable ν₂) hε'pos
  -- step 1: replace `f` by `p` at the pair `(ψ, η)`
  have hdom₁ : ∀ k : Fin 4, diagMeasure ha (pairVectors ψ η k) ≤ ν₁ := fun k =>
    Measure.le_add_left (diagMeasure_le_sum ha (pairVectors ψ η) k)
  have step1 : ‖pair ha f ψ η - ⟪ψ, cfcHom ha p η⟫_ℂ‖ ≤ ε :=
    norm_pair_sub_cfcHom_le ha hf ν₁ ψ η hdom₁ p hpi hple
  -- step 2: move `p` to the left slot
  have hadj : ∀ w : H, ⟪ψ, cfcHom ha p w⟫_ℂ = ⟪ζ, w⟫_ℂ := by
    intro w
    rw [hζ, map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have step2 : ⟪ψ, cfcHom ha p η⟫_ℂ = pair ha g ζ ξ := by
    rw [hadj, hη, inner_borelCalculus]
  -- step 3: replace `g` by `q` at the pair `(ζ, ξ)`
  have hdom₂ : ∀ k : Fin 4, diagMeasure ha (pairVectors ζ ξ k) ≤ ν₂ := fun k =>
    Measure.le_add_left (diagMeasure_le_sum ha (pairVectors ζ ξ) k)
  have step3 : ‖pair ha g ζ ξ - ⟪ζ, cfcHom ha q ξ⟫_ℂ‖ ≤ ε' :=
    norm_pair_sub_cfcHom_le ha hg ν₂ ζ ξ hdom₂ q hqi hqle
  -- step 4: recombine into a single continuous symbol
  have step4 : ⟪ζ, cfcHom ha q ξ⟫_ℂ = pair ha (fun x => p x * q x) ψ ξ := by
    have hpc : pair ha (fun x => p x * q x) ψ ξ = ⟪ψ, cfcHom ha (p * q) ξ⟫_ℂ :=
      pair_of_continuous ha (p * q) ψ ξ
    rw [hpc, map_mul, ← hadj]
    rfl
  -- step 5: replace the continuous product by the Borel one
  have hdomP₁ : νP ≤ ν₁ := Measure.le_add_right le_rfl
  have hdomP₂ : νP ≤ ν₂ := Measure.le_add_right le_rfl
  have hdomP : ∀ k : Fin 4, diagMeasure ha (pairVectors ψ ξ k) ≤ νP := fun k =>
    diagMeasure_le_sum ha (pairVectors ψ ξ) k
  have : IsFiniteMeasure νP := by rw [hνP]; infer_instance
  have hpq : IsBddMeasurable (fun x => p x * q x) :=
    (IsBddMeasurable.of_continuous p).mul (IsBddMeasurable.of_continuous q)
  have hfg : IsBddMeasurable (fun x => f x * g x) := hf.mul hg
  have step5 : ‖pair ha (fun x => p x * q x) ψ ξ - pair ha (fun x => f x * g x) ψ ξ‖
      ≤ ‖p‖ * ε' + hg.chooseBound * ε := by
    refine le_trans (norm_pair_sub_pair_le ha νP ψ ξ hdomP (hpq.integrable νP)
      (hfg.integrable νP)) ?_
    exact integral_norm_mul_sub_mul_le hdomP₁ hdomP₂
      (fun x => p.norm_coe_le_norm x) (fun x => hg.norm_le_chooseBound x)
      (norm_nonneg p) hg.chooseBound_nonneg
      ((hpq.integrable νP).sub (hfg.integrable νP))
      (((IsBddMeasurable.of_continuous q).integrable νP).sub (hg.integrable νP))
      (((IsBddMeasurable.of_continuous p).integrable νP).sub (hf.integrable νP))
      ((hg.integrable ν₂).sub hqi) ((hf.integrable ν₁).sub hpi) hqle hple
  -- assemble
  have hpε : ‖p‖ * ε' ≤ ε := by
    rw [hε', mul_div_assoc', div_le_iff₀ hpnn]
    nlinarith [norm_nonneg p, hε.le]
  have key : pair ha (fun x => f x * g x) ψ ξ - pair ha f ψ η
      = -((pair ha f ψ η - ⟪ψ, cfcHom ha p η⟫_ℂ)
          + (pair ha g ζ ξ - ⟪ζ, cfcHom ha q ξ⟫_ℂ)
          + (pair ha (fun x => p x * q x) ψ ξ - pair ha (fun x => f x * g x) ψ ξ)) := by
    rw [step2, step4]; ring
  rw [hη] at key ⊢
  rw [inner_borelCalculus, key, norm_neg]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
  have := hg.chooseBound_nonneg
  nlinarith [step1, step3, step5, hpε, hε'le]

/-- The image of the Borel calculus is commutative. -/
theorem borelCalculus_comm (hf : IsBddMeasurable f) (hg : IsBddMeasurable g) :
    borelCalculus ha hf * borelCalculus ha hg
      = borelCalculus ha hg * borelCalculus ha hf := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  have h1 : ⟪ψ, (borelCalculus ha hf * borelCalculus ha hg) ξ⟫_ℂ
      = pair ha (fun x => f x * g x) ψ ξ := (pair_mul_eq_inner_comp ha hf hg ψ ξ).symm
  have h2 : ⟪ψ, (borelCalculus ha hg * borelCalculus ha hf) ξ⟫_ℂ
      = pair ha (fun x => g x * f x) ψ ξ := (pair_mul_eq_inner_comp ha hg hf ψ ξ).symm
  have hfun : (fun x => f x * g x) = (fun x => g x * f x) := by funext x; ring
  rw [h1, h2, hfun]

/-- **The Borel calculus is multiplicative.** -/
theorem borelCalculus_mul (hf : IsBddMeasurable f) (hg : IsBddMeasurable g) :
    borelCalculus ha (hf.mul hg) = borelCalculus ha hf * borelCalculus ha hg := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  rw [inner_borelCalculus, pair_mul_eq_inner_comp ha hf hg]
  rfl

end Multiplicative

section Linear

variable (ha : IsStarNormal a) {f g : spectrum ℂ a → ℂ}

omit [CompleteSpace H] in
/-- Sums of admissible symbols are admissible. -/
theorem IsBddMeasurable.add (hf : IsBddMeasurable f) (hg : IsBddMeasurable g) :
    IsBddMeasurable (fun x => f x + g x) := by
  refine ⟨hf.measurable.add hg.measurable, hf.chooseBound + hg.chooseBound, ?_, fun x => ?_⟩
  · have := hf.chooseBound_nonneg; have := hg.chooseBound_nonneg; positivity
  · exact le_trans (norm_add_le _ _)
      (add_le_add (hf.norm_le_chooseBound x) (hg.norm_le_chooseBound x))

omit [CompleteSpace H] in
/-- Scalar multiples of admissible symbols are admissible. -/
theorem IsBddMeasurable.const_smul (c : ℂ) (hf : IsBddMeasurable f) :
    IsBddMeasurable (fun x => c * f x) := by
  refine ⟨measurable_const.mul hf.measurable, ‖c‖ * hf.chooseBound, ?_, fun x => ?_⟩
  · have := hf.chooseBound_nonneg; positivity
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hf.norm_le_chooseBound x) (norm_nonneg c)

/-- The Borel calculus is additive in the symbol. -/
theorem borelCalculus_add (hf : IsBddMeasurable f) (hg : IsBddMeasurable g) :
    borelCalculus ha (hf.add hg) = borelCalculus ha hf + borelCalculus ha hg := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  rw [_root_.add_apply, inner_add_right, inner_borelCalculus, inner_borelCalculus,
    inner_borelCalculus]
  simp only [pair_def]
  rw [integral_add (hf.integrable _) (hg.integrable _),
    integral_add (hf.integrable _) (hg.integrable _),
    integral_add (hf.integrable _) (hg.integrable _),
    integral_add (hf.integrable _) (hg.integrable _)]
  ring

/-- The Borel calculus is homogeneous in the symbol. -/
theorem borelCalculus_const_smul (c : ℂ) (hf : IsBddMeasurable f) :
    borelCalculus ha (hf.const_smul c) = c • borelCalculus ha hf := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  rw [_root_.smul_apply, inner_smul_right, inner_borelCalculus, inner_borelCalculus]
  simp only [pair_def]
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  ring

/-- The Borel calculus only sees the symbol up to sets that are null for every
diagonal measure. -/
theorem borelCalculus_congr_ae (hf : IsBddMeasurable f) (hg : IsBddMeasurable g)
    (h : ∀ η : H, f =ᵐ[diagMeasure ha η] g) :
    borelCalculus ha hf = borelCalculus ha hg := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  rw [inner_borelCalculus, inner_borelCalculus]
  simp only [pair_def]
  rw [integral_congr_ae (h _), integral_congr_ae (h _), integral_congr_ae (h _),
    integral_congr_ae (h _)]

end Linear

section Adjoint

variable (ha : IsStarNormal a) {f : spectrum ℂ a → ℂ}

/-- Conjugating the symbol transposes the polarised integral. -/
theorem pair_conj (hfm : Measurable f) {M : ℝ} (hfb : ∀ x, ‖f x‖ ≤ M) (ψ ξ : H) :
    pair ha (fun x => (starRingEnd ℂ) (f x)) ψ ξ = (starRingEnd ℂ) (pair ha f ξ ψ) := by
  refine eq_of_forall_norm_sub_le (C := 2) (by norm_num) fun ε hε => ?_
  classical
  set v : Fin 4 ⊕ Fin 4 → H := Sum.elim (pairVectors ψ ξ) (pairVectors ξ ψ) with hv
  set ν : Measure (spectrum ℂ a) := ∑ j, diagMeasure ha (v j) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_sum_diagMeasure ha v
  have hfi : Integrable f ν := integrable_of_bounded hfm hfb ν
  obtain ⟨g, hgi, hgle⟩ := exists_continuous_integral_norm_sub_le ν hfi hε
  have hcfi : Integrable (fun x => (starRingEnd ℂ) (f x)) ν :=
    integrable_of_bounded (f := fun x => (starRingEnd ℂ) (f x))
      (Complex.continuous_conj.measurable.comp hfm)
      (fun x => by rw [RCLike.norm_conj]; exact hfb x) ν
  have hcgi : Integrable (fun x => (starRingEnd ℂ) (g x)) ν :=
    (IsBddMeasurable.of_continuous (star g)).integrable ν
  have hnormeq : ∫ x, ‖(starRingEnd ℂ) (f x) - (starRingEnd ℂ) (g x)‖ ∂ν
      = ∫ x, ‖f x - g x‖ ∂ν := by
    congr 1
    funext x
    rw [← map_sub, RCLike.norm_conj]
  have h1 : ‖pair ha (fun x => (starRingEnd ℂ) (f x)) ψ ξ
      - pair ha (fun x => (starRingEnd ℂ) (g x)) ψ ξ‖ ≤ ε := by
    refine le_trans (norm_pair_sub_pair_le ha ν ψ ξ
      (fun k => diagMeasure_le_sum ha v (Sum.inl k)) hcfi hcgi) ?_
    rw [hnormeq]; exact hgle
  have h2 : ‖pair ha f ξ ψ - pair ha (fun x => g x) ξ ψ‖ ≤ ε :=
    le_trans (norm_pair_sub_pair_le ha ν ξ ψ
      (fun k => diagMeasure_le_sum ha v (Sum.inr k)) hfi hgi) hgle
  have hmid : pair ha (fun x => (starRingEnd ℂ) (g x)) ψ ξ
      = (starRingEnd ℂ) (pair ha (fun x => g x) ξ ψ) := by
    have hstar : pair ha (fun x => (starRingEnd ℂ) (g x)) ψ ξ
        = ⟪ψ, cfcHom ha (star g) ξ⟫_ℂ := pair_of_continuous ha (star g) ψ ξ
    rw [hstar, pair_of_continuous, map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm]
  have hkey : pair ha (fun x => (starRingEnd ℂ) (f x)) ψ ξ
      - (starRingEnd ℂ) (pair ha f ξ ψ)
      = (pair ha (fun x => (starRingEnd ℂ) (f x)) ψ ξ
          - pair ha (fun x => (starRingEnd ℂ) (g x)) ψ ξ)
        - ((starRingEnd ℂ) (pair ha f ξ ψ)
          - (starRingEnd ℂ) (pair ha (fun x => g x) ξ ψ)) := by
    rw [hmid]; ring
  rw [hkey]
  refine le_trans (norm_sub_le _ _) ?_
  have h2' : ‖(starRingEnd ℂ) (pair ha f ξ ψ)
      - (starRingEnd ℂ) (pair ha (fun x => g x) ξ ψ)‖ ≤ ε := by
    rw [← map_sub, RCLike.norm_conj]; exact h2
  linarith

/-- The Borel calculus is `⋆`-preserving. -/
theorem borelCalculus_conj (hf : IsBddMeasurable f) :
    borelCalculus ha hf.conj = ContinuousLinearMap.adjoint (borelCalculus ha hf) := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  rw [inner_borelCalculus, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm,
    inner_borelCalculus]
  exact pair_conj ha hf.measurable hf.norm_le_chooseBound ψ ξ

/-- **The sharp norm chooseBound**: `‖borelCalculus f ξ‖ ≤ M ‖ξ‖` whenever `‖f‖ ≤ M`. -/
theorem norm_borelCalculus_apply_le (hf : IsBddMeasurable f) {M : ℝ} (hM : 0 ≤ M)
    (hfb : ∀ x, ‖f x‖ ≤ M) (ξ : H) :
    ‖borelCalculus ha hf ξ‖ ≤ M * ‖ξ‖ := by
  have hsq : ‖borelCalculus ha hf ξ‖ ^ 2
      = ∫ x, ((starRingEnd ℂ) (f x) * f x).re ∂(diagMeasure ha ξ) := by
    have hinner : ⟪borelCalculus ha hf ξ, borelCalculus ha hf ξ⟫_ℂ
        = ⟪ξ, (borelCalculus ha hf.conj * borelCalculus ha hf) ξ⟫_ℂ := by
      rw [borelCalculus_conj, _root_.mul_apply_eq_comp,
        ContinuousLinearMap.adjoint_inner_right]
    rw [← borelCalculus_mul, inner_borelCalculus_self] at hinner
    have hnorm : ⟪borelCalculus ha hf ξ, borelCalculus ha hf ξ⟫_ℂ
        = ((‖borelCalculus ha hf ξ‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [hnorm] at hinner
    have hre := congrArg Complex.re hinner
    rw [Complex.ofReal_re] at hre
    have hint : (∫ x, (starRingEnd ℂ) (f x) * f x ∂(diagMeasure ha ξ)).re
        = ∫ x, ((starRingEnd ℂ) (f x) * f x).re ∂(diagMeasure ha ξ) :=
      (integral_re ((hf.conj.mul hf).integrable _)).symm
    rw [← hint]
    exact hre
  have hptwise : ∀ x, ((starRingEnd ℂ) (f x) * f x).re ≤ M ^ 2 := by
    intro x
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have h := hfb x
    have hnn : ‖f x‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (f x)]
    have : ‖f x‖ ^ 2 = (f x).re ^ 2 + (f x).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    nlinarith
  have hbound : ∫ x, ((starRingEnd ℂ) (f x) * f x).re ∂(diagMeasure ha ξ)
      ≤ M ^ 2 * ‖ξ‖ ^ 2 := by
    calc ∫ x, ((starRingEnd ℂ) (f x) * f x).re ∂(diagMeasure ha ξ)
        ≤ ∫ _x, M ^ 2 ∂(diagMeasure ha ξ) :=
          integral_mono ((hf.conj.mul hf).integrable _).re (integrable_const _) hptwise
      _ = ‖ξ‖ ^ 2 * M ^ 2 := by
          rw [integral_const, smul_eq_mul, MeasureTheory.measureReal_def,
            diagMeasure_univ_toReal]
      _ = M ^ 2 * ‖ξ‖ ^ 2 := by ring
  have hfinal : ‖borelCalculus ha hf ξ‖ ^ 2 ≤ (M * ‖ξ‖) ^ 2 := by
    rw [hsq, mul_pow]; exact hbound
  nlinarith [norm_nonneg (borelCalculus ha hf ξ), hfinal, mul_nonneg hM (norm_nonneg ξ)]

end Adjoint

end BorelCalculus
end TauCeti
