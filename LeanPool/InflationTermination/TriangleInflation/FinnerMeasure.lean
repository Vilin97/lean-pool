/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import LeanPool.InflationTermination.TriangleInflation.Main
import LeanPool.InflationTermination.TriangleInflation.Exponent

/-!
# Finner's inequality for arbitrary latent alphabets

This file removes the finite-latent-alphabet boundary from the incompatibility half of the
manuscript *Inflation for the Classical Triangle* (`papers/inflation-nontermination`).

`Defs.lean` defines `TriangleCompatible` through `TriangleModel`, whose three latent spaces
are `Fintype`s. That is a proper formalization boundary: a finite-latent model is in
particular an arbitrary-latent model, so the finite-latent compatible set is a subset of the
paper's `C_△`, and a theorem `¬ TriangleCompatible P` is therefore the *weaker* of the two
nonmembership statements. Closing the gap needs either the cardinality reduction of Rosset,
Gisin and Wolfe (2018) — quoted in the paper, not formalized — or a proof of Finner's
inequality (paper Lemma 5.7) for arbitrary latent probability spaces. This file gives the
second.

`TriangleModelM` is a triangle model whose latent alphabets are arbitrary measurable spaces
carrying probability measures, with measurable response probabilities `f, g, h` valued in
`[0,1]`; its observed law is the Bochner integral of the product of the three response
masses against the product measure `μX ⊗ μY ⊗ μZ`. No finiteness, no countability, no
determinism, no regularity beyond measurability is assumed.

* `finner_of_compatibleM` is Lemma 5.7 in that generality: `P(000)² ≤ P_A(0) P_B(0) P_C(0)`.
  The proof is the paper's: Cauchy–Schwarz in `y` for fixed `(x,z)`, Cauchy–Schwarz in the
  independent pair `(x,z)` against the constant function, then `f ≤ 1`, `g² ≤ g`, `h² ≤ h`
  because the responses are probabilities, and Fubini to factor the `(x,z)` integral of a
  product of a function of `x` and a function of `z`. Cauchy–Schwarz is proved here from
  nonnegativity of `∫ (u - λv)²`, so the only measure theory used is Fubini–Tonelli and
  linearity.
* `triangleCompatibleM_of_triangleCompatible` says the new compatible set contains the old
  one: a finite latent alphabet carries the counting measure weighted by its source law,
  with every set measurable, and the Bochner integral against the product of those measures
  is the finite sum of `TriangleModel.law`. The converse inclusion is exactly the
  Rosset–Gisin–Wolfe reduction and is *not* proved here; it is not needed, because every
  statement below is a nonmembership statement and so uses the inclusion in the direction
  proved.
* The theorems named with the suffix `M` — `witness_not_compatibleM`, `Rlaw_not_compatibleM`,
  `Peps_not_compatibleM`, `main_violationM`, `no_finite_characterizing_orderM` — are the
  arbitrary-latent forms of the incompatibility statements of `Finner.lean`, `Main.lean` and
  `Exponent.lean`. They are each the same finite computation about the three-bit law (which
  mentions no model at all) combined with `finner_of_compatibleM` in place of
  `finner_of_compatible`. For these five statements the finite-latent boundary recorded in
  the header of `Defs.lean` is gone: nothing about the latent alphabets is assumed, so
  `¬ TriangleCompatibleM P` is nonmembership in the paper's `C_△` itself.

The membership half of the paper (the inflation witnesses) is untouched: it is a statement
about finite inflation hierarchies and carries no latent-alphabet hypothesis.
-/

namespace TriangleInflation

open MeasureTheory

noncomputable
section

/-! ## Triangle models with arbitrary latent probability spaces -/

/-- A triangle model with arbitrary latent alphabets: three measurable spaces carrying
probability measures, and the three response probabilities `f(x,z) = Pr(A = 0 | x,z)`,
`g(x,y) = Pr(B = 0 | x,y)`, `h(z,y) = Pr(C = 0 | z,y)`. This is `TriangleModel` of
`Defs.lean` with `Fintype` weight functions replaced by `MeasureTheory.Measure`s. -/
structure TriangleModelM where
  /-- The latent alphabet shared by `A` and `B`. -/
  X : Type
  /-- The latent alphabet shared by `B` and `C`. -/
  Y : Type
  /-- The latent alphabet shared by `A` and `C`. -/
  Z : Type
  [measX : MeasurableSpace X]
  [measY : MeasurableSpace Y]
  [measZ : MeasurableSpace Z]
  /-- The law of the source `X`. -/
  μX : Measure X
  /-- The law of the source `Y`. -/
  μY : Measure Y
  /-- The law of the source `Z`. -/
  μZ : Measure Z
  [probX : IsProbabilityMeasure μX]
  [probY : IsProbabilityMeasure μY]
  [probZ : IsProbabilityMeasure μZ]
  /-- `f(x,z) = Pr(A = 0 | x,z)`. -/
  f : X × Z → ℝ
  /-- `g(x,y) = Pr(B = 0 | x,y)`. -/
  g : X × Y → ℝ
  /-- `h(z,y) = Pr(C = 0 | z,y)`. -/
  h : Z × Y → ℝ

attribute [instance] TriangleModelM.measX TriangleModelM.measY TriangleModelM.measZ
  TriangleModelM.probX TriangleModelM.probY TriangleModelM.probZ

/-- A measure-theoretic triangle model is valid when the three response probabilities are
measurable and take values in `[0,1]`. The source laws are probability measures by
construction, which is the measure-theoretic form of the three `IsLaw` conditions of
`TriangleModel.Valid`. -/
def TriangleModelM.Valid (M : TriangleModelM) : Prop :=
  Measurable M.f ∧ Measurable M.g ∧ Measurable M.h ∧
    (∀ p, 0 ≤ M.f p ∧ M.f p ≤ 1) ∧ (∀ p, 0 ≤ M.g p ∧ M.g p ≤ 1) ∧
    (∀ p, 0 ≤ M.h p ∧ M.h p ≤ 1)

/-- The observed law of a measure-theoretic triangle model: the integral of the product of
the three response masses against the product measure `μX ⊗ μY ⊗ μZ`, the sources being
independent and the responses conditionally independent given the sources. -/
def TriangleModelM.law (M : TriangleModelM) : ThreeBit → ℝ := fun w =>
  ∫ p : M.X × M.Y × M.Z,
      respMass (M.f (p.1, p.2.2)) w.1 * respMass (M.g (p.1, p.2.1)) w.2.1
        * respMass (M.h (p.2.2, p.2.1)) w.2.2
    ∂(M.μX.prod (M.μY.prod M.μZ))

/-- Paper Section 2.3: the triangle-compatible set `C_△`, with **no** restriction on the
latent alphabets. `triangleCompatibleM_of_triangleCompatible` shows it contains the
finite-latent set `TriangleCompatible` of `Defs.lean`. -/
def TriangleCompatibleM (P : ThreeBit → ℝ) : Prop :=
  ∃ M : TriangleModelM, M.Valid ∧ M.law = P


/-! ## Analytic tools -/

/-- A bounded measurable real function on a finite measure space is integrable. -/
private lemma integrable_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {F : α → ℝ} (hm : Measurable F) {C : ℝ} (hb : ∀ a, |F a| ≤ C) :
    Integrable F μ :=
  (integrable_const C).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using hb a)

/-- Cauchy–Schwarz for the Bochner integral, proved from nonnegativity of `∫ (u - l v)²`. -/
private lemma integral_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v : α → ℝ}
    (hu : Integrable (fun a => u a ^ 2) μ) (hv : Integrable (fun a => v a ^ 2) μ)
    (huv : Integrable (fun a => u a * v a) μ) :
    (∫ a, u a * v a ∂μ) ^ 2 ≤ (∫ a, u a ^ 2 ∂μ) * (∫ a, v a ^ 2 ∂μ) := by
  set c := ∫ a, u a ^ 2 ∂μ with hc
  set A := ∫ a, v a ^ 2 ∂μ with hA
  set b := ∫ a, u a * v a ∂μ with hb
  have hA0 : 0 ≤ A := integral_nonneg fun a => sq_nonneg _
  have hc0 : 0 ≤ c := integral_nonneg fun a => sq_nonneg _
  have expand : ∀ l : ℝ, (fun a => (u a - l * v a) ^ 2)
      = fun a => u a ^ 2 - 2 * l * (u a * v a) + l ^ 2 * v a ^ 2 := by
    intro l; funext a; ring
  have key : ∀ l : ℝ, 0 ≤ c - 2 * l * b + l ^ 2 * A := by
    intro l
    have h0 : 0 ≤ ∫ a, (u a - l * v a) ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
    have i0 : Integrable (fun a => 2 * l * (u a * v a)) μ := huv.const_mul (2 * l)
    have i1 : Integrable (fun a => u a ^ 2 - 2 * l * (u a * v a)) μ := hu.sub i0
    have i2 : Integrable (fun a => l ^ 2 * v a ^ 2) μ := hv.const_mul (l ^ 2)
    rw [expand l, integral_add i1 i2, integral_sub hu i0, integral_const_mul,
      integral_const_mul] at h0
    linarith
  rcases eq_or_lt_of_le hA0 with hA0' | hApos
  · have hbz : b = 0 := by
      by_contra hbne
      have h := key ((c + 1) / (2 * b))
      have he : 2 * ((c + 1) / (2 * b)) * b = c + 1 := by field_simp
      rw [← hA0'] at h
      rw [he] at h
      simp at h
      linarith
    rw [hbz, ← hA0']
    norm_num
  · have h2 : 0 ≤ (c - 2 * (b / A) * b + (b / A) ^ 2 * A) * A :=
      mul_nonneg (key _) hApos.le
    have e : (c - 2 * (b / A) * b + (b / A) ^ 2 * A) * A = c * A - b ^ 2 := by
      field_simp; ring
    rw [e] at h2
    linarith

/-- Cauchy–Schwarz with a nonnegative weight, the measure-theoretic form of
`Finner.weighted_cauchy_schwarz`. -/
private lemma integral_weighted_cs {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w u v : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (h1 : Integrable (fun a => w a * u a ^ 2) μ) (h2 : Integrable (fun a => w a * v a ^ 2) μ)
    (h3 : Integrable (fun a => w a * (u a * v a)) μ) :
    (∫ a, w a * (u a * v a) ∂μ) ^ 2
      ≤ (∫ a, w a * u a ^ 2 ∂μ) * (∫ a, w a * v a ^ 2 ∂μ) := by
  have e1 : (fun a => (Real.sqrt (w a) * u a) ^ 2) = fun a => w a * u a ^ 2 := by
    funext a; rw [mul_pow, Real.sq_sqrt (hw a)]
  have e2 : (fun a => (Real.sqrt (w a) * v a) ^ 2) = fun a => w a * v a ^ 2 := by
    funext a; rw [mul_pow, Real.sq_sqrt (hw a)]
  have e3 : (fun a => Real.sqrt (w a) * u a * (Real.sqrt (w a) * v a))
      = fun a => w a * (u a * v a) := by
    funext a
    have hs : Real.sqrt (w a) * Real.sqrt (w a) = w a := Real.mul_self_sqrt (hw a)
    calc Real.sqrt (w a) * u a * (Real.sqrt (w a) * v a)
        = Real.sqrt (w a) * Real.sqrt (w a) * (u a * v a) := by ring
      _ = w a * (u a * v a) := by rw [hs]
  have key := integral_cs (μ := μ) (u := fun a => Real.sqrt (w a) * u a)
    (v := fun a => Real.sqrt (w a) * v a) (by rw [e1]; exact h1) (by rw [e2]; exact h2)
    (by rw [e3]; exact h3)
  rwa [e1, e2, e3] at key

/-! ## The measure-theoretic Finner inequality -/

/-- The analytic core of Finner's inequality for the triangle with arbitrary probability
spaces as latent alphabets: Cauchy–Schwarz in `y`, then Cauchy–Schwarz in the independent
pair `(x,z)` against the constant function, then `f ≤ 1`, `g² ≤ g`, `h² ≤ h`. This is the
measure-theoretic form of `Finner.finner_core`. -/
private lemma finner_coreM {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    {f : X × Z → ℝ} {g : X × Y → ℝ} {h : Z × Y → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (hh : ∀ p, 0 ≤ h p ∧ h p ≤ 1) :
    (∫ p : X × Z, f p * (∫ y, g (p.1, y) * h (p.2, y) ∂μY) ∂(μX.prod μZ)) ^ 2
      ≤ (∫ p : X × Z, f p ∂(μX.prod μZ)) * (∫ q : X × Y, g q ∂(μX.prod μY))
          * (∫ q : Z × Y, h q ∂(μZ.prod μY)) := by
  -- measurability of the partial integrals
  have hGm : Measurable fun x => ∫ y, g (x, y) ∂μY :=
    (hgm.stronglyMeasurable.integral_prod_right').measurable
  have hHm : Measurable fun z => ∫ y, h (z, y) ∂μY :=
    (hhm.stronglyMeasurable.integral_prod_right').measurable
  have hGHm : Measurable fun r : (X × Z) × Y => g (r.1.1, r.2) * h (r.1.2, r.2) := by fun_prop
  have hKm : Measurable fun p : X × Z => ∫ y, g (p.1, y) * h (p.2, y) ∂μY :=
    (hGHm.stronglyMeasurable.integral_prod_right').measurable
  -- integrability of the bounded measurable data
  have hgi : Integrable g (μX.prod μY) :=
    integrable_of_bound hgm (C := 1) fun q => by rw [abs_of_nonneg (hg q).1]; exact (hg q).2
  have hhi : Integrable h (μZ.prod μY) :=
    integrable_of_bound hhm (C := 1) fun q => by rw [abs_of_nonneg (hh q).1]; exact (hh q).2
  have hfi : Integrable f (μX.prod μZ) :=
    integrable_of_bound hfm (C := 1) fun p => by rw [abs_of_nonneg (hf p).1]; exact (hf p).2
  have hgy : ∀ x : X, Integrable (fun y => g (x, y)) μY := fun x =>
    integrable_of_bound (hgm.comp (measurable_prodMk_left)) (C := 1)
      fun y => by rw [abs_of_nonneg (hg _).1]; exact (hg _).2
  have hhy : ∀ z : Z, Integrable (fun y => h (z, y)) μY := fun z =>
    integrable_of_bound (hhm.comp (measurable_prodMk_left)) (C := 1)
      fun y => by rw [abs_of_nonneg (hh _).1]; exact (hh _).2
  -- the one-sided marginals are in `[0,1]`
  have hG0 : ∀ x, 0 ≤ ∫ y, g (x, y) ∂μY := fun x => integral_nonneg fun y => (hg _).1
  have hH0 : ∀ z, 0 ≤ ∫ y, h (z, y) ∂μY := fun z => integral_nonneg fun y => (hh _).1
  have hG1 : ∀ x, (∫ y, g (x, y) ∂μY) ≤ 1 := by
    intro x
    have := integral_mono (hgy x) (integrable_const (1 : ℝ)) fun y => (hg (x, y)).2
    simpa using this
  have hH1 : ∀ z, (∫ y, h (z, y) ∂μY) ≤ 1 := by
    intro z
    have := integral_mono (hhy z) (integrable_const (1 : ℝ)) fun y => (hh (z, y)).2
    simpa using this
  -- step 1: Cauchy–Schwarz in `y`, then `g² ≤ g` and `h² ≤ h`
  have step1 : ∀ p : X × Z, (∫ y, g (p.1, y) * h (p.2, y) ∂μY) ^ 2
      ≤ (∫ y, g (p.1, y) ∂μY) * (∫ y, h (p.2, y) ∂μY) := by
    intro p
    have hg2 : Integrable (fun y => g (p.1, y) ^ 2) μY :=
      integrable_of_bound ((hgm.comp measurable_prodMk_left).pow_const 2) (C := 1) fun y => by
        rw [abs_of_nonneg (by positivity)]
        nlinarith [(hg (p.1, y)).1, (hg (p.1, y)).2]
    have hh2 : Integrable (fun y => h (p.2, y) ^ 2) μY :=
      integrable_of_bound ((hhm.comp measurable_prodMk_left).pow_const 2) (C := 1) fun y => by
        rw [abs_of_nonneg (by positivity)]
        nlinarith [(hh (p.2, y)).1, (hh (p.2, y)).2]
    have hgh : Integrable (fun y => g (p.1, y) * h (p.2, y)) μY :=
      integrable_of_bound ((hgm.comp measurable_prodMk_left).mul
        (hhm.comp measurable_prodMk_left)) (C := 1) fun y => by
        rw [abs_of_nonneg (mul_nonneg (hg _).1 (hh _).1)]
        nlinarith [(hg (p.1, y)).1, (hg (p.1, y)).2, (hh (p.2, y)).1, (hh (p.2, y)).2]
    have cs := integral_cs hg2 hh2 hgh
    have hle1 : (∫ y, g (p.1, y) ^ 2 ∂μY) ≤ ∫ y, g (p.1, y) ∂μY :=
      integral_mono hg2 (hgy p.1) fun y => by nlinarith [(hg (p.1, y)).1, (hg (p.1, y)).2]
    have hle2 : (∫ y, h (p.2, y) ^ 2 ∂μY) ≤ ∫ y, h (p.2, y) ∂μY :=
      integral_mono hh2 (hhy p.2) fun y => by nlinarith [(hh (p.2, y)).1, (hh (p.2, y)).2]
    have hnn : 0 ≤ ∫ y, h (p.2, y) ^ 2 ∂μY := integral_nonneg fun y => sq_nonneg _
    calc (∫ y, g (p.1, y) * h (p.2, y) ∂μY) ^ 2
        ≤ (∫ y, g (p.1, y) ^ 2 ∂μY) * (∫ y, h (p.2, y) ^ 2 ∂μY) := cs
      _ ≤ (∫ y, g (p.1, y) ∂μY) * (∫ y, h (p.2, y) ∂μY) :=
          mul_le_mul hle1 hle2 hnn (hG0 p.1)
  -- `K` is in `[0,1]`
  have hK0 : ∀ p : X × Z, 0 ≤ ∫ y, g (p.1, y) * h (p.2, y) ∂μY := fun p =>
    integral_nonneg fun y => mul_nonneg (hg _).1 (hh _).1
  have hK1 : ∀ p : X × Z, (∫ y, g (p.1, y) * h (p.2, y) ∂μY) ≤ 1 := by
    intro p
    nlinarith [step1 p, hG1 p.1, hH1 p.2, hG0 p.1, hH0 p.2, hK0 p]
  -- step 2: Cauchy–Schwarz in `(x,z)` against the constant function
  have hfK : Integrable (fun p : X × Z => f p * (1 * (∫ y, g (p.1, y) * h (p.2, y) ∂μY)))
      (μX.prod μZ) :=
    integrable_of_bound (hfm.mul (measurable_const.mul hKm)) (C := 1) fun p => by
      rw [abs_of_nonneg (by nlinarith [(hf p).1, hK0 p])]
      nlinarith [(hf p).1, (hf p).2, hK0 p, hK1 p]
  have hfone : Integrable (fun p : X × Z => f p * (1 : ℝ) ^ 2) (μX.prod μZ) := by
    simpa using hfi
  have hfK2 : Integrable (fun p : X × Z => f p * (∫ y, g (p.1, y) * h (p.2, y) ∂μY) ^ 2)
      (μX.prod μZ) :=
    integrable_of_bound (hfm.mul (hKm.pow_const 2)) (C := 1) fun p => by
      rw [abs_of_nonneg (by nlinarith [(hf p).1, hK0 p])]
      nlinarith [(hf p).1, (hf p).2, hK0 p, hK1 p]
  have cs2 := integral_weighted_cs (μ := μX.prod μZ) (w := f) (u := fun _ => (1 : ℝ))
    (v := fun p => ∫ y, g (p.1, y) * h (p.2, y) ∂μY) (fun p => (hf p).1) hfone hfK2 hfK
  simp only [one_pow, mul_one, one_mul] at cs2
  refine le_trans cs2 ?_
  -- step 3: `f ≤ 1` and `K² ≤ G H`, then independence of `x` and `z`
  have hGHi : Integrable (fun p : X × Z => (∫ y, g (p.1, y) ∂μY) * (∫ y, h (p.2, y) ∂μY))
      (μX.prod μZ) :=
    integrable_of_bound ((hGm.comp measurable_fst).mul (hHm.comp measurable_snd)) (C := 1)
      fun p => by
      rw [abs_of_nonneg (mul_nonneg (hG0 p.1) (hH0 p.2))]
      nlinarith [hG0 p.1, hG1 p.1, hH0 p.2, hH1 p.2]
  have step3 : (∫ p : X × Z, f p * (∫ y, g (p.1, y) * h (p.2, y) ∂μY) ^ 2 ∂(μX.prod μZ))
      ≤ (∫ x, (∫ y, g (x, y) ∂μY) ∂μX) * (∫ z, (∫ y, h (z, y) ∂μY) ∂μZ) := by
    have hmono := integral_mono hfK2 hGHi (fun p => by
      nlinarith [(hf p).1, (hf p).2, step1 p, hG0 p.1, hH0 p.2, sq_nonneg
        (∫ y, g (p.1, y) * h (p.2, y) ∂μY)])
    rwa [integral_prod_mul (fun x => ∫ y, g (x, y) ∂μY) fun z => ∫ y, h (z, y) ∂μY] at hmono
  have hgprod : (∫ q : X × Y, g q ∂(μX.prod μY)) = ∫ x, (∫ y, g (x, y) ∂μY) ∂μX :=
    integral_prod g hgi
  have hhprod : (∫ q : Z × Y, h q ∂(μZ.prod μY)) = ∫ z, (∫ y, h (z, y) ∂μY) ∂μZ :=
    integral_prod h hhi
  rw [hgprod, hhprod, mul_assoc]
  exact mul_le_mul_of_nonneg_left step3 (integral_nonneg fun p => (hf p).1)

/-! ## Reduction of the observed law to the integrals of the core lemma -/

/-- A measurable function with values in `[0,1]` is integrable on a finite measure. -/
private lemma integrable_of_unit {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {F : α → ℝ} (hm : Measurable F) (h0 : ∀ a, 0 ≤ F a) (h1 : ∀ a, F a ≤ 1) :
    Integrable F μ :=
  integrable_of_bound hm (C := 1) fun a => by rw [abs_of_nonneg (h0 a)]; exact h1 a

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The `A`-marginal integral collapses onto the pair `(x,z)`. -/
private lemma law_margA (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    {f : X × Z → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) :
    (∫ p : X × (Y × Z), f (p.1, p.2.2) ∂(μX.prod (μY.prod μZ)))
      = ∫ p : X × Z, f p ∂(μX.prod μZ) := by
  have hfi : Integrable f (μX.prod μZ) :=
    integrable_of_unit hfm (fun p => (hf p).1) fun p => (hf p).2
  have hFi : Integrable (fun p : X × (Y × Z) => f (p.1, p.2.2)) (μX.prod (μY.prod μZ)) :=
    integrable_of_unit (by fun_prop) (fun p => (hf _).1) fun p => (hf _).2
  rw [integral_prod _ hFi]
  have inner : ∀ x : X, (∫ q : Y × Z, f (x, q.2) ∂(μY.prod μZ)) = ∫ z, f (x, z) ∂μZ := by
    intro x
    have : Integrable (fun q : Y × Z => f (x, q.2)) (μY.prod μZ) :=
      integrable_of_unit (by fun_prop) (fun q => (hf _).1) fun q => (hf _).2
    rw [integral_prod_symm _ this]
    simp
  simp only [inner]
  exact (integral_prod _ hfi).symm

/-- The `B`-marginal integral collapses onto the pair `(x,y)`. -/
private lemma law_margB (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    {g : X × Y → ℝ} (hgm : Measurable g) (hg : ∀ q, 0 ≤ g q ∧ g q ≤ 1) :
    (∫ p : X × (Y × Z), g (p.1, p.2.1) ∂(μX.prod (μY.prod μZ)))
      = ∫ q : X × Y, g q ∂(μX.prod μY) := by
  have hgi : Integrable g (μX.prod μY) :=
    integrable_of_unit hgm (fun q => (hg q).1) fun q => (hg q).2
  have hFi : Integrable (fun p : X × (Y × Z) => g (p.1, p.2.1)) (μX.prod (μY.prod μZ)) :=
    integrable_of_unit (by fun_prop) (fun p => (hg _).1) fun p => (hg _).2
  rw [integral_prod _ hFi]
  have inner : ∀ x : X, (∫ q : Y × Z, g (x, q.1) ∂(μY.prod μZ)) = ∫ y, g (x, y) ∂μY := by
    intro x
    have : Integrable (fun q : Y × Z => g (x, q.1)) (μY.prod μZ) :=
      integrable_of_unit (by fun_prop) (fun q => (hg _).1) fun q => (hg _).2
    rw [integral_prod _ this]
    simp
  simp only [inner]
  exact (integral_prod _ hgi).symm

/-- The `C`-marginal integral collapses onto the pair `(z,y)`. -/
private lemma law_margC (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    {h : Z × Y → ℝ} (hhm : Measurable h) (hh : ∀ q, 0 ≤ h q ∧ h q ≤ 1) :
    (∫ p : X × (Y × Z), h (p.2.2, p.2.1) ∂(μX.prod (μY.prod μZ)))
      = ∫ q : Z × Y, h q ∂(μZ.prod μY) := by
  have hhi : Integrable h (μZ.prod μY) :=
    integrable_of_unit hhm (fun q => (hh q).1) fun q => (hh q).2
  have hFi : Integrable (fun p : X × (Y × Z) => h (p.2.2, p.2.1)) (μX.prod (μY.prod μZ)) :=
    integrable_of_unit (by fun_prop) (fun p => (hh _).1) fun p => (hh _).2
  have hqi : Integrable (fun q : Y × Z => h (q.2, q.1)) (μY.prod μZ) :=
    integrable_of_unit (by fun_prop) (fun q => (hh _).1) fun q => (hh _).2
  rw [integral_prod _ hFi]
  change (∫ _ : X, (∫ q : Y × Z, h (q.2, q.1) ∂(μY.prod μZ)) ∂μX) = _
  rw [integral_prod_symm _ hqi, ← integral_prod _ hhi]
  simp

/-- A product of two numbers in `[0,1]` lies in `[0,1]`. -/
private lemma unit_mul {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    0 ≤ a * b ∧ a * b ≤ 1 :=
  ⟨mul_nonneg ha.1 hb.1, by nlinarith [ha.1, ha.2, hb.1, hb.2]⟩

/-- The all-zero atom, with the `y`-integral performed first: this is Fubini together with
the independence of the three sources. -/
private lemma law_atom (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    {f : X × Z → ℝ} {g : X × Y → ℝ} {h : Z × Y → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (hg : ∀ q, 0 ≤ g q ∧ g q ≤ 1) (hh : ∀ q, 0 ≤ h q ∧ h q ≤ 1) :
    (∫ p : X × (Y × Z), f (p.1, p.2.2) * g (p.1, p.2.1) * h (p.2.2, p.2.1)
        ∂(μX.prod (μY.prod μZ)))
      = ∫ p : X × Z, f p * (∫ y, g (p.1, y) * h (p.2, y) ∂μY) ∂(μX.prod μZ) := by
  have hGHm : Measurable fun r : (X × Z) × Y => g (r.1.1, r.2) * h (r.1.2, r.2) := by fun_prop
  have hKm : Measurable fun p : X × Z => ∫ y, g (p.1, y) * h (p.2, y) ∂μY :=
    (hGHm.stronglyMeasurable.integral_prod_right').measurable
  have hghy : ∀ p : X × Z, Integrable (fun y => g (p.1, y) * h (p.2, y)) μY := fun p =>
    integrable_of_unit (by fun_prop) (fun y => (unit_mul (hg _) (hh _)).1)
      fun y => (unit_mul (hg _) (hh _)).2
  have hK : ∀ p : X × Z, 0 ≤ (∫ y, g (p.1, y) * h (p.2, y) ∂μY)
      ∧ (∫ y, g (p.1, y) * h (p.2, y) ∂μY) ≤ 1 := by
    intro p
    refine ⟨integral_nonneg fun y => (unit_mul (hg _) (hh _)).1, ?_⟩
    have := integral_mono (hghy p) (integrable_const (1 : ℝ))
      fun y => (unit_mul (hg (p.1, y)) (hh (p.2, y))).2
    simpa using this
  have hFi : Integrable (fun p : X × (Y × Z) =>
      f (p.1, p.2.2) * g (p.1, p.2.1) * h (p.2.2, p.2.1)) (μX.prod (μY.prod μZ)) :=
    integrable_of_unit (by fun_prop) (fun p => (unit_mul (unit_mul (hf _) (hg _)) (hh _)).1)
      fun p => (unit_mul (unit_mul (hf _) (hg _)) (hh _)).2
  rw [integral_prod _ hFi]
  have inner : ∀ x : X, (∫ q : Y × Z, f (x, q.2) * g (x, q.1) * h (q.2, q.1) ∂(μY.prod μZ))
      = ∫ z, f (x, z) * (∫ y, g (x, y) * h (z, y) ∂μY) ∂μZ := by
    intro x
    have hqi : Integrable (fun q : Y × Z => f (x, q.2) * g (x, q.1) * h (q.2, q.1))
        (μY.prod μZ) :=
      integrable_of_unit (by fun_prop) (fun q => (unit_mul (unit_mul (hf _) (hg _)) (hh _)).1)
        fun q => (unit_mul (unit_mul (hf _) (hg _)) (hh _)).2
    rw [integral_prod_symm _ hqi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    change (∫ y : Y, f (x, z) * g (x, y) * h (z, y) ∂μY)
      = f (x, z) * ∫ y, g (x, y) * h (z, y) ∂μY
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  simp only [inner]
  have hKi : Integrable (fun p : X × Z => f p * (∫ y, g (p.1, y) * h (p.2, y) ∂μY))
      (μX.prod μZ) :=
    integrable_of_unit (hfm.mul hKm) (fun p => (unit_mul (hf p) (hK p)).1)
      fun p => (unit_mul (hf p) (hK p)).2
  exact (integral_prod _ hKi).symm

/-! ## The Finner inequality for arbitrary latent alphabets -/

/-- The response mass of the outcome `0`. -/
private lemma respMassM_false (q : ℝ) : respMass q false = q := rfl

/-- The response mass of the outcome `1`. -/
private lemma respMassM_true (q : ℝ) : respMass q true = 1 - q := rfl

/-- A response mass of a probability in `[0,1]` lies in `[0,1]`. -/
private lemma respMass_unit {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (b : Bool) :
    0 ≤ respMass q b ∧ respMass q b ≤ 1 := by
  cases b
  · exact ⟨h0, h1⟩
  · exact ⟨show (0 : ℝ) ≤ 1 - q by linarith, show (1 : ℝ) - q ≤ 1 by linarith⟩

/-- Response masses of a measurable response probability are measurable. -/
private lemma measurable_respMass {α : Type*} [MeasurableSpace α] {F : α → ℝ}
    (hF : Measurable F) (b : Bool) : Measurable fun a => respMass (F a) b := by
  cases b
  · exact hF
  · exact measurable_const.sub hF

/-- Summing an integral over the four values of a pair of bits. -/
private lemma integral_sum_bool₂ {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : Bool → Bool → α → ℝ) (hF : ∀ b c, Integrable (F b c) μ) :
    (∑ b : Bool, ∑ c : Bool, ∫ a, F b c a ∂μ) = ∫ a, (∑ b : Bool, ∑ c : Bool, F b c a) ∂μ := by
  have i : ∀ b : Bool, Integrable (fun a => F b true a + F b false a) μ :=
    fun b => (hF b true).add (hF b false)
  simp only [Fintype.sum_bool]
  rw [integral_add (i true) (i false), integral_add (hF true true) (hF true false),
    integral_add (hF false true) (hF false false)]

/-- Paper Lemma 5.7 (`lem:finner`) with **arbitrary probability spaces** as latent alphabets:
every law that comes from a measure-theoretic triangle model satisfies
`P(000)² ≤ P_A(0) P_B(0) P_C(0)`. -/
theorem finner_of_compatibleM {P : ThreeBit → ℝ} (hc : TriangleCompatibleM P) :
    atom000 P ^ 2 ≤ margA P * margB P * margC P := by
  obtain ⟨M, ⟨hfm, hgm, hhm, hf, hg, hh⟩, rfl⟩ := hc
  set ν := M.μX.prod (M.μY.prod M.μZ) with hν
  have hfm' : Measurable fun p : M.X × (M.Y × M.Z) => M.f (p.1, p.2.2) := by fun_prop
  have hgm' : Measurable fun p : M.X × (M.Y × M.Z) => M.g (p.1, p.2.1) := by fun_prop
  have hhm' : Measurable fun p : M.X × (M.Y × M.Z) => M.h (p.2.2, p.2.1) := by fun_prop
  have hInt : ∀ (a b c : Bool),
      Integrable (fun p : M.X × (M.Y × M.Z) =>
        respMass (M.f (p.1, p.2.2)) a * respMass (M.g (p.1, p.2.1)) b
          * respMass (M.h (p.2.2, p.2.1)) c) ν := by
    intro a b c
    refine integrable_of_unit
      (((measurable_respMass hfm' a).mul (measurable_respMass hgm' b)).mul
        (measurable_respMass hhm' c)) (fun p => ?_) (fun p => ?_)
    · exact (unit_mul (unit_mul (respMass_unit (hf _).1 (hf _).2 a)
        (respMass_unit (hg _).1 (hg _).2 b)) (respMass_unit (hh _).1 (hh _).2 c)).1
    · exact (unit_mul (unit_mul (respMass_unit (hf _).1 (hf _).2 a)
        (respMass_unit (hg _).1 (hg _).2 b)) (respMass_unit (hh _).1 (hh _).2 c)).2
  -- the all-zero atom
  have hatom : atom000 M.law
      = ∫ p : M.X × M.Z, M.f p * (∫ y, M.g (p.1, y) * M.h (p.2, y) ∂M.μY) ∂(M.μX.prod M.μZ) := by
    rw [← law_atom M.μX M.μY M.μZ hfm hgm hhm hf hg hh]
    rfl
  -- the three single-party marginals
  have hmA : margA M.law = ∫ p : M.X × M.Z, M.f p ∂(M.μX.prod M.μZ) := by
    rw [← law_margA (Y := M.Y) M.μX M.μY M.μZ hfm hf]
    calc margA M.law
        = ∑ b : Bool, ∑ c : Bool, ∫ p : M.X × (M.Y × M.Z),
            respMass (M.f (p.1, p.2.2)) false * respMass (M.g (p.1, p.2.1)) b
              * respMass (M.h (p.2.2, p.2.1)) c ∂ν := rfl
      _ = ∫ p : M.X × (M.Y × M.Z), (∑ b : Bool, ∑ c : Bool,
            respMass (M.f (p.1, p.2.2)) false * respMass (M.g (p.1, p.2.1)) b
              * respMass (M.h (p.2.2, p.2.1)) c) ∂ν :=
          integral_sum_bool₂ _ fun b c => hInt false b c
      _ = ∫ p : M.X × (M.Y × M.Z), M.f (p.1, p.2.2) ∂ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only [Fintype.sum_bool, respMassM_false, respMassM_true]
          ring
  have hmB : margB M.law = ∫ q : M.X × M.Y, M.g q ∂(M.μX.prod M.μY) := by
    rw [← law_margB (Z := M.Z) M.μX M.μY M.μZ hgm hg]
    calc margB M.law
        = ∑ b : Bool, ∑ c : Bool, ∫ p : M.X × (M.Y × M.Z),
            respMass (M.f (p.1, p.2.2)) b * respMass (M.g (p.1, p.2.1)) false
              * respMass (M.h (p.2.2, p.2.1)) c ∂ν := rfl
      _ = ∫ p : M.X × (M.Y × M.Z), (∑ b : Bool, ∑ c : Bool,
            respMass (M.f (p.1, p.2.2)) b * respMass (M.g (p.1, p.2.1)) false
              * respMass (M.h (p.2.2, p.2.1)) c) ∂ν :=
          integral_sum_bool₂ _ fun b c => hInt b false c
      _ = ∫ p : M.X × (M.Y × M.Z), M.g (p.1, p.2.1) ∂ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only [Fintype.sum_bool, respMassM_false, respMassM_true]
          ring
  have hmC : margC M.law = ∫ q : M.Z × M.Y, M.h q ∂(M.μZ.prod M.μY) := by
    rw [← law_margC (X := M.X) M.μX M.μY M.μZ hhm hh]
    calc margC M.law
        = ∑ b : Bool, ∑ c : Bool, ∫ p : M.X × (M.Y × M.Z),
            respMass (M.f (p.1, p.2.2)) b * respMass (M.g (p.1, p.2.1)) c
              * respMass (M.h (p.2.2, p.2.1)) false ∂ν := rfl
      _ = ∫ p : M.X × (M.Y × M.Z), (∑ b : Bool, ∑ c : Bool,
            respMass (M.f (p.1, p.2.2)) b * respMass (M.g (p.1, p.2.1)) c
              * respMass (M.h (p.2.2, p.2.1)) false) ∂ν :=
          integral_sum_bool₂ _ fun b c => hInt b c false
      _ = ∫ p : M.X × (M.Y × M.Z), M.h (p.2.2, p.2.1) ∂ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only [Fintype.sum_bool, respMassM_false, respMassM_true]
          ring
  rw [hatom, hmA, hmB, hmC]
  exact finner_coreM M.μX M.μY M.μZ hfm hgm hhm hf hg hh

/-! ## Finite models are measure-theoretic models -/

/-- A law on a finite type, read as a `PMF`. -/
private def lawPMF {α : Type} [Fintype α] {w : α → ℝ} (hw : IsLaw w) : PMF α :=
  ⟨fun a => ENNReal.ofReal (w a), by
    have hs : ∑ a, ENNReal.ofReal (w a) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => hw.1 a, hw.2, ENNReal.ofReal_one]
    exact hs ▸ hasSum_fintype fun a => ENNReal.ofReal (w a)⟩

/-- The mass that the associated measure gives to a point is the original weight. -/
private lemma lawPMF_real {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {w : α → ℝ} (hw : IsLaw w) (a : α) :
    (lawPMF hw).toMeasure.real {a} = w a := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  exact ENNReal.toReal_ofReal (hw.1 a)

/-- A finite-latent triangle model is a measure-theoretic triangle model: put the counting
measure weighted by the source law on each latent alphabet, with all sets measurable. -/
theorem triangleCompatibleM_of_triangleCompatible {P : ThreeBit → ℝ}
    (hP : TriangleCompatible P) : TriangleCompatibleM P := by
  obtain ⟨M, ⟨hX, hY, hZ, hf, hg, hh⟩, rfl⟩ := hP
  let _ : MeasurableSpace M.X := ⊤
  let _ : MeasurableSpace M.Y := ⊤
  let _ : MeasurableSpace M.Z := ⊤
  have : DiscreteMeasurableSpace M.X := ⟨fun _ => trivial⟩
  have : DiscreteMeasurableSpace M.Y := ⟨fun _ => trivial⟩
  have : DiscreteMeasurableSpace M.Z := ⟨fun _ => trivial⟩
  refine ⟨{ X := M.X, Y := M.Y, Z := M.Z
            μX := (lawPMF hX).toMeasure
            μY := (lawPMF hY).toMeasure
            μZ := (lawPMF hZ).toMeasure
            f := M.f, g := M.g, h := M.h },
    ⟨Measurable.of_discrete, Measurable.of_discrete, Measurable.of_discrete, hf, hg, hh⟩, ?_⟩
  funext w
  simp only [TriangleModelM.law, TriangleModel.law]
  rw [integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  rw [← Set.singleton_prod_singleton, measureReal_prod_prod, ← Set.singleton_prod_singleton,
    measureReal_prod_prod, lawPMF_real, lawPMF_real, lawPMF_real, smul_eq_mul]
  ring

/-! ## The incompatibility theorems without the finite-latent boundary

Each statement below is the arbitrary-latent form of the finite-latent statement of the same
name in `Finner.lean`, `Main.lean` and `Exponent.lean`. The finite computations are reused
verbatim: they are statements about the three-bit law alone and mention no model. -/

/-- Paper Lemma 5.8 (`lem:violation`), arbitrary latent alphabets. -/
theorem witness_not_compatibleM (t : ℕ) (ht : 1 ≤ t) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1 / (t : ℝ) ^ 3) : ¬ TriangleCompatibleM (Q ε ((1 - ε) ^ (t - 1))) := fun hc =>
  absurd (finner_of_compatibleM hc) (not_le.2 (witness_violation t ht h0 h1))

/-- Paper Proposition 5.12 (`prop:Rp`), incompatibility half, arbitrary latent alphabets. -/
theorem Rlaw_not_compatibleM {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    ¬ TriangleCompatibleM (Rlaw p) := by
  intro hc
  have hfin := finner_of_compatibleM hc
  have ha : atom000 (Rlaw p) = p := by simp [atom000, Rlaw]
  have hA : margA (Rlaw p) = p := by simp [margA, Rlaw]
  have hB : margB (Rlaw p) = p := by simp [margB, Rlaw]
  have hC : margC (Rlaw p) = p := by simp [margC, Rlaw]
  rw [ha, hA, hB, hC] at hfin
  nlinarith [hfin, mul_pos (mul_pos h0 h0) (sub_pos.2 h1)]

/-- The real cube root of `ε`, with `u³ = ε` and `σ = u²/2`. -/
private lemma exists_cube_rootM {ε : ℝ} (h0 : 0 < ε) :
    ∃ u : ℝ, 0 < u ∧ u ^ 3 = ε ∧ sigmaEps ε = u ^ 2 / 2 := by
  refine ⟨ε ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos h0 _, ?_, ?_⟩
  · rw [← Real.rpow_natCast (ε ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul h0.le]
    norm_num
  · simp only [sigmaEps]
    rw [← Real.rpow_natCast (ε ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul h0.le]
    norm_num

/-- Paper Proposition 5.13 (`prop:family`), part (c), arbitrary latent alphabets. -/
theorem Peps_not_compatibleM {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 8) :
    ¬ TriangleCompatibleM (Peps ε) := by
  intro hc
  have hε1 : ε < 1 := by linarith
  have hfin := finner_of_compatibleM hc
  obtain ⟨hA, hB, hC⟩ := mEps_eq_marg (ε := ε)
  rw [zEps_eq_atom (ε := ε), hA, hB, hC] at hfin
  obtain ⟨u, hu0, hu3, hσ⟩ := exists_cube_rootM h0
  have hu2 : u < 1 / 2 := by nlinarith [hu3, h1, hu0, sq_nonneg u, mul_pos hu0 hu0]
  have hu2pos : (0 : ℝ) < u ^ 2 := pow_pos hu0 2
  have hu3pos : (0 : ℝ) < u ^ 3 := pow_pos hu0 3
  have hu3le : u ^ 3 ≤ 1 / 8 := by rw [hu3]; linarith
  have hm : mEps ε = u ^ 3 + (1 - u ^ 3) * (u ^ 2 / 2) := by
    simp only [mEps, hσ]; rw [hu3]
  have hzz : zEps ε = u ^ 3 + (1 - u ^ 3) * (u ^ 2 / 2) ^ 3 := by
    simp only [zEps, hσ]; rw [hu3]
  have hm0 : 0 < mEps ε := by
    rw [hm]
    nlinarith [mul_pos (show (0 : ℝ) < 1 - u ^ 3 by linarith) hu2pos]
  have hmub : mEps ε ≤ u ^ 3 + u ^ 2 / 2 := by
    rw [hm]
    nlinarith [mul_nonneg hu3pos.le hu2pos.le]
  have hlt1 : u ^ 3 + u ^ 2 / 2 < u ^ 2 := by
    nlinarith [mul_pos hu2pos (show (0 : ℝ) < 1 / 2 - u by linarith)]
  have hm3 : mEps ε ^ 3 < u ^ 6 :=
    calc mEps ε ^ 3 ≤ (u ^ 3 + u ^ 2 / 2) ^ 3 := pow_le_pow_left₀ hm0.le hmub 3
      _ < (u ^ 2) ^ 3 := pow_lt_pow_left₀ hlt1 (by positivity) (show (3 : ℕ) ≠ 0 by norm_num)
      _ = u ^ 6 := by ring
  have hzlb : u ^ 3 ≤ zEps ε := by
    rw [hzz]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - u ^ 3 by linarith)
      (show (0 : ℝ) ≤ (u ^ 2 / 2) ^ 3 by positivity)]
  have hz2 : u ^ 6 ≤ zEps ε ^ 2 :=
    calc u ^ 6 = (u ^ 3) ^ 2 := by ring
      _ ≤ zEps ε ^ 2 := pow_le_pow_left₀ hu3pos.le hzlb 2
  nlinarith [hfin, hm3, hz2]

/-- Paper Theorem 5.2 (`thm:main`), violation half, arbitrary latent alphabets. -/
theorem main_violationM (t : ℕ) (ht : 1 ≤ t) :
    epsFam t ^ 2 / 2
        ≤ atom000 (Pfam t) ^ 2 - margA (Pfam t) * margB (Pfam t) * margC (Pfam t)
      ∧ ¬ TriangleCompatibleM (Pfam t) := by
  refine ⟨witness_margin t ht, fun hc => ?_⟩
  have hfin := finner_of_compatibleM hc
  have hm := witness_margin t ht
  have h0 := (epsFam_mem t ht).1
  nlinarith [hfin, hm, mul_pos h0 h0]

/-- Paper Theorem 5.2 (`thm:main`), the nontermination corollary with arbitrary latent
alphabets: for every finite order `t` there is a three-bit law that passes the order-`t`
test and is not triangle compatible for **any** latent probability spaces. -/
theorem no_finite_characterizing_orderM (t : ℕ) (ht : 1 ≤ t) :
    ∃ P : ThreeBit → ℝ, IsLaw P ∧ AIFeasible t P ∧ NWFeasible t P ∧ ¬ TriangleCompatibleM P :=
  ⟨Pfam t, Pfam_isLaw t ht, (main_membership t ht).1, (main_membership t ht).2,
    (main_violationM t ht).2⟩

end

end TriangleInflation
