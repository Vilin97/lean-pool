/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.Rigidity

/-!
# Canonical spectral decomposition

Gelfand--Tsetlin completeness, Pieri channels, and projected-axis sufficiency.
-/

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

section


namespace HigherYoungAllRankInvariantPositiveRootKernel

open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem exists_jointRootKernel_mem_of_vector_wordKills
    {K V I : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    (E : I → V →ₗ[K] V) (W : Submodule K V)
    (hinvariant : ∀ i : I, ∀ v : V, v ∈ W → E i v ∈ W)
    (N : ℕ) (v : V) (hv : v ∈ W) (hvzero : v ≠ 0)
    (hwords : ∀ word : List I, word.length = N →
      rootOperatorWord E word v = 0) :
    ∃ w : V, w ∈ W ∧ w ≠ 0 ∧ ∀ i : I, E i w = 0 := by
  classical
  induction N generalizing v with
  | zero =>
      exact False.elim (hvzero (by simpa only [rootOperatorWord_nil, LinearMap.id_coe,
                                     id_eq] using hwords [] rfl))
  | succ N ih =>
      by_cases hkill : ∀ i : I, E i v = 0
      · exact ⟨v, hv, hvzero, hkill⟩
      · push Not at hkill
        obtain ⟨i, hi⟩ := hkill
        apply ih (E i v) (hinvariant i v hv) hi
        intro word hlength
        have hfull : (i :: word).length = N + 1 := by
          simp only [List.length_cons, hlength]
        simpa only [rootOperatorWord_cons_apply] using
          hwords (i :: word) hfull

theorem exists_jointRootKernel_mem_of_wordKills
    {K V I : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    (E : I → V →ₗ[K] V) (W : Submodule K V)
    (hW : W ≠ ⊥)
    (hinvariant : ∀ i : I, ∀ v : V, v ∈ W → E i v ∈ W)
    (N : ℕ)
    (hwords : ∀ (v : V), v ∈ W → ∀ word : List I,
      word.length = N → rootOperatorWord E word v = 0) :
    ∃ v : V, v ∈ W ∧ v ≠ 0 ∧ ∀ i : I, E i v = 0 := by
  obtain ⟨v, hv, hvzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  exact exists_jointRootKernel_mem_of_vector_wordKills
    E W hinvariant N v hv hvzero (hwords v hv)

end HigherYoungAllRankInvariantPositiveRootKernel

end

section


open scoped BigOperators

namespace HigherYoungFullComplexSpanHomogeneous

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem polynomialComplexSpan_le_homogeneousSubmodule
    {r n d : ℕ}
    (W : Submodule ℝ (PolynomialSpace r n))
    (hW : ∀ p ∈ W, p.IsHomogeneous d) :
    polynomialComplexSpan W ≤
      MvPolynomial.homogeneousSubmodule
        (Fin ((r + 1) * n)) ℂ d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, hp, rfl⟩
  exact (hW p hp).map Complex.ofRealHom

theorem fullYoungComplexPolynomialSpan_isHomogeneous
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    {z : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hz : z ∈ fullYoungComplexPolynomialSpan (n := n) lam) :
    z.IsHomogeneous (∑ i, lam i) := by
  exact polynomialComplexSpan_le_homogeneousSubmodule
    (harmonicYoungSubmodule lam)
    (fun p hp => ((mem_harmonicYoungSubmodule lam p).mp hp).1) hz

end HigherYoungFullComplexSpanHomogeneous

namespace HigherYoungRotationInvariantComplexRootStability

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel

theorem orthogonalPositiveRootDerivation_youngComplexPolynomialSpan_mem
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam))
    (hW : IsRotationInvariant (youngRotationFamily lam) W)
    (α : OrthogonalPositiveRoot r n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hf : f ∈ youngComplexPolynomialSpan lam W) :
    orthogonalPositiveRootDerivation h α f ∈
      youngComplexPolynomialSpan lam W := by
  cases α with
  | difference p q hpq =>
      exact ambientPositiveRoot_youngComplexPolynomialSpan_mem
        h lam W hW p q f hf
  | sum p q hpq =>
      exact ambientSumPositiveRoot_youngComplexPolynomialSpan_mem
        h lam W hW p q f hf
  | short p t ht =>
      exact ambientShortPositiveRoot_youngComplexPolynomialSpan_mem
        h lam W hW p t f hf

private def orthogonalPositiveRootLinearFamily
    {r n : ℕ} (h : 2 * (r + 1) ≤ n) :
    OrthogonalPositiveRoot r n →
      MvPolynomial (Fin ((r + 1) * n)) ℂ →ₗ[ℂ]
        MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  fun α => (orthogonalPositiveRootDerivation h α).toLinearMap

end HigherYoungRotationInvariantComplexRootStability

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungAllRankStabilizerHighestCyclicity

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.IsotropicAmbientHighestLine
open MetricCodes.Spherical.HigherYoungAllRankInvariantPositiveRootKernel
open MetricCodes.Spherical.HigherYoungAllRankIsotropicHighestMultiplicityOne
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungFullComplexSpanHomogeneous
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungRotationInvariantComplexRootStability
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem allRankRotationIrreducible_of_complexJointRootLine
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) {J : Type*}
    (E : J →
      MvPolynomial (Fin ((r + 1) * n)) ℂ →ₗ[ℂ]
        MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (L : Submodule ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ))
    (hline : Module.finrank ℂ L = 1)
    (N : ℕ)
    (hnil : ∀ z ∈ fullYoungComplexPolynomialSpan (n := n) lam,
      ∀ word : List J, word.length = N → rootOperatorWord E word z = 0)
    (hroot : ∀ W : Submodule ℝ (HarmonicYoungSpace (n := n) lam),
      IsRotationInvariant (youngRotationFamily lam) W →
      ∀ (j : J) (z : MvPolynomial (Fin ((r + 1) * n)) ℂ),
        z ∈ youngComplexPolynomialSpan lam W →
          E j z ∈ youngComplexPolynomialSpan lam W)
    (hhighest : ∀ z ∈ fullYoungComplexPolynomialSpan (n := n) lam,
      (∀ j : J, E j z = 0) → z ∈ L)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam))
    (hW : IsRotationInvariant (youngRotationFamily lam) W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  by_contra htop
  have hperp : Wᗮ ≠ ⊥ := by
    intro hzero
    exact htop (Submodule.orthogonal_eq_bot_iff.mp hzero)
  have hperpInvariant :
      IsRotationInvariant (youngRotationFamily lam) Wᗮ :=
    rotationInvariant_orthogonal (youngRotationFamily lam)
      (youngRotationFamily_inner lam) W hW
  have hcomplexW : youngComplexPolynomialSpan lam W ≠ ⊥ :=
    youngComplexPolynomialSpan_ne_bot_of_ne_bot lam W hbot
  have hcomplexPerp : youngComplexPolynomialSpan lam Wᗮ ≠ ⊥ :=
    youngComplexPolynomialSpan_ne_bot_of_ne_bot lam Wᗮ hperp
  obtain ⟨u, hu, hu0, huroot⟩ :=
    exists_jointRootKernel_mem_of_wordKills E
      (youngComplexPolynomialSpan lam W) hcomplexW (hroot W hW) N (by
        intro z hz word hlength
        exact hnil z (youngComplexPolynomialSpan_le_full lam W hz)
          word hlength)
  obtain ⟨u', hu', hu'0, hu'root⟩ :=
    exists_jointRootKernel_mem_of_wordKills E
      (youngComplexPolynomialSpan lam Wᗮ) hcomplexPerp
      (hroot Wᗮ hperpInvariant) N (by
        intro z hz word hlength
        exact hnil z (youngComplexPolynomialSpan_le_full lam Wᗮ hz)
          word hlength)
  have huL : u ∈ L :=
    hhighest u (youngComplexPolynomialSpan_le_full lam W hu) huroot
  have hu'L : u' ∈ L :=
    hhighest u' (youngComplexPolynomialSpan_le_full lam Wᗮ hu') hu'root
  have hspan : L = Submodule.span ℂ {u} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hline huL hu0
  have hu'span : u' ∈ Submodule.span ℂ {u} := hspan ▸ hu'L
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu'span
  have hu'inW : u' ∈ youngComplexPolynomialSpan lam W := by
    rw [← hc]
    exact (youngComplexPolynomialSpan lam W).smul_mem c hu
  have hintersection :
      u' ∈ youngComplexPolynomialSpan lam W ⊓
        youngComplexPolynomialSpan lam Wᗮ :=
    Submodule.mem_inf.mpr ⟨hu'inW, hu'⟩
  rw [youngComplexPolynomialSpan_inf_orthogonal_eq_bot] at hintersection
  exact hu'0 (by simpa only [Submodule.mem_bot] using hintersection)

theorem rootOperatorWord_append_singleton_apply
    {K V I : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    (R : I → V →ₗ[K] V) (word : List I) (i : I) (v : V) :
    rootOperatorWord R (word ++ [i]) v = R i (rootOperatorWord R word v) := by
  induction word generalizing v with
  | nil => rfl
  | cons j word ih => exact ih (R j v)

theorem operatorWordSpan_rotationInvariant
    {V I : Type*} [AddCommGroup V] [Module ℝ V]
    (R : I → V →ₗ[ℝ] V) (v : V) :
    IsRotationInvariant R (operatorWordSpan R v) := by
  intro i p hp
  change p ∈ Submodule.span ℝ
    (Set.range (fun word : List I => rootOperatorWord R word v)) at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨word, rfl⟩ := hp
      apply Submodule.subset_span
      refine ⟨word ++ [i], ?_⟩
      exact rootOperatorWord_append_singleton_apply R word i v
  | zero => simp only [map_zero, zero_mem]
  | add p q _ _ hp hq => simpa only [map_add] using (operatorWordSpan R v).add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using (operatorWordSpan R v).smul_mem c hp

theorem dominantHighestRotationWordSpan_rotationInvariant
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    IsRotationInvariant (youngRotationFamily lam)
      (dominantHighestRotationWordSpan hn lam hdom) := by
  intro i p hp
  change p ∈ operatorWordSpan (youngRotationFamily lam)
      (dominantHighestRealVector hn lam hdom) ⊔
    operatorWordSpan (youngRotationFamily lam)
      (dominantHighestImaginaryVector hn lam hdom) at hp
  change youngRotationFamily lam i p ∈
    operatorWordSpan (youngRotationFamily lam)
      (dominantHighestRealVector hn lam hdom) ⊔
    operatorWordSpan (youngRotationFamily lam)
      (dominantHighestImaginaryVector hn lam hdom)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hp
  rw [← huv, map_add]
  apply (operatorWordSpan (youngRotationFamily lam)
      (dominantHighestRealVector hn lam hdom) ⊔
    operatorWordSpan (youngRotationFamily lam)
      (dominantHighestImaginaryVector hn lam hdom)).add_mem
  · exact (show operatorWordSpan (youngRotationFamily lam)
        (dominantHighestRealVector hn lam hdom) ≤
      operatorWordSpan (youngRotationFamily lam)
        (dominantHighestRealVector hn lam hdom) ⊔
      operatorWordSpan (youngRotationFamily lam)
        (dominantHighestImaginaryVector hn lam hdom) from le_sup_left)
      (operatorWordSpan_rotationInvariant (youngRotationFamily lam)
        (dominantHighestRealVector hn lam hdom) i u hu)
  · exact (show operatorWordSpan (youngRotationFamily lam)
        (dominantHighestImaginaryVector hn lam hdom) ≤
      operatorWordSpan (youngRotationFamily lam)
        (dominantHighestRealVector hn lam hdom) ⊔
      operatorWordSpan (youngRotationFamily lam)
        (dominantHighestImaginaryVector hn lam hdom) from le_sup_right)
      (operatorWordSpan_rotationInvariant (youngRotationFamily lam)
        (dominantHighestImaginaryVector hn lam hdom) i v hv)

theorem dominantHighestRotationWordSpan_ne_bot
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    dominantHighestRotationWordSpan hn lam hdom ≠ ⊥ := by
  intro hbot
  rcases dominantHighestRealVector_ne_zero_or_imaginary_ne_zero
    hn lam hdom with hreal | himag
  · apply hreal
    have hmem : dominantHighestRealVector hn lam hdom ∈
        dominantHighestRotationWordSpan hn lam hdom := by
      change dominantHighestRealVector hn lam hdom ∈
        operatorWordSpan (youngRotationFamily lam)
          (dominantHighestRealVector hn lam hdom) ⊔
        operatorWordSpan (youngRotationFamily lam)
          (dominantHighestImaginaryVector hn lam hdom)
      exact (show operatorWordSpan (youngRotationFamily lam)
          (dominantHighestRealVector hn lam hdom) ≤
        operatorWordSpan (youngRotationFamily lam)
          (dominantHighestRealVector hn lam hdom) ⊔
        operatorWordSpan (youngRotationFamily lam)
          (dominantHighestImaginaryVector hn lam hdom) from le_sup_left)
        (Submodule.subset_span ⟨[], rfl⟩)
    rw [hbot] at hmem
    simpa only [Submodule.mem_bot] using hmem
  · apply himag
    have hmem : dominantHighestImaginaryVector hn lam hdom ∈
        dominantHighestRotationWordSpan hn lam hdom := by
      change dominantHighestImaginaryVector hn lam hdom ∈
        operatorWordSpan (youngRotationFamily lam)
          (dominantHighestRealVector hn lam hdom) ⊔
        operatorWordSpan (youngRotationFamily lam)
          (dominantHighestImaginaryVector hn lam hdom)
      exact (show operatorWordSpan (youngRotationFamily lam)
          (dominantHighestImaginaryVector hn lam hdom) ≤
        operatorWordSpan (youngRotationFamily lam)
          (dominantHighestRealVector hn lam hdom) ⊔
        operatorWordSpan (youngRotationFamily lam)
          (dominantHighestImaginaryVector hn lam hdom) from le_sup_right)
        (Submodule.subset_span ⟨[], rfl⟩)
    rw [hbot] at hmem
    simpa only [Submodule.mem_bot] using hmem

theorem allRankRotationIrreducible_of_orthogonalPositiveRootRigidity
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (N : ℕ)
    (hnil : ∀ z ∈ fullYoungComplexPolynomialSpan (n := n) lam,
      ∀ word : List (OrthogonalPositiveRoot r n), word.length = N →
        rootOperatorWord (orthogonalPositiveRootLinearFamily hn) word z = 0)
    (hhighest : ∀ z ∈ fullYoungComplexPolynomialSpan (n := n) lam,
      (∀ α : OrthogonalPositiveRoot r n,
        orthogonalPositiveRootDerivation hn α z = 0) →
      z ∈ ambientIsotropicHighestSubmodule hn lam)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam))
    (hW : IsRotationInvariant (youngRotationFamily lam) W) :
    W = ⊥ ∨ W = ⊤ := by
  apply allRankRotationIrreducible_of_complexJointRootLine lam
    (orthogonalPositiveRootLinearFamily hn)
    (ambientIsotropicHighestSubmodule hn lam)
    (finrank_ambientIsotropicHighestSubmodule hn lam hdom) N hnil
    (fun U hU α z hz =>
      orthogonalPositiveRootDerivation_youngComplexPolynomialSpan_mem
        hn lam U hU α z hz)
    (fun z hz hroots => hhighest z hz hroots)
    W hW

theorem dominantHighestRotationWordSpan_eq_top_of_orthogonalPositiveRootRigidity
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (N : ℕ)
    (hnil : ∀ z ∈ fullYoungComplexPolynomialSpan (n := n) lam,
      ∀ word : List (OrthogonalPositiveRoot r n), word.length = N →
        rootOperatorWord (orthogonalPositiveRootLinearFamily hn) word z = 0)
    (hhighest : ∀ z ∈ fullYoungComplexPolynomialSpan (n := n) lam,
      (∀ α : OrthogonalPositiveRoot r n,
        orthogonalPositiveRootDerivation hn α z = 0) →
      z ∈ ambientIsotropicHighestSubmodule hn lam) :
    dominantHighestRotationWordSpan hn lam hdom = ⊤ := by
  apply (allRankRotationIrreducible_of_orthogonalPositiveRootRigidity
    hn lam hdom N hnil hhighest
    (dominantHighestRotationWordSpan hn lam hdom)
    (dominantHighestRotationWordSpan_rotationInvariant hn lam hdom)).resolve_left
  exact dominantHighestRotationWordSpan_ne_bot hn lam hdom

theorem orthogonalPositiveRootWord_eq_zero_of_mem_fullYoungComplexPolynomialSpan
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {z : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hz : z ∈ fullYoungComplexPolynomialSpan (n := n) lam)
    (word : List (OrthogonalPositiveRoot r n))
    (hlength : (∑ i, lam i) * (2 * (r + 1)) < word.length) :
    rootOperatorWord (orthogonalPositiveRootLinearFamily hn) word z = 0 := by
  exact orthogonalPositiveRootWord_eq_zero_of_isHomogeneous hn
    (fullYoungComplexPolynomialSpan_isHomogeneous lam hz) word hlength

theorem orthogonalPositiveRootWord_eq_zero_of_fullYoung_uniform
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {z : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hz : z ∈ fullYoungComplexPolynomialSpan (n := n) lam)
    (word : List (OrthogonalPositiveRoot r n))
    (hlength : word.length = (∑ i, lam i) * (2 * (r + 1)) + 1) :
    rootOperatorWord (orthogonalPositiveRootLinearFamily hn) word z = 0 := by
  apply orthogonalPositiveRootWord_eq_zero_of_mem_fullYoungComplexPolynomialSpan
    hn lam hz word
  omega

theorem allRankRotationIrreducible_of_orthogonalPositiveRootHighestRigidity
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (hhighest : ∀ z ∈ fullYoungComplexPolynomialSpan (n := n) lam,
      (∀ α : OrthogonalPositiveRoot r n,
        orthogonalPositiveRootDerivation hn α z = 0) →
      z ∈ ambientIsotropicHighestSubmodule hn lam)
    (W : Submodule ℝ (HarmonicYoungSpace (n := n) lam))
    (hW : IsRotationInvariant (youngRotationFamily lam) W) :
    W = ⊥ ∨ W = ⊤ := by
  exact allRankRotationIrreducible_of_orthogonalPositiveRootRigidity
    hn lam hdom ((∑ i, lam i) * (2 * (r + 1)) + 1)
    (fun z hz word hlength =>
      orthogonalPositiveRootWord_eq_zero_of_fullYoung_uniform
        hn lam hz word hlength)
    hhighest W hW

theorem dominantHighestRotationWordSpan_eq_top_of_orthogonalPositiveRootHighestRigidity
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (hhighest : ∀ z ∈ fullYoungComplexPolynomialSpan (n := n) lam,
      (∀ α : OrthogonalPositiveRoot r n,
        orthogonalPositiveRootDerivation hn α z = 0) →
      z ∈ ambientIsotropicHighestSubmodule hn lam) :
    dominantHighestRotationWordSpan hn lam hdom = ⊤ := by
  exact dominantHighestRotationWordSpan_eq_top_of_orthogonalPositiveRootRigidity
    hn lam hdom ((∑ i, lam i) * (2 * (r + 1)) + 1)
    (fun z hz word hlength =>
      orthogonalPositiveRootWord_eq_zero_of_fullYoung_uniform
        hn lam hz word hlength)
    hhighest

end HigherYoungAllRankStabilizerHighestCyclicity

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankCanonicalEdgeRaisingGram

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankFischerGramWeylRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowRaiseLowerTensorTrace
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowRaiseTensorGram
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherYoungAllRankActualHighestKernelRigidity
open MetricCodes.Spherical.HigherYoungAllRankStabilizerHighestCyclicity
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem finiteInterlacing_two_mul_row_count_le
    {r n : ℕ} {low : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n low mu) : 2 * (r + 1) ≤ n := by
  have hstable := h.1
  omega

theorem canonicalEdge_loweredInternalYoungWeight_raiseWeight
    {r : ℕ} (low : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    loweredInternalYoungWeight (raiseWeight low row) row = low := by
  funext j
  by_cases hj : j = row
  · subst j
    simp only [loweredInternalYoungWeight, raiseWeight, Function.update_self, add_tsub_cancel_right]
  · simp only [loweredInternalYoungWeight, raiseWeight, Function.update_self, add_tsub_cancel_right,
      ne_eq, hj, not_false_eq_true, Function.update_of_ne]

theorem canonicalEdge_raiseWeight_strictly_removable
    {r : ℕ} (low : Fin (r + 1) → ℕ) (hdom : Antitone low)
    (row j : Fin (r + 1)) (hj : j.val = row.val + 1) :
    raiseWeight low row j < raiseWeight low row row := by
  have hne : j ≠ row := by
    intro heq
    subst j
    omega
  have hle : low j ≤ low row := by
    apply hdom
    change row.val ≤ j.val
    omega
  simpa only [raiseWeight, ne_eq, hne, not_false_eq_true, Function.update_of_ne,
    Function.update_self, Order.lt_add_one_iff, ge_iff_le,
    Nat.succ_eq_add_one] using Nat.lt_succ_of_le hle

private theorem canonicalEdgeRaise_inner_of_cyclic_and_loweredSignature_metriccodes2_fa003c49
    {r n : ℕ} (high low : Fin (r + 1) → ℕ)
    (row : Fin (r + 1))
    (hlowered : low = loweredInternalYoungWeight high row)
    (ha : 0 < high row)
    (hn : 2 * (r + 1) ≤ n)
    (hdomhigh : Antitone high)
    (hdomlow : Antitone low)
    (hcyclic : dominantHighestRotationWordSpan hn low hdomlow = ⊤)
    (hdeg : (∑ j, high j) = (∑ j, low j) + 1)
    (p q : HarmonicYoungSpace (n := n) low) :
    ⟪youngClebschRaise high low hdeg row p,
      youngClebschRaise high low hdeg row q⟫_ℝ =
      arbitraryRowRaiseTensorGramScalar (n := n) high row * ⟪p, q⟫_ℝ := by
  subst low
  exact youngClebschRaise_arbitrary_inner_of_cyclic
    high row ha hn hdomhigh hdomlow hcyclic p q

theorem canonicalEdgeRaisingGram_of_cyclic
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (mu : Fin r → ℕ)
    (row : Fin (r + 1))
    (h : FiniteInterlacing n low mu)
    (hraise : FiniteInterlacing n (raiseWeight low row) mu)
    (hcyclic : dominantHighestRotationWordSpan
      (finiteInterlacing_two_mul_row_count_le h)
      low h.antitone_ambient = ⊤) :
    ∃ raisingGram : ℝ, 0 < raisingGram ∧
      (∀ p q : HarmonicYoungSpace (n := n) low,
        ⟪youngClebschRaise (raiseWeight low row) low
            (sum_raiseWeight low row) row p,
          youngClebschRaise (raiseWeight low row) low
            (sum_raiseWeight low row) row q⟫_ℝ =
          raisingGram * ⟪p, q⟫_ℝ) ∧
      raisingGram = internalRowLowerGramScalar (raiseWeight low row) row *
        weylEdgeRatio n low row := by
  let high : Fin (r + 1) → ℕ := raiseWeight low row
  have hn : 2 * (r + 1) ≤ n :=
    finiteInterlacing_two_mul_row_count_le h
  have ha : 0 < high row := by
    simp only [raiseWeight, Function.update_self, lt_add_iff_pos_left, Order.lt_add_one_iff,
      zero_le, high]
  have hdomlow : Antitone low := h.antitone_ambient
  have hdomhigh : Antitone high := by
    simpa only [high] using hraise.antitone_ambient
  have hdomlower : Antitone (loweredInternalYoungWeight high row) := by
    simpa only [high, canonicalEdge_loweredInternalYoungWeight_raiseWeight]
      using hdomlow
  have hstrict : ∀ j : Fin (r + 1),
      j.val = row.val + 1 → high j < high row := by
    intro j hj
    exact canonicalEdge_raiseWeight_strictly_removable low hdomlow row j hj
  have hlowered : low = loweredInternalYoungWeight high row := by
    symm
    simpa only using canonicalEdge_loweredInternalYoungWeight_raiseWeight low row
  refine ⟨arbitraryRowRaiseTensorGramScalar (n := n) high row, ?_, ?_, ?_⟩
  · exact arbitraryRowRaiseTensorGram_pos high row hn ha
      hdomhigh hdomlower hstrict
  · intro p q
    exact canonicalEdgeRaise_inner_of_cyclic_and_loweredSignature_metriccodes2_fa003c49
      high low row hlowered ha hn hdomhigh hdomlow hcyclic
      (sum_raiseWeight low row) p q
  · simpa only [high] using
      arbitraryRowRaiseTensorGramScalar_eq_lowerGram_mul_weylEdgeRatio
        low mu row h hraise

theorem canonicalEdgeRaisingGram
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (mu : Fin r → ℕ)
    (row : Fin (r + 1))
    (h : FiniteInterlacing n low mu)
    (hraise : FiniteInterlacing n (raiseWeight low row) mu) :
    ∃ raisingGram : ℝ, 0 < raisingGram ∧
      (∀ p q : HarmonicYoungSpace (n := n) low,
        ⟪youngClebschRaise (raiseWeight low row) low
            (sum_raiseWeight low row) row p,
          youngClebschRaise (raiseWeight low row) low
            (sum_raiseWeight low row) row q⟫_ℝ =
          raisingGram * ⟪p, q⟫_ℝ) ∧
      raisingGram = internalRowLowerGramScalar (raiseWeight low row) row *
        weylEdgeRatio n low row := by
  have hstable : 2 * r + 4 ≤ n := h.1
  apply canonicalEdgeRaisingGram_of_cyclic low mu row h hraise
  apply dominantHighestRotationWordSpan_eq_top_of_orthogonalPositiveRootHighestRigidity
    (finiteInterlacing_two_mul_row_count_le h) low h.antitone_ambient
  intro z hz hroots
  exact mem_ambientIsotropicHighestSubmodule_of_positiveRootKernel
    (finiteInterlacing_two_mul_row_count_le h) (by omega) low hz hroots

end AllRankCanonicalEdgeRaisingGram

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGelfandTsetlinCanonicalFibre

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.IsotropicAmbientHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualHighestKernelRigidity
open MetricCodes.Spherical.HigherYoungAllRankStabilizerHighestCyclicity
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem positiveGelfandTsetlinFischerGram_of_positiveRootHighestRigidity
    {r n : ℕ} (hn : 2 * (r + 1) < n)
    (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hhighest : ∀ z ∈ fullYoungComplexPolynomialSpan (n := n) mu,
      (∀ α : OrthogonalPositiveRoot r n,
        orthogonalPositiveRootDerivation (Nat.le_of_lt hn) α z = 0) →
      z ∈ ambientIsotropicHighestSubmodule (Nat.le_of_lt hn) mu) :
    PositiveGelfandTsetlinFischerGram (n := n) lam mu h := by
  apply positiveGelfandTsetlinFischerGram_of_irreducible hn lam mu h
  intro W hW
  exact allRankRotationIrreducible_of_orthogonalPositiveRootHighestRigidity
    (Nat.le_of_lt hn) mu (interlaces_antitone_stabilizer h)
    hhighest W hW

theorem positiveGelfandTsetlinFischerGram
    {r n : ℕ} (hn : 2 * (r + 1) + 2 ≤ n)
    (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu) :
    PositiveGelfandTsetlinFischerGram (n := n) lam mu h := by
  have hstrict : 2 * (r + 1) < n := by omega
  apply positiveGelfandTsetlinFischerGram_of_positiveRootHighestRigidity
    hstrict lam mu h
  intro z hz hroots
  exact mem_ambientIsotropicHighestSubmodule_of_positiveRootKernel
    (Nat.le_of_lt hstrict) hn mu hz hroots

theorem canonicalBoxPositiveFischerGram
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (i : BoxIndex (r + 1) m) :
    PositiveGelfandTsetlinFischerGram (n := n - 1)
      (boxSignature (m := m) a n i)
      (Weyl.flooredWeight b n)
      (boxSignature_interlaces a b hstable i) := by
  apply positiveGelfandTsetlinFischerGram
  have hn := box_stableRange a b hstable
  omega

end AllRankGelfandTsetlinCanonicalFibre

end

end HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungAllRankActualProjectedAxisAssembly

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxProjectedAxisWitness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalEdgeRaisingGram
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamond
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungMovingFibres

private def CanonicalBoxReverseAxisRange {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row) : Prop :=
  ∀ v : BoxStabilizer (n + 1) b,
    projectedCoordinateLower
      (boxSignature (m := m) a (n + 1) low)
      (boxSignature (m := m) a (n + 1) high)
      (by rw [hrow]; exact sum_raiseWeight _ row)
      row (boxAxis (n + 1) (by omega)).val
      (canonicalBoxGelfandTsetlinFibre a b hstable hgram high v) ∈
      LinearMap.range
        (canonicalBoxGelfandTsetlinFibre a b hstable hgram low).toLinearMap

private def canonicalBoxEdgeAxisData_of_forward_and_raisingGram
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row)
    (hforward : GenuineLoweringFibreAxisData a b
      (boxAxis (n + 1) (by omega))
      (canonicalBoxGelfandTsetlinFibre a b hstable hgram)
      low high row
      (by rw [hrow]; exact sum_raiseWeight _ row))
    (hraising : ∃ raisingGram : ℝ, 0 < raisingGram ∧
      (∀ p q : YoungVertex (n := n + 1)
          (boxSignature (m := m) a (n + 1)) low,
        ⟪youngClebschRaise
            (boxSignature (m := m) a (n + 1) high)
            (boxSignature (m := m) a (n + 1) low)
            (by rw [hrow]; exact sum_raiseWeight _ row) row p,
          youngClebschRaise
            (boxSignature (m := m) a (n + 1) high)
            (boxSignature (m := m) a (n + 1) low)
            (by rw [hrow]; exact sum_raiseWeight _ row) row q⟫_ℝ =
          raisingGram * ⟪p, q⟫_ℝ) ∧
      raisingGram =
        internalRowLowerGramScalar
          (boxSignature (m := m) a (n + 1) high) row *
        weylEdgeRatio (n + 1)
          (boxSignature (m := m) a (n + 1) low) row)
    (hreverse : CanonicalBoxReverseAxisRange
      a b hstable hgram low high row hrow) :
    CanonicalBoxEdgeAxisData a b
      (boxAxis (n + 1) (by omega))
      (canonicalBoxGelfandTsetlinFibre a b hstable hgram)
      low high row hrow := by
  classical
  exact
    { forward := hforward
      raisingGram := Classical.choose hraising
      raisingGram_pos := (Classical.choose_spec hraising).1
      raisingGram_inner := (Classical.choose_spec hraising).2.1
      raisingGram_ratio := (Classical.choose_spec hraising).2.2
      reverse_range := hreverse }

theorem canonicalEdgeRaisingGram_of_signature_eq
    {r n : ℕ} (low high : Fin (r + 1) → ℕ) (mu : Fin r → ℕ)
    (row : Fin (r + 1))
    (hrow : high = raiseWeight low row)
    (hlow : FiniteInterlacing n low mu)
    (hhigh : FiniteInterlacing n high mu) :
    ∃ raisingGram : ℝ, 0 < raisingGram ∧
      (∀ p q : HarmonicYoungSpace (n := n) low,
        ⟪youngClebschRaise high low
            (by rw [hrow]; exact sum_raiseWeight low row) row p,
          youngClebschRaise high low
            (by rw [hrow]; exact sum_raiseWeight low row) row q⟫_ℝ =
          raisingGram * ⟪p, q⟫_ℝ) ∧
      raisingGram = internalRowLowerGramScalar high row *
        weylEdgeRatio n low row := by
  subst high
  exact canonicalEdgeRaisingGram low mu row hlow hhigh

/-- The canonical box edge axis data of polynomial data used in the spherical-code argument. -/
def canonicalBoxEdgeAxisDataOfPolynomialData
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row)
    (D : CanonicalBoxForwardPolynomialData
      a b hstable hgram low high row hrow)
    (hreverse : CanonicalBoxReverseAxisRange
      a b hstable hgram low high row hrow) :
    CanonicalBoxEdgeAxisData a b
      (boxAxis (n + 1) (by omega))
      (canonicalBoxGelfandTsetlinFibre a b hstable hgram)
      low high row hrow := by
  let lowSignature := boxSignature (m := m) a (n + 1) low
  let highSignature := boxSignature (m := m) a (n + 1) high
  let stabilizer := Weyl.flooredWeight b (n + 1)
  have hlow : FiniteInterlacing (n + 1) lowSignature stabilizer :=
    hstable ((Fintype.equivFin
      (RectangularVertices.Vertex (r + 1) m)).symm low)
  have hhigh : FiniteInterlacing (n + 1) highSignature stabilizer :=
    hstable ((Fintype.equivFin
      (RectangularVertices.Vertex (r + 1) m)).symm high)
  have hraising := canonicalEdgeRaisingGram_of_signature_eq
    lowSignature highSignature stabilizer row hrow hlow hhigh
  refine canonicalBoxEdgeAxisData_of_forward_and_raisingGram
    a b hstable hgram low high row hrow
    (canonicalBoxGenuineForwardAxisData
      a b hstable hgram low high row hrow D) ?_ hreverse
  exact hraising

end HigherYoungAllRankActualProjectedAxisAssembly

end

section


open scoped BigOperators InnerProductSpace

namespace HigherHarmonicYoung.AllRankActualBranchingDimension

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHierarchy

theorem finrank_harmonicYoung_eq_sum_fullBranch_of_weylBranching
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n) (hdom : Antitone lam)
    (hbranch : WeylBranchingRecurrence n lam) :
    Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) =
      ∑ mu : FullBranchWeight lam,
        Module.finrank ℝ
          (HarmonicYoungSpace (n := n - 1)
            (fullBranchSignature mu)) := by
  have hreal :
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) : ℝ) =
        (∑ mu : FullBranchWeight lam,
          Module.finrank ℝ
            (HarmonicYoungSpace (n := n - 1)
              (fullBranchSignature mu)) : ℕ) := by
    calc
      (Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) : ℝ) =
          Weyl.dimension n lam :=
        (weyl_dimension_eq_finrank_harmonicYoung (by omega) lam hdom).symm
      _ = ∑ mu : FullBranchWeight lam,
          Weyl.dimension (n - 1) (fullBranchSignature mu) := hbranch
      _ = ∑ mu : FullBranchWeight lam,
          (Module.finrank ℝ
            (HarmonicYoungSpace (n := n - 1)
              (fullBranchSignature mu)) : ℝ) := by
        apply Finset.sum_congr rfl
        intro mu _
        exact weyl_dimension_eq_finrank_harmonicYoung (by omega)
          (fullBranchSignature mu) (fullBranchSignature_antitone mu)
      _ = (∑ mu : FullBranchWeight lam,
          Module.finrank ℝ
            (HarmonicYoungSpace (n := n - 1)
              (fullBranchSignature mu)) : ℕ) := by
        rw [Nat.cast_sum]
  exact_mod_cast hreal

end HigherHarmonicYoung.AllRankActualBranchingDimension

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungAllRankDistinctSignatureStabilizerIntertwiner

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.IsotropicAmbientHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungAllRankActualHighestKernelRigidity
open MetricCodes.Spherical.HigherYoungAllRankStabilizerHighestCyclicity
open MetricCodes.Spherical.HigherYoungArbitraryRankDominantHighestLinePreservation
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem rotationIntertwiner_complexCombination_eigen_of_signatures
    {r n k : ℕ} (mu nu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A)
    (a b : Fin k → Fin n) (c : Fin k → ℂ) (z : ℂ)
    (p q : HarmonicYoungSpace (n := n) mu)
    (heigen :
      (∑ i : Fin k,
        c i • complexAmbientRotation (r := r) (a i) (b i)
          (youngComplexPair mu p q)) =
        z • youngComplexPair mu p q) :
    (∑ i : Fin k,
      c i • complexAmbientRotation (r := r) (a i) (b i)
        (youngComplexPair nu (A p) (A q))) =
      z • youngComplexPair nu (A p) (A q) := by
  rw [complexRotationCombination_youngComplexPair,
    complex_smul_youngComplexPair] at heigen ⊢
  have hreal :
      (∑ i : Fin k,
        ((c i).re • youngAmbientRotation mu (a i) (b i) p -
          (c i).im • youngAmbientRotation mu (a i) (b i) q)) =
        z.re • p - z.im • q := by
    apply Subtype.ext
    simpa only [Finset.sum_sub_distrib, AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul, youngAmbientRotation_apply_coe, ambientRotation_apply,
      ambientCoordinateDerivation_apply,
      polynomialRealPart_youngComplexPair] using congrArg polynomialRealPart heigen
  have himag :
      (∑ i : Fin k,
        ((c i).im • youngAmbientRotation mu (a i) (b i) p +
          (c i).re • youngAmbientRotation mu (a i) (b i) q)) =
        z.im • p + z.re • q := by
    apply Subtype.ext
    simpa only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_add, SetLike.val_smul,
      youngAmbientRotation_apply_coe, ambientRotation_apply, ambientCoordinateDerivation_apply,
      Finset.sum_sub_distrib,
      polynomialImaginaryPart_youngComplexPair] using congrArg polynomialImaginaryPart heigen
  have hArot (i : Fin k) (v : HarmonicYoungSpace (n := n) mu) :
      A (youngAmbientRotation mu (a i) (b i) v) =
        youngAmbientRotation nu (a i) (b i) (A v) :=
    LinearMap.congr_fun (hcomm (a i) (b i)) v
  have hrealA := congrArg A hreal
  have himagA := congrArg A himag
  simp only [map_sum, map_sub, map_add, map_smul, hArot]
    at hrealA himagA
  exact congrArg₂ (youngComplexPair nu) hrealA himagA

theorem youngComplexPair_mem_fullYoungComplexPolynomialSpan
    {r n : ℕ} (nu : Fin (r + 1) → ℕ)
    (p q : HarmonicYoungSpace (n := n) nu) :
    youngComplexPair nu p q ∈ fullYoungComplexPolynomialSpan nu := by
  unfold youngComplexPair fullYoungComplexPolynomialSpan polynomialComplexSpan
  apply (Submodule.span ℂ
    ((polynomialComplexification (r := r) (n := n)) ''
      (harmonicYoungSubmodule (n := n) nu : Set (PolynomialSpace r n)))).add_mem
  · exact Submodule.subset_span ⟨p, p.property, rfl⟩
  · exact (Submodule.span ℂ
      ((polynomialComplexification (r := r) (n := n)) ''
        (harmonicYoungSubmodule (n := n) nu : Set (PolynomialSpace r n)))).smul_mem
      Complex.I (Submodule.subset_span ⟨q, q.property, rfl⟩)

theorem rotationIntertwiner_complexRotation_eigen_of_signatures
    {r n : ℕ} (mu nu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A)
    (a b : Fin n) (c z : ℂ)
    (p q : HarmonicYoungSpace (n := n) mu)
    (heigen :
      c • complexAmbientRotation (r := r) a b
          (youngComplexPair mu p q) =
        z • youngComplexPair mu p q) :
    c • complexAmbientRotation (r := r) a b
        (youngComplexPair nu (A p) (A q)) =
      z • youngComplexPair nu (A p) (A q) := by
  have h := rotationIntertwiner_complexCombination_eigen_of_signatures
    mu nu A hcomm (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
    (fun _ : Fin 1 => c) z p q (by
      simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] using heigen)
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] using h

private def youngIntertwinerHighestPolynomial
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu nu : Fin (r + 1) → ℕ) (hdom : Antitone mu)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  youngComplexPair nu
    (A (dominantHighestRealVector hn mu hdom))
    (A (dominantHighestImaginaryVector hn mu hdom))

theorem rotationIntertwiner_ambientCartan_dominantHighest_of_signatures
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu nu : Fin (r + 1) → ℕ) (hdom : Antitone mu)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A)
    (i : Fin (r + 1)) :
    ambientCartan hn i
        (youngIntertwinerHighestPolynomial hn mu nu hdom A) =
      ((2 * mu i : ℕ) : ℂ) •
        youngIntertwinerHighestPolynomial hn mu nu hdom A := by
  unfold youngIntertwinerHighestPolynomial
  rw [ambientCartan_eq_twice_I_complexRotation]
  change
    ((2 : ℂ) * Complex.I) •
      complexAmbientRotation (r := r)
        (oddCoordinate hn i) (evenCoordinate hn i)
        (youngComplexPair nu
          (A (dominantHighestRealVector hn mu hdom))
          (A (dominantHighestImaginaryVector hn mu hdom))) = _
  apply rotationIntertwiner_complexRotation_eigen_of_signatures
    mu nu A hcomm (oddCoordinate hn i) (evenCoordinate hn i)
    ((2 : ℂ) * Complex.I) ((2 * mu i : ℕ) : ℂ)
    (dominantHighestRealVector hn mu hdom)
    (dominantHighestImaginaryVector hn mu hdom)
  rw [youngComplexPair_dominantHighest]
  change
    (((2 : ℂ) * Complex.I) •
      complexAmbientRotation (r := r)
        (oddCoordinate hn i) (evenCoordinate hn i))
        (dominantHighestWeightWitness hn mu hdom).polynomial = _
  rw [← ambientCartan_eq_twice_I_complexRotation]
  exact ambientCartan_dominantHighestWeightWitness hn mu hdom i

theorem rotationIntertwiner_ambientPositiveRoot_zero_of_signatures
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu nu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A)
    (i j : Fin (r + 1))
    (p q : HarmonicYoungSpace (n := n) mu)
    (hroot : ambientPositiveRoot hn i j (youngComplexPair mu p q) = 0) :
    ambientPositiveRoot hn i j
        (youngComplexPair nu (A p) (A q)) = 0 := by
  rw [ambientPositiveRoot_eq_complexRotations] at hroot ⊢
  change
    complexAmbientRotation (r := r) (evenCoordinate hn i)
        (evenCoordinate hn j) (youngComplexPair nu (A p) (A q)) +
      complexAmbientRotation (r := r) (oddCoordinate hn i)
        (oddCoordinate hn j) (youngComplexPair nu (A p) (A q)) +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate hn i) (evenCoordinate hn j)
          (youngComplexPair nu (A p) (A q)) +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate hn j) (evenCoordinate hn i)
          (youngComplexPair nu (A p) (A q)) = 0
  have h := rotationIntertwiner_complexCombination_eigen_of_signatures
    mu nu A hcomm
    ![evenCoordinate hn i, oddCoordinate hn i,
      oddCoordinate hn i, oddCoordinate hn j]
    ![evenCoordinate hn j, oddCoordinate hn j,
      evenCoordinate hn j, evenCoordinate hn i]
    ![(1 : ℂ), 1, Complex.I, Complex.I] 0 p q (by
      simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
        Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        one_smul, zero_smul, add_zero, zero_add, add_assoc,
        Derivation.add_apply, Derivation.smul_apply]
        using hroot)
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
    Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    one_smul, zero_smul, add_zero, zero_add, add_assoc]
    using h

theorem rotationIntertwiner_ambientSumPositiveRoot_zero_of_signatures
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu nu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A)
    (i j : Fin (r + 1))
    (p q : HarmonicYoungSpace (n := n) mu)
    (hroot : ambientSumPositiveRoot hn i j
      (youngComplexPair mu p q) = 0) :
    ambientSumPositiveRoot hn i j
        (youngComplexPair nu (A p) (A q)) = 0 := by
  rw [ambientSumPositiveRoot_eq_complexRotations] at hroot ⊢
  change
    complexAmbientRotation (r := r) (evenCoordinate hn i)
        (evenCoordinate hn j) (youngComplexPair nu (A p) (A q)) -
      complexAmbientRotation (r := r) (oddCoordinate hn i)
        (oddCoordinate hn j) (youngComplexPair nu (A p) (A q)) +
      Complex.I • complexAmbientRotation (r := r)
        (evenCoordinate hn i) (oddCoordinate hn j)
          (youngComplexPair nu (A p) (A q)) +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate hn i) (evenCoordinate hn j)
          (youngComplexPair nu (A p) (A q)) = 0
  have h := rotationIntertwiner_complexCombination_eigen_of_signatures
    mu nu A hcomm
    ![evenCoordinate hn i, oddCoordinate hn i,
      evenCoordinate hn i, oddCoordinate hn i]
    ![evenCoordinate hn j, oddCoordinate hn j,
      oddCoordinate hn j, evenCoordinate hn j]
    ![(1 : ℂ), -1, Complex.I, Complex.I] 0 p q (by
      simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
        Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        one_smul, neg_one_smul, zero_smul, add_zero,
        zero_add, sub_eq_add_neg, add_assoc, Derivation.add_apply,
        neg_apply, LinearMap.neg_apply, Derivation.neg_apply,
        Derivation.smul_apply] using hroot)
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
    Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    one_smul, neg_one_smul, zero_smul, add_zero,
    zero_add, sub_eq_add_neg, add_assoc] using h

theorem rotationIntertwiner_ambientShortPositiveRoot_zero_of_signatures
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu nu : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A)
    (i : Fin (r + 1)) (t : Fin n)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hroot : ambientShortPositiveRoot hn i t
      (youngComplexPair mu p q) = 0) :
    ambientShortPositiveRoot hn i t
        (youngComplexPair nu (A p) (A q)) = 0 := by
  rw [ambientShortPositiveRoot_eq_complexRotations] at hroot ⊢
  change
    complexAmbientRotation (r := r) (evenCoordinate hn i) t
        (youngComplexPair nu (A p) (A q)) +
      Complex.I • complexAmbientRotation (r := r)
        (oddCoordinate hn i) t
          (youngComplexPair nu (A p) (A q)) = 0
  have h := rotationIntertwiner_complexCombination_eigen_of_signatures
    mu nu A hcomm
    ![evenCoordinate hn i, oddCoordinate hn i]
    ![t, t] ![(1 : ℂ), Complex.I] 0 p q (by
      simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
        Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        one_smul, zero_smul, add_zero, zero_add, Derivation.add_apply,
        Derivation.smul_apply] using hroot)
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
    Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    one_smul, zero_smul, add_zero, zero_add] using h

theorem rotationIntertwiner_positiveRoot_dominantHighest_of_signatures
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu nu : Fin (r + 1) → ℕ) (hdom : Antitone mu)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A)
    (α : OrthogonalPositiveRoot r n) :
    orthogonalPositiveRootDerivation hn α
      (youngIntertwinerHighestPolynomial hn mu nu hdom A) = 0 := by
  cases α with
  | difference i j hij =>
      apply rotationIntertwiner_ambientPositiveRoot_zero_of_signatures
        hn mu nu A hcomm i j
      rw [youngComplexPair_dominantHighest]
      exact ambientPositiveRoot_dominantHighestWeightWitness
        hn mu hdom i j hij
  | sum i j hij =>
      apply rotationIntertwiner_ambientSumPositiveRoot_zero_of_signatures
        hn mu nu A hcomm i j
      rw [youngComplexPair_dominantHighest]
      exact ambientSumPositiveRoot_dominantHighestWeightWitness
        hn mu hdom i j
  | short i t ht =>
      apply rotationIntertwiner_ambientShortPositiveRoot_zero_of_signatures
        hn mu nu A hcomm i t
      rw [youngComplexPair_dominantHighest]
      exact ambientShortPositiveRoot_dominantHighestWeightWitness
        hn mu hdom i t ht

theorem youngRotationIntertwiner_eq_zero_of_signature_ne_of_highest_and_cyclic
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (mu nu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (hne : mu ≠ nu)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A)
    (hhighest : ∀ z ∈ fullYoungComplexPolynomialSpan (n := n) nu,
      (∀ α : OrthogonalPositiveRoot r n,
        orthogonalPositiveRootDerivation hn α z = 0) →
      z ∈ ambientIsotropicHighestSubmodule hn nu)
    (hcyclic : dominantHighestRotationWordSpan hn mu hmu = ⊤) :
    A = 0 := by
  classical
  let p := dominantHighestRealVector hn mu hmu
  let q := dominantHighestImaginaryVector hn mu hmu
  let f := youngIntertwinerHighestPolynomial hn mu nu hmu A
  have hfspan : f ∈ fullYoungComplexPolynomialSpan nu :=
    youngComplexPair_mem_fullYoungComplexPolynomialSpan nu (A p) (A q)
  have hfhighest : f ∈ ambientIsotropicHighestSubmodule hn nu :=
    hhighest f hfspan
      (rotationIntertwiner_positiveRoot_dominantHighest_of_signatures
        hn mu nu hmu A hcomm)
  obtain ⟨i, hi⟩ : ∃ i, mu i ≠ nu i :=
    not_forall.mp (fun h => hne (funext h))
  have hsource :=
    rotationIntertwiner_ambientCartan_dominantHighest_of_signatures
      hn mu nu hmu A hcomm i
  have htarget :=
    ((mem_ambientIsotropicHighestSubmodule hn nu f).mp hfhighest).2.2.1 i
  have hscalar :
      (((2 * mu i : ℕ) : ℂ) - ((2 * nu i : ℕ) : ℂ)) • f = 0 := by
    rw [sub_smul, ← hsource, ← htarget, sub_self]
  have hneNat : 2 * mu i ≠ 2 * nu i := by omega
  have hneComplex :
      (((2 * mu i : ℕ) : ℂ) - ((2 * nu i : ℕ) : ℂ)) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hneNat
  have hfzero : f = 0 := (smul_eq_zero.mp hscalar).resolve_left hneComplex
  have hpair : A p = 0 ∧ A q = 0 :=
    (youngComplexPair_eq_zero_iff nu (A p) (A q)).mp hfzero
  have hword (v : HarmonicYoungSpace (n := n) mu)
      (hv : A v = 0) :
      operatorWordSpan (youngRotationFamily mu) v ≤ LinearMap.ker A := by
    rw [operatorWordSpan, Submodule.span_le]
    rintro _ ⟨word, rfl⟩
    induction word generalizing v with
    | nil => exact hv
    | cons ab rest ih =>
        apply ih (youngRotationFamily mu ab v)
        have hrot := LinearMap.congr_fun (hcomm ab.1 ab.2) v
        change A (youngRotationFamily mu ab v) =
          youngRotationFamily nu ab (A v) at hrot
        rw [hrot, hv, map_zero]
  have hker : LinearMap.ker A = ⊤ := by
    apply top_unique
    rw [← hcyclic]
    exact sup_le (hword p hpair.1) (hword q hpair.2)
  exact LinearMap.ker_eq_top.mp hker

private theorem actualPositiveRootHighestRigidity_metriccodes2_459a111e
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (hstable : 2 * (r + 1) + 2 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    {f : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hf : f ∈ fullYoungComplexPolynomialSpan (n := n) lam)
    (hroots : ∀ α : OrthogonalPositiveRoot r n,
      orthogonalPositiveRootDerivation hn α f = 0) :
    f ∈ ambientIsotropicHighestSubmodule hn lam :=
  mem_ambientIsotropicHighestSubmodule_of_positiveRootKernel
    hn hstable lam hf hroots

theorem youngRotationIntertwiner_eq_zero_of_signature_ne
    {r n : ℕ} (hstable : 2 * (r + 1) + 2 ≤ n)
    (mu nu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (hne : mu ≠ nu)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (youngAmbientRotation nu a b).comp A) :
    A = 0 := by
  have hn : 2 * (r + 1) ≤ n := by omega
  apply youngRotationIntertwiner_eq_zero_of_signature_ne_of_highest_and_cyclic
    hn mu nu hmu hne A hcomm
  · intro z hz hroots
    exact actualPositiveRootHighestRigidity_metriccodes2_459a111e hn hstable nu hz hroots
  · apply dominantHighestRotationWordSpan_eq_top_of_orthogonalPositiveRootHighestRigidity
      hn mu hmu
    intro z hz hroots
    exact actualPositiveRootHighestRigidity_metriccodes2_459a111e hn hstable mu hz hroots

theorem canonicalGelfandTsetlinFibre_crossGram_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ)
    (hmu : Interlaces lam mu) (hnu : Interlaces lam nu)
    (hmuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam mu hmu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (a b : Fin n) :
    (((canonicalGelfandTsetlinFibre lam nu hnu hnuGram).toLinearMap.adjoint.comp
        (canonicalGelfandTsetlinFibre lam mu hmu hmuGram).toLinearMap).comp
          (youngAmbientRotation mu a b)) =
      (youngAmbientRotation nu a b).comp
        ((canonicalGelfandTsetlinFibre lam nu hnu hnuGram).toLinearMap.adjoint.comp
          (canonicalGelfandTsetlinFibre lam mu hmu hmuGram).toLinearMap) := by
  exact crossGram_intertwines_of_skew
    (canonicalGelfandTsetlinFibre lam nu hnu hnuGram).toLinearMap
    (canonicalGelfandTsetlinFibre lam mu hmu hmuGram).toLinearMap
    (youngAmbientRotation nu a b)
    (youngAmbientRotation mu a b)
    (youngAmbientRotation lam a.castSucc b.castSucc)
    (youngAmbientRotation_adjoint nu a b)
    (youngAmbientRotation_adjoint lam a.castSucc b.castSucc)
    (canonicalGelfandTsetlinFibre_rotation_intertwine
      lam nu hnu hnuGram a b)
    (canonicalGelfandTsetlinFibre_rotation_intertwine
      lam mu hmu hmuGram a b)

theorem canonicalGelfandTsetlinFibre_inner_eq_zero_of_signature_ne
    {r n : ℕ} (hstable : 2 * (r + 1) + 2 ≤ n)
    (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ)
    (hmu : Interlaces lam mu) (hnu : Interlaces lam nu)
    (hmuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam mu hmu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hne : mu ≠ nu)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n) nu) :
    ⟪canonicalGelfandTsetlinFibre lam mu hmu hmuGram p,
      canonicalGelfandTsetlinFibre lam nu hnu hnuGram q⟫_ℝ = 0 := by
  let A :=
    (canonicalGelfandTsetlinFibre lam nu hnu hnuGram).toLinearMap.adjoint.comp
      (canonicalGelfandTsetlinFibre lam mu hmu hmuGram).toLinearMap
  have hzero : A = 0 :=
    youngRotationIntertwiner_eq_zero_of_signature_ne hstable mu nu
      (interlaces_antitone_stabilizer hmu) hne A
      (canonicalGelfandTsetlinFibre_crossGram_rotation_intertwine
        lam mu nu hmu hnu hmuGram hnuGram)
  calc
    ⟪canonicalGelfandTsetlinFibre lam mu hmu hmuGram p,
      canonicalGelfandTsetlinFibre lam nu hnu hnuGram q⟫_ℝ =
      ⟪A p, q⟫_ℝ := by
        change
          ⟪canonicalGelfandTsetlinFibre lam mu hmu hmuGram p,
            canonicalGelfandTsetlinFibre lam nu hnu hnuGram q⟫_ℝ =
          ⟪(canonicalGelfandTsetlinFibre lam nu hnu hnuGram).toLinearMap.adjoint
            (canonicalGelfandTsetlinFibre lam mu hmu hmuGram p), q⟫_ℝ
        exact (LinearMap.adjoint_inner_left
          (canonicalGelfandTsetlinFibre lam nu hnu hnuGram).toLinearMap
          q (canonicalGelfandTsetlinFibre lam mu hmu hmuGram p)).symm
    _ = 0 := by
      rw [hzero, LinearMap.zero_apply, young_inner_eq_polynomialInner]
      rw [SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _

end HigherYoungAllRankDistinctSignatureStabilizerIntertwiner

end

section


open scoped BigOperators InnerProductSpace

namespace HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness

variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

variable {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

private def orthogonalBranchSum (f : (i : ι) → E i →ₗᵢ[ℝ] V) :
    ((i : ι) → E i) →ₗ[ℝ] V := by
  classical
  exact LinearMap.lsum ℝ E ℝ (fun i => (f i).toLinearMap)

omit [FiniteDimensional ℝ V] [∀ i, FiniteDimensional ℝ (E i)] in
@[simp] theorem orthogonalBranchSum_apply
    (f : (i : ι) → E i →ₗᵢ[ℝ] V) (x : (i : ι) → E i) :
    orthogonalBranchSum f x = ∑ i, f i (x i) := by
  simp only [orthogonalBranchSum, LinearMap.lsum_apply, LinearMap.coe_sum, LinearMap.coe_comp,
    LinearIsometry.coe_toLinearMap, LinearMap.coe_proj, Finset.sum_apply, Function.comp_apply,
    Function.eval]

omit [FiniteDimensional ℝ V] [∀ i, FiniteDimensional ℝ (E i)] in
theorem orthogonalBranchSum_range
    (f : (i : ι) → E i →ₗᵢ[ℝ] V) :
    LinearMap.range (orthogonalBranchSum f) =
      ⨆ i, LinearMap.range (f i).toLinearMap := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [orthogonalBranchSum_apply]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup
      (fun j => LinearMap.range (f j).toLinearMap) i)
      ⟨x i, rfl⟩
  · apply iSup_le
    intro i
    rintro _ ⟨x, rfl⟩
    refine ⟨Pi.single i x, ?_⟩
    exact LinearMap.lsum_piSingle ℝ E ℝ
      (fun j => (f j).toLinearMap) i x

omit [FiniteDimensional ℝ V] [∀ i, FiniteDimensional ℝ (E i)] in
theorem orthogonalBranchSum_injective
    (f : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0) :
    Function.Injective (orthogonalBranchSum f) := by
  classical
  intro x y heq
  let z : (i : ι) → E i := x - y
  have hz : orthogonalBranchSum f z = 0 := by
    dsimp [z]
    rw [map_sub, heq, sub_self]
  apply funext
  intro i
  have hsingle :
      (∑ j : ι, ⟪f i (z i), f j (z j)⟫_ℝ) =
        ⟪f i (z i), f i (z i)⟫_ℝ := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact horth i j (Ne.symm hji) (z i) (z j)
    · simp only [Finset.mem_univ, not_true_eq_false, inner_self_eq_norm_sq_to_K, norm_map,
        Real.ringHom_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        norm_eq_zero, IsEmpty.forall_iff]
  have hinner : ⟪f i (z i), f i (z i)⟫_ℝ = 0 := by
    calc
      ⟪f i (z i), f i (z i)⟫_ℝ =
          ∑ j : ι, ⟪f i (z i), f j (z j)⟫_ℝ := hsingle.symm
      _ = ⟪f i (z i), orthogonalBranchSum f z⟫_ℝ := by
        rw [orthogonalBranchSum_apply, inner_sum]
      _ = 0 := by rw [hz, inner_zero_right]
  have hzi : z i = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp <| by
    calc
      ⟪z i, z i⟫_ℝ = ⟪f i (z i), f i (z i)⟫_ℝ :=
        ((f i).inner_map_map (z i) (z i)).symm
      _ = 0 := hinner
  change x i - y i = 0 at hzi
  exact sub_eq_zero.mp hzi

theorem orthogonalBranch_iSup_range_eq_top
    (f : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i)) :
    (⨆ i, LinearMap.range (f i).toLinearMap) =
      (⊤ : Submodule ℝ V) := by
  rw [← orthogonalBranchSum_range]
  apply Submodule.eq_top_of_finrank_eq
  calc
    Module.finrank ℝ (LinearMap.range (orthogonalBranchSum f)) =
        Module.finrank ℝ ((i : ι) → E i) :=
      LinearMap.finrank_range_of_inj
        (orthogonalBranchSum_injective f horth)
    _ = ∑ i : ι, Module.finrank ℝ (E i) :=
      Module.finrank_pi_fintype ℝ
    _ = Module.finrank ℝ V := hdim.symm

omit [Fintype ι] [FiniteDimensional ℝ V]
    [∀ i, FiniteDimensional ℝ (E i)] in
theorem orthogonalBranch_family
    (f : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0) :
    OrthogonalFamily ℝ
      (fun i => LinearMap.range (f i).toLinearMap)
      (fun i => (LinearMap.range (f i).toLinearMap).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro i j hij
  apply Submodule.isOrtho_iff_inner_eq.mpr
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
  exact horth i j hij p q

theorem orthogonalBranch_sum_projection
    (f : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i))
    (x : V) :
    (∑ i : ι, (LinearMap.range (f i).toLinearMap).starProjection x) = x := by
  apply (orthogonalBranch_family f horth).sum_projection_of_mem_iSup
  rw [orthogonalBranch_iSup_range_eq_top f horth hdim]
  trivial

theorem orthogonalBranch_mem_range_iff
    (f : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i))
    (i : ι) (x : V) :
    x ∈ LinearMap.range (f i).toLinearMap ↔
      ∀ j : ι, j ≠ i → ∀ y : E j, ⟪x, f j y⟫_ℝ = 0 := by
  classical
  constructor
  · rintro ⟨p, rfl⟩ j hji y
    exact horth i j (Ne.symm hji) p y
  · intro hx
    have hzero : ∀ j : ι, j ≠ i →
        (LinearMap.range (f j).toLinearMap).starProjection x = 0 := by
      intro j hji
      apply (Submodule.starProjection_apply_eq_zero_iff
        (LinearMap.range (f j).toLinearMap)).mpr
      apply ((LinearMap.range (f j).toLinearMap).mem_orthogonal' x).mpr
      rintro _ ⟨y, rfl⟩
      exact hx j hji y
    have hsum := orthogonalBranch_sum_projection f horth hdim x
    have hsingle :
        (∑ j : ι,
          (LinearMap.range (f j).toLinearMap).starProjection x) =
          (LinearMap.range (f i).toLinearMap).starProjection x := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact hzero j hji
      · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
    rw [hsingle] at hsum
    rw [← hsum]
    exact Submodule.starProjection_apply_mem _ x

theorem orthogonalBranch_mem_range_of_orthogonal
    (f : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i))
    (i : ι) (x : V)
    (hx : ∀ j : ι, j ≠ i → ∀ y : E j, ⟪x, f j y⟫_ℝ = 0) :
    x ∈ LinearMap.range (f i).toLinearMap :=
  (orthogonalBranch_mem_range_iff f horth hdim i x).mpr hx

end HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness

end

section


namespace HigherYoungAllRankWeylBranchingRowDifference

private def adjacentRowDifference {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  fun i j =>
    Fin.lastCases (M (Fin.last r) j)
      (fun k : Fin r => M k.castSucc j - M k.succ j) i

@[simp] theorem adjacentRowDifference_castSucc
    {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (i : Fin r) (j : Fin (r + 1)) :
    adjacentRowDifference M i.castSucc j =
      M i.castSucc j - M i.succ j := by
  simp only [adjacentRowDifference, Fin.lastCases_castSucc]

@[simp] theorem adjacentRowDifference_last
    {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (j : Fin (r + 1)) :
    adjacentRowDifference M (Fin.last r) j = M (Fin.last r) j := by
  simp only [adjacentRowDifference, Fin.lastCases_last]

theorem det_adjacentRowDifference {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    (adjacentRowDifference M).det = M.det := by
  let e : Equiv.Perm (Fin (r + 1)) := Fin.revPerm
  have hdet : (M.submatrix e e).det =
      ((adjacentRowDifference M).submatrix e e).det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_pred
      (fun _ : Fin r => (1 : R))
    · intro j
      simp only [Matrix.submatrix_apply, Fin.revPerm_apply, Fin.rev_zero, adjacentRowDifference,
        Fin.lastCases_last, e]
    · intro i j
      change M (Fin.rev i.succ) (Fin.rev j) =
        adjacentRowDifference M (Fin.rev i.succ) (Fin.rev j) +
          1 * M (Fin.rev i.castSucc) (Fin.rev j)
      rw [Fin.rev_succ, Fin.rev_castSucc]
      simp only [adjacentRowDifference, Fin.lastCases_castSucc, one_mul, sub_add_cancel]
  simpa only [Matrix.det_submatrix_equiv_self] using hdet.symm

end HigherYoungAllRankWeylBranchingRowDifference

namespace HigherHarmonicYoung.BranchingDimension

private def branchLower {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (i : Fin (r + 1)) : ℕ :=
  Fin.lastCases 0 (fun j : Fin r => lam j.succ) i

@[simp] theorem branchLower_castSucc {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (i : Fin r) :
    branchLower lam i.castSucc = lam i.succ := by
  simp only [branchLower, Fin.lastCases_castSucc]

@[simp] theorem branchLower_last {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    branchLower lam (Fin.last r) = 0 := by
  simp only [branchLower, Fin.lastCases_last]

private def fullBranchWeightProductEquiv {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    FullBranchWeight lam ≃
      (∀ i : Fin (r + 1),
        {x : Fin (lam i + 1) // branchLower lam i ≤ x.val}) where
  toFun mu i := ⟨mu.val i, by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [branchLower_last, zero_le]
    · simpa only [branchLower_castSucc] using mu.property j⟩
  invFun x := ⟨fun i => (x i).val, by
    intro i
    simpa only [branchLower_castSucc] using (x i.castSucc).property⟩
  left_inv mu := by
    apply Subtype.ext
    rfl
  right_inv x := by
    funext i
    apply Subtype.ext
    rfl

end HigherHarmonicYoung.BranchingDimension

end

section


open scoped BigOperators

namespace HigherYoungAllRankWeylBranchingDeterminantSum

open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference

theorem det_rowSum_eq_sum_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (row : ∀ i, κ i → ι → R) :
    Matrix.det (fun i j => ∑ a : κ i, row i a j) =
      ∑ a : (∀ i, κ i),
        Matrix.det (fun i j => row i (a i) j) := by
  change Matrix.detRowAlternating (fun i j => ∑ a : κ i, row i a j) =
    ∑ a : (∀ i, κ i), Matrix.detRowAlternating (fun i j => row i (a i) j)
  have hrows :
      (fun i => ∑ a : κ i, row i a) =
        (fun i j => ∑ a : κ i, row i a j) := by
    funext i j
    simp only [Finset.sum_apply]
  rw [← hrows]
  exact
    (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R).toMultilinearMap.map_sum row

theorem sum_det_eq_det_rowSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (row : ∀ i, κ i → ι → R) :
    (∑ a : (∀ i, κ i),
        Matrix.det (fun i j => row i (a i) j)) =
      Matrix.det (fun i j => ∑ a : κ i, row i a j) :=
  (det_rowSum_eq_sum_det row).symm

private def branchJacobiTrudiRow {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1))
    (x : {a : Fin (lam i + 1) // branchLower lam i ≤ a.val})
    (j : Fin (r + 1)) : ℤ :=
  orthogonalCompleteSymmetricCoefficient n
      ((x.val.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)) -
    orthogonalCompleteSymmetricCoefficient n
      ((x.val.val : ℤ) - (i.val : ℤ) - (j.val : ℤ) - 2)

theorem sum_orthogonalJacobiTrudiDimension_eq_det_branchRowSum
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    (∑ mu : FullBranchWeight lam,
      orthogonalJacobiTrudiDimension n (fullBranchSignature mu)) =
      Matrix.det (fun i j =>
        ∑ x : {a : Fin (lam i + 1) // branchLower lam i ≤ a.val},
          branchJacobiTrudiRow n lam i x j) := by
  classical
  let row : ∀ i : Fin (r + 1),
      {a : Fin (lam i + 1) // branchLower lam i ≤ a.val} →
        Fin (r + 1) → ℤ :=
    branchJacobiTrudiRow n lam
  calc
    (∑ mu : FullBranchWeight lam,
        orthogonalJacobiTrudiDimension n (fullBranchSignature mu)) =
      ∑ x : (∀ i : Fin (r + 1),
          {a : Fin (lam i + 1) // branchLower lam i ≤ a.val}),
        Matrix.det (fun i j => row i (x i) j) := by
      rw [← (fullBranchWeightProductEquiv lam).sum_comp]
      apply Finset.sum_congr rfl
      intro mu _
      unfold orthogonalJacobiTrudiDimension orthogonalJacobiTrudiMatrix
      congr 1
    _ = Matrix.det (fun i j => ∑ x, row i x j) :=
      sum_det_eq_det_rowSum row
    _ = _ := rfl

theorem orthogonalJacobiTrudiDimension_eq_branchSum_of_rowSum
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hrow : ∀ (i j : Fin (r + 1)),
      (∑ x : {a : Fin (lam i + 1) // branchLower lam i ≤ a.val},
        branchJacobiTrudiRow (n - 1) lam i x j) =
        adjacentRowDifference (orthogonalJacobiTrudiMatrix n lam) i j) :
    orthogonalJacobiTrudiDimension n lam =
      ∑ mu : FullBranchWeight lam,
        orthogonalJacobiTrudiDimension (n - 1)
          (fullBranchSignature mu) := by
  calc
    orthogonalJacobiTrudiDimension n lam =
        Matrix.det (adjacentRowDifference
          (orthogonalJacobiTrudiMatrix n lam)) := by
      exact (det_adjacentRowDifference
        (orthogonalJacobiTrudiMatrix n lam)).symm
    _ = Matrix.det (fun i j =>
        ∑ x : {a : Fin (lam i + 1) // branchLower lam i ≤ a.val},
          branchJacobiTrudiRow (n - 1) lam i x j) := by
      congr 1
      funext i j
      exact (hrow i j).symm
    _ = _ :=
      (sum_orthogonalJacobiTrudiDimension_eq_det_branchRowSum
        (n := n - 1) lam).symm

end HigherYoungAllRankWeylBranchingDeterminantSum

namespace HigherYoungOrthogonalBranchCompleteCoefficient

open MetricCodes.Spherical.HigherWeylBinomialDeterminant

theorem orthogonalCompleteSymmetricCoefficient_dimension_sub
    {n : ℕ} (hn : 2 ≤ n) (k : ℤ) :
    orthogonalCompleteSymmetricCoefficient n k -
        orthogonalCompleteSymmetricCoefficient n (k - 1) =
      orthogonalCompleteSymmetricCoefficient (n - 1) k := by
  by_cases hk : 0 ≤ k
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    cases m with
    | zero =>
        simp only [orthogonalCompleteSymmetricCoefficient, CharP.cast_eq_zero, Std.le_refl,
          ↓reduceIte, Int.toNat_zero, add_zero, Nat.choose_zero_right, Nat.cast_one, zero_sub,
          Int.reduceNeg, Int.neg_nonneg, Int.reduceLE, sub_zero]
    | succ m =>
        have hprev : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
        rw [hprev, orthogonalCompleteSymmetricCoefficient_nat,
          orthogonalCompleteSymmetricCoefficient_nat,
          orthogonalCompleteSymmetricCoefficient_nat]
        have hfirst : n + (m + 1) - 1 = n + m := by omega
        have hthird : n - 1 + (m + 1) - 1 = n + m - 1 := by omega
        rw [hfirst, hthird]
        have hpascal := Nat.choose_succ_succ (n + m - 1) m
        have htop : n + m - 1 + 1 = n + m := by omega
        have hpascal' :
            ((n + m).choose (m + 1) : ℤ) =
              ((n + m - 1).choose m : ℤ) +
                ((n + m - 1).choose (m + 1) : ℤ) := by
          exact_mod_cast (show
            (n + m).choose (m + 1) =
              (n + m - 1).choose m +
                (n + m - 1).choose (m + 1) by
            simpa only [Nat.succ_eq_add_one, htop] using hpascal)
        omega
  · have hkneg : k < 0 := lt_of_not_ge hk
    have hkprev : k - 1 < 0 := by omega
    rw [orthogonalCompleteSymmetricCoefficient_of_neg n hkneg,
      orthogonalCompleteSymmetricCoefficient_of_neg n hkprev,
      orthogonalCompleteSymmetricCoefficient_of_neg (n - 1) hkneg]
    rfl

theorem orthogonalCompleteSymmetricCoefficient_dimension_sum_range
    {n : ℕ} (hn : 2 ≤ n) (a : ℤ) (q : ℕ) :
    (∑ j ∈ Finset.range q,
      orthogonalCompleteSymmetricCoefficient (n - 1) (a + (j : ℤ))) =
      orthogonalCompleteSymmetricCoefficient n (a + (q : ℤ) - 1) -
        orthogonalCompleteSymmetricCoefficient n (a - 1) := by
  induction q with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, CharP.cast_eq_zero, add_zero, sub_self]
  | succ q ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := orthogonalCompleteSymmetricCoefficient_dimension_sub
        hn (a + (q : ℤ))
      push_cast
      have hnext : a + ((q : ℤ) + 1) - 1 = a + (q : ℤ) := by omega
      rw [hnext]
      omega

theorem orthogonalCompleteSymmetricCoefficient_dimension_sum_range_add
    {n : ℕ} (hn : 2 ≤ n) (shift : ℤ) (q : ℕ) :
    (∑ j ∈ Finset.range q,
      orthogonalCompleteSymmetricCoefficient (n - 1) ((j : ℤ) + shift)) =
      orthogonalCompleteSymmetricCoefficient n ((q : ℤ) + shift - 1) -
        orthogonalCompleteSymmetricCoefficient n (shift - 1) := by
  simpa only [add_comm] using orthogonalCompleteSymmetricCoefficient_dimension_sum_range hn shift q

theorem orthogonalCompleteSymmetricCoefficient_dimension_sum_Icc
    {n : ℕ} (hn : 2 ≤ n) {L U : ℕ} (hLU : L ≤ U) (shift : ℤ) :
    (∑ k ∈ Finset.Icc L U,
      orthogonalCompleteSymmetricCoefficient (n - 1) ((k : ℤ) + shift)) =
      orthogonalCompleteSymmetricCoefficient n ((U : ℤ) + shift) -
        orthogonalCompleteSymmetricCoefficient n (((L : ℤ) - 1) + shift) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sub _ (show L ≤ U + 1 by omega)]
  rw [orthogonalCompleteSymmetricCoefficient_dimension_sum_range_add hn shift
    (U + 1),
    orthogonalCompleteSymmetricCoefficient_dimension_sum_range_add hn shift L]
  push_cast
  have hupper : (U : ℤ) + 1 + shift - 1 = (U : ℤ) + shift := by omega
  have hlower : (L : ℤ) + shift - 1 = ((L : ℤ) - 1) + shift := by omega
  rw [hupper, hlower]
  ring

theorem orthogonalCompleteSymmetricCoefficient_dimension_sum_subtype
    {n : ℕ} (hn : 2 ≤ n) {L U : ℕ} (hLU : L ≤ U) (shift : ℤ) :
    (∑ k : {k : Fin (U + 1) // L ≤ k.val},
      orthogonalCompleteSymmetricCoefficient (n - 1)
        ((k.val.val : ℤ) + shift)) =
      orthogonalCompleteSymmetricCoefficient n ((U : ℤ) + shift) -
        orthogonalCompleteSymmetricCoefficient n (((L : ℤ) - 1) + shift) := by
  classical
  let branchIndex (k : ℕ) (hk : k ∈ Finset.Icc L U) :
      {j : Fin (U + 1) // L ≤ j.val} :=
    ⟨⟨k, by have h := (Finset.mem_Icc.mp hk).2; omega⟩,
      (Finset.mem_Icc.mp hk).1⟩
  have hindex :
      (∑ k ∈ Finset.Icc L U,
        orthogonalCompleteSymmetricCoefficient (n - 1)
          ((k : ℤ) + shift)) =
        ∑ k : {k : Fin (U + 1) // L ≤ k.val},
          orthogonalCompleteSymmetricCoefficient (n - 1)
            ((k.val.val : ℤ) + shift) := by
    apply Finset.sum_bij branchIndex
    · intro k hk
      exact Finset.mem_univ _
    · intro k₁ hk₁ k₂ hk₂ heq
      exact congrArg (fun j : {j : Fin (U + 1) // L ≤ j.val} => j.val.val) heq
    · intro k hk
      have hmem : k.val.val ∈ Finset.Icc L U := by
        apply Finset.mem_Icc.mpr
        exact ⟨k.property, by have h := k.val.isLt; omega⟩
      refine ⟨k.val.val, hmem, ?_⟩
      apply Subtype.ext
      apply Fin.ext
      rfl
    · intro k hk
      rfl
  rw [← hindex]
  exact orthogonalCompleteSymmetricCoefficient_dimension_sum_Icc hn hLU shift

end HigherYoungOrthogonalBranchCompleteCoefficient

end

section


open scoped BigOperators InnerProductSpace

namespace HigherHarmonicYoung.AllRankWeylBranchingRecurrence

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference
open MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
open MetricCodes.Spherical.HigherWeylAllRankJacobiTrudiWeylEvaluation
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherHierarchy

private abbrev OrthogonalBranchCoordinate {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :=
  {a : Fin (lam i + 1) // branchLower lam i ≤ a.val}

private def orthogonalBranchRow {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ)
    (i : Fin (r + 1)) (a : OrthogonalBranchCoordinate lam i)
    (j : Fin (r + 1)) : ℤ :=
  orthogonalCompleteSymmetricCoefficient (n - 1)
      ((a.val.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)) -
    orthogonalCompleteSymmetricCoefficient (n - 1)
      ((a.val.val : ℤ) - (i.val : ℤ) - (j.val : ℤ) - 2)

theorem branchLower_le_of_antitone {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (i : Fin (r + 1)) : branchLower lam i ≤ lam i := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [branchLower_last, zero_le]
  · simpa only [branchLower_castSucc] using hdom (Fin.castSucc_le_succ k)

theorem orthogonalBranchRows_eq_adjacentRowDifference_of_interval
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (hinterval : ∀ (L U : ℕ), L ≤ U → ∀ shift : ℤ,
      (∑ a : {k : Fin (U + 1) // L ≤ k.val},
        orthogonalCompleteSymmetricCoefficient (n - 1)
          ((a.val.val : ℤ) + shift)) =
        orthogonalCompleteSymmetricCoefficient n
            ((U : ℤ) + shift) -
          orthogonalCompleteSymmetricCoefficient n
            (((L : ℤ) - 1) + shift)) :
    (fun i j =>
      ∑ a : OrthogonalBranchCoordinate lam i,
        orthogonalBranchRow n lam i a j) =
      adjacentRowDifference (orthogonalJacobiTrudiMatrix n lam) := by
  classical
  funext i j
  have hsum (shift : ℤ) :
      (∑ a : OrthogonalBranchCoordinate lam i,
        orthogonalCompleteSymmetricCoefficient (n - 1)
          ((a.val.val : ℤ) + shift)) =
        orthogonalCompleteSymmetricCoefficient n
            ((lam i : ℤ) + shift) -
          orthogonalCompleteSymmetricCoefficient n
            (((branchLower lam i : ℤ) - 1) + shift) :=
    hinterval (branchLower lam i) (lam i)
      (branchLower_le_of_antitone lam hdom i) shift
  have hfirst (a : OrthogonalBranchCoordinate lam i) :
      (a.val.val : ℤ) - (i.val : ℤ) + (j.val : ℤ) =
        (a.val.val : ℤ) + (-(i.val : ℤ) + (j.val : ℤ)) := by omega
  have hsecond (a : OrthogonalBranchCoordinate lam i) :
      (a.val.val : ℤ) - (i.val : ℤ) - (j.val : ℤ) - 2 =
        (a.val.val : ℤ) + (-(i.val : ℤ) - (j.val : ℤ) - 2) := by omega
  simp only [orthogonalBranchRow, Finset.sum_sub_distrib]
  simp_rw [hfirst, hsecond]
  rw [hsum (-(i.val : ℤ) + (j.val : ℤ)),
    hsum (-(i.val : ℤ) - (j.val : ℤ) - 2)]
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [branchLower_last, adjacentRowDifference_last,
      orthogonalJacobiTrudiMatrix, Fin.val_last, Nat.cast_zero]
    have hj : j.val ≤ r := by have := j.isLt; omega
    have hneg₁ : ((0 : ℤ) - 1) + (-(r : ℤ) + (j.val : ℤ)) < 0 := by
      omega
    have hneg₂ :
        ((0 : ℤ) - 1) + (-(r : ℤ) - (j.val : ℤ) - 2) < 0 := by omega
    rw [orthogonalCompleteSymmetricCoefficient_of_neg n hneg₁,
      orthogonalCompleteSymmetricCoefficient_of_neg n hneg₂]
    simp only [sub_zero]
    ring_nf
  · simp only [branchLower_castSucc, adjacentRowDifference_castSucc,
      orthogonalJacobiTrudiMatrix]
    simp only [Fin.val_castSucc, Fin.val_succ]
    push_cast
    ring_nf

theorem orthogonalJacobiTrudiDimension_branching_allRank
    {r n : ℕ} (hn : 2 ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    orthogonalJacobiTrudiDimension n lam =
      ∑ mu : FullBranchWeight lam,
        orthogonalJacobiTrudiDimension (n - 1)
          (fullBranchSignature mu) := by
  have hrows := orthogonalBranchRows_eq_adjacentRowDifference_of_interval
    lam hdom (fun L U hLU shift =>
      orthogonalCompleteSymmetricCoefficient_dimension_sum_subtype
        hn hLU shift)
  apply orthogonalJacobiTrudiDimension_eq_branchSum_of_rowSum lam
  intro i j
  exact congrFun (congrFun hrows i) j

theorem weylBranchingRecurrence_of_jacobiTrudi_branching
    {r n : ℕ} (hn : 2 * r + 5 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hbranch : orthogonalJacobiTrudiDimension n lam =
      ∑ mu : FullBranchWeight lam,
        orthogonalJacobiTrudiDimension (n - 1)
          (fullBranchSignature mu)) :
    WeylBranchingRecurrence n lam := by
  unfold WeylBranchingRecurrence
  calc
    Weyl.dimension n lam =
        (orthogonalJacobiTrudiDimension n lam : ℝ) :=
      (orthogonalJacobiTrudiDimension_eq_weyl (by omega) lam).symm
    _ = (∑ mu : FullBranchWeight lam,
        orthogonalJacobiTrudiDimension (n - 1)
          (fullBranchSignature mu) : ℤ) := by
      exact_mod_cast hbranch
    _ = ∑ mu : FullBranchWeight lam,
        (orthogonalJacobiTrudiDimension (n - 1)
          (fullBranchSignature mu) : ℝ) := by
      rw [Int.cast_sum]
    _ = ∑ mu : FullBranchWeight lam,
        Weyl.dimension (n - 1) (fullBranchSignature mu) := by
      apply Finset.sum_congr rfl
      intro mu _
      exact orthogonalJacobiTrudiDimension_eq_weyl (by omega)
        (fullBranchSignature mu)

theorem weylBranchingRecurrence_allRank
    {r n : ℕ} (hn : 2 * r + 5 ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    WeylBranchingRecurrence n lam :=
  weylBranchingRecurrence_of_jacobiTrudi_branching hn lam
    (orthogonalJacobiTrudiDimension_branching_allRank (by omega) lam hdom)

end HigherHarmonicYoung.AllRankWeylBranchingRecurrence

namespace HigherYoungAllRankZeroRowRotationEquivariance

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem ambientCoordinateDerivation_zeroRowPolynomial
    {r n : ℕ} (a b : Fin n) (p : PolynomialSpace r n) :
    ambientCoordinateDerivation (r := r + 1) a b
        (zeroRowPolynomial n p) =
      zeroRowPolynomial n
        (ambientCoordinateDerivation (r := r) a b p) := by
  rw [ambientCoordinateDerivation_apply, Fin.sum_univ_castSucc]
  simp only [pderiv_zeroRowPolynomial_castSucc,
    pderiv_zeroRowPolynomial_lastRow, mul_zero, add_zero]
  rw [ambientCoordinateDerivation_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, zeroRowPolynomial_X]

theorem ambientRotation_zeroRowPolynomial
    {r n : ℕ} (a b : Fin n) (p : PolynomialSpace r n) :
    ambientRotation (r := r + 1) a b (zeroRowPolynomial n p) =
      zeroRowPolynomial n (ambientRotation (r := r) a b p) := by
  rw [ambientRotation_apply, ambientRotation_apply, map_sub,
    ambientCoordinateDerivation_zeroRowPolynomial,
    ambientCoordinateDerivation_zeroRowPolynomial]

theorem appendZeroRowIsometryEquiv_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (a b : Fin n) :
    (appendZeroRowIsometryEquiv (n := n) lam).toLinearMap.comp
        (youngAmbientRotation lam a b) =
      (youngAmbientRotation (appendZeroWeight lam) a b).comp
        (appendZeroRowIsometryEquiv (n := n) lam).toLinearMap := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact (ambientRotation_zeroRowPolynomial a b
    (p : PolynomialSpace r n)).symm

theorem appendZeroRowIsometryEquiv_symm_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (a b : Fin n) :
    (appendZeroRowIsometryEquiv (n := n) lam).symm.toLinearMap.comp
        (youngAmbientRotation (appendZeroWeight lam) a b) =
      (youngAmbientRotation lam a b).comp
        (appendZeroRowIsometryEquiv (n := n) lam).symm.toLinearMap := by
  apply LinearMap.ext
  intro p
  have h := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_rotation_intertwine lam a b)
    ((appendZeroRowIsometryEquiv (n := n) lam).symm p)
  have hp := congrArg
    (appendZeroRowIsometryEquiv (n := n) lam).symm h
  simpa only [LinearIsometryEquiv.toLinearEquiv_symm, LinearMap.coe_comp, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_symm_toLinearEquiv, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.symm_apply_apply] using hp.symm

end HigherYoungAllRankZeroRowRotationEquivariance

namespace HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualBranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem fullBranchSignature_interlaces_appendZeroWeight
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (mu : FullBranchWeight lam) :
    Interlaces (appendZeroWeight lam) (fullBranchSignature mu) := by
  intro i
  constructor
  · simpa only [appendZeroWeight_castSucc] using
      fullBranchSignature_le mu i
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.succ_last, Nat.succ_eq_add_one, appendZeroWeight_last, zero_le]
    · simpa only [← Fin.castSucc_succ, appendZeroWeight_castSucc] using
        fullBranchSignature_succ_le mu j

theorem fullBranchSignature_injective {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Function.Injective
      (fullBranchSignature (lam := lam)) := by
  intro mu nu h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrFun h i

/-- The canonical full branch fibre used in the spherical-code argument. -/
def canonicalFullBranchFibre {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n)
    (mu : FullBranchWeight lam) :
    HarmonicYoungSpace (n := n - 1) (fullBranchSignature mu) →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n) lam := by
  cases n with
  | zero => omega
  | succ n =>
      let h := fullBranchSignature_interlaces_appendZeroWeight lam mu
      let hgram : PositiveGelfandTsetlinFischerGram (n := n)
          (appendZeroWeight lam) (fullBranchSignature mu) h :=
        positiveGelfandTsetlinFischerGram (by omega)
          (appendZeroWeight lam) (fullBranchSignature mu) h
      exact
        ((appendZeroRowIsometryEquiv (n := n + 1) lam).symm.toLinearIsometry).comp
          (canonicalGelfandTsetlinFibre
            (appendZeroWeight lam) (fullBranchSignature mu) h hgram)

theorem canonicalFullBranchFibre_rotation_intertwine {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam) (a b : Fin n) :
    (canonicalFullBranchFibre lam hn mu).toLinearMap.comp
        (youngAmbientRotation (fullBranchSignature mu) a b) =
      (youngAmbientRotation lam a.castSucc b.castSucc).comp
        (canonicalFullBranchFibre lam hn mu).toLinearMap := by
  let h := fullBranchSignature_interlaces_appendZeroWeight lam mu
  let hgram : PositiveGelfandTsetlinFischerGram (n := n)
      (appendZeroWeight lam) (fullBranchSignature mu) h :=
    positiveGelfandTsetlinFischerGram (by omega)
      (appendZeroWeight lam) (fullBranchSignature mu) h
  let B := canonicalGelfandTsetlinFibre
    (appendZeroWeight lam) (fullBranchSignature mu) h hgram
  let Z := (appendZeroRowIsometryEquiv
    (n := n + 1) lam).symm.toLinearIsometry
  have hB := canonicalGelfandTsetlinFibre_rotation_intertwine
    (appendZeroWeight lam) (fullBranchSignature mu) h hgram a b
  have hZ := appendZeroRowIsometryEquiv_symm_rotation_intertwine
    lam a.castSucc b.castSucc
  apply LinearMap.ext
  intro p
  change Z (B (youngAmbientRotation (fullBranchSignature mu) a b p)) =
    youngAmbientRotation lam a.castSucc b.castSucc (Z (B p))
  have hBp := LinearMap.congr_fun hB p
  have hZp := LinearMap.congr_fun hZ (B p)
  exact (congrArg Z hBp).trans hZp

theorem canonicalFullBranchFibre_orthogonal {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n)
    (mu nu : FullBranchWeight lam) (hne : mu ≠ nu)
    (p : HarmonicYoungSpace
      (n := n - 1) (fullBranchSignature mu))
    (q : HarmonicYoungSpace
      (n := n - 1) (fullBranchSignature nu)) :
    ⟪canonicalFullBranchFibre lam hn mu p,
      canonicalFullBranchFibre lam hn nu q⟫_ℝ = 0 := by
  cases n with
  | zero => omega
  | succ n =>
      let hmu := fullBranchSignature_interlaces_appendZeroWeight lam mu
      let hnu := fullBranchSignature_interlaces_appendZeroWeight lam nu
      let hmuGram : PositiveGelfandTsetlinFischerGram (n := n)
          (appendZeroWeight lam) (fullBranchSignature mu) hmu :=
        positiveGelfandTsetlinFischerGram (by omega)
          (appendZeroWeight lam) (fullBranchSignature mu) hmu
      let hnuGram : PositiveGelfandTsetlinFischerGram (n := n)
          (appendZeroWeight lam) (fullBranchSignature nu) hnu :=
        positiveGelfandTsetlinFischerGram (by omega)
          (appendZeroWeight lam) (fullBranchSignature nu) hnu
      let Z := (appendZeroRowIsometryEquiv
        (n := n + 1) lam).symm.toLinearIsometry
      let Bmu := canonicalGelfandTsetlinFibre
        (appendZeroWeight lam) (fullBranchSignature mu) hmu hmuGram
      let Bnu := canonicalGelfandTsetlinFibre
        (appendZeroWeight lam) (fullBranchSignature nu) hnu hnuGram
      change ⟪Z (Bmu p), Z (Bnu q)⟫_ℝ = 0
      calc
        ⟪Z (Bmu p), Z (Bnu q)⟫_ℝ = ⟪Bmu p, Bnu q⟫_ℝ :=
          Z.inner_map_map (Bmu p) (Bnu q)
        _ = 0 := canonicalGelfandTsetlinFibre_inner_eq_zero_of_signature_ne
          (by omega) (appendZeroWeight lam)
          (fullBranchSignature mu) (fullBranchSignature nu)
          hmu hnu hmuGram hnuGram
          (fun heq => hne (fullBranchSignature_injective lam heq)) p q

theorem canonicalFullBranch_finrank_sum {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n)
    (hdom : Antitone lam) (hbranch : WeylBranchingRecurrence n lam) :
    Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) =
      ∑ mu : FullBranchWeight lam,
        Module.finrank ℝ
          (HarmonicYoungSpace (n := n - 1) (fullBranchSignature mu)) :=
  finrank_harmonicYoung_eq_sum_fullBranch_of_weylBranching
    lam hn hdom hbranch

theorem canonicalFullBranch_finrank_sum_allRank {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n)
    (hdom : Antitone lam) :
    Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) =
      ∑ mu : FullBranchWeight lam,
        Module.finrank ℝ
          (HarmonicYoungSpace (n := n - 1) (fullBranchSignature mu)) :=
  canonicalFullBranch_finrank_sum lam hn hdom
    (weylBranchingRecurrence_allRank hn lam hdom)

theorem canonicalFullBranch_iSup_range_eq_top_allRank {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n)
    (hdom : Antitone lam)
    (horth : ∀ (mu nu : FullBranchWeight lam), mu ≠ nu →
      ∀ (p : HarmonicYoungSpace
          (n := n - 1) (fullBranchSignature mu))
        (q : HarmonicYoungSpace
          (n := n - 1) (fullBranchSignature nu)),
        ⟪canonicalFullBranchFibre lam hn mu p,
          canonicalFullBranchFibre lam hn nu q⟫_ℝ = 0) :
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (canonicalFullBranchFibre lam hn mu).toLinearMap) =
        ⊤ :=
  orthogonalBranch_iSup_range_eq_top (canonicalFullBranchFibre lam hn)
    horth (canonicalFullBranch_finrank_sum_allRank lam hn hdom)

theorem canonicalFullBranch_iSup_range_eq_top_unconditional {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n)
    (hdom : Antitone lam) :
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (canonicalFullBranchFibre lam hn mu).toLinearMap) =
        ⊤ :=
  canonicalFullBranch_iSup_range_eq_top_allRank lam hn hdom
    (canonicalFullBranchFibre_orthogonal lam hn)

theorem canonicalFullBranch_sum_projection {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n)
    (hdom : Antitone lam) (x : HarmonicYoungSpace (n := n) lam) :
    (∑ mu : FullBranchWeight lam,
      (LinearMap.range
        (canonicalFullBranchFibre lam hn mu).toLinearMap).starProjection x) =
      x :=
  orthogonalBranch_sum_projection (canonicalFullBranchFibre lam hn)
    (canonicalFullBranchFibre_orthogonal lam hn)
    (canonicalFullBranch_finrank_sum_allRank lam hn hdom) x

theorem canonicalFullBranch_mem_range_of_orthogonal_allRank {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n)
    (hdom : Antitone lam)
    (horth : ∀ (mu nu : FullBranchWeight lam), mu ≠ nu →
      ∀ (p : HarmonicYoungSpace
          (n := n - 1) (fullBranchSignature mu))
        (q : HarmonicYoungSpace
          (n := n - 1) (fullBranchSignature nu)),
        ⟪canonicalFullBranchFibre lam hn mu p,
          canonicalFullBranchFibre lam hn nu q⟫_ℝ = 0)
    (mu : FullBranchWeight lam) (x : HarmonicYoungSpace (n := n) lam)
    (hx : ∀ (nu : FullBranchWeight lam), nu ≠ mu →
      ∀ q : HarmonicYoungSpace
        (n := n - 1) (fullBranchSignature nu),
        ⟪x, canonicalFullBranchFibre lam hn nu q⟫_ℝ = 0) :
    x ∈ LinearMap.range (canonicalFullBranchFibre lam hn mu).toLinearMap :=
  orthogonalBranch_mem_range_of_orthogonal (canonicalFullBranchFibre lam hn)
    horth (canonicalFullBranch_finrank_sum_allRank lam hn hdom) mu x hx

end HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungAllRankGTProjectedLowerRange

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankHarmonicBranchRotationIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility
open MetricCodes.Spherical.HigherRepresentationGraph

theorem euclideanAmbientRotation_castSucc_last {n : ℕ}
    (a b : Fin n) :
    euclideanAmbientRotation a.castSucc b.castSucc
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) = 0 := by
  simp only [EuclideanSpace.basisFun_apply, euclideanAmbientRotation_apply, ne_eq,
    Fin.castSucc_ne_last, not_false_eq_true, PiLp.single_eq_of_ne, zero_smul, sub_self]

theorem projectedCoordinateLower_fixedAxis_rotation_intertwine
    {r n : ℕ} (low high : Fin (r + 2) → ℕ)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 2)) (a b : Fin n) :
    (projectedCoordinateLower low high hdeg row
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).comp
        (youngAmbientRotation high a.castSucc b.castSucc) =
      (youngAmbientRotation low a.castSucc b.castSucc).comp
        (projectedCoordinateLower low high hdeg row
          (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))) := by
  apply LinearMap.ext
  intro p
  have h := projectedCoordinateLower_rotation low high hdeg row
    a.castSucc b.castSucc
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) p
  rw [euclideanAmbientRotation_castSucc_last] at h
  have hzero : projectedCoordinateLower low high hdeg row 0 p = 0 :=
    map_zero (projectedCoordinateLowerAxis low high hdeg row p)
  rw [hzero, zero_add] at h
  exact h.symm

end HigherYoungAllRankGTProjectedLowerRange

end

section


namespace HigherYoungAllRankSelectedBranchSignature

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem fullBranch_eq_selected_iff_signature_eq_appendZeroWeight
    {r : ℕ} {lam : Fin (r + 2) → ℕ}
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (nu : FullBranchWeight lam) :
    nu = fullBranchOfInterlaces mu h ↔
      fullBranchSignature nu = appendZeroWeight mu := by
  constructor
  · intro hnu
    rw [hnu, fullBranchOfInterlaces_signature_eq_appendZeroWeight]
  · intro hnu
    apply Subtype.ext
    funext i
    apply Fin.ext
    change fullBranchSignature nu i =
      fullBranchSignature (fullBranchOfInterlaces mu h) i
    rw [fullBranchOfInterlaces_signature_eq_appendZeroWeight]
    exact congrFun hnu i

theorem fullBranch_ne_selected_iff_signature_ne_appendZeroWeight
    {r : ℕ} {lam : Fin (r + 2) → ℕ}
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (nu : FullBranchWeight lam) :
    nu ≠ fullBranchOfInterlaces mu h ↔
      fullBranchSignature nu ≠ appendZeroWeight mu := by
  exact not_congr
    (fullBranch_eq_selected_iff_signature_eq_appendZeroWeight mu h nu)

end HigherYoungAllRankSelectedBranchSignature

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankGTProjectedLowerRange
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching

private def canonicalBranchProjectedLowerCrossGram
    {r n : ℕ} (low high : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hhigh : Interlaces high mu)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 2)) (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (nu : FullBranchWeight low) :
    HarmonicYoungSpace (n := n) (appendZeroWeight mu) →ₗ[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature nu) :=
  (canonicalFullBranchFibre low hn nu).toLinearMap.adjoint.comp
    ((projectedCoordinateLower low high hdeg row
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).comp
      ((canonicalGelfandTsetlinFibre high mu hhigh
        (positiveGelfandTsetlinFischerGram (r := r) (n := n) (by omega)
          high mu hhigh)).toLinearMap.comp
        (appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap))

theorem canonicalBranchProjectedLowerCrossGram_rotation_intertwine
    {r n : ℕ} (low high : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hhigh : Interlaces high mu)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 2)) (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (nu : FullBranchWeight low) (a b : Fin n) :
    (canonicalBranchProjectedLowerCrossGram
      low high mu hhigh hdeg row hn nu).comp
        (youngAmbientRotation (appendZeroWeight mu) a b) =
      (youngAmbientRotation (fullBranchSignature nu) a b).comp
        (canonicalBranchProjectedLowerCrossGram
          low high mu hhigh hdeg row hn nu) := by
  let F := (canonicalFullBranchFibre low hn nu).toLinearMap
  let H := (canonicalGelfandTsetlinFibre high mu hhigh
    (positiveGelfandTsetlinFischerGram (r := r) (n := n) (by omega)
      high mu hhigh)).toLinearMap
  let Z := (appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap
  let D := projectedCoordinateLower low high hdeg row
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
  change (F.adjoint.comp (D.comp (H.comp Z))).comp
      (youngAmbientRotation (appendZeroWeight mu) a b) =
    (youngAmbientRotation (fullBranchSignature nu) a b).comp
      (F.adjoint.comp (D.comp (H.comp Z)))
  apply crossGram_intertwines_of_skew F (D.comp (H.comp Z))
    (youngAmbientRotation (fullBranchSignature nu) a b)
    (youngAmbientRotation (appendZeroWeight mu) a b)
    (youngAmbientRotation low a.castSucc b.castSucc)
    (youngAmbientRotation_adjoint (fullBranchSignature nu) a b)
    (youngAmbientRotation_adjoint low a.castSucc b.castSucc)
    (canonicalFullBranchFibre_rotation_intertwine low hn nu a b)
  apply LinearMap.ext
  intro p
  change D (H (Z (youngAmbientRotation (appendZeroWeight mu) a b p))) =
    youngAmbientRotation low a.castSucc b.castSucc (D (H (Z p)))
  have hZ := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_symm_rotation_intertwine mu a b) p
  have hH := LinearMap.congr_fun
    (canonicalGelfandTsetlinFibre_rotation_intertwine
      high mu hhigh
      (positiveGelfandTsetlinFischerGram (r := r) (n := n) (by omega)
        high mu hhigh) a b) (Z p)
  have hD := LinearMap.congr_fun
    (projectedCoordinateLower_fixedAxis_rotation_intertwine
      low high hdeg row a b) (H (Z p))
  exact (congrArg (fun q => D (H q)) hZ).trans
    ((congrArg D hH).trans hD)

theorem canonicalBranchProjectedLowerCrossGram_eq_zero_of_ne_selected
    {r n : ℕ} (low high : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hlow : Interlaces low mu) (hhigh : Interlaces high mu)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 2)) (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (nu : FullBranchWeight low)
    (hne : nu ≠ fullBranchOfInterlaces mu hlow) :
    canonicalBranchProjectedLowerCrossGram
      low high mu hhigh hdeg row hn nu = 0 := by
  have hsignature : appendZeroWeight mu ≠ fullBranchSignature nu :=
    Ne.symm
      ((fullBranch_ne_selected_iff_signature_ne_appendZeroWeight
        mu hlow nu).mp hne)
  have hdom : Antitone (appendZeroWeight mu) := by
    have h := fullBranchSignature_antitone
      (fullBranchOfInterlaces mu hlow)
    rwa [fullBranchOfInterlaces_signature_eq_appendZeroWeight mu hlow] at h
  exact youngRotationIntertwiner_eq_zero_of_signature_ne
    (by omega) (appendZeroWeight mu) (fullBranchSignature nu)
    hdom hsignature
    (canonicalBranchProjectedLowerCrossGram
      low high mu hhigh hdeg row hn nu)
    (canonicalBranchProjectedLowerCrossGram_rotation_intertwine
      low high mu hhigh hdeg row hn nu)

theorem canonicalBranchProjectedLower_orthogonal_of_ne_selected
    {r n : ℕ} (low high : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hlow : Interlaces low mu) (hhigh : Interlaces high mu)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 2)) (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (nu : FullBranchWeight low)
    (hne : nu ≠ fullBranchOfInterlaces mu hlow)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪projectedCoordinateLower low high hdeg row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (canonicalGelfandTsetlinFibre high mu hhigh
          (positiveGelfandTsetlinFischerGram (r := r) (n := n) (by omega)
            high mu hhigh) p),
      canonicalFullBranchFibre low hn nu q⟫_ℝ = 0 := by
  let F := (canonicalFullBranchFibre low hn nu).toLinearMap
  let H := (canonicalGelfandTsetlinFibre high mu hhigh
    (positiveGelfandTsetlinFischerGram (r := r) (n := n) (by omega)
      high mu hhigh)).toLinearMap
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  let D := projectedCoordinateLower low high hdeg row
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
  have hzero := LinearMap.congr_fun
    (canonicalBranchProjectedLowerCrossGram_eq_zero_of_ne_selected
      low high mu hlow hhigh hdeg row hn nu hne) (Z p)
  change ⟪D (H p), F q⟫_ℝ = 0
  calc
    ⟪D (H p), F q⟫_ℝ = ⟪F.adjoint (D (H p)), q⟫_ℝ :=
      (LinearMap.adjoint_inner_left F q (D (H p))).symm
    _ = 0 := by
      have hz : F.adjoint (D (H p)) = 0 := by
        change F.adjoint (D (H (Z.symm (Z p)))) = 0 at hzero
        simpa only [Nat.add_one_sub_one, LinearIsometryEquiv.symm_apply_apply] using hzero
      rw [hz, young_inner_eq_polynomialInner,
        SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _

end HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungAllRankCanonicalGTFullCrossOrthogonality

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching

private def canonicalGelfandTsetlinFullBranchCrossGram
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (nu : FullBranchWeight lam) :
    HarmonicYoungSpace (n := n) (appendZeroWeight mu) →ₗ[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature nu) :=
  (canonicalFullBranchFibre lam hn nu).toLinearMap.adjoint.comp
    ((canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap.comp
      (appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap)

theorem canonicalGelfandTsetlinFullBranchCrossGram_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (nu : FullBranchWeight lam) (a b : Fin n) :
    (canonicalGelfandTsetlinFullBranchCrossGram lam mu h hn hgram nu).comp
        (youngAmbientRotation (appendZeroWeight mu) a b) =
      (youngAmbientRotation (fullBranchSignature nu) a b).comp
        (canonicalGelfandTsetlinFullBranchCrossGram lam mu h hn hgram nu) := by
  let F := (canonicalFullBranchFibre lam hn nu).toLinearMap
  let G := (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap
  let Z := (appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap
  change (F.adjoint.comp (G.comp Z)).comp
      (youngAmbientRotation (appendZeroWeight mu) a b) =
    (youngAmbientRotation (fullBranchSignature nu) a b).comp
      (F.adjoint.comp (G.comp Z))
  apply crossGram_intertwines_of_skew F (G.comp Z)
    (youngAmbientRotation (fullBranchSignature nu) a b)
    (youngAmbientRotation (appendZeroWeight mu) a b)
    (youngAmbientRotation lam a.castSucc b.castSucc)
    (youngAmbientRotation_adjoint (fullBranchSignature nu) a b)
    (youngAmbientRotation_adjoint lam a.castSucc b.castSucc)
    (canonicalFullBranchFibre_rotation_intertwine lam hn nu a b)
  apply LinearMap.ext
  intro p
  change G (Z (youngAmbientRotation (appendZeroWeight mu) a b p)) =
    youngAmbientRotation lam a.castSucc b.castSucc (G (Z p))
  have hZ := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_symm_rotation_intertwine mu a b) p
  have hG := LinearMap.congr_fun
    (canonicalGelfandTsetlinFibre_rotation_intertwine
      lam mu h hgram a b) (Z p)
  exact (congrArg G hZ).trans hG

theorem canonicalGelfandTsetlinFullBranchCrossGram_eq_zero_of_ne_selected
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (nu : FullBranchWeight lam)
    (hne : nu ≠ fullBranchOfInterlaces mu h) :
    canonicalGelfandTsetlinFullBranchCrossGram lam mu h hn hgram nu = 0 := by
  have hsignature : appendZeroWeight mu ≠ fullBranchSignature nu :=
    Ne.symm
      ((fullBranch_ne_selected_iff_signature_ne_appendZeroWeight
        mu h nu).mp hne)
  have hdom : Antitone (appendZeroWeight mu) := by
    have hfull := fullBranchSignature_antitone
      (fullBranchOfInterlaces mu h)
    rwa [fullBranchOfInterlaces_signature_eq_appendZeroWeight mu h] at hfull
  exact youngRotationIntertwiner_eq_zero_of_signature_ne
    (by omega) (appendZeroWeight mu) (fullBranchSignature nu)
    hdom hsignature
    (canonicalGelfandTsetlinFullBranchCrossGram lam mu h hn hgram nu)
    (canonicalGelfandTsetlinFullBranchCrossGram_rotation_intertwine
      lam mu h hn hgram nu)

theorem canonicalGelfandTsetlinFibre_fullBranch_orthogonal_of_ne_selected
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (nu : FullBranchWeight lam)
    (hne : nu ≠ fullBranchOfInterlaces mu h)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪canonicalGelfandTsetlinFibre lam mu h hgram p,
      canonicalFullBranchFibre lam hn nu q⟫_ℝ = 0 := by
  let F := (canonicalFullBranchFibre lam hn nu).toLinearMap
  let G := (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  have hzero := LinearMap.congr_fun
    (canonicalGelfandTsetlinFullBranchCrossGram_eq_zero_of_ne_selected
      lam mu h hn hgram nu hne) (Z p)
  change ⟪G p, F q⟫_ℝ = 0
  calc
    ⟪G p, F q⟫_ℝ = ⟪F.adjoint (G p), q⟫_ℝ :=
      (LinearMap.adjoint_inner_left F q (G p)).symm
    _ = 0 := by
      have hz : F.adjoint (G p) = 0 := by
        change F.adjoint (G (Z.symm (Z p))) = 0 at hzero
        simpa only [LinearIsometryEquiv.symm_apply_apply] using hzero
      rw [hz]
      exact inner_zero_left q

end HigherYoungAllRankCanonicalGTFullCrossOrthogonality

namespace HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality
open MetricCodes.Spherical.ThreeRowYoungBranching

variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

variable {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem orthogonalBranch_range_eq_of_cross_orthogonal
    (f : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i))
    (g : F →ₗᵢ[ℝ] V) (i : ι)
    (hcross : ∀ j : ι, j ≠ i →
      ∀ p : F, ∀ q : E j, ⟪g p, f j q⟫_ℝ = 0)
    (heqdim : Module.finrank ℝ F = Module.finrank ℝ (E i)) :
    LinearMap.range g.toLinearMap =
      LinearMap.range (f i).toLinearMap := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨p, rfl⟩
    apply orthogonalBranch_mem_range_of_orthogonal f horth hdim i (g p)
    intro j hji q
    exact hcross j hji p q
  · calc
      Module.finrank ℝ (LinearMap.range g.toLinearMap) =
          Module.finrank ℝ F :=
        LinearMap.finrank_range_of_inj g.injective
      _ = Module.finrank ℝ (E i) := heqdim
      _ = Module.finrank ℝ (LinearMap.range (f i).toLinearMap) :=
        (LinearMap.finrank_range_of_inj (f i).injective).symm

theorem orthogonalBranch_range_eq_of_cross_orthogonal_of_equiv
    (f : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i))
    (g : F →ₗᵢ[ℝ] V) (i : ι)
    (hcross : ∀ j : ι, j ≠ i →
      ∀ p : F, ∀ q : E j, ⟪g p, f j q⟫_ℝ = 0)
    (e : F ≃ₗᵢ[ℝ] E i) :
    LinearMap.range g.toLinearMap =
      LinearMap.range (f i).toLinearMap :=
  orthogonalBranch_range_eq_of_cross_orthogonal f horth hdim g i hcross
    e.toLinearEquiv.finrank_eq

theorem canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1) (hdom : Antitone lam)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h) :
    LinearMap.range (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap =
      LinearMap.range
        (canonicalFullBranchFibre lam hn
          (fullBranchOfInterlaces mu h)).toLinearMap := by
  apply orthogonalBranch_range_eq_of_cross_orthogonal
    (canonicalFullBranchFibre lam hn)
    (canonicalFullBranchFibre_orthogonal lam hn)
    (canonicalFullBranch_finrank_sum_allRank lam hn hdom)
    (canonicalGelfandTsetlinFibre lam mu h hgram)
    (fullBranchOfInterlaces mu h)
  · intro nu hne p q
    exact canonicalGelfandTsetlinFibre_fullBranch_orthogonal_of_ne_selected
      lam mu h hn hgram nu hne p q
  · rw [fullBranchOfInterlaces_signature_eq_appendZeroWeight mu h]
    exact (finrank_harmonicYoung_appendZero_eq mu).symm

end HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange

namespace HigherYoungAllRankCanonicalBoxReverseRange

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisAssembly
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

theorem canonicalBoxReverseAxisRange_of_strongStable
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (hnstrong : 2 * (r + 1) + 5 ≤ n + 1)
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row) :
    CanonicalBoxReverseAxisRange
      a b hstable hgram low high row hrow := by
  let lam := boxSignature (m := m) a (n + 1) low
  let highLam := boxSignature (m := m) a (n + 1) high
  let mu := Weyl.flooredWeight b (n + 1)
  let hlow : Interlaces lam mu := boxSignature_interlaces a b hstable low
  let hhigh : Interlaces highLam mu :=
    boxSignature_interlaces a b hstable high
  let selected : FullBranchWeight lam := fullBranchOfInterlaces mu hlow
  have hdom : Antitone lam := hlow.antitone_ambient
  have hdeg : (∑ i, highLam i) = (∑ i, lam i) + 1 := by
    change (∑ i, boxSignature (m := m) a (n + 1) high i) =
      (∑ i, boxSignature (m := m) a (n + 1) low i) + 1
    rw [hrow]
    exact sum_raiseWeight (boxSignature (m := m) a (n + 1) low) row
  have hrange :
      LinearMap.range
        (canonicalBoxGelfandTsetlinFibre a b hstable hgram low).toLinearMap =
        LinearMap.range
          (canonicalFullBranchFibre lam hnstrong selected).toLinearMap := by
    change LinearMap.range
        (canonicalGelfandTsetlinFibre lam mu hlow (hgram low)).toLinearMap = _
    exact canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
      lam mu hlow hnstrong hdom (hgram low)
  intro p
  rw [hrange]
  apply canonicalFullBranch_mem_range_of_orthogonal_allRank
    lam hnstrong hdom
    (canonicalFullBranchFibre_orthogonal lam hnstrong) selected
  intro nu hnu q
  rw [boxAxis_succ_val_eq_basisFun]
  exact canonicalBranchProjectedLower_orthogonal_of_ne_selected
    lam highLam mu hlow hhigh hdeg row hnstrong nu hnu p q

end HigherYoungAllRankCanonicalBoxReverseRange

end

section


open scoped BigOperators InnerProductSpace

namespace HigherHarmonicYoung.AllRankActualFischerGramRecurrence

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalForwardAxisRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowBaseAxisChannel
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowUnconditionalBranch
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherRepresentationGraph

theorem canonicalGelfandTsetlinFischerGram_adjacent_of_projectedLower
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hdom : Antitone low)
    (hlowGram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) (raiseWeight low row) mu hhigh)
    (hexchange : ∀ p : HarmonicYoungSpace (n := n) mu,
      arbitraryRowAxialRaise low row (Fin.last n)
          (reverseInterlacingPolynomialSeed low mu p) -
        reverseInterlacingPolynomialSeed (raiseWeight low row) mu p ∈
          youngGramRadialIdeal (r + 1) (n + 1))
    (hcartan : ∀ p : HarmonicYoungSpace (n := n) mu,
      projectedCoordinateLower low (raiseWeight low row)
          (sum_raiseWeight low row) row
          (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
          (arbitraryRowSameAxisHarmonicRaise low hdom row (Fin.last n)
            (reverseInterlacingHarmonicBranch low mu hlow p)) =
        (arbitraryRowAxialLowerScalar low row *
          internalRowLowerGramScalar (raiseWeight low row) row *
          plusProbability (n + 1) low mu row) •
          reverseInterlacingHarmonicBranch low mu hlow p)
    (p : HarmonicYoungSpace (n := n) mu) (hp : p ≠ 0) :
    canonicalGelfandTsetlinFischerGram
        (raiseWeight low row) mu hhigh hhighGram =
      arbitraryRowAxialLowerScalar low row ^ 2 *
        internalRowLowerGramScalar (raiseWeight low row) row *
        canonicalGelfandTsetlinFischerGram low mu hlow hlowGram *
        plusProbability (n + 1) low mu row := by
  have hraise := arbitraryRowSameAxisHarmonicRaise_reverseBranch_eq_of_pathExchange
    low mu row hlow hhigh hdom 1 (fun p => by rw [one_smul]; exact hexchange p) p
  rw [one_smul] at hraise
  have hforward :=
    projectedCoordinateRaise_reverseInterlacingHarmonicBranch_eq_of_pathExchange
      low mu row hlow hhigh hdom 1 (fun p => by rw [one_smul]; exact hexchange p) p
  rw [mul_one] at hforward
  have hlower := hcartan p
  rw [hraise] at hlower
  have hactual := projectedCoordinateRaise_inner
    (raiseWeight low row) low (sum_raiseWeight low row) row
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
    (reverseInterlacingHarmonicBranch low mu hlow p)
    (reverseInterlacingHarmonicBranch
      (raiseWeight low row) mu hhigh p)
  rw [hforward, hlower] at hactual
  have hleft := real_inner_smul_left
    (reverseInterlacingHarmonicBranch
      (raiseWeight low row) mu hhigh p)
    (reverseInterlacingHarmonicBranch
      (raiseWeight low row) mu hhigh p)
    (arbitraryRowAxialLowerScalar low row)⁻¹
  have hright := real_inner_smul_right
    (reverseInterlacingHarmonicBranch low mu hlow p)
    (reverseInterlacingHarmonicBranch low mu hlow p)
    (arbitraryRowAxialLowerScalar low row *
      internalRowLowerGramScalar (raiseWeight low row) row *
      plusProbability (n + 1) low mu row)
  have hpairHigh := canonicalGelfandTsetlinFischerGram_inner
    (raiseWeight low row) mu hhigh hhighGram p p
  have hpairLow := canonicalGelfandTsetlinFischerGram_inner
    low mu hlow hlowGram p p
  have hscalar :
      (arbitraryRowAxialLowerScalar low row)⁻¹ *
          (canonicalGelfandTsetlinFischerGram
            (raiseWeight low row) mu hhigh hhighGram * ⟪p, p⟫_ℝ) =
        (arbitraryRowAxialLowerScalar low row *
          internalRowLowerGramScalar (raiseWeight low row) row *
          plusProbability (n + 1) low mu row) *
          (canonicalGelfandTsetlinFischerGram low mu hlow hlowGram *
            ⟪p, p⟫_ℝ) := by
    calc
      _ = (arbitraryRowAxialLowerScalar low row)⁻¹ *
          ⟪reverseInterlacingHarmonicBranch
              (raiseWeight low row) mu hhigh p,
            reverseInterlacingHarmonicBranch
              (raiseWeight low row) mu hhigh p⟫_ℝ :=
        congrArg ((arbitraryRowAxialLowerScalar low row)⁻¹ * ·)
          hpairHigh.symm
      _ = (arbitraryRowAxialLowerScalar low row *
            internalRowLowerGramScalar (raiseWeight low row) row *
            plusProbability (n + 1) low mu row) *
          ⟪reverseInterlacingHarmonicBranch low mu hlow p,
            reverseInterlacingHarmonicBranch low mu hlow p⟫_ℝ :=
        hleft.symm.trans (hactual.trans hright)
      _ = _ := congrArg
        ((arbitraryRowAxialLowerScalar low row *
          internalRowLowerGramScalar (raiseWeight low row) row *
          plusProbability (n + 1) low mu row) * ·) hpairLow
  have hpositive : 0 < ⟪p, p⟫_ℝ := real_inner_self_pos.mpr hp
  have hgap : arbitraryRowAxialLowerScalar low row ≠ 0 :=
    (arbitraryRowAxialLowerScalar_pos low row).ne'
  field_simp [hgap] at hscalar
  simpa only [mul_comm, mul_left_comm] using hscalar

end HigherHarmonicYoung.AllRankActualFischerGramRecurrence

end

section


open scoped BigOperators

namespace HigherYoungAllRankGTCharacteristicResidue

open MetricCodes.Spherical.HigherChannel

/-- The signed ambient characteristic used in the spherical-code argument. -/
def signedAmbientCharacteristic {r : ℕ}
    (L : Fin (r + 1) → ℝ) : Polynomial ℝ :=
  Lagrange.nodal
    (Finset.univ : Finset (Fin (r + 1) × Bool))
    (signedNode L)

theorem signedAmbientCharacteristic_derivative_eval_pos {r : ℕ}
    (L : Fin (r + 1) → ℝ) (row : Fin (r + 1)) :
    (signedAmbientCharacteristic L).derivative.eval (L row) =
      activeDenominator L row := by
  classical
  change Polynomial.eval (L row)
    (Polynomial.derivative
      (Lagrange.nodal
        (Finset.univ : Finset (Fin (r + 1) × Bool))
        (signedNode L))) = _
  have hnode : signedNode L (row, true) = L row := by
    simp only [signedNode, ↓reduceIte]
  rw [← hnode,
    Lagrange.eval_nodal_derivative_eval_node_eq
      (Finset.mem_univ (row, true)),
    Lagrange.eval_nodal]
  simpa only [hnode] using signedNode_denominator_pos_eq_active L row

theorem signedAmbientCharacteristic_derivative_eval_neg {r : ℕ}
    (L : Fin (r + 1) → ℝ) (row : Fin (r + 1)) :
    (signedAmbientCharacteristic L).derivative.eval (-L row) =
      -activeDenominator L row := by
  classical
  change Polynomial.eval (-L row)
    (Polynomial.derivative
      (Lagrange.nodal
        (Finset.univ : Finset (Fin (r + 1) × Bool))
        (signedNode L))) = _
  have hnode : signedNode L (row, false) = -L row := by
    simp only [signedNode, Bool.false_eq_true, ↓reduceIte]
  rw [← hnode,
    Lagrange.eval_nodal_derivative_eval_node_eq
      (Finset.mem_univ (row, false)),
    Lagrange.eval_nodal]
  simpa only [hnode] using signedNode_denominator_neg_eq_active L row

/-- The gt channel characteristic polynomial used in the spherical-code argument. -/
def gtChannelCharacteristicPolynomial {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) : Polynomial ℝ :=
  signedAmbientCharacteristic (ambientShift n lam)

theorem gtChannelCharacteristic_derivative_eval_pos {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    (gtChannelCharacteristicPolynomial n lam).derivative.eval
        (ambientShift n lam row) =
      activeDenominator (ambientShift n lam) row :=
  signedAmbientCharacteristic_derivative_eval_pos
    (ambientShift n lam) row

theorem gtChannelCharacteristic_derivative_eval_neg {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    (gtChannelCharacteristicPolynomial n lam).derivative.eval
        (-ambientShift n lam row) =
      -activeDenominator (ambientShift n lam) row :=
  signedAmbientCharacteristic_derivative_eval_neg
    (ambientShift n lam) row

theorem plusProbability_eq_gtCharacteristic_residue {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (mu : Fin r → ℕ)
    (row : Fin (r + 1)) :
    plusProbability n lam mu row =
      (channelNumeratorPolynomial (wallShift n r)
          (stabilizerShift n mu)).eval (ambientShift n lam row) /
        (gtChannelCharacteristicPolynomial n lam).derivative.eval
          (ambientShift n lam row) := by
  rw [channelNumeratorPolynomial_eval_pos,
    gtChannelCharacteristic_derivative_eval_pos]
  rfl

theorem FiniteInterlacing.gtChannelCharacteristic_derivative_eval_ne_zero
    {r n : ℕ} {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu)
    (row : Fin (r + 1)) (sign : Bool) :
    (gtChannelCharacteristicPolynomial n lam).derivative.eval
      (signedNode (ambientShift n lam) (row, sign)) ≠ 0 := by
  cases sign
  · simp only [signedNode, Bool.false_eq_true, ↓reduceIte,
      gtChannelCharacteristic_derivative_eval_neg, neg_ne_zero]
    exact h.activeDenominator_ne_zero row
  · simp only [signedNode, ↓reduceIte,
      gtChannelCharacteristic_derivative_eval_pos]
    exact h.activeDenominator_ne_zero row

theorem characteristicResidue_unique_of_resolvent
    {ι : Type*} [Fintype ι]
    (nodes : ι → ℝ) (hinjective : Function.Injective nodes)
    (numerator : Polynomial ℝ) (weight : ι → ℝ)
    (hresolvent : ∀ z : ℝ, (∀ i : ι, z ≠ nodes i) →
      numerator.eval z /
          (Lagrange.nodal (Finset.univ : Finset ι) nodes).eval z =
        ∑ i : ι, weight i / (z - nodes i))
    (i : ι) :
    weight i = numerator.eval (nodes i) /
      (Lagrange.nodal (Finset.univ : Finset ι) nodes).derivative.eval
        (nodes i) := by
  classical
  let characteristic : Polynomial ℝ :=
    Lagrange.nodal (Finset.univ : Finset ι) nodes
  have hderivative (j : ι) :
      characteristic.derivative.eval (nodes j) ≠ 0 := by
    intro hzero
    have hweight := Lagrange.nodalWeight_ne_zero
      (s := (Finset.univ : Finset ι)) (v := nodes)
      hinjective.injOn (Finset.mem_univ j)
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal
      (Finset.mem_univ j)] at hweight
    exact hweight (by simp only [hzero, inv_zero, characteristic])
  let values : ι → ℝ := fun j =>
    weight j * characteristic.derivative.eval (nodes j)
  let interpolation : Polynomial ℝ :=
    Lagrange.interpolate (Finset.univ : Finset ι) nodes values
  have hinterpolation (z : ℝ) (hz : ∀ j : ι, z ≠ nodes j) :
      interpolation.eval z / characteristic.eval z =
        ∑ j : ι, weight j / (z - nodes j) := by
    have hz' : ∀ j ∈ (Finset.univ : Finset ι), z ≠ nodes j := by
      intro j _
      exact hz j
    have hvalue := Lagrange.eval_interpolate_not_at_node
      (s := (Finset.univ : Finset ι)) (v := nodes) (x := z)
      values hz'
    have hnonzero : characteristic.eval z ≠ 0 :=
      Lagrange.eval_nodal_not_at_node hz'
    change
      (Lagrange.interpolate (Finset.univ : Finset ι) nodes values).eval z /
          characteristic.eval z = _
    rw [hvalue, mul_div_cancel_left₀ _ hnonzero]
    apply Finset.sum_congr rfl
    intro j _
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal
      (Finset.mem_univ j)]
    dsimp [values]
    change
      (characteristic.derivative.eval (nodes j))⁻¹ *
        (z - nodes j)⁻¹ *
        (weight j * characteristic.derivative.eval (nodes j)) =
        weight j / (z - nodes j)
    have hsub : z - nodes j ≠ 0 := sub_ne_zero.mpr (hz j)
    field_simp [hderivative j, hsub]
  have hpoly : numerator = interpolation := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine (Set.finite_range nodes).infinite_compl.mono ?_
    intro z hz
    have haway : ∀ j : ι, z ≠ nodes j := by
      intro j heq
      exact hz ⟨j, heq.symm⟩
    have hnonzero : characteristic.eval z ≠ 0 :=
      Lagrange.eval_nodal_not_at_node
        (fun j _ => haway j)
    exact (div_left_inj' hnonzero).mp
      ((hresolvent z haway).trans (hinterpolation z haway).symm)
  apply (eq_div_iff (hderivative i)).2
  calc
    weight i * characteristic.derivative.eval (nodes i) = values i := rfl
    _ = interpolation.eval (nodes i) :=
      (Lagrange.eval_interpolate_at_node values hinjective.injOn
        (Finset.mem_univ i)).symm
    _ = numerator.eval (nodes i) := by rw [hpoly]

theorem characteristicResidue_scaled_unique_of_resolvent
    {ι : Type*} [Fintype ι]
    (nodes : ι → ℝ) (hinjective : Function.Injective nodes)
    (numerator : Polynomial ℝ) (weight : ι → ℝ) (scale : ℝ)
    (hresolvent : ∀ z : ℝ, (∀ i : ι, z ≠ nodes i) →
      scale * numerator.eval z /
          (Lagrange.nodal (Finset.univ : Finset ι) nodes).eval z =
        ∑ i : ι, weight i / (z - nodes i))
    (i : ι) :
    weight i = scale * numerator.eval (nodes i) /
      (Lagrange.nodal (Finset.univ : Finset ι) nodes).derivative.eval
        (nodes i) := by
  have h := characteristicResidue_unique_of_resolvent
    nodes hinjective (Polynomial.C scale * numerator) weight (by
      intro z hz
      simpa only [Polynomial.eval_mul, Polynomial.eval_C] using hresolvent z hz) i
  simpa only [Polynomial.eval_mul, Polynomial.eval_C] using h

theorem FiniteInterlacing.gtChannel_positiveWeight_eq_mul_plusProbability_of_resolvent
    {r n : ℕ} {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu)
    (weight : Fin (r + 1) × Bool → ℝ) (scale : ℝ)
    (hresolvent : ∀ z : ℝ,
      (∀ i : Fin (r + 1) × Bool,
        z ≠ signedNode (ambientShift n lam) i) →
      scale * (channelNumeratorPolynomial (wallShift n r)
          (stabilizerShift n mu)).eval z /
          (gtChannelCharacteristicPolynomial n lam).eval z =
        ∑ i : Fin (r + 1) × Bool,
          weight i / (z - signedNode (ambientShift n lam) i))
    (row : Fin (r + 1)) :
    weight (row, true) = scale * plusProbability n lam mu row := by
  rw [plusProbability_eq_gtCharacteristic_residue lam mu row]
  have hresidue := characteristicResidue_scaled_unique_of_resolvent
    (signedNode (ambientShift n lam))
    (signedNode_injective h.ambientShift_pos
      h.ambientShift_strictAnti.injective)
    (channelNumeratorPolynomial (wallShift n r)
      (stabilizerShift n mu)) weight scale hresolvent (row, true)
  simpa only [gtChannelCharacteristicPolynomial, signedAmbientCharacteristic, div_eq_mul_inv,
    signedNode, ↓reduceIte, mul_assoc] using hresidue

end HigherYoungAllRankGTCharacteristicResidue

end

namespace HigherHarmonicYoung

section


open scoped BigOperators

namespace AllRankCartanCharacteristicInterpolation

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

private def cartanCharacteristicInterpolationProjector
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V]
    (nodes : ι → ℝ) (T : Module.End ℝ V) (i : ι) :
    Module.End ℝ V :=
  Polynomial.aeval T (Lagrange.basis Finset.univ nodes i)

theorem cartanCharacteristicInterpolationProjector_apply_of_eigenvector
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V]
    (nodes : ι → ℝ) (T : Module.End ℝ V)
    (hnode : Function.Injective nodes)
    (i j : ι) (x : V) (hx : T x = nodes j • x) :
    cartanCharacteristicInterpolationProjector nodes T i x =
      if i = j then x else 0 := by
  unfold cartanCharacteristicInterpolationProjector
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul hx]
  by_cases hij : i = j
  · subst j
    rw [Lagrange.eval_basis_self hnode.injOn (Finset.mem_univ i)]
    simp only [one_smul, ↓reduceIte]
  · rw [Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)]
    simp only [zero_smul, hij, ↓reduceIte]

theorem cartanCharacteristicInterpolationBasis_mul_eq_nodal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℝ) (i : ι) :
    (Polynomial.X - Polynomial.C (nodes i)) *
        Lagrange.basis Finset.univ nodes i =
      Polynomial.C (Lagrange.nodalWeight Finset.univ nodes i) *
        Lagrange.nodal Finset.univ nodes := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ i),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ i),
    Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i)]
  ring

theorem signedAmbientCharacteristicNodes_injective
    {r n : ℕ} {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) :
    Function.Injective (signedNode (ambientShift n lam)) :=
  signedNode_injective h.ambientShift_pos h.ambientShift_strictAnti.injective

end AllRankCartanCharacteristicInterpolation

end

section


open scoped BigOperators TensorProduct

namespace AllRankGTRelativeCasimirProjector

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

private def gtTensorCasimir {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    Module.End ℝ (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam) :=
  (2 : ℝ)⁻¹ • ∑ a : Fin n, ∑ b : Fin n,
    -((ClebschRotation.tensorAmbientRotation lam a b).comp
      (ClebschRotation.tensorAmbientRotation lam a b))

theorem gtTensorCasimir_intertwiner {r n : ℕ}
    (source target : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) source →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation source a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp A) :
    (gtTensorCasimir target).comp A =
      A.comp (youngAmbientCasimir source) := by
  apply LinearMap.ext
  intro p
  have hrot (a b : Fin n)
      (q : HarmonicYoungSpace (n := n) source) :
      ClebschRotation.tensorAmbientRotation target a b (A q) =
        A (youngAmbientRotation source a b q) :=
    (LinearMap.congr_fun (hA a b) q).symm
  simp only [LinearMap.comp_apply, gtTensorCasimir, youngAmbientCasimir,
    LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.neg_apply]
  simp_rw [hrot]
  simp only [Finset.sum_neg_distrib, smul_neg, map_neg, map_smul, map_sum]

theorem gtTensorCasimir_channel {r n : ℕ}
    (source target : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) source →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation source a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp A)
    (p : HarmonicYoungSpace (n := n) source) :
    gtTensorCasimir target (A p) =
      allRankCasimirEigenvalue n source • A p := by
  have h := LinearMap.congr_fun
    (gtTensorCasimir_intertwiner source target A hA) p
  rw [youngAmbientCasimir_allRank_eq_smul_id] at h
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_smul, LinearMap.id_coe,
    Pi.smul_apply, id_eq, map_smul] using h

/-- The gt relative casimir used in the spherical-code argument. -/
def gtRelativeCasimir {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    Module.End ℝ (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam) :=
  (2 : ℝ)⁻¹ • (gtTensorCasimir lam -
    (allRankCasimirEigenvalue n lam + 1) • LinearMap.id)

theorem gtRelativeCasimir_channel {r n : ℕ}
    (source target : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) source →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation source a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp A)
    (p : HarmonicYoungSpace (n := n) source) :
    gtRelativeCasimir target (A p) =
      ((allRankCasimirEigenvalue n source -
          allRankCasimirEigenvalue n target - 1) / 2) • A p := by
  simp only [gtRelativeCasimir, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply,
    gtTensorCasimir_channel source target A hA]
  rw [← sub_smul, smul_smul]
  congr 1
  ring

theorem gtRelativeCasimir_raise_eigenvalue {r n : ℕ}
    (target : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    (allRankCasimirEigenvalue n (raiseWeight target row) -
      allRankCasimirEigenvalue n target - 1) / 2 =
      ambientShift n target row := by
  change
    (adjacentCasimirEigenvalue n (raiseWeight target row) -
      adjacentCasimirEigenvalue n target - 1) / 2 = _
  rw [adjacentCasimirEigenvalue_raiseWeight]
  unfold ambientShift
  ring

theorem gtRelativeCasimir_lower_eigenvalue {r n : ℕ}
    (target source : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hsource : target = raiseWeight source row) :
    (allRankCasimirEigenvalue n source -
      allRankCasimirEigenvalue n target - 1) / 2 =
      -ambientShift n target row := by
  subst target
  change
    (adjacentCasimirEigenvalue n source -
      adjacentCasimirEigenvalue n (raiseWeight source row) - 1) / 2 = _
  rw [adjacentCasimirEigenvalue_raiseWeight]
  unfold ambientShift raiseWeight
  simp only [Function.update_self, Nat.cast_add, Nat.cast_one]
  ring

theorem gtRelativeCasimir_raise_channel {r n : ℕ}
    (target : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (A : HarmonicYoungSpace (n := n) (raiseWeight target row) →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation (raiseWeight target row) a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp A)
    (p : HarmonicYoungSpace (n := n) (raiseWeight target row)) :
    gtRelativeCasimir target (A p) =
      signedNode (ambientShift n target) (row, true) • A p := by
  rw [gtRelativeCasimir_channel _ _ A hA,
    gtRelativeCasimir_raise_eigenvalue]
  rfl

theorem gtRelativeCasimir_lower_channel {r n : ℕ}
    (target source : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hsource : target = raiseWeight source row)
    (A : HarmonicYoungSpace (n := n) source →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation source a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp A)
    (p : HarmonicYoungSpace (n := n) source) :
    gtRelativeCasimir target (A p) =
      signedNode (ambientShift n target) (row, false) • A p := by
  rw [gtRelativeCasimir_channel source target A hA,
    gtRelativeCasimir_lower_eigenvalue target source row hsource]
  rfl

/-- The gt characteristic projector used in the spherical-code argument. -/
def gtCharacteristicProjector {r n : ℕ}
    (target : Fin (r + 1) → ℕ) (z : Fin (r + 1) × Bool) :
    Module.End ℝ (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) target) :=
  Polynomial.aeval (gtRelativeCasimir target)
    (Lagrange.basis Finset.univ (signedNode (ambientShift n target)) z)

end AllRankGTRelativeCasimirProjector

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTCompressedResolvent

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

/-- The canonical gelfand tsetlin axis tensor used in the spherical-code argument. -/
def canonicalGelfandTsetlinAxisTensor
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (TensorProduct.mk ℝ (SpherePacking.Euclidean (n + 1))
      (HarmonicYoungSpace (n := n + 1) lam)
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).comp
    (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap

@[simp] theorem canonicalGelfandTsetlinAxisTensor_apply
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p : HarmonicYoungSpace (n := n) mu) :
    canonicalGelfandTsetlinAxisTensor lam mu h hgram p =
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ]
        canonicalGelfandTsetlinFibre lam mu h hgram p := rfl

theorem canonicalGelfandTsetlinAxisTensor_inner
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
      canonicalGelfandTsetlinAxisTensor lam mu h hgram q⟫_ℝ =
      ⟪p, q⟫_ℝ := by
  rw [canonicalGelfandTsetlinAxisTensor_apply,
    canonicalGelfandTsetlinAxisTensor_apply, TensorProduct.inner_tmul,
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).inner_eq_one,
    one_mul, (canonicalGelfandTsetlinFibre lam mu h hgram).inner_map_map]
  rfl

/-- The signed characteristic projector used in the spherical-code argument. -/
def signedCharacteristicProjector {r : ℕ}
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : Fin (r + 1) → ℝ) (T : Module.End ℝ V)
    (i : Fin (r + 1) × Bool) : Module.End ℝ V :=
  Polynomial.aeval T
    (Lagrange.basis Finset.univ (signedNode L) i)

theorem sum_signedCharacteristicProjector
    {r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : Fin (r + 1) → ℝ)
    (hL : Function.Injective (signedNode L))
    (T : Module.End ℝ V) :
    (∑ i : Fin (r + 1) × Bool,
      signedCharacteristicProjector L T i) = LinearMap.id := by
  classical
  unfold signedCharacteristicProjector
  rw [← map_sum]
  have hsum := Lagrange.sum_basis
    (s := (Finset.univ : Finset (Fin (r + 1) × Bool)))
    hL.injOn (Finset.univ_nonempty)
  rw [hsum]
  exact Polynomial.aeval_one T

theorem signedNode_sub_mul_basis
    {r : ℕ} (L : Fin (r + 1) → ℝ)
    (i : Fin (r + 1) × Bool) :
    (Polynomial.X - Polynomial.C (signedNode L i)) *
        Lagrange.basis Finset.univ (signedNode L) i =
      Polynomial.C
        (Lagrange.nodalWeight Finset.univ (signedNode L) i) *
        signedAmbientCharacteristic L := by
  exact cartanCharacteristicInterpolationBasis_mul_eq_nodal
    (signedNode L) i

theorem signedCharacteristicProjector_eigen_of_aeval_apply
    {r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : Fin (r + 1) → ℝ) (T : Module.End ℝ V)
    (i : Fin (r + 1) × Bool) (v : V)
    (hchar : Polynomial.aeval T (signedAmbientCharacteristic L) v = 0) :
    T (signedCharacteristicProjector L T i v) =
      signedNode L i • signedCharacteristicProjector L T i v := by
  have hzero := congrArg (Polynomial.aeval T)
    (signedNode_sub_mul_basis L i)
  simp only [map_mul, Polynomial.aeval_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at hzero
  have happly := LinearMap.congr_fun hzero v
  apply sub_eq_zero.mp
  simpa only [signedCharacteristicProjector, Module.algebraMap_end_eq_smul_id, Module.End.mul_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, Algebra.smul_mul_assoc,
      hchar, smul_zero] using
    happly

end AllRankGTCompressedResolvent

end

section


open scoped BigOperators TensorProduct

namespace AllRankGTRelativeCasimirPureAxis

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

private def gtEuclideanCasimir (n : ℕ) :
    Module.End ℝ (SpherePacking.Euclidean n) :=
  (2 : ℝ)⁻¹ • ∑ a : Fin n, ∑ b : Fin n,
    -((euclideanAmbientRotation a b).comp
      (euclideanAmbientRotation a b))

theorem gtEuclideanCasimir_eq_smul_id (n : ℕ) :
    gtEuclideanCasimir n = ((n : ℝ) - 1) • LinearMap.id := by
  apply LinearMap.ext
  intro v
  ext k
  simp only [gtEuclideanCasimir, Finset.sum_neg_distrib, smul_neg, LinearMap.neg_apply,
    LinearMap.smul_apply, LinearMap.coe_sum, LinearMap.coe_comp, Finset.sum_apply,
    Function.comp_apply, euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply,
    PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, PiLp.neg_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
    PiLp.ofLp_single, Pi.smul_apply, Pi.single_apply, Finset.sum_ite_irrel, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq, LinearMap.id_coe, id_eq]
  ring

theorem gtTensorCasimir_tmul {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    gtTensorCasimir lam (v ⊗ₜ[ℝ] p) =
      (2 : ℝ)⁻¹ • ∑ a : Fin n, ∑ b : Fin n,
        -(((euclideanAmbientRotation a b
              (euclideanAmbientRotation a b v)) ⊗ₜ[ℝ] p +
            (euclideanAmbientRotation a b v) ⊗ₜ[ℝ]
              (youngAmbientRotation lam a b p)) +
          ((euclideanAmbientRotation a b v) ⊗ₜ[ℝ]
              (youngAmbientRotation lam a b p) +
            v ⊗ₜ[ℝ]
              (youngAmbientRotation lam a b
                (youngAmbientRotation lam a b p)))) := by
  simp only [gtTensorCasimir, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.neg_apply, LinearMap.comp_apply]
  congr 1

/-- The gt mixed rotation operator used in the spherical-code argument. -/
def gtMixedRotationOperator {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Module.End ℝ (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam) :=
  ∑ a : Fin n, ∑ b : Fin n,
    TensorProduct.map (euclideanAmbientRotation a b)
      (youngAmbientRotation lam a b)

@[simp] theorem gtMixedRotationOperator_tmul {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    gtMixedRotationOperator lam (v ⊗ₜ[ℝ] p) =
      ∑ a : Fin n, ∑ b : Fin n,
        (euclideanAmbientRotation a b v) ⊗ₜ[ℝ]
          (youngAmbientRotation lam a b p) := by
  simp only [gtMixedRotationOperator, LinearMap.coe_sum, Finset.sum_apply, TensorProduct.map_tmul,
    euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply]

theorem gtEuclideanCasimir_tmul
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    (gtEuclideanCasimir n v) ⊗ₜ[ℝ] p =
      (2 : ℝ)⁻¹ • ∑ a : Fin n, ∑ b : Fin n,
        -((euclideanAmbientRotation a b
          (euclideanAmbientRotation a b v)) ⊗ₜ[ℝ] p) := by
  simp only [gtEuclideanCasimir, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.neg_apply, LinearMap.comp_apply]
  rw [← TensorProduct.smul_tmul']
  congr 1
  change
    ((TensorProduct.mk ℝ (SpherePacking.Euclidean n)
      (HarmonicYoungSpace (n := n) lam)).flip p)
        (∑ a : Fin n, ∑ b : Fin n,
          -(euclideanAmbientRotation a b
            (euclideanAmbientRotation a b v))) = _
  rw [map_sum]
  simp_rw [map_sum, map_neg]
  rfl

theorem gtYoungCasimir_tmul
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    v ⊗ₜ[ℝ] (youngAmbientCasimir lam p) =
      (2 : ℝ)⁻¹ • ∑ a : Fin n, ∑ b : Fin n,
        -(v ⊗ₜ[ℝ]
          (youngAmbientRotation lam a b
            (youngAmbientRotation lam a b p))) := by
  simp only [youngAmbientCasimir, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.neg_apply, LinearMap.comp_apply]
  rw [TensorProduct.tmul_smul]
  congr 1
  change
    ((TensorProduct.mk ℝ (SpherePacking.Euclidean n)
      (HarmonicYoungSpace (n := n) lam)) v)
        (∑ a : Fin n, ∑ b : Fin n,
          -(youngAmbientRotation lam a b
            (youngAmbientRotation lam a b p))) = _
  rw [map_sum]
  simp_rw [map_sum, map_neg]
  rfl

theorem gtTensorCasimir_tmul_eq_vector_add_young_sub_mixed
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    gtTensorCasimir lam (v ⊗ₜ[ℝ] p) =
      (gtEuclideanCasimir n v) ⊗ₜ[ℝ] p +
        v ⊗ₜ[ℝ] (youngAmbientCasimir lam p) -
          gtMixedRotationOperator lam (v ⊗ₜ[ℝ] p) := by
  rw [gtTensorCasimir_tmul, gtEuclideanCasimir_tmul,
    gtYoungCasimir_tmul, gtMixedRotationOperator_tmul]
  simp_rw [Finset.smul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  module

theorem gtRelativeCasimir_tmul_eq_scalar_sub_mixed
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    gtRelativeCasimir lam (v ⊗ₜ[ℝ] p) =
      (((n : ℝ) - 2) / 2) • (v ⊗ₜ[ℝ] p) -
        (2 : ℝ)⁻¹ • gtMixedRotationOperator lam (v ⊗ₜ[ℝ] p) := by
  simp only [gtRelativeCasimir, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply]
  rw [gtTensorCasimir_tmul_eq_vector_add_young_sub_mixed,
    gtEuclideanCasimir_eq_smul_id,
    youngAmbientCasimir_allRank_eq_smul_id]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  module

end AllRankGTRelativeCasimirPureAxis

namespace AllRankCartanCharacteristicProjector

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

/-- The all rank cartan characteristic projector used in the spherical-code argument. -/
def allRankCartanCharacteristicProjector {r n : ℕ}
    (target : Fin (r + 1) → ℕ) (channel : Fin (r + 1) × Bool) :
    Module.End ℝ (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) target) :=
  cartanCharacteristicInterpolationProjector
    (signedNode (ambientShift n target))
    (gtRelativeCasimir target) channel

theorem allRankCartanCharacteristicProjector_apply_eigenvector
    {r n : ℕ} (target : Fin (r + 1) → ℕ)
    (mu : Fin r → ℕ) (h : FiniteInterlacing n target mu)
    (selected actual : Fin (r + 1) × Bool)
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) target)
    (hx : gtRelativeCasimir target x =
      signedNode (ambientShift n target) actual • x) :
    allRankCartanCharacteristicProjector target selected x =
      if selected = actual then x else 0 := by
  exact cartanCharacteristicInterpolationProjector_apply_of_eigenvector
    (signedNode (ambientShift n target)) (gtRelativeCasimir target)
    (signedAmbientCharacteristicNodes_injective h)
    selected actual x hx

theorem allRankCartanCharacteristicProjector_raise_channel
    {r n : ℕ} (target : Fin (r + 1) → ℕ)
    (mu : Fin r → ℕ) (h : FiniteInterlacing n target mu)
    (selected : Fin (r + 1) × Bool) (row : Fin (r + 1))
    (A : HarmonicYoungSpace (n := n) (raiseWeight target row) →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation (raiseWeight target row) a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp A)
    (p : HarmonicYoungSpace (n := n) (raiseWeight target row)) :
    allRankCartanCharacteristicProjector target selected (A p) =
      if selected = (row, true) then A p else 0 := by
  apply allRankCartanCharacteristicProjector_apply_eigenvector
    target mu h selected (row, true) (A p)
  exact gtRelativeCasimir_raise_channel target row A hA p

theorem allRankCartanCharacteristicProjector_lower_channel
    {r n : ℕ} (target : Fin (r + 1) → ℕ)
    (mu : Fin r → ℕ) (h : FiniteInterlacing n target mu)
    (selected : Fin (r + 1) × Bool)
    (row : Fin (r + 1)) (source : Fin (r + 1) → ℕ)
    (hsource : target = raiseWeight source row)
    (A : HarmonicYoungSpace (n := n) source →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation source a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp A)
    (p : HarmonicYoungSpace (n := n) source) :
    allRankCartanCharacteristicProjector target selected (A p) =
      if selected = (row, false) then A p else 0 := by
  apply allRankCartanCharacteristicProjector_apply_eigenvector
    target mu h selected (row, false) (A p)
  exact gtRelativeCasimir_lower_channel target source row hsource A hA p

theorem allRankCartanCharacteristicProjector_youngClebschLower
    {r n : ℕ} (target : Fin (r + 1) → ℕ)
    (mu : Fin r → ℕ) (h : FiniteInterlacing n target mu)
    (selected : Fin (r + 1) × Bool) (row : Fin (r + 1))
    (p : HarmonicYoungSpace (n := n) (raiseWeight target row)) :
    allRankCartanCharacteristicProjector target selected
        (youngClebschLower target (raiseWeight target row)
          (sum_raiseWeight target row) row p) =
      if selected = (row, true) then
        youngClebschLower target (raiseWeight target row)
          (sum_raiseWeight target row) row p
      else 0 := by
  exact allRankCartanCharacteristicProjector_raise_channel
    target mu h selected row
    (youngClebschLower target (raiseWeight target row)
      (sum_raiseWeight target row) row)
    (fun a b => ClebschRotation.youngClebschLower_rotation_intertwine
      target (raiseWeight target row) (sum_raiseWeight target row) row a b)
    p

end AllRankCartanCharacteristicProjector

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTAxisCompressedCharacteristicMinor

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

/-- The gt axis compressed signed projector coefficient used in the spherical-code argument. -/
def gtAxisCompressedSignedProjectorCoefficient
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p q : HarmonicYoungSpace (n := n) mu)
    (channel : Fin (r + 2) × Bool) : ℝ :=
  ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
    signedCharacteristicProjector
      (ambientShift (n + 1) lam)
      (gtRelativeCasimir (n := n + 1) lam) channel
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram q)⟫_ℝ

/-- The gt axis compressed characteristic minor used in the spherical-code argument. -/
def gtAxisCompressedCharacteristicMinor
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p q : HarmonicYoungSpace (n := n) mu) : Polynomial ℝ :=
  Lagrange.interpolate Finset.univ
    (signedNode (ambientShift (n + 1) lam))
      (fun channel : Fin (r + 2) × Bool =>
        (gtChannelCharacteristicPolynomial (n + 1) lam).derivative.eval
            (signedNode (ambientShift (n + 1) lam) channel) *
          gtAxisCompressedSignedProjectorCoefficient
            lam mu h hgram p q channel)

theorem gtAxisCompressedCharacteristicMinor_eval_signedNode
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu)
    (channel : Fin (r + 2) × Bool) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (signedNode (ambientShift (n + 1) lam) channel) =
      (gtChannelCharacteristicPolynomial (n + 1) lam).derivative.eval
          (signedNode (ambientShift (n + 1) lam) channel) *
        gtAxisCompressedSignedProjectorCoefficient
          lam mu h hgram p q channel := by
  unfold gtAxisCompressedCharacteristicMinor
  exact Lagrange.eval_interpolate_at_node _
    (signedNode_injective hfinite.ambientShift_pos
      hfinite.ambientShift_strictAnti.injective).injOn
    (Finset.mem_univ channel)

theorem gtAxisCompressedCharacteristicMinor_degree_lt
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).degree <
      (Finset.univ : Finset (Fin (r + 2) × Bool)).card := by
  unfold gtAxisCompressedCharacteristicMinor
  exact Lagrange.degree_interpolate_lt _
    (signedNode_injective hfinite.ambientShift_pos
      hfinite.ambientShift_strictAnti.injective).injOn

theorem sum_gtAxisCompressedSignedProjectorCoefficient
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (∑ channel : Fin (r + 2) × Bool,
      gtAxisCompressedSignedProjectorCoefficient
        lam mu h hgram p q channel) = ⟪p, q⟫_ℝ := by
  classical
  unfold gtAxisCompressedSignedProjectorCoefficient
  calc
    (∑ channel : Fin (r + 2) × Bool,
      ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
        signedCharacteristicProjector
          (ambientShift (n + 1) lam)
          (gtRelativeCasimir (n := n + 1) lam) channel
            (canonicalGelfandTsetlinAxisTensor lam mu h hgram q)⟫_ℝ) =
      ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
        (∑ channel : Fin (r + 2) × Bool,
          signedCharacteristicProjector
            (ambientShift (n + 1) lam)
            (gtRelativeCasimir (n := n + 1) lam) channel
              (canonicalGelfandTsetlinAxisTensor lam mu h hgram q))⟫_ℝ := by
        exact (map_sum
          (innerₛₗ ℝ (canonicalGelfandTsetlinAxisTensor lam mu h hgram p))
          (fun channel : Fin (r + 2) × Bool =>
            signedCharacteristicProjector
              (ambientShift (n + 1) lam)
              (gtRelativeCasimir (n := n + 1) lam) channel
                (canonicalGelfandTsetlinAxisTensor lam mu h hgram q))
          Finset.univ).symm
    _ = ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
      (∑ channel : Fin (r + 2) × Bool,
        signedCharacteristicProjector
          (ambientShift (n + 1) lam)
          (gtRelativeCasimir (n := n + 1) lam) channel)
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram q)⟫_ℝ := by
          rw [LinearMap.sum_apply]
    _ = ⟪p, q⟫_ℝ := by
      rw [sum_signedCharacteristicProjector
        (ambientShift (n + 1) lam)
        (signedNode_injective hfinite.ambientShift_pos
          hfinite.ambientShift_strictAnti.injective), LinearMap.id_apply,
        canonicalGelfandTsetlinAxisTensor_inner]

theorem gtAxisCompressedCharacteristicMinor_eq_sum_nodal_erase
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      ∑ channel : Fin (r + 2) × Bool,
        Polynomial.C
          (gtAxisCompressedSignedProjectorCoefficient
            lam mu h hgram p q channel) *
          Lagrange.nodal
            ((Finset.univ : Finset (Fin (r + 2) × Bool)).erase channel)
            (signedNode (ambientShift (n + 1) lam)) := by
  classical
  unfold gtAxisCompressedCharacteristicMinor
  rw [Lagrange.interpolate_apply]
  apply Finset.sum_congr rfl
  intro channel _
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div
    (Finset.mem_univ channel),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ channel),
    Lagrange.nodalWeight_eq_eval_derivative_nodal
      (Finset.mem_univ channel)]
  have hderivative :
      (gtChannelCharacteristicPolynomial (n + 1) lam).derivative.eval
        (signedNode (ambientShift (n + 1) lam) channel) ≠ 0 := by
    rcases channel with ⟨row, sign⟩
    exact FiniteInterlacing.gtChannelCharacteristic_derivative_eval_ne_zero
      hfinite row sign
  have hcharacteristic :
      Lagrange.nodal
        (Finset.univ : Finset (Fin (r + 2) × Bool))
        (signedNode (ambientShift (n + 1) lam)) =
        gtChannelCharacteristicPolynomial (n + 1) lam := rfl
  rw [hcharacteristic]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  congr 1
  field_simp [hderivative]

theorem gtAxisCompressedCharacteristicMinor_div_characteristic
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu)
    (z : ℝ)
    (hz : ∀ channel : Fin (r + 2) × Bool,
      z ≠ signedNode (ambientShift (n + 1) lam) channel) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval z /
        (gtChannelCharacteristicPolynomial (n + 1) lam).eval z =
      ∑ channel : Fin (r + 2) × Bool,
        gtAxisCompressedSignedProjectorCoefficient
            lam mu h hgram p q channel /
          (z - signedNode (ambientShift (n + 1) lam) channel) := by
  classical
  let nodes : Fin (r + 2) × Bool → ℝ :=
    signedNode (ambientShift (n + 1) lam)
  let characteristic : Polynomial ℝ :=
    gtChannelCharacteristicPolynomial (n + 1) lam
  let weights : Fin (r + 2) × Bool → ℝ :=
    gtAxisCompressedSignedProjectorCoefficient lam mu h hgram p q
  have hnonzero : characteristic.eval z ≠ 0 := by
    apply Lagrange.eval_nodal_not_at_node
    intro channel _
    exact hz channel
  have hvalue := Lagrange.eval_interpolate_not_at_node
    (s := (Finset.univ : Finset (Fin (r + 2) × Bool)))
    (v := nodes) (x := z)
    (fun channel => characteristic.derivative.eval (nodes channel) *
      weights channel)
    (fun channel _ => hz channel)
  change
    (Lagrange.interpolate Finset.univ nodes
      (fun channel => characteristic.derivative.eval (nodes channel) *
        weights channel)).eval z / characteristic.eval z = _
  have hcharacteristic :
      Lagrange.nodal (Finset.univ : Finset (Fin (r + 2) × Bool)) nodes =
        characteristic := rfl
  rw [hvalue, hcharacteristic, mul_div_cancel_left₀ _ hnonzero]
  apply Finset.sum_congr rfl
  intro channel _
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal
    (Finset.mem_univ channel)]
  have hderivative : characteristic.derivative.eval (nodes channel) ≠ 0 := by
    rcases channel with ⟨row, sign⟩
    exact FiniteInterlacing.gtChannelCharacteristic_derivative_eval_ne_zero
      hfinite row sign
  change
    (characteristic.derivative.eval (nodes channel))⁻¹ *
        (z - nodes channel)⁻¹ *
        (characteristic.derivative.eval (nodes channel) *
          weights channel) =
      weights channel / (z - nodes channel)
  field_simp [hderivative, sub_ne_zero.mpr (hz channel)]

theorem gtAxisCompressedSignedProjectorCoefficient_pos_eq_plusProbability_of_minor
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hminor : gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu))
    (row : Fin (r + 2)) :
    gtAxisCompressedSignedProjectorCoefficient
        lam mu h hgram p q (row, true) =
      ⟪p, q⟫_ℝ * plusProbability (n + 1) lam mu row := by
  apply FiniteInterlacing.gtChannel_positiveWeight_eq_mul_plusProbability_of_resolvent
    hfinite
    (gtAxisCompressedSignedProjectorCoefficient lam mu h hgram p q)
    ⟪p, q⟫_ℝ
  · intro z hz
    rw [← gtAxisCompressedCharacteristicMinor_div_characteristic
      lam mu h hgram hfinite p q z hz, hminor]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]

end AllRankGTAxisCompressedCharacteristicMinor

namespace AllRankGTCartanHodgeSelector

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowBaseAxisChannel
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.UniversalBGGRootComplex
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.HigherRepresentationGraph

private def gtYoungAxisTensor {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (axis : SpherePacking.Euclidean n) :
    HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) lam) :=
  TensorProduct.mk ℝ (SpherePacking.Euclidean n)
    (HarmonicYoungSpace (n := n) lam) axis

@[simp] theorem gtYoungAxisTensor_apply {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (axis : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    gtYoungAxisTensor lam axis p = axis ⊗ₜ[ℝ] p := rfl

theorem youngClebschLower_adjoint_comp_gtYoungAxisTensor
    {r n : ℕ} (low high : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 1)) (axis : SpherePacking.Euclidean n) :
    (youngClebschLower low high hdeg row).adjoint.comp
        (gtYoungAxisTensor low axis) =
      projectedCoordinateRaise high low hdeg row axis := by
  apply LinearMap.ext
  intro p
  exact youngClebschLower_adjoint_tmul low high hdeg row axis p

theorem gtYoungAxisTensor_adjoint_comp_youngClebschLower
    {r n : ℕ} (low high : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 1)) (axis : SpherePacking.Euclidean n) :
    (gtYoungAxisTensor low axis).adjoint.comp
        (youngClebschLower low high hdeg row) =
      projectedCoordinateLower low high hdeg row axis := by
  apply LinearMap.ext
  intro p
  apply ext_inner_left ℝ
  intro q
  calc
    ⟪q, (gtYoungAxisTensor low axis).adjoint
        (youngClebschLower low high hdeg row p)⟫_ℝ =
      ⟪gtYoungAxisTensor low axis q,
        youngClebschLower low high hdeg row p⟫_ℝ :=
        LinearMap.adjoint_inner_right (gtYoungAxisTensor low axis)
          q (youngClebschLower low high hdeg row p)
    _ = ⟪(youngClebschLower low high hdeg row).adjoint
          (gtYoungAxisTensor low axis q), p⟫_ℝ :=
        (LinearMap.adjoint_inner_left
          (youngClebschLower low high hdeg row) p
            (gtYoungAxisTensor low axis q)).symm
    _ = ⟪projectedCoordinateRaise high low hdeg row axis q, p⟫_ℝ := by
        rw [gtYoungAxisTensor_apply,
          youngClebschLower_adjoint_tmul]
    _ = ⟪q, projectedCoordinateLower low high hdeg row axis p⟫_ℝ :=
        projectedCoordinateRaise_inner high low hdeg row axis q p

theorem arbitraryRowSameAxisHarmonicRaise_eq_lowerScalar_smul_projectedCoordinateRaise
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (hdom : Antitone low)
    (row : Fin (r + 1)) (k : Fin n)
    (p : HarmonicYoungSpace (n := n) low) :
    arbitraryRowSameAxisHarmonicRaise low hdom row k p =
      arbitraryRowAxialLowerScalar low row •
        projectedCoordinateRaise (raiseWeight low row) low
          (sum_raiseWeight low row) row
          (EuclideanSpace.basisFun (Fin n) ℝ k) p := by
  rw [projectedCoordinateRaise_eq_arbitraryRowSameAxisHarmonicRaise low hdom]
  simp only [smul_smul, ne_eq, (arbitraryRowAxialLowerScalar_pos low row).ne', not_false_eq_true,
    mul_inv_cancel₀, one_smul]

theorem projectedCoordinateLower_sameAxisHarmonicRaise_eq_axisClebschGram
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (hdom : Antitone low)
    (row : Fin (r + 1)) (k : Fin n)
    (p : HarmonicYoungSpace (n := n) low) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin n) ℝ k)
        (arbitraryRowSameAxisHarmonicRaise low hdom row k p) =
      arbitraryRowAxialLowerScalar low row •
        (gtYoungAxisTensor low (EuclideanSpace.basisFun (Fin n) ℝ k)).adjoint
          (((youngClebschLower low (raiseWeight low row)
              (sum_raiseWeight low row) row).comp
            (youngClebschLower low (raiseWeight low row)
              (sum_raiseWeight low row) row).adjoint)
            (gtYoungAxisTensor low (EuclideanSpace.basisFun (Fin n) ℝ k) p)) := by
  rw [arbitraryRowSameAxisHarmonicRaise_eq_lowerScalar_smul_projectedCoordinateRaise,
    map_smul]
  congr 1
  have hlower := LinearMap.congr_fun
    (gtYoungAxisTensor_adjoint_comp_youngClebschLower
      low (raiseWeight low row) (sum_raiseWeight low row) row
      (EuclideanSpace.basisFun (Fin n) ℝ k))
    (projectedCoordinateRaise (raiseWeight low row) low
      (sum_raiseWeight low row) row
      (EuclideanSpace.basisFun (Fin n) ℝ k) p)
  have hraise := LinearMap.congr_fun
    (youngClebschLower_adjoint_comp_gtYoungAxisTensor
      low (raiseWeight low row) (sum_raiseWeight low row) row
      (EuclideanSpace.basisFun (Fin n) ℝ k)) p
  simp only [LinearMap.comp_apply] at hraise
  simp only [LinearMap.comp_apply]
  rw [hraise]
  simpa only [LinearMap.comp_apply] using hlower.symm

/-- The gt selected row clebsch range projector used in the spherical-code argument. -/
def gtSelectedRowClebschRangeProjector {r n : ℕ}
    (low : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    Module.End ℝ (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) low) :=
  (internalRowLowerGramScalar (raiseWeight low row) row)⁻¹ •
    ((youngClebschLower low (raiseWeight low row)
      (sum_raiseWeight low row) row).comp
      (youngClebschLower low (raiseWeight low row)
        (sum_raiseWeight low row) row).adjoint)

theorem internalRowLowerGramScalar_raiseWeight_pos
    {r : ℕ} (low : Fin (r + 1) → ℕ)
    (hdom : Antitone low) (row : Fin (r + 1)) :
    0 < internalRowLowerGramScalar (raiseWeight low row) row := by
  apply internalRowLowerGramScalar_pos
  · simp only [raiseWeight, Function.update_self, lt_add_iff_pos_left, Order.lt_add_one_iff,
      zero_le]
  · exact raiseWeight_strictly_removable low hdom row

theorem youngClebschLower_raiseWeight_adjoint_comp_self
    {r n : ℕ} (low : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hhigh : Antitone (raiseWeight low row)) :
    (youngClebschLower (n := n) low (raiseWeight low row)
      (sum_raiseWeight low row) row).adjoint.comp
      (youngClebschLower low (raiseWeight low row)
        (sum_raiseWeight low row) row) =
      internalRowLowerGramScalar (raiseWeight low row) row • LinearMap.id := by
  apply SpherePacking.HarmonicCoordinateOperators.adjoint_comp_self_of_inner
  intro p q
  exact youngClebschLower_inner_of_raisedSignature
    (raiseWeight low row) low row
    (loweredInternalYoungWeight_raiseWeight low row).symm
    (by simp only [raiseWeight, Function.update_self, lt_add_iff_pos_left, Order.lt_add_one_iff,
          zero_le]) hhigh (sum_raiseWeight low row) p q

theorem gtSelectedRowClebschRangeProjector_youngClebschLower
    {r n : ℕ} (low : Fin (r + 1) → ℕ)
    (hdom : Antitone low) (row : Fin (r + 1))
    (hhigh : Antitone (raiseWeight low row))
    (p : HarmonicYoungSpace (n := n) (raiseWeight low row)) :
    gtSelectedRowClebschRangeProjector (n := n) low row
        (youngClebschLower low (raiseWeight low row)
          (sum_raiseWeight low row) row p) =
      youngClebschLower low (raiseWeight low row)
        (sum_raiseWeight low row) row p := by
  have hgram := LinearMap.congr_fun
    (youngClebschLower_raiseWeight_adjoint_comp_self
      (n := n) low row hhigh) p
  simp only [LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq] at hgram
  unfold gtSelectedRowClebschRangeProjector
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [hgram, map_smul, smul_smul]
  simp only [ne_eq, (internalRowLowerGramScalar_raiseWeight_pos low hdom row).ne',
    not_false_eq_true, inv_mul_cancel₀, youngClebschLower_apply, EuclideanSpace.basisFun_apply,
    one_smul]

theorem projectedCoordinateLower_sameAxisHarmonicRaise_eq_selectedClebschProjector_compression
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (hdom : Antitone low)
    (row : Fin (r + 1)) (k : Fin n)
    (p : HarmonicYoungSpace (n := n) low) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin n) ℝ k)
        (arbitraryRowSameAxisHarmonicRaise low hdom row k p) =
      (arbitraryRowAxialLowerScalar low row *
        internalRowLowerGramScalar (raiseWeight low row) row) •
          (gtYoungAxisTensor low (EuclideanSpace.basisFun (Fin n) ℝ k)).adjoint
            (gtSelectedRowClebschRangeProjector low row
              (gtYoungAxisTensor low (EuclideanSpace.basisFun (Fin n) ℝ k) p)) := by
  rw [projectedCoordinateLower_sameAxisHarmonicRaise_eq_axisClebschGram]
  unfold gtSelectedRowClebschRangeProjector
  simp only [LinearMap.smul_apply, map_smul, smul_smul]
  simp only [EuclideanSpace.basisFun_apply, gtYoungAxisTensor_apply, LinearMap.coe_comp,
    Function.comp_apply, youngClebschLower_apply, map_sum, ne_eq,
    (internalRowLowerGramScalar_raiseWeight_pos low hdom row).ne', not_false_eq_true,
    mul_inv_cancel_right₀]

theorem projectedCoordinateLower_sameAxisHarmonicRaise_eq_plusProbability_iff
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (mu : Fin r → ℕ)
    (hdom : Antitone low) (row : Fin (r + 1)) (k : Fin n)
    (p : HarmonicYoungSpace (n := n) low) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin n) ℝ k)
        (arbitraryRowSameAxisHarmonicRaise low hdom row k p) =
      (arbitraryRowAxialLowerScalar low row *
        internalRowLowerGramScalar (raiseWeight low row) row *
        plusProbability n low mu row) • p ↔
      (gtYoungAxisTensor low (EuclideanSpace.basisFun (Fin n) ℝ k)).adjoint
          (gtSelectedRowClebschRangeProjector low row
            (gtYoungAxisTensor low (EuclideanSpace.basisFun (Fin n) ℝ k) p)) =
        plusProbability n low mu row • p := by
  rw [projectedCoordinateLower_sameAxisHarmonicRaise_eq_selectedClebschProjector_compression]
  have hnonzero :
      arbitraryRowAxialLowerScalar low row *
        internalRowLowerGramScalar (raiseWeight low row) row ≠ 0 :=
    mul_ne_zero (arbitraryRowAxialLowerScalar_pos low row).ne'
      (internalRowLowerGramScalar_raiseWeight_pos low hdom row).ne'
  constructor
  · intro h
    apply smul_right_injective (HarmonicYoungSpace (n := n) low) hnonzero
    simpa only [EuclideanSpace.basisFun_apply, gtYoungAxisTensor_apply, mul_smul] using h
  · intro h
    rw [h, smul_smul]

theorem reverseInterlacing_projectedCoordinateLower_sameAxis_eq_plusProbability_iff
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hlow : Interlaces low mu)
    (hdom : Antitone low) (row : Fin (r + 2))
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (arbitraryRowSameAxisHarmonicRaise low hdom row (Fin.last n)
          (reverseInterlacingHarmonicBranch low mu hlow p)) =
      (arbitraryRowAxialLowerScalar low row *
        internalRowLowerGramScalar (raiseWeight low row) row *
        plusProbability (n + 1) low mu row) •
        reverseInterlacingHarmonicBranch low mu hlow p ↔
      (gtYoungAxisTensor low
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).adjoint
          (gtSelectedRowClebschRangeProjector low row
            (gtYoungAxisTensor low
              (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
                (reverseInterlacingHarmonicBranch low mu hlow p))) =
        plusProbability (n + 1) low mu row •
          reverseInterlacingHarmonicBranch low mu hlow p :=
  projectedCoordinateLower_sameAxisHarmonicRaise_eq_plusProbability_iff
    low mu hdom row (Fin.last n)
      (reverseInterlacingHarmonicBranch low mu hlow p)

theorem canonicalGelfandTsetlinFibre_selectedClebschCompression_iff_reverse
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hlow : Interlaces low mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (row : Fin (r + 2)) (p : HarmonicYoungSpace (n := n) mu) :
    (gtYoungAxisTensor low
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).adjoint
        (gtSelectedRowClebschRangeProjector low row
          (gtYoungAxisTensor low
            (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
              (canonicalGelfandTsetlinFibre low mu hlow hgram p))) =
      plusProbability (n + 1) low mu row •
        canonicalGelfandTsetlinFibre low mu hlow hgram p ↔
    (gtYoungAxisTensor low
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).adjoint
        (gtSelectedRowClebschRangeProjector low row
          (gtYoungAxisTensor low
            (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
              (reverseInterlacingHarmonicBranch low mu hlow p))) =
      plusProbability (n + 1) low mu row •
        reverseInterlacingHarmonicBranch low mu hlow p := by
  have hscalar := (canonicalGelfandTsetlinFibre_phase_pos
    low mu hlow hgram).ne'
  simp only [canonicalGelfandTsetlinFibre_apply, map_smul, smul_smul]
  rw [mul_comm (plusProbability (n + 1) low mu row), mul_smul,
    smul_right_inj hscalar]

theorem gtSelectedRowClebschRangeProjector_axisCompression_mem_reverseBranch_range
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hforward : ∀ p : HarmonicYoungSpace (n := n) mu,
      projectedCoordinateRaise (raiseWeight low row) low
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (reverseInterlacingHarmonicBranch low mu hlow p) ∈
      LinearMap.range
        (reverseInterlacingHarmonicBranch (raiseWeight low row) mu hhigh))
    (hreverse : ∀ p : HarmonicYoungSpace (n := n) mu,
      projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (reverseInterlacingHarmonicBranch
          (raiseWeight low row) mu hhigh p) ∈
      LinearMap.range (reverseInterlacingHarmonicBranch low mu hlow))
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtYoungAxisTensor low
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).adjoint
        (gtSelectedRowClebschRangeProjector low row
          (gtYoungAxisTensor low
            (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
              (reverseInterlacingHarmonicBranch low mu hlow p))) ∈
      LinearMap.range (reverseInterlacingHarmonicBranch low mu hlow) := by
  obtain ⟨q, hq⟩ := hforward p
  unfold gtSelectedRowClebschRangeProjector
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
  apply Submodule.smul_mem
    (LinearMap.range (reverseInterlacingHarmonicBranch low mu hlow))
  have hraise := LinearMap.congr_fun
    (youngClebschLower_adjoint_comp_gtYoungAxisTensor
      low (raiseWeight low row) (sum_raiseWeight low row) row
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)))
    (reverseInterlacingHarmonicBranch low mu hlow p)
  simp only [LinearMap.comp_apply] at hraise
  rw [hraise, ← hq]
  have hlower := LinearMap.congr_fun
    (gtYoungAxisTensor_adjoint_comp_youngClebschLower
      low (raiseWeight low row) (sum_raiseWeight low row) row
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)))
    (reverseInterlacingHarmonicBranch (raiseWeight low row) mu hhigh q)
  simp only [LinearMap.comp_apply] at hlower
  rw [hlower]
  exact hreverse q

theorem gtSelectedRowClebschRangeProjector_axisCompression_mem_canonicalFibre_range
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hforward : ∀ p : HarmonicYoungSpace (n := n) mu,
      projectedCoordinateRaise (raiseWeight low row) low
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (reverseInterlacingHarmonicBranch low mu hlow p) ∈
      LinearMap.range
        (reverseInterlacingHarmonicBranch (raiseWeight low row) mu hhigh))
    (hreverse : ∀ p : HarmonicYoungSpace (n := n) mu,
      projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (reverseInterlacingHarmonicBranch
          (raiseWeight low row) mu hhigh p) ∈
      LinearMap.range (reverseInterlacingHarmonicBranch low mu hlow))
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtYoungAxisTensor low
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).adjoint
        (gtSelectedRowClebschRangeProjector low row
          (gtYoungAxisTensor low
            (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
              (canonicalGelfandTsetlinFibre low mu hlow hgram p))) ∈
      LinearMap.range (canonicalGelfandTsetlinFibre low mu hlow hgram).toLinearMap := by
  obtain ⟨q, hq⟩ :=
    gtSelectedRowClebschRangeProjector_axisCompression_mem_reverseBranch_range
      low mu row hlow hhigh hforward hreverse p
  refine ⟨q, ?_⟩
  simp only [canonicalGelfandTsetlinFibre_apply, map_smul]
  change
    (Real.sqrt (canonicalGelfandTsetlinFischerGram
      low mu hlow hgram))⁻¹ •
        reverseInterlacingHarmonicBranch low mu hlow q = _
  rw [hq]

end AllRankGTCartanHodgeSelector

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTSelectedProjectorCompression

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

private def gtSelectedProjectorCompression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (row : Fin (r + 2)) :
    Module.End ℝ (HarmonicYoungSpace (n := n) mu) :=
  (canonicalGelfandTsetlinAxisTensor lam mu h hgram).adjoint.comp
    ((signedCharacteristicProjector
      (ambientShift (n + 1) lam)
      (gtRelativeCasimir (n := n + 1) lam) (row, true)).comp
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram))

theorem gtSelectedProjectorCompression_inner
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (row : Fin (r + 2))
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪p, gtSelectedProjectorCompression lam mu h hgram row q⟫_ℝ =
      gtAxisCompressedSignedProjectorCoefficient
        lam mu h hgram p q (row, true) := by
  unfold gtSelectedProjectorCompression
    gtAxisCompressedSignedProjectorCoefficient
  simp only [LinearMap.comp_apply]
  exact LinearMap.adjoint_inner_right
    (canonicalGelfandTsetlinAxisTensor lam mu h hgram) p _

theorem gtSelectedProjectorCompression_inner_eq_plusProbability_of_minor
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 2))
    (p q : HarmonicYoungSpace (n := n) mu)
    (hminor : gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu)) :
    ⟪p, gtSelectedProjectorCompression lam mu h hgram row q⟫_ℝ =
      ⟪p, q⟫_ℝ * plusProbability (n + 1) lam mu row := by
  rw [gtSelectedProjectorCompression_inner]
  exact gtAxisCompressedSignedProjectorCoefficient_pos_eq_plusProbability_of_minor
    lam mu h hgram hfinite p q hminor row

theorem gtSelectedProjectorCompression_eq_plusProbability_of_minor
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 2))
    (hminor : ∀ p q : HarmonicYoungSpace (n := n) mu,
      gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
        Polynomial.C ⟪p, q⟫_ℝ *
          channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
            (stabilizerShift (n + 1) mu)) :
    gtSelectedProjectorCompression lam mu h hgram row =
      plusProbability (n + 1) lam mu row • LinearMap.id := by
  apply LinearMap.ext
  intro q
  apply ext_inner_left ℝ
  intro p
  calc
    ⟪p, gtSelectedProjectorCompression lam mu h hgram row q⟫_ℝ =
        ⟪p, q⟫_ℝ * plusProbability (n + 1) lam mu row :=
      gtSelectedProjectorCompression_inner_eq_plusProbability_of_minor
        lam mu h hgram hfinite row p q (hminor p q)
    _ = ⟪p, (plusProbability (n + 1) lam mu row • LinearMap.id) q⟫_ℝ := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [young_inner_eq_polynomialInner mu p q,
        young_inner_eq_polynomialInner mu p
          (plusProbability (n + 1) lam mu row • q)]
      change
        SpherePacking.Fischer.polynomialInner ((r + 1) * n)
            (p : PolynomialSpace r n) (q : PolynomialSpace r n) *
              plusProbability (n + 1) lam mu row =
          SpherePacking.Fischer.polynomialInner ((r + 1) * n)
            (p : PolynomialSpace r n)
            (plusProbability (n + 1) lam mu row •
              (q : PolynomialSpace r n))
      rw [SpherePacking.Fischer.polynomialInner_smul_right]
      ring

private def gtSelectedPhysicalAxisCompression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (row : Fin (r + 2)) :
    Module.End ℝ (HarmonicYoungSpace (n := n + 1) lam) :=
  (gtYoungAxisTensor lam
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).adjoint.comp
      ((gtSelectedRowClebschRangeProjector lam row).comp
        (gtYoungAxisTensor lam
          (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))))

theorem gtSelectedProjectorCompression_eq_fibre_adjoint_physical_of_selected
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (row : Fin (r + 2))
    (hselected : ∀ p : HarmonicYoungSpace (n := n) mu,
      allRankCartanCharacteristicProjector lam (row, true)
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) =
        gtSelectedRowClebschRangeProjector lam row
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)) :
    gtSelectedProjectorCompression lam mu h hgram row =
      (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap.adjoint.comp
        ((gtSelectedPhysicalAxisCompression lam row).comp
          (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap) := by
  let axis := EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)
  let F := canonicalGelfandTsetlinFibre lam mu h hgram
  let A := gtYoungAxisTensor lam axis
  have haxis : canonicalGelfandTsetlinAxisTensor lam mu h hgram =
      A.comp F.toLinearMap := rfl
  apply LinearMap.ext
  intro p
  unfold gtSelectedProjectorCompression gtSelectedPhysicalAxisCompression
  rw [haxis, LinearMap.adjoint_comp]
  simp only [LinearMap.comp_apply]
  change
    F.adjoint (A.adjoint
      (allRankCartanCharacteristicProjector lam (row, true)
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram p))) =
      F.adjoint (A.adjoint
        (gtSelectedRowClebschRangeProjector lam row
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)))
  rw [hselected p]

theorem gtSelectedPhysicalAxisCompression_fibre_eq_plusProbability_of_minor_and_range
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 2))
    (hminor : ∀ p q : HarmonicYoungSpace (n := n) mu,
      gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
        Polynomial.C ⟪p, q⟫_ℝ *
          channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
            (stabilizerShift (n + 1) mu))
    (hselected : ∀ p : HarmonicYoungSpace (n := n) mu,
      allRankCartanCharacteristicProjector lam (row, true)
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) =
        gtSelectedRowClebschRangeProjector lam row
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram p))
    (hrange : ∀ p : HarmonicYoungSpace (n := n) mu,
      gtSelectedPhysicalAxisCompression lam row
          (canonicalGelfandTsetlinFibre lam mu h hgram p) ∈
        LinearMap.range
          (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtSelectedPhysicalAxisCompression lam row
        (canonicalGelfandTsetlinFibre lam mu h hgram p) =
      plusProbability (n + 1) lam mu row •
        canonicalGelfandTsetlinFibre lam mu h hgram p := by
  let F := canonicalGelfandTsetlinFibre lam mu h hgram
  obtain ⟨q, hq⟩ := hrange p
  have hcompressed := LinearMap.congr_fun
    (gtSelectedProjectorCompression_eq_plusProbability_of_minor
      lam mu h hgram hfinite row hminor) p
  rw [gtSelectedProjectorCompression_eq_fibre_adjoint_physical_of_selected
    lam mu h hgram row hselected] at hcompressed
  simp only [LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hcompressed
  change F.adjoint (gtSelectedPhysicalAxisCompression lam row (F p)) =
    plusProbability (n + 1) lam mu row • p at hcompressed
  rw [← hq] at hcompressed
  have hleft := LinearMap.congr_fun F.adjoint_comp_self' q
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hleft
  rw [hleft] at hcompressed
  calc
    gtSelectedPhysicalAxisCompression lam row (F p) = F q := hq.symm
    _ = F (plusProbability (n + 1) lam mu row • p) := by
      rw [hcompressed]
    _ = plusProbability (n + 1) lam mu row • F p := F.map_smul _ _

theorem reverseInterlacing_projectedCoordinateLower_sameAxis_eq_plusProbability_of_minor
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hlow : Interlaces low mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hfinite : FiniteInterlacing (n + 1) low mu)
    (hdom : Antitone low) (row : Fin (r + 2))
    (hminor : ∀ p q : HarmonicYoungSpace (n := n) mu,
      gtAxisCompressedCharacteristicMinor low mu hlow hgram p q =
        Polynomial.C ⟪p, q⟫_ℝ *
          channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
            (stabilizerShift (n + 1) mu))
    (hselected : ∀ p : HarmonicYoungSpace (n := n) mu,
      allRankCartanCharacteristicProjector low (row, true)
          (canonicalGelfandTsetlinAxisTensor low mu hlow hgram p) =
        gtSelectedRowClebschRangeProjector low row
          (canonicalGelfandTsetlinAxisTensor low mu hlow hgram p))
    (hrange : ∀ p : HarmonicYoungSpace (n := n) mu,
      gtSelectedPhysicalAxisCompression low row
          (canonicalGelfandTsetlinFibre low mu hlow hgram p) ∈
        LinearMap.range
          (canonicalGelfandTsetlinFibre low mu hlow hgram).toLinearMap)
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (arbitraryRowSameAxisHarmonicRaise low hdom row (Fin.last n)
          (reverseInterlacingHarmonicBranch low mu hlow p)) =
      (arbitraryRowAxialLowerScalar low row *
        internalRowLowerGramScalar (raiseWeight low row) row *
        plusProbability (n + 1) low mu row) •
        reverseInterlacingHarmonicBranch low mu hlow p := by
  apply (reverseInterlacing_projectedCoordinateLower_sameAxis_eq_plusProbability_iff
    low mu hlow hdom row p).2
  apply (canonicalGelfandTsetlinFibre_selectedClebschCompression_iff_reverse
    low mu hlow hgram row p).1
  simpa only [gtSelectedPhysicalAxisCompression, LinearMap.comp_apply] using
    gtSelectedPhysicalAxisCompression_fibre_eq_plusProbability_of_minor_and_range
      low mu hlow hgram hfinite row hminor hselected hrange p

end AllRankGTSelectedProjectorCompression

end

section


open scoped BigOperators InnerProductSpace

namespace AllRankGTSelectedPhysicalAxisRange

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalForwardAxisRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem projectedCoordinateLower_canonicalGelfandTsetlinFibre_mem_range_of_strongStable
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hnstrong : 2 * (r + 1) + 5 ≤ n + 1)
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hlowGram : PositiveGelfandTsetlinFischerGram
      (n := n) low mu hlow)
    (hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) (raiseWeight low row) mu hhigh)
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (canonicalGelfandTsetlinFibre
          (raiseWeight low row) mu hhigh hhighGram p) ∈
      LinearMap.range
        (canonicalGelfandTsetlinFibre low mu hlow hlowGram).toLinearMap := by
  let selected : FullBranchWeight low := fullBranchOfInterlaces mu hlow
  have hdom : Antitone low := hlow.antitone_ambient
  rw [canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
    low mu hlow hnstrong hdom hlowGram]
  apply canonicalFullBranch_mem_range_of_orthogonal_allRank
    low hnstrong hdom
    (canonicalFullBranchFibre_orthogonal low hnstrong) selected
  intro nu hnu q
  exact canonicalBranchProjectedLower_orthogonal_of_ne_selected
    low (raiseWeight low row) mu hlow hhigh
    (sum_raiseWeight low row) row hnstrong nu hnu p q

theorem projectedCoordinateLower_reverseInterlacingHarmonicBranch_mem_range_of_strongStable
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hnstrong : 2 * (r + 1) + 5 ≤ n + 1)
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (reverseInterlacingHarmonicBranch
          (raiseWeight low row) mu hhigh p) ∈
      LinearMap.range
        (reverseInterlacingHarmonicBranch low mu hlow) := by
  have hstable : 2 * (r + 1) + 2 ≤ n := by omega
  let glow : PositiveGelfandTsetlinFischerGram
    (n := n) low mu hlow :=
      positiveGelfandTsetlinFischerGram hstable low mu hlow
  let ghigh : PositiveGelfandTsetlinFischerGram
    (n := n) (raiseWeight low row) mu hhigh :=
      positiveGelfandTsetlinFischerGram hstable
        (raiseWeight low row) mu hhigh
  let highScale : ℝ := Real.sqrt
    (canonicalGelfandTsetlinFischerGram
      (raiseWeight low row) mu hhigh ghigh)
  have hscale : highScale ≠ 0 :=
    (Real.sqrt_pos.mpr
      (canonicalGelfandTsetlinFischerGram_pos
        (raiseWeight low row) mu hhigh ghigh)).ne'
  have hinput :
      canonicalGelfandTsetlinFibre
          (raiseWeight low row) mu hhigh ghigh
          (highScale • p) =
        reverseInterlacingHarmonicBranch
          (raiseWeight low row) mu hhigh p := by
    simp only [map_smul, canonicalGelfandTsetlinFibre_apply, smul_smul, ne_eq, hscale,
      not_false_eq_true, mul_inv_cancel₀, one_smul, highScale]
  have hrange :=
    projectedCoordinateLower_canonicalGelfandTsetlinFibre_mem_range_of_strongStable
      low mu row hnstrong hlow hhigh glow ghigh (highScale • p)
  rw [hinput] at hrange
  obtain ⟨q, hq⟩ := hrange
  refine ⟨(Real.sqrt
    (canonicalGelfandTsetlinFischerGram low mu hlow glow))⁻¹ • q, ?_⟩
  simpa only [map_smul, EuclideanSpace.basisFun_apply, LinearIsometry.coe_toLinearMap,
    canonicalGelfandTsetlinFibre_apply] using hq

theorem projectedCoordinateRaise_reverseInterlacingHarmonicBranch_mem_range
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateRaise (raiseWeight low row) low
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (reverseInterlacingHarmonicBranch low mu hlow p) ∈
      LinearMap.range
        (reverseInterlacingHarmonicBranch
          (raiseWeight low row) mu hhigh) := by
  apply projectedCoordinateRaise_reverseInterlacingHarmonicBranch_mem_range_of_pathExchange
    low mu row hlow hhigh hlow.antitone_ambient 1
  · intro q
    rw [reverseInterlacingPolynomialSeed_adjacent_raise_of_diamond
      (dominantSameAxisDiamond_allRows (r + 1) (n + 1)) hlow row q]
    simp only [one_smul, sub_self, zero_mem]

theorem gtSelectedPhysicalAxisCompression_canonicalFibre_mem_range_of_strongStable
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hnstrong : 2 * (r + 1) + 5 ≤ n + 1)
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hgram : PositiveGelfandTsetlinFischerGram
      (n := n) low mu hlow)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtSelectedPhysicalAxisCompression low row
        (canonicalGelfandTsetlinFibre low mu hlow hgram p) ∈
      LinearMap.range
        (canonicalGelfandTsetlinFibre low mu hlow hgram).toLinearMap := by
  exact
    gtSelectedRowClebschRangeProjector_axisCompression_mem_canonicalFibre_range
      low mu row hlow hhigh hgram
      (projectedCoordinateRaise_reverseInterlacingHarmonicBranch_mem_range
        low mu row hlow hhigh)
      (projectedCoordinateLower_reverseInterlacingHarmonicBranch_mem_range_of_strongStable
        low mu row hnstrong hlow hhigh) p

theorem
  reverseInterlacing_projectedCoordinateLower_sameAxis_eq_plusProbability_of_minor_of_strongStable
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hnstrong : 2 * (r + 1) + 5 ≤ n + 1)
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hgram : PositiveGelfandTsetlinFischerGram
      (n := n) low mu hlow)
    (hfinite : FiniteInterlacing (n + 1) low mu)
    (hdom : Antitone low)
    (hminor : ∀ p q : HarmonicYoungSpace (n := n) mu,
      gtAxisCompressedCharacteristicMinor low mu hlow hgram p q =
        Polynomial.C ⟪p, q⟫_ℝ *
          channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
            (HigherChannel.stabilizerShift (n + 1) mu))
    (hselected : ∀ p : HarmonicYoungSpace (n := n) mu,
      allRankCartanCharacteristicProjector low (row, true)
          (canonicalGelfandTsetlinAxisTensor low mu hlow hgram p) =
        gtSelectedRowClebschRangeProjector low row
          (canonicalGelfandTsetlinAxisTensor low mu hlow hgram p))
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (arbitraryRowSameAxisHarmonicRaise low hdom row (Fin.last n)
          (reverseInterlacingHarmonicBranch low mu hlow p)) =
      (arbitraryRowAxialLowerScalar low row *
        internalRowLowerGramScalar (raiseWeight low row) row *
        plusProbability (n + 1) low mu row) •
        reverseInterlacingHarmonicBranch low mu hlow p := by
  exact reverseInterlacing_projectedCoordinateLower_sameAxis_eq_plusProbability_of_minor
    low mu hlow hgram hfinite hdom row hminor hselected
    (gtSelectedPhysicalAxisCompression_canonicalFibre_mem_range_of_strongStable
      low mu row hnstrong hlow hhigh hgram) p

end AllRankGTSelectedPhysicalAxisRange

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankCanonicalBoxFischerRecurrenceOfCharacteristicMinor

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalAxisRange
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisAssembly

theorem canonicalBoxAdjacentFischerRecurrence_of_minor_of_strongStable
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row)
    (hnstrong : 2 * (r + 1) + 5 ≤ n + 1)
    (hminor : ∀ p q : HarmonicYoungSpace (n := n)
        (Weyl.flooredWeight b (n + 1)),
      gtAxisCompressedCharacteristicMinor
          (boxSignature (m := m) a (n + 1) low)
          (Weyl.flooredWeight b (n + 1))
          (boxSignature_interlaces a b hstable low)
          (hgram low) p q =
        Polynomial.C ⟪p, q⟫_ℝ *
          channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
            (HigherChannel.stabilizerShift (n + 1)
              (Weyl.flooredWeight b (n + 1))))
    (hselected : ∀ p : HarmonicYoungSpace (n := n)
        (Weyl.flooredWeight b (n + 1)),
      allRankCartanCharacteristicProjector
          (boxSignature (m := m) a (n + 1) low) (row, true)
          (canonicalGelfandTsetlinAxisTensor
            (boxSignature (m := m) a (n + 1) low)
            (Weyl.flooredWeight b (n + 1))
            (boxSignature_interlaces a b hstable low) (hgram low) p) =
        gtSelectedRowClebschRangeProjector
          (boxSignature (m := m) a (n + 1) low) row
          (canonicalGelfandTsetlinAxisTensor
            (boxSignature (m := m) a (n + 1) low)
            (Weyl.flooredWeight b (n + 1))
            (boxSignature_interlaces a b hstable low) (hgram low) p)) :
    CanonicalBoxAdjacentFischerRecurrence
      a b hstable hgram low high row := by
  let lam := boxSignature (m := m) a (n + 1) low
  let mu := Weyl.flooredWeight b (n + 1)
  have hfinite : FiniteInterlacing (n + 1) lam mu := by
    exact hstable
      ((Fintype.equivFin (RectangularVertices.Vertex (r + 1) m)).symm low)
  have hn : 2 * (r + 1) ≤ n := by
    have hbound := box_stableRange a b hstable
    omega
  let hlow : Interlaces lam mu := boxSignature_interlaces a b hstable low
  have hhigh : Interlaces (raiseWeight lam row) mu := by
    rw [← hrow]
    exact boxSignature_interlaces a b hstable high
  have hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) (raiseWeight lam row) mu hhigh := by
    simpa only [lam, mu, hrow] using (hgram high)
  obtain ⟨p, hp⟩ :=
    DeterminantVectors.exists_nonzero_harmonicYoung_of_antitone
      hn mu (interlaces_antitone_stabilizer hlow)
  have hprobability :=
    reverseInterlacing_projectedCoordinateLower_sameAxis_eq_plusProbability_of_minor_of_strongStable
      lam mu row hnstrong hlow hhigh (hgram low) hfinite
      hlow.antitone_ambient hminor hselected
  have hresult :=
    AllRankActualFischerGramRecurrence.canonicalGelfandTsetlinFischerGram_adjacent_of_projectedLower
      lam mu row hlow hhigh hlow.antitone_ambient
      (hgram low) hhighGram
      (fun q => by
        rw
          [reverseInterlacingPolynomialSeed_adjacent_raise_of_diamond
          (dominantSameAxisDiamond_allRows (r + 1) (n + 1)) hlow row q,
          sub_self]
        exact (youngGramRadialIdeal (r + 1) (n + 1)).zero_mem)
      hprobability
      p hp
  simpa only [CanonicalBoxAdjacentFischerRecurrence, lam, mu, hrow]
    using hresult

end AllRankCanonicalBoxFischerRecurrenceOfCharacteristicMinor

end

end HigherHarmonicYoung

section


namespace HigherYoungAllRankOrthogonalTensorPieriCoefficient

open MetricCodes.Spherical.HigherWeylBinomialDeterminant

private def orthogonalTensorPieriCoefficient (n : ℕ) (z j : ℤ) : ℤ :=
  orthogonalCompleteSymmetricCoefficient n (z + j) -
    orthogonalCompleteSymmetricCoefficient n (z - j - 2)

theorem orthogonalTensorPieriCoefficient_row_shift
    (n : ℕ) (z j : ℤ) :
    orthogonalTensorPieriCoefficient n (z + 1) j +
        orthogonalTensorPieriCoefficient n (z - 1) j =
      orthogonalTensorPieriCoefficient n z (j + 1) +
        orthogonalTensorPieriCoefficient n z (j - 1) := by
  unfold orthogonalTensorPieriCoefficient
  have h₁ : z + 1 + j = z + (j + 1) := by ring
  have h₂ : z + 1 - j - 2 = z - (j - 1) - 2 := by ring
  have h₃ : z - 1 + j = z + (j - 1) := by ring
  have h₄ : z - 1 - j - 2 = z - (j + 1) - 2 := by ring
  rw [h₁, h₂, h₃, h₄]
  ring

@[simp] theorem orthogonalTensorPieriCoefficient_neg_one
    (n : ℕ) (z : ℤ) :
    orthogonalTensorPieriCoefficient n z (-1) = 0 := by
  unfold orthogonalTensorPieriCoefficient
  have h : z - (-1) - 2 = z + (-1) := by ring
  rw [h]
  ring

theorem orthogonalTensorPieriCoefficient_padded_zero_lt
    (n r j : ℕ) (hj : j < r) :
    orthogonalTensorPieriCoefficient n (-(r : ℤ)) (j : ℤ) = 0 := by
  unfold orthogonalTensorPieriCoefficient
  have hj' : (j : ℤ) < (r : ℤ) := by exact_mod_cast hj
  have hfirst : -(r : ℤ) + (j : ℤ) < 0 := by omega
  have hsecond : -(r : ℤ) - (j : ℤ) - 2 < 0 := by omega
  rw [orthogonalCompleteSymmetricCoefficient_of_neg n hfirst,
    orthogonalCompleteSymmetricCoefficient_of_neg n hsecond]
  rfl

@[simp] theorem orthogonalTensorPieriCoefficient_padded_zero_self
    (n r : ℕ) :
    orthogonalTensorPieriCoefficient n (-(r : ℤ)) (r : ℤ) = 1 := by
  unfold orthogonalTensorPieriCoefficient
  have hfirst : -(r : ℤ) + (r : ℤ) = 0 := by ring
  have hsecond : -(r : ℤ) - (r : ℤ) - 2 < 0 := by omega
  rw [hfirst, orthogonalCompleteSymmetricCoefficient_of_neg n hsecond]
  simp only [orthogonalCompleteSymmetricCoefficient, Std.le_refl, ↓reduceIte, Int.toNat_zero,
    add_zero, Nat.choose_zero_right, Nat.cast_one, sub_zero]

theorem orthogonalTensorPieriCoefficient_padded_zero_succ
    (n r : ℕ) :
    orthogonalTensorPieriCoefficient n (-(r : ℤ)) ((r + 1 : ℕ) : ℤ) =
      (n : ℤ) := by
  unfold orthogonalTensorPieriCoefficient
  have hfirst : -(r : ℤ) + ((r + 1 : ℕ) : ℤ) = 1 := by omega
  have hsecond : -(r : ℤ) - ((r + 1 : ℕ) : ℤ) - 2 < 0 := by omega
  rw [hfirst, orthogonalCompleteSymmetricCoefficient_of_neg n hsecond]
  norm_num [orthogonalCompleteSymmetricCoefficient, Nat.choose_one_right]

theorem orthogonalTensorPieriCoefficient_padded_zero_fin
    (n r : ℕ) (j : Fin (r + 1)) :
    orthogonalTensorPieriCoefficient n (-(r : ℤ)) (j.val : ℤ) =
      if j.val = r then 1 else 0 := by
  split_ifs with h
  · rw [h, orthogonalTensorPieriCoefficient_padded_zero_self]
  · apply orthogonalTensorPieriCoefficient_padded_zero_lt n r j.val
    have hj := j.isLt
    omega

theorem orthogonalTensorPieriCoefficient_padded_zero_pred_fin
    (n r : ℕ) (j : Fin (r + 1)) :
    orthogonalTensorPieriCoefficient n (-(r : ℤ) - 1) (j.val : ℤ) = 0 := by
  unfold orthogonalTensorPieriCoefficient
  have hj := j.isLt
  have hfirst : -(r : ℤ) - 1 + (j.val : ℤ) < 0 := by omega
  have hsecond : -(r : ℤ) - 1 - (j.val : ℤ) - 2 < 0 := by omega
  rw [orthogonalCompleteSymmetricCoefficient_of_neg n hfirst,
    orthogonalCompleteSymmetricCoefficient_of_neg n hsecond]
  rfl

theorem orthogonalTensorPieriCoefficient_eq_matrix
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) :
    orthogonalJacobiTrudiMatrix n lam i j =
      orthogonalTensorPieriCoefficient n
        ((lam i : ℤ) - (i.val : ℤ)) (j.val : ℤ) := by
  simp only [orthogonalJacobiTrudiMatrix, orthogonalTensorPieriCoefficient]

theorem orthogonalTensorPieriCoefficient_raise_row
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) :
    orthogonalJacobiTrudiMatrix n
        (Function.update lam i (lam i + 1)) i j =
      orthogonalTensorPieriCoefficient n
        (((lam i : ℤ) - (i.val : ℤ)) + 1) (j.val : ℤ) := by
  rw [orthogonalTensorPieriCoefficient_eq_matrix]
  simp only [Function.update_self, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

theorem orthogonalTensorPieriCoefficient_lower_row
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) (hi : 0 < lam i) :
    orthogonalJacobiTrudiMatrix n
        (Function.update lam i (lam i - 1)) i j =
      orthogonalTensorPieriCoefficient n
        (((lam i : ℤ) - (i.val : ℤ)) - 1) (j.val : ℤ) := by
  rw [orthogonalTensorPieriCoefficient_eq_matrix]
  simp only [Function.update_self]
  rw [Nat.cast_sub (show 1 ≤ lam i by omega)]
  norm_num
  congr 1
  ring

theorem orthogonalTensorPieriCoefficient_update_row_ne
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (i ell j : Fin (r + 1)) (m : ℕ) (hi : i ≠ ell) :
    orthogonalJacobiTrudiMatrix n (Function.update lam ell m) i j =
      orthogonalJacobiTrudiMatrix n lam i j := by
  simp only [orthogonalJacobiTrudiMatrix, Function.update_of_ne hi]

end HigherYoungAllRankOrthogonalTensorPieriCoefficient

namespace HigherYoungAllRankOrthogonalTensorPieriInvalidRows

open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient

theorem orthogonalJacobiTrudiMatrix_raiseWeight_eq_updateRow
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :
    orthogonalJacobiTrudiMatrix n (raiseWeight lam i) =
      (orthogonalJacobiTrudiMatrix n lam).updateRow i
        (fun j => orthogonalTensorPieriCoefficient n
          (((lam i : ℤ) - (i.val : ℤ)) + 1) (j.val : ℤ)) := by
  ext k j
  by_cases hk : k = i
  · subst k
    rw [Matrix.updateRow_self]
    exact orthogonalTensorPieriCoefficient_raise_row n lam i j
  · rw [Matrix.updateRow_ne hk]
    exact orthogonalTensorPieriCoefficient_update_row_ne n lam k i j (lam i + 1) hk

theorem orthogonalJacobiTrudiMatrix_lowered_eq_updateRow
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (i : Fin (r + 1)) (hi : 0 < lam i) :
    orthogonalJacobiTrudiMatrix n (loweredInternalYoungWeight lam i) =
      (orthogonalJacobiTrudiMatrix n lam).updateRow i
        (fun j => orthogonalTensorPieriCoefficient n
          (((lam i : ℤ) - (i.val : ℤ)) - 1) (j.val : ℤ)) := by
  ext k j
  by_cases hk : k = i
  · subst k
    rw [Matrix.updateRow_self]
    exact orthogonalTensorPieriCoefficient_lower_row n lam i j hi
  · rw [Matrix.updateRow_ne hk]
    exact orthogonalTensorPieriCoefficient_update_row_ne n lam k i j (lam i - 1) hk

theorem orthogonalJacobiTrudiDimension_raiseWeight_eq_zero_of_not_antitone
    {r : ℕ} (n : ℕ) {lam : Fin (r + 1) → ℕ}
    (hlam : Antitone lam) (i : Fin (r + 1))
    (hbad : ¬ Antitone (raiseWeight lam i)) :
    orthogonalJacobiTrudiDimension n (raiseWeight lam i) = 0 := by
  classical
  have hviol : ∃ j : Fin r,
      raiseWeight lam i j.castSucc < raiseWeight lam i j.succ := by
    have hnot : ¬ ∀ j : Fin r,
        raiseWeight lam i j.succ ≤ raiseWeight lam i j.castSucc := by
      intro h
      exact hbad (Fin.antitone_iff_succ_le.mpr h)
    push Not at hnot
    exact hnot
  obtain ⟨j, hlt⟩ := hviol
  have hdom := hlam (Fin.castSucc_le_succ j)
  have hji : j.succ = i := by
    by_contra hsucc
    by_cases hcast : j.castSucc = i
    · subst i
      simp only [raiseWeight, Function.update_self, ne_eq, hsucc, not_false_eq_true,
        Function.update_of_ne] at hlt
      omega
    · simp only [raiseWeight, ne_eq, hcast, not_false_eq_true, Function.update_of_ne, hsucc] at hlt
      omega
  subst i
  have hne : j.castSucc ≠ j.succ := ne_of_lt Fin.castSucc_lt_succ
  have heq : lam j.castSucc = lam j.succ := by
    simp only [raiseWeight, ne_eq, hne, not_false_eq_true, Function.update_of_ne,
      Function.update_self, Order.lt_add_one_iff] at hlt
    omega
  unfold orthogonalJacobiTrudiDimension
  apply Matrix.det_zero_of_row_eq hne
  funext k
  rw [orthogonalTensorPieriCoefficient_eq_matrix,
    orthogonalTensorPieriCoefficient_eq_matrix]
  have hshift :
      ((raiseWeight lam j.succ j.castSucc : ℤ) -
          (j.castSucc.val : ℤ)) =
        ((raiseWeight lam j.succ j.succ : ℤ) -
          (j.succ.val : ℤ)) := by
    simp only [raiseWeight, ne_eq, hne, not_false_eq_true, Function.update_of_ne, heq,
      Fin.val_castSucc, Function.update_self, Nat.cast_add, Nat.cast_one, Fin.val_succ,
      add_sub_add_right_eq_sub]
  rw [hshift]

theorem orthogonalJacobiTrudiDimension_lowered_eq_zero_of_not_antitone
    {r : ℕ} (n : ℕ) {lam : Fin (r + 1) → ℕ}
    (hlam : Antitone lam) (i : Fin (r + 1))
    (hbad : ¬ Antitone (loweredInternalYoungWeight lam i)) :
    orthogonalJacobiTrudiDimension n (loweredInternalYoungWeight lam i) = 0 := by
  classical
  have hviol : ∃ j : Fin r,
      loweredInternalYoungWeight lam i j.castSucc <
        loweredInternalYoungWeight lam i j.succ := by
    have hnot : ¬ ∀ j : Fin r,
        loweredInternalYoungWeight lam i j.succ ≤
          loweredInternalYoungWeight lam i j.castSucc := by
      intro h
      exact hbad (Fin.antitone_iff_succ_le.mpr h)
    push Not at hnot
    exact hnot
  obtain ⟨j, hlt⟩ := hviol
  have hdom := hlam (Fin.castSucc_le_succ j)
  have hji : j.castSucc = i := by
    by_contra hcast
    by_cases hsucc : j.succ = i
    · subst i
      simp only [loweredInternalYoungWeight, ne_eq, hcast, not_false_eq_true, Function.update_of_ne,
        Function.update_self] at hlt
      omega
    · simp only [loweredInternalYoungWeight, ne_eq, hcast, not_false_eq_true, Function.update_of_ne,
        hsucc] at hlt
      omega
  subst i
  have hne : j.castSucc ≠ j.succ := ne_of_lt Fin.castSucc_lt_succ
  have hne' : j.succ ≠ j.castSucc := Ne.symm hne
  have hpos : 0 < lam j.castSucc := by
    simp only [loweredInternalYoungWeight, Function.update_self, ne_eq, hne', not_false_eq_true,
      Function.update_of_ne] at hlt
    omega
  have heq : lam j.castSucc = lam j.succ := by
    simp only [loweredInternalYoungWeight, Function.update_self, ne_eq, hne', not_false_eq_true,
      Function.update_of_ne] at hlt
    omega
  unfold orthogonalJacobiTrudiDimension
  apply Matrix.det_zero_of_row_eq hne
  funext k
  rw [orthogonalTensorPieriCoefficient_eq_matrix,
    orthogonalTensorPieriCoefficient_eq_matrix]
  have hshift :
      ((loweredInternalYoungWeight lam j.castSucc j.castSucc : ℤ) -
          (j.castSucc.val : ℤ)) =
        ((loweredInternalYoungWeight lam j.castSucc j.succ : ℤ) -
          (j.succ.val : ℤ)) := by
    simp only [loweredInternalYoungWeight, Function.update_self, Fin.val_castSucc, ne_eq, hne',
      not_false_eq_true, Function.update_of_ne, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    rw [Nat.cast_sub (show 1 ≤ lam j.castSucc by omega)]
    push_cast
    have heq' : (lam j.castSucc : ℤ) = (lam j.succ : ℤ) := by
      exact_mod_cast heq
    omega
  rw [hshift]

theorem orthogonalJacobiTrudiMatrix_signed_lower_update_det_eq_zero
    {r : ℕ} (n : ℕ) {lam : Fin (r + 1) → ℕ}
    (hlam : Antitone lam) (i : Fin (r + 1)) (hi : lam i = 0) :
    ((orthogonalJacobiTrudiMatrix n lam).updateRow i
      (fun j => orthogonalTensorPieriCoefficient n
        (((lam i : ℤ) - (i.val : ℤ)) - 1) (j.val : ℤ))).det = 0 := by
  classical
  by_cases hilast : i = Fin.last r
  · subst i
    apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last r)
    intro j
    rw [Matrix.updateRow_self]
    simpa only [hi, CharP.cast_eq_zero, Fin.val_last, zero_sub] using
      orthogonalTensorPieriCoefficient_padded_zero_pred_fin n r j
  · have hilt : i < Fin.last r := Fin.lt_last_iff_ne_last.mpr hilast
    let next : Fin (r + 1) :=
      ⟨i.val + 1, by have h := hilt; omega⟩
    have hinext : i < next := by
      change i.val < i.val + 1
      omega
    have hnext : lam next = 0 := by
      have h := hlam hinext.le
      omega
    apply Matrix.det_zero_of_row_eq (ne_of_lt hinext)
    funext j
    rw [Matrix.updateRow_self,
      Matrix.updateRow_ne (Ne.symm (ne_of_lt hinext)),
      orthogonalTensorPieriCoefficient_eq_matrix]
    congr 1
    simp only [hi, CharP.cast_eq_zero, zero_sub, hnext, Nat.cast_add, Nat.cast_one, neg_add_rev,
      Int.reduceNeg, next]
    ring

end HigherYoungAllRankOrthogonalTensorPieriInvalidRows

end

section


open scoped BigOperators

namespace HigherYoungAllRankOrthogonalTensorPieriRowFiltering

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

private def orthogonalTensorPieriRaiseRow {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1)) : Fin (r + 1) → ℤ :=
  fun j => orthogonalTensorPieriCoefficient n
    (((lam i : ℤ) - (i.val : ℤ)) + 1) (j.val : ℤ)

private def orthogonalTensorPieriLowerRow {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1)) : Fin (r + 1) → ℤ :=
  fun j => orthogonalTensorPieriCoefficient n
    (((lam i : ℤ) - (i.val : ℤ)) - 1) (j.val : ℤ)

theorem sum_eq_subtype_of_eq_zero
    {ι A : Type*} [Fintype ι] [AddCommMonoid A]
    (P : ι → Prop) [DecidablePred P]
    (f : ι → A) (hzero : ∀ i : ι, ¬ P i → f i = 0) :
    (∑ i : ι, f i) = ∑ i : {i : ι // P i}, f i.val := by
  classical
  calc
    (∑ i : ι, f i) = ∑ i : ι, if P i then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P i
      · simp only [hi, ↓reduceIte]
      · simp only [hzero i hi, hi, ↓reduceIte]
    _ = ∑ i : {i : ι // P i}, f i.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter P) (by simp only [Finset.mem_filter,
                                                            Finset.mem_univ, true_and,
                                                              implies_true]) f

theorem sum_det_updateRow_raise_eq_dominant_subtype
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (hlam : Antitone lam) :
    (∑ i : Fin (r + 1),
      ((orthogonalJacobiTrudiMatrix n lam).updateRow i
        (orthogonalTensorPieriRaiseRow n lam i)).det) =
      ∑ i : {i : Fin (r + 1) // Antitone (raiseWeight lam i)},
        orthogonalJacobiTrudiDimension n (raiseWeight lam i.val) := by
  classical
  have hterm (i : Fin (r + 1)) :
      ((orthogonalJacobiTrudiMatrix n lam).updateRow i
        (orthogonalTensorPieriRaiseRow n lam i)).det =
        orthogonalJacobiTrudiDimension n (raiseWeight lam i) := by
    unfold orthogonalJacobiTrudiDimension orthogonalTensorPieriRaiseRow
    rw [orthogonalJacobiTrudiMatrix_raiseWeight_eq_updateRow]
  calc
    (∑ i : Fin (r + 1),
      ((orthogonalJacobiTrudiMatrix n lam).updateRow i
        (orthogonalTensorPieriRaiseRow n lam i)).det) =
        ∑ i : Fin (r + 1),
          orthogonalJacobiTrudiDimension n (raiseWeight lam i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hterm i
    _ = ∑ i : {i : Fin (r + 1) // Antitone (raiseWeight lam i)},
          orthogonalJacobiTrudiDimension n (raiseWeight lam i.val) := by
            apply sum_eq_subtype_of_eq_zero
              (fun i : Fin (r + 1) => Antitone (raiseWeight lam i))
            intro i hbad
            exact orthogonalJacobiTrudiDimension_raiseWeight_eq_zero_of_not_antitone
              n hlam i hbad

theorem sum_det_updateRow_lower_eq_positive_dominant_subtype
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (hlam : Antitone lam) :
    (∑ i : Fin (r + 1),
      ((orthogonalJacobiTrudiMatrix n lam).updateRow i
        (orthogonalTensorPieriLowerRow n lam i)).det) =
      ∑ i : {i : Fin (r + 1) //
        0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)},
        orthogonalJacobiTrudiDimension n
          (loweredInternalYoungWeight lam i.val) := by
  classical
  let P : Fin (r + 1) → Prop :=
    fun i => 0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)
  let f : Fin (r + 1) → ℤ := fun i =>
    ((orthogonalJacobiTrudiMatrix n lam).updateRow i
      (orthogonalTensorPieriLowerRow n lam i)).det
  have hpositive (i : Fin (r + 1)) (hi : 0 < lam i) :
      f i = orthogonalJacobiTrudiDimension n
        (loweredInternalYoungWeight lam i) := by
    dsimp [f]
    unfold orthogonalJacobiTrudiDimension orthogonalTensorPieriLowerRow
    rw [orthogonalJacobiTrudiMatrix_lowered_eq_updateRow n lam i hi]
  have hzero (i : Fin (r + 1)) (hi : ¬ P i) : f i = 0 := by
    by_cases hpos : 0 < lam i
    · have hbad : ¬ Antitone (loweredInternalYoungWeight lam i) := by
        intro hdom
        exact hi ⟨hpos, hdom⟩
      rw [hpositive i hpos]
      exact orthogonalJacobiTrudiDimension_lowered_eq_zero_of_not_antitone
        n hlam i hbad
    · have hweight : lam i = 0 := by omega
      exact orthogonalJacobiTrudiMatrix_signed_lower_update_det_eq_zero
        n hlam i hweight
  change (∑ i : Fin (r + 1), f i) =
    ∑ i : {i : Fin (r + 1) // P i},
      orthogonalJacobiTrudiDimension n
        (loweredInternalYoungWeight lam i.val)
  rw [sum_eq_subtype_of_eq_zero P f hzero]
  apply Finset.sum_congr rfl
  intro i _
  exact hpositive i.val i.property.1

end HigherYoungAllRankOrthogonalTensorPieriRowFiltering

end

section


namespace HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

/-- The padded pieri raise row used in the spherical-code argument. -/
def PaddedPieriRaiseRow {r : ℕ} (lam : Fin (r + 1) → ℕ) :=
  {i : Fin (r + 1) // Antitone (raiseWeight lam i)}

noncomputable instance paddedPieriRaiseRowFintype {r : ℕ}
    (lam : Fin (r + 1) → ℕ) : Fintype (PaddedPieriRaiseRow lam) := by
  classical
  unfold PaddedPieriRaiseRow
  infer_instance

/-- The padded pieri lower row used in the spherical-code argument. -/
def PaddedPieriLowerRow {r : ℕ} (lam : Fin (r + 1) → ℕ) :=
  {i : Fin (r + 1) //
    0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)}

noncomputable instance paddedPieriLowerRowFintype {r : ℕ}
    (lam : Fin (r + 1) → ℕ) : Fintype (PaddedPieriLowerRow lam) := by
  classical
  unfold PaddedPieriLowerRow
  infer_instance

/-- The padded pieri channel used in the spherical-code argument. -/
def PaddedPieriChannel {r : ℕ} (lam : Fin (r + 1) → ℕ) :=
  PaddedPieriRaiseRow lam ⊕ PaddedPieriLowerRow lam

noncomputable instance paddedPieriChannelFintype {r : ℕ}
    (lam : Fin (r + 1) → ℕ) : Fintype (PaddedPieriChannel lam) := by
  unfold PaddedPieriChannel
  infer_instance

/-- The padded pieri source used in the spherical-code argument. -/
def paddedPieriSource {r : ℕ} (lam : Fin (r + 1) → ℕ) :
    PaddedPieriChannel lam → Fin (r + 1) → ℕ :=
  Sum.elim
    (fun i : PaddedPieriRaiseRow lam => raiseWeight lam i.val)
    (fun i : PaddedPieriLowerRow lam =>
      loweredInternalYoungWeight lam i.val)

@[simp] theorem paddedPieriSource_inr {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (i : PaddedPieriLowerRow lam) :
    paddedPieriSource lam (Sum.inr i) =
      loweredInternalYoungWeight lam i.val := rfl

theorem raiseWeight_row_injective {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Function.Injective (raiseWeight lam) := by
  intro i j hij
  by_contra hne
  have hcoordinate := congrFun hij i
  simp only [raiseWeight, Function.update_self, ne_eq, hne, not_false_eq_true,
    Function.update_of_ne, Nat.add_eq_left, one_ne_zero] at hcoordinate

theorem loweredInternalYoungWeight_row_injective_of_positive {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    {i j : Fin (r + 1)} (hi : 0 < lam i)
    (hij : loweredInternalYoungWeight lam i =
      loweredInternalYoungWeight lam j) : i = j := by
  by_contra hne
  have hcoordinate := congrFun hij i
  simp only [loweredInternalYoungWeight, Function.update_self, ne_eq, hne, not_false_eq_true,
    Function.update_of_ne] at hcoordinate
  omega

theorem raiseWeight_ne_loweredInternalYoungWeight {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (i j : Fin (r + 1)) :
    raiseWeight lam i ≠ loweredInternalYoungWeight lam j := by
  intro hij
  have hcoordinate := congrFun hij i
  by_cases heq : i = j
  · subst j
    simp only [raiseWeight, Function.update_self, loweredInternalYoungWeight] at hcoordinate
    omega
  · simp only [raiseWeight, Function.update_self, loweredInternalYoungWeight, ne_eq, heq,
      not_false_eq_true, Function.update_of_ne, Nat.add_eq_left, one_ne_zero] at hcoordinate

theorem paddedPieriSource_injective {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Function.Injective (paddedPieriSource lam) := by
  intro i j hij
  cases i with
  | inl a =>
      cases j with
      | inl b =>
          have hab : a.val = b.val :=
            raiseWeight_row_injective lam hij
          exact congrArg Sum.inl (Subtype.ext hab)
      | inr b =>
          exact False.elim
            (raiseWeight_ne_loweredInternalYoungWeight lam a.val b.val hij)
  | inr a =>
      cases j with
      | inl b =>
          exact False.elim
            (raiseWeight_ne_loweredInternalYoungWeight lam b.val a.val
              hij.symm)
      | inr b =>
          have hab : a.val = b.val :=
            loweredInternalYoungWeight_row_injective_of_positive lam
              a.property.1 hij
          exact congrArg Sum.inr (Subtype.ext hab)

theorem raiseWeight_loweredInternalYoungWeight {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1))
    (hi : 0 < lam i) :
    raiseWeight (loweredInternalYoungWeight lam i) i = lam := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [raiseWeight, loweredInternalYoungWeight, Function.update_self]
    omega
  · simp only [raiseWeight, loweredInternalYoungWeight, Function.update_self, ne_eq, hji,
      not_false_eq_true, Function.update_of_ne]

theorem paddedPieriSource_isOneBoxNeighbor {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (i : PaddedPieriChannel lam) :
    IsAllRankOneBoxNeighbor lam (paddedPieriSource lam i) := by
  cases i with
  | inl a =>
      exact ⟨a.val, Or.inl rfl⟩
  | inr a =>
      exact ⟨a.val, Or.inr
        (raiseWeight_loweredInternalYoungWeight lam a.val a.property.1).symm⟩

end HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

/-- The normalized padded pieri lower used in the spherical-code argument. -/
def normalizedPaddedPieriLower
    {r n : ℕ} (target : Fin (r + 1) → ℕ)
    (hdominant : Antitone target)
    (row : Fin (r + 1))
    (hsource : Antitone (raiseWeight target row)) :
    HarmonicYoungSpace (n := n) (raiseWeight target row) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target) :=
  normalizedYoungClebschLower target (raiseWeight target row)
    (sum_raiseWeight target row) row
    (internalRowLowerGramScalar (raiseWeight target row) row)
    (internalRowLowerGramScalar_pos (raiseWeight target row) row
      (by simp only [raiseWeight, Function.update_self, lt_add_iff_pos_left, Order.lt_add_one_iff,
            zero_le])
      (raiseWeight_strictly_removable target hdominant row))
    (youngClebschLower_inner_of_raisedSignature
      (raiseWeight target row) target row
      (loweredInternalYoungWeight_raiseWeight target row).symm
      (by simp only [raiseWeight, Function.update_self, lt_add_iff_pos_left, Order.lt_add_one_iff,
            zero_le]) hsource
      (sum_raiseWeight target row))

@[simp] theorem normalizedPaddedPieriLower_toLinearMap
    {r n : ℕ} (target : Fin (r + 1) → ℕ)
    (hdominant : Antitone target)
    (row : Fin (r + 1))
    (hsource : Antitone (raiseWeight target row)) :
    (normalizedPaddedPieriLower (n := n)
      target hdominant row hsource).toLinearMap =
      (Real.sqrt (internalRowLowerGramScalar
        (raiseWeight target row) row))⁻¹ •
        youngClebschLower target (raiseWeight target row)
          (sum_raiseWeight target row) row := rfl

theorem normalizedPaddedPieriLower_rotation_intertwine
    {r n : ℕ} (target : Fin (r + 1) → ℕ)
    (hdominant : Antitone target)
    (row : Fin (r + 1))
    (hsource : Antitone (raiseWeight target row))
    (i j : Fin n) :
    (normalizedPaddedPieriLower (n := n)
      target hdominant row hsource).toLinearMap.comp
        (youngAmbientRotation (raiseWeight target row) i j) =
      (ClebschRotation.tensorAmbientRotation target i j).comp
        (normalizedPaddedPieriLower (n := n)
          target hdominant row hsource).toLinearMap := by
  exact boundaryNormalizedYoungClebschLower_rotation_intertwine
    target (raiseWeight target row) (sum_raiseWeight target row) row
    (internalRowLowerGramScalar (raiseWeight target row) row)
    (internalRowLowerGramScalar_pos (raiseWeight target row) row
      (by simp only [raiseWeight, Function.update_self, lt_add_iff_pos_left, Order.lt_add_one_iff,
            zero_le])
      (raiseWeight_strictly_removable target hdominant row))
    (youngClebschLower_inner_of_raisedSignature
      (raiseWeight target row) target row
      (loweredInternalYoungWeight_raiseWeight target row).symm
      (by simp only [raiseWeight, Function.update_self, lt_add_iff_pos_left, Order.lt_add_one_iff,
            zero_le]) hsource
      (sum_raiseWeight target row))
    i j

end HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherYoungAllRankGTAppendedRowLegality

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem appendZeroWeight_antitone {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    Antitone (appendZeroWeight lam) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
      have hj : j = Fin.last (r + 1) := by
        apply Fin.ext
        have hbound := j.isLt
        change r + 1 ≤ j.val at hij
        change j.val = r + 1
        omega
      subst j
      exact le_rfl
  | cast i =>
      induction j using Fin.lastCases with
      | last => simp only [appendZeroWeight_last, appendZeroWeight_castSucc, zero_le]
      | cast j =>
          have hle : i ≤ j := by simpa only [Fin.castSucc_le_castSucc_iff] using hij
          simpa only [appendZeroWeight_castSucc, ge_iff_le] using hdom hle

end HigherYoungAllRankGTAppendedRowLegality

end

namespace HigherHarmonicYoung

section


namespace AllRankGTAppendedRowExclusion

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem appendedRowFullBranchSignature_terminal_pos
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (nu : FullBranchWeight
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 1)))) :
    0 < fullBranchSignature nu (Fin.last r).castSucc := by
  have hlast := fullBranchSignature_succ_le nu (Fin.last r)
  have hpositive : 1 ≤ fullBranchSignature nu (Fin.last r).castSucc := by
    simpa only [raiseWeight, appendZeroWeight_last, zero_add, Fin.succ_last, Nat.succ_eq_add_one,
      Function.update_self] using hlast
  omega

theorem appendedRowFullBranchSignature_ne_appendZero
    {r : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (nu : FullBranchWeight
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    fullBranchSignature nu ≠ appendZeroWeight (appendZeroWeight mu) := by
  intro hsignature
  have hpositive := appendedRowFullBranchSignature_terminal_pos lam nu
  rw [hsignature] at hpositive
  simp only [appendZeroWeight_castSucc, appendZeroWeight_last, lt_self_iff_false] at hpositive

end AllRankGTAppendedRowExclusion

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankTensorClebschCompleteness

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

theorem actualTensorClebsch_iSup_range_eq_top_of_finrank
    {ι : Type*} [Fintype ι]
    {r n : ℕ} (hn : 2 * r + 2 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (source : ι → Fin (r + 1) → ℕ)
    (hsource : ∀ i, IsAllRankOneBoxNeighbor target (source i))
    (hinj : Function.Injective source)
    (A : (i : ι) → HarmonicYoungSpace (n := n) (source i) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ (i : ι) (a b : Fin n),
      (A i).toLinearMap.comp (youngAmbientRotation (source i) a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp
          (A i).toLinearMap)
    (hdim : n * Module.finrank ℝ (HarmonicYoungSpace (n := n) target) =
      ∑ i : ι, Module.finrank ℝ
        (HarmonicYoungSpace (n := n) (source i))) :
    (⨆ i : ι, LinearMap.range (A i).toLinearMap) =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) target)) := by
  apply orthogonalBranch_iSup_range_eq_top A
  · intro i j hij p q
    have hne : source i ≠ source j := fun h => hij (hinj h)
    have hzero := allRankYoungChannel_crossGram_eq_zero_of_oneBoxNeighbors
      hn target (source i) (source j) hdom (hsource i) (hsource j) hne
      (A i).toLinearMap (A j).toLinearMap (hA i) (hA j)
    calc
      ⟪A i p, A j q⟫_ℝ =
          ⟪p, (A i).toLinearMap.adjoint (A j q)⟫_ℝ :=
            (LinearMap.adjoint_inner_right (A i).toLinearMap p (A j q)).symm
      _ = 0 := by
        have hz : (A i).toLinearMap.adjoint (A j q) = 0 := by
          simpa only [LinearMap.coe_comp, LinearIsometry.coe_toLinearMap, Function.comp_apply,
            LinearMap.zero_apply] using LinearMap.congr_fun hzero q
        rw [hz]
        exact @inner_zero_right ℝ
          (HarmonicYoungSpace (n := n) (source i)) _ _ _ p
  · rw [Module.finrank_tensorProduct]
    simpa only [SpherePacking.Euclidean, finrank_euclideanSpace, Fintype.card_fin] using hdim

theorem orthogonalCompleteBranch_mem_selected_iSup
    {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i))
    (P : ι → Prop)
    (x : V)
    (hexcluded : ∀ i : ι, ¬ P i → ∀ y : E i, ⟪x, A i y⟫_ℝ = 0) :
    x ∈ (⨆ i : {i : ι // P i}, LinearMap.range (A i.val).toLinearMap) := by
  classical
  have hsum := orthogonalBranch_sum_projection A horth hdim x
  rw [← hsum]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : P i
  · exact
      (le_iSup
        (fun j : {i : ι // P i} =>
          LinearMap.range (A j.val).toLinearMap)
        ⟨i, hi⟩)
          (Submodule.starProjection_apply_mem
            (LinearMap.range (A i).toLinearMap) x)
  · have hzero :
        (LinearMap.range (A i).toLinearMap).starProjection x = 0 := by
      apply (Submodule.starProjection_apply_eq_zero_iff
        (LinearMap.range (A i).toLinearMap)).mpr
      apply ((LinearMap.range (A i).toLinearMap).mem_orthogonal' x).mpr
      rintro _ ⟨y, rfl⟩
      exact hexcluded i hi y
    rw [hzero]
    exact Submodule.zero_mem _

end AllRankTensorClebschCompleteness

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTCompressedResolventSpectral

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedRowExclusion
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.ThreeRowYoungBranching

/-- The gt signed eigenvector span used in the spherical-code argument. -/
def gtSignedEigenvectorSpan {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Submodule ℝ
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) lam) :=
  ⨆ z : Fin (r + 1) × Bool,
    Module.End.eigenspace (gtRelativeCasimir (n := n) lam)
      (signedNode (HigherChannel.ambientShift n lam) z)

theorem gtChannelCharacteristic_eval_signedNode {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (z : Fin (r + 1) × Bool) :
    (gtChannelCharacteristicPolynomial n lam).eval
      (signedNode (HigherChannel.ambientShift n lam) z) = 0 := by
  unfold gtChannelCharacteristicPolynomial signedAmbientCharacteristic
  exact Lagrange.eval_nodal_at_node (Finset.mem_univ z)

theorem gtChannelCharacteristic_aeval_apply_eigen {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (z : Fin (r + 1) × Bool)
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hv : gtRelativeCasimir (n := n) lam v =
      signedNode (HigherChannel.ambientShift n lam) z • v) :
    Polynomial.aeval (gtRelativeCasimir (n := n) lam)
      (gtChannelCharacteristicPolynomial n lam) v = 0 := by
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul hv,
    gtChannelCharacteristic_eval_signedNode lam z, zero_smul]

theorem gtSignedEigenspace_le_characteristic_ker {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (z : Fin (r + 1) × Bool) :
    Module.End.eigenspace (gtRelativeCasimir (n := n) lam)
        (signedNode (HigherChannel.ambientShift n lam) z) ≤
      LinearMap.ker
        (Polynomial.aeval (gtRelativeCasimir (n := n) lam)
          (gtChannelCharacteristicPolynomial n lam)) := by
  intro v hv
  exact gtChannelCharacteristic_aeval_apply_eigen lam z v
    ((Module.End.mem_eigenspace_iff).mp hv)

theorem gtSignedEigenvectorSpan_le_characteristic_ker {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    gtSignedEigenvectorSpan (n := n) lam ≤
      LinearMap.ker
        (Polynomial.aeval (gtRelativeCasimir (n := n) lam)
          (gtChannelCharacteristicPolynomial n lam)) := by
  unfold gtSignedEigenvectorSpan
  exact iSup_le (gtSignedEigenspace_le_characteristic_ker lam)

theorem gtSignedEigenvectorSpan_mem_of_orthogonalComplete_retained_channels
    {ι : Type*} [Fintype ι]
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (A : (i : ι) → E i →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) lam))
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) lam) =
      ∑ i : ι, Module.finrank ℝ (E i))
    (P : ι → Prop)
    (heigen : ∀ i : ι, P i → ∃ z : Fin (r + 1) × Bool,
      ∀ q : E i,
        gtRelativeCasimir (n := n) lam (A i q) =
          signedNode (HigherChannel.ambientShift n lam) z • A i q)
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hexcluded : ∀ i : ι, ¬ P i →
      ∀ q : E i, ⟪v, A i q⟫_ℝ = 0) :
    v ∈ gtSignedEigenvectorSpan (n := n) lam := by
  classical
  have hretained := orthogonalCompleteBranch_mem_selected_iSup
    A horth hdim P v hexcluded
  have hle :
      (⨆ i : {i : ι // P i}, LinearMap.range (A i.val).toLinearMap) ≤
        gtSignedEigenvectorSpan (n := n) lam := by
    apply iSup_le
    intro i
    rintro _ ⟨q, rfl⟩
    obtain ⟨z, hz⟩ := heigen i.val i.property
    apply Submodule.mem_iSup_of_mem z
    exact Module.End.mem_eigenspace_iff.mpr (hz q)
  exact hle hretained

theorem gtSignedEigenvectorSpan_gtRelativeCasimir_mem {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hv : v ∈ gtSignedEigenvectorSpan (n := n) lam) :
    gtRelativeCasimir (n := n) lam v ∈
      gtSignedEigenvectorSpan (n := n) lam := by
  change v ∈ ⨆ z : Fin (r + 1) × Bool,
    Module.End.eigenspace (gtRelativeCasimir (n := n) lam)
      (signedNode (HigherChannel.ambientShift n lam) z) at hv
  change gtRelativeCasimir (n := n) lam v ∈
    ⨆ z : Fin (r + 1) × Bool,
      Module.End.eigenspace (gtRelativeCasimir (n := n) lam)
        (signedNode (HigherChannel.ambientShift n lam) z)
  refine Submodule.iSup_induction
    (motive := fun w => gtRelativeCasimir (n := n) lam w ∈
      gtSignedEigenvectorSpan (n := n) lam) _ hv ?_ ?_ ?_
  · intro z w hw
    apply Submodule.mem_iSup_of_mem z
    rw [(Module.End.mem_eigenspace_iff).mp hw]
    exact (Module.End.eigenspace _ _).smul_mem _ hw
  · simp only [map_zero, zero_mem]
  · intro v w hv hw
    rw [map_add]
    exact (gtSignedEigenvectorSpan (n := n) lam).add_mem hv hw

theorem gtSignedEigenvectorSpan_gtRelativeCasimir_iterate_mem
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hv : v ∈ gtSignedEigenvectorSpan (n := n) lam) (k : ℕ) :
    (gtRelativeCasimir (n := n) lam ^ k) v ∈
      gtSignedEigenvectorSpan (n := n) lam := by
  induction k with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hv
  | succ k ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
      exact gtSignedEigenvectorSpan_gtRelativeCasimir_mem lam _ ih

theorem gtChannelCharacteristic_aeval_apply_iterate_eq_zero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hv : v ∈ gtSignedEigenvectorSpan (n := n) lam) (k : ℕ) :
    Polynomial.aeval (gtRelativeCasimir (n := n) lam)
        (gtChannelCharacteristicPolynomial n lam)
        ((gtRelativeCasimir (n := n) lam ^ k) v) = 0 :=
  gtSignedEigenvectorSpan_le_characteristic_ker lam
    (gtSignedEigenvectorSpan_gtRelativeCasimir_iterate_mem lam v hv k)

theorem gtChannelCharacteristic_aeval_apply_canonicalAxis_iterate_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p : HarmonicYoungSpace (n := n) mu)
    (hp : canonicalGelfandTsetlinAxisTensor lam mu h hgram p ∈
      gtSignedEigenvectorSpan (n := n + 1) lam) (k : ℕ) :
    Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam)
        ((gtRelativeCasimir (n := n + 1) lam ^ k)
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)) = 0 :=
  gtChannelCharacteristic_aeval_apply_iterate_eq_zero lam _ hp k

end AllRankGTCompressedResolventSpectral

end

end HigherHarmonicYoung

section


namespace HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn

theorem det_updateCol_of_row_delta
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (i : ι) (v : ι → R)
    (hrow : ∀ j, M i j = if j = i then 1 else 0) :
    (M.updateCol i v).det = v i * M.det := by
  classical
  let residual : ι → R := fun k => v k - v i * M k i
  have hv : v = v i • (fun k => M k i) + residual := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel, residual]
  have hzero : (M.updateCol i residual).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    by_cases hji : j = i
    · subst j
      simp only [Matrix.updateCol_self, hrow i, ↓reduceIte, mul_one, sub_self, residual]
    · simp only [Matrix.updateCol, Matrix.of_apply, ne_eq, hji, not_false_eq_true,
        Function.update_of_ne, hrow j, ↓reduceIte]
  calc
    (M.updateCol i v).det =
        (M.updateCol i (v i • (fun k => M k i) + residual)).det := by
      exact congrArg (fun w => (M.updateCol i w).det) hv
    _ = (M.updateCol i (v i • (fun k => M k i))).det +
        (M.updateCol i residual).det :=
      Matrix.det_updateCol_add M i _ _
    _ = v i * M.det + (M.updateCol i residual).det := by
      rw [Matrix.det_updateCol_smul, Matrix.updateCol_eq_self]
    _ = v i * M.det := by rw [hzero, add_zero]

theorem det_updateCol_last_of_lastRow_delta
    {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (v : Fin (r + 1) → R)
    (hrow : ∀ j, M (Fin.last r) j = if j = Fin.last r then 1 else 0) :
    (M.updateCol (Fin.last r) v).det = v (Fin.last r) * M.det :=
  det_updateCol_of_row_delta M (Fin.last r) v hrow

end HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn

end

namespace HigherHarmonicYoung

section


open scoped BigOperators

namespace AllRankOrthogonalTensorPieriDimension

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherWeylAllRankJacobiTrudiWeylEvaluation
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

private def orthogonalTensorPieriSignedShiftMatrix {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ :=
  fun i j =>
    orthogonalTensorPieriCoefficient n
        (((lam i : ℤ) - (i.val : ℤ)) + 1) (j.val : ℤ) +
      orthogonalTensorPieriCoefficient n
        (((lam i : ℤ) - (i.val : ℤ)) - 1) (j.val : ℤ)

private def orthogonalTensorPieriNextColumn {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (j : Fin (r + 1)) : Fin (r + 1) → ℤ :=
  fun i => orthogonalTensorPieriCoefficient n
    ((lam i : ℤ) - (i.val : ℤ)) ((j.val : ℤ) + 1)

private def orthogonalTensorPieriPrevColumn {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (j : Fin (r + 1)) : Fin (r + 1) → ℤ :=
  fun i => orthogonalTensorPieriCoefficient n
    ((lam i : ℤ) - (i.val : ℤ)) ((j.val : ℤ) - 1)

theorem orthogonalTensorPieriSignedShiftMatrix_column
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (j : Fin (r + 1)) :
    (fun i => orthogonalTensorPieriSignedShiftMatrix n lam i j) =
      orthogonalTensorPieriNextColumn n lam j +
        orthogonalTensorPieriPrevColumn n lam j := by
  funext i
  exact orthogonalTensorPieriCoefficient_row_shift n
    ((lam i : ℤ) - (i.val : ℤ)) (j.val : ℤ)

theorem det_updateCol_orthogonalTensorPieriNextColumn_eq_zero
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (j : Fin (r + 1)) (hj : j ≠ Fin.last r) :
    ((orthogonalJacobiTrudiMatrix n lam).updateCol j
      (orthogonalTensorPieriNextColumn n lam j)).det = 0 := by
  have hlt : j.val < r := by
    have h := Fin.lt_last_iff_ne_last.mpr hj
    exact h
  let next : Fin (r + 1) := ⟨j.val + 1, by omega⟩
  have hne : next ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Nat.add_eq_left, one_ne_zero, next] at hv
  have hcol : orthogonalTensorPieriNextColumn n lam j =
      (fun i => orthogonalJacobiTrudiMatrix n lam i next) := by
    funext i
    rw [orthogonalTensorPieriCoefficient_eq_matrix]
    change
      orthogonalTensorPieriCoefficient n
          ((lam i : ℤ) - (i.val : ℤ)) ((j.val : ℤ) + 1) =
        orthogonalTensorPieriCoefficient n
          ((lam i : ℤ) - (i.val : ℤ)) (next.val : ℤ)
    simp only [Nat.cast_add, Nat.cast_one, next]
  rw [hcol]
  exact Matrix.det_updateCol_eq_zero hne

theorem det_updateCol_orthogonalTensorPieriPrevColumn_eq_zero
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (j : Fin (r + 1)) :
    ((orthogonalJacobiTrudiMatrix n lam).updateCol j
      (orthogonalTensorPieriPrevColumn n lam j)).det = 0 := by
  by_cases hj : j.val = 0
  · apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    simp only [Matrix.updateCol_self, orthogonalTensorPieriPrevColumn, hj, CharP.cast_eq_zero,
      zero_sub, Int.reduceNeg, orthogonalTensorPieriCoefficient_neg_one]
  · have hpositive : 0 < j.val := Nat.pos_of_ne_zero hj
    let prev : Fin (r + 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hne : prev ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      simp only [prev] at hv
      omega
    have hcol : orthogonalTensorPieriPrevColumn n lam j =
        (fun i => orthogonalJacobiTrudiMatrix n lam i prev) := by
      funext i
      rw [orthogonalTensorPieriCoefficient_eq_matrix]
      change
        orthogonalTensorPieriCoefficient n
            ((lam i : ℤ) - (i.val : ℤ)) ((j.val : ℤ) - 1) =
          orthogonalTensorPieriCoefficient n
            ((lam i : ℤ) - (i.val : ℤ)) (prev.val : ℤ)
      congr 1
      simp only [Nat.cast_sub (show 1 ≤ j.val by omega), Nat.cast_one, prev]
    rw [hcol]
    exact Matrix.det_updateCol_eq_zero hne

theorem sum_det_updateCol_orthogonalTensorPieriSignedShiftMatrix
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    (∑ j : Fin (r + 1),
      ((orthogonalJacobiTrudiMatrix n lam).updateCol j
        (fun i => orthogonalTensorPieriSignedShiftMatrix n lam i j)).det) =
      ((orthogonalJacobiTrudiMatrix n lam).updateCol (Fin.last r)
        (orthogonalTensorPieriNextColumn n lam (Fin.last r))).det := by
  classical
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [orthogonalTensorPieriSignedShiftMatrix_column,
      Matrix.det_updateCol_add,
      det_updateCol_orthogonalTensorPieriPrevColumn_eq_zero,
      add_zero]
  · intro j _ hj
    rw [orthogonalTensorPieriSignedShiftMatrix_column,
      Matrix.det_updateCol_add,
      det_updateCol_orthogonalTensorPieriNextColumn_eq_zero n lam j hj,
      det_updateCol_orthogonalTensorPieriPrevColumn_eq_zero,
      add_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]

theorem sum_det_updateRow_eq_sum_det_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M B : Matrix ι ι R) :
    (∑ i : ι, (M.updateRow i (B i)).det) =
      ∑ j : ι, (M.updateCol j (fun i => B i j)).det := by
  classical
  calc
    (∑ i : ι, (M.updateRow i (B i)).det) =
        ∑ i : ι, ∑ j : ι, M.adjugate j i * B i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Matrix.cramer_transpose_apply M (B i) i,
        Matrix.cramer_eq_adjugate_mulVec]
      simp only [Matrix.mulVec, dotProduct, ← Matrix.adjugate_transpose, Matrix.transpose_apply]
    _ = ∑ j : ι, ∑ i : ι, M.adjugate j i * B i j := by
      rw [Finset.sum_comm]
    _ = ∑ j : ι, (M.updateCol j (fun i => B i j)).det := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Matrix.cramer_apply M (fun i => B i j) j,
        Matrix.cramer_eq_adjugate_mulVec]
      simp only [Matrix.mulVec, dotProduct]

theorem orthogonalJacobiTrudiMatrix_lastRow_delta
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (hzero : lam (Fin.last r) = 0) (j : Fin (r + 1)) :
    orthogonalJacobiTrudiMatrix n lam (Fin.last r) j =
      if j = Fin.last r then 1 else 0 := by
  rw [orthogonalTensorPieriCoefficient_eq_matrix]
  have harg :
      ((lam (Fin.last r) : ℤ) - ((Fin.last r).val : ℤ)) =
        -(r : ℤ) := by simp only [hzero, CharP.cast_eq_zero, Fin.val_last, zero_sub]
  rw [harg, orthogonalTensorPieriCoefficient_padded_zero_fin]
  by_cases hj : j = Fin.last r
  · subst j
    simp only [Fin.val_last, ↓reduceIte]
  · have hval : j.val ≠ r := by
      intro heq
      apply hj
      apply Fin.ext
      simpa only [Fin.val_last] using heq
    simp only [hval, ↓reduceIte, hj]

theorem orthogonalTensorPieriNextColumn_last
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (hzero : lam (Fin.last r) = 0) :
    orthogonalTensorPieriNextColumn n lam (Fin.last r)
      (Fin.last r) = (n : ℤ) := by
  unfold orthogonalTensorPieriNextColumn
  simp only [Fin.val_last]
  have harg : ((lam (Fin.last r) : ℤ) - (r : ℤ)) =
      -(r : ℤ) := by simp only [hzero, CharP.cast_eq_zero, zero_sub]
  rw [harg]
  convert orthogonalTensorPieriCoefficient_padded_zero_succ n r using 1
  push_cast
  ring

theorem sum_det_updateRow_orthogonalTensorPieriSignedShiftMatrix
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (hzero : lam (Fin.last r) = 0) :
    (∑ i : Fin (r + 1),
      ((orthogonalJacobiTrudiMatrix n lam).updateRow i
        (orthogonalTensorPieriSignedShiftMatrix n lam i)).det) =
      (n : ℤ) * orthogonalJacobiTrudiDimension n lam := by
  calc
    (∑ i : Fin (r + 1),
        ((orthogonalJacobiTrudiMatrix n lam).updateRow i
          (orthogonalTensorPieriSignedShiftMatrix n lam i)).det) =
        ∑ j : Fin (r + 1),
          ((orthogonalJacobiTrudiMatrix n lam).updateCol j
            (fun i => orthogonalTensorPieriSignedShiftMatrix n lam i j)).det :=
      sum_det_updateRow_eq_sum_det_updateCol
        (orthogonalJacobiTrudiMatrix n lam)
        (orthogonalTensorPieriSignedShiftMatrix n lam)
    _ = ((orthogonalJacobiTrudiMatrix n lam).updateCol (Fin.last r)
          (orthogonalTensorPieriNextColumn n lam (Fin.last r))).det :=
      sum_det_updateCol_orthogonalTensorPieriSignedShiftMatrix n lam
    _ = orthogonalTensorPieriNextColumn n lam (Fin.last r)
          (Fin.last r) * (orthogonalJacobiTrudiMatrix n lam).det :=
      det_updateCol_last_of_lastRow_delta
        (orthogonalJacobiTrudiMatrix n lam)
        (orthogonalTensorPieriNextColumn n lam (Fin.last r))
        (orthogonalJacobiTrudiMatrix_lastRow_delta n lam hzero)
    _ = (n : ℤ) * orthogonalJacobiTrudiDimension n lam := by
      rw [orthogonalTensorPieriNextColumn_last n lam hzero]
      rfl

theorem orthogonalJacobiTrudiDimension_tensorPieri
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam) (hzero : lam (Fin.last r) = 0) :
    (∑ i : {i : Fin (r + 1) // Antitone (raiseWeight lam i)},
      orthogonalJacobiTrudiDimension n (raiseWeight lam i.val)) +
      (∑ i : {i : Fin (r + 1) //
        0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)},
        orthogonalJacobiTrudiDimension n
          (loweredInternalYoungWeight lam i.val)) =
      (n : ℤ) * orthogonalJacobiTrudiDimension n lam := by
  classical
  have hsplit :
      (∑ i : Fin (r + 1),
        ((orthogonalJacobiTrudiMatrix n lam).updateRow i
          (orthogonalTensorPieriSignedShiftMatrix n lam i)).det) =
        (∑ i : Fin (r + 1),
          ((orthogonalJacobiTrudiMatrix n lam).updateRow i
            (orthogonalTensorPieriRaiseRow n lam i)).det) +
        (∑ i : Fin (r + 1),
          ((orthogonalJacobiTrudiMatrix n lam).updateRow i
            (orthogonalTensorPieriLowerRow n lam i)).det) := by
    calc
      (∑ i : Fin (r + 1),
        ((orthogonalJacobiTrudiMatrix n lam).updateRow i
          (orthogonalTensorPieriSignedShiftMatrix n lam i)).det) =
          ∑ i : Fin (r + 1),
            (((orthogonalJacobiTrudiMatrix n lam).updateRow i
              (orthogonalTensorPieriRaiseRow n lam i)).det +
            ((orthogonalJacobiTrudiMatrix n lam).updateRow i
              (orthogonalTensorPieriLowerRow n lam i)).det) := by
        apply Finset.sum_congr rfl
        intro i _
        change
          ((orthogonalJacobiTrudiMatrix n lam).updateRow i
            (orthogonalTensorPieriRaiseRow n lam i +
              orthogonalTensorPieriLowerRow n lam i)).det = _
        exact Matrix.det_updateRow_add _ _ _ _
      _ = _ := by rw [Finset.sum_add_distrib]
  have hraw := sum_det_updateRow_orthogonalTensorPieriSignedShiftMatrix
    n lam hzero
  rw [hsplit,
    sum_det_updateRow_raise_eq_dominant_subtype n lam hdom,
    sum_det_updateRow_lower_eq_positive_dominant_subtype n lam hdom] at hraw
  exact hraw

theorem weyl_tensorPieri_dimension
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam) (hzero : lam (Fin.last r) = 0) :
    (∑ i : {i : Fin (r + 1) // Antitone (raiseWeight lam i)},
      Weyl.dimension n (raiseWeight lam i.val)) +
      (∑ i : {i : Fin (r + 1) //
        0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)},
        Weyl.dimension n (loweredInternalYoungWeight lam i.val)) =
      (n : ℝ) * Weyl.dimension n lam := by
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (orthogonalJacobiTrudiDimension_tensorPieri n lam hdom hzero)
  push_cast at h
  simpa only [orthogonalJacobiTrudiDimension_eq_weyl hn] using h

theorem finrank_harmonicYoung_tensorPieri
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone lam) (hzero : lam (Fin.last r) = 0) :
    (∑ i : {i : Fin (r + 1) // Antitone (raiseWeight lam i)},
      Module.finrank ℝ
        (HarmonicYoungSpace (n := n) (raiseWeight lam i.val))) +
      (∑ i : {i : Fin (r + 1) //
        0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)},
        Module.finrank ℝ
          (HarmonicYoungSpace (n := n)
            (loweredInternalYoungWeight lam i.val))) =
      n * Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) := by
  have h := weyl_tensorPieri_dimension hn lam hdom hzero
  have hreal :
      ((∑ i : {i : Fin (r + 1) // Antitone (raiseWeight lam i)},
          Module.finrank ℝ
            (HarmonicYoungSpace (n := n) (raiseWeight lam i.val))) +
        (∑ i : {i : Fin (r + 1) //
          0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)},
          Module.finrank ℝ
            (HarmonicYoungSpace (n := n)
              (loweredInternalYoungWeight lam i.val))) : ℕ) =
        ((n * Module.finrank ℝ
          (HarmonicYoungSpace (n := n) lam) : ℕ) : ℝ) := by
    push_cast
    convert h using 1
    · apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i _
        exact (weyl_dimension_eq_finrank_harmonicYoung hn
          (raiseWeight lam i.val) i.property).symm
      · apply Finset.sum_congr rfl
        intro i _
        exact (weyl_dimension_eq_finrank_harmonicYoung hn
          (loweredInternalYoungWeight lam i.val) i.property.2).symm
    · rw [weyl_dimension_eq_finrank_harmonicYoung hn lam hdom]
  exact_mod_cast hreal

end AllRankOrthogonalTensorPieriDimension

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTTensorPieriNormalizedChannels

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalEdgeRaisingGram
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisAssembly
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

private theorem target_tail_finiteInterlacing_metriccodes2_9210a270
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target) :
    FiniteInterlacing n target (fun i : Fin r => target i.succ) := by
  refine ⟨hn, ?_⟩
  intro i
  exact ⟨hdom (Fin.castSucc_le_succ i), le_rfl⟩

private theorem lowered_target_tail_finiteInterlacing_metriccodes2_9210a270
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (row : Fin (r + 1))
    (hlow : Antitone (loweredInternalYoungWeight target row)) :
    FiniteInterlacing n
      (loweredInternalYoungWeight target row)
      (fun i : Fin r => target i.succ) := by
  refine ⟨hn, ?_⟩
  intro i
  constructor
  · by_cases hrow : i.castSucc = row
    · have hnext : i.succ ≠ row := by
        rw [← hrow]
        exact ne_of_gt (Fin.castSucc_lt_succ (i := i))
      have h := hlow (Fin.castSucc_le_succ i)
      simpa only [loweredInternalYoungWeight, hrow, Function.update_self, ge_iff_le, ne_eq, hnext,
        not_false_eq_true, Function.update_of_ne] using h
    · simpa only [loweredInternalYoungWeight, ne_eq, hrow, not_false_eq_true,
      Function.update_of_ne] using
        hdom (Fin.castSucc_le_succ i)
  · by_cases hrow : i.succ = row
    · simp only [loweredInternalYoungWeight, hrow, Function.update_self, tsub_le_iff_right,
        le_add_iff_nonneg_right, zero_le]
    · simp only [loweredInternalYoungWeight, ne_eq, hrow, not_false_eq_true, Function.update_of_ne,
        Std.le_refl]

private theorem existsNormalizedPaddedPieriRaising_metriccodes2_9210a270
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (row : PaddedPieriLowerRow target) :
    ∃ A : HarmonicYoungSpace (n := n)
        (loweredInternalYoungWeight target row.val) →ₗᵢ[ℝ]
          (SpherePacking.Euclidean n ⊗[ℝ]
            HarmonicYoungSpace (n := n) target),
      ∀ a b : Fin n,
        A.toLinearMap.comp
            (youngAmbientRotation
              (loweredInternalYoungWeight target row.val) a b) =
          (ClebschRotation.tensorAmbientRotation target a b).comp
            A.toLinearMap := by
  let low := loweredInternalYoungWeight target row.val
  let mu : Fin r → ℕ := fun i => target i.succ
  have hrecover : raiseWeight low row.val = target :=
    raiseWeight_loweredInternalYoungWeight target row.val row.property.1
  have htail : FiniteInterlacing n target mu :=
    target_tail_finiteInterlacing_metriccodes2_9210a270 hn target hdom
  have hlowtail : FiniteInterlacing n low mu :=
    lowered_target_tail_finiteInterlacing_metriccodes2_9210a270 hn target hdom
      row.val row.property.2
  obtain ⟨c, hc, hinner, _⟩ :=
    canonicalEdgeRaisingGram_of_signature_eq low target mu row.val
      hrecover.symm hlowtail htail
  let hdegree : (∑ i, target i) = (∑ i, low i) + 1 :=
    loweredInternalYoungWeight_sum_add_one target row.val row.property.1
  let A := normalizedYoungClebschRaise target low hdegree row.val c hc hinner
  refine ⟨A, ?_⟩
  intro a b
  exact boundaryNormalizedYoungClebschRaise_rotation_intertwine
    target low hdegree row.val c hc hinner a b

private def normalizedPaddedPieriRaising
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (row : PaddedPieriLowerRow target) :
    HarmonicYoungSpace (n := n)
        (loweredInternalYoungWeight target row.val) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target) :=
  Classical.choose (existsNormalizedPaddedPieriRaising_metriccodes2_9210a270 hn target hdom row)

theorem normalizedPaddedPieriRaising_rotation_intertwine
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (row : PaddedPieriLowerRow target) (a b : Fin n) :
    (normalizedPaddedPieriRaising hn target hdom row).toLinearMap.comp
        (youngAmbientRotation
          (loweredInternalYoungWeight target row.val) a b) =
      (ClebschRotation.tensorAmbientRotation target a b).comp
        (normalizedPaddedPieriRaising hn target hdom row).toLinearMap :=
  Classical.choose_spec
    (existsNormalizedPaddedPieriRaising_metriccodes2_9210a270 hn target hdom row) a b

end AllRankGTTensorPieriNormalizedChannels

end

end HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherYoungAllRankOrthogonalTensorPieriActualChannels

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTensorPieriNormalizedChannels
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

/-- The padded orthogonal tensor pieri channel used in the spherical-code argument. -/
def paddedOrthogonalTensorPieriChannel
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target) :
    (i : PaddedPieriChannel target) →
      HarmonicYoungSpace (n := n) (paddedPieriSource target i) →ₗᵢ[ℝ]
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) target)
  | Sum.inl row =>
      normalizedPaddedPieriLower target hdom row.val row.property
  | Sum.inr row =>
      normalizedPaddedPieriRaising hn target hdom row

theorem paddedOrthogonalTensorPieriChannel_rotation_intertwine
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (i : PaddedPieriChannel target) (a b : Fin n) :
    (paddedOrthogonalTensorPieriChannel hn target hdom i).toLinearMap.comp
        (youngAmbientRotation (paddedPieriSource target i) a b) =
      (ClebschRotation.tensorAmbientRotation target a b).comp
        (paddedOrthogonalTensorPieriChannel hn target hdom i).toLinearMap := by
  cases i with
  | inl row =>
      exact normalizedPaddedPieriLower_rotation_intertwine
        target hdom row.val row.property a b
  | inr row =>
      exact normalizedPaddedPieriRaising_rotation_intertwine
        hn target hdom row a b

theorem paddedOrthogonalTensorPieri_finrank
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (hzero : target (Fin.last r) = 0) :
    n * Module.finrank ℝ (HarmonicYoungSpace (n := n) target) =
      ∑ i : PaddedPieriChannel target,
        Module.finrank ℝ
          (HarmonicYoungSpace (n := n) (paddedPieriSource target i)) := by
  change
    n * Module.finrank ℝ (HarmonicYoungSpace (n := n) target) =
      ∑ i : PaddedPieriRaiseRow target ⊕ PaddedPieriLowerRow target,
        Module.finrank ℝ
          (HarmonicYoungSpace (n := n) (paddedPieriSource target i))
  rw [Fintype.sum_sum_type]
  exact (finrank_harmonicYoung_tensorPieri hn target hdom hzero).symm

theorem paddedOrthogonalTensorPieri_iSup_range_eq_top
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (hzero : target (Fin.last r) = 0) :
    (⨆ i : PaddedPieriChannel target,
      LinearMap.range
        (paddedOrthogonalTensorPieriChannel hn target hdom i).toLinearMap) =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) target)) := by
  apply actualTensorClebsch_iSup_range_eq_top_of_finrank
    (by omega) target hdom (paddedPieriSource target)
    (paddedPieriSource_isOneBoxNeighbor target)
    (paddedPieriSource_injective target)
    (paddedOrthogonalTensorPieriChannel hn target hdom)
    (paddedOrthogonalTensorPieriChannel_rotation_intertwine hn target hdom)
  exact paddedOrthogonalTensorPieri_finrank hn target hdom hzero

end HigherYoungAllRankOrthogonalTensorPieriActualChannels

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankZeroRowTensorCasimirConjugacy

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching

@[simp] theorem allRankCasimirEigenvalue_appendZeroWeight
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    allRankCasimirEigenvalue n (appendZeroWeight lam) =
      allRankCasimirEigenvalue n lam := by
  unfold allRankCasimirEigenvalue
  rw [Fin.sum_univ_castSucc]
  simp only [appendZeroWeight_castSucc, Fin.val_castSucc, appendZeroWeight_last, CharP.cast_eq_zero,
    zero_add, Fin.val_last, Nat.cast_add, Nat.cast_one, zero_mul, add_zero]

/-- The zero row tensor isometry equiv used in the spherical-code argument. -/
def zeroRowTensorIsometryEquiv {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam) ≃ₗᵢ[ℝ]
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) (appendZeroWeight lam)) :=
  (appendZeroRowIsometryEquiv (n := n) lam).lTensor
    (SpherePacking.Euclidean n)

@[simp] theorem zeroRowTensorIsometryEquiv_tmul
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    zeroRowTensorIsometryEquiv lam (v ⊗ₜ[ℝ] p) =
      v ⊗ₜ[ℝ] appendZeroRowIsometryEquiv lam p := rfl

@[simp] theorem zeroRowTensorIsometryEquiv_symm_tmul
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) (appendZeroWeight lam)) :
    (zeroRowTensorIsometryEquiv lam).symm (v ⊗ₜ[ℝ] p) =
      v ⊗ₜ[ℝ] (appendZeroRowIsometryEquiv lam).symm p := rfl

theorem zeroRowTensorIsometryEquiv_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (a b : Fin n) :
    (zeroRowTensorIsometryEquiv lam).toLinearMap.comp
        (tensorAmbientRotation lam a b) =
      (tensorAmbientRotation (appendZeroWeight lam) a b).comp
        (zeroRowTensorIsometryEquiv lam).toLinearMap := by
  apply TensorProduct.ext'
  intro v p
  change zeroRowTensorIsometryEquiv lam
      (tensorAmbientRotation lam a b (v ⊗ₜ[ℝ] p)) =
    tensorAmbientRotation (appendZeroWeight lam) a b
      (zeroRowTensorIsometryEquiv lam (v ⊗ₜ[ℝ] p))
  simp only [tensorAmbientRotation_tmul, map_add,
    zeroRowTensorIsometryEquiv_tmul]
  congr 1
  exact congrArg (fun q => v ⊗ₜ[ℝ] q)
    (LinearMap.congr_fun
      (appendZeroRowIsometryEquiv_rotation_intertwine lam a b) p)

theorem zeroRowTensorIsometryEquiv_symm_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (a b : Fin n) :
    (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap.comp
        (tensorAmbientRotation (appendZeroWeight lam) a b) =
      (tensorAmbientRotation lam a b).comp
        (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap := by
  apply TensorProduct.ext'
  intro v p
  change (zeroRowTensorIsometryEquiv (n := n) lam).symm
      (tensorAmbientRotation (appendZeroWeight lam) a b (v ⊗ₜ[ℝ] p)) =
    tensorAmbientRotation lam a b
      ((zeroRowTensorIsometryEquiv (n := n) lam).symm (v ⊗ₜ[ℝ] p))
  simp only [tensorAmbientRotation_tmul, map_add,
    zeroRowTensorIsometryEquiv_symm_tmul]
  congr 1
  exact congrArg (fun q => v ⊗ₜ[ℝ] q)
    (LinearMap.congr_fun
      (appendZeroRowIsometryEquiv_symm_rotation_intertwine lam a b) p)

theorem zeroRowTensorIsometryEquiv_symm_tensorCasimir_intertwine
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap.comp
        (gtTensorCasimir (appendZeroWeight lam)) =
      (gtTensorCasimir lam).comp
        (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  have hrot (a b : Fin n)
      (y : SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) (appendZeroWeight lam)) :
      (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap
          (tensorAmbientRotation (appendZeroWeight lam) a b y) =
        tensorAmbientRotation lam a b
          ((zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap y) :=
    LinearMap.congr_fun
      (zeroRowTensorIsometryEquiv_symm_rotation_intertwine lam a b) y
  simp only [LinearMap.comp_apply, gtTensorCasimir, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.neg_apply, map_smul, map_sum, map_neg]
  simp_rw [hrot]

theorem zeroRowTensorIsometryEquiv_symm_relativeCasimir_intertwine
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap.comp
        (gtRelativeCasimir (appendZeroWeight lam)) =
      (gtRelativeCasimir lam).comp
        (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun
    (zeroRowTensorIsometryEquiv_symm_tensorCasimir_intertwine lam) x
  simp only [LinearMap.comp_apply] at h
  simp only [gtRelativeCasimir, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_sub]
  rw [allRankCasimirEigenvalue_appendZeroWeight, h]

end AllRankZeroRowTensorCasimirConjugacy

namespace AllRankGTRelativeCasimirZeroRowTransport

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.ThreeRowYoungBranching

@[simp] theorem ambientShift_appendZeroWeight_castSucc
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :
    HigherChannel.ambientShift n (appendZeroWeight lam) i.castSucc =
      HigherChannel.ambientShift n lam i := by
  simp only [ambientShift, appendZeroWeight_castSucc, Fin.val_castSucc]

/-- The retained padded pieri channel used in the spherical-code argument. -/
def retainedPaddedPieriChannel {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    PaddedPieriChannel (appendZeroWeight lam) → Prop
  | Sum.inl row => row.val ≠ Fin.last (r + 1)
  | Sum.inr _ => True

theorem paddedPieriLowerRow_ne_last {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (row : PaddedPieriLowerRow (appendZeroWeight lam)) :
    row.val ≠ Fin.last (r + 1) := by
  intro h
  have hpos := row.property.1
  rw [h, appendZeroWeight_last] at hpos
  omega

theorem raiseWeight_appendZeroWeight_castSucc
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    raiseWeight (appendZeroWeight lam) row.castSucc =
      appendZeroWeight (raiseWeight lam row) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [raiseWeight, appendZeroWeight_last,
      Function.update_of_ne (Ne.symm (Fin.castSucc_ne_last row))]
  · by_cases h : j = row
    · subst j
      simp only [raiseWeight, appendZeroWeight_castSucc, Function.update_self]
    · have hcast : j.castSucc ≠ row.castSucc := by
        intro h'
        exact h (Fin.ext (congrArg (fun k : Fin (r + 2) => k.val) h'))
      simp only [raiseWeight, appendZeroWeight_castSucc, ne_eq, hcast, not_false_eq_true,
        Function.update_of_ne, h]

theorem loweredInternalYoungWeight_appendZeroWeight_castSucc
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    loweredInternalYoungWeight (appendZeroWeight lam) row.castSucc =
      appendZeroWeight (loweredInternalYoungWeight lam row) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [loweredInternalYoungWeight, appendZeroWeight_last,
      Function.update_of_ne (Ne.symm (Fin.castSucc_ne_last row))]
  · by_cases h : j = row
    · subst j
      simp only [loweredInternalYoungWeight, appendZeroWeight_castSucc, Function.update_self]
    · have hcast : j.castSucc ≠ row.castSucc := by
        intro h'
        exact h (Fin.ext (congrArg (fun k : Fin (r + 2) => k.val) h'))
      simp only [loweredInternalYoungWeight, appendZeroWeight_castSucc, ne_eq, hcast,
        not_false_eq_true, Function.update_of_ne, h]

/-- The retained padded pieri signed node used in the spherical-code argument. -/
def retainedPaddedPieriSignedNode {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    {i : PaddedPieriChannel (appendZeroWeight lam) //
      retainedPaddedPieriChannel lam i} → Fin (r + 1) × Bool
  | ⟨Sum.inl row, hrow⟩ => ⟨row.val.castPred hrow, true⟩
  | ⟨Sum.inr row, _⟩ =>
      ⟨row.val.castPred (paddedPieriLowerRow_ne_last lam row), false⟩

/-- The retained padded pieri physical source used in the spherical-code argument. -/
def retainedPaddedPieriPhysicalSource {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    {i : PaddedPieriChannel (appendZeroWeight lam) //
      retainedPaddedPieriChannel lam i} → Fin (r + 1) → ℕ
  | ⟨Sum.inl row, hrow⟩ =>
      raiseWeight lam (row.val.castPred hrow)
  | ⟨Sum.inr row, _⟩ =>
      loweredInternalYoungWeight lam
        (row.val.castPred (paddedPieriLowerRow_ne_last lam row))

theorem paddedPieriSource_retained_eq_appendZero
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (i : {j : PaddedPieriChannel (appendZeroWeight lam) //
      retainedPaddedPieriChannel lam j}) :
    paddedPieriSource (appendZeroWeight lam) i.val =
      appendZeroWeight (retainedPaddedPieriPhysicalSource lam i) := by
  rcases i with ⟨(row | row), hrow⟩
  · change raiseWeight (appendZeroWeight lam) row.val =
      appendZeroWeight (raiseWeight lam (row.val.castPred hrow))
    calc
      raiseWeight (appendZeroWeight lam) row.val =
          raiseWeight (appendZeroWeight lam)
            (row.val.castPred hrow).castSucc := by
              congr 1
      _ = _ := raiseWeight_appendZeroWeight_castSucc lam _
  · change loweredInternalYoungWeight (appendZeroWeight lam) row.val =
      appendZeroWeight (loweredInternalYoungWeight lam
        (row.val.castPred (paddedPieriLowerRow_ne_last lam row)))
    calc
      loweredInternalYoungWeight (appendZeroWeight lam) row.val =
          loweredInternalYoungWeight (appendZeroWeight lam)
            (row.val.castPred
              (paddedPieriLowerRow_ne_last lam row)).castSucc := by
                congr 1
      _ = _ := loweredInternalYoungWeight_appendZeroWeight_castSucc lam _

theorem retainedPaddedPieriSignedNode_injective {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Function.Injective (retainedPaddedPieriSignedNode lam) := by
  intro i j hij
  rcases i with ⟨(a | a), ha⟩
  · rcases j with ⟨(b | b), hb⟩
    · have hrow := congrArg Prod.fst hij
      change a.val.castPred ha = b.val.castPred hb at hrow
      have hab : a.val = b.val :=
        Fin.ext (congrArg (fun k : Fin (r + 1) => k.val) hrow)
      apply Subtype.ext
      exact congrArg Sum.inl (Subtype.ext hab)
    · have hsign := congrArg Prod.snd hij
      simp only [retainedPaddedPieriSignedNode, Bool.true_eq_false] at hsign
  · rcases j with ⟨(b | b), hb⟩
    · have hsign := congrArg Prod.snd hij
      simp only [retainedPaddedPieriSignedNode, Bool.false_eq_true] at hsign
    · have hrow := congrArg Prod.fst hij
      change a.val.castPred (paddedPieriLowerRow_ne_last lam a) =
        b.val.castPred (paddedPieriLowerRow_ne_last lam b) at hrow
      have hab : a.val = b.val :=
        Fin.ext (congrArg (fun k : Fin (r + 1) => k.val) hrow)
      apply Subtype.ext
      exact congrArg Sum.inr (Subtype.ext hab)

theorem signedNode_appendZeroWeight_retained_raise
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : PaddedPieriRaiseRow (appendZeroWeight lam))
    (hrow : row.val ≠ Fin.last (r + 1)) :
    signedNode (HigherChannel.ambientShift n (appendZeroWeight lam))
        (row.val, true) =
      signedNode (HigherChannel.ambientShift n lam)
        (retainedPaddedPieriSignedNode lam
          ⟨Sum.inl row, hrow⟩) := by
  change HigherChannel.ambientShift n (appendZeroWeight lam) row.val =
    HigherChannel.ambientShift n lam (row.val.castPred hrow)
  calc
    HigherChannel.ambientShift n (appendZeroWeight lam) row.val =
        HigherChannel.ambientShift n (appendZeroWeight lam)
          (row.val.castPred hrow).castSucc := by
            rw [Fin.castSucc_castPred]
    _ = _ := ambientShift_appendZeroWeight_castSucc lam _

theorem signedNode_appendZeroWeight_retained_lower
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : PaddedPieriLowerRow (appendZeroWeight lam)) :
    signedNode (HigherChannel.ambientShift n (appendZeroWeight lam))
        (row.val, false) =
      signedNode (HigherChannel.ambientShift n lam)
        (retainedPaddedPieriSignedNode lam
          ⟨Sum.inr row, trivial⟩) := by
  change -HigherChannel.ambientShift n (appendZeroWeight lam) row.val =
    -HigherChannel.ambientShift n lam
      (row.val.castPred (paddedPieriLowerRow_ne_last lam row))
  congr 1
  calc
    HigherChannel.ambientShift n (appendZeroWeight lam) row.val =
        HigherChannel.ambientShift n (appendZeroWeight lam)
          (row.val.castPred
            (paddedPieriLowerRow_ne_last lam row)).castSucc := by
              rw [Fin.castSucc_castPred]
    _ = _ := ambientShift_appendZeroWeight_castSucc lam _

/-- The zero row transport padded pieri channel used in the spherical-code argument. -/
def zeroRowTransportPaddedPieriChannel
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) (appendZeroWeight lam))) :
    E →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) lam) :=
  (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearIsometry.comp A

theorem zeroRowTransportPaddedPieriChannel_eigen_of_intertwine
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) (appendZeroWeight lam)))
    (hconj :
      (gtRelativeCasimir (n := n) lam).comp
        (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap =
      (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap.comp
        (gtRelativeCasimir (n := n) (appendZeroWeight lam)))
    (c : ℝ) (p : E)
    (heigen : gtRelativeCasimir (n := n) (appendZeroWeight lam) (A p) =
      c • A p) :
    gtRelativeCasimir (n := n) lam
        (zeroRowTransportPaddedPieriChannel lam A p) =
      c • zeroRowTransportPaddedPieriChannel lam A p := by
  have h := LinearMap.congr_fun hconj (A p)
  change gtRelativeCasimir (n := n) lam
      ((zeroRowTensorIsometryEquiv (n := n) lam).symm (A p)) =
    (zeroRowTensorIsometryEquiv (n := n) lam).symm
      (gtRelativeCasimir (n := n) (appendZeroWeight lam) (A p)) at h
  rw [heigen, map_smul] at h
  exact h

theorem transportedPaddedPieriChannel_eigen_of_retained
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (i : {j : PaddedPieriChannel (appendZeroWeight lam) //
      retainedPaddedPieriChannel lam j})
    (p : HarmonicYoungSpace (n := n)
      (paddedPieriSource (appendZeroWeight lam) i.val)) :
    gtRelativeCasimir (n := n) lam
        (zeroRowTransportPaddedPieriChannel lam
          (paddedOrthogonalTensorPieriChannel
            hn (appendZeroWeight lam) hdom i.val) p) =
      signedNode (HigherChannel.ambientShift n lam)
          (retainedPaddedPieriSignedNode lam i) •
        zeroRowTransportPaddedPieriChannel lam
          (paddedOrthogonalTensorPieriChannel
            hn (appendZeroWeight lam) hdom i.val) p := by
  rcases i with ⟨(row | row), hrow⟩
  · have hchannel := gtRelativeCasimir_raise_channel
      (appendZeroWeight lam) row.val
      (paddedOrthogonalTensorPieriChannel hn
        (appendZeroWeight lam) hdom (Sum.inl row)).toLinearMap
      (paddedOrthogonalTensorPieriChannel_rotation_intertwine hn
        (appendZeroWeight lam) hdom (Sum.inl row)) p
    have htransport := zeroRowTransportPaddedPieriChannel_eigen_of_intertwine
      lam
      (paddedOrthogonalTensorPieriChannel hn
        (appendZeroWeight lam) hdom (Sum.inl row))
      (zeroRowTensorIsometryEquiv_symm_relativeCasimir_intertwine lam).symm
      (signedNode
        (HigherChannel.ambientShift n (appendZeroWeight lam))
        (row.val, true)) p hchannel
    rw [signedNode_appendZeroWeight_retained_raise lam row hrow]
      at htransport
    exact htransport
  · have hsource : appendZeroWeight lam =
        raiseWeight
          (paddedPieriSource (appendZeroWeight lam) (Sum.inr row)) row.val := by
      simpa only [paddedPieriSource_inr] using
        (raiseWeight_loweredInternalYoungWeight (appendZeroWeight lam) row.val row.property.1).symm
    have hchannel := gtRelativeCasimir_lower_channel
      (appendZeroWeight lam)
      (paddedPieriSource (appendZeroWeight lam) (Sum.inr row)) row.val
      hsource
      (paddedOrthogonalTensorPieriChannel hn
        (appendZeroWeight lam) hdom (Sum.inr row)).toLinearMap
      (paddedOrthogonalTensorPieriChannel_rotation_intertwine hn
        (appendZeroWeight lam) hdom (Sum.inr row)) p
    have htransport := zeroRowTransportPaddedPieriChannel_eigen_of_intertwine
      lam
      (paddedOrthogonalTensorPieriChannel hn
        (appendZeroWeight lam) hdom (Sum.inr row))
      (zeroRowTensorIsometryEquiv_symm_relativeCasimir_intertwine lam).symm
      (signedNode
        (HigherChannel.ambientShift n (appendZeroWeight lam))
        (row.val, false)) p hchannel
    rw [signedNode_appendZeroWeight_retained_lower lam row] at htransport
    exact htransport

end AllRankGTRelativeCasimirZeroRowTransport

end

end HigherHarmonicYoung

section


open scoped BigOperators

namespace HigherYoungAllRankGTArrowheadSchurComplement

open MetricCodes.Spherical.HigherChannel

/-- The gt stabilizer arrowhead node used in the spherical-code argument. -/
def gtStabilizerArrowheadNode {r : ℕ} (rho : ℝ) (M : Fin r → ℝ) :
    Unit ⊕ (Fin r × Bool) → ℝ
  | .inl _ => -rho
  | .inr (m, true) => M m - 1 / 2
  | .inr (m, false) => -M m - 1 / 2

@[simp] theorem gtStabilizerArrowheadNode_pos {r : ℕ}
    (rho : ℝ) (M : Fin r → ℝ) (m : Fin r) :
    gtStabilizerArrowheadNode rho M (.inr (m, true)) =
      M m - 1 / 2 := rfl

@[simp] theorem gtStabilizerArrowheadNode_neg {r : ℕ}
    (rho : ℝ) (M : Fin r → ℝ) (m : Fin r) :
    gtStabilizerArrowheadNode rho M (.inr (m, false)) =
      -M m - 1 / 2 := rfl

/-- The gt stabilizer arrowhead minor used in the spherical-code argument. -/
def gtStabilizerArrowheadMinor {r : ℕ}
    (rho : ℝ) (M : Fin r → ℝ) : Polynomial ℝ :=
  Lagrange.nodal
    (Finset.univ : Finset (Unit ⊕ (Fin r × Bool)))
    (gtStabilizerArrowheadNode rho M)

theorem gtStabilizerArrowheadMinor_eq_channelNumerator {r : ℕ}
    (rho : ℝ) (M : Fin r → ℝ) :
    gtStabilizerArrowheadMinor rho M =
      channelNumeratorPolynomial rho M := by
  classical
  unfold gtStabilizerArrowheadMinor Lagrange.nodal
    channelNumeratorPolynomial
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique, Fintype.prod_prod_type,
    Fintype.prod_bool]
  congr 1
  · simp only [gtStabilizerArrowheadNode, map_neg, sub_neg_eq_add]
  · apply Finset.prod_congr rfl
    intro m _
    simp only [gtStabilizerArrowheadNode, map_sub, map_neg, map_add]
    ring

end HigherYoungAllRankGTArrowheadSchurComplement

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace AllRankGTInvalidRowCharacteristicMinorVanishing

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem not_interlaces_raiseWeight_iff_upperWall
    {r : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu) (row : Fin (r + 1)) :
    ¬ Interlaces lam (raiseWeight mu row) ↔
      lam row.castSucc = mu row := by
  constructor
  · intro hbad
    by_contra hne
    have hstrict : mu row < lam row.castSucc := by
      have hle := (h row).1
      omega
    apply hbad
    intro j
    by_cases hj : j = row
    · subst j
      simp only [raiseWeight, Function.update_self]
      constructor
      · omega
      · have hle := (h row).2
        omega
    · simpa only [raiseWeight, ne_eq, hj, not_false_eq_true, Function.update_of_ne] using h j
  · intro hwall hraise
    have hupper := (hraise row).1
    simp only [raiseWeight, Function.update_self, hwall, add_le_iff_nonpos_right,
      nonpos_iff_eq_zero, one_ne_zero] at hupper

theorem not_interlaces_loweredInternalYoungWeight_iff_lowerWall
    {r : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu) (row : Fin (r + 1))
    (hpositive : 0 < mu row) :
    ¬ Interlaces lam (loweredInternalYoungWeight mu row) ↔
      lam row.succ = mu row := by
  constructor
  · intro hbad
    by_contra hne
    have hstrict : lam row.succ < mu row := by
      have hle := (h row).2
      omega
    apply hbad
    intro j
    by_cases hj : j = row
    · subst j
      simp only [loweredInternalYoungWeight, Function.update_self]
      constructor
      · have hle := (h row).1
        omega
      · omega
    · simpa only [loweredInternalYoungWeight, ne_eq, hj, not_false_eq_true,
        Function.update_of_ne] using h j
  · intro hwall hlower
    have hlowerwall := (hlower row).2
    simp only [hwall, loweredInternalYoungWeight, Function.update_self] at hlowerwall
    omega

theorem negativeStabilizerNode_eq_negativeAmbient_of_upperWall
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hwall : lam row.castSucc = mu row) :
    gtStabilizerArrowheadNode
        (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, false)) =
      signedNode (ambientShift (n + 1) lam)
        (row.castSucc, false) := by
  simp only [gtStabilizerArrowheadNode_neg, stabilizerShift, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right, neg_sub, one_div, signedNode, Bool.false_eq_true, ↓reduceIte,
    ambientShift, hwall, Fin.val_castSucc]
  ring

theorem positiveStabilizerNode_eq_positiveAmbient_of_lowerWall
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hwall : lam row.succ = mu row) :
    gtStabilizerArrowheadNode
        (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, true)) =
      signedNode (ambientShift (n + 1) lam) (row.succ, true) := by
  simp only [gtStabilizerArrowheadNode_pos, stabilizerShift, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right, one_div, signedNode, ↓reduceIte, ambientShift, hwall, Fin.val_succ]
  ring

theorem not_interlaces_raiseAmbient_of_lowerWall
    {r : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hwall : lam row.succ = mu row) :
    ¬ Interlaces (raiseWeight lam row.succ) mu := by
  intro h
  have hbad := (h row).2
  simp only [raiseWeight, hwall, Function.update_self, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
    one_ne_zero] at hbad

theorem not_interlaces_lowerAmbient_of_upperWall
    {r : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hwall : lam row.castSucc = mu row)
    (hpositive : 0 < lam row.castSucc) :
    ¬ Interlaces (loweredInternalYoungWeight lam row.castSucc) mu := by
  intro h
  have hbad := (h row).1
  simp only [loweredInternalYoungWeight, hwall, Function.update_self] at hbad
  omega

theorem gtAxisCompressedCharacteristicMinor_eval_negativeStabilizerNode
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 1)) (hbad : ¬ Interlaces lam (raiseWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) (.inr (row, false))) =
      (gtChannelCharacteristicPolynomial (n + 1) lam).derivative.eval
          (signedNode (ambientShift (n + 1) lam)
            (row.castSucc, false)) *
        gtAxisCompressedSignedProjectorCoefficient lam mu h hgram p q
          (row.castSucc, false) := by
  rw [negativeStabilizerNode_eq_negativeAmbient_of_upperWall lam mu row
    ((not_interlaces_raiseWeight_iff_upperWall lam mu h row).mp hbad)]
  exact gtAxisCompressedCharacteristicMinor_eval_signedNode
    lam mu h hgram hfinite p q (row.castSucc, false)

theorem lowerWall_of_invalid_lower_stabilizer
    {r : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu) (row : Fin (r + 1))
    (hbad : mu row = 0 ∨
      ¬ Interlaces lam (loweredInternalYoungWeight mu row)) :
    lam row.succ = mu row := by
  rcases hbad with hzero | hnot
  · have hle := (h row).2
    omega
  · by_cases hzero : mu row = 0
    · have hle := (h row).2
      omega
    · exact
        (not_interlaces_loweredInternalYoungWeight_iff_lowerWall
          lam mu h row (Nat.pos_of_ne_zero hzero)).mp hnot

theorem gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 1))
    (hbad : mu row = 0 ∨
      ¬ Interlaces lam (loweredInternalYoungWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) (.inr (row, true))) =
      (gtChannelCharacteristicPolynomial (n + 1) lam).derivative.eval
          (signedNode (ambientShift (n + 1) lam) (row.succ, true)) *
        gtAxisCompressedSignedProjectorCoefficient lam mu h hgram p q
          (row.succ, true) := by
  rw [positiveStabilizerNode_eq_positiveAmbient_of_lowerWall lam mu row
    (lowerWall_of_invalid_lower_stabilizer lam mu h row hbad)]
  exact gtAxisCompressedCharacteristicMinor_eval_signedNode
    lam mu h hgram hfinite p q (row.succ, true)

theorem gtAxisCompressedCharacteristicMinor_eval_negativeStabilizerNode_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 1)) (hbad : ¬ Interlaces lam (raiseWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu)
    (hzero : gtAxisCompressedSignedProjectorCoefficient
      lam mu h hgram p q (row.castSucc, false) = 0) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) (.inr (row, false))) = 0 := by
  rw [gtAxisCompressedCharacteristicMinor_eval_negativeStabilizerNode
    lam mu h hgram hfinite row hbad p q, hzero, mul_zero]

theorem gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 1))
    (hbad : mu row = 0 ∨
      ¬ Interlaces lam (loweredInternalYoungWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu)
    (hzero : gtAxisCompressedSignedProjectorCoefficient
      lam mu h hgram p q (row.succ, true) = 0) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) (.inr (row, true))) = 0 := by
  rw [gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode
    lam mu h hgram hfinite row hbad p q, hzero, mul_zero]

end AllRankGTInvalidRowCharacteristicMinorVanishing

end

section


open scoped BigOperators InnerProductSpace

namespace AllRankTensorClebschSpectralProjection

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation

theorem orthogonalChannelSelector_apply_eq_comp_adjoint_of_mem_span
    {ι V : Type*} [DecidableEq ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (P : Module.End ℝ V) (selected : ι)
    (hselector : ∀ (j : ι) (p : E j),
      P (A j p) = if selected = j then A j p else 0)
    (x : V)
    (hx : x ∈ (⨆ j : ι, LinearMap.range (A j).toLinearMap)) :
    P x =
      ((A selected).toLinearMap.comp
        (A selected).toLinearMap.adjoint) x := by
  have hadjoint_zero (i j : ι) (hij : i ≠ j) (p : E j) :
      (A i).toLinearMap.adjoint (A j p) = 0 := by
    apply ext_inner_left ℝ
    intro q
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact horth i j hij q p
  have hadjoint_self (i : ι) (p : E i) :
      (A i).toLinearMap.adjoint (A i p) = p :=
    LinearMap.congr_fun (A i).adjoint_comp_self' p
  let Q : Module.End ℝ V :=
    (A selected).toLinearMap.comp (A selected).toLinearMap.adjoint
  have hle : (⨆ j : ι, LinearMap.range (A j).toLinearMap) ≤
      LinearMap.ker (P - Q) := by
    apply iSup_le
    intro j
    rintro _ ⟨p, rfl⟩
    change (P - Q) (A j p) = 0
    simp only [LinearMap.sub_apply, Q, LinearMap.comp_apply]
    rw [hselector j p]
    by_cases h : selected = j
    · subst j
      simp only [↓reduceIte, hadjoint_self, LinearIsometry.coe_toLinearMap, sub_self]
    · simp only [h, ↓reduceIte, hadjoint_zero selected j h p, map_zero, sub_self]
  have hzero := hle hx
  change (P - Q) x = 0 at hzero
  exact sub_eq_zero.mp hzero

theorem cartanCharacteristicProjector_eq_channel_comp_adjoint_of_complete
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (nodes : ι → ℝ) (hnode : Function.Injective nodes)
    (T : Module.End ℝ V)
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (hcomplete : (⨆ i : ι, LinearMap.range (A i).toLinearMap) = ⊤)
    (heigen : ∀ (i : ι) (p : E i), T (A i p) = nodes i • A i p)
    (selected : ι) :
    cartanCharacteristicInterpolationProjector nodes T selected =
      (A selected).toLinearMap.comp (A selected).toLinearMap.adjoint := by
  have hadjoint_zero (i j : ι) (hij : i ≠ j) (p : E j) :
      (A i).toLinearMap.adjoint (A j p) = 0 := by
    apply ext_inner_left ℝ
    intro q
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact horth i j hij q p
  have hadjoint_self (i : ι) (p : E i) :
      (A i).toLinearMap.adjoint (A i p) = p := by
    exact LinearMap.congr_fun (A i).adjoint_comp_self' p
  let P : Module.End ℝ V :=
    cartanCharacteristicInterpolationProjector nodes T selected
  let Q : Module.End ℝ V :=
    (A selected).toLinearMap.comp (A selected).toLinearMap.adjoint
  have hle : (⨆ j : ι, LinearMap.range (A j).toLinearMap) ≤
      LinearMap.ker (P - Q) := by
    apply iSup_le
    intro j
    rintro _ ⟨p, rfl⟩
    change (P - Q) (A j p) = 0
    simp only [LinearMap.sub_apply, P, Q, LinearMap.comp_apply]
    rw [cartanCharacteristicInterpolationProjector_apply_of_eigenvector
      nodes T hnode selected j (A j p) (heigen j p)]
    by_cases h : selected = j
    · subst j
      simp only [↓reduceIte, hadjoint_self, LinearIsometry.coe_toLinearMap, sub_self]
    · simp only [h, ↓reduceIte, hadjoint_zero selected j h p, map_zero, sub_self]
  rw [hcomplete] at hle
  apply LinearMap.ext
  intro x
  have hx := hle (show x ∈ (⊤ : Submodule ℝ V) from trivial)
  change (P - Q) x = 0 at hx
  exact sub_eq_zero.mp hx

end AllRankTensorClebschSpectralProjection

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTAbsentSignedProjectorOnRetainedSpan

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherChannel

theorem cartanCharacteristicProjector_apply_eq_zero_of_absent_eigenchannel_span
    {κ ι V : Type*} [Fintype κ] [DecidableEq κ]
    [AddCommGroup V] [Module ℝ V]
    {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (nodes : κ → ℝ) (hnode : Function.Injective nodes)
    (T : Module.End ℝ V) (selected : κ)
    (channelIndex : ι → κ)
    (A : (i : ι) → E i →ₗ[ℝ] V)
    (heigen : ∀ (i : ι) (p : E i),
      T (A i p) = nodes (channelIndex i) • A i p)
    (habsent : ∀ i : ι, selected ≠ channelIndex i)
    (x : V) (hx : x ∈ (⨆ i : ι, LinearMap.range (A i))) :
    cartanCharacteristicInterpolationProjector nodes T selected x = 0 := by
  let P := cartanCharacteristicInterpolationProjector nodes T selected
  have hle : (⨆ i : ι, LinearMap.range (A i)) ≤ LinearMap.ker P := by
    apply iSup_le
    intro i
    rintro _ ⟨p, rfl⟩
    change P (A i p) = 0
    dsimp [P]
    rw [cartanCharacteristicInterpolationProjector_apply_of_eigenvector
      nodes T hnode selected (channelIndex i) (A i p) (heigen i p),
      ite_eq_right (habsent i)]
  exact hle hx

theorem cartanCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
    {κ ι V : Type*} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (nodes : κ → ℝ) (hnode : Function.Injective nodes)
    (T : Module.End ℝ V) (selected : κ)
    (channelIndex : ι → κ) (hindex : Function.Injective channelIndex)
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (heigen : ∀ (i : ι) (p : E i),
      T (A i p) = nodes (channelIndex i) • A i p)
    (x : V)
    (hx : x ∈ (⨆ i : ι, LinearMap.range (A i).toLinearMap))
    (hzero : ∀ i : ι, channelIndex i = selected →
      (A i).toLinearMap.adjoint x = 0) :
    cartanCharacteristicInterpolationProjector nodes T selected x = 0 := by
  classical
  by_cases hmatch : ∃ i : ι, channelIndex i = selected
  · obtain ⟨i, hi⟩ := hmatch
    have hselector (j : ι) (p : E j) :
        cartanCharacteristicInterpolationProjector nodes T selected (A j p) =
          if i = j then A j p else 0 := by
      rw [cartanCharacteristicInterpolationProjector_apply_of_eigenvector
        nodes T hnode selected (channelIndex j) (A j p) (heigen j p)]
      by_cases hij : i = j
      · subst j
        simp only [hi, ↓reduceIte]
      · have hne : selected ≠ channelIndex j := by
          intro heq
          exact hij (hindex (hi.trans heq))
        simp only [hne, ↓reduceIte, hij]
    rw [orthogonalChannelSelector_apply_eq_comp_adjoint_of_mem_span
      A horth (cartanCharacteristicInterpolationProjector nodes T selected)
      i hselector x hx, LinearMap.comp_apply, hzero i hi, map_zero]
  · apply cartanCharacteristicProjector_apply_eq_zero_of_absent_eigenchannel_span
      nodes hnode T selected channelIndex (fun i => (A i).toLinearMap)
      heigen _ x hx
    intro i h
    exact hmatch ⟨i, h.symm⟩

theorem gtCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
    {r n : ℕ} (target : Fin (r + 1) → ℕ)
    (mu : Fin r → ℕ) (hfinite : FiniteInterlacing n target mu)
    {ι : Type*}
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (channelIndex : ι → Fin (r + 1) × Bool)
    (hindex : Function.Injective channelIndex)
    (A : (i : ι) → E i →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (heigen : ∀ (i : ι) (p : E i),
      gtRelativeCasimir target (A i p) =
        signedNode (ambientShift n target) (channelIndex i) • A i p)
    (selected : Fin (r + 1) × Bool)
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) target)
    (hx : x ∈ (⨆ i : ι, LinearMap.range (A i).toLinearMap))
    (hzero : ∀ i : ι, channelIndex i = selected →
      (A i).toLinearMap.adjoint x = 0) :
    gtCharacteristicProjector target selected x = 0 := by
  change cartanCharacteristicInterpolationProjector
    (signedNode (ambientShift n target))
      (gtRelativeCasimir target) selected x = 0
  apply cartanCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
    (signedNode (ambientShift n target))
    (signedNode_injective hfinite.ambientShift_pos
      hfinite.ambientShift_strictAnti.injective)
    (gtRelativeCasimir target) selected channelIndex hindex A horth heigen
    x hx hzero

end AllRankGTAbsentSignedProjectorOnRetainedSpan

end

section


namespace AllRankGTInvalidFullBranchExclusion

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidRowCharacteristicMinorVanishing
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem interlaces_of_fullBranchSignature_eq_appendZeroWeight
    {r : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (nu : FullBranchWeight lam)
    (hsignature : fullBranchSignature nu = appendZeroWeight mu) :
    Interlaces lam mu := by
  intro i
  have hi :=
    fullBranchSignature_interlaces_appendZeroWeight lam nu i.castSucc
  rw [hsignature] at hi
  simpa only [appendZeroWeight_castSucc, ← Fin.castSucc_succ] using hi

theorem fullBranchSignature_ne_appendZeroWeight_of_not_interlaces
    {r : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hbad : ¬ Interlaces lam mu)
    (nu : FullBranchWeight lam) :
    fullBranchSignature nu ≠ appendZeroWeight mu := by
  intro heq
  exact hbad
    (interlaces_of_fullBranchSignature_eq_appendZeroWeight lam mu nu heq)

end AllRankGTInvalidFullBranchExclusion

end

section


open scoped BigOperators InnerProductSpace

namespace AllRankGTIllegalStabilizerIntertwiner

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidFullBranchExclusion
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.ThreeRowYoungBranching

private theorem appendZeroWeight_antitone_metriccodes2_2d029a10 {r : ℕ}
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu) :
    Antitone (appendZeroWeight mu) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
      have hj : j = Fin.last (r + 1) := by
        apply Fin.ext
        have hbound := j.isLt
        change r + 1 ≤ j.val at hij
        change j.val = r + 1
        omega
      subst j
      exact le_rfl
  | cast i =>
      induction j using Fin.lastCases with
      | last => simp only [appendZeroWeight_last, appendZeroWeight_castSucc, zero_le]
      | cast j =>
          have hle : i ≤ j := by simpa only [Fin.castSucc_le_castSucc_iff] using hij
          simpa only [appendZeroWeight_castSucc, ge_iff_le] using hmu hle

theorem illegalYoungStabilizerIntertwiner_eq_zero
    {r n : ℕ} (S : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hn : 2 * (r + 2) + 2 ≤ n)
    (hdomS : Antitone S) (hdomMu : Antitone mu)
    (hbad : ¬ Interlaces S mu)
    (A : HarmonicYoungSpace (n := n) (appendZeroWeight mu) →ₗ[ℝ]
      HarmonicYoungSpace (n := n + 1) S)
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation (appendZeroWeight mu) a b) =
        (youngAmbientRotation S a.castSucc b.castSucc).comp A) :
    A = 0 := by
  have hnbranch : 2 * (r + 1) + 5 ≤ n + 1 := by omega
  have hdomPadded := appendZeroWeight_antitone_metriccodes2_2d029a10 mu hdomMu
  have hcross (nu : FullBranchWeight S) :
      (canonicalFullBranchFibre S hnbranch nu).toLinearMap.adjoint.comp A =
        0 := by
    have hne : appendZeroWeight mu ≠ fullBranchSignature nu := by
      intro heq
      exact fullBranchSignature_ne_appendZeroWeight_of_not_interlaces
        S mu hbad nu heq.symm
    apply youngRotationIntertwiner_eq_zero_of_signature_ne
      (by omega : 2 * ((r + 1) + 1) + 2 ≤ n)
      (appendZeroWeight mu) (fullBranchSignature nu)
      hdomPadded hne
    intro a b
    exact crossGram_intertwines_of_skew
      (canonicalFullBranchFibre S hnbranch nu).toLinearMap A
      (youngAmbientRotation (fullBranchSignature nu) a b)
      (youngAmbientRotation (appendZeroWeight mu) a b)
      (youngAmbientRotation S a.castSucc b.castSucc)
      (youngAmbientRotation_adjoint (fullBranchSignature nu) a b)
      (youngAmbientRotation_adjoint S a.castSucc b.castSucc)
      (canonicalFullBranchFibre_rotation_intertwine S hnbranch nu a b)
      (hA a b)
  apply LinearMap.ext
  intro p
  have hsum := canonicalFullBranch_sum_projection
    S hnbranch hdomS (A p)
  have hprojection (nu : FullBranchWeight S) :
      (LinearMap.range
        (canonicalFullBranchFibre S hnbranch nu).toLinearMap).starProjection
          (A p) = 0 := by
    apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
    apply ((LinearMap.range
      (canonicalFullBranchFibre S hnbranch nu).toLinearMap).mem_orthogonal'
        (A p)).mpr
    rintro _ ⟨q, rfl⟩
    have hzero := LinearMap.congr_fun (hcross nu) p
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hzero
    rw [real_inner_comm,
      ← LinearMap.adjoint_inner_right
        (canonicalFullBranchFibre S hnbranch nu).toLinearMap q (A p),
      hzero, inner_zero_right]
  simp only [hprojection, Finset.sum_const_zero] at hsum
  simpa only [LinearMap.zero_apply] using hsum.symm

end AllRankGTIllegalStabilizerIntertwiner

end

end HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherYoungAllRankGTAxisTensorRotationIntertwining

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem euclideanAmbientRotation_castSucc_last
    {n : ℕ} (a b : Fin n) :
    euclideanAmbientRotation a.castSucc b.castSucc
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) = 0 := by
  simp only [EuclideanSpace.basisFun_apply, euclideanAmbientRotation_apply, ne_eq,
    Fin.castSucc_ne_last, not_false_eq_true, PiLp.single_eq_of_ne, zero_smul, sub_self]

theorem canonicalGelfandTsetlinAxisTensor_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (a b : Fin n) :
    (canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram) := by
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply,
    canonicalGelfandTsetlinAxisTensor_apply,
    tensorAmbientRotation_tmul,
    euclideanAmbientRotation_castSucc_last,
    TensorProduct.zero_tmul, zero_add]
  congr 1
  exact LinearMap.congr_fun
    (canonicalGelfandTsetlinFibre_rotation_intertwine
      lam mu h hgram a b) p

end HigherYoungAllRankGTAxisTensorRotationIntertwining

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTNoninterlacingTensorChannelAxisOrthogonality

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTIllegalStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem paddedPieriSource_antitone
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (i : PaddedPieriChannel lam) : Antitone (paddedPieriSource lam i) := by
  cases i with
  | inl row => exact row.property
  | inr row => exact row.property.2

end AllRankGTNoninterlacingTensorChannelAxisOrthogonality

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTInvalidNonterminalProjectorVanishing

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidRowCharacteristicMinorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNoninterlacingTensorChannelAxisOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

/-- The padded pieri signed channel used in the spherical-code argument. -/
def paddedPieriSignedChannel {r : ℕ} (lam : Fin (r + 1) → ℕ) :
    PaddedPieriChannel lam → Fin (r + 1) × Bool
  | Sum.inl row => (row.val, true)
  | Sum.inr row => (row.val, false)

@[simp] theorem paddedPieriSignedChannel_inl {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : PaddedPieriRaiseRow lam) :
    paddedPieriSignedChannel lam (Sum.inl row) = (row.val, true) := rfl

@[simp] theorem paddedPieriSignedChannel_inr {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : PaddedPieriLowerRow lam) :
    paddedPieriSignedChannel lam (Sum.inr row) = (row.val, false) := rfl

theorem paddedPieriSignedChannel_injective {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Function.Injective (paddedPieriSignedChannel lam) := by
  intro i j hij
  cases i with
  | inl a =>
      cases j with
      | inl b =>
          exact congrArg Sum.inl
            (Subtype.ext (congrArg Prod.fst hij))
      | inr b =>
          have hsign := congrArg Prod.snd hij
          simp only [paddedPieriSignedChannel_inl, paddedPieriSignedChannel_inr,
            Bool.true_eq_false] at hsign
  | inr a =>
      cases j with
      | inl b =>
          have hsign := congrArg Prod.snd hij
          simp only [paddedPieriSignedChannel_inr, paddedPieriSignedChannel_inl,
            Bool.false_eq_true] at hsign
      | inr b =>
          exact congrArg Sum.inr
            (Subtype.ext (congrArg Prod.fst hij))

theorem paddedOrthogonalTensorPieriChannel_relativeCasimir
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (i : PaddedPieriChannel target)
    (p : HarmonicYoungSpace (n := n) (paddedPieriSource target i)) :
    gtRelativeCasimir target
        (paddedOrthogonalTensorPieriChannel hn target hdom i p) =
      signedNode (HigherChannel.ambientShift n target)
        (paddedPieriSignedChannel target i) •
        paddedOrthogonalTensorPieriChannel hn target hdom i p := by
  cases i with
  | inl row =>
      exact gtRelativeCasimir_raise_channel target row.val
        (paddedOrthogonalTensorPieriChannel hn target hdom
          (Sum.inl row)).toLinearMap
        (paddedOrthogonalTensorPieriChannel_rotation_intertwine
          hn target hdom (Sum.inl row)) p
  | inr row =>
      have hsource : target =
          raiseWeight (paddedPieriSource target (Sum.inr row)) row.val :=
        (raiseWeight_loweredInternalYoungWeight
          target row.val row.property.1).symm
      exact gtRelativeCasimir_lower_channel target
        (paddedPieriSource target (Sum.inr row)) row.val hsource
        (paddedOrthogonalTensorPieriChannel hn target hdom
          (Sum.inr row)).toLinearMap
        (paddedOrthogonalTensorPieriChannel_rotation_intertwine
          hn target hdom (Sum.inr row)) p

end AllRankGTInvalidNonterminalProjectorVanishing

namespace AllRankGTRelativeCasimirCompressedResolvent

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

theorem gtTensorCasimir_adjoint
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    (gtTensorCasimir (n := n) lam).adjoint =
      gtTensorCasimir (n := n) lam := by
  unfold gtTensorCasimir
  simp only [Finset.sum_neg_distrib, smul_neg, map_neg, map_smul, map_sum, LinearMap.adjoint_comp,
    tensorAmbientRotation_adjoint, LinearMap.comp_neg, LinearMap.neg_comp, neg_neg]

theorem gtRelativeCasimir_adjoint
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    (gtRelativeCasimir (n := n) lam).adjoint =
      gtRelativeCasimir (n := n) lam := by
  unfold gtRelativeCasimir
  simp only [map_smul, map_sub, gtTensorCasimir_adjoint, LinearMap.IsSymmetric.id,
    LinearMap.IsSymmetric.adjoint_eq]

theorem gtRelativeCasimir_isSymmetric
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    (gtRelativeCasimir (n := n) lam).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint,
    LinearMap.isSelfAdjoint_iff']
  exact gtRelativeCasimir_adjoint (n := n) lam

theorem gtRelativeCasimir_eigen_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (u v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (s t : ℝ)
    (hu : gtRelativeCasimir lam u = s • u)
    (hv : gtRelativeCasimir lam v = t • v)
    (hne : s ≠ t) :
    ⟪u, v⟫_ℝ = 0 := by
  have hsym := gtRelativeCasimir_isSymmetric lam u v
  rw [hu, hv] at hsym
  rw [real_inner_smul_left u v s,
    real_inner_smul_right u v t] at hsym
  have hmul : (s - t) * ⟪u, v⟫_ℝ = 0 := by
    nlinarith
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)

end AllRankGTRelativeCasimirCompressedResolvent

namespace AllRankGTTransportedPieriOrthogonality

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching

/-- The physical padded pieri channel used in the spherical-code argument. -/
def physicalPaddedPieriChannel {r n : ℕ}
    (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (i : PaddedPieriChannel (appendZeroWeight lam)) :
    HarmonicYoungSpace (n := n)
        (paddedPieriSource (appendZeroWeight lam) i) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) lam) :=
  (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearIsometry.comp
    (paddedOrthogonalTensorPieriChannel hn (appendZeroWeight lam) hdom i)

theorem physicalPaddedPieriChannel_inner_eq_zero {r n : ℕ}
    (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (i j : PaddedPieriChannel (appendZeroWeight lam)) (hij : i ≠ j)
    (p : HarmonicYoungSpace (n := n)
      (paddedPieriSource (appendZeroWeight lam) i))
    (q : HarmonicYoungSpace (n := n)
      (paddedPieriSource (appendZeroWeight lam) j)) :
    ⟪physicalPaddedPieriChannel hn lam hdom i p,
      physicalPaddedPieriChannel hn lam hdom j q⟫_ℝ = 0 := by
  change
    ⟪(zeroRowTensorIsometryEquiv (n := n) lam).symm
        (paddedOrthogonalTensorPieriChannel hn
          (appendZeroWeight lam) hdom i p),
      (zeroRowTensorIsometryEquiv (n := n) lam).symm
        (paddedOrthogonalTensorPieriChannel hn
          (appendZeroWeight lam) hdom j q)⟫_ℝ = 0
  rw [(zeroRowTensorIsometryEquiv (n := n) lam).symm.inner_map_map]
  have hne :
      paddedPieriSource (appendZeroWeight lam) i ≠
        paddedPieriSource (appendZeroWeight lam) j := by
    intro heq
    exact hij (paddedPieriSource_injective (appendZeroWeight lam) heq)
  have hzero := allRankYoungChannel_crossGram_eq_zero_of_oneBoxNeighbors
    (by omega) (appendZeroWeight lam)
    (paddedPieriSource (appendZeroWeight lam) i)
    (paddedPieriSource (appendZeroWeight lam) j)
    hdom
    (paddedPieriSource_isOneBoxNeighbor (appendZeroWeight lam) i)
    (paddedPieriSource_isOneBoxNeighbor (appendZeroWeight lam) j)
    hne
    (paddedOrthogonalTensorPieriChannel hn
      (appendZeroWeight lam) hdom i).toLinearMap
    (paddedOrthogonalTensorPieriChannel hn
      (appendZeroWeight lam) hdom j).toLinearMap
    (paddedOrthogonalTensorPieriChannel_rotation_intertwine hn
      (appendZeroWeight lam) hdom i)
    (paddedOrthogonalTensorPieriChannel_rotation_intertwine hn
      (appendZeroWeight lam) hdom j)
  calc
    ⟪paddedOrthogonalTensorPieriChannel hn
        (appendZeroWeight lam) hdom i p,
      paddedOrthogonalTensorPieriChannel hn
        (appendZeroWeight lam) hdom j q⟫_ℝ =
        ⟪p, (paddedOrthogonalTensorPieriChannel hn
          (appendZeroWeight lam) hdom i).toLinearMap.adjoint
            (paddedOrthogonalTensorPieriChannel hn
              (appendZeroWeight lam) hdom j q)⟫_ℝ :=
      (LinearMap.adjoint_inner_right
        (paddedOrthogonalTensorPieriChannel hn
          (appendZeroWeight lam) hdom i).toLinearMap p
        (paddedOrthogonalTensorPieriChannel hn
          (appendZeroWeight lam) hdom j q)).symm
    _ = 0 := by
      have hz :
          (paddedOrthogonalTensorPieriChannel hn
            (appendZeroWeight lam) hdom i).toLinearMap.adjoint
              (paddedOrthogonalTensorPieriChannel hn
                (appendZeroWeight lam) hdom j q) = 0 := by
        simpa only [LinearMap.coe_comp, LinearIsometry.coe_toLinearMap, Function.comp_apply,
          LinearMap.zero_apply] using LinearMap.congr_fun hzero q
      rw [hz]
      exact @inner_zero_right ℝ
        (HarmonicYoungSpace (n := n)
          (paddedPieriSource (appendZeroWeight lam) i)) _ _ _ p

theorem physicalPaddedPieriChannel_finrank {r n : ℕ}
    (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam)) :
    Module.finrank ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) lam) =
      ∑ i : PaddedPieriChannel (appendZeroWeight lam),
        Module.finrank ℝ
          (HarmonicYoungSpace (n := n)
            (paddedPieriSource (appendZeroWeight lam) i)) := by
  calc
    Module.finrank ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) lam) =
        Module.finrank ℝ
          (SpherePacking.Euclidean n ⊗[ℝ]
            HarmonicYoungSpace (n := n) (appendZeroWeight lam)) :=
      (zeroRowTensorIsometryEquiv (n := n) lam).toLinearEquiv.finrank_eq
    _ = n * Module.finrank ℝ
          (HarmonicYoungSpace (n := n) (appendZeroWeight lam)) := by
      rw [Module.finrank_tensorProduct]
      simp only [SpherePacking.Euclidean, finrank_euclideanSpace, Fintype.card_fin]
    _ = _ := paddedOrthogonalTensorPieri_finrank hn
      (appendZeroWeight lam) hdom (appendZeroWeight_last lam)

end AllRankGTTransportedPieriOrthogonality

namespace AllRankGTTransverseWignerEckartHighest

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching

private def appendZeroRowIsometryEquiv_of_weight_eq
    {r n : ℕ} (physicalSource : Fin (r + 1) → ℕ)
    (paddedSource : Fin (r + 2) → ℕ)
    (hweight : paddedSource = appendZeroWeight physicalSource) :
    HarmonicYoungSpace (n := n) physicalSource ≃ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n) paddedSource := by
  rw [hweight]
  exact appendZeroRowIsometryEquiv physicalSource

private def paddedSelectedYoungSourceIsometryEquiv
    {r n : ℕ} (target physicalSource : Fin (r + 1) → ℕ)
    (selected : PaddedPieriChannel (appendZeroWeight target))
    (hselected : paddedPieriSource (appendZeroWeight target) selected =
      appendZeroWeight physicalSource) :
    HarmonicYoungSpace (n := n) physicalSource ≃ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n)
        (paddedPieriSource (appendZeroWeight target) selected) :=
  appendZeroRowIsometryEquiv_of_weight_eq
    physicalSource (paddedPieriSource (appendZeroWeight target) selected)
    hselected

end AllRankGTTransverseWignerEckartHighest

end

end HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungAllRankOrthogonalEigenchannelEigenspace

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection

theorem orthogonalEigenchannel_eigenspace_eq_range
    {ι V : Type*} [Finite ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (nodes : ι → ℝ) (hnode : Function.Injective nodes)
    (T : Module.End ℝ V)
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (hcomplete : (⨆ i : ι, LinearMap.range (A i).toLinearMap) = ⊤)
    (heigen : ∀ (i : ι) (p : E i), T (A i p) = nodes i • A i p)
    (selected : ι) :
    Module.End.eigenspace T (nodes selected) =
      LinearMap.range (A selected).toLinearMap := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  apply le_antisymm
  · intro x hx
    have hxeigen := (Module.End.mem_eigenspace_iff).mp hx
    have hselector :
        cartanCharacteristicInterpolationProjector nodes T selected x = x := by
      simpa only [↓reduceIte] using
        cartanCharacteristicInterpolationProjector_apply_of_eigenvector nodes T hnode selected
          selected x hxeigen
    have hproject := LinearMap.congr_fun
      (cartanCharacteristicProjector_eq_channel_comp_adjoint_of_complete
        nodes hnode T A horth hcomplete heigen selected) x
    rw [hselector] at hproject
    exact ⟨(A selected).toLinearMap.adjoint x, hproject.symm⟩
  · rintro _ ⟨y, rfl⟩
    exact (Module.End.mem_eigenspace_iff).mpr (heigen selected y)

theorem orthogonalEigenchannel_eigenspace_eq_range_of_finrank
    {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (nodes : ι → ℝ) (hnode : Function.Injective nodes)
    (T : Module.End ℝ V)
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i))
    (heigen : ∀ (i : ι) (p : E i), T (A i p) = nodes i • A i p)
    (selected : ι) :
    Module.End.eigenspace T (nodes selected) =
      LinearMap.range (A selected).toLinearMap :=
  orthogonalEigenchannel_eigenspace_eq_range nodes hnode T A horth
    (orthogonalBranch_iSup_range_eq_top A horth hdim) heigen selected

end HigherYoungAllRankOrthogonalEigenchannelEigenspace

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTSelectedPhysicalChannelRange

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartHighest
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankGTAppendedRowLegality
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalEigenchannelEigenspace
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem physicalPaddedPieriChannel_relativeCasimir
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (low : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight low))
    (channel : PaddedPieriChannel (appendZeroWeight low))
    (q : HarmonicYoungSpace (n := n)
      (paddedPieriSource (appendZeroWeight low) channel)) :
    gtRelativeCasimir low
        (physicalPaddedPieriChannel hn low hdom channel q) =
      signedNode (HigherChannel.ambientShift n (appendZeroWeight low))
          (paddedPieriSignedChannel (appendZeroWeight low) channel) •
        physicalPaddedPieriChannel hn low hdom channel q := by
  exact zeroRowTransportPaddedPieriChannel_eigen_of_intertwine
    low (paddedOrthogonalTensorPieriChannel
      hn (appendZeroWeight low) hdom channel)
    (zeroRowTensorIsometryEquiv_symm_relativeCasimir_intertwine low).symm
    (signedNode (HigherChannel.ambientShift n (appendZeroWeight low))
      (paddedPieriSignedChannel (appendZeroWeight low) channel)) q
    (paddedOrthogonalTensorPieriChannel_relativeCasimir
      hn (appendZeroWeight low) hdom channel q)

theorem selectedSignedEigenspace_le_youngClebschLower_range
    {r n : ℕ} (hn : 2 * (r + 2) + 4 ≤ n + 1)
    (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hfinite : FiniteInterlacing (n + 1) low mu)
    (hdom : Antitone low)
    (row : Fin (r + 2))
    (hhigh : Antitone (raiseWeight low row)) :
    Module.End.eigenspace (gtRelativeCasimir (n := n + 1) low)
        (signedNode (HigherChannel.ambientShift (n + 1) low)
          (row, true)) ≤
      LinearMap.range
        (youngClebschLower low (raiseWeight low row)
          (sum_raiseWeight low row) row) := by
  classical
  let padded := appendZeroWeight low
  have hpadded : Antitone padded := appendZeroWeight_antitone low hdom
  have hraised : Antitone (raiseWeight padded row.castSucc) := by
    rw [raiseWeight_appendZeroWeight_castSucc]
    exact appendZeroWeight_antitone (raiseWeight low row) hhigh
  let selected : PaddedPieriChannel padded :=
    Sum.inl ⟨row.castSucc, hraised⟩
  have hselected : paddedPieriSource padded selected =
      appendZeroWeight (raiseWeight low row) :=
    raiseWeight_appendZeroWeight_castSucc low row
  have hpadInter : Interlaces padded (appendZeroWeight mu) := by
    have h := fullBranchSignature_interlaces_appendZeroWeight low
      (fullBranchOfInterlaces mu hfinite.2)
    rw [fullBranchOfInterlaces_signature_eq_appendZeroWeight mu hfinite.2] at h
    simpa only [padded] using h
  have hpadFinite : FiniteInterlacing (n + 1) padded
      (appendZeroWeight mu) := ⟨hn, hpadInter⟩
  let F := physicalPaddedPieriChannel hn low hpadded
  let G := normalizedPaddedPieriLower (n := n + 1)
    low hdom row hhigh
  let nodes : PaddedPieriChannel padded → ℝ := fun channel =>
    signedNode (HigherChannel.ambientShift (n + 1) padded)
      (paddedPieriSignedChannel padded channel)
  have hnodes : Function.Injective nodes := by
    intro i j hij
    apply paddedPieriSignedChannel_injective padded
    exact signedAmbientCharacteristicNodes_injective hpadFinite hij
  have horth := physicalPaddedPieriChannel_inner_eq_zero hn low hpadded
  have hdim := physicalPaddedPieriChannel_finrank hn low hpadded
  have hnode :
      signedNode (HigherChannel.ambientShift (n + 1) low) (row, true) =
        nodes selected := by
    change HigherChannel.ambientShift (n + 1) low row =
      HigherChannel.ambientShift (n + 1) (appendZeroWeight low) row.castSucc
    exact (ambientShift_appendZeroWeight_castSucc low row).symm
  have hspectral : Module.End.eigenspace (gtRelativeCasimir low)
      (nodes selected) = LinearMap.range (F selected).toLinearMap := by
    apply orthogonalEigenchannel_eigenspace_eq_range_of_finrank
      nodes hnodes (gtRelativeCasimir low) F horth hdim
    intro channel q
    exact physicalPaddedPieriChannel_relativeCasimir
      hn low hpadded channel q
  have hcross : ∀ other : PaddedPieriChannel padded, other ≠ selected →
      ∀ p : HarmonicYoungSpace (n := n + 1) (raiseWeight low row),
      ∀ q : HarmonicYoungSpace (n := n + 1)
        (paddedPieriSource padded other),
        ⟪G p, F other q⟫_ℝ = 0 := by
    intro other hother p q
    apply gtRelativeCasimir_eigen_inner_eq_zero low (G p) (F other q)
      (signedNode (HigherChannel.ambientShift (n + 1) low) (row, true))
      (nodes other)
    · exact gtRelativeCasimir_raise_channel low row G.toLinearMap
        (normalizedPaddedPieriLower_rotation_intertwine
          low hdom row hhigh) p
    · exact physicalPaddedPieriChannel_relativeCasimir
        hn low hpadded other q
    · intro heq
      rw [hnode] at heq
      exact hother (hnodes heq).symm
  have hGrange : LinearMap.range G.toLinearMap =
      LinearMap.range (F selected).toLinearMap :=
    orthogonalBranch_range_eq_of_cross_orthogonal_of_equiv
      F horth hdim G selected hcross
      (paddedSelectedYoungSourceIsometryEquiv
        low (raiseWeight low row) selected hselected)
  have hGphysical : LinearMap.range G.toLinearMap =
      LinearMap.range
        (youngClebschLower low (raiseWeight low row)
          (sum_raiseWeight low row) row) := by
    dsimp only [G]
    rw [normalizedPaddedPieriLower_toLinearMap, LinearMap.range_smul]
    exact inv_ne_zero
      (Real.sqrt_pos.2
        (internalRowLowerGramScalar_raiseWeight_pos low hdom row)).ne'
  intro v hv
  rw [hnode, hspectral, ← hGrange, hGphysical] at hv
  exact hv

end AllRankGTSelectedPhysicalChannelRange

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTSelectedRestrictedProjectorEquality

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherRepresentationGraph

private def gtSelectedPhysicalSignedSpan {r n : ℕ}
    (low : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    Submodule ℝ
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) low) :=
  LinearMap.range
      (youngClebschLower low (raiseWeight low row)
        (sum_raiseWeight low row) row) ⊔
    ⨆ channel : {channel : Fin (r + 1) × Bool //
        channel ≠ (row, true)},
      Module.End.eigenspace (gtRelativeCasimir (n := n) low)
        (signedNode (HigherChannel.ambientShift n low) channel.val)

theorem youngClebschLower_adjoint_signedEigen_eq_zero
    {r n : ℕ} (low : Fin (r + 1) → ℕ)
    (mu : Fin r → ℕ) (hfinite : FiniteInterlacing n low mu)
    (row : Fin (r + 1)) (channel : Fin (r + 1) × Bool)
    (hne : channel ≠ (row, true))
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) low)
    (hv : gtRelativeCasimir low v =
      signedNode (HigherChannel.ambientShift n low) channel • v) :
    (youngClebschLower low (raiseWeight low row)
      (sum_raiseWeight low row) row).adjoint v = 0 := by
  apply ext_inner_left ℝ
  intro p
  rw [LinearMap.adjoint_inner_right, inner_zero_right]
  apply gtRelativeCasimir_eigen_inner_eq_zero low
    (youngClebschLower low (raiseWeight low row)
      (sum_raiseWeight low row) row p) v
    (signedNode (HigherChannel.ambientShift n low) (row, true))
    (signedNode (HigherChannel.ambientShift n low) channel)
  · exact gtRelativeCasimir_raise_channel low row
      (youngClebschLower low (raiseWeight low row)
        (sum_raiseWeight low row) row)
      (fun a b => ClebschRotation.youngClebschLower_rotation_intertwine
        low (raiseWeight low row) (sum_raiseWeight low row) row a b) p
  · exact hv
  · intro heq
    apply hne
    exact (signedAmbientCharacteristicNodes_injective hfinite heq).symm

theorem gtSelectedRowClebschRangeProjector_signedEigen_eq_zero
    {r n : ℕ} (low : Fin (r + 1) → ℕ)
    (mu : Fin r → ℕ) (hfinite : FiniteInterlacing n low mu)
    (row : Fin (r + 1)) (channel : Fin (r + 1) × Bool)
    (hne : channel ≠ (row, true))
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) low)
    (hv : gtRelativeCasimir low v =
      signedNode (HigherChannel.ambientShift n low) channel • v) :
    gtSelectedRowClebschRangeProjector low row v = 0 := by
  unfold gtSelectedRowClebschRangeProjector
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [youngClebschLower_adjoint_signedEigen_eq_zero
    low mu hfinite row channel hne v hv, map_zero, smul_zero]

theorem allRankCartanCharacteristicProjector_eq_selectedClebsch_of_mem_physicalSignedSpan
    {r n : ℕ} (low : Fin (r + 1) → ℕ)
    (mu : Fin r → ℕ) (hfinite : FiniteInterlacing n low mu)
    (hdom : Antitone low) (row : Fin (r + 1))
    (hhigh : Antitone (raiseWeight low row))
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) low)
    (hv : v ∈ gtSelectedPhysicalSignedSpan (n := n) low row) :
    allRankCartanCharacteristicProjector low (row, true) v =
      gtSelectedRowClebschRangeProjector low row v := by
  let P := allRankCartanCharacteristicProjector (n := n) low (row, true)
  let Q := gtSelectedRowClebschRangeProjector (n := n) low row
  have hle : gtSelectedPhysicalSignedSpan (n := n) low row ≤
      LinearMap.ker (P - Q) := by
    unfold gtSelectedPhysicalSignedSpan
    apply sup_le
    · rintro _ ⟨p, rfl⟩
      change
        (P - Q)
            (youngClebschLower low (raiseWeight low row)
              (sum_raiseWeight low row) row p) = 0
      change
        allRankCartanCharacteristicProjector low (row, true)
            (youngClebschLower low (raiseWeight low row)
              (sum_raiseWeight low row) row p) -
          gtSelectedRowClebschRangeProjector low row
            (youngClebschLower low (raiseWeight low row)
              (sum_raiseWeight low row) row p) = 0
      rw [allRankCartanCharacteristicProjector_youngClebschLower
        low mu hfinite (row, true) row,
        gtSelectedRowClebschRangeProjector_youngClebschLower
          low hdom row hhigh]
      simp only [↓reduceIte, youngClebschLower_apply, EuclideanSpace.basisFun_apply, sub_self]
    · apply iSup_le
      intro channel v hv
      have heigen := (Module.End.mem_eigenspace_iff).mp hv
      change (P - Q) v = 0
      change
        allRankCartanCharacteristicProjector low (row, true) v -
          gtSelectedRowClebschRangeProjector low row v = 0
      rw [allRankCartanCharacteristicProjector_apply_eigenvector
        low mu hfinite (row, true) channel.val v heigen,
        gtSelectedRowClebschRangeProjector_signedEigen_eq_zero
          low mu hfinite row channel.val channel.property v heigen]
      simp only [ne_eq, Ne.symm channel.property, ↓reduceIte, sub_self]
  have hzero := hle hv
  change (P - Q) v = 0 at hzero
  exact sub_eq_zero.mp hzero

theorem gtSignedEigenvectorSpan_le_selectedPhysicalSignedSpan
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hselected :
      Module.End.eigenspace (gtRelativeCasimir (n := n) low)
        (signedNode (HigherChannel.ambientShift n low) (row, true)) ≤
      LinearMap.range
        (youngClebschLower low (raiseWeight low row)
          (sum_raiseWeight low row) row)) :
    gtSignedEigenvectorSpan (n := n) low ≤
      gtSelectedPhysicalSignedSpan (n := n) low row := by
  unfold gtSignedEigenvectorSpan gtSelectedPhysicalSignedSpan
  apply iSup_le
  intro channel
  by_cases hchannel : channel = (row, true)
  · subst channel
    exact hselected.trans le_sup_left
  · exact
      (le_iSup
        (fun channel : {channel : Fin (r + 1) × Bool //
          channel ≠ (row, true)} =>
          Module.End.eigenspace (gtRelativeCasimir (n := n) low)
            (signedNode (HigherChannel.ambientShift n low) channel.val))
        ⟨channel, hchannel⟩).trans le_sup_right

end AllRankGTSelectedRestrictedProjectorEquality

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTAppendedClebschOrthogonality

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedRowExclusion
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching

/-- The appended full branch pieri lower used in the spherical-code argument. -/
def appendedFullBranchPieriLower
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    HarmonicYoungSpace (n := n) (fullBranchSignature nu) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight lam)) :=
  (normalizedPaddedPieriLower (n := n + 1)
    (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource).toLinearMap.comp
      (canonicalFullBranchFibre
        (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))) hn nu).toLinearMap

theorem appendedFullBranchPieriLower_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (a b : Fin n) :
    (appendedFullBranchPieriLower lam hdominant hsource hn nu).comp
        (youngAmbientRotation (fullBranchSignature nu) a b) =
      (tensorAmbientRotation (appendZeroWeight lam)
        a.castSucc b.castSucc).comp
          (appendedFullBranchPieriLower lam hdominant hsource hn nu) := by
  let C := (normalizedPaddedPieriLower (n := n + 1)
    (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource).toLinearMap
  let F := (canonicalFullBranchFibre
    (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))) hn nu).toLinearMap
  apply LinearMap.ext
  intro p
  change C (F (youngAmbientRotation (fullBranchSignature nu) a b p)) =
    tensorAmbientRotation (appendZeroWeight lam)
      a.castSucc b.castSucc (C (F p))
  have hF := LinearMap.congr_fun
    (canonicalFullBranchFibre_rotation_intertwine
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))
      hn nu a b) p
  have hC := LinearMap.congr_fun
    (normalizedPaddedPieriLower_rotation_intertwine
      (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource
      a.castSucc b.castSucc) (F p)
  exact (congrArg C hF).trans hC

end AllRankGTAppendedClebschOrthogonality

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTAppendedPieriPhysicalAxisOrthogonality

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedClebschOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedRowExclusion
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching

private theorem appendZeroWeight_antitone_metriccodes2_17c0be6a {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    Antitone (appendZeroWeight lam) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
      have hj : j = Fin.last (r + 1) := by
        apply Fin.ext
        have hbound := j.isLt
        change r + 1 ≤ j.val at hij
        change j.val = r + 1
        omega
      subst j
      exact le_rfl
  | cast i =>
      induction j using Fin.lastCases with
      | last => simp only [appendZeroWeight_last, appendZeroWeight_castSucc, zero_le]
      | cast j =>
          have hle : i ≤ j := by simpa only [Fin.castSucc_le_castSucc_iff] using hij
          simpa only [appendZeroWeight_castSucc, ge_iff_le] using hdom hle

/-- The original padded selected axis tensor used in the spherical-code argument. -/
def originalPaddedSelectedAxisTensor
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h) :
    HarmonicYoungSpace (n := n)
        (appendZeroWeight (appendZeroWeight mu)) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight lam)) :=
  (zeroRowTensorIsometryEquiv (n := n + 1) lam).toLinearMap.comp
    ((canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp
      ((appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap.comp
        (appendZeroRowIsometryEquiv
          (n := n) (appendZeroWeight mu)).symm.toLinearMap))

theorem originalPaddedSelectedAxisTensor_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (a b : Fin n) :
    (originalPaddedSelectedAxisTensor lam mu h hgram).comp
        (youngAmbientRotation
          (appendZeroWeight (appendZeroWeight mu)) a b) =
      (tensorAmbientRotation (appendZeroWeight lam)
        a.castSucc b.castSucc).comp
          (originalPaddedSelectedAxisTensor lam mu h hgram) := by
  let T := (zeroRowTensorIsometryEquiv (n := n + 1) lam).toLinearMap
  let A := canonicalGelfandTsetlinAxisTensor lam mu h hgram
  let Z := (appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap
  let W := (appendZeroRowIsometryEquiv
    (n := n) (appendZeroWeight mu)).symm.toLinearMap
  apply LinearMap.ext
  intro p
  change T (A (Z (W (youngAmbientRotation
    (appendZeroWeight (appendZeroWeight mu)) a b p)))) =
    tensorAmbientRotation (appendZeroWeight lam)
      a.castSucc b.castSucc (T (A (Z (W p))))
  have hW := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_symm_rotation_intertwine
      (appendZeroWeight mu) a b) p
  have hZ := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_symm_rotation_intertwine
      mu a b) (W p)
  have hA := LinearMap.congr_fun
    (canonicalGelfandTsetlinAxisTensor_rotation_intertwine
      lam mu h hgram a b) (Z (W p))
  have hT := LinearMap.congr_fun
    (zeroRowTensorIsometryEquiv_rotation_intertwine
      lam a.castSucc b.castSucc) (A (Z (W p)))
  exact (congrArg (fun q => T (A (Z q))) hW).trans
    ((congrArg (fun q => T (A q)) hZ).trans
      ((congrArg T hA).trans hT))

private def originalAppendedFullBranchAxisCrossGram
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    HarmonicYoungSpace (n := n)
        (appendZeroWeight (appendZeroWeight mu)) →ₗ[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature nu) :=
  (appendedFullBranchPieriLower lam hdominant hsource hn nu).adjoint.comp
    (originalPaddedSelectedAxisTensor lam mu h hgram)

theorem originalAppendedFullBranchAxisCrossGram_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    originalAppendedFullBranchAxisCrossGram
      lam mu h hgram hdominant hsource hn nu = 0 := by
  have hmu : Antitone (appendZeroWeight (appendZeroWeight mu)) :=
    appendZeroWeight_antitone_metriccodes2_17c0be6a (appendZeroWeight mu)
      (appendZeroWeight_antitone_metriccodes2_17c0be6a mu
        (interlaces_antitone_stabilizer h))
  apply youngRotationIntertwiner_eq_zero_of_signature_ne
    (by omega)
    (appendZeroWeight (appendZeroWeight mu)) (fullBranchSignature nu)
    hmu (Ne.symm (appendedRowFullBranchSignature_ne_appendZero lam mu nu))
  intro a b
  exact crossGram_intertwines_of_skew
    (appendedFullBranchPieriLower lam hdominant hsource hn nu)
    (originalPaddedSelectedAxisTensor lam mu h hgram)
    (youngAmbientRotation (fullBranchSignature nu) a b)
    (youngAmbientRotation (appendZeroWeight (appendZeroWeight mu)) a b)
    (tensorAmbientRotation (appendZeroWeight lam) a.castSucc b.castSucc)
    (youngAmbientRotation_adjoint (fullBranchSignature nu) a b)
    (tensorAmbientRotation_adjoint (appendZeroWeight lam)
      a.castSucc b.castSucc)
    (appendedFullBranchPieriLower_rotation_intertwine
      lam hdominant hsource hn nu a b)
    (originalPaddedSelectedAxisTensor_rotation_intertwine
      lam mu h hgram a b)

theorem originalAppendedFullBranchAxis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (p : HarmonicYoungSpace (n := n)
      (appendZeroWeight (appendZeroWeight mu)))
    (q : HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪originalPaddedSelectedAxisTensor lam mu h hgram p,
      appendedFullBranchPieriLower lam hdominant hsource hn nu q⟫_ℝ = 0 := by
  let A := originalPaddedSelectedAxisTensor lam mu h hgram
  let B := appendedFullBranchPieriLower lam hdominant hsource hn nu
  have hzero := LinearMap.congr_fun
    (originalAppendedFullBranchAxisCrossGram_eq_zero
      lam mu h hgram hdominant hsource hn nu) p
  have hz : B.adjoint (A p) = 0 := by
    simpa only [originalAppendedFullBranchAxisCrossGram,
      LinearMap.comp_apply, LinearMap.zero_apply] using hzero
  change ⟪A p, B q⟫_ℝ = 0
  calc
    ⟪A p, B q⟫_ℝ = ⟪B.adjoint (A p), q⟫_ℝ :=
      (LinearMap.adjoint_inner_left B q (A p)).symm
    _ = 0 := by
      rw [hz, young_inner_eq_polynomialInner,
        SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _

theorem appendedPaddedPieriLower_adjoint_originalPaddedSelectedAxisTensor_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1) :
    (normalizedPaddedPieriLower (n := n + 1)
      (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource).adjoint.comp
        (originalPaddedSelectedAxisTensor lam mu h hgram) = 0 := by
  classical
  let source := raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))
  let C := (normalizedPaddedPieriLower (n := n + 1)
    (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource).toLinearMap
  let A := originalPaddedSelectedAxisTensor lam mu h hgram
  apply LinearMap.ext
  intro p
  change C.adjoint (A p) = 0
  apply ext_inner_left ℝ
  intro q
  rw [inner_zero_right]
  have hsum := canonicalFullBranch_sum_projection source hn hsource q
  rw [← hsum, sum_inner]
  apply Finset.sum_eq_zero
  intro nu _
  let F := (canonicalFullBranchFibre source hn nu).toLinearMap
  obtain ⟨z, hz⟩ := Submodule.starProjection_apply_mem
    (LinearMap.range F) q
  change F z = (LinearMap.range F).starProjection q at hz
  rw [← hz]
  calc
    ⟪F z, C.adjoint (A p)⟫_ℝ = ⟪C (F z), A p⟫_ℝ :=
      LinearMap.adjoint_inner_right C (F z) (A p)
    _ = ⟪A p, C (F z)⟫_ℝ := real_inner_comm (A p) (C (F z))
    _ = 0 := originalAppendedFullBranchAxis_inner_eq_zero
      lam mu h hgram hdominant hsource hn nu p z

theorem appendedPaddedPieriLower_originalCanonicalAxis_orthogonal
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n + 1)
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    ⟪zeroRowTensorIsometryEquiv (n := n + 1) lam
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram p),
      normalizedPaddedPieriLower (n := n + 1)
        (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource q⟫_ℝ =
      0 := by
  let C := (normalizedPaddedPieriLower (n := n + 1)
    (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource).toLinearMap
  let A := originalPaddedSelectedAxisTensor lam mu h hgram
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  let W := appendZeroRowIsometryEquiv (n := n) (appendZeroWeight mu)
  have hzero := LinearMap.congr_fun
    (appendedPaddedPieriLower_adjoint_originalPaddedSelectedAxisTensor_eq_zero
      lam mu h hgram hdominant hsource hn) (W (Z p))
  have hz : C.adjoint
      (zeroRowTensorIsometryEquiv (n := n + 1) lam
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)) = 0 := by
    change C.adjoint (A (W (Z p))) = 0 at hzero
    change C.adjoint
      (zeroRowTensorIsometryEquiv (n := n + 1) lam
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram
          (Z.symm (W.symm (W (Z p)))))) = 0 at hzero
    rw [W.symm_apply_apply, Z.symm_apply_apply] at hzero
    exact hzero
  calc
    ⟪zeroRowTensorIsometryEquiv (n := n + 1) lam
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram p), C q⟫_ℝ =
      ⟪C.adjoint (zeroRowTensorIsometryEquiv (n := n + 1) lam
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)), q⟫_ℝ :=
        (LinearMap.adjoint_inner_left C q _).symm
    _ = 0 := by
      rw [hz, young_inner_eq_polynomialInner,
        SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _

theorem paddedOrthogonalTensorPieriChannel_appended_originalCanonicalAxis_orthogonal
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n + 1)
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdominant
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0 := by
  let T := zeroRowTensorIsometryEquiv (n := n + 1) lam
  let x := canonicalGelfandTsetlinAxisTensor lam mu h hgram p
  let y := normalizedPaddedPieriLower (n := n + 1)
    (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource q
  change ⟪x, T.symm y⟫_ℝ = 0
  calc
    ⟪x, T.symm y⟫_ℝ = ⟪T x, T (T.symm y)⟫_ℝ :=
      (T.inner_map_map x (T.symm y)).symm
    _ = ⟪T x, y⟫_ℝ := by rw [LinearIsometryEquiv.apply_symm_apply]
    _ = 0 := appendedPaddedPieriLower_originalCanonicalAxis_orthogonal
      lam mu h hgram hdominant hsource hn p q

end AllRankGTAppendedPieriPhysicalAxisOrthogonality

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTPhysicalPaddedPieriSignedSpan

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem gtSignedEigenvectorSpan_mem_of_physicalPaddedPieriChannel_excluded
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hexcluded :
      ∀ i : PaddedPieriChannel (appendZeroWeight lam),
        ¬ retainedPaddedPieriChannel lam i →
          ∀ q : HarmonicYoungSpace (n := n)
            (paddedPieriSource (appendZeroWeight lam) i),
              ⟪v, physicalPaddedPieriChannel hn lam hdom i q⟫_ℝ = 0) :
    v ∈ gtSignedEigenvectorSpan (n := n) lam := by
  classical
  refine gtSignedEigenvectorSpan_mem_of_orthogonalComplete_retained_channels
    lam
    (fun i : PaddedPieriChannel (appendZeroWeight lam) =>
      HarmonicYoungSpace (n := n)
        (paddedPieriSource (appendZeroWeight lam) i))
    (physicalPaddedPieriChannel hn lam hdom)
    (physicalPaddedPieriChannel_inner_eq_zero hn lam hdom)
    (physicalPaddedPieriChannel_finrank hn lam hdom)
    (retainedPaddedPieriChannel lam) ?_ v hexcluded
  intro i hi
  refine ⟨retainedPaddedPieriSignedNode lam ⟨i, hi⟩, ?_⟩
  intro q
  exact transportedPaddedPieriChannel_eigen_of_retained
    hn lam hdom ⟨i, hi⟩ q

end AllRankGTPhysicalPaddedPieriSignedSpan

end

section


open scoped InnerProductSpace TensorProduct

namespace AllRankGTTransverseOrthogonalCompleteness

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedPieriPhysicalAxisOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriSignedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem canonicalGelfandTsetlinAxisTensor_mem_gtSignedEigenvectorSpan
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p : HarmonicYoungSpace (n := n) mu) :
    canonicalGelfandTsetlinAxisTensor lam mu h hgram p ∈
      gtSignedEigenvectorSpan (n := n + 1) lam := by
  have hdominant : Antitone (appendZeroWeight lam) :=
    (fullBranchSignature_interlaces_appendZeroWeight lam
      (fullBranchOfInterlaces mu h)).antitone_ambient
  have hfamily : 2 * (r + 2) + 4 ≤ n + 1 := by omega
  apply gtSignedEigenvectorSpan_mem_of_physicalPaddedPieriChannel_excluded
    hfamily lam hdominant
    (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)
  intro i hi q
  cases i with
  | inl row =>
      have hlast : row.val = Fin.last (r + 2) := by
        by_contra hne
        exact hi hne
      have hsource : Antitone
          (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))) := by
        simpa only [hlast] using row.property
      have hrow : row = ⟨Fin.last (r + 2), hsource⟩ :=
        Subtype.ext hlast
      subst row
      exact paddedOrthogonalTensorPieriChannel_appended_originalCanonicalAxis_orthogonal
        lam mu h hgram hdominant hsource hn p q
  | inr row =>
      exact False.elim (hi trivial)

end AllRankGTTransverseOrthogonalCompleteness

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTCanonicalPhysicalSignedSpan

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalChannelRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseOrthogonalCompleteness
open MetricCodes.Spherical.HigherRepresentationGraph

theorem canonicalGelfandTsetlinAxisTensor_mem_gtSelectedPhysicalSignedSpan
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces low mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) low mu h)
    (hfinite : FiniteInterlacing (n + 1) low mu)
    (hdom : Antitone low) (row : Fin (r + 2))
    (hhigh : Antitone (raiseWeight low row))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    canonicalGelfandTsetlinAxisTensor low mu h hgram p ∈
      gtSelectedPhysicalSignedSpan (n := n + 1) low row := by
  apply gtSignedEigenvectorSpan_le_selectedPhysicalSignedSpan
    low row
      (selectedSignedEigenspace_le_youngClebschLower_range
        (by omega) low mu hfinite hdom row hhigh)
  exact canonicalGelfandTsetlinAxisTensor_mem_gtSignedEigenvectorSpan
    low mu h hn hgram p

theorem allRankCartanCharacteristicProjector_canonicalAxis_eq_physicalClebsch
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces low mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) low mu h)
    (hfinite : FiniteInterlacing (n + 1) low mu)
    (hdom : Antitone low) (row : Fin (r + 2))
    (hhigh : Antitone (raiseWeight low row))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    allRankCartanCharacteristicProjector low (row, true)
        (canonicalGelfandTsetlinAxisTensor low mu h hgram p) =
      gtSelectedRowClebschRangeProjector low row
        (canonicalGelfandTsetlinAxisTensor low mu h hgram p) :=
  allRankCartanCharacteristicProjector_eq_selectedClebsch_of_mem_physicalSignedSpan
    low mu hfinite hdom row hhigh _
      (canonicalGelfandTsetlinAxisTensor_mem_gtSelectedPhysicalSignedSpan
        low mu h hgram hfinite hdom row hhigh hn p)

end AllRankGTCanonicalPhysicalSignedSpan

end

end HigherHarmonicYoung

section


open Filter Topology
open scoped BigOperators InnerProductSpace Topology

namespace HigherYoungAllRankStrongStableActualBoxSufficiency

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungMovingFibres

theorem fixedLevelHierarchyCodeBound_of_extraStrongStableBoxRepresentationData
    (hrepresentation : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
        Interlacing a b → 0 < a (Fin.last (r + 1)) →
        2 * (r + 2) + 5 ≤ n →
        (∀ v : RectangularVertices.Vertex (r + 1) m,
          FiniteInterlacing n (RectangularVertices.signature a n v)
            (flooredCoordinates b n)) →
        Nonempty (BoxRepresentationData (m := m) (n := n) a b)) :
    FixedLevelHierarchyCodeBound := by
  classical
  apply fixedLevelHierarchyCodeBound_of_actualRectangularGraphs
  intro r s R hs hs' a b hinterlacing hlast hspectral hR
  have hpositive : ∀ i : Fin (r + 2), 0 < a i := by
    intro i
    exact hlast.trans_le
      (hinterlacing.strictAnti_ambient.antitone i.le_last)
  obtain ⟨m, gap, _hm, hgap, hperron⟩ :=
    HigherHierarchyBoxPerron.exists_boxWidth_positive_gap_eventually_positive_eigenpair
      hinterlacing hpositive hspectral
  let stable : ℕ → Prop := fun n =>
    2 * (r + 2) + 5 ≤ n ∧
      (∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing n (RectangularVertices.signature a n v)
          (flooredCoordinates b n)) ∧
      Nonempty (BoxPerronData (m := m) (n := n) a b s gap)
  let : DecidablePred stable := Classical.decPred stable
  have heventual : ∀ᶠ n : ℕ in atTop, stable n := by
    filter_upwards
      [eventually_ge_atTop (2 * (r + 2) + 5),
        RectangularVertices.eventually_finiteInterlacing_all
          (m := m) a b hinterlacing, hperron] with n hn hinter he
    refine ⟨hn, hinter, ?_⟩
    obtain ⟨eigenvalue, eigenvector, hmargin, hpos, hunit, heq⟩ := he
    exact ⟨⟨eigenvalue, eigenvector, hmargin, hpos, hunit, heq⟩⟩
  let D : (n : ℕ) → stable n →
      BoxRepresentationData (m := m) (n := n) a b :=
    fun n h => Classical.choice
      (hrepresentation a b hinterlacing hlast h.1 h.2.1)
  let P : (n : ℕ) → (h : stable n) →
      BoxPerronData (m := m) (n := n) a b s gap :=
    fun n h => Classical.choice h.2.2
  let H : (n : ℕ) → (h : stable n) →
      RealizedHilbertGraph
        (BoxIndex (r + 1) m) (SpherePoint n) (BoxStabilizer n b)
        (YoungAmbient n (boxSignature (m := m) a n))
        (YoungCoordinateAmbient n (boxSignature (m := m) a n)) :=
    fun n h =>
      (D n h).toHilbertGraph h.2.1 (P n h).eigenvalue
        (by linarith [(P n h).spectral_gap])
        (P n h).eigenvector (P n h).positive (P n h).unit
        (P n h).equation
  let G : (n : ℕ) → stable n → IndexedHierarchyGraph n :=
    fun n h => actualYoungIndexedHierarchyGraph
      (boxSignature (m := m) a n) (H n h)
  refine ⟨m, gap, hgap, stable, inferInstance, heventual, G,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro n h
    change 0 < Fintype.card (RectangularVertices.Vertex (r + 1) m)
    exact Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
  · intro n h
    exact (D n h).stabilizer_pos
  · intro n h x y
    rfl
  · exact Filter.Eventually.of_forall fun n h => (P n h).spectral_gap
  · apply Filter.Eventually.of_forall
    intro n h
    exact actualYoungBox_rankQuotient_eq_weyl a b (H n h)
      (fun _ => rfl) (D n h).vertex_weyl (D n h).stabilizer_weyl

theorem fixedLevelHierarchyCodeBound_of_extraStrongStableProjectedAxis
    (hrealization : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
      Interlacing a b → 0 < a (Fin.last (r + 1)) →
      2 * (r + 2) + 5 ≤ n →
      (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing n (RectangularVertices.signature a n v)
          (flooredCoordinates b n)) →
      ∃ (o : SpherePoint n)
        (fibre : (i : BoxIndex (r + 1) m) →
          BoxStabilizer n b →ₗᵢ[ℝ]
            YoungVertex (n := n) (boxSignature (m := m) a n) i),
        ∀ (target source : BoxIndex (r + 1) m)
          (h : 0 < boxProbability a b n target source),
          Nonempty (BoxProjectedAxisWitness a b o fibre target source h)) :
    FixedLevelHierarchyCodeBound := by
  classical
  apply fixedLevelHierarchyCodeBound_of_extraStrongStableBoxRepresentationData
  intro r m n a b hinterlacing hlast hn hstable
  obtain ⟨o, fibre, hwitness⟩ :=
    hrealization a b hinterlacing hlast hn hstable
  exact ⟨boxRepresentationDataOfProjectedAxisWitnesses a b hstable
    (fun lam hd hdom =>
      weyl_dimension_eq_finrank_harmonicYoung hd lam hdom)
    o fibre (fun target source h =>
      Classical.choice (hwitness target source h))⟩

end HigherYoungAllRankStrongStableActualBoxSufficiency

end

end Spherical

end MetricCodes

end MetricCodesNoncomputable
