/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ProductBasisAndAnnuli
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.TrueLevelBasis
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite.MissingMathlib
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval
import Mathlib.Order.Filter.AtTopBot.Finset

/-! # BlockLocalization -/



open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Hermite1DimdLEAN

private lemma mem_squareBlock_iff_blockIndexMulti_eq
    {d : ℕ} (α ℓ : MultiIndex d) :
    α ∈ squareBlock ℓ ↔ blockIndexMulti α = ℓ := by
  constructor
  · intro h
    funext q
    have hq : α q ∈ HermiteLEAN.squareBlock (ℓ q) := h q
    rw [HermiteLEAN.squareBlock, Finset.mem_Ico] at hq
    exact ((Nat.eq_sqrt).2 (by simpa [Nat.pow_two] using hq)).symm
  · intro h q
    rw [HermiteLEAN.squareBlock, Finset.mem_Ico]
    have hq : Nat.sqrt (α q) = ℓ q := by
      simpa [blockIndexMulti, HermiteLEAN.blockIndex] using congrArg (fun f => f q) h
    exact by simpa [Nat.pow_two] using (Nat.eq_sqrt).1 hq.symm

/-!
# BlockLocalization

Square-block support decomposition and leakage.
Scaffolding notes: `ScaffoldingNotes/Blocks/block_localization.md`.
-/

/-- Orthogonal block decomposition by square blocks. -/
theorem blockDecompositionNorm
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    hermiteNormSq κ G = ∑' ℓ : MultiIndex d, hermiteNormSq κ (blockPart ℓ G) := by
  /-
  Scaffolding guidance:
  the block decomposition is the quantitative backbone for both local windows
  and leakage. Keep it exported in norm-squared form.
  -/
  classical
  let s : Finset (MultiIndex d) := G.support.image blockIndexMulti
  have hzero : ∀ ℓ ∉ s, hermiteNormSq κ (blockPart ℓ G) = 0 := by
    intro ℓ hℓ
    rw [finiteParseval]
    refine Finset.sum_eq_zero ?_
    intro α hα
    have hsuppnz : (blockPart ℓ G).coeff α ≠ 0 := by
      simpa [FiniteHermiteSum.support, Finsupp.mem_support_iff] using hα
    rw [blockPart, Finsupp.onFinset_apply] at hsuppnz
    by_cases hb : α ∈ squareBlock ℓ
    · have hGnz : G.coeff α ≠ 0 := by simpa [hb] using hsuppnz
      have hαG : α ∈ G.support := by
        simpa [FiniteHermiteSum.support, Finsupp.mem_support_iff] using hGnz
      have himg : ℓ ∈ s := by
        refine Finset.mem_image.mpr ?_
        exact ⟨α, hαG, (mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mp hb⟩
      exact (hℓ himg).elim
    · simp [hb] at hsuppnz
  have htsum :
      ∑' ℓ : MultiIndex d, hermiteNormSq κ (blockPart ℓ G) =
        Finset.sum s (fun ℓ => hermiteNormSq κ (blockPart ℓ G)) := by
    exact tsum_eq_sum hzero
  rw [htsum, finiteParseval]
  simp_rw [finiteParseval]
  have hsupport :
      ∀ ℓ : MultiIndex d,
        (blockPart ℓ G).support = G.support.filter (fun α => blockIndexMulti α = ℓ) := by
    intro ℓ
    ext α
    simp [FiniteHermiteSum.support, blockPart, Finsupp.mem_support_iff,
      mem_squareBlock_iff_blockIndexMulti_eq, and_comm]
  symm
  calc
    Finset.sum s (fun ℓ => Finset.sum (blockPart ℓ G).support (fun α => ‖(blockPart ℓ G).coeff α‖
        ^ 2))
      = Finset.sum s (fun ℓ => Finset.sum G.support (fun α => if blockIndexMulti α = ℓ then
          ‖G.coeff α‖ ^ 2 else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro ℓ hℓ
          rw [hsupport ℓ, Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro α hα
          by_cases hblock : blockIndexMulti α = ℓ
          · have hsq : α ∈ squareBlock ℓ := (mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mpr hblock
            simp [blockPart, Finsupp.onFinset_apply, hsq, hblock]
          · rw [if_neg hblock]
            have hnot : α ∉ squareBlock ℓ := by
              intro hsq
              exact hblock ((mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mp hsq)
            simp [hblock]
    _ = Finset.sum G.support (fun α => Finset.sum s (fun ℓ => if blockIndexMulti α = ℓ then
        ‖G.coeff α‖ ^ 2 else 0)) := by
          rw [Finset.sum_comm]
    _ = Finset.sum G.support (fun α => ‖G.coeff α‖ ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro α hα
          have himg : blockIndexMulti α ∈ s := Finset.mem_image.mpr ⟨α, hα, rfl⟩
          exact Finset.sum_ite_eq_of_mem s (blockIndexMulti α) (fun _ => ‖G.coeff α‖ ^ 2) himg

private lemma blockPart_coeff_eq_zero_of_not_mem_support_image
    {d : ℕ} (G : FiniteHermiteSum d) (ℓ α : MultiIndex d)
    (hℓ : ℓ ∉ G.support.image blockIndexMulti) :
    (blockPart ℓ G).coeff α = 0 := by
  by_cases hb : α ∈ squareBlock ℓ
  · have hidx : blockIndexMulti α = ℓ := (mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mp hb
    by_cases hsupp : α ∈ G.support
    · have himg : ℓ ∈ G.support.image blockIndexMulti := by
        exact Finset.mem_image.mpr ⟨α, hsupp, hidx⟩
      exact (hℓ himg).elim
    · have hcoeff : G.coeff α = 0 := by
        simpa [FiniteHermiteSum.support, Finsupp.mem_support_iff] using hsupp
      simp [blockPart, Finsupp.onFinset_apply, hb, hcoeff]
  · simp [blockPart, Finsupp.onFinset_apply, hb]

private lemma hermiteNormSq_blockPart_eq_zero_of_not_mem_support_image
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) (ℓ : MultiIndex d)
    (hℓ : ℓ ∉ G.support.image blockIndexMulti) :
    hermiteNormSq κ (blockPart ℓ G) = 0 := by
  rw [finiteParseval]
  refine Finset.sum_eq_zero ?_
  intro α hα
  simp [blockPart_coeff_eq_zero_of_not_mem_support_image G ℓ α hℓ]

private lemma tsum_hermiteNormSq_blockPart_eq_sum_support_image
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    ∑' ℓ : MultiIndex d, hermiteNormSq κ (blockPart ℓ G) =
      Finset.sum (G.support.image blockIndexMulti) (fun ℓ => hermiteNormSq κ (blockPart ℓ G)) := by
  exact tsum_eq_sum
    (fun ℓ hℓ => hermiteNormSq_blockPart_eq_zero_of_not_mem_support_image κ G ℓ hℓ)

private lemma blockDecompositionNorm_sum_support_image
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    hermiteNormSq κ G =
      Finset.sum (G.support.image blockIndexMulti) (fun ℓ => hermiteNormSq κ (blockPart ℓ G)) := by
  rw [blockDecompositionNorm, tsum_hermiteNormSq_blockPart_eq_sum_support_image]

private lemma localizationLeakageCoefficient_nonneg
    {C c B : ℝ} {d M : ℕ} (hC : 0 ≤ C) :
    0 ≤ localizationLeakageCoefficient C c B d M := by
  unfold localizationLeakageCoefficient
  positivity

private lemma annulusMass_blockDecomposition_sum_support_image
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (G : FiniteHermiteSum d) :
    annulusMass j (evalHermiteSum κ G) =
      Finset.sum (G.support.image blockIndexMulti)
        (fun ℓ => annulusMass j (evalHermiteSum κ (blockPart ℓ G))) := by
  classical
  rw [annulusParseval]
  have hsupport :
      ∀ ℓ : MultiIndex d,
        (blockPart ℓ G).support = G.support.filter (fun α => blockIndexMulti α = ℓ) := by
    intro ℓ
    ext α
    simp [FiniteHermiteSum.support, blockPart, Finsupp.mem_support_iff,
      mem_squareBlock_iff_blockIndexMulti_eq, and_comm]
  symm
  calc
    Finset.sum (G.support.image blockIndexMulti)
        (fun ℓ => annulusMass j (evalHermiteSum κ (blockPart ℓ G)))
      =
        Finset.sum (G.support.image blockIndexMulti)
          (fun ℓ =>
            Finset.sum (blockPart ℓ G).support
              (fun α => ‖(blockPart ℓ G).coeff α‖ ^ 2 * annulusMass j (PhiKappaAlpha κ α))) := by
            refine Finset.sum_congr rfl ?_
            intro ℓ hℓ
            rw [annulusParseval]
    _ =
        Finset.sum (G.support.image blockIndexMulti)
          (fun ℓ =>
            Finset.sum G.support
              (fun α =>
                if blockIndexMulti α = ℓ then
                  ‖G.coeff α‖ ^ 2 * annulusMass j (PhiKappaAlpha κ α)
                else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro ℓ hℓ
          rw [hsupport ℓ, Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro α hα
          by_cases hblock : blockIndexMulti α = ℓ
          · have hsq : α ∈ squareBlock ℓ :=
              (mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mpr hblock
            simp [blockPart, Finsupp.onFinset_apply, hsq, hblock]
          · rw [if_neg hblock]
            have hnot : α ∉ squareBlock ℓ := by
              intro hsq
              exact hblock ((mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mp hsq)
            simp [hblock]
    _ =
        Finset.sum G.support
          (fun α =>
            Finset.sum (G.support.image blockIndexMulti)
              (fun ℓ =>
                if blockIndexMulti α = ℓ then
                  ‖G.coeff α‖ ^ 2 * annulusMass j (PhiKappaAlpha κ α)
                else 0)) := by
          rw [Finset.sum_comm]
    _ =
        Finset.sum G.support fun α => ‖G.coeff α‖ ^ 2 * annulusMass j (PhiKappaAlpha κ α) := by
          refine Finset.sum_congr rfl ?_
          intro α hα
          have himg : blockIndexMulti α ∈ G.support.image blockIndexMulti :=
            Finset.mem_image.mpr ⟨α, hα, rfl⟩
          exact Finset.sum_ite_eq_of_mem
            (G.support.image blockIndexMulti) (blockIndexMulti α)
            (fun _ => ‖G.coeff α‖ ^ 2 * annulusMass j (PhiKappaAlpha κ α)) himg

private lemma blockPart_remainderPart_coeff
    {d : ℕ} (j ℓ α : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    (blockPart ℓ (remainderPart j M G)).coeff α =
      if M < blockDistance j ℓ then (blockPart ℓ G).coeff α else 0 := by
  by_cases hb : α ∈ squareBlock ℓ
  · have hidx : blockIndexMulti α = ℓ :=
      (mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mp hb
    by_cases hfar : M < blockDistance j ℓ
    · simp [blockPart, remainderPart, Finsupp.onFinset_apply, hb, hfar, hidx]
    · simp [blockPart, remainderPart, Finsupp.onFinset_apply, hb, hfar, hidx]
  · by_cases hfar : M < blockDistance j ℓ
    · simp [blockPart, remainderPart, Finsupp.onFinset_apply, hb, hfar]
    · simp [blockPart, remainderPart, Finsupp.onFinset_apply, hb, hfar]

private lemma hermiteNormSq_blockPart_remainderPart
    {d : ℕ} (κ j ℓ : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    hermiteNormSq κ (blockPart ℓ (remainderPart j M G)) =
      if M < blockDistance j ℓ then hermiteNormSq κ (blockPart ℓ G) else 0 := by
  by_cases hfar : M < blockDistance j ℓ
  · rw [finiteParseval, finiteParseval, if_pos hfar]
    have hsupport :
        (blockPart ℓ (remainderPart j M G)).support = (blockPart ℓ G).support := by
      ext α
      simp [FiniteHermiteSum.support, Finsupp.mem_support_iff, blockPart_remainderPart_coeff, hfar]
    rw [hsupport]
    refine Finset.sum_congr rfl ?_
    intro α hα
    simp [blockPart_remainderPart_coeff, hfar]
  · rw [finiteParseval, if_neg hfar]
    refine Finset.sum_eq_zero ?_
    intro α hα
    simp [blockPart_remainderPart_coeff, hfar]

private lemma remainderPart_annulus_blockwise_bound
    {d : ℕ} (κ : MultiIndex d) {C c B : ℝ}
    (hC : 0 ≤ C)
    (hloc :
      ∀ j ℓ : MultiIndex d, ∀ G : FiniteHermiteSum d,
        annulusMass j (evalHermiteSum κ (blockPart ℓ G)) ≤
          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
            hermiteNormSq κ (blockPart ℓ G))
    (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤
      Finset.sum ((remainderPart j M G).support.image blockIndexMulti)
        (fun ℓ =>
          if M < blockDistance j ℓ then
            C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
              hermiteNormSq κ (blockPart ℓ G)
          else 0) := by
  rw [annulusMass_blockDecomposition_sum_support_image]
  exact Finset.sum_le_sum (fun ℓ hℓ => by
    have hbase := hloc j ℓ (remainderPart j M G)
    by_cases hfar : M < blockDistance j ℓ
    · rw [hermiteNormSq_blockPart_remainderPart (κ := κ) (j := j) (ℓ := ℓ) (M := M)
        (G := G), if_pos hfar] at hbase
      simpa [hfar] using hbase
    · rw [hermiteNormSq_blockPart_remainderPart (κ := κ) (j := j) (ℓ := ℓ) (M := M)
        (G := G), if_neg hfar] at hbase
      have hle0 :
          annulusMass j (evalHermiteSum κ (blockPart ℓ (remainderPart j M G))) ≤ 0 := by
        simpa using hbase
      have hnonneg : 0 ≤ annulusMass j (evalHermiteSum κ (blockPart ℓ (remainderPart j M G))) := by
        unfold annulusMass
        positivity
      have hzero :
          annulusMass j (evalHermiteSum κ (blockPart ℓ (remainderPart j M G))) = 0 := by
        exact le_antisymm hle0 hnonneg
      have hright_nonneg :
          0 ≤ C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
            hermiteNormSq κ (blockPart ℓ G) := by
        have hexp_nonneg :
            0 ≤ Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) := by
          positivity
        have hnorm_nonneg : 0 ≤ hermiteNormSq κ (blockPart ℓ G) := by
          rw [finiteParseval]
          positivity
        have hmul_nonneg :
            0 ≤ C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) := by
          exact mul_nonneg hC hexp_nonneg
        exact mul_nonneg hmul_nonneg hnorm_nonneg
      simp [hfar, hzero])

private lemma blockPart_remainderPart_coeff_eq_of_far
    {d : ℕ} (j ℓ α : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d)
    (hfar : M < blockDistance j ℓ) :
    (blockPart ℓ (remainderPart j M G)).coeff α = (blockPart ℓ G).coeff α := by
  simpa [hfar] using blockPart_remainderPart_coeff (j := j) (ℓ := ℓ) (α := α) (M := M) (G := G)

private lemma hermiteNormSq_blockPart_remainderPart_eq_of_far
    {d : ℕ} (κ j ℓ : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d)
    (hfar : M < blockDistance j ℓ) :
    hermiteNormSq κ (blockPart ℓ (remainderPart j M G)) =
      hermiteNormSq κ (blockPart ℓ G) := by
  simpa [hfar] using
    hermiteNormSq_blockPart_remainderPart (κ := κ) (j := j) (ℓ := ℓ) (M := M) (G := G)

/-- Explicit local and far support sets relative to an annulus and width. -/
theorem explicitLocalAndFarSupport
    {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    Disjoint (localCoeffSet j M G) (farCoeffSet j M G) ∧
      localCoeffSet j M G ∪ farCoeffSet j M G = G.support ∧
      (localPart j M G).support = localCoeffSet j M G ∧
      (remainderPart j M G).support = farCoeffSet j M G := by
  /-
  Scaffolding guidance:
  later files need the explicit finite sets, not an opaque decomposition lemma.
  This is where regrouping by total degree starts.
  -/
  classical
  have hdisj : Disjoint (localCoeffSet j M G) (farCoeffSet j M G) := by
    refine Finset.disjoint_left.mpr ?_
    intro α hlocal hfar
    have hle : blockDistance j (blockIndexMulti α) ≤ M := (Finset.mem_filter.mp hlocal).2
    have hgt : M < blockDistance j (blockIndexMulti α) := (Finset.mem_filter.mp hfar).2
    exact (not_lt_of_ge hle hgt).elim
  have hunion : localCoeffSet j M G ∪ farCoeffSet j M G = G.support := by
    ext α
    simp only [localCoeffSet, farCoeffSet, mem_union, mem_filter]
    constructor
    · intro h
      rcases h with ⟨hsupp, _⟩ | ⟨hsupp, _⟩
      · exact hsupp
      · exact hsupp
    · intro hsupp
      by_cases hlocal : blockDistance j (blockIndexMulti α) ≤ M
      · exact Or.inl ⟨hsupp, hlocal⟩
      · exact Or.inr ⟨hsupp, Nat.lt_of_not_ge hlocal⟩
  have hlocal_support : (localPart j M G).support = localCoeffSet j M G := by
    ext α
    simp [FiniteHermiteSum.support, localPart, localCoeffSet, Finsupp.mem_support_iff, and_comm]
  have hfar_support : (remainderPart j M G).support = farCoeffSet j M G := by
    ext α
    simp [FiniteHermiteSum.support, remainderPart, farCoeffSet, Finsupp.mem_support_iff, and_comm]
  exact ⟨hdisj, hunion, hlocal_support, hfar_support⟩

private lemma blockPart_support_eq_filter
    {d : ℕ} (G : FiniteHermiteSum d) (ℓ : MultiIndex d) :
    (blockPart ℓ G).support = G.support.filter (fun α => blockIndexMulti α = ℓ) := by
  ext α
  simp [FiniteHermiteSum.support, blockPart, Finsupp.mem_support_iff,
    mem_squareBlock_iff_blockIndexMulti_eq, and_comm]

private lemma gaussianInner_self
    {d : ℕ} (F : CSpace d → ℂ) :
    gaussianInner F F = ((gaussianL2NormSq F : ℝ) : ℂ) := by
  unfold gaussianInner gaussianL2NormSq
  have hfun :
      (fun z : CSpace d => F z * conj (F z)) =
        fun z : CSpace d => ((‖F z‖ ^ 2 : ℝ) : ℂ) := by
    funext z
    simpa using Complex.mul_conj' (F z)
  rw [hfun, integral_complex_ofReal]

private lemma measurableSet_oneDimAnnulus
    (j : ℕ) :
    MeasurableSet (productAnnulus (d := 1) (fun _ => j)) := by
  have hge :
      MeasurableSet {z : CSpace 1 | (j : ℝ) ≤ ‖z 0‖} := by
    exact measurableSet_le measurable_const
      (measurable_norm.comp (continuous_apply 0).measurable)
  have hlt :
      MeasurableSet {z : CSpace 1 | ‖z 0‖ < (j : ℝ) + 1} := by
    exact measurableSet_lt
      (measurable_norm.comp (continuous_apply 0).measurable) measurable_const
  simpa [productAnnulus, Set.setOf_forall, Set.setOf_and] using hge.inter hlt

private lemma integrable_oneDimPhi_cross_gaussian
    (k m n : ℕ) :
    Integrable
      (fun z : CSpace 1 => oneDimPhi k m (z 0) * conj (oneDimPhi k n (z 0)))
      (gaussianMeasure 1) := by
  change
    Integrable
      (fun z : CSpace 1 => HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))
      (gaussianMeasure 1)
  rw [gaussianMeasure]
  rw [MeasureTheory.integrable_withDensity_iff_integrable_smul']
  · have hcross :
        Integrable
          (fun z : CSpace 1 =>
            HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)) *
              (Real.exp (-‖z 0‖ ^ 2) : ℂ)) := by
      have h :=
        (MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integrable_comp_of_integrable
          (g := fun z : ℂ =>
            HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z) *
              (Real.exp (-‖z‖ ^ 2) : ℂ))
          (HermitekLEAN.integrable_weightedCross k m n)
      refine h.congr ?_
      filter_upwards with z
      rfl
    have hsmul :
        Integrable
          (fun z : CSpace 1 =>
            Real.exp (-‖z 0‖ ^ 2) •
              (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
      convert hcross using 1
      funext z
      simp [Algebra.smul_def, mul_left_comm, mul_comm]
    convert hsmul.const_mul (1 / Real.pi) using 1
    case e'_5 => rfl
    funext z
    have hnonneg : 0 ≤ π⁻¹ * rexp (-‖z 0‖ ^ 2) := by
      positivity
    simp only [gaussianDensity, pow_one, one_div, univ_unique, Fin.default_eq_zero,
      Fin.isValue, sum_singleton, hnonneg, ENNReal.toReal_ofReal, real_smul, ofReal_exp,
      ofReal_neg, ofReal_pow]
    have hleft :
        (π⁻¹ * rexp (-‖z 0‖ ^ 2)) •
            (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) =
          (((π⁻¹ * rexp (-‖z 0‖ ^ 2) : ℝ) : ℂ) *
            (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
      simp [Algebra.smul_def]
    calc
      (π⁻¹ * rexp (-‖z 0‖ ^ 2)) •
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) =
        (((π⁻¹ * rexp (-‖z 0‖ ^ 2) : ℝ) : ℂ) *
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := hleft
      _ = (↑π)⁻¹ * (cexp (-↑‖z 0‖ ^ 2) *
            (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
          simp [mul_assoc, mul_left_comm]
  · change
      Measurable
        (fun z : CSpace 1 =>
          ENNReal.ofReal ((1 / Real.pi ^ 1) * Real.exp (-(∑ q : Fin 1, ‖z q‖ ^ 2))))
    fun_prop
  · simp

private lemma productBasis_annulusFactorization
    {d : ℕ} (κ α j : MultiIndex d) :
    annulusMass j (PhiKappaAlpha κ α) =
      ∏ q : Fin d,
        annulusMass (d := 1) (fun _ => j q) (oneDimLift (oneDimPhi (κ q) (α q))) := by
  classical
  let F : Fin d → ℂ → ℂ := fun q z =>
    if (j q : ℝ) ≤ ‖z‖ ∧ ‖z‖ < (j q : ℝ) + 1 then oneDimPhi (κ q) (α q) z else 0
  have hFG :
      ∀ q : Fin d,
        Integrable
          (fun z : CSpace 1 => F q (z 0) * conj (F q (z 0)))
          (gaussianMeasure 1) := by
    intro q
    have hbase :
        Integrable
          (fun z : CSpace 1 => oneDimPhi (κ q) (α q) (z 0) * conj (oneDimPhi (κ q) (α q) (z 0)))
          (gaussianMeasure 1) :=
      integrable_oneDimPhi_cross_gaussian (κ q) (α q) (α q)
    have hind :
        Integrable
          (fun z : CSpace 1 =>
            if z ∈ productAnnulus (d := 1) (fun _ => j q) then
              oneDimPhi (κ q) (α q) (z 0) * conj (oneDimPhi (κ q) (α q) (z 0))
            else 0)
          (gaussianMeasure 1) := by
      refine (hbase.indicator (measurableSet_oneDimAnnulus (j q))).congr ?_
      filter_upwards with z
      simp only [Set.indicator]
    convert hind using 1
    funext z
    by_cases hz : z ∈ productAnnulus (d := 1) (fun _ => j q)
    · have hz0 : (j q : ℝ) ≤ ‖z 0‖ ∧ ‖z 0‖ < (j q : ℝ) + 1 := by
        simpa [productAnnulus] using hz
      simp [F, hz, hz0]
    · have hz0 : ¬ ((j q : ℝ) ≤ ‖z 0‖ ∧ ‖z 0‖ < (j q : ℝ) + 1) := by
        simpa [productAnnulus] using hz
      simp [F, hz, hz0]
  have htensor := tensorGaussianFactorization d F F hFG
  apply Complex.ofReal_injective
  calc
    (((annulusMass j (PhiKappaAlpha κ α) : ℝ)) : ℂ)
        = gaussianInner (fun z => ∏ q : Fin d, F q (z q)) (fun z => ∏ q : Fin d, F q (z q)) := by
            rw [gaussianInner_self]
            congr 1
            unfold annulusMass gaussianL2NormSq
            refine integral_congr_ae ?_
            filter_upwards with z
            by_cases hz : z ∈ productAnnulus j
            · have hq :
                ∀ q : Fin d, (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1 := hz
              simp [F, PhiKappaAlpha, hz, hq]
            · have hq : ∃ q : Fin d, ¬ ((j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1) := by
                simpa [productAnnulus] using hz
              rcases hq with ⟨q, hq⟩
              have hFq : F q (z q) = 0 := by simp [F, hq]
              have hprod : (∏ q' : Fin d, F q' (z q')) = 0 := by
                refine Finset.prod_eq_zero_iff.mpr ?_
                exact ⟨q, Finset.mem_univ q, hFq⟩
              simp [hz, hprod]
    _ = ∏ q : Fin d,
          gaussianInner (d := 1) (fun z : CSpace 1 => F q (z 0)) (fun z : CSpace 1 => F q (z 0))
              := by
            simpa using htensor.2
    _ = ∏ q : Fin d, (((annulusMass (d := 1) (fun _ => j q) (oneDimLift (oneDimPhi (κ q) (α q))) :
        ℝ)) : ℂ) := by
          refine Finset.prod_congr rfl ?_
          intro q hq
          rw [gaussianInner_self]
          congr 1
          unfold gaussianL2NormSq annulusMass
          refine integral_congr_ae ?_
          filter_upwards with z
          by_cases hz : z ∈ productAnnulus (d := 1) (fun _ => j q)
          · have hz0 : (j q : ℝ) ≤ ‖z 0‖ ∧ ‖z 0‖ < (j q : ℝ) + 1 := by
              simpa [productAnnulus] using hz
            simp [F, hz, hz0, oneDimLift]
          · have hz0 : ¬ ((j q : ℝ) ≤ ‖z 0‖ ∧ ‖z 0‖ < (j q : ℝ) + 1) := by
              simpa [productAnnulus] using hz
            simp [F, hz, hz0]
    _ = (((∏ q : Fin d,
            annulusMass (d := 1) (fun _ => j q) (oneDimLift (oneDimPhi (κ q) (α q))) : ℝ)) : ℂ) :=
                by
          simp

private lemma block_decay_compare_coord
    {d : ℕ} (κ α j ℓ : MultiIndex d) (q : Fin d)
    (hblock : α ∈ squareBlock ℓ) :
    max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0
      ≤
    max (|((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| - ((κ q + 4 : ℕ) : ℝ)) 0 := by
  have hsqrt : Nat.sqrt (α q) = ℓ q := by
    simpa [blockIndexMulti, HermiteLEAN.blockIndex] using
      congrArg (fun f => f q) ((mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mp hblock)
  have hle : ((ℓ q : ℕ) : ℝ) ≤ Real.sqrt (α q : ℝ) := by
    simpa [hsqrt] using (Real.nat_sqrt_le_real_sqrt (a := α q))
  have hlt : Real.sqrt (α q : ℝ) < ((ℓ q + 1 : ℕ) : ℝ) := by
    simpa [hsqrt] using (Real.real_sqrt_lt_nat_sqrt_succ (a := α q))
  have hclose : |Real.sqrt (α q : ℝ) - ((ℓ q : ℕ) : ℝ)| < 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    have hlt' :
        Real.sqrt (α q : ℝ) - ((ℓ q : ℕ) : ℝ) < (((ℓ q + 1 : ℕ) : ℝ) - ((ℓ q : ℕ) : ℝ)) := by
      exact sub_lt_sub_right hlt _
    simpa using hlt'
  have hdist_eq : ((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) = |((j q : ℕ) : ℝ) - ((ℓ q : ℕ) : ℝ)| := by
    rcases Nat.le_total (j q) (ℓ q) with hj | hℓ
    · rw [Nat.dist_eq_sub_of_le hj, abs_of_nonpos]
      · rw [Nat.cast_sub hj]
        simp
      · exact sub_nonpos.mpr (by exact_mod_cast hj)
    · rw [Nat.dist_eq_sub_of_le_right hℓ, abs_of_nonneg]
      · rw [Nat.cast_sub hℓ]
      · exact sub_nonneg.mpr (by exact_mod_cast hℓ)
  have htri :
      |((j q : ℕ) : ℝ) - ((ℓ q : ℕ) : ℝ)|
        ≤ |((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| +
            |Real.sqrt (α q : ℝ) - ((ℓ q : ℕ) : ℝ)| := by
    calc
      |((j q : ℕ) : ℝ) - ((ℓ q : ℕ) : ℝ)|
          = |(((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)) +
              (Real.sqrt (α q : ℝ) - ((ℓ q : ℕ) : ℝ))| := by ring_nf
      _ ≤ |((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| +
            |Real.sqrt (α q : ℝ) - ((ℓ q : ℕ) : ℝ)| := by
              simpa using
                abs_add_le (((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ))
                  (Real.sqrt (α q : ℝ) - ((ℓ q : ℕ) : ℝ))
  have hbound :
      ((Nat.dist (j q) (ℓ q) : ℕ) : ℝ)
        ≤ |((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| + 1 := by
    rw [hdist_eq]
    linarith
  have hmain :
      ((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)
        ≤ |((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| - ((κ q + 4 : ℕ) : ℝ) := by
    have hk :
        (((κ q + 5 : ℕ) : ℝ)) = (((κ q + 4 : ℕ) : ℝ)) + 1 := by
      have hk' : (((κ q : ℕ) : ℝ) + 5) = ((((κ q : ℕ) : ℝ) + 4) + 1) := by ring
      simpa [Nat.cast_add] using hk'
    linarith
  exact max_le_max hmain le_rfl

private lemma sup_coord_exists
    {d : ℕ} (hd : d ≠ 0) (j ℓ : MultiIndex d) :
    ∃ q0 : Fin d, blockDistance j ℓ = Nat.dist (j q0) (ℓ q0) := by
  let q0 : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨q0, Finset.mem_univ q0⟩
  have hbd_eq :
      blockDistance j ℓ = Finset.univ.sup' hne (fun q : Fin d => Nat.dist (j q) (ℓ q)) := by
    rw [blockDistance, Finset.sup'_eq_sup hne]
  rw [hbd_eq]
  rcases Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin d))) hne
      (f := fun q : Fin d => Nat.dist (j q) (ℓ q)) with ⟨q0, hq0, hsup⟩
  refine ⟨q0, ?_⟩
  simpa [Finset.sup'_eq_sup hne] using hsup

private lemma shell_offset_mem_cube_sdiff
    {d : ℕ} (hd : d ≠ 0) {ℓ j : MultiIndex d} {r : ℕ}
    (hj : blockDistance j ℓ = r) (hr : 1 ≤ r) :
    let x : Fin d → ℤ := fun q => (j q : ℤ) - ℓ q
    let cube : Finset (Fin d → ℤ) :=
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ))
    let inner : Finset (Fin d → ℤ) :=
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) : ℤ)))
    x ∈ cube ∧ x ∉ inner := by
  dsimp
  constructor
  · change (fun q : Fin d => (j q : ℤ) - ℓ q) ∈
        Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ))
    rw [Fintype.mem_piFinset]
    intro q
    have hq : Nat.dist (j q) (ℓ q) ≤ r := by
      rw [← hj]
      exact (Finset.univ : Finset (Fin d)).le_sup (f := fun q' : Fin d => Nat.dist (j q') (ℓ q'))
        (Finset.mem_univ q)
    simp [Finset.mem_Icc]
    by_cases hle : j q ≤ ℓ q
    · rw [Nat.dist_eq_sub_of_le hle] at hq
      omega
    · have hle' : ℓ q ≤ j q := Nat.le_of_lt (Nat.lt_of_not_ge hle)
      rw [Nat.dist_eq_sub_of_le_right hle'] at hq
      omega
  · intro hx
    change (fun q : Fin d => (j q : ℤ) - ℓ q) ∈
        Fintype.piFinset
          (fun _ : Fin d => Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) : ℤ))) at hx
    rw [Fintype.mem_piFinset] at hx
    rcases sup_coord_exists hd j ℓ with ⟨q0, hq0⟩
    have hdist : Nat.dist (j q0) (ℓ q0) = r := by
      simpa [hj] using hq0.symm
    have hxq := hx q0
    simp [Finset.mem_Icc] at hxq
    by_cases hle : j q0 ≤ ℓ q0
    · rw [Nat.dist_eq_sub_of_le hle] at hdist
      omega
    · have hle' : ℓ q0 ≤ j q0 := Nat.le_of_lt (Nat.lt_of_not_ge hle)
      rw [Nat.dist_eq_sub_of_le_right hle'] at hdist
      omega

private lemma cube_boundary_card
    (d r : ℕ) (hr : 1 ≤ r) :
    let cube : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r :
        ℤ))
    let inner : Finset (Fin d → ℤ) :=
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) : ℤ)))
    (cube \ inner).card = shellCardinality d r := by
  dsimp
  have hsubset :
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) : ℤ))) ⊆
        Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ)) := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    intro q
    have hxq := hx q
    simp [Finset.mem_Icc] at hxq ⊢
    omega
  have hcube : (Finset.Icc (-(r : ℤ)) (r : ℤ)).card = 2 * r + 1 := by
    simp [Int.card_Icc]
    omega
  have hinner : (Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) : ℤ))).card = 2 * r - 1 := by
    simp [Int.card_Icc]
    omega
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubset, Fintype.card_piFinset_const,
    Fintype.card_piFinset_const, hcube, hinner, shellCardinality]

private lemma finiteShellSubtype
    {d : ℕ} (ℓ : MultiIndex d) {r : ℕ} (hr : 1 ≤ r) :
    Finite {j : MultiIndex d // blockDistance j ℓ = r} := by
  by_cases hd : d = 0
  · classical
    subst hd
    have hempty :
        IsEmpty {j : MultiIndex 0 // blockDistance j ℓ = r} := by
      refine ⟨?_⟩
      intro j
      have hdist0 : blockDistance j.1 ℓ = 0 := by
        simp [blockDistance]
      omega
    letI : IsEmpty {j : MultiIndex 0 // blockDistance j ℓ = r} := hempty
    infer_instance
  · let f : {j : MultiIndex d // blockDistance j ℓ = r} →
        {x // x ∈
          (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ)))
            \ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) :
                ℤ)))} :=
      fun j =>
        ⟨(fun q => (j.1 q : ℤ) - ℓ q), by
          simpa [Finset.mem_sdiff] using shell_offset_mem_cube_sdiff hd j.2 hr⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      funext q
      have hq : (f a).1 q = (f b).1 q := by
        simpa using congrArg (fun x => x.1 q) hab
      dsimp [f] at hq
      omega
    exact Finite.of_injective f hf

private lemma sharpShellCount_of_pos
    {d : ℕ} (ℓ : MultiIndex d) {r : ℕ} (hr : 1 ≤ r) :
    Nat.card {j : MultiIndex d // blockDistance j ℓ = r} ≤ shellCardinality d r := by
  by_cases hd : d = 0
  · subst hd
    have hempty :
        IsEmpty {j : MultiIndex 0 // blockDistance j ℓ = r} := by
      refine ⟨?_⟩
      intro j
      have hdist0 : blockDistance j.1 ℓ = 0 := by
        simp [blockDistance]
      omega
    have hcard0 : Nat.card {j : MultiIndex 0 // blockDistance j ℓ = r} = 0 := by
      letI : IsEmpty {j : MultiIndex 0 // blockDistance j ℓ = r} := hempty
      simp [Nat.card_eq_fintype_card]
    rw [hcard0]
    have hr0 : r ≠ 0 := by
      omega
    simp [shellCardinality]
  · let f : {j : MultiIndex d // blockDistance j ℓ = r} →
        {x // x ∈
          (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ)))
            \ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) :
                ℤ)))} :=
      fun j =>
        ⟨(fun q => (j.1 q : ℤ) - ℓ q), by
          simpa [Finset.mem_sdiff] using shell_offset_mem_cube_sdiff hd j.2 hr⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      funext q
      have hq : (f a).1 q = (f b).1 q := by
        simpa using congrArg (fun x => x.1 q) hab
      dsimp [f] at hq
      omega
    let shell :
        Finset (Fin d → ℤ) :=
      (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ))) \
        Fintype.piFinset
          (fun _ : Fin d => Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) : ℤ)))
    have hshell :
        Nat.card {x // x ∈ shell} = shellCardinality d r := by
      have hattach : shell.attach.card = shell.card := Finset.card_attach
      rw [Nat.card_eq_fintype_card]
      simpa [shell] using hattach.trans (cube_boundary_card d r hr)
    letI := finiteShellSubtype ℓ hr
    exact le_trans (Nat.card_le_card_of_injective f hf) (le_of_eq hshell)

private lemma shell_cardinality_bound_filter
    {d : ℕ} (ℓ : MultiIndex d) (r : ℕ) (s : Finset (MultiIndex d))
    (hr : 1 ≤ r) :
    (((s.filter fun j => blockDistance j ℓ = r).card : ℕ) : ℝ) ≤ shellCardinality d r := by
  by_cases hd : d = 0
  · subst hd
    have hfilter0 : s.filter (fun j => blockDistance j ℓ = r) = ∅ := by
      ext j
      simp only [mem_filter, notMem_empty, iff_false, not_and]
      intro hj hEq
      have hdist0 : blockDistance j ℓ = 0 := by
        simp [blockDistance]
      have : r = 0 := by simpa [hdist0] using hEq.symm
      omega
    simp [hfilter0, shellCardinality]
  · let f :
        {j // j ∈ s.filter fun j => blockDistance j ℓ = r} →
        {j : MultiIndex d // blockDistance j ℓ = r} :=
      fun j => ⟨j.1, (Finset.mem_filter.mp j.2).2⟩
    have hf : Function.Injective f := by
      intro a b hab
      cases a
      cases b
      cases hab
      rfl
    letI := finiteShellSubtype ℓ hr
    have hcard :
        Nat.card {j // j ∈ s.filter fun j => blockDistance j ℓ = r} ≤
          Nat.card {j : MultiIndex d // blockDistance j ℓ = r} :=
      Nat.card_le_card_of_injective f hf
    have hfilter :
        Nat.card {j // j ∈ s.filter fun j => blockDistance j ℓ = r} =
          (s.filter fun j => blockDistance j ℓ = r).card := by
      rw [Nat.card_eq_fintype_card]
      simp
    rw [← hfilter]
    calc
      ((Nat.card {j // j ∈ s.filter fun j => blockDistance j ℓ = r} : ℕ) : ℝ)
          ≤ Nat.card {j : MultiIndex d // blockDistance j ℓ = r} := by
            exact_mod_cast hcard
      _ ≤ shellCardinality d r := by
            exact_mod_cast sharpShellCount_of_pos ℓ hr

/-- Single-basis localization on a product annulus. -/
theorem productBasisLocalization
    {d : ℕ} (κ : MultiIndex d) :
    ∃ C c B : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
      ∀ α j ℓ : MultiIndex d, α ∈ squareBlock ℓ →
        annulusMass j (PhiKappaAlpha κ α) ≤
          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) := by
  /-
  Scaffolding guidance:
  this is the coordinatewise product version of the imported one-dimensional
  localization estimate.
  -/
  by_cases hd : d = 0
  · subst hd
    refine ⟨1, 1, 0, by positivity, by positivity, le_rfl, ?_⟩
    intro α j ℓ hblock
    have hα : α = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    have hℓ : ℓ = 0 := Subsingleton.elim _ _
    subst hα hj hℓ
    rw [productBasis_annulusFactorization]
    simp
  · choose Cq cq hCq_pos hcq_pos hloc using (fun q : Fin d => localizationIncludingZero (κ q))
    let q0 : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    let C : ℝ := ∏ q : Fin d, Cq q
    let c : ℝ := Finset.univ.inf' ⟨q0, Finset.mem_univ q0⟩ cq
    let B : ℝ := ∑ q : Fin d, ((κ q + 5 : ℕ) : ℝ)
    have hC_pos : 0 < C := by
      dsimp [C]
      exact Finset.prod_pos (fun q hq => hCq_pos q)
    have hc_pos : 0 < c := by
      dsimp [c]
      rw [Finset.lt_inf'_iff]
      intro q hq
      exact hcq_pos q
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      positivity
    refine ⟨C, c, B, hC_pos, hc_pos, hB_nonneg, ?_⟩
    intro α j ℓ hblock
    rw [productBasis_annulusFactorization]
    have hcoord :
        ∀ q : Fin d,
          annulusMass (d := 1) (fun _ => j q) (oneDimLift (oneDimPhi (κ q) (α q))) ≤
            Cq q *
              Real.exp
                (-(cq q) *
                  max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2) := by
      intro q
      have hbase := hloc q (α q) (j q)
      have hcmp := block_decay_compare_coord (κ := κ) (α := α) (j := j) (ℓ := ℓ) q hblock
      have hsq :
          max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2 ≤
            max (|((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| - ((κ q + 4 : ℕ) : ℝ)) 0 ^ 2 := by
        have hnonneg :
            0 ≤ max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 := by
          exact le_max_right _ _
        have hnonneg' :
            0 ≤ max (|((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| - ((κ q + 4 : ℕ) : ℝ)) 0 := by
          exact le_max_right _ _
        nlinarith [hcmp, hnonneg, hnonneg']
      have hexp :
          Real.exp
              (-(cq q) *
                max (|((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| - ((κ q + 4 : ℕ) : ℝ)) 0 ^ 2) ≤
            Real.exp
              (-(cq q) *
                max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hsq, hcq_pos q]
      exact le_trans hbase <| mul_le_mul_of_nonneg_left hexp (le_of_lt (hCq_pos q))
    have hprod_bound :
        ∏ q : Fin d, annulusMass (d := 1) (fun _ => j q) (oneDimLift (oneDimPhi (κ q) (α q))) ≤
          ∏ q : Fin d,
            (Cq q *
              Real.exp
                (-(cq q) *
                  max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2)) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro q hq
        unfold annulusMass
        positivity
      · intro q hq
        exact hcoord q
    refine le_trans hprod_bound ?_
    have hcsmall : ∀ q : Fin d, c ≤ cq q := by
      intro q
      dsimp [c]
      exact Finset.inf'_le _ (Finset.mem_univ q)
    have hsq_ge :
        max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2 ≤
          ∑ q : Fin d, max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2 := by
      rcases sup_coord_exists hd j ℓ with ⟨q0, hq0⟩
      have hBq : ((κ q0 + 5 : ℕ) : ℝ) ≤ B := by
        dsimp [B]
        simpa using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset (Fin d)))
            (a := q0)
            (f := fun q : Fin d => ((κ q + 5 : ℕ) : ℝ))
            (fun q hq => by positivity)
            (Finset.mem_univ q0))
      have hmax :
          max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ≤
            max (((Nat.dist (j q0) (ℓ q0) : ℕ) : ℝ) - ((κ q0 + 5 : ℕ) : ℝ)) 0 := by
        rw [hq0]
        exact max_le_max (sub_le_sub_left hBq _) le_rfl
      have hsq0 :
          max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2 ≤
            max (((Nat.dist (j q0) (ℓ q0) : ℕ) : ℝ) - ((κ q0 + 5 : ℕ) : ℝ)) 0 ^ 2 := by
        have hnonneg :
            0 ≤ max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 := by
          exact le_max_right _ _
        have hnonneg' :
            0 ≤ max (((Nat.dist (j q0) (ℓ q0) : ℕ) : ℝ) - ((κ q0 + 5 : ℕ) : ℝ)) 0 := by
          exact le_max_right _ _
        nlinarith [hmax, hnonneg, hnonneg']
      have hsingle :
          max (((Nat.dist (j q0) (ℓ q0) : ℕ) : ℝ) - ((κ q0 + 5 : ℕ) : ℝ)) 0 ^ 2 ≤
            ∑ q : Fin d, max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2 := by
        simpa using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset (Fin d)))
            (a := q0)
            (f := fun q : Fin d =>
              max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2)
            (fun q hq => by positivity)
            (Finset.mem_univ q0))
      exact le_trans hsq0 hsingle
    calc
      ∏ q : Fin d,
          (Cq q *
            Real.exp
              (-(cq q) * max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2))
        = C *
            Real.exp
              (∑ q : Fin d,
                (-(cq q) * max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2)) :=
                    by
              rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      _ ≤ C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) := by
            have hsum_le :
                ∑ q : Fin d,
                    (-(cq q) * max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2) ≤
                  -(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2 := by
              have hterm :
                  ∀ q : Fin d,
                    (-(cq q) * max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2) ≤
                      (-(c) * max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2)
                          := by
                intro q
                nlinarith [hcsmall q,
                  sq_nonneg (max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0)]
              have hsum_term :
                  ∑ q : Fin d,
                      (-(cq q) * max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^
                          2) ≤
                    ∑ q : Fin d,
                      (-(c) * max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2)
                          := by
                exact Finset.sum_le_sum (fun q _ => hterm q)
              have hcollapse :
                  ∑ q : Fin d,
                      (-(c) * max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2) =
                    -(c) *
                      ∑ q : Fin d, max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0
                          ^ 2 := by
                rw [← Finset.mul_sum]
              have hfinal :
                  -(c) * ∑ q : Fin d, max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ))
                      0 ^ 2 ≤
                    -(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2 := by
                nlinarith [hsq_ge, hc_pos]
              linarith
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum_le) (le_of_lt hC_pos)

/-- Quantitative block localization estimate. -/
theorem blockLocalization
    {d : ℕ} (κ : MultiIndex d) :
    ∃ C c B : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
      ∀ j ℓ : MultiIndex d, ∀ G : FiniteHermiteSum d,
        annulusMass j (evalHermiteSum κ (blockPart ℓ G)) ≤
          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
            hermiteNormSq κ (blockPart ℓ G) := by
  classical
  obtain ⟨C, c, B, hCpos, hcpos, hBnonneg, hloc⟩ := productBasisLocalization (κ := κ)
  refine ⟨C, c, B, hCpos, hcpos, hBnonneg, ?_⟩
  intro j ℓ G
  rw [annulusParseval]
  have hC_nonneg : 0 ≤ C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) := by
    positivity
  calc
    Finset.sum (blockPart ℓ G).support
        (fun α => ‖(blockPart ℓ G).coeff α‖ ^ 2 * annulusMass j (PhiKappaAlpha κ α))
      ≤ Finset.sum (blockPart ℓ G).support
          (fun α =>
            ‖(blockPart ℓ G).coeff α‖ ^ 2 *
              (C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2))) := by
                refine Finset.sum_le_sum ?_
                intro α hα
                have hblock : α ∈ squareBlock ℓ := by
                  have hsuppnz : (blockPart ℓ G).coeff α ≠ 0 := by
                    simpa [FiniteHermiteSum.support, Finsupp.mem_support_iff] using hα
                  rw [blockPart, Finsupp.onFinset_apply] at hsuppnz
                  by_cases hb : α ∈ squareBlock ℓ
                  · exact hb
                  · simp [hb] at hsuppnz
                exact mul_le_mul_of_nonneg_left (hloc α j ℓ hblock) (by positivity)
    _ =
        (C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)) *
          Finset.sum (blockPart ℓ G).support (fun α => ‖(blockPart ℓ G).coeff α‖ ^ 2) := by
            calc
              Finset.sum (blockPart ℓ G).support
                  (fun α =>
                    ‖(blockPart ℓ G).coeff α‖ ^ 2 *
                      (C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)))
                =
                  Finset.sum (blockPart ℓ G).support
                    (fun α =>
                      (C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)) *
                        ‖(blockPart ℓ G).coeff α‖ ^ 2) := by
                          refine Finset.sum_congr rfl ?_
                          intro α hα
                          ring
              _ =
                  (C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)) *
                    Finset.sum (blockPart ℓ G).support (fun α => ‖(blockPart ℓ G).coeff α‖ ^ 2) :=
                        by
                      rw [Finset.mul_sum]
    _ =
        (C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)) *
          hermiteNormSq κ (blockPart ℓ G) := by
            rw [← finiteParseval]

/-- Crude shell-count helper for sup-norm block shells. -/
theorem shellCountingFormula
    (d r : ℕ) :
    (2 * r + 1) ^ d - (2 * r - 1) ^ d ≤ (2 * r + 1) ^ d := by
  /-
  Scaffolding guidance:
  replace this placeholder inequality with exact shell-count formulas on
  `ℤ^d` once the finite shell enumerators are fixed.
  -/
  exact Nat.sub_le _ _

/-- Gaussian tails with polynomial weights are summable. -/
theorem polynomialGaussianSeriesSummable
    (m : ℕ) (c : ℝ) (hc : 0 < c) :
    Summable (fun r : ℕ => (r : ℝ) ^ m * Real.exp (-c * r ^ 2)) := by
  obtain ⟨C, hCpos, hbound⟩ :=
    HermiteLEAN.polynomial_times_gaussian_le_gaussian hc m
  have hgeom :
      Summable (fun r : ℕ => Real.exp (-(c / 2) * (r : ℝ) ^ 2)) := by
    refine Real.summable_exp_nat_mul_of_ge ?_ ?_
    · linarith
    · intro i
      have hnat : i ≤ i * i := Nat.le_mul_self i
      have hreal : (i : ℝ) ≤ (i : ℝ) * (i : ℝ) := by
        exact_mod_cast hnat
      simpa [pow_two] using hreal
  have hmajor : Summable (fun r : ℕ => C * Real.exp (-(c / 2) * (r : ℝ) ^ 2)) :=
    hgeom.mul_left C
  exact Summable.of_nonneg_of_le
      (f := fun r : ℕ => C * Real.exp (-(c / 2) * (r : ℝ) ^ 2))
      (g := fun r : ℕ => (r : ℝ) ^ m * Real.exp (-c * (r : ℝ) ^ 2))
      (fun r => by positivity)
      (fun r => by
        calc
          (r : ℝ) ^ m * Real.exp (-c * (r : ℝ) ^ 2)
            ≤ (1 + (r : ℝ) ^ m) * Real.exp (-c * (r : ℝ) ^ 2) := by
              have hpow_le : (r : ℝ) ^ m ≤ 1 + (r : ℝ) ^ m := by linarith
              exact mul_le_mul_of_nonneg_right hpow_le (by positivity)
          _ ≤ C * Real.exp (-(c / 2) * (r : ℝ) ^ 2) := hbound (r : ℝ) (by positivity))
      hmajor

private lemma polynomialGaussianTailMajorant_summable
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Summable (fun r : ℕ => (1 + (r : ℝ) ^ k) * Real.exp (-a * (r : ℝ) ^ 2)) := by
  obtain ⟨C, hCpos, hbound⟩ :=
    HermiteLEAN.polynomial_times_gaussian_le_gaussian ha k
  have hgeom :
      Summable (fun r : ℕ => Real.exp (-(a / 2) * (r : ℝ) ^ 2)) := by
    refine Real.summable_exp_nat_mul_of_ge ?_ ?_
    · linarith
    · intro i
      have hnat : i ≤ i * i := Nat.le_mul_self i
      have hreal : (i : ℝ) ≤ (i : ℝ) * (i : ℝ) := by
        exact_mod_cast hnat
      simpa [pow_two] using hreal
  have hmajor : Summable (fun r : ℕ => C * Real.exp (-(a / 2) * (r : ℝ) ^ 2)) :=
    hgeom.mul_left C
  exact Summable.of_nonneg_of_le
      (f := fun r : ℕ => C * Real.exp (-(a / 2) * (r : ℝ) ^ 2))
      (g := fun r : ℕ => (1 + (r : ℝ) ^ k) * Real.exp (-a * (r : ℝ) ^ 2))
      (fun r => by positivity)
      (fun r => hbound (r : ℝ) (by positivity))
      hmajor

private lemma tailIndicator_tendsto_zero
    {u : ℕ → ℝ} (hu : Summable u) :
    Filter.Tendsto
      (fun M : ℕ => ∑' r : ℕ, if M + 1 ≤ r then u r else 0)
      Filter.atTop (nhds 0) := by
  have htail :
      Filter.Tendsto (fun M : ℕ => ∑' k : ℕ, u (k + (M + 1)))
        Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (tendsto_sum_nat_add u).comp (Filter.tendsto_add_atTop_nat 1)
  refine htail.congr' ?_
  filter_upwards [] with M
  have hsub :
      (∑' r : {r // r ∉ Finset.range (M + 1)}, u r) =
        ∑' r : ℕ, if M < r then u r else 0 := by
    simpa [Set.indicator, Finset.mem_range, Nat.not_lt] using
      (tsum_subtype (s := {r : ℕ | r ∉ Finset.range (M + 1)}) (f := u))
  have h1 :
      (∑ i ∈ Finset.range (M + 1), u i) +
          (∑' r : ℕ, if M < r then u r else 0) =
        ∑' i : ℕ, u i := by
    rw [← hsub]
    simpa using hu.sum_add_tsum_subtype_compl (Finset.range (M + 1))
  have h2 :
      (∑ i ∈ Finset.range (M + 1), u i) +
          (∑' k : ℕ, u (k + (M + 1))) =
        ∑' i : ℕ, u i := by
    simpa using hu.sum_add_tsum_nat_add (M + 1)
  have hEq : (∑' r : ℕ, if M < r then u r else 0) = ∑' k : ℕ, u (k + (M + 1)) := by
    linarith [h1, h2]
  simpa [Nat.succ_le_iff] using hEq.symm

private lemma shellExp_global_majorant
    {d : ℕ} {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧
      ∀ r : ℕ,
        (shellCardinality d r : ℝ) *
            Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2)
          ≤ K * (1 + (r : ℝ) ^ d) * Real.exp (-(c / 8) * (r : ℝ) ^ 2) := by
  refine ⟨(3 : ℝ) ^ d * Real.exp (c * B ^ 2), by positivity, ?_⟩
  intro r
  have hshell :
      (shellCardinality d r : ℝ) ≤ (3 : ℝ) ^ d * (1 + (r : ℝ) ^ d) := by
    by_cases hr0 : r = 0
    · subst hr0
      have hzero_nat : shellCardinality d 0 ≤ 1 := by
        simp [shellCardinality]
      have hzero : (shellCardinality d 0 : ℝ) ≤ 1 := by
        exact_mod_cast hzero_nat
      have hpow_pos : 0 < (3 : ℝ) ^ d := by
        positivity
      have hone :
          (1 : ℝ) ≤ (3 : ℝ) ^ d * (1 + (((0 : ℕ) : ℝ) ^ d)) := by
        have hpow1 : (1 : ℝ) ≤ (3 : ℝ) ^ d := by
          exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
        have hfac : (1 : ℝ) ≤ 1 + (((0 : ℕ) : ℝ) ^ d) := by
          have hnonneg : (0 : ℝ) ≤ (((0 : ℕ) : ℝ) ^ d) := by positivity
          linarith
        calc
          (1 : ℝ) ≤ (3 : ℝ) ^ d := hpow1
          _ ≤ (3 : ℝ) ^ d * (1 + (((0 : ℕ) : ℝ) ^ d)) := by
            exact le_mul_of_one_le_right (le_of_lt hpow_pos) hfac
      exact le_trans hzero hone
    · have hr1 : 1 ≤ r := Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mpr hr0)
      have hs : (shellCardinality d r : ℝ) ≤ ((2 * r + 1) ^ d : ℕ) := by
        exact_mod_cast shellCountingFormula d r
      have hbase : (2 * r + 1 : ℝ) ≤ 3 * r := by
        nlinarith [show (1 : ℝ) ≤ r by exact_mod_cast hr1]
      have hpow : (2 * r + 1 : ℝ) ^ d ≤ (3 * r : ℝ) ^ d := by
        gcongr
      have hshell' : (shellCardinality d r : ℝ) ≤ (3 : ℝ) ^ d * (r : ℝ) ^ d := by
        calc
          (shellCardinality d r : ℝ) ≤ (2 * r + 1 : ℝ) ^ d := by
            exact_mod_cast hs
          _ ≤ (3 * r : ℝ) ^ d := hpow
          _ = (3 : ℝ) ^ d * (r : ℝ) ^ d := by rw [mul_pow]
      have hrpow_nonneg : 0 ≤ (r : ℝ) ^ d := by positivity
      exact le_trans hshell' <| mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have hexp :
      Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) ≤
        Real.exp (c * B ^ 2) * Real.exp (-(c / 8) * (r : ℝ) ^ 2) := by
    have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
    have hsq :
        (r : ℝ) ^ 2 / 8 - B ^ 2 ≤ max ((r : ℝ) - B) 0 ^ 2 := by
      by_cases hsmall : (r : ℝ) ≤ 2 * B
      · have hrhs_nonpos : (r : ℝ) ^ 2 / 8 - B ^ 2 ≤ 0 := by
          nlinarith
        have hnonneg : 0 ≤ max ((r : ℝ) - B) 0 ^ 2 := by positivity
        linarith
      · have hlarge : 2 * B < (r : ℝ) := by linarith
        have hhalf : (r : ℝ) / 2 ≤ (r : ℝ) - B := by
          nlinarith
        have hmaxeq : max ((r : ℝ) - B) 0 = (r : ℝ) - B := by
          apply max_eq_left
          linarith
        rw [hmaxeq]
        have hsquare_half : ((r : ℝ) / 2) ^ 2 ≤ ((r : ℝ) - B) ^ 2 := by
          nlinarith
        nlinarith [hsquare_half]
    have hlog :
        -(c) * max ((r : ℝ) - B) 0 ^ 2 ≤ c * B ^ 2 - (c / 8) * (r : ℝ) ^ 2 := by
      nlinarith [hsq, hc]
    calc
      Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2)
        ≤ Real.exp (c * B ^ 2 - (c / 8) * (r : ℝ) ^ 2) := by
          exact Real.exp_le_exp.mpr hlog
      _ = Real.exp (c * B ^ 2) * Real.exp (-(c / 8) * (r : ℝ) ^ 2) := by
          have hsplit :
              c * B ^ 2 - (c / 8) * (r : ℝ) ^ 2 =
                c * B ^ 2 + (-(c / 8) * (r : ℝ) ^ 2) := by
            ring
          rw [hsplit, Real.exp_add]
  calc
    (shellCardinality d r : ℝ) * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2)
      ≤ ((3 : ℝ) ^ d * (1 + (r : ℝ) ^ d)) *
          (Real.exp (c * B ^ 2) * Real.exp (-(c / 8) * (r : ℝ) ^ 2)) := by
            exact mul_le_mul hshell hexp (by positivity) (by positivity)
    _ = ((3 : ℝ) ^ d * Real.exp (c * B ^ 2)) *
          (1 + (r : ℝ) ^ d) * Real.exp (-(c / 8) * (r : ℝ) ^ 2) := by ring

private lemma localizationLeakageSeriesSummable
    {d : ℕ} {C c B : ℝ} (hC : 0 < C) (hc : 0 < c) (hB : 0 ≤ B) :
    Summable
      (fun r : ℕ =>
        C * ((shellCardinality d r : ℝ) *
          Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2))) := by
  obtain ⟨K, hKpos, hmajor⟩ := shellExp_global_majorant (d := d) hc hB
  have hsum : Summable (fun r : ℕ => K * (1 + (r : ℝ) ^ d) * Real.exp (-(c / 8) * (r : ℝ) ^ 2)) :=
      by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (polynomialGaussianTailMajorant_summable
        (a := c / 8)
        (by linarith)
        d).mul_left K
  exact Summable.of_nonneg_of_le
      (f := fun r : ℕ =>
        K * (1 + (r : ℝ) ^ d) * Real.exp (-(c / 8) * (r : ℝ) ^ 2) * C)
      (g := fun r : ℕ =>
        C * ((shellCardinality d r : ℝ) *
          Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2)))
      (fun r => by positivity)
      (fun r => by
        have := hmajor r
        nlinarith [this, hC])
      (hsum.mul_right C)

private lemma localizationLeakageCoefficient_tendsto_zero
    {d : ℕ} {C c B : ℝ} (hC : 0 < C) (hc : 0 < c) (hB : 0 ≤ B) :
    Filter.Tendsto
      (fun M : ℕ => localizationLeakageCoefficient C c B d M)
      Filter.atTop (nhds 0) := by
  have hu := localizationLeakageSeriesSummable (d := d) hC hc hB
  have htail :=
    tailIndicator_tendsto_zero
      (u := fun r : ℕ =>
        C * ((shellCardinality d r : ℝ) *
          Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2))) hu
  refine htail.congr' ?_
  filter_upwards [] with M
  unfold localizationLeakageCoefficient
  have hterm :
      (∑' r : ℕ,
        if M + 1 ≤ r then
          C * ((shellCardinality d r : ℝ) * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2))
        else 0) =
      ∑' r : ℕ,
        C * (if M + 1 ≤ r then
          (shellCardinality d r : ℝ) * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2)
        else 0) := by
    apply tsum_congr
    intro r
    by_cases hr : M + 1 ≤ r
    · simp [hr]
    · simp [hr]
  rw [hterm, tsum_mul_left]

private lemma shell_sum_localizationLeakageCoefficient_bound
    {d : ℕ} {C c B : ℝ} (hC : 0 < C) (hc : 0 < c) (hB : 0 ≤ B)
    (M : ℕ) (t : Finset ℕ) :
    Finset.sum t
      (fun r =>
        (shellCardinality d r : ℝ) *
          (if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0)) ≤
      localizationLeakageCoefficient C c B d M := by
  let u : ℕ → ℝ := fun r =>
    if M + 1 ≤ r then
      C * ((shellCardinality d r : ℝ) *
        Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2))
    else 0
  have hu_base := localizationLeakageSeriesSummable (d := d) hC hc hB
  have hu : Summable u := by
    refine Summable.of_nonneg_of_le ?_ ?_ hu_base
    · intro r
      by_cases hlt : M < r
      · simp only [Order.add_one_le_iff, neg_mul, hlt, ↓reduceIte, u]
        positivity
      · have : ¬ M + 1 ≤ r := by omega
        simp [u, hlt]
    · intro r
      by_cases hr : M + 1 ≤ r
      · by_cases hlt : M < r
        · simp [u, hlt]
        · have : False := by omega
          contradiction
      · have hlt : ¬ M < r := by omega
        simp only [Order.add_one_le_iff, neg_mul, hlt, ↓reduceIte, ge_iff_le, u]
        positivity
  calc
    Finset.sum t
      (fun r =>
        (shellCardinality d r : ℝ) *
          (if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0))
      = Finset.sum t u := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          by_cases hMr : M < r
          · have hMr' : M + 1 ≤ r := by omega
            simp [u, hMr]
            ring
          · have hMr' : ¬ M + 1 ≤ r := by omega
            simp [u, hMr]
    _ ≤ ∑' r : ℕ, u r := by
          exact hu.sum_le_tsum _ (fun r hr => by
            by_cases hMr : M + 1 ≤ r
            · simp only [hMr, ↓reduceIte, neg_mul]
              positivity
            · by_cases hlt : M < r
              · have : False := by omega
                contradiction
              · simp [hMr])
    _ = localizationLeakageCoefficient C c B d M := by
          let v : ℕ → ℝ := fun r =>
            if M + 1 ≤ r then
              (shellCardinality d r : ℝ) * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2)
            else 0
          have huv : u = fun r => C * v r := by
            funext r
            by_cases hMr : M + 1 ≤ r
            · simp [u, v]
            · simp [u, v]
          unfold localizationLeakageCoefficient
          rw [show (∑' r : ℕ, u r) = ∑' r : ℕ, C * v r by simp [huv]]
          rw [tsum_mul_left]

private lemma remainderPart_annulus_le_of_support_image_bound
    {d : ℕ} (κ : MultiIndex d) {C c B R : ℝ}
    (hC : 0 ≤ C)
    (hloc :
      ∀ j ℓ : MultiIndex d, ∀ G : FiniteHermiteSum d,
        annulusMass j (evalHermiteSum κ (blockPart ℓ G)) ≤
          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
            hermiteNormSq κ (blockPart ℓ G))
    {j : MultiIndex d} {M : ℕ} {G : FiniteHermiteSum d}
    (hbound :
      Finset.sum ((remainderPart j M G).support.image blockIndexMulti)
        (fun ℓ =>
          if M < blockDistance j ℓ then
            C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
              hermiteNormSq κ (blockPart ℓ G)
          else 0) ≤ R) :
    annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤ R := by
  exact le_trans (remainderPart_annulus_blockwise_bound (κ := κ) (hC := hC) hloc j M G) hbound

private lemma finitePartialLeakage_bound_of_shell_sum_bound
    {d : ℕ} (κ : MultiIndex d) {C c B : ℝ}
    (hC : 0 ≤ C)
    (hloc :
      ∀ j ℓ : MultiIndex d, ∀ G : FiniteHermiteSum d,
        annulusMass j (evalHermiteSum κ (blockPart ℓ G)) ≤
          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
            hermiteNormSq κ (blockPart ℓ G))
    (hshell :
      ∀ (M : ℕ) (ℓ : MultiIndex d) (s : Finset (MultiIndex d)),
        Finset.sum s
          (fun j =>
            if M < blockDistance j ℓ then
              C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
            else 0) ≤
          localizationLeakageCoefficient C c B d M)
    (s : Finset (MultiIndex d)) (M : ℕ) (G : FiniteHermiteSum d) :
    Finset.sum s (fun j => annulusMass j (evalHermiteSum κ (remainderPart j M G))) ≤
      localizationLeakageCoefficient C c B d M * hermiteNormSq κ G := by
  have hpoint :
      ∀ j : MultiIndex d,
        annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤
          Finset.sum (G.support.image blockIndexMulti)
            (fun ℓ =>
              if M < blockDistance j ℓ then
                C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                  hermiteNormSq κ (blockPart ℓ G)
              else 0) := by
    intro j
    have hrem_support_subset : (remainderPart j M G).support ⊆ G.support := by
      intro α hα
      have hfar_support := (explicitLocalAndFarSupport (j := j) (M := M) (G := G)).2.2.2
      rw [hfar_support] at hα
      exact (Finset.mem_filter.mp hα).1
    have hrem_image_subset :
        (remainderPart j M G).support.image blockIndexMulti ⊆ G.support.image blockIndexMulti := by
      intro ℓ hℓ
      rcases Finset.mem_image.mp hℓ with ⟨α, hα, rfl⟩
      exact Finset.mem_image.mpr ⟨α, hrem_support_subset hα, rfl⟩
    calc
      annulusMass j (evalHermiteSum κ (remainderPart j M G))
        ≤ Finset.sum ((remainderPart j M G).support.image blockIndexMulti)
            (fun ℓ =>
              if M < blockDistance j ℓ then
                C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                  hermiteNormSq κ (blockPart ℓ G)
              else 0) := by
                exact remainderPart_annulus_blockwise_bound (κ := κ) (hC := hC) hloc j M G
      _ ≤ Finset.sum (G.support.image blockIndexMulti)
            (fun ℓ =>
              if M < blockDistance j ℓ then
                C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                  hermiteNormSq κ (blockPart ℓ G)
              else 0) := by
                exact Finset.sum_le_sum_of_subset_of_nonneg hrem_image_subset (by
                  intro ℓ hℓ hnot
                  by_cases hfar : M < blockDistance j ℓ
                  · have hexp_nonneg :
                        0 ≤ Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) := by
                      positivity
                    have hnorm_nonneg : 0 ≤ hermiteNormSq κ (blockPart ℓ G) := by
                      rw [finiteParseval]
                      positivity
                    simpa [hfar] using
                      (mul_nonneg (mul_nonneg hC hexp_nonneg) hnorm_nonneg)
                  · simp [hfar])
  calc
    Finset.sum s (fun j => annulusMass j (evalHermiteSum κ (remainderPart j M G)))
      ≤ Finset.sum s
          (fun j =>
            Finset.sum (G.support.image blockIndexMulti)
              (fun ℓ =>
                if M < blockDistance j ℓ then
                  C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                    hermiteNormSq κ (blockPart ℓ G)
                else 0)) := by
                  refine Finset.sum_le_sum ?_
                  intro j hj
                  exact hpoint j
    _ = Finset.sum (G.support.image blockIndexMulti)
          (fun ℓ =>
            Finset.sum s
              (fun j =>
                if M < blockDistance j ℓ then
                  C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                    hermiteNormSq κ (blockPart ℓ G)
                else 0)) := by
            rw [Finset.sum_comm]
    _ ≤ Finset.sum (G.support.image blockIndexMulti)
          (fun ℓ => localizationLeakageCoefficient C c B d M * hermiteNormSq κ (blockPart ℓ G)) :=
              by
            refine Finset.sum_le_sum ?_
            intro ℓ hℓ
            have hnorm_nonneg : 0 ≤ hermiteNormSq κ (blockPart ℓ G) := by
              rw [finiteParseval]
              positivity
            have hshell' := hshell M ℓ s
            have hfactor :
                Finset.sum s
                  (fun j =>
                    if M < blockDistance j ℓ then
                      C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                        hermiteNormSq κ (blockPart ℓ G)
                    else 0) =
                  (Finset.sum s
                    (fun j =>
                      if M < blockDistance j ℓ then
                        C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
                      else 0)) *
                    hermiteNormSq κ (blockPart ℓ G) := by
                      calc
                        Finset.sum s
                            (fun j =>
                              if M < blockDistance j ℓ then
                                C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^
                                    2) *
                                  hermiteNormSq κ (blockPart ℓ G)
                              else 0)
                          =
                            Finset.sum s
                              (fun j =>
                                (if M < blockDistance j ℓ then
                                  C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^
                                      2)
                                else 0) * hermiteNormSq κ (blockPart ℓ G)) := by
                                  refine Finset.sum_congr rfl ?_
                                  intro j hj
                                  by_cases hfar : M < blockDistance j ℓ
                                  · simp [hfar, mul_left_comm, mul_comm]
                                  · simp [hfar]
                        _ =
                            (Finset.sum s
                              (fun j =>
                                if M < blockDistance j ℓ then
                                  C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^
                                      2)
                                else 0)) *
                              hermiteNormSq κ (blockPart ℓ G) := by
                                rw [← Finset.sum_mul]
            rw [hfactor]
            exact mul_le_mul_of_nonneg_right hshell' hnorm_nonneg
    _ = localizationLeakageCoefficient C c B d M * hermiteNormSq κ G := by
          rw [← Finset.mul_sum, ← blockDecompositionNorm_sum_support_image]

private lemma hermiteNormSq_nonneg
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    0 ≤ hermiteNormSq κ G := by
  rw [finiteParseval]
  positivity

private lemma shell_sum_bound_of_shell_cardinality_bound
    {d : ℕ} {C c B : ℝ}
    (hC : 0 ≤ C)
    (htail :
      ∀ (M : ℕ) (t : Finset ℕ),
        Finset.sum t
          (fun r =>
            (shellCardinality d r : ℝ) *
              (if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0)) ≤
          localizationLeakageCoefficient C c B d M)
    (hcard :
      ∀ (ℓ : MultiIndex d) (r : ℕ) (s : Finset (MultiIndex d)),
        1 ≤ r →
        (((s.filter fun j => blockDistance j ℓ = r).card : ℕ) : ℝ) ≤ shellCardinality d r)
    (M : ℕ) (ℓ : MultiIndex d) (s : Finset (MultiIndex d)) :
    Finset.sum s
      (fun j =>
        if M < blockDistance j ℓ then
          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
        else 0) ≤
      localizationLeakageCoefficient C c B d M := by
  let t : Finset ℕ := s.image (fun j => blockDistance j ℓ)
  have hmaps : ∀ j ∈ s, blockDistance j ℓ ∈ t := by
    intro j hj
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hdecomp := Finset.sum_fiberwise_of_maps_to (s := s) (t := t)
    (g := fun j : MultiIndex d => blockDistance j ℓ)
    (h := hmaps)
    (f := fun j : MultiIndex d =>
      if M < blockDistance j ℓ then
        C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
      else 0)
  dsimp [t] at hdecomp
  rw [← hdecomp]
  have hfiber :
      ∀ r ∈ s.image (fun j => blockDistance j ℓ),
        Finset.sum (s.filter fun j => blockDistance j ℓ = r)
          (fun j =>
            if M < blockDistance j ℓ then
              C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
            else 0) =
          (((s.filter fun j => blockDistance j ℓ = r).card : ℕ) : ℝ) *
            (if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0) := by
    intro r hr
    calc
      Finset.sum (s.filter fun j => blockDistance j ℓ = r)
        (fun j =>
          if M < blockDistance j ℓ then
            C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
          else 0)
        =
          Finset.sum (s.filter fun j => blockDistance j ℓ = r)
            (fun _ =>
              if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hjr : blockDistance j ℓ = r := by
                simpa using (Finset.mem_filter.mp hj).2
              simp [hjr]
      _ =
          (((s.filter fun j => blockDistance j ℓ = r).card : ℕ) : ℝ) *
            (if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0) := by
              rw [Finset.sum_const, nsmul_eq_mul]
  calc
    Finset.sum (s.image (fun j => blockDistance j ℓ))
      (fun r =>
        Finset.sum (s.filter fun j => blockDistance j ℓ = r)
          (fun j =>
            if M < blockDistance j ℓ then
              C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
            else 0))
      ≤
        Finset.sum (s.image (fun j => blockDistance j ℓ))
          (fun r =>
            (shellCardinality d r : ℝ) *
              (if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0)) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          rw [hfiber r hr]
          have hker_nonneg :
              0 ≤ if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0 := by
            by_cases hMr : M < r
            · simp only [hMr, ↓reduceIte, neg_mul]
              positivity
            · simp [hMr]
          by_cases hMr : M < r
          · have hr1 : 1 ≤ r := by omega
            exact mul_le_mul_of_nonneg_right (hcard ℓ r s hr1) hker_nonneg
          · simp [hMr] at hker_nonneg
            simp [hMr]
    _ ≤ localizationLeakageCoefficient C c B d M := by
          exact htail M (s.image (fun j => blockDistance j ℓ))

private lemma finiteLeakage_global_bound_of_shell_sum_bound
    {d : ℕ} (κ : MultiIndex d)
    {C c B : ℝ}
    (hC : 0 ≤ C)
    (hloc : ∀ j ℓ : MultiIndex d, ∀ G : FiniteHermiteSum d,
      annulusMass j (evalHermiteSum κ (blockPart ℓ G)) ≤
        C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
          hermiteNormSq κ (blockPart ℓ G))
    (hshell : ∀ (M : ℕ) (ℓ : MultiIndex d) (s : Finset (MultiIndex d)),
      Finset.sum s
        (fun j =>
          if M < blockDistance j ℓ then
            C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
          else 0) ≤
        localizationLeakageCoefficient C c B d M) :
    ∀ (M : ℕ) (G : FiniteHermiteSum d),
      ∑' j : MultiIndex d, annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤
        localizationLeakageCoefficient C c B d M * hermiteNormSq κ G := by
  intro M G
  refine Real.tsum_le_of_sum_le ?_ ?_
  · intro j
    unfold annulusMass
    exact integral_nonneg fun z => by
      by_cases hz : z ∈ productAnnulus j <;> simp [hz]
  · intro s
    have hpoint :
        ∀ j : MultiIndex d,
          annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤
            Finset.sum (G.support.image blockIndexMulti)
              (fun ℓ => if M < blockDistance j ℓ then
                C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                  hermiteNormSq κ (blockPart ℓ G)
              else 0) := by
      intro j
      have hrem_support_subset : (remainderPart j M G).support ⊆ G.support := by
        intro α hα
        have hfar_support := (explicitLocalAndFarSupport (j := j) (M := M) (G := G)).2.2.2
        rw [hfar_support] at hα
        exact (Finset.mem_filter.mp hα).1
      have hrem_image_subset :
          (remainderPart j M G).support.image blockIndexMulti ⊆ G.support.image blockIndexMulti :=
              by
        intro ℓ hℓ
        rcases Finset.mem_image.mp hℓ with ⟨α, hα, rfl⟩
        exact Finset.mem_image.mpr ⟨α, hrem_support_subset hα, rfl⟩
      calc
        annulusMass j (evalHermiteSum κ (remainderPart j M G))
          ≤ Finset.sum ((remainderPart j M G).support.image blockIndexMulti)
              (fun ℓ => if M < blockDistance j ℓ then
                C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                  hermiteNormSq κ (blockPart ℓ G)
              else 0) := remainderPart_annulus_blockwise_bound (κ := κ) (hC := hC) hloc j M G
        _ ≤ Finset.sum (G.support.image blockIndexMulti)
              (fun ℓ => if M < blockDistance j ℓ then
                C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                  hermiteNormSq κ (blockPart ℓ G)
              else 0) := by
                exact Finset.sum_le_sum_of_subset_of_nonneg hrem_image_subset (by
                  intro ℓ hℓ hnot
                  by_cases hfar : M < blockDistance j ℓ
                  · have hexp_nonneg :
                        0 ≤ Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) := by
                      positivity
                    have hnorm_nonneg : 0 ≤ hermiteNormSq κ (blockPart ℓ G) := by
                      exact hermiteNormSq_nonneg κ (blockPart ℓ G)
                    simpa [hfar] using
                      (mul_nonneg (mul_nonneg hC hexp_nonneg) hnorm_nonneg)
                  · simp [hfar])
    calc
      Finset.sum s (fun j => annulusMass j (evalHermiteSum κ (remainderPart j M G)))
        ≤ Finset.sum s
            (fun j =>
              Finset.sum (G.support.image blockIndexMulti)
                (fun ℓ => if M < blockDistance j ℓ then
                  C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                    hermiteNormSq κ (blockPart ℓ G)
                else 0)) := by
                refine Finset.sum_le_sum ?_
                intro j hj
                exact hpoint j
      _ = Finset.sum (G.support.image blockIndexMulti)
            (fun ℓ =>
              Finset.sum s
                (fun j =>
                  if M < blockDistance j ℓ then
                    C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                      hermiteNormSq κ (blockPart ℓ G)
                  else 0)) := by
              rw [Finset.sum_comm]
      _ ≤ Finset.sum (G.support.image blockIndexMulti)
            (fun ℓ => localizationLeakageCoefficient C c B d M * hermiteNormSq κ (blockPart ℓ G))
                := by
              refine Finset.sum_le_sum ?_
              intro ℓ hℓ
              have hnorm_nonneg : 0 ≤ hermiteNormSq κ (blockPart ℓ G) :=
                hermiteNormSq_nonneg κ (blockPart ℓ G)
              have hshell' := hshell M ℓ s
              have hfactor :
                  Finset.sum s
                    (fun j =>
                      if M < blockDistance j ℓ then
                        C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                          hermiteNormSq κ (blockPart ℓ G)
                      else 0) =
                    (Finset.sum s
                      (fun j =>
                        if M < blockDistance j ℓ then
                          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
                        else 0)) *
                    hermiteNormSq κ (blockPart ℓ G) := by
                      rw [Finset.sum_mul]
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      by_cases hfar : M < blockDistance j ℓ
                      · simp [hfar, mul_left_comm, mul_comm]
                      · simp [hfar]
              rw [hfactor]
              exact mul_le_mul_of_nonneg_right hshell' hnorm_nonneg
      _ = localizationLeakageCoefficient C c B d M * hermiteNormSq κ G := by
            rw [← Finset.mul_sum, ← blockDecompositionNorm_sum_support_image]

private theorem finiteLeakage_of_blockLocalization_shell_sum_bound
    {d : ℕ} (κ : MultiIndex d)
    (htail :
      ∀ {C c B : ℝ},
        0 < C → 0 < c → 0 ≤ B →
        (∀ j ℓ : MultiIndex d, ∀ G : FiniteHermiteSum d,
          annulusMass j (evalHermiteSum κ (blockPart ℓ G)) ≤
            C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
              hermiteNormSq κ (blockPart ℓ G)) →
        Filter.Tendsto
          (fun M : ℕ => localizationLeakageCoefficient C c B d M)
          Filter.atTop (nhds 0))
    (hshell :
      ∀ {C c B : ℝ},
        0 < C → 0 < c → 0 ≤ B →
        (∀ j ℓ : MultiIndex d, ∀ G : FiniteHermiteSum d,
          annulusMass j (evalHermiteSum κ (blockPart ℓ G)) ≤
            C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
              hermiteNormSq κ (blockPart ℓ G)) →
        ∀ (M : ℕ) (ℓ : MultiIndex d) (s : Finset (MultiIndex d)),
          Finset.sum s
            (fun j =>
              if M < blockDistance j ℓ then
                C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
              else 0) ≤
            localizationLeakageCoefficient C c B d M) :
    ∃ C c B : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
      Filter.Tendsto
        (fun M : ℕ => localizationLeakageCoefficient C c B d M)
        Filter.atTop (nhds 0) ∧
      ∀ (M : ℕ) (G : FiniteHermiteSum d),
        ∑' j : MultiIndex d, annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤
          localizationLeakageCoefficient C c B d M * hermiteNormSq κ G := by
  obtain ⟨C, c, B, hCpos, hcpos, hBnonneg, hloc⟩ := blockLocalization (κ := κ)
  refine ⟨C, c, B, hCpos, hcpos, hBnonneg, ?_, ?_⟩
  · exact htail hCpos hcpos hBnonneg hloc
  · exact finiteLeakage_global_bound_of_shell_sum_bound (κ := κ) (le_of_lt hCpos) hloc
      (hshell hCpos hcpos hBnonneg hloc)

/-- Leakage coefficient tends to zero and controls the global remainder. -/
theorem finiteLeakage
    {d : ℕ} (κ : MultiIndex d) :
    ∃ C c B : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
      Filter.Tendsto
        (fun M : ℕ => localizationLeakageCoefficient C c B d M)
        Filter.atTop (nhds 0) ∧
      ∀ (M : ℕ) (G : FiniteHermiteSum d),
        ∑' j : MultiIndex d, annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤
          localizationLeakageCoefficient C c B d M * hermiteNormSq κ G := by
  /-
  Scaffolding guidance:
  the second clause is the one consumed by the coercivity assembly file.
  Keep it in exactly this global summed form.
  -/
  refine finiteLeakage_of_blockLocalization_shell_sum_bound (κ := κ) ?_ ?_
  · intro C c B hC hc hB hloc
    exact localizationLeakageCoefficient_tendsto_zero (d := d) hC hc hB
  · intro C c B hC hc hB hloc M ℓ s
    exact shell_sum_bound_of_shell_cardinality_bound
      (d := d) (C := C) (c := c) (B := B) (le_of_lt hC)
      (shell_sum_localizationLeakageCoefficient_bound (d := d) hC hc hB)
      (fun ℓ r s hr => shell_cardinality_bound_filter ℓ r s hr)
      M ℓ s

/-- Leakage coefficient tends to zero and controls all finite partial remainder sums. -/
theorem finitePartialLeakage
    {d : ℕ} (κ : MultiIndex d) :
    ∃ C c B : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
      Filter.Tendsto
        (fun M : ℕ => localizationLeakageCoefficient C c B d M)
        Filter.atTop (nhds 0) ∧
      ∀ (s : Finset (MultiIndex d)) (M : ℕ) (G : FiniteHermiteSum d),
        ∑ j ∈ s, annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤
          localizationLeakageCoefficient C c B d M * hermiteNormSq κ G := by
  obtain ⟨C, c, B, hCpos, hcpos, hBnonneg, hloc⟩ := blockLocalization (κ := κ)
  refine ⟨C, c, B, hCpos, hcpos, hBnonneg, ?_, ?_⟩
  · exact localizationLeakageCoefficient_tendsto_zero (d := d) hCpos hcpos hBnonneg
  · intro s M G
    exact finitePartialLeakage_bound_of_shell_sum_bound
      (κ := κ) (hC := le_of_lt hCpos) hloc
      (shell_sum_bound_of_shell_cardinality_bound
        (d := d) (C := C) (c := c) (B := B) (le_of_lt hCpos)
        (shell_sum_localizationLeakageCoefficient_bound (d := d) hCpos hcpos hBnonneg)
        (fun ℓ r s hr => shell_cardinality_bound_filter ℓ r s hr))
      s M G

end Hermite1DimdLEAN
