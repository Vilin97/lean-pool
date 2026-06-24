/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ImportedAnalyticInputs
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.TrueLevelBasis
import Mathlib.Analysis.Complex.Isometry

/-! # ProductBasisAndAnnuli -/



open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Hermite1DimdLEAN

/-!
# ProductBasisAndAnnuli

Finite several-variable basis infrastructure.
Scaffolding notes: `ScaffoldingNotes/Basis/product_basis_and_annuli.md`.
-/

private lemma integrable_oneDimPhi_cross_gaussian
    (k m n : ℕ) :
    Integrable
      (fun z : CSpace 1 => oneDimPhi k m (z 0) * conj (oneDimPhi k n (z 0)))
      (gaussianMeasure 1) := by
  change
    Integrable
      (fun z : CSpace 1 => HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))
      (gaussianMeasure 1)
  rw [gaussianMeasure, MeasureTheory.integrable_withDensity_iff_integrable_smul']
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
    have hnonneg : 0 ≤ π⁻¹ * rexp (-‖z 0‖ ^ 2) := by positivity
    simp only [gaussianDensity, pow_one, one_div, univ_unique, Fin.default_eq_zero, Fin.isValue,
      sum_singleton, hnonneg, ENNReal.toReal_ofReal, real_smul, ofReal_exp, ofReal_neg, ofReal_pow]
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

private theorem gaussianInner_self
    {d : ℕ} (F : CSpace d → ℂ) :
    gaussianInner F F = ((gaussianL2NormSq F : ℝ) : ℂ) := by
  unfold gaussianInner gaussianL2NormSq
  have hfun :
      (fun z : CSpace d => F z * conj (F z)) =
        fun z : CSpace d => ((‖F z‖ ^ 2 : ℝ) : ℂ) := by
    funext z
    simpa using Complex.mul_conj' (F z)
  rw [hfun, integral_complex_ofReal]

private lemma integrable_productBasis_cross
    {d : ℕ} (κ α β : MultiIndex d) :
    Integrable
      (fun z : CSpace d => PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z))
      (gaussianMeasure d) := by
  simpa [PhiKappaAlpha, Finset.prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm] using
    (tensorGaussianFactorization d
      (fun q z => oneDimPhi (κ q) (α q) z)
      (fun q z => oneDimPhi (κ q) (β q) z)
      (fun q => by
        simpa [oneDimLift] using
          integrable_oneDimPhi_cross_gaussian (κ q) (α q) (β q))).1

private lemma gaussianInner_finite_sum_basis
    {d : ℕ} (κ β : MultiIndex d)
    (s : Finset (MultiIndex d)) (c : MultiIndex d → ℂ) :
    gaussianInner (fun z => Finset.sum s (fun α => c α * PhiKappaAlpha κ α z)) (PhiKappaAlpha κ β) =
      Finset.sum s (fun α => c α * gaussianInner (PhiKappaAlpha κ α) (PhiKappaAlpha κ β)) := by
  unfold gaussianInner
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul]
  · intro α hα
    simpa [mul_assoc] using (integrable_productBasis_cross κ α β).const_mul (c α)

private lemma gaussianInner_finite_sum
    {d : ℕ} (κ : MultiIndex d)
    (s t : Finset (MultiIndex d)) (a b : MultiIndex d → ℂ) :
    gaussianInner
        (fun z => Finset.sum s (fun α => a α * PhiKappaAlpha κ α z))
        (fun z => Finset.sum t (fun β => b β * PhiKappaAlpha κ β z)) =
      Finset.sum t
        (fun β =>
          conj (b β) *
            gaussianInner
              (fun z => Finset.sum s (fun α => a α * PhiKappaAlpha κ α z))
              (PhiKappaAlpha κ β)) := by
  unfold gaussianInner
  have hfun :
      (fun z : CSpace d =>
        (Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) *
          conj (Finset.sum t (fun β => b β * PhiKappaAlpha κ β z))) =
        fun z : CSpace d =>
          Finset.sum t
            (fun β =>
              conj (b β) *
                ((Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) *
                  conj (PhiKappaAlpha κ β z))) := by
    funext z
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro β hβ
    simp [mul_assoc, mul_comm]
  rw [hfun, MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul]
  · intro β hβ
    have hsumInt :
        Integrable
          (fun z : CSpace d =>
            (Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) *
              conj (PhiKappaAlpha κ β z))
          (gaussianMeasure d) := by
      simp_rw [Finset.sum_mul, mul_assoc]
      exact MeasureTheory.integrable_finsetSum _ fun α _ =>
        (integrable_productBasis_cross κ α β).const_mul (a α)
    simpa [mul_assoc] using (hsumInt.const_mul (conj (b β)))

private lemma measurableSet_productAnnulus
    {d : ℕ} (j : MultiIndex d) :
    MeasurableSet (productAnnulus j) := by
  classical
  have h :
      MeasurableSet (⋂ q : Fin d, {z : CSpace d | (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1}) := by
    refine MeasurableSet.iInter (f := fun q : Fin d => {z : CSpace d | (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ <
        (j q : ℝ) + 1}) ?_
    intro q
    have hge : MeasurableSet {z : CSpace d | (j q : ℝ) ≤ ‖z q‖} :=
      measurableSet_le measurable_const (measurable_norm.comp (continuous_apply q).measurable)
    have hlt : MeasurableSet {z : CSpace d | ‖z q‖ < (j q : ℝ) + 1} :=
      measurableSet_lt (measurable_norm.comp (continuous_apply q).measurable) measurable_const
    simpa [Set.setOf_and] using hge.inter hlt
  simpa [productAnnulus, Set.setOf_forall] using h

private lemma productAnnulus_eq_of_mem
    {d : ℕ} {j ℓ : MultiIndex d} {z : CSpace d}
    (hj : z ∈ productAnnulus j) (hℓ : z ∈ productAnnulus ℓ) :
    j = ℓ := by
  funext q
  rcases hj q with ⟨hj_lower, hj_upper⟩
  rcases hℓ q with ⟨hℓ_lower, hℓ_upper⟩
  have h1 : j q < ℓ q + 1 := by exact_mod_cast lt_of_le_of_lt hj_lower hℓ_upper
  have h2 : ℓ q < j q + 1 := by exact_mod_cast lt_of_le_of_lt hℓ_lower hj_upper
  omega

private lemma integrable_evalHermiteSum_cross
    {d : ℕ} (κ : MultiIndex d) (G H : FiniteHermiteSum d) :
    Integrable
      (fun z : CSpace d => evalHermiteSum κ G z * conj (evalHermiteSum κ H z))
      (gaussianMeasure d) := by
  classical
  unfold evalHermiteSum
  have hrewrite :
      (fun z : CSpace d =>
        (∑ α ∈ G.support, G.coeff α * PhiKappaAlpha κ α z) *
          conj (∑ β ∈ H.support, H.coeff β * PhiKappaAlpha κ β z)) =
        (fun z : CSpace d =>
          ∑ α ∈ G.support,
            ∑ β ∈ H.support,
              G.coeff α * conj (H.coeff β) *
                (PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z))) := by
    funext z
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [map_sum, mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hrewrite]
  refine MeasureTheory.integrable_finsetSum _ ?_
  intro α hα
  refine MeasureTheory.integrable_finsetSum _ ?_
  intro β hβ
  simpa [mul_assoc] using
    (integrable_productBasis_cross κ α β).const_mul (G.coeff α * conj (H.coeff β))

/-- Product basis orthonormality at fixed multi-index `κ`. -/
theorem productBasisOrthonormal
    {d : ℕ} (κ α β : MultiIndex d) :
    gaussianInner (PhiKappaAlpha κ α) (PhiKappaAlpha κ β) =
      if α = β then (1 : ℂ) else 0 := by
  /-
  Key scaffolding step:
  use tensor-product factorization and the imported one-variable orthonormality
  theorem coordinate by coordinate.
  -/
  have hfactor := tensorGaussianFactorization d
    (fun q z => oneDimPhi (κ q) (α q) z)
    (fun q z => oneDimPhi (κ q) (β q) z)
    (fun q => by
      simpa [oneDimLift] using
        integrable_oneDimPhi_cross_gaussian (κ q) (α q) (β q))
  have hprod :
      (∏ q : Fin d,
          gaussianInner (d := 1) (fun z : CSpace 1 => oneDimPhi (κ q) (α q) (z 0))
            (fun z : CSpace 1 => oneDimPhi (κ q) (β q) (z 0))) =
        if α = β then (1 : ℂ) else 0 := by
    by_cases h : α = β
    · subst h
      have hcoord :
          ∀ q : Fin d,
            gaussianInner (d := 1) (fun z : CSpace 1 => oneDimPhi (κ q) (α q) (z 0))
              (fun z : CSpace 1 => oneDimPhi (κ q) (α q) (z 0)) = 1 := fun q => by
        have hov := oneVariableBasisOrthonormal (k := κ q) (m := α q) (n := α q)
        rwa [if_pos rfl] at hov
      simp [hcoord]
    · obtain ⟨q, hq⟩ : ∃ q : Fin d, α q ≠ β q := by simpa [funext_iff] using h
      rw [if_neg h, Finset.prod_eq_zero_iff]
      refine ⟨q, Finset.mem_univ q, ?_⟩
      have hov := oneVariableBasisOrthonormal (k := κ q) (m := α q) (n := β q)
      rwa [if_neg hq] at hov
  exact hfactor.2.trans hprod

/-- The distinguished basis vector has Gaussian norm one. -/
theorem nuKappa_norm_one
    {d : ℕ} (κ : MultiIndex d) :
    gaussianL2Norm (nuKappa κ) = 1 := by
  have hinner : gaussianInner (nuKappa κ) (nuKappa κ) = 1 := by
    simpa [nuKappa] using
      (productBasisOrthonormal (κ := κ) (α := 0) (β := 0))
  have hsq : gaussianL2NormSq (nuKappa κ) = 1 :=
    Complex.ofReal_injective (by rw [← gaussianInner_self, hinner, Complex.ofReal_one])
  rw [gaussianL2Norm, hsq, Real.sqrt_one]

/-- Finite Parseval for a finite several-variable Hermite sum. -/
theorem finiteParseval
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    hermiteNormSq κ G = Finset.sum G.support fun α => ‖G.coeff α‖ ^ 2 := by
  /-
  Scaffolding guidance:
  keep the public statement on literal finite coefficient families.
  This is the version later files regroup by blocks and total degree.
  -/
  classical
  have hinner :
      gaussianInner (evalHermiteSum κ G) (evalHermiteSum κ G) =
        Finset.sum G.support fun α => G.coeff α * conj (G.coeff α) := by
    unfold evalHermiteSum
    rw [gaussianInner_finite_sum (κ := κ) (s := G.support) (t := G.support)
      (a := G.coeff) (b := G.coeff)]
    calc
      ∑ β ∈ G.support,
          conj (G.coeff β) *
            gaussianInner (fun z => ∑ α ∈ G.support, G.coeff α * PhiKappaAlpha κ α z)
              (PhiKappaAlpha κ β)
          = ∑ β ∈ G.support,
              conj (G.coeff β) *
                ∑ α ∈ G.support, G.coeff α * gaussianInner (PhiKappaAlpha κ α) (PhiKappaAlpha κ β)
                    := by
                  refine Finset.sum_congr rfl ?_
                  intro β hβ
                  rw [gaussianInner_finite_sum_basis (κ := κ) (β := β)
                    (s := G.support) (c := G.coeff)]
      _ = ∑ α ∈ G.support, G.coeff α * conj (G.coeff α) := by
            refine Finset.sum_congr rfl fun β hβ => ?_
            rw [Finset.sum_eq_single β]
            · simp [productBasisOrthonormal, mul_comm]
            · intro α hα hne
              simp [productBasisOrthonormal, hne]
            · exact fun hnotin => absurd hβ hnotin
  unfold hermiteNormSq
  apply Complex.ofReal_injective
  rw [← gaussianInner_self, hinner]
  simp [Complex.mul_conj']

/-- Coefficient extraction against the distinguished vector `ν_κ`. -/
theorem coefficientAtZero
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    hermiteInnerNu κ G = G.coeff 0 := by
  /-
  Key downstream use:
  this is the exact reason the zero degree disappears from local windows when
  the perturbation is orthogonal to `ν_κ`.
  -/
  classical
  unfold hermiteInnerNu evalHermiteSum nuKappa
  rw [gaussianInner_finite_sum_basis (κ := κ) (β := 0) (s := G.support) (c := G.coeff),
    Finset.sum_eq_single 0]
  · simp [productBasisOrthonormal]
  · intro α hα hne
    simp [productBasisOrthonormal, hne]
  · intro h0
    simp only [FiniteHermiteSum.support, Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at h0
    rw [h0]
    simp

/-- Orthogonality to `ν_κ` is equivalent to vanishing zero coefficient. -/
theorem orthogonalToNu_iff_coeff_zero
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    hermiteInnerNu κ G = 0 ↔ G.coeff 0 = 0 := by simp [coefficientAtZero (κ := κ) (G := G)]

private lemma oneDimPhi_phaseLaw
    (k n : ℕ) (t : ℝ) (z : ℂ) :
    oneDimPhi k n (Complex.exp (Complex.I * t) * z) =
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) * oneDimPhi k n z := by
  obtain ⟨radial, hradial⟩ := oneVariableAngularFactorization k n
  have hz : ((‖z‖ : ℂ) * Complex.exp (Complex.I * z.arg)) = z := by
    simp [mul_comm Complex.I (z.arg : ℂ)]
  have hrot :
      Complex.exp (Complex.I * t) * z =
        ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by
    rw [mul_add, Complex.exp_add]
    conv_lhs => rw [← hz]
    ring
  have hleft :
      oneDimPhi k n ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by simpa using hradial ‖z‖ (t + z.arg)
  have hright :
      oneDimPhi k n z =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by simpa [hz] using hradial ‖z‖ z.arg
  have hexp :
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
          Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hrot, hleft, hexp, hright]
  ring

/-- Global phase law on the product basis. -/
theorem productBasisPhaseLaw
    {d : ℕ} (κ α : MultiIndex d) (t : ℝ) (z : CSpace d) :
    PhiKappaAlpha κ α (fun q => Complex.exp (Complex.I * t) * z q) =
      Complex.exp (Complex.I * (((totalDegree α : ℤ) - (totalDegree κ : ℤ) : ℂ) * t)) *
        PhiKappaAlpha κ α z := by
  /-
  Scaffolding guidance:
  later files use only the induced phase law by total degree, so expose that
  form directly here.
  -/
  unfold PhiKappaAlpha
  simp_rw [oneDimPhi_phaseLaw]
  rw [Finset.prod_mul_distrib]
  have haux :
      (∏ q, Complex.exp (Complex.I * (((α q : ℤ) - (κ q : ℤ) : ℂ) * t))) =
        Complex.exp (Complex.I * ((↑↑(∑ q, α q) - ↑↑(∑ q, κ q)) * ↑t)) := by
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih,
          ← Complex.exp_add]
        congr 1
        push_cast
        ring
  simpa [totalDegree, mul_assoc] using
    congrArg (fun c : ℂ => c * ∏ q, oneDimPhi (κ q) (α q) (z q)) haux

/-- The same phase law for a fixed total-degree piece. -/
theorem totalDegreePiecePhaseLaw
    {d : ℕ} (κ : MultiIndex d) (n : ℕ) (G : FiniteHermiteSum d) (t : ℝ) (z : CSpace d) :
    evalHermiteSum κ (totalDegreePiece n G) (fun q => Complex.exp (Complex.I * t) * z q) =
      Complex.exp (Complex.I * (((n : ℤ) - (totalDegree κ : ℤ) : ℂ) * t)) *
        evalHermiteSum κ (totalDegreePiece n G) z := by
  unfold evalHermiteSum totalDegreePiece
  simp_rw [Finsupp.onFinset_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro α hα
  by_cases hdeg : totalDegree α = n
  · rw [if_pos hdeg, productBasisPhaseLaw]
    simp [hdeg, mul_assoc, mul_left_comm, mul_comm]
  · simp [hdeg]

/-- Partition of the Gaussian norm by product annuli. -/
theorem partitionOfGaussianNorm
    {d : ℕ} (F : CSpace d → ℂ)
    (hF : Integrable (fun z : CSpace d => ‖F z‖ ^ 2) (gaussianMeasure d)) :
    gaussianL2NormSq F = ∑' j : MultiIndex d, annulusMass j F := by
  /-
  Scaffolding guidance:
  later files only need the partition formula, not an explicit derivation.
  Keep it annulus-facing and do not force downstream code to reopen Tonelli.
  -/
  have hmeas : ∀ j : MultiIndex d, MeasurableSet (productAnnulus j) := measurableSet_productAnnulus
  have hdisj : Pairwise (fun j k : MultiIndex d => Disjoint (productAnnulus j) (productAnnulus k))
      := by
    intro j k hjk
    rw [Set.disjoint_iff]
    intro z hz
    exact hjk (productAnnulus_eq_of_mem hz.1 hz.2)
  have hcover : (⋃ j : MultiIndex d, productAnnulus j) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨fun q => Nat.floor ‖z q‖, fun q => ⟨?_, ?_⟩⟩
    · exact_mod_cast Nat.floor_le (show 0 ≤ ‖z q‖ by positivity)
    · exact_mod_cast Nat.lt_floor_add_one ‖z q‖
  have hfi :
      IntegrableOn (fun z : CSpace d => ‖F z‖ ^ 2)
        (⋃ j : MultiIndex d, productAnnulus j) (gaussianMeasure d) := by simpa [hcover] using hF
  calc
    gaussianL2NormSq F
        = ∫ z in ⋃ j : MultiIndex d, productAnnulus j, ‖F z‖ ^ 2 ∂ gaussianMeasure d := by
            simp [gaussianL2NormSq, hcover]
    _ = ∑' j : MultiIndex d, ∫ z in productAnnulus j, ‖F z‖ ^ 2 ∂ gaussianMeasure d := by
          simpa [hcover] using
            MeasureTheory.integral_iUnion
              (f := fun z : CSpace d => ‖F z‖ ^ 2) hmeas hdisj hfi
    _ = ∑' j : MultiIndex d, annulusMass j F := by
          congr with j
          simpa [annulusMass, Set.indicator] using
            (MeasureTheory.integral_indicator
              (μ := gaussianMeasure d)
              (f := fun z : CSpace d => ‖F z‖ ^ 2)
              (hs := hmeas j)).symm

/-- Finite-Hermite annulus integrability wrapper on a fixed annulus. -/
theorem annulusIntegrablePolynomial
    {d : ℕ} (j κ : MultiIndex d) (G H : FiniteHermiteSum d) :
    Integrable
      (indicatorMul (productAnnulus j)
        (fun z => evalHermiteSum κ G z * conj (evalHermiteSum κ H z)))
      (gaussianMeasure d) := by
  refine ((integrable_evalHermiteSum_cross κ G H).indicator
    (measurableSet_productAnnulus j)).congr ?_
  filter_upwards with z
  rfl

private theorem annulusInner_self
    {d : ℕ} (j : MultiIndex d) (F : CSpace d → ℂ) :
    annulusInner j F F = ((annulusMass j F : ℝ) : ℂ) := by
  classical
  unfold annulusInner annulusMass
  have hfun :
      (fun z : CSpace d => if z ∈ productAnnulus j then F z * conj (F z) else 0) =
        fun z : CSpace d => ((if z ∈ productAnnulus j then ‖F z‖ ^ 2 else 0 : ℝ) : ℂ) := by
    funext z
    split_ifs with hz <;> simp [Complex.mul_conj']
  rw [hfun, integral_complex_ofReal]

private lemma annulusInner_finite_sum_basis
    {d : ℕ} (j κ β : MultiIndex d)
    (s : Finset (MultiIndex d)) (c : MultiIndex d → ℂ) :
    annulusInner j (fun z => Finset.sum s (fun α => c α * PhiKappaAlpha κ α z)) (PhiKappaAlpha κ
        β) =
      Finset.sum s (fun α => c α * annulusInner j (PhiKappaAlpha κ α) (PhiKappaAlpha κ β)) := by
  classical
  unfold annulusInner
  change
    ∫ z : CSpace d,
      if z ∈ productAnnulus j then
        (∑ α ∈ s, c α * PhiKappaAlpha κ α z) * conj (PhiKappaAlpha κ β z)
      else 0 ∂ gaussianMeasure d =
      Finset.sum s (fun α =>
        c α * ∫ z : CSpace d,
          if z ∈ productAnnulus j then
            PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z)
          else 0 ∂ gaussianMeasure d)
  have hsum :
      (fun z : CSpace d =>
        if z ∈ productAnnulus j then
          (∑ α ∈ s, c α * PhiKappaAlpha κ α z) * conj (PhiKappaAlpha κ β z)
        else 0) =
        (fun z : CSpace d =>
          Finset.sum s (fun α =>
            if z ∈ productAnnulus j then
              c α * (PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z))
            else 0)) := by
    funext z
    by_cases hz : z ∈ productAnnulus j
    · rw [if_pos hz, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro α hα
      simp [hz, mul_assoc]
    · simp [hz]
  rw [hsum, MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ productAnnulus j <;> simp [hz]
  · intro α hα
    simpa [indicatorMul, Set.indicator, mul_assoc] using
      ((integrable_productBasis_cross κ α β).indicator (measurableSet_productAnnulus j)).const_mul
        (c α)

private lemma annulusInner_finite_sum
    {d : ℕ} (j κ : MultiIndex d)
    (s t : Finset (MultiIndex d))
    (a b : MultiIndex d → ℂ) :
    annulusInner j
        (fun z => Finset.sum s (fun α => a α * PhiKappaAlpha κ α z))
        (fun z => Finset.sum t (fun β => b β * PhiKappaAlpha κ β z)) =
      Finset.sum t (fun β =>
        conj (b β) *
          annulusInner j
            (fun z => Finset.sum s (fun α => a α * PhiKappaAlpha κ α z))
            (PhiKappaAlpha κ β)) := by
  classical
  unfold annulusInner
  change
    ∫ z : CSpace d,
      if z ∈ productAnnulus j then
        (∑ α ∈ s, a α * PhiKappaAlpha κ α z) *
          conj (∑ β ∈ t, b β * PhiKappaAlpha κ β z)
      else 0 ∂ gaussianMeasure d =
      Finset.sum t (fun β =>
        conj (b β) *
          ∫ z : CSpace d,
            if z ∈ productAnnulus j then
              (∑ α ∈ s, a α * PhiKappaAlpha κ α z) *
                conj (PhiKappaAlpha κ β z)
            else 0 ∂ gaussianMeasure d)
  have hrewrite :
      (fun z : CSpace d =>
        (if z ∈ productAnnulus j then
          (∑ α ∈ s, a α * PhiKappaAlpha κ α z) *
            conj (∑ β ∈ t, b β * PhiKappaAlpha κ β z)
        else 0)) =
        (fun z : CSpace d =>
          Finset.sum t fun β =>
            if z ∈ productAnnulus j then
              conj (b β) *
                ((Finset.sum s fun α => a α * PhiKappaAlpha κ α z) *
                  conj (PhiKappaAlpha κ β z))
            else 0) := by
    funext z
    by_cases hz : z ∈ productAnnulus j
    · rw [if_pos hz, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      simp [hz, mul_assoc, mul_comm]
    · simp [hz]
  rw [hrewrite, MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ productAnnulus j <;> simp [hz]
  · intro β hβ
    have hsum :
        (fun z : CSpace d =>
          if z ∈ productAnnulus j then
            conj (b β) *
              ((Finset.sum s fun α => a α * PhiKappaAlpha κ α z) *
                conj (PhiKappaAlpha κ β z))
          else 0) =
          (fun z : CSpace d =>
            Finset.sum s fun α =>
              if z ∈ productAnnulus j then
                (conj (b β) * a α) *
                  (PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z))
              else 0) := by
      funext z
      by_cases hz : z ∈ productAnnulus j
      · simp [hz, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      · simp [hz]
    rw [hsum]
    refine MeasureTheory.integrable_finsetSum _ ?_
    intro α hα
    convert
      (((integrable_productBasis_cross κ α β).indicator (measurableSet_productAnnulus j)).const_mul
        (conj (b β) * a α)) using 1
    case e'_3 => rfl
    funext z
    by_cases hz : z ∈ productAnnulus j
    · simp [Set.indicator, hz, mul_left_comm, mul_comm]
    · simp [Set.indicator, hz]

/-- Rotation preserves a product annulus. -/
theorem annulusRotationInvariant
    {d : ℕ} (j : MultiIndex d) (t : ℝ) (z : CSpace d) :
    z ∈ productAnnulus j ↔
      (fun q => Complex.exp (Complex.I * t) * z q) ∈ productAnnulus j := by
  have hnorm : ‖Complex.exp (Complex.I * t)‖ = 1 := by simp []
  simp [productAnnulus, hnorm]

private def mulCircleLIE (ω : _root_.Circle) : ℂ ≃ₗᵢ[ℝ] ℂ := by
  refine LinearIsometryEquiv.mk
    (LinearEquiv.ofBijective
      (LinearMap.mulLeft ℝ ((ω : ℂ)))
      ?_)
    ?_
  · refine ⟨?inj, ?surj⟩
    · intro x y hxy
      exact mul_left_cancel₀ (Circle.coe_ne_zero ω) (by simpa using hxy)
    · intro z
      refine ⟨((ω⁻¹ : _root_.Circle) : ℂ) * z, ?_⟩
      simp []
  · intro z
    simp []

/-- A measure-preserving (for volume), measurable-embedding, density-preserving map
preserves the Gaussian measure. -/
private lemma gaussianMeasure_map_eq_of_density
    {d : ℕ} {f : CSpace d → CSpace d}
    (hvol : MeasurePreserving f (volume : Measure (CSpace d)) (volume : Measure (CSpace d)))
    (hmeas : MeasurableEmbedding f)
    (hdens : ∀ z : CSpace d,
      ENNReal.ofReal (gaussianDensity d (f z)) = ENNReal.ofReal (gaussianDensity d z)) :
    Measure.map f (gaussianMeasure d) = gaussianMeasure d := by
  classical
  let dens : CSpace d → ENNReal := fun z => ENNReal.ofReal (gaussianDensity d z)
  change Measure.map f (volume.withDensity dens) = volume.withDensity dens
  ext s hs
  have hs' : MeasurableSet (f ⁻¹' s) := measurableSet_preimage hmeas.measurable hs
  rw [Measure.map_apply_of_aemeasurable hmeas.measurable.aemeasurable hs,
    withDensity_apply _ hs', withDensity_apply _ hs]
  rw [← MeasureTheory.lintegral_indicator (hs := hs'),
    ← MeasureTheory.lintegral_indicator (hs := hs)]
  simpa [Set.preimage, Set.indicator, Set.mem_setOf_eq, dens, hdens] using
    (hvol.lintegral_comp_emb hmeas (fun x => if x ∈ s then dens x else 0))

private lemma gaussian_lintegral_rotate_eq
    {d : ℕ} (ω : _root_.Circle) (g : CSpace d → ENNReal) :
    ∫⁻ z : CSpace d, g (fun q => (ω : ℂ) * z q) ∂ gaussianMeasure d =
      ∫⁻ z : CSpace d, g z ∂ gaussianMeasure d := by
  classical
  let f : CSpace d → CSpace d := fun z q => (ω : ℂ) * z q
  have hvol : MeasurePreserving f (volume : Measure (CSpace d)) (volume : Measure (CSpace d)) :=
    MeasureTheory.volume_preserving_pi (f := fun _ : Fin d => mulCircleLIE ω)
      (fun _ => (mulCircleLIE ω).measurePreserving)
  have hmeas : MeasurableEmbedding f := by
    let inv : CSpace d → CSpace d := fun z q => (((ω⁻¹ : _root_.Circle) : ℂ) * z q)
    have hinv : Function.LeftInverse inv f := by
      intro z
      funext q
      simp [f, inv]
    have hcont : Continuous f := by fun_prop
    exact hcont.measurableEmbedding hinv.injective
  have hdens : ∀ z : CSpace d,
      ENNReal.ofReal (gaussianDensity d (f z)) = ENNReal.ofReal (gaussianDensity d z) := by
    intro z
    simp [f, gaussianDensity]
  have hgauss : MeasurePreserving f (gaussianMeasure d) (gaussianMeasure d) :=
    ⟨hmeas.measurable, gaussianMeasure_map_eq_of_density hvol hmeas hdens⟩
  simpa [f] using hgauss.lintegral_comp_emb hmeas g

private lemma fourier_mk_eq_exp
    (n : ℤ) (θ : ℝ) :
    (fourier n (QuotientAddGroup.mk θ : Circle) : ℂ) =
      Complex.exp (Complex.I * (n : ℂ) * θ) := by
  rw [fourier_coe_apply]
  congr 1
  simp only [T, HermiteLEAN.T]
  push_cast
  field_simp

private lemma annulusRotationInvariantCircle
    {d : ℕ} (j : MultiIndex d) (t : Circle) (z : CSpace d) :
    z ∈ productAnnulus j ↔
      (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q) ∈ productAnnulus j := by
  induction t using Quotient.inductionOn with
  | h θ =>
      rw [fourier_mk_eq_exp]
      simpa using (annulusRotationInvariant (j := j) (t := θ) (z := z))

/-- Rotating a single coordinate preserves product annuli. -/
private lemma productAnnulus_rotate_one_iff
    {d : ℕ} (j : MultiIndex d) (q0 : Fin d) (ω : _root_.Circle) (z : CSpace d) :
    Function.update z q0 ((ω : ℂ) * z q0) ∈ productAnnulus j ↔ z ∈ productAnnulus j := by
  have hω : ‖(ω : ℂ)‖ = 1 := _root_.Circle.norm_coe ω
  constructor <;> intro hz <;> intro q
  · by_cases hq : q = q0
    · subst hq
      simpa [productAnnulus, Function.update, Complex.norm_mul, hω] using hz q
    · simpa [productAnnulus, Function.update, hq] using hz q
  · by_cases hq : q = q0
    · subst hq
      simpa [productAnnulus, Function.update, Complex.norm_mul, hω] using hz q
    · simpa [productAnnulus, Function.update, hq] using hz q

/-- Rotating one coordinate preserves volume. -/
private lemma rotate_one_volume_preserving
    {d : ℕ} (q0 : Fin d) (ω : _root_.Circle) :
    MeasurePreserving
      (fun z : CSpace d => Function.update z q0 ((ω : ℂ) * z q0))
      (volume : Measure (CSpace d)) (volume : Measure (CSpace d)) := by
  classical
  let f : Fin d → ℂ → ℂ := fun i => if h : i = q0 then fun z => (ω : ℂ) * z else id
  have hf : ∀ i : Fin d, MeasurePreserving (f i) (volume : Measure ℂ) (volume : Measure ℂ) := by
    intro i
    by_cases h : i = q0
    · subst h
      have hfeq : ⇑(mulCircleLIE ω) = f i := by
        funext z
        simp only [f, dite_true]
        rfl
      rw [← hfeq]
      exact (mulCircleLIE ω).measurePreserving
    · simpa [f, h] using
        (show MeasurePreserving (id : ℂ → ℂ) (volume : Measure ℂ) (volume : Measure ℂ) from
          ⟨measurable_id, by simp⟩)
  have hpi :
      MeasurePreserving
        (fun z : CSpace d => fun i => f i (z i))
        (volume : Measure (CSpace d)) (volume : Measure (CSpace d)) := by
    simpa [MeasureTheory.Measure.pi, f] using
      (MeasureTheory.volume_preserving_pi (f := f) hf)
  have hfun :
      (fun z : CSpace d => fun i => f i (z i)) =
        fun z => Function.update z q0 ((ω : ℂ) * z q0) := by
    funext z i
    by_cases h : i = q0
    · subst h
      simp [f]
    · simp [f, h]
  simpa [hfun] using hpi

/-- Rotating one coordinate is a measurable embedding. -/
private lemma rotate_one_measurableEmbedding
    {d : ℕ} (q0 : Fin d) (ω : _root_.Circle) :
    MeasurableEmbedding (fun z : CSpace d => Function.update z q0 ((ω : ℂ) * z q0)) := by
  classical
  let f : CSpace d → CSpace d := fun z => Function.update z q0 ((ω : ℂ) * z q0)
  let g : CSpace d → CSpace d := fun z => Function.update z q0 (((ω⁻¹ : _root_.Circle) : ℂ) * z q0)
  have hf : Measurable f := by fun_prop
  have hcont : Continuous f := by fun_prop
  have hgf : Function.LeftInverse g f := by
    intro z
    funext q
    by_cases hq : q = q0
    · subst hq
      simp [f, g, Function.update]
    · simp [f, g, Function.update, hq]
  have hrange : MeasurableSet (Set.range f) :=
    MeasureTheory.measurableSet_range_of_continuous_injective hcont hgf.injective
  exact MeasurableEmbedding.of_measurable_inverse hf hrange (by fun_prop) hgf

/-- Rotating one coordinate by a phase preserves the Gaussian measure. -/
private lemma rotate_one_gaussian_preserving
    {d : ℕ} (q0 : Fin d) (ω : _root_.Circle) :
    MeasurePreserving
      (fun z : CSpace d => Function.update z q0 ((ω : ℂ) * z q0))
      (gaussianMeasure d) (gaussianMeasure d) := by
  classical
  let f : CSpace d → CSpace d := fun z => Function.update z q0 ((ω : ℂ) * z q0)
  have hvol : MeasurePreserving f (volume : Measure (CSpace d)) (volume : Measure (CSpace d)) := by
    simpa [f] using (rotate_one_volume_preserving (q0 := q0) (ω := ω))
  have hmeas : MeasurableEmbedding f := rotate_one_measurableEmbedding (q0 := q0) (ω := ω)
  have hdens : ∀ z : CSpace d,
      ENNReal.ofReal (gaussianDensity d (f z)) = ENNReal.ofReal (gaussianDensity d z) := by
    intro z
    have hsum :
        ∑ q : Fin d, ‖Function.update z q0 ((ω : ℂ) * z q0) q‖ ^ 2 =
          ∑ q : Fin d, ‖z q‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      by_cases h : q = q0
      · subst h
        simp [Function.update]
      · simp [Function.update, h]
    simp [f, gaussianDensity, hsum]
  exact ⟨hmeas.measurable, gaussianMeasure_map_eq_of_density hvol hmeas hdens⟩

/-- Rotating one coordinate contributes exactly the corresponding phase factor. -/
private lemma PhiKappaAlpha_rotate_one
    {d : ℕ} (κ α : MultiIndex d) (q0 : Fin d) (t : ℝ) (z : CSpace d) :
    PhiKappaAlpha κ α (Function.update z q0 (Complex.exp (Complex.I * t) * z q0)) =
      Complex.exp (Complex.I * (((α q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t)) * PhiKappaAlpha κ α z := by
  classical
  unfold PhiKappaAlpha
  have hupdate :
      (fun q : Fin d =>
        oneDimPhi (κ q) (α q) (Function.update z q0 (Complex.exp (Complex.I * t) * z q0) q)) =
        Function.update
          (fun q : Fin d => oneDimPhi (κ q) (α q) (z q))
          q0
          (oneDimPhi (κ q0) (α q0) (Complex.exp (Complex.I * t) * z q0)) := by
    funext q
    by_cases hq : q = q0
    · subst hq
      simp
    · simp [Function.update, hq]
  rw [hupdate, Finset.prod_update_of_mem (s := Finset.univ) (i := q0) (by simp), oneDimPhi_phaseLaw]
  conv_rhs => rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (s := Finset.univ) (i := q0) (by
      simp)]
  ring

/-- Rotation averaging on a product annulus for nonnegative measurable functions. -/
theorem annulusRotationAveraging
    {d : ℕ} (j : MultiIndex d) (F : CSpace d → ENNReal) (hF : Measurable F) :
    by
      classical
      exact
        ∫⁻ z : CSpace d,
            if _h : z ∈ productAnnulus j then
              ∫⁻ t : Hermite1DimdLEAN.Circle,
                  F (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q)
                    ∂ AddCircle.haarAddCircle
            else 0
          ∂ gaussianMeasure d
          =
        ∫⁻ z : CSpace d, if _h : z ∈ productAnnulus j then F z else 0 ∂ gaussianMeasure d := by
  classical
  let G : CSpace d → ENNReal := fun z => if z ∈ productAnnulus j then F z else 0
  have hG : Measurable G := hF.piecewise (measurableSet_productAnnulus j) measurable_const
  letI : MeasureTheory.SFinite (gaussianMeasure d) := by
    change MeasureTheory.SFinite
      ((volume : Measure (CSpace d)).withDensity (fun z => ENNReal.ofReal (gaussianDensity d z)))
    infer_instance
  calc
    ∫⁻ z : CSpace d,
        if h : z ∈ productAnnulus j then
          ∫⁻ t : Hermite1DimdLEAN.Circle,
              F (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q)
                ∂ AddCircle.haarAddCircle
        else 0
      ∂ gaussianMeasure d
      = ∫⁻ z : CSpace d,
          ∫⁻ t : Hermite1DimdLEAN.Circle,
              G (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q)
                ∂ AddCircle.haarAddCircle
          ∂ gaussianMeasure d := by
            refine lintegral_congr_ae ?_
            filter_upwards with z
            by_cases hz : z ∈ productAnnulus j
            · simp only [hz, ↓reduceDIte, fourier_apply, one_smul]
              refine lintegral_congr_ae ?_
              filter_upwards with t
              have hrot :
                  (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q) ∈
                    productAnnulus j :=
                (annulusRotationInvariantCircle (j := j) (t := t) (z := z)).mp hz
              have hrot' :
                  (fun q => ((AddCircle.toCircle t : _root_.Circle) : ℂ) * z q) ∈
                    productAnnulus j := by simpa [fourier_one] using hrot
              simp only [G]
              split_ifs with hmem
              · rfl
              · exact (hmem hrot').elim
            · have hzero :
                ∫⁻ t : Hermite1DimdLEAN.Circle,
                    G (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q)
                  ∂ AddCircle.haarAddCircle = 0 := by
                    refine lintegral_eq_zero_of_ae_eq_zero ?_
                    filter_upwards with t
                    have hrot :
                        (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q) ∉
                          productAnnulus j := fun hz' =>
                      hz ((annulusRotationInvariantCircle (j := j) (t := t) (z := z)).mpr hz')
                    simp only [G, Pi.zero_apply]
                    split_ifs with hmem
                    · exact (hrot hmem).elim
                    · rfl
              have hzero' :
                  ∫⁻ t : Hermite1DimdLEAN.Circle,
                      G (fun q => ((AddCircle.toCircle t : _root_.Circle) : ℂ) * z q)
                    ∂ AddCircle.haarAddCircle = 0 := by simpa [fourier_one] using hzero
              simpa [hz, fourier_one] using hzero'.symm
    _ = ∫⁻ t : Hermite1DimdLEAN.Circle,
          ∫⁻ z : CSpace d,
              G (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q)
            ∂ gaussianMeasure d
        ∂ AddCircle.haarAddCircle := by
          rw [MeasureTheory.lintegral_lintegral_swap]
          · have hpair :
                Measurable (fun p : CSpace d × Hermite1DimdLEAN.Circle =>
                  G (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) p.2 : ℂ) * p.1 q)) := by
                  refine hG.comp ?_
                  fun_prop
            exact hpair.aemeasurable
    _ = ∫⁻ t : Hermite1DimdLEAN.Circle,
          ∫⁻ z : CSpace d, G z ∂ gaussianMeasure d
        ∂ AddCircle.haarAddCircle := by
          refine lintegral_congr_ae ?_
          filter_upwards with t
          simpa [fourier_one] using
            (gaussian_lintegral_rotate_eq (ω := AddCircle.toCircle t) (g := G))
    _ = ∫⁻ z : CSpace d, G z ∂ gaussianMeasure d := by
          rw [lintegral_const]
          simp []
    _ = ∫⁻ z : CSpace d, if h : z ∈ productAnnulus j then F z else 0 ∂ gaussianMeasure d := by rfl

/-- Annulus orthogonality of distinct basis vectors. -/
theorem annulusOrthogonality
    {d : ℕ} (κ j α β : MultiIndex d) (hαβ : α ≠ β) :
    annulusInner j (PhiKappaAlpha κ α) (PhiKappaAlpha κ β) = 0 := by
  classical
  obtain ⟨q0, hq0⟩ : ∃ q0 : Fin d, α q0 ≠ β q0 := by simpa [funext_iff] using hαβ
  let n : ℤ := (α q0 : ℤ) - (β q0 : ℤ)
  have hn : n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hq0)
  let t : ℝ := Real.pi / (n : ℝ)
  let ω : _root_.Circle := _root_.Circle.exp t
  let rot : CSpace d → CSpace d :=
    fun z => Function.update z q0 ((ω : ℂ) * z q0)
  let H : CSpace d → ℂ := fun z =>
    if z ∈ productAnnulus j then
      PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z)
    else 0
  have hω : (ω : ℂ) = Complex.exp (Complex.I * t) := by simp [ω, _root_.Circle.coe_exp, mul_comm]
  have hpres :
      MeasurePreserving rot (gaussianMeasure d) (gaussianMeasure d) := by
    simpa [rot, hω] using rotate_one_gaussian_preserving (q0 := q0) (ω := ω)
  have hmeas : MeasurableEmbedding rot := by
    simpa [rot, hω] using rotate_one_measurableEmbedding (q0 := q0) (ω := ω)
  have hcomp :
      ∫ z : CSpace d, H (rot z) ∂ gaussianMeasure d
        = ∫ z : CSpace d, H z ∂ gaussianMeasure d := by
    simpa [rot] using (MeasurePreserving.integral_comp hpres hmeas H)
  have hneg_point : ∀ z : CSpace d, H (rot z) = - H z := by
    intro z
    by_cases hz : z ∈ productAnnulus j
    · have hzrot : rot z ∈ productAnnulus j := by
        simpa [rot, hω] using
          (productAnnulus_rotate_one_iff (j := j) (q0 := q0) (ω := ω) (z := z)).2 hz
      have hαrot :=
        PhiKappaAlpha_rotate_one (κ := κ) (α := α) (q0 := q0) (t := t) (z := z)
      have hβrot :=
        PhiKappaAlpha_rotate_one (κ := κ) (α := β) (q0 := q0) (t := t) (z := z)
      have hrot_eq : rot z = Function.update z q0 (Complex.exp (Complex.I * t) * z q0) := by
        simp [rot, hω]
      simp only [hzrot, ↓reduceIte, hz, H]
      rw [hrot_eq, hαrot, hβrot]
      have hconj :
          conj (Complex.exp (Complex.I * ((((β q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t)))) =
            Complex.exp (-Complex.I * ((((β q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t))) := by
        rw [← Complex.exp_conj]
        simp [mul_comm]
      rw [map_mul, hconj]
      have hphase :
          Complex.exp (Complex.I * ((((α q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t))) *
              Complex.exp (-Complex.I * ((((β q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t))) =
            (-1 : ℂ) := by
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        have hnt : ((n : ℂ) * t) = (Real.pi : ℂ) := by
          have hntR : (n : ℝ) * (Real.pi / (n : ℝ)) = Real.pi := by field_simp [hnR]
          simpa [t] using congrArg Complex.ofReal hntR
        have hntI : Complex.I * ((n : ℂ) * t) = (Real.pi : ℂ) * Complex.I := by
          simpa [mul_comm] using congrArg (fun x : ℂ => Complex.I * x) hnt
        have hexpsum :
            Complex.I * ((((α q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t)) +
                -Complex.I * ((((β q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t)) =
              Complex.I * ((n : ℂ) * t) := by
          simp only [n]
          push_cast
          ring
        rw [← Complex.exp_add, hexpsum, hntI]
        simpa [mul_comm] using Complex.exp_pi_mul_I
      have hneg_core :
          Complex.exp (Complex.I * ((((α q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t))) * PhiKappaAlpha κ α z *
              (Complex.exp (-Complex.I * ((((β q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t))) *
                conj (PhiKappaAlpha κ β z)) =
            -(PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z)) := by
        linear_combination (PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z)) * hphase
      simpa [H, hz] using hneg_core
    · have hzrot : rot z ∉ productAnnulus j := by
        intro hzrot
        exact hz <|
          (productAnnulus_rotate_one_iff (j := j) (q0 := q0) (ω := ω) (z := z)).1
            (by simpa [rot, hω] using hzrot)
      simp [H, hz, hzrot]
  have hneg_int :
      ∫ z : CSpace d, H (rot z) ∂ gaussianMeasure d
        = - ∫ z : CSpace d, H z ∂ gaussianMeasure d := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hneg_point),
      MeasureTheory.integral_neg]
  have hzero_int : ∫ z : CSpace d, H z ∂ gaussianMeasure d = 0 :=
    CharZero.eq_neg_self_iff.mp (hcomp.symm.trans hneg_int)
  simpa [annulusInner, H] using hzero_int

/-- Annulus Parseval for finite Hermite sums. -/
theorem annulusParseval
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (G : FiniteHermiteSum d) :
    annulusMass j (evalHermiteSum κ G) =
      Finset.sum G.support fun α => ‖G.coeff α‖ ^ 2 * annulusMass j (PhiKappaAlpha κ α) := by
  classical
  have hinner :
      annulusInner j (evalHermiteSum κ G) (evalHermiteSum κ G) =
        Finset.sum G.support
          (fun α => G.coeff α * conj (G.coeff α) * ((annulusMass j (PhiKappaAlpha κ α) : ℝ) : ℂ))
              := by
    unfold evalHermiteSum
    rw [annulusInner_finite_sum (j := j) (κ := κ) (s := G.support) (t := G.support)
      (a := G.coeff) (b := G.coeff)]
    calc
      ∑ β ∈ G.support,
          conj (G.coeff β) *
            annulusInner j (fun z => ∑ α ∈ G.support, G.coeff α * PhiKappaAlpha κ α z)
              (PhiKappaAlpha κ β)
          = ∑ β ∈ G.support,
              conj (G.coeff β) *
                ∑ α ∈ G.support, G.coeff α * annulusInner j (PhiKappaAlpha κ α) (PhiKappaAlpha κ
                    β) := by
                  refine Finset.sum_congr rfl ?_
                  intro β hβ
                  rw [annulusInner_finite_sum_basis (j := j) (κ := κ) (β := β)
                    (s := G.support) (c := G.coeff)]
      _ = ∑ α ∈ G.support,
            G.coeff α * conj (G.coeff α) * ((annulusMass j (PhiKappaAlpha κ α) : ℝ) : ℂ) := by
              refine Finset.sum_congr rfl fun β hβ => ?_
              rw [Finset.sum_eq_single β]
              · simp [annulusInner_self, mul_comm, mul_left_comm]
              · intro α hα hne
                simp [annulusOrthogonality, hne]
              · exact fun hnotin => absurd hβ hnotin
  apply Complex.ofReal_injective
  rw [← annulusInner_self, hinner]
  simp [Complex.mul_conj', mul_comm]

end Hermite1DimdLEAN
