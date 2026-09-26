/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.LinearTerms

/-! # Bridge -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# ProductBridge

Generic cutoff-product bridge bounds.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Direct cutoff-product duality bound in the manuscript `s,t` form, through
Ch01's legacy disjoint-Besov compatibility lane.

This is the deterministic source for the final Cauchy product: the positive
side is Ch01's cutoff-product theorem for
`(u - (u)_Q) ∇φ`, and the negative side is the scaled `t`-weak norm of the
flux with the exponent comparison `t ≤ 1 - s`. -/
theorem abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {s t : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (hst : s + t ≤ 1)
    (flux : Vec d → Vec d) (u : H1Function (openCubeSet Q))
    (ξ : Vec d → Vec d) {B gradWeak fluxWeak : ℝ}
    (hB : 0 ≤ B)
    (hξLp : MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hflux : MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgradWeak :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N u.grad ≤ gradWeak)
    (hfluxWeak :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q t N flux ≤ fluxWeak) :
    let scaledGrad := cubeBesovScaleWeight (-s) Q * gradWeak
    let scaledFlux := cubeBesovScaleWeight (-t) Q * fluxWeak
    let gradCoeff :=
      (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
        ((Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (Fintype.card (Fin d) : ℝ))
    let fluxCoeff :=
      (Fintype.card (Fin d) : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + (1 - s)) *
          cubeBesovScaleWeight (-(1 - s - t)) Q)
    |cubeAverage Q
        (fun x => vecDot (flux x)
          (((u x - cubeAverage Q (fun y => u y)) • ξ x : Vec d)))| ≤
      (gradCoeff * fluxCoeff) * (scaledGrad * scaledFlux) := by
  intro scaledGrad scaledFlux gradCoeff fluxCoeff
  let r : ℝ := 1 - s
  let productField : Vec d → Vec d :=
    fun x => ((u x - cubeAverage Q (fun y => u y)) • ξ x : Vec d)
  let productBound : ℝ := gradCoeff * scaledGrad
  have hr_pos : 0 < r := by dsimp [r]; linarith
  have hr_lt_one : r < 1 := by dsimp [r]; linarith
  have ht_le_r : t ≤ r := by dsimp [r]; linarith
  have hgradWeak_nonneg : 0 ≤ gradWeak :=
    (cubeBesovNegativeVectorPartialSeminorm_nonneg Q s 0 u.grad).trans (hgradWeak 0)
  have hfluxWeak_nonneg : 0 ≤ fluxWeak :=
    (cubeBesovNegativeVectorPartialSeminorm_nonneg Q t 0 flux).trans (hfluxWeak 0)
  have hscaledGrad_nonneg : 0 ≤ scaledGrad := by
    dsimp [scaledGrad]
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) hgradWeak_nonneg
  have hscaledFlux_nonneg : 0 ≤ scaledFlux := by
    dsimp [scaledFlux]
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-t) Q) hfluxWeak_nonneg
  have hfront_nonneg : 0 ≤ 2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (cubeScaleFactor_nonneg Q)) hB)
      (mul_nonneg (by norm_num) (cubeLpNorm_nonneg Q ∞ ξ))
  have hpoincare_nonneg :
      0 ≤ Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1) := by
    exact mul_nonneg (Ch01.Legacy.fullVectorPoincareConstant_nonneg Q)
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hgradCoeff_nonneg : 0 ≤ gradCoeff := by
    dsimp [gradCoeff]
    exact mul_nonneg hfront_nonneg
      (mul_nonneg hpoincare_nonneg (Nat.cast_nonneg _))
  have hproductBound_nonneg : 0 ≤ productBound := by
    dsimp [productBound]
    exact mul_nonneg hgradCoeff_nonneg hscaledGrad_nonneg
  have hgradComp :
      ∀ i : Fin d,
        cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) ≤
          scaledGrad := by
    intro i
    simpa [scaledGrad] using
      cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBound
        Q s u.grad i hgradWeak
  have hgradCircSum :
      (∑ i : Fin d,
        Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x i)) ≤
        (Fintype.card (Fin d) : ℝ) * scaledGrad := by
    calc
      _ ≤ ∑ _i : Fin d, scaledGrad :=
        Finset.sum_le_sum fun i _ => by
          simpa only [Ch01.Legacy.circNegativeBesovNorm] using hgradComp i
      _ = (Fintype.card (Fin d) : ℝ) * scaledGrad := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hproductDual :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (fun x => productField x i) ≤
          productBound := by
    have hpConj :
        cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
      simpa [cubeBesovConjExponent] using
        (ENNReal.HolderConjugate.conjExponent_eq
          (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
    have hqConj :
        cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
      simpa [cubeBesovConjExponent] using
        (ENNReal.HolderConjugate.conjExponent_eq
          (p := (1 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)))
    intro i N
    have hch01 :
        cubeBesovPartialNormTop Q r (2 : ℝ≥0∞) N (fun x => productField x i) ≤
          (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
            ((Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ∑ i : Fin d,
                Ch01.Legacy.circNegativeBesovNorm Q (1 - r) (2 : ℝ≥0∞)
                  (1 : ℝ≥0∞)
                  (fun x => u.grad x i)) := by
      simpa [productField, r, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        Ch01.Legacy.cutoffProduct_component_partialNormTop_le_gradient_rhs
          Q r N u ξ hB hξLp hξ hderiv hr_pos hr_lt_one i
    have hsum :
        (∑ i : Fin d,
          Ch01.Legacy.circNegativeBesovNorm Q (1 - r) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) ≤
          (Fintype.card (Fin d) : ℝ) * scaledGrad := by
      simpa [r] using hgradCircSum
    have hmain := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsum hpoincare_nonneg) hfront_nonneg
    have hdual :
        cubeBesovDualTestNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (fun x => productField x i) =
          cubeBesovPartialNormTop Q r (2 : ℝ≥0∞) N (fun x => productField x i) := by
      rw [cubeBesovDualTestNorm_of_conjExponent_eq_top
        Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => productField x i) hqConj]
      rw [hpConj]
    rw [hdual]
    refine hch01.trans (hmain.trans ?_)
    apply le_of_eq
    dsimp [productBound, gradCoeff]
    ring
  have hu : MemLp (fun x => u x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hfluct :
      MemLp (fun x => u x - cubeAverage Q (fun y => u y)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    hu.sub (MeasureTheory.memLp_const (cubeAverage Q (fun y => u y)))
  have hproductField :
      MemLp productField (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
    simpa [productField] using! hξLp.smul (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hfluct
  have hproductMem :
      ∀ i : Fin d,
        CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => productField x i) := by
    intro i
    exact cubeBesovDualLocalMemLpGlobal_component_of_memLp Q productField i hproductField
  have hfluxComp :
      ∀ i : Fin d,
        MemLp (fun x => flux x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp flux i hflux
  have hpair :
      |cubeAverage Q (fun x => vecDot (flux x) (productField x))| ≤
        ∑ i : Fin d,
          (((3 : ℝ) ^ ((d : ℝ) + r) *
              cubeBesovCircNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => flux x i)) *
            productBound) := by
    simpa [productField] using
      abs_cubeAverage_vecDot_le_sum_note_constant_mul_of_uniform_component_bounds_two_one_of_nonneg
        Q r flux productField (fun _ : Fin d => productBound) hr_pos hfluxComp
        (fun _ => hproductBound_nonneg) hproductDual hproductMem
  have hfluxScaledPartial :
      ∀ N : ℕ,
        cubeBesovScaleWeight (-t) Q *
            cubeBesovNegativeVectorPartialSeminorm Q t N flux ≤
          scaledFlux := by
    intro N
    dsimp [scaledFlux]
    exact mul_le_mul_of_nonneg_left (hfluxWeak N) (cubeBesovScaleWeight_nonneg (-t) Q)
  have hfluxCompCirc :
      ∀ i : Fin d,
        cubeBesovCircNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => flux x i) ≤
          cubeBesovScaleWeight (-(r - t)) Q * scaledFlux := by
    intro i
    exact
      cubeBesovCircNorm_two_one_component_le_scaleWeight_gap_mul_of_scaled_negativeVectorPartialBound
        Q ht_le_r flux i hfluxScaledPartial
  have hsum :
      (∑ i : Fin d,
          (((3 : ℝ) ^ ((d : ℝ) + r) *
              cubeBesovCircNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => flux x i)) *
            productBound)) ≤
        (gradCoeff * fluxCoeff) * (scaledGrad * scaledFlux) := by
    have hpow_nonneg : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + r) :=
      Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    have hcomponent :
        ∀ i : Fin d,
          (((3 : ℝ) ^ ((d : ℝ) + r) *
              cubeBesovCircNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => flux x i)) *
            productBound) ≤
          (((3 : ℝ) ^ ((d : ℝ) + r) *
              (cubeBesovScaleWeight (-(r - t)) Q * scaledFlux)) *
            productBound) := by
      intro i
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hfluxCompCirc i) hpow_nonneg)
        hproductBound_nonneg
    calc
      (∑ i : Fin d,
          (((3 : ℝ) ^ ((d : ℝ) + r) *
              cubeBesovCircNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => flux x i)) *
            productBound))
          ≤
        ∑ _i : Fin d,
          (((3 : ℝ) ^ ((d : ℝ) + r) *
              (cubeBesovScaleWeight (-(r - t)) Q * scaledFlux)) *
            productBound) := by
            exact Finset.sum_le_sum fun i _hi => hcomponent i
      _ =
        (gradCoeff * fluxCoeff) * (scaledGrad * scaledFlux) := by
            simp [fluxCoeff, productBound, r]
            ring
  exact hpair.trans hsum

/-- Private Section 5.3 product-term bridge.

This is the manuscript integration-by-parts product estimate in the form needed
before inserting the canonical maximizer fields: `potential` is
`v_m - ell_{p0}`, `cutoffGradient` is `grad phi`, and `flux` is
`a grad v_m - q0`.  The proof deliberately consumes the active deterministic
cutoff-product theorem directly, without recreating the archived
`HasCutoffProduct...` socket layer. -/
theorem productTerm_le_cutoffProductBridge
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (potential : Vec d → ℝ) (dualField cutoffGradient : Vec d → Vec d)
    {fluxWeakOne fluxWeakS fluxAverage cutoffCircOne cutoffCircS
      cutoffDerivative poincareConst cutoffConstant centeredCutoffConstant : ℝ}
    (hcutoffDerivative : 0 ≤ cutoffDerivative)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hflux : MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hpotential : MemLp potential (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hdualField :
      ∀ i : Fin d,
        MemLp (fun x => dualField x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hcutoffGradient : MemLp cutoffGradient ∞ (normalizedCubeMeasure Q))
    (hcutoffConstant : 0 ≤ cutoffConstant)
    (hcenteredCutoffConstant : 0 ≤ centeredCutoffConstant)
    (hfluxAverage : 0 ≤ fluxAverage)
    (hpoincareConst : 0 ≤ poincareConst)
    (hcutoffCircOne : 0 ≤ cutoffCircOne)
    (hcutoffCircS : 0 ≤ cutoffCircS)
    (havg : ‖cubeAverageVec Q flux‖ ≤ fluxAverage)
    (hfluxWeakOne :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q 1 N flux ≤ fluxWeakOne)
    (hfluxWeakS :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ fluxWeakS)
    (hfull :
      ∀ N : ℕ,
        CubeDescendantDualFullVectorPoincareEstimate Q poincareConst
          (cubeFluctuation Q potential) dualField N)
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => cutoffGradient x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => cutoffGradient x i) z‖ ≤ cutoffDerivative)
    (hdualCircOne :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircOne)
    (hdualCircS :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircS)
    (hcutoffConstant_bound :
      cubeLpNorm Q (2 : ℝ≥0∞) potential *
          (cutoffDerivative + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ cutoffGradient) ≤
        cutoffConstant)
    (hcenteredCutoffConstant_bound :
      2 * (cubeScaleFactor Q * cutoffDerivative *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * cutoffCircOne)) +
        cubeLpNorm Q ∞ cutoffGradient *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * cutoffCircS))) ≤
        centeredCutoffConstant) :
    |cubeAverage Q
        (fun x => vecDot (flux x) (potential x • cutoffGradient x))| ≤
      cutoffProductBridgeRHS Q s cutoffGradient fluxWeakOne fluxWeakS fluxAverage
        cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant := by
  simpa [cutoffProductBridgeRHS] using
    abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_sharp_note_terms_of_dualFull_fullCirc_effective_constant
      (Q := Q) (s := s) (flux := flux) (u := potential)
      (G := dualField) (ξ := cutoffGradient)
      (Bu1 := fluxWeakOne) (BuS := fluxWeakS) (Bavg := fluxAverage)
      (Bcirc1 := cutoffCircOne) (BcircS := cutoffCircS)
      (B := cutoffDerivative) (C := poincareConst)
      (BgConst := cutoffConstant) (BgCent := centeredCutoffConstant)
      hcutoffDerivative hs_pos hs_lt_one hflux hpotential hdualField
      hcutoffGradient hcutoffConstant hcenteredCutoffConstant hfluxAverage
      hpoincareConst hcutoffCircOne hcutoffCircS havg hfluxWeakOne hfluxWeakS
      hfull hcutoffSmooth hcutoffDeriv hdualCircOne hdualCircS
      hcutoffConstant_bound hcenteredCutoffConstant_bound

/-- Private product-term bridge after inserting the raw Chapter 2 canonical
maximizer.  The remaining hypotheses are the analytic inputs for the cutoff
and duality estimates; this theorem does not create a public proof package. -/
theorem productTerm_le_cutoffProductBridge_of_canonicalMaximizer
    {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (p q p0 q0 : Vec d)
    (dualField cutoffGradient : Vec d → Vec d)
    {fluxWeakOne fluxWeakS fluxAverage cutoffCircOne cutoffCircS
      cutoffDerivative poincareConst cutoffConstant centeredCutoffConstant : ℝ}
    (hcutoffDerivative : 0 ≤ cutoffDerivative)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hdualField :
      ∀ i : Fin d,
        MemLp (fun x => dualField x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hcutoffGradient : MemLp cutoffGradient ∞ (normalizedCubeMeasure Q))
    (hcutoffConstant : 0 ≤ cutoffConstant)
    (hcenteredCutoffConstant : 0 ≤ centeredCutoffConstant)
    (hfluxAverage : 0 ≤ fluxAverage)
    (hpoincareConst : 0 ≤ poincareConst)
    (hcutoffCircOne : 0 ≤ cutoffCircOne)
    (hcutoffCircS : 0 ≤ cutoffCircS)
    (havg :
      ‖cubeAverageVec Q (canonicalMaximizerFluxDefectOnCube Q a p q q0)‖ ≤
        fluxAverage)
    (hfluxWeakOne :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q 1 N
          (canonicalMaximizerFluxDefectOnCube Q a p q q0) ≤ fluxWeakOne)
    (hfluxWeakS :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q s N
          (canonicalMaximizerFluxDefectOnCube Q a p q q0) ≤ fluxWeakS)
    (hfull :
      ∀ N : ℕ,
        CubeDescendantDualFullVectorPoincareEstimate Q poincareConst
          (cubeFluctuation Q (canonicalMaximizerPotentialDefectOnCube Q a p q p0))
          dualField N)
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => cutoffGradient x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => cutoffGradient x i) z‖ ≤ cutoffDerivative)
    (hdualCircOne :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircOne)
    (hdualCircS :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircS)
    (hcutoffConstant_bound :
      cubeLpNorm Q (2 : ℝ≥0∞)
            (canonicalMaximizerPotentialDefectOnCube Q a p q p0) *
          (cutoffDerivative + cubeBesovScaleWeight 1 Q *
            cubeLpNorm Q ∞ cutoffGradient) ≤
        cutoffConstant)
    (hcenteredCutoffConstant_bound :
      2 * (cubeScaleFactor Q * cutoffDerivative *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * cutoffCircOne)) +
        cubeLpNorm Q ∞ cutoffGradient *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * cutoffCircS))) ≤
        centeredCutoffConstant) :
    |cubeAverage Q
        (fun x =>
          vecDot (canonicalMaximizerFluxDefectOnCube Q a p q q0 x)
            (canonicalMaximizerPotentialDefectOnCube Q a p q p0 x •
              cutoffGradient x))| ≤
      cutoffProductBridgeRHS Q s cutoffGradient fluxWeakOne fluxWeakS fluxAverage
        cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant := by
  exact productTerm_le_cutoffProductBridge
    (Q := Q) (s := s)
    (flux := canonicalMaximizerFluxDefectOnCube Q a p q q0)
    (potential := canonicalMaximizerPotentialDefectOnCube Q a p q p0)
    (dualField := dualField) (cutoffGradient := cutoffGradient)
    hcutoffDerivative hs_pos hs_lt_one
    (canonicalMaximizerFluxDefectOnCube_memLp Q a p q q0)
    (canonicalMaximizerPotentialDefectOnCube_memLp Q a p q p0) hdualField
    hcutoffGradient hcutoffConstant hcenteredCutoffConstant hfluxAverage
    hpoincareConst hcutoffCircOne hcutoffCircS havg hfluxWeakOne hfluxWeakS
    hfull hcutoffSmooth hcutoffDeriv hdualCircOne hdualCircS
    hcutoffConstant_bound hcenteredCutoffConstant_bound

/-- Private product-term bridge for the Ch4 dependent coefficient family.

Compared with `productTerm_le_cutoffProductBridge_of_canonicalMaximizer`, the
raw flux-average and weak-norm hypotheses have been discharged through the Ch4
scalar-response surface.  The remaining hypotheses are the genuine analytic
cutoff/duality inputs for this deterministic product estimate. -/
theorem productTerm_le_cutoffProductBridge_of_dependentCanonicalMaximizer
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : ℝ)
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (p q p0 q0 : Vec d)
    (dualField cutoffGradient : Vec d → Vec d)
    {cutoffCircOne cutoffCircS cutoffDerivative poincareConst cutoffConstant
      centeredCutoffConstant : ℝ}
    (hcutoffDerivative : 0 ≤ cutoffDerivative)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hdualField :
      ∀ i : Fin d,
        MemLp (fun x => dualField x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hcutoffGradient : MemLp cutoffGradient ∞ (normalizedCubeMeasure Q))
    (hcutoffConstant : 0 ≤ cutoffConstant)
    (hcenteredCutoffConstant : 0 ≤ centeredCutoffConstant)
    (hpoincareConst : 0 ≤ poincareConst)
    (hcutoffCircOne : 0 ≤ cutoffCircOne)
    (hcutoffCircS : 0 ≤ cutoffCircS)
    (hfull :
      ∀ N : ℕ,
        CubeDescendantDualFullVectorPoincareEstimate Q poincareConst
          (cubeFluctuation Q
            (canonicalMaximizerPotentialDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0))
          dualField N)
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => cutoffGradient x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => cutoffGradient x i) z‖ ≤ cutoffDerivative)
    (hdualCircOne :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircOne)
    (hdualCircS :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircS)
    (hcutoffConstant_bound :
      cubeLpNorm Q (2 : ℝ≥0∞)
            (canonicalMaximizerPotentialDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0) *
          (cutoffDerivative + cubeBesovScaleWeight 1 Q *
            cubeLpNorm Q ∞ cutoffGradient) ≤
        cutoffConstant)
    (hcenteredCutoffConstant_bound :
      2 * (cubeScaleFactor Q * cutoffDerivative *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * cutoffCircOne)) +
        cubeLpNorm Q ∞ cutoffGradient *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * cutoffCircS))) ≤
        centeredCutoffConstant) :
    |cubeAverage Q
        (fun x =>
          vecDot
            (canonicalMaximizerFluxDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q q0 x)
            (canonicalMaximizerPotentialDefectOnCube Q
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
                p q p0 x • cutoffGradient x))| ≤
      cutoffProductBridgeRHS Q s cutoffGradient
        (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
        (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
        ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
        cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  exact productTerm_le_cutoffProductBridge_of_canonicalMaximizer
    (Q := Q) (s := s) (a := aQ) (p := p) (q := q) (p0 := p0) (q0 := q0)
    (dualField := dualField) (cutoffGradient := cutoffGradient)
    (fluxWeakOne := Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
    (fluxWeakS := Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
    (fluxAverage := ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖)
    (cutoffCircOne := cutoffCircOne) (cutoffCircS := cutoffCircS)
    (cutoffDerivative := cutoffDerivative) (poincareConst := poincareConst)
    (cutoffConstant := cutoffConstant)
    (centeredCutoffConstant := centeredCutoffConstant)
    hcutoffDerivative hs_pos hs_lt_one hdualField hcutoffGradient
    hcutoffConstant hcenteredCutoffConstant (norm_nonneg _)
    hpoincareConst hcutoffCircOne hcutoffCircS
    (by
      simpa [F, aQ] using
        norm_cubeAverageVec_canonicalMaximizerFluxDefectOnDependentFamily_le_ch04
          a ha Q p q q0)
    (by
      intro N
      simpa [F, aQ] using
        cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_le_ch04WeakNorm
          a ha Q (by norm_num : (0 : ℝ) < 1) N p q q0)
    (by
      intro N
      simpa [F, aQ] using
        cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_le_ch04WeakNorm
          a ha Q hs_pos N p q q0)
    (by simpa [F, aQ] using hfull)
    hcutoffSmooth hcutoffDeriv hdualCircOne hdualCircS
    (by simpa [F, aQ] using hcutoffConstant_bound)
    hcenteredCutoffConstant_bound

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
