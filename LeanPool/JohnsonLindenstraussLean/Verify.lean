import JL.SquaredGaussian
import JL.ChiSquared
import JL.Projection
import JL.NormPreservation
import JL.Rotation
import JL.Lemma
import JL.EndToEnd
import JL.InnerProduct
import JL.QJL
import JL.QJLDistortion

/-!
# Verification: sanity instantiations and axiom audit

This file contains small `example`-level sanity checks instantiating the main
results, plus `#print axioms` commands confirming the development depends only on
mathlib's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — i.e. it is
genuinely `sorry`-free.
-/

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

namespace JL

/-- At `t = 0` the squared-Gaussian MGF is `1` (the total mass of `N(0,1)`). -/
example : mgf (fun x => x ^ 2) stdGaussian 0 = 1 := by
  rw [sqGaussian_mgf (by norm_num)]; norm_num

/-- The chi-squared MGF specialises to the squared-Gaussian MGF at `k = 1`. -/
example {t : ℝ} (ht : t < 1 / 2) :
    mgf (chiSq 1) (gaussianVec 1) t = (√(1 - 2 * t))⁻¹ := by
  rw [chiSq_mgf 1 ht, pow_one]

/-- A concrete two-sided concentration instance: `k = 100`, `ε = 1/2`. -/
example :
    (gaussianVec 100).real
        {ω | (1 + (1 / 2 : ℝ)) * (100 : ℝ) ≤ chiSq 100 ω
              ∨ chiSq 100 ω ≤ (1 - (1 / 2 : ℝ)) * (100 : ℝ)}
      ≤ 2 * rexp (-((1 / 2 : ℝ) ^ 2 - (1 / 2 : ℝ) ^ 3) * (100 : ℝ) / 4) :=
  chiSq_concentration 100 (by norm_num) (by norm_num)

/-- The JL existence theorem is vacuously instantiable on the empty point set. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Fin 0 → Fin 0 → Ω → ℝ) (D : Fin 0 → Fin 0 → ℝ) :
    ∃ ω, ∀ a b : Fin 0, a ≠ b → |r a b ω - D a b| < (1 / 2 : ℝ) * D a b :=
  johnson_lindenstrauss (μ := μ) (C := 0) r D (fun a => a.elim0) le_rfl (by norm_num)

/-- The end-to-end Gaussian JL theorem is vacuously instantiable on the empty point set. -/
example {d k : ℕ} (hk : 0 < k) (p : Fin 0 → EuclideanSpace ℝ (Fin d)) :
    ∃ A : Fin k → Fin d → ℝ, ∀ a b : Fin 0, a ≠ b →
      |(∑ i, (jlMap k d A (fun j => (p a - p b) j) i) ^ 2) - ‖p a - p b‖ ^ 2|
        < (1 / 2 : ℝ) * ‖p a - p b‖ ^ 2 :=
  johnson_lindenstrauss_pointset hk p (by norm_num) (by norm_num)
    (fun a => a.elim0)
    (by
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, Real.log_zero]
      nlinarith [hkR])

/-- The exponential (sub-Gaussian) QJL distortion bound is now **unconditional**: it no longer
requires the `IsPerRowSubgaussian` hypothesis (discharged by `isPerRowSubgaussian_normalized`),
nor any `key ≠ 0` assumption (the `key = 0` case holds trivially). -/
example {m d : ℕ} (hm : 0 < m) (key q : EuclideanSpace ℝ (Fin d))
    {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).real
        {S | ε ≤ |qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫|}
      ≤ 2 * rexp (-((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2)) :=
  qjlEstimator_concentration_exp hm key q hε

end JL

-- Axiom audit for the main results.
#print axioms JL.sqGaussian_mgf
#print axioms JL.chiSq_mgf
#print axioms JL.chiSq_upper_tail
#print axioms JL.chiSq_lower_tail
#print axioms JL.chiSq_concentration
#print axioms JL.map_dotProduct_gaussianReal
#print axioms JL.gaussianMatrix_map_dotProduct
#print axioms JL.jlMap_concentration
#print axioms JL.johnson_lindenstrauss
#print axioms JL.johnson_lindenstrauss_pointset
#print axioms JL.inner_product_preservation
#print axioms JL.integral_abs_gaussianReal
#print axioms JL.sign_product_identity
#print axioms JL.qjlEstimator_unbiased
#print axioms JL.qjlEstimator_unbiased_inner
#print axioms JL.qjl_perrow_variance_le
#print axioms JL.qjlEstimator_variance_le
#print axioms JL.qjlEstimator_concentration
#print axioms JL.foldedNormal_subgaussian
#print axioms JL.isPerRowSubgaussian_of_unit
#print axioms JL.isPerRowSubgaussian_normalized
#print axioms JL.qjlEstimator_centered_hasSubgaussianMGF
#print axioms JL.qjlEstimator_concentration_exp
