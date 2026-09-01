/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Germs.Representatives
import LeanPool.LocalComplexGeometry.Nullstellensatz.PreparedRootLocality
import LeanPool.LocalComplexGeometry.WPTBridge.GermDivision

/-!
# Representatives of canonical Weierstrass division

The germ-level division identity becomes one pointwise identity on a common
ambient neighborhood after choosing analytic representatives.  Uniform
prepared-root locality then specializes it simultaneously at every root of a
nearby prepared fiber.
-/

open Filter
open scoped BigOperators Topology


namespace LocalComplexGeometry

open WPTBridge

noncomputable section

/-- Chosen representatives satisfy the canonical Weierstrass division
identity on one ambient neighborhood. -/
theorem eventually_representative_preparedGermDivision
    {n d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (h : HolomorphicGerm (n + 1)) :
    ∀ᶠ x in 𝓝 (0 : ComplexEuclidean (n + 1)),
      HolomorphicGerm.representative h x =
        HolomorphicGerm.representative
            (preparedGermDivisionQuotient a ha ha0 h) x *
          preparedValue a (dropLastCLM n x) (lastCoordinateCLM n x) +
        ∑ i : Fin d,
          HolomorphicGerm.representative
              (preparedGermDivisionRemainder a ha ha0 h i)
              (dropLastCLM n x) *
            lastCoordinateCLM n x ^ (i : ℕ) := by
  let q := preparedGermDivisionQuotient a ha ha0 h
  let r := preparedGermDivisionRemainder a ha ha0 h
  let qrep := HolomorphicGerm.representative q
  let rrep : Fin d → ComplexEuclidean n → ℂ :=
    fun i ↦ HolomorphicGerm.representative (r i)
  have hqanalytic : AnalyticAt ℂ qrep 0 :=
    HolomorphicGerm.analyticAt_representative q
  have hranalytic : ∀ i, AnalyticAt ℂ (rrep i) 0 :=
    fun i ↦ HolomorphicGerm.analyticAt_representative (r i)
  have hqof : HolomorphicGerm.ofFunction qrep hqanalytic = q := by
    apply Subtype.ext
    exact HolomorphicGerm.coe_representative q
  have hrof :
      (fun i ↦ HolomorphicGerm.ofFunction (rrep i) (hranalytic i)) = r := by
    funext i
    apply Subtype.ext
    exact HolomorphicGerm.coe_representative (r i)
  have hspec := preparedGermDivision_spec a ha ha0 h
  unfold IsPreparedGermDivision at hspec
  have hspecCoe := congrArg
    (fun f : HolomorphicGerm (n + 1) ↦ (f : FunctionGerm (n + 1))) hspec
  change (h : FunctionGerm (n + 1)) =
    ((q * preparedPolynomialGerm a ha + remainderPolynomialGerm r :
      HolomorphicGerm (n + 1)) : FunctionGerm (n + 1)) at hspecCoe
  rw [← hqof, ← hrof] at hspecCoe
  have hexpression := coe_preparedDivisionExpression_ofFunction
    a ha qrep hqanalytic rrep hranalytic
  have hfunGerm :
      ((HolomorphicGerm.representative h :
          ComplexEuclidean (n + 1) → ℂ) : FunctionGerm (n + 1)) =
        ((fun x ↦ qrep x * preparedPolynomialFunction a x +
          ∑ i : Fin d,
            rrep i (baseProjectionCLM n x) *
              lastCoordinateCLM n x ^ (i : ℕ)) : FunctionGerm (n + 1)) :=
    (HolomorphicGerm.coe_representative h).trans
      (hspecCoe.trans hexpression)
  apply Filter.Germ.coe_eq.mp
  refine hfunGerm.trans ?_
  apply congrArg Filter.Germ.ofFun
  funext x
  rfl

/-- At every root of every sufficiently nearby prepared fiber, the chosen
representative of a germ equals the specialized polynomial represented by its
canonical WPT remainder. -/
theorem eventually_representative_eq_remainder_on_preparedRoots
    {n d : ℕ} (hd : 0 < d)
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (h : HolomorphicGerm (n + 1)) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n), ∀ w : ℂ,
      preparedValue a z w = 0 →
        HolomorphicGerm.representative h (appendLastCLE n (z, w)) =
          ∑ i : Fin d,
            HolomorphicGerm.representative
                (preparedGermDivisionRemainder a ha ha0 h i) z *
              w ^ (i : ℕ) := by
  have hdivision := eventually_representative_preparedGermDivision
    a ha ha0 h
  have hall := eventually_on_all_prepared_roots hd a ha ha0 hdivision
  filter_upwards [hall] with z hz
  intro w hw
  have heq := hz w hw
  simpa only [dropLastCLM_appendLastCLE,
    lastCoordinateCLM_appendLastCLE, hw, mul_zero, zero_add] using heq

end

end LocalComplexGeometry
