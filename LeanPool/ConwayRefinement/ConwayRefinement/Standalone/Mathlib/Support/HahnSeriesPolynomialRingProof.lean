/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.HahnSeriesPolynomialRing
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PolynomialAlgebra.PolynomialRing

/-! # Hahn Series Polynomial Ring Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.HahnPolynomial

universe u

private def seriesEquiv (K : Type u) [Field K] :
    Series K ≃+* Berarducci.Series K := by
  have h : Series K = HahnSeries.nonpositiveSubring ℝ K := by
    ext x
    rfl
  rw [h]

private def finiteSupportEquiv (K : Type u) [Field K] :
    FiniteSupport K ≃+*
      HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K) where
  toFun x := ⟨seriesEquiv K x.1, by
    rw [HahnSeries.Nonpositive.mem_finiteSupportSubring_iff]
    exact (mem_finiteSupport_iff K x.1).mp x.2⟩
  invFun x := ⟨(seriesEquiv K).symm x.1, by
    rw [mem_finiteSupport_iff]
    exact (HahnSeries.Nonpositive.mem_finiteSupportSubring_iff x.1).mp x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

namespace IsPolynomialRing

/-- A minimal homogeneous system and lifts of its generators supply the polynomial variables. -/
theorem of_polynomiality (K : Type u) [Field K] :
    HahnPolynomial.IsPolynomialRing K := by
  intro hK
  let := hK
  obtain ⟨ι, weight, generators, hminimal, ⟨lifts⟩⟩ :=
    Berarducci.exists_isMinimalSystem_and_generatorLifts K
  let ringEquiv : MvPolynomial ι (FiniteSupport K) ≃+* Series K :=
    (MvPolynomial.mapEquiv ι (finiteSupportEquiv K)).trans
      ((Berarducci.polynomialRingEquiv hminimal lifts).toRingEquiv.trans
        (seriesEquiv K).symm)
  let algEquiv : MvPolynomial ι (FiniteSupport K) ≃ₐ[FiniteSupport K] Series K :=
    AlgEquiv.ofRingEquiv (f := ringEquiv) fun x ↦ by
      change ringEquiv (MvPolynomial.C x) = (x : Series K)
      simp only [ringEquiv, RingEquiv.trans_apply, MvPolynomial.mapEquiv_apply,
        MvPolynomial.map_C]
      change (seriesEquiv K).symm
        (Berarducci.polynomialRingEquiv hminimal lifts
          (MvPolynomial.C (finiteSupportEquiv K x))) = (x : Series K)
      rw [Berarducci.polynomialRingEquiv_apply, Berarducci.evalAtLifts_C]
      rfl
  exact ⟨ι, ⟨algEquiv⟩⟩

end IsPolynomialRing

end ConwayRefinement.Standalone.HahnPolynomial
