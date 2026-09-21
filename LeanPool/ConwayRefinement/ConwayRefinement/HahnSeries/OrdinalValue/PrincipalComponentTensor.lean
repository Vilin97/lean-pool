/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubring
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportResidue
public import Mathlib.LinearAlgebra.TensorProduct.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.GermDegree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NormalForm
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PrincipalAddition
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Extension of scalars for `P_α`

This module proves LM24, Proposition 5.3.1. For each Hahn-series degree `α`, multiplication
induces the canonical linear equivalence

`P_α ⊗[K] K(ℝ^{≤ 0}) ≃ RV_α`.

Here `P_α` is the intrinsic quotient `J_(ω^(α+1)) / J_(ω^α)`, the finite-support
factor has its canonical monomial basis, and `RV_α` is the degree-`α` component of `RV̂`.
No basis or complement is chosen in `P_α`.

Surjectivity follows by sending each term of the unique LM24 normal form to its principal
coefficient tensored with the corresponding monomial; lower-degree terms vanish in `RV_α`.
For injectivity, translated closed truncation at an exponent extracts the coefficient at that
monomial in `P_α`. This proves linear independence without choosing representatives coherently.
-/

open scoped DirectSum HahnSeries NatOrdinal TensorProduct

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K]

abbrev FiniteSupportRing :=
  HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)

private theorem coe_translatedTruncation_translate (p : Series K) (h g : ℝ) :
    ((translatedTruncation (HahnSeries.translate h (p : K⟦ℝ⟧)) g : Series K) :
        K⟦ℝ⟧) =
      HahnSeries.translate (h - g)
        (HahnSeries.truncLE (g - h) (p : K⟦ℝ⟧)) := by
  rw [coe_translatedTruncation, HahnSeries.truncLE_translate,
    HahnSeries.translate_add_apply]
  congr 2
  · ring

variable (K) in
/-- On a series `b` of degree `≤ α`, the class of the translated truncation `b^{|γ}` in `P_α`,
additive in `b`. -/
private def degreeLayerTruncationAtRepresentative (alpha : NatOrdinal) (g : ℝ) :
    (HahnSeries.Nonpositive.degreeValuation K).filtrationLE alpha →+
      PrincipalComponent K alpha := by
  let wDegree := HahnSeries.Nonpositive.degreeValuation K
  let wOrder := ordinalValueDegreeValuation K
  refine
    { toFun := fun b ↦ wOrder.componentMk alpha ⟨translatedTruncation (b : Series K) g, ?_⟩
      map_zero' := ?_
      map_add' := ?_ }
  · rw [wOrder.mem_filtrationLE_iff,
      ordinalValueDegreeValuation_apply]
    have hbDegree := (wDegree.mem_filtrationLE_iff alpha (b : Series K)).mp b.2
    rw [HahnSeries.Nonpositive.degreeValuation_apply] at hbDegree
    exact (ordinalValueDegree_translatedTruncation_le_degree
      ((b : Series K) : K⟦ℝ⟧) g).trans hbDegree
  · change wOrder.componentMk alpha ⟨translatedTruncation 0 g, _⟩ = 0
    rw [← map_zero (wOrder.componentMk alpha)]
    apply congrArg (wOrder.componentMk alpha)
    apply Subtype.ext
    exact translatedTruncation_zero_input (K := K) g
  · intro b c
    change wOrder.componentMk alpha
        ⟨translatedTruncation ((b : Series K) + (c : Series K)) g, _⟩ =
      wOrder.componentMk alpha ⟨translatedTruncation (b : Series K) g, _⟩ +
        wOrder.componentMk alpha ⟨translatedTruncation (c : Series K) g, _⟩
    rw [← map_add]
    apply congrArg (wOrder.componentMk alpha)
    apply Subtype.ext
    exact translatedTruncation_add
      ((b : Series K) : K⟦ℝ⟧) ((c : Series K) : K⟦ℝ⟧) g

variable (K) in
private theorem degreeLayerTruncationAt_lower_le_ker (alpha : NatOrdinal) (g : ℝ) :
    (HahnSeries.Nonpositive.degreeValuation K).lowerFiltration alpha ≤
      (degreeLayerTruncationAtRepresentative K alpha g).ker := by
  let wDegree := HahnSeries.Nonpositive.degreeValuation K
  let wOrder := ordinalValueDegreeValuation K
  intro b hb
  rw [AddMonoidHom.mem_ker]
  change wOrder.componentMk alpha ⟨translatedTruncation (b : Series K) g, _⟩ = 0
  rw [wOrder.componentMk_eq_zero_iff,
    ordinalValueDegreeValuation_apply]
  have hbDegree := (wDegree.mem_lowerFiltration_iff alpha b).mp hb
  rw [HahnSeries.Nonpositive.degreeValuation_apply] at hbDegree
  exact (ordinalValueDegree_translatedTruncation_le_degree
    ((b : Series K) : K⟦ℝ⟧) g).trans_lt hbDegree

variable (K) in
/-- The class of the translated truncation `b^{|γ}` in `P_α`, as an additive map on the degree
component `{deg ≤ α}/{deg < α}`: series of degree `< α` have `b^{|γ} ∈ J_{ω^α}`. -/
private def degreeLayerTruncationAt (alpha : NatOrdinal) (g : ℝ) :
    (HahnSeries.Nonpositive.degreeValuation K).Component alpha →+
      PrincipalComponent K alpha :=
  QuotientAddGroup.lift
    ((HahnSeries.Nonpositive.degreeValuation K).lowerFiltration alpha)
    (degreeLayerTruncationAtRepresentative K alpha g)
    (degreeLayerTruncationAt_lower_le_ker K alpha g)

/-- On the degree-`α` homogeneous class of `b`, the map is the class of `b^{|γ}` in `P_α`. -/
private theorem degreeLayerTruncationAt_mk (alpha : NatOrdinal) (g : ℝ)
    (b : Series K) (hb : (b : K⟦ℝ⟧).degree ≤
      (alpha : WithBot NatOrdinal)) :
    degreeLayerTruncationAt K alpha g (degreeLayerMk alpha b hb) =
      principalComponentMk alpha (translatedTruncation (b : K⟦ℝ⟧) g)
        ((ordinalValueDegree_le_coe_iff (translatedTruncation (b : K⟦ℝ⟧) g) alpha).mp
          ((ordinalValueDegree_translatedTruncation_le_degree (b : K⟦ℝ⟧) g).trans hb)) := by
  let wDegree := HahnSeries.Nonpositive.degreeValuation K
  rw [degreeLayerMk_eq_componentMk]
  change degreeLayerTruncationAt K alpha g
      (wDegree.componentMk alpha ⟨b, _⟩) = _
  rw [← wDegree.coe_component_eq_componentMk]
  rw [principalComponentMk_eq_componentMk]
  rfl

/-- The finite-support residue equivalence sends a constant series to its canonical
degree-zero homogeneous class. -/
theorem degreeFiniteSupportResidueEquiv_scalar (k : K) :
    HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K
        (HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k) =
      degreeLayerScalarHom K k := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  rw [HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv_apply,
    degreeLayerScalarHom_apply]
  rw [w.residueMap_apply, degreeLayerMk_eq_componentMk]
  apply congrArg (w.componentMk 0)
  apply Subtype.ext
  rw [w.coe_nonpositiveEquivFiltrationLEZero]
  rw [RingEquiv.coe_subringCongr_apply]
  apply Subtype.ext
  exact (HahnSeries.Nonpositive.coe_finiteSupportScalarHom
    (G := ℝ) (K := K) k).trans (HahnSeries.Nonpositive.coe_C k).symm

/-- Successive scalar actions by degree-zero residue classes agree with multiplication in the
residue ring. -/
theorem degreeResidue_smul_smul (alpha : NatOrdinal)
    (a b : (HahnSeries.Nonpositive.degreeValuation K).ResidueRing)
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component alpha) :
    (a * b) • x = a • (b • x) := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  apply DirectSum.of_injective (β := w.Component) alpha
  rw [DirectSum.of_zero_smul, DirectSum.of_zero_smul,
    DirectSum.of_zero_smul, DirectSum.of_zero_mul]
  rw [mul_assoc]

/-- The unit residue class acts identically on every degree component. -/
theorem degreeResidue_one_smul (alpha : NatOrdinal)
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component alpha) :
    (1 : (HahnSeries.Nonpositive.degreeValuation K).ResidueRing) • x =
      x := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  apply DirectSum.of_injective (β := w.Component) alpha
  rw [DirectSum.of_zero_smul, DirectSum.of_zero_one, one_mul]

private theorem residue_smul_comm (alpha : NatOrdinal)
    (a b : (HahnSeries.Nonpositive.degreeValuation K).ResidueRing)
    (x : (HahnSeries.Nonpositive.degreeValuation K).Component alpha) :
    a • (b • x) = b • (a • x) := by
  rw [← degreeResidue_smul_smul alpha,
    ← degreeResidue_smul_smul alpha, mul_comm]

private theorem residueEquiv_eq_degreeLayerMk (p : FiniteSupportRing (K := K)) :
    HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K p =
      degreeLayerMk 0 (p : Series K) (by
        simpa using (HahnSeries.degree_le_zero_iff.mpr
          ((HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
            (p : Series K)).mp p.2))) := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  rw [HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv_apply,
    w.residueMap_apply, degreeLayerMk_eq_componentMk]
  apply congrArg (w.componentMk 0)
  apply Subtype.ext
  rw [w.coe_nonpositiveEquivFiltrationLEZero,
    RingEquiv.coe_subringCongr_apply]

/-- The degree-zero residue action of a finite-support series on a fixed component is
multiplication of representatives. -/
theorem degreeFiniteSupportResidueEquiv_smul_degreeLayerMk (alpha : NatOrdinal)
    (p : FiniteSupportRing (K := K)) (b : Series K)
    (hb : (b : K⟦ℝ⟧).degree ≤ (alpha : WithBot NatOrdinal)) :
    HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K p •
        degreeLayerMk alpha b hb =
      degreeLayerMk alpha ((p : Series K) * b) (by
        apply (HahnSeries.degree_mul_le _ _).trans
        exact (add_le_add (by
          simpa using (HahnSeries.degree_le_zero_iff.mpr
            ((HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
              (p : Series K)).mp p.2))) hb).trans_eq (zero_add _)) := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  apply DirectSum.of_injective (β := w.Component) alpha
  rw [DirectSum.of_zero_smul, DirectSum.of_mul_of]
  change DirectSum.of w.Component (0 + alpha)
      (w.componentMul
        (HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K p)
        (degreeLayerMk alpha b hb)) = _
  rw [residueEquiv_eq_degreeLayerMk, degreeLayerMk_mul]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply Sigma.ext (zero_add alpha)
  rw [degreeLayerMk_eq_componentMk, degreeLayerMk_eq_componentMk]
  exact w.componentMk_heq_of_grade_eq_of_coe_eq (zero_add alpha) _ _ rfl

theorem principalComponentToHahnDegreeLayer_mk (alpha : NatOrdinal)
    (p : Series K) (hp : HahnSeries.Nonpositive.IsPrincipal p)
    (hpDegree : (p : K⟦ℝ⟧).degree = (alpha : WithBot NatOrdinal))
    (hpBound : ordinalValue p < ω^ (alpha + 1)) :
    principalComponentToHahnDegreeLayer K alpha
        (principalComponentMk alpha p hpBound) =
      degreeLayerMk alpha p hpDegree.le := by
  rw [← degreeLayerToPrincipalComponent_mk alpha p hpDegree.le]
  apply principalComponentToHahnDegreeLayer_degreeLayerToPrincipalComponent_of_isPrincipal
  rw [isPrincipalDegreeClass_iff]
  exact Or.inr ⟨p, hp, hpDegree, rfl⟩

variable (K) in
def principalComponentFiniteSupportMul (alpha : NatOrdinal) :
    PrincipalComponent K alpha →ₗ[K]
      FiniteSupportRing (K := K) →ₗ[K]
        (HahnSeries.Nonpositive.degreeValuation K).Component alpha :=
  LinearMap.mk₂ K
    (fun x p ↦
      HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K p •
        principalComponentToHahnDegreeLayer K alpha x)
    (by
      intro x y p
      simpa only [map_add] using
        (smul_add
          (HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K p)
          (principalComponentToHahnDegreeLayer K alpha x)
          (principalComponentToHahnDegreeLayer K alpha y)))
    (by
      intro k x p
      rw [map_smul]
      rw [degreeLayer_smul_eq_residue_smul,
        degreeLayer_smul_eq_residue_smul]
      exact residue_smul_comm alpha _ _ _)
    (by
      intro x p q
      simpa only [map_add] using
        (add_smul
          (HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K p)
          (HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K q)
          (principalComponentToHahnDegreeLayer K alpha x)))
    (by
      intro k x p
      rw [HahnSeries.Nonpositive.smul_finiteSupport_eq_scalar_mul]
      rw [map_mul, degreeFiniteSupportResidueEquiv_scalar]
      rw [degreeLayer_smul_eq_residue_smul]
      exact degreeResidue_smul_smul alpha _ _ _)

@[simp]
theorem principalComponentFiniteSupportMul_apply (alpha : NatOrdinal)
    (x : PrincipalComponent K alpha) (p : FiniteSupportRing (K := K)) :
    principalComponentFiniteSupportMul K alpha x p =
      HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K p •
        principalComponentToHahnDegreeLayer K alpha x :=
  (rfl)

variable (K) in
def principalComponentTensorMap (alpha : NatOrdinal) :
    PrincipalComponent K alpha ⊗[K] FiniteSupportRing (K := K) →ₗ[K]
      (HahnSeries.Nonpositive.degreeValuation K).Component alpha :=
  TensorProduct.lift (principalComponentFiniteSupportMul K alpha)

@[simp]
theorem principalComponentTensorMap_tmul (alpha : NatOrdinal)
    (x : PrincipalComponent K alpha) (p : FiniteSupportRing (K := K)) :
    principalComponentTensorMap K alpha (x ⊗ₜ p) =
      HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K p •
        principalComponentToHahnDegreeLayer K alpha x := by
  rw [principalComponentTensorMap, TensorProduct.lift.tmul]
  rfl

theorem principalComponentTensorMap_principal_monomial (alpha : NatOrdinal)
    (p : Series K) (hp : HahnSeries.Nonpositive.IsPrincipal p)
    (hpDegree : (p : K⟦ℝ⟧).degree = (alpha : WithBot NatOrdinal))
    (hpBound : ordinalValue p < ω^ (alpha + 1))
    (g : HahnSeries.Nonpositive.exponentMonoid ℝ) :
    principalComponentTensorMap K alpha
        (principalComponentMk alpha p hpBound ⊗ₜ
          HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g) =
      degreeLayerMk alpha
        (((HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g :
          FiniteSupportRing (K := K)) : Series K) * p) (by
            apply (HahnSeries.degree_mul_le _ _).trans
            exact (add_le_add (by
              exact HahnSeries.degree_le_zero_iff.mpr
                ((HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
                  ((HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g :
                    FiniteSupportRing (K := K)) : Series K)).mp
                      (HahnSeries.Nonpositive.finiteSupportMonomial
                        (K := K) g).2)) hpDegree.le).trans_eq (zero_add _)) := by
  rw [principalComponentTensorMap_tmul,
    principalComponentToHahnDegreeLayer_mk alpha p hp hpDegree hpBound]
  rw [degreeFiniteSupportResidueEquiv_smul_degreeLayerMk]

private theorem finiteSupportMonomial_degree (g : HahnSeries.Nonpositive.exponentMonoid ℝ) :
    ((((HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g :
      FiniteSupportRing (K := K)) : Series K) : K⟦ℝ⟧).degree) = 0 := by
  apply HahnSeries.degree_eq_zero.mpr
  constructor
  · rw [HahnSeries.Nonpositive.coe_finiteSupportMonomial]
    exact HahnSeries.single_ne_zero one_ne_zero
  · exact (HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
      ((HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g :
        FiniteSupportRing (K := K)) : Series K)).mp
        (HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g).2

private theorem coe_finiteSupportMonomial_mul (g : HahnSeries.Nonpositive.exponentMonoid ℝ) (p : Series K) :
    ((((HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g :
        FiniteSupportRing (K := K)) : Series K) * p : Series K) : K⟦ℝ⟧) =
      HahnSeries.translate (g : ℝ) (p : K⟦ℝ⟧) := by
  change
    (((HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g :
      FiniteSupportRing (K := K)) : Series K) : K⟦ℝ⟧) * (p : K⟦ℝ⟧) = _
  rw [HahnSeries.Nonpositive.coe_finiteSupportMonomial,
    HahnSeries.single_one_mul_eq_translate]

private def shiftedSeries (g : HahnSeries.Nonpositive.exponentMonoid ℝ) (p : Series K) : Series K :=
  ⟨HahnSeries.translate (g : ℝ) (p : K⟦ℝ⟧), by
    rw [HahnSeries.mem_nonpositiveSubring, HahnSeries.support_translate]
    rintro _ ⟨x, hx, rfl⟩
    exact add_nonpos g.2 (HahnSeries.Nonpositive.support_subset p hx)⟩

@[simp]
private theorem coe_shiftedSeries (g : HahnSeries.Nonpositive.exponentMonoid ℝ) (p : Series K) :
    ((shiftedSeries g p : Series K) : K⟦ℝ⟧) =
      HahnSeries.translate (g : ℝ) (p : K⟦ℝ⟧) :=
  (rfl)

private theorem finiteSupportMonomial_mul_eq_shiftedSeries (g : HahnSeries.Nonpositive.exponentMonoid ℝ) (p : Series K) :
    ((HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g :
        FiniteSupportRing (K := K)) : Series K) * p = shiftedSeries g p := by
  apply Subtype.ext
  exact coe_finiteSupportMonomial_mul g p

private abbrev PrincipalMonomialTerm (K : Type v) [Field K] :=
  Series K × HahnSeries.Nonpositive.exponentMonoid ℝ

private def principalMonomialTermSeries (t : PrincipalMonomialTerm K) : Series K :=
  (HahnSeries.Nonpositive.finiteSupportMonomial (K := K) t.2 :
      FiniteSupportRing (K := K)) * t.1

private theorem principalMonomialTermSeries_degree (t : PrincipalMonomialTerm K) :
    ((principalMonomialTermSeries t : Series K) : K⟦ℝ⟧).degree =
      (t.1 : K⟦ℝ⟧).degree := by
  rw [principalMonomialTermSeries, coe_finiteSupportMonomial_mul, HahnSeries.degree_translate]

private def normalTermSeries (t : HahnSeries.NormalForm.Term K)
    (ht : t.exponent ≤ 0) : Series K :=
  ⟨t.series, (HahnSeries.mem_nonpositiveSubring (x := t.series)).mpr (by
    rw [HahnSeries.NormalForm.Term.series_eq_translate,
      HahnSeries.support_translate]
    rintro _ ⟨g, hg, rfl⟩
    exact add_nonpos ht (HahnSeries.Nonpositive.support_subset t.coefficient hg))⟩

private theorem principalMonomialTerm_series_eq_normalTermSeries
    (t : HahnSeries.NormalForm.Term K) (ht : t.exponent ≤ 0) :
    principalMonomialTermSeries
        (⟨t.coefficient, ⟨t.exponent, ht⟩⟩ : PrincipalMonomialTerm K) =
      normalTermSeries t ht := by
  apply Subtype.ext
  change
    (((HahnSeries.Nonpositive.finiteSupportMonomial (K := K)
      ⟨t.exponent, ht⟩ : FiniteSupportRing (K := K)) : Series K) : K⟦ℝ⟧) *
        (t.coefficient : K⟦ℝ⟧) = t.series
  rw [HahnSeries.Nonpositive.coe_finiteSupportMonomial,
    HahnSeries.single_one_mul_eq_translate,
    HahnSeries.NormalForm.Term.series_eq_translate]

private theorem principalMonomialTerms_sum_degree_le (alpha : NatOrdinal)
    (terms : List (PrincipalMonomialTerm K))
    (hdegree : ∀ t ∈ terms,
      (t.1 : K⟦ℝ⟧).degree ≤ (alpha : WithBot NatOrdinal)) :
    (((terms.map principalMonomialTermSeries).sum : Series K) : K⟦ℝ⟧).degree ≤
      (alpha : WithBot NatOrdinal) := by
  induction terms with
  | nil => simp
  | cons t terms ih =>
      rw [List.map_cons, List.sum_cons]
      exact (HahnSeries.degree_add_le _ _).trans (max_le
        (by rw [principalMonomialTermSeries_degree]
            exact hdegree t (by simp))
        (ih fun s hs ↦ hdegree s (by simp [hs])))

private theorem exists_tensor_eq_degreeLayerMk_terms (alpha : NatOrdinal)
    (terms : List (PrincipalMonomialTerm K))
    (hprincipal : ∀ t ∈ terms,
      HahnSeries.Nonpositive.IsPrincipal t.1)
    (hdegree : ∀ t ∈ terms,
      (t.1 : K⟦ℝ⟧).degree ≤ (alpha : WithBot NatOrdinal)) :
    ∃ z : PrincipalComponent K alpha ⊗[K] FiniteSupportRing (K := K),
      principalComponentTensorMap K alpha z =
        degreeLayerMk alpha
          (terms.map principalMonomialTermSeries).sum
          (principalMonomialTerms_sum_degree_le alpha terms hdegree) := by
  induction terms with
  | nil =>
      refine ⟨0, ?_⟩
      rw [map_zero]
      symm
      rw [degreeLayerMk_eq_zero_iff]
      simp
  | cons t terms ih =>
      have htPrincipal := hprincipal t (by simp)
      have htDegreeLE := hdegree t (by simp)
      have htSeriesLE : ((principalMonomialTermSeries t : Series K) : K⟦ℝ⟧).degree ≤
          (alpha : WithBot NatOrdinal) := by
        rw [principalMonomialTermSeries_degree]
        exact htDegreeLE
      have htailPrincipal : ∀ s ∈ terms,
          HahnSeries.Nonpositive.IsPrincipal s.1 :=
        fun s hs ↦ hprincipal s (by simp [hs])
      have htailDegree : ∀ s ∈ terms,
          (s.1 : K⟦ℝ⟧).degree ≤ (alpha : WithBot NatOrdinal) :=
        fun s hs ↦ hdegree s (by simp [hs])
      obtain ⟨z, hz⟩ := ih htailPrincipal htailDegree
      by_cases htDegree : (t.1 : K⟦ℝ⟧).degree =
          (alpha : WithBot NatOrdinal)
      · have htBound : ordinalValue t.1 < ω^ (alpha + 1) :=
          (ordinalValueDegree_le_coe_iff t.1 alpha).mp
            ((ordinalValueDegree_le_degree t.1).trans htDegreeLE)
        let zt : PrincipalComponent K alpha ⊗[K] FiniteSupportRing (K := K) :=
          principalComponentMk alpha t.1 htBound ⊗ₜ
            HahnSeries.Nonpositive.finiteSupportMonomial (K := K) t.2
        refine ⟨zt + z, ?_⟩
        rw [map_add, hz]
        rw [show principalComponentTensorMap K alpha zt =
            degreeLayerMk alpha (principalMonomialTermSeries t) htSeriesLE by
          exact principalComponentTensorMap_principal_monomial alpha
            t.1 htPrincipal htDegree htBound t.2]
        simpa only [List.map_cons, List.sum_cons] using
          (degreeLayerMk_add alpha (principalMonomialTermSeries t)
            (terms.map principalMonomialTermSeries).sum
            htSeriesLE
            (principalMonomialTerms_sum_degree_le alpha terms htailDegree)).symm
      · have htDegreeLT : (t.1 : K⟦ℝ⟧).degree <
            (alpha : WithBot NatOrdinal) := lt_of_le_of_ne htDegreeLE htDegree
        refine ⟨z, ?_⟩
        rw [hz]
        have htSeriesLT : ((principalMonomialTermSeries t : Series K) : K⟦ℝ⟧).degree <
            (alpha : WithBot NatOrdinal) := by
          rw [principalMonomialTermSeries_degree]
          exact htDegreeLT
        have htZero : degreeLayerMk alpha
            (principalMonomialTermSeries t) htSeriesLE = 0 :=
          (degreeLayerMk_eq_zero_iff alpha
            (principalMonomialTermSeries t) htSeriesLE).mpr
            htSeriesLT
        have hadd := degreeLayerMk_add alpha (principalMonomialTermSeries t)
          (terms.map principalMonomialTermSeries).sum
          htSeriesLE
          (principalMonomialTerms_sum_degree_le alpha terms htailDegree)
        rw [htZero, zero_add] at hadd
        simpa only [List.map_cons, List.sum_cons] using hadd.symm

variable (K) in
private theorem principalComponentTensorMap_surjective (alpha : NatOrdinal) :
    Function.Surjective (principalComponentTensorMap K alpha) := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H b =>
      have hbDegree : ((b : Series K) : K⟦ℝ⟧).degree ≤
          (alpha : WithBot NatOrdinal) := by
        have hbValue := (w.mem_filtrationLE_iff alpha (b : Series K)).mp b.2
        rw [HahnSeries.Nonpositive.degreeValuation_apply] at hbValue
        exact hbValue
      obtain ⟨terms, hterms⟩ := HahnSeries.exists_isNormalForm (b : Series K)
      obtain ⟨hsum, _, hprincipal, _, hpair⟩ :=
        HahnSeries.isNormalForm_iff.mp hterms
      have htermSupport (t : HahnSeries.NormalForm.Term K) (ht : t ∈ terms) :
          t.series.support ⊆ ((b : Series K) : K⟦ℝ⟧).support := by
        have htMem : t.series ∈ terms.map HahnSeries.NormalForm.Term.series :=
          List.mem_map.mpr ⟨t, ht, rfl⟩
        have hsubset := HahnSeries.support_subset_list_sum_of_mem hpair htMem
        rwa [hsum] at hsubset
      have htermExponent (t : HahnSeries.NormalForm.Term K) (ht : t ∈ terms) :
          t.exponent ≤ 0 := by
        rw [← HahnSeries.NormalForm.Term.csSup_support_series t
          (hprincipal t ht)]
        apply csSup_le
          (HahnSeries.support_nonempty_iff.mpr
            (HahnSeries.NormalForm.Term.series_ne_zero (hprincipal t ht)))
        intro g hg
        exact HahnSeries.Nonpositive.support_subset (b : Series K)
          (htermSupport t ht hg)
      have htermDegree (t : HahnSeries.NormalForm.Term K) (ht : t ∈ terms) :
          (t.coefficient : K⟦ℝ⟧).degree ≤
            (alpha : WithBot NatOrdinal) := by
        calc
          (t.coefficient : K⟦ℝ⟧).degree = t.series.degree := by
            rw [HahnSeries.NormalForm.Term.series_eq_translate,
              HahnSeries.degree_translate]
          _ ≤ ((b : Series K) : K⟦ℝ⟧).degree :=
            HahnSeries.degree_mono_support (htermSupport t ht)
          _ ≤ (alpha : WithBot NatOrdinal) := hbDegree
      let principalTerms : List (PrincipalMonomialTerm K) := terms.pmap
        (fun t ht ↦ ⟨t.coefficient, ⟨t.exponent, ht⟩⟩) htermExponent
      have hprincipalTerms : ∀ t ∈ principalTerms,
          HahnSeries.Nonpositive.IsPrincipal t.1 := by
        intro t ht
        simp only [principalTerms, List.mem_pmap] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        exact hprincipal s hs
      have hdegreeTerms : ∀ t ∈ principalTerms,
          (t.1 : K⟦ℝ⟧).degree ≤
            (alpha : WithBot NatOrdinal) := by
        intro t ht
        simp only [principalTerms, List.mem_pmap] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        exact htermDegree s hs
      have hseriesList :
          principalTerms.map
              (fun t ↦ ((principalMonomialTermSeries t : Series K) : K⟦ℝ⟧)) =
            terms.map HahnSeries.NormalForm.Term.series := by
        simp only [principalTerms, List.map_pmap]
        calc
          List.pmap
              (fun t ht ↦
                ((principalMonomialTermSeries
                    (⟨t.coefficient, ⟨t.exponent, ht⟩⟩ : PrincipalMonomialTerm K) :
                      Series K) : K⟦ℝ⟧))
              terms htermExponent =
              List.pmap (fun t _ ↦ t.series) terms htermExponent := by
                apply List.pmap_congr_left
                intro t _ ht _
                exact congrArg (fun x : Series K ↦ (x : K⟦ℝ⟧))
                  (principalMonomialTerm_series_eq_normalTermSeries t ht)
          _ = terms.map HahnSeries.NormalForm.Term.series :=
            List.pmap_eq_map htermExponent
      have hseriesSum :
          (((principalTerms.map principalMonomialTermSeries).sum : Series K) :
              K⟦ℝ⟧) = (b : Series K) := by
        change (HahnSeries.nonpositiveSubring ℝ K).subtype
            (principalTerms.map principalMonomialTermSeries).sum =
          ((b : Series K) : K⟦ℝ⟧)
        rw [map_list_sum]
        have hcoeList :
            (principalTerms.map principalMonomialTermSeries).map
                (HahnSeries.nonpositiveSubring ℝ K).subtype =
              principalTerms.map
                (fun t ↦ ((principalMonomialTermSeries t : Series K) : K⟦ℝ⟧)) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro t _
          rfl
        rw [hcoeList]
        exact (congrArg List.sum hseriesList).trans hsum
      obtain ⟨z, hz⟩ := exists_tensor_eq_degreeLayerMk_terms alpha principalTerms hprincipalTerms
        hdegreeTerms
      refine ⟨z, ?_⟩
      rw [hz, degreeLayerMk_eq_componentMk, w.coe_component_eq_componentMk]
      apply congrArg (w.componentMk alpha)
      apply Subtype.ext
      exact Subtype.ext hseriesSum

private theorem degreeLayerTruncationAt_principalComponentTensorMap_tmul_monomial
    (alpha : NatOrdinal) (x : PrincipalComponent K alpha)
    (h g : HahnSeries.Nonpositive.exponentMonoid ℝ) :
    degreeLayerTruncationAt K alpha g
        (principalComponentTensorMap K alpha
          (x ⊗ₜ HahnSeries.Nonpositive.finiteSupportMonomial (K := K) h)) =
      if h = g then x else 0 := by
  by_cases hx : x = 0
  · subst x
    simp
  obtain ⟨p, hpBound, hp, hpDegree, hpx⟩ :=
    exists_principal_representative_of_ne_zero alpha x hx
  rw [← hpx]
  have hshiftedDegree : ((shiftedSeries h p : Series K) : K⟦ℝ⟧).degree =
      (alpha : WithBot NatOrdinal) := by
    rw [coe_shiftedSeries, HahnSeries.degree_translate, hpDegree]
  have himage :
      principalComponentTensorMap K alpha
          (principalComponentMk alpha p hpBound ⊗ₜ
            HahnSeries.Nonpositive.finiteSupportMonomial (K := K) h) =
        degreeLayerMk alpha (shiftedSeries h p) hshiftedDegree.le := by
    rw [principalComponentTensorMap_principal_monomial alpha
      p hp hpDegree hpBound h]
    rw [degreeLayerMk_eq_componentMk, degreeLayerMk_eq_componentMk]
    apply congrArg
      ((HahnSeries.Nonpositive.degreeValuation K).componentMk alpha)
    apply Subtype.ext
    exact finiteSupportMonomial_mul_eq_shiftedSeries h p
  rw [himage, degreeLayerTruncationAt_mk]
  simp only [coe_shiftedSeries]
  by_cases hhg : h = g
  · subst g
    rw [ite_eq_left rfl]
    have hgerm : translatedTruncation
        (HahnSeries.translate (h : ℝ) (p : K⟦ℝ⟧)) h = p := by
      apply Subtype.ext
      rw [coe_translatedTruncation_translate]
      rw [sub_self, HahnSeries.truncLE_eq_self_of_support_subset_Iic
        (HahnSeries.Nonpositive.support_subset p)]
      simp
    apply (principalComponentMk_eq_iff alpha _ p _ hpBound).mpr
    rw [hgerm, sub_self, ordinalValue_zero]
    exact NatOrdinal.wpow_pos alpha
  · rw [ite_eq_right hhg]
    rw [principalComponentMk_eq_zero_iff]
    rcases lt_or_gt_of_ne (Subtype.coe_ne_coe.mpr hhg) with hhgLT | hghLT
    · have htrunc : HahnSeries.truncLE ((g : ℝ) - (h : ℝ))
          (p : K⟦ℝ⟧) = p := by
        apply HahnSeries.truncLE_eq_self_of_support_subset_Iic
        exact (HahnSeries.Nonpositive.support_subset p).trans fun y hy ↦
          hy.trans (sub_nonneg.mpr hhgLT.le)
      have hgermCoe :
          ((translatedTruncation
              (HahnSeries.translate (h : ℝ) (p : K⟦ℝ⟧)) g : Series K) :
                K⟦ℝ⟧) =
            HahnSeries.translate ((h : ℝ) - (g : ℝ)) (p : K⟦ℝ⟧) := by
        rw [coe_translatedTruncation_translate, htrunc]
      have hpCoeNe : (p : K⟦ℝ⟧) ≠ 0 := by simpa using hp.ne_zero
      have htranslatedNe :
          HahnSeries.translate ((h : ℝ) - (g : ℝ)) (p : K⟦ℝ⟧) ≠ 0 :=
        fun hzero ↦ hpCoeNe ((HahnSeries.translate
          ((h : ℝ) - (g : ℝ))).injective (by simpa using hzero))
      have hgermNe :
          translatedTruncation
            (HahnSeries.translate (h : ℝ) (p : K⟦ℝ⟧)) g ≠ 0 := by
        intro hzero
        apply htranslatedNe
        rw [← hgermCoe]
        exact congrArg Subtype.val hzero
      have hpSup : sSup (p : K⟦ℝ⟧).support = 0 := by
        have hsup := hp.supportSup_eq_zero
        rw [HahnSeries.Nonpositive.supportSup_of_ne hp.ne_zero] at hsup
        change ((sSup (p : K⟦ℝ⟧).support : ℝ) : WithBot ℝ) =
          ((0 : ℝ) : WithBot ℝ) at hsup
        exact WithBot.coe_eq_coe.mp hsup
      have hgermJ : translatedTruncation
          (HahnSeries.translate (h : ℝ) (p : K⟦ℝ⟧)) g ∈
            HahnSeries.Nonpositive.negativeMonomialIdeal K := by
        rw [HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero]
        rw [HahnSeries.Nonpositive.supportSup_of_ne hgermNe]
        change
          ((sSup (((translatedTruncation
            (HahnSeries.translate (h : ℝ) (p : K⟦ℝ⟧)) g : Series K) :
              K⟦ℝ⟧).support) : ℝ) : WithBot ℝ) < ((0 : ℝ) : WithBot ℝ)
        apply WithBot.coe_lt_coe.mpr
        rw [hgermCoe]
        rw [HahnSeries.csSup_support_translate hpCoeNe
          (HahnSeries.Nonpositive.bddAbove_support p), hpSup, add_zero]
        exact sub_neg.mpr hhgLT
      rw [ordinalValue_of_mem_negativeMonomialIdeal hgermJ]
      exact NatOrdinal.wpow_pos alpha
    · apply (ordinalValueDegree_lt_coe_iff _ alpha).mp
      calc
        ordinalValueDegree
            (translatedTruncation
              (HahnSeries.translate (h : ℝ) (p : K⟦ℝ⟧)) g) ≤
            (((translatedTruncation
              (HahnSeries.translate (h : ℝ) (p : K⟦ℝ⟧)) g : Series K) :
                K⟦ℝ⟧).degree) := ordinalValueDegree_le_degree _
        _ = (HahnSeries.truncLE ((g : ℝ) - (h : ℝ))
              (p : K⟦ℝ⟧)).degree := by
          rw [coe_translatedTruncation_translate, HahnSeries.degree_translate]
        _ < (alpha : WithBot NatOrdinal) :=
          hp.degree_truncLE_lt_of_degree_eq hpDegree (sub_neg.mpr hghLT)

private theorem degreeLayerTruncationAt_principalComponentTensorMap (alpha : NatOrdinal)
    (z : PrincipalComponent K alpha ⊗[K] FiniteSupportRing (K := K))
    (g : HahnSeries.Nonpositive.exponentMonoid ℝ) :
    degreeLayerTruncationAt K alpha g
        (principalComponentTensorMap K alpha z) =
      TensorProduct.equivFinsuppOfBasisRight
        (HahnSeries.Nonpositive.finiteSupportBasis (G := ℝ) (K := K)) z g := by
  let basis := HahnSeries.Nonpositive.finiteSupportBasis (G := ℝ) (K := K)
  let coordinates := TensorProduct.equivFinsuppOfBasisRight
    (M := PrincipalComponent K alpha) basis
  let f := coordinates z
  change degreeLayerTruncationAt K alpha g
      (principalComponentTensorMap K alpha z) = f g
  have hz : z = f.sum fun i x ↦ x ⊗ₜ basis i := by
    calc
      z = coordinates.symm f := by simp [f]
      _ = f.sum fun i x ↦ x ⊗ₜ basis i :=
        TensorProduct.equivFinsuppOfBasisRight_symm_apply basis f
  rw [hz]
  induction f using Finsupp.induction with
  | zero => simp
  | single_add a b f ha hb ih =>
      have hzero : ∀ i,
          (0 : PrincipalComponent K alpha) ⊗ₜ[K] basis i = 0 :=
        fun i ↦ TensorProduct.zero_tmul (PrincipalComponent K alpha) (basis i)
      have hadd : ∀ i b₁ b₂,
          (b₁ + b₂ : PrincipalComponent K alpha) ⊗ₜ[K] basis i =
            b₁ ⊗ₜ[K] basis i + b₂ ⊗ₜ[K] basis i :=
        fun i b₁ b₂ ↦ TensorProduct.add_tmul b₁ b₂ (basis i)
      rw [Finsupp.sum_add_index' hzero hadd]
      rw [Finsupp.sum_single_index (hzero a)]
      rw [map_add, map_add, ih]
      rw [HahnSeries.Nonpositive.finiteSupportBasis_apply]
      rw [degreeLayerTruncationAt_principalComponentTensorMap_tmul_monomial]
      rw [Finsupp.add_apply, Finsupp.single_apply]

variable (K) in
private theorem principalComponentTensorMap_injective (alpha : NatOrdinal) :
    Function.Injective (principalComponentTensorMap K alpha) := by
  intro x y hxy
  let basis := HahnSeries.Nonpositive.finiteSupportBasis (G := ℝ) (K := K)
  let coordinates := TensorProduct.equivFinsuppOfBasisRight
    (M := PrincipalComponent K alpha) basis
  apply coordinates.injective
  ext g
  rw [← degreeLayerTruncationAt_principalComponentTensorMap alpha,
    ← degreeLayerTruncationAt_principalComponentTensorMap alpha, hxy]

variable (K) in
/-- The canonical extension-of-scalars equivalence
`P_α ⊗[K] K(ℝ^{≤ 0}) ≃ RV_α` from LM24, Proposition 5.3.1. -/
def principalComponentTensorEquiv (α : NatOrdinal) :
    PrincipalComponent K α ⊗[K] FiniteSupportRing (K := K) ≃ₗ[K]
      (HahnSeries.Nonpositive.degreeValuation K).Component α :=
  LinearEquiv.ofBijective (principalComponentTensorMap K α)
    ⟨principalComponentTensorMap_injective K α,
      principalComponentTensorMap_surjective K α⟩

/-- The extension-of-scalars equivalence has the canonical multiplication map as its forward
linear map. -/
@[simp]
theorem principalComponentTensorEquiv_apply (α : NatOrdinal)
    (z : PrincipalComponent K α ⊗[K] FiniteSupportRing (K := K)) :
    principalComponentTensorEquiv K α z =
      principalComponentTensorMap K α z :=
  (rfl)

/-- On a pure tensor, the extension-of-scalars equivalence is multiplication by the image of
the finite-support factor in the degree-zero residue ring. -/
theorem principalComponentTensorEquiv_tmul (α : NatOrdinal)
    (x : PrincipalComponent K α) (p : FiniteSupportRing (K := K)) :
    principalComponentTensorEquiv K α (x ⊗ₜ p) =
      HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K p •
        principalComponentToHahnDegreeLayer K α x := by
  rw [principalComponentTensorEquiv_apply, principalComponentTensorMap_tmul]

end

end Berarducci
