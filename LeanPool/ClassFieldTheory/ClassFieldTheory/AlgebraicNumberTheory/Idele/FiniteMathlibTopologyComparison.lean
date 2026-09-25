/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.RestrictedProductUnitsTopology
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
/-!
# The finite idèle topology and adele units

The algebraic equivalence from finite idèles to units of the finite adele ring
is continuous for the restricted-product topology on idèles and the graph
topology on units.  Both the value and inverse-value maps are induced by
continuous maps on local factors.
-/

@[expose] public section

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- The finite restricted-product idèles and finite adele units are
canonically isomorphic as topological groups. -/
noncomputable def finiteEquivFiniteAdeleUnitsContinuousMulEquiv :
    FiniteIdeleGroup K ≃ₜ*
      (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ :=
  (RestrictedProduct.unitsContinuousMulEquiv
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (B := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletionIntegers K)
    (fun _ => Valued.isOpen_valuationSubring _)).symm

/-- The topological and algebraic finite-idèle comparisons agree pointwise. -/
@[simp]
theorem finiteEquivFiniteAdeleUnitsContinuousMulEquiv_apply
    (a : FiniteIdeleGroup K) :
    finiteEquivFiniteAdeleUnitsContinuousMulEquiv K a =
      finiteEquivFiniteAdeleUnits a :=
  rfl

/-- The algebraic finite-idèle comparison is continuous in the forward
direction. -/
theorem continuous_finiteEquivFiniteAdeleUnits :
    Continuous (finiteEquivFiniteAdeleUnits (K := K)) := by
  let hval : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Set.MapsTo (fun u : (v.adicCompletion K)ˣ =>
        (u : v.adicCompletion K))
        ((v.adicCompletionIntegers K).units : Set (v.adicCompletion K)ˣ)
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Filter.Eventually.of_forall (fun _ u hu => hu.1)
  let hinv : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Set.MapsTo (fun u : (v.adicCompletion K)ˣ =>
        ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))
        ((v.adicCompletionIntegers K).units : Set (v.adicCompletion K)ˣ)
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Filter.Eventually.of_forall (fun _ u hu => hu.2)
  apply Units.continuous_iff.mpr
  constructor
  · have h : Continuous (RestrictedProduct.mapAlong
        (fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletion K)ˣ)
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (𝓕₁ := Filter.cofinite) (𝓕₂ := Filter.cofinite)
        (A₁ := fun v => ((v.adicCompletionIntegers K).units :
          Set (v.adicCompletion K)ˣ))
        (A₂ := fun v => (v.adicCompletionIntegers K :
          Set (v.adicCompletion K)))
        id Filter.tendsto_id
        (fun v (u : (v.adicCompletion K)ˣ) =>
          (u : v.adicCompletion K)) hval) := by
      apply RestrictedProduct.mapAlong_continuous
      intro v
      exact Units.continuous_val
    exact h.congr (fun a => by
      apply RestrictedProduct.ext
      intro v
      rfl)
  · have h : Continuous (RestrictedProduct.mapAlong
        (fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletion K)ˣ)
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (𝓕₁ := Filter.cofinite) (𝓕₂ := Filter.cofinite)
        (A₁ := fun v => ((v.adicCompletionIntegers K).units :
          Set (v.adicCompletion K)ˣ))
        (A₂ := fun v => (v.adicCompletionIntegers K :
          Set (v.adicCompletion K)))
        id Filter.tendsto_id
        (fun v (u : (v.adicCompletion K)ˣ) =>
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) hinv) := by
      apply RestrictedProduct.mapAlong_continuous
      intro v
      exact Units.continuous_coe_inv
    exact h.congr (fun a => by
      apply RestrictedProduct.ext
      intro v
      rfl)

/-- The algebraic equivalence from restricted-product idèles to adele units
is continuous in the forward direction. -/
theorem continuous_equivAdeleRingUnits :
    Continuous (equivAdeleRingUnits (K := K)) := by
  have hprod : Continuous (fun a : IdeleGroup K =>
      (a.1, finiteEquivFiniteAdeleUnits (K := K) a.2)) :=
    continuous_fst.prodMk
      ((continuous_finiteEquivFiniteAdeleUnits K).comp continuous_snd)
  exact (Homeomorph.prodUnits.symm.continuous.comp hprod).congr
    (fun _ => rfl)

/-- The full restricted-product idèle group is canonically isomorphic to
Mathlib's adele-unit idèle group as a topological group. -/
noncomputable def equivAdeleRingUnitsContinuousMulEquiv :
    IdeleGroup K ≃ₜ* (NumberField.AdeleRing (𝓞 K) K)ˣ := by
  let e := finiteEquivFiniteAdeleUnitsContinuousMulEquiv K
  refine
    { toMulEquiv := equivAdeleRingUnits (K := K)
      continuous_toFun := continuous_equivAdeleRingUnits K
      continuous_invFun := ?_ }
  have hprod : Continuous (fun a : (NumberField.AdeleRing (𝓞 K) K)ˣ =>
      ((Homeomorph.prodUnits a).1,
        e.symm (Homeomorph.prodUnits a).2)) :=
    (Homeomorph.prodUnits.continuous.fst).prodMk
      (e.symm.continuous.comp Homeomorph.prodUnits.continuous.snd)
  exact hprod.congr (fun _ => rfl)

end IdeleGroup
