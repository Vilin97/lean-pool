/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.DerivationIdeal
public import
  LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.TranslatedTruncationInterpolationOnSets

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Prescribing a derivative germ on a discrete set of exponents

The graded derivative of a class of successor degree is the germ of a function supported on the
exact-rank level of a representative. Conversely a function supported on any discrete set of
nonpositive exponents, with homogeneous values of one fixed degree, is such a germ.

This is the integration theorem for a discrete set of cutoffs, stated in the associated graded
ring rather than in one component, which is the form required by the syzygy induction.
-/

universe u v w

open scoped NatOrdinal Topology

open Filter Set HahnSeries

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

open Classical in
/-- **A function supported on a discrete set is a derivative germ.** Prescribed homogeneous values
of degree `ρ` at the points of a discrete set of nonpositive exponents, whose closure adds nothing
near zero, are the graded derivative of a class of degree `ρ + 1`. -/
@[blueprint "lem:prescribed-cantor-bendixson-derivative-discrete-set"
  (phase := "Algebraic independence in graded rings")
  (title := "Prescribing the Cantor--Bendixson derivative on a discrete set")
  (statement := /--
    Let $K$ be a field of characteristic zero and $G$ a nontrivial complete
    ordered abelian group with compatible additive uniformity and order
    topology.  Write $\nu$ for the Cantor--Bendixson degree on
    $K((G^{\leq 0}))$.  Suppose $S\subseteq G^{\leq0}$ is partially well
    ordered and discrete, and that $\overline S\subseteq S$ on some left
    neighbourhood of $0$.  If every $a(\gamma)$ is homogeneous of degree
    $\rho$ in $\operatorname{gr}_\nu$, then there is a homogeneous
    $s\in\operatorname{gr}_\nu$ of degree $\rho+1$ whose
    Cantor--Bendixson derivative agrees near $0$ with
    \[
      \gamma\longmapsto
      \begin{cases}a(\gamma),&\gamma\in S,\\0,&\gamma\notin S.
      \end{cases}
    \]
  -/)
  (proof := /--
    Regard each prescribed value as an element of the degree-$\rho$
    component.  Discreteness supplies pairwise separated left intervals about
    the points of $S$.  Place a representative of $a(\gamma)$ in the interval
    ending at $\gamma$ and sum the resulting Hahn series.  Partial
    well-ordering makes the family summable.  Because the closure of $S$ adds
    no points near $0$, translated truncation at a point of $S$ recovers the
    prescribed class and gives zero elsewhere.  The resulting series has
    degree at most $\rho+1$, and its degree-$(\rho+1)$ class is the required
    $s$ by
    \ref{lem:cantor-bendixson-derivation-successor-formula}.
  -/)]
theorem exists_derivation_eq_of_isDiscrete (ρ : NatOrdinal.{u}) (S : Set G)
    (hSneg : S ⊆ Iic 0) (hSpwo : (Set.univ : Set ↥S).IsPWO) (hSdisc : IsDiscrete S)
    (hnear : ∀ᶠ γ in 𝓝[<] (0 : G), γ ∈ closure S → γ ∈ S)
    (a : G → (ν).AssociatedGraded)
    (ha : ∀ γ, a γ ∈ DirectSum.rangeLof K (ν).Component ρ) :
    ∃ s : (ν).AssociatedGraded, s ∈ DirectSum.rangeLof K (ν).Component (ρ + 1) ∧
      cantorBendixsonGradedDerivation s =
        ((fun γ ↦ if γ ∈ S then a γ else 0) :
          Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) := by
  classical
  -- the prescribed values, as elements of the component
  have hcomp : ∀ i : ↥S, ∃ y : (ν).Component ρ,
      DirectSum.of (ν).Component ρ y = a (i : G) := by
    intro i
    obtain ⟨y, hy⟩ := (DirectSum.mem_rangeLof_iff K (ν).Component ρ (a (i : G))).mp (ha (i : G))
    exact ⟨y, by simpa only [DirectSum.lof_eq_of] using hy⟩
  choose y hy using hcomp
  obtain ⟨c, hc, -, hderiv⟩ :=
    exists_prescribed_components_on_set_of_isDiscrete ρ S hSneg hSpwo hSdisc hnear y
  refine ⟨(ν).homogeneousMk (ρ + 1) ⟨c, ((ν).mem_filtrationLE_iff (ρ + 1) c).mpr hc⟩, ?_, ?_⟩
  · rw [(ν).homogeneousMk_apply]
    exact DirectSum.of_mem_rangeLof K (ν).Component (ρ + 1) _
  · rw [cantorBendixsonGradedDerivation_homogeneousMk_succ ρ rfl]
    calc
      ((fun γ ↦ DirectSum.of (ν).Component ρ (cantorBendixsonDerivAt ρ c γ)) :
            Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) =
          Filter.Germ.mapLinear (DirectSum.of (ν).Component ρ).toIntLinearMap
            (cantorBendixsonLayerDeriv ρ
              ((ν).componentMk (ρ + 1)
                ⟨c, ((ν).mem_filtrationLE_iff (ρ + 1) c).mpr hc⟩)) := by
            rw [cantorBendixsonLayerDeriv_componentMk, Filter.Germ.mapLinear_coe]
            rfl
      _ = Filter.Germ.mapLinear (DirectSum.of (ν).Component ρ).toIntLinearMap
            (((fun γ ↦ if h : γ ∈ S then y ⟨γ, h⟩ else 0) :
              Filter.Germ (𝓝[<] (0 : G)) ((ν).Component ρ))) := congrArg _ hderiv
      _ = _ := by
        rw [Filter.Germ.mapLinear_coe, Filter.Germ.coe_eq]
        refine Filter.Eventually.of_forall fun γ ↦ ?_
        by_cases hγ : γ ∈ S
        · simp only [dite_eq_left hγ, ite_eq_left hγ, Function.comp_apply]
          exact hy ⟨γ, hγ⟩
        · simp only [dite_eq_right hγ, ite_eq_right hγ, Function.comp_apply, map_zero]

end HahnSeries.Nonpositive

end
