/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Scalar
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.PrincipalGraded
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.CantorBendixsonRank

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# The subring $\widehat{\mathrm P}$ and Cantor–Bendixson degree

For real exponents, Berarducci's ordinal value is `omega` raised to the Cantor–Bendixson rank of
zero in the closed support, so its Cantor degree is that rank. Consequently `P̂`
is canonically isomorphic to the associated graded algebra of the Cantor–Bendixson degree. The
isomorphism preserves every homogeneous component and therefore carries minimal homogeneous
generating systems to minimal generating systems.
-/

universe v w

open scoped DirectSum HahnSeries NatOrdinal

open Berarducci HahnSeries

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K]

omit [CharZero K] in
private theorem principalSubring_algebraMap_eq_initialForm (k : K) :
    algebraMap K (PrincipalSubring K) k =
      (ordinalValueDegreeValuation K).initialForm (HahnSeries.Nonpositive.C k) := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [principalSubring_algebraMap_apply, principalComponentScalarHom_apply,
      principalComponentMk_eq_componentMk, ← MaxAddDegree.homogeneousMk_apply]
    apply MaxAddDegree.homogeneousMk_eq_initialForm_of_degree_eq
    rw [ordinalValueDegreeValuation_apply]
    simpa only [WithBot.coe_zero] using ordinalValueDegree_C_of_ne (K := K) hk

private theorem cantorBendixson_algebraMap_eq_initialForm (k : K) :
    algebraMap K
        (HahnSeries.Nonpositive.cantorBendixsonDegreeValuation
          (G := ℝ) (R := K)).AssociatedGraded k =
      (HahnSeries.Nonpositive.cantorBendixsonDegreeValuation
        (G := ℝ) (R := K)).initialForm (HahnSeries.Nonpositive.C k) := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [HahnSeries.Nonpositive.cantorBendixson_algebraMap_apply,
      HahnSeries.Nonpositive.cantorBendixsonLayerScalarHom_apply,
      ← MaxAddDegree.homogeneousMk_apply]
    apply MaxAddDegree.homogeneousMk_eq_initialForm_of_degree_eq
    exact HahnSeries.Nonpositive.degree_C_of_ne k hk

/-- The subring `P̂` is canonically the associated graded algebra defined by the
Cantor–Bendixson degree. -/
@[expose, blueprint "lem:principal-subring-cantor-bendixson"
  (phase := "Principal RV-elements")
  (title := "Cantor--Bendixson grading of $\\widehat{\\mathrm P}$")
  (statement := /--
    Let $\widehat{\mathrm P}$ be the subring of principal elements of
    $\widehat{\mathrm{RV}}$, equivalently the associated graded $K$-algebra
    for $\deg_J$. Define
    \[
      \delta_{\mathrm{CB}}(b)=
      \begin{cases}
        -\infty, & 0\notin\mathrm{cl}(\operatorname{supp}(b)),\\
        \operatorname{rk}_{\mathrm{CB},\mathrm{cl}(\operatorname{supp}(b))}(0),
          & 0\in\mathrm{cl}(\operatorname{supp}(b)).
      \end{cases}
    \]
    There is a canonical isomorphism of $K$-algebras
    \[
      \widehat{\mathrm P}\simeq_K
        \operatorname{gr}_{\delta_{\mathrm{CB}}}K((\mathbb R^{\le0})).
    \]
  -/)
  (proof := /--
  The subring $\widehat{\mathrm P}$ is the associated graded algebra for $\deg_J$.
  \ref{lem:ordinal-value-degree-is-cantor-bendixson-rank} identifies
  $\deg_J$ with $\delta_{\mathrm{CB}}$, so the identity on series induces a
  ring isomorphism between the associated graded algebras. Both scalar
  embeddings send $k\in K$ to the initial form of the constant series $k$;
  hence this is an isomorphism of $K$-algebras.
  -/)]
def principalSubringCantorBendixsonAlgEquiv : PrincipalSubring K ≃ₐ[K]
    (HahnSeries.Nonpositive.cantorBendixsonDegreeValuation
      (G := ℝ) (R := K)).AssociatedGraded where
  toRingEquiv := (ordinalValueDegreeValuation K).associatedGradedCongr
    (ordinalValueDegreeValuation_eq_cantorBendixsonDegreeValuation (K := K))
  commutes' k := by
    rw [principalSubring_algebraMap_eq_initialForm, cantorBendixson_algebraMap_eq_initialForm]
    exact MaxAddDegree.associatedGradedCongr_initialForm _ _

/-- The underlying map is transport along equality of the two degree functions. -/
theorem principalSubringCantorBendixsonAlgEquiv_apply (x : PrincipalSubring K) :
    principalSubringCantorBendixsonAlgEquiv x =
      (ordinalValueDegreeValuation K).associatedGradedCongr
        (ordinalValueDegreeValuation_eq_cantorBendixsonDegreeValuation (K := K)) x :=
  rfl

/-- The canonical equivalence preserves each homogeneous component. -/
theorem principalSubringCantorBendixsonAlgEquiv_mem_grading
    (n : NatOrdinal) (x : PrincipalSubring K) :
    x ∈ principalGrading K n ↔
      principalSubringCantorBendixsonAlgEquiv x ∈ DirectSum.rangeLof K
        (HahnSeries.Nonpositive.cantorBendixsonDegreeValuation
          (G := ℝ) (R := K)).Component n := by
  let ν := ordinalValueDegreeValuation K
  let δ := HahnSeries.Nonpositive.cantorBendixsonDegreeValuation (G := ℝ) (R := K)
  let hν : ν = δ := ordinalValueDegreeValuation_eq_cantorBendixsonDegreeValuation
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (DirectSum.mem_rangeLof_iff K ν.Component n x).mp hx
    rw [DirectSum.lof_eq_of] at ha
    subst x
    rw [show principalSubringCantorBendixsonAlgEquiv (DirectSum.of ν.Component n a) =
      ν.associatedGradedCongr hν (DirectSum.of ν.Component n a) by rfl,
      ν.associatedGradedCongr_of hν n a]
    exact DirectSum.of_mem_rangeLof K δ.Component n (ν.componentCongr hν n a)
  · intro hx
    obtain ⟨a, ha⟩ := (DirectSum.mem_rangeLof_iff K δ.Component n
      (principalSubringCantorBendixsonAlgEquiv x)).mp hx
    rw [DirectSum.lof_eq_of] at ha
    have hxa : x = DirectSum.of ν.Component n ((ν.componentCongr hν n).symm a) := by
      apply (principalSubringCantorBendixsonAlgEquiv (K := K)).injective
      rw [← ha]
      change DirectSum.of δ.Component n a =
        ν.associatedGradedCongr hν
          (DirectSum.of ν.Component n ((ν.componentCongr hν n).symm a))
      rw [ν.associatedGradedCongr_of]
      congr 2
      exact (ν.componentCongr hν n).apply_symm_apply a |>.symm
    rw [hxa]
    exact DirectSum.of_mem_rangeLof K ν.Component n _

variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

/-- Evaluation commutes with the canonical graded-algebra equivalence. -/
theorem principalSubringCantorBendixsonAlgEquiv_aeval (F : MvPolynomial ι K) :
    principalSubringCantorBendixsonAlgEquiv (MvPolynomial.aeval x F) =
      MvPolynomial.aeval (fun i ↦ principalSubringCantorBendixsonAlgEquiv (x i)) F := by
  change principalSubringCantorBendixsonAlgEquiv.toAlgHom (MvPolynomial.aeval x F) = _
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1

/-- Degreewise injectivity is preserved by the canonical graded-algebra equivalence. -/
theorem principalSubringCantorBendixson_injectiveAt_iff (n : NatOrdinal) :
    OrdinalGraded.InjectiveAt K wt x n ↔
      OrdinalGraded.InjectiveAt K wt
        (fun i ↦ principalSubringCantorBendixsonAlgEquiv (x i)) n := by
  constructor
  · intro h
    rw [OrdinalGraded.injectiveAt_iff] at h ⊢
    intro F hF hzero
    apply h F hF
    apply principalSubringCantorBendixsonAlgEquiv.injective
    rw [map_zero, principalSubringCantorBendixsonAlgEquiv_aeval, hzero]
  · intro h
    rw [OrdinalGraded.injectiveAt_iff] at h ⊢
    intro F hF hzero
    apply h F hF
    rw [← principalSubringCantorBendixsonAlgEquiv_aeval, hzero, map_zero]

/-- A minimal system in `P̂` remains minimal in the equivalent graded algebra. -/
theorem minimalSystem_cantorBendixson
    (hx : OrdinalGraded.IsMinimalSystem (principalGrading K) wt x) :
    OrdinalGraded.IsMinimalSystem
      (DirectSum.rangeLof K (HahnSeries.Nonpositive.cantorBendixsonDegreeValuation
        (G := ℝ) (R := K)).Component)
      wt (fun i ↦ principalSubringCantorBendixsonAlgEquiv (x i)) :=
  hx.map_algEquiv principalSubringCantorBendixsonAlgEquiv
    principalSubringCantorBendixsonAlgEquiv_mem_grading

end Berarducci
