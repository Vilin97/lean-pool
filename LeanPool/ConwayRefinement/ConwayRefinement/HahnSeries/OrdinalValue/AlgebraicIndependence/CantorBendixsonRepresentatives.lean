/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.LiftFamily
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.CantorBendixsonGrading
public import
  LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.PrincipalRepresentatives

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Principal representatives for the Cantor–Bendixson degree

The canonical identification of the two degree functions leaves the representing Hahn series
unchanged. Thus representatives for `P̂` give representatives for the associated graded ring
defined by the Cantor–Bendixson degree, and the series remain principal.
-/

universe v w

open scoped HahnSeries NatOrdinal

open Berarducci HahnSeries

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K]
variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

namespace Lifts

/-- Reinterpret principal-subring lifts in the equivalent Cantor–Bendixson graded algebra. -/
@[expose] def cantorBendixson (σ : Lifts wt x) : HahnSeries.Nonpositive.LiftFamily wt
    (fun i ↦ principalSubringCantorBendixsonAlgEquiv (x i)) where
  lift := σ.lift
  represents i := by
    simpa only [principalSubringCantorBendixsonAlgEquiv_apply] using
      (σ.represents i).congr
        (ordinalValueDegreeValuation_eq_cantorBendixsonDegreeValuation (K := K))

@[simp]
theorem cantorBendixson_lift (σ : Lifts wt x) (i : ι) : σ.cantorBendixson.lift i = σ.lift i :=
  rfl

omit [CharZero K] in
/-- The generic and real translated truncations are the same Hahn series. -/
theorem translatedTruncLE_eq_translatedTruncation (b : Series K) (y : ℝ) :
    HahnSeries.Nonpositive.translatedTruncLE y b =
      translatedTruncation ((b : Series K) : K⟦ℝ⟧) y := by
  apply Subtype.ext
  rw [HahnSeries.Nonpositive.coe_translatedTruncLE,
    Berarducci.coe_translatedTruncation]

/-- Principal real Hahn-series representatives remain principal under the graded-algebra
equivalence. -/
@[blueprint "lem:principal-representatives-cantor-bendixson"
  (phase := "Principal RV-elements")
  (title := "Principal series representatives for the Cantor--Bendixson grading")
  (statement := /--
    Let $K$ be a field of characteristic zero. For each $i\in I$, let
    $x_i\in\mathrm P_{w_i}\subseteq\widehat{\mathrm P}$ and choose a principal
    series $b_i$ of degree $w_i$ representing $x_i$. Let
    $\delta_{\mathrm{CB}}$ be the Cantor--Bendixson degree identified with
    $\deg_J$ by
    \ref{lem:ordinal-value-degree-is-cantor-bendixson-rank}, and identify
    $\widehat{\mathrm P}$ with
    $\operatorname{gr}_{\delta_{\mathrm{CB}}}
      K((\mathbb R^{\le0}))$
    by \ref{lem:principal-subring-cantor-bendixson}.

    The same series $b_i$ represent the images of the $x_i$ under this
    isomorphism, and, for every $i\in I$,
    \[
      \delta_{\mathrm{CB}}(b_i)=w_i,\qquad
      \delta_{\mathrm{CB}}(b_i^{|\gamma})<w_i
      \quad\text{for every }\gamma<0.
    \]
  -/)
  (proof := /--
    By \ref{lem:principal-subring-cantor-bendixson}, the isomorphism between
    $\widehat{\mathrm P}$ and the Cantor--Bendixson associated graded ring is
    induced by the identity on representing series. Thus the $b_i$ still
    represent the $x_i$, and
    $\delta_{\mathrm{CB}}(b_i)=\deg_J(b_i)=w_i$. For $\gamma<0$,
    \ref{lem:principal-truncations-lower-value} gives
    \[
      v_J(b_i^{|\gamma})<\omega^{w_i}.
    \]
    Under the same identification this is precisely
    $\delta_{\mathrm{CB}}(b_i^{|\gamma})<w_i$.
  -/)]
theorem IsPrincipal.cantorBendixson {σ : Lifts wt x} (hσ : σ.IsPrincipal) :
    HahnSeries.Nonpositive.LiftFamily.HasLowerTruncationDegrees σ.cantorBendixson := by
  rw [HahnSeries.Nonpositive.LiftFamily.hasLowerTruncationDegrees_iff]
  intro i
  rw [HahnSeries.Nonpositive.hasLowerTruncationDegree_iff]
  have hσi := (isPrincipal_iff σ).mp hσ i
  constructor
  · rw [cantorBendixson_lift]
    rw [← ordinalValueDegreeValuation_eq_cantorBendixsonDegreeValuation,
      ordinalValueDegreeValuation_apply]
    rw [ordinalValueDegree_eq_degree_of_isPrincipal hσi.1, hσi.2]
  · intro y hy
    rw [cantorBendixson_lift]
    change HahnSeries.Nonpositive.cantorBendixsonDegreeValuation
      (HahnSeries.Nonpositive.translatedTruncLE y (σ.lift i)) < wt i
    rw [← ordinalValueDegreeValuation_eq_cantorBendixsonDegreeValuation,
      ordinalValueDegreeValuation_apply]
    apply (ordinalValueDegree_lt_coe_iff _ _).mpr
    rw [translatedTruncLE_eq_translatedTruncation]
    exact hσ.ordinalValue_translatedTruncation_lift_lt i hy

end Lifts

end Berarducci
