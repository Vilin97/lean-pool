/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.HomogeneousSpan
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Scalar
public import
  LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.TranslatedTruncationInterpolation

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Successor ideal integration for the Cantor–Bendixson derivation

Prescribed homogeneous coefficient germs on one exact Cantor–Bendixson rank can be integrated at
arbitrary cofinality. This module combines that construction with homogeneous ideal
decomposition and the injective successor derivation.
-/

public noncomputable section

open Set Filter Topology
open scoped DirectSum NatOrdinal

universe u v w

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

/-- A finite pointwise sum represents the sum of the corresponding filter germs. -/
theorem germ_coe_sum {ι : Type w} [Fintype ι] (g : ι → G → (ν).AssociatedGraded) :
    ((fun γ ↦ ∑ i, g i γ : G → (ν).AssociatedGraded) :
      Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) =
        ∑ i, ((g i : G → (ν).AssociatedGraded) :
          Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) := by
  have hfun : (fun γ ↦ ∑ i, g i γ : G → (ν).AssociatedGraded) = ∑ i, g i := by
    ext γ
    simp only [Finset.sum_apply]
  rw [hfun]
  exact map_sum (Filter.Germ.coeRingHom (𝓝[<] (0 : G))) g Finset.univ

/-- The graded derivative vanishes on a homogeneous element whose grade has zero finite Cantor
coefficient. -/
theorem cantorBendixsonGradedDerivation_eq_zero_of_constantCoeff_eq_zero
    {c : NatOrdinal.{u}} (hc : c.constantCoeff = 0) {q : (ν).AssociatedGraded}
    (hq : q ∈ DirectSum.rangeLof K (ν).Component c) :
    cantorBendixsonGradedDerivation q = 0 := by
  obtain ⟨a, ha⟩ := (DirectSum.mem_rangeLof_iff K (ν).Component c q).mp hq
  rw [DirectSum.lof_eq_of] at ha
  rw [← ha, cantorBendixsonGradedDerivation_of,
    cantorBendixsonHomogeneousDerivation_limit c hc, AddMonoidHom.zero_apply]

open Classical in
/-- A homogeneous function prescribed on the exact-rank points of a successor representative is
the graded derivative of a homogeneous class. The product with a fixed homogeneous element has
the expected successor grade. -/
@[blueprint "lem:prescribed-cantor-bendixson-derivative-exact-rank"
  (phase := "Algebraic independence in graded rings")
  (title := "Prescribing the Cantor--Bendixson derivative on one exact-rank set")
  (statement := /--
    Let $q\in\operatorname{gr}_\nu$ be homogeneous of degree $c$, and let a
    series $p$ have Cantor--Bendixson degree at most $\delta+1$.  Prescribe at
    every point of exact rank $\delta$ in
    $\overline{\operatorname{supp}(p)}$ a homogeneous class $a_\gamma$ whose
    degree $\beta$ satisfies $\beta+c=\delta$, taking $a_\gamma=0$ when no
    such $\beta$ exists.  Then there is $z\in\operatorname{gr}_\nu$ such that
    $qz$ is homogeneous of degree $\delta+1$ and the Cantor--Bendixson
    derivative of $z$ agrees near $0$ with $a_\gamma$ on that exact-rank set
    and is zero away from it.
  -/)
  (proof := /--
    If no $\beta$ satisfies $\beta+c=\delta$, take $z=0$.  Otherwise, all
    prescribed values have the same degree $\beta$.  Choose component
    representatives and place them on pairwise separated left intervals
    ending at the exact-rank points of $p$.  Their Hahn sum has degree at most
    $\beta+1$ and has the prescribed translated-truncation classes.  Its
    degree-$(\beta+1)$ class is $z$; the graded product has degree
    $c+(\beta+1)=\delta+1$, and
    \ref{lem:cantor-bendixson-derivation-successor-formula} gives the required
    near-zero equality.
  -/)]
theorem exists_grading_mul_and_derivation_eq_rankLevel
    {δ c : NatOrdinal.{u}} {q : (ν).AssociatedGraded}
    (hq : q ∈ DirectSum.rangeLof K (ν).Component c)
    (p : Nonpositive G K) (hp : ν p ≤ (δ + 1 : NatOrdinal))
    (a : {x // x ∈ (p : HahnSeries G K).closedSupport ∧
      (p : HahnSeries G K).closedSupport.cantorBendixsonRank
        (p : HahnSeries G K).closedSupport_isPWO x = δ.val} → (ν).AssociatedGraded)
    (ha : ∀ i β, β + c = δ →
      a i ∈ DirectSum.rangeLof K (ν).Component β)
    (ha0 : ∀ i, (¬ ∃ β, β + c = δ) → a i = 0) :
    ∃ z : (ν).AssociatedGraded,
      q * z ∈ DirectSum.rangeLof K (ν).Component (δ + 1) ∧
      cantorBendixsonGradedDerivation z =
        ((fun γ ↦ if h : γ ∈ (p : HahnSeries G K).closedSupport ∧
            (p : HahnSeries G K).closedSupport.cantorBendixsonRank
              (p : HahnSeries G K).closedSupport_isPWO γ = δ.val then
            a ⟨γ, h⟩ else 0) :
          Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) := by
  classical
  by_cases hβ : ∃ β, β + c = δ
  · obtain ⟨β, hβ⟩ := hβ
    have hcomponent : ∀ i, ∃ b : (ν).Component β,
        DirectSum.of (ν).Component β b = a i := by
      intro i
      obtain ⟨b, hb⟩ := (DirectSum.mem_rangeLof_iff K (ν).Component β (a i)).mp
        (ha i β hβ)
      exact ⟨b, by simpa only [DirectSum.lof_eq_of] using hb⟩
    choose b hb using hcomponent
    obtain ⟨s, hs, -, hderiv⟩ := exists_prescribed_components_on_rankLevel δ β p hp b
    let z : (ν).AssociatedGraded :=
      (ν).homogeneousMk (β + 1)
        ⟨s, ((ν).mem_filtrationLE_iff (β + 1) s).mpr hs⟩
    refine ⟨z, ?_, ?_⟩
    · have hz : z ∈ DirectSum.rangeLof K (ν).Component (β + 1) := by
        dsimp only [z]
        rw [(ν).homogeneousMk_apply]
        exact DirectSum.of_mem_rangeLof K (ν).Component (β + 1) _
      have hmul := SetLike.mul_mem_graded hq hz
      have hgrade : c + (β + 1) = δ + 1 := by
        rw [← hβ]
        ac_rfl
      rwa [hgrade] at hmul
    · rw [show z = (ν).homogeneousMk (β + 1)
          ⟨s, ((ν).mem_filtrationLE_iff (β + 1) s).mpr hs⟩ from rfl,
        cantorBendixsonGradedDerivation_homogeneousMk_succ β rfl]
      calc
        ((fun γ ↦ DirectSum.of (ν).Component β
            (cantorBendixsonDerivAt β s γ)) :
              Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) =
            Filter.Germ.mapLinear (DirectSum.of (ν).Component β).toIntLinearMap
              (cantorBendixsonLayerDeriv β
                ((ν).componentMk (β + 1)
                  ⟨s, ((ν).mem_filtrationLE_iff (β + 1) s).mpr hs⟩)) := by
              rw [cantorBendixsonLayerDeriv_componentMk, Filter.Germ.mapLinear_coe]
              rfl
        _ = Filter.Germ.mapLinear (DirectSum.of (ν).Component β).toIntLinearMap
              (((fun γ ↦ if h : γ ∈ (p : HahnSeries G K).closedSupport ∧
                  (p : HahnSeries G K).closedSupport.cantorBendixsonRank
                    (p : HahnSeries G K).closedSupport_isPWO γ = δ.val then
                  b ⟨γ, h⟩ else 0) :
                Filter.Germ (𝓝[<] (0 : G)) ((ν).Component β))) :=
              congrArg _ hderiv
        _ = _ := by
          rw [Filter.Germ.mapLinear_coe, Filter.Germ.coe_eq]
          exact Filter.Eventually.of_forall fun γ ↦ by
            by_cases hγ : γ ∈ (p : HahnSeries G K).closedSupport ∧
                (p : HahnSeries G K).closedSupport.cantorBendixsonRank
                  (p : HahnSeries G K).closedSupport_isPWO γ = δ.val
            · simp only [dite_eq_left hγ, Function.comp_apply]
              change DirectSum.of (ν).Component β (b ⟨γ, hγ⟩) = a ⟨γ, hγ⟩
              exact hb ⟨γ, hγ⟩
            · simp only [dite_eq_right hγ, Function.comp_apply, map_zero]
  · refine ⟨0, ?_, ?_⟩
    · rw [mul_zero]
      exact zero_mem _
    · rw [map_zero, ← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
      exact Filter.Eventually.of_forall fun γ ↦ by
        by_cases hγ : γ ∈ (p : HahnSeries G K).closedSupport ∧
            (p : HahnSeries G K).closedSupport.cantorBendixsonRank
              (p : HahnSeries G K).closedSupport_isPWO γ = δ.val
        · simp only [Pi.zero_apply, dite_eq_left hγ, ha0 ⟨γ, hγ⟩ hβ]
        · simp only [Pi.zero_apply, dite_eq_right hγ]

open Classical in
/-- Ideal membership of a successor homogeneous class follows from pointwise ideal membership
of its Cantor–Bendixson derivative germ. -/
@[blueprint "lem:successor-ideal-membership-from-cantor-bendixson-derivative"
  (phase := "Algebraic independence in graded rings")
  (title := "The derivative criterion for successor ideal membership")
  (statement := /--
    Let $(q_j)$ be a finite homogeneous family in $\operatorname{gr}_\nu$, of
    degrees $c_j$ with zero constant Cantor coefficient.  Let $x$ be
    homogeneous of degree $\delta+1$.  If the Cantor--Bendixson derivative of
    $x$ is represented near $0$ by a function $f$ satisfying
    \[
      f(\gamma)\in(q_j:j)\qquad\text{for every }\gamma\in G,
    \]
    then $x\in(q_j:j)$.
  -/)
  (proof := /--
    Decompose each $f(\gamma)$ homogeneously in the generators $q_j$ using
    \ref{lem:homogeneous-element-of-generated-ideal}.  On the exact-rank set
    of a representative of $x$, apply
    \ref{lem:prescribed-cantor-bendixson-derivative-exact-rank} to each
    coefficient.  The resulting classes $z_j$ make
    $y=\sum_jq_jz_j$ homogeneous of degree $\delta+1$ and give $x$ and $y$
    the same Cantor--Bendixson derivative near $0$.  The derivative is
    injective in successor degree, so $x=y\in(q_j:j)$.  Products are
    differentiated using
    \ref{lem:cantor-bendixson-derivation-leibniz}.
  -/)]
theorem mem_span_of_cantorBendixsonGradedDerivation_eq_coe
    {ι : Type w} [Finite ι]
    {q : ι → (ν).AssociatedGraded} {c : ι → NatOrdinal.{u}}
    (hq : ∀ j, q j ∈ DirectSum.rangeLof K (ν).Component (c j))
    (hc : ∀ j, (c j).constantCoeff = 0)
    {δ : NatOrdinal.{u}} {x : (ν).AssociatedGraded}
    (hx : x ∈ DirectSum.rangeLof K (ν).Component (δ + 1))
    {f : G → (ν).AssociatedGraded}
    (hf : ∀ γ, f γ ∈ Ideal.span (Set.range q))
    (hD : cantorBendixsonGradedDerivation x =
      (f : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded)) :
    x ∈ Ideal.span (Set.range q) := by
  classical
  letI := Fintype.ofFinite ι
  obtain ⟨xδ, hxδ⟩ :=
    (DirectSum.mem_rangeLof_iff K (ν).Component (δ + 1) x).mp hx
  rw [DirectSum.lof_eq_of] at hxδ
  rw [← hxδ]
  induction xδ using MaxAddDegree.componentInductionOn with
  | H p =>
      have hp : ν (p : Nonpositive G K) ≤ (δ + 1 : NatOrdinal) :=
        ((ν).mem_filtrationLE_iff (δ + 1) _).mp p.property
      have hDrep : cantorBendixsonGradedDerivation
          (DirectSum.of (ν).Component (δ + 1) ((ν).componentMk (δ + 1) p)) =
          ((fun γ ↦ DirectSum.of (ν).Component δ
            (cantorBendixsonDerivAt δ (p : Nonpositive G K) γ)) :
              Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) := by
        rw [← (ν).homogeneousMk_apply,
          cantorBendixsonGradedDerivation_homogeneousMk_succ δ rfl]
      have hD' : cantorBendixsonGradedDerivation
          (DirectSum.of (ν).Component (δ + 1) ((ν).componentMk (δ + 1) p)) =
          (f : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) := by
        rw [hxδ]
        exact hD
      have hevent : ∀ᶠ γ in 𝓝[<] (0 : G),
          DirectSum.of (ν).Component δ
              (cantorBendixsonDerivAt δ (p : Nonpositive G K) γ) = f γ := by
        rw [hDrep] at hD'
        exact Filter.Germ.coe_eq.mp hD'
      let good : Set G := {γ | DirectSum.of (ν).Component δ
        (cantorBendixsonDerivAt δ (p : Nonpositive G K) γ) = f γ}
      have hgood : ∀ᶠ γ in 𝓝[<] (0 : G), γ ∈ good := hevent
      let I := {γ // γ ∈ (p : HahnSeries G K).closedSupport ∧
        (p : HahnSeries G K).closedSupport.cantorBendixsonRank
          (p : HahnSeries G K).closedSupport_isPWO γ = δ.val}
      let a : I → (ν).AssociatedGraded := fun i ↦
        if (i : G) ∈ good then f i else 0
      have haGrade : ∀ i, a i ∈ DirectSum.rangeLof K (ν).Component δ := by
        intro i
        by_cases hi : (i : G) ∈ good
        · change (if (i : G) ∈ good then f i else 0) ∈
            DirectSum.rangeLof K (ν).Component δ
          rw [ite_eq_left hi, ← hi]
          exact DirectSum.of_mem_rangeLof K (ν).Component δ _
        · change (if (i : G) ∈ good then f i else 0) ∈
            DirectSum.rangeLof K (ν).Component δ
          rw [ite_eq_right hi]
          exact zero_mem _
      have haIdeal : ∀ i, a i ∈ Ideal.span (Set.range q) := by
        intro i
        by_cases hi : (i : G) ∈ good
        · change (if (i : G) ∈ good then f i else 0) ∈ Ideal.span (Set.range q)
          rw [ite_eq_left hi]
          exact hf i
        · change (if (i : G) ∈ good then f i else 0) ∈ Ideal.span (Set.range q)
          rw [ite_eq_right hi]
          exact Ideal.zero_mem _
      have hdec := fun i ↦ OrdinalGraded.exists_eq_sum_mul_of_mem_span
        (𝒜 := DirectSum.rangeLof K (ν).Component) hq (haGrade i) (haIdeal i)
      choose u hu hu0 hsum using hdec
      have hreal := fun j ↦ exists_grading_mul_and_derivation_eq_rankLevel
        (hq j) (p : Nonpositive G K) hp (fun i ↦ u i j)
        (fun i β hβ ↦ hu i j β hβ) (fun i hnone ↦ hu0 i j hnone)
      choose z hz hDz using hreal
      let y : (ν).AssociatedGraded := ∑ j, q j * z j
      have hy : y ∈ DirectSum.rangeLof K (ν).Component (δ + 1) := by
        exact sum_mem fun j _ ↦ hz j
      have hDy : cantorBendixsonGradedDerivation y =
          ((fun γ ↦ ∑ j, q j *
            (if h : γ ∈ (p : HahnSeries G K).closedSupport ∧
                (p : HahnSeries G K).closedSupport.cantorBendixsonRank
                  (p : HahnSeries G K).closedSupport_isPWO γ = δ.val then
              u ⟨γ, h⟩ j else 0)) :
            Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) := by
        dsimp only [y]
        rw [map_sum, germ_coe_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [cantorBendixsonGradedDerivation_mul,
          cantorBendixsonGradedDerivation_eq_zero_of_constantCoeff_eq_zero
            (hc j) (hq j), zero_mul, zero_add, hDz j]
        rfl
      have hDxy : cantorBendixsonGradedDerivation
          (DirectSum.of (ν).Component (δ + 1) ((ν).componentMk (δ + 1) p)) =
          cantorBendixsonGradedDerivation y := by
        rw [hDrep, hDy, Filter.Germ.coe_eq]
        filter_upwards [hgood, eventually_degree_translatedTruncLE_le
          (p : Nonpositive G K) δ hp] with γ hγgood hγdegree
        by_cases hγ : γ ∈ (p : HahnSeries G K).closedSupport ∧
            (p : HahnSeries G K).closedSupport.cantorBendixsonRank
              (p : HahnSeries G K).closedSupport_isPWO γ = δ.val
        · simp only [dite_eq_left hγ]
          calc
            DirectSum.of (ν).Component δ
                (cantorBendixsonDerivAt δ (p : Nonpositive G K) γ) =
                f γ := hγgood
            _ = a ⟨γ, hγ⟩ := by
              change f γ = if γ ∈ good then f γ else 0
              rw [ite_eq_left hγgood]
            _ = ∑ j, q j * u ⟨γ, hγ⟩ j := hsum ⟨γ, hγ⟩
        · simp only [dite_eq_right hγ, mul_zero, Finset.sum_const_zero]
          have hzero : cantorBendixsonDerivAt δ (p : Nonpositive G K) γ = 0 := by
            by_contra hne
            have hs := (cantorBendixsonDerivAt_ne_zero_iff δ
              (p : Nonpositive G K) γ hγdegree).mp hne
            apply hγ
            refine ⟨hs.1, ?_⟩
            simpa only [cantorBendixsonRank_eq] using hs.2
          rw [hzero, map_zero]
      obtain ⟨yδ, hyδ⟩ :=
        (DirectSum.mem_rangeLof_iff K (ν).Component (δ + 1) y).mp hy
      rw [DirectSum.lof_eq_of] at hyδ
      have hcomp : (ν).componentMk (δ + 1) p = yδ := by
        apply cantorBendixsonGradedDerivation_injective_on_successor δ
        calc
          cantorBendixsonGradedDerivation
              (DirectSum.of (ν).Component (δ + 1) ((ν).componentMk (δ + 1) p)) =
              cantorBendixsonGradedDerivation y := hDxy
          _ = cantorBendixsonGradedDerivation
              (DirectSum.of (ν).Component (δ + 1) yδ) :=
                congrArg cantorBendixsonGradedDerivation hyδ.symm
      rw [hcomp, hyδ]
      exact Ideal.sum_mem _ fun j _ ↦
        Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)

end HahnSeries.Nonpositive
