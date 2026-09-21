/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Truncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Additive
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.PWOAdditionFiber
public import Mathlib.RingTheory.HahnSeries.Multiplication

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Finite convolution for translated Hahn truncations

In an ordered uniform exponent group that is Cauchy complete, the finite fiber of addition on the
closed supports indexes a local coefficient identity for a product. Translating weak truncations
turns this into a finite convolution identity with an error of Cantor–Bendixson value zero.
The indices use closed supports, including limit exponents where the actual coefficient is zero.

The coefficient argument reindexes finite antidiagonal sums. No infinite sum of germs or
commutation with an uncontrolled infinite sum is used. The hypotheses do not require density.
-/

public noncomputable section

open Set Filter Topology TopologicalSpace

universe u v

namespace HahnSeries

variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

section Semiring

variable [NonUnitalNonAssocSemiring R]

/-- The coefficient of two weak truncations is a restricted finite antidiagonal sum. -/
theorem coeff_truncLE_mul_truncLE (b d : HahnSeries G R) (a c z : G) :
    (truncLE a b * truncLE c d).coeff z =
      ∑ p ∈ (Finset.antidiagonal b.isPWO_support d.isPWO_support z).filter
        (fun p ↦ p.1 ≤ a ∧ p.2 ≤ c), b.coeff p.1 * d.coeff p.2 := by
  classical
  rw [coeff_mul]
  have he : Finset.antidiagonal (truncLE a b).isPWO_support
      (truncLE c d).isPWO_support z =
      (Finset.antidiagonal b.isPWO_support d.isPWO_support z).filter
        (fun p ↦ p.1 ≤ a ∧ p.2 ≤ c) := by
    ext p
    simp only [Finset.mem_antidiagonal, support_truncLE, mem_setOf_eq, Finset.mem_filter]
    tauto
  rw [he]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨_, ha, hc⟩ := Finset.mem_filter.mp hp
  rw [coeff_truncLE_of_le ha, coeff_truncLE_of_le hc]

end Semiring

variable [UniformSpace G] [OrderTopology G]

section Zero

variable [Zero R]

/-- The finite pairs of closed-support exponents whose sum is the prescribed cutoff. -/
def closedSupportAddFiber (b d : HahnSeries G R) (γ : G) : Finset (G × G) :=
  (b.closedSupport_isPWO.finite_add_fiber d.closedSupport_isPWO γ).toFinset

/-- The addition fiber consists exactly of the closed-support pairs at the cutoff. -/
theorem mem_closedSupportAddFiber (b d : HahnSeries G R) (γ : G) (p : G × G) :
    p ∈ b.closedSupportAddFiber d γ ↔
      p.1 ∈ b.closedSupport ∧ p.2 ∈ d.closedSupport ∧ p.1 + p.2 = γ := by
  simp only [closedSupportAddFiber, Set.Finite.mem_toFinset, mem_setOf_eq, mem_prod]
  tauto

end Zero

variable [IsUniformAddGroup G] [Nontrivial G] [CompleteSpace G]

section Semiring

variable [NonUnitalNonAssocSemiring R]

/-- Near a cutoff, the product coefficients are the finite sum of the indexed truncated products. -/
theorem eventually_coeff_mul_eq_sum_truncLE (b d : HahnSeries G R) (γ : G) :
    ∀ᶠ z in 𝓝 γ, (b * d).coeff z =
      ∑ p ∈ b.closedSupportAddFiber d γ, (truncLE p.1 b * truncLE p.2 d).coeff z := by
  classical
  have hev := b.closedSupport_isPWO.eventually_existsUnique_add_dominator
    d.closedSupport_isPWO b.closedSupport.isClosed d.closedSupport.isClosed γ
  filter_upwards [hev] with z hz
  rw [coeff_mul]
  simp_rw [coeff_truncLE_mul_truncLE, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hqb, hqd, hqz⟩ := Finset.mem_antidiagonal.mp hq
  let q' : (b.closedSupport : Set G) ×ˢ (d.closedSupport : Set G) :=
    ⟨q, (b.mem_closedSupport q.1).mpr (subset_closure hqb),
      (d.mem_closedSupport q.2).mpr (subset_closure hqd)⟩
  obtain ⟨p, hp, huniq⟩ := hz q' hqz
  symm
  refine (Finset.sum_eq_single p.1 ?_ ?_).trans (ite_eq_left hp.2)
  · intro r hr hne
    apply ite_eq_right
    intro hdom
    have hr' := (b.mem_closedSupportAddFiber d γ r).mp hr
    let r' : (b.closedSupport : Set G) ×ˢ (d.closedSupport : Set G) :=
      ⟨r, hr'.1, hr'.2.1⟩
    exact hne (congrArg Subtype.val (huniq r' ⟨hr'.2.2, hdom⟩))
  · intro hnot
    exact (hnot ((b.mem_closedSupportAddFiber d γ p.1).mpr ⟨p.2.1, p.2.2, hp.1⟩)).elim

end Semiring

section Ring

variable [Ring R]

/-- The translated finite convolution identity has an error of value zero. -/
theorem cantorBendixsonValue_convolution_error (b d : HahnSeries G R) (γ : G) :
    (translate (-γ) (truncLE γ (b * d)) -
      ∑ p ∈ b.closedSupportAddFiber d γ,
        translate (-p.1) (truncLE p.1 b) *
          translate (-p.2) (truncLE p.2 d)).cantorBendixsonValue = 0 := by
  classical
  let S : HahnSeries G R :=
    ∑ p ∈ b.closedSupportAddFiber d γ, truncLE p.1 b * truncLE p.2 d
  have hs : ∑ p ∈ b.closedSupportAddFiber d γ,
        translate (-p.1) (truncLE p.1 b) * translate (-p.2) (truncLE p.2 d) =
      translate (-γ) S := by
    dsimp only [S]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [translate_mul_translate, ← neg_add,
      ((b.mem_closedSupportAddFiber d γ p).mp hp).2.2]
  have hS (z : G) (hz : γ < z) : S.coeff z = 0 := by
    dsimp only [S]
    rw [coeff_sum]
    apply Finset.sum_eq_zero
    intro p hp
    by_contra hzmem
    obtain ⟨x, hx, y, hy, hxy⟩ := support_mul_subset hzmem
    rw [support_truncLE] at hx hy
    have hle : z ≤ γ := by
      rw [← hxy, ← ((b.mem_closedSupportAddFiber d γ p).mp hp).2.2]
      exact add_le_add hx.2 hy.2
    exact (not_le_of_gt hz) hle
  rw [hs, ← map_sub]
  apply cantorBendixsonValue_of_notMem
  rw [mem_closure_iff_frequently, Filter.not_frequently]
  have ht : Tendsto (fun z : G ↦ γ + z) (𝓝 0) (𝓝 γ) := by
    simpa only [Homeomorph.coe_addLeft, add_zero] using
      (Homeomorph.addLeft γ).continuous.continuousAt.tendsto (x := 0)
  filter_upwards [ht.eventually (b.eventually_coeff_mul_eq_sum_truncLE d γ)] with z hz
  change ¬ (translate (-γ) (truncLE γ (b * d) - S)).coeff z ≠ 0
  apply not_not.mpr
  rw [coeff_translate, coeff_sub, HahnSeries.coeff_truncLE]
  have he : z - -γ = γ + z := by simp only [sub_neg_eq_add, add_comm]
  rw [he]
  by_cases hzγ : γ + z ≤ γ
  · rw [ite_eq_left hzγ, hz]
    have hcoef : S.coeff (γ + z) =
        ∑ p ∈ b.closedSupportAddFiber d γ, (truncLE p.1 b * truncLE p.2 d).coeff (γ + z) :=
      coeff_sum _
    rw [hcoef, sub_self]
  · rw [ite_eq_right hzγ, hS _ (lt_of_not_ge hzγ), sub_self]

/-- The translated product truncation and its finite convolution sum have the same value. -/
@[blueprint "lem:cantor-bendixson-convolution"
  (phase := "Cantor–Bendixson ranks of supports")
  (title := "Finite convolution of translated truncations")
  (statement := /--
    Let $R$ be a ring, let $G$ be a nontrivial ordered abelian group equipped
    with a compatible additive uniformity and its order topology, and assume
    that $G$ is Cauchy complete.  Let $b,d\in R((G))$.  For $\gamma\in G$,
    let $F_\gamma$ be the
    finite addition fiber
    \[
      F_\gamma=
      \{(x,y)\in\operatorname{cl}(\operatorname{supp}(b))
          \times\operatorname{cl}(\operatorname{supp}(d)):x+y=\gamma\}.
    \]
    Then
    \[
      V_{\mathrm{CB}}((bd)^{\vert\gamma})=
      V_{\mathrm{CB}}\!\left(
        \sum_{(x,y)\in F_\gamma}b^{\vert x}d^{\vert y}
      \right).
    \]
  -/)
  (proof := /--
    Closed well-ordered supports have finite addition fibers.  In a
    neighbourhood of $\gamma$, each coefficient of $bd$ is the finite sum of
    the products of the corresponding truncations indexed by
    $F_\gamma$.  After translating $\gamma$ to $0$, the difference between
    the two displayed series vanishes on a neighbourhood of $0$.  By
    \ref{def:cantor-bendixson-value}, its value is zero, and adding it does
    not change the Cantor--Bendixson rank at $0$.  The two values are
    therefore equal.
  -/)]
theorem cantorBendixsonValue_convolution (b d : HahnSeries G R) (γ : G) :
    (translate (-γ) (truncLE γ (b * d))).cantorBendixsonValue =
      (∑ p ∈ b.closedSupportAddFiber d γ,
        translate (-p.1) (truncLE p.1 b) *
          translate (-p.2) (truncLE p.2 d)).cantorBendixsonValue :=
  cantorBendixsonValue_eq_of_sub_value_eq_zero _ _ (b.cantorBendixsonValue_convolution_error d γ)

end Ring

end HahnSeries
