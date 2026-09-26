/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.Polynomiality
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.Extension
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.PrincipalGraded
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFraction

/-!
# Consequences of the polynomiality of `P̂`

By the polynomiality of `P̂`, evaluation `K[X_B : B ∈ 𝓑] → P̂` at a minimal system `𝓑` of
homogeneous generators is injective (`Berarducci.aeval_injective_of_isMinimalSystem`), and it
is surjective since the generators span. Hence:

* `P̂` is a polynomial algebra over `K` on any minimal system of homogeneous generators
  (`algEquivOfIsMinimalSystem`), so `P̂` is a unique factorisation domain;
* every family of homogeneous elements of positive degrees whose members of each degree `β` are
  linearly independent modulo `(P̂_+)² ∩ P_β` (the decomposable elements, `decomposableAt`) is
  algebraically independent: it extends to a minimal system of homogeneous generators
  (`OrdinalGraded.exists_isMinimalSystem_extension`);
* at an additively principal degree `ω^γ` the space `(P̂_+)² ∩ P_{ω^γ}` is zero — no two nonzero
  degrees have natural sum `ω^γ` — so every `K`-linearly independent family in `P_{ω^γ}`, in
  particular every `K`-basis of `P_ω`, is algebraically independent in `P̂`;
* every nonzero element of `P_{ω^γ}` is prime in `P̂`, being a variable of a polynomial
  presentation: the analogue at every additively principal degree of [LM24, Cor. 7.2.8], principal
  elements of degree one are prime.
-/

universe u v w o

open scoped NatOrdinal
open MvPolynomial OrdinalGraded Berarducci

public noncomputable section

namespace OrdinalGraded

variable {E : Type u} {R : Type v} [Field E] [CommRing R] [Algebra E R]
variable (𝒜 : NatOrdinal.{o} → Submodule E R)

/-- At an additively principal degree `ω^γ` the square of the ideal of positive degree has zero
component, `(A_+)² ∩ A_{ω^γ} = 0`: two nonzero degrees have natural sum below `ω^γ` or above it. -/
theorem decomposableAt_wpow_eq_bot (γ : NatOrdinal.{o}) : decomposableAt 𝒜 (ω^ γ) = ⊥ := by
  refine le_bot_iff.mp (decomposableAt_le 𝒜 fun i j hi hj hij ↦ ?_)
  exfalso
  have hi' : i < ω^ γ := by
    rw [← hij]; exact lt_add_of_pos_right i (pos_iff_ne_zero.mpr hj)
  have hj' : j < ω^ γ := by
    rw [← hij]; exact lt_add_of_pos_left j (pos_iff_ne_zero.mpr hi)
  exact (NatOrdinal.add_lt_wpow hi' hj').ne hij

end OrdinalGraded

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommRing R] [IsDomain R]

/-- A variable is prime in a polynomial ring over a domain: separating it, the ring is
`R[X_j : j ≠ i][X_i]`, where `X_i` is prime. -/
theorem prime_X (i : σ) : Prime (X i : MvPolynomial σ R) := by
  classical
  let e : MvPolynomial σ R ≃ₐ[R] Polynomial (MvPolynomial {j // j ≠ i} R) :=
    (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft R {j // j ≠ i})
  have he : e (X i) = Polynomial.X := by
    simp only [e, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
      Equiv.optionSubtypeNe_symm_self, optionEquivLeft_X_none]
  rw [← MulEquiv.prime_iff e, he]
  exact Polynomial.prime_X

end MvPolynomial

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K] {ι : Type w} {wt : ι → NatOrdinal}
  {x : ι → PrincipalSubring K}

/-! ### `P̂` is a polynomial algebra -/

/-- Evaluation at any minimal homogeneous generating system gives a polynomial presentation of
`P̂` over `K`. -/
@[expose, blueprint "cor:principal-subring-polynomial-algebra"
  (phase := "Polynomial presentations")
  (title := "Polynomial presentation of $\\Ph$")
  (statement := /--
    Let $K$ be a field of characteristic $0$, and let
    $\calB=(B_i)_{i\in I}$ be a minimal homogeneous generating system of
    $\Ph$.  Evaluation $X_i\mapsto B_i$ is a $K$-algebra isomorphism
    $K[X_i:i\in I]\simeq\Ph$.
  -/)
  (proof := /--
  Principal representatives identify $\Prin_0$ with $K$.  The homogeneous
  generation theorem then makes evaluation at $\calB$ surjective, while
  \ref{thm:polynomial} makes it injective.  Hence
  evaluation is a $K$-algebra isomorphism.
  -/)]
def algEquivOfIsMinimalSystem (hx : IsMinimalSystem (principalGrading K) wt x) :
    MvPolynomial ι K ≃ₐ[K] PrincipalSubring K :=
  AlgEquiv.ofBijective (aeval x)
    ⟨aeval_injective_of_isMinimalSystem hx,
      hx.aeval_surjective (principalGrading_gradeZeroScalars K)⟩

theorem algEquivOfIsMinimalSystem_apply (hx : IsMinimalSystem (principalGrading K) wt x)
    (F : MvPolynomial ι K) : algEquivOfIsMinimalSystem hx F = aeval x F :=
  rfl

/-- `P̂` is a unique factorisation domain: it is a polynomial algebra over the field `K`. -/
instance : UniqueFactorizationMonoid (PrincipalSubring K) := by
  obtain ⟨ι', wt', x', hx⟩ := exists_isMinimalSystem (principalGrading K)
  exact (algEquivOfIsMinimalSystem hx).toMulEquiv.uniqueFactorizationMonoid inferInstance

/-! ### Algebraic independence of independent homogeneous families -/

/-- An indexed homogeneous family of positive degrees that is linearly independent degree by
degree modulo `(P̂_+)²` is algebraically independent. -/
@[blueprint "cor:independent-homogeneous-family"
  (phase := "Polynomial presentations")
  (title := "Algebraic independence of homogeneous families in $\\Ph$")
  (statement := /--
    Let $K$ be a field of characteristic $0$, and let $(x_i)_{i\in I}$ be a
    family in $\Ph$ with positive weights $w_i$ and
    $x_i\in\Prin_{w_i}$.  Suppose that for every $\beta$, the images of the
    indexed subfamily $(x_i)_{w_i=\beta}$ in
    $\Prin_\beta/((\Ph_+)^2\cap\Prin_\beta)$ are $K$-linearly independent.
    Then evaluation $X_i\mapsto x_i$ is injective; equivalently, $(x_i)$ is
    algebraically independent over $K$.
  -/)
  (proof := /--
  \ref{lem:extend-to-minimal-system} enlarges the given
  indexed family, degree by degree, to a minimal homogeneous generating system.
  \ref{thm:polynomial} makes this extended system
  algebraically independent.  Algebraic independence passes to the original
  indexed subfamily.
  -/)]
theorem aeval_injective_of_independent_mod_decomposableAt (hwt : ∀ i, wt i ≠ 0)
    (hmem : ∀ i, x i ∈ principalGrading K (wt i))
    (hind : ∀ (β : NatOrdinal) (c : ι →₀ K), (∀ i ∈ c.support, wt i = β) →
      Finsupp.linearCombination K x c ∈ decomposableAt (principalGrading K) β → c = 0) :
    Function.Injective (aeval x : MvPolynomial ι K →ₐ[K] PrincipalSubring K) := by
  obtain ⟨ι', wt', x', e, he, -, hx', hmin⟩ :=
    exists_isMinimalSystem_extension (principalGrading K) hwt hmem hind
  intro F G hFG
  apply rename_injective e he
  apply aeval_injective_of_isMinimalSystem hmin
  have hxe : x' ∘ e = x := funext hx'
  rw [aeval_rename, aeval_rename, hxe]
  exact hFG

/-- Every `K`-linearly independent family in an additively principal degree `P_{ω^γ}` is
algebraically independent in `P̂`. -/
@[blueprint "cor:principal-degree-linear-independence"
  (phase := "Polynomial presentations")
  (title := "Algebraic independence in additively principal degree")
  (statement := /--
    Let $K$ be a field of characteristic $0$ and $\gamma<\omega_1$.  Every
    $K$-linearly independent family $(x_i)_{i\in I}$ in
    $\Prin_{\omega^\gamma}$ is algebraically independent over $K$ in $\Ph$.
  -/)
  (proof := /--
  No two positive degrees have Hessenberg's natural sum $\omega^\gamma$, so the
  decomposable subspace in that degree is zero.  Linear independence therefore
  gives independence modulo $(\Ph_+)^2$. Then
  \ref{cor:independent-homogeneous-family} gives algebraic independence.
  -/)]
theorem aeval_injective_of_linearIndependent_of_mem_principalGrading_wpow
    (γ : NatOrdinal)
    (hmem : ∀ i, x i ∈ principalGrading K (ω^ γ)) (hli : LinearIndependent K x) :
    Function.Injective (aeval x : MvPolynomial ι K →ₐ[K] PrincipalSubring K) :=
  aeval_injective_of_independent_mod_decomposableAt
    (wt := fun _ ↦ ω^ γ) (fun _ ↦ (NatOrdinal.wpow_pos γ).ne') hmem fun β c hc hdec ↦ by
      rcases c.support.eq_empty_or_nonempty with h | ⟨i, hi⟩
      · exact Finsupp.support_eq_empty.mp h
      · obtain rfl : β = ω^ γ := (hc i hi).symm
        rw [decomposableAt_wpow_eq_bot, Submodule.mem_bot] at hdec
        exact linearIndependent_iff.mp hli c hdec

/-! ### Homogeneous elements of an additively principal degree are prime -/

/-- Every nonzero element of an additively principal degree `P_{ω^γ}` is prime in `P̂`. This is
the analogue at every additively principal degree of [LM24, Cor. 7.2.8], which treats degree one. -/
@[blueprint "cor:prime-at-principal-degree"
  (phase := "Polynomial presentations")
  (title := "Prime elements of additively principal degree")
  (statement := /--
    Let $K$ be a field of characteristic $0$ and $\gamma<\omega_1$.  Every
    nonzero element of $\Prin_{\omega^\gamma}$ is prime in $\Ph$.
  -/)
  (proof := /--
  No two positive degrees have Hessenberg's natural sum $\omega^\gamma$, so the
  decomposable subspace in that degree is zero and the nonzero singleton $y$
  is independent modulo it.  By \ref{lem:extend-to-minimal-system}, this
  singleton extends to a minimal homogeneous generating system.  By
  \ref{cor:principal-subring-polynomial-algebra}, $y$ corresponds to one of the
  polynomial variables, which is prime; the isomorphism therefore makes $y$ prime
  in $\Ph$.
  -/)]
theorem prime_of_mem_principalGrading_wpow {γ : NatOrdinal} {y : PrincipalSubring K}
    (hy : y ∈ principalGrading K (ω^ γ)) (hy0 : y ≠ 0) : Prime y := by
  obtain ⟨ι', wt', x', e, -, -, hx', hmin⟩ :=
    exists_isMinimalSystem_extension (principalGrading K) (wt := fun _ : Unit ↦ ω^ γ)
      (x := fun _ ↦ y) (fun _ ↦ (NatOrdinal.wpow_pos γ).ne') (fun _ ↦ hy) fun β c hc hdec ↦ by
        rcases c.support.eq_empty_or_nonempty with h | ⟨i, hi⟩
        · exact Finsupp.support_eq_empty.mp h
        · obtain rfl : β = ω^ γ := (hc i hi).symm
          rw [decomposableAt_wpow_eq_bot, Submodule.mem_bot, Finsupp.linearCombination_unique,
            smul_eq_zero] at hdec
          have h0 : c default = 0 := hdec.resolve_right hy0
          exact Finsupp.ext fun u ↦ by rw [Subsingleton.elim u default, h0, Finsupp.zero_apply]
  have hX : algEquivOfIsMinimalSystem hmin (X (e ())) = y := by
    rw [algEquivOfIsMinimalSystem_apply, aeval_X, hx']
  rw [← hX]
  exact (MulEquiv.prime_iff (algEquivOfIsMinimalSystem hmin)).mpr (MvPolynomial.prime_X _)

/-- Every nonzero element of `P_{ω^γ}` is irreducible in `P̂`. -/
theorem irreducible_of_mem_principalGrading_wpow {γ : NatOrdinal} {y : PrincipalSubring K}
    (hy : y ∈ principalGrading K (ω^ γ)) (hy0 : y ≠ 0) : Irreducible y :=
  (prime_of_mem_principalGrading_wpow hy hy0).irreducible

end Berarducci
