/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Primality.Consequences
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue

/-!
# The ordinal-value quotient by `J` is a polynomial algebra

Let `K((ℝ^{≤0}))/J` be Berarducci's quotient ring (`Berarducci.Germ`). For a minimal system of
homogeneous generators `Y` of `P̂` with lifts `b_B`, the map `K[X_B] → K((ℝ^{≤0}))/J`,
`F ↦ F(b_𝓑) + J`, is a homomorphism of `K`-algebras. It is surjective: every series `u` is
congruent modulo `J` to a value `F(b_𝓑)`, namely to that of its polynomial `pol(u)`
(`Lifts.exists_degreeLT_toGerm_aeval_eq`). It is injective: for `F ≠ 0` the ordinal value of
`F(b_𝓑)` is `ω^{deg F}`, the degree formula, which rests on Conjecture (P); so `F(b_𝓑) ∉ J`.
Hence `K((ℝ^{≤0}))/J ≃ K[X_B] ≃ P̂` (`Lifts.ordinalValueQuotientAlgEquiv`), the class of a series
`u` of ordinal value below `ω^α` going to `pol(u)`, and the quotient admits unique factorisation.
This is the conjecture of Berarducci as stated in [LM17, Conjecture 1.5]: every nonzero germ
admits a unique factorisation into irreducibles.

The classes of the series of ordinal value below `ω^α` are the classes of the values `F(b_𝓑)` with
every monomial of `F` of degree below `α` (`Lifts.toGerm_image_ordinalValue_lt_eq`).
-/

universe v w

open scoped NatOrdinal
open MvPolynomial OrdinalGraded Berarducci HahnSeries.Nonpositive

public noncomputable section

namespace NatOrdinal

/-- Every ordinal lies below `ω^(α + 1)`. -/
theorem lt_wpow_add_one_self (a : NatOrdinal) : a < ω^ (a + 1) := by
  have h : a ≤ ω^ a :=
    NatOrdinal.of.le_iff_le.mpr (Ordinal.right_le_opow a.val Ordinal.one_lt_omega0)
  exact h.trans_lt (wpow_lt_wpow.mpr (lt_add_one a))

end NatOrdinal

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K] {ι : Type w} {wt : ι → NatOrdinal}
  {x : ι → PrincipalSubring K}

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (principalGrading K) wt x)

/-- Evaluation at the lifts, read in the quotient by `J`: `F ↦ F(b_𝓑) + J`. -/
def ordinalValueQuotientAlgHom : MvPolynomial ι K →ₐ[K] Germ K :=
  (Ideal.Quotient.mkₐ K (negativeMonomialIdeal K)).comp (aeval σ.lift)

omit [CharZero K] in
theorem ordinalValueQuotientAlgHom_apply (F : MvPolynomial ι K) :
    σ.ordinalValueQuotientAlgHom F = toGerm (aeval σ.lift F) := by
  change Ideal.Quotient.mkₐ K _ (aeval σ.lift F) = _
  rw [Ideal.Quotient.mkₐ_eq_mk, toGerm_apply]

include hx

omit [CharZero K] in
/-- Every class modulo `J` is represented by a value `F(b_𝓑)`. -/
@[blueprint "lem:ordinal-value-quotient-evaluation-surjective"
  (phase := "Polynomial presentations")
  (title := "Surjectivity of evaluation modulo $J$")
  (statement := /--
    Let $K$ be a field. Let $(x_i)$ be a minimal homogeneous generating system
    of $\widehat{\mathrm P}$, with $x_i\in\mathrm P_{w_i}$, and choose
    $b_i\in K((\mathbb R^{\le0}))$ representing $x_i$ in degree $w_i$.
    Every class in $K((\mathbb R^{\le0}))/J$ is the class of $F(b_i)$ for some
    polynomial $F\in K[X_i:i\in I]$.
  -/)
  (proof := /--
    For a representative $u$ of the class, choose
    $\alpha>v_J(u)$.  By
    \ref{prop:polynomial-representative-exists}, there is a polynomial $F$
    of weighted degree below $\alpha$ such that $F(b_i)\equiv u\pmod J$.
  -/)]
theorem ordinalValueQuotientAlgHom_surjective :
    Function.Surjective σ.ordinalValueQuotientAlgHom := by
  intro g
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨F, -, hF⟩ := σ.exists_degreeLT_toGerm_aeval_eq hx (ordinalValue u + 1) u
    (NatOrdinal.lt_wpow_add_one_self _)
  refine ⟨F, ?_⟩
  rw [ordinalValueQuotientAlgHom_apply, hF, toGerm_apply]

/-- A nonzero polynomial has a value `F(b_𝓑)` outside `J`: its ordinal value is `ω^{deg F}`, the
degree formula, by Conjecture (P). -/
@[blueprint "lem:ordinal-value-quotient-evaluation-injective"
  (phase := "Polynomial presentations")
  (title := "Injectivity of evaluation modulo $J$")
  (statement := /--
    Let $K$ be a field of characteristic zero. Let $(x_i)$ be a minimal
    homogeneous generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$, and choose
    $b_i\in K((\mathbb R^{\le0}))$ representing $x_i$ in degree $w_i$.
    If the class of $F(b_i)$ is zero in $K((\mathbb R^{\le0}))/J$, then
    $F=0$.
  -/)
  (proof := /--
    By \ref{lem:principal-representatives-cantor-bendixson}, the chosen representatives
    give a minimal homogeneous generating system for the Cantor--Bendixson
    associated graded ring. The two relation hypotheses of
    \ref{thm:cantor-bendixson-polynomiality} are supplied by
    \ref{lem:linear-occurrence} and
    \ref{lem:real-translated-truncation-partials}. Thus evaluation at $(x_i)$
    is injective. If $F\ne0$, its top
    homogeneous component therefore evaluates nontrivially, so the
    ordinal-value calculation gives
    $v_J(F(b_i))=\omega^{\deg_w(F)}\ne0$. Hence $F(b_i)\notin J$, contrary to
    the vanishing of its class.
  -/)]
theorem ordinalValueQuotientAlgHom_injective : Function.Injective σ.ordinalValueQuotientAlgHom := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  by_contra hF0
  have hval := σ.ordinalValue_aeval_eq_wpow_weightedTotalDegree
    (injectiveAt_of_isMinimalSystem hx _) hF0
  rw [ordinalValueQuotientAlgHom_apply, toGerm_apply, Ideal.Quotient.eq_zero_iff_mem,
    ← ordinalValue_eq_zero_iff, hval] at hF
  exact NatOrdinal.wpow_ne_zero _ hF

/-- **The quotient by `J` is a polynomial algebra**: `K((ℝ^{≤0}))/J ≃ K[X_B]`, with the
class of `F(b_𝓑)` mapping to `F`. -/
@[blueprint "thm:ordinal-value-quotient"
  (phase := "Polynomial presentations")
  (title := "Polynomial presentation of the quotient by $J$")
  (statement := /--
    Let $K$ be a field of characteristic $0$.  Let $(x_i)_{i\in\iota}$ be a
    minimal homogeneous generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$, and choose
    $b_i\in K((\mathbb R^{\le0}))$ representing $x_i$ in degree $w_i$.
    There is a $K$-algebra isomorphism
    \[
      K((\mathbb R^{\le 0}))/J \longrightarrow K[X_i:i\in\iota]
    \]
    whose inverse sends $F$ to the class of $F(b_i)$ modulo $J$.
  -/)
  (proof := /--
    Evaluation followed by passage to the quotient is surjective by
    \ref{lem:ordinal-value-quotient-evaluation-surjective} and injective by
    \ref{lem:ordinal-value-quotient-evaluation-injective}.  Its inverse is the
    stated $K$-algebra isomorphism.
  -/)]
def ordinalValueQuotientAlgEquiv : Germ K ≃ₐ[K] MvPolynomial ι K :=
  (AlgEquiv.ofBijective σ.ordinalValueQuotientAlgHom
    ⟨σ.ordinalValueQuotientAlgHom_injective hx,
      σ.ordinalValueQuotientAlgHom_surjective hx⟩).symm

theorem ordinalValueQuotientAlgEquiv_symm_apply (F : MvPolynomial ι K) :
    (σ.ordinalValueQuotientAlgEquiv hx).symm F = toGerm (aeval σ.lift F) := by
  have h := (AlgEquiv.ofBijective_apply σ.ordinalValueQuotientAlgHom
    ⟨σ.ordinalValueQuotientAlgHom_injective hx,
      σ.ordinalValueQuotientAlgHom_surjective hx⟩ F).trans
        (σ.ordinalValueQuotientAlgHom_apply F)
  simpa only [ordinalValueQuotientAlgEquiv, AlgEquiv.symm_symm] using h

theorem ordinalValueQuotientAlgEquiv_toGerm_aeval (F : MvPolynomial ι K) :
    σ.ordinalValueQuotientAlgEquiv hx (toGerm (aeval σ.lift F)) = F := by
  rw [← σ.ordinalValueQuotientAlgEquiv_symm_apply hx F]
  exact (σ.ordinalValueQuotientAlgEquiv hx).apply_symm_apply F

/-- The class of a series `u` of ordinal value below `ω^α` goes to its polynomial `pol(u)`
modulo `J`. -/
@[blueprint "thm:ordinal-value-quotient-polynomial-representative"
  (phase := "Polynomial presentations")
  (title := "Polynomial representative of a germ")
  (statement := /--
    Let $K$ be a field of characteristic $0$.  Let $(x_i)_{i\in\iota}$ be a
    minimal homogeneous generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$, and choose
    $b_i\in K((\mathbb R^{\le0}))$ representing $x_i$ in degree $w_i$.
    For every $\alpha<\omega_1$ and every $u\in K((\mathbb R^{\le 0}))$ with
    $v_J(u)<\omega^\alpha$, the polynomial presentation of the quotient by $J$
    sends the class of $u$ to its polynomial representative
    $\operatorname{pol}_\alpha(u)$.
  -/)
  (proof := /--
    By definition, $\operatorname{pol}_\alpha(u)$ has value congruent to $u$
    modulo $J$.  The inverse description in
    \ref{thm:ordinal-value-quotient} therefore sends this polynomial to the class
    of $u$; applying the isomorphism gives the stated formula.
  -/)]
theorem ordinalValueQuotientAlgEquiv_toGerm {α : NatOrdinal} {u : Series K}
    (hu : ordinalValue u < ω^ α) :
    σ.ordinalValueQuotientAlgEquiv hx (toGerm u) = σ.pol hx α u := by
  rw [← σ.toGerm_aeval_pol hx hu]
  exact σ.ordinalValueQuotientAlgEquiv_toGerm_aeval hx _

/-- `K((ℝ^{≤0}))/J ≃ P̂`: the composite with the polynomial presentation of `P̂`. -/
def ordinalValueQuotientAlgEquivPrincipalSubring : Germ K ≃ₐ[K] PrincipalSubring K :=
  (σ.ordinalValueQuotientAlgEquiv hx).trans (algEquivOfIsMinimalSystem hx)

omit [CharZero K] in
/-- The classes modulo `J` of series of ordinal value below `ω^α` are exactly the classes of
values `F(b_𝓑)` whose monomials all have weighted degree below `α`. -/
@[blueprint "thm:ordinal-value-quotient-filtration"
  (phase := "Polynomial presentations")
  (title := "Polynomial representatives below an ordinal-value bound")
  (statement := /--
    Let $K$ be a field.  Let $(x_i)_{i\in\iota}$ be a minimal homogeneous
    generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$, and choose
    $b_i\in K((\mathbb R^{\le0}))$ representing $x_i$ in degree $w_i$.
    For every $\alpha<\omega_1$,
    \[
      \{u+J:v_J(u)<\omega^\alpha\}
      =\{F(b_i)+J:\text{every monomial of }F\text{ has weighted degree}<\alpha\}.
    \]
  -/)
  (proof := /--
    The forward inclusion follows from
    \ref{prop:polynomial-representative-exists}.  Conversely, if every monomial
    of $F$ has weighted degree below $\alpha$, then
    $v_J(F(b_i))<\omega^\alpha$, so the class of $F(b_i)$ belongs to the
    left-hand set.
  -/)]
theorem toGerm_image_ordinalValue_lt_eq (α : NatOrdinal) :
    toGerm '' {u : Series K | ordinalValue u < ω^ α} =
      (fun F ↦ toGerm (aeval σ.lift F)) '' {F : MvPolynomial ι K | DegreeLT wt F α} := by
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨F, hF, h⟩ := σ.exists_degreeLT_toGerm_aeval_eq hx α u hu
    exact ⟨F, hF, h⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨_, σ.ordinalValue_aeval_lt_of_degreeLT hF, rfl⟩

end Lifts

/-! ### Unique factorisation in the quotient by `J` -/

/-- The quotient by `J` is a domain: `J` is prime (Berarducci, Corollary 9.8). -/
instance : IsDomain (Germ K) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr negativeMonomialIdeal_isPrime

/-- **Berarducci's conjecture [LM17, Conjecture 1.5].** The quotient
`K((ℝ^{≤0}))/J` admits unique factorisation: it is a polynomial algebra over `K`. -/
instance : UniqueFactorizationMonoid (Germ K) := by
  obtain ⟨ι', wt', x', hx⟩ := exists_isMinimalSystem (principalGrading K)
  obtain ⟨σ⟩ := exists_lifts hx.mem
  exact (σ.ordinalValueQuotientAlgEquiv hx).toMulEquiv.symm.uniqueFactorizationMonoid inferInstance

end Berarducci
