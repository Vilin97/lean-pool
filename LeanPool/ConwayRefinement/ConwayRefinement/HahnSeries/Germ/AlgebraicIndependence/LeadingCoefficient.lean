/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.LimitOrdinalEvaluation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.TruncationPolynomial
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.ScalarLeadingCoefficientAtLimitOrdinal

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Leading coefficients when the degree is a limit ordinal

The polynomial of each proper translated truncation is read through the finite convolution
formula. Its highest coefficient in a maximal variable is the polynomial of the corresponding
truncation of the leading coefficient. The uniform degree drop for the evaluated relation then
contradicts the degrees of sufficiently late translated truncations of that coefficient.

If the leading coefficient is a scalar, the coefficient one below the top instead combines with
the derivative contribution from the leading power. That branch is proved separately and joined
to the nonconstant branch here.
-/

universe u v w

open scoped NatOrdinal Topology

open Filter MvPolynomial HahnSeries HahnSeries.Nonpositive

public noncomputable section

namespace HahnSeries.Germ

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

variable {ι : Type w} {wt : ι → NatOrdinal.{u}}
  {xg : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded}
variable (σ : LiftFamily wt xg)
variable (hx : OrdinalGraded.IsMinimalSystem
  (DirectSum.rangeLof K (cantorBendixsonDegreeValuation (G := G) (R := K)).Component) wt xg)

include hx in
open Classical in
/-- A homogeneous relation is impossible when its leading coefficient has nonzero weighted
degree and the least Cantor term of that degree precedes the least term of the maximal weight. -/
theorem false_of_aeval_eq_zero_of_leastTerm_le_of_ne_zero
    (hσ : LiftFamily.HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {F : MvPolynomial ι K} (hF : IsWeightedHomogeneous wt F α)
    (hF0 : aeval xg F = 0) {B₀ : ι} (hB₀ : B₀ ∈ F.vars)
    (hmax : ∀ i ∈ F.vars, wt i ≤ wt B₀) (hg : wt B₀ < α)
    {degHD : NatOrdinal.{u}} (hdegHD : degHD + degreeOf B₀ F • wt B₀ = α)
    (hdegHD0 : degHD ≠ 0)
    (hcase : NatOrdinal.leastTerm degHD ≤ NatOrdinal.leastTerm (wt B₀)) : False := by
  classical
  obtain ⟨D, hDdef⟩ : ∃ D, degreeOf B₀ F = D := ⟨_, rfl⟩
  rw [hDdef] at hdegHD
  have hD : 1 ≤ D := by
    rw [← hDdef]
    exact Nat.one_le_iff_ne_zero.mpr (mem_vars_iff_degreeOf_ne_zero.mp hB₀)
  have hFkmem : ∀ k, xCoeff B₀ k F ∈ supported K {B₀}ᶜ := fun k ↦
    xCoeff_mem_supported B₀ k F
  have hFkvars : ∀ k, ∀ i ∈ (xCoeff B₀ k F).vars, wt i ≤ wt B₀ := fun k i hi ↦
    hmax i (vars_xCoeff_subset B₀ k F hi)
  have hαk : ∀ k ≤ D, (degHD + (D - k) • wt B₀) + k • wt B₀ = α := by
    intro k hk
    rw [add_assoc, ← add_nsmul, Nat.sub_add_cancel hk]
    exact hdegHD
  have hFkhom : ∀ k ≤ D,
      IsWeightedHomogeneous wt (xCoeff B₀ k F) (degHD + (D - k) • wt B₀) :=
    fun k hk ↦ xCoeff_isWeightedHomogeneous' B₀ wt hF k (hαk k hk)
  have hαklt : ∀ k, 1 ≤ k → k ≤ D → degHD + (D - k) • wt B₀ < α := by
    intro k hk1 hk
    rw [← hαk k hk]
    exact lt_add_of_pos_right _
      (pos_iff_ne_zero.mpr (NatOrdinal.nsmul_ne_zero_of_ne_zero (hx.ne_zero B₀) hk1))
  have hFne : F ≠ 0 := by
    rintro rfl
    simp at hB₀
  have hFD : xCoeff B₀ D F ≠ 0 := by
    rw [← hDdef]
    exact xCoeff_degreeOf_ne_zero B₀ hFne
  have hFDhom : IsWeightedHomogeneous wt (xCoeff B₀ D F) degHD := by
    have h := hFkhom D le_rfl
    rwa [Nat.sub_self, zero_smul, add_zero] at h
  have hdegHDlt : degHD < α := by
    have h := hαklt D hD le_rfl
    rwa [Nat.sub_self, zero_smul, add_zero] at h
  have hfree : LiftFamily.FreeOfVariable σ hx α B₀
      (aeval σ.lift (xCoeff B₀ D F)) degHD :=
    LiftFamily.FreeOfVariable.aeval (σ := σ) (hx := hx) hσ hinj hg hFDhom hdegHDlt
      (hFkmem D) (hFkvars D)
  have hterm : ∀ k ≤ D, HasLowerTruncationDegree
      (σ.lift B₀ ^ k * aeval σ.lift (xCoeff B₀ k F))
      (k • wt B₀ + (degHD + (D - k) • wt B₀)) := by
    intro k hk
    exact (((LiftFamily.hasLowerTruncationDegrees_iff σ).mp hσ B₀).pow k).mul rfl
      (σ.hasLowerTruncationDegree_aeval hσ (hFkhom k hk))
  have hGexp : aeval σ.lift F = ∑ k ∈ Finset.range (D + 1),
      σ.lift B₀ ^ k * aeval σ.lift (xCoeff B₀ k F) := by
    conv_lhs => rw [← sum_xCoeff_mul_X_pow B₀ F]
    rw [hDdef, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_pow, aeval_X, mul_comm]
  have hα0 : α ≠ 0 := ne_of_gt ((zero_le : (0 : NatOrdinal) ≤ wt B₀).trans_lt hg)
  obtain ⟨bound, hboundα, hcuts⟩ :=
    exists_lt_forall_degree_translatedTruncLE_lt σ hα0 hF hF0
  obtain ⟨l, hl0, hcuts'⟩ := eventually_nhdsLT_iff_exists.mp hcuts
  have hcoeffD : ∀ γ : G, γ < 0 →
      xCoeff B₀ D (σ.pol hx α (translatedTruncLE γ (aeval σ.lift F))) =
        σ.pol hx α (translatedTruncLE γ (aeval σ.lift (xCoeff B₀ D F))) := by
    intro γ hγ
    rw [hGexp, map_sum, σ.pol_sum hx hinj _ _ (fun k hk ↦ by
      have hkD : k ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hdrop := (hterm k hkD).degree_translatedTruncLE_lt hγ
      rwa [add_comm (k • wt B₀), hαk k hkD] at hdrop), map_sum]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun k hk ↦ ?_), zero_add]
    · exact (LiftFamily.FreeOfVariable.xCoeff_pol_translatedTruncLE_lift_pow_mul
        (σ := σ) (hx := hx) hσ hinj hg hfree D (by
          rw [add_comm]
          exact hdegHD.le) hγ).2
    · have hkD : k < D := Finset.mem_range.mp hk
      have hkD' : k ≤ D := hkD.le
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · have hF0hom : IsWeightedHomogeneous wt (xCoeff B₀ 0 F) α := by
          have h := hFkhom 0 hkD'
          rw [Nat.sub_zero, hdegHD] at h
          exact h
        rw [pow_zero, one_mul, xCoeff_of_mem_supported B₀
          (LiftFamily.FreeOfVariable.pol_translatedTruncLE_aeval_mem_supported
            (σ := σ) (hx := hx) hσ hinj hg hF0hom (hFkmem 0) (hFkvars 0) hγ) D,
          ite_eq_right (Nat.ne_of_gt hD)]
      · have hfreeK := LiftFamily.FreeOfVariable.aeval (σ := σ) (hx := hx) hσ hinj hg
          (hFkhom k hkD') (hαklt k hk1 hkD') (hFkmem k) (hFkvars k)
        exact (LiftFamily.FreeOfVariable.xCoeff_pol_translatedTruncLE_lift_pow_mul
          (σ := σ) (hx := hx) hσ hinj hg hfreeK k (by
            rw [add_comm]
            exact (hαk k hkD').le) hγ).1 D hkD
  have hdegree : ν (aeval σ.lift (xCoeff B₀ D F)) =
      (degHD : WithBot NatOrdinal) := by
    have hrep := σ.represents_aeval hFDhom
    have hgrade : aeval xg (xCoeff B₀ D F) ≠ 0 := by
      intro hzero
      exact hFD (((OrdinalGraded.injectiveAt_iff degHD).mp (hinj degHD hdegHDlt))
        (xCoeff B₀ D F) hFDhom hzero)
    exact hrep.degree_eq hgrade
  have hsep : D • wt B₀ = 0 ∨
      NatOrdinal.leastTerm degHD ≤ NatOrdinal.leastTerm (D • wt B₀) := by
    right
    rw [NatOrdinal.leastTerm_nsmul (hx.ne_zero B₀) hD]
    exact hcase
  apply σ.false_of_forall_weightedTotalDegree_pol_add_lt hx hdegree hdegHD0 hsep
    (by rw [hdegHD]; exact hboundα) hl0
  · intro γ hlγ hγ hp0
    rw [← hcoeffD γ hγ] at hp0 ⊢
    exact LiftFamily.weightedTotalDegree_xCoeff_add_nsmul_lt
      (σ.pol_weight_lt_of_degree_lt hx hboundα.le (hcuts' γ hlγ hγ)) B₀ D hp0
  · exact hdegHDlt

include hx in
/-- A homogeneous relation is impossible when its leading coefficient in a maximal variable is
scalar, or its least Cantor term is no greater than that of the variable's weight. -/
@[blueprint "lem:cantor-bendixson-leading-coefficient"
  (phase := "Algebraic independence in graded rings")
  (title := "Leading-coefficient obstruction for homogeneous relations")
  (statement := /--
    Let $K$ be a field of characteristic zero and $G$ a nontrivial complete
    ordered abelian group with compatible additive uniformity and order
    topology. Let $x_i$ be a minimal homogeneous generating system for the
    associated graded ring of the degree filtration, of weights $w_i$. Choose
    series $b_i$ representing $x_i$ such that
    \[
      \deg(b_i)\le w_i,
      \qquad \deg(b_i^{\vert y})<w_i\quad\text{for every }y<0.
    \]
    Assume
    evaluation at $x_i$ is injective on every homogeneous degree below
    $\alpha$.

    Let $F\in K[X_i:i\in I]$ be weighted homogeneous of degree $\alpha$ with
    $F(x)=0$. Choose a variable $X_{B_0}$ occurring in $F$, of maximal weight
    among its variables, and suppose $w_{B_0}<\alpha$. Write
    \[
      F=\sum_{k=0}^D H_kX_{B_0}^k,
      \qquad \Delta+D w_{B_0}=\alpha.
    \]
    If $\Delta=0$, or if the last Cantor term of $\Delta$ is at most the last
    Cantor term of $w_{B_0}$, then these hypotheses are inconsistent.
  -/)
  (proof := /--
  By \ref{thm:cantor-bendixson-value-multiplicative}, the
  Cantor--Bendixson degree defines the associated graded ring in which the
  weighted-homogeneous relation is evaluated.

  Suppose first that $\Delta\ne0$. Then $H_D\ne0$ is homogeneous of degree
  $\Delta<\alpha$. Injectivity below $\alpha$ shows that $H_D(x)\ne0$, so
  $H_D(b)$ has degree exactly $\Delta$. By \ref{lem:generate}, each proper
  translated truncation has a representing polynomial. Expanding $F$ in
  $X_{B_0}$ and using the finite convolution formula identifies the
  coefficient of $X_{B_0}^D$ in that polynomial with the polynomial
  representing the corresponding translated truncation of $H_D(b)$.

  Since $F(x)=0$, the translated truncations of $F(b)$ have their representing
  polynomials bounded in weighted degree by some $q<\alpha$. The hypothesis on
  the last Cantor terms and \ref{lem:natural-sum-approach} give
  $\rho<\Delta$ with $q\le\rho\oplus D w_{B_0}$. A sufficiently late
  translated truncation of $H_D(b)$ has degree $\rho$, so its representing
  polynomial has weighted degree $\rho$. Its contribution in degree
  $\rho\oplus D w_{B_0}$ contradicts the bound $q$.

  If $\Delta=0$, then $H_D$ is a nonzero scalar and $D\ge2$. The polynomial
  $H_{D-1}+D H_DX_{B_0}$ is nonzero and homogeneous of degree $w_{B_0}$.
  Injectivity below $\alpha$ makes its value at $b$ have that exact degree.
  The coefficient of $X_{B_0}^{D-1}$ in the translated-truncation polynomial
  is the polynomial representing its translated truncation, and the same
  argument gives the contradiction.
  -/)]
theorem false_of_aeval_eq_zero_of_leastTerm_le
    (hσ : LiftFamily.HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {F : MvPolynomial ι K} (hF : IsWeightedHomogeneous wt F α)
    (hF0 : aeval xg F = 0) {B₀ : ι} (hB₀ : B₀ ∈ F.vars)
    (hmax : ∀ i ∈ F.vars, wt i ≤ wt B₀) (hg : wt B₀ < α)
    {degHD : NatOrdinal.{u}} (hdegHD : degHD + degreeOf B₀ F • wt B₀ = α)
    (hcase : degHD = 0 ∨ NatOrdinal.leastTerm degHD ≤
      NatOrdinal.leastTerm (wt B₀)) : False := by
  by_cases hdegHD0 : degHD = 0
  · exact false_of_aeval_eq_zero_of_leadingCoefficientDegree_eq_zero σ hx hσ hinj
      hF hF0 hB₀ hmax hg hdegHD hdegHD0
  · exact false_of_aeval_eq_zero_of_leastTerm_le_of_ne_zero σ hx hσ hinj
      hF hF0 hB₀ hmax hg hdegHD hdegHD0 (hcase.resolve_left hdegHD0)

end HahnSeries.Germ

end
