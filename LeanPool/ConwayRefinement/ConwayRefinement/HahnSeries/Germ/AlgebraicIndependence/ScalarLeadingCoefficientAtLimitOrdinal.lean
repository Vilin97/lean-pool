/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.LimitOrdinalEvaluation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.TruncationPolynomial
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.OrdinalGenerators

/-!
# Scalar leading coefficients when the degree is a limit ordinal

When the leading coefficient in a maximal variable is a nonzero scalar, the coefficient one
below the top combines with the derivative contribution from the leading power. The resulting
nonzero homogeneous polynomial has the maximal variable's weight. The finite convolution formula
then contradicts the degrees of sufficiently late translated truncations.
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
/-- The first limit configuration is impossible when its leading coefficient has weighted degree
zero. -/
theorem false_of_aeval_eq_zero_of_leadingCoefficientDegree_eq_zero
    (hσ : LiftFamily.HasLowerTruncationDegrees σ) {α : NatOrdinal.{u}}
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt xg β)
    {F : MvPolynomial ι K} (hF : IsWeightedHomogeneous wt F α)
    (hF0 : aeval xg F = 0) {B₀ : ι} (hB₀ : B₀ ∈ F.vars)
    (hmax : ∀ i ∈ F.vars, wt i ≤ wt B₀) (hg : wt B₀ < α)
    {degHD : NatOrdinal.{u}} (hdegHD : degHD + degreeOf B₀ F • wt B₀ = α)
    (hdegHD0 : degHD = 0) : False := by
  classical
  obtain ⟨D, hDdef⟩ : ∃ D, degreeOf B₀ F = D := ⟨_, rfl⟩
  rw [hDdef, hdegHD0, zero_add] at hdegHD
  have hD : 1 ≤ D := by
    rw [← hDdef]
    exact Nat.one_le_iff_ne_zero.mpr (mem_vars_iff_degreeOf_ne_zero.mp hB₀)
  have hD2 : 2 ≤ D := by
    by_contra h
    have hD1 : D = 1 := by omega
    rw [hD1, one_smul] at hdegHD
    exact hg.ne hdegHD
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  have hD'1 : 1 ≤ D' := by omega
  have hFkmem : ∀ k, xCoeff B₀ k F ∈ supported K {B₀}ᶜ := fun k ↦
    xCoeff_mem_supported B₀ k F
  have hFkvars : ∀ k, ∀ i ∈ (xCoeff B₀ k F).vars, wt i ≤ wt B₀ := fun k i hi ↦
    hmax i (vars_xCoeff_subset B₀ k F hi)
  have hαk : ∀ k ≤ D' + 1, ((D' + 1 - k) • wt B₀) + k • wt B₀ = α := by
    intro k hk
    rw [← add_nsmul, Nat.sub_add_cancel hk]
    exact hdegHD
  have hFkhom : ∀ k ≤ D' + 1,
      IsWeightedHomogeneous wt (xCoeff B₀ k F) ((D' + 1 - k) • wt B₀) :=
    fun k hk ↦ xCoeff_isWeightedHomogeneous' B₀ wt hF k (hαk k hk)
  have hFne : F ≠ 0 := by
    rintro rfl
    simp at hB₀
  have hFD : xCoeff B₀ (D' + 1) F ≠ 0 := by
    rw [← hDdef]
    exact xCoeff_degreeOf_ne_zero B₀ hFne
  have hFDhom : IsWeightedHomogeneous wt (xCoeff B₀ (D' + 1) F) 0 := by
    have h := hFkhom (D' + 1) le_rfl
    rwa [Nat.sub_self, zero_smul] at h
  have hFDC : xCoeff B₀ (D' + 1) F =
      MvPolynomial.C ((xCoeff B₀ (D' + 1) F).coeff 0) :=
    OrdinalGraded.eq_C_of_isWeightedHomogeneous_zero hx.ne_zero hFDhom
  let c := (xCoeff B₀ (D' + 1) F).coeff 0
  have hc0 : c ≠ 0 := fun hc ↦ hFD (by
    rw [hFDC]
    change MvPolynomial.C c = 0
    rw [hc, map_zero])
  have hDc : ((D' + 1 : ℕ) : K) * c ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hc0
  let hpoly := xCoeff B₀ D' F +
    MvPolynomial.C (((D' + 1 : ℕ) : K) * c) * X B₀
  have hFD'hom : IsWeightedHomogeneous wt (xCoeff B₀ D' F) (wt B₀) := by
    have h := hFkhom D' (by omega)
    rwa [Nat.add_sub_cancel_left, one_smul] at h
  have hhhom : IsWeightedHomogeneous wt hpoly (wt B₀) := by
    refine hFD'hom.add ?_
    have h := (isWeightedHomogeneous_C wt (((D' + 1 : ℕ) : K) * c)).mul
      (isWeightedHomogeneous_X K wt B₀)
    rwa [zero_add] at h
  have hhne : hpoly ≠ 0 := by
    intro h
    have hc := congrArg (fun p : MvPolynomial ι K ↦ p.coeff (Finsupp.single B₀ 1)) h
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_X,
      ite_eq_left rfl, mul_one, AddMonoidAlgebra.coeff_zero] at hc
    have hleft : (xCoeff B₀ D' F).coeff (Finsupp.single B₀ 1) = 0 := by
      by_contra hne
      exact (mem_supported.mp (hFkmem D'))
        ((mem_vars_iff_mem_support B₀).mpr
          ⟨Finsupp.single B₀ 1, mem_support_iff.mpr hne, by simp⟩) rfl
    rw [hleft, zero_add] at hc
    exact hDc hc
  have hdegree : ν (aeval σ.lift hpoly) = (wt B₀ : WithBot NatOrdinal) := by
    have hrep := σ.represents_aeval hhhom
    have hgrade : aeval xg hpoly ≠ 0 := by
      intro hzero
      exact hhne (((OrdinalGraded.injectiveAt_iff (wt B₀)).mp (hinj _ hg))
        hpoly hhhom hzero)
    exact hrep.degree_eq hgrade
  have hterm : ∀ k ≤ D' + 1, HasLowerTruncationDegree
      (σ.lift B₀ ^ k * aeval σ.lift (xCoeff B₀ k F))
      (k • wt B₀ + (D' + 1 - k) • wt B₀) := by
    intro k hk
    exact (((LiftFamily.hasLowerTruncationDegrees_iff σ).mp hσ B₀).pow k).mul rfl
      (σ.hasLowerTruncationDegree_aeval hσ (hFkhom k hk))
  have hGexp : aeval σ.lift F = ∑ k ∈ Finset.range (D' + 2),
      σ.lift B₀ ^ k * aeval σ.lift (xCoeff B₀ k F) := by
    conv_lhs => rw [← sum_xCoeff_mul_X_pow B₀ F]
    rw [hDdef, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_pow, aeval_X, mul_comm]
  have hα0 : α ≠ 0 := ne_of_gt ((zero_le : (0 : NatOrdinal) ≤ wt B₀).trans_lt hg)
  obtain ⟨bound, hboundα, hcuts⟩ :=
    exists_lt_forall_degree_translatedTruncLE_lt σ hα0 hF hF0
  obtain ⟨l, hl0, hcuts'⟩ := eventually_nhdsLT_iff_exists.mp hcuts
  have hcoeffD' : ∀ γ : G, γ < 0 →
      xCoeff B₀ D' (σ.pol hx α (translatedTruncLE γ (aeval σ.lift F))) =
        σ.pol hx α (translatedTruncLE γ (aeval σ.lift hpoly)) := by
    intro γ hγ
    rw [hGexp, map_sum, σ.pol_sum hx hinj _ _ (fun k hk ↦ by
      have hkD : k ≤ D' + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hdrop := (hterm k hkD).degree_translatedTruncLE_lt hγ
      rwa [add_comm, hαk k hkD] at hdrop), map_sum]
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_eq_zero (fun k hk ↦ ?_), zero_add]
    · have hfreeD' := LiftFamily.FreeOfVariable.aeval (σ := σ) (hx := hx) hσ hinj hg
        hFD'hom hg (hFkmem D') (hFkvars D')
      rw [(LiftFamily.FreeOfVariable.xCoeff_pol_translatedTruncLE_lift_pow_mul
        (σ := σ) (hx := hx) hσ hinj hg hfreeD' D' (by
          rw [add_comm]
          rw [← hdegHD, succ_nsmul, add_comm]) hγ).2]
      have htopterm : σ.lift B₀ ^ (D' + 1) *
          aeval σ.lift (xCoeff B₀ (D' + 1) F) = c • σ.lift B₀ ^ (D' + 1) := by
        rw [hFDC, aeval_C, Algebra.smul_def]
        change σ.lift B₀ ^ (D' + 1) * algebraMap K (Nonpositive G K) c =
          algebraMap K (Nonpositive G K) c * σ.lift B₀ ^ (D' + 1)
        exact mul_comm _ _
      have hpowdrop : ν (translatedTruncLE γ (σ.lift B₀ ^ (D' + 1))) <
          (α : WithBot NatOrdinal) := by
        have h := (((LiftFamily.hasLowerTruncationDegrees_iff σ).mp hσ B₀).pow
          (D' + 1)).degree_translatedTruncLE_lt hγ
        rwa [hdegHD] at h
      rw [htopterm, translatedTruncLE_smul, σ.pol_smul hx hinj c hpowdrop]
      rw [(xCoeff B₀ D').map_smul, LiftFamily.FreeOfVariable.xCoeff_pol_translatedTruncLE_lift_pow
        (σ := σ) (hx := hx) hσ hinj hg D' hdegHD.le hγ]
      rw [smul_eq_C_mul, nsmul_eq_mul, ← C_eq_coe_nat]
      have hC : (MvPolynomial.C c : MvPolynomial ι K) *
          MvPolynomial.C ((D' + 1 : ℕ) : K) =
          MvPolynomial.C (((D' + 1 : ℕ) : K) * c) := by
        rw [← map_mul, mul_comm c]
      rw [← mul_assoc, hC]
      rw [show aeval σ.lift hpoly = aeval σ.lift (xCoeff B₀ D' F) +
          (((D' + 1 : ℕ) : K) * c) • σ.lift B₀ by
        rw [map_add, map_mul, aeval_C, aeval_X, Algebra.smul_def,
          HahnSeries.Nonpositive.algebraMap_apply]]
      rw [map_add, translatedTruncLE_smul, σ.pol_add hx hinj,
        σ.pol_smul hx hinj, smul_eq_C_mul]
      all_goals first
        | have hdrop :=
            HasLowerTruncationDegree.degree_translatedTruncLE_lt
              ((LiftFamily.hasLowerTruncationDegrees_iff σ).mp hσ B₀) hγ
          exact hdrop.trans (WithBot.coe_lt_coe.mpr hg)
        | exact
            (σ.hasLowerTruncationDegree_aeval hσ hFD'hom).degree_translatedTruncLE_lt hγ
            |>.trans
            (WithBot.coe_lt_coe.mpr hg)
        | have hdrop :=
            HasLowerTruncationDegree.degree_translatedTruncLE_lt
              ((LiftFamily.hasLowerTruncationDegrees_iff σ).mp hσ B₀) hγ
          exact (degree_smul_le _ _).trans_lt (hdrop.trans (WithBot.coe_lt_coe.mpr hg))
    · have hkD' : k < D' := Finset.mem_range.mp hk
      have hkD : k ≤ D' + 1 := by omega
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · have hF0hom : IsWeightedHomogeneous wt (xCoeff B₀ 0 F) α := by
          have h := hFkhom 0 hkD
          rw [Nat.sub_zero, hdegHD] at h
          exact h
        rw [pow_zero, one_mul, xCoeff_of_mem_supported B₀
          (LiftFamily.FreeOfVariable.pol_translatedTruncLE_aeval_mem_supported
            (σ := σ) (hx := hx) hσ hinj hg hF0hom (hFkmem 0) (hFkvars 0) hγ) D',
          ite_eq_right (Nat.ne_of_gt hD'1)]
      · have hmk : (D' + 1 - k) • wt B₀ < α := by
          rw [← hαk k hkD]
          exact lt_add_of_pos_right _
            (pos_iff_ne_zero.mpr (NatOrdinal.nsmul_ne_zero_of_ne_zero (hx.ne_zero B₀) hk1))
        have hfreeK := LiftFamily.FreeOfVariable.aeval (σ := σ) (hx := hx) hσ hinj hg
          (hFkhom k hkD) hmk (hFkmem k) (hFkvars k)
        exact (LiftFamily.FreeOfVariable.xCoeff_pol_translatedTruncLE_lift_pow_mul
          (σ := σ) (hx := hx) hσ hinj hg hfreeK k (by
            rw [add_comm]
            exact (hαk k hkD).le) hγ).1 D' hkD'
  have hsep : D' • wt B₀ = 0 ∨
      NatOrdinal.leastTerm (wt B₀) ≤ NatOrdinal.leastTerm (D' • wt B₀) := by
    right
    rw [NatOrdinal.leastTerm_nsmul (hx.ne_zero B₀) hD'1]
  apply σ.false_of_forall_weightedTotalDegree_pol_add_lt hx
    (lam := wt B₀) (sigma := D' • wt B₀) (bound := bound)
    hdegree (hx.ne_zero B₀) hsep (by
      have ha : α = wt B₀ + D' • wt B₀ := by
        rw [← hdegHD, succ_nsmul, add_comm]
      exact hboundα.trans_eq ha) hl0
  · intro γ hlγ hγ hp0
    rw [← hcoeffD' γ hγ] at hp0 ⊢
    exact LiftFamily.weightedTotalDegree_xCoeff_add_nsmul_lt
      (σ.pol_weight_lt_of_degree_lt hx hboundα.le (hcuts' γ hlγ hγ)) B₀ D' hp0
  · exact hg

end HahnSeries.Germ

end
