/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SecondFeedbackUsing

/-!
# Low--low products after the first feedback

The zero-high branch is reduced along the zero-wedge alternatives in the
feedback coefficient space.  The independent alternative is confined to the
four-dimensional first-jet support `K₀` by cubic rows.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- A linear form is supported on the first two coefficients of each input polynomial. -/
@[expose] def InK0Linear (ell : LinearForm) : Prop :=
  ell 2 = 0 ∧ ell 3 = 0 ∧ ell 6 = 0 ∧ ell 7 = 0

theorem normalizedFirstJetVector_inK0 (pa pb ja jb : F₂) :
    InK0Linear (normalizedFirstJetVector pa pb ja jb) := by
  simp [InK0Linear, normalizedFirstJetVector]

theorem feedbackCoeffRep_firstPlane (q : FeedbackCoord)
    (hq : InFirstJetPlane q) :
    feedbackCoeffRep q = q 0 • targetBasis 0 + q 1 • targetBasis 1 := by
  rcases hq with ⟨h2, h3⟩
  funext i
  fin_cases i <;>
    simp [feedbackCoeffRep, targetBasis, Pi.basisFun, rOneCoeff, h2, h3]

theorem targetANF_feedback_firstPlane (q : FeedbackCoord)
    (hq : InFirstJetPlane q) :
    targetANF (feedbackCoeffRep q) = q 0 • Mul 4 0 + q 1 • Mul 4 1 := by
  rw [feedbackCoeffRep_firstPlane q hq]
  change targetANFLinear
      (q 0 • targetBasis 0 + q 1 • targetBasis 1) = _
  rw [map_add, map_smul, map_smul]
  change q 0 • targetANF (targetBasis 0) +
      q 1 • targetANF (targetBasis 1) = _
  rw [targetANF_targetBasis_feedback,
    targetANF_targetBasis_feedback]

theorem feedbackTarget_rationalLow_of_rational
    (q : FeedbackCoord) (hq : IsRationalCoeff (feedbackCoeffRep q)) :
    targetANF (feedbackCoeffRep q) ∈ rationalLowSpace := by
  rcases (IsRationalCoeff_iff (feedbackCoeffRep q)).mp hq with ⟨alpha, ha⟩
  rw [ha]
  change rationalANF alpha ∈ rationalLowSpace
  simpa [representedLowFactor, affineANF, linearANF] using
    representedLowFactor_mem 0 0 alpha

theorem feedbackLowRep_rationalLow_of_rational
    (a : F₂) (ell : LinearForm) (q : FeedbackCoord)
    (hq : IsRationalCoeff (feedbackCoeffRep q)) :
    affineANF a ell + targetANF (feedbackCoeffRep q) ∈ rationalLowSpace := by
  exact Submodule.add_mem _ (Submodule.mem_sup_left (affineANF_mem a ell))
    (feedbackTarget_rationalLow_of_rational q hq)

private theorem zero_feedback_factor_product_mem
    (a b : F₂) (ell m : LinearForm) (c : FeedbackCoord)
    (hprod :
      (affineANF a ell + targetANF (feedbackCoeffRep 0)) *
          (affineANF b m + targetANF (feedbackCoeffRep c)) ∈
        targetAmbient 8 (mulTarget 4)) :
    (affineANF a ell + targetANF (feedbackCoeffRep 0)) *
        (affineANF b m + targetANF (feedbackCoeffRep c)) ∈
      zeroFeedbackLowSpace := by
  have hzeroCoeff : feedbackCoeffRep (0 : FeedbackCoord) = 0 := by
    funext i
    simp [feedbackCoeffRep]
  have hzeroANF : targetANF (feedbackCoeffRep (0 : FeedbackCoord)) = 0 := by
    rw [hzeroCoeff]
    change targetANFLinear 0 = 0
    exact map_zero targetANFLinear
  by_cases hrat : IsRationalCoeff (feedbackCoeffRep c)
  · have hleftLow : affineANF a ell + targetANF (feedbackCoeffRep 0) ∈
        rationalLowSpace := by
      rw [hzeroANF, add_zero]
      exact Submodule.mem_sup_left (affineANF_mem a ell)
    have hrightLow := feedbackLowRep_rationalLow_of_rational b m c hrat
    exact Submodule.mem_sup_left
      (rationalLow_mul_mem_of_mem_targetAmbient hleftLow hrightLow hprod)
  · have hcubic := anfThreeProjection_eq_zero_of_mem_targetAmbient hprod
    have hlinearWedge :
        vectorWedgeTwo ell (targetTwo (feedbackCoeffRep c)) = 0 := by
      rw [hzeroANF, add_zero] at hcubic
      simpa [mul_add, anfThreeProjection_affine_mul_affine, mul_comm (affineANF a ell)
        (targetANF (feedbackCoeffRep c)), anfThreeProjection_target_mul_affine] using hcubic
    have hell : ell = 0 :=
      nonrational_target_vectorWedge_injective hrat hlinearWedge
    rw [hzeroANF, add_zero, hell]
    have haffine : affineANF a 0 = a • (1 : ANF 8) := by
      simp [affineANF, linearANF]
    rw [haffine, smul_mul_assoc]
    exact Submodule.smul_mem _ _
      (by simpa using (show
        affineANF b m + targetANF (feedbackCoeffRep c) ∈
            zeroFeedbackLowSpace from by
        apply Submodule.add_mem
        · exact Submodule.mem_sup_left
            (Submodule.mem_sup_left (affineANF_mem b m))
        · exact feedbackTarget_mem_zeroFeedbackLow c))

private theorem equal_feedback_factor_product_mem
    (a b : F₂) (ell m : LinearForm) (q : FeedbackCoord)
    (hprod :
      (affineANF a ell + targetANF (feedbackCoeffRep q)) *
          (affineANF b m + targetANF (feedbackCoeffRep q)) ∈
        targetAmbient 8 (mulTarget 4)) :
    (affineANF a ell + targetANF (feedbackCoeffRep q)) *
        (affineANF b m + targetANF (feedbackCoeffRep q)) ∈
      zeroFeedbackLowSpace := by
  by_cases hrat : IsRationalCoeff (feedbackCoeffRep q)
  · exact Submodule.mem_sup_left
      (rationalLow_mul_mem_of_mem_targetAmbient
        (feedbackLowRep_rationalLow_of_rational a ell q hrat)
        (feedbackLowRep_rationalLow_of_rational b m q hrat) hprod)
  · have hcubic := anfThreeProjection_eq_zero_of_mem_targetAmbient hprod
    let T := targetANF (feedbackCoeffRep q)
    have hsumWedge :
        vectorWedgeTwo (ell + m) (targetTwo (feedbackCoeffRep q)) = 0 := by
      have hTthree : anfThreeProjection T = 0 :=
        anfThreeProjection_eq_zero_of_mem_targetAmbient
          (Submodule.mem_sup_right (targetANF_mem_mulTarget _))
      change anfThreeProjection
        ((affineANF a ell + T) * (affineANF b m + T)) = 0 at hcubic
      simp only [add_mul, mul_add, map_add] at hcubic
      have hAT : anfThreeProjection (affineANF a ell * T) =
          vectorWedgeTwo ell (targetTwo (feedbackCoeffRep q)) := by
        rw [mul_comm]
        exact anfThreeProjection_target_mul_affine _ _ _
      rw [anfThreeProjection_affine_mul_affine, hAT,
        anfThreeProjection_target_mul_affine, anf_mul_self,
        hTthree, add_zero] at hcubic
      rw [vectorWedgeTwo_add_left]
      simpa [add_comm, add_assoc] using hcubic
    have hsum : ell + m = 0 :=
      nonrational_target_vectorWedge_injective hrat hsumWedge
    have hm : m = ell := by
      funext i
      apply sub_eq_zero.mp
      rw [CharTwo.sub_eq_add]
      have hi := congrFun hsum i
      simpa [add_comm] using hi
    subst m
    let X0 : ANF 8 := linearANF ell + targetANF (feedbackCoeffRep q)
    have hleft : affineANF a ell + targetANF (feedbackCoeffRep q) =
        a • (1 : ANF 8) + X0 := by
      simp [X0, affineANF, add_assoc]
    have hright : affineANF b ell + targetANF (feedbackCoeffRep q) =
        b • (1 : ANF 8) + X0 := by
      simp [X0, affineANF, add_assoc]
    rw [hleft, hright]
    have hproduct :
        (a • (1 : ANF 8) + X0) * (b • (1 : ANF 8) + X0) =
          (a * b) • (1 : ANF 8) + (a + b + 1) • X0 := by
      rcases f2_eq_zero_or_one a with rfl | rfl <;>
        rcases f2_eq_zero_or_one b with rfl | rfl <;>
        simp [add_mul, mul_add, anf_mul_self] <;>
        ring_nf <;>
        try simp [N3Certificate.two_eq_zero_f2, N3Certificate.three_eq_one_f2]
    rw [hproduct]
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      apply Submodule.mem_sup_left
      apply Submodule.mem_sup_left
      have hone : affineANF 1 0 = (1 : ANF 8) := by
        simp [affineANF, linearANF]
      rw [← hone]
      exact affineANF_mem 1 0
    · apply Submodule.smul_mem
      apply Submodule.add_mem
      · exact Submodule.mem_sup_left
          (Submodule.mem_sup_left (by simpa [affineANF] using affineANF_mem 0 ell))
      · exact feedbackTarget_mem_zeroFeedbackLow q

/-- An input coordinate outside the normalized first-jet support. -/
@[expose]
def OutsideK0Index (i : Fin 8) : Prop :=
  i = 2 ∨ i = 3 ∨ i = 6 ∨ i = 7

theorem anfThreeProjection_affine_mul_target
    (a : F₂) (ell : LinearForm) (c : TargetCoeff) :
    anfThreeProjection (affineANF a ell * targetANF c) =
      vectorWedgeTwo ell (targetTwo c) := by
  rw [mul_comm]
  exact anfThreeProjection_target_mul_affine c a ell

theorem monomialThree_eq_zero_of_not_mem
    (s : Finset (Fin 8)) (i j k : Fin 8) (hi : i ∉ s) :
    monomialThree s i j k = 0 := by
  simp only [monomialThree]
  split_ifs with hcard hs
  · exfalso
    apply hi
    rw [hs]
    simp
  · rfl
  · rfl

private theorem firstPlane_targetProduct_cubic_rows
    (q c : FeedbackCoord) (hq : InFirstJetPlane q)
    (hc : InFirstJetPlane c) (z : Fin 8) (hz : OutsideK0Index z) :
    anfThreeProjection
        (targetANF (feedbackCoeffRep q) *
          targetANF (feedbackCoeffRep c)) z 0 4 = 0 ∧
      anfThreeProjection
        (targetANF (feedbackCoeffRep q) *
          targetANF (feedbackCoeffRep c)) z 0 5 = 0 := by
  rw [targetANF_feedback_firstPlane q hq,
    targetANF_feedback_firstPlane c hc]
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp (disch := decide)
      [mul_target_zero_anf, mul_target_one_anf,
        anfThreeProjection_monomial,
        monomialThree_eq_zero_of_not_mem,
        monomial_mul, add_mul, mul_add]

private theorem firstPlane_scalar_det_one :
    ∀ q0 q1 c0 c1 : F₂,
      (q0 ≠ 0 ∨ q1 ≠ 0) → (c0 ≠ 0 ∨ c1 ≠ 0) →
      (q0 ≠ c0 ∨ q1 ≠ c1) → c0 * q1 + c1 * q0 = 1 := by
  decide

private theorem firstPlane_independent_det_one
    (q c : FeedbackCoord)
    (hq : InFirstJetPlane q) (hc : InFirstJetPlane c)
    (hq0 : q ≠ 0) (hc0 : c ≠ 0) (hqc : q ≠ c) :
    c 0 * q 1 + c 1 * q 0 = 1 := by
  have hqne : q 0 ≠ 0 ∨ q 1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hq0
    funext i
    fin_cases i <;> simp [h.1, h.2, hq.1, hq.2]
  have hcne : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hc0
    funext i
    fin_cases i <;> simp [h.1, h.2, hc.1, hc.2]
  have hne : q 0 ≠ c 0 ∨ q 1 ≠ c 1 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hqc
    funext i
    fin_cases i <;> simp [h.1, h.2, hq.1, hq.2, hc.1, hc.2]
  exact firstPlane_scalar_det_one _ _ _ _ hqne hcne hne

private theorem solve_firstPlane_pair
    (c0 c1 q0 q1 x y : F₂)
    (hdet : c0 * q1 + c1 * q0 = 1)
    (h0 : x * c0 + y * q0 = 0)
    (h1 : x * c1 + y * q1 = 0) : x = 0 ∧ y = 0 := by
  revert c0 c1 q0 q1 x y
  decide

theorem independentFirstPlane_linears_inK0
    (a b : F₂) (ell m : LinearForm) (q c : FeedbackCoord)
    (hq : InFirstJetPlane q) (hc : InFirstJetPlane c)
    (hq0 : q ≠ 0) (hc0 : c ≠ 0) (hqc : q ≠ c)
    (hprod :
      (affineANF a ell + targetANF (feedbackCoeffRep q)) *
          (affineANF b m + targetANF (feedbackCoeffRep c)) ∈
        targetAmbient 8 (mulTarget 4)) :
    InK0Linear ell ∧ InK0Linear m := by
  have hthree := anfThreeProjection_eq_zero_of_mem_targetAmbient hprod
  simp only [add_mul, mul_add, map_add, anfThreeProjection_affine_mul_affine,
    anfThreeProjection_affine_mul_target, anfThreeProjection_target_mul_affine, zero_add
    ] at hthree
  have hdet := firstPlane_independent_det_one q c hq hc hq0 hc0 hqc
  have solveZ (z : Fin 8) (hz : OutsideK0Index z) :
      ell z = 0 ∧ m z = 0 := by
    have htarget := firstPlane_targetProduct_cubic_rows q c hq hc z hz
    have hrow0 := congrFun (congrFun (congrFun hthree z) 0) 4
    have hrow1 := congrFun (congrFun (congrFun hthree z) 0) 5
    rcases hq with ⟨hq2, hq3⟩
    rcases hc with ⟨hc2, hc3⟩
    have hzv : z = 2 ∨ z = 3 ∨ z = 6 ∨ z = 7 := hz
    rcases hzv with rfl | rfl | rfl | rfl <;>
      simp only [feedbackCoeffRep, Fin.isValue, targetBasis, Pi.basisFun,
        Module.Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply, hq2,
        zero_smul, add_zero, hq3, rOneCoeff, hc2, hc3, Pi.add_apply, vectorWedgeTwo,
        targetTwo, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.ofNat_pos, ↓reduceDIte,
        Nat.reduceMod, Std.le_refl, tsub_self, Fin.zero_eta, Pi.smul_apply, Pi.single_eq_same,
        smul_eq_mul, mul_one, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne,
        mul_zero, Nat.reduceLT, Fin.reduceFinMk, Fin.reduceEq, nonpos_iff_eq_zero,
        OfNat.ofNat_ne_zero, Pi.zero_apply, Nat.reduceLeDiff, Nat.reduceSub, zero_add,
        Fin.mk_one, one_ne_zero, Nat.reduceAdd, Nat.lt_add_one, lt_self_iff_false,
        Nat.mod_succ] at hrow0 hrow1 htarget ⊢
        <;>
      exact solve_firstPlane_pair _ _ _ _ _ _ hdet
        (by simpa [htarget.1, add_comm] using hrow0)
        (by simpa [htarget.2, add_comm] using hrow1)
  have h2 := solveZ 2 (Or.inl rfl)
  have h3 := solveZ 3 (Or.inr (Or.inl rfl))
  have h6 := solveZ 6 (Or.inr (Or.inr (Or.inl rfl)))
  have h7 := solveZ 7 (Or.inr (Or.inr (Or.inr rfl)))
  exact ⟨⟨h2.1, h3.1, h6.1, h7.1⟩,
    ⟨h2.2, h3.2, h6.2, h7.2⟩⟩

/-- The same outside-row solve when the cubic part is the normalized seed
rather than zero.  The seed has no row leaving `K₀`, so the two scalar
equations used above are unchanged. -/
theorem independentFirstPlane_linears_inK0_of_seedCubic
    (a b : F₂) (ell m M : LinearForm) (q c : FeedbackCoord)
    (hq : InFirstJetPlane q) (hc : InFirstJetPlane c)
    (hq0 : q ≠ 0) (hc0 : c ≠ 0) (hqc : q ≠ c)
    (hM : InK0Linear M)
    (hthree :
      anfThreeProjection
          ((affineANF a ell + targetANF (feedbackCoeffRep q)) *
            (affineANF b m + targetANF (feedbackCoeffRep c))) =
        vectorWedgeTwo M (rationalPlaceTwo 0)) :
    InK0Linear ell ∧ InK0Linear m := by
  have hthree' := hthree
  simp only [add_mul, mul_add, map_add, anfThreeProjection_affine_mul_affine,
    anfThreeProjection_affine_mul_target, anfThreeProjection_target_mul_affine, zero_add
    ] at hthree'
  have hdet := firstPlane_independent_det_one q c hq hc hq0 hc0 hqc
  have solveZ (z : Fin 8) (hz : OutsideK0Index z) :
      ell z = 0 ∧ m z = 0 := by
    have htarget := firstPlane_targetProduct_cubic_rows q c hq hc z hz
    have hrow0 := congrFun (congrFun (congrFun hthree' z) 0) 4
    have hrow1 := congrFun (congrFun (congrFun hthree' z) 0) 5
    have hseed0 : vectorWedgeTwo M (rationalPlaceTwo 0) z 0 4 = 0 := by
      rcases hM with ⟨hM2, hM3, hM6, hM7⟩
      rcases hz with rfl | rfl | rfl | rfl <;>
        simp [vectorWedgeTwo, rationalPlaceTwo, vectorWedge, placeA, placeB, hM2, hM3, hM6,
          hM7]
    have hseed1 : vectorWedgeTwo M (rationalPlaceTwo 0) z 0 5 = 0 := by
      rcases hM with ⟨hM2, hM3, hM6, hM7⟩
      rcases hz with rfl | rfl | rfl | rfl <;>
        simp [vectorWedgeTwo, rationalPlaceTwo, vectorWedge, placeA, placeB, hM2, hM3, hM6,
          hM7]
    rw [hseed0] at hrow0
    rw [hseed1] at hrow1
    rcases hq with ⟨hq2, hq3⟩
    rcases hc with ⟨hc2, hc3⟩
    have hzv : z = 2 ∨ z = 3 ∨ z = 6 ∨ z = 7 := hz
    rcases hzv with rfl | rfl | rfl | rfl <;>
      simp only [feedbackCoeffRep, Fin.isValue, targetBasis, Pi.basisFun,
        Module.Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply, hq2,
        zero_smul, add_zero, hq3, rOneCoeff, hc2, hc3, Pi.add_apply, vectorWedgeTwo,
        targetTwo, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.ofNat_pos, ↓reduceDIte,
        Nat.reduceMod, Std.le_refl, tsub_self, Fin.zero_eta, Pi.smul_apply, Pi.single_eq_same,
        smul_eq_mul, mul_one, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne,
        mul_zero, Nat.reduceLT, Fin.reduceFinMk, Fin.reduceEq, nonpos_iff_eq_zero,
        OfNat.ofNat_ne_zero, Nat.reduceLeDiff, Nat.reduceSub, zero_add, Fin.mk_one,
        one_ne_zero, Nat.reduceAdd, Nat.lt_add_one, lt_self_iff_false, Nat.mod_succ
        ] at hrow0 hrow1 htarget ⊢ <;>
      exact solve_firstPlane_pair _ _ _ _ _ _ hdet
        (by simpa [htarget.1, add_comm] using hrow0)
        (by simpa [htarget.2, add_comm] using hrow1)
  have h2 := solveZ 2 (Or.inl rfl)
  have h3 := solveZ 3 (Or.inr (Or.inl rfl))
  have h6 := solveZ 6 (Or.inr (Or.inr (Or.inl rfl)))
  have h7 := solveZ 7 (Or.inr (Or.inr (Or.inr rfl)))
  exact ⟨⟨h2.1, h3.1, h6.1, h7.1⟩,
    ⟨h2.2, h3.2, h6.2, h7.2⟩⟩

theorem linearANF_eq_k0 (ell : LinearForm) (h : InK0Linear ell) :
    linearANF ell = ell 0 • X 0 + ell 1 • X 1 +
      ell 4 • X 4 + ell 5 • X 5 := by
  rcases h with ⟨h2, h3, h6, h7⟩
  rw [linearANF]
  simp [Fin.sum_univ_succ, h2, h3, h6, h7, add_assoc]

theorem monomialTwo_eq_zero_of_not_mem
    (s : Finset (Fin 8)) (i j : Fin 8) (hi : i ∉ s) :
    monomialTwo s i j = 0 := by
  simp only [monomialTwo]
  split_ifs with hij hs
  · rfl
  · exfalso
    apply hi
    rw [hs]
    simp
  · rfl

theorem firstPlane_product_two_outside
    (a b : F₂) (ell m : LinearForm) (q c : FeedbackCoord)
    (hell : InK0Linear ell) (hm : InK0Linear m)
    (hq : InFirstJetPlane q) (hc : InFirstJetPlane c)
    (z : Fin 8) (hz : OutsideK0Index z) :
    ∀ j : Fin 8,
      anfTwoProjection
        ((affineANF a ell + targetANF (feedbackCoeffRep q)) *
          (affineANF b m + targetANF (feedbackCoeffRep c))) z j = 0 := by
  intro j
  rw [targetANF_feedback_firstPlane q hq,
    targetANF_feedback_firstPlane c hc,
    show affineANF a ell = a • (1 : ANF 8) + linearANF ell by rfl,
    show affineANF b m = b • (1 : ANF 8) + linearANF m by rfl,
    linearANF_eq_k0 ell hell, linearANF_eq_k0 m hm]
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp (disch := decide)
      [mul_target_zero_anf, mul_target_one_anf,
        X, monomial_mul, anfTwoProjection_monomial,
        anfTwoProjection_one, monomialTwo_eq_zero_of_not_mem,
        add_mul, mul_add]

private theorem coeff_mem_feedback_of_tail_zero
    (d : TargetCoeff)
    (h2 : d 2 = 0) (h3 : d 3 = 0) (h4 : d 4 = 0)
    (h5 : d 5 = 0) (h6 : d 6 = 0) : d ∈ feedbackCoeffSpace := by
  apply (mem_feedbackCoeffSpace_iff_exists_rep d).mpr
  let q : FeedbackCoord := ![d 0, d 1, 0, 0]
  refine ⟨q, ?_⟩
  funext i
  fin_cases i <;>
    simp [q, feedbackCoeffRep, targetBasis, Pi.basisFun, rOneCoeff, h2, h3, h4, h5, h6]

private theorem independent_firstPlane_product_mem
    (a b : F₂) (ell m : LinearForm) (q c : FeedbackCoord)
    (hq : InFirstJetPlane q) (hc : InFirstJetPlane c)
    (hq0 : q ≠ 0) (hc0 : c ≠ 0) (hqc : q ≠ c)
    (hprod :
      (affineANF a ell + targetANF (feedbackCoeffRep q)) *
          (affineANF b m + targetANF (feedbackCoeffRep c)) ∈
        targetAmbient 8 (mulTarget 4)) :
    (affineANF a ell + targetANF (feedbackCoeffRep q)) *
        (affineANF b m + targetANF (feedbackCoeffRep c)) ∈
      zeroFeedbackLowSpace := by
  rcases independentFirstPlane_linears_inK0
      a b ell m q c hq hc hq0 hc0 hqc hprod with ⟨hell, hm⟩
  rcases exists_targetAmbient_rep hprod with ⟨u, d, hu, hrep⟩
  rcases exists_affineANF_of_mem hu with ⟨A, L, huA⟩
  have hrep' :
      (affineANF a ell + targetANF (feedbackCoeffRep q)) *
          (affineANF b m + targetANF (feedbackCoeffRep c)) =
        affineANF A L + targetANF d := by
    rw [hrep, huA]
  have hproj := congrArg anfTwoProjection hrep'
  rw [map_add, anfTwoProjection_kills_affine (affineANF_mem A L),
    anfTwoProjection_targetANF, zero_add] at hproj
  have hz := firstPlane_product_two_outside a b ell m q c
    hell hm hq hc
  have row (i j : Fin 8) (hi : OutsideK0Index i) :
      targetTwo d i j = 0 := by
    rw [← hproj]
    exact hz i hi j
  have h2 : d 2 = 0 := by
    simpa [targetTwo, aCoord, bCoord] using
      row 2 4 (Or.inl rfl)
  have h3 : d 3 = 0 := by
    simpa [targetTwo, aCoord, bCoord] using
      row 3 4 (Or.inr (Or.inl rfl))
  have h4 : d 4 = 0 := by
    simpa [targetTwo, aCoord, bCoord] using
      row 3 5 (Or.inr (Or.inl rfl))
  have h5 : d 5 = 0 := by
    simpa [targetTwo, aCoord, bCoord] using
      row 3 6 (Or.inr (Or.inl rfl))
  have h6 : d 6 = 0 := by
    simpa [targetTwo, aCoord, bCoord] using
      row 3 7 (Or.inr (Or.inl rfl))
  rw [hrep']
  exact (targetRep_mem_zeroFeedbackLow_iff A L d).mpr
    (coeff_mem_feedback_of_tail_zero d h2 h3 h4 h5 h6)

/-- A product of two feedback-low wires whose high part vanishes cannot
leave the feedback-low state. -/
theorem feedbackLow_mul_mem_of_mem_targetAmbient
    {p r : ANF 8} (hp : p ∈ zeroFeedbackLowSpace)
    (hr : r ∈ zeroFeedbackLowSpace)
    (hprod : p * r ∈ targetAmbient 8 (mulTarget 4)) :
    p * r ∈ zeroFeedbackLowSpace := by
  rcases exists_feedbackLow_rep hp with ⟨a, ell, q, hpRep⟩
  rcases exists_feedbackLow_rep hr with ⟨b, m, c, hrRep⟩
  rw [hpRep, hrRep] at hprod ⊢
  have hquartic : feedbackQuarticProbeANF
      ((affineANF a ell + targetANF (feedbackCoeffRep q)) *
        (affineANF b m + targetANF (feedbackCoeffRep c))) = 0 :=
    feedbackQuarticProbeANF_eq_zero_of_degreeLE_three
      ((targetAmbient_le_quadraticANFSpace hprod).mono (by omega))
  rcases feedbackProduct_zeroWedgeStructure a b ell m q c hquartic with
    hq | hc | hqc | hfirst
  · subst q
    exact zero_feedback_factor_product_mem a b ell m c hprod
  · subst c
    rw [mul_comm] at hprod ⊢
    exact zero_feedback_factor_product_mem b a m ell q hprod
  · subst c
    exact equal_feedback_factor_product_mem a b ell m q hprod
  · rcases hfirst with ⟨hqPlane, hcPlane⟩
    by_cases hq0 : q = 0
    · subst q
      exact zero_feedback_factor_product_mem a b ell m c hprod
    by_cases hc0 : c = 0
    · subst c
      rw [mul_comm] at hprod ⊢
      exact zero_feedback_factor_product_mem b a m ell q hprod
    by_cases hqc : q = c
    · subst c
      exact equal_feedback_factor_product_mem a b ell m q hprod
    exact independent_firstPlane_product_mem a b ell m q c
      hqPlane hcPlane hq0 hc0 hqc hprod

end

end N4
end UnrestrictedBooleanMul
