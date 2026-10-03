/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SecondFeedbackLow

/-!
# Jet separation from a two-wedge shadow

This is the interface between the homogeneous bookkeeping of a cancelled
low--low product and the coordinate `jet_separation` lemma.  All terms wholly
supported in `K₀` disappear on the four outside slices; the two remaining
wedge directions give a subspace of rank at most two.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Every row indexed outside the normalized first-jet coordinates vanishes. -/
@[expose]
def SupportedK0Two (k : TwoForm) : Prop :=
  ∀ z j : Fin 8, OutsideK0Index z → k z j = 0

theorem SupportedK0Two.zero : SupportedK0Two 0 := by
  intro z j hz
  rfl

theorem SupportedK0Two.add {k l : TwoForm}
    (hk : SupportedK0Two k) (hl : SupportedK0Two l) :
    SupportedK0Two (k + l) := by
  intro z j hz
  simp [hk z j hz, hl z j hz]

theorem SupportedK0Two.smul (a : F₂) {k : TwoForm}
    (hk : SupportedK0Two k) : SupportedK0Two (a • k) := by
  intro z j hz
  simp [hk z j hz]

theorem SupportedK0Two.vectorWedge {u v : LinearForm}
    (hu : InK0Linear u) (hv : InK0Linear v) :
    SupportedK0Two (vectorWedge u v) := by
  intro z j hz
  rcases hu with ⟨hu2, hu3, hu6, hu7⟩
  rcases hv with ⟨hv2, hv3, hv6, hv7⟩
  unfold UnrestrictedBooleanMul.N4.vectorWedge
  rcases hz with rfl | rfl | rfl | rfl
  · rw [hu2, hv2]
    ring
  · rw [hu3, hv3]
    ring
  · rw [hu6, hv6]
    ring
  · rw [hu7, hv7]
    ring

private theorem twoGenerator_mem
    (M N : LinearForm) (a b : F₂) :
    a • M + b • N ∈
      Submodule.span F₂ (Set.range ![M, N]) := by
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨0, by simp⟩)
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨1, by simp⟩)

/-- Coordinate wrapper for `jet_separation`: a target shadow consisting of a
feedback term, a `K₀` term, and two wedge directions is already feedback. -/
theorem jet_separation_of_twoWedge_shadow
    (M N p r : LinearForm) (k : TwoForm) (s d : TargetCoeff)
    (hM : InK0Linear M) (hN : InK0Linear N)
    (hk : SupportedK0Two k) (hs : s ∈ feedbackCoeffSpace)
    (hUne : Submodule.span F₂ (Set.range ![M, N]) ≠ anchorPlane)
    (hshadow : targetTwo d = targetTwo s + k +
      vectorWedge M p + vectorWedge N r) :
    d ∈ feedbackCoeffSpace := by
  rcases (mem_feedbackCoeffSpace_iff_exists_rep s).mp hs with ⟨q, rfl⟩
  let U : Submodule F₂ LinearForm :=
    Submodule.span F₂ (Set.range ![M, N])
  have hUdim : Module.finrank F₂ U ≤ 2 := by
    exact (finrank_span_le_card (Set.range ![M, N])).trans (by
      rw [Set.toFinset_card]
      simpa using Fintype.card_range_le ![M, N])
  rcases hM with ⟨hM2, hM3, hM6, hM7⟩
  rcases hN with ⟨hN2, hN3, hN6, hN7⟩
  have eqAt (i j : Fin 8) := congrFun (congrFun hshadow i) j
  have e20 := eqAt 2 0
  have e21 := eqAt 2 1
  have e24 := eqAt 2 4
  have e25 := eqAt 2 5
  have e26 := eqAt 2 6
  have e27 := eqAt 2 7
  have e30 := eqAt 3 0
  have e31 := eqAt 3 1
  have e34 := eqAt 3 4
  have e35 := eqAt 3 5
  have e60 := eqAt 6 0
  have e61 := eqAt 6 1
  have e64 := eqAt 6 4
  have e65 := eqAt 6 5
  have e70 := eqAt 7 0
  have e71 := eqAt 7 1
  have e74 := eqAt 7 4
  have e75 := eqAt 7 5
  have hk2 (j : Fin 8) : k 2 j = 0 := hk 2 j (Or.inl rfl)
  have hk3 (j : Fin 8) : k 3 j = 0 :=
    hk 3 j (Or.inr (Or.inl rfl))
  have hk6 (j : Fin 8) : k 6 j = 0 :=
    hk 6 j (Or.inr (Or.inr (Or.inl rfl)))
  have hk7 (j : Fin 8) : k 7 j = 0 :=
    hk 7 j (Or.inr (Or.inr (Or.inr rfl)))
  simp only [targetTwo, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceLT,
    ↓reduceDIte, Nat.zero_mod, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, feedbackCoeffRep,
    Pi.add_apply, hk2, add_zero, vectorWedge, hM2, zero_mul, zero_add, hN2, Nat.one_mod,
    Nat.not_ofNat_le_one, Std.le_refl, tsub_self, Fin.reduceFinMk, Pi.smul_apply,
    targetBasis_apply, Fin.reduceEq, ↓reduceIte, smul_eq_mul, mul_zero, rOneCoeff_apply,
    mul_one, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceAdd, hM6, hN6, Nat.mod_succ, hM7, hN7,
    Nat.lt_add_one, hk3, hM3, hN3, Nat.ofNat_pos, hk6, Nat.one_lt_ofNat, lt_self_iff_false,
    hk7] at e20 e21 e24 e25 e26 e27 e30 e31 e34 e35 e60 e61 e64 e65 e70 e71 e74 e75
  have hOutside :
      targetTwo (jetResidualCoeff d) (aCoord 2) (bCoord 2) = 0 := by
    have hC : jetC d = 0 := by
      simp only [jetC, Fin.isValue]
      rw [e26, e27]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    simpa [jetResidualCoeff, jetC, jetA, jetB, targetTwo_cross, targetBasis, Pi.basisFun] using hC
  have hA2eq : jetSliceA2 d = p 2 • M + r 2 • N := by
    funext i
    fin_cases i
    · simp [jetSliceA2, jetA, jetB, bLinear, bCoord, Pi.basisFun]
      simpa [mul_comm] using e20
    · simp [jetSliceA2, jetA, jetB, bLinear, bCoord, Pi.basisFun]
      simpa [mul_comm] using e21
    · simp [jetSliceA2, bLinear, bCoord, Pi.basisFun, hM2, hN2]
    · simp [jetSliceA2, bLinear, bCoord, Pi.basisFun, hM3, hN3]
    · simp only [jetSliceA2, jetA, Fin.isValue, bLinear, Pi.basisFun, bCoord,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.reduceFinMk,
      Module.Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply, jetB,
      Nat.one_mod, Nat.reduceAdd, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, ne_eq, Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne, mul_zero]
      rw [e24, e27]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    · simp only [jetSliceA2, jetA, Fin.isValue, bLinear, Pi.basisFun, bCoord,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.reduceFinMk,
      Module.Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply, jetB,
      Nat.one_mod, Nat.reduceAdd, Pi.add_apply, Pi.smul_apply, ne_eq, Fin.reduceEq,
      not_false_eq_true, Pi.single_eq_of_ne, smul_eq_mul, mul_zero, Pi.single_eq_same,
      mul_one, zero_add]
      rw [e25, e27]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    · simp [jetSliceA2, bLinear, bCoord, Pi.basisFun, hM6, hN6]
    · simp [jetSliceA2, bLinear, bCoord, Pi.basisFun, hM7, hN7]
  have hA3eq : jetSliceA3 d = p 3 • M + r 3 • N := by
    funext i
    fin_cases i
    · simp [jetSliceA3, jetB, bLinear, bCoord, Pi.basisFun]
      simpa [mul_comm] using e30
    · simp [jetSliceA3, jetB, bLinear, bCoord, Pi.basisFun]
      simpa [mul_comm] using e31
    · simp [jetSliceA3, bLinear, bCoord, Pi.basisFun, hM2, hN2]
    · simp [jetSliceA3, bLinear, bCoord, Pi.basisFun, hM3, hN3]
    · simp only [jetSliceA3, jetB, Fin.isValue, bLinear, Pi.basisFun, bCoord,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.reduceFinMk,
      Module.Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
      Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.add_apply]
      rw [e34, e27]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    · simp [jetSliceA3, bLinear, bCoord, Pi.basisFun]
      linear_combination e35 - e26
    · simp [jetSliceA3, bLinear, bCoord, Pi.basisFun, hM6, hN6]
    · simp [jetSliceA3, bLinear, bCoord, Pi.basisFun, hM7, hN7]
  have hB2eq : jetSliceB2 d = p 6 • M + r 6 • N := by
    funext i
    fin_cases i
    · simp only [jetSliceB2, jetA, Fin.isValue, aLinear, Pi.basisFun, aCoord,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta, Module.Basis.coe_ofEquivFun,
      LinearEquiv.refl_symm, LinearEquiv.refl_apply, jetB, Nat.one_mod, Fin.mk_one,
      Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, ne_eq,
      zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero]
      rw [e60, e27]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    · simp only [jetSliceB2, jetA, Fin.isValue, aLinear, Pi.basisFun, aCoord,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta, Module.Basis.coe_ofEquivFun,
      LinearEquiv.refl_symm, LinearEquiv.refl_apply, jetB, Nat.one_mod, Fin.mk_one,
      Pi.add_apply, Pi.smul_apply, ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne,
      smul_eq_mul, mul_zero, Pi.single_eq_same, mul_one, zero_add]
      rw [e61, e27]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    · simp [jetSliceB2, aLinear, aCoord, Pi.basisFun, hM2, hN2]
    · simp [jetSliceB2, aLinear, aCoord, Pi.basisFun, hM3, hN3]
    · simp [jetSliceB2, aLinear, aCoord, Pi.basisFun]
      simpa [mul_comm] using e64
    · simp [jetSliceB2, aLinear, aCoord, Pi.basisFun]
      simpa [mul_comm] using e65
    · simp [jetSliceB2, aLinear, aCoord, Pi.basisFun, hM6, hN6]
    · simp [jetSliceB2, aLinear, aCoord, Pi.basisFun, hM7, hN7]
  have hB3eq : jetSliceB3 d = p 7 • M + r 7 • N := by
    funext i
    fin_cases i
    · simp only [jetSliceB3, jetB, Fin.isValue, aLinear, Pi.basisFun, aCoord,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta, Module.Basis.coe_ofEquivFun,
      LinearEquiv.refl_symm, LinearEquiv.refl_apply, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one, Pi.add_apply]
      rw [e70, e27]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    · simp [jetSliceB3, aLinear, aCoord, Pi.basisFun]
      linear_combination e71 - e26
    · simp [jetSliceB3, aLinear, aCoord, Pi.basisFun, hM2, hN2]
    · simp [jetSliceB3, aLinear, aCoord, Pi.basisFun, hM3, hN3]
    · simp [jetSliceB3, aLinear, aCoord, Pi.basisFun]
      simpa [mul_comm] using e74
    · simp [jetSliceB3, aLinear, aCoord, Pi.basisFun]
      simpa [mul_comm] using e75
    · simp [jetSliceB3, aLinear, aCoord, Pi.basisFun, hM6, hN6]
    · simp [jetSliceB3, aLinear, aCoord, Pi.basisFun, hM7, hN7]
  apply jet_separation U hUdim hUne d hOutside
  · rw [hA2eq]
    exact twoGenerator_mem M N (p 2) (r 2)
  · rw [hA3eq]
    exact twoGenerator_mem M N (p 3) (r 3)
  · rw [hB2eq]
    exact twoGenerator_mem M N (p 6) (r 6)
  · rw [hB3eq]
    exact twoGenerator_mem M N (p 7) (r 7)

end

end N4
end UnrestrictedBooleanMul
