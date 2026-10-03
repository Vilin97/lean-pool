/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.TwoForm

/-!
# Cubic seed normal form

This file formalizes the exterior-algebra core of the manuscript's
low-product normal form.  It is deliberately independent of circuit syntax:
two rational-place quadratic parts with vanishing quartic wedge share one
quadratic direction, and the remaining cubic is a single vector wedged with
that direction.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

@[simp] theorem vectorWedge_self (x : LinearForm) : vectorWedge x x = 0 := by
  funext i j
  simp only [vectorWedge, Pi.zero_apply]
  rw [mul_comm (x j) (x i)]
  exact @CharTwo.add_self_eq_zero F₂ _ _ (x i * x j)

theorem vectorWedge_comm (x y : LinearForm) :
    vectorWedge x y = vectorWedge y x := by
  funext i j
  simp only [vectorWedge]
  ring

theorem vectorWedgeTwo_add_left (x y : LinearForm) (q : TwoForm) :
    vectorWedgeTwo (x + y) q = vectorWedgeTwo x q + vectorWedgeTwo y q := by
  funext i j k
  simp only [vectorWedgeTwo, Pi.add_apply]
  ring

theorem vectorWedgeTwo_zero_left (q : TwoForm) :
    vectorWedgeTwo (0 : LinearForm) q = 0 := by
  funext i j k
  simp [vectorWedgeTwo]

theorem vectorWedgeTwo_zero_right (x : LinearForm) :
    vectorWedgeTwo x (0 : TwoForm) = 0 := by
  funext i j k
  simp [vectorWedgeTwo]

theorem rationalTwo_zero : rationalTwo (0 : Fin 3 → F₂) = 0 := by
  funext i j
  simp [rationalTwo]

theorem vectorWedge_add_right (x y z : LinearForm) :
    vectorWedge x (y + z) = vectorWedge x y + vectorWedge x z := by
  funext i j
  simp only [vectorWedge, Pi.add_apply]
  ring

/-- Cubic high part of a product whose linear factors are `ell,m` and whose
quadratic factors have rational-place coefficient words `α,β`. -/
@[expose] def rationalProductCubic (ell m : LinearForm) (α β : Fin 3 → F₂) : ThreeForm :=
  vectorWedgeTwo ell (rationalTwo β) + vectorWedgeTwo m (rationalTwo α)

/-- Boolean degree-lowering contraction: the quadratic part created when a
linear form multiplies a quadratic form and repeats one of its variables. -/
@[expose] def booleanContraction (ell : LinearForm) (q : TwoForm) : TwoForm :=
  fun i j => (ell i + ell j) * q i j

/-- Quadratic terms created by multiplying identical quadratic monomials. -/
@[expose] def twoHadamard (q c : TwoForm) : TwoForm := fun i j => q i j * c i j

/-- Boolean contraction along a rational-place support only rescales that
place.  The two support vectors use disjoint `A` and `B` coordinates. -/
theorem booleanContraction_rationalPlace (a b : F₂) (θ : Fin 3) :
    booleanContraction (a • placeA θ + b • placeB θ)
        (rationalPlaceTwo θ) =
      (a + b) • rationalPlaceTwo θ := by
  funext i j
  fin_cases θ <;> fin_cases i <;> fin_cases j <;>
    simp [booleanContraction, rationalPlaceTwo, vectorWedge, placeA, placeB] <;> ring

/-- Complete quadratic shadow of a product
`(a + ell + Q) * (b + m + C)`. -/
@[expose] def rationalProductQuadratic (a b : F₂) (ell m : LinearForm)
    (α β : Fin 3 → F₂) : TwoForm :=
  a • rationalTwo β + b • rationalTwo α + vectorWedge ell m +
    booleanContraction ell (rationalTwo β) +
    booleanContraction m (rationalTwo α) +
    twoHadamard (rationalTwo α) (rationalTwo β)

/-- Exterior low-product normal form.  The equality `wedgeTwo Q C = 0`
forces the two rational coefficient vectors to be dependent.  The three
possible dependencies over `F₂` give the normal form directly. -/
theorem low_product_normal_form_exterior
    (ell m : LinearForm) (α β : Fin 3 → F₂)
    (hquartic : wedgeTwo (rationalTwo α) (rationalTwo β) = 0)
    (hcubic : rationalProductCubic ell m α β ≠ 0) :
    ∃ (γ : Fin 3 → F₂) (N z : LinearForm),
      γ ≠ 0 ∧
      rationalProductCubic ell m α β = vectorWedgeTwo N (rationalTwo γ) ∧
      vectorWedge ell m = vectorWedge z N := by
  rcases rational_wedge_zero_dependent α β hquartic with hα | hβ | hαβ
  · subst α
    have hβ0 : β ≠ 0 := by
      intro h
      subst β
      apply hcubic
      simp [rationalProductCubic, rationalTwo_zero, vectorWedgeTwo_zero_right]
    refine ⟨β, ell, m, hβ0, ?_, ?_⟩
    · simp [rationalProductCubic, rationalTwo_zero, vectorWedgeTwo_zero_right]
    · exact vectorWedge_comm ell m
  · subst β
    have hα0 : α ≠ 0 := by
      intro h
      subst α
      apply hcubic
      simp [rationalProductCubic, rationalTwo_zero, vectorWedgeTwo_zero_right]
    refine ⟨α, m, ell, hα0, ?_, ?_⟩
    · simp [rationalProductCubic, rationalTwo_zero, vectorWedgeTwo_zero_right]
    · rfl
  · subst β
    have hα0 : α ≠ 0 := by
      intro h
      subst α
      apply hcubic
      simp [rationalProductCubic, rationalTwo_zero, vectorWedgeTwo_zero_right]
    refine ⟨α, ell + m, ell, hα0, ?_, ?_⟩
    · simp only [rationalProductCubic, vectorWedgeTwo_add_left]
    · rw [vectorWedge_add_right, vectorWedge_self, zero_add]

/-- The quadratic companion to `low_product_normal_form_exterior`, including
the Boolean contraction `κ_G(N)`.  The remaining scalar multiple of `G` lies
in the rational target space. -/
theorem low_product_quadratic_normal_form
    (a b : F₂) (ell m : LinearForm) (α β : Fin 3 → F₂)
    (hquartic : wedgeTwo (rationalTwo α) (rationalTwo β) = 0)
    (hcubic : rationalProductCubic ell m α β ≠ 0) :
    ∃ (γ : Fin 3 → F₂) (N z : LinearForm) (ρ : F₂),
      γ ≠ 0 ∧
      rationalProductCubic ell m α β =
        vectorWedgeTwo N (rationalTwo γ) ∧
      rationalProductQuadratic a b ell m α β =
        ρ • rationalTwo γ + vectorWedge z N +
          booleanContraction N (rationalTwo γ) := by
  rcases rational_wedge_zero_dependent α β hquartic with hα | hβ | hαβ
  · subst α
    have hβ0 : β ≠ 0 := by
      intro h
      subst β
      apply hcubic
      simp [rationalProductCubic, rationalTwo_zero, vectorWedgeTwo_zero_right]
    refine ⟨β, ell, m, a, hβ0, ?_, ?_⟩
    · simp [rationalProductCubic, rationalTwo_zero, vectorWedgeTwo_zero_right]
    · funext i j
      simp [rationalProductQuadratic, rationalTwo_zero, booleanContraction, twoHadamard,
        vectorWedge]
      ring
  · subst β
    have hα0 : α ≠ 0 := by
      intro h
      subst α
      apply hcubic
      simp [rationalProductCubic, rationalTwo_zero, vectorWedgeTwo_zero_right]
    refine ⟨α, m, ell, b, hα0, ?_, ?_⟩
    · simp [rationalProductCubic, rationalTwo_zero, vectorWedgeTwo_zero_right]
    · funext i j
      simp [rationalProductQuadratic, rationalTwo_zero, booleanContraction, twoHadamard,
        vectorWedge]
  · subst β
    have hα0 : α ≠ 0 := by
      intro h
      subst α
      apply hcubic
      simp [rationalProductCubic, rationalTwo_zero, vectorWedgeTwo_zero_right]
    refine ⟨α, ell + m, ell, a + b + 1, hα0, ?_, ?_⟩
    · simp only [rationalProductCubic, vectorWedgeTwo_add_left]
    · funext i j
      simp only [rationalProductQuadratic, booleanContraction, twoHadamard, vectorWedge,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [N3Certificate.mul_self_f2]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]

/-- The same companion normal form without assuming the cubic part is
nonzero.  This is the form used by prefix rigidity. -/
theorem low_product_quadratic_normal_form_weak
    (a b : F₂) (ell m : LinearForm) (α β : Fin 3 → F₂)
    (hquartic : wedgeTwo (rationalTwo α) (rationalTwo β) = 0) :
    ∃ (γ : Fin 3 → F₂) (N z : LinearForm) (ρ : F₂),
      rationalProductCubic ell m α β =
        vectorWedgeTwo N (rationalTwo γ) ∧
      rationalProductQuadratic a b ell m α β =
        ρ • rationalTwo γ + vectorWedge z N +
          booleanContraction N (rationalTwo γ) := by
  rcases rational_wedge_zero_dependent α β hquartic with hα | hβ | hαβ
  · subst α
    refine ⟨β, ell, m, a, ?_, ?_⟩
    · simp [rationalProductCubic, rationalTwo_zero, vectorWedgeTwo_zero_right]
    · funext i j
      simp [rationalProductQuadratic, rationalTwo_zero, booleanContraction, twoHadamard,
        vectorWedge]
      ring
  · subst β
    refine ⟨α, m, ell, b, ?_, ?_⟩
    · simp [rationalProductCubic, rationalTwo_zero, vectorWedgeTwo_zero_right]
    · funext i j
      simp [rationalProductQuadratic, rationalTwo_zero, booleanContraction, twoHadamard,
        vectorWedge]
  · subst β
    refine ⟨α, ell + m, ell, a + b + 1, ?_, ?_⟩
    · simp only [rationalProductCubic, vectorWedgeTwo_add_left]
    · funext i j
      simp only [rationalProductQuadratic, booleanContraction, twoHadamard, vectorWedge,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [N3Certificate.mul_self_f2]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]

/-- Cubic target-annihilator map in the concrete exterior coordinates. -/
def targetAnnihilatorMap (h : ThreeForm) : TargetCoeff →ₗ[F₂] FiveForm where
  toFun c := wedgeThreeTwo h (targetTwo c)
  map_add' c d := by
    have ht : targetTwo (c + d) = targetTwo c + targetTwo d :=
      targetTwoLinear.map_add c d
    funext i j k l m
    rw [ht]
    simp only [Pi.add_apply, wedgeThreeTwo]
    ring
  map_smul' a c := by
    have ht : targetTwo (a • c) = a • targetTwo c :=
      targetTwoLinear.map_smul a c
    funext i j k l m
    rw [ht]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, wedgeThreeTwo]
    ring

/-- Target coefficient vectors whose two-form wedges to zero with the given three-form. -/
def targetAnnihilator (h : ThreeForm) : Submodule F₂ TargetCoeff :=
  LinearMap.ker (targetAnnihilatorMap h)

theorem mem_targetAnnihilator_iff (h : ThreeForm) (c : TargetCoeff) :
    c ∈ targetAnnihilator h ↔ wedgeThreeTwo h (targetTwo c) = 0 := by
  rfl

/-- The anchor and its first Hasse jet always annihilate a cubic anchored at
the rational place zero.  This is the algebraic source of the baseline
two-dimensional annihilator in the manuscript. -/
theorem zero_anchor_wedge_firstJet :
    wedgeTwo zeroPlaceTwo zeroFirstJetTwo = 0 := by
  exact wedge_place_firstJet_zero (aLinear 0) (aLinear 1)
    (bLinear 0) (bLinear 1)

theorem targetBasis_zero_mem_anchoredAnnihilator (M : LinearForm) :
    targetBasis 0 ∈ targetAnnihilator
      (vectorWedgeTwo M (rationalPlaceTwo 0)) := by
  rw [mem_targetAnnihilator_iff, targetTwo_basis_zero,
    rationalPlaceTwo_zero_eq]
  exact wedgeThreeTwo_vectorWedgeTwo_eq_zero (wedgeTwo_self zeroPlaceTwo)

theorem targetBasis_one_mem_anchoredAnnihilator (M : LinearForm) :
    targetBasis 1 ∈ targetAnnihilator
      (vectorWedgeTwo M (rationalPlaceTwo 0)) := by
  rw [mem_targetAnnihilator_iff, targetTwo_basis_one,
    rationalPlaceTwo_zero_eq]
  exact wedgeThreeTwo_vectorWedgeTwo_eq_zero zero_anchor_wedge_firstJet

/-- The plane spanned by the constant and first product coefficients. -/
def zeroFirstJetCoeffSpace : Submodule F₂ TargetCoeff :=
  Submodule.span F₂ (Set.range ![targetBasis 0, targetBasis 1])

theorem zeroFirstJetCoeffSpace_le_anchoredAnnihilator (M : LinearForm) :
    zeroFirstJetCoeffSpace ≤
      targetAnnihilator (vectorWedgeTwo M (rationalPlaceTwo 0)) := by
  rw [zeroFirstJetCoeffSpace, Submodule.span_le]
  rintro c ⟨i, rfl⟩
  fin_cases i
  · exact targetBasis_zero_mem_anchoredAnnihilator M
  · exact targetBasis_one_mem_anchoredAnnihilator M

theorem zeroFirstJetCoeff_linearIndependent :
    LinearIndependent F₂ ![targetBasis 0, targetBasis 1] := by
  rw [Fintype.linearIndependent_iff]
  intro f h i
  have hc := congrFun h (⟨i.val, by omega⟩ : Fin 7)
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, targetBasis, Pi.basisFun, Fin.isValue,
      Module.Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
      Fin.zero_eta, Finset.sum_apply, Pi.smul_apply, Matrix.cons_val', Pi.single_eq_same,
      ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, Matrix.cons_val_fin_one,
      smul_eq_mul, Fin.sum_univ_succ, Matrix.cons_val_zero, mul_one, Finset.univ_unique,
      Fin.default_eq_zero, Matrix.cons_val_succ, mul_zero, Finset.sum_const_zero, add_zero,
      Pi.zero_apply, Fin.mk_one, one_ne_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
      zero_add] at hc ⊢
  · exact hc
  · exact hc

theorem zeroFirstJetCoeffSpace_finrank :
    Module.finrank F₂ zeroFirstJetCoeffSpace = 2 := by
  exact finrank_span_eq_card zeroFirstJetCoeff_linearIndependent

theorem anchoredAnnihilator_finrank_ge_two (M : LinearForm) :
    2 ≤ Module.finrank F₂
      (targetAnnihilator (vectorWedgeTwo M (rationalPlaceTwo 0))) := by
  calc
    2 = Module.finrank F₂ zeroFirstJetCoeffSpace :=
      zeroFirstJetCoeffSpace_finrank.symm
    _ ≤ Module.finrank F₂
        (targetAnnihilator (vectorWedgeTwo M (rationalPlaceTwo 0))) :=
      Submodule.finrank_mono (zeroFirstJetCoeffSpace_le_anchoredAnnihilator M)

end

end N4
end UnrestrictedBooleanMul
