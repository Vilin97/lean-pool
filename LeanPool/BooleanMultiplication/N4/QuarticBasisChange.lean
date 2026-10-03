/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticLowLow

/-!
# Algebraic alignment of two quartic factor bases

Equality of two nonzero rational quartic wedges says that the two ordered
quadratic pairs are bases of the same plane.  The explicit inverse minor
below produces the basis-change coefficients.  Applying the same change to
the affine and linear parts preserves the cubic projection; its quadratic
projection changes only by an explicitly rational form.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The minor computing the first coefficient in a rational-plane basis change. -/
@[expose] def basisChangeP (β γ : Fin 3 → F₂) (i j : Fin 3) : F₂ :=
  γ i * β j + γ j * β i

/-- The minor computing the second coefficient in a rational-plane basis change. -/
@[expose] def basisChangeQ (α γ : Fin 3 → F₂) (i j : Fin 3) : F₂ :=
  α i * γ j + α j * γ i

/-- A two-term linear combination of rational-place coefficient vectors. -/
@[expose] def coeffCombination (p q : F₂) (α β : Fin 3 → F₂) : Fin 3 → F₂ :=
  p • α + q • β

/-- The two pairs of rational coefficient vectors have the same three exterior minors. -/
@[expose] def SameRationalMinors (α β γ δ : Fin 3 → F₂) : Prop :=
  ∀ pair : Fin 3,
    rationalCoeffMinor α β (quarticSupportPair pair).1
        (quarticSupportPair pair).2 =
      rationalCoeffMinor γ δ (quarticSupportPair pair).1
        (quarticSupportPair pair).2

instance (α β γ δ : Fin 3 → F₂) :
    Decidable (SameRationalMinors α β γ δ) := by
  unfold SameRationalMinors
  infer_instance

theorem rationalTwo_coeffCombination
    (p q : F₂) (α β : Fin 3 → F₂) :
    rationalTwo (coeffCombination p q α β) =
      p • rationalTwo α + q • rationalTwo β := by
  funext i j
  simp [coeffCombination, rationalTwo, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem rational_basis_change_certificate
    (α β γ δ : Fin 3 → F₂) (pair : Fin 3)
    (hminor : rationalCoeffMinor α β (quarticSupportPair pair).1
      (quarticSupportPair pair).2 = 1)
    (hsame : SameRationalMinors α β γ δ) :
    let i := (quarticSupportPair pair).1
    let j := (quarticSupportPair pair).2
    let p := basisChangeP β γ i j
    let q := basisChangeQ α γ i j
    let r := basisChangeP β δ i j
    let s := basisChangeQ α δ i j
    γ = coeffCombination p q α β ∧
      δ = coeffCombination r s α β ∧ p * s + q * r = 1 := by
  revert α β γ δ pair
  decide +kernel

theorem same_rational_minors_of_wedge_eq
    (α β γ δ : Fin 3 → F₂)
    (h : wedgeTwo (rationalTwo α) (rationalTwo β) =
      wedgeTwo (rationalTwo γ) (rationalTwo δ)) :
    SameRationalMinors α β γ δ := by
  have h01 : rationalCoeffMinor α β 0 1 =
      rationalCoeffMinor γ δ 0 1 := by
    have hc := congrFun (congrFun (congrFun (congrFun h 0) 1) 4) 6
    simpa [rationalCoeffMinor, rational_wedge_coord_01] using hc
  have h12 : rationalCoeffMinor α β 1 2 =
      rationalCoeffMinor γ δ 1 2 := by
    have hc := congrFun (congrFun (congrFun (congrFun h 1) 3) 5) 7
    simpa [rationalCoeffMinor, rational_wedge_coord_12] using hc
  have hmid := congrFun (congrFun (congrFun (congrFun h 0) 3) 4) 7
  have h02 : rationalCoeffMinor α β 0 2 =
      rationalCoeffMinor γ δ 0 2 := by
    have ha := rational_wedge_coord_mid α β
    have hg := rational_wedge_coord_mid γ δ
    rw [ha] at hmid
    rw [hg] at hmid
    simp only [rationalCoeffMinor] at h01 h12 ⊢
    rw [h01, h12] at hmid
    have hcancel :
        (γ 0 * δ 1 + γ 1 * δ 0 +
            (γ 1 * δ 2 + γ 2 * δ 1)) +
            (α 0 * β 2 + α 2 * β 0) =
          (γ 0 * δ 1 + γ 1 * δ 0 +
            (γ 1 * δ 2 + γ 2 * δ 1)) +
            (γ 0 * δ 2 + γ 2 * δ 0) := by
      calc
        _ = (γ 0 * δ 1 + γ 1 * δ 0) +
            (α 0 * β 2 + α 2 * β 0) +
              (γ 1 * δ 2 + γ 2 * δ 1) := by ac_rfl
        _ = (γ 0 * δ 1 + γ 1 * δ 0) +
            (γ 0 * δ 2 + γ 2 * δ 0) +
              (γ 1 * δ 2 + γ 2 * δ 1) := hmid
        _ = _ := by ac_rfl
    exact add_left_cancel hcancel
  intro pair
  fin_cases pair
  · simpa [quarticSupportPair, rationalCoeffMinor, add_comm, mul_comm] using h01
  · simpa [quarticSupportPair] using h02
  · simpa [quarticSupportPair] using h12

/-- The first linear factor after applying the inverse two-dimensional basis change. -/
@[expose]
def changedFirstLinear (s q : F₂) (ell m : LinearForm) : LinearForm :=
  s • ell + q • m

/-- The second linear factor after applying the inverse two-dimensional basis change. -/
@[expose]
def changedSecondLinear (r p : F₂) (ell m : LinearForm) : LinearForm :=
  r • ell + p • m

/-- The rational correction arising in the quadratic part of a basis change. -/
def basisChangeEta (p q r s : F₂) (γ δ : Fin 3 → F₂) : Fin 3 → F₂ :=
  (s * r) • γ + (q * p) • δ

theorem rationalProductCubic_basis_change
    (α β γ δ : Fin 3 → F₂) (p q r s : F₂)
    (ell m : LinearForm)
    (hγ : γ = coeffCombination p q α β)
    (hδ : δ = coeffCombination r s α β) :
    rationalProductCubic ell m γ δ =
      rationalProductCubic
        (changedFirstLinear s q ell m)
        (changedSecondLinear r p ell m) α β := by
  rw [hγ, hδ]
  simp only [rationalProductCubic]
  rw [rationalTwo_coeffCombination, rationalTwo_coeffCombination]
  funext i j k
  simp [changedFirstLinear, changedSecondLinear, vectorWedgeTwo_add_left,
    vectorWedgeTwo_smul_left, vectorWedgeTwo_add_right_h, vectorWedgeTwo_smul_right_h]
  ring

theorem rationalProductQuadratic_basis_change
    (α β γ δ : Fin 3 → F₂) (p q r s a b : F₂)
    (ell m : LinearForm)
    (hγ : γ = coeffCombination p q α β)
    (hδ : δ = coeffCombination r s α β)
    (hdet : p * s + q * r = 1) :
    rationalProductQuadratic a b ell m γ δ =
      rationalTwo (basisChangeEta p q r s γ δ) +
      rationalProductQuadratic
          (s * a + q * b) (r * a + p * b)
          (changedFirstLinear s q ell m)
          (changedSecondLinear r p ell m) α β := by
  rw [hγ, hδ]
  unfold rationalProductQuadratic basisChangeEta
  simp only [rationalTwo_coeffCombination]
  funext i j
  simp only [smul_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vectorWedge,
    booleanContraction, twoHadamard, changedFirstLinear, changedSecondLinear]
  rcases f2_eq_zero_or_one p with rfl | rfl <;>
    rcases f2_eq_zero_or_one q with rfl | rfl <;>
      rcases f2_eq_zero_or_one r with rfl | rfl <;>
        rcases f2_eq_zero_or_one s with rfl | rfl <;>
          simp [rationalTwo_zero, coeffCombination] at hdet ⊢ <;>
          ring_nf <;>
          simp [pow_two, f2_mul_self_quartic, N3Certificate.two_eq_zero_f2] <;> ring

/-- Arbitrary low--low collision with the same nonzero quartic part has only
a rational target quadratic shadow. -/
theorem lowLow_quartic_collision_target_is_rational
    (α β γ δ : Fin 3 → F₂)
    (a₀ b₀ a₁ b₁ : F₂)
    (ell₀ m₀ ell₁ m₁ : LinearForm)
    (t : TargetCoeff)
    (hquartic : wedgeTwo (rationalTwo α) (rationalTwo β) ≠ 0)
    (hquarticEq : wedgeTwo (rationalTwo α) (rationalTwo β) =
      wedgeTwo (rationalTwo γ) (rationalTwo δ))
    (hcubic : rationalProductCubic ell₀ m₀ α β =
      rationalProductCubic ell₁ m₁ γ δ)
    (hquadratic : targetTwo t =
      rationalProductQuadratic a₀ b₀ ell₀ m₀ α β +
        rationalProductQuadratic a₁ b₁ ell₁ m₁ γ δ) :
    IsRationalCoeff t := by
  have hind := rational_coeff_independent_of_wedge_ne_zero α β hquartic
  rcases exists_supportPair_minor_one α β hind.1 hind.2.1 hind.2.2 with
    ⟨pair, hminor⟩
  have hsame := same_rational_minors_of_wedge_eq α β γ δ hquarticEq
  let i := (quarticSupportPair pair).1
  let j := (quarticSupportPair pair).2
  let p := basisChangeP β γ i j
  let q := basisChangeQ α γ i j
  let r := basisChangeP β δ i j
  let s := basisChangeQ α δ i j
  rcases rational_basis_change_certificate α β γ δ pair hminor hsame with
    ⟨hγ, hδ, hdet⟩
  let ell₁' := changedFirstLinear s q ell₁ m₁
  let m₁' := changedSecondLinear r p ell₁ m₁
  let a₁' := s * a₁ + q * b₁
  let b₁' := r * a₁ + p * b₁
  let eta := basisChangeEta p q r s γ δ
  have hcubic' : rationalProductCubic ell₀ m₀ α β =
      rationalProductCubic ell₁' m₁' α β := by
    rw [hcubic]
    exact rationalProductCubic_basis_change α β γ δ p q r s ell₁ m₁
      hγ hδ
  have hchild : rationalProductQuadratic a₁ b₁ ell₁ m₁ γ δ =
      rationalTwo eta +
        rationalProductQuadratic a₁' b₁' ell₁' m₁' α β := by
    exact rationalProductQuadratic_basis_change α β γ δ p q r s
      a₁ b₁ ell₁ m₁ hγ hδ hdet
  apply aligned_lowLow_quartic_target_is_rational_add_rational
    α β eta a₀ b₀ a₁' b₁' ell₀ m₀ ell₁' m₁' t
    hquartic hcubic'
  rw [hquadratic, hchild]
  module

end

end N4
end UnrestrictedBooleanMul
