/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticBasisChange

/-!
# ANF form of the low--low quartic exclusion

The rational--rational product may have Boolean lower-degree terms when the
quartic part is nonzero.  For two aligned products it is literally the same
term, so it cancels before the cubic and quadratic projections are
evaluated.  This is the circuit-facing version of the exterior theorem.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- An affine factor together with a linear combination of rational-place targets. -/
@[expose] def representedLowFactor (a : F₂) (ell : LinearForm)
    (α : Fin 3 → F₂) : ANF 8 :=
  affineANF a ell + rationalANF α

theorem rationalANF_add (α β : Fin 3 → F₂) :
    rationalANF (α + β) = rationalANF α + rationalANF β := by
  change targetANFLinear (rationalCoeffRep (α + β)) =
    targetANFLinear (rationalCoeffRep α) +
      targetANFLinear (rationalCoeffRep β)
  rw [rationalCoeffRep_add, map_add]

theorem rationalANF_smul (a : F₂) (α : Fin 3 → F₂) :
    rationalANF (a • α) = a • rationalANF α := by
  rcases f2_eq_zero_or_one a with rfl | rfl <;> simp

theorem alignedLowProducts_quarticProjection
    (a₀ b₀ a₁ b₁ : F₂) (ell₀ m₀ ell₁ m₁ : LinearForm)
    (α β : Fin 3 → F₂) :
    quarticProbeANF
      (representedLowFactor a₀ ell₀ α * representedLowFactor b₀ m₀ β +
        representedLowFactor a₁ ell₁ α * representedLowFactor b₁ m₁ β) = 0 := by
  rw [map_add]
  simp only [representedLowFactor, lowProduct_quarticProjection]
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem alignedLowProducts_cubicProjection
    (a₀ b₀ a₁ b₁ : F₂) (ell₀ m₀ ell₁ m₁ : LinearForm)
    (α β : Fin 3 → F₂) :
    anfThreeProjection
      (representedLowFactor a₀ ell₀ α * representedLowFactor b₀ m₀ β +
        representedLowFactor a₁ ell₁ α * representedLowFactor b₁ m₁ β) =
      rationalProductCubic ell₀ m₀ α β +
        rationalProductCubic ell₁ m₁ α β := by
  simp only [representedLowFactor, map_add, add_mul, mul_add,
    anfThreeProjection_affine_mul_affine, anfThreeProjection_affine_mul_rational,
    anfThreeProjection_rational_mul_affine, rationalProductCubic, zero_add]
  funext i j k
  simp only [Pi.add_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

theorem alignedLowProducts_quadraticProjection
    (a₀ b₀ a₁ b₁ : F₂) (ell₀ m₀ ell₁ m₁ : LinearForm)
    (α β : Fin 3 → F₂) :
    anfTwoProjection
      (representedLowFactor a₀ ell₀ α * representedLowFactor b₀ m₀ β +
        representedLowFactor a₁ ell₁ α * representedLowFactor b₁ m₁ β) =
      rationalProductQuadratic a₀ b₀ ell₀ m₀ α β +
        rationalProductQuadratic a₁ b₁ ell₁ m₁ α β := by
  simp only [representedLowFactor, map_add, add_mul, mul_add,
    anfTwoProjection_affine_mul_affine, anfTwoProjection_affine_mul_rational,
    anfTwoProjection_rational_mul_affine]
  funext i j
  simp only [rationalProductQuadratic, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    booleanContraction, vectorWedge, twoHadamard]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

theorem wedge_ne_zero_of_quarticProbe_ne_zero (q r : TwoForm)
    (h : quarticWedgeProbe q r ≠ 0) : wedgeTwo q r ≠ 0 := by
  intro hw
  apply h
  funext t
  fin_cases t <;>
    simp [quarticWedgeProbe, hw]

theorem same_rational_minors_of_probe_eq
    (α β γ δ : Fin 3 → F₂)
    (h : quarticWedgeProbe (rationalTwo α) (rationalTwo β) =
      quarticWedgeProbe (rationalTwo γ) (rationalTwo δ)) :
    SameRationalMinors α β γ δ := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h01 : rationalCoeffMinor α β 0 1 =
      rationalCoeffMinor γ δ 0 1 := by
    simpa [quarticWedgeProbe, rationalCoeffMinor, rational_wedge_coord_01] using h0
  have h12 : rationalCoeffMinor α β 1 2 =
      rationalCoeffMinor γ δ 1 2 := by
    simpa [quarticWedgeProbe, rationalCoeffMinor, rational_wedge_coord_12] using h1
  have h02 : rationalCoeffMinor α β 0 2 =
      rationalCoeffMinor γ δ 0 2 := by
    have hmid :
        (α 0 * β 1 + α 1 * β 0) +
            (α 0 * β 2 + α 2 * β 0) +
            (α 1 * β 2 + α 2 * β 1) =
          (γ 0 * δ 1 + γ 1 * δ 0) +
            (γ 0 * δ 2 + γ 2 * δ 0) +
            (γ 1 * δ 2 + γ 2 * δ 1) := by
      simpa [quarticWedgeProbe, rational_wedge_coord_mid] using h2
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

theorem representedLowFactor_basis_change_first
    (α β γ δ : Fin 3 → F₂) (p q r s a b : F₂)
    (ell m : LinearForm)
    (hγ : γ = coeffCombination p q α β)
    (hδ : δ = coeffCombination r s α β)
    (hdet : p * s + q * r = 1) :
    s • representedLowFactor a ell γ +
        q • representedLowFactor b m δ =
      representedLowFactor (s * a + q * b)
        (changedFirstLinear s q ell m) α := by
  have hcoeff : s • γ + q • δ = α := by
    rw [hγ, hδ]
    funext i
    simp only [coeffCombination, smul_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← one_mul (α i), ← hdet]
    ring_nf
    simp [pow_two, f2_mul_self_quartic, N3Certificate.two_eq_zero_f2]
  calc
    s • representedLowFactor a ell γ +
        q • representedLowFactor b m δ =
      (s • affineANF a ell + q • affineANF b m) +
        (s • rationalANF γ + q • rationalANF δ) := by
          simp only [representedLowFactor, smul_add]
          module
    _ = affineANF (s * a + q * b) (s • ell + q • m) +
        rationalANF (s • γ + q • δ) := by
          rw [← affineANF_smul, ← affineANF_smul,
            ← affineANF_add, ← rationalANF_smul, ← rationalANF_smul,
            ← rationalANF_add]
    _ = _ := by rw [hcoeff]; rfl

theorem representedLowFactor_basis_change_second
    (α β γ δ : Fin 3 → F₂) (p q r s a b : F₂)
    (ell m : LinearForm)
    (hγ : γ = coeffCombination p q α β)
    (hδ : δ = coeffCombination r s α β)
    (hdet : p * s + q * r = 1) :
    r • representedLowFactor a ell γ +
        p • representedLowFactor b m δ =
      representedLowFactor (r * a + p * b)
        (changedSecondLinear r p ell m) β := by
  have hcoeff : r • γ + p • δ = β := by
    rw [hγ, hδ]
    funext i
    simp only [coeffCombination, smul_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← one_mul (β i), ← hdet]
    ring_nf
    simp [pow_two, f2_mul_self_quartic, N3Certificate.two_eq_zero_f2]
  calc
    r • representedLowFactor a ell γ +
        p • representedLowFactor b m δ =
      (r • affineANF a ell + p • affineANF b m) +
        (r • rationalANF γ + p • rationalANF δ) := by
          simp only [representedLowFactor, smul_add]
          module
    _ = affineANF (r * a + p * b) (r • ell + p • m) +
        rationalANF (r • γ + p • δ) := by
          rw [← affineANF_smul, ← affineANF_smul,
            ← affineANF_add, ← rationalANF_smul, ← rationalANF_smul,
            ← rationalANF_add]
    _ = _ := by rw [hcoeff]; rfl

theorem basis_changed_product_eq
    (u v : ANF 8) (p q r s : F₂)
    (hdet : p * s + q * r = 1) :
    (s • u + q • v) * (r • u + p • v) =
      u * v + (s * r) • u + (q * p) • v := by
  rcases f2_eq_zero_or_one p with rfl | rfl <;>
    rcases f2_eq_zero_or_one q with rfl | rfl <;>
      rcases f2_eq_zero_or_one r with rfl | rfl <;>
        rcases f2_eq_zero_or_one s with rfl | rfl <;>
          simp [anf_mul_self, mul_add, add_comm, mul_comm] at hdet ⊢

theorem representedLowFactor_mem
    (a : F₂) (ell : LinearForm) (α : Fin 3 → F₂) :
    representedLowFactor a ell α ∈ rationalLowSpace := by
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left (affineANF_mem a ell)
  · apply Submodule.mem_sup_right
    exact (mem_rationalTargetSpace_iff (rationalANF α)).mpr ⟨α, rfl⟩

/-- Two products with an aligned nonzero quartic basis cannot expose a new
target quadratic direction. -/
theorem alignedLowProducts_mem_rationalLow
    (a₀ b₀ a₁ b₁ : F₂) (ell₀ m₀ ell₁ m₁ : LinearForm)
    (α β : Fin 3 → F₂)
    (hquartic : quarticWedgeProbe (rationalTwo α) (rationalTwo β) ≠ 0)
    (hsum :
      representedLowFactor a₀ ell₀ α * representedLowFactor b₀ m₀ β +
        representedLowFactor a₁ ell₁ α * representedLowFactor b₁ m₁ β ∈
          targetAmbient 8 (mulTarget 4)) :
    representedLowFactor a₀ ell₀ α * representedLowFactor b₀ m₀ β +
        representedLowFactor a₁ ell₁ α * representedLowFactor b₁ m₁ β ∈
      rationalLowSpace := by
  let z : ANF 8 :=
    representedLowFactor a₀ ell₀ α * representedLowFactor b₀ m₀ β +
      representedLowFactor a₁ ell₁ α * representedLowFactor b₁ m₁ β
  rcases exists_targetAmbient_rep hsum with ⟨u, c, hu, hz⟩
  have hcubicZero : anfThreeProjection z = 0 :=
    anfThreeProjection_eq_zero_of_mem_targetAmbient hsum
  have hcubicSum :
      rationalProductCubic ell₀ m₀ α β +
        rationalProductCubic ell₁ m₁ α β = 0 := by
    rw [← alignedLowProducts_cubicProjection]
    exact hcubicZero
  have hcubic : rationalProductCubic ell₀ m₀ α β =
      rationalProductCubic ell₁ m₁ α β := by
    funext i j k
    have hc := congrFun (congrFun (congrFun hcubicSum i) j) k
    simp only [Pi.add_apply, Pi.zero_apply] at hc
    rw [← CharTwo.sub_eq_add] at hc
    exact sub_eq_zero.mp hc
  have htwo : anfTwoProjection z = targetTwo c := by
    have hz' : z = u + targetANF c := by simpa [z] using hz
    rw [hz', map_add, anfTwoProjection_kills_affine hu,
      anfTwoProjection_targetANF, zero_add]
  have hquadratic : targetTwo c =
      rationalProductQuadratic a₀ b₀ ell₀ m₀ α β +
        rationalProductQuadratic a₁ b₁ ell₁ m₁ α β := by
    rw [← htwo]
    exact alignedLowProducts_quadraticProjection
      a₀ b₀ a₁ b₁ ell₀ m₀ ell₁ m₁ α β
  have hwedge : wedgeTwo (rationalTwo α) (rationalTwo β) ≠ 0 :=
    wedge_ne_zero_of_quarticProbe_ne_zero _ _ hquartic
  have hcRat := aligned_lowLow_quartic_target_is_rational
    α β a₀ b₀ a₁ b₁ ell₀ m₀ ell₁ m₁ c
    hwedge hcubic hquadratic
  rcases (IsRationalCoeff_iff c).mp hcRat with ⟨gamma, hgamma⟩
  apply Submodule.mem_sup.mpr
  refine ⟨u, hu, targetANF c, ?_, hz.symm⟩
  apply (mem_rationalTargetSpace_iff (targetANF c)).mpr
  exact ⟨gamma, by rw [hgamma]⟩

/-- Adding a rational-low correction preserves the target ambient space.  Keeping
this elementary submodule step opaque prevents the elaborator from repeatedly
unfolding the represented low factors in the basis-change argument below. -/
theorem add_mem_targetAmbient_of_mem_rationalLow
    {x y : ANF 8}
    (hx : x ∈ targetAmbient 8 (mulTarget 4))
    (hy : y ∈ rationalLowSpace) :
    x + y ∈ targetAmbient 8 (mulTarget 4) :=
  Submodule.add_mem _ hx (rationalLowSpace_le_targetAmbient hy)

/-- Complete ANF low--low quartic collision, including algebraic basis
alignment. -/
theorem lowLowProducts_mem_rationalLow_of_quartic_nonzero
    (a₀ b₀ a₁ b₁ : F₂) (ell₀ m₀ ell₁ m₁ : LinearForm)
    (α β γ δ : Fin 3 → F₂)
    (hquartic : quarticWedgeProbe (rationalTwo α) (rationalTwo β) ≠ 0)
    (hsum :
      representedLowFactor a₀ ell₀ α * representedLowFactor b₀ m₀ β +
        representedLowFactor a₁ ell₁ γ * representedLowFactor b₁ m₁ δ ∈
          targetAmbient 8 (mulTarget 4)) :
    representedLowFactor a₀ ell₀ α * representedLowFactor b₀ m₀ β +
        representedLowFactor a₁ ell₁ γ * representedLowFactor b₁ m₁ δ ∈
      rationalLowSpace := by
  let u₀ := representedLowFactor a₀ ell₀ α
  let v₀ := representedLowFactor b₀ m₀ β
  let u₁ := representedLowFactor a₁ ell₁ γ
  let v₁ := representedLowFactor b₁ m₁ δ
  have hsum' : u₀ * v₀ + u₁ * v₁ ∈ targetAmbient 8 (mulTarget 4) := by
    simpa [u₀, v₀, u₁, v₁] using hsum
  have hprobeZero := quarticProbeANF_eq_zero_of_mem_targetAmbient hsum
  have hprobeEq : quarticWedgeProbe (rationalTwo α) (rationalTwo β) =
      quarticWedgeProbe (rationalTwo γ) (rationalTwo δ) := by
    simp only [representedLowFactor] at hprobeZero
    rw [map_add, lowProduct_quarticProjection,
      lowProduct_quarticProjection] at hprobeZero
    funext theta
    have hc := congrFun hprobeZero theta
    simp only [Pi.add_apply, Pi.zero_apply] at hc
    rw [← CharTwo.sub_eq_add] at hc
    exact sub_eq_zero.mp hc
  have hsame := same_rational_minors_of_probe_eq α β γ δ hprobeEq
  have hwedge : wedgeTwo (rationalTwo α) (rationalTwo β) ≠ 0 :=
    wedge_ne_zero_of_quarticProbe_ne_zero _ _ hquartic
  have hind := rational_coeff_independent_of_wedge_ne_zero α β hwedge
  rcases exists_supportPair_minor_one α β hind.1 hind.2.1 hind.2.2 with
    ⟨pair, hminor⟩
  let i := (quarticSupportPair pair).1
  let j := (quarticSupportPair pair).2
  let p := basisChangeP β γ i j
  let q := basisChangeQ α γ i j
  let r := basisChangeP β δ i j
  let s := basisChangeQ α δ i j
  rcases rational_basis_change_certificate α β γ δ pair hminor hsame with
    ⟨hγ, hδ, hdet⟩
  have hproduct := basis_changed_product_eq u₁ v₁ p q r s hdet
  let a₁' := s * a₁ + q * b₁
  let b₁' := r * a₁ + p * b₁
  let ell₁' := changedFirstLinear s q ell₁ m₁
  let m₁' := changedSecondLinear r p ell₁ m₁
  have hu₁ : u₁ ∈ rationalLowSpace := by
    exact representedLowFactor_mem a₁ ell₁ γ
  have hv₁ : v₁ ∈ rationalLowSpace := by
    exact representedLowFactor_mem b₁ m₁ δ
  have hu₁' : s • u₁ + q • v₁ =
      representedLowFactor a₁' ell₁' α := by
    exact representedLowFactor_basis_change_first
      α β γ δ p q r s a₁ b₁ ell₁ m₁ hγ hδ hdet
  have hv₁' : r • u₁ + p • v₁ =
      representedLowFactor b₁' m₁' β := by
    exact representedLowFactor_basis_change_second
      α β γ δ p q r s a₁ b₁ ell₁ m₁ hγ hδ hdet
  have hcorrection : (s * r) • u₁ + (q * p) • v₁ ∈
      rationalLowSpace := by
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ hu₁)
      (Submodule.smul_mem _ _ hv₁)
  have halignedTarget : u₀ * v₀ +
      (s • u₁ + q • v₁) * (r • u₁ + p • v₁) ∈
      targetAmbient 8 (mulTarget 4) := by
    rw [hproduct]
    simpa only [add_assoc] using
      add_mem_targetAmbient_of_mem_rationalLow hsum' hcorrection
  have halignedRat : u₀ * v₀ +
      (s • u₁ + q • v₁) * (r • u₁ + p • v₁) ∈
      rationalLowSpace := by
    rw [hu₁', hv₁'] at halignedTarget ⊢
    exact alignedLowProducts_mem_rationalLow
      a₀ b₀ a₁' b₁' ell₀ m₀ ell₁' m₁' α β hquartic halignedTarget
  have horiginal : u₀ * v₀ + u₁ * v₁ =
      (u₀ * v₀ +
        (s • u₁ + q • v₁) * (r • u₁ + p • v₁)) +
          ((s * r) • u₁ + (q * p) • v₁) := by
    rw [hproduct]
    rw [show
      (u₀ * v₀ + (u₁ * v₁ + (s * r) • u₁ + (q * p) • v₁)) +
          ((s * r) • u₁ + (q * p) • v₁) =
        (u₀ * v₀ + u₁ * v₁) +
          (((s * r) • u₁ + (q * p) • v₁) +
            ((s * r) • u₁ + (q * p) • v₁)) by abel]
    simp only [anf_add_self, add_zero]
  have horiginalRat : u₀ * v₀ + u₁ * v₁ ∈ rationalLowSpace := by
    rw [horiginal]
    exact Submodule.add_mem _ halignedRat hcorrection
  simpa [u₀, v₀, u₁, v₁] using horiginalRat

end

end N4
end UnrestrictedBooleanMul
