/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticSeedClassified

/-!
# Normalizing a quartic seed plane at the zero place

Once the feedback coefficient is the singleton at zero, the independent seed
quadratics can be changed to a basis whose first member is that singleton.
The second member has one of the three concrete coefficient words below.
Changing factor basis modifies the seed product only by rational-low wires,
which are absorbed into the existing correction.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- One of the three nonzero coefficient vectors supported away from the zero place. -/
@[expose]
def QuarticPlaneTypeAtZero (zeta : Fin 3 → F₂) : Prop :=
  zeta = rationalSingleton 1 ∨
  zeta = rationalSingleton 2 ∨
  zeta = rationalSingleton 1 + rationalSingleton 2

instance (zeta : Fin 3 → F₂) : Decidable (QuarticPlaneTypeAtZero zeta) := by
  unfold QuarticPlaneTypeAtZero
  infer_instance

/-- A nonzero coefficient word with zero coordinate at the anchor is one of
the three possible complementary plane directions. -/
theorem quarticPlaneTypeAtZero_of_coord_zero
    (zeta : Fin 3 → F₂) (hzero : zeta 0 = 0) (hne : zeta ≠ 0) :
    QuarticPlaneTypeAtZero zeta := by
  revert zeta
  decide

/-- Explicit `GL₂(F₂)` basis selection for a coefficient plane containing
the zero singleton. -/
theorem rational_plane_basis_at_zero
    (alpha beta : Fin 3 → F₂)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hab : alpha ≠ beta)
    (hzero : InRationalCoeffPlane alpha beta (rationalSingleton 0)) :
    ∃ (p q r s : F₂),
      p * s + q * r = 1 ∧
      s • alpha + q • beta = rationalSingleton 0 ∧
      (r • alpha + p • beta) 0 = 0 ∧
      r • alpha + p • beta ≠ 0 := by
  revert alpha beta
  decide

theorem representedLowFactor_linear_combination
    (s q a b : F₂) (ell m : LinearForm)
    (alpha beta gamma : Fin 3 → F₂)
    (hgamma : s • alpha + q • beta = gamma) :
    s • representedLowFactor a ell alpha +
        q • representedLowFactor b m beta =
      representedLowFactor (s * a + q * b)
        (s • ell + q • m) gamma := by
  rw [representedLowFactor, representedLowFactor, representedLowFactor]
  rw [smul_add, smul_add]
  calc
    s • affineANF a ell + s • rationalANF alpha +
          (q • affineANF b m + q • rationalANF beta) =
        (s • affineANF a ell + q • affineANF b m) +
          (s • rationalANF alpha + q • rationalANF beta) := by ac_rfl
    _ = affineANF (s * a + q * b) (s • ell + q • m) +
          rationalANF (s • alpha + q • beta) := by
      rw [← affineANF_smul, ← affineANF_smul, ← affineANF_add,
        ← rationalANF_smul, ← rationalANF_smul, ← rationalANF_add]
    _ = _ := by rw [hgamma]

/-- A quartic seed and correction expressed in the normalized zero-anchored plane form. -/
@[expose]
def ZeroAnchoredQuarticSeedForm (g correction : ANF 8) : Prop :=
  ∃ (normalizedSeed normalizedCorrection : ANF 8)
    (leftConst rightConst : F₂)
    (leftLinear rightLinear : LinearForm)
    (zeta : Fin 3 → F₂),
    normalizedSeed =
      representedLowFactor leftConst leftLinear (rationalSingleton 0) *
        representedLowFactor rightConst rightLinear zeta ∧
    normalizedCorrection ∈ rationalLowSpace ∧
    g + correction = normalizedSeed + normalizedCorrection ∧
    QuarticPlaneTypeAtZero zeta

/-- Absorb a `GL₂(F₂)` change of the two seed factors into the
rational-low correction. -/
theorem zeroAnchoredQuarticSeedForm_of_plane
    {g correction : ANF 8}
    {leftConst rightConst : F₂}
    {leftLinear rightLinear : LinearForm}
    {alpha beta : Fin 3 → F₂}
    (hg : g =
      representedLowFactor leftConst leftLinear alpha *
        representedLowFactor rightConst rightLinear beta)
    (hcorrection : correction ∈ rationalLowSpace)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hab : alpha ≠ beta)
    (hzero : InRationalCoeffPlane alpha beta (rationalSingleton 0)) :
    ZeroAnchoredQuarticSeedForm g correction := by
  rcases rational_plane_basis_at_zero alpha beta
      halpha hbeta hab hzero with
    ⟨p, q, r, s, hdet, hfirstCoeff, hsecondZero, hsecondNonzero⟩
  let zeta := r • alpha + p • beta
  have hsecondCoeff : r • alpha + p • beta = zeta := rfl
  have htype : QuarticPlaneTypeAtZero zeta :=
    quarticPlaneTypeAtZero_of_coord_zero zeta hsecondZero hsecondNonzero
  let u := representedLowFactor leftConst leftLinear alpha
  let v := representedLowFactor rightConst rightLinear beta
  let u' := s • u + q • v
  let v' := r • u + p • v
  let normalizedSeed := u' * v'
  let error := (s * r) • u + (q * p) • v
  let normalizedCorrection := correction + error
  have huLow : u ∈ rationalLowSpace :=
    representedLowFactor_mem leftConst leftLinear alpha
  have hvLow : v ∈ rationalLowSpace :=
    representedLowFactor_mem rightConst rightLinear beta
  have herrorLow : error ∈ rationalLowSpace := by
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ huLow) (Submodule.smul_mem _ _ hvLow)
  have hcorrectionLow : normalizedCorrection ∈ rationalLowSpace :=
    Submodule.add_mem _ hcorrection herrorLow
  have huv : u * v = g := by
    dsimp only [u, v]
    exact hg.symm
  have hchanged : u' * v' = u * v + error := by
    simpa only [u', v', error, add_assoc] using
      basis_changed_product_eq u v p q r s hdet
  have hproduct : normalizedSeed = g + error := by
    calc
      normalizedSeed = u' * v' := rfl
      _ = u * v + error := hchanged
      _ = g + error := congrArg (fun w => w + error) huv
  have hu' : u' =
      representedLowFactor (s * leftConst + q * rightConst)
        (s • leftLinear + q • rightLinear) (rationalSingleton 0) :=
    representedLowFactor_linear_combination s q leftConst rightConst
      leftLinear rightLinear alpha beta _ hfirstCoeff
  have hv' : v' =
      representedLowFactor (r * leftConst + p * rightConst)
        (r • leftLinear + p • rightLinear) zeta :=
    representedLowFactor_linear_combination r p leftConst rightConst
      leftLinear rightLinear alpha beta _ hsecondCoeff
  refine
    ⟨normalizedSeed, normalizedCorrection,
      s * leftConst + q * rightConst, r * leftConst + p * rightConst,
      s • leftLinear + q • rightLinear,
      r • leftLinear + p • rightLinear, zeta, ?_,
      hcorrectionLow, ?_, htype⟩
  · change u' * v' = _
    rw [hu', hv']
  · dsimp [normalizedCorrection]
    rw [hproduct]
    simp [add_comm, add_left_comm]

end

end N4
end UnrestrictedBooleanMul
