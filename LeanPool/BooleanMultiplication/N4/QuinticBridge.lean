/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.CubicSeed

/-!
# Quintic anchor certificate

After place normalization the first feedback target is a tangent at the
zero rational place.  Sixteen degree-five monomials separate a rational
cubic from every cubic not anchored there.  The ANF bridge is checked only
on the `8 * 3 * 2` input/place/tangent basis rows and extended by linearity.
This is a fixed algebraic matrix certificate, not circuit enumeration.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Sixteen quintic coordinates used to detect the cubic anchor. -/
def quinticAnchorCoord : Fin 16 →
    Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8 :=
  ![(0,1,2,4,7), (0,3,5,6,7), (0,3,4,5,6), (1,2,3,4,7),
    (0,1,3,5,7), (0,2,3,4,6), (0,2,4,6,7), (1,3,4,5,7),
    (0,1,3,4,7), (0,2,3,4,7), (0,1,2,5,7), (0,3,4,5,7),
    (0,3,4,6,7), (0,2,3,5,6), (0,2,5,6,7), (1,2,4,5,7)]

/-- The squarefree monomial corresponding to a quintic anchor coordinate. -/
def quinticAnchorSet (k : Fin 16) : Finset (Fin 8) :=
  let c := quinticAnchorCoord k
  {c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2}

/-- Extract the sixteen quintic anchor coefficients from an ANF. -/
def anfQuinticAnchorProbe : ANF 8 →ₗ[F₂] (Fin 16 → F₂) where
  toFun p k := p.coeff ⟨quinticAnchorSet k⟩
  map_add' p q := by funext k; simp
  map_smul' a p := by funext k; simp

/-- The sixteen anchor coordinates of a three-form wedged with a two-form. -/
def cubicAnchorWedgeProbe (h : ThreeForm) (q : TwoForm) : Fin 16 → F₂ :=
  fun k =>
    let c := quinticAnchorCoord k
    wedgeThreeTwo h q c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2

/-- The quintic anchor wedge probes as a bilinear map. -/
def cubicAnchorWedgeProbeBilinear :
    ThreeForm →ₗ[F₂] TwoForm →ₗ[F₂] (Fin 16 → F₂) where
  toFun h :=
    { toFun := fun q => cubicAnchorWedgeProbe h q
      map_add' := by
        intro q r
        funext k
        simp [cubicAnchorWedgeProbe, wedgeThreeTwo]
        ring
      map_smul' := by
        intro a q
        funext k
        simp [cubicAnchorWedgeProbe, wedgeThreeTwo]
        ring }
  map_add' h g := by
    apply LinearMap.ext
    intro q
    funext k
    simp [cubicAnchorWedgeProbe, wedgeThreeTwo]
    ring
  map_smul' a h := by
    apply LinearMap.ext
    intro q
    funext k
    simp [cubicAnchorWedgeProbe, wedgeThreeTwo]
    ring

theorem anfQuinticAnchorProbe_eq_zero_of_degreeLE_four
    {p : ANF 8} (hp : DegreeLE 4 p) : anfQuinticAnchorProbe p = 0 := by
  funext k
  apply hp ⟨quinticAnchorSet k⟩
  change 4 < (quinticAnchorSet k).card
  have hc : (quinticAnchorSet k).card = 5 := by
    fin_cases k <;> decide
  omega

@[simp] theorem anfQuinticAnchorProbe_monomial
    (u : Finset (Fin 8)) (k : Fin 16) :
    anfQuinticAnchorProbe (monomial u) k =
      if u = quinticAnchorSet k then 1 else 0 := by
  simp [anfQuinticAnchorProbe, coeff_monomial]

theorem DegreeLE.smul {m d : Nat} {p : ANF m}
    (hp : DegreeLE d p) (a : F₂) : DegreeLE d (a • p) := by
  intro s hs
  simp [hp s hs]

theorem degreeLE_monomial_of_card_le {m d : Nat}
    (u : Finset (Fin m)) (hu : u.card ≤ d) :
    DegreeLE d (monomial u) := by
  intro s hs
  by_cases hus : u = s.vars
  · subst u
    omega
  · change (monomial u).coeff ⟨s.vars⟩ = 0
    rw [coeff_monomial]
    simp [hus]

/-- The ANF sum of a list of squarefree monomials. -/
def anfMonomialList : List (Finset (Fin 8)) → ANF 8
  | [] => 0
  | u :: rest => monomial u + anfMonomialList rest

/-- The anchor coefficients after multiplying a monomial list by one input variable. -/
def monomialListProbeModel
    (sets : List (Finset (Fin 8))) (r : Fin 8) : Fin 16 → F₂ :=
  fun k => sets.foldr (fun u z =>
    (if {r} ∪ u = quinticAnchorSet k then 1 else 0) + z) 0

theorem anfQuinticAnchorProbe_X_mul_monomialList
    (sets : List (Finset (Fin 8))) (r : Fin 8) :
    anfQuinticAnchorProbe (X r * anfMonomialList sets) =
      monomialListProbeModel sets r := by
  induction sets with
  | nil =>
      simp only [anfMonomialList, mul_zero, map_zero]
      change (0 : Fin 16 → F₂) = fun _ => 0
      rfl
  | cons u rest ih =>
      rw [anfMonomialList, mul_add, map_add, ih]
      funext k
      simp [X, monomial_mul, monomialListProbeModel]
      rfl

theorem degreeLE_anfMonomialList {d : Nat}
    (sets : List (Finset (Fin 8)))
    (hsets : ∀ u ∈ sets, u.card ≤ d) :
    DegreeLE d (anfMonomialList sets) := by
  induction sets with
  | nil =>
      intro s hs
      simp [anfMonomialList]
  | cons u rest ih =>
      rw [anfMonomialList]
      apply DegreeLE.add
      · exact degreeLE_monomial_of_card_le u (hsets u (by simp))
      · apply ih
        intro v hv
        exact hsets v (by simp [hv])

private theorem anfQuinticAnchorProbe_linear_place_zero
    (ell : LinearForm) (eps : F₂) :
    anfQuinticAnchorProbe
        ((linearANF ell * targetANF (rationalPlaceCoeff 0)) *
          targetANF (rationalTangentAt 0 eps)) =
      cubicAnchorWedgeProbe
        (vectorWedgeTwo ell (rationalPlaceTwo 0))
        (targetTwo (rationalTangentAt 0 eps)) := by
  have hplace : targetANF (rationalPlaceCoeff (0 : Fin 3)) = Mul 4 0 := by
    change targetANF rZeroCoeff = Mul 4 0
    rw [rZeroCoeff_eq_targetBasis_zero]
    exact targetANF_targetBasis_feedback 0
  have hprod :
      targetANF (rationalPlaceCoeff (0 : Fin 3)) *
          targetANF (rationalTangentAt 0 eps) =
        eps • Mul 4 0 +
          (monomial ({0, 4, 5} : Finset (Fin 8)) +
            monomial ({0, 1, 4} : Finset (Fin 8))) := by
    rw [hplace, targetANF_zero_tangent, mul_add, mul_smul_comm,
      anf_mul_self, mul_comm (Mul 4 0) (Mul 4 1), mul_target_one_zero]
  have hlin : DegreeLE 1 (linearANF ell) := by
    simpa [affineANF] using degreeLE_one_affineANF 0 ell
  have hplaceLE : DegreeLE 2 (Mul 4 0) := by
    rw [← hplace]
    exact degreeLE_two_targetANF _
  have hcubicA : DegreeLE 3
      (monomial ({0, 4, 5} : Finset (Fin 8))) := by
    apply degreeLE_monomial_of_card_le
    decide
  have hcubicB : DegreeLE 3
      (monomial ({0, 1, 4} : Finset (Fin 8))) := by
    apply degreeLE_monomial_of_card_le
    decide
  have hprodLE : DegreeLE 3
      (eps • Mul 4 0 +
        (monomial ({0, 4, 5} : Finset (Fin 8)) +
          monomial ({0, 1, 4} : Finset (Fin 8)))) :=
    (hplaceLE.mono (by omega)).smul eps |>.add (hcubicA.add hcubicB)
  have hlhs : anfQuinticAnchorProbe
      ((linearANF ell * targetANF (rationalPlaceCoeff 0)) *
        targetANF (rationalTangentAt 0 eps)) = 0 := by
    apply anfQuinticAnchorProbe_eq_zero_of_degreeLE_four
    rw [mul_assoc, hprod]
    simpa using hlin.mul hprodLE
  have hwedge : wedgeTwo (rationalPlaceTwo 0)
      (targetTwo (rationalTangentAt 0 eps)) = 0 := by
    rcases f2_eq_zero_or_one eps with rfl | rfl
    · simpa [targetTwo_zero_tangent, rationalPlaceTwo_zero_eq] using
        zero_anchor_wedge_firstJet
    · rw [targetTwo_zero_tangent, rationalPlaceTwo_zero_eq, one_smul,
        wedgeTwo_add_right, wedgeTwo_self, zero_anchor_wedge_firstJet,
        zero_add]
  have hfive : wedgeThreeTwo
      (vectorWedgeTwo ell (rationalPlaceTwo 0))
      (targetTwo (rationalTangentAt 0 eps)) = 0 :=
    wedgeThreeTwo_vectorWedgeTwo_eq_zero hwedge
  rw [hlhs]
  funext k
  change 0 = wedgeThreeTwo
    (vectorWedgeTwo ell (rationalPlaceTwo 0))
    (targetTwo (rationalTangentAt 0 eps))
      (quinticAnchorCoord k).1
      (quinticAnchorCoord k).2.1
      (quinticAnchorCoord k).2.2.1
      (quinticAnchorCoord k).2.2.2.1
      (quinticAnchorCoord k).2.2.2.2
  rw [hfive]
  rfl

/-- The lower-degree monomials in the evaluation-at-one tangent product. -/
def oneTangentLowList (eps : F₂) : List (Finset (Fin 8)) :=
  if eps = 0 then
    [{0, 5}, {1, 4}, {0, 1, 4}, {0, 1, 5}, {0, 2, 5}, {0, 3, 5},
      {0, 4, 5}, {0, 5, 6}, {0, 5, 7}, {1, 2, 4}, {1, 3, 4},
      {1, 4, 5}, {1, 4, 6}, {1, 4, 7}]
  else
    [{0, 4}, {0, 5}, {1, 4}, {0, 1, 5}, {0, 2, 4}, {0, 2, 5},
      {0, 3, 4}, {0, 3, 5}, {0, 4, 6}, {0, 4, 7}, {0, 5, 6},
      {0, 5, 7}, {1, 2, 4}, {1, 3, 4}, {1, 4, 5}, {1, 4, 6},
      {1, 4, 7}]

/-- The quartic monomials in the evaluation-at-one tangent product. -/
def oneTangentQuarticList (eps : F₂) : List (Finset (Fin 8)) :=
  if eps = 0 then
    [{0, 1, 4, 6}, {0, 1, 4, 7}, {0, 1, 5, 6}, {0, 1, 5, 7},
      {0, 2, 4, 5}, {0, 2, 5, 6}, {0, 2, 5, 7}, {0, 3, 4, 5},
      {0, 3, 5, 6}, {0, 3, 5, 7}, {1, 2, 4, 5}, {1, 2, 4, 6},
      {1, 2, 4, 7}, {1, 3, 4, 5}, {1, 3, 4, 6}, {1, 3, 4, 7}]
  else
    [{0, 1, 4, 5}, {0, 1, 5, 6}, {0, 1, 5, 7}, {0, 2, 4, 6},
      {0, 2, 4, 7}, {0, 2, 5, 6}, {0, 2, 5, 7}, {0, 3, 4, 6},
      {0, 3, 4, 7}, {0, 3, 5, 6}, {0, 3, 5, 7}, {1, 2, 4, 5},
      {1, 2, 4, 6}, {1, 2, 4, 7}, {1, 3, 4, 5}, {1, 3, 4, 6},
      {1, 3, 4, 7}]

/-- The ANF of the evaluation-at-one target times its chosen tangent target. -/
def oneTangentProductANF (eps : F₂) : ANF 8 :=
  anfMonomialList (oneTangentLowList eps) +
    anfMonomialList (oneTangentQuarticList eps)

private theorem one_tangent_product (eps : F₂) :
    targetANF (rationalPlaceCoeff 1) *
        targetANF (rationalTangentAt 0 eps) =
      oneTangentProductANF eps := by
  rcases f2_eq_zero_or_one eps with rfl | rfl
  · rw [rationalPlaceANF_direct, targetANF_zero_tangent]
    simp (disch := decide) only [linearANF, placeA, Fin.isValue, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero, X,
      Fin.sum_univ_succ, one_smul, Matrix.cons_val_succ, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Fin.reduceSucc, zero_smul, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_const_zero, add_zero, placeB, Finset.sum_singleton, zero_add, mul_add,
      add_mul, monomial_mul, Finset.singleton_union, Nat.reduceMul, mul_target_one_anf,
      Finset.union_insert, Finset.insert_union, Finset.insert_eq_of_mem, Finset.insert_comm,
      anf_mul_self, Finset.union_idempotent, oneTangentProductANF, oneTangentLowList,
      ↓reduceIte, anfMonomialList, oneTangentQuarticList]
    simp only [show ({0, 6, 5} : Finset (Fin 8)) = {0, 5, 6} by decide, show ({0, 3, 6, 5} :
      Finset (Fin 8)) = {0, 3, 5, 6} by decide, show ({0, 7, 5} : Finset (Fin 8)) = {0, 5, 7}
      by decide, show ({0, 3, 7, 5} : Finset (Fin 8)) = {0, 3, 5, 7} by decide, show ({1, 5,
      4} : Finset (Fin 8)) = {1, 4, 5} by decide, show ({1, 3, 5, 4} : Finset (Fin 8)) = {1,
      3, 4, 5} by decide, show ({1, 6, 4} : Finset (Fin 8)) = {1, 4, 6} by decide, show ({1,
      3, 6, 4} : Finset (Fin 8)) = {1, 3, 4, 6} by decide, show ({1, 7, 4} : Finset (Fin 8)) =
      {1, 4, 7} by decide, show ({1, 3, 7, 4} : Finset (Fin 8)) = {1, 3, 4, 7} by decide]
    simp only [show ({1, 0, 4, 5} : Finset (Fin 8)) = {0, 1, 4, 5} by decide, show ({2, 0, 4,
      5} : Finset (Fin 8)) = {0, 2, 4, 5} by decide, show ({1, 0, 5} : Finset (Fin 8)) = {0,
      1, 5} by decide, show ({2, 0, 5} : Finset (Fin 8)) = {0, 2, 5} by decide, show ({1, 0,
      5, 6} : Finset (Fin 8)) = {0, 1, 5, 6} by decide, show ({2, 0, 5, 6} : Finset (Fin 8)) =
      {0, 2, 5, 6} by decide, show ({1, 0, 5, 7} : Finset (Fin 8)) = {0, 1, 5, 7} by decide,
      show ({2, 0, 5, 7} : Finset (Fin 8)) = {0, 2, 5, 7} by decide, show ({2, 1, 4} : Finset
      (Fin 8)) = {1, 2, 4} by decide, show ({2, 1, 4, 5} : Finset (Fin 8)) = {1, 2, 4, 5} by
      decide, show ({2, 1, 4, 6} : Finset (Fin 8)) = {1, 2, 4, 6} by decide, show ({2, 1, 4,
      7} : Finset (Fin 8)) = {1, 2, 4, 7} by decide]
    apply MonoidAlgebra.coeff_injective
    ext u
    rcases u with ⟨u⟩
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  · rw [rationalPlaceANF_direct, targetANF_zero_tangent,
      mul_target_zero_anf, mul_target_one_anf]
    simp (disch := decide) only [linearANF, placeA, Fin.isValue, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero, X,
      Fin.sum_univ_succ, one_smul, Matrix.cons_val_succ, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Fin.reduceSucc, zero_smul, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_const_zero, add_zero, placeB, Finset.sum_singleton, zero_add, mul_add,
      add_mul, monomial_mul, Finset.singleton_union, Nat.reduceMul, anf_mul_self,
      Finset.union_insert, Finset.insert_union, Finset.union_idempotent, Finset.insert_comm,
      Finset.insert_eq_of_mem, oneTangentProductANF, oneTangentLowList, one_ne_zero,
      ↓reduceIte, anfMonomialList, oneTangentQuarticList]
    simp only [show ({1, 0, 4} : Finset (Fin 8)) = {0, 1, 4} by decide, show ({2, 0, 4} :
      Finset (Fin 8)) = {0, 2, 4} by decide, show ({0, 5, 4} : Finset (Fin 8)) = {0, 4, 5} by
      decide, show ({0, 3, 5, 4} : Finset (Fin 8)) = {0, 3, 4, 5} by decide, show ({0, 6, 4} :
      Finset (Fin 8)) = {0, 4, 6} by decide, show ({0, 3, 6, 4} : Finset (Fin 8)) = {0, 3, 4,
      6} by decide, show ({0, 7, 4} : Finset (Fin 8)) = {0, 4, 7} by decide, show ({0, 3, 7,
      4} : Finset (Fin 8)) = {0, 3, 4, 7} by decide, show ({1, 0, 4, 5} : Finset (Fin 8)) =
      {0, 1, 4, 5} by decide, show ({2, 0, 4, 5} : Finset (Fin 8)) = {0, 2, 4, 5} by decide,
      show ({1, 0, 5} : Finset (Fin 8)) = {0, 1, 5} by decide, show ({2, 0, 5} : Finset (Fin
      8)) = {0, 2, 5} by decide, show ({0, 6, 5} : Finset (Fin 8)) = {0, 5, 6} by decide, show
      ({0, 3, 6, 5} : Finset (Fin 8)) = {0, 3, 5, 6} by decide, show ({0, 7, 5} : Finset (Fin
      8)) = {0, 5, 7} by decide, show ({0, 3, 7, 5} : Finset (Fin 8)) = {0, 3, 5, 7} by
      decide, show ({2, 1, 4} : Finset (Fin 8)) = {1, 2, 4} by decide, show ({1, 5, 4} :
      Finset (Fin 8)) = {1, 4, 5} by decide, show ({1, 3, 5, 4} : Finset (Fin 8)) = {1, 3, 4,
      5} by decide, show ({1, 6, 4} : Finset (Fin 8)) = {1, 4, 6} by decide, show ({1, 3, 6,
      4} : Finset (Fin 8)) = {1, 3, 4, 6} by decide, show ({1, 7, 4} : Finset (Fin 8)) = {1,
      4, 7} by decide, show ({1, 3, 7, 4} : Finset (Fin 8)) = {1, 3, 4, 7} by decide]
    simp only [show ({1, 0, 4, 6} : Finset (Fin 8)) = {0, 1, 4, 6} by decide, show ({2, 0, 4,
      6} : Finset (Fin 8)) = {0, 2, 4, 6} by decide, show ({1, 0, 4, 7} : Finset (Fin 8)) =
      {0, 1, 4, 7} by decide, show ({2, 0, 4, 7} : Finset (Fin 8)) = {0, 2, 4, 7} by decide,
      show ({1, 0, 5, 6} : Finset (Fin 8)) = {0, 1, 5, 6} by decide, show ({2, 0, 5, 6} :
      Finset (Fin 8)) = {0, 2, 5, 6} by decide, show ({1, 0, 5, 7} : Finset (Fin 8)) = {0, 1,
      5, 7} by decide, show ({2, 0, 5, 7} : Finset (Fin 8)) = {0, 2, 5, 7} by decide, show
      ({2, 1, 4, 5} : Finset (Fin 8)) = {1, 2, 4, 5} by decide, show ({2, 1, 4, 6} : Finset
      (Fin 8)) = {1, 2, 4, 6} by decide, show ({2, 1, 4, 7} : Finset (Fin 8)) = {1, 2, 4, 7}
      by decide]
    apply MonoidAlgebra.coeff_injective
    ext u
    rcases u with ⟨u⟩
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2, N3Certificate.three_eq_one_f2]

private theorem oneTangentLowList_card
    (eps : F₂) (u : Finset (Fin 8))
    (hu : u ∈ oneTangentLowList eps) : u.card ≤ 3 := by
  rcases f2_eq_zero_or_one eps with rfl | rfl <;>
    simp only [oneTangentLowList, ↓reduceIte, Fin.isValue, List.mem_cons, List.not_mem_nil,
      or_false, one_ne_zero] at hu <;>
    rcases hu with (rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    decide

private theorem anfQuinticAnchorProbe_one_basis_model
    (r : Fin 8) (eps : F₂) :
    anfQuinticAnchorProbe
        ((X r * targetANF (rationalPlaceCoeff 1)) *
          targetANF (rationalTangentAt 0 eps)) =
      monomialListProbeModel (oneTangentQuarticList eps) r := by
  rw [mul_assoc, one_tangent_product, oneTangentProductANF, mul_add,
    map_add]
  have hX : DegreeLE 1 (X r) := by
    apply degreeLE_monomial_of_card_le
    simp []
  have hlow : DegreeLE 3
      (anfMonomialList (oneTangentLowList eps)) := by
    exact degreeLE_anfMonomialList _ (oneTangentLowList_card eps)
  have hzero : anfQuinticAnchorProbe
      (X r * anfMonomialList (oneTangentLowList eps)) = 0 := by
    apply anfQuinticAnchorProbe_eq_zero_of_degreeLE_four
    simpa using hX.mul hlow
  rw [hzero, zero_add, anfQuinticAnchorProbe_X_mul_monomialList]

private theorem oneTangentBasisModel_eq_exterior :
    ∀ (r : Fin 8) (eps : F₂),
      monomialListProbeModel (oneTangentQuarticList eps) r =
        cubicAnchorWedgeProbe
          (vectorWedgeTwo (coordinateLinear r) (rationalPlaceTwo 1))
          (targetTwo (rationalTangentAt 0 eps)) := by
  decide

private theorem anfQuinticAnchorProbe_basis_one
    (r : Fin 8) (eps : F₂) :
    anfQuinticAnchorProbe
        ((X r * targetANF (rationalPlaceCoeff 1)) *
          targetANF (rationalTangentAt 0 eps)) =
      cubicAnchorWedgeProbe
        (vectorWedgeTwo (coordinateLinear r) (rationalPlaceTwo 1))
        (targetTwo (rationalTangentAt 0 eps)) := by
  rw [anfQuinticAnchorProbe_one_basis_model,
    oneTangentBasisModel_eq_exterior]

private theorem anfQuinticAnchorProbe_linear_place_one
    (ell : LinearForm) (eps : F₂) :
    anfQuinticAnchorProbe
        ((linearANF ell * targetANF (rationalPlaceCoeff 1)) *
          targetANF (rationalTangentAt 0 eps)) =
      cubicAnchorWedgeProbe
        (vectorWedgeTwo ell (rationalPlaceTwo 1))
        (targetTwo (rationalTangentAt 0 eps)) := by
  rw [linearANF]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul]
  simp_rw [anfQuinticAnchorProbe_basis_one]
  change _ = cubicAnchorWedgeProbeBilinear
    (vectorWedgeTwoBilinear ell (rationalPlaceTwo 1))
      (targetTwo (rationalTangentAt 0 eps))
  conv_rhs =>
    rw [linear_eq_sum_coordinate ell]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

/-- The quintic anchor coefficients of a variable times the infinity tangent product. -/
def infinityTangentBasisModel
    (r : Fin 8) (eps : F₂) (k : Fin 16) : F₂ :=
  eps * (if {r} ∪ {0, 3, 4, 7} = quinticAnchorSet k then 1 else 0) +
    (if {r} ∪ {0, 3, 5, 7} = quinticAnchorSet k then 1 else 0) +
    (if {r} ∪ {1, 3, 4, 7} = quinticAnchorSet k then 1 else 0)

private theorem targetANF_infinity_place :
    targetANF (rationalPlaceCoeff 2) =
      monomial ({3, 7} : Finset (Fin 8)) := by
  rw [rationalPlaceANF_direct]
  simp [linearANF, placeA, placeB, Fin.sum_univ_succ, X, monomial_mul]

private theorem infinity_tangent_product (eps : F₂) :
    targetANF (rationalPlaceCoeff 2) *
        targetANF (rationalTangentAt 0 eps) =
      eps • monomial ({0, 3, 4, 7} : Finset (Fin 8)) +
        monomial ({0, 3, 5, 7} : Finset (Fin 8)) +
        monomial ({1, 3, 4, 7} : Finset (Fin 8)) := by
  rw [targetANF_infinity_place, targetANF_zero_tangent,
    mul_target_zero_anf, mul_target_one_anf, mul_add,
    mul_smul_comm, mul_add]
  simp only [monomial_mul]
  have h0 : ({3, 7} : Finset (Fin 8)) ∪ {0, 4} = {0, 3, 4, 7} := by
    decide
  have h1 : ({3, 7} : Finset (Fin 8)) ∪ {0, 5} = {0, 3, 5, 7} := by
    decide
  have h2 : ({3, 7} : Finset (Fin 8)) ∪ {1, 4} = {1, 3, 4, 7} := by
    decide
  rw [h0, h1, h2]
  module

private theorem anfQuinticAnchorProbe_infinity_basis_model
    (r : Fin 8) (eps : F₂) :
    anfQuinticAnchorProbe
        ((X r * targetANF (rationalPlaceCoeff 2)) *
          targetANF (rationalTangentAt 0 eps)) =
      infinityTangentBasisModel r eps := by
  rw [mul_assoc, infinity_tangent_product, mul_add, mul_add,
    mul_smul_comm]
  funext k
  simp [X, monomial_mul, infinityTangentBasisModel]

private theorem infinityTangentBasisModel_eq_exterior :
    ∀ (r : Fin 8) (eps : F₂),
      infinityTangentBasisModel r eps =
        cubicAnchorWedgeProbe
          (vectorWedgeTwo (coordinateLinear r) (rationalPlaceTwo 2))
          (targetTwo (rationalTangentAt 0 eps)) := by
  decide

private theorem anfQuinticAnchorProbe_basis_infinity
    (r : Fin 8) (eps : F₂) :
    anfQuinticAnchorProbe
        ((X r * targetANF (rationalPlaceCoeff 2)) *
          targetANF (rationalTangentAt 0 eps)) =
      cubicAnchorWedgeProbe
        (vectorWedgeTwo (coordinateLinear r) (rationalPlaceTwo 2))
        (targetTwo (rationalTangentAt 0 eps)) := by
  rw [anfQuinticAnchorProbe_infinity_basis_model,
    infinityTangentBasisModel_eq_exterior]

private theorem anfQuinticAnchorProbe_linear_place_infinity
    (ell : LinearForm) (eps : F₂) :
    anfQuinticAnchorProbe
        ((linearANF ell * targetANF (rationalPlaceCoeff 2)) *
          targetANF (rationalTangentAt 0 eps)) =
      cubicAnchorWedgeProbe
        (vectorWedgeTwo ell (rationalPlaceTwo 2))
        (targetTwo (rationalTangentAt 0 eps)) := by
  rw [linearANF]
  simp only [Finset.sum_mul, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul]
  simp_rw [anfQuinticAnchorProbe_basis_infinity]
  change _ = cubicAnchorWedgeProbeBilinear
    (vectorWedgeTwoBilinear ell (rationalPlaceTwo 2))
      (targetTwo (rationalTangentAt 0 eps))
  conv_rhs =>
    rw [linear_eq_sum_coordinate ell]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

private theorem anfQuinticAnchorProbe_linear_place_zero_tangent :
    ∀ (ell : LinearForm) (theta : Fin 3) (eps : F₂),
      anfQuinticAnchorProbe
          ((linearANF ell * targetANF (rationalPlaceCoeff theta)) *
            targetANF (rationalTangentAt 0 eps)) =
        cubicAnchorWedgeProbe
          (vectorWedgeTwo ell (rationalPlaceTwo theta))
          (targetTwo (rationalTangentAt 0 eps)) := by
  intro ell theta eps
  fin_cases theta
  · exact anfQuinticAnchorProbe_linear_place_zero ell eps
  · exact anfQuinticAnchorProbe_linear_place_one ell eps
  · exact anfQuinticAnchorProbe_linear_place_infinity ell eps

/-- The selected degree-five coefficients of a rational cubic times a
zero-place tangent are its exterior anchor probes. -/
theorem anfQuinticAnchorProbe_linear_rational_zero_tangent
    (ell : LinearForm) (alpha : Fin 3 → F₂) (eps : F₂) :
    anfQuinticAnchorProbe
        ((linearANF ell * rationalANF alpha) *
          targetANF (rationalTangentAt 0 eps)) =
      cubicAnchorWedgeProbe (vectorWedgeTwo ell (rationalTwo alpha))
        (targetTwo (rationalTangentAt 0 eps)) := by
  rw [rationalANF_eq_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, map_sum, map_smul]
  simp_rw [anfQuinticAnchorProbe_linear_place_zero_tangent]
  change _ = cubicAnchorWedgeProbeBilinear
    (vectorWedgeTwoBilinear ell (rationalTwo alpha))
      (targetTwo (rationalTangentAt 0 eps))
  rw [rationalTwo]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro theta _
  rfl

private theorem f2_eq_of_add_eq_zero {x y : F₂} (h : x + y = 0) : x = y := by
  apply sub_eq_zero.mp
  rw [CharTwo.sub_eq_add]
  exact h

private theorem cubicAnchorProbe_rOne_span
    (ell : LinearForm) (a eps : F₂)
    (hann : ∀ t : Fin 16, cubicAnchorWedgeProbe
      (vectorWedgeTwo ell (rationalTwo ![a, 1, 0]))
      (targetTwo (rationalTangentAt 0 eps)) t = 0) :
    ell = ell 0 • placeA 1 + ell 4 • placeB 1 := by
  rcases f2_eq_zero_or_one eps with rfl | rfl
  · have h0 := hann 0
    have h1 := hann 1
    have h2 := hann 2
    have h3 := hann 3
    have h4 := hann 4
    have h7 := hann 7
    simp only [cubicAnchorWedgeProbe, wedgeThreeTwo, vectorWedgeTwo, quinticAnchorCoord,
      Fin.isValue, Matrix.cons_val_zero, rationalTwo, rationalPlaceTwo, placeA, placeB,
      Finset.sum_apply, Pi.smul_apply, vectorWedge, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val, smul_eq_mul, Fin.sum_univ_succ, mul_zero,
      add_zero, Matrix.cons_val_succ, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_const_zero, targetTwo, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
      lt_self_iff_false, ↓reduceDIte, Nat.mod_succ, Nat.reduceLT, f2_mul_self_quartic,
      mul_one, zero_add, Nat.reduceLeDiff, rationalTangentAt, Nat.reduceSub, Nat.reduceAdd,
      Fin.reduceFinMk, Std.le_refl, tsub_self, Nat.one_mod, Nat.one_lt_ofNat, Fin.mk_one,
      Nat.zero_mod, Nat.ofNat_pos, Fin.zero_eta, Nat.not_ofNat_le_one, Nat.lt_add_one
      ] at h0 h1 h2 h3 h4 h7
    have h20 : ell 2 = ell 0 := (f2_eq_of_add_eq_zero h0).symm
    have h30 : ell 3 = ell 0 :=
      (f2_eq_of_add_eq_zero h3).symm.trans h20
    have h10 : ell 1 = ell 0 := (f2_eq_of_add_eq_zero h4).trans h30
    have h64 : ell 6 = ell 4 := (f2_eq_of_add_eq_zero h2).symm
    have h74 : ell 7 = ell 4 :=
      (f2_eq_of_add_eq_zero h1).symm.trans h64
    have h54 : ell 5 = ell 4 := (f2_eq_of_add_eq_zero h7).trans h74
    funext i
    fin_cases i <;> simp [placeA, placeB, h10, h20, h30, h54, h64, h74]
  · have h0 := hann 0
    have h1 := hann 1
    have h2 := hann 2
    have h3 := hann 3
    have h4 := hann 4
    have h7 := hann 7
    simp only [cubicAnchorWedgeProbe, wedgeThreeTwo, vectorWedgeTwo, quinticAnchorCoord,
      Fin.isValue, Matrix.cons_val_zero, rationalTwo, rationalPlaceTwo, placeA, placeB,
      Finset.sum_apply, Pi.smul_apply, vectorWedge, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val, smul_eq_mul, Fin.sum_univ_succ, mul_zero,
      add_zero, Matrix.cons_val_succ, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_const_zero, targetTwo, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
      lt_self_iff_false, ↓reduceDIte, Nat.mod_succ, Nat.reduceLT, f2_mul_self_quartic,
      mul_one, zero_add, Nat.reduceLeDiff, rationalTangentAt, Nat.reduceSub, Nat.reduceAdd,
      Fin.reduceFinMk, Std.le_refl, tsub_self, Nat.one_mod, Nat.one_lt_ofNat, Fin.mk_one,
      Nat.zero_mod, Nat.ofNat_pos, Fin.zero_eta, Nat.not_ofNat_le_one, Nat.lt_add_one
      ] at h0 h1 h2 h3 h4 h7
    have h10 : ell 1 = ell 0 :=
      add_right_cancel (f2_eq_of_add_eq_zero h0).symm
    have h30 : ell 3 = ell 0 :=
      (f2_eq_of_add_eq_zero h4).symm.trans h10
    have h20 : ell 2 = ell 0 := (f2_eq_of_add_eq_zero h3).trans h30
    have h54 : ell 5 = ell 4 :=
      add_right_cancel (f2_eq_of_add_eq_zero h2).symm
    have h74 : ell 7 = ell 4 :=
      (f2_eq_of_add_eq_zero h7).symm.trans h54
    have h64 : ell 6 = ell 4 := (f2_eq_of_add_eq_zero h1).trans h74
    funext i
    fin_cases i <;> simp [placeA, placeB, h10, h20, h30, h54, h64, h74]

private theorem cubicAnchorProbe_rInfinity_span
    (ell : LinearForm) (a eps : F₂)
    (hann : ∀ t : Fin 16, cubicAnchorWedgeProbe
      (vectorWedgeTwo ell (rationalTwo ![a, 0, 1]))
      (targetTwo (rationalTangentAt 0 eps)) t = 0) :
    ell = ell 3 • placeA 2 + ell 7 • placeB 2 := by
  rcases f2_eq_zero_or_one eps with rfl | rfl
  · have h1 := hann 1
    have h3 := hann 3
    have h4 := hann 4
    have h7 := hann 7
    have h8 := hann 8
    have h11 := hann 11
    simp [cubicAnchorWedgeProbe, quinticAnchorCoord, wedgeThreeTwo, vectorWedgeTwo, targetTwo,
      rationalTangentAt, rationalTwo, rationalPlaceTwo, vectorWedge, placeA, placeB,
      Fin.sum_univ_succ] at h1 h3 h4 h7 h8 h11
    funext i
    fin_cases i <;> simp [placeA, placeB, h1, h3, h4, h7, h8, h11]
  · have h1 := hann 1
    have h3 := hann 3
    have h4 := hann 4
    have h7 := hann 7
    have h8 := hann 8
    have h11 := hann 11
    simp only [cubicAnchorWedgeProbe, wedgeThreeTwo, vectorWedgeTwo, quinticAnchorCoord,
      Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, rationalTwo, rationalPlaceTwo,
      placeA, placeB, Finset.sum_apply, Pi.smul_apply, vectorWedge, Matrix.cons_val',
      Matrix.cons_val, Matrix.cons_val_fin_one, f2_mul_self_quartic, smul_eq_mul,
      Fin.sum_univ_succ, mul_zero, add_zero, Matrix.cons_val_succ, mul_one,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_const_zero, targetTwo,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceLT, ↓reduceDIte, Nat.mod_succ,
      Finset.sum_const, Finset.card_singleton, one_smul, zero_add, Nat.lt_add_one,
      Nat.reduceLeDiff, rationalTangentAt, Nat.reduceSub, Nat.reduceAdd, Fin.reduceFinMk,
      Nat.zero_mod, Nat.ofNat_pos, Fin.mk_one, lt_self_iff_false, Std.le_refl, tsub_self,
      Nat.one_mod, Nat.one_lt_ofNat, Nat.not_ofNat_le_one, Fin.zero_eta] at h1 h3 h4 h7 h8 h11
    have h0 : ell 0 = 0 := (f2_eq_of_add_eq_zero h8).trans h4
    have h4' : ell 4 = 0 := (f2_eq_of_add_eq_zero h11).trans h7
    funext i
    fin_cases i <;> simp [placeA, placeB, h0, h1, h3, h4, h4', h7]

private theorem cubicAnchorProbe_twoPlaces_zero
    (ell : LinearForm) (a eps : F₂)
    (hann : ∀ t : Fin 16, cubicAnchorWedgeProbe
      (vectorWedgeTwo ell (rationalTwo ![a, 1, 1]))
      (targetTwo (rationalTangentAt 0 eps)) t = 0) :
    ell = 0 := by
  rcases f2_eq_zero_or_one eps with rfl | rfl
  · have h0 := hann 0
    have h1 := hann 1
    have h2 := hann 2
    have h3 := hann 3
    have h10 := hann 10
    have h13 := hann 13
    have h14 := hann 14
    have h15 := hann 15
    simp only [cubicAnchorWedgeProbe, wedgeThreeTwo, vectorWedgeTwo, quinticAnchorCoord,
      Fin.isValue, Matrix.cons_val_zero, rationalTwo, rationalPlaceTwo, placeA, placeB,
      Finset.sum_apply, Pi.smul_apply, vectorWedge, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val, smul_eq_mul, Fin.sum_univ_succ, mul_zero,
      add_zero, Matrix.cons_val_succ, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_const_zero, targetTwo, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
      lt_self_iff_false, ↓reduceDIte, Nat.mod_succ, Nat.reduceLT, f2_mul_self_quartic,
      mul_one, zero_add, Nat.reduceLeDiff, rationalTangentAt, Nat.reduceSub, Nat.reduceAdd,
      Fin.reduceFinMk, Std.le_refl, tsub_self, Nat.one_mod, Nat.one_lt_ofNat, Fin.mk_one,
      Nat.zero_mod, Nat.ofNat_pos, Fin.zero_eta, Nat.not_ofNat_le_one, Finset.sum_const,
      Finset.card_singleton, one_smul, Nat.lt_add_one] at h0 h1 h2 h3 h10 h13 h14 h15
    have hone : (1 : F₂) + 1 = 0 := CharTwo.add_self_eq_zero 1
    simp only [hone, mul_zero, zero_add] at h1 h3
    have h7z : ell 7 = 0 := h1
    have h3z : ell 3 = 0 := h3
    have h2z : ell 2 = 0 := (f2_eq_of_add_eq_zero h13).trans h3z
    have h1z : ell 1 = 0 := (f2_eq_of_add_eq_zero h10).trans h2z
    have h0z : ell 0 = 0 := (f2_eq_of_add_eq_zero h0).trans h2z
    have h6z : ell 6 = 0 := (f2_eq_of_add_eq_zero h14).trans h7z
    have h4z : ell 4 = 0 := (f2_eq_of_add_eq_zero h2).trans h6z
    have h5z : ell 5 = 0 := (f2_eq_of_add_eq_zero h15).trans h7z
    funext i
    fin_cases i <;> simp [h0z, h1z, h2z, h3z, h4z, h5z, h6z, h7z]
  · have h0 := hann 0
    have h1 := hann 1
    have h2 := hann 2
    have h3 := hann 3
    have h5 := hann 5
    have h6 := hann 6
    have h10 := hann 10
    have h15 := hann 15
    simp only [cubicAnchorWedgeProbe, wedgeThreeTwo, vectorWedgeTwo, quinticAnchorCoord,
      Fin.isValue, Matrix.cons_val_zero, rationalTwo, rationalPlaceTwo, placeA, placeB,
      Finset.sum_apply, Pi.smul_apply, vectorWedge, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val, smul_eq_mul, Fin.sum_univ_succ, mul_zero,
      add_zero, Matrix.cons_val_succ, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_const_zero, targetTwo, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
      lt_self_iff_false, ↓reduceDIte, Nat.mod_succ, Nat.reduceLT, f2_mul_self_quartic,
      mul_one, zero_add, Nat.reduceLeDiff, rationalTangentAt, Nat.reduceSub, Nat.reduceAdd,
      Fin.reduceFinMk, Std.le_refl, tsub_self, Nat.one_mod, Nat.one_lt_ofNat, Fin.mk_one,
      Nat.zero_mod, Nat.ofNat_pos, Fin.zero_eta, Nat.not_ofNat_le_one, Finset.sum_const,
      Finset.card_singleton, one_smul, Nat.lt_add_one] at h0 h1 h2 h3 h5 h6 h10 h15
    have hone : (1 : F₂) + 1 = 0 := CharTwo.add_self_eq_zero 1
    simp only [hone, mul_zero, zero_add] at h1 h3
    have h7z : ell 7 = 0 := h1
    have h3z : ell 3 = 0 := h3
    have h2z : ell 2 = 0 := (f2_eq_of_add_eq_zero h5).trans h3z
    have h1z : ell 1 = 0 := (f2_eq_of_add_eq_zero h10).trans h2z
    have h6z : ell 6 = 0 := (f2_eq_of_add_eq_zero h6).trans h7z
    have h5z : ell 5 = 0 := (f2_eq_of_add_eq_zero h15).trans h7z
    simp [h1z, h2z] at h0
    simp [h5z, h6z] at h2
    funext i
    fin_cases i <;>
      simp [h0, h1z, h2z, h3z, h2, h5z, h6z, h7z]

private theorem vectorWedgeTwo_place_span_zero
    (ell : LinearForm) (theta : Fin 3) (a b : F₂)
    (hell : ell = a • placeA theta + b • placeB theta) :
    vectorWedgeTwo ell (rationalPlaceTwo theta) = 0 := by
  rw [hell, rationalPlaceTwo, vectorWedgeTwo_add_left,
    vectorWedgeTwo_smul_left, vectorWedgeTwo_smul_left,
    vectorWedgeTwo_repeated_left, vectorWedgeTwo_repeated_right]
  simp

private theorem vectorWedgeTwo_rational_zero_only
    (ell : LinearForm) (a : F₂) :
    vectorWedgeTwo ell (rationalTwo ![a, 0, 0]) =
      vectorWedgeTwo (a • ell) (rationalPlaceTwo 0) := by
  have hq : rationalTwo ![a, 0, 0] = a • rationalPlaceTwo 0 := by
    simp [rationalTwo, Fin.sum_univ_succ]
  rw [hq, vectorWedgeTwo_smul_right_h, vectorWedgeTwo_smul_left]

private theorem vectorWedgeTwo_rational_one_support
    (ell : LinearForm) (a : F₂)
    (hell : ell = ell 0 • placeA 1 + ell 4 • placeB 1) :
    vectorWedgeTwo ell (rationalTwo ![a, 1, 0]) =
      vectorWedgeTwo (a • ell) (rationalPlaceTwo 0) := by
  have hq : rationalTwo ![a, 1, 0] =
      a • rationalPlaceTwo 0 + rationalPlaceTwo 1 := by
    simp [rationalTwo, Fin.sum_univ_succ]
  have hv := vectorWedgeTwo_place_span_zero ell 1 (ell 0) (ell 4) hell
  calc
    vectorWedgeTwo ell (rationalTwo ![a, 1, 0]) =
        a • vectorWedgeTwo ell (rationalPlaceTwo 0) +
          vectorWedgeTwo ell (rationalPlaceTwo 1) := by
            rw [hq, vectorWedgeTwo_add_right_h,
              vectorWedgeTwo_smul_right_h]
    _ = a • vectorWedgeTwo ell (rationalPlaceTwo 0) := by rw [hv, add_zero]
    _ = vectorWedgeTwo (a • ell) (rationalPlaceTwo 0) := by
      rw [vectorWedgeTwo_smul_left]

private theorem vectorWedgeTwo_rational_infinity_support
    (ell : LinearForm) (a : F₂)
    (hell : ell = ell 3 • placeA 2 + ell 7 • placeB 2) :
    vectorWedgeTwo ell (rationalTwo ![a, 0, 1]) =
      vectorWedgeTwo (a • ell) (rationalPlaceTwo 0) := by
  have hq : rationalTwo ![a, 0, 1] =
      a • rationalPlaceTwo 0 + rationalPlaceTwo 2 := by
    simp [rationalTwo, Fin.sum_univ_succ]
  have hv := vectorWedgeTwo_place_span_zero ell 2 (ell 3) (ell 7) hell
  calc
    vectorWedgeTwo ell (rationalTwo ![a, 0, 1]) =
        a • vectorWedgeTwo ell (rationalPlaceTwo 0) +
          vectorWedgeTwo ell (rationalPlaceTwo 2) := by
            rw [hq, vectorWedgeTwo_add_right_h,
              vectorWedgeTwo_smul_right_h]
    _ = a • vectorWedgeTwo ell (rationalPlaceTwo 0) := by rw [hv, add_zero]
    _ = vectorWedgeTwo (a • ell) (rationalPlaceTwo 0) := by
      rw [vectorWedgeTwo_smul_left]

/-- Scalar form of the 16-row annihilator certificate. -/
private theorem cubicAnchorProbe_zero_tangent_scalar_certificate :
    ∀ (ell : LinearForm) (alpha : Fin 3 → F₂) (eps : F₂),
      (∀ t : Fin 16, cubicAnchorWedgeProbe
        (vectorWedgeTwo ell (rationalTwo alpha))
        (targetTwo (rationalTangentAt 0 eps)) t = 0) →
      ∀ i j k : Fin 8,
        vectorWedgeTwo ell (rationalTwo alpha) i j k =
          vectorWedgeTwo (alpha 0 • ell) (rationalPlaceTwo 0) i j k := by
  intro ell alpha eps hann i j k
  let a : F₂ := alpha 0
  rcases f2_eq_zero_or_one (alpha 1) with h1 | h1 <;>
    rcases f2_eq_zero_or_one (alpha 2) with h2 | h2
  · have halpha : alpha = ![a, 0, 0] := by
      funext theta
      fin_cases theta <;> simp [a, h1, h2]
    have heq := vectorWedgeTwo_rational_zero_only ell a
    simpa [halpha] using congrFun (congrFun (congrFun heq i) j) k
  · have halpha : alpha = ![a, 0, 1] := by
      funext theta
      fin_cases theta <;> simp [a, h1, h2]
    have hann' : ∀ t : Fin 16, cubicAnchorWedgeProbe
        (vectorWedgeTwo ell (rationalTwo ![a, 0, 1]))
        (targetTwo (rationalTangentAt 0 eps)) t = 0 := by
      simpa [halpha] using hann
    have hell := cubicAnchorProbe_rInfinity_span ell a eps hann'
    have heq := vectorWedgeTwo_rational_infinity_support ell a hell
    simpa [halpha] using congrFun (congrFun (congrFun heq i) j) k
  · have halpha : alpha = ![a, 1, 0] := by
      funext theta
      fin_cases theta <;> simp [a, h1, h2]
    have hann' : ∀ t : Fin 16, cubicAnchorWedgeProbe
        (vectorWedgeTwo ell (rationalTwo ![a, 1, 0]))
        (targetTwo (rationalTangentAt 0 eps)) t = 0 := by
      simpa [halpha] using hann
    have hell := cubicAnchorProbe_rOne_span ell a eps hann'
    have heq := vectorWedgeTwo_rational_one_support ell a hell
    simpa [halpha] using congrFun (congrFun (congrFun heq i) j) k
  · have halpha : alpha = ![a, 1, 1] := by
      funext theta
      fin_cases theta <;> simp [a, h1, h2]
    have hann' : ∀ t : Fin 16, cubicAnchorWedgeProbe
        (vectorWedgeTwo ell (rationalTwo ![a, 1, 1]))
        (targetTwo (rationalTangentAt 0 eps)) t = 0 := by
      simpa [halpha] using hann
    have hell := cubicAnchorProbe_twoPlaces_zero ell a eps hann'
    subst ell
    simp [vectorWedgeTwo]

/-- The 16-row certificate: a rational cubic annihilating a
zero-place tangent is anchored at the zero rational place. -/
theorem cubicAnchorProbe_zero_tangent_classification
    (ell : LinearForm) (alpha : Fin 3 → F₂) (eps : F₂)
    (hann : cubicAnchorWedgeProbe
      (vectorWedgeTwo ell (rationalTwo alpha))
      (targetTwo (rationalTangentAt 0 eps)) = 0) :
    vectorWedgeTwo ell (rationalTwo alpha) =
      vectorWedgeTwo (alpha 0 • ell) (rationalPlaceTwo 0) := by
  have hann' : ∀ t : Fin 16, cubicAnchorWedgeProbe
      (vectorWedgeTwo ell (rationalTwo alpha))
      (targetTwo (rationalTangentAt 0 eps)) t = 0 := by
    exact congrFun hann
  funext i j k
  exact cubicAnchorProbe_zero_tangent_scalar_certificate
    ell alpha eps hann' i j k

/-- A degree-at-most-two ANF times a quadratic target contributes no
degree-five anchor probe. -/
theorem anfQuinticAnchorProbe_low_mul_target_zero
    {p : ANF 8} (hp : DegreeLE 2 p) (c : TargetCoeff) :
    anfQuinticAnchorProbe (p * targetANF c) = 0 := by
  apply anfQuinticAnchorProbe_eq_zero_of_degreeLE_four
  exact hp.mul (degreeLE_two_targetANF c)

end
end N4
end UnrestrictedBooleanMul
