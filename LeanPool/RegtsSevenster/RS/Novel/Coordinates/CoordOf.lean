/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ParameterModel
public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourConj

/-!
# Coordinates of model vectors

The coordinate reading of a power vector at a colouring (zero on
odd parity), the cast rule, the conjugation transfer, and the
basis expansion: the vocabulary in which the final computation
evaluates.
-/

@[expose] public section

namespace RS

variable {k ℓ : ℕ}

/-- The coordinate of a model vector at a colouring. -/
noncomputable def coordOf {n : ℕ}
    (v : (superPow (stdSuperPair k ℓ) n).even)
    (c : MixedColouring k ℓ n) : ℂ :=
  if hc : c.IsEven then
    (colourPowerEquiv k ℓ n).evenEquiv v ⟨c, hc⟩ else 0

/-- Coordinates vanish on odd parity. -/
theorem coordOf_odd {n : ℕ}
    (v : (superPow (stdSuperPair k ℓ) n).even)
    (c : MixedColouring k ℓ n) (hc : ¬ c.IsEven) :
    coordOf v c = 0 :=
  dite_eq_right hc

/-- The cast rule: coordinates of a recast vector read the
recast colouring. -/
theorem coordOf_cast {n₁ n₂ : ℕ} (h : n₁ = n₂)
    (v : (superPow (stdSuperPair k ℓ) n₁).even)
    (c : MixedColouring k ℓ n₂) :
    coordOf (((CategoryTheory.eqToHom
        (congrArg (superPow (stdSuperPair k ℓ)) h) :
      superPow (stdSuperPair k ℓ) n₁ ⟶
        superPow (stdSuperPair k ℓ) n₂) :
      SuperVect.Hom _ _).evenMap v) c =
    coordOf v (c ∘ finCongr h) := by
  subst h
  rfl

/-- The conjugation transfer: colour-model conjugates act on
coordinate functions. -/
theorem toColour_apply {n : ℕ}
    (g : superPow (stdSuperPair k ℓ) n ⟶ superPow (stdSuperPair k ℓ) n)
    (v : (superPow (stdSuperPair k ℓ) n).even) :
    ((toColour n g) : SuperVect.Hom _ _).evenMap
        ((colourPowerEquiv k ℓ n).evenEquiv v) =
      (colourPowerEquiv k ℓ n).evenEquiv
        ((g : SuperVect.Hom _ _).evenMap v) := by
  change (colourPowerEquiv k ℓ n).evenEquiv
    ((g : SuperVect.Hom _ _).evenMap
      ((colourPowerEquiv k ℓ n).evenEquiv.symm
        ((colourPowerEquiv k ℓ n).evenEquiv v))) = _
  rw [(colourPowerEquiv k ℓ n).evenEquiv.symm_apply_apply]

/-- The basis expansion of a model vector by its coordinates. -/
theorem coord_expansion {n : ℕ}
    (v : (superPow (stdSuperPair k ℓ) n).even) :
    v = ∑ c : {c : MixedColouring k ℓ n // c.IsEven},
      ((colourPowerEquiv k ℓ n).evenEquiv v c) •
        (colourPowerEquiv k ℓ n).evenEquiv.symm
          (Pi.single c 1) := by
  apply (colourPowerEquiv k ℓ n).evenEquiv.injective
  rw [map_sum]
  have hterm : ∀ c' : {c : MixedColouring k ℓ n // c.IsEven},
      (colourPowerEquiv k ℓ n).evenEquiv
        (((colourPowerEquiv k ℓ n).evenEquiv v c') •
          (colourPowerEquiv k ℓ n).evenEquiv.symm
            (Pi.single c' 1)) =
      Pi.single c' ((colourPowerEquiv k ℓ n).evenEquiv v c') :=
    fun c' => by
      rw [map_smul]
      rw [show (colourPowerEquiv k ℓ n).evenEquiv
          ((colourPowerEquiv k ℓ n).evenEquiv.symm
            (Pi.single c' 1)) = Pi.single c' (1 : ℂ) from
        (colourPowerEquiv k ℓ n).evenEquiv.apply_symm_apply _]
      funext j
      by_cases hj : j = c'
      · subst hj
        have h1 : (Pi.single j (1 : ℂ) :
            {c : MixedColouring k ℓ n // c.IsEven} → ℂ) j =
            (1 : ℂ) := Pi.single_eq_same j 1
        have h2 : (Pi.single j
            ((colourPowerEquiv k ℓ n).evenEquiv v j) :
            {c : MixedColouring k ℓ n // c.IsEven} → ℂ) j =
            (colourPowerEquiv k ℓ n).evenEquiv v j :=
          Pi.single_eq_same j _
        trans ((colourPowerEquiv k ℓ n).evenEquiv v j)
        · exact (congrArg (fun z : ℂ =>
            ((colourPowerEquiv k ℓ n).evenEquiv v j) • z)
            h1).trans (mul_one _)
        · exact h2.symm
      · have h1 : (Pi.single c' (1 : ℂ) :
            {c : MixedColouring k ℓ n // c.IsEven} → ℂ) j =
            0 := Pi.single_eq_of_ne hj 1
        have h2 : (Pi.single c'
            ((colourPowerEquiv k ℓ n).evenEquiv v c') :
            {c : MixedColouring k ℓ n // c.IsEven} → ℂ) j =
            0 := Pi.single_eq_of_ne hj _
        trans (0 : ℂ)
        · exact (congrArg (fun z : ℂ =>
            ((colourPowerEquiv k ℓ n).evenEquiv v c') • z)
            h1).trans (smul_zero _)
        · exact h2.symm
  rw [Finset.sum_congr rfl (fun c' _ => hterm c')]
  exact (Finset.univ_sum_single
    ((colourPowerEquiv k ℓ n).evenEquiv v)).symm

end RS
