/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StrandTransport

/-!
# One-position basis vectors

The colour-model basis vectors at a single position are the
unit-padded standard basis vectors: the single-layer computation
of `colourPowerEquiv 1` on padded pure tensors.
-/

@[expose] public section

namespace RS

open scoped TensorProduct

variable {k ℓ : ℕ}

/-- The one-position even colouring. -/
def oneColourE (k ℓ : ℕ) (i : Fin k) :
    MixedColouring k ℓ 1 := fun _ => Sum.inl i

/-- The one-position odd colouring. -/
def oneColourO (k ℓ : ℕ) (a : Fin (2 * ℓ)) :
    MixedColouring k ℓ 1 := fun _ => Sum.inr a

/-- An even one-position colouring is even. -/
theorem oneColourE_isEven (i : Fin k) :
    MixedColouring.IsEven (oneColourE k ℓ i) :=
  ⟨0, by simp [MixedColouring.oddSet, oneColourE]⟩

/-- And an odd one is not — the grading at a single position. -/
theorem oneColourO_not_isEven (a : Fin (2 * ℓ)) :
    ¬ MixedColouring.IsEven (oneColourO k ℓ a) := by
  intro h
  have hcard : (MixedColouring.oddSet
      (oneColourO k ℓ a)).card = 1 := by
    simp [MixedColouring.oddSet, oneColourO]
  rw [MixedColouring.IsEven, hcard] at h
  exact (Nat.not_even_iff_odd.mpr (by decide)) h

/-- One-position colourings are determined at zero. -/
theorem oneColour_ext {c₁ c₂ : MixedColouring k ℓ 1}
    (h : c₁ 0 = c₂ 0) : c₁ = c₂ := by
  funext j
  rw [Subsingleton.elim j 0]
  exact h

/-- The forward even split at one position, even colour. -/
private theorem evenSplit0_inl (c : MixedColouring k ℓ 1)
    (hc : c.IsEven) (i : Fin k)
    (hi : c (Fin.last 0) = Sum.inl i) :
    evenSplitEquiv k ℓ 0 ⟨c, hc⟩ =
      Sum.inl (⟨MixedColouring.tail c,
        (c.isEven_succ_left i hi).mp hc⟩, i) := by
  have inv : (evenSplitEquiv k ℓ 0).symm
      (Sum.inl (⟨MixedColouring.tail c,
        (c.isEven_succ_left i hi).mp hc⟩, i)) = ⟨c, hc⟩ := by
    apply Subtype.ext
    rw [evenSplitEquiv_symm_inl]
    funext j
    refine Fin.lastCases ?_ (fun j' => j'.elim0) j
    exact (colouringSplit_symm_last _ _).trans hi.symm
  rw [← inv, Equiv.apply_symm_apply]

/-- The forward odd split at one position, odd colour. -/
private theorem oddSplit0_inr (c : MixedColouring k ℓ 1)
    (hc : ¬ c.IsEven) (a : Fin (2 * ℓ))
    (ha : c (Fin.last 0) = Sum.inr a) :
    oddSplitEquiv k ℓ 0 ⟨c, hc⟩ =
      Sum.inr (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact hc ((c.isEven_succ_right a ha).mpr hcontra)⟩,
        a) := by
  have inv : (oddSplitEquiv k ℓ 0).symm
      (Sum.inr (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact hc ((c.isEven_succ_right a ha).mpr hcontra)⟩,
        a)) = ⟨c, hc⟩ := by
    apply Subtype.ext
    rw [oddSplitEquiv_symm_inr]
    funext j
    refine Fin.lastCases ?_ (fun j' => j'.elim0) j
    exact (colouringSplit_symm_last _ _).trans ha.symm
  rw [← inv, Equiv.apply_symm_apply]

-- Raised budget: the one-position basis vector is identified
-- coordinate by coordinate through the colouring equivalence.
/-- **The one-position even basis vector is the unit-padded
standard even basis vector.** -/
theorem evenBasisVec_one (i : Fin k) :
    evenBasisVec (⟨oneColourE k ℓ i, oneColourE_isEven i⟩ :
      {c : MixedColouring k ℓ 1 // c.IsEven}) =
      evenPair (1 : ℂ) (stdE k i) := by
  apply (colourPowerEquiv k ℓ 1).evenEquiv.injective
  rw [show (colourPowerEquiv k ℓ 1).evenEquiv
      (evenBasisVec (⟨oneColourE k ℓ i,
        oneColourE_isEven i⟩ :
        {c : MixedColouring k ℓ 1 // c.IsEven})) =
    Pi.single ⟨oneColourE k ℓ i, oneColourE_isEven i⟩ 1 from
    (colourPowerEquiv k ℓ 1).evenEquiv.apply_symm_apply _]
  funext ⟨c', hc'⟩
  change _ = ((colourPowerEquiv k ℓ 1).evenEquiv
    (evenPair (1 : ℂ) (stdE k i)) ⟨c', hc'⟩)
  change _ = (colourPowerStep k ℓ 0).evenEquiv
    ((TensorProduct.congr
        (colourPowerZero k ℓ).evenEquiv
        (LinearEquiv.refl ℂ (Fin k → ℂ)))
      ((1 : ℂ) ⊗ₜ[ℂ] stdE k i),
      (TensorProduct.congr
        (colourPowerZero k ℓ).oddEquiv
        (LinearEquiv.refl ℂ (Fin (2 * ℓ) → ℂ))) 0) ⟨c', hc'⟩
  rw [TensorProduct.congr_tmul, map_zero]
  change _ = Sum.elim
    (fun p => funTensorFun _ _
      (((colourPowerZero k ℓ).evenEquiv (1 : ℂ)) ⊗ₜ[ℂ]
        (LinearEquiv.refl ℂ (Fin k → ℂ) (stdE k i))) p)
    (fun q => funTensorFun _ _
      (0 : ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} → ℂ)
        ⊗[ℂ] (Fin (2 * ℓ) → ℂ)) q)
    (evenSplitEquiv k ℓ 0 ⟨c', hc'⟩)
  rcases hlast : c' (Fin.last 0) with j | b
  · rw [evenSplit0_inl c' hc' j hlast, Sum.elim_inl]
    refine Eq.trans ?_ ((funTensorFun_tmul _ _ _).symm)
    rw [show ((colourPowerZero k ℓ).evenEquiv (1 : ℂ))
        (⟨MixedColouring.tail c',
          (c'.isEven_succ_left j hlast).mp hc'⟩, j).1 = 1
      from rfl]
    rw [one_mul]
    have hval : (Pi.single (⟨oneColourE k ℓ i,
        oneColourE_isEven i⟩ :
      {c : MixedColouring k ℓ 1 // c.IsEven}) (1 : ℂ) :
        {c : MixedColouring k ℓ 1 // c.IsEven} → ℂ)
        ⟨c', hc'⟩ =
      (Pi.single i (1 : ℂ) : Fin k → ℂ) j := by
      by_cases hij : j = i
      · subst hij
        rw [single_val_same ⟨oneColourE k ℓ j,
            oneColourE_isEven j⟩ ⟨c', hc'⟩
          (oneColour_ext (show oneColourE k ℓ j 0 =
            c' 0 from hlast.symm)),
          Pi.single_eq_same]
      · rw [single_val_ne ⟨oneColourE k ℓ i,
            oneColourE_isEven i⟩ ⟨c', hc'⟩
          (fun he => hij (Sum.inl.inj
            (show Sum.inl j = Sum.inl i from by
              have he' : c' = oneColourE k ℓ i := he
              rw [← hlast, he']; rfl))),
          Pi.single_eq_of_ne hij]
    exact hval.trans rfl
  · -- Odd colour at an even one-position colouring: both sides
    -- vanish.
    rw [single_val_ne ⟨oneColourE k ℓ i,
        oneColourE_isEven i⟩ ⟨c', hc'⟩
      (fun he => Sum.inr_ne_inl
        (show Sum.inr b = Sum.inl i from by
          have he' : c' = oneColourE k ℓ i := he
          rw [← hlast, he']; rfl))]
    rcases hs : evenSplitEquiv k ℓ 0 ⟨c', hc'⟩ with ⟨cp, j₀⟩ | p
    · exfalso
      have hval := congrArg
        (fun z => ((evenSplitEquiv k ℓ 0).symm z).val
          (Fin.last 0)) hs
      rw [Equiv.symm_apply_apply] at hval
      rw [evenSplitEquiv_symm_inl] at hval
      rw [colouringSplit_symm_last] at hval
      have hval' : c' (Fin.last 0) = Sum.inl j₀ := hval
      exact Sum.inr_ne_inl (hlast.symm.trans hval')
    · rw [Sum.elim_inr]
      rw [show funTensorFun _ _
          (0 : ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} → ℂ)
            ⊗[ℂ] (Fin (2 * ℓ) → ℂ)) p = 0 from by
        rw [map_zero]
        rfl]

-- As for the even basis vector, on the odd half.
/-- **The one-position odd basis vector is the unit-padded
standard odd basis vector.** -/
theorem oddBasisVec_one (a : Fin (2 * ℓ)) :
    oddBasisVec (⟨oneColourO k ℓ a, oneColourO_not_isEven a⟩ :
      {c : MixedColouring k ℓ 1 // ¬ c.IsEven}) =
      oddUnitPad (stdF ℓ a) := by
  apply (colourPowerEquiv k ℓ 1).oddEquiv.injective
  rw [show (colourPowerEquiv k ℓ 1).oddEquiv
      (oddBasisVec (⟨oneColourO k ℓ a,
        oneColourO_not_isEven a⟩ :
        {c : MixedColouring k ℓ 1 // ¬ c.IsEven})) =
    Pi.single ⟨oneColourO k ℓ a, oneColourO_not_isEven a⟩ 1 from
    (colourPowerEquiv k ℓ 1).oddEquiv.apply_symm_apply _]
  funext ⟨c', hc'⟩
  change _ = ((colourPowerEquiv k ℓ 1).oddEquiv
    (oddUnitPad (stdF ℓ a)) ⟨c', hc'⟩)
  change _ = (colourPowerStep k ℓ 0).oddEquiv
    ((TensorProduct.congr
        (colourPowerZero k ℓ).evenEquiv
        (LinearEquiv.refl ℂ (Fin (2 * ℓ) → ℂ)))
      ((1 : ℂ) ⊗ₜ[ℂ] stdF ℓ a),
      (TensorProduct.congr
        (colourPowerZero k ℓ).oddEquiv
        (LinearEquiv.refl ℂ (Fin k → ℂ))) 0) ⟨c', hc'⟩
  rw [TensorProduct.congr_tmul, map_zero]
  change _ = Sum.elim
    (fun p => funTensorFun _ _
      (((colourPowerZero k ℓ).evenEquiv (1 : ℂ)) ⊗ₜ[ℂ]
        (LinearEquiv.refl ℂ (Fin (2 * ℓ) → ℂ) (stdF ℓ a))) p)
    (fun q => funTensorFun _ _
      (0 : ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} → ℂ)
        ⊗[ℂ] (Fin k → ℂ)) q)
    ((Equiv.sumComm _ _).symm (oddSplitEquiv k ℓ 0 ⟨c', hc'⟩))
  rcases hlast : c' (Fin.last 0) with j | b
  · -- Even colour at an odd one-position colouring: vacuous.
    exfalso
    refine hc' ⟨0, ?_⟩
    have hset : MixedColouring.oddSet c' = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      rw [MixedColouring.oddSet, Finset.mem_filter] at hp
      have hp0 : c' p = Sum.inl j := by
        rw [Subsingleton.elim p (Fin.last 0)]
        exact hlast
      rw [hp0] at hp
      exact Bool.noConfusion hp.2
    rw [hset]
    rfl
  · rw [oddSplit0_inr c' hc' b hlast]
    rw [show ((Equiv.sumComm
        ({c : MixedColouring k ℓ 0 // c.IsEven} ×
          Fin (2 * ℓ))
        ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} ×
          Fin k)).symm
        (Sum.inr (⟨MixedColouring.tail c', by
          by_contra hcontra
          exact hc' ((c'.isEven_succ_right b hlast).mpr
            hcontra)⟩, b))) =
      Sum.inl (⟨MixedColouring.tail c', by
        by_contra hcontra
        exact hc' ((c'.isEven_succ_right b hlast).mpr
          hcontra)⟩, b) from rfl]
    rw [Sum.elim_inl]
    refine Eq.trans ?_ ((funTensorFun_tmul _ _ _).symm)
    rw [show ((colourPowerZero k ℓ).evenEquiv (1 : ℂ))
        (⟨MixedColouring.tail c', by
          by_contra hcontra
          exact hc' ((c'.isEven_succ_right b hlast).mpr
            hcontra)⟩, b).1 = 1
      from rfl]
    rw [one_mul]
    have hval : (Pi.single (⟨oneColourO k ℓ a,
        oneColourO_not_isEven a⟩ :
      {c : MixedColouring k ℓ 1 // ¬ c.IsEven}) (1 : ℂ) :
        {c : MixedColouring k ℓ 1 // ¬ c.IsEven} → ℂ)
        ⟨c', hc'⟩ =
      (Pi.single a (1 : ℂ) : Fin (2 * ℓ) → ℂ) b := by
      by_cases hab : b = a
      · subst hab
        rw [single_val_same ⟨oneColourO k ℓ b,
            oneColourO_not_isEven b⟩ ⟨c', hc'⟩
          (oneColour_ext (show oneColourO k ℓ b 0 =
            c' 0 from hlast.symm)),
          Pi.single_eq_same]
      · rw [single_val_ne ⟨oneColourO k ℓ a,
            oneColourO_not_isEven a⟩ ⟨c', hc'⟩
          (fun he => hab (Sum.inr.inj
            (show Sum.inr b = Sum.inr a from by
              have he' : c' = oneColourO k ℓ a := he
              rw [← hlast, he']; rfl))),
          Pi.single_eq_of_ne hab]
    exact hval.trans rfl

end RS
