/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.LowProductBridge

/-!
# Algebraic exclusion of seven gates

A seven-gate circuit computing `Mul 4` would have no defect: its final wire
space contains the sixteen-dimensional space `Aff + T`, while seven gates can
raise the affine dimension by at most seven.  Thus every intermediate wire
lands in `Aff + T`.  The rational-prefix closure theorem then traps every gate
in `Aff + R`, contradicting the presence of a non-rational target direction.

This argument uses neither circuit enumeration nor a truth-table search.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

theorem targetAmbient_le_finalWire {r : Nat} (C : Circuit 8 r)
    (hC : C.Computes (Mul 4)) :
    targetAmbient 8 (mulTarget 4) ≤ C.finalWire := by
  apply sup_le
  · simpa [Circuit.finalWire] using
      affine_le_wireSpace C.gate (j := r)
  · rw [mulTarget, Submodule.span_le]
    rintro p ⟨i, rfl⟩
    exact hC i

/-- Seven gates leave no room for a direction outside `Aff + T`. -/
theorem finalWire_eq_targetAmbient_of_seven
    (C : Circuit 8 7) (hC : C.Computes (Mul 4)) :
    C.finalWire = targetAmbient 8 (mulTarget 4) := by
  apply (Submodule.eq_of_le_of_finrank_le
    (targetAmbient_le_finalWire C hC) ?_).symm
  have hdim := finalWire_finrank_le_affine_add C
  rw [affine_eight_finrank] at hdim
  rw [targetAmbient_four_finrank]
  omega

theorem wireSpace_le_rationalLow_of_prefix
    {r j : Nat} (C : Circuit 8 r)
    (hgate : ∀ i : Fin r, i.val < j → C.gate i ∈ rationalLowSpace) :
    wireSpace C.gate j ≤ rationalLowSpace := by
  rw [wireSpace]
  apply sup_le le_sup_left
  rw [Submodule.span_le]
  rintro p ⟨i, hi, rfl⟩
  exact hgate i hi

private theorem targetBasis_one_not_rational :
    targetBasis (1 : Fin 7) ∉ rationalCoeffSpace := by
  intro h
  rcases targetCoeff_eq_rationalCoeffRep_of_mem h with ⟨α, hα⟩
  have h1 := congrFun hα (1 : Fin 7)
  have h2 := congrFun hα (2 : Fin 7)
  simp [targetBasis, Pi.basisFun, rationalCoeffRep, rZeroCoeff, rOneCoeff, rInfinityCoeff
    ] at h1 h2
  exact one_ne_zero (h1.trans h2.symm)

private theorem mul_one_not_mem_rationalLow :
    Mul 4 (1 : Fin 7) ∉ rationalLowSpace := by
  intro h
  rcases exists_lowProduct_rep_of_mem_rationalLow h with
    ⟨a, ell, α, hrep⟩
  have hproj := congrArg anfTwoProjection hrep
  have haff : affineANF a ell ∈ affine 8 := affineANF_mem a ell
  rw [anfTwoProjection_Mul, map_add,
    anfTwoProjection_kills_affine haff,
    anfTwoProjection_rationalANF, zero_add,
    ← targetTwo_rationalCoeffRep] at hproj
  apply targetBasis_one_not_rational
  have hc : targetBasis (1 : Fin 7) = rationalCoeffRep α :=
    targetTwo_injective hproj
  rw [hc]
  exact rationalCoeffRep_mem α

/-- The purely algebraic seven-gate lower bound used by normalization. -/
theorem no_seven_gate_circuit :
    ¬ Nonempty {C : Circuit 8 7 // C.Computes (Mul 4)} := by
  rintro ⟨⟨C, hC⟩⟩
  have hfinal := finalWire_eq_targetAmbient_of_seven C hC
  have hgateAmbient (i : Fin 7) :
      C.gate i ∈ targetAmbient 8 (mulTarget 4) := by
    rw [← hfinal]
    exact gate_mem_finalWire C i
  have nextGate (j : Fin 7)
      (hprev : ∀ i : Fin 7, i.val < j.val →
        C.gate i ∈ rationalLowSpace) :
      C.gate j ∈ rationalLowSpace := by
    have hwire := wireSpace_le_rationalLow_of_prefix C hprev
    rw [C.gate_eq j]
    exact rationalLow_mul_mem_of_mem_targetAmbient
      (hwire (C.left_mem j)) (hwire (C.right_mem j))
      (by simpa [C.gate_eq j] using hgateAmbient j)
  have h0 : C.gate 0 ∈ rationalLowSpace :=
    nextGate 0 (by intro i hi; omega)
  have h1 : C.gate 1 ∈ rationalLowSpace :=
    nextGate 1 (by intro i hi; fin_cases i <;> simp_all)
  have h2 : C.gate 2 ∈ rationalLowSpace :=
    nextGate 2 (by intro i hi; fin_cases i <;> simp_all)
  have h3 : C.gate 3 ∈ rationalLowSpace :=
    nextGate 3 (by intro i hi; fin_cases i <;> simp_all)
  have h4 : C.gate 4 ∈ rationalLowSpace :=
    nextGate 4 (by intro i hi; fin_cases i <;> simp_all)
  have h5 : C.gate 5 ∈ rationalLowSpace :=
    nextGate 5 (by intro i hi; fin_cases i <;> simp_all)
  have h6 : C.gate 6 ∈ rationalLowSpace :=
    nextGate 6 (by intro i hi; fin_cases i <;> simp_all)
  apply mul_one_not_mem_rationalLow
  have htarget : Mul 4 (1 : Fin 7) ∈ C.finalWire := hC 1
  have hfinalRat : C.finalWire ≤ rationalLowSpace := by
    rw [C.finalWire_eq]
    apply sup_le le_sup_left
    rw [Submodule.span_le]
    rintro p ⟨i, rfl⟩
    fin_cases i <;> assumption
  exact hfinalRat htarget

/-- The defect budget of eight gates is attained.  If it were zero, the same
rational-prefix trap used above would contain the entire target space. -/
theorem eight_gate_defect_is_one_algebraic
    (C : Circuit 8 8) (hC : C.Computes (Mul 4)) :
    flagDefectRank C.finalWire (mulTarget 4) = 1 := by
  have hle := eight_gate_defect_le_one C hC
  have hne : flagDefectRank C.finalWire (mulTarget 4) ≠ 0 := by
    intro hzero
    have hfinalLe : C.finalWire ≤ targetAmbient 8 (mulTarget 4) :=
      finalWire_le_targetAmbient_of_defect_zero C hzero
    have hgateAmbient (i : Fin 8) :
        C.gate i ∈ targetAmbient 8 (mulTarget 4) :=
      hfinalLe (gate_mem_finalWire C i)
    have nextGate (j : Fin 8)
        (hprev : ∀ i : Fin 8, i.val < j.val →
          C.gate i ∈ rationalLowSpace) :
        C.gate j ∈ rationalLowSpace := by
      have hwire := wireSpace_le_rationalLow_of_prefix C hprev
      rw [C.gate_eq j]
      exact rationalLow_mul_mem_of_mem_targetAmbient
        (hwire (C.left_mem j)) (hwire (C.right_mem j))
        (by simpa [C.gate_eq j] using hgateAmbient j)
    have h0 : C.gate 0 ∈ rationalLowSpace :=
      nextGate 0 (by intro i hi; omega)
    have h1 : C.gate 1 ∈ rationalLowSpace :=
      nextGate 1 (by intro i hi; fin_cases i <;> simp_all)
    have h2 : C.gate 2 ∈ rationalLowSpace :=
      nextGate 2 (by intro i hi; fin_cases i <;> simp_all)
    have h3 : C.gate 3 ∈ rationalLowSpace :=
      nextGate 3 (by intro i hi; fin_cases i <;> simp_all)
    have h4 : C.gate 4 ∈ rationalLowSpace :=
      nextGate 4 (by intro i hi; fin_cases i <;> simp_all)
    have h5 : C.gate 5 ∈ rationalLowSpace :=
      nextGate 5 (by intro i hi; fin_cases i <;> simp_all)
    have h6 : C.gate 6 ∈ rationalLowSpace :=
      nextGate 6 (by intro i hi; fin_cases i <;> simp_all)
    have h7 : C.gate 7 ∈ rationalLowSpace :=
      nextGate 7 (by intro i hi; fin_cases i <;> simp_all)
    apply mul_one_not_mem_rationalLow
    have hfinalRat : C.finalWire ≤ rationalLowSpace := by
      rw [C.finalWire_eq]
      apply sup_le le_sup_left
      rw [Submodule.span_le]
      rintro p ⟨i, rfl⟩
      fin_cases i <;> assumption
    exact hfinalRat (hC 1)
  omega

/-- Attaining target rank seven and defect one forces every one of the eight
gate outputs to be a genuinely new wire-space direction. -/
theorem eight_gate_all_nonredundant
    (C : Circuit 8 8) (hC : C.Computes (Mul 4)) :
    ∀ i : Fin 8, NonredundantAt C i := by
  have hdef := eight_gate_defect_is_one_algebraic C hC
  have ht := final_target_rank_four C hC
  have hledger := flag_rank_ledger (V := C.finalWire) (T := mulTarget 4)
    (by simpa [Circuit.finalWire] using
      affine_le_wireSpace C.gate (j := 8))
  have hfinalDim : Module.finrank F₂ C.finalWire = 17 := by
    rw [affine_eight_finrank, ht, hdef] at hledger
    have ha : 9 ≤ Module.finrank F₂ C.finalWire := by
      simpa [affine_eight_finrank] using
        Submodule.finrank_mono
          (show affine 8 ≤ C.finalWire by
            simpa [Circuit.finalWire] using
              affine_le_wireSpace C.gate (j := 8))
    omega
  intro i hred
  let Other := {k : Fin 8 // k ≠ i}
  let otherGate : Other → ANF 8 := fun k => C.gate k.1
  let otherOutputs : Finset (ANF 8) := Finset.univ.image otherGate
  let W : Submodule F₂ (ANF 8) :=
    affine 8 ⊔ Submodule.span F₂ (↑otherOutputs : Set (ANF 8))
  have hgateW (k : Fin 8) : C.gate k ∈ W := by
    by_cases hki : k = i
    · subst k
      have hprefix :
          prefixGates C.gate i.val ⊆ (↑otherOutputs : Set (ANF 8)) := by
        rintro p ⟨k, hk, rfl⟩
        simp only [otherOutputs, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨k, ne_of_lt hk⟩, rfl⟩
      have hred' : C.gate i ∈
          affine 8 ⊔ Submodule.span F₂ (prefixGates C.gate i.val) := by
        simpa [NonredundantAt, circuitFlag, wireSpace] using hred
      have hincl :
          affine 8 ⊔ Submodule.span F₂ (prefixGates C.gate i.val) ≤
            affine 8 ⊔
              Submodule.span F₂ (↑otherOutputs : Set (ANF 8)) := by
        apply sup_le
        · exact le_sup_left
        · exact (Submodule.span_mono hprefix).trans le_sup_right
      exact hincl hred'
    · apply Submodule.mem_sup_right
      apply Submodule.subset_span
      simp only [otherOutputs, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨k, hki⟩, rfl⟩
  have hfinalLe : C.finalWire ≤ W := by
    rw [C.finalWire_eq]
    exact sup_le le_sup_left (by
      rw [Submodule.span_le]
      rintro p ⟨k, rfl⟩
      exact hgateW k)
  have hspan :
      Module.finrank F₂
        (Submodule.span F₂ (↑otherOutputs : Set (ANF 8))) ≤ 7 := by
    have hrange :
        Module.finrank F₂
            (Submodule.span F₂ (↑otherOutputs : Set (ANF 8))) ≤
          otherOutputs.card := by
      simpa using finrank_span_le_card (R := F₂)
        (↑otherOutputs : Set (ANF 8))
    have hcard : otherOutputs.card ≤ 7 := by
      have hc : (Finset.univ.image otherGate).card ≤
          (Finset.univ : Finset Other).card := Finset.card_image_le
      have hOther : Fintype.card Other = 7 := by
        simp [Other]
      simpa [otherOutputs, hOther] using hc
    exact hrange.trans hcard
  have hWdim : Module.finrank F₂ W ≤ 16 := by
    have hsup := Submodule.finrank_add_le_finrank_add_finrank
      (affine 8)
        (Submodule.span F₂ (↑otherOutputs : Set (ANF 8)))
    dsimp [W]
    rw [affine_eight_finrank] at hsup
    exact hsup.trans (by omega)
  have := (Submodule.finrank_mono hfinalLe).trans hWdim
  rw [hfinalDim] at this
  omega

end

end N4
end UnrestrictedBooleanMul
