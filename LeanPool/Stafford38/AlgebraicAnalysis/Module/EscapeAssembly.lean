/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.EscapeSpan

/-!
# Finite-tuple central-coordinate escape

This is the finite-dimensional algebraic part of packet 7.  A tuple of
coefficient-left PBW terms with strictly decreasing active degrees is assumed
to lie in a right `S`-submodule.  If the submodule is also closed under left
multiplication by the central coordinate, the commutator iterates isolate
one coordinate at a time.  `Escape.ad_unit_production` supplies the unit at
the selected coordinate, and the right-module lemma in `EscapeSpan` then
gives the whole free module.

The theorem deliberately stops at this local span result.  It does not claim
that a global Stafford correction family supplies the hypotheses.
-/

namespace AlgebraicAnalysis.EscapeAssembly

open AlgebraicAnalysis.Escape
open AlgebraicAnalysis.EscapeSpan

noncomputable section

open scoped BigOperators
open Polynomial

variable {E S : Type*} [DivisionRing E] [CharZero E] [Ring S]
variable {n : ℕ}

lemma iterate_commutatorVector_mem
    (H : Submodule Sᵐᵒᵖ (Fin n → S)) (x : S)
    (hleft : ∀ v : Fin n → S, v ∈ H → (fun i => x * v i) ∈ H)
    {v : Fin n → S} (hv : v ∈ H) (k : ℕ) :
    (commutatorVector x)^[k] v ∈ H := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact commutatorVector_mem H x hleft ih

/-- Coordinates whose index is below the current active degree. -/
def knownCoordinates (m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j.val < m)

/-- Remove the currently known coordinate contributions from a vector. -/
def residualVector (v : Fin n → S) (m : ℕ) : Fin n → S :=
  v - ∑ j ∈ knownCoordinates m, Pi.single j (v j)

lemma residualVector_apply_lt (v : Fin n → S) (m : ℕ)
    {j : Fin n} (hj : j.val < m) : residualVector v m j = 0 := by
  classical
  simp only [residualVector, Pi.sub_apply]
  have hmem : j ∈ knownCoordinates m := by simp [knownCoordinates, hj]
  have hsum :
      (∑ k ∈ knownCoordinates m,
        (Pi.single k (v k) : Fin n → S)) j = v j := by
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [Ne.symm hbj]
    · intro hjnot
      exact (hjnot hmem).elim
  rw [hsum, sub_self]

lemma residualVector_apply_not_lt (v : Fin n → S) (m : ℕ)
    {j : Fin n} (hj : ¬ j.val < m) : residualVector v m j = v j := by
  classical
  simp only [residualVector, Pi.sub_apply]
  have hsum :
      (∑ k ∈ knownCoordinates m,
        (Pi.single k (v k) : Fin n → S)) j = 0 := by
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k ≠ j := by
      intro hEq
      subst j
      exact hj (by simpa [knownCoordinates] using hk)
    simp [hkj]
  rw [hsum, sub_zero]

/--
The actual finite-tuple escape theorem.  The only analytic-looking input is
the PBW transport packaged by `CentralEscapeData`; all module operations are
right-sided through `Sᵐᵒᵖ`.
-/
theorem finite_tuple_escape
    (D : CentralEscapeData (E := E) (S := S))
    (p : Fin n → Polynomial E)
    (hp : ∀ i, p i ≠ 0)
    (hstrict : StrictAnti (fun i => (p i).natDegree))
    (H : Submodule Sᵐᵒᵖ (Fin n → S))
    (hv : (fun i => D.normal (p i)) ∈ H)
    (hleft : ∀ v : Fin n → S, v ∈ H →
      (fun i => D.embed D.coordinate * v i) ∈ H) :
    H = ⊤ := by
  let v : Fin n → S := fun i => D.normal (p i)
  have hv' : v ∈ H := hv
  have hpure : ∀ i : Fin n, ∃ u : S, IsUnit u ∧
      (Pi.single i u : Fin n → S) ∈ H := by
    have hprocess : ∀ m : ℕ, m ≤ n →
        ∀ j : Fin n, j.val < m → ∃ u : S, IsUnit u ∧
          (Pi.single j u : Fin n → S) ∈ H := by
      intro m hm
      induction m with
      | zero =>
          intro j hj
          omega
      | succ m ih =>
          have hm' : m < n := by omega
          let i : Fin n := ⟨m, hm'⟩
          have hprior : ∀ j : Fin n, j.val < m → ∃ u : S, IsUnit u ∧
              (Pi.single j u : Fin n → S) ∈ H := by
            intro j hj
            exact ih (by omega) j hj
          have hsum :
              (∑ j ∈ knownCoordinates m, (Pi.single j (v j) : Fin n → S)) ∈ H := by
            apply H.sum_mem
            intro j hj
            have hjlt : j.val < m := by
              simpa [knownCoordinates] using hj
            obtain ⟨u, hu, huH⟩ := hprior j hjlt
            exact single_mem_of_unit_single_mem H j hu huH (v j)
          have hres : residualVector v m ∈ H :=
            H.sub_mem hv' hsum
          have hzmem :
              (commutatorVector (D.embed D.coordinate))^[((p i).natDegree)]
                  (residualVector v m) ∈ H :=
            iterate_commutatorVector_mem H (D.embed D.coordinate) hleft hres _
          let z : Fin n → S :=
            (commutatorVector (D.embed D.coordinate))^[((p i).natDegree)]
              (residualVector v m)
          have hzi : IsUnit (z i) := by
            dsimp [z]
            rw [commutatorVector_iterate_apply]
            rw [residualVector_apply_not_lt]
            · simpa [v] using D.ad_unit_production (hp i)
            · exact Nat.not_lt_of_ge (Nat.le_refl m)
          have hzj : ∀ j : Fin n, j ≠ i → z j = 0 := by
            intro j hji
            by_cases hjlt : j.val < m
            · dsimp [z]
              rw [commutatorVector_iterate_apply,
                residualVector_apply_lt v m hjlt]
              simp
            · have hjval : j.val ≠ m := by
                intro hEq
                apply hji
                apply Fin.ext
                exact hEq
              have hmj : m < j.val := by omega
              have hij : i < j := by
                exact Fin.mk_lt_mk.mpr hmj
              have hdeg : (p j).natDegree < (p i).natDegree :=
                hstrict hij
              have hzero :
                  (derivative^[((p i).natDegree)]) (p j) = 0 :=
                iterate_derivative_eq_zero hdeg
              dsimp [z]
              rw [commutatorVector_iterate_apply,
                residualVector_apply_not_lt v m hjlt]
              rw [D.iterate_commutator_normal, hzero]
              simp
          have hzpure : z = Pi.single i (z i) := by
            funext j
            by_cases hji : i = j
            · subst j
              simp
            · rw [hzj j (Ne.symm hji)]
              simp [hji]
          have hpure_i : (Pi.single i (z i) : Fin n → S) ∈ H := by
            rw [← hzpure]
            exact hzmem
          intro j hj
          by_cases hEq : j.val = m
          · have hji : j = i := by
              apply Fin.ext
              exact hEq
            subst j
            exact ⟨z i, hzi, hpure_i⟩
          · have hjlt : j.val < m := by omega
            exact hprior j hjlt
    intro i
    have hi : i.val + 1 ≤ n := by exact i.isLt.succ_le
    exact hprocess (i.val + 1) hi i (by simp)
  exact top_of_unit_singletons H hpure


end
end AlgebraicAnalysis.EscapeAssembly
