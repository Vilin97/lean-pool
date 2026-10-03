/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SevenGate

/-!
# Semantic circuit rewiring

The circuit model stores wires as ANFs and records availability by membership
in a wire space.  Consequently a basis replacement at one gate can leave all
later factor ANFs unchanged: only their membership proofs have to be
transported across the equality of wire spaces.  This file implements that
transport as an actual `Circuit`, rather than only as a flag-level statement.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Replace one gate output in a circuit output sequence. -/
def updateGate {m r : Nat} (C : Circuit m r) (j : Fin r) (t : ANF m) :
    Fin r → ANF m := Function.update C.gate j t

theorem wireSpace_updateGate_eq_of_le {m r : Nat}
    (C : Circuit m r) (j : Fin r) (t : ANF m) (k : Nat) (hk : k ≤ j.val) :
    wireSpace (updateGate C j t) k = wireSpace C.gate k := by
  unfold wireSpace
  congr 1
  apply congrArg (Submodule.span F₂)
  ext p
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hij : i ≠ j := by
      intro hij
      subst i
      omega
    exact ⟨i, hi, by simp [updateGate, hij]⟩
  · rintro ⟨i, hi, rfl⟩
    have hij : i ≠ j := by
      intro hij
      subst i
      omega
    exact ⟨i, hi, by simp [updateGate, hij]⟩

theorem wireSpace_updateGate_eq_of_lt {m r : Nat}
    (C : Circuit m r) (j : Fin r) (t : ANF m)
    (hstate : wireSpace C.gate (j.val + 1) =
      wireSpace C.gate j.val ⊔ Submodule.span F₂ {t})
    (k : Nat) (hjk : j.val < k) (hkr : k ≤ r) :
    wireSpace (updateGate C j t) k = wireSpace C.gate k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      by_cases hnj : n = j.val
      · subst n
        rw [wireSpace_succ (updateGate C j t) j.isLt,
          wireSpace_updateGate_eq_of_le C j t j.val (by rfl)]
        have hjeta : (⟨j.val, j.isLt⟩ : Fin r) = j := Fin.ext rfl
        rw [show updateGate C j t ⟨j.val, j.isLt⟩ = t by
          simp [updateGate, hjeta]]
        exact hstate.symm
      · have hjn : j.val < n := by omega
        have hnr : n < r := by omega
        have hprev := ih n (by omega) hjn (by omega)
        rw [wireSpace_succ (updateGate C j t) hnr,
          wireSpace_succ C.gate hnr, hprev]
        have hidx : (⟨n, hnr⟩ : Fin r) ≠ j := by
          intro h
          apply hnj
          exact congrArg Fin.val h
        rw [show updateGate C j t ⟨n, hnr⟩ = C.gate ⟨n, hnr⟩ by
          simp [updateGate, hidx]]

/-- Replace a first-entry gate by a direct affine product while preserving all
later gate functions and the final wire space. -/
def replaceFirstEntryCircuit {m r : Nat} (C : Circuit m r)
    (j : Fin r) (u v t : ANF m)
    (hu : u ∈ affine m) (hv : v ∈ affine m) (ht : t = u * v)
    (hstate : wireSpace C.gate (j.val + 1) =
      wireSpace C.gate j.val ⊔ Submodule.span F₂ {t}) : Circuit m r where
  gate := updateGate C j t
  left := Function.update C.left j u
  right := Function.update C.right j v
  left_mem i := by
    by_cases hij : i = j
    · subst i
      simp only [Function.update_self]
      exact affine_le_wireSpace _ hu
    · rw [Function.update_of_ne hij]
      by_cases hijlt : i.val < j.val
      · rw [wireSpace_updateGate_eq_of_le C j t i.val (by omega)]
        exact C.left_mem i
      · rw [wireSpace_updateGate_eq_of_lt C j t hstate i.val
          (by
            have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
            omega)
          (Nat.le_of_lt i.isLt)]
        exact C.left_mem i
  right_mem i := by
    by_cases hij : i = j
    · subst i
      simp only [Function.update_self]
      exact affine_le_wireSpace _ hv
    · rw [Function.update_of_ne hij]
      by_cases hijlt : i.val < j.val
      · rw [wireSpace_updateGate_eq_of_le C j t i.val (by omega)]
        exact C.right_mem i
      · rw [wireSpace_updateGate_eq_of_lt C j t hstate i.val
          (by
            have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
            omega)
          (Nat.le_of_lt i.isLt)]
        exact C.right_mem i
  gate_eq i := by
    by_cases hij : i = j
    · subst i
      simp [updateGate, ht]
    · simp [updateGate, hij, C.gate_eq i]

theorem replaceFirstEntryCircuit_finalWire {m r : Nat} (C : Circuit m r)
    (j : Fin r) (u v t : ANF m)
    (hu : u ∈ affine m) (hv : v ∈ affine m) (ht : t = u * v)
    (hstate : wireSpace C.gate (j.val + 1) =
      wireSpace C.gate j.val ⊔ Submodule.span F₂ {t}) :
    (replaceFirstEntryCircuit C j u v t hu hv ht hstate).finalWire = C.finalWire := by
  exact wireSpace_updateGate_eq_of_lt C j t hstate r j.isLt (by rfl)

theorem replaceFirstEntryCircuit_computes {m r o : Nat}
    (C : Circuit m r) (target : Fin o → ANF m)
    (j : Fin r) (u v t : ANF m)
    (hu : u ∈ affine m) (hv : v ∈ affine m) (ht : t = u * v)
    (hstate : wireSpace C.gate (j.val + 1) =
      wireSpace C.gate j.val ⊔ Submodule.span F₂ {t})
    (hC : C.Computes target) :
    (replaceFirstEntryCircuit C j u v t hu hv ht hstate).Computes target := by
  intro i
  rw [replaceFirstEntryCircuit_finalWire C j u v t hu hv ht hstate]
  exact hC i

/-- Exchange two entries of a finite sequence. -/
def swapAdjacentFun {r : Nat} {X : Type*} (f : Fin r → X)
    (a b : Fin r) : Fin r → X := fun i =>
  if i = a then f b else if i = b then f a else f i

theorem wireSpace_swapAdjacent_eq_of_le {m r : Nat}
    (C : Circuit m r) (a b : Fin r) (hab : a.val + 1 = b.val)
    (k : Nat) (hk : k ≤ a.val) :
    wireSpace (swapAdjacentFun C.gate a b) k = wireSpace C.gate k := by
  unfold wireSpace
  congr 1
  apply congrArg (Submodule.span F₂)
  ext p
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hia : i ≠ a := by
      intro h
      subst i
      omega
    have hib : i ≠ b := by
      intro h
      subst i
      omega
    exact ⟨i, hi, by simp [swapAdjacentFun, hia, hib]⟩
  · rintro ⟨i, hi, rfl⟩
    have hia : i ≠ a := by
      intro h
      subst i
      omega
    have hib : i ≠ b := by
      intro h
      subst i
      omega
    exact ⟨i, hi, by simp [swapAdjacentFun, hia, hib]⟩

theorem wireSpace_swapAdjacent_at_right {m r : Nat}
    (C : Circuit m r) (a b : Fin r) (hab : a.val + 1 = b.val) :
    wireSpace (swapAdjacentFun C.gate a b) b.val =
      wireSpace C.gate a.val ⊔ Submodule.span F₂ {C.gate b} := by
  have habne : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    omega
  rw [← hab, wireSpace_succ (swapAdjacentFun C.gate a b) a.isLt,
    wireSpace_swapAdjacent_eq_of_le C a b hab a.val (by rfl)]
  congr 2
  simp [swapAdjacentFun]

theorem wireSpace_swapAdjacent_after_pair {m r : Nat}
    (C : Circuit m r) (a b : Fin r) (hab : a.val + 1 = b.val) :
    wireSpace (swapAdjacentFun C.gate a b) (b.val + 1) =
      wireSpace C.gate (b.val + 1) := by
  have habne : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    omega
  rw [wireSpace_succ (swapAdjacentFun C.gate a b) b.isLt,
    wireSpace_swapAdjacent_at_right C a b hab,
    wireSpace_succ C.gate b.isLt]
  have hbprev : wireSpace C.gate b.val =
      wireSpace C.gate a.val ⊔ Submodule.span F₂ {C.gate a} := by
    rw [← hab, wireSpace_succ C.gate a.isLt]
  rw [hbprev]
  have hba : b ≠ a := habne.symm
  rw [show swapAdjacentFun C.gate a b b = C.gate a by
    simp [swapAdjacentFun, hba]]
  ac_rfl

theorem wireSpace_swapAdjacent_eq_of_right_lt {m r : Nat}
    (C : Circuit m r) (a b : Fin r) (hab : a.val + 1 = b.val)
    (k : Nat) (hbk : b.val < k) (hkr : k ≤ r) :
    wireSpace (swapAdjacentFun C.gate a b) k = wireSpace C.gate k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      by_cases hnb : n = b.val
      · subst n
        exact wireSpace_swapAdjacent_after_pair C a b hab
      · have hbn : b.val < n := by omega
        have hnr : n < r := by omega
        have hprev := ih n (by omega) hbn (by omega)
        rw [wireSpace_succ (swapAdjacentFun C.gate a b) hnr,
          wireSpace_succ C.gate hnr, hprev]
        let ni : Fin r := ⟨n, hnr⟩
        have hnia : ni ≠ a := by
          intro h
          have := congrArg Fin.val h
          dsimp [ni] at this
          omega
        have hnib : ni ≠ b := by
          intro h
          apply hnb
          exact congrArg Fin.val h
        rw [show swapAdjacentFun C.gate a b ni = C.gate ni by
          simp [swapAdjacentFun, hnia, hnib]]

/-- Commute a gate whose two factors are affine one position toward the
front.  No earlier gate can depend on it, and after the pair the wire space is
unchanged. -/
def swapAdjacentDirectCircuit {m r : Nat} (C : Circuit m r)
    (a b : Fin r) (hab : a.val + 1 = b.val)
    (hleft : C.left b ∈ affine m) (hright : C.right b ∈ affine m) :
    Circuit m r where
  gate := swapAdjacentFun C.gate a b
  left := swapAdjacentFun C.left a b
  right := swapAdjacentFun C.right a b
  left_mem i := by
    have habne : a ≠ b := by
      intro h
      have := congrArg Fin.val h
      omega
    by_cases hia : i = a
    · subst i
      simp only [swapAdjacentFun, ↓reduceIte]
      exact affine_le_wireSpace _ hleft
    by_cases hib : i = b
    · subst i
      have hba : b ≠ a := habne.symm
      simp only [swapAdjacentFun, ite_eq_right hba]
      rw [wireSpace_swapAdjacent_at_right C a b hab]
      exact Submodule.mem_sup_left (C.left_mem a)
    · simp only [swapAdjacentFun, ite_eq_right hia, ite_eq_right hib]
      by_cases hlt : i.val < a.val
      · rw [wireSpace_swapAdjacent_eq_of_le C a b hab i.val (by omega)]
        exact C.left_mem i
      · rw [wireSpace_swapAdjacent_eq_of_right_lt C a b hab i.val
          (by
            have hiva : i.val ≠ a.val := fun h => hia (Fin.ext h)
            have hivb : i.val ≠ b.val := fun h => hib (Fin.ext h)
            omega)
          (Nat.le_of_lt i.isLt)]
        exact C.left_mem i
  right_mem i := by
    have habne : a ≠ b := by
      intro h
      have := congrArg Fin.val h
      omega
    by_cases hia : i = a
    · subst i
      simp only [swapAdjacentFun, ↓reduceIte]
      exact affine_le_wireSpace _ hright
    by_cases hib : i = b
    · subst i
      have hba : b ≠ a := habne.symm
      simp only [swapAdjacentFun, ite_eq_right hba]
      rw [wireSpace_swapAdjacent_at_right C a b hab]
      exact Submodule.mem_sup_left (C.right_mem a)
    · simp only [swapAdjacentFun, ite_eq_right hia, ite_eq_right hib]
      by_cases hlt : i.val < a.val
      · rw [wireSpace_swapAdjacent_eq_of_le C a b hab i.val (by omega)]
        exact C.right_mem i
      · rw [wireSpace_swapAdjacent_eq_of_right_lt C a b hab i.val
          (by
            have hiva : i.val ≠ a.val := fun h => hia (Fin.ext h)
            have hivb : i.val ≠ b.val := fun h => hib (Fin.ext h)
            omega)
          (Nat.le_of_lt i.isLt)]
        exact C.right_mem i
  gate_eq i := by
    by_cases hia : i = a
    · subst i
      have habne : a ≠ b := by
        intro h
        have := congrArg Fin.val h
        omega
      simp [swapAdjacentFun, C.gate_eq b]
    by_cases hib : i = b
    · subst i
      have hba : b ≠ a := by
        intro h
        have := congrArg Fin.val h
        omega
      simp [swapAdjacentFun, hba, C.gate_eq a]
    · simp [swapAdjacentFun, hia, hib, C.gate_eq i]

theorem swapAdjacentDirectCircuit_finalWire {m r : Nat} (C : Circuit m r)
    (a b : Fin r) (hab : a.val + 1 = b.val)
    (hleft : C.left b ∈ affine m) (hright : C.right b ∈ affine m) :
    (swapAdjacentDirectCircuit C a b hab hleft hright).finalWire = C.finalWire := by
  exact wireSpace_swapAdjacent_eq_of_right_lt C a b hab r b.isLt (by rfl)

theorem swapAdjacentDirectCircuit_computes {m r o : Nat}
    (C : Circuit m r) (target : Fin o → ANF m)
    (a b : Fin r) (hab : a.val + 1 = b.val)
    (hleft : C.left b ∈ affine m) (hright : C.right b ∈ affine m)
    (hC : C.Computes target) :
    (swapAdjacentDirectCircuit C a b hab hleft hright).Computes target := by
  intro i
  rw [swapAdjacentDirectCircuit_finalWire C a b hab hleft hright]
  exact hC i

/-- A non-affine final wire has a first gate at which it enters the flag. -/
theorem exists_first_entry_gate {m r : Nat} (C : Circuit m r) (t : ANF m)
    (hfinal : t ∈ C.finalWire) (hnotAffine : t ∉ affine m) :
    ∃ j : Fin r,
      t ∈ circuitFlag C (j.val + 1) ∧ t ∉ circuitFlag C j.val := by
  classical
  let P : Nat → Prop := fun n => t ∈ wireSpace C.gate n
  have hPr : P r := by simpa [P, Circuit.finalWire] using hfinal
  have hex : ∃ n, P n := ⟨r, hPr⟩
  let n := Nat.find hex
  have hnmem : P n := Nat.find_spec hex
  have hnle : n ≤ r := Nat.find_min' hex hPr
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    apply hnotAffine
    simpa [P, hn0] using hnmem
  let j : Fin r := ⟨n - 1, by omega⟩
  refine ⟨j, ?_, ?_⟩
  · have hj : j.val + 1 = n := by dsimp [j]; omega
    simpa [circuitFlag, hj, P] using hnmem
  · have hlt : n - 1 < n := by omega
    have hmin := Nat.find_min hex hlt
    simpa [circuitFlag, j, P] using hmin

theorem linearANF_mem_affine (ell : LinearForm) :
    linearANF ell ∈ affine 8 := by
  simpa [affineANF] using affineANF_mem 0 ell

theorem rationalPlaceANF_direct (theta : Fin 3) :
    targetANF (rationalPlaceCoeff theta) =
      linearANF (placeA theta) * linearANF (placeB theta) := by
  fin_cases theta <;>
    simp (disch := decide)
      [targetANF_eq_double_sum, linearANF, rationalPlaceCoeff,
        rZeroCoeff, rOneCoeff, rInfinityCoeff, placeA, placeB,
        hankelIndex, targetPair, aCoord, bCoord, Fin.sum_univ_succ,
        X, monomial_mul, mul_add, add_mul];
    module

theorem rationalPlaceANF_not_mem_affine (theta : Fin 3) :
    targetANF (rationalPlaceCoeff theta) ∉ affine 8 := by
  intro h
  have hz := anfTwoProjection_kills_affine h
  change anfTwoProjection (targetANF (rationalPlaceCoeff theta)) = 0 at hz
  rw [anfTwoProjection_targetANF, targetTwo_rationalPlaceCoeff] at hz
  exact rationalPlaceTwo_ne_zero theta hz

theorem rationalPlaceANF_mem_finalWire (C : Circuit 8 8)
    (hC : C.Computes (Mul 4)) (theta : Fin 3) :
    targetANF (rationalPlaceCoeff theta) ∈ C.finalWire := by
  exact targetAmbient_le_finalWire C hC
    (Submodule.mem_sup_right (targetANF_mem_mulTarget _))

/-- Move a direct affine-product gate left to any earlier position by adjacent
legal commutations.  Gates strictly before the destination are untouched. -/
theorem exists_move_direct_gate_left {m r : Nat}
    (C : Circuit m r) (p j : Fin r) (hpj : p.val ≤ j.val)
    (t : ANF m) (hgate : C.gate j = t)
    (hleft : C.left j ∈ affine m) (hright : C.right j ∈ affine m) :
    ∃ D : Circuit m r,
      D.finalWire = C.finalWire ∧
      D.gate p = t ∧
      D.left p ∈ affine m ∧
      D.right p ∈ affine m ∧
      (∀ k : Fin r, k.val < p.val → D.gate k = C.gate k) := by
  generalize hd : j.val - p.val = d
  induction d using Nat.strong_induction_on generalizing C j with
  | h d ih =>
      by_cases hpjeq : p = j
      · subst j
        exact ⟨C, rfl, hgate, hleft, hright, by intros; rfl⟩
      · have hpjlt : p.val < j.val := by
          have hvals : p.val ≠ j.val := fun h => hpjeq (Fin.ext h)
          omega
        let a : Fin r := ⟨j.val - 1, by omega⟩
        have haj : a.val + 1 = j.val := by dsimp [a]; omega
        let C' := swapAdjacentDirectCircuit C a j haj hleft hright
        have hpa : p.val ≤ a.val := by dsimp [a]; omega
        have hdist : a.val - p.val < d := by dsimp [a]; omega
        have hC'gate : C'.gate a = t := by
          dsimp [C', swapAdjacentDirectCircuit]
          simp [swapAdjacentFun, hgate]
        have hC'left : C'.left a ∈ affine m := by
          dsimp [C', swapAdjacentDirectCircuit]
          simpa [swapAdjacentFun] using hleft
        have hC'right : C'.right a ∈ affine m := by
          dsimp [C', swapAdjacentDirectCircuit]
          simpa [swapAdjacentFun] using hright
        have hda : a.val - p.val = a.val - p.val := rfl
        rcases ih (a.val - p.val) hdist C' a hpa hC'gate
            hC'left hC'right hda with
          ⟨D, hDfinal, hDgate, hDleft, hDright, hDbefore⟩
        refine ⟨D, ?_, hDgate, hDleft, hDright, ?_⟩
        · exact hDfinal.trans
            (swapAdjacentDirectCircuit_finalWire C a j haj hleft hright)
        · intro k hk
          rw [hDbefore k hk]
          dsimp [C', swapAdjacentDirectCircuit]
          have hka : k ≠ a := by
            intro h
            subst k
            dsimp [a] at hk
            omega
          have hkj : k ≠ j := by
            intro h
            subst k
            omega
          simp [swapAdjacentFun, hka, hkj]

/-- Promote a rational target direction which is absent from a chosen prefix
to a direct affine-product gate at the end of that prefix.  The transformation
preserves the final wire space and every earlier gate. -/
theorem exists_promote_rational_place (C : Circuit 8 8)
    (hC : C.Computes (Mul 4)) (p : Fin 8) (theta : Fin 3)
    (hmissing : targetANF (rationalPlaceCoeff theta) ∉ circuitFlag C p.val) :
    ∃ D : Circuit 8 8,
      D.Computes (Mul 4) ∧
      D.finalWire = C.finalWire ∧
      D.gate p = targetANF (rationalPlaceCoeff theta) ∧
      D.left p ∈ affine 8 ∧
      D.right p ∈ affine 8 ∧
      (∀ k : Fin 8, k.val < p.val → D.gate k = C.gate k) := by
  let t := targetANF (rationalPlaceCoeff theta)
  let u := linearANF (placeA theta)
  let v := linearANF (placeB theta)
  have htfinal : t ∈ C.finalWire :=
    rationalPlaceANF_mem_finalWire C hC theta
  have htnaff : t ∉ affine 8 :=
    rationalPlaceANF_not_mem_affine theta
  rcases exists_first_entry_gate C t htfinal htnaff with
    ⟨j, htj, htfirst⟩
  have hpj : p.val ≤ j.val := by
    by_contra h
    have hjp : j.val + 1 ≤ p.val := by omega
    apply hmissing
    exact wireSpace_mono (g := C.gate) hjp htj
  have hu : u ∈ affine 8 := linearANF_mem_affine _
  have hv : v ∈ affine 8 := linearANF_mem_affine _
  have htprod : t = u * v := rationalPlaceANF_direct theta
  have hstate : wireSpace C.gate (j.val + 1) =
      wireSpace C.gate j.val ⊔ Submodule.span F₂ {t} :=
    circuit_first_entry_replacement C j t htj htfirst
  let C₁ := replaceFirstEntryCircuit C j u v t hu hv htprod hstate
  have hC₁gate : C₁.gate j = t := by
    simp [C₁, replaceFirstEntryCircuit, updateGate]
  have hC₁left : C₁.left j ∈ affine 8 := by
    simpa [C₁, replaceFirstEntryCircuit] using hu
  have hC₁right : C₁.right j ∈ affine 8 := by
    simpa [C₁, replaceFirstEntryCircuit] using hv
  rcases exists_move_direct_gate_left C₁ p j hpj t hC₁gate hC₁left hC₁right with
    ⟨D, hDfinal₁, hDgate, hDleft, hDright, hDbefore₁⟩
  have hC₁final : C₁.finalWire = C.finalWire :=
    replaceFirstEntryCircuit_finalWire C j u v t hu hv htprod hstate
  have hDfinal : D.finalWire = C.finalWire := hDfinal₁.trans hC₁final
  refine ⟨D, ?_, hDfinal, hDgate, hDleft, hDright, ?_⟩
  · intro i
    rw [hDfinal]
    exact hC i
  · intro k hk
    rw [hDbefore₁ k hk]
    dsimp [C₁, replaceFirstEntryCircuit]
    have hkj : k ≠ j := by
      intro h
      subst k
      omega
    simp [updateGate, hkj]

end

end N4
end UnrestrictedBooleanMul
