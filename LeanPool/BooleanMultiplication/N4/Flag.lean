/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Hankel

/-!
# Circuit flags and the defect ledger

The definitions in this file isolate the two components of a circuit flag:
the target dimension and the complementary defect dimension.  The main
identity is the reusable form of the manuscript's ledger

`number of nonredundant gates = target rank + defect rank`.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The target ambient space `Aff + T`. -/
@[expose] def targetAmbient (m : Nat) (T : Submodule F₂ (ANF m)) : Submodule F₂ (ANF m) :=
  affine m ⊔ T

/-- Target dimension of a wire space, measured modulo affine functions. -/
@[expose] def flagTargetRank {m : Nat} (V T : Submodule F₂ (ANF m)) : Nat :=
  Module.finrank F₂ ↥(V ⊓ targetAmbient m T) - Module.finrank F₂ ↥(affine m)

/-- Defect dimension: directions in the wire space outside `Aff + T`. -/
@[expose] def flagDefectRank {m : Nat} (V T : Submodule F₂ (ANF m)) : Nat :=
  Module.finrank F₂ ↥V - Module.finrank F₂ ↥(V ⊓ targetAmbient m T)

/-- The wire-space flag associated with a semantic circuit. -/
@[expose] def circuitFlag {m r : Nat} (C : Circuit m r) (j : Nat) : Submodule F₂ (ANF m) :=
  wireSpace C.gate j

/-- A gate is nonredundant when its output is not already in the preceding
wire space.  Minimal circuits have this property at every gate. -/
@[expose] def NonredundantAt {m r : Nat} (C : Circuit m r) (j : Fin r) : Prop :=
  C.gate j ∉ circuitFlag C j.val

/-- A gate is useful when adjoining it raises the target rank. -/
@[expose] def UsefulAt {m r : Nat} (C : Circuit m r) (T : Submodule F₂ (ANF m))
    (j : Fin r) : Prop :=
  flagTargetRank (circuitFlag C (j.val + 1)) T =
    flagTargetRank (circuitFlag C j.val) T + 1

theorem prefixGates_mono {m r j k : Nat} {g : Fin r → ANF m} (hjk : j ≤ k) :
    prefixGates g j ⊆ prefixGates g k := by
  rintro p ⟨i, hi, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi hjk, rfl⟩

theorem wireSpace_mono {m r j k : Nat} {g : Fin r → ANF m} (hjk : j ≤ k) :
    wireSpace g j ≤ wireSpace g k := by
  apply sup_le le_sup_left
  exact le_sup_of_le_right (Submodule.span_mono (prefixGates_mono hjk))

@[simp] theorem prefixGates_zero {m r : Nat} (g : Fin r → ANF m) :
    prefixGates g 0 = ∅ := by
  ext p
  simp [prefixGates]

@[simp] theorem wireSpace_zero {m r : Nat} (g : Fin r → ANF m) :
    wireSpace g 0 = affine m := by
  simp [wireSpace]

theorem prefixGates_succ {m r j : Nat} (g : Fin r → ANF m) (hj : j < r) :
    prefixGates g (j + 1) = prefixGates g j ∪ {g ⟨j, hj⟩} := by
  ext p
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hij : i.val ≤ j := Nat.lt_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using hi)
    rcases lt_or_eq_of_le hij with hij | hij
    · exact Set.mem_union_left _ ⟨i, hij, rfl⟩
    · apply Set.mem_union_right
      simp only [Set.mem_singleton_iff]
      congr
      exact Fin.ext hij
  · intro hp
    rcases hp with hp | hp
    · rcases hp with ⟨i, hi, rfl⟩
      exact ⟨i, lt_trans hi (Nat.lt_succ_self j), rfl⟩
    · have hp : p = g ⟨j, hj⟩ := by simpa only [Set.mem_singleton_iff] using hp
      subst p
      exact ⟨⟨j, hj⟩, Nat.lt_succ_self j, rfl⟩

/-- Each step of the circuit flag adjoins exactly the span of the new gate
output (possibly redundantly). -/
theorem wireSpace_succ {m r j : Nat} (g : Fin r → ANF m) (hj : j < r) :
    wireSpace g (j + 1) =
      wireSpace g j ⊔ Submodule.span F₂ {g ⟨j, hj⟩} := by
  rw [wireSpace, prefixGates_succ g hj, Submodule.span_union]
  change affine m ⊔
      (Submodule.span F₂ (prefixGates g j) ⊔ Submodule.span F₂ {g ⟨j, hj⟩}) =
    (affine m ⊔ Submodule.span F₂ (prefixGates g j)) ⊔
      Submodule.span F₂ {g ⟨j, hj⟩}
  exact (sup_assoc _ _ _).symm

/-- Intersecting a one-vector extension with any fixed ambient subspace can
raise dimension by at most one.  This is the linear-algebra core of “one gate
buys at most one target dimension.” -/
theorem finrank_inf_extension_le_one {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A W : Submodule K V) (x : V) :
    Module.finrank K ↥((A ⊔ Submodule.span K {x}) ⊓ W) ≤
      Module.finrank K ↥(A ⊓ W) + 1 := by
  let B : Submodule K V := A ⊔ Submodule.span K {x}
  let I : Submodule K V := A ⊓ W
  let J : Submodule K V := B ⊓ W
  have hAB : A ≤ B := le_sup_left
  have hAJ : A ⊓ J = I := by
    apply le_antisymm
    · intro y hy
      exact ⟨hy.1, hy.2.2⟩
    · intro y hy
      exact ⟨hy.1, hAB hy.1, hy.2⟩
  have hsup : A ⊔ J ≤ B := sup_le hAB inf_le_left
  have hsupdim : Module.finrank K ↥(A ⊔ J) ≤ Module.finrank K ↥B :=
    Submodule.finrank_mono hsup
  have hBdim : Module.finrank K ↥B ≤ Module.finrank K ↥A + 1 := by
    by_cases hx : x ∈ A
    · have hspan : Submodule.span K {x} ≤ A :=
        Submodule.span_le.mpr (by simpa using hx)
      have hBA : B = A := sup_eq_left.mpr hspan
      rw [hBA]
      omega
    · rw [show B = A ⊔ Submodule.span K {x} by rfl,
        Submodule.finrank_sup_span_singleton hx]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq A J
  rw [hAJ] at hdim
  change Module.finrank K ↥J ≤ Module.finrank K ↥I + 1
  omega

theorem flagTargetRank_step_le_one {m r : Nat} (C : Circuit m r)
    (T : Submodule F₂ (ANF m)) (j : Fin r) :
    flagTargetRank (circuitFlag C (j.val + 1)) T ≤
      flagTargetRank (circuitFlag C j.val) T + 1 := by
  have hstep := finrank_inf_extension_le_one
    (circuitFlag C j.val) (targetAmbient m T) (C.gate j)
  have hstep' : Module.finrank F₂
        ↥(circuitFlag C (j.val + 1) ⊓ targetAmbient m T) ≤
      Module.finrank F₂ ↥(circuitFlag C j.val ⊓ targetAmbient m T) + 1 := by
    rw [circuitFlag, wireSpace_succ C.gate j.isLt]
    have hjeta : (⟨j.val, j.isLt⟩ : Fin r) = j := Fin.ext rfl
    rw [hjeta]
    change Module.finrank F₂
        ↥((wireSpace C.gate j.val ⊔ Submodule.span F₂ {C.gate j}) ⊓
          targetAmbient m T) ≤
      Module.finrank F₂ ↥(wireSpace C.gate j.val ⊓ targetAmbient m T) + 1 at hstep
    exact hstep
  have ha0 : Module.finrank F₂ ↥(affine m) ≤
      Module.finrank F₂ ↥(circuitFlag C j.val ⊓ targetAmbient m T) := by
    apply Submodule.finrank_mono
    exact fun p hp => ⟨affine_le_wireSpace C.gate hp,
      Submodule.mem_sup_left hp⟩
  have ha1 : Module.finrank F₂ ↥(affine m) ≤
      Module.finrank F₂ ↥(circuitFlag C (j.val + 1) ⊓ targetAmbient m T) := by
    apply Submodule.finrank_mono
    exact fun p hp => ⟨affine_le_wireSpace C.gate hp,
      Submodule.mem_sup_left hp⟩
  unfold flagTargetRank
  omega

/-- The exact short-exact-sequence ledger for any wire space containing the
affine inputs. -/
theorem flag_rank_ledger {m : Nat} {V T : Submodule F₂ (ANF m)}
    (hAff : affine m ≤ V) :
    Module.finrank F₂ ↥V - Module.finrank F₂ ↥(affine m) =
      flagTargetRank V T + flagDefectRank V T := by
  have hAI : affine m ≤ V ⊓ targetAmbient m T :=
    fun p hp => ⟨hAff hp, Submodule.mem_sup_left hp⟩
  have hIV : V ⊓ targetAmbient m T ≤ V := inf_le_left
  have hdAI := Submodule.finrank_mono hAI
  have hdIV := Submodule.finrank_mono hIV
  unfold flagTargetRank flagDefectRank
  omega

/-- A nonredundant prefix of `j` AND gates has quotient dimension exactly
`j` modulo affine functions. -/
theorem circuitFlag_finrank {m r j : Nat} (C : Circuit m r) (hj : j ≤ r)
    (hnr : ∀ i : Fin r, i.val < j → NonredundantAt C i) :
    Module.finrank F₂ ↥(circuitFlag C j) =
      Module.finrank F₂ ↥(affine m) + j := by
  induction j with
  | zero => rw [circuitFlag, wireSpace_zero, add_zero]
  | succ j ih =>
      have hjr : j < r := Nat.lt_of_succ_le hj
      have hprefix : ∀ i : Fin r, i.val < j → NonredundantAt C i := by
        intro i hi
        exact hnr i (lt_trans hi (Nat.lt_succ_self j))
      have hih := ih (Nat.le_of_lt hjr) hprefix
      change Module.finrank F₂ ↥(wireSpace C.gate (j + 1)) =
        Module.finrank F₂ ↥(affine m) + (j + 1)
      rw [wireSpace_succ C.gate hjr,
        Submodule.finrank_sup_span_singleton]
      · change Module.finrank F₂ ↥(wireSpace C.gate j) =
          Module.finrank F₂ ↥(affine m) + j at hih
        rw [hih]
        omega
      · simpa [NonredundantAt, circuitFlag] using
          hnr ⟨j, hjr⟩ (Nat.lt_succ_self j)

/-- The manuscript identity `j = t(V_j) + e(V_j)` for a nonredundant circuit
prefix. -/
theorem circuit_flag_defect_count {m r j : Nat} (C : Circuit m r)
    (T : Submodule F₂ (ANF m)) (hj : j ≤ r)
    (hnr : ∀ i : Fin r, i.val < j → NonredundantAt C i) :
    j = flagTargetRank (circuitFlag C j) T +
      flagDefectRank (circuitFlag C j) T := by
  have hledger := flag_rank_ledger (T := T)
    (affine_le_wireSpace C.gate (j := j))
  have hdim := circuitFlag_finrank C hj hnr
  change Module.finrank F₂ ↥(wireSpace C.gate j) =
    Module.finrank F₂ ↥(affine m) + j at hdim
  rw [hdim] at hledger
  change j = flagTargetRank (wireSpace C.gate j) T +
    flagDefectRank (wireSpace C.gate j) T
  omega

end

end N4
end UnrestrictedBooleanMul
