/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.ANF

/-!
# Unrestricted XOR--AND circuits

Free XORs are represented by submodule spans. At gate `j`, both factors must
belong to the affine span enlarged by the outputs of gates with index below
`j`. This semantic presentation is equivalent to storing coefficient masks,
but makes the unrestricted nature of nonlinear feedback explicit.
-/

public section

namespace UnrestrictedBooleanMul

noncomputable section

/-- Outputs of gates whose index is strictly before `j`. -/
@[expose] def prefixGates {m r : Nat} (g : Fin r → ANF m) (j : Nat) : Set (ANF m) :=
  {p | ∃ i : Fin r, i.val < j ∧ g i = p}

/-- The functions available for free immediately before gate `j`. -/
@[expose] def wireSpace {m r : Nat} (g : Fin r → ANF m) (j : Nat) : Submodule F₂ (ANF m) :=
  affine m ⊔ Submodule.span F₂ (prefixGates g j)

theorem affine_le_wireSpace {m r j : Nat} (g : Fin r → ANF m) :
    affine m ≤ wireSpace g j := le_sup_left

/-- An unrestricted XOR--AND circuit with exactly `r` AND gates. -/
structure Circuit (m r : Nat) where
  /-- The Boolean function produced by each AND gate. -/
  gate : Fin r → ANF m
  /-- The left input function of each AND gate. -/
  left : Fin r → ANF m
  /-- The right input function of each AND gate. -/
  right : Fin r → ANF m
  left_mem : ∀ j, left j ∈ wireSpace gate j.val
  right_mem : ∀ j, right j ∈ wireSpace gate j.val
  gate_eq : ∀ j, gate j = left j * right j

/-- A circuit all of whose AND inputs are affine in the original inputs. -/
@[expose] def Circuit.ofAffineProducts {m r : Nat} (left right : Fin r → ANF m)
    (left_affine : ∀ i, left i ∈ affine m)
    (right_affine : ∀ i, right i ∈ affine m) : Circuit m r where
  gate i := left i * right i
  left := left
  right := right
  left_mem i := affine_le_wireSpace _ (left_affine i)
  right_mem i := affine_le_wireSpace _ (right_affine i)
  gate_eq _ := rfl

@[simp]
theorem Circuit.ofAffineProducts_gate {m r : Nat} (left right : Fin r → ANF m)
    (left_affine : ∀ i, left i ∈ affine m)
    (right_affine : ∀ i, right i ∈ affine m) (i : Fin r) :
    (Circuit.ofAffineProducts left right left_affine right_affine).gate i = left i * right i := by
  rfl

/-- The circuit with no AND gates. -/
def Circuit.empty (m : Nat) : Circuit m 0 :=
  Circuit.ofAffineProducts (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

/-- The final free-XOR wire space of a circuit. -/
@[expose] def Circuit.finalWire {m r : Nat} (C : Circuit m r) : Submodule F₂ (ANF m) :=
  wireSpace C.gate r

/-- A circuit computes a vector-valued target when every coordinate is in its final span. -/
@[expose] def Circuit.Computes {m r o : Nat} (C : Circuit m r) (target : Fin o → ANF m) : Prop :=
  ∀ i, target i ∈ C.finalWire

/-- There is an unrestricted circuit with `r` AND gates computing `target`. -/
@[expose] def HasCircuit {m o : Nat} (target : Fin o → ANF m) (r : Nat) : Prop :=
  Nonempty {C : Circuit m r // C.Computes target}

/-- Unrestricted Boolean multiplicative complexity (zero for an uncomputable target). -/
def multiplicativeComplexity {m o : Nat} (target : Fin o → ANF m) : Nat :=
  by
    classical
    exact if h : ∃ r, HasCircuit target r then Nat.find h else 0

/-- Unrestricted AND-gate complexity, with XOR and constants free. -/
notation "MC(" target ")" => multiplicativeComplexity target

theorem mc_eq_of_lower_upper {m o r : Nat} {target : Fin o → ANF m}
    (upper : HasCircuit target r)
    (lower : ∀ s, HasCircuit target s → r ≤ s) : MC(target) = r := by
  classical
  rw [multiplicativeComplexity, dite_eq_left ⟨r, upper⟩]
  apply Nat.le_antisymm
  · exact Nat.find_min' ⟨r, upper⟩ upper
  · exact lower _ (Nat.find_spec ⟨r, upper⟩)

theorem gate_mem_wireSpace {m r : Nat} (g : Fin r → ANF m) (i : Fin r) {j : Nat}
    (hij : i.val < j) : g i ∈ wireSpace g j := by
  apply Submodule.mem_sup_right
  apply Submodule.subset_span
  exact ⟨i, hij, rfl⟩

@[simp]
theorem gate_mem_finalWire {m r : Nat} (C : Circuit m r) (i : Fin r) :
    C.gate i ∈ C.finalWire := by
  apply gate_mem_wireSpace
  exact i.isLt

theorem prefixGates_all {m r : Nat} (g : Fin r → ANF m) :
    prefixGates g r = Set.range g := by
  ext p
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩

theorem Circuit.finalWire_eq {m r : Nat} (C : Circuit m r) :
    C.finalWire = affine m ⊔ Submodule.span F₂ (Set.range C.gate) := by
  rw [Circuit.finalWire, wireSpace, prefixGates_all]

/-- Mapping a final wire space through a linear map that kills affine functions
leaves exactly the span of the mapped AND-gate outputs. -/
theorem Circuit.map_finalWire_eq_span {m r : Nat} (C : Circuit m r)
    {V : Type*} [AddCommGroup V] [Module F₂ V] (P : ANF m →ₗ[F₂] V)
    (killsAffine : affine m ≤ LinearMap.ker P) :
    Submodule.map P C.finalWire = Submodule.span F₂ (Set.range fun i => P (C.gate i)) := by
  have hmapAffine : Submodule.map P (affine m) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨x, hx, rfl⟩
    exact killsAffine hx
  rw [C.finalWire_eq, Submodule.map_sup, hmapAffine, bot_sup_eq, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨C.gate i, ⟨i, rfl⟩, rfl⟩

/-- Dimension lower bound obtained from any coordinate projection that kills
affine functions and sends the targets to the standard basis. -/
theorem circuit_lower_bound_of_projection {m d r : Nat} (C : Circuit m r)
    (target : Fin d → ANF m) (P : ANF m →ₗ[F₂] (Fin d → F₂))
    (killsAffine : affine m ≤ LinearMap.ker P)
    (mapsTarget : ∀ i, P (target i) = (Pi.basisFun F₂ (Fin d)) i)
    (computes : C.Computes target) : d ≤ r := by
  let S := Submodule.span F₂ (Set.range fun i => P (C.gate i))
  have hbasis : ∀ i, (Pi.basisFun F₂ (Fin d)) i ∈ S := by
    intro i
    rw [← mapsTarget i]
    have hmapped : P (target i) ∈ Submodule.map P C.finalWire :=
      ⟨target i, computes i, rfl⟩
    rwa [C.map_finalWire_eq_span P killsAffine] at hmapped
  have htop : S = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun F₂ (Fin d)).span_eq]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hbasis i
  have hdim : Module.finrank F₂ (Fin d → F₂) ≤ Fintype.card (Fin r) :=
    finrank_le_of_span_eq_top (by simpa [S] using htop)
  simpa using hdim

/-- Target dimension modulo the free affine functions. -/
def targetDimension {m r : Nat} (C : Circuit m r) (target : Submodule F₂ (ANF m))
    (j : Nat) : Nat :=
  Module.finrank F₂ ↥(wireSpace C.gate j ⊓ (affine m ⊔ target)) -
    Module.finrank F₂ ↥(affine m)

end

end UnrestrictedBooleanMul
