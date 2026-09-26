/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.NativeAction

/-!
# The native projector and its action table

Character, dimension, and normalized projector of a simple
submodule on the native carrier; the scalar action, the
orthogonality-evaluated action table, idempotency, centrality,
and the block rank.
-/

@[expose] public section

namespace RS

open Finset LinearMap

variable {G : Type*}

/-- The character of a submodule of the regular module. -/
noncomputable def nChar
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (g : G) : ℂ :=
  (rhoS S).character g

/-- The dimension of a submodule of the regular module. -/
noncomputable def nDim
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) : ℕ :=
  Module.finrank ℂ (subCarrier S)

/-- The normalized projector coefficient. -/
noncomputable def nCoeff [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) : G → ℂ :=
  fun g => ((nDim S : ℂ) / (Fintype.card G : ℂ)) * nChar S g⁻¹

/-- The normalized projector. -/
noncomputable def nProjector [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    MonoidAlgebra ℂ G :=
  classElem (nCoeff S)

/-- The native projector's coefficient is a class function. -/
theorem nCoeff_classFun [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (g h : G) :
    nCoeff S (h * g * h⁻¹) = nCoeff S g := by
  rw [nCoeff, nCoeff]
  congr 1
  rw [show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ from by group]
  exact (rhoS S).char_conj g⁻¹ h

/-- Membership transfer to the restricted-scalars form. -/
theorem mem_subCarrier
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    {t : MonoidAlgebra ℂ G} (ht : t ∈ S) :
    t ∈ S.restrictScalars ℂ := ht

/-- **The native scalar action**: a class element multiplies each
element of a simple submodule by the character-pairing scalar. -/
theorem classElem_mul_mem_native [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S)
    (c : G → ℂ) (hc : ∀ g h : G, c (h * g * h⁻¹) = c g)
    (t : MonoidAlgebra ℂ G) (ht : t ∈ S) :
    classElem c * t =
      ((∑ g : G, c g * nChar S g) / (nDim S : ℂ)) • t := by
  classical
  have hsc := classElem_scalar_eq (ρ := rhoS S)
    (isIrredRep_rhoS S hS) c hc
  have happ := congrFun (congrArg (fun (f : Module.End ℂ
      (subCarrier S)) => (f : subCarrier S → subCarrier S)) hsc)
    ⟨t, mem_subCarrier S ht⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at happ
  rw [rhoS_asAlgebraHom_apply] at happ
  have h2 := congrArg
    (fun v : subCarrier S => (v : MonoidAlgebra ℂ G)) happ
  rw [show ((classElem c • (⟨t, mem_subCarrier S ht⟩ :
      subCarrier S) : subCarrier S) : MonoidAlgebra ℂ G) =
    classElem c * t from rfl] at h2
  rw [h2]
  rfl

/-- The native representation of a simple submodule is
irreducible in the subrepresentation-lattice sense. -/
theorem rhoS_isIrreducible
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S) :
    (rhoS S).IsIrreducible := by
  have hirr := isIrredRep_rhoS S hS
  have hnt : Nontrivial (Subrepresentation (rhoS S)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    have : Nontrivial (subCarrier S) := hirr.1
    intro hbt
    have h1 := congrArg Subrepresentation.toSubmodule hbt
    have h2 : (⊥ : Submodule ℂ (subCarrier S)) =
        (⊤ : Submodule ℂ (subCarrier S)) := h1
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (subCarrier S)
    apply hxy
    have hx : x ∈ (⊥ : Submodule ℂ (subCarrier S)) := by
      rw [h2]; trivial
    have hy : y ∈ (⊥ : Submodule ℂ (subCarrier S)) := by
      rw [h2]; trivial
    rw [Submodule.mem_bot] at hx hy
    rw [hx, hy]
  refine ⟨?_⟩
  intro σ
  rcases hirr.2 σ.toSubmodule
    (fun g v hv => σ.apply_mem_toSubmodule g hv) with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    exact hb
  · right
    apply Subrepresentation.toSubmodule_injective
    exact ht

open scoped Classical in
/-- **The native action table**: the projector of a simple
submodule acts on each simple submodule as `1` or `0` by
equivalence. -/
theorem nProjector_mul_mem [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (T : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S)
    (hT : IsSimpleModule (MonoidAlgebra ℂ G) T)
    (t : MonoidAlgebra ℂ G) (ht : t ∈ T) :
    nProjector S * t =
      (if Nonempty ((rhoS S).Equiv (rhoS T)) then (1 : ℂ) else 0)
        • t := by
  classical
  have := rhoS_isIrreducible S hS
  have := rhoS_isIrreducible T hT
  rw [nProjector, classElem_mul_mem_native T hT _
    (nCoeff_classFun S) t ht]
  congr 1
  have hcard0 : ((Nat.card G : ℂ)) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  have : Invertible ((Nat.card G : ℂ)) := invertibleOfNonzero hcard0
  have horth := Representation.char_orthonormal (rhoS T) (rhoS S)
  have hcard : ((Nat.card G : ℂ)) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ g : G, nCoeff S g * nChar T g) =
      ((nDim S : ℂ) / (Fintype.card G : ℂ)) *
        ∑ g : G, (rhoS T).character g *
          (rhoS S).character g⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [nCoeff, nChar, nChar]
    ring
  have h2 : (∑ g : G, (rhoS T).character g *
      (rhoS S).character g⁻¹) =
      (Nat.card G : ℂ) *
        (if Nonempty ((rhoS S).Equiv (rhoS T)) then 1 else 0) := by
    rw [← horth, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  rw [hsum, h2]
  by_cases heq : Nonempty ((rhoS S).Equiv (rhoS T))
  · rw [ite_eq_left heq]
    have hdim : nDim S = nDim T := by
      obtain ⟨e⟩ := heq
      exact e.toLinearEquiv.finrank_eq
    rw [hdim, Nat.card_eq_fintype_card, mul_one]
    have hd : ((nDim T : ℂ)) ≠ 0 := by
      have : Nontrivial (subCarrier T) :=
        (isIrredRep_rhoS T hT).1
      have h1 := Module.finrank_pos
        (R := ℂ) (M := subCarrier T)
      exact_mod_cast Nat.cast_ne_zero.mpr h1.ne'
    have hc : ((Fintype.card G : ℂ)) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp
  · rw [ite_eq_right heq]
    simp

open scoped Classical in
/-- **Idempotency of the native projector.** -/
theorem nProjector_idem [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S) :
    nProjector S * nProjector S = nProjector S := by
  classical
  have hkill : ∀ T : Submodule (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G),
      IsSimpleModule (MonoidAlgebra ℂ G) T →
      ∀ t ∈ T, (nProjector S * nProjector S -
        nProjector S) * t = 0 := by
    intro T hT t ht
    rw [sub_mul, mul_assoc]
    rw [nProjector_mul_mem S T hS hT t ht]
    rw [mul_smul_comm, nProjector_mul_mem S T hS hT t ht]
    by_cases heq : Nonempty ((rhoS S).Equiv (rhoS T))
    · rw [ite_eq_left heq, one_smul, one_smul, sub_self]
    · rw [ite_eq_right heq]
      simp
  have h0 := eq_zero_of_kills_simples _ hkill
  exact sub_eq_zero.mp h0

/-- Centrality of the native projector. -/
theorem nProjector_central [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (y : MonoidAlgebra ℂ G) :
    nProjector S * y = y * nProjector S := by
  classical
  exact
    classElem_mul_comm (nCoeff S) (nCoeff_classFun S) y

/-- The projector's coefficient at the identity. -/
theorem nProjector_coeff_one [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    (nProjector S).coeff 1 =
      ((nDim S : ℂ) ^ 2) / (Fintype.card G : ℂ) := by
  classical
  rw [nProjector, classElem_coeff, nCoeff, inv_one]
  rw [nChar, Representation.char_one]
  rw [show Module.finrank ℂ (subCarrier S) = nDim S from rfl]
  ring

/-- **The native block rank.** -/
theorem nProjector_block_rank [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S) :
    Module.finrank ℂ
      (LinearMap.range (mulLeft ℂ (nProjector S))) =
      nDim S ^ 2 := by
  classical
  have h := finrank_range_mulLeft (nProjector S)
    (nProjector_idem S hS)
  rw [nProjector_coeff_one] at h
  have hc : ((Fintype.card G : ℂ)) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [mul_div_cancel₀ _ hc] at h
  exact_mod_cast h

end RS
