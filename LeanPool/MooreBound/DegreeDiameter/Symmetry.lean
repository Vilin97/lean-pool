/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.CompletionCount
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Symmetry and regularity of the halved flag graph

Linear automorphisms act on complete and partial flags.  The common-apartment
part of Lemma 2.1 supplies an automorphism taking any chosen completion of one
vertex to a chosen completion of another.  Consequently the action on even
partial flags is transitive and the halved graph is regular.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

public section

namespace MooreBound

open Module

namespace DegreeDiameter

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  {n : ℕ}

@[simp]
theorem submodule_map_symm_map (e : V ≃ₗ[K] V) (S : Submodule K V) :
    (S.map e.toLinearMap).map e.symm.toLinearMap = S := by
  rw [Submodule.map_equiv_eq_comap_symm]
  exact Submodule.comap_map_eq_of_injective e.injective S

namespace CompleteFlag

/-- Transport every member of a complete flag along a linear equivalence. -/
noncomputable def map (e : V ≃ₗ[K] V) (F : CompleteFlag K V n) : CompleteFlag K V n where
  space i := (Submodule.orderIsoMapComap e) (F i)
  strictMono_space := (Submodule.orderIsoMapComap e).strictMono.comp F.strictMono_space
  finrank_space i := by
    change finrank K ((F i).map e.toLinearMap) = i
    exact (e.finrank_map_eq (F i)).trans (F.finrank_space i)
  space_zero := by simp [F.space_zero]
  space_last := by simp [F.space_last]

@[simp]
theorem map_apply (e : V ≃ₗ[K] V) (F : CompleteFlag K V n) (i : Fin (n + 1)) :
    F.map e i = (Submodule.orderIsoMapComap e) (F i) := rfl

@[simp]
theorem map_symm_map (e : V ≃ₗ[K] V) (F : CompleteFlag K V n) :
    (F.map e).map e.symm = F := by
  apply CompleteFlag.ext
  intro i
  exact submodule_map_symm_map e (F i)

@[simp]
theorem map_map_symm (e : V ≃ₗ[K] V) (F : CompleteFlag K V n) :
    (F.map e.symm).map e = F := by
  simpa using map_symm_map e.symm F

/-- Transporting a basis flag transports its basis. -/
theorem map_ofBasis (e : V ≃ₗ[K] V) (b : Basis (Fin n) K V) :
    (CompleteFlag.ofBasis b).map e = CompleteFlag.ofBasis (b.map e) := by
  apply CompleteFlag.ext
  intro i
  change (b.flag i).map e.toLinearMap = (b.map e).flag i
  simp only [Module.Basis.flag, Submodule.map_span, Set.image_image]
  congr 2

end CompleteFlag

namespace PartialFlag

/-- Transport a partial flag along a linear equivalence. -/
noncomputable def map {parity : ℕ} (e : V ≃ₗ[K] V)
    (P : PartialFlag (K := K) (V := V) (n := n) parity) :
    PartialFlag (K := K) (V := V) (n := n) parity := by
  refine ⟨fun i ↦ (Submodule.orderIsoMapComap e) (P.1 i), ?_⟩
  obtain ⟨F, hF⟩ := P.property
  refine ⟨F.map e, ?_⟩
  funext i
  rw [← congrFun hF i]
  by_cases hi : i.val % 2 = parity % 2
  · simp [flagPart, hi]
  · simp [flagPart, hi]

@[simp]
theorem map_val {parity : ℕ} (e : V ≃ₗ[K] V)
    (P : PartialFlag (K := K) (V := V) (n := n) parity) (i : Fin (n + 1)) :
    (P.map e).1 i = (Submodule.orderIsoMapComap e) (P.1 i) := rfl

@[simp]
theorem map_symm_map {parity : ℕ} (e : V ≃ₗ[K] V)
    (P : PartialFlag (K := K) (V := V) (n := n) parity) :
    (P.map e).map e.symm = P := by
  apply PartialFlag.ext
  intro i
  exact submodule_map_symm_map e (P.1 i)

@[simp]
theorem map_map_symm {parity : ℕ} (e : V ≃ₗ[K] V)
    (P : PartialFlag (K := K) (V := V) (n := n) parity) :
    (P.map e.symm).map e = P := by
  simpa using map_symm_map e.symm P

/-- Linear transport is an equivalence on partial flags. -/
noncomputable def mapEquiv {parity : ℕ} (e : V ≃ₗ[K] V) :
    PartialFlag (K := K) (V := V) (n := n) parity ≃
      PartialFlag (K := K) (V := V) (n := n) parity where
  toFun := map e
  invFun := map e.symm
  left_inv := map_symm_map e
  right_inv := map_map_symm e

@[simp]
theorem mapEquiv_apply {parity : ℕ} (e : V ≃ₗ[K] V)
    (P : PartialFlag (K := K) (V := V) (n := n) parity) :
    mapEquiv e P = P.map e := rfl

@[simp]
theorem map_ofComplete {parity : ℕ} (e : V ≃ₗ[K] V)
    (F : CompleteFlag K V n) :
    (PartialFlag.ofComplete parity F).map e =
      PartialFlag.ofComplete parity (F.map e) := by
  apply PartialFlag.ext
  intro i
  by_cases hi : i.val % 2 = parity % 2
  · change (Submodule.orderIsoMapComap e) (flagPart parity F i) =
        flagPart parity (F.map e) i
    simp [flagPart, hi]
  · change (Submodule.orderIsoMapComap e) (flagPart parity F i) =
        flagPart parity (F.map e) i
    simp [flagPart, hi]

end PartialFlag

theorem Compatible.map
    {P : EvenPartialFlag (K := K) (V := V) (n := n)}
    {Q : OddPartialFlag (K := K) (V := V) (n := n)}
    (h : Compatible P Q) (e : V ≃ₗ[K] V) :
    Compatible (P.map e) (Q.map e) := by
  obtain ⟨F, hEven, hOdd⟩ := h
  refine ⟨F.map e, ?_, ?_⟩
  · exact (PartialFlag.map_ofComplete e F).symm.trans (congrArg (PartialFlag.map e) hEven)
  · exact (PartialFlag.map_ofComplete e F).symm.trans (congrArg (PartialFlag.map e) hOdd)

theorem compatible_map_iff (e : V ≃ₗ[K] V)
    (P : EvenPartialFlag (K := K) (V := V) (n := n))
    (Q : OddPartialFlag (K := K) (V := V) (n := n)) :
    Compatible (P.map e) (Q.map e) ↔ Compatible P Q := by
  constructor
  · intro h
    simpa using h.map e.symm
  · intro h
    exact h.map e

/-- Every linear equivalence acts by an automorphism of the halved graph. -/
noncomputable def halvedFlagGraphIso (e : V ≃ₗ[K] V) :
    halvedFlagGraph (K := K) (V := V) (n := n) ≃g
      halvedFlagGraph (K := K) (V := V) (n := n) where
  __ := PartialFlag.mapEquiv e
  map_rel_iff' := by
    intro P P'
    rw [halvedFlagGraph_adj_iff, halvedFlagGraph_adj_iff]
    constructor
    · rintro ⟨hne, Q, hPQ, hP'Q⟩
      refine ⟨fun h ↦ hne (congrArg (PartialFlag.map e) h), Q.map e.symm, ?_, ?_⟩
      · simpa using hPQ.map e.symm
      · simpa using hP'Q.map e.symm
    · rintro ⟨hne, Q, hPQ, hP'Q⟩
      refine ⟨fun h ↦ hne ((PartialFlag.mapEquiv e).injective h), Q.map e, ?_, ?_⟩
      · exact hPQ.map e
      · exact hP'Q.map e

@[simp]
theorem halvedFlagGraphIso_apply (e : V ≃ₗ[K] V)
    (P : EvenPartialFlag (K := K) (V := V) (n := n)) :
    halvedFlagGraphIso e P = P.map e := rfl

/-- Transitivity on even partial flags. -/
theorem exists_halvedFlagGraphIso_map_eq
    (P P' : EvenPartialFlag (K := K) (V := V) (n := n)) :
    ∃ φ : halvedFlagGraph (K := K) (V := V) (n := n) ≃g
        halvedFlagGraph (K := K) (V := V) (n := n), φ P = P' := by
  obtain ⟨F, hF⟩ := P.property
  obtain ⟨F', hF'⟩ := P'.property
  have hPF : PartialFlag.ofComplete 0 F = P := Subtype.ext hF
  have hPF' : PartialFlag.ofComplete 0 F' = P' := Subtype.ext hF'
  obtain ⟨b, π, hFb, hF'b⟩ := common_apartment K V F F'
  let b' : Basis (Fin n) K V := b.reindex π.symm
  let e : V ≃ₗ[K] V := b.equiv b' (Equiv.refl (Fin n))
  have hmapBasis : b.map e = b' := by
    dsimp [e]
    rw [Basis.map_equiv]
    simp
  have hmapFlag : F.map e = F' := by
    calc
      F.map e = (CompleteFlag.ofBasis b).map e := congrArg (fun H ↦ H.map e) hFb
      _ = CompleteFlag.ofBasis (b.map e) := CompleteFlag.map_ofBasis e b
      _ = CompleteFlag.ofBasis b' := congrArg CompleteFlag.ofBasis hmapBasis
      _ = F' := hF'b.symm
  refine ⟨halvedFlagGraphIso e, ?_⟩
  calc
    halvedFlagGraphIso e P = P.map e := rfl
    _ = (PartialFlag.ofComplete 0 F).map e := congrArg (PartialFlag.map e) hPF.symm
    _ = PartialFlag.ofComplete 0 (F.map e) := PartialFlag.map_ofComplete e F
    _ = PartialFlag.ofComplete 0 F' := congrArg (PartialFlag.ofComplete 0) hmapFlag
    _ = P' := hPF'

/-- All neighbor sets have the same finite cardinality. -/
theorem halvedFlagGraph_natCard_neighborSet_eq
    (P P' : EvenPartialFlag (K := K) (V := V) (n := n)) :
    Nat.card ((halvedFlagGraph (K := K) (V := V) (n := n)).neighborSet P) =
      Nat.card ((halvedFlagGraph (K := K) (V := V) (n := n)).neighborSet P') := by
  obtain ⟨φ, hφ⟩ := exists_halvedFlagGraphIso_map_eq P P'
  simpa [hφ] using Nat.card_congr (φ.mapNeighborSet P)

/-- A common natural-number degree for all vertices, stated without making
the particular `Fintype` structures on neighbor sets part of the theorem. -/
theorem exists_halvedFlagGraph_common_degree
    [Nonempty (EvenPartialFlag (K := K) (V := V) (n := n))] :
    ∃ Δ : ℕ, ∀ P : EvenPartialFlag (K := K) (V := V) (n := n),
      Nat.card ((halvedFlagGraph (K := K) (V := V) (n := n)).neighborSet P) = Δ := by
  classical
  let P₀ : EvenPartialFlag (K := K) (V := V) (n := n) := Classical.choice inferInstance
  exact ⟨Nat.card ((halvedFlagGraph (K := K) (V := V) (n := n)).neighborSet P₀),
    fun P ↦ halvedFlagGraph_natCard_neighborSet_eq P P₀⟩

end DegreeDiameter

end MooreBound
