/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import LeanPool.BruhatTits.Graph.Tree

/-!
# Proof that the Bruhat-Tits tree is regular

Let `R` be a discrete valuation ring. Assume that the residue field `k = R ⧸ 𝓂 R` of `R`
is finite.

In this file we show that the Bruhat-Tits tree associated to `R` is regular, i.e. that every
vertex has the same finite number of neighbours. Furthermore we show that this number is `#k+1`.

# Main result

- `BruhatTits.btgraph_regular` : The Bruhat-Tits Tree is `q + 1`-regular, where `q` is the
  cardinality of `R ⧸ 𝓂 R`.
-/

open Module


suppress_compilation

-- Let R be a discrete valuation ring and K its field of fractions
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

namespace BruhatTits

/-- A basis putting a neighbour of `L` into standard form. -/
def standardNeighbourBasis {L : Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) :
    Basis (Fin 2) K (Fin 2 → K) :=
  (exists_basis_eq_ntwist_of_isNeighbour L y ((isNeighbour_symm _ _).mp h)).choose

@[simp]
lemma standardNeighbourBasis_toLattice_Eq {L : Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) :
    (standardNeighbourBasis h).toLattice = L :=
  (exists_basis_eq_ntwist_of_isNeighbour L y
    ((isNeighbour_symm _ _).mp h)).choose_spec.choose_spec.choose_spec.left

/-- The uniformizer used in the standard representative of a neighbour. -/
def standardNeighbourϖ {L : Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) : R :=
  (exists_basis_eq_ntwist_of_isNeighbour L y ((isNeighbour_symm _ _).mp h)).choose_spec.choose

lemma standardNeighbourϖ_irreducible {L : Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) :
    Irreducible (standardNeighbourϖ h) :=
  (exists_basis_eq_ntwist_of_isNeighbour L y
    ((isNeighbour_symm _ _).mp h)).choose_spec.choose_spec.choose

/-- The standard lattice representative of a neighbour of `L`. -/
def standardNeighbour {L : Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) :
    Lattice R :=
  ((standardNeighbourBasis h).ntwist₂ (standardNeighbourϖ_irreducible h) 1 0).toLattice

@[simp]
lemma standardNeighbourBasis_ntwist_eq {L : Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) :
    ((standardNeighbourBasis h).ntwist₂ (standardNeighbourϖ_irreducible h) 1 0).toLattice =
      standardNeighbour h :=
  rfl

lemma standardNeighbour_isStandardNeighbour {L : Lattice R} {y : Vertices R}
    (h : IsNeighbour y ⟦L⟧) :
    IsStandardNeighbour (standardNeighbour h) L := by
  nth_rw 2 [← standardNeighbourBasis_toLattice_Eq h]
  apply ntwist_isStandardNeighbour

@[simp]
lemma standardNeighbour_mk_eq {L : Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) :
    ⟦standardNeighbour h⟧ = y :=
  (exists_basis_eq_ntwist_of_isNeighbour L y
    ((isNeighbour_symm _ _).mp h)).choose_spec.choose_spec.choose_spec.right

lemma exists_basis_standardNeighbour_eq_twist {L : Lattice R} {y : Vertices R}
    (h : IsNeighbour y ⟦L⟧) :
    ∃ (ϖ : R) (hϖ : Irreducible ϖ) (b : Basis (Fin 2) K (Fin 2 → K)),
      L = b.toLattice ∧ standardNeighbour h = (b.ntwist₂ hϖ 1 0).toLattice := by
  use standardNeighbourϖ h, standardNeighbourϖ_irreducible h, standardNeighbourBasis h
  simp

lemma eq_standardNeighbour_of_isStandardNeighbour {L : Lattice R} {y : Vertices R}
    (h : IsNeighbour y ⟦L⟧) (M : Lattice R) (hM : ⟦M⟧ = y)
    (hML : IsStandardNeighbour M L) :
    M = standardNeighbour h := by
  obtain ⟨ϖ, hϖ, b, rfl, hstd⟩ := exists_basis_standardNeighbour_eq_twist h
  have : (⟦M⟧ : Vertices R) = ⟦standardNeighbour h⟧ := by simp [hM]
  have : Lattice.IsSimilar R (standardNeighbour h) M := Quotient.exact this.symm
  obtain ⟨a, rfl⟩ := this
  obtain ⟨n, u, ha⟩ := eq_unit_mul_pow_irreducible' ϖ hϖ a
  rw [ha, mul_comm, mul_smul, unit_smul_eq] at hML ⊢
  rw [hstd] at hML
  nth_rw 2 [← b.ntwist₂_zero_zero hϖ] at hML
  have h1 := hML.lt
  have h2 := hML.ϖlt ϖ hϖ
  rw [Basis.toLattice_module, b.smul_ntwist₂] at h2
  simp only [Lattice.smul_module, Basis.toLattice_module, Units.smul_def,
    Units.val_zpow_eq_zpow_val, Units.val_mk0, Basis.ntwist₂] at h1 h2
  rw [b.smul_pow_twist₂] at h1
  simp only [Nat.cast_one, Nat.cast_zero, zero_add] at h1
  rw [b.smul_pow_twist₂] at h2
  simp only [zero_add, Nat.cast_one, CharP.cast_eq_zero] at h2
  apply le_of_lt at h1
  apply le_of_lt at h2
  rw [b.twist₂_le_twist₂_iff] at h1 h2
  have : n = 0 := by omega
  rw [this]
  simp

open IsLocalRing

/-- The neighbours of `⟦L⟧` are in one to one correspondence to standard neighbours of `L`. -/
def neighborsEquivStandardNeighbors (L : Lattice R) :
    { y : Vertices R | IsNeighbour y ⟦L⟧ } ≃ { M : Lattice R | IsStandardNeighbour M L } where
  toFun y := ⟨standardNeighbour y.property, standardNeighbour_isStandardNeighbour y.property⟩
  invFun M := ⟨⟦M⟧, isNeighbour_of_isStandardNeighbour M.property⟩
  left_inv y := by simp
  right_inv M := by
    ext : 1
    simp only [Set.mem_setOf_eq]
    symm
    apply eq_standardNeighbour_of_isStandardNeighbour
    · rfl
    · exact M.property

/-- Restrict scalars from the residue field quotient to an `R`-submodule. -/
def _root_.BruhatTits.Lattice.quotientRestrictScalarsEquiv (L : Lattice R) :
    Submodule (ResidueField R) L.quotient ≃o Submodule R L.quotient where
  toFun M := M.restrictScalars R
  invFun M := {
      toAddSubmonoid := M.toAddSubmonoid
      smul_mem' := fun r _ hx ↦
        Quotient.inductionOn' r (fun r ↦ Submodule.smul_mem _ r hx)
    }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

instance (priority := 99999) (L : Lattice R) : SMul (Ideal R) (Submodule R L.M) :=
  Submodule.instSMul

/--
Relate quotient submodules to submodules of the lattice containing the maximal ideal multiple.
-/
def _root_.BruhatTits.Lattice.submoduleRestrictQuotientEquiv (L : Lattice R) :
    Submodule R L.quotient ≃o
      { M : Submodule R L.M // (maximalIdeal R • ⊤ : Submodule R L.M) ≤ M } :=
  Submodule.comapMkQRelIso (maximalIdeal R • ⊤ : Submodule R L.M)

/-- Relate residue-field subspaces of the quotient to intermediate `R`-submodules of the lattice. -/
def _root_.BruhatTits.Lattice.submoduleQuotientEquiv (L : Lattice R) :
    Submodule (ResidueField R) L.quotient ≃o { M : Submodule R L.M // maximalIdeal R • ⊤ ≤ M } :=
  L.quotientRestrictScalarsEquiv.trans L.submoduleRestrictQuotientEquiv

lemma submodule_ne_top_of_finrank {L : Lattice R}
    {M : Submodule (ResidueField R) L.quotient}
    (h : Module.finrank (ResidueField R) M = 1) : M ≠ ⊤ := by
  rintro rfl
  simp only [finrank_top] at h
  have : Module.finrank (ResidueField ↥R) L.quotient = 2 := Lattice.quotient_finrank L
  omega

omit [IsFractionRing R K] in
lemma submodule_ne_bot_of_finrank {L : Lattice R}
    {M : Submodule (ResidueField R) L.quotient}
    (h : Module.finrank (ResidueField R) M = 1) : M ≠ ⊥ := by
  rintro rfl
  simp at h

lemma submodule_finrank_eq_one_of_ne_bot_of_ne_top {L : Lattice R}
    {M : Submodule (ResidueField R) L.quotient}
    (h₁ : M ≠ ⊥) (h₂ : M ≠ ⊤) :
    Module.finrank (ResidueField R) M = 1 := by
  have : Module.finrank (ResidueField R) M < 2 := by
    rw [← L.quotient_finrank]
    apply Submodule.finrank_lt_finrank_of_ne_top
    exact h₂
  have : 0 < Module.finrank (ResidueField R) M := by
    apply Submodule.zero_lt_finrank_of_ne_bot
    exact h₁
  omega

lemma submodule_finrank_eq_one_iff {L : Lattice R}
    {M : Submodule (ResidueField R) L.quotient} :
    Module.finrank (ResidueField R) M = 1 ↔ M ≠ ⊥ ∧ M ≠ ⊤ :=
  ⟨fun h ↦ ⟨submodule_ne_bot_of_finrank h, submodule_ne_top_of_finrank h⟩,
   fun h ↦ submodule_finrank_eq_one_of_ne_bot_of_ne_top h.left h.right⟩

/-- Lines in the residue quotient correspond to proper nonzero intermediate submodules. -/
def linesQuotientEquiv (L : Lattice R) :
    { M : Submodule (ResidueField R) L.quotient // Module.finrank (ResidueField R) M = 1 } ≃
      { M : { M : Submodule R L.M // maximalIdeal R • ⊤ ≤ M } // M ≠ ⊥ ∧ M ≠ ⊤ } where
  toFun M := ⟨L.submoduleQuotientEquiv M, by
    simp only [ne_eq, map_eq_bot_iff, map_eq_top_iff, ← submodule_finrank_eq_one_iff]
    exact M.property⟩
  invFun M := ⟨L.submoduleQuotientEquiv.symm M, by
    rw [submodule_finrank_eq_one_iff]
    simp only [ne_eq, map_eq_bot_iff, M.property, not_false_eq_true, map_eq_top_iff, and_self]⟩
  left_inv M := by simp only [OrderIso.symm_apply_apply, Subtype.coe_eta]
  right_inv M := by simp only [ne_eq, OrderIso.apply_symm_apply, Subtype.coe_eta]

private def Lattice.submoduleNeAndNeEquivLtAndLt (L : Lattice R) :
    { M : { M : Submodule R L.M // maximalIdeal R • ⊤ ≤ M } // M ≠ ⊥ ∧ M ≠ ⊤ } ≃
      { M : Submodule R (Fin 2 → K) // maximalIdeal R • L.M < M ∧ M < L.M } where
  toFun M := ⟨Submodule.map L.M.subtype M.val.val, by
    refine ⟨ideal_smul_lt_of_ne_bot _ _ M.property.left, ?_⟩
    apply lt_of_ne_top
    exact M.property.right⟩
  invFun M := ⟨⟨Submodule.comap L.M.subtype M, by
      rw [← Submodule.comap_subtype_smul]
      apply Submodule.comap_mono
      exact le_of_lt M.property.left⟩, by
    refine ⟨?_, ?_⟩
    · simp only [ne_eq, Submodule.quotient_equiv_eq_bot_iff]
      intro hc
      apply_fun Submodule.map L.M.subtype at hc
      rw [Submodule.map_comap_eq_self, Submodule.map_subtype_smul] at hc
      · exact (ne_of_gt M.property.left) hc
      · simp only [Submodule.range_subtype]
        exact le_of_lt M.property.right
    · simp only [ne_eq, le_top, Subtype.mk_eq_top_iff, Submodule.comap_subtype_eq_top]
      exact not_le_of_gt M.property.right⟩
  left_inv M := by
    ext : 2
    simp only [ne_eq, Submodule.comap_map_eq_self, Submodule.ker_subtype, bot_le]
  right_inv M := by
    ext : 1
    dsimp only
    rw [Submodule.map_comap_eq_self]
    simp only [Submodule.range_subtype]
    exact le_of_lt M.property.right

open Pointwise

/-- `R`-submodules of `K^2` that are strictly between `ϖ L` and `L` are in one-to-one
correspondence to standard neighbours of `L`. -/
def _root_.BruhatTits.Lattice.standardNeighboursEquivLinesAux (L : Lattice R) :
    { M : Submodule R (Fin 2 → K) // maximalIdeal R • L.M < M ∧ M < L.M } ≃
      { M : Lattice R // IsStandardNeighbour M L } where
  toFun M := ⟨⟨M, .of_le_of_isLattice_right L.M M
      (le_of_lt M.property.right) (le_of_lt M.property.left)⟩,
    M.property.right, fun ϖ hϖ ↦ by
      rw [← maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
      exact M.property.left⟩
  invFun M := ⟨M.val.M, by
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
      rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
      exact M.property.ϖlt ϖ hϖ, M.property.lt⟩
  left_inv M := rfl
  right_inv M := rfl

/-- The standard neighbours of `⟦L⟧` are in one-to-one correspondence to
one-dimensional subspaces of `L ⧸ ϖ L`, i.e. lines. -/
def standardNeighboursEquivLines (L : Lattice R) :
    { M : Lattice R // IsStandardNeighbour M L } ≃
      { M : Submodule (ResidueField R) L.quotient // Module.finrank (ResidueField R) M = 1 } :=
  L.standardNeighboursEquivLinesAux.symm.trans <|
    L.submoduleNeAndNeEquivLtAndLt.symm.trans (linesQuotientEquiv L).symm

/-- Neighbors of a vertex `⟦L⟧` correspond to lines in `L ⧸ ϖ L`. -/
def neighborsEquivLines (L : Lattice R) :
    { y : Vertices R // IsNeighbour y ⟦L⟧ } ≃
      { M : Submodule (ResidueField R) L.quotient // Module.finrank (ResidueField R) M = 1 } :=
  (neighborsEquivStandardNeighbors L).trans (standardNeighboursEquivLines L)

open scoped LinearAlgebra.Projectivization

/-- Neighbors of a vertex `⟦L⟧` correspond the projectivization of `L ⧸ ϖ L`. -/
def neighborSetEquivProjectivization (L : Lattice R) :
    BTgraph.neighborSet ⟦L⟧ ≃ ℙ (ResidueField R) L.quotient :=
  (Equiv.setCongr <| by ext; simp [BTgraph_adj, isNeighbour_symm]; rfl).trans <|
  (neighborsEquivLines L).trans
    (Projectivization.equivSubmodule (ResidueField R) L.quotient).symm

variable [Finite (ResidueField R)]

/-- If the residue field of `R` is finite, every vertex has finitely many neighbors. -/
instance (x : Vertices R) : Finite ((BTgraph (R := R)).neighborSet x) := by
  refine Quotient.inductionOn x (fun L ↦ ?_)
  change Finite {y : Vertices R // IsNeighbour ⟦L⟧ y}
  have : Finite L.quotient := Module.finite_of_finite (ResidueField R)
  apply Finite.of_equiv _ (neighborSetEquivProjectivization L).symm

instance (x : Vertices R) : Fintype ((BTgraph (R := R)).neighborSet x) :=
  Fintype.ofFinite _

/-- The degree of the Bruhat-Tits tree is `q + 1` where `q` is the cardinality of `R ⧸ 𝓂 R`. -/
lemma btgraph_degree (x : Vertices R) :
    (BTgraph (R := R)).degree x = Nat.card (ResidueField R) + 1 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card]
  refine Quotient.inductionOn x (fun L ↦ ?_)
  rw [Nat.card_congr (neighborSetEquivProjectivization L)]
  apply Projectivization.card_of_finrank_two
  exact Lattice.quotient_finrank L

/-- If `R ⧸ 𝓂 R` is finite, the Bruhat-Tits Tree is `q + 1`-regular, where `q` is the
cardinality of `R ⧸ 𝓂 R`. -/
theorem btgraph_regular :
    (BTgraph (R := R)).IsRegularOfDegree (Nat.card (ResidueField R) + 1) :=
  btgraph_degree

end BruhatTits
