/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Lattice.Distance
import LeanPool.BruhatTits.Lattice.Construction

/-!
# Definition of vertices

In this file we define the type of vertices of the Bruhat-Tits tree. A vertex is
an equivalence class of `R`-lattices with respect to homothety.

The distance of lattices is invariant under homothety (see `BruhatTits.dist_inv_isSimilar`),
hence the distance function descends to vertices which is called `BruhatTits.inv`. This
is later used to define the edge relations on the Bruhat-Tits graph (see `BruhatTits.Graph.Edges`).

## Main definitions and results

- `BruhatTits.inv`: the distance between vertices defined as the distance between lattice
  representatives.
- `BruhatTits.exists_repr_inv'`: given two vertices `x` and `y`, there exists a basis `b` of
  `Fin 2 → K` such that `x = ⟦b.toLattice⟧` and `y = `⟦(b.ntwist₂ (inv x y) 0).toLattice⟧`.
- `BruhatTits.exists_intermediate_vertex`: Given two vertices `x` and `y` of distance `n + 1`,
  there exists a vertex `z` such that `inv x z = n` and `inv z y = 1`. This will later be used to
  deduce that the Bruhat-Tits graph is connected.

-/

open Module

namespace BruhatTits

variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]

/-- The vertices of the Bruhat-Tits tree are `R`-lattices modulo the equivalence relation
`IsSimilar`. -/
def Vertices : Type _ :=
  Quotient (Lattice.IsSimilar.setoid R)

variable {R}

/-- An abbreviation for `Quotient.mk` for vertices. We only use this it the additional type
information is needed. -/
abbrev _root_.BruhatTits.Vertices.mk (L : Lattice R) : Vertices R := ⟦L⟧

/-- The distance of vertices defined as the distance of representatives. This is well-defined
by `BruhatTits.dist_inv_isSimilar`. -/
noncomputable def inv (L M : Vertices R) : ℕ :=
 Quotient.lift₂ dist dist_inv_isSimilar L M

@[simp]
lemma inv_mk (L M : BruhatTits.Lattice R) :
    inv (Quotient.mk'' L) (Quotient.mk'' M) = dist L M :=
  rfl

lemma inv_symm (L M : Vertices R) : inv L M = inv M L := by
  refine Quotient.inductionOn₂' L M (fun L M ↦ ?_)
  simpa only [inv_mk] using dist_symm L M

lemma inv_self (L : Vertices R) : inv L L = 0 := by
  refine Quotient.inductionOn' L (fun L ↦ ?_)
  simp

open Pointwise

/-- Variant of `exists_repr_inv` where the first vertex has a fixed representative. -/
lemma exists_repr_inv_of_fixed (M : Lattice R) (y : Vertices R) :
    ∃ (ϖ : R) (_ : Irreducible ϖ) (L : Lattice R)
      (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M),
      ⟦L⟧ = y ∧ bL 0 = ϖ ^ (inv ⟦M⟧ y) • (bM 0).val ∧ bL 1 = (bM 1).val := by
  refine Quotient.inductionOn' y (fun L ↦ ?_)
  obtain ⟨ϖ, bM, bL, f, hϖ, _, hrep, hdiff⟩ := exists_repr_dist M L
  have hϖ' : ϖ.val ≠ 0 := by simpa using hϖ.ne_zero
  let L' : Lattice R := (Units.mk0 ϖ.val hϖ') ^ (- f 1) • L
  let bL' : Basis (Fin 2) R L'.M := mulBasisScalar ((Units.mk0 ϖ.val hϖ') ^ (-f 1)) bL
  refine ⟨ϖ, hϖ, L', bM, bL', ?_, ?_, ?_⟩
  · exact Quotient.sound (show Lattice.IsSimilar R L' L from by
      simpa [L', zpow_neg] using
        Lattice.smul_isSimilar R L ((Units.mk0 ϖ.val hϖ') ^ (-f 1)))
  · simp only [bL']
    rw [mulBasisScalar_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0,
      inv_mk, hrep, smul_smul, ← zpow_add₀ hϖ', neg_add_eq_sub, hdiff, R.smul_def, R.coe_pow,
      zpow_natCast]
  · simp only [bL']
    rw [mulBasisScalar_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0, hrep,
      smul_smul, ← zpow_add₀ hϖ', neg_add_eq_sub, sub_self, zpow_zero, one_smul]

/-- Given vertices `x` and `y`, there exist representatives `M` and `L` and a basis
`bM` of `M` such that `(ϖ ^ (inv x y) • (bM 0), bM 1)` is a basis of `L`. -/
lemma exists_repr_inv (x y : Vertices R) :
    ∃ (ϖ : R) (_ : Irreducible ϖ) (M L : Lattice R)
      (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M),
      ⟦M⟧ = x ∧ ⟦L⟧ = y ∧ bL 0 = ϖ ^ (inv x y) • (bM 0).val ∧ bL 1 = (bM 1).val := by
  refine Quotient.inductionOn' x (fun M ↦ ?_)
  obtain ⟨ϖ, hϖ, L, bM, bL, hL, hbL₀, hbL₁⟩ := exists_repr_inv_of_fixed M y
  use ϖ, hϖ, M, L, bM, bL

/-- Variant of `exists_repr_dist` in terms of `Basis.twist`. -/
lemma exists_repr_dist' (M L : Lattice R) :
    ∃ (ϖ : R) (hϖ : Irreducible ϖ) (b : Basis (Fin 2) K (Fin 2 → K))
      (f : Fin 2 → ℤ) (_ : Antitone f),
      M = b.toLattice ∧ L = (b.twist hϖ f).toLattice ∧ f 0 - f 1 = dist M L := by
  obtain ⟨ϖ, bM, bL, f, hϖ, hf, hrep, hdiff⟩ := exists_repr_dist M L
  have hML : bM.fromLattice.twist hϖ f = bL.fromLattice := by
    ext i : 1
    simp [hrep]
  refine ⟨ϖ, hϖ, bM.fromLattice, f, hf, ?_, ?_, hdiff⟩
  · simp
  · simp [hML]

/-- Variant of `exists_repr_inv_of_fixed` in terms of `Basis.ntwist₂`. -/
lemma exists_repr_inv'_of_fixed (M : Lattice R) (L : Vertices R) :
    ∃ (ϖ : R) (hϖ : Irreducible ϖ) (b : Basis (Fin 2) K (Fin 2 → K)),
      b.toLattice = M ∧ ⟦(b.ntwist₂ hϖ (inv ⟦M⟧ L) 0).toLattice⟧ = L := by
  refine Quotient.inductionOn' L (fun L ↦ ?_)
  obtain ⟨ϖ, hϖ, L', bM, bL, hL, h0, h1⟩ := exists_repr_inv_of_fixed M ⟦L⟧
  have hML : bM.fromLattice.ntwist₂ hϖ (inv ⟦M⟧ (Quotient.mk'' L)) 0 = bL.fromLattice := by
    ext i : 1
    simp only [inv_mk, Basis.fromLattice_apply]
    match i with
    | 0 =>
      simp only [Basis.ntwist₂_apply₀, Basis.fromLattice_apply, h0]
      rfl
    | 1 => simp [h1]
  refine ⟨ϖ, hϖ, bM.fromLattice, ?_, ?_⟩
  · simp only [Basis.toLattice_fromLattice]
  · rw [hML]
    simp only [Basis.toLattice_fromLattice, hL]

/-- Variant of `exists_repr_inv` in terms of `Basis.ntwist₂`. -/
lemma exists_repr_inv' (M L : Vertices R) :
    ∃ (ϖ : R) (hϖ : Irreducible ϖ) (b : Basis (Fin 2) K (Fin 2 → K)),
      ⟦b.toLattice⟧ = M ∧ ⟦(b.ntwist₂ hϖ (inv M L) 0).toLattice⟧ = L := by
  refine Quotient.inductionOn' M (fun M ↦ ?_)
  obtain ⟨ϖ, hϖ, b, rfl, hL⟩ := exists_repr_inv'_of_fixed M L
  use ϖ, hϖ, b

/-- If `b` is a basis of `Fin 2 → K` and `f₀ ≥ f₁`, the distance of `b.toLattice` and
`(b.twist hϖ f).toLattice` is `f₀ - f₁`. -/
lemma dist_twist (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ)
    {f : Fin 2 → ℤ} (hf : Antitone f) :
    dist b.toLattice (R := R) (b.twist hϖ f).toLattice = f 0 - f 1 := by
  have hcast : f 0 - f 1 = ↑(f 0 - f 1).toNat :=
    (Int.toNat_sub_of_le <| hf (by simp)).symm
  rw [hcast, Nat.cast_inj, eq_dist_iff]
  refine ⟨ϖ, b.restrictToLattice, (b.twist hϖ f).restrictToLattice, f, hϖ, hf, ?_, hcast⟩
  intro i
  simp only [Basis.restrictToLattice_apply, Basis.twist_apply]

/-- If `b` is a basis of `Fin 2 → K` and `f₀ ≤ f₁`, the distance of `b.toLattice` and
`(b.twist hϖ f).toLattice` is `f₁ - f₀`. -/
lemma dist_twist_monotone (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ)
    {f : Fin 2 → ℤ} (hf : Monotone f) :
    dist b.toLattice (R := R) (b.twist hϖ f).toLattice = f 1 - f 0 := by
  have hcast : f 1 - f 0 = ↑(f 1 - f 0).toNat :=
    (Int.toNat_sub_of_le <| hf (by simp)).symm
  rw [hcast, Nat.cast_inj, eq_dist_iff_monotone]
  refine ⟨ϖ, b.restrictToLattice, (b.twist hϖ f).restrictToLattice, f, hϖ, hf, ?_, hcast⟩
  intro i
  simp only [Basis.restrictToLattice_apply, Basis.twist_apply]

@[simp]
lemma dist_smul_GL_eq_dist (M L : Lattice R) (g : GL (Fin 2) K) :
    dist (g • M) (g • L) = dist M L := by
  obtain ⟨ϖ, hϖ, b, f, hf, rfl, rfl, hdiff⟩ := exists_repr_dist' M L
  rw [← Basis.smulGL_toLattice, ← Basis.smulGL_toLattice, Basis.smulGL_twist,
    ← Nat.cast_inj (R := ℤ), dist_twist _ _ hf, dist_twist _ _ hf]

lemma dist_twist₂ (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n m : ℤ) :
    dist b.toLattice (R := R) (b.twist₂ hϖ n m).toLattice = |n - m| := by
  simp only [Basis.twist₂]
  symm
  by_cases h : m ≤ n
  · rw [dist_twist, abs_eq_self]
    · omega
    · intro i j hij
      aesop
  · rw [dist_twist_monotone]
    · conv_rhs => rw [← neg_sub]
      rw [abs_eq_neg_self]
      omega
    · intro i j hij
      match i, j with
      | 0, 0 => rfl
      | 0, 1 =>
        change n ≤ m
        omega
      | 1, 0 => simp at hij
      | 1, 1 => rfl

lemma dist_ntwist₂ (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    dist (b.toLattice (R := R)) (b.ntwist₂ hϖ n 0).toLattice = n := by
  simp [Basis.ntwist₂, ← Nat.cast_inj (R := ℤ), dist_twist₂]

/-- If vertices `x` and `y` have distance `n + 1`, there exists a vertex `o`
with `inv o x = 1` and `inv y o = n`.
This is the inductive step for showing that the Bruhat-Tits graph is connected
(see `BruhatTits.reachable`). -/
lemma exists_intermediate_vertex (n : ℕ) (x y : Vertices R) (h : inv x y = n + 1) :
    ∃ (o : Vertices R), inv y o = n ∧ inv o x = 1 := by
  obtain ⟨ϖ, hϖ, M', L', bM, bL, rfl, rfl, h0, h1⟩ := exists_repr_inv x y
  rw [h] at h0
  let bT := bM.fromLattice.ntwist₂ hϖ 1 0
  let T : Lattice R := bT.toLattice
  let bT' : Basis (Fin 2) R T.M := bT.restrictToLattice
  refine ⟨⟦T⟧, ?_, ?_⟩
  · rw [inv_mk, dist_symm, eq_dist_iff₂]
    refine ⟨ϖ, bT', bL, n, 0, hϖ, by simp, ?_, ?_, ?_⟩
    · simp only [h0, bT', bT]
      rw [Basis.restrictToLattice_apply, Basis.ntwist₂_apply₀, Basis.fromLattice_apply, pow_add,
        ← smul_smul, Subring.smul_def, Subring.coe_pow, zpow_natCast]
    · simp only [Fin.isValue, h1, zpow_zero, one_smul, bT', bT, T, Basis.restrictToLattice_apply]
      simp [Basis.ntwist₂_apply₁, Basis.fromLattice_apply]
    · simp
  · change dist T M' = 1
    rw [dist_symm, eq_dist_iff₂]
    refine ⟨ϖ, bM, bT', 1, 0, hϖ, by simp, ?_, ?_, ?_⟩
    · simp only [bT', bT]
      rw [Basis.restrictToLattice_apply, Basis.ntwist₂_apply₀, Basis.fromLattice_apply,
        Subring.smul_def, Subring.coe_pow, zpow_one, pow_one]
    · rw [Basis.restrictToLattice_apply]
      simp [bT, Basis.ntwist₂_apply₁, Basis.fromLattice_apply]
    · simp

/-- If two lattices have distance zero, they are equal up to a unit. -/
lemma isSimilar_of_dist_eq_zero {M L : Lattice R} (h : dist M L = 0) :
    Lattice.IsSimilar R M L := by
  obtain ⟨ϖ, hϖ, b, f, _, hM, hL, hdiff⟩ := exists_repr_dist' M L
  subst hM hL
  simp only [h, Fin.isValue, CharP.cast_eq_zero] at hdiff
  have hϖ' : ϖ.val ≠ 0 := by simpa using hϖ.ne_zero
  use (Units.mk0 ϖ.val hϖ') ^ f 0
  apply Lattice.ext
  simp only [Fin.isValue, Lattice.smul_module, Basis.toLattice_module, Basis.smul_toSubmodule]
  apply congr_arg
  ext i : 1
  have h : f 0 = f 1 := Int.eq_of_sub_eq_zero hdiff
  simp only [Fin.isValue, Basis.smul'_apply, Units.smul_def, Units.val_zpow_eq_zpow_val,
    Units.val_mk0, Basis.twist_apply]
  match i with
  | 0 => rfl
  | 1 => rw [h]

/-- Two vertices are equal if and only if their distance is zero. -/
lemma eq_iff (M L : Vertices R) : M = L ↔ inv M L = 0 := by
  constructor
  · rintro rfl
    exact inv_self M
  · refine Quotient.inductionOn₂' M L (fun M L ↦ ?_)
    intro h
    simp only [inv_mk] at h
    apply Quotient.sound
    exact isSimilar_of_dist_eq_zero h

end BruhatTits
