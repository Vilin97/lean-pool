/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Graph.Vertices
import LeanPool.BruhatTits.Lattice.Quotient
import LeanPool.BruhatTits.Utils.GLSubmoduleAction
import LeanPool.BruhatTits.Utils.List

open Module

/-!
# The edges of the Bruhat-Tits graph

In this file we define the edge relation of the Bruhat-Tits graph. Two vertices
are connected by an edge if they are neighbours, i.e. if their distance, in the
sense of `inv`, is one.

## Main definitions

- `BruhatTits.IsNeighbour`: vertices `x` and `y` are neighbours if `inv x y = 1`.
- `BruhatTits.IsStandardNeighbour`: lattices `L` and `M` are standard neighbours, if
  `ϖ • L < M < L`.
- `List.IsBTChain`: a non-empty list of lattices is a chain, if adjacent elements are standard
  neighbours.
- `List.IsBTSimpleChain`: a chain is simple if it does not backtrack.
- `List.IsBTStandard`: a simple chain `L₀, ..., Lₙ` is standard if there exists a basis
  `b = (b₁, b₂)` of `L₀` such that `Lᵢ` is the span of `(ϖ ^ i • b₁, b₂)` for all `i`.

## Main results

- `BruhatTits.isNeighbour_iff`: vertices are neighbours if and only if there exist standard
  neighbour representatives.
- `BruhatTits.length_eq_dist_add_one_of_isStandard`: the length of a standard chain agrees with
  the distance of its endpoints plus one.
- `BruhatTits.exists_trafo_to_isStandard`: every simple chain can be transformed into a standard
  chain by the action of `GL₂(K)`.

-/

suppress_compilation

variable {K : Type*} [Field K] {R : Subring K}

namespace BruhatTits

open Pointwise

section «IsNeighbour»

variable [IsDiscreteValuationRing R] [IsFractionRing R K]

/-- Two vertices `x` and `y` in the Bruhat-Tits tree are neighbours if `inv L M = 1`.
For a common alternative definition see `BruhatTits.isNeighbour_iff`. -/
def IsNeighbour (x y : Vertices R) : Prop := inv x y = 1

lemma isNeighbour_def (x y : Vertices R) :
    IsNeighbour x y ↔ inv x y = 1 :=
  Iff.rfl

/-- If `M` is a lattice and `x` a neighbour of `⟦M⟧`, there exists a representative
`L` of `x` such that `L ≤ M` and `dist M L = 1`. -/
lemma exists_repr_le_of_isNeighbour (M : Lattice R) (x : Vertices R)
    (h : IsNeighbour ⟦M⟧ x) :
    ∃ (L : Lattice R), ⟦L⟧ = x ∧ L.M ≤ M.M ∧ dist M L = 1 := by
  classical
  obtain ⟨ϖ, hϖ, b, hM, hL⟩ := exists_repr_inv'_of_fixed M x
  refine ⟨(b.ntwist₂ hϖ (inv ⟦M⟧ x) 0).toLattice, hL, ?_, ?_⟩
  · rw [← hM, Basis.toLattice_module]
    apply b.ntwist₂_toSubmodule_le
  · rw [isNeighbour_def] at h
    rw [h, ← hM, Basis.ntwist₂, Nat.cast_one, CharP.cast_eq_zero, ← Nat.cast_inj (R := ℤ),
      dist_twist₂ b hϖ]
    simp

lemma isNeighbour_symm (x y : Vertices R) :
    IsNeighbour x y ↔ IsNeighbour y x := by
  classical
  rw [isNeighbour_def, isNeighbour_def, inv_symm]

end «IsNeighbour»

section «StandardNeighbour»

/-- `M` is a standard neighbour of `L` if `ϖ • L < M < L`. -/
structure IsStandardNeighbour (M L : Lattice R) : Prop where
  lt : M.M < L.M
  ϖlt : ∀ (ϖ : R) (_ : Irreducible ϖ), ϖ • L.M < M.M

/-- `GL₂(K)` preserves `IsStandardNeighbour`. -/
lemma smul_isStandardNeighbour (g : GL (Fin 2) K) (M L : Lattice R) (h : IsStandardNeighbour M L) :
    IsStandardNeighbour (g • M) (g • L) where
  lt := by
    rw [Lattice.smul_M, Lattice.smul_M, smul_lt_iff]
    exact h.lt
  ϖlt ϖ hϖ := by
    rw [Lattice.smul_M, Lattice.smul_M]
    change (ϖ.val : K) • (g • L.M) < g • M.M
    rw [scalar_smul_GL_smul, smul_lt_iff]
    exact h.ϖlt ϖ hϖ

variable [IsDiscreteValuationRing R]

/-- If `b = (b₁, b₂)` is a basis of `Fin 2 → K`, the span of `(ϖ • b₁, b₂)` is a standard neighbour
of the span of `b`. -/
lemma ntwist_isStandardNeighbour (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ) :
    IsStandardNeighbour (b.ntwist₂ hϖ 1 0).toLattice (b.toLattice (R := R)) where
  lt := by
    simp only [Basis.toLattice_module]
    nth_rw 2 [← b.twist_zero hϖ]
    rw [Module.Basis.ntwist₂, Module.Basis.twist₂]
    rw [b.twist_lt_twist_iff]
    constructor
    · intro i
      match i with
      | 0 => simp
      | 1 => simp
    · use 0
      simp
  ϖlt := by
    intro ϖ' hϖ'
    rw [← maximalIdeal_smul_eq_uniformizer_smul _ hϖ', maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
    simp only [Basis.toLattice_module]
    nth_rw 1 [← b.twist_zero hϖ]
    rw [b.smul_twist]
    rw [Module.Basis.ntwist₂, Module.Basis.twist₂]
    rw [b.twist_lt_twist_iff]
    constructor
    · intro i
      match i with
      | 0 => simp
      | 1 => simp
    · use 1
      simp

variable [IsFractionRing R K]

/-- If `M` is a standard neighbour of `L`, the vertices `⟦M⟧` and `⟦L⟧` are neighbours. -/
lemma isNeighbour_of_isStandardNeighbour {M L : Lattice R} (h : IsStandardNeighbour M L) :
    IsNeighbour ⟦M⟧ ⟦L⟧ := by
  classical
  obtain ⟨ϖ, hϖ, b, f, hf, rfl, rfl, hdiff⟩ := exists_repr_dist' L M
  have h1 := h.lt
  simp only [Basis.toLattice_module] at h1
  nth_rw 2 [← b.twist_zero hϖ] at h1
  rw [b.twist_lt_twist_iff] at h1
  have h2 := h.ϖlt ϖ hϖ
  simp only [Basis.toLattice_module] at h2
  nth_rw 1 [← b.twist_zero hϖ] at h2
  rw [b.smul_twist] at h2
  rw [b.twist_lt_twist_iff] at h2
  simp at h2 h1
  have h3 : f 1 ≤ f 0 := by
    apply hf
    simp
  have : 0 ≤ f 1 := h1.left 1
  have : 0 ≤ f 0 := h1.left 0
  have : f 0 ≤ 1 := h2.left 0
  have : f 1 ≤ 1 := h2.left 1
  have : f 1 = 0 ∧ f 0 = 1 := by
    omega
  rw [this.left, this.right] at hdiff
  simp at hdiff
  change dist _ _ = 1
  rw [dist_symm]
  omega

lemma exists_basis_eq_ntwist_of_isNeighbour (M : Lattice R) (L : Vertices R)
    (h : IsNeighbour ⟦M⟧ L) :
    ∃ (b : Basis (Fin 2) K (Fin 2 → K)) (ϖ : R) (hϖ : Irreducible ϖ),
    b.toLattice = M ∧ ⟦(b.ntwist₂ hϖ 1 0).toLattice⟧ = L := by
  classical
  obtain ⟨ϖ, hϖ, b, rfl, h1⟩ := exists_repr_inv'_of_fixed M L
  have : inv _ _ = 1 := h
  rw [this] at h1
  use b, ϖ, hϖ

/-- If `M` is a lattice with neighbour `x`, there exists a representative `L` of `x` such that
`L` is a standard neighbour of `M`. -/
lemma exists_repr_isStandardNeighbour_of_isNeighbour (M : Lattice R) (x : Vertices R)
    (h : IsNeighbour ⟦M⟧ x) :
    ∃ (L : Lattice R), ⟦L⟧ = x ∧ IsStandardNeighbour L M := by
  obtain ⟨b, ϖ, hϖ, rfl, h1⟩ := exists_basis_eq_ntwist_of_isNeighbour M x h
  refine ⟨(b.ntwist₂ hϖ 1 0).toLattice (R := R), h1, ntwist_isStandardNeighbour b hϖ⟩

/--
Two vertices are neighbours if and only if there exist representatives L and M and a uniformizer ϖ
such that ϖ • L < M < L, i.e. if `L` is a standard neighbour of `M`.

This is a common alternative way of defining `BruhatTits.IsNeighbour`.
-/
theorem isNeighbour_iff (L M : Vertices R) :
    IsNeighbour L M ↔ ∃ (ϖ : R) (_ : Irreducible ϖ) (L' M' : Lattice R),
      ⟦L'⟧ = L ∧ ⟦M'⟧ = M ∧ ϖ • L'.M < M'.M ∧ M'.M < L'.M := by
  constructor
  · refine Quotient.inductionOn L (fun L h ↦ ?_)
    obtain ⟨M', hM, hstd⟩ := exists_repr_isStandardNeighbour_of_isNeighbour L M h
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    exact ⟨ϖ, hϖ, L, M', rfl, hM, hstd.ϖlt ϖ hϖ, hstd.lt⟩
  · intro ⟨ϖ, hϖ, L', M', hL, hM, hϖlt, hlt⟩
    have hstd : IsStandardNeighbour M' L' := {
      lt := hlt
      ϖlt := by
        intro ϖ' hϖ'
        rw [← maximalIdeal_smul_eq_uniformizer_smul _ hϖ',
          maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
        exact hϖlt
    }
    rw [← hL, ← hM, isNeighbour_symm]
    exact isNeighbour_of_isStandardNeighbour hstd

end «StandardNeighbour»

open IsLocalRing

section «Chain»

/-- A list `(Lᵢ)` of lattices is a chain, if `Lᵢ ≤ Lᵢ₊₁` and `dist Lᵢ Lᵢ₊₁ = 1` forall i. -/
structure _root_.List.IsBTChain (l : List (Lattice R)) : Prop where
  ne_nil : l ≠ []
  isStandardNeighbour : l.IsChain IsStandardNeighbour

lemma singleton_isChain (L : Lattice R) : [L].IsBTChain where
  ne_nil := by simp
  isStandardNeighbour := List.isChain_singleton L

lemma cons_isChain_of {l : List (Lattice R)} {M L : Lattice R} (hl : (L :: l).IsBTChain)
    (hML : IsStandardNeighbour M L) : (M :: L :: l).IsBTChain where
  ne_nil := by simp
  isStandardNeighbour := by
    rw [List.isChain_cons_cons]
    exact ⟨hML, hl.isStandardNeighbour⟩

lemma isChain_of_cons_isChain {l : List (Lattice R)} {M : Lattice R} (hl : l ≠ [])
    (h : (M :: l).IsBTChain) : l.IsBTChain where
  ne_nil := hl
  isStandardNeighbour := h.isStandardNeighbour.tail

/-- A chain is simple if it does not backtrack in the interior (i.e. in principle
first and last entry can coincide). We will show that every chain is simple. -/
structure _root_.List.IsBTSimpleChain (l : List (Lattice R)) : Prop extends List.IsBTChain l where
  no_backtrack :
    (List.zipWith₃ (fun L₁ _ L₃ ↦ ¬ Lattice.IsSimilar R L₁ L₃) l l.tail l.tail.tail).Forall id

lemma singleton_isSimpleChain (L : Lattice R) : [L].IsBTSimpleChain where
  toIsBTChain := singleton_isChain L
  no_backtrack := by simp [List.zipWith₃]

lemma isSimpleChain_of_cons_isSimpleChain {l : List (Lattice R)} {M : Lattice R}
    (hl : l ≠ [])
    (h : (M :: l).IsBTSimpleChain) : l.IsBTSimpleChain where
  toIsBTChain := isChain_of_cons_isChain hl h.toIsBTChain
  no_backtrack := by
    match l with
    | [_] => simp [List.zipWith₃]
    | L₁ :: L₂ :: l =>
    have := h.no_backtrack
    simp [List.zipWith₃] at this
    simp only [List.tail_cons]
    exact this.right

/-- A chain `(Lᵢ)` is a standard chain, if `L₀` has a basis `b` such that
each `Lᵢ` is given by `b.ntwist₂ hϖ n 0`. -/
structure _root_.List.IsBTStandard (l : List (Lattice R)) : Prop
    extends List.IsBTSimpleChain l where
  exists_basis : ∃ (b : Basis (Fin 2) K (Fin 2 → K)) (ϖ : R) (hϖ : Irreducible ϖ),
    l.zipIdx.Forall (fun (L, n) ↦ L = (b.ntwist₂ hϖ (l.length - n - 1) 0).toLattice)

instance : SMul (GL (Fin 2) K) (List (Lattice R)) where
  smul g l := l.map (fun L ↦ g • L)

lemma _root_.List.smul_lattice_def (g : GL (Fin 2) K) (l : List (Lattice R)) :
    g • l = l.map (fun L ↦ g • L) :=
  rfl

@[simp]
lemma _root_.List.smul_lattice_length (g : GL (Fin 2) K) (l : List (Lattice R)) :
    (g • l).length = l.length := by
  simp [l.smul_lattice_def]


/-- `GL₂(K)` preserves `IsSimilar`. -/
lemma smul_isSimilar_iff (g : GL (Fin 2) K) (M L : Lattice R) :
    Lattice.IsSimilar R (g • M) (g • L) ↔ Lattice.IsSimilar R M L := by
  rw [Lattice.IsSimilar, Lattice.IsSimilar]
  constructor
  · intro ⟨a, ha⟩
    use a
    apply_fun Lattice.M at ha
    rw [Lattice.smul_M] at ha
    change a • (g • M).M = g • L.M at ha
    rw [Lattice.smul_M] at ha
    apply Lattice.ext
    change a • M.M = L.M
    rw [Units.smul_def] at ha ⊢
    rw [scalar_smul_GL_smul] at ha
    rw [smul_eq_iff] at ha
    assumption
  · intro ⟨a, ha⟩
    use a
    apply Lattice.ext
    have hM : ↑a • M.M = L.M := by
      simpa only [Lattice.smul_module] using congrArg Lattice.M ha
    rw [Lattice.smul_module, Lattice.smul_M, Units.smul_def, scalar_smul_GL_smul,
      Lattice.smul_M]
    exact congrArg (fun S : Submodule R (Fin 2 → K) => g • S) hM

/-- `GL₂(K)` preserves `IsBTSimpleChain`. -/
lemma smul_isChain (g : GL (Fin 2) K) {l : List (Lattice R)} (hl : l.IsBTSimpleChain) :
    (g • l).IsBTSimpleChain where
  ne_nil := by
    rw [List.smul_lattice_def]
    simpa using hl.ne_nil
  isStandardNeighbour := by
    rw [List.smul_lattice_def]
    exact List.isChain_map_of_isChain (fun L ↦ g • L)
      (fun M L hML ↦ smul_isStandardNeighbour g M L hML) hl.isStandardNeighbour
  no_backtrack := by
    rw [List.smul_lattice_def]
    repeat rw [← List.map_tail]
    rw [List.zipWith₃_map]
    simp_rw [smul_isSimilar_iff]
    exact hl.no_backtrack

variable [IsDiscreteValuationRing R] [IsFractionRing R K]

/-- If `L₀, ..., Lₙ` is a standard chain of length `n + 1`, `dist L₀ Lₙ = n`. -/
lemma length_eq_dist_add_one_of_isStandard {l : List (Lattice R)} (hl : l.IsBTStandard) :
    l.length = dist (l.head hl.ne_nil) (l.getLast hl.ne_nil) + 1 := by
  classical
  obtain ⟨b, ϖ, hϖ, h⟩ := hl.exists_basis
  rw [List.forall_iff_forall_mem] at h
  rw [List.forall_mem_zipIdx'] at h
  have hlen : 0 < l.length := List.length_pos_of_ne_nil hl.ne_nil
  have h1 : l.head hl.ne_nil = (b.ntwist₂ hϖ (l.length - 1) 0).toLattice := by
    simpa [List.head_eq_getElem_zero hl.ne_nil] using h 0 hlen
  have h2 : l.getLast hl.ne_nil = (b.ntwist₂ hϖ 0 0).toLattice := by
    have hlast_lt : l.length - 1 < l.length := Nat.sub_one_lt_of_lt hlen
    have hlast := h (l.length - 1) hlast_lt
    have hsub : l.length - (l.length - 1) - 1 = 0 := by omega
    simpa [List.getLast_eq_getElem, hsub] using hlast
  rw [h1, h2, Basis.ntwist₂_zero_zero]
  rw [dist_symm, dist_ntwist₂]
  have : 1 ≤ l.length := by
    match l with | (_ :: l) => simp
  omega

end «Chain»

section «TrafoStandard»

/-!
### Transformation of a simple chain to a standard chain

In this section we show that every simple chain can be transformed under `GL₂(K)` to a standard
chain. This is done by induction on the length of the chain.
-/

variable [IsDiscreteValuationRing R] [IsFractionRing R K]

/-- If `M` is a lattice, `b = (b₁, b₂)` a basis of `K^2` and `M` is a standard
neighbour of `b.toLattice`, there exists `g : GL₂(K)` preserving `b.toLattice` and
transforming `M` into the span of `(ϖ • b₁, b₂)`. -/
lemma exists_trafo_step_one (M : Lattice R) (b : Basis (Fin 2) K (Fin 2 → K))
    {ϖ : R} (hϖ : Irreducible ϖ)
    (h1 : M.M < b.toSubmodule)
    (h2 : ϖ • b.toSubmodule < M.M) :
    ∃ (g : GL (Fin 2) K),
        g • M = (b.ntwist₂ hϖ 1 0).toLattice ∧ g • b.toLattice (R := R) = b.toLattice := by
  let L : Lattice R := b.toLattice
  let κ := ResidueField R
  let bQ : Basis (Fin 2) κ L.quotient := b.toQuotient'
  let T : Lattice R := (b.ntwist₂ hϖ 1 0).toLattice
  let T' : Submodule κ L.quotient := L.mapIntermediate T
  have hT' : T' = Submodule.span κ { bQ 1 } :=
    mapIntermediate_stdLine₀ b hϖ
  by_cases h : M.M = (b.ntwist₂ hϖ 0 1).toSubmodule
  · refine ⟨b.swapMatrix, ?_, ?_⟩
    · apply Lattice.ext
      simp [Lattice.smul_M, h, b.swapMatrix_smul_ntwist₂]
    · apply Lattice.ext
      rw [Lattice.smul_M]
      nth_rw 2 [← b.ntwist₂_zero_zero hϖ]
      simp only [Basis.toLattice_module, b.swapMatrix_smul_ntwist₂]
      rw [b.ntwist₂_zero_zero hϖ]
  · obtain ⟨α, hα⟩ := Lattice.mapIntermediate_eq_span'' b M hϖ h1 h2 h
    use b.unipotent (-α)
    have huniL : b.unipotent (-α) • L.M = L.M := by
      simp only [Basis.toLattice_module, L]
      have : -α = ϖ ^ 0 * (-α) := by simp
      nth_rw 2 [← b.ntwist₂_zero_zero hϖ]
      nth_rw 3 [← b.ntwist₂_zero_zero hϖ]
      rw [this]
      apply unipotent_pow_irred_smul_eq_submodule
      simp
    refine ⟨?_, ?_⟩
    · apply L.mapIntermediate_inj_of
      · rw [Lattice.smul_M]
        exact le_trans (smul_GL_mono _ (le_of_lt h1)) (le_of_eq huniL)
      · rw [Lattice.smul_M, ← huniL, maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
        change (ϖ.val : K) • (b.unipotent (-α) • L.M) ≤ b.unipotent (-α) • M.M
        rw [scalar_smul_GL_smul]
        exact smul_GL_mono _ (le_of_lt h2)
      · apply Basis.ntwist₂_toSubmodule_le
      · simp only [maximalIdeal_smul_eq_uniformizer_smul _ hϖ, Basis.toLattice_module, L]
        conv_lhs => rw [← b.ntwist₂_zero_zero hϖ]
        rw [b.smul_ntwist₂]
        apply b.ntwist₂_toSubmodule_le_ntwist₂_toSubmodule
        · simp
        · simp
      · rw [mapIntermediate_unipotent_smul]
        change Submodule.map (b.unipotentResidue (-α)).toLinearMap (b.toLattice.mapIntermediate M) =
          b.toLattice.mapIntermediate T
        rw [hα, LinearMap.map_span, Set.image_singleton, map_add]
        simp [Basis.unipotentResidue_apply₀, Basis.unipotentResidue_apply₁]
        simpa using hT'.symm
    · apply Lattice.ext
      rwa [Lattice.smul_M]

/--
Core of induction step in `Lattice.exists_GL_smul_eq_ntwist₂_of_isSimpleChain_cons`:

If `M` is a lattice and `b` a basis of `K^2` such that
- `M` is a standard neighbour of the lattice spanned by `(ϖ ^ (n + 1) • b₁, b₂)`, and
- `M` is not equal to the lattice spanned by `(ϖ ^ n • b₁, b₂)`, then
there exists a unipotent matrix transforming `M` to `(ϖ ^ (n + 2) • b₁, b₂)`.

In more geometric terms, when we later apply this to a walk in the Bruhat-Tits graph,
the second condition requires the walk to not backtrack, i.e. to be a trail.
-/
lemma _root_.BruhatTits.IsStandardNeighbour.exists_unipotent_smul_eq_ntwist₂
    {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ)
    (M : Lattice R) (b : Basis (Fin 2) K (Fin 2 → K))
    (h : IsStandardNeighbour M (b.ntwist₂ hϖ (n + 1) 0).toLattice)
    (hne : ϖ • (b.ntwist₂ hϖ n 0).toSubmodule ≠ M.M) :
    ∃ (x : R), b.unipotent (ϖ ^ (n + 1) * x) • M = (b.ntwist₂ hϖ (n + 2) 0).toLattice := by
  let L : Lattice R := (b.ntwist₂ hϖ (n + 1) 0).toLattice
  let κ := ResidueField R
  let M' : Submodule κ L.quotient := L.mapIntermediate M
  let ϖL' : Submodule κ L.quotient :=
    L.mapIntermediate (b.ntwist₂ hϖ (n + 1) 1).toLattice
  have : M' ≠ ϖL' := by
    intro heq
    apply hne
    have : (b.ntwist₂ hϖ (n + 1) 1).toLattice = M := by
      refine L.mapIntermediate_inj_of _ _ ?_ ?_ (le_of_lt h.1) ?_ heq.symm
      · simp only [Basis.toLattice_module, L]
        exact b.ntwist₂_toSubmodule_le_ntwist₂_toSubmodule _ le_rfl zero_le_one
      · simp only [maximalIdeal_smul_eq_uniformizer_smul _ hϖ, Basis.toLattice_module, L,
          b.smul_ntwist₂]
        exact b.ntwist₂_toSubmodule_le_ntwist₂_toSubmodule _ (Nat.le_succ _) le_rfl
      · rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
        exact le_of_lt (h.2 _ hϖ)
    simp only [← this, Basis.toLattice_module, b.smul_ntwist₂]
  have hT : L.mapIntermediate ((b.ntwist₂ hϖ (n + 2) 0).toLattice (R := R)) =
      Submodule.span κ { (b.ntwist₂ hϖ (n + 1) 0).toQuotient' (R := R) 1 } := by
    have : b.ntwist₂ hϖ (n + 2) 0 = (b.ntwist₂ hϖ (n + 1) 0).ntwist₂ hϖ 1 0 := by
      rw [b.ntwist₂_ntwist₂]
    rw [this]
    apply mapIntermediate_stdLine₀ (b.ntwist₂ hϖ (n + 1) 0) hϖ
  have ha : ∃ (α : R),
      M' = Submodule.span κ { α • (b.ntwist₂ hϖ (n + 1) 0).toQuotient' (R := R) 0 +
        (b.ntwist₂ hϖ (n + 1) 0).toQuotient' (R := R) 1 } := by
    refine Lattice.mapIntermediate_eq_span'' _ _ hϖ h.1 (h.2 _ hϖ) fun heq ↦ hne ?_
    rw [b.smul_ntwist₂]
    rw [b.ntwist₂_ntwist₂] at heq
    exact heq.symm
  obtain ⟨α, ha⟩ := ha
  use (- α)
  have huniL : b.unipotent (ϖ ^ (n + 1) * (- α)) • L.M = L.M := by
    simp only [L]
    apply unipotent_pow_irred_smul_eq_submodule
    simp
  apply L.mapIntermediate_inj_of
  · rw [← huniL]
    exact smul_GL_mono _ (le_of_lt h.1)
  · rw [Lattice.smul_M, ← huniL, maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
    change (ϖ.val : K) • (b.unipotent (ϖ ^ (n + 1) * (-α)) • L.M) ≤
      b.unipotent (ϖ ^ (n + 1) * (-α)) • M.M
    rw [scalar_smul_GL_smul]
    exact smul_GL_mono _ (le_of_lt <| h.2 _ hϖ)
  · simp only [Basis.toLattice_module]
    apply b.ntwist₂_toSubmodule_le_ntwist₂_toSubmodule _ (by simp) le_rfl
  · rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
    simp only [Basis.toLattice_module, L, b.smul_ntwist₂]
    exact b.ntwist₂_toSubmodule_le_ntwist₂_toSubmodule _ le_rfl zero_le_one
  · rw [mapIntermediate_unipotent_smul']
    change Submodule.map _ M' = _
    rw [ha, LinearMap.map_span, Set.image_singleton, map_add]
    erw [LinearMap.CompatibleSMul.map_smul]
    simp only [LinearEquiv.coe_coe]
    rw [Basis.unipotentResidue_apply₀]
    rw [Basis.unipotentResidue_apply₁]
    simp
    simpa using hT.symm

/--
Core of lemma 2.2 in Casselman: If `M :: l` is a simple chain of lattices and `b` a basis of `K^2`
such that `l` is a standard chain defined by `b`, then there exists `x : R` such that the upper
unipotent matrix defined by `x` transforms `M` into the lattice spanned by
`(ϖ ^ (l.length - 1) • b₁, b₂)`.

We don't yet show that this transformation does not change the entries in `l`, see
`Lattice.exists_forall_GL_smul_eq_ntwist₂_of_isSimpleChain_cons` for the full result.

Implementation detail: We require that the `n`-th entry of `l` equals the lattice generated by
`(ϖ ^ (l.length - n - 1) • b₁, b₂)` and not `(ϖ ^ n • b₁, b₂)`, because it is easier
to work with `M :: l` than with `l ++ [M]`.
-/
lemma _root_.BruhatTits.Lattice.exists_GL_smul_eq_ntwist₂_of_isSimpleChain_cons
    (l : List (Lattice R))
    (hlen : 2 ≤ l.length) (M : Lattice R) (hMl : (M :: l).IsBTSimpleChain)
    (b : Basis (Fin 2) K (Fin 2 → K)) (ϖ : R) (hϖ : Irreducible ϖ)
    (hl : l.zipIdx.Forall (fun (L, n) ↦ L = (b.ntwist₂ hϖ (l.length - n - 1) 0).toLattice)) :
    ∃ (x : R), b.unipotent (ϖ ^ (l.length - 1) * x) • M =
      (b.ntwist₂ hϖ l.length 0).toLattice := by
  have h1 : l.length - 1 = l.length - 2 + 1 := by omega
  have h2 : l.length = l.length - 2 + 2 := by omega
  rw [h1, h2]
  dsimp at hl
  match l with
  | (L₁ :: L₂ :: l) =>
  simp at hl
  have hstd : IsStandardNeighbour M (b.ntwist₂ hϖ (l.length + 1) 0).toLattice := by
    rw [← hl.left]
    exact hMl.isStandardNeighbour.rel_head
  refine hstd.exists_unipotent_smul_eq_ntwist₂ hϖ l.length M b fun heq ↦ ?_
  have hϖ' : ϖ.val ≠ 0 := by simpa using hϖ.ne_zero
  have : (Units.mk0 ϖ.val hϖ') • L₂ = M := by
    rw [hl.right.left]
    apply Lattice.ext
    simpa [Units.smul_def]
  have hsim : Lattice.IsSimilar R L₂ M := ⟨(Units.mk0 ϖ.val hϖ'), this⟩
  have := hMl.no_backtrack
  simp only [List.tail_cons, List.zipWith₃, List.forall_cons, id_eq] at this
  exact this.left <| (Lattice.IsSimilar.equivalence R).symm hsim

/--
Lemma 2.2 in Casselman and the induction step of `exists_trafo_to_isStandard` (used via:
`IsBTSimpleChain.exists_GL_forall_smul`):

If `M :: l` is a simple chain of lattices and `b` a basis of `K^2`
such that `l` is a standard chain defined by `b`, then there exists `g : GL₂(K)`
such that `g • M :: g • l` is a standard chain defined by `b`.

Implementation detail: We require that the `n`-th entry of `l` equals the lattice generated by
`(ϖ ^ (l.length - n - 1) • b₁, b₂)` and not `(ϖ ^ n • b₁, b₂)`, because it is easier
to work with `M :: l` than with `l ++ [M]`.
-/
lemma _root_.BruhatTits.Lattice.exists_GL_forall_smul_eq_ntwist₂_of_isSimpleChain_cons
    (l : List (Lattice R)) (M : Lattice R) (hMl : (M :: l).IsBTSimpleChain)
    (b : Basis (Fin 2) K (Fin 2 → K)) (ϖ : R) (hϖ : Irreducible ϖ)
    (hl : l.zipIdx.Forall (fun (L, n) ↦ L = (b.ntwist₂ hϖ (l.length - n - 1) 0).toLattice)) :
    ∃ (g : GL (Fin 2) K), (M :: l).zipIdx.Forall
      (fun (L, n) ↦ g • L = (b.ntwist₂ hϖ (l.length - n) 0).toLattice) := by
  match l with
  | [] =>
    simp only [List.length_nil]
    apply MulAction.IsPretransitive.exists_smul_eq
  | [L] =>
    simp only [List.length_cons, List.length_nil, zero_add, List.zipIdx_cons, Nat.reduceAdd,
      List.zipIdx_nil, List.Forall, tsub_zero, tsub_self]
    simp only [List.length_cons, List.length_nil, zero_add, tsub_le_iff_right,
      le_add_iff_nonneg_right, zero_le, Nat.sub_eq_zero_of_le, List.zipIdx_cons, List.zipIdx_nil,
      List.forall_cons, List.Forall, and_true] at hl
    rw [hl]
    have : b.ntwist₂ hϖ 0 0 = b := by
      ext i
      fin_cases i <;> simp
    rw [this]
    have hbLM : b.toSubmodule = L.M := by simp [hl, this]
    have hstd : IsStandardNeighbour M L := List.isChain_pair.mp hMl.isStandardNeighbour
    apply exists_trafo_step_one
    · rw [hbLM]
      exact hstd.lt
    · rw [hbLM]
      exact hstd.ϖlt ϖ hϖ
  | L₁ :: L₂ :: l' =>
    generalize hldef : L₁ :: L₂ :: l' = l at *
    have hlen : 2 ≤ l.length := by simp [← hldef]
    obtain ⟨x, h⟩ := M.exists_GL_smul_eq_ntwist₂_of_isSimpleChain_cons l hlen hMl b ϖ hϖ hl
    use b.unipotent (ϖ ^ (l.length - 1) * x)
    simp only [List.zipIdx_cons, zero_add, List.forall_cons, tsub_zero]
    refine ⟨h, ?_⟩
    dsimp only at hl
    rw [show 1 = 1 + 0 by simp, ← List.map_snd_add_zipIdx_eq_zipIdx]
    simp only [add_zero, List.forall_map_iff]
    change List.Forall (fun (L, n) ↦ b.unipotent (ϖ ^ (l.length - 1) * x) • L =
      (b.ntwist₂ hϖ (l.length - (n + 1)) 0).toLattice) l.zipIdx
    rw [List.forall_iff_forall_mem] at hl ⊢
    intro ⟨L, n⟩ h
    have : l.length - (n + 1) = l.length - n - 1 := by omega
    replace hl := hl (L, n) h
    dsimp only at hl ⊢
    rw [this, hl]
    apply unipotent_pow_irred_smul_eq
    omega

/-- (Implementation detail) Intermediate lemma for `exists_trafo_to_isStandard`, more adapted
to induction. -/
lemma _root_.List.IsBTSimpleChain.exists_GL_forall_smul (l : List (Lattice R))
    (hl : l.IsBTSimpleChain) :
    ∃ (g : GL (Fin 2) K) (b : Basis (Fin 2) K (Fin 2 → K)) (ϖ : R) (hϖ : Irreducible ϖ),
    l.zipIdx.Forall (fun (L, n) ↦ g • L = (b.ntwist₂ hϖ (l.length - n - 1) 0).toLattice) := by
  match l with
  | [] =>
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    refine ⟨1, Pi.basisFun K (Fin 2), ϖ, hϖ, by simp⟩
  | [M] =>
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    use 1, M.basis.fromLattice, ϖ, hϖ
    simp [Basis.ntwist₂_zero_zero]
  | (M :: L :: l') =>
    generalize hldef : L :: l' = l at *
    have : l ≠ [] := by simp [← hldef]
    have hl' : l.IsBTSimpleChain := isSimpleChain_of_cons_isSimpleChain this hl
    obtain ⟨g, b, ϖ, hϖ, h⟩ := hl'.exists_GL_forall_smul l
    obtain ⟨g', hg'⟩ := by
      refine (g • M).exists_GL_forall_smul_eq_ntwist₂_of_isSimpleChain_cons (g • l) ?_ b ϖ hϖ ?_
      · exact smul_isChain g hl
      · simpa [List.smul_lattice_def, List.length_map, ← List.map_zipIdx]
    use g' * g, b, ϖ, hϖ
    simp only [List.smul_lattice_length, List.zipIdx_cons, zero_add, List.forall_cons, tsub_zero,
      List.length_cons, add_tsub_cancel_right] at hg' ⊢
    simp_rw [mul_smul]
    refine ⟨?_, ?_⟩
    · exact hg'.left
    · rw [List.smul_lattice_def, ← List.map_zipIdx, List.forall_map_iff] at hg'
      convert hg'.right with ⟨L, n⟩
      have : l.length + 1 - n - 1 = l.length - n := by omega
      simp [this]

/--
Any simple chain of lattices can be transformed by an element of `GL₂(K)` to a standard
chain, i.e. up to a change of coordinates is every simple chain a standard chain.
This is later used to show acyclicity of the Bruhat-Tits graph.

Prop. 2.1 in Casselman.
-/
lemma exists_trafo_to_isStandard (l : List (Lattice R)) (hl : l.IsBTSimpleChain) :
    ∃ (g : GL (Fin 2) K), (g • l).IsBTStandard := by
  obtain ⟨g, b, ϖ, hϖ, h⟩ := hl.exists_GL_forall_smul l
  refine ⟨g, ⟨smul_isChain g hl, ⟨b, ϖ, hϖ, ?_⟩⟩⟩
  rw [List.smul_lattice_def, List.zipIdx_map]
  simpa

end «TrafoStandard»

end BruhatTits
