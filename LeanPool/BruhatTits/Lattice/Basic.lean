/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Utils.Matrix
import LeanPool.BruhatTits.Utils.Misc
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite

/-!
# Definition of lattices

Let `K` be a field and `R` a subring. Then an `R`-submodule `M` of `ι → K` is a lattice,
if `M` is finitely generated and it spans `ι → K` as a `K`-module.

If `R` is a principal ideal domain, any lattice is a free `R`-module of rank cardinality of `ι`.

-/

open Module


variable {K : Type*} [Field K] {R : Subring K}

open Pointwise

variable {ι : Type*}

/-- An `R`-submodule `M` of `ι → K` is a lattice if it is finitely generated
and spans `ι → K` as a `K`-module. -/
class IsLattice (M : Submodule R (ι → K)) : Prop where
  /-- `M` is finitely generated. -/
  isFG : M.FG
  /-- `M` spans `ι → K` -/
  spans : Submodule.span K (M : Set (ι → K)) = ⊤

namespace IsLattice

variable (M : Submodule R (ι → K)) [IsLattice M]

/-- Any `R`-lattice is finite. -/
instance finite : Module.Finite R M := by
  rw [Module.Finite.iff_fg]
  exact isFG

/-- The action of `Kˣ` on `R`-submodules of `ι → K` preserves `IsLattice`. -/
instance smul (a : Kˣ) : IsLattice (a • M) where
  isFG := by
    obtain ⟨s, hs⟩ := IsLattice.isFG (M := M)
    subst hs
    rw [Submodule.fg_def]
    refine ⟨a • (s : Set (ι → K)), ?_, ?_⟩
    · simp only [Set.finite_smul_set, Finset.finite_toSet]
    · exact (Submodule.smul_span a (s : Set (ι → K))).symm
  spans := by
    change Submodule.span K (a • (M : Set (ι → K))) = ⊤
    rw [← Submodule.smul_span, IsLattice.spans]
    ext x
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    rw [show x = a • a⁻¹ • x by simp]
    apply Submodule.smul_mem_pointwise_smul
    trivial

lemma of_le_of_isLattice [IsNoetherianRing R]
    {M L P : Submodule R (ι → K)} [IsLattice M] [IsLattice P]
    (hML : M ≤ L) (hLP : L ≤ P) : IsLattice L where
  isFG := IsLattice.isFG.of_le hLP
  spans := by
    rw [eq_top_iff, ← IsLattice.spans (M := M)]
    exact Submodule.span_mono hML

end IsLattice

variable [IsFractionRing R K]

namespace Matrix.GeneralLinearGroup

variable [Fintype ι] [DecidableEq ι]

/-- The submodule spanned by the columns of an invertible matrix is a lattice. -/
instance toSubmodule_isLattice (g : GL ι K) :
    IsLattice (R := R) g.toSubmodule where
  isFG := Submodule.fg_def.mpr ⟨Set.range (fun col row ↦ g.val row col), Set.finite_range _, rfl⟩
  spans := by
    rw [_root_.eq_top_iff]
    let b := g.toBasis
    rw [← b.span_eq]
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    erw [mem_toSubmodule]
    use Pi.single i 1
    ext
    simp [b]

instance (g : GL ι K) (M : Submodule R (ι → K)) [IsLattice M] : IsLattice (g • M) where
  isFG := by
    rw [GeneralLinearGroup.smul_def]
    apply Submodule.FG.map
    exact IsLattice.isFG
  spans := by
    rw [GeneralLinearGroup.smul_def]
    simp_rw [Submodule.map_coe, LinearMap.coe_restrictScalars, mulVecLin_apply]
    erw [Submodule.span_image g.val.mulVecLin]
    rw [IsLattice.spans]
    simp only [Submodule.map_top]
    rw [_root_.eq_top_iff]
    intro x _
    simp only [LinearMap.mem_range, mulVecLin_apply]
    use g⁻¹ *ᵥ x
    simp [mulVec_mulVec]

end Matrix.GeneralLinearGroup

namespace Module.Basis

omit [IsFractionRing (↥R) K] in
lemma top_le_submodule_span_of_isLattice {κ : Type*} [Finite κ]
    {M : Submodule R (ι → K)} (b : Basis κ R M)
    [IsLattice M] : ⊤ ≤ Submodule.span K (Set.range fun i ↦ (b i).val) := by
  letI : Fintype κ := Fintype.ofFinite κ
  rintro x -
  have hx : x ∈ Submodule.span K (M : Set (ι → K)) := by
    rw [IsLattice.spans]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro x hx
    have hv : ⟨x, hx⟩ ∈ Submodule.span R (Set.range b) := Basis.mem_span b ⟨x, hx⟩
    rw [Submodule.mem_span_range_iff_exists_fun] at hv
    obtain ⟨c, hc⟩ := hv
    apply congrArg Subtype.val at hc
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at hc
    rw [← hc]
    apply Submodule.sum_smul_mem
    intro i _
    apply Submodule.subset_span
    exact Set.mem_range_self i
  · simp
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    exact Submodule.smul_mem _ _ hx

variable [Fintype ι] [DecidableEq ι]

/-- Given an `R`-lattice `M` of `ι → K` and an `R`-basis of `M`, this basis is
also a `K` basis of `ι → K`. -/
noncomputable def ofSubmodule {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M) :
    Basis ι K (ι → K) := Basis.mk (v := fun i : ι ↦ (b i).val)
  b.linearIndependent_of_submodule
  b.top_le_submodule_span_of_isLattice

/-- Any `K`-basis of `ι → K` defines an element of `GL ι K`. -/
noncomputable def toGeneralLinearGroup (b : Basis ι K (ι → K)) : GL ι K :=
  Matrix.GeneralLinearGroup.toLin.symm <| LinearMap.GeneralLinearGroup.ofLinearEquiv <|
    Basis.equiv (Pi.basisFun K ι) b (Equiv.refl ι)

@[simp]
lemma toGeneralLinearGroup_apply (b : Basis ι K (ι → K))
    (i j : ι) : b.toGeneralLinearGroup i j = b j i := by
  simp only [toGeneralLinearGroup,
    Matrix.GeneralLinearGroup.toLinear_symm_ofLinearEquiv_apply]
  rw [← Pi.basisFun_eq_single, Basis.equiv_apply]
  simp

/-- Given an `R`-lattice `M` of `ι → K` and an `R`-basis `b` of `M`, the columns of `b`
form an invertible `K`-matrix. -/
noncomputable def toGL {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M) :
    GL ι K :=
  b.ofSubmodule.toGeneralLinearGroup

@[simp]
lemma toGL_apply {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M)
    (i j : ι) : b.toGL i j = (b j).val i := by
  simp [toGL, ofSubmodule]

@[simp]
lemma transpose_toGL {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M)
    (i : ι) : b.toGL.val.transpose i = b i := by
  ext
  simp

lemma toGL_toSubmodule {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M) :
    (Basis.toGL b).toSubmodule = M := by
  ext x
  simp only [Matrix.GeneralLinearGroup.mem_toSubmodule]
  constructor
  · rintro ⟨y, hy, rfl⟩
    let bs : Basis ι R (ι → R) := Pi.basisFun R ι
    have hym : y ∈ Submodule.span R (Set.range bs) := by simp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hym
    · intro y hym
      obtain ⟨i, rfl⟩ := hym
      convert (b i).property using 1
      ext j
      simp only [bs, Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · simp
      · intro x _ hx
        simp [Pi.single_eq_of_ne hx]
      · intro hi
        simp at hi
    · simp
    · intro y z _ _ hym hzm
      simp only [Subtype.val_comp_add, Matrix.mulVec_add]
      exact Submodule.add_mem _ hym hzm
    · intro a y _ hym
      simp only [Subtype.val_comp_smul, Matrix.mulVec_smul]
      exact Submodule.smul_mem _ a hym
  · intro hx
    rw [Basis.mem_submodule_iff' b] at hx
    obtain ⟨c, rfl⟩ := hx
    use c
    change (b.toGL).val.mulVec (fun i ↦ c i) = _
    unfold Matrix.mulVec
    unfold dotProduct
    ext j
    simp only [Basis.toGL_apply, Finset.sum_apply, Pi.smul_apply]
    congr
    ext i
    rw [mul_comm]
    rfl

end Module.Basis

section

/-!
## Lattices are free

In this section we prove that every lattice is a free `R`-module of finite rank the cardinality
of `ι` and that every such `R`-module is a lattice.
-/

variable [IsPrincipalIdealRing R] (M : Submodule R (ι → K)) [IsLattice M]

/-- Any lattice is a free `R`-module. -/
instance IsLattice.free (M : Submodule R (ι → K)) [IsLattice M] : Module.Free R M :=
  /- torsion free, finite module over a PID -/
  letI : SMul R M := M.smul
  have : NoZeroSMulDivisors R (ι → K) := by
    constructor
    intro c x hcx
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      ext i
      have hcxi : (c : K) * x i = 0 := by
        simpa [Pi.smul_apply, Subring.smul_def] using congrFun hcx i
      exact (mul_eq_zero.mp hcxi).resolve_left (fun hcK ↦ hc (Subtype.ext hcK))
  have : NoZeroSMulDivisors R M :=
    Function.Injective.noZeroSMulDivisors Subtype.val Subtype.val_injective rfl (by
      intro c x
      rfl)
  Module.free_of_finite_type_torsion_free' --inferInstance

variable [Fintype ι]

/-- Any lattice has the cardinality of `ι` as `R`-rank. -/
theorem IsLattice.rank' (M : Submodule R (ι → K)) [IsLattice M] :
    Module.rank R M = Fintype.card ι := by
  --have : Module.Free R M := IsLattice.free M
  let b := Module.Free.chooseBasis R M
  have hli : LinearIndependent K (fun i ↦ (b i).val) :=
    Basis.linearIndependent_of_submodule b
  have hsp : ⊤ ≤ Submodule.span K (Set.range <| fun i ↦ (b i).val) :=
    b.top_le_submodule_span_of_isLattice
  let b' := Basis.mk hli hsp
  rw [rank_eq_card_basis b, ← rank_eq_card_basis b', rank_fun']

/-- Any `R`-lattice has rank `k` as an `R`-module. -/
theorem IsLattice.rank {k : ℕ} (M : Submodule R (Fin k → K)) [IsLattice M] :
    Module.rank R M = k := by
  rw [IsLattice.rank' M]
  simp

/-- `FiniteDimensional.finrank` version of `IsLattice.rank`. -/
theorem IsLattice.finrank {k : ℕ} (M : Submodule R (Fin k → K)) [IsLattice M] :
    Module.finrank R M = k :=
  Module.finrank_eq_of_rank_eq (IsLattice.rank M)

/-- The supremum of two lattices is a lattice. -/
instance IsLattice.sup (M N : Submodule R (ι → K)) [IsLattice M] [IsLattice N] :
    IsLattice (M ⊔ N) where
  isFG := Submodule.FG.sup IsLattice.isFG IsLattice.isFG
  spans := by
    rw [_root_.eq_top_iff]
    trans
    · change ⊤ ≤ Submodule.span K (M : Set (ι → K))
      rw [IsLattice.spans (M := M)]
    · apply Submodule.span_mono
      simp

omit [IsPrincipalIdealRing ↥R] in
lemma Submodule.span_eq_top_of_rank {M : Submodule R (ι → K)}
    (h : Module.rank R M = Fintype.card ι) :
    Submodule.span K (M : Set (ι → K)) = ⊤ := by
  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent R M
  replace hli := hli.map' M.subtype (Submodule.ker_subtype M)
  rw [LinearIndependent.iff_fractionRing (R := R) (K := K)] at hli
  rw [h, Cardinal.mk_eq_nat_iff_fintype] at hs
  obtain ⟨hfin, hcard⟩ := hs
  have hsubset : Set.range (fun x : s ↦ x.val.val) ⊆ M := by
    rintro x ⟨a, rfl⟩
    simp
  have hcard : Fintype.card ↑s = Module.finrank K (ι → K) := by
    rw [hcard, Module.finrank_fintype_fun_eq_card K]
  rw [_root_.eq_top_iff]
  rw [← LinearIndependent.span_eq_top_of_card_eq_finrank' hli hcard]
  exact Submodule.span_mono hsubset

omit [IsPrincipalIdealRing ↥R] in
/-- An `R`-submodule of `ι → K` that is finitely generated and has rank the cardinality of `ι` is
a lattice. -/
lemma IsLattice.of_rank {M : Submodule R (ι → K)} (hfg : M.FG)
    (hr : Module.rank R M = Fintype.card ι) : IsLattice M where
  isFG := hfg
  spans := Submodule.span_eq_top_of_rank hr

omit [Fintype ι] in
/-- The intersection of two lattices is a lattice. -/
lemma IsLattice.intersection (M N : Submodule R (ι → K)) [Finite ι]
    [IsLattice M] [IsLattice N] :
    IsLattice (M ⊓ N) where
  isFG := by
    have aux : M.FG := IsLattice.isFG
    have : IsNoetherian R M := isNoetherian_of_fg_of_noetherian M aux
    have g : (M ⊓ N) ≤ M := inf_le_left
    have : IsNoetherian R ↥(M ⊓ N) := isNoetherian_of_le g
    have h: Module.Finite R ↥(M ⊓ N):= Module.IsNoetherian.finite R ↥(M ⊓ N)
    apply Module.Finite.iff_fg.mp
    exact h
  spans := by
    letI : Fintype ι := Fintype.ofFinite ι
    apply Submodule.span_eq_top_of_rank
    have h := Submodule.rank_sup_add_rank_inf_eq M N
    rw [IsLattice.rank' M, IsLattice.rank' N, IsLattice.rank'] at h
    apply Cardinal.eq_of_add_eq_add_left h
    exact Cardinal.natCast_lt_aleph0

end

namespace BruhatTits

variable (R)

/-- An `R`-lattice is a submodule `M` of `Fin 2 → K` which satisfies `IsLattice`. -/
@[ext]
structure Lattice where
  /-- The underlying submodule of a lattice. -/
  M : Submodule R (Fin 2 → K)
  isLattice : IsLattice M := by infer_instance

namespace Lattice

attribute [instance] isLattice

instance : SMul Kˣ (Lattice R) where
  smul a L := { M := a • L.M }

omit [IsFractionRing R K] in
@[simp]
lemma smul_module (a : Kˣ) (L : Lattice R) : (a • L).M = a • L.M :=
  rfl

/-- `Kˣ` acts on `R`-lattices by acting on the submodule. -/
instance : MulAction Kˣ (Lattice R) where
  one_smul L := by
    apply Lattice.ext
    simp only [smul_module, one_smul]
  mul_smul a b L := by
    apply Lattice.ext
    simp only [smul_module, mul_smul]

instance : SMul (GL (Fin 2) K) (BruhatTits.Lattice R) where
  smul g L := { M := g • L.M }

variable {R}

omit [IsFractionRing R K] in
lemma smul_M (g : GL (Fin 2) K) (L : BruhatTits.Lattice R) :
    (g • L).M = g • L.M :=
  rfl

instance : MulAction (GL (Fin 2) K) (BruhatTits.Lattice R) where
  one_smul L := by
    apply BruhatTits.Lattice.ext
    rw [smul_M, one_smul]
  mul_smul g h L := by
    apply BruhatTits.Lattice.ext
    rw [smul_M, smul_M, smul_M, mul_smul]

omit [IsFractionRing R K] in
lemma embDiagonal_smul_eq_smul (L : Lattice R) (u : Kˣ) :
    Matrix.GeneralLinearGroup.embDiagonal _ (Fin 2) u • L = u • L := by
  simp only [Matrix.GeneralLinearGroup.embDiagonal_apply]
  ext : 1
  rw [Lattice.smul_M, Matrix.GeneralLinearGroup.diagonal_smul _ _ (by tauto) 1]
  rfl

variable [IsPrincipalIdealRing R]

/-- Given a lattice, this is an arbitrary choice of a basis. -/
noncomputable def basis (L : BruhatTits.Lattice R) :
    Basis (Fin 2) R L.M :=
  Module.finBasisOfFinrankEq R L.M (IsLattice.finrank L.M)


variable (R)

/-- Two `R`-lattices `L` and `N` are similar, if `N` is a `Kˣ`-multiple of `L`. -/
def IsSimilar (L N : Lattice R) : Prop := ∃ (a : Kˣ), a • L = N

omit [IsFractionRing R K] [IsPrincipalIdealRing R]
/-- `IsSimilar` is an equivalence relation. -/
lemma _root_.BruhatTits.Lattice.IsSimilar.equivalence : Equivalence (IsSimilar R) where
  refl M := ⟨1, MulAction.one_smul M⟩
  symm {M N} h := by
    obtain ⟨a, ha⟩ := h
    use a⁻¹
    rw [← ha, inv_smul_smul]
  trans {M N P} h1 h2 := by
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    use b * a
    rw [← hb, ← ha, mul_smul]

lemma isSimilar_smul (L : Lattice R) (a : Kˣ) : IsSimilar R L (a • L) := ⟨a, rfl⟩

lemma smul_isSimilar (L : Lattice R) (a : Kˣ) : IsSimilar R (a • L) L := by
  apply (IsSimilar.equivalence R).symm
  apply isSimilar_smul

instance _root_.BruhatTits.Lattice.IsSimilar.setoid : Setoid (Lattice R) where
  r := IsSimilar R
  iseqv := IsSimilar.equivalence R

end Lattice

end BruhatTits
