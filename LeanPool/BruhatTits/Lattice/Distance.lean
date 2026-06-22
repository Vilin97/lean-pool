/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Cartan.Uniqueness
import LeanPool.BruhatTits.Lattice.Basic
import LeanPool.BruhatTits.Utils.Matrix

/-!
# Distance on lattices and vertices

In this file we define the distance function `dist` on lattices. For this
we apply the Cartan decomposition to bring every pair of lattices `M` and `L` into a
standard form:

There exists a basis `bM` of `M` and a basis `bL` of `L` such that `bLᵢ = ϖ ^ fᵢ • bMᵢ` for
`i = 1,2` and integers `fᵢ`. If we fix the order of `fᵢ` to be `f₁ ≥ f₂`, the `fᵢ` are unique,
i.e. don't depend on `ϖ`, `bM` or `bL`.

We then say that the distance of `M` and `L` is `f₁ - f₂` which is `≥ 0` by our assumption on
the `fᵢ`.

One then verifies that the difference `f₁ - f₂` is invariant under multiplying `M` or `L` with
units of `K` and hence we obtain a distance function `inv` on the vertices of the Bruhat-Tits
graph.

## Main definitions

- `BruhatTits.dist L M`: The distance between two lattices`L` and `M`.

## Main results

- `BruhatTits.exists_normal_basis`: Given two lattices, we can find good bases using the Cartan
  decomposition.
- `BruhatTits.dist_symm`: The distance function is symmetric.
- `BruhatTits.dist_inv_isSimilar`: The distance function is invariant under homothety.
-/

open Module


variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

open Algebra BruhatTits Matrix GeneralLinearGroup

variable {k : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

namespace BruhatTits

omit [IsDiscreteValuationRing R] in
lemma smulBasis_apply_of_isLattice {M : Submodule R (ι → K)} [IsLattice M] (g : GL ι R)
    (b : Basis ι R M) (i j : ι) :
    ((smulBasis g b) i).val j = (b.toGL * g) j i := by
  dsimp only [smulBasis, toLinearEquivOfBasis]
  simp only [Basis.map_apply, LinearEquiv.trans_apply, Basis.equivFun_apply, Basis.repr_self,
    Basis.equivFun_symm_apply, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Finset.sum_apply,
    Pi.smul_apply, «GL».map, RingHom.mapMatrix_apply, Subring.coe_subtype, Units.inv_eq_val_inv,
    coe_units_inv, Units.val_mul]
  change (Finset.univ.sum fun x ↦ g.val.mulVec (Finsupp.single i 1) x * (b x).val j) =
    (b.toGL * g.val.map Subtype.val) j i
  rw [Finsupp.single_eq_pi_single]
  simp only [mulVec_single]
  rw [Matrix.mul_apply]
  congr
  ext k
  simp [Basis.toGL_apply, map_apply, mul_comm]

/-- `GL₂(K)` acts transitively on `R`-lattices. -/
instance : MulAction.IsPretransitive (GL (Fin 2) K) (BruhatTits.Lattice R) where
  exists_smul_eq L M := by
    classical
    let bL : Basis (Fin 2) R L.M :=
      Module.finBasisOfFinrankEq R L.M (IsLattice.finrank L.M)
    let gL := bL.toGL
    have hL : gL.toSubmodule = L.M :=
      bL.toGL_toSubmodule
    let bM : Basis (Fin 2) R M.M :=
      Module.finBasisOfFinrankEq R M.M (IsLattice.finrank M.M)
    let gM := bM.toGL
    have hM : gM.toSubmodule = M.M :=
      bM.toGL_toSubmodule
    use gM * gL⁻¹
    apply BruhatTits.Lattice.ext
    rw [Lattice.smul_M, ← hM, ← hL, smul_toSubmodule]
    simp

omit [IsDiscreteValuationRing ↥R] in
lemma basis_smul_def_of_isLattice {M : Submodule R (ι → K)} [IsLattice M] (g : GL ι R)
    (b : Basis ι R M) (i j : ι) :
    (((MulOpposite.op g) • b) i).val j = (b.toGL * g) j i :=
  smulBasis_apply_of_isLattice g b i j

omit [IsDiscreteValuationRing ↥R] in
lemma basis_smul_toGL {M : Submodule R (ι → K)} [IsLattice M] (g : GL ι R)
    (b : Basis ι R M) :
    ((MulOpposite.op g) • b).toGL = b.toGL * g := by
  ext i j
  simp [basis_smul_def_of_isLattice]

section «NormalBasis»

variable (ϖ : R) (hϖ : Irreducible ϖ)

include hϖ in
/--
Given two `R`-lattices `M` and `L`, there exists a basis `bM` of `M`
and a basis `bL` of `L` such that `bLᵢ = ϖ ^ fᵢ • bMᵢ` for `i = 1,2` and integers
`fᵢ`. If we fix the order of `fᵢ` to be `f₁ ≥ f₂`, the `fᵢ` are unique, i.e. don't
depend on `ϖ`, `bM` or `bL`.
-/
lemma exists_normal_basis (M L : BruhatTits.Lattice R) :
    ∃ (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M) (f : Fin 2 → ℤ),
    Antitone f ∧ ∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val := by
  classical
  let bL : Basis (Fin 2) R L.M := L.basis
  let bM : Basis (Fin 2) R M.M := M.basis
  obtain ⟨(k₁ : GL (Fin 2) R), (k₂ : GL (Fin 2) R), f, hf, hk⟩ :=
    cartan_decomposition' (k := 2) ϖ hϖ (bM.toGL⁻¹ * bL.toGL)
  let bM' : Basis (Fin 2) R M.M :=
    (MulOpposite.op k₁) • bM
  let bL' : Basis (Fin 2) R L.M :=
    (MulOpposite.op k₂⁻¹) • bL
  use bM', bL', f, hf
  intro i
  simp only [bL', bM']
  ext j
  have hk' : bL.toGL * GL.map R.subtype k₂⁻¹ =
    bM.toGL * GL.map R.subtype k₁ *
      (cartanDiag (k := 2) ϖ hϖ f : GL (Fin 2) K) := by
    rw [GL.map_inv]
    calc
      bL.toGL * (GL.map R.subtype k₂)⁻¹ =
          bM.toGL * (bM.toGL⁻¹ * bL.toGL) * (GL.map R.subtype k₂)⁻¹ := by
            group
      _ = bM.toGL * (GL.map R.subtype k₁ *
            (cartanDiag (k := 2) ϖ hϖ f : GL (Fin 2) K) *
            GL.map R.subtype k₂) * (GL.map R.subtype k₂)⁻¹ := by
            rw [← hk]
            rfl
      _ = bM.toGL * GL.map R.subtype k₁ *
            (cartanDiag (k := 2) ϖ hϖ f : GL (Fin 2) K) := by
            group
  rw [basis_smul_def_of_isLattice, hk']
  simp only [GL.map, RingHom.mapMatrix_apply, Subring.coe_subtype,
    Units.inv_eq_val_inv, coe_units_inv, Units.val_mul, val_cartanDiag, Pi.smul_apply,
    smul_eq_mul]
  rw [basis_smul_def_of_isLattice]
  simp only [GL.map, RingHom.mapMatrix_apply, Subring.coe_subtype, Units.inv_eq_val_inv,
    coe_units_inv, Units.val_mul]
  rw [mul_diagonal]
  rw [mul_comm]

end «NormalBasis»

/-- A variant of `BruhatTits.exists_normal_basis` where also a uniformizer is provided. -/
lemma exists_normal_basis_uniformizer (M L : BruhatTits.Lattice R) :
    ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M) (f : Fin 2 → ℤ),
    Irreducible ϖ ∧ Antitone f ∧ ∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨bM, bL, f, hf, heq⟩ := exists_normal_basis ϖ hϖ M L
  exact ⟨ϖ, bM, bL, f, hϖ, hf, heq⟩

/-- The integers `fᵢ` of `BruhatTits.exists_normal_basis` are unique. More precisely,
given two lattices `M` and `L`, uniformizers `ϖ`, `ϖ'`, basis
`bM`, `bM'` of `M` and `bL`, `bL'` of `L` and integers `fᵢ`, `fᵢ'` such that
`bLᵢ = ϖ ^ fᵢ • bMᵢ` and `bL'ᵢ = ϖ' ^ f'ᵢ • bM'ᵢ` and with `f₂ ≥ f₁`, `f'₁ ≥ f'₂`,
then `fᵢ = fᵢ'`. This unique pair of integers `fᵢ` is called the signature of `L` and `M`.
-/
lemma signature_unique {M L : BruhatTits.Lattice R}
    {ϖ ϖ' : R} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    {bM bM' : Basis (Fin 2) R M.M} {bL bL' : Basis (Fin 2) R L.M}
    {f f' : Fin 2 → ℤ} (hf : Antitone f) (hf' : Antitone f')
    (h : ∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val)
    (h' : ∀ i, (bL' i).val = (ϖ' ^ f' i : K) • (bM' i).val) :
    f = f' := by
  obtain ⟨⟨k₁⟩, hk₁⟩ := MulAction.IsPretransitive.exists_smul_eq (M := (GL (Fin 2) R)ᵐᵒᵖ)
    bM bM'
  obtain ⟨⟨k₂⟩, hk₂⟩ := MulAction.IsPretransitive.exists_smul_eq (M := (GL (Fin 2) R)ᵐᵒᵖ)
    bL bL'
  let d : GL (Fin 2) K := cartanDiag (k := 2) ϖ hϖ f
  have hd : bL.toGL = bM.toGL * d := by
    ext i j
    simp only [Basis.toGL_apply, Units.val_mul, val_cartanDiag, mul_diagonal, d]
    rw [mul_comm, h j]
    simp
  let d' : GL (Fin 2) K := cartanDiag (k := 2) ϖ' hϖ' f'
  have hd' : bL'.toGL = bM'.toGL * d' := by
    ext i j
    simp only [Basis.toGL_apply, Units.val_mul, val_cartanDiag, mul_diagonal, d']
    rw [mul_comm, h' j]
    simp
  have hbMd' : bM'.toGL * d' = bM.toGL * d * k₂ := by
    rw [← hd', ← hk₂]
    erw [basis_smul_toGL, hd]
  have hbM : bM.toGL = bM'.toGL * k₁⁻¹ := by
    rw [← hk₁]
    erw [basis_smul_toGL k₁ bM]
    rw [mul_assoc, GL.map_mul_map_inv, mul_one]
  have : (1 : GL (Fin 2) R) * d' * (1 : GL (Fin 2) R) = k₁⁻¹ * d * k₂ := by
    calc (1 : GL (Fin 2) R) * d' * (1 : GL (Fin 2) R) = bM'.toGL⁻¹ * (bM'.toGL * d') :=
        by rw [GL.map_one]; group
                  _ = bM'.toGL⁻¹ * bM.toGL * d * k₂ := by rw [hbMd']; group
                  _ = bM'.toGL⁻¹ * bM'.toGL * k₁⁻¹ * d * k₂ := by rw [hbM]; group
                  _ = k₁⁻¹ * d * k₂ := by group
  apply cartan_decomposition_unique_uniformizer (k := 2) hϖ hϖ' hf hf'
    (k₁ := k₁⁻¹) (k₂ := k₂) (k₁' := 1) (k₂' := 1)
    this.symm

section «Choices»

/-!
## Choice of signature

In this section for every pair of lattices `M` and `L`, we fix arbitrarily chosen
basis `bM` of `M` and `bL` of `L` and the (antitone) signature `fᵢ` such that
`bLᵢ = ϖ ^ fᵢ • bMᵢ`.

-/

/-- A choice of uniformizer. -/
noncomputable def signatureϖ (M L : BruhatTits.Lattice R) : R :=
  (exists_normal_basis_uniformizer M L).choose

/-- The chosen uniformizer is irreducible. -/
lemma signatureϖ_irreducible (M L : BruhatTits.Lattice R) :
    Irreducible (signatureϖ M L) :=
  (exists_normal_basis_uniformizer M L).choose_spec.choose_spec.choose_spec.choose_spec.left

/-- A choice of basis for `M`. -/
noncomputable def signatureBasisSource (M L : BruhatTits.Lattice R) :
    Basis (Fin 2) R M.M :=
  (exists_normal_basis_uniformizer M L).choose_spec.choose

/-- A choice of basis for `L`. -/
noncomputable def signatureBasisTarget (M L : BruhatTits.Lattice R) :
    Basis (Fin 2) R L.M :=
  (exists_normal_basis_uniformizer M L).choose_spec.choose_spec.choose

/-- The unique (antitone) signature of `M` and `L`. -/
noncomputable def signature (M L : BruhatTits.Lattice R) : Fin 2 → ℤ :=
  (exists_normal_basis_uniformizer M L).choose_spec.choose_spec.choose_spec.choose

lemma signature_antitone (M L : BruhatTits.Lattice R) :
    Antitone (signature M L) :=
  (exists_normal_basis_uniformizer M L).choose_spec.choose_spec.choose_spec.choose_spec.right.left

lemma signatureBasisTarget_eq (M L : BruhatTits.Lattice R) (i : Fin 2) :
    signatureBasisTarget M L i =
      (signatureϖ M L ^ signature M L i : K) • (signatureBasisSource M L i).val :=
  (exists_normal_basis_uniformizer M L).choose_spec.choose_spec.choose_spec.choose_spec.right.right
    i

/-- To show that an antitone pair of integers `fᵢ` is the signature of `M` and `L` it
suffices to find basis that satisfy the defining property of the signature. -/
lemma eq_signature_iff (M L : BruhatTits.Lattice R)
    (f : Fin 2 → ℤ) (hf : Antitone f) :
    signature M L = f ↔ ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M),
      Irreducible ϖ ∧ ∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val := by
  constructor
  · rintro rfl
    exact ⟨signatureϖ M L, signatureBasisSource M L, signatureBasisTarget M L,
      signatureϖ_irreducible M L, signatureBasisTarget_eq M L⟩
  · intro ⟨ϖ, bM, bL, hϖ, h⟩
    exact signature_unique (signatureϖ_irreducible M L) hϖ (signature_antitone M L) hf
      (signatureBasisTarget_eq M L)
      h

end «Choices»

/-- We define the distance between lattices `M` and `L` to be `f₁ - f₂` where
`fᵢ` is the (antitone) signature. This is always `≥ 0`, because `f₁ ≥ f₂`. -/
noncomputable def dist (M L : BruhatTits.Lattice R) : ℕ :=
  (signature M L 0 - signature M L 1).toNat

lemma signature_diff_eq_dist (M L : BruhatTits.Lattice R) :
    signature M L 0 - signature M L 1 = dist M L := by
  simp only [dist]
  have : signature M L 0 - signature M L 1 ≥ 0 :=
    Int.sub_nonneg_of_le (signature_antitone M L (Fin.zero_le 1))
  exact (Int.toNat_of_nonneg this).symm

/-- A rephrasing of uniqueness of signatures in terms of the distance of lattices. -/
lemma eq_dist_iff (M L : BruhatTits.Lattice R) (n : ℕ) :
    dist M L = n ↔ ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M)
      (f : Fin 2 → ℤ),
      Irreducible ϖ ∧
        Antitone f ∧
        (∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val) ∧ f 0 - f 1 = n := by
  constructor
  · rintro rfl
    exact ⟨signatureϖ M L, signatureBasisSource M L, signatureBasisTarget M L, signature M L,
      signatureϖ_irreducible M L, signature_antitone M L, signatureBasisTarget_eq M L,
      signature_diff_eq_dist M L⟩
  · intro ⟨ϖ, bM, bL, f, hϖ, hf, hi, hn⟩
    have : signature M L = f := by
      apply (eq_signature_iff M L f hf).mpr
      use ϖ, bM, bL
    subst this
    rw [signature_diff_eq_dist M L] at hn
    exact Int.ofNat_inj.mp hn

/-- Variant of `BruhatTits.eq_dist_iff` where the signature is unwrapped as two integers `a` and
`b`. -/
lemma eq_dist_iff₂ (M L : BruhatTits.Lattice R) (n : ℕ) :
    dist M L = n ↔ ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M)
      (a b : ℤ), Irreducible ϖ ∧
         b ≤ a ∧ bL 0 = ϖ.val ^ a • (bM 0).val ∧ bL 1 = ϖ.val ^ b • (bM 1).val ∧ a - b = n := by
  rw [eq_dist_iff]
  constructor
  · rintro ⟨ϖ, bM, bL, f, hϖ, _, hrep, hdiff⟩
    refine ⟨ϖ, bM, bL, f 0, f 1, hϖ, Int.le.intro_sub n hdiff, hrep 0, hrep 1, hdiff⟩
  · rintro ⟨ϖ, bM, bL, a, b, hϖ, hle, h0, h1, hdiff⟩
    refine ⟨ϖ, bM, bL, ![a, b], hϖ, ?_, ?_, hdiff⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
    · intro i
      fin_cases i <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Monotone variant of `BruhatTits.eq_dist_iff`. -/
lemma eq_dist_iff_monotone (M L : BruhatTits.Lattice R) (n : ℕ) :
    dist M L = n ↔ ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M)
      (f : Fin 2 → ℤ),
      Irreducible ϖ ∧ Monotone f ∧
        (∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val) ∧ f 1 - f 0 = n := by
  rw [eq_dist_iff]
  constructor
  · intro ⟨ϖ, bM, bL, f, hϖ, hf, hi, hn⟩
    use ϖ, bM.reindex Fin.revPerm, bL.reindex Fin.revPerm, f ∘ Fin.revPerm
    refine ⟨hϖ, ?_, fun i ↦ ?_, ?_⟩
    · exact hf.comp (Fin.rev_antitone 2)
    · simp only [Basis.coe_reindex, Fin.revPerm_symm, Function.comp_apply, Fin.revPerm_apply]
      exact hi i.rev
    · simpa
  · intro ⟨ϖ, bM, bL, f, hϖ, hf, hi, hn⟩
    use ϖ, bM.reindex Fin.revPerm, bL.reindex Fin.revPerm, f ∘ Fin.revPerm
    refine ⟨hϖ, ?_, fun i ↦ ?_, ?_⟩
    · exact hf.comp_antitone (Fin.rev_antitone 2)
    · simp only [Basis.coe_reindex, Fin.revPerm_symm, Function.comp_apply, Fin.revPerm_apply]
      exact hi i.rev
    · simpa

lemma exists_repr_dist (M L : BruhatTits.Lattice R) :
    ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M) (f : Fin 2 → ℤ),
      Irreducible ϖ ∧ Antitone f ∧
        (∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val) ∧ f 0 - f 1 = dist M L := by
  set n := dist M L with hn
  exact (eq_dist_iff M L n).mp hn.symm

/-- The distance on lattices is symmetric. -/
lemma dist_symm (M L : BruhatTits.Lattice R) :
    dist M L = dist L M := by
  obtain ⟨ϖ, bM, bL, f, hϖ, hf, hrep, hdiff⟩ := exists_repr_dist M L
  symm
  rw [eq_dist_iff_monotone]
  use ϖ, bL, bM, (fun i ↦ - f i)
  refine ⟨hϖ, ?_, ?_, ?_⟩
  · exact hf.neg
  · intro i
    have : ϖ.val ^ f i ≠ 0 := by
      apply zpow_ne_zero
      simpa using hϖ.ne_zero
    simp only [_root_.zpow_neg, hrep i, smul_smul]
    field_simp
    simp
  · simpa only [Fin.isValue, sub_neg_eq_add, add_comm]

/-- The distance of a lattice to itself is zero. -/
@[simp]
lemma dist_self (L : BruhatTits.Lattice R) :
    dist L L = 0 := by
  rw [eq_dist_iff]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  use ϖ, L.basis, L.basis, fun _ ↦ 0, hϖ, antitone_const
  simp

/-- Transport a basis of a submodule along the action of `GL`. -/
noncomputable def mulBasis (g : GL ι K) {M : Submodule R (ι → K)} (b : Basis ι R M) :
    Basis ι R (g • M : Submodule R (ι → K)) :=
  let e' : M ≃ₗ[R] (g • M : Submodule R (ι → K)) := equivSMulGL g M
  b.map e'

open Pointwise

/-- The linear equivalence from a submodule to its scalar multiple. -/
def equivSMul (a : Kˣ) (M : Submodule R (ι → K)) :
    M ≃ₗ[R] (a • M : Submodule R (ι → K)) :=
  let e : (ι → K) ≃ₗ[R] (ι → K) := (LinearEquiv.smulOfUnit a).restrictScalars R
  e.submoduleMap M

/-- Transport a lattice basis along scalar multiplication. -/
noncomputable def mulBasisScalar (a : Kˣ) {M : BruhatTits.Lattice R} (b : Basis ι R M.M) :
    Basis ι R (a • M).M :=
  let e : M.M ≃ₗ[R] (a • M.M : Submodule R (Fin 2 → K)) := equivSMul a M.M
  b.map e

omit [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]

omit [DecidableEq ι] [Fintype ι] in
lemma mulBasisScalar_apply (a : Kˣ) (M : BruhatTits.Lattice R) (b : Basis ι R M.M) (i : ι) :
    (mulBasisScalar a b i).val = a.val • (b i).val := by
  simp only [Lattice.smul_module, mulBasisScalar, equivSMul, Basis.map_apply]
  rfl

lemma mulBasis_apply (g : GL ι K) {M : Submodule R (ι → K)} (b : Basis ι R M) (i : ι) :
    (mulBasis g b i).val = g *ᵥ (b i).val := by
  simp [mulBasis, equivSMulGL]
  rfl

lemma mulBasisScalar_toGL [IsFractionRing R K] (a : Kˣ) (M : BruhatTits.Lattice R)
    (b : Basis (Fin 2) R M.M) : (mulBasisScalar a b).toGL = GL.diagonal (fun _ ↦ a) * b.toGL := by
  ext i j
  simp only [Lattice.smul_module, Basis.toGL_apply, Units.val_mul, GL.val_diagonal, diagonal_mul]
  rfl

lemma unit_smul_eq (u : Rˣ) (M : BruhatTits.Lattice R) : (Units.map R.subtype u : Kˣ) • M = M := by
  ext x
  constructor
  · intro hx
    simp only [Lattice.smul_module] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [Units.coe_map, MonoidHom.coe_coe, Subring.coe_subtype,
      DistribSMul.toLinearMap_apply]
    exact Submodule.smul_mem _ u.val hy
  · intro hx
    simp only [Lattice.smul_module]
    refine ⟨u⁻¹ • x, ?_, ?_⟩
    · exact Submodule.smul_mem _ u.inv hx
    · simp only [Units.coe_map, MonoidHom.coe_coe, Subring.coe_subtype, LinearMap.map_smul_of_tower,
        DistribSMul.toLinearMap_apply]
      rw [← Subring.smul_def, Units.smul_def, smul_smul]
      simp

variable [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]

/-- The distance of a lattice `M` to a given lattice `L` does not change when `M` is scaled
by some `a : Kˣ`. -/
lemma dist_smul_eq_dist (M L : BruhatTits.Lattice R) (a : Kˣ) :
    dist (a • M) L = dist M L := by
  obtain ⟨ϖ, bM, bL, f, hϖ, hf, hrep, hdiff⟩ := exists_repr_dist M L
  obtain ⟨n, u, ha⟩ := eq_unit_mul_pow_irreducible' ϖ hϖ a
  have h0 : ϖ.val ≠ 0 := by simpa using hϖ.ne_zero
  have : a • M = (Units.mk0 ϖ.val h0) ^ n • M := by
    rw [ha, mul_comm, ← smul_smul, unit_smul_eq]
  rw [this]
  rw [mul_comm] at ha
  have : ϖ.val ^ n ≠ 0 := by
    apply zpow_ne_zero
    simpa using hϖ.ne_zero
  let bM' : Basis (Fin 2) R ((Units.mk0 ϖ.val h0) ^ n • M).M :=
    mulBasisScalar ((Units.mk0 ϖ.val h0) ^ n) bM
  have hbM' (i : Fin 2) : ϖ.val ^ (-n) • (bM' i).val = bM i := by
    simp only [bM', mulBasisScalar_apply]
    simp only [_root_.zpow_neg, Units.val_zpow_eq_zpow_val, Units.val_mk0, smul_smul]
    field_simp
    simp
  let f' (i : Fin 2) : ℤ := f i + (-n)
  rw [eq_dist_iff]
  use ϖ, bM', bL, f', hϖ
  refine ⟨?_, ?_, ?_⟩
  · apply hf.add_const
  · intro i
    simp only [Lattice.smul_module, f']
    rw [zpow_add₀ (by simpa using hϖ.ne_zero)]
    rw [← smul_smul]
    erw [hbM' i]
    exact hrep i
  · simp [f', hdiff]

/-- The distance of lattices is invariant under the equivalence relation `IsSimilar`. -/
lemma dist_inv_isSimilar (M L M' L' : BruhatTits.Lattice R)
    (hM : Lattice.IsSimilar R M M') (hL : Lattice.IsSimilar R L L') : dist M L = dist M' L' := by
  obtain ⟨a, rfl⟩ := hM
  obtain ⟨b, rfl⟩ := hL
  rw [dist_smul_eq_dist]
  nth_rw 2 [dist_symm]
  rw [dist_smul_eq_dist, dist_symm]

end BruhatTits
