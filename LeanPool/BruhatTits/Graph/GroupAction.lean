/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Graph.Graph
import LeanPool.BruhatTits.Utils.GraphAction

/-!
# Group actions on the Bruhat-Tits graph

In this file we equip the Bruhat-Tits graph with group actions of `GL₂(K)` and compute stabilizers.

# Main results

- `MulAction.IsPretransitive (GL (Fin 2) K) (Vertices R)` : We show that `GL₂(K)` acts transitively
  on the vertices.
- `GraphAction (GL (Fin 2) K) (BTgraph (R:= R))` : The group `GL₂(K)` acts on `BTgraph`.
- `stabilizer_mk_standard_eq_sup` : The stabilizer of the standard vertex of the `GL₂(K)`-action
  is `Kˣ * GL₂(R)`.
- `stabilizer_fun_mk_ntwist₂_eq_sup_comap_upperTriangularSubgroup`: The pointwise stabilizer of
  `GL₂(K)` of the segment `⟦v₀⟧ - ⟦v₁⟧ - ... - ⟦vₙ⟧` is the subgroup `Kˣ * Iₙ` where `Iₙ` is
  the subgroup of `GL₂(R)` that is upper triangular modulo `ϖ ^ n`.

-/

open Module


-- Let R be a discrete valuation ring and K its field of fractions
variable {K : Type*} [Field K]
variable {R : Subring K}

local notation "v" => ValuationRing.valuation R K

namespace BruhatTits

section «Action»

lemma isSimilar_smul_of_isSimilar (g : GL (Fin 2) K) (L M : Lattice R) (h : L.IsSimilar R M) :
    (g • L).IsSimilar R (g • M) := by
  obtain ⟨a, rfl⟩ := h
  have : g • a • L = a • g • L := by
    apply Lattice.ext
    simp only [Lattice.smul_M, Lattice.smul_module, Units.smul_def]
    ext x
    simp only [Matrix.GeneralLinearGroup.mem_smul]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simp only [DistribSMul.toLinearMap_apply, Matrix.mulVec_smul]
      refine ⟨g.val.mulVec z, ?_, rfl⟩
      simp only [SetLike.mem_coe, Matrix.GeneralLinearGroup.mem_smul]
      use z, hz
    · rintro ⟨y, hy, rfl⟩
      simp only [SetLike.mem_coe, Matrix.GeneralLinearGroup.mem_smul] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      refine ⟨a.val • z, ?_, ?_⟩
      · use z, hz
        rfl
      · simp [Matrix.mulVec_smul]
  rw [this]
  exact Lattice.isSimilar_smul R (g • L) a

/-- The action of `GL₂(K)` on vertices induced by its action on lattices. -/
def smulGL (g : GL (Fin 2) K) : Vertices R → Vertices R :=
  Quotient.lift (fun L ↦ ⟦g • L⟧) <| by
    intro L M h
    apply Quotient.sound
    exact isSimilar_smul_of_isSimilar g L M h

lemma smulGL_mk (g : GL (Fin 2) K) (L : Lattice R) :
    smulGL g ⟦L⟧ = ⟦g • L⟧ :=
  rfl

instance : SMul (GL (Fin 2) K) (Vertices R) where
  smul := smulGL

lemma _root_.BruhatTits.Vertices.smul_def (g : GL (Fin 2) K) (x : Vertices R) :
    g • x = smulGL g x :=
  rfl

/-- The action of `GL₂(K)` on vertices. -/
instance : MulAction (GL (Fin 2) K) (Vertices R) where
  one_smul x := by
    refine Quotient.inductionOn x (fun L ↦ ?_)
    rw [Vertices.smul_def, smulGL_mk, one_smul]
  mul_smul g h x := by
    refine Quotient.inductionOn x (fun L ↦ ?_)
    rw [Vertices.smul_def, smulGL_mk]
    rw [mul_smul]
    rw [← smulGL_mk, ← Vertices.smul_def]
    rw [← smulGL_mk, ← Vertices.smul_def]

variable [IsDiscreteValuationRing R] [IsFractionRing R K]

/-- `GL₂(K)` acts transitively on the vertices. -/
instance : MulAction.IsPretransitive (GL (Fin 2) K) (Vertices R) where
  exists_smul_eq L M := by
    classical
    refine Quotient.inductionOn₂ L M ?_
    intro L M
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL (Fin 2) K) L M
    use g
    rfl

@[simp]
lemma inv_smul_smul_eq_inv (g : GL (Fin 2) K) (x y : Vertices R) :
    inv (g • x) (g • y) = inv x y := by
  refine Quotient.inductionOn₂ x y (fun L M ↦ ?_)
  rw [Vertices.smul_def, smulGL_mk]
  rw [Vertices.smul_def, smulGL_mk]
  change dist (g • L) (g • M) = dist L M
  simp

lemma adj_smul_smul_iff_adj (g : GL (Fin 2) K) (x y : Vertices R) :
    BTgraph.Adj (g • x) (g • y) ↔ BTgraph.Adj x y := by
  change inv (g • x) (g • y) = 1 ↔ inv x y = 1
  simp

/-- `GL₂(K)` acts by graph isomorphisms on the Bruhat-Tits tree. -/
def _root_.Matrix.GeneralLinearGroup.toGraphIso (g : GL (Fin 2) K) :
    BTgraph (R := R) ≃g BTgraph (R := R) where
  toEquiv := MulAction.toPerm g
  map_rel_iff' {x y} := by
    exact adj_smul_smul_iff_adj g x y

/-- The action of `GL₂(K)` on the Bruhat-Tits graph. -/
instance : GraphAction (GL (Fin 2) K) (BTgraph (R:= R)) where
  smul_adj_smul g x y := (adj_smul_smul_iff_adj g x y).mpr

omit [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K] in
lemma cartanDiag_smul_standard
    (ϖ : R) (hϖ : Irreducible ϖ) (f : Fin 2 → ℤ) :
    cartanDiag ϖ hϖ f • Lattice.standard R =
      ((Pi.basisFun K (Fin 2)).twist hϖ f).toLattice := by
  simp only [Lattice.standard]
  have : cartanDiag ϖ hϖ f • ((Pi.basisFun K (Fin 2))) =
        (((Pi.basisFun K (Fin 2)).twist hϖ f)) := by
    ext i j
    simp only [Basis.smulGL_apply, val_cartanDiag, Basis.twist_apply, Pi.smul_apply,
      smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp
  rw [← this, Basis.smulGL_toLattice]

open Pointwise in
lemma pow_smul_range_eq_range_iff {ι : Type*} [Finite ι] [Nonempty ι] {ϖ : R}
    (hϖ : Irreducible ϖ) (n : ℤ) :
    ϖ.val ^ n • Set.range ((Algebra.linearMap R K).compLeft ι) =
      Set.range ((Algebra.linearMap R K).compLeft ι) ↔ n = 0 := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; simp⟩
  let i : ι := ‹Nonempty ι›.some
  by_cases hn : n ≥ 0
  · rw [Set.ext_iff] at h
    have : (Pi.basisFun K ι) i ∈
        ϖ.val ^ n • Set.range ⇑((Algebra.linearMap (↥R) K).compLeft ι) := by
      rw [h]
      use Pi.basisFun R ι i
      ext
      simp [Pi.single_apply]
    change Pi.single i 1 ∈
      ϖ.val ^ n • Set.range ⇑((Algebra.linearMap (↥R) K).compLeft ι) at this
    rw [Set.mem_smul_set] at this
    obtain ⟨-, ⟨z, rfl⟩, hy⟩ := this
    rw [funext_iff] at hy
    have := hy i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at this
    change (ϖ.val ^ n) * (z i).val = 1 at this
    have heq : (ValuationRing.valuation R K) (z i).val = 1 := by
      rw [← valuation_eq_one_iff, isUnit_iff_exists_inv']
      use ⟨ϖ.val ^ n, (irreducible_zpow_mem_subring_iff ϖ hϖ n).mpr hn⟩
      ext
      simpa
    apply_fun (ValuationRing.valuation R K ·) at this
    rw [map_mul, map_one] at this
    rw [heq] at this
    exact (valuation_irreducible_zpow_eq_one_iff _ hϖ n).mp
      (by simpa only [mul_one] using this)
  · have : Pi.single i (ϖ.val ^ n) ∈ Set.range ((Algebra.linearMap (↥R) K).compLeft ι) := by
      rw [← h]
      rw [Set.mem_smul_set]
      refine ⟨Pi.single i 1, ?_, ?_⟩
      · use Pi.single i 1
        ext
        simp [Pi.single_apply]
      · ext j
        simp [Pi.single_apply]
    rw [Set.mem_range] at this
    obtain ⟨z, hz⟩ := this
    rw [funext_iff] at hz
    have := hz i
    simp only [Pi.single_eq_same] at this
    change (z i).val = ϖ.val ^ n at this
    have : ϖ.val ^ n ∈ R := by
      rw [← this]
      exact (z i).property
    rw [irreducible_zpow_mem_subring_iff _ hϖ] at this
    omega

open Pointwise in
/-- The stabilizer of the standard lattice of the `GL₂(K)`-action on lattices is `GL₂(R)`. -/
lemma stabilizer_standard_eq_range_map_subtype :
    MulAction.stabilizer (GL (Fin 2) K) (Lattice.standard R) =
      (Matrix.GeneralLinearGroup.map R.subtype).range := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  ext g
  simp only [MulAction.mem_stabilizer_iff, MonoidHom.mem_range]
  constructor
  · intro hg
    obtain ⟨(k₁ : GL (Fin 2) R), (k₂ : GL (Fin 2) R), (f : Fin 2 → ℤ), hf, h⟩ :=
      cartan_decomposition' (k := 2) ϖ hϖ g
    rw [← h] at hg
    erw [mul_smul, GL_map_eq, GL_map_eq, map_subtype_smul_standard_eq_standard k₂, mul_smul] at hg
    apply_fun (Matrix.GeneralLinearGroup.map R.subtype k₁⁻¹ • ·) at hg
    simp only [map_inv, ← mul_smul] at hg
    rw [← map_inv, map_subtype_smul_standard_eq_standard] at hg
    have hmul : ((Matrix.GeneralLinearGroup.map R.subtype) k₁)⁻¹ *
        ((Matrix.GeneralLinearGroup.map R.subtype) k₁ * cartanDiag ϖ hϖ f) =
        cartanDiag ϖ hϖ f := by
      group
    have hg' : cartanDiag ϖ hϖ f • Lattice.standard R = Lattice.standard R := by
      rw [← hmul]
      exact hg
    have hdist : dist (Lattice.standard R) (cartanDiag ϖ hϖ f • Lattice.standard R) = 0 := by
      simp [hg']
    simp only [cartanDiag_smul_standard] at hdist
    simp only [Lattice.standard] at hdist
    apply_fun Int.ofNat at hdist
    simp only [Int.ofNat_eq_natCast, dist_twist _ _ hf, Fin.isValue, CharP.cast_eq_zero,
      sub_eq_zero] at hdist
    rw [Lattice.ext_iff, Lattice.smul_M] at hg'
    simp only [cartanDiag] at hg'
    rw [Matrix.GeneralLinearGroup.diagonal_smul _ _ _ 0] at hg'
    · simp only [Fin.isValue, zpow_neg, Units.smul_mk_apply] at hg'
      have : ϖ.val ^ f 0 • (Lattice.standard R).M = (Lattice.standard R).M := hg'
      rw [Lattice.standard_M, SetLike.ext'_iff] at this
      simp only [Fin.isValue, Submodule.coe_pointwise_smul, LinearMap.coe_range] at this
      have hf_zero : f 0 = 0 := (pow_smul_range_eq_range_iff hϖ (f 0)).mp this
      have : f = 0 := by
        ext i
        fin_cases i
        · exact hf_zero
        · simpa [← hdist]
      subst this
      use k₁ * k₂
      calc
        (Matrix.GeneralLinearGroup.map R.subtype) (k₁ * k₂) =
            (Matrix.GeneralLinearGroup.map R.subtype) k₁ *
              (Matrix.GeneralLinearGroup.map R.subtype) k₂ := by rw [map_mul]
        _ = (Matrix.GeneralLinearGroup.map R.subtype) k₁ * 1 *
            (Matrix.GeneralLinearGroup.map R.subtype) k₂ := by rw [mul_one]
        _ = (Matrix.GeneralLinearGroup.map R.subtype) k₁ * cartanDiag ϖ hϖ 0 *
            (Matrix.GeneralLinearGroup.map R.subtype) k₂ := by rw [cartanDiag_zero hϖ]
        _ = g := h
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [hdist]
  · rintro ⟨k, rfl⟩
    rw [map_subtype_smul_standard_eq_standard]

/-- The stabilizer of any lattice `g • Lattice.standard R`
is the conjugate `g GL₂(R) g⁻¹`. -/
lemma stabilizer_smul_standard_eq_map_conj_subtype_range (g : GL (Fin 2) K) :
    MulAction.stabilizer (GL (Fin 2) K) (g • Lattice.standard R) =
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))
        (Matrix.GeneralLinearGroup.map R.subtype).range := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_standard_eq_range_map_subtype]

lemma _root_.BruhatTits.Lattice.valuation_det_eq_one_of_mem_stabilizer
    (L : Lattice R) (g : GL (Fin 2) K)
      (hg : g ∈ MulAction.stabilizer _ L) :
    v g.det = 1 := by
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL (Fin 2) K) (Lattice.standard R) L
  rw [stabilizer_smul_standard_eq_map_conj_subtype_range] at hg
  obtain ⟨k, ⟨k, rfl⟩, rfl⟩ := hg
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, map_mul, map_inv,
    mul_inv_cancel_comm, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_map_apply, Subring.coe_subtype, Subring.coe_det]
  rw [← valuation_eq_one_iff]
  exact Matrix.isUnits_det_units k

lemma _root_.Matrix.GL.mem_range_map_iff {R K : Type*} [CommRing R]
    [CommRing K] (f : R →+* K) (hf : Function.Injective f)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : GL ι K) :
    g ∈ Set.range (Matrix.GeneralLinearGroup.map f) ↔
      (∀ (i j : ι), g i j ∈ Set.range f) ∧
        ↑g.det⁻¹ ∈ Set.range f := by
  refine ⟨fun ⟨k, hk⟩ ↦ hk ▸ by simp [Matrix.GeneralLinearGroup.map_det], fun ⟨h1, ⟨u, hu⟩⟩ ↦ ?_⟩
  choose r hr using h1
  refine ⟨.mk'' r ?_, by ext; simp [Matrix.GeneralLinearGroup.mk'', Matrix.nonsingInvUnit, hr]⟩
  rw [isUnit_iff_exists_inv]
  use u
  apply hf
  simp only [map_mul, RingHom.map_det, RingHom.mapMatrix_apply, map_one]
  rw [hu]
  convert (Matrix.GeneralLinearGroup.det g).val_inv using 2
  · congr; ext; simp [hr]
  · exact (Units.inv_eq_val_inv _).symm

lemma mem_stabilizer_twist_iff_mem {ϖ : R} (hϖ : Irreducible ϖ) (g : GL (Fin 2) R)
    (f : Fin 2 → ℤ) :
    (g : GL (Fin 2) K) ∈ MulAction.stabilizer (GL (Fin 2) K)
      (((Pi.basisFun K (Fin 2)).twist hϖ f).toLattice (R := R)) ↔
    ϖ.val ^ (f 1 - f 0) * g 0 1 ∈ R ∧
      ϖ.val ^ (f 0 - f 1) * g 1 0 ∈ R := by
  rw [← cartanDiag_smul_standard, stabilizer_smul_standard_eq_map_conj_subtype_range]
  refine ⟨fun ⟨_, ⟨k, rfl⟩, hk⟩ ↦ ?_, ?_⟩
  · have hk := congr($(hk).val)
    dsimp [- MulAut.conj_apply] at hk
    rw [← Matrix.ext_iff] at hk
    have hne : ϖ.val ≠ 0 := by simp [hϖ.ne_zero]
    refine ⟨?_, ?_⟩
    · have := hk 0 1
      simp only [Fin.isValue, conj_cartanDiag_zero_one, Matrix.GeneralLinearGroup.map_apply,
        Subring.subtype_apply] at this
      change ϖ.val ^ (f 1 - f 0) * (GL.map R.subtype g : GL (Fin 2) K) 0 1 ∈ R
      rw [← this, zpow_sub₀ hne, zpow_sub₀ hne]
      ring_nf
      field_simp [zpow_ne_zero]
      exact (k 0 1).property
    · have := hk 1 0
      simp only [Fin.isValue, conj_cartanDiag_one_zero, Matrix.GeneralLinearGroup.map_apply,
        Subring.subtype_apply] at this
      change ϖ.val ^ (f 0 - f 1) * (GL.map R.subtype g : GL (Fin 2) K) 1 0 ∈ R
      rw [← this, zpow_sub₀ hne, zpow_sub₀ hne]
      ring_nf
      field_simp [zpow_ne_zero]
      exact (k 1 0).property
  · intro ⟨h1, h2⟩
    let k : GL (Fin 2) K := MulAut.conj (cartanDiag ϖ hϖ f)⁻¹ g
    refine ⟨k, ?_, ?_⟩
    · dsimp [k, - MulAut.conj_apply]
      rw [cartanDiag_inv]
      rw [Matrix.GL.mem_range_map_iff R.subtype R.subtype_injective]
      refine ⟨fun i j ↦ ?_, ?_⟩
      · fin_cases i <;> fin_cases j
        · simp [conj_cartanDiag_zero_zero, - MulAut.conj_apply]
        · simpa [conj_cartanDiag_zero_one, ← sub_eq_neg_add, - MulAut.conj_apply] using h1
        · simpa [conj_cartanDiag_one_zero, ← sub_eq_neg_add, - MulAut.conj_apply] using h2
        · simp [conj_cartanDiag_one_one, - MulAut.conj_apply]
      · have : ((g.val).det.val)⁻¹ = g.det.inv.val := by
          change g.det.val.val⁻¹ = (Units.map R.subtype g.det⁻¹).val
          simp [map_inv]
        simp [this]
    · dsimp [k, - MulAut.conj_apply]
      rw [map_inv, MulAut.inv_def, MulEquiv.apply_symm_apply]

/--
`g` in `GL₂(K)` stabilizes `(ϖ ^ n • e₀, ϖ ^ m • e₁)` if and only if `g` is of the form
```
      a           ϖ ^ (n - m) * b
ϖ ^ (m - n) * c         d
```
for some `(a b, c d)` in `GL₂(R)`.
-/
lemma mem_stabilizer_twist_iff_exists {ϖ : R} (hϖ : Irreducible ϖ) (g : GL (Fin 2) K)
    (f : Fin 2 → ℤ) :
    g ∈ MulAction.stabilizer (GL (Fin 2) K)
      (((Pi.basisFun K (Fin 2)).twist hϖ f).toLattice (R := R)) ↔
    ∃ (k : GL (Fin 2) R),
      g 0 0 = k 0 0 ∧
      g 1 1 = k 1 1 ∧
      g 1 0 = ϖ ^ (f 1 - f 0) * k 1 0 ∧
      g 0 1 = ϖ ^ (f 0 - f 1) * k 0 1 := by
  rw [← cartanDiag_smul_standard, stabilizer_smul_standard_eq_map_conj_subtype_range]
  refine ⟨?_, ?_⟩
  · rintro ⟨-, ⟨k, rfl⟩, rfl⟩
    use k
    simp [conj_cartanDiag_zero_zero, conj_cartanDiag_one_one, conj_cartanDiag_one_zero,
      conj_cartanDiag_zero_one, -MulAut.conj_apply]
  · rintro ⟨k, hk⟩
    use k, ⟨k, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp_all [conj_cartanDiag_zero_zero, conj_cartanDiag_one_one, conj_cartanDiag_one_zero,
        conj_cartanDiag_zero_one, -MulAut.conj_apply]

/-- `g` in `GL₂(R)` is in the stabilizer of `(e₀, ϖ ^ n • e₁)` if and only if
`g 1 0 ≡ 0 (mod ϖ ^ n)`. -/
lemma mem_stabilizer_ntwist₂_iff_mem_span {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) (g : GL (Fin 2) R) :
    (g : GL (Fin 2) K) ∈ MulAction.stabilizer (GL (Fin 2) K)
      (((Pi.basisFun K (Fin 2)).ntwist₂ hϖ 0 n).toLattice (R := R)) ↔
    g 1 0 ∈ Ideal.span {ϖ ^ n} := by
  rw [Basis.ntwist₂, Basis.twist₂, mem_stabilizer_twist_iff_mem]
  simp only [CharP.cast_eq_zero, sub_zero, zpow_natCast, Fin.isValue, zero_sub, zpow_neg]
  refine ⟨fun ⟨_, h⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · rw [Ideal.mem_span_singleton]
    use ⟨((ϖ : K) ^ n)⁻¹ * ((g 1 0 : R) : K), h⟩
    ext
    simp only [Subring.coe_mul, Subring.coe_pow]
    field_simp [zpow_ne_zero, hϖ.ne_zero]
  · exact R.mul_mem (R.pow_mem ϖ.2 _) (g 0 1).2
  · rw [Ideal.mem_span_singleton] at h
    obtain ⟨a, ha⟩ := h
    rw [ha]
    simp only [Subring.coe_mul, Subring.coe_pow]
    field_simp [zpow_ne_zero, hϖ.ne_zero]
    exact a.property

open Matrix GeneralLinearGroup in
/--
The pointwise stabilizer of the chain of lattices `L₀ - L₁ - ... - Lₙ` where `Lᵢ = (e₀, ϖ ^ n • eᵢ)`
is the subgroup of matrices in `GL₂(R)` that are upper triangular modulo `ϖ ^ n`.
We express the stabilizer of the chain as the stabilizer of the function `i ↦ Lᵢ`. Here `GL₂(K)`
acts pointwise on pi types.
-/
lemma stabilizer_fun_ntwist₂_eq_sup_comap_upperTriangularSubgroup {ϖ : R} (hϖ : Irreducible ϖ)
    (n : ℕ) :
    MulAction.stabilizer (GL (Fin 2) K)
      (fun k : Fin (n + 1) ↦ ((Pi.basisFun K (Fin 2)).ntwist₂ hϖ 0 k).toLattice (R := R)) =
    ((upperTriangularSubgroup _ _).comap
      (map (Ideal.Quotient.mk (.span {ϖ ^ n})))).map (map R.subtype) := by
  ext g
  simp_rw [MulAction.mem_stabilizer_pi]
  refine ⟨fun hg ↦ ?_, fun ⟨k, hk, heq⟩ ↦ ?_⟩
  · have h0 := hg 0
    dsimp at h0
    rw [Basis.ntwist₂_zero_zero, ← Lattice.standard,
      stabilizer_standard_eq_range_map_subtype] at h0
    obtain ⟨k, rfl⟩ := h0
    refine ⟨k, ?_, rfl⟩
    have hn := hg (Fin.last n)
    erw [mem_stabilizer_ntwist₂_iff_mem_span] at hn
    dsimp
    simp only [Set.mem_preimage, SetLike.mem_coe, mem_upperTriangularSubgroup_iff,
      val_map_apply, BlockTriangular.fin_two_iff, Fin.isValue, map_apply]
    simp only [Fin.val_last, Fin.isValue] at hn
    rwa [← RingHom.mem_ker, Ideal.mk_ker]
  · subst heq
    dsimp at hk
    simp only [Set.mem_preimage, SetLike.mem_coe, mem_upperTriangularSubgroup_iff,
      val_map_apply, BlockTriangular.fin_two_iff, Fin.isValue, map_apply] at hk
    rw [← RingHom.mem_ker, Ideal.mk_ker] at hk
    intro i
    erw [mem_stabilizer_ntwist₂_iff_mem_span]
    have : Ideal.span {ϖ ^ n} ≤ Ideal.span {ϖ ^ i.val} := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
      exact pow_dvd_pow ϖ (by omega)
    exact this hk

open Matrix GeneralLinearGroup in
/--
The pointwise stabilizer of the `GL₂(K)`-action on a family of vertices `{⟦Lᵢ⟧}ᵢ`
is `Kˣ * Stab({Lᵢ})`. We express the stabilizer of `{⟦Lᵢ⟧}ᵢ` as the stabilizer
of the function `i ↦ ⟦Lᵢ⟧`. Here `GL₂(K)` acts pointwise on pi types.
-/
lemma stabilizer_fun_mk_eq_sup {ι : Type*} (L : ι → Lattice R) :
    MulAction.stabilizer (GL (Fin 2) K) (fun i ↦ Vertices.mk (L i)) =
      (embDiagonal K (Fin 2)).range ⊔
        MulAction.stabilizer (GL (Fin 2) K) L := by
  refine le_antisymm ?_ ?_
  · intro g hg
    have (i : ι) : ∃ (u : Kˣ), (g * embDiagonal _ _ u) • L i = L i := by
      simp only [MulAction.mem_stabilizer_iff] at hg
      rw [funext_iff] at hg
      replace hg : ⟦g • L i⟧ = ⟦L i⟧ := hg i
      rw [Quotient.eq] at hg
      obtain ⟨u, hu⟩ := hg
      use u
      rwa [← (isMulCentral_embDiagonal u).comm, SemigroupAction.mul_smul,
        Lattice.embDiagonal_smul_eq_smul]
    choose u hu using this
    have hval (i : ι) : v ((g * (embDiagonal K (Fin 2)) (u i))).det = 1 :=
      (L i).valuation_det_eq_one_of_mem_stabilizer _ (hu i)
    simp only [embDiagonal_apply, map_mul, Units.val_mul, val_det_apply, «GL».val_diagonal,
      det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow] at hval
    obtain (h | ⟨⟨i⟩⟩) := isEmpty_or_nonempty ι
    · apply Subgroup.mem_sup_right
      ext i : 1
      exact h.elim i
    · have : g = (embDiagonal K (Fin 2) (u i))⁻¹ * (g * embDiagonal K (Fin 2) (u i)) := by
        rw [← mul_assoc, IsMulCentral.right_comm, inv_mul_cancel, one_mul]
        exact Matrix.GL.isMulCentral_diagonal _
      rw [this]
      refine Subgroup.mul_mem_sup (Subgroup.inv_mem _ ?_) ?_
      · use u i
      · ext j : 1
        rw [← hu, SemigroupAction.mul_smul, SemigroupAction.mul_smul,
          Lattice.embDiagonal_smul_eq_smul,
          Pi.smul_apply, Pi.smul_apply, Lattice.embDiagonal_smul_eq_smul]
        have hval : v (u i) = v (u j) := by
          have := hval i
          rw [← hval j] at this
          rwa [mul_right_inj', pow_left_inj₀] at this
          · simp
          · simp
          · simp
          · simpa using det_ne_zero g
        rw [valuation_eq_iff] at hval
        obtain ⟨a, ha⟩ := hval
        have : u i = u j * Units.map R.subtype a := by ext; simp [← ha, mul_comm]
        rw [this, SemigroupAction.mul_smul, unit_smul_eq]
  · rw [sup_le_iff]
    refine ⟨?_, fun x (h : x • L = L) ↦ ?_⟩
    · rintro - ⟨u, rfl⟩
      ext i
      change ⟦_⟧ = _
      rw [Lattice.embDiagonal_smul_eq_smul, Quotient.eq]
      exact Lattice.smul_isSimilar _ _ _
    · rw [MulAction.mem_stabilizer_iff]
      simp_rw [funext_iff, Pi.smul_apply] at h
      ext i
      change ⟦_⟧ = _
      rw [h i]

open Matrix GeneralLinearGroup in
/-- The stabilizer of the `GL₂(K)`-action on a vertex `⟦L⟧` is `Kˣ * Stab(L)`. -/
lemma stabilizer_mk_eq_sup (L : Lattice R) :
    MulAction.stabilizer (GL (Fin 2) K) (Vertices.mk L) =
      (embDiagonal K (Fin 2)).range ⊔ MulAction.stabilizer (GL (Fin 2) K) L := by
  rw [← MulAction.stabilizer_fun_const Unit, ← MulAction.stabilizer_fun_const Unit _ L,
    stabilizer_fun_mk_eq_sup]

open Pointwise in
/-- The stabilizer of the `GL₂(K)`-action on the standard vertex is `Kˣ * GL₂(R)`. -/
lemma stabilizer_mk_standard_eq_sup :
    MulAction.stabilizer (GL (Fin 2) K) (Vertices.mk <| Lattice.standard R) =
      (Matrix.GeneralLinearGroup.embDiagonal K (Fin 2)).range ⊔
        (Matrix.GeneralLinearGroup.map (n := Fin 2) R.subtype).range := by
  rw [stabilizer_mk_eq_sup, stabilizer_standard_eq_range_map_subtype]

open Matrix GeneralLinearGroup in
/--
The pointwise stabilizer of `GL₂(K)` of the segment `v₀ - v₁ - ... - vₙ` is the subgroup
`Kˣ * Iₙ` where `Iₙ` is the subgroup of `GL₂(R)` that is upper triangular
modulo `ϖ ^ n`. Here the vertex `vᵢ` is the image of the lattice `(e₀, ϖ ^ i • e₁)`.
In particular, this shows that the stabilizer of the edge `v₀ - v₁` is `Kˣ * I₁`.
-/
lemma stabilizer_fun_mk_ntwist₂_eq_sup_comap_upperTriangularSubgroup {ϖ : R} (hϖ : Irreducible ϖ)
    (n : ℕ) :
    MulAction.stabilizer (GL (Fin 2) K)
      (fun k : Fin (n + 1) ↦
        Vertices.mk <| ((Pi.basisFun K (Fin 2)).ntwist₂ hϖ 0 k).toLattice (R := R)) =
    (embDiagonal K (Fin 2)).range ⊔
      ((upperTriangularSubgroup _ _).comap
        (map (Ideal.Quotient.mk (.span {ϖ ^ n})))).map (map R.subtype) := by
  rw [stabilizer_fun_mk_eq_sup, stabilizer_fun_ntwist₂_eq_sup_comap_upperTriangularSubgroup hϖ]

end «Action»

end BruhatTits
