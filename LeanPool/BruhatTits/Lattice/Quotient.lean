/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Lattice.Transvect
import LeanPool.BruhatTits.Utils.LinearAlgebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The `R ⧸ ϖ R`-vector space `L ⧸ ϖ L`

Let `L` be an `R`-lattice and `ϖ` be a uniformiser. In this file we examine
the two-dimensional `R ⧸ ϖ R`-vector space `L ⧸ ϖ L`.

## Main definitions

- `Lattice.quotient`: `L ⧸ ϖ L`.
- `Basis.toQuotient`: If `b` is an `R`-basis of the lattice `L`, this is the induced
  `R ⧸ ϖ R`-basis of `L ⧸ ϖ L`.
- `Lattice.mapIntermediate`: If `L` and `M` are lattices, this is the
  `R ⧸ ϖ R`-submodule spanned by the image of `M ⊓ L` in `L ⧸ ϖ L`.

## Main results

- `Lattice.mapIntermediate_inj_of`: `Lattice.mapIntermediate` is injective on lattices between
  `ϖ L` and `L``.

-/

open Module


suppress_compilation

variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R]

namespace BruhatTits


/-- The `R ⧸ ϖ R`-module `L ⧸ ϖ L`. We define this in terms of the maximal ideal of `R`. -/
def _root_.BruhatTits.Lattice.quotient (L : Lattice R) : Type _ :=
  L.M ⧸ (IsLocalRing.maximalIdeal R • ⊤ : Submodule R L.M)

instance (L : Lattice R) : AddCommGroup L.quotient :=
  inferInstanceAs <| AddCommGroup (L.M ⧸ (IsLocalRing.maximalIdeal R • ⊤ : Submodule R L.M))

instance _root_.BruhatTits.Lattice.quotientModule (L : Lattice R) : Module R L.quotient :=
  inferInstanceAs <| Module R (L.M ⧸ (IsLocalRing.maximalIdeal R • ⊤ : Submodule R L.M))

/-- The natural map `L → L ⧸ ϖ L`. -/
def _root_.BruhatTits.Lattice.toQuotient (L : Lattice R) : L.M →ₗ[R] L.quotient :=
  (IsLocalRing.maximalIdeal R • ⊤ : Submodule R L.M).mkQ

open IsLocalRing

instance (L : Lattice R) : Module (ResidueField R) L.quotient :=
  inferInstanceAs <|
    Module (R ⧸ maximalIdeal R) (L.M ⧸ (maximalIdeal R • ⊤ : Submodule R L.M))


instance (priority := 9999999) instSMulSubtypeMemSubringQuotientIdealMaximalIdealLeanPool :
    SMul (↥R) (↥R ⧸ maximalIdeal ↥R) :=
  Submodule.Quotient.instSMul (maximalIdeal ↥R)

instance (priority := 9999999) (L : Lattice R) :
    SMul (↥R ⧸ maximalIdeal ↥R) (↥L.M ⧸ (maximalIdeal ↥R • ⊤ : Submodule R L.M)) :=
  (Module.instQuotientIdealSubmoduleHSMulTop (↥L.M) (maximalIdeal ↥R)).toSMul

instance (L : Lattice R) : IsScalarTower R (ResidueField R) L.quotient where
  smul_assoc r c x := by
    refine Quotient.inductionOn' c ?_
    intro c
    refine Quotient.inductionOn' x ?_
    intro x
    change Submodule.Quotient.mk ((r * c) • x) = Submodule.Quotient.mk (r • c • x)
    rw [mul_smul]

lemma _root_.BruhatTits.Lattice.quotient_finrank [IsFractionRing R K] (L : Lattice R) :
    Module.finrank (ResidueField R) L.quotient = 2 := by
  change Module.finrank (R ⧸ maximalIdeal R) (L.M ⧸ (maximalIdeal R • ⊤ : Submodule R L.M)) =
    Fintype.card (Fin 2)
  apply quotient_finrank_eq
  exact L.basis

/-- If `b` is an `R`-basis of the lattice `L`, this is the induced
`R ⧸ ϖ R`-basis of `L ⧸ ϖ L`. -/
def _root_.Module.Basis.toQuotient [IsFractionRing R K] {L : Lattice R} (b : Basis (Fin 2) R L.M) :
    Basis (Fin 2) (ResidueField R) L.quotient :=
  let v (i : Fin 2) : L.quotient := L.toQuotient (b i)
  have hsp : ⊤ ≤ Submodule.span (ResidueField R) (Set.range v) := by
    rintro x -
    refine Quotient.inductionOn' x (fun x ↦ ?_)
    have hx : x ∈ Submodule.span R (Set.range b) := by
      rw [b.span_eq]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      apply Submodule.subset_span
      use i
      rfl
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      exact Submodule.smul_mem _ (Ideal.Quotient.mk _ a) hx
  have hli : LinearIndependent (ResidueField R) v := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank hsp
    exact L.quotient_finrank.symm
  Basis.mk hli hsp

instance [IsFractionRing R K] (L : Lattice R) : Module.Free (ResidueField R) L.quotient :=
  Module.Free.of_basis L.basis.toQuotient

instance [IsFractionRing R K] (L : Lattice R) : Module.Finite (ResidueField R) L.quotient := by
  apply Module.finite_of_finrank_eq_succ
  rw [L.quotient_finrank]

/-- Variant of `Basis.toQuotient` for the lattice spanned by `b`. -/
def _root_.Module.Basis.toQuotient' [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) :
    Basis (Fin 2) (ResidueField R) (b.toLattice (R := R)).quotient :=
  (b.restrictToLattice (R := R)).toQuotient

lemma _root_.Module.Basis.toQuotient'_apply [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) (i : Fin 2) :
    b.toQuotient' (R := R) i =
      Submodule.Quotient.mk
        (p := (maximalIdeal R • ⊤ : Submodule R _)) (b.restrict (R := R) i) := by
  simp [Basis.toQuotient', Basis.toQuotient, Basis.restrictToLattice]
  rfl

/-- `Basis.transvect` pushed to `L ⧸ ϖ L` where `L` is the lattice generated by `b`. -/
def _root_.Module.Basis.transvectResidue [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    Basis (Fin 2) (ResidueField R) (b.toLattice (R := R)).quotient :=
  let bQ := b.toQuotient' (R := R)
  bQ.transvect (Ideal.Quotient.mk _ x)

@[simp] lemma _root_.Module.Basis.transvectResidue_apply₀ [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    b.transvectResidue x 0 = b.toQuotient' (R := R) 0 := by
  simp [Basis.transvectResidue]

@[simp] lemma _root_.Module.Basis.transvectResidue_apply₁ [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    b.transvectResidue x 1 = x • b.toQuotient' (R := R) 0 + b.toQuotient' (R := R) 1 := by
  simp [Basis.transvectResidue]; rfl

/-- `Basis.unipotent` pushed to `L ⧸ ϖ L` where `L` is the lattice generated by `b`. -/
def _root_.Module.Basis.unipotentResidue [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    (b.toLattice (R := R)).quotient ≃ₗ[ResidueField R] (b.toLattice (R := R)).quotient :=
  let bQ := b.toQuotient' (R := R)
  bQ.equiv (b.transvectResidue x) (Equiv.refl _)

lemma _root_.Module.Basis.unipotentResidue_apply₁ [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    (b.unipotentResidue x) (b.toQuotient' (R := R) 1) =
      x • (b.toQuotient' (R := R) 0) + (b.toQuotient' (R := R) 1) := by
  simp [Basis.unipotentResidue]

lemma _root_.Module.Basis.unipotentResidue_apply₀ [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    (b.unipotentResidue x) (b.toQuotient' (R := R) 0) =
      (b.toQuotient' (R := R) 0) := by
  simp [Basis.unipotentResidue]

lemma _root_.Module.Basis.transvectEquiv_apply_mem (b : Basis (Fin 2) K (Fin 2 → K)) (x : R)
    (y : b.toSubmodule (R := R)) :
    b.transvectEquiv x y ∈ b.toSubmodule (R := R) := by
  apply b.transvectEquiv_mem_of_mem
  exact y.property

lemma _root_.Module.Basis.unipotentResidue_mk [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K))
    (x : R) (y : b.toSubmodule (R := R)) :
    (b.unipotentResidue x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (⟨b.transvectEquiv x y, b.transvectEquiv_apply_mem x y⟩) := by
  let b' : Basis (Fin 2) R (b.toSubmodule (R := R)) := b.restrict
  have : y ∈ Submodule.span R (Set.range b') := by
    rw [b'.span_eq]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ this
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    have h0 : b 0 = (b.restrict (R := R) 0).val := by
      simp
    have h1 : b 1 = (b.restrict (R := R) 1).val := by
      simp
    have hq :
        (Submodule.Quotient.mk
          (p := (maximalIdeal R • ⊤ : Submodule R (b.toLattice (R := R)).M)) (b' i)) =
          b.toQuotient' (R := R) i := by
      exact (b.toQuotient'_apply (R := R) i).symm
    rw [hq]
    match i with
    | 0 =>
      rw [b.unipotentResidue_apply₀]
      simp only [Fin.isValue, b.toQuotient'_apply, Basis.toLattice_module, Basis.restrict_apply,
        Basis.transvectEquiv_apply₀, b']
      simp_rw [h0]
      rfl
    | 1 =>
      rw [b.unipotentResidue_apply₁]
      simp only [Fin.isValue, b.toQuotient'_apply, Basis.toLattice_module, Basis.restrict_apply,
        Basis.transvectEquiv_apply₁, b']
      simp_rw [h0, h1]
      rfl
  · let z : (b.toLattice (R := R)).M :=
      ⟨(b.transvectEquiv x) ↑(0 : b.toSubmodule (R := R)),
        b.transvectEquiv_apply_mem x 0⟩
    have hmk0 :
        (Submodule.Quotient.mk
          (p := (maximalIdeal R • ⊤ : Submodule R (b.toLattice (R := R)).M))
          (0 : (b.toLattice (R := R)).M)) = 0 := rfl
    have hz : z = 0 := by
      ext i
      simp [z]
    calc
      (b.unipotentResidue x) (Submodule.Quotient.mk 0) =
          (b.unipotentResidue x) (0 : (b.toLattice (R := R)).quotient) := by
            rw [hmk0]
            rfl
      _ = 0 := map_zero (b.unipotentResidue x)
      _ = Submodule.Quotient.mk z := by
            rw [hz]
            rfl
  · intro u v _ _ hu hv
    calc
      (b.unipotentResidue x) (Submodule.Quotient.mk (u + v)) =
          (b.unipotentResidue x) (Submodule.Quotient.mk u + Submodule.Quotient.mk v) := by rfl
      _ = (b.unipotentResidue x) (Submodule.Quotient.mk u) +
          (b.unipotentResidue x) (Submodule.Quotient.mk v) := by
            exact map_add (b.unipotentResidue x) (Submodule.Quotient.mk u)
              (Submodule.Quotient.mk v)
      _ = Submodule.Quotient.mk ⟨(b.transvectEquiv x) ↑u, b.transvectEquiv_apply_mem x u⟩ +
          Submodule.Quotient.mk ⟨(b.transvectEquiv x) ↑v, b.transvectEquiv_apply_mem x v⟩ := by
            exact congrArg₂ (fun p q => p + q) hu hv
      _ = Submodule.Quotient.mk
          ⟨(b.transvectEquiv x) ↑(u + v), b.transvectEquiv_apply_mem x (u + v)⟩ := by
            exact (Submodule.Quotient.eq _).mpr (by
              let z1 : (b.toLattice (R := R)).M :=
                ⟨(b.transvectEquiv x) ↑u, b.transvectEquiv_apply_mem x u⟩
              let z2 : (b.toLattice (R := R)).M :=
                ⟨(b.transvectEquiv x) ↑v, b.transvectEquiv_apply_mem x v⟩
              let z3 : (b.toLattice (R := R)).M :=
                ⟨(b.transvectEquiv x) ↑(u + v), b.transvectEquiv_apply_mem x (u + v)⟩
              have hz : z1 + z2 - z3 = 0 := by
                rw [sub_eq_zero]
                ext i
                change (b.transvectEquiv x) ↑u i + (b.transvectEquiv x) ↑v i =
                  (b.transvectEquiv x) ↑(u + v) i
                simp [map_add]
              change z1 + z2 - z3 ∈
                (maximalIdeal R • ⊤ : Submodule R (b.toLattice (R := R)).M)
              rw [hz]
              exact Submodule.zero_mem _)
  · intro a u _ hu
    calc
      (b.unipotentResidue x) (Submodule.Quotient.mk (a • u)) =
          (b.unipotentResidue x) (a • Submodule.Quotient.mk u) := by rfl
      _ = a • (b.unipotentResidue x) (Submodule.Quotient.mk u) := by
            exact LinearMap.CompatibleSMul.map_smul (b.unipotentResidue x).toLinearMap a
              (Submodule.Quotient.mk u)
      _ = a • Submodule.Quotient.mk
          ⟨(b.transvectEquiv x) ↑u, b.transvectEquiv_apply_mem x u⟩ := by
            exact congrArg (fun z => a • z) hu
      _ = Submodule.Quotient.mk
          ⟨(b.transvectEquiv x) ↑(a • u), b.transvectEquiv_apply_mem x (a • u)⟩ := by
            exact (Submodule.Quotient.eq _).mpr (by
              let z1 : (b.toLattice (R := R)).M :=
                ⟨(b.transvectEquiv x) ↑u, b.transvectEquiv_apply_mem x u⟩
              let z2 : (b.toLattice (R := R)).M :=
                ⟨(b.transvectEquiv x) ↑(a • u), b.transvectEquiv_apply_mem x (a • u)⟩
              have hz : a • z1 - z2 = 0 := by
                rw [sub_eq_zero]
                ext i
                change ↑a * (b.transvectEquiv x) ↑u i =
                  (b.transvectEquiv x) ↑(a • u) i
                simp [Subring.smul_def, map_smul]
              change a • z1 - z2 ∈
                (maximalIdeal R • ⊤ : Submodule R (b.toLattice (R := R)).M)
              rw [hz]
              exact Submodule.zero_mem _)

/-- If `L` is a lattice and `M` any submodule of `K^2`, this is the image
of `M ⊓ L` in `L ⧸ ϖ L` as a `R ⧸ ϖ R`-submodule. -/
def _root_.BruhatTits.Lattice.mapIntermediateSubmodule
    (L : Lattice R) (M : Submodule R (Fin 2 → K)) :
    Submodule (ResidueField R) L.quotient :=
  let M' : Submodule R (L.M ⧸ (maximalIdeal R • ⊤ : Submodule R L.M)) :=
    (M.comap L.M.subtype).map L.toQuotient
  {
    toAddSubmonoid := M'.toAddSubmonoid
    smul_mem' := by
      intro c x hx
      refine Quotient.inductionOn' c (fun c ↦ ?_)
      change c • x ∈ M'
      exact M'.smul_mem c hx
  }

/-- Variant of `Lattice.mapIntermediateSubmodule` where `M` is a second lattice. This is
the most frequent use case. -/
def _root_.BruhatTits.Lattice.mapIntermediate (L M : Lattice R) :
    Submodule (ResidueField R) L.quotient :=
  L.mapIntermediateSubmodule M.M

lemma _root_.BruhatTits.Lattice.mem_mapIntermediate (L M : Lattice R) (x : L.quotient) :
    x ∈ L.mapIntermediate M ↔ ∃ y : L.M, y.val ∈ M.M ∧ x = L.toQuotient y := by
  rw [Lattice.mapIntermediate, Lattice.mapIntermediateSubmodule]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

/-- `Lattice.mapIntermediateSubmodule` is injective on submodules between `ϖ L` and `L``. -/
lemma _root_.BruhatTits.Lattice.mapIntermediateSubmodule_inj_of
    (L : Lattice R) (M₁ M₂ : Submodule R (Fin 2 → K))
    (hle₁ : M₁ ≤ L.M) (hge₁ : IsLocalRing.maximalIdeal R • L.M ≤ M₁)
    (hle₂ : M₂ ≤ L.M) (hge₂ : IsLocalRing.maximalIdeal R • L.M ≤ M₂)
    (h : L.mapIntermediateSubmodule M₁ = L.mapIntermediateSubmodule M₂) :
    M₁ = M₂ := by
  let p : Submodule R L.M := IsLocalRing.maximalIdeal R • ⊤
  have hp : p = (IsLocalRing.maximalIdeal R • L.M).comap L.M.subtype := by
    simp [p]
  let Q₁ : Submodule R L.M := M₁.comap L.M.subtype
  let Q₂ : Submodule R L.M := M₂.comap L.M.subtype
  have hQ₁ : p ≤ Q₁ := by
    rw [hp]
    apply Submodule.comap_mono
    exact hge₁
  have hQ₂ : p ≤ Q₂ := by
    rw [hp]
    apply Submodule.comap_mono
    exact hge₂
  have h' : Q₁.map p.mkQ = Q₂.map p.mkQ := by
    rwa [← SetLike.coe_set_eq] at h ⊢
  have h'' : p.comapMkQRelIso.symm ⟨Q₁, hQ₁⟩ = p.comapMkQRelIso.symm ⟨Q₂, hQ₂⟩ := h'
  have h1 := p.comapMkQRelIso.symm.injective h''
  replace h1 : Q₁ = Q₂ := congrArg Subtype.val h1
  have hM₁ : M₁ ≤ LinearMap.range L.M.subtype := by simpa
  have hM₂ : M₂ ≤ LinearMap.range L.M.subtype := by simpa
  rw [← Submodule.map_comap_eq_self hM₁, ← Submodule.map_comap_eq_self hM₂]
  exact congrArg _ h1

/-- `Lattice.mapIntermediate` is injective on lattices between `ϖ L` and `L``. -/
lemma _root_.BruhatTits.Lattice.mapIntermediate_inj_of (L M₁ M₂ : Lattice R)
    (hle₁ : M₁.M ≤ L.M) (hge₁ : IsLocalRing.maximalIdeal R • L.M ≤ M₁.M)
    (hle₂ : M₂.M ≤ L.M) (hge₂ : IsLocalRing.maximalIdeal R • L.M ≤ M₂.M)
    (h : L.mapIntermediate M₁ = L.mapIntermediate M₂) :
    M₁ = M₂ := by
  apply Lattice.ext
  exact L.mapIntermediateSubmodule_inj_of _ _ hle₁ hge₁ hle₂ hge₂ h

/-- The image of the lattice spanned by `(ϖ • b₀, b₁)` in `L ⧸ ϖ L`
where `L` is spanned by `(b₀, b₁)`. -/
def _root_.Module.Basis.quotientStdLine₀ (b : Basis (Fin 2) K (Fin 2 → K))
    {ϖ : R} (hϖ : Irreducible ϖ) :
    Submodule (ResidueField R) (b.toLattice (R := R)).quotient :=
  (b.toLattice (R := R)).mapIntermediate (b.ntwist₂ hϖ 1 0).toLattice

/-- The image of the lattice spanned by `(b₀, ϖ • b₁)` in `L ⧸ ϖ L`
where `L` is spanned by `(b₀, b₁)`. -/
def _root_.Module.Basis.quotientStdLine₁ (b : Basis (Fin 2) K (Fin 2 → K))
    {ϖ : R} (hϖ : Irreducible ϖ) :
    Submodule (ResidueField R) (b.toLattice (R := R)).quotient :=
  (b.toLattice (R := R)).mapIntermediate (b.ntwist₂ hϖ 0 1).toLattice

/-- The image of the span of `(ϖ • b₀, b₁)` in `L ⧸ ϖ L` is the submodule generated
by the image of `b₁`. -/
lemma mapIntermediate_stdLine₀ [IsFractionRing R K] (b : Basis (Fin 2) K (Fin 2 → K))
    {ϖ : R} (hϖ : Irreducible ϖ) :
    b.quotientStdLine₀ hϖ = Submodule.span (ResidueField R) { b.toQuotient' (R := R) 1 } := by
  simp only [Basis.quotientStdLine₀, Fin.isValue]
  ext x
  constructor
  · intro hx
    rw [Lattice.mem_mapIntermediate] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    replace hy : y.val ∈ (b.ntwist₂ hϖ 1 0).toSubmodule := hy
    obtain ⟨α, β, hab⟩ := b.is_linear_comb_of_mem_ntwist hϖ y hy
    simp only [pow_one, Fin.isValue, pow_zero, one_smul] at hab
    rw [Submodule.mem_span_singleton]
    use Ideal.Quotient.mk _ β
    simp only [hab, Fin.isValue, Basis.toQuotient'_apply, Basis.toLattice_module, map_add, map_smul]
    have : residue R ϖ = 0 := by
      change (Ideal.Quotient.mk (maximalIdeal R)) ϖ = (0 : R ⧸ maximalIdeal R)
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal, mem_nonunits_iff]
      exact hϖ.not_isUnit
    have : α • ϖ • (b.toLattice (R := R)).toQuotient (b.restrict (R := R) 0) = 0 := by
      change α • residue R ϖ • (b.toLattice (R := R)).toQuotient (b.restrict (R := R) 0) = 0
      rw [this]
      simp
    erw [this]
    simp only [Fin.isValue, zero_add]
    rfl
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    refine Quotient.inductionOn' a (fun a ↦ ?_)
    rw [Lattice.mem_mapIntermediate]
    refine ⟨a • b.restrictToLattice (R := R) 1, ?_, ?_⟩
    · change _ ∈ Submodule.span R _
      simp only [Basis.toLattice_module, Fin.isValue]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      use 1
      simpa [Basis.restrictToLattice, Basis.ntwist₂_apply₁] using
        (Basis.restrictToLattice_apply (R := R) b 1).symm
    · simp only [Fin.isValue, Basis.toLattice_module, Basis.restrictToLattice]
      rw [Basis.toQuotient'_apply]
      rfl

/-- The image of the span of `(b₀, ϖ • b₁)` in `L ⧸ ϖ L` is the submodule generated
by the image of `b₀`. -/
lemma mapIntermediate_stdLine₁ [IsFractionRing R K] (b : Basis (Fin 2) K (Fin 2 → K))
    {ϖ : R} (hϖ : Irreducible ϖ) :
    b.quotientStdLine₁ hϖ = Submodule.span (ResidueField R) { b.toQuotient' (R := R) 0 } := by
  simp only [Basis.quotientStdLine₁, Fin.isValue]
  ext x
  constructor
  · intro hx
    rw [Lattice.mem_mapIntermediate] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    replace hy : y.val ∈ (b.ntwist₂ hϖ 0 1).toSubmodule := hy
    obtain ⟨α, β, hab⟩ := b.is_linear_comb_of_mem_ntwist hϖ y hy
    simp only [pow_zero, Fin.isValue, one_smul, pow_one] at hab
    rw [Submodule.mem_span_singleton]
    use Ideal.Quotient.mk _ α
    rw [hab]
    simp only [Fin.isValue, Basis.toQuotient'_apply, Basis.toLattice_module, map_add, map_smul]
    have : residue R ϖ = 0 := by
      change (Ideal.Quotient.mk (maximalIdeal R)) ϖ = (0 : R ⧸ maximalIdeal R)
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal, mem_nonunits_iff]
      exact hϖ.not_isUnit
    have : β • ϖ • (b.toLattice (R := R)).toQuotient (b.restrict (R := R) 1) = 0 := by
      change β • residue R ϖ • (b.toLattice (R := R)).toQuotient (b.restrict (R := R) 1) = 0
      rw [this]
      simp
    erw [this]
    simp
    rfl
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    refine Quotient.inductionOn' a (fun a ↦ ?_)
    rw [Lattice.mem_mapIntermediate]
    refine ⟨a • b.restrictToLattice (R := R) 0, ?_, ?_⟩
    · change _ ∈ Submodule.span R _
      simp only [Basis.toLattice_module, Fin.isValue]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      use 0
      simpa [Basis.restrictToLattice, Basis.ntwist₂_apply₀] using
        (Basis.restrictToLattice_apply (R := R) b 0).symm
    · simp only [Fin.isValue, Basis.toLattice_module, Basis.restrictToLattice]
      rw [Basis.toQuotient'_apply]
      rfl

open Pointwise

lemma _root_.BruhatTits.Lattice.mapIntermediate_ne_bot_of (L M : Lattice R)
    {ϖ : R} (hϖ : Irreducible ϖ)
    (h1 : M.M ≤ L.M)
    (h2 : ϖ • L.M < M.M) :
    L.mapIntermediate M ≠ ⊥ := by
  let p : Submodule R L.M := IsLocalRing.maximalIdeal R • ⊤
  have hp : p = (IsLocalRing.maximalIdeal R • L.M).comap L.M.subtype := by
    simp [p]
  have : ⊥ = L.mapIntermediateSubmodule (ϖ • L.M) := by
    rw [← SetLike.coe_set_eq, ← maximalIdeal_smul_eq_uniformizer_smul _ hϖ,
      ← Submodule.carrier_eq_coe, ← Submodule.carrier_eq_coe]
    dsimp only [Lattice.mapIntermediateSubmodule, Lattice.toQuotient]
    rw [Submodule.bot_toAddSubmonoid, ← hp, Submodule.mkQ_map_self]
    rfl
  rw [this]
  intro heq
  have : M.M = ϖ • L.M := by
    apply L.mapIntermediateSubmodule_inj_of _ _ h1
    · apply le_of_lt
      rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
      exact h2
    · exact Submodule.smul_le_self_of_tower ϖ L.M
    · rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
    · exact heq
  rw [this] at h2
  simp at h2

lemma _root_.BruhatTits.Lattice.mapIntermediate_ne_top_of (L M : Lattice R)
    {ϖ : R} (hϖ : Irreducible ϖ) (h1 : M.M < L.M) (h2 : ϖ • L.M ≤ M.M) :
    L.mapIntermediate M ≠ ⊤ := by
  have : ⊤ = L.mapIntermediateSubmodule L.M := by
    rw [← SetLike.coe_set_eq, ← Submodule.carrier_eq_coe, ← Submodule.carrier_eq_coe]
    simp only [Submodule.top_toAddSubmonoid, Lattice.mapIntermediateSubmodule, Lattice.toQuotient,
      Submodule.comap_subtype_self, Submodule.map_top]
    have := (maximalIdeal R • ⊤ : Submodule R L.M).mkQ_surjective
    rw [← LinearMap.range_eq_top] at this
    rw [this]
    rfl
  rw [this]
  intro heq
  have : M.M = L.M := by
    apply L.mapIntermediateSubmodule_inj_of
    · apply le_of_lt
      exact h1
    · rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
      exact h2
    · rfl
    · rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
      exact Submodule.smul_le_self_of_tower ϖ L.M
    · exact heq
  rw [this] at h1
  simp at h1

variable [IsFractionRing R K]

lemma _root_.BruhatTits.Lattice.mapIntermediate_finrank_eq_one_of
    {L M : Lattice R} {ϖ : R} (hϖ : Irreducible ϖ)
    (h1 : M.M < L.M)
    (h2 : ϖ • L.M < M.M) :
    Module.finrank (ResidueField R) (L.mapIntermediate M) = 1 := by
  have hM'_ne_bot : L.mapIntermediate M ≠ ⊥ := by
    apply Lattice.mapIntermediate_ne_bot_of _ _ hϖ
    · apply le_of_lt
      exact h1
    · exact h2
  have hM'_ne_top : L.mapIntermediate M ≠ ⊤ := by
    apply Lattice.mapIntermediate_ne_top_of _ _ hϖ
    · exact h1
    · apply le_of_lt
      exact h2
  have h1' : Module.finrank (ResidueField R) (L.mapIntermediate M) < 2 := by
    rw [← L.quotient_finrank]
    apply Submodule.finrank_lt_finrank_of_ne_top
    exact hM'_ne_top
  have h2' : 0 < Module.finrank (ResidueField R) (L.mapIntermediate M) := by
    apply Submodule.zero_lt_finrank_of_ne_bot
    exact hM'_ne_bot
  omega

lemma _root_.BruhatTits.Lattice.mapIntermediate_eq_span''
    (b : Basis (Fin 2) K (Fin 2 → K)) (M : Lattice R)
    {ϖ : R} (hϖ : Irreducible ϖ)
    (h1 : M.M < b.toSubmodule)
    (h2 : ϖ • b.toSubmodule < M.M)
    (h3 : M.M ≠ (b.ntwist₂ hϖ 0 1).toSubmodule) :
    ∃ (α : R), b.toLattice.mapIntermediate M =
      Submodule.span (ResidueField R)
        {α • b.toQuotient' (R := R) 0 + b.toQuotient' (R := R) 1} := by
  let M' : Submodule (ResidueField R) b.toLattice.quotient := b.toLattice.mapIntermediate M
  have ht : M' ≠ Submodule.span (ResidueField ↥R) {b.toQuotient' 0} := by
    rw [← mapIntermediate_stdLine₁ b hϖ]
    intro heq
    apply h3
    have : (b.ntwist₂ hϖ 0 1).toLattice = M := by
      apply b.toLattice.mapIntermediate_inj_of
      · apply b.ntwist₂_toSubmodule_le
      · rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ, Basis.toLattice_module]
        nth_rw 1 [← b.ntwist₂_zero_zero hϖ]
        rw [b.smul_ntwist₂]
        apply b.ntwist₂_toSubmodule_le_ntwist₂_toSubmodule
        · simp
        · simp
      · apply le_of_lt h1
      · rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
        exact le_of_lt h2
      · exact heq.symm
    rw [← this]
    simp
  have hr : Module.finrank (ResidueField R) M' = 1 :=
    Lattice.mapIntermediate_finrank_eq_one_of hϖ h1 h2
  obtain ⟨a, ha⟩ := Submodule.exists_generator_of_finrank_eq_one_basis
    (b.toQuotient' (R := R)) M' hr ht
  obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective a
  use α
  exact ha

/-- The action of `b.unipotent` on lattices commutes with the projection `L` to `L ⧸ ϖ L`. -/
lemma mapIntermediate_unipotent_smul (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) (M : Lattice R) :
    (b.toLattice (R := R)).mapIntermediate (b.unipotent x • M) =
      ((b.toLattice (R := R)).mapIntermediate M).map (b.unipotentResidue x).toLinearMap := by
  apply le_antisymm
  · intro x hx
    rw [Lattice.mem_mapIntermediate] at hx
    obtain ⟨y, hymem, rfl⟩ := hx
    rw [Lattice.smul_M, Matrix.GeneralLinearGroup.mem_smul] at hymem
    obtain ⟨m, hm, heq⟩ := hymem
    rw [Basis.unipotent_mulVec] at heq
    have hmL : m ∈ (b.toLattice (R := R)).M := by
      have : m = (b.transvectEquiv x).symm ((b.transvectEquiv x) m) := by simp
      rw [this, heq]
      apply b.transvectEquiv_symm_mem_of_mem
      exact y.property
    let y' : (b.toLattice (R := R)).M := ⟨b.transvectEquiv x m, by
      rw [heq]
      exact y.property⟩
    have : y = y' := by
      ext : 1
      rw [← heq]
    simp only [this, Basis.toLattice_module, Submodule.mem_map, Basis.toLattice_module, y']
    refine ⟨Submodule.Quotient.mk ⟨m, hmL⟩, ?_, ?_⟩
    · rw [Lattice.mem_mapIntermediate]
      refine ⟨⟨m, hmL⟩, hm, rfl⟩
    · convert Basis.unipotentResidue_mk (R := R) b x (⟨m, hmL⟩ : b.toSubmodule (R := R)) using 1
      · rfl
      · rfl
  · rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [(b.toLattice (R := R)).mem_mapIntermediate] at hy
    obtain ⟨m, hmmem, rfl⟩ := hy
    simp only [Basis.toLattice_module, Submodule.mem_comap]
    rw [(b.toLattice (R := R)).mem_mapIntermediate]
    have hmL : b.transvectEquiv x m ∈ (b.toLattice (R := R)).M := by
      apply b.transvectEquiv_mem_of_mem
      exact m.property
    refine ⟨⟨b.transvectEquiv x m, hmL⟩, ?_, ?_⟩
    · rw [Lattice.smul_M, Matrix.GeneralLinearGroup.mem_smul]
      refine ⟨m, hmmem, ?_⟩
      rw [Basis.unipotent_mulVec]
    · erw [Basis.unipotentResidue_mk]
      rfl

/-- Variant of `mapIntermediate_unipotent_smul` for the lattice spanned by `(ϖ ^ n • b₀, b₁)`. -/
lemma mapIntermediate_unipotent_smul' (b : Basis (Fin 2) K (Fin 2 → K)) (x : R)
    (M : Lattice R) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    ((b.ntwist₂ hϖ n 0).toLattice (R := R)).mapIntermediate (b.unipotent (ϖ ^ n * x) • M) =
      (((b.ntwist₂ hϖ n 0).toLattice (R := R)).mapIntermediate M).map
        ((b.ntwist₂ hϖ n 0).unipotentResidue x).toLinearMap := by
  rw [Basis.unipotent_pow_irred_mul_eq (hϖ := hϖ)]
  apply mapIntermediate_unipotent_smul

end BruhatTits
