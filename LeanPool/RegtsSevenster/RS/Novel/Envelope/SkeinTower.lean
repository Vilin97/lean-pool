/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinLinear
import LeanPool.RegtsSevenster.RS.Novel.Skein.PermCompose
import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTensor
import LeanPool.RegtsSevenster.RS.Novel.Envelope.HookConfinement

/-!
# The skein endomorphism tower

Instantiation of the abstract `PermTower` at the skein category of
an `EdgeRankParameter R`: the family `skeinEnd f n` of endomorphism
algebras carries the symmetric-group representations given by
permutation fragments, the exponential dimension bound inherited
from the Hom-space rank bound, and vanishing propagation along the
standard embeddings (compatibility with `symCast`).

## Main definitions

* `skeinEnd f n` — the endomorphism algebra of the `n`-strand object
* `permToEnd f n` — the monoid hom `Perm (Fin n) →* skeinEnd f n`
* `skeinRep f n` — the representation `SymGroupAlgebra n →ₐ[ℂ] skeinEnd f n`
* `skeinPermTower f` — the `PermTower` instance

## Implementation notes

`skeinEnd` is defined as `CategoryTheory.End (SkeinObj.mk n)`, which
is definitionally `HomSpace f.val (n + n)`.  This lives in `Type 1`
(since `Fragment` contains `Type`-valued fields); the universe
polymorphism of `PermTower` accommodates this.

The monoid-hom direction uses `End.mul_def : x * y = y ≫ x`, so the
map `σ ↦ [permFragment σ]` is a genuine `MonoidHom` from
`Perm (Fin n)` to `End (SkeinObj.mk n)` by `permFragmentCompose`.
-/

namespace RS

open CategoryTheory

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### The endomorphism algebra -/

/-- The endomorphism ℂ-algebra of the `n`-strand object of the skein
category.  Definitionally `HomSpace f.val (n + n)`. -/
noncomputable def skeinEnd (n : ℕ) : Type 1 :=
  End (SkeinObj.mk (f := f) n)

/-- Each level of the tower is a ring. -/
noncomputable instance skeinEndRing (n : ℕ) : Ring (skeinEnd f n) :=
  inferInstanceAs (Ring (End (SkeinObj.mk (f := f) n)))

/-- And a ℂ-algebra. -/
noncomputable instance skeinEndAlgebra (n : ℕ) : Algebra ℂ (skeinEnd f n) :=
  inferInstanceAs (Algebra ℂ (End (SkeinObj.mk (f := f) n)))

/-- Its additive structure. -/
noncomputable instance skeinEndAddCommGroup (n : ℕ) :
    AddCommGroup (skeinEnd f n) :=
  inferInstanceAs (AddCommGroup (End (SkeinObj.mk (f := f) n)))

/-- And its ℂ-module structure. -/
noncomputable instance skeinEndModule (n : ℕ) : Module ℂ (skeinEnd f n) :=
  inferInstanceAs (Module ℂ (End (SkeinObj.mk (f := f) n)))

/-! ### The permutation representation -/

/-- The class of a permutation fragment in the endomorphism algebra. -/
noncomputable def permClass (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    skeinEnd f n :=
  HomSpace.ofFragment f.val (permFragment σ)

/-- The map `σ ↦ [permFragment σ]` is a monoid homomorphism.
Identity: `permFragment 1 = strandBundle n` is the categorical
identity.  Multiplication: `End.mul_def` reverses composition
order, and `permFragmentCompose τ σ` gives
`(permFragment τ).compose (permFragment σ) ≃ permFragment (σ * τ)`,
so `[P_σ] * [P_τ] = [P_τ] ≫ [P_σ] = [compose P_τ P_σ] = [P_{σ*τ}]`. -/
noncomputable def permToEnd (n : ℕ) :
    Equiv.Perm (Fin n) →* skeinEnd f n where
  toFun σ := permClass f n σ
  map_one' := by
    show HomSpace.ofFragment f.val (permFragment 1) =
      HomSpace.ofFragment f.val (strandBundle n)
    rw [permFragment_one]
  map_mul' σ τ := by
    -- Goal: permClass f n (σ * τ) = permClass f n σ * permClass f n τ
    -- End multiplication: x * y = y ≫ x (definitional)
    -- So RHS = (permClass τ) ≫ (permClass σ) = comp (permClass τ) (permClass σ)
    --        = ofFragment (compose (permFragment τ) (permFragment σ))
    --        = ofFragment (permFragment (σ * τ))
    change HomSpace.ofFragment f.val (permFragment (σ * τ)) =
      HomSpace.comp f n n n
        (HomSpace.ofFragment f.val (permFragment τ))
        (HomSpace.ofFragment f.val (permFragment σ))
    rw [HomSpace.comp_ofFragment]
    exact (HomSpace.ofFragment_congr f
      (permFragmentCompose τ σ)).symm

/-- The symmetric-group representation on the `n`-strand endomorphism
algebra: the algebra homomorphism `SymGroupAlgebra n →ₐ[ℂ] skeinEnd f n`
obtained by lifting `permToEnd` through the universal property of the
group algebra. -/
noncomputable def skeinRep (n : ℕ) :
    SymGroupAlgebra n →ₐ[ℂ] skeinEnd f n :=
  MonoidAlgebra.lift ℂ (skeinEnd f n) (Equiv.Perm (Fin n))
    (permToEnd f n)

/-- `skeinRep` on a single permutation is `permClass`. -/
theorem skeinRep_of (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    skeinRep f n (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ) =
      permClass f n σ :=
  MonoidAlgebra.lift_of (permToEnd f n) σ

/-! ### Finite-dimensionality and the rank bound -/

/-- The Hom space at arity `t` is a finite ℂ-module: its rank is
bounded by `R ^ t`, a natural number, so `rank < ℵ₀`. -/
noncomputable instance homSpace_finite (t : ℕ) :
    Module.Finite ℂ (HomSpace f.val t) := by
  rw [← Module.rank_lt_aleph0_iff]
  calc Module.rank ℂ (HomSpace f.val t)
      ≤ (R : Cardinal) ^ t := HomSpace.rank_le f t
    _ = ↑(R ^ t : ℕ) := (Nat.cast_pow R t).symm
    _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0

/-- The skein endomorphism algebra at level `n` is finite-dimensional. -/
noncomputable instance skeinEnd_finite (n : ℕ) :
    Module.Finite ℂ (skeinEnd f n) :=
  homSpace_finite f (n + n)

/-- The finrank of a Hom space is at most `R ^ t`. -/
theorem homSpace_finrank_le (t : ℕ) :
    Module.finrank ℂ (HomSpace f.val t) ≤ R ^ t := by
  have hrank := HomSpace.rank_le f t
  rw [show (R : Cardinal) ^ t = ↑(R ^ t : ℕ) from (Nat.cast_pow R t).symm]
    at hrank
  exact Module.finrank_le_of_rank_le hrank

/-- **The dimension bound**: `finrank ℂ (skeinEnd f n) ≤ R ^ (2 * n)`.
Uses `HomSpace.rank_le` at arity `n + n` and the identity `n + n = 2 * n`. -/
theorem skeinEnd_finrank_le (n : ℕ) :
    Module.finrank ℂ (skeinEnd f n) ≤ R ^ (2 * n) := by
  show Module.finrank ℂ (HomSpace f.val (n + n)) ≤ R ^ (2 * n)
  rw [show n + n = 2 * n from by omega]
  exact homSpace_finrank_le f (2 * n)

/-! ### Vanishing propagation (compat)

The geometric content: extending a permutation σ ∈ S_m by identity
strands to get σ' ∈ S_n corresponds to tensoring the permutation
fragment with identity strands:
  `permFragment σ' ≃ tensorFragment (permFragment σ) (strandBundle (n-m))`.
The linear factorization: both sides of `skeinRep n ∘ symCast h`
and `L ∘ skeinRep m` (where `L` = tensor-with-identity) agree on
group-algebra generators by the fragment equivalence, hence agree on
all elements by linearity; and linear maps send 0 to 0.
-/

/-- The tensor of a permutation fragment with identity strands is
equivalent to the extended permutation fragment. -/
noncomputable def permFragmentExtendEquiv {m k : ℕ}
    (σ : Equiv.Perm (Fin m)) (h : m ≤ m + k) :
    (tensorFragment (permFragment σ) (strandBundle k)).Equiv
      (permFragment (σ.viaEmbedding (Fin.castLEEmb h))) where
  flagEquiv :=
    (Equiv.sumProdDistrib (Fin m) (Fin k) Bool).symm.trans
      (Equiv.prodCongr finSumFinEquiv (Equiv.refl Bool))
  vertexEquiv := @Equiv.equivOfIsEmpty _ _
    (instIsEmptySum (α := Empty) (β := Empty)) Empty.instIsEmpty
  attach_comm f := by
    set τ := σ.viaEmbedding (Fin.castLEEmb h)
    rcases f with ⟨i, b⟩ | ⟨j, b⟩ <;> cases b <;>
      apply congrArg Sum.inr <;> apply Fin.ext
    · -- Sum.inl (i, false): incoming σ-strand
      -- LHS val: i.val   RHS val: (interleaveEquiv ... (Sum.inl ...)).val
      change i.val = (interleaveEquiv m m k k
        (Sum.inl (⟨i.val, by have := i.isLt; omega⟩ : Fin (m + m)))).val
      rw [show (⟨i.val, by have := i.isLt; omega⟩ : Fin (m + m)) =
          Fin.castAdd m i from Fin.ext rfl, interleaveEquiv_inl_low]; rfl
    · -- Sum.inl (i, true): outgoing σ-strand
      -- LHS val: (m+k) + (τ (Fin.castAdd k i)).val
      -- RHS val: (interleaveEquiv ... (Sum.inl ⟨m + (σ i).val, _⟩)).val
      change (m + k) + (τ (Fin.castAdd k i)).val =
        (interleaveEquiv m m k k
          (Sum.inl (⟨m + (σ i).val,
            by have := (σ i).isLt; omega⟩ : Fin (m + m)))).val
      have : (τ (Fin.castAdd k i)).val = (σ i).val := by
        rw [show (Fin.castAdd k i : Fin (m + k)) =
            Fin.castLEEmb h i from Fin.ext rfl,
          Equiv.Perm.viaEmbedding_apply]; rfl
      rw [this, show (⟨m + (σ i).val, by have := (σ i).isLt; omega⟩ :
          Fin (m + m)) = Fin.natAdd m (σ i) from Fin.ext rfl,
        interleaveEquiv_inl_high]; rfl
    · -- Sum.inr (j, false): incoming identity strand
      -- LHS val: m + j.val   RHS val: (interleaveEquiv ...).val
      change m + j.val = (interleaveEquiv m m k k
        (Sum.inr (⟨j.val, by have := j.isLt; omega⟩ : Fin (k + k)))).val
      rw [show (⟨j.val, by have := j.isLt; omega⟩ : Fin (k + k)) =
          Fin.castAdd k j from Fin.ext rfl, interleaveEquiv_inr_low]; rfl
    · -- Sum.inr (j, true): outgoing identity strand
      -- LHS val: (m+k) + (τ (Fin.natAdd m j)).val
      -- RHS val: (interleaveEquiv ... (Sum.inr ⟨k + j.val, _⟩)).val
      change (m + k) + (τ (Fin.natAdd m j)).val =
        (interleaveEquiv m m k k
          (Sum.inr (⟨k + j.val,
            by have := j.isLt; omega⟩ : Fin (k + k)))).val
      have : (τ (Fin.natAdd m j)).val = (Fin.natAdd m j).val :=
        congrArg Fin.val (Equiv.Perm.viaEmbedding_apply_of_notMem σ
          (Fin.castLEEmb h) (Fin.natAdd m j)
          (fun ⟨a, ha⟩ => absurd (congrArg Fin.val ha)
            (by simp [Fin.castLEEmb]; omega)))
      rw [this, show (⟨k + j.val, by have := j.isLt; omega⟩ :
          Fin (k + k)) = Fin.natAdd k j from Fin.ext rfl,
        interleaveEquiv_inr_high]; rfl
  pairing_comm f := by
    rcases f with ⟨i, b⟩ | ⟨j, b⟩ <;> rfl
  circles_eq := rfl

/-- The per-generator tensor identity: extending a permutation class
by identity strands agrees with tensoring. -/
theorem permClass_extend (m k : ℕ) (σ : Equiv.Perm (Fin m))
    (h : m ≤ m + k) :
    HomSpace.tensor f m m k k (permClass f m σ)
        (HomSpace.ofFragment f.val (strandBundle k)) =
      permClass f (m + k)
        (σ.viaEmbedding (Fin.castLEEmb h)) := by
  unfold permClass
  rw [HomSpace.tensor_ofFragment]
  exact HomSpace.ofFragment_congr f (permFragmentExtendEquiv σ h)

/-- Vanishing propagation: if `x` is in the kernel of the level-`m`
representation, its image under `symCast` is in the kernel at
level `n`. -/
theorem skeinRep_compat {m n : ℕ} (h : m ≤ n) (x : SymGroupAlgebra m)
    (hx : skeinRep f m x = 0) :
    skeinRep f n (symCast h x) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  -- L = tensor-with-identity: the linear map skeinEnd m →ₗ skeinEnd (m+k)
  let idClass := HomSpace.ofFragment f.val (strandBundle k)
  let L := LinearMap.flip (HomSpace.tensor f m m k k) idClass
  -- Factor: skeinRep (m+k) ∘ symCast = L ∘ skeinRep m on generators,
  -- hence on all elements by linearity.
  suffices hfact : ∀ y : SymGroupAlgebra m,
      skeinRep f (m + k) (symCast _ y) = L (skeinRep f m y) by
    exact (hfact x).trans ((congrArg L hx).trans (map_zero L))
  intro y
  apply MonoidAlgebra.induction_on y
  · intro σ
    have hsym : symCast h (MonoidAlgebra.of ℂ _ σ) =
        MonoidAlgebra.of ℂ _ (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ)
          := by
      show MonoidAlgebra.mapDomain _ (MonoidAlgebra.single σ 1) =
        MonoidAlgebra.single _ 1
      exact MonoidAlgebra.mapDomain_single
    conv_lhs => rw [hsym, skeinRep_of]
    exact ((congrArg L (skeinRep_of f m σ)).trans (permClass_extend f m k σ
      h)).symm
  · intro y₁ y₂ ih₁ ih₂
    simp only [map_add, ih₁, ih₂]
    exact (map_add L _ _).symm
  · intro c z ih
    simp only [map_smul, ih]
    exact (map_smul L c _).symm

/-! ### The tower instance -/

/-- **The skein endomorphism tower**: the `PermTower` at growth
`R ^ 2` on the family `skeinEnd f`, with the symmetric-group
representation given by permutation fragments, compatibility from
the tensor extension, and the dimension bound from the Hom-space
rank bound.  The growth constant is `R ^ 2` because the tower's
bound is `A ^ n` while the Hom-space bound is `R ^ (2n)`; its square
root, which is what the threshold `2e√A` reads, is `R`. -/
noncomputable def skeinPermTower :
    PermTower (skeinEnd f) ((R : ℝ) ^ 2) where
  rep := skeinRep f
  compat h x hx := skeinRep_compat f h x hx
  bound n := by
    have h : ((Module.finrank ℂ (skeinEnd f n) : ℕ) : ℝ)
        ≤ ((R ^ (2 * n) : ℕ) : ℝ) := by
      exact_mod_cast skeinEnd_finrank_le f n
    calc ((Module.finrank ℂ (skeinEnd f n) : ℕ) : ℝ)
        ≤ ((R ^ (2 * n) : ℕ) : ℝ) := h
      _ = ((R : ℝ) ^ 2) ^ n := by push_cast; rw [← pow_mul]

end RS
