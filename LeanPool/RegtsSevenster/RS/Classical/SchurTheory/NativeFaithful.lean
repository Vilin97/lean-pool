/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.NativeTable

/-!
# Native block faithfulness

The representation map of the native carrier is injective on the
block (kill criterion plus the faithfulness trick) and surjective
onto the submodule endomorphisms (dimension count over canonical
instances); the sandwich identity of a nonzero block element then
pulls back to express the projector in the two-sided ideal it
generates, so an algebra map vanishing on a block element but not
on the projector is impossible.
-/

@[expose] public section

namespace RS

open Finset LinearMap

variable {G : Type*}

/-- The native representation map. -/
noncomputable abbrev nPsi
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ (subCarrier S) :=
  (rhoS S).asAlgebraHom

/-- The kill criterion for the native action. -/
theorem nPsi_eq_zero_iff
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (y : MonoidAlgebra ℂ G) :
    nPsi S y = 0 ↔ ∀ t ∈ S, y * t = 0 := by
  constructor
  · intro h0 t ht
    have happ := congrFun (congrArg (fun (f : Module.End ℂ
        (subCarrier S)) => (f : subCarrier S → subCarrier S)) h0)
      ⟨t, mem_subCarrier S ht⟩
    rw [rhoS_asAlgebraHom_apply] at happ
    have h2 := congrArg
      (fun v : subCarrier S => (v : MonoidAlgebra ℂ G)) happ
    rw [show ((y • (⟨t, mem_subCarrier S ht⟩ : subCarrier S) :
      subCarrier S) : MonoidAlgebra ℂ G) = y * t from rfl] at h2
    rw [h2]
    rfl
  · intro hk
    apply LinearMap.ext
    intro m
    rw [rhoS_asAlgebraHom_apply]
    apply Subtype.ext
    rw [show ((y • m : subCarrier S) : MonoidAlgebra ℂ G) =
      y * (m : MonoidAlgebra ℂ G) from rfl]
    rw [hk _ m.2]
    rfl

/-- Annihilation transports along equivalences of the native
representations. -/
theorem kills_of_equiv_kills_native
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (T : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hequiv : Nonempty ((rhoS S).Equiv (rhoS T)))
    (y : MonoidAlgebra ℂ G)
    (hy : ∀ s ∈ S, y * s = 0) : ∀ t ∈ T, y * t = 0 := by
  obtain ⟨e⟩ := hequiv
  rw [← nPsi_eq_zero_iff] at hy ⊢
  have hcomm := intertwiner_comp_asAlgebraHom
    (e.toLinearEquiv : subCarrier S →ₗ[ℂ] subCarrier T)
    (fun g => by
      apply LinearMap.ext
      intro v
      exact congrFun (congrArg (fun (f : subCarrier S →ₗ[ℂ]
        subCarrier T) => (f : subCarrier S → subCarrier T))
        (e.isIntertwining' g)) v) y
  apply LinearMap.ext
  intro m
  have h2 := congrFun (congrArg (fun (f : subCarrier S →ₗ[ℂ]
    subCarrier T) => (f : subCarrier S → subCarrier T)) hcomm)
    (e.toLinearEquiv.symm m)
  simp only [LinearMap.comp_apply] at h2
  rw [hy] at h2
  simp only [LinearMap.zero_apply, map_zero] at h2
  have h3 : (nPsi T y) (e.toLinearEquiv
      (e.toLinearEquiv.symm m)) = 0 := h2.symm
  rw [LinearEquiv.apply_symm_apply] at h3
  simpa using h3

open scoped Classical in
/-- A block element acting as zero on its simple kills every
simple submodule. -/
theorem natBlock_kills_of_psi_zero [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S)
    (x : MonoidAlgebra ℂ G)
    (h0 : nPsi S (nProjector S * x) = 0) :
    nProjector S * x = 0 := by
  classical
  have hkS := (nPsi_eq_zero_iff S _).mp h0
  refine eq_zero_of_kills_simples _ ?_
  intro T hT t ht
  by_cases heq : Nonempty ((rhoS S).Equiv (rhoS T))
  · exact kills_of_equiv_kills_native S T heq _ hkS t ht
  · rw [mul_assoc]
    have hxt : x * t ∈ T := T.smul_mem x ht
    rw [nProjector_mul_mem S T hS hT _ hxt, ite_eq_right heq,
      zero_smul]

open scoped Classical in
/-- The projector acts as the identity on its own simple. -/
theorem nPsi_projector_eq_one [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S) :
    nPsi S (nProjector S) = 1 := by
  classical
  apply LinearMap.ext
  intro m
  rw [show (nPsi S (nProjector S)) m = nProjector S • m from
    rhoS_asAlgebraHom_apply S _ m]
  apply Subtype.ext
  rw [show ((nProjector S • m : subCarrier S) :
    MonoidAlgebra ℂ G) = nProjector S * (m : MonoidAlgebra ℂ G)
    from rfl]
  rw [nProjector_mul_mem S S hS hS _ m.2]
  rw [ite_eq_left ⟨Representation.Equiv.refl _⟩, one_smul]
  rfl

/-- The native block. -/
noncomputable abbrev natBlock [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    Submodule ℂ (MonoidAlgebra ℂ G) :=
  LinearMap.range (mulLeft ℂ (nProjector S))

/-- The standard-coordinates equivalence of the carrier. -/
noncomputable def stdEquiv [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    subCarrier S ≃ₗ[ℂ] (Fin (nDim S) → ℂ) :=
  (Module.finBasis ℂ (subCarrier S)).equivFun

/-- The block map in standard coordinates. -/
noncomputable def mPsi [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (y : MonoidAlgebra ℂ G) :
    (Fin (nDim S) → ℂ) →ₗ[ℂ] (Fin (nDim S) → ℂ) :=
  ((stdEquiv S).toLinearMap.comp (nPsi S y)).comp
    (stdEquiv S).symm.toLinearMap

/-- The coordinate form of the block map, unfolded. -/
theorem mPsi_apply [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (y : MonoidAlgebra ℂ G)
    (v : Fin (nDim S) → ℂ) :
    mPsi S y v = stdEquiv S (nPsi S y ((stdEquiv S).symm v)) :=
  rfl

/-- It carries multiplication to composition. -/
theorem mPsi_mul [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (y y' : MonoidAlgebra ℂ G) :
    mPsi S (y * y') = (mPsi S y).comp (mPsi S y') := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, mPsi_apply, mPsi_apply, mPsi_apply]
  rw [(stdEquiv S).symm_apply_apply]
  rw [show nPsi S (y * y') = nPsi S y * nPsi S y' from
    map_mul _ _ _]
  rfl

/-- It vanishes exactly when the block map does, the coordinates
being an isomorphism. -/
theorem mPsi_zero_iff [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (y : MonoidAlgebra ℂ G) :
    mPsi S y = 0 ↔ nPsi S y = 0 := by
  constructor
  · intro h0
    apply LinearMap.ext
    intro m
    have h2 := congrFun (congrArg (fun (f : (Fin (nDim S) → ℂ)
      →ₗ[ℂ] (Fin (nDim S) → ℂ)) => (f : _ → _)) h0)
      (stdEquiv S m)
    rw [mPsi_apply, (stdEquiv S).symm_apply_apply] at h2
    have h3 := congrArg (stdEquiv S).symm h2
    simp only [LinearMap.zero_apply, map_zero,
      LinearEquiv.symm_apply_apply] at h3
    simpa using h3
  · intro h0
    apply LinearMap.ext
    intro v
    rw [mPsi_apply, h0]
    simp

/-- The projector acts as the identity on the carrier. -/
theorem mPsi_projector_eq_one [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S) :
    mPsi S (nProjector S) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro v
  rw [mPsi_apply, nPsi_projector_eq_one S hS]
  rw [show ((1 : Module.End ℂ (subCarrier S)))
    ((stdEquiv S).symm v) = (stdEquiv S).symm v from rfl]
  rw [(stdEquiv S).apply_symm_apply]
  rfl

/-- The standard-coordinates block map on the block. -/
noncomputable def mPsiLin [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    natBlock S →ₗ[ℂ]
      ((Fin (nDim S) → ℂ) →ₗ[ℂ] (Fin (nDim S) → ℂ)) where
  toFun y := mPsi S y.1
  map_add' a b := by
    apply LinearMap.ext
    intro v
    rw [show mPsi S ((a + b : natBlock S) : MonoidAlgebra ℂ G) =
      mPsi S ((a : MonoidAlgebra ℂ G) + b) from rfl]
    rw [mPsi_apply]
    rw [show nPsi S ((a : MonoidAlgebra ℂ G) + b) =
      nPsi S (a : MonoidAlgebra ℂ G) + nPsi S (b : MonoidAlgebra ℂ G)
      from map_add _ _ _]
    simp [mPsi_apply]
  map_smul' c a := by
    apply LinearMap.ext
    intro v
    rw [show mPsi S ((c • a : natBlock S) : MonoidAlgebra ℂ G) =
      mPsi S (c • (a : MonoidAlgebra ℂ G)) from rfl]
    rw [mPsi_apply]
    rw [show nPsi S (c • (a : MonoidAlgebra ℂ G)) =
      c • nPsi S (a : MonoidAlgebra ℂ G) from map_smul _ _ _]
    simp [mPsi_apply]

/-- The coordinate block map is injective. -/
theorem mPsiLin_injective [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S) :
    Function.Injective (mPsiLin S) := by
  classical
  intro a b hab
  have hd : mPsiLin S (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨w, hw⟩ := (a - b).2
  have h1 : nPsi S (nProjector S * w) = 0 := by
    rw [show nProjector S * w = ((a - b : natBlock S) :
      MonoidAlgebra ℂ G) from hw]
    exact (mPsi_zero_iff S _).mp hd
  have h2 := natBlock_kills_of_psi_zero S hS w h1
  have h3 : (a - b : natBlock S) = 0 := by
    apply Subtype.ext
    rw [← hw]
    exact h2
  exact sub_eq_zero.mp h3

/-- And surjective onto the endomorphisms, by a dimension count —
so the block is the full matrix algebra of its carrier. -/
theorem mPsiLin_surjective [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S) :
    Function.Surjective (mPsiLin S) := by
  classical
  have hrk : Module.finrank ℂ (natBlock S) =
      Module.finrank ℂ
        ((Fin (nDim S) → ℂ) →ₗ[ℂ] (Fin (nDim S) → ℂ)) := by
    rw [nProjector_block_rank S hS, Module.finrank_linearMap,
      Module.finrank_pi, Fintype.card_fin, sq]
  intro A
  refine ⟨(LinearMap.linearEquivOfInjective (mPsiLin S)
    (mPsiLin_injective S hS) hrk).symm A, ?_⟩
  exact (LinearMap.linearEquivOfInjective (mPsiLin S)
    (mPsiLin_injective S hS) hrk).apply_symm_apply A

open scoped Classical in
/-- **Native block faithfulness**: an algebra map that does not
kill the projector is injective on its block. -/
theorem nProjector_block_faithful [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S)
    {B : Type*} [Ring B] [Algebra ℂ B]
    (φ : MonoidAlgebra ℂ G →ₐ[ℂ] B)
    (hφ : φ (nProjector S) ≠ 0)
    (x : MonoidAlgebra ℂ G)
    (h0 : φ (nProjector S * x) = 0) :
    nProjector S * x = 0 := by
  classical
  by_contra hne
  have hA : mPsi S (nProjector S * x) ≠ 0 := by
    intro hz
    exact hne (natBlock_kills_of_psi_zero S hS x
      ((mPsi_zero_iff S _).mp hz))
  obtain ⟨n, U, W, hUW⟩ := exists_sum_conj_eq_one
    (V := Fin (nDim S) → ℂ) (mPsi S (nProjector S * x)) hA
  choose u hup using fun i => mPsiLin_surjective S hS (U i)
  choose w hwp using fun i => mPsiLin_surjective S hS (W i)
  have hblock : ∀ i : Fin n,
      ((u i : MonoidAlgebra ℂ G) * (nProjector S * x) *
        (w i : MonoidAlgebra ℂ G)) ∈ natBlock S := by
    intro i
    obtain ⟨a, ha⟩ := (u i).2
    exact ⟨a * (nProjector S * x) * (w i : MonoidAlgebra ℂ G),
      by
        rw [← ha]
        change nProjector S * (a * (nProjector S * x) *
          (w i : MonoidAlgebra ℂ G)) =
          nProjector S * a * (nProjector S * x) *
            (w i : MonoidAlgebra ℂ G)
        simp only [mul_assoc]⟩
  have hproj : nProjector S ∈ natBlock S :=
    ⟨nProjector S, nProjector_idem S hS⟩
  have hmem : (∑ i : Fin n,
      ((u i : MonoidAlgebra ℂ G) * (nProjector S * x) *
        (w i : MonoidAlgebra ℂ G))) ∈ natBlock S :=
    Submodule.sum_mem _ (fun i _ => hblock i)
  have hsum : (∑ i : Fin n,
      ((u i : MonoidAlgebra ℂ G) * (nProjector S * x) *
        (w i : MonoidAlgebra ℂ G))) = nProjector S := by
    have hsub : (⟨∑ i : Fin n,
        ((u i : MonoidAlgebra ℂ G) * (nProjector S * x) *
          (w i : MonoidAlgebra ℂ G)), hmem⟩ : natBlock S) =
        ∑ i : Fin n, (⟨((u i : MonoidAlgebra ℂ G) *
          (nProjector S * x) * (w i : MonoidAlgebra ℂ G)),
          hblock i⟩ : natBlock S) := by
      apply Subtype.ext
      simp
    have happly : mPsiLin S ⟨∑ i : Fin n,
        ((u i : MonoidAlgebra ℂ G) * (nProjector S * x) *
          (w i : MonoidAlgebra ℂ G)), hmem⟩ =
        mPsiLin S ⟨nProjector S, hproj⟩ := by
      rw [hsub, map_sum]
      rw [show mPsiLin S (⟨nProjector S, hproj⟩ : natBlock S) =
        mPsi S (nProjector S) from rfl]
      rw [mPsi_projector_eq_one S hS]
      rw [Finset.sum_congr rfl (fun i _ => show
        mPsiLin S (⟨((u i : MonoidAlgebra ℂ G) *
          (nProjector S * x) * (w i : MonoidAlgebra ℂ G)),
          hblock i⟩ : natBlock S) =
          U i * mPsi S (nProjector S * x) * W i from by
        rw [show mPsiLin S (⟨((u i : MonoidAlgebra ℂ G) *
          (nProjector S * x) * (w i : MonoidAlgebra ℂ G)),
          hblock i⟩ : natBlock S) =
          mPsi S ((u i : MonoidAlgebra ℂ G) *
            (nProjector S * x) * (w i : MonoidAlgebra ℂ G))
          from rfl]
        rw [mul_assoc]
        rw [mPsi_mul, mPsi_mul]
        rw [show mPsi S ((u i : MonoidAlgebra ℂ G)) = U i from
          hup i]
        rw [show mPsi S ((w i : MonoidAlgebra ℂ G)) = W i from
          hwp i]
        rfl)]
      exact hUW
    have hinj := mPsiLin_injective S hS happly
    exact congrArg Subtype.val hinj
  apply hφ
  rw [← hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, map_mul, h0, mul_zero, zero_mul]

end RS
