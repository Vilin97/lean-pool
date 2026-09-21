/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.AtomDichotomy

/-!
# The matrix-envelope trace and semisimplicity

The diagonal trace on endomorphisms of matrix-envelope objects:
linear, cyclic, and nondegenerate (entrywise, via single-entry
test matrices).  Semisimplicity of every `End M` follows from the
trace criterion once nilpotents are known to have vanishing trace,
which the atom decomposition supplies.
-/

namespace RS

open CategoryTheory CategoryTheory.Idempotents

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### Linear structure on the matrix envelope -/

/-- Scaling a matrix of morphisms entrywise. -/
noncomputable instance matHomSMul (M N : Mat_ (Karoubi (SkeinObj f))) :
    SMul ℂ (M ⟶ N) where
  smul c φ := fun i j => c • φ i j

/-- The matrix layer's hom-sets are ℂ-modules. -/
noncomputable instance matHomModule
    (M N : Mat_ (Karoubi (SkeinObj f))) : Module ℂ (M ⟶ N) where
  one_smul φ := by funext i j; exact one_smul ℂ (φ i j)
  mul_smul c d φ := by funext i j; exact mul_smul c d (φ i j)
  smul_zero c := by funext i j; exact smul_zero c
  smul_add c φ ψ := by
    funext i j
    show c • (φ i j + ψ i j) = c • φ i j + c • ψ i j
    exact smul_add c _ _
  add_smul c d φ := by
    funext i j
    show (c + d) • φ i j = c • φ i j + d • φ i j
    exact add_smul c d _
  zero_smul φ := by funext i j; exact zero_smul ℂ (φ i j)

/-- Hence the matrix layer is ℂ-linear. -/
noncomputable instance matLinear :
    CategoryTheory.Linear ℂ (Mat_ (Karoubi (SkeinObj f))) where
  smul_comp M N K c φ ψ := by
    funext i k
    show ∑ j, (c • φ i j) ≫ ψ j k = c • ∑ j, φ i j ≫ ψ j k
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [CategoryTheory.Linear.smul_comp]
  comp_smul M N K φ c ψ := by
    funext i k
    show ∑ j, φ i j ≫ (c • ψ j k) = c • ∑ j, φ i j ≫ ψ j k
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [CategoryTheory.Linear.comp_smul]

/-! ### The diagonal trace -/

/-- The diagonal trace on matrix-envelope endomorphisms. -/
noncomputable def matTrace (M : Mat_ (Karoubi (SkeinObj f))) :
    End M →ₗ[ℂ] ℂ where
  toFun φ := ∑ i : M.ι,
    HomSpace.traceMap f.val (M.X i).X.arity (φ i i).f
  map_add' φ ψ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ((φ + ψ) i i).f = (φ i i).f + (ψ i i).f from rfl,
      map_add]
  map_smul' c φ := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ((c • φ) i i).f = c • (φ i i).f from rfl,
      map_smul, smul_eq_mul]

/-- Karoubi-level mixed cyclicity. -/
private theorem karoubi_trace_comm
    {X Y : Karoubi (SkeinObj f)} (a : X ⟶ Y) (b : Y ⟶ X) :
    HomSpace.traceMap f.val X.X.arity (a.f ≫ b.f) =
      HomSpace.traceMap f.val Y.X.arity (b.f ≫ a.f) :=
  HomSpace.traceMap_comp_comm f a.f b.f

/-- **Cyclicity of the diagonal trace.** -/
theorem matTrace_comp_comm {M N : Mat_ (Karoubi (SkeinObj f))}
    (α : M ⟶ N) (β : N ⟶ M) :
    matTrace f M (α ≫ β) = matTrace f N (β ≫ α) := by
  show (∑ i : M.ι, HomSpace.traceMap f.val (M.X i).X.arity
      ((α ≫ β) i i).f) =
    ∑ j : N.ι, HomSpace.traceMap f.val (N.X j).X.arity
      ((β ≫ α) j j).f
  have hM : ∀ i : M.ι,
      HomSpace.traceMap f.val (M.X i).X.arity
        ((α ≫ β) i i).f =
      ∑ j : N.ι, HomSpace.traceMap f.val (M.X i).X.arity
        ((α i j).f ≫ (β j i).f) := by
    intro i
    rw [show ((α ≫ β) i i).f =
      ((∑ j : N.ι, α i j ≫ β j i : M.X i ⟶ M.X i)).f from rfl]
    rw [show (((∑ j : N.ι, α i j ≫ β j i :
        M.X i ⟶ M.X i))).f =
      ∑ j : N.ι, ((α i j ≫ β j i :
        M.X i ⟶ M.X i)).f from map_sum (karoubiHomAddHom _ _) _ _]
    rw [map_sum]
    rfl
  have hN : ∀ j : N.ι,
      HomSpace.traceMap f.val (N.X j).X.arity
        ((β ≫ α) j j).f =
      ∑ i : M.ι, HomSpace.traceMap f.val (N.X j).X.arity
        ((β j i).f ≫ (α i j).f) := by
    intro j
    rw [show ((β ≫ α) j j).f =
      ((∑ i : M.ι, β j i ≫ α i j : N.X j ⟶ N.X j)).f from rfl]
    rw [show (((∑ i : M.ι, β j i ≫ α i j :
        N.X j ⟶ N.X j))).f =
      ∑ i : M.ι, ((β j i ≫ α i j :
        N.X j ⟶ N.X j)).f from map_sum (karoubiHomAddHom _ _) _ _]
    rw [map_sum]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hM i,
    Finset.sum_congr rfl fun j _ => hN j]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  exact karoubi_trace_comm f (α i j) (β j i)

/-! ### Single-entry tests and nondegeneracy -/

open scoped Classical in
/-- The single-entry endomorphism matrix. -/
private noncomputable def matSingle
    {M : Mat_ (Karoubi (SkeinObj f))} (j i : M.ι)
    (b : M.X j ⟶ M.X i) : M ⟶ M := fun l k =>
  if h : l = j ∧ k = i then
    eqToHom (congrArg M.X h.1) ≫ b ≫
      eqToHom (congrArg M.X h.2.symm)
  else 0

/-- Evaluating the trace against a single-entry test extracts one
entry's closure trace. -/
private theorem matTrace_matSingle_mul
    {M : Mat_ (Karoubi (SkeinObj f))} (i j : M.ι)
    (b : M.X j ⟶ M.X i) (φ : End M) :
    matTrace f M ((show End M from matSingle f j i b) * φ) =
      HomSpace.traceMap f.val (M.X i).X.arity
        ((φ i j).f ≫ b.f) := by
  classical
  show (∑ k : M.ι, HomSpace.traceMap f.val (M.X k).X.arity
      ((φ ≫ matSingle f j i b) k k).f) = _
  rw [Finset.sum_eq_single i
    (fun k _ hk => by
      rw [show ((φ ≫ matSingle f j i b) k k).f =
        ((∑ l : M.ι, φ k l ≫ matSingle f j i b l k :
          M.X k ⟶ M.X k)).f from rfl]
      rw [show (((∑ l : M.ι, φ k l ≫ matSingle f j i b l k :
          M.X k ⟶ M.X k))).f =
        ∑ l : M.ι, ((φ k l ≫ matSingle f j i b l k :
          M.X k ⟶ M.X k)).f from map_sum (karoubiHomAddHom _ _) _ _]
      rw [Finset.sum_eq_zero, map_zero]
      intro l _
      rw [show matSingle f j i b l k = 0 from
        dif_neg (fun h => hk h.2)]
      rw [show ((φ k l ≫ (0 : M.X l ⟶ M.X k) :
        M.X k ⟶ M.X k)).f = 0 from by
          rw [Limits.comp_zero]
          rfl])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [show ((φ ≫ matSingle f j i b) i i).f =
    ((∑ l : M.ι, φ i l ≫ matSingle f j i b l i :
      M.X i ⟶ M.X i)).f from rfl]
  rw [show (((∑ l : M.ι, φ i l ≫ matSingle f j i b l i :
      M.X i ⟶ M.X i))).f =
    ∑ l : M.ι, ((φ i l ≫ matSingle f j i b l i :
      M.X i ⟶ M.X i)).f from map_sum (karoubiHomAddHom _ _) _ _]
  rw [map_sum]
  rw [Finset.sum_eq_single j
    (fun l _ hl => by
      rw [show matSingle f j i b l i = 0 from
        dif_neg (fun h => hl h.1)]
      rw [show ((φ i l ≫ (0 : M.X l ⟶ M.X i) :
        M.X i ⟶ M.X i)).f = 0 from by
          rw [Limits.comp_zero]
          rfl]
      rw [map_zero])
    (fun h => absurd (Finset.mem_univ j) h)]
  rw [show matSingle f j i b j i =
    eqToHom (congrArg M.X rfl) ≫ b ≫
      eqToHom (congrArg M.X rfl) from dif_pos ⟨rfl, rfl⟩]
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id,
    Category.id_comp]
  rfl

/-- **Nondegeneracy of the diagonal trace.** -/
theorem matEnd_eq_zero_of_traces_vanish
    {M : Mat_ (Karoubi (SkeinObj f))} (φ : End M)
    (hφ : ∀ ψ : End M, matTrace f M (ψ * φ) = 0) :
    φ = 0 := by
  apply Mat_.hom_ext
  intro i j
  show φ i j = 0
  apply karoubiHom_eq_zero_of_traces_vanish f (φ i j)
  intro b
  have h := hφ (show End M from matSingle f j i b)
  rw [matTrace_matSingle_mul] at h
  exact h

/-! ### Finiteness and the semisimplicity criterion -/

/-- Karoubi hom-spaces are finite-dimensional, being subspaces of
the skein hom-spaces. -/
noncomputable instance karoubiHomFinite
    (P Q : Karoubi (SkeinObj f)) :
    FiniteDimensional ℂ (P ⟶ Q) := by
  haveI : FiniteDimensional ℂ (P.X ⟶ Q.X) :=
    inferInstanceAs (Module.Finite ℂ
      (HomSpace f.val (P.X.arity + Q.X.arity)))
  exact FiniteDimensional.of_injective (karoubiHomLinearMap P Q)
    (fun _ _ h => Karoubi.Hom.ext h)

/-- The matrix-envelope Hom underlying map, linearly. -/
private noncomputable def matHomLin
    (M N : Mat_ (Karoubi (SkeinObj f))) :
    (M ⟶ N) →ₗ[ℂ] ((i : M.ι) → (j : N.ι) →
      (M.X i ⟶ N.X j)) where
  toFun φ := fun i j => φ i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- So are matrix hom-spaces, being finite products of them. -/
noncomputable instance matHomFinite
    (M N : Mat_ (Karoubi (SkeinObj f))) :
    FiniteDimensional ℂ (M ⟶ N) :=
  FiniteDimensional.of_injective (matHomLin f M N)
    (fun _ _ h => by
      apply Mat_.hom_ext
      intro i j
      exact congrFun (congrFun h i) j)

/-- In particular every matrix endomorphism algebra is
finite-dimensional — the standing hypothesis of the trace
criterion. -/
noncomputable instance matEndFinite
    (M : Mat_ (Karoubi (SkeinObj f))) :
    FiniteDimensional ℂ (End M) :=
  matHomFinite f M M

end RS
