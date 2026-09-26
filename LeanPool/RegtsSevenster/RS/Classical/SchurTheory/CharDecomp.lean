/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.CharEquiv
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SimpleEmbed

/-!
# Character decomposition into native characters

Every character of a finite-dimensional representation over ℂ
decomposes as a sum of native characters `nChar S g` for simple
submodules `S` of the regular module.
-/

@[expose] public section

namespace RS

open Finset LinearMap DirectSum

variable {G : Type*}

section Aux

/-- `ρ g` preserves every `MonoidAlgebra ℂ G`-submodule of `ρ.asModule`. -/
private theorem rho_mem_of_mem
    [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (U : Submodule (MonoidAlgebra ℂ G) ρ.asModule) (g : G)
    {v : ρ.asModule} (hv : v ∈ U) : ρ g v ∈ U := by
  have key : (MonoidAlgebra.single g (1 : ℂ)) • v ∈ U := U.smul_mem _ hv
  have heq : MonoidAlgebra.single g (1 : ℂ) • v = ρ g v := by
    rw [Representation.single_smul, one_smul]; rfl
  rw [← heq]; exact key

/-- The representation on a `MonoidAlgebra ℂ G`-submodule of `ρ.asModule`,
using the restrictScalars carrier. -/
private noncomputable def rhoSub
    [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (U : Submodule (MonoidAlgebra ℂ G) ρ.asModule) :
    Representation ℂ G ↥(U.restrictScalars ℂ) :=
  Representation.ofModule' (k := ℂ) (G := G) ↥(U.restrictScalars ℂ)

/-- The algebra action of `rhoSub` is scalar multiplication. -/
private theorem rhoSub_asAlgebraHom_apply
    [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (U : Submodule (MonoidAlgebra ℂ G) ρ.asModule)
    (y : MonoidAlgebra ℂ G) (m : ↥(U.restrictScalars ℂ)) :
    (rhoSub ρ U).asAlgebraHom y m = y • m := by
  rw [rhoSub, Representation.asAlgebraHom_def, Representation.ofModule']
  rw [Equiv.apply_symm_apply]
  rfl

/-- The `rhoSub` action at `g` coerces to `ρ g` on the ambient module. -/
private theorem rhoSub_val_eq
    [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (U : Submodule (MonoidAlgebra ℂ G) ρ.asModule)
    (g : G) (m : ↥(U.restrictScalars ℂ)) :
    (rhoSub ρ U g m : ρ.asModule) = ρ g (m : ρ.asModule) := by
  have h1 : rhoSub ρ U g m = (MonoidAlgebra.single g (1 : ℂ)) • m := by
    have h := rhoSub_asAlgebraHom_apply ρ U (MonoidAlgebra.single g 1) m
    rw [Representation.asAlgebraHom_single, one_smul] at h
    exact h
  rw [h1]
  change (MonoidAlgebra.single g (1 : ℂ)) • (m : ρ.asModule) = ρ g (m :
    ρ.asModule)
  rw [Representation.single_smul, one_smul]; rfl

end Aux

section Main

private theorem character_zero_of_finrank_zero {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hd : Module.finrank ℂ V = 0) (g : G) :
    ρ.character g = 0 := by
  have hall : ∀ x : V, x = 0 := finrank_zero_iff_forall_zero.mp hd
  change (trace ℂ V) (ρ g) = 0
  rw [show (ρ g : V →ₗ[ℂ] V) = 0 from by ext v; exact hall _]
  exact map_zero _

private theorem character_eq_sum_nChar_aux {G : Type*} [Group G] [Finite G] :
    ∀ (n : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V),
      Module.finrank ℂ V ≤ n →
      ∃ (m : ℕ) (S : Fin m → Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)),
        (∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (S i)) ∧
        ∀ g : G, ρ.character g = ∑ i, nChar (S i) g := by
  classical
  let := Fintype.ofFinite G
  intro n
  induction n with
  | zero =>
    intro V _ _ _ ρ hn
    exact ⟨0, Fin.elim0, fun i => i.elim0, fun g => by
      rw [character_zero_of_finrank_zero ρ (Nat.le_zero.mp hn) g]; simp⟩
  | succ n ih =>
    intro V inst1 inst2 inst3 ρ hn
    by_cases htriv : Module.finrank ℂ V = 0
    · exact ⟨0, Fin.elim0, fun i => i.elim0, fun g => by
        rw [character_zero_of_finrank_zero ρ htriv g]; simp⟩
    · have hfpos : 0 < Module.finrank ℂ V := Nat.pos_of_ne_zero htriv
      have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos hfpos
      have : Nontrivial ρ.asModule := hnt
      have : NeZero ((Nat.card G : ℂ)) := ⟨by
        rw [Nat.card_eq_fintype_card]
        exact_mod_cast Fintype.card_ne_zero⟩
      have : IsSemisimpleRing (MonoidAlgebra ℂ G) := inferInstance
      have : IsSemisimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
        IsSemisimpleRing.isSemisimpleModule
      obtain ⟨T, hTsimp⟩ :=
        IsSemisimpleModule.exists_simple_submodule (MonoidAlgebra ℂ G)
          ρ.asModule
      obtain ⟨W, hTW⟩ := exists_isCompl T
      have : Nontrivial (↥T) := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) T
      have hTpos : 0 < Module.finrank ℂ ↥(T.restrictScalars ℂ) := by
        have : Nontrivial ↥(T.restrictScalars ℂ) := inferInstanceAs
          (Nontrivial ↥T)
        exact Module.finrank_pos
      have hTW_C : IsCompl (T.restrictScalars ℂ : Submodule ℂ ρ.asModule)
          (W.restrictScalars ℂ) :=
        (Submodule.isCompl_restrictScalars_iff ℂ).mpr hTW
      have hWfin : Module.finrank ℂ ↥(W.restrictScalars ℂ) ≤ n := by
        have h1 := Submodule.finrank_add_eq_of_isCompl hTW_C
        change Module.finrank ℂ ↥(T.restrictScalars ℂ) +
          Module.finrank ℂ ↥(W.restrictScalars ℂ) =
          Module.finrank ℂ V at h1
        omega
      let ρW := rhoSub ρ W
      obtain ⟨m', S', hS'simp, hS'char⟩ := @ih ↥(W.restrictScalars ℂ) _ _ _ ρW
        hWfin
      let ρT := rhoSub ρ T
      obtain ⟨S₀, hS₀simp, ⟨eTS⟩⟩ :=
        exists_simple_submodule_linearEquiv (↥T) hTsimp
      -- Character of ρT = nChar S₀
      have hcharT : ∀ g : G, ρT.character g = nChar S₀ g := by
        intro g
        apply character_of_equiv
        refine Representation.Equiv.mk (eTS.symm.restrictScalars ℂ) (fun g
          => ?_)
        apply LinearMap.ext; intro ⟨v, hv⟩
        simp only [comp_apply]
        -- Both ρT and rhoS act by single g 1 •, and eTS.symm is
        --   MonoidAlgebra-linear
        change eTS.symm (ρT g ⟨v, hv⟩) = rhoS S₀ g (eTS.symm ⟨v, hv⟩)
        have h1 : ρT g ⟨v, hv⟩ = (MonoidAlgebra.single g (1 : ℂ)) •
            (⟨v, hv⟩ : ↥(T.restrictScalars ℂ)) := by
          change (rhoSub ρ T) g ⟨v, hv⟩ = _
          have h := rhoSub_asAlgebraHom_apply ρ T (MonoidAlgebra.single g 1)
            ⟨v, hv⟩
          rw [Representation.asAlgebraHom_single, one_smul] at h
          exact h
        have h2 : rhoS S₀ g (eTS.symm ⟨v, hv⟩) =
            (MonoidAlgebra.single g (1 : ℂ)) • eTS.symm ⟨v, hv⟩ :=
          rhoS_apply S₀ g _
        erw [h1, map_smul, h2]
        rfl
      -- Character additivity via trace decomposition
      have hchar_split : ∀ g : G,
          ρ.character g = ρT.character g + ρW.character g := by
        intro g
        -- Cast ρ g to an endomorphism of ρ.asModule for type compatibility
        let f : ρ.asModule →ₗ[ℂ] ρ.asModule := ρ g
        -- Bool-indexed decomposition: true ↦ T, false ↦ W
        let N : Bool → Submodule ℂ ρ.asModule := fun b =>
          bif b then T.restrictScalars ℂ else W.restrictScalars ℂ
        have hInt : IsInternal N :=
          (isInternal_submodule_iff_isCompl N (i := true) (j := false)
            (by decide)
            (by ext x; cases x <;> simp [Set.mem_insert_iff])).mpr hTW_C
        have hMaps : ∀ i, Set.MapsTo f ↑(N i) ↑(N i) := by
          intro i; cases i <;> dsimp only [N, f, cond]
          · exact fun _ hv => rho_mem_of_mem ρ W g hv
          · exact fun _ hv => rho_mem_of_mem ρ T g hv
        have htrace := trace_eq_sum_trace_restrict hInt hMaps
        -- ρ.character g = trace ℂ V (ρ g) = trace ℂ ρ.asModule f
        change (trace ℂ V) (ρ g) = (trace ℂ _) (ρT g) + (trace ℂ _) (ρW g)
        change (trace ℂ ρ.asModule) f = _
        rw [htrace, Fintype.sum_bool]
        -- After sum_bool: trace on N true + trace on N false = ρT + ρW
        -- N true = T.restrictScalars ℂ, N false = W.restrictScalars ℂ
        congr 1
        · -- trace on N true (= T) = ρT.character g
          change (trace ℂ ↥(T.restrictScalars ℂ)) (f.restrict (hMaps true)) =
            (trace ℂ _) (ρT g)
          congr 1
          ext ⟨v, hv⟩ : 1
          apply Subtype.ext
          exact (rhoSub_val_eq ρ T g ⟨v, hv⟩).symm
        · -- trace on N false (= W) = ρW.character g
          change (trace ℂ ↥(W.restrictScalars ℂ)) (f.restrict (hMaps false)) =
            (trace ℂ _) (ρW g)
          congr 1
          ext ⟨v, hv⟩ : 1
          apply Subtype.ext
          exact (rhoSub_val_eq ρ W g ⟨v, hv⟩).symm
      -- Assemble final result
      refine ⟨m' + 1, Fin.cons S₀ S', ?_, ?_⟩
      · intro ⟨i, hi⟩
        cases i with
        | zero => exact hS₀simp
        | succ j => exact hS'simp ⟨j, Nat.lt_of_succ_lt_succ hi⟩
      · intro g
        rw [hchar_split g, hcharT g, hS'char g, Fin.sum_univ_succ]
        simp [Fin.cons_zero, Fin.cons_succ]

/-- **Every character decomposes** into native characters of simple
submodules of the regular module. -/
theorem character_eq_sum_nChar {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ∃ (m : ℕ) (S : Fin m → Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)),
      (∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (S i)) ∧
      ∀ g : G, ρ.character g = ∑ i, nChar (S i) g := by
  classical
  let := Fintype.ofFinite G
  exact
    character_eq_sum_nChar_aux (Module.finrank ℂ V) ρ le_rfl

end Main

end RS
