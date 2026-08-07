/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Cech.Colimit
import LeanPool.JacobianDiffgeo.Meromorphic.Gluing

/-!
# Forster 12.4: refinement maps are injective on `H¹` (CC8, D8, proof plan §6.7)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.4, §6.7).

* `resH1_injective`: `resH1 D τ hτ : H1Cover D 𝒰 →ₗ H1Cover D 𝒱` is injective — a pure
  sheaf-axiom argument (`MeroGermOn.exists_glue`/`glue_unique`), no analysis.
* `toH1_injective`/`toH1_eq_zero_iff`: every cover-level `H¹` embeds in the colimit `H1 D`
  (via `Module.DirectLimit.of.zero_exact` + `resH1_injective`).
* `subsingleton_H1_iff`: the colimit vanishes iff every cover-level `H¹` vanishes.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (D : RS.Divisor X) {Ω : Opens X} {𝒰 𝒱 : FinCover Ω}
variable (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ)

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Any member `A ≤ Ω` is exhausted by its intersections with the members of a cover `𝒱` of `Ω`
(§6.7's covering fact, used both to glue `injPatch` over `𝒰.U i` and to compare cochains over
`𝒰.U i ⊓ 𝒰.U j`). -/
theorem iUnion_inf_eq (A : Opens X) (hA : A ≤ Ω) :
    (⋃ k : Fin 𝒱.n, ((A ⊓ 𝒱.U k : Opens X) : Set X)) = (A : Set X) := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun k => inf_le_left
  · intro x hx
    obtain ⟨k, hk⟩ := 𝒱.covers x (hA hx)
    exact Set.mem_iUnion.2 ⟨k, hx, hk⟩

/-- The local candidate for the glued section on `𝒰.U i`, restricted to `𝒰.U i ⊓ 𝒱.U k`
(Forster p. 99 / §6.7). -/
noncomputable def injPatch (f : C1 D 𝒰) (g : C0 D 𝒱) (i : Fin 𝒰.n) (k : Fin 𝒱.n) :
    RS.LinSysOn D ((𝒰.U i ⊓ 𝒱.U k : Opens X) : Set X) :=
  LinSysOn.restrictL D (inf_le_inf (le_refl (𝒰.U i)) (hτ k)) (f (i, τ k)) -
    LinSysOn.restrictL D (inf_le_right : 𝒰.U i ⊓ 𝒱.U k ≤ 𝒱.U k) (g k)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem injPatch_compat {f : C1 D 𝒰} (hf : f ∈ Z1 D 𝒰) {g : C0 D 𝒱}
    (hgeq : resC1 D τ hτ f = d0 D 𝒱 g) (i : Fin 𝒰.n) (k l : Fin 𝒱.n) :
    RS.MeroGermOn.restrict
        (Set.inter_subset_left :
          (((𝒰.U i ⊓ 𝒱.U k : Opens X) : Set X) ∩ ((𝒰.U i ⊓ 𝒱.U l : Opens X) : Set X)) ⊆
            ((𝒰.U i ⊓ 𝒱.U k : Opens X) : Set X))
        (injPatch D τ hτ f g i k : RS.MeroGermOn X ((𝒰.U i ⊓ 𝒱.U k : Opens X) : Set X)) =
      RS.MeroGermOn.restrict
        (Set.inter_subset_right :
          (((𝒰.U i ⊓ 𝒱.U k : Opens X) : Set X) ∩ ((𝒰.U i ⊓ 𝒱.U l : Opens X) : Set X)) ⊆
            ((𝒰.U i ⊓ 𝒱.U l : Opens X) : Set X))
        (injPatch D τ hτ f g i l : RS.MeroGermOn X ((𝒰.U i ⊓ 𝒱.U l : Opens X) : Set X)) := by
  set Wraw : Opens X := (𝒰.U i ⊓ 𝒱.U k) ⊓ (𝒰.U i ⊓ 𝒱.U l) with hWraw_def
  have hWA : Wraw ≤ (𝒰.U i ⊓ 𝒱.U k : Opens X) := inf_le_left
  have hWB : Wraw ≤ (𝒰.U i ⊓ 𝒱.U l : Opens X) := inf_le_right
  have hWi : Wraw ≤ 𝒰.U i := hWA.trans inf_le_left
  have hWk : Wraw ≤ 𝒱.U k := hWA.trans inf_le_right
  have hWl : Wraw ≤ 𝒱.U l := hWB.trans inf_le_right
  have hWtk : Wraw ≤ 𝒰.U (τ k) := hWk.trans (hτ k)
  have hWtl : Wraw ≤ 𝒰.U (τ l) := hWl.trans (hτ l)
  have hab : Wraw ≤ 𝒰.U i ⊓ 𝒰.U (τ k) := le_inf hWi hWtk
  have hac : Wraw ≤ 𝒰.U i ⊓ 𝒰.U (τ l) := le_inf hWi hWtl
  have hbc : Wraw ≤ 𝒰.U (τ k) ⊓ 𝒰.U (τ l) := le_inf hWtk hWtl
  have hWkl : Wraw ≤ 𝒱.U k ⊓ 𝒱.U l := le_inf hWk hWl
  -- the cocycle relation on the triple `(i, τ k, τ l)`, at `Wraw`
  have key1 := Z1.rel_res D hf i (τ k) (τ l) (le_inf (le_inf hWi hWtk) hWtl) hbc hac hab
  -- the hypothesis `resC1 τ hτ f = d0 g`, at `(k, l)`, restricted down to `Wraw`
  have hgeq_kl := congrFun hgeq (k, l)
  rw [resC1_apply, d0_apply] at hgeq_kl
  have key2 : LinSysOn.restrictL D hbc (f (τ k, τ l)) =
      LinSysOn.restrictL D hWl (g l) - LinSysOn.restrictL D hWk (g k) := by
    have hcongr := congrArg (LinSysOn.restrictL D hWkl) hgeq_kl
    simp only [map_sub] at hcongr
    rwa [restrictL_restrictL D (inf_le_inf (hτ k) (hτ l)) hWkl hbc,
      restrictL_restrictL D (inf_le_right : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒱.U l) hWkl hWl,
      restrictL_restrictL D (inf_le_left : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒱.U k) hWkl hWk] at hcongr
  rw [key2] at key1
  -- combine: the two restricted `injPatch`s agree on `Wraw`
  have key3 : LinSysOn.restrictL D hab (f (i, τ k)) - LinSysOn.restrictL D hWk (g k) =
      LinSysOn.restrictL D hac (f (i, τ l)) - LinSysOn.restrictL D hWl (g l) := by
    have e : LinSysOn.restrictL D hab (f (i, τ k)) - LinSysOn.restrictL D hWk (g k) -
        (LinSysOn.restrictL D hac (f (i, τ l)) - LinSysOn.restrictL D hWl (g l)) =
        (LinSysOn.restrictL D hWl (g l) - LinSysOn.restrictL D hWk (g k)) -
          LinSysOn.restrictL D hac (f (i, τ l)) + LinSysOn.restrictL D hab (f (i, τ k)) := by
      abel
    rw [key1] at e
    exact sub_eq_zero.1 e
  have hcoeK : LinSysOn.restrictL D hWA (injPatch D τ hτ f g i k) =
      LinSysOn.restrictL D hab (f (i, τ k)) - LinSysOn.restrictL D hWk (g k) := by
    unfold injPatch
    rw [map_sub, restrictL_restrictL D (inf_le_inf (le_refl (𝒰.U i)) (hτ k)) hWA hab,
      restrictL_restrictL D (inf_le_right : 𝒰.U i ⊓ 𝒱.U k ≤ 𝒱.U k) hWA hWk]
  have hcoeL : LinSysOn.restrictL D hWB (injPatch D τ hτ f g i l) =
      LinSysOn.restrictL D hac (f (i, τ l)) - LinSysOn.restrictL D hWl (g l) := by
    unfold injPatch
    rw [map_sub, restrictL_restrictL D (inf_le_inf (le_refl (𝒰.U i)) (hτ l)) hWB hac,
      restrictL_restrictL D (inf_le_right : 𝒰.U i ⊓ 𝒱.U l ≤ 𝒱.U l) hWB hWl]
  have key4 : LinSysOn.restrictL D hWA (injPatch D τ hτ f g i k) =
      LinSysOn.restrictL D hWB (injPatch D τ hτ f g i l) := by
    rw [hcoeK, hcoeL, key3]
  have hval := congrArg Subtype.val key4
  simpa only [restrictL_apply_coe] using hval

/-- Glue the local candidates `injPatch D τ hτ f g i ·` (compatible by `injPatch_compat`) into a
genuine section on the whole member `𝒰.U i` (Forster p. 99 / §6.7, sheaf axioms only). -/
theorem exists_injGlue {f : C1 D 𝒰} (hf : f ∈ Z1 D 𝒰) {g : C0 D 𝒱}
    (hgeq : resC1 D τ hτ f = d0 D 𝒱 g) (i : Fin 𝒰.n) :
    ∃ ψ : RS.LinSysOn D (𝒰.U i : Set X), ∀ k : Fin 𝒱.n,
      LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒱.U k ≤ 𝒰.U i) ψ = injPatch D τ hτ f g i k := by
  set W : Fin 𝒱.n → Set X := fun k => ((𝒰.U i ⊓ 𝒱.U k : Opens X) : Set X) with hW_def
  have hWopen : ∀ k, IsOpen (W k) := fun k => (𝒰.U i ⊓ 𝒱.U k).isOpen
  have hunion : (⋃ k, W k) = (𝒰.U i : Set X) := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun k => inf_le_left
    · intro x hx
      obtain ⟨k, hk⟩ := 𝒱.covers x (𝒰.le_base i hx)
      exact Set.mem_iUnion.2 ⟨k, hx, hk⟩
  obtain ⟨Φ, hΦ⟩ := RS.MeroGermOn.exists_glue hWopen
    (fun k => (injPatch D τ hτ f g i k : RS.MeroGermOn X (W k)))
    (fun k l => injPatch_compat D τ hτ hf hgeq i k l)
  set e := MeroGermOn.congrSet hunion with he_def
  have hrestr : ∀ k : Fin 𝒱.n, RS.MeroGermOn.restrict
      (inf_le_left : 𝒰.U i ⊓ 𝒱.U k ≤ 𝒰.U i) (e Φ) =
      (injPatch D τ hτ f g i k : RS.MeroGermOn X (W k)) := by
    intro k
    change RS.MeroGermOn.restrict inf_le_left (RS.MeroGermOn.restrict _ Φ) = _
    rw [RS.MeroGermOn.restrict_restrict, hΦ]
  have hmem : e Φ ∈ RS.LinSysOn D (𝒰.U i : Set X) := by
    rw [RS.mem_linSysOn_iff_of_isOpen (𝒰.U i).isOpen]
    intro x hx
    rw [← hunion] at hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.1 hx
    have hord := RS.MeroGermOn.ord_restrict
      (inf_le_left : 𝒰.U i ⊓ 𝒱.U k ≤ 𝒰.U i) (hWopen k) (𝒰.U i).isOpen hxk (e Φ)
    rw [hrestr k] at hord
    rw [← hord]
    exact (RS.mem_linSysOn_iff_of_isOpen (hWopen k)).1 (injPatch D τ hτ f g i k).2 x hxk
  exact ⟨⟨e Φ, hmem⟩, fun k => Subtype.ext (hrestr k)⟩

/-- The glued cochain `ψ` is a coboundary witness for `-f` (a sign artifact of `injPatch`'s
convention, harmless — `f = d0 D 𝒰 (-ψ)`). -/
theorem d0_injGlue_eq_neg {f : C1 D 𝒰} (hf : f ∈ Z1 D 𝒰) {g : C0 D 𝒱}
    (_hgeq : resC1 D τ hτ f = d0 D 𝒱 g) (ψ : ∀ i, RS.LinSysOn D (𝒰.U i : Set X))
    (hψ : ∀ (i : Fin 𝒰.n) (k : Fin 𝒱.n),
      LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒱.U k ≤ 𝒰.U i) (ψ i) =
        injPatch D τ hτ f g i k) :
    d0 D 𝒰 ψ = -f := by
  funext p
  obtain ⟨i, j⟩ := p
  apply Subtype.ext
  set A : Opens X := 𝒰.U i ⊓ 𝒰.U j with hA_def
  set W' : Fin 𝒱.n → Set X := fun k => ((A ⊓ 𝒱.U k : Opens X) : Set X) with hW'_def
  have hW'open : ∀ k, IsOpen (W' k) := fun k => (A ⊓ 𝒱.U k).isOpen
  have hunion' : (⋃ k, W' k) = (A : Set X) :=
    iUnion_inf_eq A (le_trans inf_le_left (𝒰.le_base i))
  set e' := MeroGermOn.congrSet hunion'.symm with he'_def
  have hrewrite : ∀ (Z : RS.MeroGermOn X (A : Set X)) (k : Fin 𝒱.n),
      RS.MeroGermOn.restrict (Set.subset_iUnion W' k) (e' Z) =
        RS.MeroGermOn.restrict (inf_le_left : A ⊓ 𝒱.U k ≤ A) Z := by
    intro Z k
    change RS.MeroGermOn.restrict (Set.subset_iUnion W' k) (RS.MeroGermOn.restrict _ Z) = _
    rw [RS.MeroGermOn.restrict_restrict]
  have hcore : ∀ k : Fin 𝒱.n,
      LinSysOn.restrictL D (inf_le_left : A ⊓ 𝒱.U k ≤ A) (d0 D 𝒰 ψ (i, j)) =
        LinSysOn.restrictL D (inf_le_left : A ⊓ 𝒱.U k ≤ A) (-(f (i, j))) := by
    intro k
    have hWi : A ⊓ 𝒱.U k ≤ 𝒰.U i := inf_le_left.trans inf_le_left
    have hWj : A ⊓ 𝒱.U k ≤ 𝒰.U j := inf_le_left.trans inf_le_right
    have hWk : A ⊓ 𝒱.U k ≤ 𝒱.U k := inf_le_right
    have hWtk : A ⊓ 𝒱.U k ≤ 𝒰.U (τ k) := hWk.trans (hτ k)
    have hab : A ⊓ 𝒱.U k ≤ 𝒰.U i ⊓ 𝒰.U j := inf_le_left
    have hac : A ⊓ 𝒱.U k ≤ 𝒰.U i ⊓ 𝒰.U (τ k) := le_inf hWi hWtk
    have hbc : A ⊓ 𝒱.U k ≤ 𝒰.U j ⊓ 𝒰.U (τ k) := le_inf hWj hWtk
    have hjk : A ⊓ 𝒱.U k ≤ 𝒰.U j ⊓ 𝒱.U k := le_inf hWj hWk
    have hik : A ⊓ 𝒱.U k ≤ 𝒰.U i ⊓ 𝒱.U k := le_inf hWi hWk
    -- unfold `d0 D 𝒰 ψ (i,j)` and relate each term to `injPatch` via `hψ`
    have hLHS : LinSysOn.restrictL D (inf_le_left : A ⊓ 𝒱.U k ≤ A) (d0 D 𝒰 ψ (i, j)) =
        LinSysOn.restrictL D hjk (injPatch D τ hτ f g j k) -
          LinSysOn.restrictL D hik (injPatch D τ hτ f g i k) := by
      rw [d0_apply, map_sub,
        restrictL_restrictL D (inf_le_right : A ≤ 𝒰.U j) (inf_le_left : A ⊓ 𝒱.U k ≤ A) hWj,
        restrictL_restrictL D (inf_le_left : A ≤ 𝒰.U i) (inf_le_left : A ⊓ 𝒱.U k ≤ A) hWi,
        ← hψ j k, ← hψ i k,
        restrictL_restrictL D (inf_le_left : 𝒰.U j ⊓ 𝒱.U k ≤ 𝒰.U j) hjk
          (hjk.trans (inf_le_left : 𝒰.U j ⊓ 𝒱.U k ≤ 𝒰.U j)),
        restrictL_restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒱.U k ≤ 𝒰.U i) hik
          (hik.trans (inf_le_left : 𝒰.U i ⊓ 𝒱.U k ≤ 𝒰.U i))]
    have hexpand : LinSysOn.restrictL D hjk (injPatch D τ hτ f g j k) -
        LinSysOn.restrictL D hik (injPatch D τ hτ f g i k) =
        LinSysOn.restrictL D hbc (f (j, τ k)) - LinSysOn.restrictL D hac (f (i, τ k)) := by
      have e1 : LinSysOn.restrictL D hjk (injPatch D τ hτ f g j k) =
          LinSysOn.restrictL D hbc (f (j, τ k)) -
            LinSysOn.restrictL D hWk (g k) := by
        unfold injPatch
        rw [map_sub,
          restrictL_restrictL D (inf_le_inf (le_refl (𝒰.U j)) (hτ k)) hjk hbc,
          restrictL_restrictL D (inf_le_right : 𝒰.U j ⊓ 𝒱.U k ≤ 𝒱.U k) hjk hWk]
      have e2 : LinSysOn.restrictL D hik (injPatch D τ hτ f g i k) =
          LinSysOn.restrictL D hac (f (i, τ k)) -
            LinSysOn.restrictL D hWk (g k) := by
        unfold injPatch
        rw [map_sub,
          restrictL_restrictL D (inf_le_inf (le_refl (𝒰.U i)) (hτ k)) hik hac,
          restrictL_restrictL D (inf_le_right : 𝒰.U i ⊓ 𝒱.U k ≤ 𝒱.U k) hik hWk]
      rw [e1, e2]
      abel
    have key1 := Z1.rel_res D hf i j (τ k) (le_inf hab hWtk) hbc hac hab
    have hRHS : LinSysOn.restrictL D (inf_le_left : A ⊓ 𝒱.U k ≤ A) (-(f (i, j))) =
        -LinSysOn.restrictL D hab (f (i, j)) := by
      rw [map_neg]
    rw [hLHS, hexpand, hRHS]
    have e : LinSysOn.restrictL D hbc (f (j, τ k)) - LinSysOn.restrictL D hac (f (i, τ k)) =
        LinSysOn.restrictL D hbc (f (j, τ k)) - LinSysOn.restrictL D hac (f (i, τ k)) +
          LinSysOn.restrictL D hab (f (i, j)) - LinSysOn.restrictL D hab (f (i, j)) := by
      abel
    rw [e, key1, zero_sub]
  have hglu : e' ((d0 D 𝒰 ψ (i, j) : RS.MeroGermOn X (A : Set X))) =
      e' ((-(f (i, j)) : RS.MeroGermOn X (A : Set X))) := by
    apply RS.MeroGermOn.glue_unique hW'open
    intro k
    rw [hrewrite _ k, hrewrite _ k]
    exact congrArg Subtype.val (hcore k)
  have hval := e'.injective hglu
  simpa using hval

/-- **Forster 12.4 / Miranda IX.3.11**: refinement maps are injective on `H¹` — a pure
sheaf-axiom argument (`MeroGermOn.exists_glue`/`glue_unique`), no analysis. -/
theorem resH1_injective : Function.Injective (resH1 D τ hτ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro ξ hξ
  obtain ⟨f, rfl⟩ := H1Cover.mk_surjective D 𝒰 ξ
  rw [LinearMap.mem_ker, resH1_mk, H1Cover.mk_eq_zero_iff] at hξ
  obtain ⟨g, hg⟩ := hξ
  have hgeq : resC1 D τ hτ (f : C1 D 𝒰) = d0 D 𝒱 g := by
    rw [← resZ1_apply_coe]
    exact hg.symm
  have hf : (f : C1 D 𝒰) ∈ Z1 D 𝒰 := f.2
  choose ψ hψ using fun i => exists_injGlue D τ hτ hf hgeq i
  have hd0 : d0 D 𝒰 ψ = -(f : C1 D 𝒰) := d0_injGlue_eq_neg D τ hτ hf hgeq ψ hψ
  have hmemB1 : (f : C1 D 𝒰) ∈ B1 D 𝒰 := ⟨-ψ, by rw [map_neg, hd0, neg_neg]⟩
  rw [H1Cover.mk_eq_zero_iff]
  exact hmemB1

/-- **12.4 + `exists_eq_of_of_eq`**: every cover-level `H¹` embeds in the colimit `H1 D`. -/
theorem toH1_injective (𝒰 : FinCover (⊤ : Opens X)) : Function.Injective (toH1 D 𝒰) := by
  intro c c' hc
  obtain ⟨𝒱, hij, hz⟩ := Module.DirectLimit.exists_eq_of_of_eq hc
  exact resH1_injective D (chosenRefIdx hij) (chosenRefIdx_spec hij) hz

@[simp] theorem toH1_eq_zero_iff {𝒰 : FinCover (⊤ : Opens X)} (c : H1Cover D 𝒰) :
    toH1 D 𝒰 c = 0 ↔ c = 0 := by
  constructor
  · intro h
    exact toH1_injective D 𝒰 (h.trans (map_zero (toH1 D 𝒰)).symm)
  · intro h
    rw [h, map_zero]

/-- The colimit `H1 D` vanishes iff every cover-level `H¹(𝒰,D)` vanishes. -/
theorem subsingleton_H1_iff : Subsingleton (H1 D) ↔ ∀ 𝒰 : FinCover (⊤ : Opens X),
    Subsingleton (H1Cover D 𝒰) := by
  constructor
  · intro h 𝒰
    refine ⟨fun c c' => ?_⟩
    exact toH1_injective D 𝒰 (Subsingleton.elim (toH1 D 𝒰 c) (toH1 D 𝒰 c'))
  · exact subsingleton_H1_of_all_subsingleton D

end RS.Cech
