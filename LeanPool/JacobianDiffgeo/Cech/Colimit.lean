/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Cech.Refinement
import Mathlib.Algebra.Colimit.Module

/-!
# `H¹(D)` as a directed colimit (CC8, D1)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.5, §5).

* `resH1'`: the transition map for `h : 𝒰 ≤ 𝒱`, via a chosen refinement index — independent of
  the choice by Forster 12.3 (`resH1'_eq_resH1`).
* `DirectedSystem` instance on `fun 𝒰 => H1Cover D 𝒰`, from `resH1_id`/`resH1_comp`
(Refinement.lean).
* `H1 D`: the colimit (CC8, frozen). `toH1`, `exists_rep(_good/_refined)`, `H1.induction_on`.
* `H1.lift`: the universal property (target for dolbeault-comparison's comparison map).
* `H1Incl`: `D`-monotone functoriality (`H1 D →ₗ H1 D'` for `D ≤ D'`), via `Module.DirectLimit.map`.

`toH1_injective`/`toH1_eq_zero_iff`/`subsingleton_H1_iff` (needing Forster 12.4,
`resH1_injective`) are exported from `Injectivity.lean` instead, which imports this file;
`subsingleton_H1_of_good` below (the direction actually needed downstream, via good-cover
cofinality) does not need 12.4 and is proved here.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech Module

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (D : RS.Divisor X)

/-! ### The transition maps and the `DirectedSystem` instance -/

/-- The transition map for `𝒰 ≤ 𝒱`, via a chosen (classical) refinement index. -/
noncomputable def resH1' {𝒰 𝒱 : FinCover (⊤ : Opens X)} (h : 𝒰 ≤ 𝒱) :
    H1Cover D 𝒰 →ₗ[ℂ] H1Cover D 𝒱 := resH1 D (chosenRefIdx h) (chosenRefIdx_spec h)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Forster 12.3: `resH1'` does not depend on the chosen witness. -/
theorem resH1'_eq_resH1 {𝒰 𝒱 : FinCover (⊤ : Opens X)} (h : 𝒰 ≤ 𝒱) (τ : Fin 𝒱.n → Fin 𝒰.n)
    (hτ : IsRefIdx 𝒰 𝒱 τ) : resH1' D h = resH1 D τ hτ :=
  resH1_indep D (chosenRefIdx h) τ (chosenRefIdx_spec h) hτ

instance directedSystemH1Cover :
    DirectedSystem (fun 𝒰 : FinCover (⊤ : Opens X) => H1Cover D 𝒰) (fun _ _ h => resH1' D h) where
  map_self 𝒰 x := by
    change resH1' D (le_refl 𝒰) x = x
    rw [resH1'_eq_resH1 D (le_refl 𝒰) id (fun _ => le_rfl)]
    exact LinearMap.congr_fun (resH1_id D (fun _ => le_rfl)) x
  map_map {𝒰c 𝒰b 𝒰a} hab hbc x := by
    show resH1' D hbc (resH1' D hab x) = resH1' D (hab.trans hbc) x
    rw [resH1'_eq_resH1 D hab (chosenRefIdx hab) (chosenRefIdx_spec hab),
      resH1'_eq_resH1 D hbc (chosenRefIdx hbc) (chosenRefIdx_spec hbc),
      resH1'_eq_resH1 D (hab.trans hbc) (chosenRefIdx hab ∘ chosenRefIdx hbc)
        (fun k => (chosenRefIdx_spec hbc k).trans (chosenRefIdx_spec hab (chosenRefIdx hbc k)))]
    exact LinearMap.congr_fun
      (resH1_comp D (chosenRefIdx hab) (chosenRefIdx_spec hab) (chosenRefIdx hbc)
        (chosenRefIdx_spec hbc)) x

/-! ### `H1 D`, the colimit -/

/-- CC8 (frozen by design): the first Čech cohomology of `O_D` on `X`, as a directed colimit
over finite covers of `X` under refinement. Reducible (`abbrev`) so that instance search and the
`Module.DirectLimit` API (`of`, `lift`, `map`, `exists_of`, `induction_on`, …) apply transparently
— the same reason `C0/C1/C2`/`H1Cover` are `abbrev` (Cochains.lean). -/
noncomputable abbrev H1 (D : RS.Divisor X) : Type _ :=
  Module.DirectLimit (fun 𝒰 : FinCover (⊤ : Opens X) => H1Cover D 𝒰) (fun _ _ h => resH1' D h)

/-- The canonical map from a cover-level `H¹` to the colimit. -/
noncomputable def toH1 (𝒰 : FinCover (⊤ : Opens X)) : H1Cover D 𝒰 →ₗ[ℂ] H1 D :=
  Module.DirectLimit.of ℂ (FinCover (⊤ : Opens X)) (fun 𝒰 => H1Cover D 𝒰)
      (fun _ _ h => resH1' D h) 𝒰

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem toH1_resH1' {𝒰 𝒱 : FinCover (⊤ : Opens X)} (h : 𝒰 ≤ 𝒱) (ξ : H1Cover D 𝒰) :
    toH1 D 𝒱 (resH1' D h ξ) = toH1 D 𝒰 ξ :=
  Module.DirectLimit.of_f

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem toH1_resH1 {𝒰 𝒱 : FinCover (⊤ : Opens X)} (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ)
    (ξ : H1Cover D 𝒰) : toH1 D 𝒱 (resH1 D τ hτ ξ) = toH1 D 𝒰 ξ := by
  rw [← resH1'_eq_resH1 D (le_def.2 ⟨τ, hτ⟩) τ hτ, toH1_resH1']

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem exists_rep (ξ : H1 D) : ∃ 𝒰 c, toH1 D 𝒰 c = ξ :=
  Module.DirectLimit.exists_of ξ

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Refine the produced cover to a good one, pushing the class along (§5.3). -/
theorem exists_rep_good [CompactSpace X] (ξ : H1 D) :
    ∃ 𝒰 : FinCover (⊤ : Opens X), 𝒰.IsGood ∧ ∃ c, toH1 D 𝒰 c = ξ := by
  obtain ⟨𝒰₀, c₀, hc₀⟩ := exists_rep D ξ
  obtain ⟨𝒰, h, hgood⟩ := exists_good_refinement 𝒰₀
  exact ⟨𝒰, hgood, resH1' D h c₀, by rw [toH1_resH1', hc₀]⟩

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem exists_rep_refined (𝒰₀ : FinCover (⊤ : Opens X)) (ξ : H1 D) :
    ∃ (𝒰 : FinCover (⊤ : Opens X)) (_ : 𝒰₀ ≤ 𝒰), ∃ c, toH1 D 𝒰 c = ξ := by
  obtain ⟨𝒰₁, c₁, hc₁⟩ := exists_rep D ξ
  obtain ⟨𝒰, h₀, h₁⟩ := exists_ge_ge 𝒰₀ 𝒰₁
  exact ⟨𝒰, h₀, resH1' D h₁ c₁, by rw [toH1_resH1', hc₁]⟩

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[elab_as_elim] theorem H1.induction_on {C : H1 D → Prop} (ξ : H1 D)
    (ih : ∀ (𝒰 : FinCover (⊤ : Opens X)) (c : H1Cover D 𝒰), C (toH1 D 𝒰 c)) : C ξ :=
  Module.DirectLimit.induction_on ξ ih

/-! ### Subsingleton criteria not requiring 12.4 -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- If every cover-level `H¹` vanishes, so does the colimit (no injectivity needed: every class
already has a cover-level representative, and the hypothesis kills every representative). -/
theorem subsingleton_H1_of_all_subsingleton
    (h : ∀ 𝒰 : FinCover (⊤ : Opens X), Subsingleton (H1Cover D 𝒰)) : Subsingleton (H1 D) := by
  refine ⟨fun ξ η => ?_⟩
  induction ξ using H1.induction_on with
  | _ 𝒰 c =>
    induction η using H1.induction_on with
    | _ 𝒱 c' =>
      have hc : c = (0 : H1Cover D 𝒰) := Subsingleton.elim _ _
      have hc' : c' = (0 : H1Cover D 𝒱) := Subsingleton.elim _ _
      rw [hc, hc', map_zero, map_zero]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- If every *good* cover-level `H¹` vanishes, so does the colimit (good covers are cofinal). -/
theorem subsingleton_H1_of_good [CompactSpace X]
    (h : ∀ 𝒰 : FinCover (⊤ : Opens X), 𝒰.IsGood → Subsingleton (H1Cover D 𝒰)) :
    Subsingleton (H1 D) := by
  refine ⟨fun ξ η => ?_⟩
  obtain ⟨𝒰, hgood, c, hc⟩ := exists_rep_good D ξ
  obtain ⟨𝒱, hgood', c', hc'⟩ := exists_rep_good D η
  have := h 𝒰 hgood
  have := h 𝒱 hgood'
  have hc0 : c = 0 := Subsingleton.elim _ _
  have hc0' : c' = 0 := Subsingleton.elim _ _
  rw [← hc, ← hc', hc0, hc0', map_zero, map_zero]

/-! ### The universal property -/

/-- The universal property of `H¹(D)` (target for dolbeault-comparison's comparison map). -/
noncomputable def H1.lift {P : Type*} [AddCommGroup P] [Module ℂ P]
    (g : ∀ 𝒰 : FinCover (⊤ : Opens X), H1Cover D 𝒰 →ₗ[ℂ] P)
    (hg : ∀ (𝒰 𝒱 : FinCover (⊤ : Opens X)) (h : 𝒰 ≤ 𝒱) (ξ : H1Cover D 𝒰),
      g 𝒱 (resH1' D h ξ) = g 𝒰 ξ) :
    H1 D →ₗ[ℂ] P :=
  Module.DirectLimit.lift ℂ (FinCover (⊤ : Opens X)) (fun 𝒰 => H1Cover D 𝒰)
      (fun _ _ h => resH1' D h)
    g (fun i j hij x => hg i j hij x)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem H1.lift_toH1 {P : Type*} [AddCommGroup P] [Module ℂ P]
    (g : ∀ 𝒰 : FinCover (⊤ : Opens X), H1Cover D 𝒰 →ₗ[ℂ] P)
    (hg : ∀ (𝒰 𝒱 : FinCover (⊤ : Opens X)) (h : 𝒰 ≤ 𝒱) (ξ : H1Cover D 𝒰),
      g 𝒱 (resH1' D h ξ) = g 𝒰 ξ)
    (𝒰 : FinCover (⊤ : Opens X)) (ξ : H1Cover D 𝒰) :
    H1.lift D g hg (toH1 D 𝒰 ξ) = g 𝒰 ξ :=
  Module.DirectLimit.lift_of _ _ ξ

/-! ### `D`-functoriality -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Compat: requested from meromorphic-and-divisors (`docs/requests/meromorphic-and-divisors.md`
item 1), not yet upstreamed — proved locally (one-line carrier implication). -/
theorem linSysOn_mono {U : Set X} {D D' : RS.Divisor X} (h : D ≤ D') :
    RS.LinSysOn D U ≤ RS.LinSysOn D' U := by
  intro φ hφ hU x hx
  have hDx : (D x : ℤ) ≤ D' x := Function.locallyFinsuppWithin.le_def.1 h x
  have hcast : ((-(D' x) : ℤ) : WithTop ℤ) ≤ ((-(D x) : ℤ) : WithTop ℤ) := by
    exact_mod_cast neg_le_neg hDx
  exact hcast.trans (hφ hU x hx)

variable {D' : RS.Divisor X}

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem inclusion_restrictL_comm {V U : Opens X} (h' : V ≤ U) (hD : D ≤ D')
    (φ : RS.LinSysOn D (U : Set X)) :
    Submodule.inclusion (RS.Cech.linSysOn_mono hD) (LinSysOn.restrictL D h' φ) =
      LinSysOn.restrictL D' h' (Submodule.inclusion (RS.Cech.linSysOn_mono hD) φ) :=
  Subtype.ext rfl

/-- `D`-inclusion of `1`-cochains (`Submodule.inclusion`, componentwise). -/
noncomputable def inclC1 {Ω : Opens X} (𝒰 : FinCover Ω) (h : D ≤ D') : C1 D 𝒰 →ₗ[ℂ] C1 D' 𝒰 :=
  LinearMap.pi fun p => (Submodule.inclusion (RS.Cech.linSysOn_mono h)).comp (LinearMap.proj p)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem inclC1_apply {Ω : Opens X} {𝒰 : FinCover Ω} (h : D ≤ D') (f : C1 D 𝒰)
    (p : Fin 𝒰.n × Fin 𝒰.n) :
    inclC1 D 𝒰 h f p = Submodule.inclusion (RS.Cech.linSysOn_mono h) (f p) := rfl

/-- `D`-inclusion of `0`-cochains. -/
noncomputable def inclC0 {Ω : Opens X} (𝒰 : FinCover Ω) (h : D ≤ D') : C0 D 𝒰 →ₗ[ℂ] C0 D' 𝒰 :=
  LinearMap.pi fun i => (Submodule.inclusion (RS.Cech.linSysOn_mono h)).comp (LinearMap.proj i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem inclC0_apply {Ω : Opens X} {𝒰 : FinCover Ω} (h : D ≤ D') (f : C0 D 𝒰) (i : Fin 𝒰.n) :
    inclC0 D 𝒰 h f i = Submodule.inclusion (RS.Cech.linSysOn_mono h) (f i) := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem inclC1_mem_Z1 {Ω : Opens X} {𝒰 : FinCover Ω} (h : D ≤ D') {f : C1 D 𝒰}
    (hf : f ∈ Z1 D 𝒰) : inclC1 D 𝒰 h f ∈ Z1 D' 𝒰 := by
  rw [mem_Z1_iff]
  rintro ⟨i, j, k⟩
  rw [d1_apply, inclC1_apply, inclC1_apply, inclC1_apply,
    ← inclusion_restrictL_comm (hD := h), ← inclusion_restrictL_comm (hD := h),
    ← inclusion_restrictL_comm (hD := h),
    ← map_sub, ← map_add, ← d1_apply, (mem_Z1_iff D 𝒰 f).1 hf (i, j, k), map_zero]

/-- `D`-inclusion on cover-level `H¹`. -/
noncomputable def h1CoverIncl {Ω : Opens X} (𝒰 : FinCover Ω) (h : D ≤ D') :
    H1Cover D 𝒰 →ₗ[ℂ] H1Cover D' 𝒰 :=
  Submodule.mapQ _ _ (LinearMap.restrict (inclC1 D 𝒰 h) (fun _ hf => inclC1_mem_Z1 D h hf))
    (fun z hz => by
      rw [Submodule.mem_comap] at hz ⊢
      obtain ⟨g, hg⟩ := hz
      have hg' : d0 D 𝒰 g = (z : C1 D 𝒰) := hg
      refine ⟨inclC0 D 𝒰 h g, ?_⟩
      change d0 D' 𝒰 (inclC0 D 𝒰 h g) =
        (↑(LinearMap.restrict (inclC1 D 𝒰 h) (fun _ hf => inclC1_mem_Z1 D h hf) z) : C1 D' 𝒰)
      rw [LinearMap.coe_restrict_apply, ← hg']
      funext p
      show d0 D' 𝒰 (inclC0 D 𝒰 h g) p = inclC1 D 𝒰 h (d0 D 𝒰 g) p
      rw [d0_apply, inclC1_apply, d0_apply, inclC0_apply, inclC0_apply, map_sub,
        inclusion_restrictL_comm (hD := h), inclusion_restrictL_comm (hD := h)])

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem h1CoverIncl_mk {Ω : Opens X} {𝒰 : FinCover Ω} (h : D ≤ D') (f : Z1 D 𝒰) :
    h1CoverIncl D 𝒰 h (H1Cover.mk D 𝒰 f) =
      H1Cover.mk D' 𝒰 (LinearMap.restrict (inclC1 D 𝒰 h) (fun _ hf => inclC1_mem_Z1 D h hf) f) :=
  Submodule.mapQ_apply _ _ _ f

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem inclC1_comp_resC1 {Ω : Opens X} {𝒰 𝒱 : FinCover Ω} (h : D ≤ D') (τ : Fin 𝒱.n → Fin 𝒰.n)
    (hτ : IsRefIdx 𝒰 𝒱 τ) (f : C1 D 𝒰) :
    inclC1 D 𝒱 h (resC1 D τ hτ f) = resC1 D' τ hτ (inclC1 D 𝒰 h f) := by
  funext p
  change Submodule.inclusion (RS.Cech.linSysOn_mono h) (resC1 D τ hτ f p) =
    resC1 D' τ hτ (inclC1 D 𝒰 h f) p
  rw [resC1_apply, resC1_apply, inclC1_apply]
  exact inclusion_restrictL_comm D (inf_le_inf (hτ p.1) (hτ p.2)) h (f (τ p.1, τ p.2))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem h1CoverIncl_resH1 {Ω : Opens X} {𝒰 𝒱 : FinCover Ω} (h : D ≤ D') (τ : Fin 𝒱.n → Fin 𝒰.n)
    (hτ : IsRefIdx 𝒰 𝒱 τ) (ξ : H1Cover D 𝒰) :
    h1CoverIncl D 𝒱 h (resH1 D τ hτ ξ) = resH1 D' τ hτ (h1CoverIncl D 𝒰 h ξ) := by
  obtain ⟨f, rfl⟩ := H1Cover.mk_surjective D 𝒰 ξ
  rw [resH1_mk, h1CoverIncl_mk, h1CoverIncl_mk, resH1_mk]
  congr 1

/-- `D`-monotone functoriality of `H¹`: `H1Incl h : H1 D →ₗ H1 D'` for `D ≤ D'`. -/
noncomputable def H1Incl (h : D ≤ D') : H1 D →ₗ[ℂ] H1 D' :=
  Module.DirectLimit.map (fun 𝒰 : FinCover (⊤ : Opens X) => h1CoverIncl D 𝒰 h) (fun 𝒰 𝒱 h𝒰𝒱 => by
    apply LinearMap.ext
    intro ξ
    change h1CoverIncl D 𝒱 h (resH1' D h𝒰𝒱 ξ) = resH1' D' h𝒰𝒱 (h1CoverIncl D 𝒰 h ξ)
    rw [resH1'_eq_resH1 D h𝒰𝒱 (chosenRefIdx h𝒰𝒱) (chosenRefIdx_spec h𝒰𝒱),
      resH1'_eq_resH1 D' h𝒰𝒱 (chosenRefIdx h𝒰𝒱) (chosenRefIdx_spec h𝒰𝒱)]
    exact h1CoverIncl_resH1 D h (chosenRefIdx h𝒰𝒱) (chosenRefIdx_spec h𝒰𝒱) ξ)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem H1Incl_toH1 (h : D ≤ D') (𝒰 : FinCover (⊤ : Opens X)) (c : H1Cover D 𝒰) :
    H1Incl D h (toH1 D 𝒰 c) = toH1 D' 𝒰 (h1CoverIncl D 𝒰 h c) :=
  Module.DirectLimit.map_apply_of _ _ c

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem H1Incl_id : H1Incl D (le_refl D) = LinearMap.id := by
  apply LinearMap.ext
  intro ξ
  induction ξ using H1.induction_on with
  | _ 𝒰 c =>
    rw [H1Incl_toH1, LinearMap.id_apply]
    congr 1
    obtain ⟨f, rfl⟩ := H1Cover.mk_surjective D 𝒰 c
    rw [h1CoverIncl_mk]
    congr 1

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem H1Incl_comp {D'' : RS.Divisor X} (h : D ≤ D') (h' : D' ≤ D'') :
    H1Incl D' h' ∘ₗ H1Incl D h = H1Incl D (h.trans h') := by
  apply LinearMap.ext
  intro ξ
  induction ξ using H1.induction_on with
  | _ 𝒰 c =>
    -- `simp only` traverses once; three successive `rw`s of the same `@[simp]` lemma each
    -- re-solve the direct-limit unification and together blow the heartbeat budget.
    simp only [LinearMap.comp_apply, H1Incl_toH1]
    congr 1
    obtain ⟨f, rfl⟩ := H1Cover.mk_surjective D 𝒰 c
    simp only [h1CoverIncl_mk]
    congr 1

/-!
### Leray interface (recorded; proof owned by dolbeault-comparison / dbar-solvability)

`toH1_surjective_of_isGood [CompactSpace X] {𝒰 : FinCover (⊤ : Opens X)} (h𝒰 : 𝒰.IsGood) :
    Function.Surjective (toH1 D 𝒰)`

together with `toH1_injective` (`Injectivity.lean`) this is Forster 12.8. Its input, disk
acyclicity `∀ (V : Opens X), IsChartDisk V → ∀ 𝒱 : FinCover V, Subsingleton (H1Cover D 𝒱)`, is
owned by **dbar-solvability**; the surjectivity statement itself is owned by
**dolbeault-comparison**. Neither is proved in this unit (§7).
-/

end RS.Cech
