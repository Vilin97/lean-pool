/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import LeanPool.JacobianDiffgeo.Cech.Cochains
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Refinement maps, 12.3 independence (CC8)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.4, proof plans §6.4–§6.7).

* `resC0`/`resC1`: restriction of cochains along a chosen refinement index `τ`.
* `Z1.rel_res`: the cocycle-relation workhorse (§6.5) — any cocycle triple relation, restricted
  down to any smaller open.
* `resZ1`/`resH1`: the induced maps on cocycles / cover-level `H¹`.
* `resH1_indep` (Forster 12.3): the induced `H¹`-map does not depend on the chosen refinement
  index — the `DirectedSystem` key for `Colimit.lean`.

**Forster 12.4** (`resH1_injective`/`toH1_injective`) has landed — see `Injectivity.lean`
(sheaf-axiom gluing argument via `injPatch`/`exists_injGlue`, no analysis).
-/

public section

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (D : RS.Divisor X) {Ω : Opens X} {𝒰 𝒱 : FinCover Ω}

/-! ### Restriction along a refinement index -/

/-- Restriction of `0`-cochains along a refinement index `τ`. -/
noncomputable def resC0 (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) : C0 D 𝒰 →ₗ[ℂ] C0 D 𝒱 :=
  LinearMap.pi fun k => (LinSysOn.restrictL D (hτ k)).comp (LinearMap.proj (τ k))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC0_apply (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) (f : C0 D 𝒰) (k : Fin 𝒱.n) :
    resC0 D τ hτ f k = LinSysOn.restrictL D (hτ k) (f (τ k)) := by rfl

/-- Restriction of `1`-cochains along a refinement index `τ`. -/
@[expose]
noncomputable def resC1 (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) : C1 D 𝒰 →ₗ[ℂ] C1 D 𝒱 :=
  LinearMap.pi fun p : Fin 𝒱.n × Fin 𝒱.n =>
    (LinSysOn.restrictL D (inf_le_inf (hτ p.1) (hτ p.2))).comp (LinearMap.proj (τ p.1, τ p.2))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC1_apply (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) (f : C1 D 𝒰)
    (p : Fin 𝒱.n × Fin 𝒱.n) :
    resC1 D τ hτ f p = LinSysOn.restrictL D (inf_le_inf (hτ p.1) (hτ p.2)) (f (τ p.1, τ p.2)) := by
  rfl

variable (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC1_comp_d0 : (resC1 D τ hτ) ∘ₗ (d0 D 𝒰) = (d0 D 𝒱) ∘ₗ (resC0 D τ hτ) := by
  apply LinearMap.ext
  intro f
  funext p
  have hij := inf_le_inf (hτ p.1) (hτ p.2)
  refine (map_sub (LinSysOn.restrictL D hij) _ _).trans ?_
  exact congrArg₂ (· - ·)
    ((restrictL_restrictL D inf_le_right hij (inf_le_right.trans (hτ p.2)) _).trans
      (restrictL_restrictL D (hτ p.2) inf_le_right _ _).symm)
    ((restrictL_restrictL D inf_le_left hij (inf_le_left.trans (hτ p.1)) _).trans
      (restrictL_restrictL D (hτ p.1) inf_le_left _ _).symm)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC1_mem_B1 {f : C1 D 𝒰} (hf : f ∈ B1 D 𝒰) : resC1 D τ hτ f ∈ B1 D 𝒱 := by
  obtain ⟨g, rfl⟩ := hf
  exact ⟨resC0 D τ hτ g, (LinearMap.congr_fun (resC1_comp_d0 D τ hτ) g).symm⟩

/-! ### The cocycle-relation workhorse (§6.5) -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Forster p. 97 / the workhorse: any cocycle-relation triple, restricted to any smaller
open `W` (via arbitrary — by proof irrelevance, any — witnessing inequalities). -/
theorem Z1.rel_res {f : C1 D 𝒰} (hf : f ∈ Z1 D 𝒰) (a b c : Fin 𝒰.n) {W : Opens X}
    (h : W ≤ 𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c) (hbc : W ≤ 𝒰.U b ⊓ 𝒰.U c) (hac : W ≤ 𝒰.U a ⊓ 𝒰.U c)
    (hab : W ≤ 𝒰.U a ⊓ 𝒰.U b) :
    LinSysOn.restrictL D hbc (f (b, c)) - LinSysOn.restrictL D hac (f (a, c)) +
      LinSysOn.restrictL D hab (f (a, b)) = 0 := by
  have hcongr := congrArg (LinSysOn.restrictL D h) ((mem_Z1_iff D 𝒰 f).1 hf (a, b, c))
  simp only [d1_apply, map_add, map_sub, map_zero] at hcongr
  rw [restrictL_restrictL D (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h hbc,
    restrictL_restrictL D (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h hac,
    restrictL_restrictL D inf_le_left h hab] at hcongr
  exact hcongr

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC1_mem_Z1 {f : C1 D 𝒰} (hf : f ∈ Z1 D 𝒰) : resC1 D τ hτ f ∈ Z1 D 𝒱 := by
  apply (mem_Z1_iff D 𝒱 _).2
  rintro ⟨k, l, m⟩
  have hkτ : 𝒱.U k ⊓ 𝒱.U l ⊓ 𝒱.U m ≤ 𝒰.U (τ k) := (inf_le_left.trans inf_le_left).trans (hτ k)
  have hlτ : 𝒱.U k ⊓ 𝒱.U l ⊓ 𝒱.U m ≤ 𝒰.U (τ l) := (inf_le_left.trans inf_le_right).trans (hτ l)
  have hmτ : 𝒱.U k ⊓ 𝒱.U l ⊓ 𝒱.U m ≤ 𝒰.U (τ m) := inf_le_right.trans (hτ m)
  refine Eq.trans ?_ (Z1.rel_res D hf (τ k) (τ l) (τ m)
    (le_inf (le_inf hkτ hlτ) hmτ) (le_inf hlτ hmτ) (le_inf hkτ hmτ) (le_inf hkτ hlτ))
  exact congrArg₂ (· + ·)
    (congrArg₂ (· - ·)
      (restrictL_restrictL D _ _ (le_inf hlτ hmτ) _)
      (restrictL_restrictL D _ _ (le_inf hkτ hmτ) _))
    (restrictL_restrictL D _ _ (le_inf hkτ hlτ) _)

/-! ### `resZ1`, `resH1` -/

/-- The induced map on `1`-cocycles. -/
@[expose] noncomputable def resZ1 : Z1 D 𝒰 →ₗ[ℂ] Z1 D 𝒱 :=
  LinearMap.restrict (resC1 D τ hτ) (fun _ hf => resC1_mem_Z1 D τ hτ hf)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resZ1_apply_coe (f : Z1 D 𝒰) :
    (resZ1 D τ hτ f : C1 D 𝒱) = resC1 D τ hτ (f : C1 D 𝒰) := by rfl

/-- The induced map on cover-level `H¹`. -/
noncomputable def resH1 : H1Cover D 𝒰 →ₗ[ℂ] H1Cover D 𝒱 :=
  Submodule.mapQ _ _ (resZ1 D τ hτ) (fun z hz => by
    simp only [Submodule.mem_comap] at hz ⊢
    exact resC1_mem_B1 D τ hτ hz)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem resH1_mk (f : Z1 D 𝒰) :
    resH1 D τ hτ (H1Cover.mk D 𝒰 f) = H1Cover.mk D 𝒱 (resZ1 D τ hτ f) :=
  Submodule.mapQ_apply _ _ _ f

/-! ### Refinement independence (Forster 12.3) -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resH1_indep (τ τ' : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) (hτ' : IsRefIdx 𝒰 𝒱 τ') :
    resH1 D τ hτ = resH1 D τ' hτ' := by
  apply LinearMap.ext
  intro ξ
  obtain ⟨f, rfl⟩ := H1Cover.mk_surjective D 𝒰 ξ
  have hmem : (f : C1 D 𝒰) ∈ Z1 D 𝒰 := f.2
  -- The connecting `0`-cochain `h_k := restrict (f (τ k, τ' k))` (D3/§6.6).
  let h : C0 D 𝒱 :=
    fun k => LinSysOn.restrictL D (le_inf (hτ k) (hτ' k)) ((f : C1 D 𝒰) (τ k, τ' k))
  have hdiff : (resZ1 D τ hτ f : C1 D 𝒱) - (resZ1 D τ' hτ' f : C1 D 𝒱) = d0 D 𝒱 (-h) := by
    funext p
    obtain ⟨k, l⟩ := p
    change resC1 D τ hτ (f : C1 D 𝒰) (k, l) - resC1 D τ' hτ' (f : C1 D 𝒰) (k, l) =
      d0 D 𝒱 (-h) (k, l)
    have hab : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒰.U (τ k) ⊓ 𝒰.U (τ l) :=
      le_inf (inf_le_left.trans (hτ k)) (inf_le_right.trans (hτ l))
    have hbc : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒰.U (τ l) ⊓ 𝒰.U (τ' l) :=
      le_inf (inf_le_right.trans (hτ l)) (inf_le_right.trans (hτ' l))
    have hac : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒰.U (τ k) ⊓ 𝒰.U (τ' l) :=
      le_inf (inf_le_left.trans (hτ k)) (inf_le_right.trans (hτ' l))
    have hab' : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒰.U (τ k) ⊓ 𝒰.U (τ' k) :=
      le_inf (inf_le_left.trans (hτ k)) (inf_le_left.trans (hτ' k))
    have hbc' : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒰.U (τ' k) ⊓ 𝒰.U (τ' l) :=
      le_inf (inf_le_left.trans (hτ' k)) (inf_le_right.trans (hτ' l))
    have keyA := Z1.rel_res D hmem (τ k) (τ l) (τ' l) (le_inf hab (inf_le_right.trans (hτ' l)))
      hbc hac hab
    have keyB := Z1.rel_res D hmem (τ k) (τ' k) (τ' l) (le_inf hab' (inf_le_right.trans (hτ' l)))
      hbc' hac hab'
    have hcomb : LinSysOn.restrictL D hab ((f : C1 D 𝒰) (τ k, τ l)) -
        LinSysOn.restrictL D hbc' ((f : C1 D 𝒰) (τ' k, τ' l)) =
        LinSysOn.restrictL D hab' ((f : C1 D 𝒰) (τ k, τ' k)) -
        LinSysOn.restrictL D hbc ((f : C1 D 𝒰) (τ l, τ' l)) := by
      have hA := eq_neg_of_add_eq_zero_right keyA
      have hB := eq_neg_of_add_eq_zero_right keyB
      rw [neg_sub] at hA hB
      rw [hA, hB, sub_right_comm]
    have eεδ : LinSysOn.restrictL D hbc ((f : C1 D 𝒰) (τ l, τ' l)) =
        LinSysOn.restrictL D (inf_le_right : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒱.U l) (h l) :=
      (restrictL_restrictL D (le_inf (hτ l) (hτ' l)) inf_le_right hbc _).symm
    have eγhab' : LinSysOn.restrictL D hab' ((f : C1 D 𝒰) (τ k, τ' k)) =
        LinSysOn.restrictL D (inf_le_left : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒱.U k) (h k) :=
      (restrictL_restrictL D (le_inf (hτ k) (hτ' k)) inf_le_left hab' _).symm
    exact hcomb.trans ((congrArg₂ (· - ·) eγhab' eεδ).trans
      ((neg_sub _ _).symm.trans (congrFun (map_neg (d0 D 𝒱) h) (k, l)).symm))
  have hclasses : H1Cover.mk D 𝒱 (resZ1 D τ hτ f) = H1Cover.mk D 𝒱 (resZ1 D τ' hτ' f) :=
    (Submodule.Quotient.eq _).2 ⟨-h, hdiff.symm⟩
  exact (resH1_mk D τ hτ f).trans (hclasses.trans (resH1_mk D τ' hτ' f).symm)

/-! ### Functor laws: identity and composition -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC0_id (h : IsRefIdx 𝒰 𝒰 id) : resC0 D id h = LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext i
  exact restrictL_id D (f i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC1_id (h : IsRefIdx 𝒰 𝒰 id) : resC1 D id h = LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext p
  obtain ⟨i, j⟩ := p
  exact restrictL_id D (f (i, j))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resZ1_id (h : IsRefIdx 𝒰 𝒰 id) : resZ1 D id h = LinearMap.id := by
  apply LinearMap.ext
  intro f
  exact Subtype.ext (LinearMap.congr_fun (resC1_id D h) (f : C1 D 𝒰))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resH1_id (h : IsRefIdx 𝒰 𝒰 id) : resH1 D id h = LinearMap.id := by
  apply LinearMap.ext
  intro ξ
  obtain ⟨f, rfl⟩ := H1Cover.mk_surjective D 𝒰 ξ
  exact (resH1_mk D id h f).trans
    (congrArg (H1Cover.mk D 𝒰) (LinearMap.congr_fun (resZ1_id D h) f))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC0_comp {𝒲 : FinCover Ω} (σ : Fin 𝒲.n → Fin 𝒱.n) (hσ : IsRefIdx 𝒱 𝒲 σ) :
    (resC0 D σ hσ) ∘ₗ (resC0 D τ hτ) =
      resC0 D (τ ∘ σ) (fun k => (hσ k).trans (hτ (σ k))) := by
  apply LinearMap.ext
  intro f
  funext k
  exact restrictL_restrictL D (hτ (σ k)) (hσ k) ((hσ k).trans (hτ (σ k))) (f (τ (σ k)))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC1_comp {𝒲 : FinCover Ω} (σ : Fin 𝒲.n → Fin 𝒱.n) (hσ : IsRefIdx 𝒱 𝒲 σ) :
    (resC1 D σ hσ) ∘ₗ (resC1 D τ hτ) =
      resC1 D (τ ∘ σ) (fun k => (hσ k).trans (hτ (σ k))) := by
  apply LinearMap.ext
  intro f
  funext p
  obtain ⟨k, l⟩ := p
  exact restrictL_restrictL D (inf_le_inf (hτ (σ k)) (hτ (σ l))) (inf_le_inf (hσ k) (hσ l))
    (inf_le_inf ((hσ k).trans (hτ (σ k))) ((hσ l).trans (hτ (σ l)))) (f (τ (σ k), τ (σ l)))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resZ1_comp {𝒲 : FinCover Ω} (σ : Fin 𝒲.n → Fin 𝒱.n) (hσ : IsRefIdx 𝒱 𝒲 σ) (f : Z1 D 𝒰) :
    (resZ1 D σ hσ) (resZ1 D τ hτ f) = resZ1 D (τ ∘ σ) (fun k => (hσ k).trans (hτ (σ k))) f := by
  exact Subtype.ext (LinearMap.congr_fun (resC1_comp D τ hτ σ hσ) (f : C1 D 𝒰))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resH1_comp {𝒲 : FinCover Ω} (σ : Fin 𝒲.n → Fin 𝒱.n) (hσ : IsRefIdx 𝒱 𝒲 σ) :
    (resH1 D σ hσ) ∘ₗ (resH1 D τ hτ) = resH1 D (τ ∘ σ) (fun k => (hσ k).trans (hτ (σ k))) := by
  apply LinearMap.ext
  intro ξ
  obtain ⟨f, rfl⟩ := H1Cover.mk_surjective D 𝒰 ξ
  exact (congrArg (resH1 D σ hσ) (resH1_mk D τ hτ f)).trans
    ((resH1_mk D σ hσ (resZ1 D τ hτ f)).trans
      ((congrArg (H1Cover.mk D 𝒲) (resZ1_comp D τ hτ σ hσ f)).trans
        (resH1_mk D _ _ f).symm))

end RS.Cech
