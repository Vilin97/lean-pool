/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Cech.H0

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
    resC0 D τ hτ f k = LinSysOn.restrictL D (hτ k) (f (τ k)) := rfl

/-- Restriction of `1`-cochains along a refinement index `τ`. -/
noncomputable def resC1 (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) : C1 D 𝒰 →ₗ[ℂ] C1 D 𝒱 :=
  LinearMap.pi fun p : Fin 𝒱.n × Fin 𝒱.n =>
    (LinSysOn.restrictL D (inf_le_inf (hτ p.1) (hτ p.2))).comp (LinearMap.proj (τ p.1, τ p.2))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC1_apply (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) (f : C1 D 𝒰)
    (p : Fin 𝒱.n × Fin 𝒱.n) :
    resC1 D τ hτ f p = LinSysOn.restrictL D (inf_le_inf (hτ p.1) (hτ p.2)) (f (τ p.1, τ p.2)) :=
  rfl

variable (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC1_comp_d0 : (resC1 D τ hτ) ∘ₗ (d0 D 𝒰) = (d0 D 𝒱) ∘ₗ (resC0 D τ hτ) := by
  apply LinearMap.ext
  intro f
  funext p
  change LinSysOn.restrictL D (inf_le_inf (hτ p.1) (hτ p.2)) (d0 D 𝒰 f (τ p.1, τ p.2)) =
    d0 D 𝒱 (resC0 D τ hτ f) p
  rw [d0_apply, d0_apply, resC0_apply, resC0_apply]
  simp only [map_sub]
  rw [restrictL_restrictL D inf_le_right (inf_le_inf (hτ p.1) (hτ p.2))
      ((inf_le_inf (hτ p.1) (hτ p.2)).trans inf_le_right),
    restrictL_restrictL D inf_le_left (inf_le_inf (hτ p.1) (hτ p.2))
      ((inf_le_inf (hτ p.1) (hτ p.2)).trans inf_le_left),
    restrictL_restrictL D (hτ p.2) inf_le_right (inf_le_right.trans (hτ p.2)),
    restrictL_restrictL D (hτ p.1) inf_le_left (inf_le_left.trans (hτ p.1))]

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
  have hzero : d1 D 𝒰 f (a, b, c) = 0 := (mem_Z1_iff D 𝒰 f).1 hf (a, b, c)
  rw [d1_apply] at hzero
  have hcongr := congrArg (LinSysOn.restrictL D h) hzero
  simp only [map_add, map_sub, map_zero] at hcongr
  rw [restrictL_restrictL D (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h hbc,
    restrictL_restrictL D (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h hac,
    restrictL_restrictL D inf_le_left h hab] at hcongr
  exact hcongr

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC1_mem_Z1 {f : C1 D 𝒰} (hf : f ∈ Z1 D 𝒰) : resC1 D τ hτ f ∈ Z1 D 𝒱 := by
  rw [mem_Z1_iff]
  rintro ⟨k, l, m⟩
  rw [d1_apply, resC1_apply, resC1_apply, resC1_apply]
  set hkτ : 𝒱.U k ⊓ 𝒱.U l ⊓ 𝒱.U m ≤ 𝒰.U (τ k) := (inf_le_left.trans inf_le_left).trans (hτ k)
    with hkτ_def
  set hlτ : 𝒱.U k ⊓ 𝒱.U l ⊓ 𝒱.U m ≤ 𝒰.U (τ l) := (inf_le_left.trans inf_le_right).trans (hτ l)
    with hlτ_def
  set hmτ : 𝒱.U k ⊓ 𝒱.U l ⊓ 𝒱.U m ≤ 𝒰.U (τ m) := inf_le_right.trans (hτ m) with hmτ_def
  have key := Z1.rel_res D hf (τ k) (τ l) (τ m)
    (le_inf (le_inf hkτ hlτ) hmτ) (le_inf hlτ hmτ) (le_inf hkτ hmτ) (le_inf hkτ hlτ)
  rw [restrictL_restrictL D (inf_le_inf (hτ l) (hτ m))
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf hlτ hmτ),
    restrictL_restrictL D (inf_le_inf (hτ k) (hτ m))
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf hkτ hmτ),
    restrictL_restrictL D (inf_le_inf (hτ k) (hτ l)) inf_le_left (le_inf hkτ hlτ)]
  exact key

/-! ### `resZ1`, `resH1` -/

/-- The induced map on `1`-cocycles. -/
noncomputable def resZ1 : Z1 D 𝒰 →ₗ[ℂ] Z1 D 𝒱 :=
  LinearMap.restrict (resC1 D τ hτ) (fun _ hf => resC1_mem_Z1 D τ hτ hf)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resZ1_apply_coe (f : Z1 D 𝒰) :
    (resZ1 D τ hτ f : C1 D 𝒱) = resC1 D τ hτ (f : C1 D 𝒰) := rfl

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
  set h : C0 D 𝒱 :=
    fun k => LinSysOn.restrictL D (le_inf (hτ k) (hτ' k)) ((f : C1 D 𝒰) (τ k, τ' k)) with hh_def
  have hdiff : (resZ1 D τ hτ f : C1 D 𝒱) - (resZ1 D τ' hτ' f : C1 D 𝒱) = d0 D 𝒱 (-h) := by
    funext p
    obtain ⟨k, l⟩ := p
    change resC1 D τ hτ (f : C1 D 𝒰) (k, l) - resC1 D τ' hτ' (f : C1 D 𝒰) (k, l) =
      d0 D 𝒱 (-h) (k, l)
    set hab : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒰.U (τ k) ⊓ 𝒰.U (τ l) :=
      le_inf (inf_le_left.trans (hτ k)) (inf_le_right.trans (hτ l)) with hhab_def
    set hbc : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒰.U (τ l) ⊓ 𝒰.U (τ' l) :=
      le_inf (inf_le_right.trans (hτ l)) (inf_le_right.trans (hτ' l)) with hhbc_def
    set hac : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒰.U (τ k) ⊓ 𝒰.U (τ' l) :=
      le_inf (inf_le_left.trans (hτ k)) (inf_le_right.trans (hτ' l)) with hhac_def
    set hab' : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒰.U (τ k) ⊓ 𝒰.U (τ' k) :=
      le_inf (inf_le_left.trans (hτ k)) (inf_le_left.trans (hτ' k)) with hhab'_def
    set hbc' : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒰.U (τ' k) ⊓ 𝒰.U (τ' l) :=
      le_inf (inf_le_left.trans (hτ' k)) (inf_le_right.trans (hτ' l)) with hhbc'_def
    have keyA := Z1.rel_res D hmem (τ k) (τ l) (τ' l) (le_inf hab (inf_le_right.trans (hτ' l)))
      hbc hac hab
    have keyB := Z1.rel_res D hmem (τ k) (τ' k) (τ' l) (le_inf hab' (inf_le_right.trans (hτ' l)))
      hbc' hac hab'
    have hcomb : LinSysOn.restrictL D hab ((f : C1 D 𝒰) (τ k, τ l)) -
        LinSysOn.restrictL D hbc' ((f : C1 D 𝒰) (τ' k, τ' l)) =
        LinSysOn.restrictL D hab' ((f : C1 D 𝒰) (τ k, τ' k)) -
        LinSysOn.restrictL D hbc ((f : C1 D 𝒰) (τ l, τ' l)) := by
      have e : LinSysOn.restrictL D hab ((f : C1 D 𝒰) (τ k, τ l)) -
          LinSysOn.restrictL D hbc' ((f : C1 D 𝒰) (τ' k, τ' l)) -
          (LinSysOn.restrictL D hab' ((f : C1 D 𝒰) (τ k, τ' k)) -
            LinSysOn.restrictL D hbc ((f : C1 D 𝒰) (τ l, τ' l))) =
          (LinSysOn.restrictL D hbc ((f : C1 D 𝒰) (τ l, τ' l)) -
            LinSysOn.restrictL D hac ((f : C1 D 𝒰) (τ k, τ' l)) +
            LinSysOn.restrictL D hab ((f : C1 D 𝒰) (τ k, τ l))) -
          (LinSysOn.restrictL D hbc' ((f : C1 D 𝒰) (τ' k, τ' l)) -
            LinSysOn.restrictL D hac ((f : C1 D 𝒰) (τ k, τ' l)) +
            LinSysOn.restrictL D hab' ((f : C1 D 𝒰) (τ k, τ' k))) := by
        abel
      rw [keyA, keyB, sub_zero] at e
      exact sub_eq_zero.1 e
    have eεδ : LinSysOn.restrictL D hbc ((f : C1 D 𝒰) (τ l, τ' l)) =
        LinSysOn.restrictL D (inf_le_right : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒱.U l) (h l) := by
      change LinSysOn.restrictL D hbc ((f : C1 D 𝒰) (τ l, τ' l)) =
        LinSysOn.restrictL D inf_le_right
          (LinSysOn.restrictL D (le_inf (hτ l) (hτ' l)) ((f : C1 D 𝒰) (τ l, τ' l)))
      rw [restrictL_restrictL]
    have eγhab' : LinSysOn.restrictL D hab' ((f : C1 D 𝒰) (τ k, τ' k)) =
        LinSysOn.restrictL D (inf_le_left : 𝒱.U k ⊓ 𝒱.U l ≤ 𝒱.U k) (h k) := by
      change LinSysOn.restrictL D hab' ((f : C1 D 𝒰) (τ k, τ' k)) =
        LinSysOn.restrictL D inf_le_left
          (LinSysOn.restrictL D (le_inf (hτ k) (hτ' k)) ((f : C1 D 𝒰) (τ k, τ' k)))
      rw [restrictL_restrictL]
    change LinSysOn.restrictL D hab ((f : C1 D 𝒰) (τ k, τ l)) -
      LinSysOn.restrictL D hbc' ((f : C1 D 𝒰) (τ' k, τ' l)) = d0 D 𝒱 (-h) (k, l)
    rw [hcomb, eγhab', eεδ, d0_apply]
    change LinSysOn.restrictL D inf_le_left (h k) - LinSysOn.restrictL D inf_le_right (h l) =
      LinSysOn.restrictL D inf_le_right ((-h) l) - LinSysOn.restrictL D inf_le_left ((-h) k)
    rw [show (-h) l = -(h l) from rfl, show (-h) k = -(h k) from rfl, map_neg, map_neg]
    abel
  rw [resH1_mk, resH1_mk, ← sub_eq_zero, ← map_sub, H1Cover.mk_eq_zero_iff]
  change (↑(resZ1 D τ hτ f) - ↑(resZ1 D τ' hτ' f) : C1 D 𝒱) ∈ B1 D 𝒱
  rw [hdiff]
  exact ⟨-h, rfl⟩

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
  apply Subtype.ext
  rw [resZ1_apply_coe]
  change resC1 D id h (f : C1 D 𝒰) = (f : C1 D 𝒰)
  rw [resC1_id]
  rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resH1_id (h : IsRefIdx 𝒰 𝒰 id) : resH1 D id h = LinearMap.id := by
  apply LinearMap.ext
  intro ξ
  obtain ⟨f, rfl⟩ := H1Cover.mk_surjective D 𝒰 ξ
  rw [resH1_mk, resZ1_id]
  rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC0_comp {𝒲 : FinCover Ω} (σ : Fin 𝒲.n → Fin 𝒱.n) (hσ : IsRefIdx 𝒱 𝒲 σ) :
    (resC0 D σ hσ) ∘ₗ (resC0 D τ hτ) =
      resC0 D (τ ∘ σ) (fun k => (hσ k).trans (hτ (σ k))) := by
  apply LinearMap.ext
  intro f
  funext k
  change LinSysOn.restrictL D (hσ k) (resC0 D τ hτ f (σ k)) =
    LinSysOn.restrictL D ((hσ k).trans (hτ (σ k))) (f (τ (σ k)))
  rw [resC0_apply]
  exact restrictL_restrictL D (hτ (σ k)) (hσ k) ((hσ k).trans (hτ (σ k))) (f (τ (σ k)))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resC1_comp {𝒲 : FinCover Ω} (σ : Fin 𝒲.n → Fin 𝒱.n) (hσ : IsRefIdx 𝒱 𝒲 σ) :
    (resC1 D σ hσ) ∘ₗ (resC1 D τ hτ) =
      resC1 D (τ ∘ σ) (fun k => (hσ k).trans (hτ (σ k))) := by
  apply LinearMap.ext
  intro f
  funext p
  obtain ⟨k, l⟩ := p
  change LinSysOn.restrictL D (inf_le_inf (hσ k) (hσ l)) (resC1 D τ hτ f (σ k, σ l)) =
    LinSysOn.restrictL D (inf_le_inf ((hσ k).trans (hτ (σ k))) ((hσ l).trans (hτ (σ l))))
      (f (τ (σ k), τ (σ l)))
  rw [resC1_apply]
  exact restrictL_restrictL D (inf_le_inf (hτ (σ k)) (hτ (σ l))) (inf_le_inf (hσ k) (hσ l))
    (inf_le_inf ((hσ k).trans (hτ (σ k))) ((hσ l).trans (hτ (σ l)))) (f (τ (σ k), τ (σ l)))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resZ1_comp {𝒲 : FinCover Ω} (σ : Fin 𝒲.n → Fin 𝒱.n) (hσ : IsRefIdx 𝒱 𝒲 σ) (f : Z1 D 𝒰) :
    (resZ1 D σ hσ) (resZ1 D τ hτ f) = resZ1 D (τ ∘ σ) (fun k => (hσ k).trans (hτ (σ k))) f := by
  apply Subtype.ext
  simp only [resZ1_apply_coe]
  exact LinearMap.congr_fun (resC1_comp D τ hτ σ hσ) (f : C1 D 𝒰)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem resH1_comp {𝒲 : FinCover Ω} (σ : Fin 𝒲.n → Fin 𝒱.n) (hσ : IsRefIdx 𝒱 𝒲 σ) :
    (resH1 D σ hσ) ∘ₗ (resH1 D τ hτ) = resH1 D (τ ∘ σ) (fun k => (hσ k).trans (hτ (σ k))) := by
  apply LinearMap.ext
  intro ξ
  obtain ⟨f, rfl⟩ := H1Cover.mk_surjective D 𝒰 ξ
  change resH1 D σ hσ (resH1 D τ hτ (H1Cover.mk D 𝒰 f)) = _
  simp only [resH1_mk]
  rw [resZ1_comp]
  exact (resH1_mk D _ _ f).symm

end RS.Cech
