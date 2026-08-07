/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.DolbeaultComparison.Leray
import LeanPool.JacobianDiffgeo.DolbeaultComparison.Splitting

/-!
# The Dolbeault comparison `H¹(X, 𝒪) ≅ H^{0,1}(X)` (`Jacobian/DolbeaultComparison/Comparison.lean`)

Unit: dolbeault-comparison (`docs/design/dolbeault-comparison.md` §4.4/§6.4). Forster 15.14(a),
PDE-free at `D = 0`: `H01 X := Form01 X ⧸ range dbar`, the Čech → Dolbeault map `cechToH01`
(built via `H1.lift` from the per-good-cover map `toDolb`, using `dolbForm`), its injectivity
(the CR-bridge argument) and surjectivity (chart-disk dbar-solvability + PoU gluing), packaged as
`dolbeaultEquiv : H1 (0 : Divisor X) ≃ₗ[ℂ] H01 X`.

`finiteDimensional_H01` is gated on a `[FiniteDimensional ℂ (H1 (0 : Divisor X))]` hypothesis: at
the time of this build `Jacobian/Finiteness/H1Finite.lean` (the file that would discharge this
hypothesis unconditionally) has not landed; see the unit's build-log entry.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

-- `H1 D` is a `Module.DirectLimit` over the (large, `Classical`-decidable-equality) index type
-- `FinCover ⊤`; instance search for `AddCommGroup`/`Module` on it, and definitional unfolding of
-- `H1Cover`/`C0`/`C1` through it, is heavy throughout this file (mirrors `Colimit.lean`'s own
-- `directedSystemH1Cover` heartbeat bump).

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Compat: `Module.DirectLimit.addCommGroup` (needing the Pi-type hypothesis
`[∀ 𝒰, AddCommGroup (H1Cover 0 𝒰)]`) is not found by plain `inferInstance` for `H1 0` — Lean's
instance search does not automatically distribute over the `∀`-quantified instance argument of a
`Module.DirectLimit`-style instance with explicit index data; register it once, by hand, as a
concrete named instance so ordinary instance search (`Sub`, `LinearMap.ker_eq_bot`,
`LinearEquiv`'s `CoeFun`, …) finds it downstream. Spiked/isolated in a throwaway scratch file
before landing here. -/
noncomputable instance : AddCommGroup (H1 (0 : RS.Divisor X)) :=
  Module.DirectLimit.addCommGroup (fun 𝒰 : FinCover (⊤ : Opens X) => H1Cover (0 : RS.Divisor X) 𝒰)
    (fun _ _ h => resH1' (0 : RS.Divisor X) h)

/-! ### `H01 X` -/

/-- The Dolbeault `H^{0,1}(X)`: the naked quotient of `Form01 X` by `range dbar` (D3). -/
noncomputable def H01 (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  Form01 X ⧸ LinearMap.range (RS.dbar (X := X))

noncomputable instance : AddCommGroup (H01 X) :=
  Submodule.Quotient.addCommGroup _

noncomputable instance : Module ℂ (H01 X) :=
  Submodule.Quotient.module _

/-- The quotient map onto `H01 X`. -/
noncomputable def H01.mk : Form01 X →ₗ[ℂ] H01 X := Submodule.mkQ _

theorem H01.mk_surjective : Function.Surjective (H01.mk (X := X)) := Submodule.mkQ_surjective _

theorem H01.mk_eq_zero_iff {η : Form01 X} :
    H01.mk η = 0 ↔ ∃ u : SmoothC X, RS.dbar u = η := by
  rw [← LinearMap.mem_ker]
  change η ∈ LinearMap.ker (Submodule.mkQ (LinearMap.range (RS.dbar (X := X)))) ↔ _
  rw [Submodule.ker_mkQ]
  exact LinearMap.mem_range

theorem H01.mk_eq_mk_iff {η θ : Form01 X} :
    H01.mk η = H01.mk θ ↔ ∃ u : SmoothC X, RS.dbar u = η - θ := by
  rw [← sub_eq_zero, ← map_sub]
  exact H01.mk_eq_zero_iff

/-! ### `toDolb`: the Čech → Dolbeault map on a good cover -/

/-- The raw (pre-quotient) map `Z1 0 𝒰 → H01 X`, `f ↦ H01.mk (dolbForm h𝒰 f)`. Additivity and
homogeneity come from `dolbForm_add_sub_mem`/`dolbForm_smul_sub_mem` (§6.3): the discrepancies
land in `range dbar = ker H01.mk`. -/
noncomputable def toDolbRaw {𝒰 : FinCover (⊤ : Opens X)} [T2Space X] [CompactSpace X]
    (h𝒰 : 𝒰.IsGood) : Z1 (0 : RS.Divisor X) 𝒰 →ₗ[ℂ] H01 X where
  toFun f := H01.mk (RS.Dolb.dolbForm h𝒰 f)
  map_add' f f' := by
    have hmem := RS.Dolb.dolbForm_add_sub_mem h𝒰 f f'
    have hz : H01.mk (RS.Dolb.dolbForm h𝒰 (f + f') - RS.Dolb.dolbForm h𝒰 f -
        RS.Dolb.dolbForm h𝒰 f') = 0 := H01.mk_eq_zero_iff.2 (LinearMap.mem_range.mp hmem)
    rw [map_sub, map_sub, sub_sub] at hz
    exact sub_eq_zero.mp hz
  map_smul' c f := by
    have hmem := RS.Dolb.dolbForm_smul_sub_mem h𝒰 c f
    have hz : H01.mk (RS.Dolb.dolbForm h𝒰 (c • f) - c • RS.Dolb.dolbForm h𝒰 f) = 0 :=
      H01.mk_eq_zero_iff.2 (LinearMap.mem_range.mp hmem)
    rw [map_sub, map_smul] at hz
    exact sub_eq_zero.mp hz

/-- The Čech → Dolbeault map on a good cover (Forster 15.14(a) forward map, cover level). -/
noncomputable def toDolb {𝒰 : FinCover (⊤ : Opens X)} [T2Space X] [CompactSpace X]
    (h𝒰 : 𝒰.IsGood) : H1Cover (0 : RS.Divisor X) 𝒰 →ₗ[ℂ] H01 X :=
  Submodule.liftQ _ (toDolbRaw h𝒰) (by
    intro f hf
    rw [Submodule.mem_comap] at hf
    change H01.mk (RS.Dolb.dolbForm h𝒰 f) = 0
    exact H01.mk_eq_zero_iff.2
      (LinearMap.mem_range.mp (RS.Dolb.dolbForm_mem_range_of_mem_B1 h𝒰 hf)))

@[simp] theorem toDolb_mk {𝒰 : FinCover (⊤ : Opens X)} [T2Space X] [CompactSpace X]
    (h𝒰 : 𝒰.IsGood) (f : Z1 (0 : RS.Divisor X) 𝒰) :
    toDolb h𝒰 (H1Cover.mk (0 : RS.Divisor X) 𝒰 f) = H01.mk (RS.Dolb.dolbForm h𝒰 f) := by
  change Submodule.liftQ _ (toDolbRaw h𝒰) _ (Submodule.Quotient.mk f) = _
  rw [Submodule.liftQ_apply]
  rfl

theorem toDolb_res {𝒰 𝒱 : FinCover (⊤ : Opens X)} [T2Space X] [CompactSpace X]
    (h𝒰 : 𝒰.IsGood) (h𝒱 : 𝒱.IsGood) (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) :
    (toDolb h𝒱) ∘ₗ (resH1 (0 : RS.Divisor X) τ hτ) = toDolb h𝒰 := by
  apply LinearMap.ext
  intro ξ
  obtain ⟨f, rfl⟩ := H1Cover.mk_surjective (0 : RS.Divisor X) 𝒰 ξ
  change toDolb h𝒱 (resH1 (0 : RS.Divisor X) τ hτ (H1Cover.mk (0 : RS.Divisor X) 𝒰 f)) =
    toDolb h𝒰 (H1Cover.mk (0 : RS.Divisor X) 𝒰 f)
  rw [resH1_mk, toDolb_mk, toDolb_mk]
  have hmem := RS.Dolb.dolbForm_res_sub_mem h𝒰 h𝒱 τ hτ f
  rw [← sub_eq_zero, ← map_sub]
  exact H01.mk_eq_zero_iff.2 (LinearMap.mem_range.mp hmem)

/-! ### `cechToH01`: extend `toDolb` to the whole colimit via `H1.lift` -/

/-- A classical choice of good refinement of any cover. -/
noncomputable def goodRef [CompactSpace X] (𝒰 : FinCover (⊤ : Opens X)) :
    FinCover (⊤ : Opens X) := (exists_good_refinement 𝒰).choose

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem goodRef_le [CompactSpace X] (𝒰 : FinCover (⊤ : Opens X)) :
    𝒰 ≤ goodRef 𝒰 := (exists_good_refinement 𝒰).choose_spec.1

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem goodRef_isGood [CompactSpace X] (𝒰 : FinCover (⊤ : Opens X)) :
    (goodRef 𝒰).IsGood := (exists_good_refinement 𝒰).choose_spec.2


/-- `toDolb` extended to every cover by pushing to a good refinement. -/
noncomputable def toDolbAll [T2Space X] [CompactSpace X] (𝒰 : FinCover (⊤ : Opens X)) :
    H1Cover (0 : RS.Divisor X) 𝒰 →ₗ[ℂ] H01 X :=
  toDolb (goodRef_isGood 𝒰) ∘ₗ resH1' (0 : RS.Divisor X) (goodRef_le 𝒰)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Restriction along `h : 𝒰 ≤ 𝒱` followed by any `𝒱 → 𝒲` refinement index is restriction along
the composite. Term-level, so it does not spend the compat proof's budget. -/
private theorem resH1_resH1' {𝒰 𝒱 𝒲 : FinCover (⊤ : Opens X)} (h : 𝒰 ≤ 𝒱)
    {ρ : Fin 𝒱.n → Fin 𝒰.n} (hρ : IsRefIdx 𝒰 𝒱 ρ)
    {c : Fin 𝒲.n → Fin 𝒱.n} (hc : IsRefIdx 𝒱 𝒲 c) (hidx : IsRefIdx 𝒰 𝒲 (ρ ∘ c))
    (ξ : H1Cover (0 : RS.Divisor X) 𝒰) :
    resH1 (0 : RS.Divisor X) c hc (resH1' (0 : RS.Divisor X) h ξ) =
      resH1 (0 : RS.Divisor X) (ρ ∘ c) hidx ξ := by
  rw [resH1'_eq_resH1 (0 : RS.Divisor X) h ρ hρ]
  exact LinearMap.congr_fun (resH1_comp (0 : RS.Divisor X) ρ hρ c hc) ξ

/-- `toDolb` does not see which refinement index was used (`resH1_indep`). -/
private theorem toDolb_resH1_congr [T2Space X] [CompactSpace X]
    {𝒴 𝒲 : FinCover (⊤ : Opens X)} (h𝒲good : 𝒲.IsGood)
    {a b : Fin 𝒲.n → Fin 𝒴.n} (ha : IsRefIdx 𝒴 𝒲 a) (hb : IsRefIdx 𝒴 𝒲 b)
    (η : H1Cover (0 : RS.Divisor X) 𝒴) :
    toDolb h𝒲good (resH1 (0 : RS.Divisor X) a ha η) =
      toDolb h𝒲good (resH1 (0 : RS.Divisor X) b hb η) :=
  congrArg (toDolb h𝒲good) (LinearMap.congr_fun (resH1_indep (0 : RS.Divisor X) a b ha hb) η)

/-- `toDolbAll 𝒴` computed through ANY good cover `𝒲` refining `goodRef 𝒴`, via ANY refinement
index `𝒴 → 𝒲`.

`goodRef`'s own indices appear only inside this proof, never in the statement: they have type
`Fin (goodRef 𝒴).n → _`, and since `goodRef` is a `Classical.choice`, every such type sends
`whnf` through the choice term. Keeping them out of the statement is what lets the caller
(`toDolbAll_compat`) stay inside the default heartbeat budget. -/
private theorem toDolbAll_eq_toDolb [T2Space X] [CompactSpace X]
    {𝒴 𝒲 : FinCover (⊤ : Opens X)} (hg : goodRef 𝒴 ≤ 𝒲) (h𝒲good : 𝒲.IsGood)
    {a : Fin 𝒲.n → Fin 𝒴.n} (ha : IsRefIdx 𝒴 𝒲 a) (η : H1Cover (0 : RS.Divisor X) 𝒴) :
    toDolbAll 𝒴 η = toDolb h𝒲good (resH1 (0 : RS.Divisor X) a ha η) := by
  obtain ⟨τ, hτ⟩ : ∃ τ, IsRefIdx 𝒴 (goodRef 𝒴) τ :=
    ⟨chosenRefIdx (goodRef_le 𝒴), chosenRefIdx_spec (goodRef_le 𝒴)⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, IsRefIdx (goodRef 𝒴) 𝒲 σ := ⟨chosenRefIdx hg, chosenRefIdx_spec hg⟩
  have hidx : IsRefIdx 𝒴 𝒲 (τ ∘ σ) := fun k => (hσ k).trans (hτ (σ k))
  have h1 : toDolbAll 𝒴 η = toDolb h𝒲good (resH1 (0 : RS.Divisor X) (τ ∘ σ) hidx η) := by
    change toDolb (goodRef_isGood 𝒴) (resH1' (0 : RS.Divisor X) (goodRef_le 𝒴) η) = _
    rw [resH1'_eq_resH1 (0 : RS.Divisor X) (goodRef_le 𝒴) τ hτ]
    have hc1 : resH1 (0 : RS.Divisor X) σ hσ (resH1 (0 : RS.Divisor X) τ hτ η) =
        resH1 (0 : RS.Divisor X) (τ ∘ σ) hidx η :=
      LinearMap.congr_fun (resH1_comp (0 : RS.Divisor X) τ hτ σ hσ) η
    have hc2 : toDolb h𝒲good (resH1 (0 : RS.Divisor X) σ hσ (resH1 (0 : RS.Divisor X) τ hτ η)) =
        toDolb (goodRef_isGood 𝒴) (resH1 (0 : RS.Divisor X) τ hτ η) :=
      LinearMap.congr_fun (toDolb_res (goodRef_isGood 𝒴) h𝒲good σ hσ)
        (resH1 (0 : RS.Divisor X) τ hτ η)
    rw [← hc2, hc1]
  exact h1.trans (toDolb_resH1_congr h𝒲good hidx ha η)

theorem toDolbAll_compat [T2Space X] [CompactSpace X] (𝒰 𝒱 : FinCover (⊤ : Opens X)) (h : 𝒰 ≤ 𝒱)
    (ξ : H1Cover (0 : RS.Divisor X) 𝒰) :
    toDolbAll 𝒱 (resH1' (0 : RS.Divisor X) h ξ) = toDolbAll 𝒰 ξ := by
  obtain ⟨𝒲, h𝒲le, h𝒲good⟩ := exists_good_refinement ((goodRef 𝒰).meet (goodRef 𝒱))
  have hU𝒲 : goodRef 𝒰 ≤ 𝒲 := (le_meet_left _ _).trans h𝒲le
  have hV𝒲 : goodRef 𝒱 ≤ 𝒲 := (le_meet_right _ _).trans h𝒲le
  obtain ⟨a, ha⟩ : ∃ a, IsRefIdx 𝒰 𝒲 a :=
    ⟨chosenRefIdx ((goodRef_le 𝒰).trans hU𝒲), chosenRefIdx_spec ((goodRef_le 𝒰).trans hU𝒲)⟩
  obtain ⟨b, hb⟩ : ∃ b, IsRefIdx 𝒱 𝒲 b :=
    ⟨chosenRefIdx ((goodRef_le 𝒱).trans hV𝒲), chosenRefIdx_spec ((goodRef_le 𝒱).trans hV𝒲)⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, IsRefIdx 𝒰 𝒱 ρ := ⟨chosenRefIdx h, chosenRefIdx_spec h⟩
  have hidx : IsRefIdx 𝒰 𝒲 (ρ ∘ b) := fun k => (hb k).trans (hρ (b k))
  -- composed as terms rather than by `rw`: building rewrite motives over the `H1Cover`
  -- direct-limit types is expensive here.
  exact (toDolbAll_eq_toDolb hV𝒲 h𝒲good hb (resH1' (0 : RS.Divisor X) h ξ)).trans
    (((congrArg (toDolb h𝒲good) (resH1_resH1' h hρ hb hidx ξ)).trans
      (toDolb_resH1_congr h𝒲good hidx ha ξ)).trans
      (toDolbAll_eq_toDolb hU𝒲 h𝒲good ha ξ).symm)

/-- **THE comparison map on the colimit** (Forster 15.14(a), forward map). -/
noncomputable def cechToH01 [T2Space X] [CompactSpace X] :
    H1 (0 : RS.Divisor X) →ₗ[ℂ] H01 X :=
  H1.lift (0 : RS.Divisor X) toDolbAll toDolbAll_compat

@[simp] theorem cechToH01_toH1_all [T2Space X] [CompactSpace X] (𝒰 : FinCover (⊤ : Opens X))
    (c : H1Cover (0 : RS.Divisor X) 𝒰) : cechToH01 (toH1 (0 : RS.Divisor X) 𝒰 c) = toDolbAll 𝒰 c :=
  H1.lift_toH1 (0 : RS.Divisor X) toDolbAll toDolbAll_compat 𝒰 c

theorem cechToH01_toH1 [T2Space X] [CompactSpace X] {𝒰 : FinCover (⊤ : Opens X)}
    (h𝒰 : 𝒰.IsGood) (c : H1Cover (0 : RS.Divisor X) 𝒰) :
    cechToH01 (toH1 (0 : RS.Divisor X) 𝒰 c) = toDolb h𝒰 c := by
  rw [cechToH01_toH1_all]
  change toDolb (goodRef_isGood 𝒰) (resH1' (0 : RS.Divisor X) (goodRef_le 𝒰) c) = toDolb h𝒰 c
  rw [resH1'_eq_resH1 (0 : RS.Divisor X) (goodRef_le 𝒰) (chosenRefIdx (goodRef_le 𝒰))
    (chosenRefIdx_spec (goodRef_le 𝒰))]
  exact LinearMap.congr_fun (toDolb_res h𝒰 (goodRef_isGood 𝒰) (chosenRefIdx (goodRef_le 𝒰))
    (chosenRefIdx_spec (goodRef_le 𝒰))) c

/-! ### Injectivity -/

theorem cechToH01_injective [T2Space X] [CompactSpace X] :
    Function.Injective (cechToH01 (X := X)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro ξ hξ
  obtain ⟨𝒰, h𝒰, f, hf⟩ := exists_rep_good (0 : RS.Divisor X) ξ
  obtain ⟨F, rfl⟩ := H1Cover.mk_surjective (0 : RS.Divisor X) 𝒰 f
  rw [← hf, cechToH01_toH1 h𝒰, toDolb_mk, H01.mk_eq_zero_iff] at hξ
  obtain ⟨u, hu⟩ := hξ
  set s := (RS.Dolb.exists_smoothSplitting 𝒰 F).some with hs_def
  have hform : RS.Dolb.dolbForm h𝒰 F = (s.glueData h𝒰).form := rfl
  rw [hform] at hu
  have hIsDbarOn_u : ∀ i, IsDbarOn (⇑u) (s.glueData h𝒰).form (𝒰.U i : Set X) := fun i x _ => by
    have h1 := RS.isDbarOn_dbar u x trivial
    rwa [hu] at h1
  have hCMu : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑u) (Set.univ : Set X) := u.contMDiff.contMDiffOn
  have hholo : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (s.g i - ⇑u) (𝒰.U i : Set X) := fun i =>
    RS.contMDiffOn_omega_sub_of_isDbarOn (𝒰.U i).isOpen (s.smoothOn i)
      (hCMu.mono (Set.subset_univ _)) ((s.glueData h𝒰).isDbarOn_form i) (hIsDbarOn_u i)
  have hmero : ∀ i, MeromorphicOnX (s.g i - ⇑u) (𝒰.U i : Set X) := fun i =>
    RS.meromorphicOnX_of_contMDiffOn_omega (𝒰.U i).isOpen (hholo i)
  set b : C0 (0 : RS.Divisor X) 𝒰 := fun i =>
    (⟨RS.MeroGermOn.mk (s.g i - ⇑u) (hmero i), RS.mk_mem_linSysOn_zero (𝒰.U i).isOpen (hholo i)⟩ :
      RS.LinSysOn (0 : RS.Divisor X) (𝒰.U i : Set X)) with hb_def
  have hd0b : d0 (0 : RS.Divisor X) 𝒰 b = (F : C1 (0 : RS.Divisor X) 𝒰) := by
    funext p
    obtain ⟨i, j⟩ := p
    apply Subtype.ext
    rw [d0_apply]
    -- the subset proofs are named `have`s at the `Set`-level type: an `Opens`-`≤` proof makes
    -- the application ill-typed at `implicit` transparency, which blocks every later rewrite
    have hj : (↑(𝒰.U i ⊓ 𝒰.U j) : Set X) ⊆ ↑(𝒰.U j) := fun _ hx => hx.2
    have hi : (↑(𝒰.U i ⊓ 𝒰.U j) : Set X) ⊆ ↑(𝒰.U i) := fun _ hx => hx.1
    change (RS.MeroGermOn.restrict hj
          (b j : RS.MeroGermOn X (𝒰.U j : Set X)) -
        RS.MeroGermOn.restrict hi
          (b i : RS.MeroGermOn X (𝒰.U i : Set X)) :
        RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X)) =
      ((F : C1 (0 : RS.Divisor X) 𝒰) (i, j) : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X))
    change (RS.MeroGermOn.restrict hj
          (RS.MeroGermOn.mk (s.g j - ⇑u) (hmero j)) -
        RS.MeroGermOn.restrict hi
          (RS.MeroGermOn.mk (s.g i - ⇑u) (hmero i)) :
        RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X)) =
      ((F : C1 (0 : RS.Divisor X) 𝒰) (i, j) : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X))
    rw [← RS.MeroGermOn.mk_holoRepr (𝒰.U i ⊓ 𝒰.U j).isOpen
      ((F : C1 (0 : RS.Divisor X) 𝒰) (i, j) : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X))]
    rw [RS.MeroGermOn.restrict_mk, RS.MeroGermOn.restrict_mk]
    refine RS.MeroGermOn.mk_sub.trans ?_
    apply RS.MeroGermOn.mk_eq_mk.2
    refine Filter.mem_of_superset (Filter.self_mem_codiscreteWithin _) ?_
    intro y hy
    change (s.g j y - u y) - (s.g i y - u y) =
      RS.Dolb.Z1.repr F (i, j) y
    rw [s.split i j y hy]
    ring
  have hFB1 : (F : C1 (0 : RS.Divisor X) 𝒰) ∈ B1 (0 : RS.Divisor X) 𝒰 := ⟨b, hd0b⟩
  have hFmk0 : H1Cover.mk (0 : RS.Divisor X) 𝒰 F = 0 :=
    (H1Cover.mk_eq_zero_iff (0 : RS.Divisor X) 𝒰 F).2 hFB1
  rw [← hf, hFmk0, map_zero]

/-! ### Surjectivity -/

theorem cechToH01_surjective [T2Space X] [CompactSpace X] :
    Function.Surjective (cechToH01 (X := X)) := by
  intro η'
  obtain ⟨η, rfl⟩ := H01.mk_surjective η'
  obtain ⟨𝒰, h𝒰⟩ := exists_goodCover (X := X)
  have hsol : ∀ i : Fin 𝒰.n, ∃ u : X → ℂ, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u (𝒰.U i : Set X) ∧
      IsDbarOn u η (𝒰.U i : Set X) := by
    intro i
    obtain ⟨x0, r, hr, hx0, hVs, hVim⟩ := h𝒰 i
    exact RS.exists_dbar_solution_chart_ball hr hVs hVim η
  choose h hCM hDbar using hsol
  have hholoDiff : ∀ i j, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (h j - h i) (𝒰.U i ⊓ 𝒰.U j : Set X) := by
    intro i j
    exact RS.contMDiffOn_omega_sub_of_isDbarOn (𝒰.U i ⊓ 𝒰.U j).isOpen
      ((hCM j).mono inf_le_right) ((hCM i).mono inf_le_left)
      (fun x hx => hDbar j x hx.2) (fun x hx => hDbar i x hx.1)
  have hmero : ∀ i j, MeromorphicOnX (h j - h i) (𝒰.U i ⊓ 𝒰.U j : Set X) := fun i j =>
    RS.meromorphicOnX_of_contMDiffOn_omega (𝒰.U i ⊓ 𝒰.U j).isOpen (hholoDiff i j)
  set F : C1 (0 : RS.Divisor X) 𝒰 := fun p =>
    (⟨RS.MeroGermOn.mk (h p.2 - h p.1) (hmero p.1 p.2),
      RS.mk_mem_linSysOn_zero (𝒰.U p.1 ⊓ 𝒰.U p.2).isOpen (hholoDiff p.1 p.2)⟩ :
      RS.LinSysOn (0 : RS.Divisor X) (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X)) with hF_def
  have hFZ1 : F ∈ Z1 (0 : RS.Divisor X) 𝒰 := by
    rw [mem_Z1_iff]
    rintro ⟨i, j, k⟩
    apply Subtype.ext
    rw [d1_apply]
    have hjk : (↑(𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k) : Set X) ⊆ ↑(𝒰.U j ⊓ 𝒰.U k) :=
      fun _ hx => ⟨hx.1.2, hx.2⟩
    have hik : (↑(𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k) : Set X) ⊆ ↑(𝒰.U i ⊓ 𝒰.U k) :=
      fun _ hx => ⟨hx.1.1, hx.2⟩
    have hij : (↑(𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k) : Set X) ⊆ ↑(𝒰.U i ⊓ 𝒰.U j) := fun _ hx => hx.1
    change (RS.MeroGermOn.restrict hjk
          (F (j, k) : RS.MeroGermOn X (𝒰.U j ⊓ 𝒰.U k : Set X)) -
        RS.MeroGermOn.restrict hik
          (F (i, k) : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U k : Set X)) +
        RS.MeroGermOn.restrict hij
          (F (i, j) : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X)) :
        RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k : Set X)) = 0
    change (RS.MeroGermOn.restrict hjk
          (RS.MeroGermOn.mk (h k - h j) (hmero j k)) -
        RS.MeroGermOn.restrict hik
          (RS.MeroGermOn.mk (h k - h i) (hmero i k)) +
        RS.MeroGermOn.restrict hij
          (RS.MeroGermOn.mk (h j - h i) (hmero i j)) :
        RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k : Set X)) = 0
    rw [RS.MeroGermOn.restrict_mk, RS.MeroGermOn.restrict_mk, RS.MeroGermOn.restrict_mk,
      ← RS.MeroGermOn.mk_zero (U := (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k : Set X))]
    refine (congrArg (· + _) RS.MeroGermOn.mk_sub).trans ?_
    refine RS.MeroGermOn.mk_add.trans ?_
    apply RS.MeroGermOn.mk_eq_mk.2
    refine Filter.mem_of_superset (Filter.self_mem_codiscreteWithin _) ?_
    intro y _
    change (h k y - h j y) - (h k y - h i y) + (h j y - h i y) = 0
    ring
  set FZ1 : Z1 (0 : RS.Divisor X) 𝒰 := ⟨F, hFZ1⟩ with hFZ1_def
  have hsplit : ∀ i j, ∀ x ∈ (𝒰.U i ⊓ 𝒰.U j : Opens X),
      RS.Dolb.Z1.repr FZ1 (i, j) x = h j x - h i x := by
    intro i j x hx
    change ((FZ1 : C1 (0 : RS.Divisor X) 𝒰) (i, j) :
        RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X)).evalAt x = h j x - h i x
    change (RS.MeroGermOn.mk (h j - h i) (hmero i j) :
        RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X)).evalAt x = h j x - h i x
    have hCMAt : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (h j - h i) x :=
      (hholoDiff i j).contMDiffAt ((𝒰.U i ⊓ 𝒰.U j).isOpen.mem_nhds hx)
    exact RS.MeroGermOn.evalAt_mk_of_contMDiffAt (𝒰.U i ⊓ 𝒰.U j).isOpen hx hCMAt
  set s : RS.Dolb.SmoothSplitting 𝒰 FZ1 := ⟨h, hCM, hsplit⟩ with hs_def
  have hIsDbarZero : ∀ i, IsDbarOn (h i) η (𝒰.U i : Set X) := hDbar
  have hformEq : (s.glueData h𝒰).form = η :=
    (RS.DbarGlueData.form_unique (s.glueData h𝒰) hIsDbarZero).symm
  refine ⟨toH1 (0 : RS.Divisor X) 𝒰 (H1Cover.mk (0 : RS.Divisor X) 𝒰 FZ1), ?_⟩
  rw [cechToH01_toH1 h𝒰, toDolb_mk, ← hformEq, ← sub_eq_zero, ← map_sub]
  exact H01.mk_eq_zero_iff.2 (LinearMap.mem_range.mp
    (RS.Dolb.sub_mem_range_dbar_of_splittings h𝒰 (RS.Dolb.exists_smoothSplitting 𝒰 FZ1).some s))

/-! ### Assembly -/

/-- **DOLBEAULT** (Forster 15.14(a), PDE-free): `H¹(X, 𝒪) ≃ H^{0,1}_dbar(X)`. -/
noncomputable def dolbeaultEquiv [T2Space X] [CompactSpace X] :
    H1 (0 : RS.Divisor X) ≃ₗ[ℂ] H01 X :=
  LinearEquiv.ofBijective cechToH01 ⟨cechToH01_injective, cechToH01_surjective⟩

-- `(X := X)` pins the equiv's implicit type argument before the `CoeFun` search starts; left to
-- unification it searches with `H01 ?X` still a metavariable and exhausts the instance budget.
@[simp] theorem dolbeaultEquiv_apply [T2Space X] [CompactSpace X] (ξ : H1 (0 : RS.Divisor X)) :
    dolbeaultEquiv (X := X) ξ = cechToH01 ξ := rfl

/-- The blueprint's stated purpose: Čech finiteness transfers to `H^{0,1}`. Gated on
`[FiniteDimensional ℂ (H1 (0 : Divisor X))]` — the unconditional discharge of this hypothesis
lives in `Jacobian/Finiteness/H1Finite.lean`, not yet built at the time of this unit. -/
theorem finiteDimensional_H01 [T2Space X] [CompactSpace X]
    [FiniteDimensional ℂ (H1 (0 : RS.Divisor X))] : FiniteDimensional ℂ (H01 X) :=
  Module.Finite.equiv dolbeaultEquiv

/-- Global dbar-solvability criterion (free corollary): solvable iff the Čech class of the Leray
cocycle of local solutions vanishes. -/
theorem exists_dbar_eq_iff [T2Space X] [CompactSpace X] {η : Form01 X}
    {ξ : H1 (0 : RS.Divisor X)} (hξ : cechToH01 ξ = H01.mk η) :
    (∃ u : SmoothC X, RS.dbar u = η) ↔ ξ = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    apply cechToH01_injective
    rw [hξ, map_zero]
    exact H01.mk_eq_zero_iff.2 ⟨u, hu⟩
  · rintro rfl
    rw [map_zero] at hξ
    exact H01.mk_eq_zero_iff.1 hξ.symm

end RS
