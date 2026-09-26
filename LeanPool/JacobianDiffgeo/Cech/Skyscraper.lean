/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import LeanPool.JacobianDiffgeo.Cech.Colimit
import LeanPool.JacobianDiffgeo.Cech.H0
import LeanPool.JacobianDiffgeo.Cech.Injectivity
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The Mittag-Leffler atom and the skyscraper fragment (CC8, D7, proof plan §6.9)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.7).

* `C1.MemLD`/`C1.retype`: a `D'`-cochain all of whose components satisfy the smaller `D`-bound,
  re-tagged as a `D`-cochain (same underlying germs).
* `mlClass`: the Mittag-Leffler atom — a `D'`-`0`-cochain with `D`-bounded coboundary yields a
  class in `H¹(D)`. Both the χ connecting map (finiteness-and-chi) and laurent-tails'
  `T[D] → H¹(D)` factor through this.
* `mlClass_eq_zero_iff`: the vanishing criterion (the "engine" — uses `H⁰ ≃ L(D')` gluing and
  `toH1`'s colimit description).

`mlClass`/`mlClass_eq_zero_iff` (both directions — the `⇒` half uses `toH1_injective`, Forster
12.4, from `Injectivity.lean`) are proved with zero sorries; both the χ ledger and laurent-tails'
`T[D] → H¹(D)` map factor through `mlClass`. The rest of the six-term fragment —
`H1Incl_surjective` (part (g)), `windowConnect`, `exists_realization`, Lemma A
(`mlClass_eq_of_realizes`), `exact_windowMap_windowConnect`, `exact_windowConnect_H1Incl` —
is proved in `SixTerm.lean`.
-/

public section

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `C1.MemLD`, `C1.retype` -/

variable {Ω : Opens X} {𝒰 : FinCover Ω} {D D' : RS.Divisor X}

/-- A `C¹(D')`-cochain all of whose components satisfy the `D`-bound. -/
def C1.MemLD (f : C1 D' 𝒰) (D : RS.Divisor X) : Prop :=
  ∀ p : Fin 𝒰.n × Fin 𝒰.n, (f p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) ∈
    RS.LinSysOn D ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)

/-- Re-tag a `D'`-cochain satisfying the `D`-bound as a `D`-cochain (same underlying germs). -/
noncomputable def C1.retype (f : C1 D' 𝒰) (hf : f.MemLD D) : C1 D 𝒰 :=
  fun p => ⟨(f p : RS.MeroGermOn X _), hf p⟩

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem C1.retype_apply_coe (f : C1 D' 𝒰) (hf : f.MemLD D) (p : Fin 𝒰.n × Fin 𝒰.n) :
    (C1.retype f hf p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) =
      (f p : RS.MeroGermOn X _) := by rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem C1.retype_mem_Z1 {g : C0 D' 𝒰} (hg : (d0 D' 𝒰 g).MemLD D) :
    C1.retype (d0 D' 𝒰 g) hg ∈ Z1 D 𝒰 := by
  apply (mem_Z1_iff D 𝒰 _).2
  intro t
  exact Subtype.ext (congrArg (fun z : RS.LinSysOn D' _ => z.val)
    ((mem_Z1_iff D' 𝒰 (d0 D' 𝒰 g)).1 (B1_le_Z1 D' 𝒰 ⟨g, rfl⟩) t))

/-! ### The Mittag-Leffler atom -/

variable {𝒰 : FinCover (⊤ : Opens X)}

/-- The Mittag-Leffler atom (D7): a `D'`-`0`-cochain with `D`-bounded coboundary yields a class
in `H¹(D)`. -/
noncomputable def mlClass (𝒰 : FinCover (⊤ : Opens X)) (g : C0 D' 𝒰)
    (hg : (d0 D' 𝒰 g).MemLD D) : H1 D :=
  toH1 D 𝒰 (H1Cover.mk D 𝒰 ⟨C1.retype (d0 D' 𝒰 g) hg, C1.retype_mem_Z1 hg⟩)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mlClass_add (g g' : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D) (hg' : (d0 D' 𝒰 g').MemLD D)
    (hgg' : (d0 D' 𝒰 (g + g')).MemLD D) :
    mlClass 𝒰 (g + g') hgg' = mlClass 𝒰 g hg + mlClass 𝒰 g' hg' := by
  have hval : C1.retype (d0 D' 𝒰 (g + g')) hgg' =
      (C1.retype (d0 D' 𝒰 g) hg : C1 D 𝒰) + C1.retype (d0 D' 𝒰 g') hg' := by
    funext p
    exact Subtype.ext (congrArg (fun c : C1 D' 𝒰 => (c p).val) ((d0 D' 𝒰).map_add g g'))
  exact (congrArg ((toH1 D 𝒰).comp (H1Cover.mk D 𝒰)) (Subtype.ext hval)).trans
    (((toH1 D 𝒰).comp (H1Cover.mk D 𝒰)).map_add _ _)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mlClass_smul (a : ℂ) (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D)
    (hag : (d0 D' 𝒰 (a • g)).MemLD D) :
    mlClass 𝒰 (a • g) hag = a • mlClass 𝒰 g hg := by
  have hval : C1.retype (d0 D' 𝒰 (a • g)) hag = a • (C1.retype (d0 D' 𝒰 g) hg : C1 D 𝒰) := by
    funext p
    exact Subtype.ext (congrArg (fun c : C1 D' 𝒰 => (c p).val) ((d0 D' 𝒰).map_smul a g))
  exact (congrArg ((toH1 D 𝒰).comp (H1Cover.mk D 𝒰)) (Subtype.ext hval)).trans
    (((toH1 D 𝒰).comp (H1Cover.mk D 𝒰)).map_smul a _)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem H1Incl_mlClass (h : D ≤ D') (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D) :
    H1Incl D h (mlClass 𝒰 g hg) = 0 := by
  have hz : H1Cover.mk D' 𝒰 (LinearMap.restrict (inclC1 D 𝒰 h) (fun _ hf => inclC1_mem_Z1 D h hf)
      ⟨C1.retype (d0 D' 𝒰 g) hg, C1.retype_mem_Z1 hg⟩) = 0 :=
    (H1Cover.mk_eq_zero_iff D' 𝒰 _).2 ⟨g, rfl⟩
  exact (H1Incl_toH1 D h 𝒰 _).trans
    ((congrArg (toH1 D' 𝒰) ((h1CoverIncl_mk D h _).trans hz)).trans (toH1 D' 𝒰).map_zero)

/-! ### `mlClass` is refinement-stable (§6.9(a), `mlClass_res`) -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Refining the cover and restricting the realizing cochain preserves its Mittag-Leffler class. -/
theorem mlClass_res {𝒰 𝒱 : FinCover (⊤ : Opens X)} (τ : Fin 𝒱.n → Fin 𝒰.n)
    (hτ : IsRefIdx 𝒰 𝒱 τ) (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D)
    (hgr : (d0 D' 𝒱 (resC0 D' τ hτ g)).MemLD D) :
    mlClass 𝒱 (resC0 D' τ hτ g) hgr = mlClass 𝒰 g hg := by
  symm
  change toH1 D 𝒰 (H1Cover.mk D 𝒰 _) = toH1 D 𝒱 (H1Cover.mk D 𝒱 _)
  rw [← toH1_resH1 D τ hτ, resH1_mk]
  apply congrArg (toH1 D 𝒱)
  apply congrArg (H1Cover.mk D 𝒱)
  apply Subtype.ext
  change C1.retype (resC1 D' τ hτ (d0 D' 𝒰 g)) _ = _
  congr 1
  exact LinearMap.congr_fun (resC1_comp_d0 D' τ hτ) g

/-! ### The vanishing criterion (§6.9(b), `⇐` half)

The `⇐` half below (a class realized by a global section vanishes) needs no injectivity and is
what laurent-tails' truncation map `α_D` actually produces classes *from*; it is proved here with
zero sorries. The `⇒` half (needing `toH1_injective`, Forster 12.4) is proved further down,
after `Injectivity.lean`'s import — see `mlClass_eq_zero_iff` below. -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mlClass_eq_zero_of_exists (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D) (φ : RS.LinSys D')
    (hφ : ∀ i : Fin 𝒰.n, ∀ x ∈ 𝒰.U i, (-(D x : ℤ) : WithTop ℤ) ≤
      ((g i : RS.MeroGermOn X (𝒰.U i : Set X)) -
        RS.MeroGermOn.restrict (𝒰.le_base i) (φ : RS.MeroGermOn X (Set.univ : Set X))).ord x) :
    mlClass 𝒰 g hg = 0 := by
  let h : C0 D 𝒰 := fun i => ⟨(g i : RS.MeroGermOn X (𝒰.U i : Set X)) -
      RS.MeroGermOn.restrict (𝒰.le_base i) (φ : RS.MeroGermOn X (Set.univ : Set X)),
      fun hU x hx => hφ i x hx⟩
  let φ' : RS.LinSysOn D' ((⊤ : Opens X) : Set X) :=
    ⟨φ, by rw [linSysOn_top_eq_linSys D']; exact φ.property⟩
  have hdiff : d0 D' 𝒰 (g - toC0 D' 𝒰 φ') = d0 D' 𝒰 g := by
    rw [map_sub, LinearMap.mem_ker.mp (toC0_mem_ker D' 𝒰 φ'), sub_zero]
  have hkey : C1.retype (d0 D' 𝒰 g) hg = d0 D 𝒰 h := by
    funext p
    exact Subtype.ext (congrArg (fun c : C1 D' 𝒰 => (c p).val) hdiff.symm)
  have hz : H1Cover.mk D 𝒰 (⟨C1.retype (d0 D' 𝒰 g) hg, C1.retype_mem_Z1 hg⟩ : Z1 D 𝒰) = 0 := by
    rw [H1Cover.mk_eq_zero_iff]
    exact ⟨h, hkey.symm⟩
  exact (congrArg (toH1 D 𝒰) hz).trans (toH1 D 𝒰).map_zero

/-! ### The vanishing criterion (§6.9(b), `⇒` half): now unlocked by `toH1_injective` (12.4). -/

/-- **§6.9(b)**: the full vanishing criterion for `mlClass` — `toH1_injective` spares us any
refinement: a coboundary witness for `retype (d0 g)` already lives on `𝒰` itself. -/
theorem mlClass_eq_zero_iff (h : D ≤ D') (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D) :
    mlClass 𝒰 g hg = 0 ↔ ∃ φ : RS.LinSys D', ∀ i : Fin 𝒰.n, ∀ x ∈ 𝒰.U i,
      (-(D x : ℤ) : WithTop ℤ) ≤ ((g i : RS.MeroGermOn X (𝒰.U i : Set X)) -
        RS.MeroGermOn.restrict (𝒰.le_base i) (φ : RS.MeroGermOn X (Set.univ : Set X))).ord x := by
  constructor
  swap
  · rintro ⟨φ, hφ⟩
    exact mlClass_eq_zero_of_exists g hg φ hφ
  intro hz
  have hz' : H1Cover.mk D 𝒰 (⟨C1.retype (d0 D' 𝒰 g) hg, C1.retype_mem_Z1 hg⟩ : Z1 D 𝒰) = 0 :=
    toH1_injective D 𝒰 (hz.trans (toH1 D 𝒰).map_zero.symm)
  rw [H1Cover.mk_eq_zero_iff] at hz'
  obtain ⟨hc, hhc⟩ := hz'
  let k : C0 D' 𝒰 :=
    fun i => (g i) - Submodule.inclusion (RS.Cech.linSysOn_mono h) (hc i)
  have hk0 : d0 D' 𝒰 k = 0 := by
    change d0 D' 𝒰 (g - inclC0 D 𝒰 h hc) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg (inclC1 D 𝒰 h) hhc).symm
  obtain ⟨ψ, hψ⟩ := toC0'_surjective D' 𝒰 ⟨k, hk0⟩
  have hψ' : toC0 D' 𝒰 ψ = k := congrArg Subtype.val hψ
  have hψi : ∀ i, LinSysOn.restrictL D' (𝒰.le_base i) ψ = k i := fun i =>
    congrFun hψ' i
  have hmemφ : (ψ : RS.MeroGermOn X (Set.univ : Set X)) ∈ RS.LinSys D' := by
    have hψ2 := ψ.2
    rwa [← linSysOn_top_eq_linSys D']
  refine ⟨⟨(ψ : RS.MeroGermOn X (Set.univ : Set X)), hmemφ⟩, fun i x hx => ?_⟩
  change (-(D x : ℤ) : WithTop ℤ) ≤
      ((g i : RS.MeroGermOn X (𝒰.U i : Set X)) -
        RS.MeroGermOn.restrict (𝒰.le_base i) (ψ : RS.MeroGermOn X (Set.univ : Set X))).ord x
  rw [← restrictL_apply_coe, hψi i]
  change (-(D x : ℤ) : WithTop ℤ) ≤
    ((g i : RS.MeroGermOn X (𝒰.U i : Set X)) -
      ((g i : RS.MeroGermOn X (𝒰.U i : Set X)) - (hc i : RS.MeroGermOn X (𝒰.U i : Set X)))).ord x
  rw [sub_sub_cancel]
  exact (RS.mem_linSysOn_iff_of_isOpen (𝒰.U i).isOpen).1 (hc i).2 x hx

end RS.Cech
