/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Cech.Window
import LeanPool.JacobianDiffgeo.Cech.Injectivity

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
      (f p : RS.MeroGermOn X _) := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem C1.retype_mem_Z1 {g : C0 D' 𝒰} (hg : (d0 D' 𝒰 g).MemLD D) :
    C1.retype (d0 D' 𝒰 g) hg ∈ Z1 D 𝒰 := by
  rw [mem_Z1_iff]
  intro t
  apply Subtype.ext
  have hcoe : (d1 D 𝒰 (C1.retype (d0 D' 𝒰 g) hg) t :
        RS.MeroGermOn X ((𝒰.U t.1 ⊓ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2 : Opens X) : Set X)) =
      (d1 D' 𝒰 (d0 D' 𝒰 g) t :
        RS.MeroGermOn X ((𝒰.U t.1 ⊓ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2 : Opens X) : Set X)) := rfl
  rw [hcoe, (mem_Z1_iff D' 𝒰 (d0 D' 𝒰 g)).1 (B1_le_Z1 D' 𝒰 ⟨g, rfl⟩) t]
  simp

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
    apply Subtype.ext
    change (C1.retype (d0 D' 𝒰 (g + g')) hgg' p :
        RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) =
      (C1.retype (d0 D' 𝒰 g) hg p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) +
        (C1.retype (d0 D' 𝒰 g') hg' p :
          RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X))
    change RS.MeroGermOn.restrict inf_le_right
          ((g p.2 : RS.MeroGermOn X (𝒰.U p.2 : Set X)) + (g' p.2 : RS.MeroGermOn X (𝒰.U p.2 : Set
              X))) -
        RS.MeroGermOn.restrict inf_le_left
          ((g p.1 : RS.MeroGermOn X (𝒰.U p.1 : Set X)) + (g' p.1 : RS.MeroGermOn X (𝒰.U p.1 : Set
              X))) =
      (RS.MeroGermOn.restrict inf_le_right (g p.2 : RS.MeroGermOn X (𝒰.U p.2 : Set X)) -
          RS.MeroGermOn.restrict inf_le_left (g p.1 : RS.MeroGermOn X (𝒰.U p.1 : Set X))) +
        (RS.MeroGermOn.restrict inf_le_right (g' p.2 : RS.MeroGermOn X (𝒰.U p.2 : Set X)) -
          RS.MeroGermOn.restrict inf_le_left (g' p.1 : RS.MeroGermOn X (𝒰.U p.1 : Set X)))
    simp only [map_add]
    abel
  simp only [mlClass]
  rw [← map_add, ← map_add]
  exact congrArg (toH1 D 𝒰) (congrArg (H1Cover.mk D 𝒰) (Subtype.ext hval))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mlClass_smul (a : ℂ) (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D)
    (hag : (d0 D' 𝒰 (a • g)).MemLD D) :
    mlClass 𝒰 (a • g) hag = a • mlClass 𝒰 g hg := by
  have hval : C1.retype (d0 D' 𝒰 (a • g)) hag = a • (C1.retype (d0 D' 𝒰 g) hg : C1 D 𝒰) := by
    funext p
    apply Subtype.ext
    change (C1.retype (d0 D' 𝒰 (a • g)) hag p :
        RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) =
      a • (C1.retype (d0 D' 𝒰 g) hg p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X))
    change RS.MeroGermOn.restrict inf_le_right (a • (g p.2 : RS.MeroGermOn X (𝒰.U p.2 : Set X))) -
        RS.MeroGermOn.restrict inf_le_left (a • (g p.1 : RS.MeroGermOn X (𝒰.U p.1 : Set X))) =
      a • (RS.MeroGermOn.restrict inf_le_right (g p.2 : RS.MeroGermOn X (𝒰.U p.2 : Set X)) -
        RS.MeroGermOn.restrict inf_le_left (g p.1 : RS.MeroGermOn X (𝒰.U p.1 : Set X)))
    simp only [map_smul, smul_sub]
  rw [mlClass, mlClass, ← map_smul]
  exact congrArg (toH1 D 𝒰) (congrArg (H1Cover.mk D 𝒰) (Subtype.ext hval))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem H1Incl_mlClass (h : D ≤ D') (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D) :
    H1Incl D h (mlClass 𝒰 g hg) = 0 := by
  rw [mlClass, H1Incl_toH1, h1CoverIncl_mk D h]
  have hz : H1Cover.mk D' 𝒰 (LinearMap.restrict (inclC1 D 𝒰 h) (fun _ hf => inclC1_mem_Z1 D h hf)
      ⟨C1.retype (d0 D' 𝒰 g) hg, C1.retype_mem_Z1 hg⟩) = 0 := by
    rw [H1Cover.mk_eq_zero_iff]
    refine ⟨g, ?_⟩
    rw [LinearMap.coe_restrict_apply]
    funext p
    apply Subtype.ext
    change (Submodule.inclusion (RS.Cech.linSysOn_mono h)
        (C1.retype (d0 D' 𝒰 g) hg p) : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) =
      (d0 D' 𝒰 g p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X))
    rfl
  rw [hz, map_zero]

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
  set h : C0 D 𝒰 := fun i => ⟨(g i : RS.MeroGermOn X (𝒰.U i : Set X)) -
      RS.MeroGermOn.restrict (𝒰.le_base i) (φ : RS.MeroGermOn X (Set.univ : Set X)),
      fun hU x hx => hφ i x hx⟩ with hh_def
  have hkey : C1.retype (d0 D' 𝒰 g) hg = d0 D 𝒰 h := by
    funext p
    apply Subtype.ext
    obtain ⟨i, j⟩ := p
    change RS.MeroGermOn.restrict inf_le_right (g j : RS.MeroGermOn X _) -
        RS.MeroGermOn.restrict inf_le_left (g i : RS.MeroGermOn X _) =
      RS.MeroGermOn.restrict inf_le_right
          ((g j : RS.MeroGermOn X _) -
            RS.MeroGermOn.restrict (𝒰.le_base j) (φ : RS.MeroGermOn X (Set.univ : Set X))) -
        RS.MeroGermOn.restrict inf_le_left
          ((g i : RS.MeroGermOn X _) -
            RS.MeroGermOn.restrict (𝒰.le_base i) (φ : RS.MeroGermOn X (Set.univ : Set X)))
    simp only [map_sub]
    -- proofs supplied explicitly: `rw`/`simp` will not instantiate a metavariable sitting in a
    -- proof-valued argument of `MeroGermOn.restrict`
    rw [RS.MeroGermOn.restrict_restrict (𝒰.le_base j) inf_le_right
        (φ : RS.MeroGermOn X (Set.univ : Set X)),
      RS.MeroGermOn.restrict_restrict (𝒰.le_base i) inf_le_left
        (φ : RS.MeroGermOn X (Set.univ : Set X))]
    have hcancel : RS.MeroGermOn.restrict (inf_le_right.trans (𝒰.le_base j))
        (φ : RS.MeroGermOn X (Set.univ : Set X)) =
        RS.MeroGermOn.restrict (inf_le_left.trans (𝒰.le_base i))
          (φ : RS.MeroGermOn X (Set.univ : Set X)) := rfl
    rw [hcancel]
    abel
  rw [mlClass]
  have hz : H1Cover.mk D 𝒰 (⟨C1.retype (d0 D' 𝒰 g) hg, C1.retype_mem_Z1 hg⟩ : Z1 D 𝒰) = 0 := by
    rw [H1Cover.mk_eq_zero_iff]
    exact ⟨h, hkey.symm⟩
  rw [hz, map_zero]

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
  rw [mlClass] at hz
  have hz' : H1Cover.mk D 𝒰 (⟨C1.retype (d0 D' 𝒰 g) hg, C1.retype_mem_Z1 hg⟩ : Z1 D 𝒰) = 0 :=
    toH1_injective D 𝒰 (by rw [hz, map_zero])
  rw [H1Cover.mk_eq_zero_iff] at hz'
  obtain ⟨hc, hhc⟩ := hz'
  -- `hhc : d0 D 𝒰 hc = C1.retype (d0 D' 𝒰 g) hg` (as `C1 D 𝒰` elements).
  have hincl_retype : ∀ p : Fin 𝒰.n × Fin 𝒰.n,
      Submodule.inclusion (RS.Cech.linSysOn_mono h) (C1.retype (d0 D' 𝒰 g) hg p) =
        d0 D' 𝒰 g p := by
    intro p
    apply Subtype.ext
    rw [Submodule.coe_inclusion, C1.retype_apply_coe]
  set k : C0 D' 𝒰 :=
      fun i => (g i) - Submodule.inclusion (RS.Cech.linSysOn_mono h) (hc i) with hk_def
  have hk0 : d0 D' 𝒰 k = 0 := by
    funext p
    obtain ⟨i, j⟩ := p
    show d0 D' 𝒰 k (i, j) = (0 : C1 D' 𝒰) (i, j)
    rw [Pi.zero_apply, d0_apply]
    have step1 : LinSysOn.restrictL D' (inf_le_right : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U j) (k j) -
        LinSysOn.restrictL D' (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U i) (k i) =
        (LinSysOn.restrictL D' inf_le_right (g j) - LinSysOn.restrictL D' inf_le_left (g i)) -
        (Submodule.inclusion (RS.Cech.linSysOn_mono h) (LinSysOn.restrictL D inf_le_right (hc j)) -
          Submodule.inclusion (RS.Cech.linSysOn_mono h)
              (LinSysOn.restrictL D inf_le_left (hc i))) := by
      change LinSysOn.restrictL D' inf_le_right
            (g j - Submodule.inclusion (RS.Cech.linSysOn_mono h) (hc j)) -
          LinSysOn.restrictL D' inf_le_left
            (g i - Submodule.inclusion (RS.Cech.linSysOn_mono h) (hc i)) = _
      rw [map_sub, map_sub, inclusion_restrictL_comm D inf_le_right h (hc j),
        inclusion_restrictL_comm D inf_le_left h (hc i)]
      abel
    rw [step1]
    have step2 : Submodule.inclusion (RS.Cech.linSysOn_mono h)
        (LinSysOn.restrictL D inf_le_right (hc j)) -
        Submodule.inclusion (RS.Cech.linSysOn_mono h) (LinSysOn.restrictL D inf_le_left (hc i)) =
        Submodule.inclusion (RS.Cech.linSysOn_mono h) (d0 D 𝒰 hc (i, j)) := by
      rw [d0_apply, map_sub]
    rw [step2, congrFun hhc (i, j), hincl_retype, d0_apply, sub_self]
  obtain ⟨ψ, hψ⟩ := toC0'_surjective D' 𝒰 ⟨k, hk0⟩
  have hψ' : toC0 D' 𝒰 ψ = k := congrArg Subtype.val hψ
  have hψi : ∀ i, LinSysOn.restrictL D' (𝒰.le_base i) ψ = k i := fun i =>
    congrFun hψ' i
  have hmemφ : (ψ : RS.MeroGermOn X (Set.univ : Set X)) ∈ RS.LinSys D' := by
    have hψ2 := ψ.2
    rwa [← linSysOn_top_eq_linSys D']
  refine ⟨⟨(ψ : RS.MeroGermOn X (Set.univ : Set X)), hmemφ⟩, fun i x hx => ?_⟩
  have hrel : (k i : RS.MeroGermOn X (𝒰.U i : Set X)) =
      (g i : RS.MeroGermOn X (𝒰.U i : Set X)) -
        (Submodule.inclusion (RS.Cech.linSysOn_mono h) (hc i) : RS.MeroGermOn X (𝒰.U i : Set X)) :=
            by
    change ((g i - Submodule.inclusion (RS.Cech.linSysOn_mono h) (hc i) : RS.LinSysOn D' _) :
      RS.MeroGermOn X (𝒰.U i : Set X)) = _
    rw [Submodule.coe_sub]
  change (-(D x : ℤ) : WithTop ℤ) ≤
      ((g i : RS.MeroGermOn X (𝒰.U i : Set X)) -
        RS.MeroGermOn.restrict (𝒰.le_base i) (ψ : RS.MeroGermOn X (Set.univ : Set X))).ord x
  rw [← restrictL_apply_coe, hψi i, hrel, sub_sub_cancel, Submodule.coe_inclusion]
  exact (RS.mem_linSysOn_iff_of_isOpen (𝒰.U i).isOpen).1 (hc i).2 x hx

end RS.Cech
