/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Cech.Covers
import LeanPool.JacobianDiffgeo.Meromorphic

/-!
# Čech cochains, coboundary maps, `Z¹`/`B¹`/`H¹(𝒰,D)` (CC8, D5/D6)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.2).

* `LinSysOn.restrictL`: restriction of relative linear systems as a `ℂ`-linear map (wrapper on
  mero's `restrict` AlgHom), with the presheaf laws `restrictL_restrictL`/`restrictL_id` and
  `ord`-rigidity `ord_restrictL`.
* `MeroGermOn.congrSet` [Compat, D6]: transport along a propositional set equality.
* `C0`/`C1`/`C2` (full-product cochains, D5), `d0`/`d1` (coboundary), `d1_comp_d0`.
* `Z1`/`B1`/`H1Cover` — the cover-level Čech `H¹(𝒰,D)`.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `LinSysOn.restrictL` -/

/-- Restriction as a `ℂ`-linear map of relative linear systems (wrapper on mero's `restrict`). -/
noncomputable def LinSysOn.restrictL {V U : Opens X} (D : RS.Divisor X) (h : V ≤ U) :
    RS.LinSysOn D (U : Set X) →ₗ[ℂ] RS.LinSysOn D (V : Set X) :=
  LinearMap.restrict (RS.MeroGermOn.restrict h).toLinearMap
    (fun _φ hφ => RS.restrict_mem_linSysOn h V.2 U.2 hφ)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem restrictL_apply_coe {V U : Opens X} (D : RS.Divisor X) (h : V ≤ U)
    (φ : RS.LinSysOn D (U : Set X)) :
    (LinSysOn.restrictL D h φ : RS.MeroGermOn X (V : Set X)) =
      RS.MeroGermOn.restrict h (φ : RS.MeroGermOn X (U : Set X)) := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem restrictL_restrictL {W V U : Opens X} (D : RS.Divisor X) (h1 : V ≤ U) (h2 : W ≤ V)
    (h3 : W ≤ U) (φ : RS.LinSysOn D (U : Set X)) :
    LinSysOn.restrictL D h2 (LinSysOn.restrictL D h1 φ) = LinSysOn.restrictL D h3 φ := by
  apply Subtype.ext
  rw [restrictL_apply_coe, restrictL_apply_coe, restrictL_apply_coe]
  exact RS.MeroGermOn.restrict_restrict h1 h2 _

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem restrictL_id {U : Opens X} (D : RS.Divisor X) (φ : RS.LinSysOn D (U : Set X)) :
    LinSysOn.restrictL D (le_refl U) φ = φ := by
  apply Subtype.ext
  rw [restrictL_apply_coe, RS.MeroGermOn.restrict_id]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem ord_restrictL {V U : Opens X} (D : RS.Divisor X) (h : V ≤ U) {x : X} (hx : x ∈ V)
    (φ : RS.LinSysOn D (U : Set X)) :
    (LinSysOn.restrictL D h φ : RS.MeroGermOn X (V : Set X)).ord x =
      (φ : RS.MeroGermOn X (U : Set X)).ord x := by
  rw [restrictL_apply_coe]
  exact RS.MeroGermOn.ord_restrict h V.2 U.2 hx _

/-! ### `MeroGermOn.congrSet` (Compat, D6) -/

namespace MeroGermOn

/-- Transport along a propositional set equality (D6): built from `restrict` both ways using the
presheaf laws. Used to move gluing targets `⋃ i, ↑(U i)` against `↑Ω`. -/
noncomputable def congrSet {U V : Set X} (h : U = V) :
    RS.MeroGermOn X U ≃ₗ[ℂ] RS.MeroGermOn X V :=
  LinearEquiv.ofLinear (RS.MeroGermOn.restrict h.ge).toLinearMap
    (RS.MeroGermOn.restrict h.le).toLinearMap
    (LinearMap.ext fun φ => by
      change RS.MeroGermOn.restrict h.ge (RS.MeroGermOn.restrict h.le φ) = φ
      rw [RS.MeroGermOn.restrict_restrict, RS.MeroGermOn.restrict_id])
    (LinearMap.ext fun φ => by
      change RS.MeroGermOn.restrict h.le (RS.MeroGermOn.restrict h.ge φ) = φ
      rw [RS.MeroGermOn.restrict_restrict, RS.MeroGermOn.restrict_id])

end MeroGermOn

/-! ### Cochains `C0`/`C1`/`C2` (D5: full-product convention) -/

variable (D : RS.Divisor X) {Ω : Opens X} (𝒰 : FinCover Ω)

/-- `0`-cochains. Reducible (`abbrev`): lets instance search and `ext`/`funext` see straight
through to the underlying Pi type, which is what actually carries the `AddCommGroup`/`Module`
structure — avoids diamond/opacity friction in `d0_apply`/`d1_apply`/`Z1`/`H1Cover`. -/
abbrev C0 : Type _ := ∀ i : Fin 𝒰.n, RS.LinSysOn D (𝒰.U i : Set X)

/-- `1`-cochains (full product over ordered pairs, D5 — no `i < j` convention). -/
abbrev C1 : Type _ := ∀ p : Fin 𝒰.n × Fin 𝒰.n, RS.LinSysOn D ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)

/-- `2`-cochains (kept internal; only used to define `Z1` via `ker d1`). -/
abbrev C2 : Type _ := ∀ t : Fin 𝒰.n × Fin 𝒰.n × Fin 𝒰.n,
    RS.LinSysOn D ((𝒰.U t.1 ⊓ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2 : Opens X) : Set X)

/-! ### The coboundary maps -/

/-- `(δ⁰f)_{ij} = f_j − f_i` (after restriction to `U i ⊓ U j`). -/
noncomputable def d0 : C0 D 𝒰 →ₗ[ℂ] C1 D 𝒰 :=
  LinearMap.pi fun p : Fin 𝒰.n × Fin 𝒰.n =>
    (LinSysOn.restrictL D (inf_le_right : 𝒰.U p.1 ⊓ 𝒰.U p.2 ≤ 𝒰.U p.2)).comp
        (LinearMap.proj p.2)
    - (LinSysOn.restrictL D (inf_le_left : 𝒰.U p.1 ⊓ 𝒰.U p.2 ≤ 𝒰.U p.1)).comp
        (LinearMap.proj p.1)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem d0_apply (f : C0 D 𝒰) (p : Fin 𝒰.n × Fin 𝒰.n) :
    d0 D 𝒰 f p = LinSysOn.restrictL D inf_le_right (f p.2) -
      LinSysOn.restrictL D inf_le_left (f p.1) := rfl

/-- `(δ¹f)_{ijk} = f_{jk} − f_{ik} + f_{ij}` (after restriction to `U i ⊓ U j ⊓ U k`). -/
noncomputable def d1 : C1 D 𝒰 →ₗ[ℂ] C2 D 𝒰 :=
  LinearMap.pi fun t : Fin 𝒰.n × Fin 𝒰.n × Fin 𝒰.n =>
    (LinSysOn.restrictL D
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          𝒰.U t.1 ⊓ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2 ≤ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2)).comp
        (LinearMap.proj (t.2.1, t.2.2))
    - (LinSysOn.restrictL D
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          𝒰.U t.1 ⊓ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2 ≤ 𝒰.U t.1 ⊓ 𝒰.U t.2.2)).comp
        (LinearMap.proj (t.1, t.2.2))
    + (LinSysOn.restrictL D
        (inf_le_left : 𝒰.U t.1 ⊓ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2 ≤ 𝒰.U t.1 ⊓ 𝒰.U t.2.1)).comp
        (LinearMap.proj (t.1, t.2.1))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem d1_apply (f : C1 D 𝒰) (t : Fin 𝒰.n × Fin 𝒰.n × Fin 𝒰.n) :
    d1 D 𝒰 f t =
      LinSysOn.restrictL D (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
          (f (t.2.1, t.2.2))
      - LinSysOn.restrictL D (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
          (f (t.1, t.2.2))
      + LinSysOn.restrictL D inf_le_left (f (t.1, t.2.1)) := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem d1_comp_d0 : (d1 D 𝒰) ∘ₗ (d0 D 𝒰) = 0 := by
  apply LinearMap.ext
  intro f
  funext t
  obtain ⟨i, j, k⟩ := t
  simp only [LinearMap.comp_apply, d1_apply, d0_apply, LinearMap.zero_apply]
  have e1 : LinSysOn.restrictL D (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U j ⊓ 𝒰.U k)
      (LinSysOn.restrictL D (inf_le_right : 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U k) (f k)) =
      LinSysOn.restrictL D
        (le_trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_right :
          𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U k) (f k) :=
    restrictL_restrictL D inf_le_right _ _ (f k)
  have e2 : LinSysOn.restrictL D (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U j ⊓ 𝒰.U k)
      (LinSysOn.restrictL D (inf_le_left : 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U j) (f j)) =
      LinSysOn.restrictL D
        (le_trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left :
          𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U j) (f j) :=
    restrictL_restrictL D inf_le_left _ _ (f j)
  have e3 : LinSysOn.restrictL D (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U i ⊓ 𝒰.U k)
      (LinSysOn.restrictL D (inf_le_right : 𝒰.U i ⊓ 𝒰.U k ≤ 𝒰.U k) (f k)) =
      LinSysOn.restrictL D
        (le_trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right) inf_le_right :
          𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U k) (f k) :=
    restrictL_restrictL D inf_le_right _ _ (f k)
  have e4 : LinSysOn.restrictL D (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U i ⊓ 𝒰.U k)
      (LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒰.U k ≤ 𝒰.U i) (f i)) =
      LinSysOn.restrictL D
        (le_trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right) inf_le_left :
          𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U i) (f i) :=
    restrictL_restrictL D inf_le_left _ _ (f i)
  have e5 : LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U i ⊓ 𝒰.U j)
      (LinSysOn.restrictL D (inf_le_right : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U j) (f j)) =
      LinSysOn.restrictL D
        (le_trans inf_le_left inf_le_right : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U j) (f j) :=
    restrictL_restrictL D inf_le_right _ _ (f j)
  have e6 : LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U i ⊓ 𝒰.U j)
      (LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U i) (f i)) =
      LinSysOn.restrictL D
        (le_trans inf_le_left inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U i) (f i) :=
    restrictL_restrictL D inf_le_left _ _ (f i)
  simp only [map_sub]
  rw [e1, e2, e3, e4, e5, e6]
  have p1 : (le_trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_right :
        𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U k) =
      (le_trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right) inf_le_right :
        𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U k) := rfl
  have p2 : (le_trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left :
        𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U j) =
      (le_trans inf_le_left inf_le_right : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U j) := rfl
  have p3 : (le_trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right) inf_le_left :
        𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U i) =
      (le_trans inf_le_left inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U i) := rfl
  rw [p1, p2, p3, Pi.zero_apply]
  abel

/-! ### `Z1`, `B1`, `H1Cover` -/

/-- `1`-cocycles. -/
noncomputable def Z1 : Submodule ℂ (C1 D 𝒰) := LinearMap.ker (d1 D 𝒰)

/-- `1`-coboundaries. -/
noncomputable def B1 : Submodule ℂ (C1 D 𝒰) := LinearMap.range (d0 D 𝒰)

/-- Registered explicitly (rather than left to ad-hoc re-derivation at `H1Cover`'s `⧸`): the
newer toolchain's `synthInstance` no longer reliably re-discharges the *dependent* Pi-instance
goal `∀ i, AddCommGroup ↥(RS.LinSysOn D _)` that `Submodule.addCommGroup`/`Submodule.instModule`
would otherwise have to solve afresh (as a precondition on the ambient `C1 D 𝒰`) at every
downstream use of `Z1 D 𝒰 ⧸ _`. Supplying the resolved instance for `↥(Z1 D 𝒰)` once, directly,
lets every later lookup match it verbatim instead of re-deriving it. -/
noncomputable instance instAddCommGroupZ1 : AddCommGroup (Z1 D 𝒰) := (Z1 D 𝒰).addCommGroup

noncomputable instance instModuleZ1 : Module ℂ (Z1 D 𝒰) := (Z1 D 𝒰).module

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem B1_le_Z1 : B1 D 𝒰 ≤ Z1 D 𝒰 := by
  rintro y ⟨x, rfl⟩
  change d1 D 𝒰 (d0 D 𝒰 x) = 0
  exact LinearMap.congr_fun (d1_comp_d0 D 𝒰) x

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mem_Z1_iff (f : C1 D 𝒰) : f ∈ Z1 D 𝒰 ↔ ∀ t, d1 D 𝒰 f t = 0 := by
  rw [Z1, LinearMap.mem_ker]
  exact ⟨fun h t => congrFun h t, fun h => funext h⟩

/-- The Čech `H¹(𝒰,D)` at cover level. Reducible (`abbrev`) for the same reason as `C0/C1/C2`. -/
noncomputable abbrev H1Cover : Type _ := Z1 D 𝒰 ⧸ (B1 D 𝒰).comap (Z1 D 𝒰).subtype

/-- The quotient map onto `H¹(𝒰,D)`. -/
noncomputable def H1Cover.mk : Z1 D 𝒰 →ₗ[ℂ] H1Cover D 𝒰 := Submodule.mkQ _

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem H1Cover.mk_surjective : Function.Surjective (H1Cover.mk D 𝒰) := Submodule.mkQ_surjective _

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem H1Cover.mk_eq_zero_iff (f : Z1 D 𝒰) :
    H1Cover.mk D 𝒰 f = 0 ↔ (f : C1 D 𝒰) ∈ B1 D 𝒰 := by
  rw [H1Cover.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem subsingleton_h1Cover_iff : Subsingleton (H1Cover D 𝒰) ↔ Z1 D 𝒰 ≤ B1 D 𝒰 := by
  rw [H1Cover, Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]

/-! ### Diagonal vanishing (used by the skyscraper fragment §6.9(g)) -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem Z1.ord_diag {f : C1 D 𝒰} (hf : f ∈ Z1 D 𝒰) (i : Fin 𝒰.n) {x : X}
    (hx : x ∈ (𝒰.U i ⊓ 𝒰.U i : Opens X)) :
    (f (i, i) : RS.MeroGermOn X ((𝒰.U i ⊓ 𝒰.U i : Opens X) : Set X)).ord x = ⊤ := by
  have hzero : d1 D 𝒰 f (i, i, i) = 0 := (mem_Z1_iff D 𝒰 f).1 hf (i, i, i)
  rw [d1_apply] at hzero
  have hcollapse : LinSysOn.restrictL D
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          𝒰.U i ⊓ 𝒰.U i ⊓ 𝒰.U i ≤ 𝒰.U i ⊓ 𝒰.U i) (f (i, i))
      - LinSysOn.restrictL D
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          𝒰.U i ⊓ 𝒰.U i ⊓ 𝒰.U i ≤ 𝒰.U i ⊓ 𝒰.U i) (f (i, i))
      + LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒰.U i ⊓ 𝒰.U i ≤ 𝒰.U i ⊓ 𝒰.U i) (f (i, i))
      = LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒰.U i ⊓ 𝒰.U i ≤ 𝒰.U i ⊓ 𝒰.U i) (f (i, i)) := by
    abel
  rw [hcollapse] at hzero
  have hxx : x ∈ (𝒰.U i ⊓ 𝒰.U i ⊓ 𝒰.U i : Opens X) := ⟨hx, hx.2⟩
  have := ord_restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒰.U i ⊓ 𝒰.U i ≤ 𝒰.U i ⊓ 𝒰.U i) hxx (f (i, i))
  rw [hzero] at this
  rw [← this]
  simp only [ZeroMemClass.coe_zero, RS.MeroGermOn.ord_zero]
  exact if_pos ⟨(𝒰.U i ⊓ 𝒰.U i ⊓ 𝒰.U i : Opens X).2, hxx⟩

end RS.Cech
