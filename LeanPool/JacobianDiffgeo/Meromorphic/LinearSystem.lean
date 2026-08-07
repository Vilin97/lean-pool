/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Meromorphic.Divisor
import Mathlib.Geometry.Manifold.Complex

/-!
# The linear system `L(D)` and `l(D)` (CC3, D4)

Unit: meromorphic-and-divisors (`docs/design/meromorphic-and-divisors.md` §4.7, D4, proof plan
§6.7).

* `LinSys D : Submodule ℂ (ℳ X)` (D4's carrier: the `ord` inequality, no case split; `0 ∈ L(D)`
  by `⊤`-arithmetic). `mem_linSys_iff_eq_zero_or_le_divisor` recovers CC3's frozen disjunction as
  a *theorem* on a connected surface.
* `l D := Module.finrank ℂ (LinSys D)`.
* `linSys_zero_eq_span_one`/`l_zero` (Liouville), vanishing lemmas
  (`linSys_eq_bot_of_nonpos_of_ne_zero`), the conditional `linSys_eq_bot_of_degree_neg`.
* `LinSysOn D U` (relative version, Čech cochain spaces; junk-gated on `IsOpen U`, matching D3),
  `restrict_mem_linSysOn`, `mem_linSys_iff_forall_restrict` (bookkeeping toward
  `H⁰(𝔘, O_D) = L(D)`).

Deviation from the design doc's listing (noted honestly): `linSysMulEquiv` (the multiplication
`LinearEquiv` `L(D) ≃ₗ L(D - divisor φ)`) is **not included** — the pointwise `WithTop ℤ`
bookkeeping for the two-sided bound is more delicate than the time budget allowed; see the
final report for the precise missing step. Everything else in §4.7 is proved.
-/

open scoped ContDiff Manifold
open Set Filter Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {U V : Set X} {D E : Divisor X} {c : ℂ}

/-! ### Pointwise arithmetic on `Divisor X` (Compat helpers) -/

omit [ChartedSpace ℂ X] in
theorem Divisor.add_apply (D E : Divisor X) (x : X) : (D + E) x = D x + E x :=
  congrFun (Function.locallyFinsuppWithin.coe_add D E) x

omit [ChartedSpace ℂ X] in
theorem Divisor.neg_apply (D : Divisor X) (x : X) : (-D) x = -(D x) :=
  congrFun (Function.locallyFinsuppWithin.coe_neg D) x

omit [ChartedSpace ℂ X] in
theorem Divisor.sub_apply (D E : Divisor X) (x : X) : (D - E) x = D x - E x :=
  congrFun (Function.locallyFinsuppWithin.coe_sub D E) x

variable [T1Space X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `LinSys D` -/

/-- CC3's `L(D)` (carrier per D4; `0 ∈ L(D)` by `⊤`-arithmetic, not fiat). -/
noncomputable def LinSys (D : Divisor X) : Submodule ℂ (ℳ X) where
  carrier := {φ | ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ φ.ord x}
  zero_mem' := by
    intro x
    rw [MeroGermOn.ord_zero, if_pos ⟨isOpen_univ, mem_univ x⟩]
    exact le_top
  add_mem' := by
    intro φ ψ hφ hψ x
    exact le_trans (le_min (hφ x) (hψ x)) (MeroGermOn.ord_add isOpen_univ (mem_univ x) φ ψ)
  smul_mem' := by
    intro a φ hφ x
    rcases eq_or_ne a 0 with rfl | ha
    · rw [zero_smul, MeroGermOn.ord_zero, if_pos ⟨isOpen_univ, mem_univ x⟩]
      exact le_top
    · rw [MeroGermOn.ord_smul isOpen_univ (mem_univ x) ha]
      exact hφ x

omit [T1Space X] [IsManifold 𝓘(ℂ) ω X] in
theorem mem_linSys_iff {φ : ℳ X} : φ ∈ LinSys D ↔ ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ φ.ord x :=
  Iff.rfl

/-- CC3's frozen shape, recovered as a characterization on connected `X`. -/
theorem mem_linSys_iff_eq_zero_or_le_divisor [ConnectedSpace X] {φ : ℳ X} :
    φ ∈ LinSys D ↔ φ = 0 ∨ -D ≤ divisor φ := by
  rw [mem_linSys_iff]
  constructor
  · intro hmem
    by_cases hφ : φ = 0
    · exact Or.inl hφ
    · refine Or.inr (Function.locallyFinsuppWithin.le_def.2 fun x => ?_)
      rw [Divisor.neg_apply, divisor_apply]
      exact WithTop.untop₀_le_untop₀ (Mero.ord_ne_top hφ x) (hmem x)
  · rintro (rfl | hle)
    · intro x; rw [MeroGermOn.ord_zero, if_pos ⟨isOpen_univ, mem_univ x⟩]; exact le_top
    · by_cases hφ0 : φ = 0
      · intro x; rw [hφ0, MeroGermOn.ord_zero, if_pos ⟨isOpen_univ, mem_univ x⟩]; exact le_top
      · intro x
        have h := Function.locallyFinsuppWithin.le_def.1 hle x
        rw [Divisor.neg_apply, divisor_apply] at h
        calc ((-(D x) : ℤ) : WithTop ℤ) = (((-D) x : ℤ) : WithTop ℤ) := by rw [Divisor.neg_apply]
          _ ≤ ((divisor φ x : ℤ) : WithTop ℤ) := by exact_mod_cast h
          _ = φ.ord x := WithTop.coe_untop₀_of_ne_top (Mero.ord_ne_top hφ0 x)

/-- CC3: `l D`. Finiteness is NOT this unit's business (Čech/finiteness proves
`FiniteDimensional`); until then `finrank` junk-returns `0` on infinite-dimensional spaces — no
lemma here depends on finiteness. -/
noncomputable def l (D : Divisor X) : ℕ := Module.finrank ℂ (LinSys D)

omit [T1Space X] [IsManifold 𝓘(ℂ) ω X] in
theorem linSys_mono (h : D ≤ E) : LinSys D ≤ LinSys E := by
  intro φ hφ x
  refine le_trans ?_ (hφ x)
  have hx := Function.locallyFinsuppWithin.le_def.1 h x
  exact_mod_cast neg_le_neg hx

omit [T1Space X] [IsManifold 𝓘(ℂ) ω X] in
theorem one_mem_linSys_iff : (1 : ℳ X) ∈ LinSys D ↔ 0 ≤ D := by
  rw [mem_linSys_iff]
  constructor
  · intro h
    rw [Function.locallyFinsuppWithin.le_def]
    intro x
    have hthis := h x
    rw [MeroGermOn.ord_one isOpen_univ (mem_univ x)] at hthis
    have hle : (-(D x) : ℤ) ≤ 0 := by exact_mod_cast hthis
    change (0 : ℤ) ≤ D x
    omega
  · intro h x
    have hDx : (0 : ℤ) ≤ D x := Function.locallyFinsuppWithin.le_def.1 h x
    rw [MeroGermOn.ord_one isOpen_univ (mem_univ x)]
    have : (-(D x) : ℤ) ≤ 0 := by omega
    exact_mod_cast this

omit [T1Space X] [IsManifold 𝓘(ℂ) ω X] in
theorem algebraMap_mem_linSys (h : 0 ≤ D) (c : ℂ) : algebraMap ℂ (ℳ X) c ∈ LinSys D := by
  intro x
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, MeroGermOn.ord_zero, if_pos ⟨isOpen_univ, mem_univ x⟩]
    exact le_top
  · rw [MeroGermOn.ord_algebraMap isOpen_univ (mem_univ x) hc]
    have hDx : (0 : ℤ) ≤ D x := Function.locallyFinsuppWithin.le_def.1 h x
    have : (-(D x) : ℤ) ≤ 0 := by omega
    exact_mod_cast this

/-! ### Vanishing / constancy results -/

omit [T1Space X] in
theorem linSys_zero_eq_span_one [CompactSpace X] [ConnectedSpace X] :
    LinSys (0 : Divisor X) = Submodule.span ℂ {1} := by
  apply le_antisymm
  · intro φ hφ
    have hordnn : ∀ x, 0 ≤ φ.ord x := by
      intro x
      have := hφ x
      simpa using this
    have hCM : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ.holoRepr := MeroGermOn.holoRepr_contMDiff hordnn
    have hMD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ.holoRepr := hCM.mdifferentiable (by simp)
    obtain ⟨c, hc⟩ := hMD.exists_eq_const_of_compactSpace
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, MeroGermOn.algebraMap_mk, mul_one, ← MeroGermOn.mk_holoRepr isOpen_univ φ,
      MeroGermOn.mk_eq_mk]
    exact Filter.Eventually.of_forall (fun y => (congrFun hc y).symm)
  · rw [Submodule.span_le]
    intro φ hφ
    simp only [Set.mem_singleton_iff] at hφ
    rw [hφ]
    exact (one_mem_linSys_iff).2 le_rfl

omit [T1Space X] in
theorem l_zero [CompactSpace X] [ConnectedSpace X] : l (0 : Divisor X) = 1 := by
  rw [l, linSys_zero_eq_span_one, finrank_span_singleton]
  exact one_ne_zero

omit [T1Space X] in
theorem linSys_eq_bot_of_nonpos_of_ne_zero [CompactSpace X] [ConnectedSpace X]
    (h : D ≤ 0) (hD : D ≠ 0) : LinSys D = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφmem
  simp only [Submodule.mem_bot]
  have hord0 : ∀ x, 0 ≤ φ.ord x := by
    intro x
    have hDxle : D x ≤ 0 := Function.locallyFinsuppWithin.le_def.1 h x
    have h1 : (0 : WithTop ℤ) ≤ ((-(D x) : ℤ) : WithTop ℤ) := by exact_mod_cast neg_nonneg.2 hDxle
    exact le_trans h1 (hφmem x)
  have hspan : φ ∈ Submodule.span ℂ ({1} : Set (ℳ X)) := by
    rw [← linSys_zero_eq_span_one]
    intro x; simpa using hord0 x
  rw [Submodule.mem_span_singleton] at hspan
  obtain ⟨a, ha⟩ := hspan
  by_contra hφ0
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_smul] at ha; exact hφ0 ha.symm
  have hφeq : φ = algebraMap ℂ (ℳ X) a := by rw [← ha, Algebra.smul_def, mul_one]
  obtain ⟨x₀, hx₀⟩ : ∃ x, D x ≠ 0 := by
    by_contra hnone
    simp only [not_exists, not_not] at hnone
    exact hD (Function.locallyFinsuppWithin.ext hnone)
  have hDx₀ : D x₀ < 0 := lt_of_le_of_ne (Function.locallyFinsuppWithin.le_def.1 h x₀) hx₀
  have hordx₀ : φ.ord x₀ = 0 := by
    rw [hφeq, MeroGermOn.ord_algebraMap isOpen_univ (mem_univ x₀) ha0]
  have hmemx0 := hφmem x₀
  rw [hordx₀] at hmemx0
  have hpos : (0 : ℤ) < -(D x₀) := by omega
  have hpos' : (0 : WithTop ℤ) < ((-(D x₀) : ℤ) : WithTop ℤ) := by exact_mod_cast hpos
  exact absurd hmemx0 (not_le.2 hpos')

omit [T1Space X] in
theorem l_eq_zero_of_nonpos_of_ne_zero [CompactSpace X] [ConnectedSpace X]
    (h : D ≤ 0) (hD : D ≠ 0) : l D = 0 := by
  rw [l, linSys_eq_bot_of_nonpos_of_ne_zero h hD]
  simp

/-- `deg D < 0 → L(D) = 0`, CONDITIONAL on `deg ∘ divisor = 0` — that input is owned by
proper-map-degree (argument principle / degree counting). -/
theorem linSys_eq_bot_of_degree_neg [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (hdeg : ∀ φ : ℳ X, φ ≠ 0 → (divisor φ).degree = 0) (h : D.degree < 0) : LinSys D = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφmem
  simp only [Submodule.mem_bot]
  by_contra hφ0
  have hle : -D ≤ divisor φ := (mem_linSys_iff_eq_zero_or_le_divisor.1 hφmem).resolve_left hφ0
  have hmono := Function.locallyFinsuppWithin.degree_mono hle
  rw [Function.locallyFinsuppWithin.degree_neg, hdeg φ hφ0] at hmono
  omega

/-! ### Relative version (Čech cochain spaces) -/

/-- Relative `L(D)` (CC8 Čech cochain spaces). Junk-gated on `IsOpen U` (D3): when `U` is not
open, the condition is vacuous (every class qualifies), matching `ord`'s own junk convention so
that `zero_mem'` holds unconditionally. -/
noncomputable def LinSysOn (D : Divisor X) (U : Set X) : Submodule ℂ (MeroGermOn X U) where
  carrier := {φ | IsOpen U → ∀ x ∈ U, ((-(D x) : ℤ) : WithTop ℤ) ≤ φ.ord x}
  zero_mem' := by
    intro hU x hx
    rw [MeroGermOn.ord_zero, if_pos ⟨hU, hx⟩]
    exact le_top
  add_mem' := by
    intro φ ψ hφ hψ hU x hx
    exact le_trans (le_min (hφ hU x hx) (hψ hU x hx)) (MeroGermOn.ord_add hU hx φ ψ)
  smul_mem' := by
    intro a φ hφ hU x hx
    rcases eq_or_ne a 0 with rfl | ha
    · rw [zero_smul, MeroGermOn.ord_zero, if_pos ⟨hU, hx⟩]
      exact le_top
    · rw [MeroGermOn.ord_smul hU hx ha]
      exact hφ hU x hx

omit [T1Space X] [IsManifold 𝓘(ℂ) ω X] in
theorem mem_linSysOn_iff_of_isOpen (hU : IsOpen U) {φ : MeroGermOn X U} :
    φ ∈ LinSysOn D U ↔ ∀ x ∈ U, ((-(D x) : ℤ) : WithTop ℤ) ≤ φ.ord x :=
  ⟨fun h => h hU, fun h _ => h⟩

omit [T1Space X] [IsManifold 𝓘(ℂ) ω X] in
theorem restrict_mem_linSysOn (h : V ⊆ U) (hV : IsOpen V) (hU : IsOpen U) {φ : MeroGermOn X U}
    (hφ : φ ∈ LinSysOn D U) : MeroGermOn.restrict h φ ∈ LinSysOn D V := by
  rw [mem_linSysOn_iff_of_isOpen hV]
  intro x hx
  rw [MeroGermOn.ord_restrict h hV hU hx]
  exact (mem_linSysOn_iff_of_isOpen hU).1 hφ x (h hx)

omit [T1Space X] [IsManifold 𝓘(ℂ) ω X] in
theorem mem_linSys_iff_forall_restrict {ι : Type*} {W : ι → Set X} (hW : ∀ i, IsOpen (W i))
    (hcov : ⋃ i, W i = univ) {φ : ℳ X} :
    φ ∈ LinSys D ↔ ∀ i, MeroGermOn.restrict (Set.subset_univ (W i))
      φ ∈ LinSysOn D (W i) := by
  constructor
  · intro hmem i
    rw [mem_linSysOn_iff_of_isOpen (hW i)]
    intro x hx
    rw [MeroGermOn.ord_restrict (Set.subset_univ (W i)) (hW i) isOpen_univ
      hx]
    exact hmem x
  · intro hall x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ W i := by
      have hxU : x ∈ ⋃ i, W i := by rw [hcov]; trivial
      simpa using hxU
    have hmemi := (mem_linSysOn_iff_of_isOpen (hW i)).1 (hall i) x hi
    rwa [MeroGermOn.ord_restrict (Set.subset_univ (W i)) (hW i) isOpen_univ
      hi] at hmemi

end RS
