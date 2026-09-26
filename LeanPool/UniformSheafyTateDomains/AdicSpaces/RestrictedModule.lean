/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization project
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictedPowerSeries
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Order.Filter.CountablyGenerated

/-!
# Restricted Module-valued Power Series M⟨X⟩

This file defines restricted power series with coefficients in a topological module `M`
over a nonarchimedean topological ring `A`, and proves the key surjection lifting lemma.

## Main definitions

* `MvPowerSeries.IsRestrictedModule`: A power series `f ∈ MvPowerSeries (Fin 1) M` is
  **restricted** if its coefficients converge to `0` along the cofinite filter.
* `restrictedModule A M`: The submodule `M⟨X⟩` of restricted `M`-valued power series.
* `restrictedModule.map f`: The induced map `M⟨X⟩ → N⟨X⟩` from a continuous linear map.

## Main results

* `restrictedModule_map_surjective`: If `f : M →ₗ[A] N` is surjective, continuous, and
  open, then the induced map `M⟨X⟩ → N⟨X⟩` is surjective (Wedhorn's *Adic Spaces*).

## Implementation notes

`MvPowerSeries (Fin 1) M` is definitionally `(Fin 1 →₀ ℕ) → M`, with pointwise module
structure. We access coefficients via function application `f s` rather than
`MvPowerSeries.coeff`, since the latter requires a `Semiring` instance on the
coefficient type.

The surjection lifting proof uses a diagonal construction over a countable decreasing
basis of open additive subgroups, requiring `FirstCountableTopology M` and `T2Space M`.
-/

@[expose] public section

open Filter

universe u v w

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! ### Restricted module-valued power series -/

/-- An element `f` of `MvPowerSeries (Fin 1) M` (i.e., a function `(Fin 1 →₀ ℕ) → M`) is
**restricted** if its coefficients converge to `0` along the cofinite filter. This is the
module-valued analogue of `MvPowerSeries.IsRestricted`. -/
def MvPowerSeries.IsRestrictedModule {M : Type*} [Zero M] [TopologicalSpace M]
    (f : MvPowerSeries (Fin 1) M) : Prop :=
  Tendsto (fun s : Fin 1 →₀ ℕ ↦ f s) cofinite (nhds 0)

/-- The submodule `M⟨X⟩` of restricted `M`-valued power series over a nonarchimedean ring `A`.
An element of `MvPowerSeries (Fin 1) M` is restricted if its coefficients tend to `0`
along the cofinite filter on multi-indices. -/
def restrictedModule (A : Type u) [CommRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul A M] :
    Submodule A (MvPowerSeries (Fin 1) M) where
  carrier := {f | MvPowerSeries.IsRestrictedModule f}
  zero_mem' := tendsto_const_nhds
  add_mem' {f g} hf hg := by
    change Tendsto _ cofinite (nhds 0)
    have : Tendsto (fun s ↦ f s + g s) cofinite (nhds 0) := by
      rw [show (0 : M) = 0 + 0 from (add_zero 0).symm]; exact hf.add hg
    exact this.congr (fun s ↦ (Pi.add_apply f g s).symm)
  smul_mem' a f hf := by
    change Tendsto _ cofinite (nhds 0)
    have : Tendsto (fun s ↦ a • f s) cofinite (nhds 0) := by
      rw [show (0 : M) = a • (0 : M) from (smul_zero a).symm]; exact hf.const_smul a
    exact this.congr (fun s ↦ (Pi.smul_apply a f s).symm)

/-! ### Induced map on restricted modules -/

/-- The induced map `M⟨X⟩ → N⟨X⟩` from a continuous linear map `f : M → N`. Sends
`∑ mₙ Xⁿ ↦ ∑ f(mₙ) Xⁿ`. -/
def restrictedModule.map
    {M : Type v} [AddCommGroup M] [Module A M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul A M]
    {N : Type w} [AddCommGroup N] [Module A N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [ContinuousConstSMul A N]
    (f : M →ₗ[A] N) (hf_cont : Continuous f) :
    restrictedModule A M →ₗ[A] restrictedModule A N where
  toFun g := ⟨fun s ↦ f (g.1 s), by
    change Tendsto (fun s ↦ f (g.1 s)) cofinite (nhds 0)
    rw [show (0 : N) = f 0 from (map_zero f).symm]
    exact (hf_cont.tendsto 0).comp g.2⟩
  map_add' g₁ g₂ := by
    apply Subtype.ext; funext s; exact map_add f (g₁.1 s) (g₂.1 s)
  map_smul' a g := by
    apply Subtype.ext; funext s; exact map_smul f a (g.1 s)

omit [NonarchimedeanRing A] in
omit [TopologicalSpace A] in
/-- The induced map is compatible with function composition. -/
theorem restrictedModule.map_comp
    {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [ContinuousConstSMul A N]
    {P : Type*} [AddCommGroup P] [Module A P] [TopologicalSpace P]
    [IsTopologicalAddGroup P] [ContinuousConstSMul A P]
    (f : M →ₗ[A] N) (hf : Continuous f)
    (g : N →ₗ[A] P) (hg : Continuous g) :
    restrictedModule.map (g.comp f) (hg.comp hf) =
      (restrictedModule.map g hg).comp (restrictedModule.map f hf) := by
  apply LinearMap.ext; intro x
  apply Subtype.ext; funext _
  rfl

/-! ### Surjection lifting -/

section SurjectionLifting

/-- Auxiliary lemma: in a Hausdorff space with an antitone basis of open additive subgroups
`W`, if `b` lies in `f '' (W n)` for every `n`, then `b = 0`. Choose `mₙ ∈ W n` with
`f(mₙ) = b`; then `mₙ → 0`, so `b = f(mₙ) → f(0) = 0` by continuity. -/
private theorem eq_zero_of_mem_image_all
    {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    {N : Type*} [AddCommGroup N] [TopologicalSpace N] [T2Space N]
    (f : M →+ N) (hf_cont : Continuous f)
    (W : ℕ → OpenAddSubgroup M)
    (hW : (nhds (0 : M)).HasAntitoneBasis (fun n ↦ (W n : Set M)))
    (b : N) (hb : ∀ n, b ∈ f '' (W n : Set M)) : b = 0 := by
  choose m hm_mem hm_eq using hb
  have hm_tend : Tendsto m atTop (nhds (0 : M)) :=
    hW.1.tendsto_right_iff.mpr fun n _ ↦
      eventually_atTop.mpr ⟨n, fun k hk ↦ hW.2 hk (hm_mem k)⟩
  have : Tendsto (fun _ : ℕ ↦ b) atTop (nhds (0 : N)) := by
    have hfc : Tendsto (f ∘ m) atTop (nhds (f 0)) := (hf_cont.tendsto 0).comp hm_tend
    rw [map_zero] at hfc
    exact hfc.congr (fun n ↦ by simp only [Function.comp_apply]; exact hm_eq n)
  exact tendsto_const_nhds_iff.mp this

omit [NonarchimedeanRing A] in
omit [TopologicalSpace A] in
/-- **Surjection lifting for restricted modules.** If `f : M →ₗ[A] N` is surjective,
continuous, and open, then the induced map `M⟨X⟩ → N⟨X⟩` is surjective.

The proof uses a diagonal construction. Given a countable antitone basis `W₀ ⊇ W₁ ⊇ ⋯`
of open additive subgroups of `M` and `g = ∑ bₛ Xˢ ∈ N⟨X⟩`:
- For each index `s`, compute the "level" `k(s) = min{n ∣ g s ∉ f(Wₙ)}`.
- If `k(s) ≥ 1`, lift `g s` to some `h s ∈ W_{k(s)-1}` (since `g s ∈ f(W_{k(s)-1})`).
- If `k(s) = 0`, take any lift. If `g s ∈ f(Wₙ)` for all `n`, then `g s = 0` and `h s = 0`.
- Then `{s ∣ h s ∉ Wₙ} ⊆ {s ∣ g s ∉ f(Wₙ)}`, which is finite for each `n`.

Follows Wedhorn's *Adic Spaces*. -/
theorem restrictedModule_map_surjective
    {M : Type v} [AddCommGroup M] [Module A M] [TopologicalSpace M]
     [ContinuousConstSMul A M] [NonarchimedeanAddGroup M]
    [FirstCountableTopology M]
    {N : Type w} [AddCommGroup N] [Module A N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [ContinuousConstSMul A N] [T2Space N]
    (f : M →ₗ[A] N) (hf_cont : Continuous f) (hf_surj : Function.Surjective f)
    (hf_open : IsOpenMap f) :
    Function.Surjective (restrictedModule.map (A := A) f hf_cont) := by
  classical
  intro ⟨g, hg⟩
  -- Reduce to finding h with f ∘ h = g and h → 0 cofinitely.
  suffices ∃ h : (Fin 1 →₀ ℕ) → M,
      (∀ s, f (h s) = g s) ∧ Tendsto h cofinite (nhds 0) by
    obtain ⟨h, hfh, hh⟩ := this
    exact ⟨⟨h, hh⟩, by apply Subtype.ext; funext s; exact hfh s⟩
  -- Step 1: Obtain an antitone basis of open additive subgroups of M.
  obtain ⟨W, _, hW⟩ := (Filter.HasBasis.mk (fun U ↦ ⟨fun hU ↦
    let ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
    ⟨V, trivial, hV⟩, fun ⟨V, _, hV⟩ ↦
    mem_nhds_iff.mpr ⟨(V : Set M), hV, V.isOpen, V.zero_mem⟩⟩) :
    (nhds (0 : M)).HasBasis (fun _ : OpenAddSubgroup M ↦ True)
      (fun V ↦ (V : Set M))).exists_antitone_subbasis
  -- Step 2: Sₙ = {s | g s ∉ f(Wₙ)} is finite for each n.
  have hS_fin : ∀ n, {s : Fin 1 →₀ ℕ | g s ∉ f '' (W n : Set M)}.Finite := by
    intro n
    exact mem_cofinite.mp (hg ((hf_open _ (W n).isOpen).mem_nhds
      ⟨0, (W n).zero_mem, map_zero f⟩))
  -- Step 3: g s ∈ f(Wₙ) for all n implies g s = 0 (Hausdorff argument).
  have hzero : ∀ s, (∀ n, g s ∈ f '' (W n : Set M)) → g s = 0 :=
    fun s hs ↦ eq_zero_of_mem_image_all f.toAddMonoidHom hf_cont W hW (g s) hs
  -- Step 4: Define h by diagonal construction.
  -- For each s: if g s ∈ f(Wₙ) for all n, then g s = 0 and h s := 0.
  -- Otherwise let k(s) = min{n | g s ∉ f(Wₙ)}.
  -- If k(s) = 0, take any lift. If k(s) ≥ 1, lift in W_{k(s)-1}.
  set h : (Fin 1 →₀ ℕ) → M := fun s ↦
    if hall : ∀ n, g s ∈ f '' (W n : Set M) then 0
    else by
      push Not at hall
      exact if hk0 : Nat.find hall = 0 then (hf_surj (g s)).choose
        else (not_not.mp (Nat.find_min hall (Nat.sub_one_lt hk0))).choose
  -- Step 5: f(h s) = g s for all s.
  have hfh : ∀ s, f (h s) = g s := by
    intro s; simp only [h]
    split_ifs with hall hk0
    · exact (map_zero f).trans (hzero s hall).symm
    · exact (hf_surj (g s)).choose_spec
    · have hall' : ∃ n, g s ∉ f '' (W n : Set M) := by push Not at hall; exact hall
      exact (not_not.mp (Nat.find_min hall' (by omega))).choose_spec.2
  -- Step 6: h → 0 cofinitely.
  -- For each Wₙ, {s | h s ∉ Wₙ} ⊆ Sₙ = {s | g s ∉ f(Wₙ)} (finite).
  -- Key: if g s ∈ f(Wₙ), then either h s = 0 ∈ Wₙ, or k(s) > n (since
  -- k(s) ≤ n would mean g s ∉ f(W_{k(s)}) and f(Wₙ) ⊆ f(W_{k(s)}), contradiction),
  -- so h s ∈ W_{k(s)-1} ⊆ Wₙ (antitone, k(s)-1 ≥ n).
  have hh : Tendsto h cofinite (nhds 0) := by
    rw [hW.1.tendsto_right_iff]
    intro n _
    rw [eventually_cofinite]
    apply (hS_fin n).subset
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs ⊢
    intro hgs; apply hs; clear hs
    simp only [h]
    split_ifs with hall hk0
    · -- g s ∈ f(Wₙ) for all n, h s = 0 ∈ Wₙ.
      exact (W n).zero_mem
    · -- k(s) = 0: g s ∉ f(W₀). Since W antitone, f(Wₙ) ⊆ f(W₀), contradiction.
      have hall' : ∃ m, g s ∉ f '' (W m : Set M) := by push Not at hall; exact hall
      have hspec := Nat.find_spec hall'
      rw [hk0] at hspec
      exact absurd (Set.image_mono (hW.2 (Nat.zero_le n)) hgs) hspec
    · -- k(s) ≥ 1: g s ∈ f(Wₙ) forces k(s) > n, so h s ∈ W_{k(s)-1} ⊆ Wₙ.
      have hall' : ∃ m, g s ∉ f '' (W m : Set M) := by push Not at hall; exact hall
      have hk_gt : n < Nat.find hall' := by
        by_contra h_le; push Not at h_le
        exact Nat.find_spec hall' (Set.image_mono (hW.2 h_le) hgs)
      exact hW.2 (by omega : n ≤ Nat.find hall' - 1)
        (not_not.mp (Nat.find_min hall' (by omega))).choose_spec.1
  exact ⟨h, hfh, hh⟩

end SurjectionLifting
