/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.TailDuality.TailOps
import LeanPool.JacobianDiffgeo.CanonicalForms
import LeanPool.JacobianDiffgeo.ResidueCalculus.GermFunctionals
import LeanPool.JacobianDiffgeo.ResidueTheorem.Unconditional

/-!
# `pairT`/`resMap`: the residue pairing on the germ model (serre-duality-tails)

Unit: serre-duality-tails (`docs/design/serre-duality-tails.md` §3 D2, §5.2, §6 P2–P4).

**Adaptation** (mirrors `SerrePairing/Pairing.lean`'s own note): `MForm X` is a quotient of
`MFormData X` exposing only the LIFTED reading maps (`ord`/`resAt`/`laurentCoeffAt`), no raw
`coeffAt`. So the pairing is built at the `MFormData` level first (`pairAtData`, honestly using
`θ.coeffAt p`), then descended to `MForm X` via `Quotient.liftOn` (congruence:
`MFormData.Eqv`, i.e. `𝓝[≠]`-agreement of `coeffAt` at every center — exactly what the residue
functional needs). All PUBLIC lemmas are stated at the `MForm`/`laurentCoeffAt` level.

* `readAt`: chart-read of a manifold germ as a punctured planar germ at the chart center.
* `pairAtData`/`pairAt`/`pairTailAt`/`pairT`: Miranda's `Res_ω` on `T[D]`.
* `pairT_trunc`/`pairT_mulInto`/`pairT_alpha`: the compatibilities Miranda's diagram needs
  (`pairT_alpha` is the only citation of the residue theorem; the `ℳ(X)`-module laws
  `MForm.ord_smul_mero`/`divisor_smul_mero`/`mul_smul` are ALREADY built unconditionally by
  canonical-forms, so no separate D5/D6 "ord kit"/"congruence" layer is needed here).
* `pairAt_tailGerm_order_ne_zero`/`pairT_ne_zero`: Miranda Thm 3.3's injectivity half.
* `resMap`/`resMap_injective`: the induced map `Ω(-D) →ₗ Dual(H1Tail D)`.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace Filter Topology
open RS RS.LaurentTail

namespace RS.TailDuality

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `readAt`: chart-read of a manifold germ as a punctured planar germ -/

/-- Chart-read of a manifold germ as a punctured planar germ at the chart center. -/
noncomputable def readAt (p : X) :
    RS.MeroGermOn X (chartAt ℂ p).source →ₗ[ℂ]
      Filter.Germ (𝓝[≠] (chartAt ℂ p p)) ℂ where
  toFun ψ := ψ.1.liftOn (fun f => (f ∘ (chartAt ℂ p).symm : Filter.Germ (𝓝[≠] (chartAt ℂ p p)) ℂ))
    (fun f g hfg => Filter.Germ.coe_eq.2 (eventuallyEq_nhdsNE_comp_chart_iff.mp
      ((eventuallyEq_codiscreteWithin_iff_of_isOpen (chartAt ℂ p).open_source).1 hfg p
        (mem_chart_source ℂ p))))
  map_add' ψ ψ' := by
    induction ψ using RS.MeroGermOn.ind with
    | h f hf =>
      induction ψ' using RS.MeroGermOn.ind with
      | h g hg =>
        change ((f + g) ∘ (chartAt ℂ p).symm : Filter.Germ (𝓝[≠] (chartAt ℂ p p)) ℂ)
            = (f ∘ (chartAt ℂ p).symm : Filter.Germ (𝓝[≠] (chartAt ℂ p p)) ℂ)
              + (g ∘ (chartAt ℂ p).symm : Filter.Germ (𝓝[≠] (chartAt ℂ p p)) ℂ)
        rw [show (f + g) ∘ (chartAt ℂ p).symm
          = f ∘ (chartAt ℂ p).symm + g ∘ (chartAt ℂ p).symm from rfl, Filter.Germ.coe_add]
  map_smul' c ψ := by
    induction ψ using RS.MeroGermOn.ind with
    | h f hf => rfl

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem readAt_mk (p : X) {f : X → ℂ} (hf : RS.MeromorphicOnX f (chartAt ℂ p).source) :
    readAt p (RS.MeroGermOn.mk f hf) = (f ∘ (chartAt ℂ p).symm : Filter.Germ _ ℂ) := rfl

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem meromorphicGerm_readAt (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    readAt p ψ ∈ RS.meromorphicGermsAt (chartAt ℂ p p) := by
  induction ψ using RS.MeroGermOn.ind with
  | h f hf =>
    rw [readAt_mk]
    exact hf p (mem_chart_source ℂ p)

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem readAt_mul (p : X) (ψ ψ' : RS.MeroGermOn X (chartAt ℂ p).source) :
    readAt p (ψ * ψ') = readAt p ψ * readAt p ψ' := by
  induction ψ using RS.MeroGermOn.ind with
  | h f hf =>
    induction ψ' using RS.MeroGermOn.ind with
    | h g hg =>
      rw [RS.MeroGermOn.mk_mul, readAt_mk, readAt_mk, readAt_mk,
        show (f * g) ∘ (chartAt ℂ p).symm = f ∘ (chartAt ℂ p).symm * g ∘ (chartAt ℂ p).symm
          from rfl, Filter.Germ.coe_mul]

omit [T2Space X] in
theorem readAt_tailGerm (p : X) (m : ℤ) :
    readAt p (RS.Cech.tailGerm p m) =
      (fun z => (z - chartAt ℂ p p) ^ m : Filter.Germ (𝓝[≠] (chartAt ℂ p p)) ℂ) := by
  rw [RS.Cech.tailGerm, readAt_mk]
  apply Filter.Germ.coe_eq.2
  have htarget_nhds : (chartAt ℂ p).target ∈ 𝓝 (chartAt ℂ p p) :=
    (chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
  have h1 : ∀ᶠ z in 𝓝 (chartAt ℂ p p), z ∈ (chartAt ℂ p).target := htarget_nhds
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds] with z hz
  change (chartAt ℂ p ((chartAt ℂ p).symm z) - chartAt ℂ p p) ^ m = (z - chartAt ℂ p p) ^ m
  rw [(chartAt ℂ p).right_inv hz]

/-! ### `pairAtData`/`pairAt`: the per-point residue pairing -/

/-- The per-point residue pairing at the `MFormData` (raw) level, built directly through
`resAt` on representatives (well-definedness: `resAt_congr` + the codiscrete→`𝓝[≠]` chart
transport, the same bridge `readAt` uses). -/
noncomputable def pairAtData (θ : MFormData X) (p : X) :
    RS.MeroGermOn X (chartAt ℂ p).source →ₗ[ℂ] ℂ where
  toFun ψ := ψ.1.liftOn
    (fun f => RS.resAt (fun z => f ((chartAt ℂ p).symm z) * θ.coeffAt p z) (chartAt ℂ p p))
    (fun f g hfg => by
      apply RS.resAt_congr
      have h1 := (eventuallyEq_codiscreteWithin_iff_of_isOpen (chartAt ℂ p).open_source).1 hfg p
        (mem_chart_source ℂ p)
      have h2 := eventuallyEq_nhdsNE_comp_chart_iff.mp h1
      filter_upwards [h2] with z hz
      simp only [Function.comp_apply] at hz
      rw [hz])
  map_add' ψ ψ' := by
    induction ψ using RS.MeroGermOn.ind with
    | h f hf =>
      induction ψ' using RS.MeroGermOn.ind with
      | h g hg =>
        change RS.resAt (fun z => (f + g) ((chartAt ℂ p).symm z) * θ.coeffAt p z) (chartAt ℂ p p)
          = RS.resAt (fun z => f ((chartAt ℂ p).symm z) * θ.coeffAt p z) (chartAt ℂ p p)
            + RS.resAt (fun z => g ((chartAt ℂ p).symm z) * θ.coeffAt p z) (chartAt ℂ p p)
        rw [show (fun z => (f + g) ((chartAt ℂ p).symm z) * θ.coeffAt p z)
          = (fun z => f ((chartAt ℂ p).symm z) * θ.coeffAt p z
              + g ((chartAt ℂ p).symm z) * θ.coeffAt p z) from by funext z; simp [add_mul]]
        have hf' : MeromorphicAt (fun z => f ((chartAt ℂ p).symm z) * θ.coeffAt p z)
            (chartAt ℂ p p) :=
          (show MeromorphicAt (fun z => f ((chartAt ℂ p).symm z)) (chartAt ℂ p p) from
            hf p (mem_chart_source ℂ p)).mul (θ.meromorphicAt_coeffAt p)
        have hg' : MeromorphicAt (fun z => g ((chartAt ℂ p).symm z) * θ.coeffAt p z)
            (chartAt ℂ p p) :=
          (show MeromorphicAt (fun z => g ((chartAt ℂ p).symm z)) (chartAt ℂ p p) from
            hg p (mem_chart_source ℂ p)).mul (θ.meromorphicAt_coeffAt p)
        exact RS.resAt_fun_add hf' hg'
  map_smul' c ψ := by
    induction ψ using RS.MeroGermOn.ind with
    | h f hf =>
      change RS.resAt (fun z => (c • f) ((chartAt ℂ p).symm z) * θ.coeffAt p z) (chartAt ℂ p p)
        = c * RS.resAt (fun z => f ((chartAt ℂ p).symm z) * θ.coeffAt p z) (chartAt ℂ p p)
      rw [show (fun z => (c • f) ((chartAt ℂ p).symm z) * θ.coeffAt p z)
        = (fun z => c * (f ((chartAt ℂ p).symm z) * θ.coeffAt p z)) from by
          funext z; simp [mul_assoc]]
      exact RS.resAt_const_mul c

omit [T2Space X] in
theorem pairAtData_mk (θ : MFormData X) (p : X) {f : X → ℂ}
    (hf : RS.MeromorphicOnX f (chartAt ℂ p).source) :
    pairAtData θ p (RS.MeroGermOn.mk f hf) =
      RS.resAt (fun z => f ((chartAt ℂ p).symm z) * θ.coeffAt p z) (chartAt ℂ p p) := rfl

omit [T2Space X] in
theorem pairAtData_congr {θ θ' : MFormData X} (p : X)
    (h : θ.coeffAt p =ᶠ[𝓝[≠] (chartAt ℂ p p)] θ'.coeffAt p) :
    pairAtData θ p = pairAtData θ' p := by
  apply LinearMap.ext
  intro ψ
  obtain ⟨f, hf, rfl⟩ := RS.MeroGermOn.exists_rep ψ
  rw [pairAtData_mk, pairAtData_mk]
  apply RS.resAt_congr
  filter_upwards [h] with z hz
  rw [hz]

/-- The residue pairing, `Res_ω` (Miranda VI.3), on classes. -/
noncomputable def pairAt (θ : MForm X) (p : X) :
    RS.MeroGermOn X (chartAt ℂ p).source →ₗ[ℂ] ℂ :=
  Quotient.liftOn θ (pairAtData · p) (fun _ _ hab => pairAtData_congr p (hab p))

omit [T2Space X] in
theorem pairAt_apply_mk (θ : MFormData X) (p : X) : pairAt (MForm.mk θ) p = pairAtData θ p := rfl

omit [T2Space X] in
theorem pairAt_tailGerm (θ : MForm X) (p : X) (m : ℤ) :
    pairAt θ p (RS.Cech.tailGerm p m) = θ.laurentCoeffAt p (-1 - m) := by
  obtain ⟨θdata, rfl⟩ := MForm.exists_rep θ
  rw [pairAt_apply_mk, MForm.laurentCoeffAt_mk, RS.Cech.tailGerm, pairAtData_mk]
  have heq : (fun z => (chartAt ℂ p ((chartAt ℂ p).symm z) - chartAt ℂ p p) ^ m * θdata.coeffAt p z)
      =ᶠ[𝓝[≠] (chartAt ℂ p p)] (fun z => (z - chartAt ℂ p p) ^ m * θdata.coeffAt p z) := by
    have htarget_nhds : ∀ᶠ z in 𝓝 (chartAt ℂ p p), z ∈ (chartAt ℂ p).target :=
      (chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    filter_upwards [htarget_nhds.filter_mono nhdsWithin_le_nhds] with z hz
    rw [(chartAt ℂ p).right_inv hz]
  rw [RS.resAt_congr heq, RS.resAt_zpow_mul (θdata.meromorphicAt_coeffAt p)]

omit [T2Space X] in
theorem pairAt_eq_zero_of_mem_ordGe {θ : MForm X} {D : RS.Divisor X} {p : X}
    (hθ : θ ∈ MForm.OmegaSpace (-D)) {ψ : RS.MeroGermOn X (chartAt ℂ p).source}
    (hψ : ψ ∈ RS.Cech.ordGe p (-(D p))) : pairAt θ p ψ = 0 := by
  rw [RS.Cech.mem_ordGe_iff] at hψ
  obtain ⟨θdata, rfl⟩ := MForm.exists_rep θ
  obtain ⟨f, hf, rfl⟩ := RS.MeroGermOn.exists_rep ψ
  rw [pairAt_apply_mk, pairAtData_mk]
  apply RS.resAt_of_order_nonneg
  have hordf : ((-(D p) : ℤ) : WithTop ℤ) ≤ RS.ordAtX f p := by
    rwa [RS.MeroGermOn.ord_mk (chartAt ℂ p).open_source (mem_chart_source ℂ p)] at hψ
  have hθp : ((D p : ℤ) : WithTop ℤ) ≤ (MForm.mk θdata).ord p := by
    have h := MForm.mem_omegaSpace_iff.mp hθ p
    rwa [Divisor.neg_apply, neg_neg] at h
  rw [MForm.ord_mk] at hθp
  have hordfmul : meromorphicOrderAt (fun z => f ((chartAt ℂ p).symm z) * θdata.coeffAt p z)
      (chartAt ℂ p p) = RS.ordAtX f p + θdata.ord p :=
    meromorphicOrderAt_mul (hf p (mem_chart_source ℂ p)) (θdata.meromorphicAt_coeffAt p)
  rw [hordfmul]
  calc (0 : WithTop ℤ) = ((-(D p) : ℤ) : WithTop ℤ) + ((D p : ℤ) : WithTop ℤ) := by
        rw [← WithTop.coe_add]; norm_num
    _ ≤ RS.ordAtX f p + θdata.ord p := add_le_add hordf hθp

/-! ### Linearity of `pairAt` in `θ` (unconditional; feeds `resMap`'s `map_add'`/`map_smul'`) -/

omit [T2Space X] in
theorem pairAt_add (θ η : MForm X) (p : X) : pairAt (θ + η) p = pairAt θ p + pairAt η p := by
  obtain ⟨θdata, rfl⟩ := MForm.exists_rep θ
  obtain ⟨ηdata, rfl⟩ := MForm.exists_rep η
  rw [MForm.mk_add, pairAt_apply_mk, pairAt_apply_mk, pairAt_apply_mk]
  apply LinearMap.ext
  intro ψ
  obtain ⟨f, hf, rfl⟩ := RS.MeroGermOn.exists_rep ψ
  rw [LinearMap.add_apply, pairAtData_mk, pairAtData_mk, pairAtData_mk]
  rw [show (fun z => f ((chartAt ℂ p).symm z) * (θdata + ηdata).coeffAt p z)
    = (fun z => f ((chartAt ℂ p).symm z) * θdata.coeffAt p z
        + f ((chartAt ℂ p).symm z) * ηdata.coeffAt p z) from by
      funext z; simp [mul_add]]
  exact RS.resAt_fun_add
    ((show MeromorphicAt (fun z => f ((chartAt ℂ p).symm z)) (chartAt ℂ p p) from
      hf p (mem_chart_source ℂ p)).mul (θdata.meromorphicAt_coeffAt p))
    ((show MeromorphicAt (fun z => f ((chartAt ℂ p).symm z)) (chartAt ℂ p p) from
      hf p (mem_chart_source ℂ p)).mul (ηdata.meromorphicAt_coeffAt p))

omit [T2Space X] in
theorem pairAt_smul (c : ℂ) (θ : MForm X) (p : X) : pairAt (c • θ) p = c • pairAt θ p := by
  obtain ⟨θdata, rfl⟩ := MForm.exists_rep θ
  rw [MForm.mk_smul, pairAt_apply_mk, pairAt_apply_mk]
  apply LinearMap.ext
  intro ψ
  obtain ⟨f, hf, rfl⟩ := RS.MeroGermOn.exists_rep ψ
  rw [LinearMap.smul_apply, pairAtData_mk, pairAtData_mk, smul_eq_mul]
  rw [show (fun z => f ((chartAt ℂ p).symm z) * (c • θdata).coeffAt p z)
    = (fun z => c * (f ((chartAt ℂ p).symm z) * θdata.coeffAt p z)) from by
      funext z; simp [MFormData.coeffAt_smul]; ring]
  exact RS.resAt_const_mul c

omit [T2Space X] in
theorem pairAt_sub (θ η : MForm X) (p : X) : pairAt (θ - η) p = pairAt θ p - pairAt η p := by
  obtain ⟨θdata, rfl⟩ := MForm.exists_rep θ
  obtain ⟨ηdata, rfl⟩ := MForm.exists_rep η
  rw [show MForm.mk θdata - MForm.mk ηdata = MForm.mk (θdata - ηdata) from rfl,
    pairAt_apply_mk, pairAt_apply_mk, pairAt_apply_mk]
  apply LinearMap.ext
  intro ψ
  obtain ⟨f, hf, rfl⟩ := RS.MeroGermOn.exists_rep ψ
  rw [LinearMap.sub_apply, pairAtData_mk, pairAtData_mk, pairAtData_mk]
  rw [show (fun z => f ((chartAt ℂ p).symm z) * (θdata - ηdata).coeffAt p z)
    = (fun z => f ((chartAt ℂ p).symm z) * θdata.coeffAt p z
        - f ((chartAt ℂ p).symm z) * ηdata.coeffAt p z) from by
      funext z; simp [mul_sub]]
  exact RS.resAt_sub
    ((show MeromorphicAt (fun z => f ((chartAt ℂ p).symm z)) (chartAt ℂ p p) from
      hf p (mem_chart_source ℂ p)).mul (θdata.meromorphicAt_coeffAt p))
    ((show MeromorphicAt (fun z => f ((chartAt ℂ p).symm z)) (chartAt ℂ p p) from
      hf p (mem_chart_source ℂ p)).mul (ηdata.meromorphicAt_coeffAt p))

/-! ### `pairAt_tailGerm_order_ne_zero`: the shared core of injectivity and Lemma 3.6 -/

omit [T2Space X] in
theorem pairAt_tailGerm_order_ne_zero {θ : MForm X} {p : X} (hne : θ.ord p ≠ ⊤) :
    pairAt θ p (RS.Cech.tailGerm p (-1 - (θ.ord p).untop₀)) ≠ 0 := by
  rw [pairAt_tailGerm, show (-1 - (-1 - (θ.ord p).untop₀)) = (θ.ord p).untop₀ from by ring]
  obtain ⟨θdata, rfl⟩ := MForm.exists_rep θ
  rw [MForm.ord_mk] at hne
  rw [MForm.ord_mk, MForm.laurentCoeffAt_mk]
  exact RS.laurentCoeffAt_order_ne_zero (θdata.meromorphicAt_coeffAt p) hne

/-! ### `pairT`: assembling `pairAt` over the tail `T D` -/

variable [DecidableEq X]

/-- `pairAt θ p` descended to the tail fibre `TailAt p D`, for `θ ∈ Ω(-D)`. -/
noncomputable def pairTailAt (θ : MForm X) {D : RS.Divisor X} (hθ : θ ∈ MForm.OmegaSpace (-D))
    (p : X) : TailAt p D →ₗ[ℂ] ℂ :=
  Submodule.liftQ _ (pairAt θ p) (fun _ψ hψ => LinearMap.mem_ker.mpr
    (pairAt_eq_zero_of_mem_ordGe hθ hψ))

omit [DecidableEq X] [T2Space X] in
theorem pairTailAt_mk (θ : MForm X) {D : RS.Divisor X} (hθ : θ ∈ MForm.OmegaSpace (-D)) (p : X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    pairTailAt θ hθ p (TailAt.mk p D ψ) = pairAt θ p ψ :=
  Submodule.liftQ_apply _ _ ψ

/-- Miranda's `Res_ω` on `T[D]` (§3 D2). -/
noncomputable def pairT (θ : MForm X) {D : RS.Divisor X} (hθ : θ ∈ MForm.OmegaSpace (-D)) :
    T D →ₗ[ℂ] ℂ :=
  DFinsupp.lsum ℕ (pairTailAt θ hθ)

omit [T2Space X] in
@[simp] theorem pairT_singleT (θ : MForm X) {D : RS.Divisor X} (hθ : θ ∈ MForm.OmegaSpace (-D))
    (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    pairT θ hθ (singleT p D ψ) = pairAt θ p ψ := by
  change DFinsupp.lsum ℕ (pairTailAt θ hθ) (DFinsupp.single p (TailAt.mk p D ψ)) = _
  rw [DFinsupp.lsum_single ℕ (pairTailAt θ hθ) p (TailAt.mk p D ψ), pairTailAt_mk]

omit [T2Space X] in
theorem pairT_zero (D : RS.Divisor X) : pairT (0 : MForm X) (zero_mem _) = (0 : T D →ₗ[ℂ] ℂ) := by
  apply DFinsupp.lhom_ext
  intro p x
  obtain ⟨ψ, rfl⟩ := TailAt.mk_surjective p D x
  change pairT (0 : MForm X) (zero_mem _) (singleT p D ψ) = (0 : T D →ₗ[ℂ] ℂ) (singleT p D ψ)
  rw [pairT_singleT, LinearMap.zero_apply,
    show (0 : MForm X) = MForm.mk (0 : MFormData X) from MForm.mk_zero.symm, pairAt_apply_mk]
  obtain ⟨f, hf, rfl⟩ := RS.MeroGermOn.exists_rep ψ
  rw [pairAtData_mk,
    show (fun z => f ((chartAt ℂ p).symm z) * (0 : MFormData X).coeffAt p z) = (fun _ => (0 : ℂ))
      from by funext z; simp]
  exact RS.resAt_zero_fun

/-! ### Monotonicity of `Ω(-D)` in `D`, and the multiplication mover -/

omit [T2Space X] [DecidableEq X] in
theorem omegaSpace_anti {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) {θ : MForm X}
    (hθ₂ : θ ∈ MForm.OmegaSpace (-D₂)) : θ ∈ MForm.OmegaSpace (-D₁) := by
  rw [MForm.mem_omegaSpace_iff] at hθ₂ ⊢
  intro p
  have hDp : D₁ p ≤ D₂ p := Function.locallyFinsuppWithin.le_def.1 h p
  have h2 := hθ₂ p
  rw [Divisor.neg_apply, neg_neg] at h2 ⊢
  calc ((D₁ p : ℤ) : WithTop ℤ) ≤ ((D₂ p : ℤ) : WithTop ℤ) := by exact_mod_cast hDp
    _ ≤ θ.ord p := h2

omit [T2Space X] [DecidableEq X] in
theorem smul_mem_omegaSpace {f : RS.Mero X} {θ : MForm X} {E F : RS.Divisor X}
    (hf : ∀ p, ((F p : ℤ) : WithTop ℤ) ≤ f.ord p) (hθ : θ ∈ MForm.OmegaSpace (-E)) :
    f • θ ∈ MForm.OmegaSpace (-(E + F)) := by
  rw [MForm.mem_omegaSpace_iff]
  intro p
  rw [RS.MForm.ord_smul_mero, Divisor.neg_apply, neg_neg, Divisor.add_apply]
  have hEp : ((E p : ℤ) : WithTop ℤ) ≤ θ.ord p := by
    have h := MForm.mem_omegaSpace_iff.mp hθ p
    rwa [Divisor.neg_apply, neg_neg] at h
  calc ((E p + F p : ℤ) : WithTop ℤ) = ((E p : ℤ) : WithTop ℤ) + ((F p : ℤ) : WithTop ℤ) := by
        push_cast; ring_nf
    _ ≤ θ.ord p + f.ord p := add_le_add hEp (hf p)
    _ = f.ord p + θ.ord p := add_comm _ _

omit [T2Space X] in
theorem pairT_trunc {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) (θ : MForm X)
    (hθ₂ : θ ∈ MForm.OmegaSpace (-D₂)) :
    (pairT θ hθ₂) ∘ₗ truncT h = pairT θ (omegaSpace_anti h hθ₂) := by
  apply DFinsupp.lhom_ext
  intro p x
  obtain ⟨ψ, rfl⟩ := TailAt.mk_surjective p D₁ x
  change ((pairT θ hθ₂) ∘ₗ truncT h) (singleT p D₁ ψ)
      = pairT θ (omegaSpace_anti h hθ₂) (singleT p D₁ ψ)
  rw [LinearMap.comp_apply, truncT_singleT, pairT_singleT, pairT_singleT]

/-! ### `pairT_mulInto`: Miranda's `Res_ω∘μ_f = Res_{fω}` -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mulInto_singleT (f : RS.Mero X) {D E : RS.Divisor X}
    (hf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) (p : X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    mulInto f hf (singleT p D ψ) =
      singleT p E (RS.MeroGermOn.restrict (Set.subset_univ _) f * ψ) := by
  change DFinsupp.mapRange (fun p => mulIntoAt f p (hf p)) (fun _ => map_zero _)
    (DFinsupp.single p (TailAt.mk p D ψ)) = _
  rw [DFinsupp.mapRange_single, mulIntoAt_mk]
  rfl

omit [DecidableEq X] [T2Space X] in
/-- Miranda's `Res_ω∘μ_f = Res_{fω}`, at the raw germ level. -/
theorem pairAt_mulInto (f : RS.Mero X) (p : X) (θ : MForm X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    pairAt θ p (RS.MeroGermOn.restrict (Set.subset_univ _) f * ψ) = pairAt (f • θ) p ψ := by
  obtain ⟨θdata, rfl⟩ := MForm.exists_rep θ
  obtain ⟨g, hg, rfl⟩ := RS.MeroGermOn.exists_rep ψ
  -- the meromorphy witness is a named `have`: applying `meromorphicOnX_holoRepr` inline leaves a
  -- term that is not type-correct at `implicit` transparency, which blocks the rewrites below
  have hholo : RS.MeromorphicOnX (RS.MeroGermOn.holoRepr f) ((chartAt ℂ p).source) :=
    fun x _ => RS.MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f x (Set.mem_univ x)
  have hrestr : RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ p).source) f
      = RS.MeroGermOn.mk f.holoRepr hholo := by
    conv_lhs => rw [← RS.MeroGermOn.mk_holoRepr isOpen_univ f]
    rw [RS.MeroGermOn.restrict_mk]
  rw [hrestr, RS.MeroGermOn.mk_mul, pairAt_apply_mk, pairAtData_mk,
    MForm.mero_smul_mk, pairAt_apply_mk, pairAtData_mk]
  apply RS.resAt_congr
  filter_upwards with z
  change f.holoRepr ((chartAt ℂ p).symm z) * g ((chartAt ℂ p).symm z) * θdata.coeffAt p z
    = g ((chartAt ℂ p).symm z) * (f • θdata).coeffAt p z
  rw [MFormData.coeffAt_smul_mero]
  ring

omit [T2Space X] in
theorem pairT_mulInto {D E : RS.Divisor X} (f : RS.Mero X)
    (hf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) (θ : MForm X)
    (hθ : θ ∈ MForm.OmegaSpace (-E)) (hfθ : f • θ ∈ MForm.OmegaSpace (-D)) :
    (pairT θ hθ) ∘ₗ mulInto f hf = pairT (f • θ) hfθ := by
  apply DFinsupp.lhom_ext
  intro p x
  obtain ⟨ψ, rfl⟩ := TailAt.mk_surjective p D x
  change ((pairT θ hθ) ∘ₗ mulInto f hf) (singleT p D ψ) = pairT (f • θ) hfθ (singleT p D ψ)
  rw [LinearMap.comp_apply, mulInto_singleT, pairT_singleT, pairT_singleT, pairAt_mulInto]

/-! ### `pairT_alpha`: the residue theorem's ONLY citation -/

variable [CompactSpace X] [ConnectedSpace X] [T1Space X]

omit [DecidableEq X] [CompactSpace X] [ConnectedSpace X] [T1Space X] [T2Space X] in
theorem pairAt_one (θ : MForm X) (p : X) :
    pairAt θ p (1 : RS.MeroGermOn X (chartAt ℂ p).source) = θ.resAt p := by
  obtain ⟨θdata, rfl⟩ := MForm.exists_rep θ
  rw [pairAt_apply_mk, MForm.resAt_mk,
    show (1 : RS.MeroGermOn X (chartAt ℂ p).source)
      = RS.MeroGermOn.mk (fun _ => 1) (RS.meromorphicOnX_const 1 _) from RS.MeroGermOn.mk_one.symm,
    pairAtData_mk]
  show RS.resAt (fun z => 1 * θdata.coeffAt p z) (chartAt ℂ p p) = θdata.resAt p
  rw [show (fun z => (1 : ℂ) * θdata.coeffAt p z) = θdata.coeffAt p from by funext z; ring]
  rfl

theorem alpha_eq_sum_singleT (D : RS.Divisor X) (f : RS.Mero X) :
    alpha D f = ∑ p ∈ alphaFinset D f, singleT p D (RS.MeroGermOn.restrict (Set.subset_univ _) f) :=
        by
  apply DFinsupp.ext
  intro q
  rw [DFinsupp.finsetSum_apply]
  by_cases hq : q ∈ alphaFinset D f
  · rw [Finset.sum_eq_single q (fun b _ hbq => singleT_apply_of_ne (Ne.symm hbq) D _)
      (fun hqS => absurd hq hqS), singleT_apply_self, alpha_apply]
  · have hbound : ((-(D q) : ℤ) : WithTop ℤ) ≤
        (RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ q).source) f).ord q := by
      rw [RS.MeroGermOn.ord_restrict (Set.subset_univ _) (chartAt ℂ q).open_source isOpen_univ
        (mem_chart_source ℂ q)]
      exact not_mem_alphaFinset D f hq
    have hzero : TailAt.mk q D (RS.MeroGermOn.restrict (Set.subset_univ _) f) = 0 :=
      (TailAt.mk_eq_zero_iff (RS.MeroGermOn.restrict (Set.subset_univ _) f)).2 hbound
    rw [alpha_apply, hzero]
    apply (Finset.sum_eq_zero ?_).symm
    intro p hp
    apply singleT_apply_of_ne _ D _
    intro h
    apply hq
    rw [h]
    exact hp

theorem pairT_alpha {D : RS.Divisor X} (θ : MForm X) (hθ : θ ∈ MForm.OmegaSpace (-D))
    (f : RS.Mero X) : pairT θ hθ (alphaL D f) = 0 := by
  have hsum : pairT θ hθ (alphaL D f)
      = ∑ p ∈ alphaFinset D f, (f • θ).resAt p := by
    change pairT θ hθ (alpha D f) = _
    rw [alpha_eq_sum_singleT, map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [pairT_singleT,
      show RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ p).source) f
        = RS.MeroGermOn.restrict (Set.subset_univ _) f * 1 from (mul_one _).symm,
      pairAt_mulInto, pairAt_one]
  rw [hsum]
  apply RS.residueTheorem (f • θ)
  intro p hp
  simp only [Function.mem_support, ne_eq] at hp
  rw [Finset.mem_coe]
  by_contra hpS
  apply hp
  have hfp : ((-(D p) : ℤ) : WithTop ℤ) ≤ f.ord p := not_mem_alphaFinset D f hpS
  have hθp : ((D p : ℤ) : WithTop ℤ) ≤ θ.ord p := by
    have h := MForm.mem_omegaSpace_iff.mp hθ p
    rwa [Divisor.neg_apply, neg_neg] at h
  have hordnn : (0 : WithTop ℤ) ≤ (f • θ).ord p := by
    rw [RS.MForm.ord_smul_mero]
    calc (0 : WithTop ℤ) = ((-(D p) : ℤ) : WithTop ℤ) + ((D p : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]; norm_num
      _ ≤ f.ord p + θ.ord p := add_le_add hfp hθp
  obtain ⟨χdata, hχ⟩ := MForm.exists_rep (f • θ)
  rw [← hχ, MForm.resAt_mk]
  apply RS.resAt_of_order_nonneg
  change (0 : WithTop ℤ) ≤ χdata.ord p
  rw [show χdata.ord p = (f • θ).ord p from by rw [← hχ, MForm.ord_mk]]
  exact hordnn

/-! ### `pairT` linearity in `θ` (feeds `resMap`) and injectivity -/

omit [CompactSpace X] [ConnectedSpace X] [T1Space X] [T2Space X] in
theorem pairT_add {D : RS.Divisor X} (θ₁ θ₂ : MForm X) (hθ₁ : θ₁ ∈ MForm.OmegaSpace (-D))
    (hθ₂ : θ₂ ∈ MForm.OmegaSpace (-D)) (hθ12 : θ₁ + θ₂ ∈ MForm.OmegaSpace (-D)) :
    pairT (θ₁ + θ₂) hθ12 = pairT θ₁ hθ₁ + pairT θ₂ hθ₂ := by
  apply DFinsupp.lhom_ext
  intro p x
  obtain ⟨ψ, rfl⟩ := TailAt.mk_surjective p D x
  change pairT (θ₁ + θ₂) hθ12 (singleT p D ψ) = (pairT θ₁ hθ₁ + pairT θ₂ hθ₂) (singleT p D ψ)
  rw [LinearMap.add_apply, pairT_singleT, pairT_singleT, pairT_singleT, pairAt_add,
    LinearMap.add_apply]

omit [CompactSpace X] [ConnectedSpace X] [T1Space X] [T2Space X] in
theorem pairT_sub {D : RS.Divisor X} (θ₁ θ₂ : MForm X) (hθ₁ : θ₁ ∈ MForm.OmegaSpace (-D))
    (hθ₂ : θ₂ ∈ MForm.OmegaSpace (-D)) (hθ12 : θ₁ - θ₂ ∈ MForm.OmegaSpace (-D)) :
    pairT (θ₁ - θ₂) hθ12 = pairT θ₁ hθ₁ - pairT θ₂ hθ₂ := by
  apply DFinsupp.lhom_ext
  intro p x
  obtain ⟨ψ, rfl⟩ := TailAt.mk_surjective p D x
  change pairT (θ₁ - θ₂) hθ12 (singleT p D ψ) = (pairT θ₁ hθ₁ - pairT θ₂ hθ₂) (singleT p D ψ)
  rw [LinearMap.sub_apply, pairT_singleT, pairT_singleT, pairT_singleT, pairAt_sub,
    LinearMap.sub_apply]

omit [CompactSpace X] [ConnectedSpace X] [T1Space X] [T2Space X] in
theorem pairT_smul {D : RS.Divisor X} (c : ℂ) (θ : MForm X) (hθ : θ ∈ MForm.OmegaSpace (-D))
    (hcθ : c • θ ∈ MForm.OmegaSpace (-D)) :
    pairT (c • θ) hcθ = c • pairT θ hθ := by
  apply DFinsupp.lhom_ext
  intro p x
  obtain ⟨ψ, rfl⟩ := TailAt.mk_surjective p D x
  change pairT (c • θ) hcθ (singleT p D ψ) = (c • pairT θ hθ) (singleT p D ψ)
  rw [LinearMap.smul_apply, pairT_singleT, pairT_singleT, pairAt_smul, LinearMap.smul_apply]

omit [CompactSpace X] [ConnectedSpace X] [T2Space X] in
theorem pairT_ne_zero [ConnectedSpace X] {D : RS.Divisor X} {θ : MForm X} (hθ0 : θ ≠ 0)
    (hθ : θ ∈ MForm.OmegaSpace (-D)) : pairT θ hθ ≠ 0 := by
  intro hz
  obtain ⟨p⟩ : Nonempty X := inferInstance
  have hne : θ.ord p ≠ ⊤ := MForm.ord_ne_top hθ0 p
  apply pairAt_tailGerm_order_ne_zero hne
  have h2 := DFunLike.congr_fun hz
    (singleT p D (RS.Cech.tailGerm p (-1 - (θ.ord p).untop₀)))
  rwa [pairT_singleT, LinearMap.zero_apply] at h2

/-! ### `resMap`: the induced map `Ω(-D) →ₗ Dual(H1Tail D)` -/

/-- The residue pairing, descended to `H1Tail D` (Miranda's `Res : L⁽¹⁾(-D) → H¹(D)^*`). -/
noncomputable def resMap (D : RS.Divisor X) :
    ↥(MForm.OmegaSpace (-D)) →ₗ[ℂ] Module.Dual ℂ (H1Tail D) where
  toFun θ := Submodule.liftQ (LinearMap.range (alphaL D)) (pairT θ.1 θ.2)
    (by rintro τ ⟨g, rfl⟩; exact pairT_alpha θ.1 θ.2 g)
  map_add' θ₁ θ₂ := by
    apply LinearMap.ext
    intro x
    obtain ⟨τ, rfl⟩ := H1Tail.mk_surjective D x
    change pairT (θ₁ + θ₂).1 (θ₁ + θ₂).2 τ = pairT θ₁.1 θ₁.2 τ + pairT θ₂.1 θ₂.2 τ
    exact DFunLike.congr_fun (pairT_add θ₁.1 θ₂.1 θ₁.2 θ₂.2 (θ₁ + θ₂).2) τ
  map_smul' c θ := by
    apply LinearMap.ext
    intro x
    obtain ⟨τ, rfl⟩ := H1Tail.mk_surjective D x
    change pairT (c • θ).1 (c • θ).2 τ = (RingHom.id ℂ) c • pairT θ.1 θ.2 τ
    rw [RingHom.id_apply]
    exact DFunLike.congr_fun (pairT_smul c θ.1 θ.2 (c • θ).2) τ

theorem resMap_mk (D : RS.Divisor X) (θ : ↥(MForm.OmegaSpace (-D))) (τ : T D) :
    resMap D θ (H1Tail.mk D τ) = pairT θ.1 θ.2 τ :=
  Submodule.liftQ_apply _ _ τ

omit [ConnectedSpace X] in
theorem resMap_injective [ConnectedSpace X] (D : RS.Divisor X) :
    Function.Injective (resMap D) := by
  intro θ₁ θ₂ heq
  apply Subtype.ext
  by_contra hne
  have hsub0 : θ₁.1 - θ₂.1 ≠ 0 := sub_ne_zero.2 hne
  have hmem : θ₁.1 - θ₂.1 ∈ MForm.OmegaSpace (-D) := Submodule.sub_mem _ θ₁.2 θ₂.2
  apply pairT_ne_zero hsub0 hmem
  apply LinearMap.ext
  intro τ
  change pairT (θ₁.1 - θ₂.1) hmem τ = (0 : T D →ₗ[ℂ] ℂ) τ
  rw [LinearMap.zero_apply, pairT_sub θ₁.1 θ₂.1 θ₁.2 θ₂.2 hmem, LinearMap.sub_apply]
  have h1 := resMap_mk D θ₁ τ
  have h2 := resMap_mk D θ₂ τ
  rw [← h1, ← h2, heq, sub_self]

end RS.TailDuality
