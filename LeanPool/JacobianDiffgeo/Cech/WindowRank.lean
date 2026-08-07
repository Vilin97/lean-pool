/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Cech.Window

/-!
# Window dimension counts (CC8, D7, proof plan §6.8)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.6, §6.8).

* `evalAt_eq_zero_iff` [Compat]: chart-transported analogue of mathlib's
  `tendsto_zero_iff_meromorphicOrderAt_pos`, filed as a request to meromorphic-and-divisors
  (`docs/requests/meromorphic-and-divisors.md`) but not upstreamed — proved here from exported
  chart-transport lemmas only.
* `leadCoeff_eq_zero_iff`: the one-step leading-coefficient functional detects the exact order.
* `finrank_windowAt`/`finrank_window`: the `θ`-basis dimension counts (design §6.8), via an
  explicit one-step splitting `WindowAt p d d' ≃ₗ WindowAt p d (d'-1) × ℂ` and induction on
  `(d' - d).toNat` (no explicit basis/independence argument needed).
-/

open scoped ContDiff Manifold Topology
open Set TopologicalSpace RS.Cech Filter

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Compat: chart-transported vanishing criterion for `evalAt` -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Compat (requested from meromorphic-and-divisors, not upstreamed): chart-transported analogue
of mathlib's `tendsto_zero_iff_meromorphicOrderAt_pos`. -/
theorem tendsto_zero_iff_ordAtX_pos {f : X → ℂ} {x : X} (hf : RS.MeromorphicAtX f x) :
    Tendsto f (𝓝[≠] x) (𝓝 0) ↔ 0 < RS.ordAtX f x := by
  rw [RS.ordAtX_def, ← tendsto_zero_iff_meromorphicOrderAt_pos hf]
  exact RS.tendsto_nhdsNE_comp_chart_iff

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Compat (requested from meromorphic-and-divisors §1.4(b), not upstreamed): `evalAt` vanishes
(given `0 ≤ ord`) iff the order is strictly positive. -/
theorem MeroGermOn.evalAt_eq_zero_iff {U : Set X} {x : X} (hU : IsOpen U) (hx : x ∈ U)
    (φ : RS.MeroGermOn X U) (h : 0 ≤ φ.ord x) :
    φ.evalAt x = 0 ↔ 0 < φ.ord x := by
  obtain ⟨f, hf, rfl⟩ := RS.MeroGermOn.exists_rep φ
  have htend := RS.MeroGermOn.tendsto_evalAt hU hx (RS.MeroGermOn.mk f hf) h rfl
  rw [RS.MeroGermOn.ord_mk hU hx] at h ⊢
  constructor
  · intro heq
    rw [heq] at htend
    exact (RS.Cech.tendsto_zero_iff_ordAtX_pos (hf x hx)).1 htend
  · intro hpos
    exact tendsto_nhds_unique htend ((RS.Cech.tendsto_zero_iff_ordAtX_pos (hf x hx)).2 hpos)

/-! ### `leadCoeff` detects the exact order -/

private theorem withTop_lt_neg_add_iff (m : ℤ) (t : WithTop ℤ) :
    0 < ((-m : ℤ) : WithTop ℤ) + t ↔ ((m + 1 : ℤ) : WithTop ℤ) ≤ t := by
  by_cases ht : t = ⊤
  · subst ht
    simp
  · obtain ⟨k, rfl⟩ := WithTop.ne_top_iff_exists.1 ht
    rw [show (((-m : ℤ) : WithTop ℤ) + (k : WithTop ℤ)) = (((-m + k : ℤ) : ℤ) : WithTop ℤ) by
      norm_cast]
    constructor
    · intro h
      have h' : (0 : ℤ) < -m + k := by exact_mod_cast h
      exact_mod_cast (show m + 1 ≤ k by omega)
    · intro h
      have h' : m + 1 ≤ k := by exact_mod_cast h
      exact_mod_cast (show (0 : ℤ) < -m + k by omega)

theorem leadCoeff_eq_zero_iff (p : X) (m : ℤ) (ψ : ordGe p m) :
    leadCoeff p m ψ = 0 ↔
      ((m + 1 : ℤ) : WithTop ℤ) ≤ (ψ : RS.MeroGermOn X ((chartAt ℂ p).source)).ord p := by
  have hmul_ord : (tailGerm p (-m) * (ψ : RS.MeroGermOn X ((chartAt ℂ p).source))).ord p =
      ((-m : ℤ) : WithTop ℤ) + (ψ : RS.MeroGermOn X ((chartAt ℂ p).source)).ord p := by
    rw [RS.MeroGermOn.ord_mul (chartAt ℂ p).open_source (mem_chart_source ℂ p), ord_tailGerm_self]
  have h0 : (0 : WithTop ℤ) ≤
      (tailGerm p (-m) * (ψ : RS.MeroGermOn X ((chartAt ℂ p).source))).ord p := by
    rw [hmul_ord]
    have hψm : (m : WithTop ℤ) ≤ (ψ : RS.MeroGermOn X ((chartAt ℂ p).source)).ord p := ψ.2
    have hstep : (((-m : ℤ) : WithTop ℤ) + (m : WithTop ℤ)) ≤
        ((-m : ℤ) : WithTop ℤ) + (ψ : RS.MeroGermOn X ((chartAt ℂ p).source)).ord p :=
      add_le_add le_rfl hψm
    have hz : (((-m : ℤ) : WithTop ℤ) + (m : WithTop ℤ)) = 0 := by
      have : (-m + m : ℤ) = 0 := by ring
      exact_mod_cast this
    rwa [hz] at hstep
  change (tailGerm p (-m) * (ψ : RS.MeroGermOn X ((chartAt ℂ p).source))).evalAt p = 0 ↔ _
  rw [RS.Cech.MeroGermOn.evalAt_eq_zero_iff (chartAt ℂ p).open_source (mem_chart_source ℂ p) _ h0,
    hmul_ord, withTop_lt_neg_add_iff]

/-- Leading-coefficient normalization (up to a nonzero scalar, all that induction needs):
`leadCoeff p m (θ_{p,m}) ≠ 0`. -/
theorem leadCoeff_tailGerm_self_ne_zero (p : X) (m : ℤ) :
    leadCoeff p m (⟨tailGerm p m, mem_ordGe_iff.2 (le_of_eq (ord_tailGerm_self p m).symm)⟩ :
      ordGe p m) ≠ 0 := by
  intro hz
  rw [leadCoeff_eq_zero_iff, ord_tailGerm_self] at hz
  have : (m + 1 : ℤ) ≤ m := by exact_mod_cast hz
  omega

/-! ### The one-step splitting `WindowAt p d d' ≃ₗ WindowAt p d (d'-1) × ℂ` -/

variable (p : X)

/-- The distinguished representative of `θ_{p,-d'}` as an `ordGe p (-d')` element. -/
private noncomputable def tailGermElt (d' : ℤ) : ordGe p (-d') :=
  ⟨tailGerm p (-d'), by rw [mem_ordGe_iff, ord_tailGerm_self]⟩

private theorem leadCoeff_tailGermElt_ne_zero (d' : ℤ) :
    leadCoeff p (-d') (tailGermElt p d') ≠ 0 :=
  leadCoeff_tailGerm_self_ne_zero p (-d')

/-- The "subtract off the leading term" correction, landing (after correction) one order
higher — the raw (pre-quotient) map underlying the one-step splitting. -/
private noncomputable def rawCorr (d' : ℤ) :
    ordGe p (-d') →ₗ[ℂ] RS.MeroGermOn X ((chartAt ℂ p).source) :=
  (ordGe p (-d')).subtype -
    LinearMap.smulRight (leadCoeff p (-d')) ((leadCoeff p (-d') (tailGermElt p d'))⁻¹ •
      tailGerm p (-d'))

private theorem rawCorr_apply (d' : ℤ) (ψ : ordGe p (-d')) :
    rawCorr p d' ψ = (ψ : RS.MeroGermOn X ((chartAt ℂ p).source)) -
      leadCoeff p (-d') ψ • ((leadCoeff p (-d') (tailGermElt p d'))⁻¹ •
        tailGerm p (-d')) := rfl

private theorem mem_ordGe_succ_rawCorr (d' : ℤ) (ψ : ordGe p (-d')) :
    rawCorr p d' ψ ∈ ordGe p (-(d' - 1)) := by
  set c := leadCoeff p (-d') ψ with hc_def
  set lam := leadCoeff p (-d') (tailGermElt p d') with hlam_def
  have hlam0 : lam ≠ 0 := leadCoeff_tailGermElt_ne_zero p d'
  have hmem0 : rawCorr p d' ψ ∈ ordGe p (-d') := by
    rw [rawCorr_apply]
    apply Submodule.sub_mem
    · exact ψ.2
    · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (tailGermElt p d').2)
  have hcongr : (⟨rawCorr p d' ψ, hmem0⟩ : ordGe p (-d')) =
      ψ - (c * lam⁻¹) • tailGermElt p d' := by
    apply Subtype.ext
    change rawCorr p d' ψ = (ψ : RS.MeroGermOn X _) - (c * lam⁻¹) • tailGerm p (-d')
    rw [rawCorr_apply, smul_smul]
  have hleadzero : leadCoeff p (-d') (⟨rawCorr p d' ψ, hmem0⟩ : ordGe p (-d')) = 0 := by
    rw [hcongr, map_sub, map_smul, ← hlam_def, smul_eq_mul, ← hc_def]
    field_simp
    ring
  have hfin := (leadCoeff_eq_zero_iff p (-d') ⟨rawCorr p d' ψ, hmem0⟩).1 hleadzero
  rw [mem_ordGe_iff]
  have heq : ((-(d' - 1) : ℤ) : WithTop ℤ) = ((-d' + 1 : ℤ) : WithTop ℤ) := by
    congr 1; omega
  rw [heq]
  exact hfin

private theorem rawCorr_eq_of_leadCoeff_eq_zero (d' : ℤ) (ψ : ordGe p (-d'))
    (h0 : leadCoeff p (-d') ψ = 0) :
    rawCorr p d' ψ = (ψ : RS.MeroGermOn X ((chartAt ℂ p).source)) := by
  rw [rawCorr_apply, h0, zero_smul, sub_zero]

/-- The one-step correction map, landing in the window numerator one order higher. -/
private noncomputable def corrMap (d' : ℤ) : ordGe p (-d') →ₗ[ℂ] ordGe p (-(d' - 1)) :=
  LinearMap.codRestrict (ordGe p (-(d' - 1))) (rawCorr p d') (mem_ordGe_succ_rawCorr p d')

private theorem corrMap_apply_coe (d' : ℤ) (ψ : ordGe p (-d')) :
    (corrMap p d' ψ : RS.MeroGermOn X ((chartAt ℂ p).source)) = rawCorr p d' ψ := rfl

/-- The one-step splitting map `ordGe p (-d') → WindowAt p d (d'-1) × ℂ`. -/
private noncomputable def bigMap (d d' : ℤ) : ordGe p (-d') →ₗ[ℂ] WindowAt p d (d' - 1) × ℂ :=
  ((WindowAt.mk p d (d' - 1)).comp (corrMap p d')).prod (leadCoeff p (-d'))

private theorem bigMap_apply (d d' : ℤ) (ψ : ordGe p (-d')) :
    bigMap p d d' ψ = (WindowAt.mk p d (d' - 1) (corrMap p d' ψ), leadCoeff p (-d') ψ) := rfl

private theorem bigMap_mem_ker_iff (d d' : ℤ) (h : d ≤ d' - 1) (ψ : ordGe p (-d')) :
    bigMap p d d' ψ = 0 ↔ ψ ∈ (ordGe p (-d)).comap (ordGe p (-d')).subtype := by
  rw [Submodule.mem_comap, mem_ordGe_iff, bigMap_apply, Prod.mk_eq_zero]
  constructor
  · rintro ⟨hmk, hlc⟩
    rw [WindowAt.mk_eq_zero_iff, corrMap_apply_coe,
      rawCorr_eq_of_leadCoeff_eq_zero p d' ψ hlc] at hmk
    exact hmk
  · intro hord
    have hlc : leadCoeff p (-d') ψ = 0 := by
      rw [leadCoeff_eq_zero_iff]
      have h1 : ((-(d' - 1) : ℤ) : WithTop ℤ) ≤ ((-d : ℤ) : WithTop ℤ) := by
        exact_mod_cast (show -(d' - 1) ≤ -d by omega)
      have h2 : ((-d' + 1 : ℤ) : WithTop ℤ) = ((-(d' - 1) : ℤ) : WithTop ℤ) := by
        congr 1; omega
      rw [h2]
      exact h1.trans hord
    refine ⟨?_, hlc⟩
    rw [WindowAt.mk_eq_zero_iff, corrMap_apply_coe, rawCorr_eq_of_leadCoeff_eq_zero p d' ψ hlc]
    exact hord

private theorem bigMap_surjective (d d' : ℤ) : Function.Surjective (bigMap p d d') := by
  rintro ⟨χ, c⟩
  have hξsurj : Function.Surjective (WindowAt.mk p d (d' - 1)) := Submodule.mkQ_surjective _
  obtain ⟨ξ, hξχ⟩ := hξsurj χ
  set lam := leadCoeff p (-d') (tailGermElt p d') with hlam_def
  have hlam0 : lam ≠ 0 := leadCoeff_tailGermElt_ne_zero p d'
  have hξmem' : ((-d' : ℤ) : WithTop ℤ) ≤ (ξ : RS.MeroGermOn X ((chartAt ℂ p).source)).ord p := by
    have h1 : ((-d' : ℤ) : WithTop ℤ) ≤ ((-(d' - 1) : ℤ) : WithTop ℤ) := by
      exact_mod_cast (show -d' ≤ -(d' - 1) by omega)
    exact h1.trans ξ.2
  set ξ' : ordGe p (-d') := ⟨(ξ : RS.MeroGermOn X ((chartAt ℂ p).source)), mem_ordGe_iff.2 hξmem'⟩
    with hξ'_def
  set ψ : ordGe p (-d') := ξ' + (c * lam⁻¹) • tailGermElt p d' with hψ_def
  refine ⟨ψ, ?_⟩
  have hleadψ : leadCoeff p (-d') ψ = c := by
    rw [hψ_def, map_add, map_smul, ← hlam_def]
    have hleadξ' : leadCoeff p (-d') ξ' = 0 := by
      rw [leadCoeff_eq_zero_iff]
      change _ ≤ (ξ : RS.MeroGermOn X ((chartAt ℂ p).source)).ord p
      have h2 : ((-d' + 1 : ℤ) : WithTop ℤ) = ((-(d' - 1) : ℤ) : WithTop ℤ) := by
        congr 1; omega
      rw [h2]
      exact ξ.2
    rw [hleadξ', zero_add, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hlam0, mul_one]
  have hcorrψ : corrMap p d' ψ = ξ := by
    apply Subtype.ext
    rw [corrMap_apply_coe, rawCorr_apply, hleadψ, ← hlam_def]
    change (ξ' : RS.MeroGermOn X ((chartAt ℂ p).source)) +
        (c * lam⁻¹) • tailGerm p (-d') - c • (lam⁻¹ • tailGerm p (-d')) = _
    rw [smul_smul, add_sub_cancel_right, hξ'_def]
  rw [bigMap_apply, hleadψ, hcorrψ, hξχ]

private theorem bigMap_ker_eq (d d' : ℤ) (h : d ≤ d' - 1) :
    (ordGe p (-d)).comap (ordGe p (-d')).subtype = LinearMap.ker (bigMap p d d') := by
  apply Submodule.ext
  intro ψ
  rw [LinearMap.mem_ker]
  exact (bigMap_mem_ker_iff p d d' h ψ).symm

/-- The one-step splitting: `WindowAt p d d' ≃ₗ WindowAt p d (d'-1) × ℂ` (Forster/Miranda's
θ-basis induction step, packaged as an explicit `LinearEquiv` via `quotKerEquivRange` — no
independence/spanning argument needed). -/
private noncomputable def windowAtSuccEquiv (d d' : ℤ) (h : d ≤ d' - 1) :
    WindowAt p d d' ≃ₗ[ℂ] WindowAt p d (d' - 1) × ℂ :=
  (Submodule.quotEquivOfEq _ _ (bigMap_ker_eq p d d' h)).trans
    ((LinearMap.quotKerEquivRange (bigMap p d d')).trans
      (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 (bigMap_surjective p d d'))))

/-! ### The dimension count, by induction on `(d' - d).toNat` -/

private theorem finrank_windowAt_aux (p : X) (d : ℤ) (n : ℕ) :
    FiniteDimensional ℂ (WindowAt p d (d + n)) ∧
      Module.finrank ℂ (WindowAt p d (d + n)) = n := by
  induction n with
  | zero =>
    have heq0 : (d + ((0 : ℕ) : ℤ) : ℤ) = d := by norm_num
    rw [heq0]
    have hsub : Subsingleton (WindowAt p d d) := by
      refine ⟨fun a b => ?_⟩
      have hsurj : Function.Surjective (WindowAt.mk p d d) := Submodule.mkQ_surjective _
      obtain ⟨x, rfl⟩ := hsurj a
      obtain ⟨y, rfl⟩ := hsurj b
      have h1 := x.2
      have h2 := y.2
      rw [mem_ordGe_iff] at h1 h2
      have hneg : ((-d : ℤ) : WithTop ℤ) ≤
          (-(y : RS.MeroGermOn X ((chartAt ℂ p).source))).ord p := by
        rw [RS.MeroGermOn.ord_neg]
        exact h2
      have hxy : ((-d : ℤ) : WithTop ℤ) ≤ ((x : RS.MeroGermOn X ((chartAt ℂ p).source)) -
          (y : RS.MeroGermOn X ((chartAt ℂ p).source))).ord p := by
        rw [sub_eq_add_neg]
        calc ((-d : ℤ) : WithTop ℤ) = min ((-d : ℤ) : WithTop ℤ) ((-d : ℤ) : WithTop ℤ) := by
              simp
          _ ≤ min ((x : RS.MeroGermOn X ((chartAt ℂ p).source)).ord p)
              ((-(y : RS.MeroGermOn X ((chartAt ℂ p).source))).ord p) := min_le_min h1 hneg
          _ ≤ ((x : RS.MeroGermOn X ((chartAt ℂ p).source)) +
              (-(y : RS.MeroGermOn X ((chartAt ℂ p).source)))).ord p :=
            RS.MeroGermOn.ord_add (chartAt ℂ p).open_source (mem_chart_source ℂ p) _ _
      have hz : WindowAt.mk p d d (x - y) = 0 := by
        rw [WindowAt.mk_eq_zero_iff]
        exact hxy
      rw [map_sub] at hz
      exact sub_eq_zero.1 hz
    exact ⟨by have := hsub; infer_instance, Module.finrank_zero_of_subsingleton⟩
  | succ n ih =>
    obtain ⟨ihFD, ihFR⟩ := ih
    have := ihFD
    have hstep : d + ((n : ℕ) + 1 : ℕ) - 1 = d + (n : ℕ) := by push_cast; ring
    have hle : d ≤ d + ((n : ℕ) + 1 : ℕ) - 1 := by rw [hstep]; omega
    have hequiv := windowAtSuccEquiv p d (d + ((n : ℕ) + 1 : ℕ)) hle
    rw [hstep] at hequiv
    refine ⟨?_, ?_⟩
    · exact Module.Finite.equiv hequiv.symm
    · rw [LinearEquiv.finrank_eq hequiv, Module.finrank_prod, ihFR, Module.finrank_self]

theorem finrank_windowAt {p : X} {d d' : ℤ} (h : d ≤ d') :
    Module.finrank ℂ (WindowAt p d d') = (d' - d).toNat := by
  set n := (d' - d).toNat with hn_def
  have hcast : (n : ℤ) = d' - d := Int.toNat_of_nonneg (by omega)
  have hd' : d' = d + n := by omega
  rw [hd']
  exact (finrank_windowAt_aux p d n).2

theorem finiteDimensional_windowAt (p : X) {d d' : ℤ} (h : d ≤ d') :
    FiniteDimensional ℂ (WindowAt p d d') := by
  set n := (d' - d).toNat with hn_def
  have hcast : (n : ℤ) = d' - d := Int.toNat_of_nonneg (by omega)
  have hd' : d' = d + n := by omega
  rw [hd']
  exact (finrank_windowAt_aux p d n).1

/-! ### `finrank_window`: the global (Pi-of-windows) dimension count -/

/-- Registered explicitly (same reason as `Jacobian/Cech/Cochains.lean`'s `Z1`/`H1Cover`
instances): `Window D D' := ∀ q, WindowAt (q:X) (D q) (D' q)` is a Pi type, so its
`Module ℂ`/`Module.Free ℂ` structure needs these per-factor instances solved as a *dependent*
Pi-instance goal — the newer toolchain's `synthInstance` no longer reliably re-derives that from
`WindowAt`'s own (quotient) definition on demand. Supplying them once, directly, for the generic
`WindowAt p d d'` lets every downstream Pi-dependent lookup match verbatim instead of
re-deriving them. -/
noncomputable instance instAddCommGroupWindowAt (p : X) (d d' : ℤ) :
    AddCommGroup (WindowAt p d d') := inferInstance

noncomputable instance instModuleWindowAt (p : X) (d d' : ℤ) : Module ℂ (WindowAt p d d') :=
  inferInstance

noncomputable instance instModuleFreeWindowAt (p : X) (d d' : ℤ) :
    Module.Free ℂ (WindowAt p d d') := inferInstance

variable [T2Space X] [CompactSpace X]

theorem finiteDimensional_window (D D' : RS.Divisor X) (h : D ≤ D') :
    FiniteDimensional ℂ (Window D D') := by
  have : ∀ q : diffSupp D D', FiniteDimensional ℂ (WindowAt (q : X) (D q) (D' q)) := fun q =>
    finiteDimensional_windowAt (q : X) (Function.locallyFinsuppWithin.le_def.1 h q)
  exact Module.Finite.pi

theorem finrank_window {D D' : RS.Divisor X} (h : D ≤ D') :
    Module.finrank ℂ (Window D D') = ((D' - D).degree).toNat := by
  have hpt : ∀ q : diffSupp D D', (D : RS.Divisor X) q ≤ D' q := fun q =>
    Function.locallyFinsuppWithin.le_def.1 h q
  have : ∀ q : diffSupp D D', FiniteDimensional ℂ (WindowAt (q : X) (D q) (D' q)) := fun q =>
    finiteDimensional_windowAt (q : X) (hpt q)
  have hpi : Module.finrank ℂ (Window D D') =
      ∑ q : diffSupp D D', Module.finrank ℂ (WindowAt (q : X) (D q) (D' q)) :=
    Module.finrank_pi_fintype ℂ
  rw [hpi]
  have hsum1 : ∑ q : diffSupp D D', Module.finrank ℂ (WindowAt (q : X) (D q) (D' q)) =
      ∑ q : diffSupp D D', (D' q - D q).toNat :=
    Finset.sum_congr rfl (fun q _ => finrank_windowAt (hpt q))
  rw [hsum1]
  have hdegsub : (D' - D).support ⊆ (diffSupp D D' : Set X) := by
    intro x hx
    rw [Finset.mem_coe, mem_diffSupp_iff]
    intro hcontra
    apply hx
    rw [Divisor.sub_apply, hcontra, sub_self]
  have hdeg : (D' - D).degree = ∑ q ∈ diffSupp D D', (D' q - D q) := by
    rw [Function.locallyFinsuppWithin.degree_eq_sum_of_subset hdegsub]
    exact Finset.sum_congr rfl (fun q _ => Divisor.sub_apply D' D q)
  have hcast : ((∑ q : diffSupp D D', (D' q - D q).toNat : ℕ) : ℤ) = (D' - D).degree := by
    rw [hdeg]
    push_cast
    rw [Finset.sum_coe_sort (diffSupp D D') (fun q => ((D' q - D q).toNat : ℤ))]
    apply Finset.sum_congr rfl
    intro q hq
    exact Int.toNat_of_nonneg (sub_nonneg.2 (hpt ⟨q, hq⟩))
  have hnn : (0 : ℤ) ≤ (D' - D).degree := by
    apply Function.locallyFinsuppWithin.degree_nonneg_of_nonneg
    rw [sub_nonneg]
    exact h
  omega

end RS.Cech
