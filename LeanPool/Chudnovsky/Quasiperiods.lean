/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.WeierstrassMore
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# Quasiperiods and the Legendre relation

Statements from chapter 2 of Milla (arXiv:1809.00533v6, file `070_Quasiperiods.tex`):

* `PeriodPair.eta₁`, `PeriodPair.eta₂` : the basic quasiperiods `η₁ = 2ζ(ω₁/2)` and
  `η₂ = 2ζ(ω₂/2)` (paper Def. `defetak`; by oddness of `ζ`, `2ζ(ω_k/2)` equals
  `ζ(z+ω_k) - ζ(z)` for any `z ∉ L`);
* quasi-periodicity of `ζ` (paper `eta`, `defetak`);
* the **Legendre relation** `η₁ω₂ - η₂ω₁ = 2πi` (paper `legendre`) — the paper's residue
  computation implicitly uses a positively oriented basis, so we state it under the
  orientation hypothesis `0 < Im(ω₂/ω₁)`, which holds for `L = Lτ τ`;
* the bridge `η₁(L_τ) = G₂(τ)` to Mathlib's Eisenstein series `EisensteinSeries.G2`
  (the Eisenstein summation of `η₁`; with `G₂ = 2ζ(2)E₂` and `ζ(2) = π²/6` this is the
  paper's `η₁ = π²E₂/3` from Thm. `fouriertheorem`, proved in `Fourier.lean`).

All statements in this file are fully proved.
-/

noncomputable section

open scoped UpperHalfPlane

namespace PeriodPair

variable (L : PeriodPair)

/-- The first basic quasiperiod `η₁(L) = 2ζ(ω₁/2)` (paper Def. `defetak`; this equals
`ζ(z+ω₁) - ζ(z)` for every `z ∉ L`, see `weierstrassZeta_add_ω₁`). -/
def eta₁ : ℂ := 2 * L.weierstrassZeta (L.ω₁ / 2)

/-- The second basic quasiperiod `η₂(L) = 2ζ(ω₂/2)` (paper Def. `defetak`; this equals
`ζ(z+ω₂) - ζ(z)` for every `z ∉ L`, see `weierstrassZeta_add_ω₂`). -/
def eta₂ : ℂ := 2 * L.weierstrassZeta (L.ω₂ / 2)

/-- The lattice is a countable subset of `ℂ`. -/
private lemma countable_lattice : (↑L.lattice : Set ℂ).Countable := by
  have : Countable ↥L.lattice := countable_of_Lindelof_of_discrete
  simpa using Set.countable_range (Subtype.val : ↥L.lattice → ℂ)

/-- Quasi-periodicity of `ζ` in an arbitrary period direction `ω ∈ L` (with `ω/2 ∉ L`):
`ζ(z+ω) = ζ(z) + 2ζ(ω/2)` for `z ∉ L`. Both quasi-period statements are instances of this. -/
private theorem weierstrassZeta_add_period (ω : ℂ) (hω : ω ∈ L.lattice)
    (hω2 : ω / 2 ∉ L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassZeta (z + ω) = L.weierstrassZeta z + 2 * L.weierstrassZeta (ω / 2) := by
  have hopen : IsOpen ((↑L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hconn : IsPreconnected ((↑L.lattice : Set ℂ)ᶜ) :=
    (L.countable_lattice.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have hmem : ∀ {x : ℂ}, x ∉ L.lattice → x + ω ∉ L.lattice := by
    intro x hx hc
    exact hx (by simpa using sub_mem hc hω)
  have hfdiff : DifferentiableOn ℂ (fun z ↦ L.weierstrassZeta (z + ω)) (↑L.lattice)ᶜ :=
    L.differentiableOn_weierstrassZeta.comp (by fun_prop) (fun x hx ↦ hmem hx)
  have hgdiff : DifferentiableOn ℂ
      (fun z ↦ L.weierstrassZeta z + 2 * L.weierstrassZeta (ω / 2)) (↑L.lattice)ᶜ :=
    L.differentiableOn_weierstrassZeta.add_const _
  have hderiv : (↑L.lattice : Set ℂ)ᶜ.EqOn
      (deriv (fun z ↦ L.weierstrassZeta (z + ω)))
      (deriv (fun z ↦ L.weierstrassZeta z + 2 * L.weierstrassZeta (ω / 2))) := by
    intro x hx
    have hx' : x ∉ L.lattice := hx
    have hxω : x + ω ∉ L.lattice := hmem hx'
    rw [deriv_comp_add_const, deriv_add_const, L.deriv_weierstrassZeta _ hxω,
      L.deriv_weierstrassZeta _ hx']
    congr 1
    exact L.weierstrassP_add_coe x ⟨ω, hω⟩
  have hx₀ : -(ω / 2) ∈ (↑L.lattice : Set ℂ)ᶜ := by
    change -(ω / 2) ∉ L.lattice
    intro hc
    exact hω2 (by simpa using neg_mem hc)
  have hval : L.weierstrassZeta (-(ω / 2) + ω)
      = L.weierstrassZeta (-(ω / 2)) + 2 * L.weierstrassZeta (ω / 2) := by
    rw [show -(ω / 2) + ω = ω / 2 by ring, L.weierstrassZeta_neg]
    ring
  exact hopen.eqOn_of_deriv_eq hconn hfdiff hgdiff hderiv hx₀ hval hz

/-- Quasi-periodicity of `ζ` in the direction `ω₁`: `ζ(z+ω₁) = ζ(z) + η₁` for `z ∉ L`
(paper `eta` and Def. `defetak`). -/
theorem weierstrassZeta_add_ω₁ (z : ℂ) (hz : z ∉ L.lattice) :
    L.weierstrassZeta (z + L.ω₁) = L.weierstrassZeta z + L.eta₁ :=
  L.weierstrassZeta_add_period L.ω₁ L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice hz

/-- Quasi-periodicity of `ζ` in the direction `ω₂`: `ζ(z+ω₂) = ζ(z) + η₂` for `z ∉ L`
(paper `eta` and Def. `defetak`). -/
theorem weierstrassZeta_add_ω₂ (z : ℂ) (hz : z ∉ L.lattice) :
    L.weierstrassZeta (z + L.ω₂) = L.weierstrassZeta z + L.eta₂ :=
  L.weierstrassZeta_add_period L.ω₂ L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice hz

/-- The `ζ`-function depends on the period pair only through the underlying lattice: two
period pairs with equal lattices have equal `ζ`. -/
private theorem weierstrassZeta_of_lattice_eq {L₁ L₂ : PeriodPair}
    (h : L₁.lattice = L₂.lattice) (z : ℂ) :
    L₁.weierstrassZeta z = L₂.weierstrassZeta z := by
  have hcoe : ∀ x : L₁.lattice, ((LinearEquiv.ofEq _ _ h x : L₂.lattice) : ℂ) = (x : ℂ) :=
    fun x => LinearEquiv.coe_ofEq_apply h x
  let e : {l : L₁.lattice // l ≠ 0} ≃ {l : L₂.lattice // l ≠ 0} :=
    (LinearEquiv.ofEq _ _ h).toEquiv.subtypeEquiv (fun a => by
      rw [ne_eq, ne_eq, ← Submodule.coe_eq_zero, ← Submodule.coe_eq_zero (p := L₂.lattice),
        LinearEquiv.coe_toEquiv, hcoe])
  change 1 / z + ∑' l : {l : L₁.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ)
      = 1 / z + ∑' l : {l : L₂.lattice // l ≠ 0}, weierstrassZetaTerm z (l.1 : ℂ)
  congr 1
  rw [← e.tsum_eq (fun m => weierstrassZetaTerm z (m.1 : ℂ))]
  exact tsum_congr (fun l => congrArg (weierstrassZetaTerm z) (hcoe l.1).symm)

/-- Two period pairs with the same periods are equal (the `indep` field is a proof). -/
private lemma periodPair_eq {L M : PeriodPair} (h₁ : L.ω₁ = M.ω₁) (h₂ : L.ω₂ = M.ω₂) : L = M := by
  obtain ⟨a, b, hab⟩ := L
  obtain ⟨c, d, hcd⟩ := M
  obtain rfl : a = c := h₁
  obtain rfl : b = d := h₂
  rfl

/-! ### A local copy of the scaling action `a • L`

The scaling action `a • L` and its transformation laws live in `Lattices.lean`, which imports
this file, so they are not available here. We replicate the small part we need as private
helpers. -/

/-- Local copy of `a • L` (see `PeriodPair.smul` in `Lattices.lean`). -/
private def smulPP (a : ℂˣ) (L : PeriodPair) : PeriodPair where
  ω₁ := a * L.ω₁
  ω₂ := a * L.ω₂
  indep := by
    have h := L.indep.map' (LinearMap.mulLeft ℝ (a : ℂ))
      (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ a.ne_zero))
    have hcomp : ⇑(LinearMap.mulLeft ℝ (a : ℂ)) ∘ ![L.ω₁, L.ω₂] =
        ![(a : ℂ) * L.ω₁, (a : ℂ) * L.ω₂] := by
      funext i; fin_cases i <;> simp
    rwa [hcomp] at h

@[simp] private lemma smulPP_ω₁ (a : ℂˣ) (L : PeriodPair) : (smulPP a L).ω₁ = a * L.ω₁ := rfl
@[simp] private lemma smulPP_ω₂ (a : ℂˣ) (L : PeriodPair) : (smulPP a L).ω₂ = a * L.ω₂ := rfl

private theorem mem_smulPP_lattice_iff (a : ℂˣ) (L : PeriodPair) (z : ℂ) :
    z ∈ (smulPP a L).lattice ↔ ∃ w ∈ L.lattice, z = a * w := by
  rw [mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m * L.ω₁ + n * L.ω₂, mem_lattice.mpr ⟨m, n, rfl⟩, ?_⟩
    rw [← h, smulPP_ω₁, smulPP_ω₂]; ring
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨m, n, rfl⟩ := mem_lattice.mp hw
    exact ⟨m, n, by rw [smulPP_ω₁, smulPP_ω₂]; ring⟩

private def smulPPLatticeEquiv (a : ℂˣ) (L : PeriodPair) : L.lattice ≃ (smulPP a L).lattice where
  toFun l := ⟨(a : ℂ) * l, (mem_smulPP_lattice_iff a L _).mpr ⟨(l : ℂ), l.2, rfl⟩⟩
  invFun z := ⟨(a : ℂ)⁻¹ * z, by
    obtain ⟨w, hw, hz⟩ := (mem_smulPP_lattice_iff a L _).mp z.2
    rw [hz, ← mul_assoc, inv_mul_cancel₀ a.ne_zero, one_mul]; exact hw⟩
  left_inv l := by
    apply Subtype.ext; simp only; rw [← mul_assoc, inv_mul_cancel₀ a.ne_zero, one_mul]
  right_inv z := by
    apply Subtype.ext; simp only; rw [← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]

@[simp] private lemma smulPPLatticeEquiv_coe (a : ℂˣ) (L : PeriodPair) (l : L.lattice) :
    ((smulPPLatticeEquiv a L l : (smulPP a L).lattice) : ℂ) = (a : ℂ) * (l : ℂ) := rfl

private def smulPPLatticeEquiv' (a : ℂˣ) (L : PeriodPair) :
    {l : L.lattice // l ≠ 0} ≃ {l : (smulPP a L).lattice // l ≠ 0} :=
  (smulPPLatticeEquiv a L).subtypeEquiv fun l => by
    have ha : (a : ℂ) ≠ 0 := a.ne_zero
    simp only [ne_eq, ← Submodule.coe_eq_zero, smulPPLatticeEquiv_coe, mul_eq_zero, ha, false_or]

@[simp] private lemma smulPPLatticeEquiv'_coe (a : ℂˣ) (L : PeriodPair)
    (l : {l : L.lattice // l ≠ 0}) :
    (((smulPPLatticeEquiv' a L l).1 : (smulPP a L).lattice) : ℂ)
      = (a : ℂ) * ((l : L.lattice) : ℂ) :=
  rfl

private lemma zetaTerm_scale {c : ℂ} (hc : c ≠ 0) {w : ℂ} (hw : w ≠ 0) (z : ℂ) :
    weierstrassZetaTerm (c * z) (c * w) = c⁻¹ * weierstrassZetaTerm z w := by
  have hcw : c * w ≠ 0 := mul_ne_zero hc hw
  unfold weierstrassZetaTerm
  by_cases hzw : z = w
  · subst hzw
    simp only [sub_self, div_zero, zero_add]
    field_simp
  · have h1 : c * z - c * w ≠ 0 := by
      rw [← mul_sub]; exact mul_ne_zero hc (sub_ne_zero.mpr hzw)
    have h2 : z - w ≠ 0 := sub_ne_zero.mpr hzw
    field_simp

/-- Local copy of `weierstrassZeta_smul` from `Lattices.lean`. -/
private theorem weierstrassZeta_smulPP (a : ℂˣ) (L : PeriodPair) (z : ℂ) :
    (smulPP a L).weierstrassZeta ((a : ℂ) * z) = (a : ℂ)⁻¹ * L.weierstrassZeta z := by
  rw [weierstrassZeta, weierstrassZeta, mul_add, ← (smulPPLatticeEquiv' a L).tsum_eq,
      ← tsum_mul_left]
  congr 1
  · simp only [one_div, mul_inv]
  · refine tsum_congr fun l => ?_
    rw [smulPPLatticeEquiv'_coe]
    exact zetaTerm_scale a.ne_zero (Submodule.coe_eq_zero.not.mpr l.2) z

private lemma eta₁_smulPP (a : ℂˣ) (L : PeriodPair) : (smulPP a L).eta₁ = (a : ℂ)⁻¹ * L.eta₁ := by
  rw [eta₁, eta₁, smulPP_ω₁, show (a : ℂ) * L.ω₁ / 2 = (a : ℂ) * (L.ω₁ / 2) from by ring,
      weierstrassZeta_smulPP]
  ring

private lemma eta₂_smulPP (a : ℂˣ) (L : PeriodPair) : (smulPP a L).eta₂ = (a : ℂ)⁻¹ * L.eta₂ := by
  rw [eta₂, eta₂, smulPP_ω₂, show (a : ℂ) * L.ω₂ / 2 = (a : ℂ) * (L.ω₂ / 2) from by ring,
      weierstrassZeta_smulPP]
  ring

section eta₁_G2_bridge

open Chudnovsky EisensteinSeries Complex Filter Topology UpperHalfPlane SummationFilter Finset

/-- Auxiliary telescoping identity for the Eisenstein-summation bridge. For fixed `m`, the
family `n ↦ 1/(z+1-mτ-n) - 1/(z-mτ-n)` (the `m`-th row of the difference `ζ(z+1) - ζ(z)`
after subtracting the Eisenstein term `1/(mτ+n)²`) telescopes to `0` along symmetric
intervals. -/
private lemma hasSum_symmetricIco_D (τ : ℍ) (z : ℂ) (m : ℤ) :
    HasSum (fun n : ℤ => 1 / (z + 1 - (m : ℂ) * τ - n) - 1 / (z - (m : ℂ) * τ - n)) 0
      (symmetricIco ℤ) := by
  rw [hasSum_symmetricIco_int_iff]
  set C : ℂ := z + 1 - (m : ℂ) * τ with hC
  set f : ℤ → ℂ := fun k => 1 / (C - (k : ℂ)) with hf
  have hterm : ∀ n : ℤ,
      (1 / (z + 1 - (m : ℂ) * τ - (n : ℂ)) - 1 / (z - (m : ℂ) * τ - (n : ℂ)))
        = f n - f (n + 1) := by
    intro n
    simp only [hf, hC]
    push_cast
    ring_nf
  have hpart : ∀ N : ℕ,
      (∑ n ∈ Ico (-(N : ℤ)) (N : ℤ),
        (1 / (z + 1 - (m : ℂ) * τ - (n : ℂ)) - 1 / (z - (m : ℂ) * τ - (n : ℂ))))
        = 1 / (1 * C + (N : ℂ)) - 1 / (1 * C - (N : ℂ)) := by
    intro N
    rw [Finset.sum_congr rfl (fun n _ => hterm n), sum_Ico_int_sub N f]
    simp only [hf]
    push_cast
    ring_nf
  refine (tendsto_congr hpart).mpr ?_
  have h1 := tendsto_zero_inv_linear C 1
  have h2 := tendsto_zero_inv_linear_sub C 1
  simpa using h1.sub h2

/-- The reindexing equivalence `ℤ × ℤ ≃ (L_τ).lattice`, `(m,n) ↦ m·τ + n`. -/
private def bridgeEqv (τ : ℍ) : ℤ × ℤ ≃ (Lτ τ).lattice :=
  (Equiv.prodComm ℤ ℤ).trans (Lτ τ).latticeEquivProd.symm.toEquiv

private lemma bridgeEqv_coe (τ : ℍ) (p : ℤ × ℤ) :
    ((bridgeEqv τ p : (Lτ τ).lattice) : ℂ) = (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ) := by
  have h1 : (bridgeEqv τ p : (Lτ τ).lattice) = (Lτ τ).latticeEquivProd.symm (p.2, p.1) := rfl
  rw [h1, latticeEquiv_symm_apply, Lτ_ω₁, Lτ_ω₂]
  push_cast; ring

private lemma bridgeEqv_zero (τ : ℍ) : bridgeEqv τ (0 : ℤ × ℤ) = 0 := by
  apply Subtype.ext
  have he0 : ((bridgeEqv τ (0 : ℤ × ℤ) : (Lτ τ).lattice) : ℂ) = 0 := by
    simpa using bridgeEqv_coe τ (0 : ℤ × ℤ)
  rw [he0]; simp

private lemma bridgeEqv_ne (τ : ℍ) (p : ℤ × ℤ) : p ≠ 0 ↔ bridgeEqv τ p ≠ 0 := by
  rw [← bridgeEqv_zero τ]
  exact ((bridgeEqv τ).injective.eq_iff).not.symm

/-- The abstract summand family `F(m,n) = ζ-term(z+1) - ζ-term(z)` at the lattice point
`m·τ + n`, used in the Eisenstein-summation bridge. -/
private def bridgeF (τ : ℍ) (z : ℂ) (p : ℤ × ℤ) : ℂ :=
  weierstrassZetaTerm (z + 1) ((p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ))
    - weierstrassZetaTerm z ((p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ))

/-- Pointwise decomposition of `bridgeF` into a telescoping difference plus the Eisenstein
term `1/(mτ+n)²`. -/
private lemma bridgeF_eq (τ : ℍ) (z : ℂ) (p : ℤ × ℤ) :
    bridgeF τ z p =
      (1 / (z + 1 - (p.1 : ℂ) * τ - p.2) - 1 / (z - (p.1 : ℂ) * τ - p.2))
        + eisSummand 2 ![p.1, p.2] τ := by
  have heis : eisSummand 2 ![p.1, p.2] τ = (((p.1 : ℂ) * τ + p.2) ^ 2)⁻¹ := by
    simp only [eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, zpow_neg, zpow_ofNat]
  simp only [bridgeF, weierstrassZetaTerm]
  rw [heis]
  ring

/-- Summability of the (eqv-indexed) summand family over the nonzero indices `{p ≠ 0}`. This
is the analytic core of the summability of `bridgeF`; kept separate so it elaborates within the
default heartbeat budget. -/
private lemma bridgeF_summable_subtype (τ : ℍ) {z : ℂ}
    (hz : z ∉ (Lτ τ).lattice) (hz1 : z + 1 ∉ (Lτ τ).lattice) :
    Summable (fun pp : {p : ℤ × ℤ // p ≠ 0} =>
      weierstrassZetaTerm (z + 1) ((bridgeEqv τ pp.1 : (Lτ τ).lattice) : ℂ)
        - weierstrassZetaTerm z ((bridgeEqv τ pp.1 : (Lτ τ).lattice) : ℂ)) := by
  have hGl_sum : Summable (fun l : {l : (Lτ τ).lattice // l ≠ 0} =>
      weierstrassZetaTerm (z + 1) (l.1 : ℂ) - weierstrassZetaTerm z (l.1 : ℂ)) :=
    (summable_weierstrassZetaTerm (Lτ τ) (z + 1) hz1).sub
      (summable_weierstrassZetaTerm (Lτ τ) z hz)
  exact ((bridgeEqv τ).subtypeEquiv (bridgeEqv_ne τ)).summable_iff.mpr hGl_sum

/-- `bridgeF τ z` is summable over `ℤ × ℤ` (for a base point `z ∉ L_τ` with `z+1 ∉ L_τ`). -/
private lemma bridgeF_summable (τ : ℍ) {z : ℂ}
    (hz : z ∉ (Lτ τ).lattice) (hz1 : z + 1 ∉ (Lτ τ).lattice) :
    Summable (bridgeF τ z) := by
  have hFsum_sub := bridgeF_summable_subtype τ hz hz1
  have hFsum : Summable (fun p : ℤ × ℤ =>
      weierstrassZetaTerm (z + 1) ((bridgeEqv τ p : (Lτ τ).lattice) : ℂ)
        - weierstrassZetaTerm z ((bridgeEqv τ p : (Lτ τ).lattice) : ℂ)) := by
    rw [← Finset.summable_compl_iff ({0} : Finset (ℤ × ℤ))]
    exact (Equiv.subtypeEquivRight (fun x => by simp)).summable_iff.mpr hFsum_sub
  refine hFsum.congr (fun p => ?_)
  simp only [bridgeF, bridgeEqv_coe]

/-- `η₁(L_τ)` written as the absolutely convergent sum of `bridgeF` over `ℤ × ℤ`. -/
private lemma bridgeF_eta₁_eq_tsum (τ : ℍ) {z : ℂ}
    (hz : z ∉ (Lτ τ).lattice) (hz1 : z + 1 ∉ (Lτ τ).lattice) :
    (Lτ τ).eta₁ = ∑' p : ℤ × ℤ, bridgeF τ z p := by
  set F : ℤ × ℤ → ℂ := fun p =>
    weierstrassZetaTerm (z + 1) ((bridgeEqv τ p : (Lτ τ).lattice) : ℂ)
      - weierstrassZetaTerm z ((bridgeEqv τ p : (Lτ τ).lattice) : ℂ) with hFdef
  have hreindex : (∑' pp : {p : ℤ × ℤ // p ≠ 0}, F pp.1)
      = ∑' l : {l : (Lτ τ).lattice // l ≠ 0},
          (weierstrassZetaTerm (z + 1) (l.1 : ℂ) - weierstrassZetaTerm z (l.1 : ℂ)) :=
    Equiv.tsum_eq ((bridgeEqv τ).subtypeEquiv (bridgeEqv_ne τ))
      (fun l : {l : (Lτ τ).lattice // l ≠ 0} =>
        weierstrassZetaTerm (z + 1) (l.1 : ℂ) - weierstrassZetaTerm z (l.1 : ℂ))
  have hFsum : Summable F :=
    (bridgeF_summable τ hz hz1).congr (fun p => by simp only [hFdef, bridgeF, bridgeEqv_coe])
  have hF0 : F 0 = 1 / (z + 1) - 1 / z := by
    simp only [hFdef]
    rw [show ((bridgeEqv τ (0 : ℤ × ℤ) : (Lτ τ).lattice) : ℂ) = 0 from by
      simpa using bridgeEqv_coe τ (0 : ℤ × ℤ)]
    simp [weierstrassZetaTerm]
  have hZeta : ∀ a : ℂ,
      (Lτ τ).weierstrassZeta a
        = 1 / a + ∑' l : {l : (Lτ τ).lattice // l ≠ 0}, weierstrassZetaTerm a (l.1 : ℂ) :=
    fun a => rfl
  have heta_diff : (Lτ τ).eta₁ = (Lτ τ).weierstrassZeta (z + 1) - (Lτ τ).weierstrassZeta z := by
    have h := (Lτ τ).weierstrassZeta_add_ω₁ z hz
    rw [Lτ_ω₁] at h
    rw [h]; ring
  have heta : (Lτ τ).eta₁ = F 0 + ∑' pp : {p : ℤ × ℤ // p ≠ 0}, F pp.1 := by
    rw [heta_diff, hZeta, hZeta, hreindex, hF0]
    rw [Summable.tsum_sub (summable_weierstrassZetaTerm (Lτ τ) (z + 1) hz1)
      (summable_weierstrassZetaTerm (Lτ τ) z hz)]
    ring
  have hsubtype :
      (∑' pp : {p : ℤ × ℤ // p ≠ 0}, F pp.1) = ∑' p : ℤ × ℤ, if p = 0 then 0 else F p := by
    rw [show (∑' pp : {p : ℤ × ℤ // p ≠ 0}, F pp.1)
          = ∑' x : ↥{p : ℤ × ℤ | p ≠ 0}, F ↑x from rfl, _root_.tsum_subtype]
    apply tsum_congr
    intro p
    by_cases hp : p = 0 <;> simp [Set.indicator, hp]
  have heta_full : (Lτ τ).eta₁ = ∑' p : ℤ × ℤ, F p := by
    rw [heta, hsubtype]
    exact (Summable.tsum_eq_add_tsum_ite hFsum 0).symm
  rw [heta_full]
  refine tsum_congr (fun p => ?_)
  simp only [hFdef, bridgeF, bridgeEqv_coe]

/-- Each `m`-th row of `bridgeF` sums to `e2Summand m τ`: the telescoping difference sums to
`0` (`hasSum_symmetricIco_D`), leaving the Eisenstein row `∑'_n 1/(mτ+n)²`. -/
private lemma bridgeF_row (τ : ℍ) {z : ℂ}
    (hz : z ∉ (Lτ τ).lattice) (hz1 : z + 1 ∉ (Lτ τ).lattice) (m : ℤ) :
    (∑' n : ℤ, bridgeF τ z (m, n)) = e2Summand m τ := by
  have hFsum := bridgeF_summable τ hz hz1
  have hEsum : Summable (fun n : ℤ => eisSummand 2 ![m, n] τ) := e2Summand_summable m τ
  have hDsum : Summable (fun n : ℤ =>
      1 / (z + 1 - (m : ℂ) * τ - n) - 1 / (z - (m : ℂ) * τ - n)) := by
    refine ((hFsum.prod_factor m).sub hEsum).congr (fun n => ?_)
    rw [bridgeF_eq τ z (m, n)]; ring
  have hDtsum : (∑' n : ℤ, (1 / (z + 1 - (m : ℂ) * τ - n) - 1 / (z - (m : ℂ) * τ - n))) = 0 := by
    rw [← tsum_eq_of_summable_unconditional (L := symmetricIco ℤ) hDsum]
    exact (hasSum_symmetricIco_D τ z m).tsum_eq
  rw [tsum_congr (fun n => bridgeF_eq τ z (m, n)), Summable.tsum_add hDsum hEsum, hDtsum, zero_add]
  rfl

/-- The Eisenstein-summation bridge `η₁(L_τ) = G₂(τ)` (see `Chudnovsky.eta₁_Lτ_eq_G2`).
Stated here as a private lemma so it can be used in the general Legendre relation.

Proof outline. Writing `η₁ = ζ(z+1) - ζ(z)` (for any `z ∉ L_τ`) as one absolutely convergent
lattice sum and reindexing the lattice by `(m,n) ↦ m·τ + n`, each summand splits as
`F(m,n) = D(m,n) + 1/(mτ+n)²`, where `D` is the telescoping difference
`1/(z+1-mτ-n) - 1/(z-mτ-n)`. Since `F` is absolutely summable over `ℤ²`, Fubini gives
`η₁ = ∑'_m ∑'_n F(m,n)`; the inner `D`-row telescopes to `0` (`hasSum_symmetricIco_D`), so
`∑'_n F(m,n) = ∑'_n 1/(mτ+n)² = e2Summand m τ`. As the outer sum is now absolutely
convergent, it agrees with `G₂`'s symmetric-interval value `∑'[symmetricIcc ℤ] m, e2Summand m τ`. -/
private theorem eta₁_Lτ_eq_G2_aux (τ : ℍ) : (Lτ τ).eta₁ = G2 τ := by
  set z : ℂ := -1 / 2 with hzdef
  have hz : z ∉ (Lτ τ).lattice := by
    have h12 : (1 : ℂ) / 2 ∉ (Lτ τ).lattice := by
      have := (Lτ τ).ω₁_div_two_notMem_lattice; rwa [Lτ_ω₁] at this
    intro h
    apply h12
    have : (1 : ℂ) / 2 = -z := by rw [hzdef]; ring
    rw [this]; exact neg_mem h
  have hone : (1 : ℂ) ∈ (Lτ τ).lattice := by rw [← Lτ_ω₁ τ]; exact (Lτ τ).ω₁_mem_lattice
  have hz1 : z + 1 ∉ (Lτ τ).lattice := by
    intro h
    exact hz (by
      have : z = (z + 1) - 1 := by ring
      rw [this]; exact sub_mem h hone)
  have hFsum : Summable (bridgeF τ z) := bridgeF_summable τ hz hz1
  have hEouter : Summable (fun m : ℤ => e2Summand m τ) :=
    (hFsum.prod).congr (fun m => bridgeF_row τ hz hz1 m)
  rw [bridgeF_eta₁_eq_tsum τ hz hz1,
    Summable.tsum_prod' hFsum (fun m => hFsum.prod_factor m),
    tsum_congr (fun m => bridgeF_row τ hz hz1 m),
    show G2 τ = ∑'[symmetricIcc ℤ] (m : ℤ), e2Summand m τ from rfl]
  exact (tsum_eq_of_summable_unconditional hEouter).symm

end eta₁_G2_bridge

open Chudnovsky EisensteinSeries in
/-- Legendre's relation for `L_τ`, proved directly from the `G₂` transformation law, so that
the general Legendre relation can be reduced to it by scaling. -/
private theorem legendre_Lτ_aux (τ : ℍ) :
    (Lτ τ).eta₁ * (τ : ℂ) - (Lτ τ).eta₂ = 2 * (Real.pi : ℂ) * Complex.I := by
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  -- The unit `u = τ⁻¹`.
  set u : ℂˣ := Units.mk0 (τ : ℂ)⁻¹ (inv_ne_zero hτ0) with hudef
  have huval : (u : ℂ) = (τ : ℂ)⁻¹ := Units.val_mk0 _
  -- Coordinate of `S • τ`.
  have hSτ : ((ModularGroup.S • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  -- The lattices of `L_{S•τ}` and `u • L_τ` coincide.
  have hlat : (Lτ (ModularGroup.S • τ)).lattice = (smulPP u (Lτ τ)).lattice := by
    apply Submodule.ext
    intro z
    rw [PeriodPair.mem_lattice, PeriodPair.mem_smulPP_lattice_iff]
    simp only [Chudnovsky.Lτ_ω₁, Chudnovsky.Lτ_ω₂, hSτ, huval]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨(-(n : ℂ)) + (m : ℂ) * (τ : ℂ),
        PeriodPair.mem_lattice.mpr ⟨-n, m, by push_cast; simp [Chudnovsky.Lτ_ω₁, Chudnovsky.Lτ_ω₂]⟩,
        ?_⟩
      field_simp
      ring
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hw
      refine ⟨n, -m, ?_⟩
      simp only [Chudnovsky.Lτ_ω₁, Chudnovsky.Lτ_ω₂]
      push_cast
      field_simp
      ring
  -- `(u • L_τ) ζ` at `1/2` equals `τ · ζ_{L_τ}(τ/2)`.
  have hz : (u : ℂ) * ((τ : ℂ) / 2) = 1 / 2 := by
    rw [huval]; field_simp
  have hsmul := PeriodPair.weierstrassZeta_smulPP u (Lτ τ) ((τ : ℂ) / 2)
  rw [hz, huval, inv_inv] at hsmul
  -- Compute `η₁(L_{S•τ}) = τ · η₂(L_τ)`.
  have key1 : (Lτ (ModularGroup.S • τ)).eta₁ = (τ : ℂ) * (Lτ τ).eta₂ := by
    simp only [PeriodPair.eta₁, PeriodPair.eta₂, Chudnovsky.Lτ_ω₁, Chudnovsky.Lτ_ω₂]
    rw [PeriodPair.weierstrassZeta_of_lattice_eq hlat, hsmul]
    ring
  -- Bridge to `G₂` and apply the transformation law.
  have hG2S : G2 (ModularGroup.S • τ) = (τ : ℂ) * (Lτ τ).eta₂ := by
    rw [← eta₁_Lτ_eq_G2_aux (ModularGroup.S • τ), key1]
  have hSt := G2_S_transform τ
  rw [← eta₁_Lτ_eq_G2_aux τ, hG2S] at hSt
  -- `hSt : η₁(L_τ) = (τ²)⁻¹ (τ η₂(L_τ)) - -2πi/τ`.
  have key : (Lτ τ).eta₁ * (τ : ℂ) ^ 2
      = (τ : ℂ) * (Lτ τ).eta₂ + 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) := by
    rw [hSt]; field_simp; ring
  apply mul_right_cancel₀ hτ0
  rw [sub_mul]
  linear_combination key

/-- **Legendre's relation** (paper `legendre`): `η₁ω₂ - η₂ω₁ = 2πi` for a positively
oriented basis (`0 < Im(ω₂/ω₁)`; for the opposite orientation the right-hand side is
`-2πi`). -/
theorem legendre_relation (h : 0 < (L.ω₂ / L.ω₁).im) :
    L.eta₁ * L.ω₂ - L.eta₂ * L.ω₁ = 2 * (Real.pi : ℂ) * Complex.I := by
  have hω₁ : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  set τ : ℍ := ⟨L.ω₂ / L.ω₁, h⟩ with hτdef
  set u : ℂˣ := Units.mk0 L.ω₁ hω₁ with hudef
  have huval : (u : ℂ) = L.ω₁ := Units.val_mk0 _
  have hτc : (τ : ℂ) = L.ω₂ / L.ω₁ := rfl
  have hLeq : L = smulPP u (Chudnovsky.Lτ τ) := by
    apply PeriodPair.periodPair_eq
    · rw [PeriodPair.smulPP_ω₁, Chudnovsky.Lτ_ω₁, huval, mul_one]
    · rw [PeriodPair.smulPP_ω₂, Chudnovsky.Lτ_ω₂, huval, hτc]
      field_simp
  have he1 : L.eta₁ = (u : ℂ)⁻¹ * (Chudnovsky.Lτ τ).eta₁ := by
    rw [hLeq]; exact PeriodPair.eta₁_smulPP u (Chudnovsky.Lτ τ)
  have he2 : L.eta₂ = (u : ℂ)⁻¹ * (Chudnovsky.Lτ τ).eta₂ := by
    rw [hLeq]; exact PeriodPair.eta₂_smulPP u (Chudnovsky.Lτ τ)
  have hω2 : L.ω₂ = L.ω₁ * (τ : ℂ) := by rw [hτc]; field_simp
  have hlτ := PeriodPair.legendre_Lτ_aux τ
  have hrw : (u : ℂ)⁻¹ * (Chudnovsky.Lτ τ).eta₁ * ((u : ℂ) * (τ : ℂ))
      - (u : ℂ)⁻¹ * (Chudnovsky.Lτ τ).eta₂ * (u : ℂ)
      = (Chudnovsky.Lτ τ).eta₁ * (τ : ℂ) - (Chudnovsky.Lτ τ).eta₂ := by
    have hune : (u : ℂ) ≠ 0 := u.ne_zero
    field_simp
  rw [he1, he2, hω2, ← huval, hrw]
  exact hlτ

end PeriodPair

namespace Chudnovsky

open UpperHalfPlane EisensteinSeries

open scoped Real

/-- Legendre's relation for the lattice `L_τ = ℤ + ℤτ`: `η₁τ - η₂ = 2πi`
(paper `legendre` with `ω₁ = 1`, `ω₂ = τ`). -/
theorem legendre_Lτ (τ : ℍ) :
    (Lτ τ).eta₁ * τ - (Lτ τ).eta₂ = 2 * (π : ℂ) * Complex.I := by
  have h := (Lτ τ).legendre_relation (by simpa using τ.im_pos)
  simpa using h

/-- The first quasiperiod of `L_τ` is the weight-2 Eisenstein series `G₂` in its
Eisenstein summation order (Mathlib's `EisensteinSeries.G2`, summed over symmetric
intervals). Together with `G₂ = 2ζ(2)·E₂` and `ζ(2) = π²/6`, this is the paper's
`η₁(L_τ) = π²E₂(τ)/3` from Thm. `fouriertheorem` (see `Fourier.lean`). -/
theorem eta₁_Lτ_eq_G2 (τ : ℍ) : (Lτ τ).eta₁ = G2 τ :=
  PeriodPair.eta₁_Lτ_eq_G2_aux τ

end Chudnovsky
