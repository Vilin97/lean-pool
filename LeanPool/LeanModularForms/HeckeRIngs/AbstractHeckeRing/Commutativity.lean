/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.AbstractHeckeRing.Ring

/-!
# Hecke Rings: Commutativity via Anti-Involution

Shimura Proposition 3.8: if an arithmetic group pair admits an anti-automorphism
`ι : G →* Gᵐᵒᵖ` that preserves H and Δ and fixes every double coset, then the
Hecke ring `𝕋 P ℤ` is commutative.
-/

open MulOpposite Set DoubleCoset Subgroup Subgroup.Commensurable Finsupp

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G] (P : HeckePair G)

/-- An anti-involution of an HeckePair: `ι : G →* Gᵐᵒᵖ`,
involutive and preserving both `H` and `Δ`. -/
structure AntiInvolution where
  /-- The underlying anti-homomorphism `G →* Gᵐᵒᵖ`. -/
  toFun : G →* MulOpposite G
  involutive : ∀ g, (toFun (toFun g).unop).unop = g
  map_H : ∀ g, g ∈ P.H → (toFun g).unop ∈ P.H
  map_Δ : ∀ g, g ∈ P.Δ → (toFun g).unop ∈ P.Δ

variable {P}

namespace AntiInvolution

variable (ι : AntiInvolution P)

/-- The underlying function of the anti-involution, mapping `g` to `ι(g)` viewed in `G`. -/
def bar (g : G) : G := (ι.toFun g).unop

/-- The anti-involution is an involution: `bar(bar(g)) = g`. -/
@[simp] lemma bar_bar (g : G) : ι.bar (ι.bar g) = g := ι.involutive g

/-- The anti-involution reverses multiplication: `bar(ab) = bar(b) * bar(a)`. -/
lemma bar_mul (a b : G) : ι.bar (a * b) = ι.bar b * ι.bar a := by
  simp only [bar, map_mul, unop_mul]

/-- The anti-involution fixes the identity. -/
lemma bar_one : ι.bar 1 = 1 := by simp [bar]

/-- The anti-involution commutes with inversion. -/
lemma bar_inv (g : G) : ι.bar g⁻¹ = (ι.bar g)⁻¹ := by simp [bar]

/-- The anti-involution is injective. -/
lemma bar_injective : Function.Injective ι.bar := by
  intro a b h; have := congr_arg ι.bar h; simp only [bar_bar] at this; exact this

/-- The anti-involution preserves membership in `H`. -/
lemma bar_mem_H {g : G} (hg : g ∈ P.H) : ι.bar g ∈ P.H :=
  ι.map_H g hg

/-- The anti-involution preserves membership in `Δ`. -/
lemma bar_mem_Δ {g : G} (hg : g ∈ P.Δ) : ι.bar g ∈ P.Δ :=
  ι.map_Δ g hg

/-- The anti-involution preserves double coset equality. -/
lemma bar_doubleCoset_eq (g₁ g₂ : G)
    (h : DoubleCoset.doubleCoset g₁ P.H P.H =
      DoubleCoset.doubleCoset g₂ P.H P.H) :
    DoubleCoset.doubleCoset (ι.bar g₁) P.H P.H =
    DoubleCoset.doubleCoset (ι.bar g₂) P.H P.H := by
  have hmem := (DoubleCoset.eq P.H P.H _ _).mp
    (DoubleCoset.mk_eq_of_doubleCoset_eq h)
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := hmem
  have hbar : ι.bar g₂ = ι.bar h₂ * ι.bar g₁ * ι.bar h₁ := by
    rw [hprod, bar_mul, bar_mul, mul_assoc]
  rw [hbar]; symm; rw [mul_assoc]
  trans DoubleCoset.doubleCoset (ι.bar g₁ * ι.bar h₁) (P.H : Set G) P.H
  · exact doset_mul_left_eq_self P ⟨ι.bar h₂, ι.bar_mem_H hh₂⟩ _
  · exact DoubleCoset.doubleCoset_mul_right_eq_self P
      ⟨ι.bar h₁, ι.bar_mem_H hh₁⟩ _

/-- The induced action of the anti-involution on double cosets, defined via `Quotient.lift`. -/
noncomputable def onHeckeCoset (D : HeckeCoset P) : HeckeCoset P :=
  Quotient.lift (fun (g : P.Δ) =>
    (⟦⟨ι.bar (g : G), ι.bar_mem_Δ g.2⟩⟧ : HeckeCoset P))
    (fun a b (h : @Setoid.r _ (dcSetoid P) a b) => by
      rw [HeckeCoset.eq_iff]
      exact ι.bar_doubleCoset_eq _ _ h) D

/-- `onHeckeCoset ⟦g⟧` equals `⟦bar(g)⟧`. -/
lemma onHeckeCoset_mk (g : P.Δ) :
    ι.onHeckeCoset (⟦g⟧ : HeckeCoset P) =
    (⟦⟨ι.bar (g : G), ι.bar_mem_Δ g.2⟩⟧ : HeckeCoset P) := rfl

/-- The set underlying `onHeckeCoset D` is the double coset of the barred representative. -/
lemma onHeckeCoset_toSet (D : HeckeCoset P) :
    HeckeCoset.toSet (ι.onHeckeCoset D) =
    DoubleCoset.doubleCoset (ι.bar (HeckeCoset.rep D : G)) P.H P.H := by
  conv_lhs => rw [show D = ⟦HeckeCoset.rep D⟧ from (Quotient.out_eq D).symm]
  simp [onHeckeCoset_mk]

/-- The action on double cosets is involutive: `onHeckeCoset(onHeckeCoset(D)) = D`. -/
lemma onHeckeCoset_involutive : Function.Involutive ι.onHeckeCoset := by
  apply HeckeCoset.ind; intro g
  simp only [onHeckeCoset_mk]
  rw [HeckeCoset.eq_iff]; simp [bar_bar]

private lemma bar_mem_doubleCoset (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D)
    (D₀ : HeckeCoset P) (x : G) (hx : x ∈ HeckeCoset.toSet D₀) :
    ι.bar x ∈ HeckeCoset.toSet D₀ := by
  have h_set : HeckeCoset.toSet (ι.onHeckeCoset D₀) = HeckeCoset.toSet D₀ :=
    congr_arg HeckeCoset.toSet (h_fix D₀)
  rw [← h_set, onHeckeCoset_toSet]
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hx
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := hx
  rw [hprod, DoubleCoset.mem_doubleCoset]
  exact ⟨ι.bar h₂, ι.bar_mem_H hh₂, ι.bar h₁, ι.bar_mem_H hh₁, by
    simp [bar_mul, mul_assoc]⟩

private lemma bar_rep_mem_doubleCoset (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D)
    (D : HeckeCoset P) : ∃ h₁ h₂ : P.H,
    ι.bar (HeckeCoset.rep D : G) = h₁ * (HeckeCoset.rep D : G) * h₂ := by
  set g := (HeckeCoset.rep D : G)
  have hg_mem : g ∈ HeckeCoset.toSet D := HeckeCoset.rep_mem D
  have hbar : ι.bar g ∈ HeckeCoset.toSet D := bar_mem_doubleCoset ι h_fix D g hg_mem
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hbar
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := hbar
  exact ⟨⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩, heq⟩

/-- Given a right-coset product condition `{rep * g₁} * {j_rep * g₂} * H = {g_D} * H`,
    the element `g₁⁻¹ * rep⁻¹ * g_D` lies in the double coset of `D₂`. -/
private lemma inverse_product_mem_doubleCoset
    (g₁ g₂ g_D : G) (D₂ : HeckeCoset P)
    (hg₂ : g₂ = (HeckeCoset.rep D₂ : G))
    (rep : P.H) (j_rep : P.H)
    (hcond : ({(rep : G) * g₁} : Set G) * {(j_rep : G) * g₂} * P.H =
        {g_D} * (P.H : Set G)) :
    g₁⁻¹ * (rep : G)⁻¹ * g_D ∈ HeckeCoset.toSet D₂ := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  rw [hg₂] at hcond
  have hmem : (rep : G) * g₁ * ((j_rep : G) * (HeckeCoset.rep D₂ : G)) ∈
      ({g_D} : Set G) * ↑P.H := by
    have h1 : (rep : G) * g₁ * ((j_rep : G) * (HeckeCoset.rep D₂ : G)) ∈
        ({(rep : G) * g₁} : Set G) * {(j_rep : G) * (HeckeCoset.rep D₂ : G)} * ↑P.H :=
      ⟨_, ⟨_, rfl, _, rfl, rfl⟩, 1, P.H.one_mem, mul_one _⟩
    rwa [hcond] at h1
  obtain ⟨w, hw, k, hk, hprod⟩ := hmem
  rw [Set.mem_singleton_iff] at hw
  have hprod' : g_D * k =
      (rep : G) * g₁ * ((j_rep : G) * (HeckeCoset.rep D₂ : G)) := by
    rw [← hw]; exact hprod
  refine ⟨(j_rep : G), j_rep.2, k⁻¹, P.H.inv_mem hk, ?_⟩
  calc g₁⁻¹ * (rep : G)⁻¹ * g_D
      = g₁⁻¹ * (rep : G)⁻¹ *
          ((rep : G) * g₁ * ((j_rep : G) * (HeckeCoset.rep D₂ : G)) * k⁻¹) := by
        rw [show g_D = (rep : G) * g₁ *
            ((j_rep : G) * (HeckeCoset.rep D₂ : G)) * k⁻¹ from by
          calc g_D = g_D * k * k⁻¹ := by group
            _ = _ := by rw [hprod']]
    _ = (j_rep : G) * (HeckeCoset.rep D₂ : G) * k⁻¹ := by group

private lemma conj_mem_of_stabilizer (g : G)
    (n : ((ConjAct.toConjAct g • P.H).subgroupOf P.H)) :
    g⁻¹ * (n : G) * g ∈ P.H := by
  have := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at this
  simpa [ConjAct.ofConjAct_toConjAct] using this

private lemma bar_quotient_diff_mem_H
    (x₁ x₂ : G) (g₂ a₁ b₁ a₂ b₂ : G)
    (_ : a₁ ∈ (P.H : Set G)) (hb₁ : b₁ ∈ (P.H : Set G))
    (_ : a₂ ∈ (P.H : Set G)) (hb₂ : b₂ ∈ (P.H : Set G))
    (hbarx₁ : ι.bar x₁ = a₁ * g₂ * b₁)
    (hbarx₂ : ι.bar x₂ = a₂ * g₂ * b₂)
    (hconj : g₂⁻¹ * a₁⁻¹ * a₂ * g₂ ∈ P.H) :
    x₂ * x₁⁻¹ ∈ P.H := by
  have hbar_diff : (ι.bar x₁)⁻¹ * ι.bar x₂ =
      b₁⁻¹ * (g₂⁻¹ * a₁⁻¹ * a₂ * g₂) * b₂ := by rw [hbarx₁, hbarx₂]; group
  have hbar_diff_H : (ι.bar x₁)⁻¹ * ι.bar x₂ ∈ P.H := by
    rw [hbar_diff]; exact P.H.mul_mem (P.H.mul_mem (P.H.inv_mem hb₁) hconj) hb₂
  have hbar_factor : (ι.bar x₁)⁻¹ * ι.bar x₂ = ι.bar (x₂ * x₁⁻¹) := by
    rw [← ι.bar_inv, ← ι.bar_mul]
  have hbar_mem := hbar_factor ▸ hbar_diff_H
  have := ι.bar_bar (x₂ * x₁⁻¹); rw [← this]; exact ι.bar_mem_H hbar_mem

private lemma decompQuot_eq_of_conj_mem (g₁ : P.Δ)
    (i₁ i₂ : decompQuot P g₁) (g_D : G)
    (hxx_H : (((g₁ : G))⁻¹ * (i₂.out : G)⁻¹ * g_D) *
      (((g₁ : G))⁻¹ * (i₁.out : G)⁻¹ * g_D)⁻¹ ∈ P.H) :
    i₁ = i₂ := by
  have hxx_calc : (((g₁ : G))⁻¹ * (i₂.out : G)⁻¹ * g_D) *
      (((g₁ : G))⁻¹ * (i₁.out : G)⁻¹ * g_D)⁻¹ =
      ((g₁ : G))⁻¹ * (i₂.out : G)⁻¹ * (i₁.out : G) * ((g₁ : G)) := by group
  have hconj_H : ((g₁ : G))⁻¹ * (i₂.out : G)⁻¹ * (i₁.out : G) *
      ((g₁ : G)) ∈ P.H := hxx_calc ▸ hxx_H
  have hconj_H' : ((g₁ : G))⁻¹ * (i₁.out : G)⁻¹ * (i₂.out : G) * ((g₁ : G)) ∈ P.H := by
    have := P.H.inv_mem hconj_H; convert this using 1; group
  rw [show i₁ = ⟦i₁.out⟧ from (Quotient.out_eq' i₁).symm,
      show i₂ = ⟦i₂.out⟧ from (Quotient.out_eq' i₂).symm]
  rw [@Quotient.eq'', QuotientGroup.leftRel_apply,
    Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  convert hconj_H' using 1; simp [Subgroup.coe_mul]; group

private lemma conj_kernel_mem_of_stabilizer_mem
    (a₁ a₂ : P.H) (g₂ : G)
    (hrel : (a₁ : P.H)⁻¹ * a₂ ∈ (ConjAct.toConjAct g₂ • P.H).subgroupOf P.H) :
    g₂⁻¹ * (a₁ : G)⁻¹ * (a₂ : G) * g₂ ∈ P.H := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hrel
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv,
    Subgroup.coe_mul, Subgroup.coe_inv] at hrel
  have : g₂⁻¹ * (a₁ : G)⁻¹ * (a₂ : G) * g₂ =
      g₂⁻¹ * ((a₁ : G)⁻¹ * (a₂ : G)) * g₂ := by group
  rw [this]; exact hrel

private lemma fwd_inj_i (g₁ g₂ : P.Δ) (g_D : G)
    (i₁ i₂ : decompQuot P g₁)
    (a₁ : P.H) (b₁ : G) (hb₁ : b₁ ∈ (P.H : Set G))
    (hbarx₁_eq : ι.bar (((g₁ : G))⁻¹ * (i₁.out : G)⁻¹ * g_D) =
      (a₁ : G) * ((g₂ : G)) * b₁)
    (a₂ : P.H) (b₂ : G) (hb₂ : b₂ ∈ (P.H : Set G))
    (hbarx₂_eq : ι.bar (((g₁ : G))⁻¹ * (i₂.out : G)⁻¹ * g_D) =
      (a₂ : G) * ((g₂ : G)) * b₂)
    (hj'_eq : (⟦a₁⟧ : decompQuot P g₂) = ⟦a₂⟧) : i₁ = i₂ := by
  rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at hj'_eq
  have ha_kernel := conj_kernel_mem_of_stabilizer_mem a₁ a₂
    ((g₂ : G)) hj'_eq
  exact decompQuot_eq_of_conj_mem g₁ i₁ i₂ g_D
    (bar_quotient_diff_mem_H ι
      (((g₁ : G))⁻¹ * (i₁.out : G)⁻¹ * g_D) (((g₁ : G))⁻¹ * (i₂.out : G)⁻¹ * g_D)
      ((g₂ : G))
      (a₁ : G) b₁ (a₂ : G) b₂
      a₁.2 hb₁ a₂.2 hb₂ hbarx₁_eq hbarx₂_eq ha_kernel)

private lemma fwd_y_mem (g₁ g₂ g_D : G)
    (i_val : G) (hi : i_val ∈ (P.H : Set G))
    (a_val : G) (b_val : G) (hb : b_val ∈ (P.H : Set G))
    (hbarx_eq : ι.bar (g₁⁻¹ * i_val⁻¹ * g_D) = a_val * g₂ * b_val)
    (h1₁ h2₁ : P.H)
    (hbar₁' : ι.bar g₁ = (h1₁ : G) * g₁ * (h2₁ : G))
    (j'_val q₀_val h'_val : G)
    (hq₀_eq : q₀_val * g_D = ι.bar g_D * h'_val)
    (h'_mem : h'_val ∈ (P.H : Set G))
    (hn₂_val : G) (hn₂_mem : g₂⁻¹ * hn₂_val * g₂ ∈ P.H)
    (hj'_coe : j'_val = a_val * hn₂_val) :
    ∃ h₁ ∈ (P.H : Set G), ∃ h₂ ∈ (P.H : Set G),
      g₂⁻¹ * j'_val⁻¹ * q₀_val * g_D = h₁ * g₁ * h₂ := by
  have hab_eq : a_val * g₂ * b_val =
      ι.bar g_D * (ι.bar i_val)⁻¹ * (ι.bar g₁)⁻¹ := by
    have : ι.bar (g₁⁻¹ * i_val⁻¹ * g_D) =
        ι.bar g_D * (ι.bar i_val)⁻¹ * (ι.bar g₁)⁻¹ := by
      rw [ι.bar_mul, ι.bar_mul, ι.bar_inv, ι.bar_inv]; group
    rw [← this]; exact hbarx_eq.symm
  have key1 : g₂⁻¹ * a_val⁻¹ * ι.bar g_D =
      b_val * ι.bar g₁ * ι.bar i_val := by
    calc g₂⁻¹ * a_val⁻¹ * ι.bar g_D
        = g₂⁻¹ * a_val⁻¹ * (a_val * g₂ * b_val *
          (ι.bar g₁ * ι.bar i_val)) := by rw [hab_eq]; group
      _ = _ := by group
  have hy_calc : g₂⁻¹ * j'_val⁻¹ * q₀_val * g_D =
      (g₂⁻¹ * hn₂_val⁻¹ * g₂) *
      (b_val * ι.bar g₁ * ι.bar i_val) * h'_val := by
    rw [hj'_coe, show g₂⁻¹ * (a_val * hn₂_val)⁻¹ * q₀_val * g_D =
      g₂⁻¹ * (a_val * hn₂_val)⁻¹ * (q₀_val * g_D) from by group,
      hq₀_eq, ← key1]; group
  rw [hy_calc, hbar₁']
  exact ⟨(g₂⁻¹ * hn₂_val⁻¹ * g₂) * b_val * h1₁,
    P.H.mul_mem (P.H.mul_mem (by convert P.H.inv_mem hn₂_mem using 1; group) hb) h1₁.2,
    h2₁ * ι.bar i_val * h'_val,
    P.H.mul_mem (P.H.mul_mem h2₁.2 (ι.bar_mem_H hi)) h'_mem, by group⟩

private lemma fwd_pair_mem (g₁ : P.Δ) (g₂ g_D q₀_val : G)
    (j'_val : G) (c : P.H) (d_val : G) (hd : d_val ∈ (P.H : Set G))
    (hy_eq : g₂⁻¹ * j'_val⁻¹ * q₀_val * g_D = (c : G) * (g₁ : G) * d_val) :
    ({j'_val * g₂} : Set G) * {((⟦c⟧ : decompQuot P g₁).out : G) * (g₁ : G)} *
      ↑P.H = {q₀_val * g_D} * ↑P.H := by
  rw [Set.singleton_mul_singleton]
  obtain ⟨n₁, hn₁_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct ((g₁ : G)) • P.H).subgroupOf P.H) c
  have hn₁_coe : ((⟦c⟧ : decompQuot P g₁).out : G) = (c : G) * (n₁ : G) := by
    have := congr_arg (Subtype.val : ↥P.H → G) hn₁_eq
    simpa [Subgroup.coe_mul] using this
  have hn₁_conj : ((g₁ : G))⁻¹ * (n₁ : G) * ((g₁ : G)) ∈ P.H :=
    conj_mem_of_stabilizer ((g₁ : G)) n₁
  apply leftCoset_eq_of_not_disjoint; rw [@not_disjoint_iff]
  refine ⟨j'_val * g₂ * (((⟦c⟧ : decompQuot P g₁).out : G) * ((g₁ : G))),
    ⟨1, P.H.one_mem, by simp [smul_eq_mul]⟩, ?_⟩
  have h_prod_eq : j'_val * g₂ * ((c : G) * ((g₁ : G)) * d_val) =
      q₀_val * g_D := by rw [← hy_eq]; group
  refine ⟨d_val⁻¹ * (((g₁ : G))⁻¹ * (n₁ : G) * ((g₁ : G))),
    P.H.mul_mem (P.H.inv_mem hd) hn₁_conj, ?_⟩
  simp only [smul_eq_mul]; rw [hn₁_coe]
  have : q₀_val * g_D * d_val⁻¹ =
      j'_val * g₂ * ((c : G) * ((g₁ : G))) := by
    calc q₀_val * g_D * d_val⁻¹
        = j'_val * g₂ * ((c : G) * ((g₁ : G)) * d_val) * d_val⁻¹ := by
          rw [← h_prod_eq]
      _ = _ := by group
  calc q₀_val * g_D * (d_val⁻¹ * (((g₁ : G))⁻¹ * (n₁ : G) *
        ((g₁ : G))))
      = (q₀_val * g_D * d_val⁻¹) * (((g₁ : G))⁻¹ * (n₁ : G) *
        ((g₁ : G))) := by group
    _ = j'_val * g₂ * ((c : G) * ((g₁ : G))) *
        (((g₁ : G))⁻¹ * (n₁ : G) * ((g₁ : G))) := by rw [this]
    _ = j'_val * g₂ * ((c : G) * (n₁ : G) * ((g₁ : G))) := by group

private lemma heckeMultiplicity_le_comm (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D)
    (D₁ D₂ D : HeckeCoset P) :
    heckeMultiplicity P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (HeckeCoset.rep D) ≤
    heckeMultiplicity P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) (HeckeCoset.rep D) := by
  set g₁ := (HeckeCoset.rep D₁ : G)
  set g₂ := (HeckeCoset.rep D₂ : G)
  set g_D := (HeckeCoset.rep D : G)
  obtain ⟨h1D, h2D, hbarD⟩ := bar_rep_mem_doubleCoset ι h_fix D
  obtain ⟨h1₁, h2₁, hbar₁⟩ := bar_rep_mem_doubleCoset ι h_fix D₁
  set q₀ : decompQuot P (HeckeCoset.rep D) := ⟦⟨(h1D : G), h1D.2⟩⟧
  have hunif := heckeMultiplicity_uniform P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) D q₀
  unfold heckeMultiplicity; push_cast; rw [← hunif]; norm_cast
  have bar_mem_dc := bar_mem_doubleCoset ι h_fix
  let fwd : {⟨i, j⟩ : decompQuot P (HeckeCoset.rep D₁) ×
      decompQuot P (HeckeCoset.rep D₂) |
      ({(i.out : G) * g₁} : Set G) * {(j.out : G) * g₂} * P.H =
      {g_D} * (P.H : Set G)} →
    {p : decompQuot P (HeckeCoset.rep D₂) ×
      decompQuot P (HeckeCoset.rep D₁) |
      ({(p.1.out : G) * g₂} : Set G) * {(p.2.out : G) * g₁} * P.H =
      {(q₀.out : G) * g_D} * (P.H : Set G)} :=
    fun ⟨⟨i, j⟩, (hcond : _ = _)⟩ =>
    let x : G := g₁⁻¹ * (i.out : G)⁻¹ * g_D
    have hbarx_dc : ∃ h₁ ∈ (P.H : Set G), ∃ h₂ ∈ (P.H : Set G),
        ι.bar x = h₁ * g₂ * h₂ := by
      have := bar_mem_dc D₂ x (inverse_product_mem_doubleCoset g₁ g₂ g_D D₂ rfl
        i.out j.out hcond)
      rwa [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at this
    let a : P.H := ⟨hbarx_dc.choose, hbarx_dc.choose_spec.1⟩
    let j' : decompQuot P (HeckeCoset.rep D₂) := ⟦a⟧
    let b_val : G := hbarx_dc.choose_spec.2.choose
    have hb : b_val ∈ (P.H : Set G) := hbarx_dc.choose_spec.2.choose_spec.1
    have hy_mem_D₁ : g₂⁻¹ * (j'.out : G)⁻¹ * (q₀.out : G) * g_D ∈
        HeckeCoset.toSet D₁ := by
      rw [HeckeCoset.toSet_eq_rep]; change _ ∈ DoubleCoset.doubleCoset g₁ _ _
      rw [DoubleCoset.mem_doubleCoset]
      obtain ⟨h', hq₀_eq⟩ : ∃ h' : P.H, (q₀.out : G) * g_D =
          ι.bar g_D * (h' : G) := by
        obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_out_eq_mul
          ((ConjAct.toConjAct g_D • P.H).subgroupOf P.H) ⟨(h1D : G), h1D.2⟩
        have hn_coe : (q₀.out : G) = (h1D : G) * (n : G) := by
          simpa [Subgroup.coe_mul] using congr_arg (Subtype.val : ↥P.H → G) hn_eq
        have hn_conj : g_D⁻¹ * (n : G) * g_D ∈ P.H := conj_mem_of_stabilizer g_D n
        have hbarD' : ι.bar g_D = (h1D : G) * g_D * (h2D : G) := hbarD
        exact ⟨⟨(h2D : G)⁻¹ * (g_D⁻¹ * (n : G) * g_D),
          P.H.mul_mem (P.H.inv_mem h2D.2) hn_conj⟩, by rw [hn_coe, hbarD']; group⟩
      obtain ⟨n₂, hn₂_eq⟩ := QuotientGroup.mk_out_eq_mul
        ((ConjAct.toConjAct g₂ • P.H).subgroupOf P.H) a
      exact fwd_y_mem ι g₁ g₂ g_D (i.out : G) i.out.2 (a : G) b_val hb
        hbarx_dc.choose_spec.2.choose_spec.2 h1₁ h2₁ hbar₁
        (j'.out : G) (q₀.out : G) (h' : G) hq₀_eq h'.2 (n₂ : G)
        (conj_mem_of_stabilizer g₂ n₂)
        (by simpa [Subgroup.coe_mul] using congr_arg (Subtype.val : ↥P.H → G) hn₂_eq)
    have hy_dc : ∃ h₁ ∈ (P.H : Set G), ∃ h₂ ∈ (P.H : Set G),
        g₂⁻¹ * (j'.out : G)⁻¹ * (q₀.out : G) * g_D = h₁ * g₁ * h₂ := by
      rwa [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hy_mem_D₁
    let c : P.H := ⟨hy_dc.choose, hy_dc.choose_spec.1⟩
    (⟨⟨j', ⟦c⟧⟩, fwd_pair_mem (HeckeCoset.rep D₁) g₂ g_D (q₀.out : G)
      (j'.out : G) c
      hy_dc.choose_spec.2.choose hy_dc.choose_spec.2.choose_spec.1
      (hy_dc.choose_spec.2.choose_spec.2 ▸ rfl)⟩ :
      {p : decompQuot P (HeckeCoset.rep D₂) ×
        decompQuot P (HeckeCoset.rep D₁) |
      ({(p.1.out : G) * g₂} : Set G) * {(p.2.out : G) * g₁} * P.H =
      {(q₀.out : G) * g_D} * (P.H : Set G)})
  apply Nat.card_le_card_of_injective fwd
  intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩ heq
  have hj'_eq := congr_arg Prod.fst (congr_arg Subtype.val heq)
  have bar_dc (i' : decompQuot P (HeckeCoset.rep D₁))
      (j' : decompQuot P (HeckeCoset.rep D₂))
      (hc : ({(i'.out : G) * g₁} : Set G) * {(j'.out : G) * g₂} * ↑P.H =
        {g_D} * ↑P.H) : ∃ h₁ ∈ (P.H : Set G), ∃ h₂ ∈ (P.H : Set G),
      ι.bar (g₁⁻¹ * (i'.out : G)⁻¹ * g_D) = h₁ * g₂ * h₂ := by
    have := bar_mem_dc D₂ _ (inverse_product_mem_doubleCoset g₁ g₂ g_D D₂ rfl
      i'.out j'.out hc)
    rwa [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at this
  have hbarx₁_dc := bar_dc i₁ j₁ h₁; have hbarx₂_dc := bar_dc i₂ j₂ h₂
  change (⟦⟨hbarx₁_dc.choose, hbarx₁_dc.choose_spec.1⟩⟧ :
      decompQuot P (HeckeCoset.rep D₂)) =
    ⟦⟨hbarx₂_dc.choose, hbarx₂_dc.choose_spec.1⟩⟧ at hj'_eq
  have hi₁₂ : i₁ = i₂ := fwd_inj_i ι (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
    g_D i₁ i₂
    ⟨hbarx₁_dc.choose, hbarx₁_dc.choose_spec.1⟩
    hbarx₁_dc.choose_spec.2.choose hbarx₁_dc.choose_spec.2.choose_spec.1
    hbarx₁_dc.choose_spec.2.choose_spec.2
    ⟨hbarx₂_dc.choose, hbarx₂_dc.choose_spec.1⟩
    hbarx₂_dc.choose_spec.2.choose hbarx₂_dc.choose_spec.2.choose_spec.1
    hbarx₂_dc.choose_spec.2.choose_spec.2 hj'_eq
  subst hi₁₂
  have hj₁₂ : j₁ = j₂ := by
    by_contra hne; apply decompQuot_coset_diff P (HeckeCoset.rep D₂) j₁ j₂ hne
    exact (show ({(j₁.out : G) * g₂} : Set G) * ↑P.H =
        ({(j₂.out : G) * g₂} : Set G) * ↑P.H from
      set_singleton_mul_left_cancel ((i₁.out : G) * g₁)
        (by have h12 := h₁.trans h₂.symm; rwa [mul_assoc, mul_assoc] at h12))
  subst hj₁₂; rfl

/-- When the anti-involution fixes all double cosets,
the multiplicity is symmetric:
`heckeMultiplicity(D₁, D₂, D) = heckeMultiplicity(D₂, D₁, D)`
(Shimura Proposition 3.8). -/
lemma heckeMultiplicity_comm_of_onHeckeCoset_eq
    (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D)
    (D₁ D₂ D : HeckeCoset P) :
    heckeMultiplicity P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (HeckeCoset.rep D) =
    heckeMultiplicity P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) (HeckeCoset.rep D) :=
  le_antisymm (ι.heckeMultiplicity_le_comm h_fix D₁ D₂ D)
    (ι.heckeMultiplicity_le_comm h_fix D₂ D₁ D)

/-- When the anti-involution fixes all double cosets,
the multiplication finsupp is symmetric: `m(D₁, D₂) = m(D₂, D₁)`. -/
lemma m_comm_of_onHeckeCoset_eq (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D)
    (D₁ D₂ : HeckeCoset P) :
    m P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) =
    m P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) := by
  ext D; simp only [m]
  exact heckeMultiplicity_comm_of_onHeckeCoset_eq ι h_fix D₁ D₂ D

/-- Shimura Proposition 3.8: the Hecke ring is commutative when the anti-involution
fixes every double coset. -/
theorem mul_comm_of_antiInvolution (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D)
    (f g : 𝕋 P ℤ) : f * g = g * f := by
  apply induction_linear_𝕋 P f
  · rw [@zero_mul _ (instNonUnitalNonAssocSemiring P).toMulZeroClass,
        @mul_zero _ (instNonUnitalNonAssocSemiring P).toMulZeroClass]
  · intro D₁ a; apply induction_linear_𝕋 P g
    · rw [@zero_mul _ (instNonUnitalNonAssocSemiring P).toMulZeroClass,
          @mul_zero _ (instNonUnitalNonAssocSemiring P).toMulZeroClass]
    · intro D₂ b
      rw [T_single_mul_T_single, T_single_mul_T_single,
        m_comm_of_onHeckeCoset_eq ι h_fix D₁ D₂, smul_comm]
    · intro g₁ g₂ hg₁ hg₂; rw [mul_add, add_mul, hg₁, hg₂]
  · intro f₁ f₂ hf₁ hf₂; rw [add_mul, mul_add, hf₁, hf₂]

end AntiInvolution

/-- Shimura Proposition 3.8: `CommRing (𝕋 P ℤ)` from an anti-involution
fixing every double coset. -/
@[reducible]
noncomputable def instCommRingOfAntiInvolution (ι : AntiInvolution P)
    (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D) : CommRing (𝕋 P ℤ) :=
  { HeckeRing.instRing P with mul_comm := ι.mul_comm_of_antiInvolution h_fix }

end HeckeRing
