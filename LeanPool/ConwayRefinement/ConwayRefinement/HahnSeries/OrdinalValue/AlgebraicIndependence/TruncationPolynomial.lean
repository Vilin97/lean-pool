/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.Lifts
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Convolution
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.TruncationDrop
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.OrdinalExpansion
import Mathlib.Topology.Order.LeftRightNhds

/-!
# The polynomial of a translated truncation, and the convolution formula read in polynomials

Fix a minimal system of homogeneous generators `𝓑` of `P̂` with lifts `b_B`, a degree `α`, and
assume evaluation `K[X] → P̂` injective in every degree below `α`; `pol` then identifies the
classes modulo `J` of ordinal value below `ω^α` with the polynomials of degree below `α`
(`Lifts.pol_eq_of_toGerm_aeval_eq`). This file records the calculus of `pol`: it respects
congruence modulo `J`, sums, scalars, and products whose polynomial has degree below `α`; a series
of ordinal value below `ω^(β+1)` has polynomial of degree at most `β`.

Berarducci's convolution formula `(uv)^{|γ} ≡ ∑_ξ u^{|ξ} v^{|γ-ξ} (mod J)` [Ber00, Lem. 7.5] then
reads, for `u, v` of ordinal value below `ω^(β_u+1)`, `ω^(β_v+1)` with `β_u, β_v < α` and
`β_u ⊕ β_v ≤ α`, and all `γ < 0` sufficiently close to `0`, as the polynomial identity
`pol((uv)^{|γ}) = ∑_ξ pol(u^{|ξ}) · pol(v^{|γ-ξ})`
(`Lifts.exists_forall_pol_translatedTruncation_mul`). The sum may be taken over any finite set of
cutoffs containing Berarducci's index set and contained in `[γ, 0]`; the terms at `ξ = 0` and
`ξ = γ` are the boundary terms `pol(u) · pol(v^{|γ})` and `pol(u^{|γ}) · pol(v)`.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci MvPolynomial OrdinalGraded Filter Topology

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-! ### The quantifier "for all `γ < 0` sufficiently close to `0`" with an explicit `ε` -/

/-- A property holds for all `γ < 0` sufficiently close to `0` exactly when there is `ε > 0` such
that it holds for all `γ ∈ (-ε, 0)`. -/
theorem eventually_nhdsLT_zero_iff {p : ℝ → Prop} :
    (∀ᶠ γ in 𝓝[<] (0 : ℝ), p γ) ↔ ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 → p γ := by
  rw [Filter.eventually_iff, mem_nhdsLT_iff_exists_Ioo_subset]
  constructor
  · rintro ⟨l, hl, hsub⟩
    exact ⟨-l, by simpa using hl, fun γ h1 h2 ↦ hsub ⟨by linarith, h2⟩⟩
  · rintro ⟨ε, hε, h⟩
    exact ⟨-ε, by simpa using hε, fun γ hγ ↦ h γ hγ.1 hγ.2⟩

/-- If `v_J(u) < ω^(β+1)`, there is `ε > 0` such that `v_J(u^{|γ}) < ω^β` for all `γ ∈ (-ε, 0)`. -/
theorem exists_forall_ordinalValue_translatedTruncation_lt {β : NatOrdinal} {u : Series K}
    (hu : ordinalValue u < ω^ (β + 1)) :
    ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 →
      ordinalValue (translatedTruncation (u : K⟦ℝ⟧) γ) < ω^ β :=
  eventually_nhdsLT_zero_iff.mp
    (eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one β u hu)

/-- The translated truncation of a constant at a negative cutoff is zero. -/
theorem translatedTruncation_C_of_neg (k : K) {γ : ℝ} (hγ : γ < 0) :
    translatedTruncation (HahnSeries.C k : K⟦ℝ⟧) γ = 0 := by
  apply Subtype.ext
  ext δ
  rw [coeff_translatedTruncation, Subring.coe_zero, HahnSeries.coeff_zero]
  split_ifs with hδ
  · rw [HahnSeries.C_apply, HahnSeries.coeff_single, ite_eq_right (by linarith)]
  · rfl

/-! ### Degree at most `β` -/

variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

variable (wt) in
/-- Every monomial of `F` has degree at most `β`. -/
def DegreeLE (F : MvPolynomial ι K) (β : NatOrdinal) : Prop :=
  ∀ d ∈ F.support, Finsupp.weight wt d ≤ β

theorem degreeLE_iff {F : MvPolynomial ι K} {β : NatOrdinal} :
    DegreeLE wt F β ↔ ∀ d ∈ F.support, Finsupp.weight wt d ≤ β :=
  Iff.rfl

theorem degreeLT_add_one_iff_degreeLE {F : MvPolynomial ι K} {β : NatOrdinal} :
    DegreeLT wt F (β + 1) ↔ DegreeLE wt F β := by
  rw [degreeLT_iff, degreeLE_iff]
  exact forall₂_congr fun _ _ ↦ Order.lt_add_one_iff

theorem DegreeLE.degreeLT {F : MvPolynomial ι K} {β α : NatOrdinal} (hF : DegreeLE wt F β)
    (h : β < α) : DegreeLT wt F α :=
  degreeLT_iff.mpr fun d hd ↦ (hF d hd).trans_lt h

theorem DegreeLT.degreeLE {F : MvPolynomial ι K} {β : NatOrdinal} (hF : DegreeLT wt F β) :
    DegreeLE wt F β := fun d hd ↦ (degreeLT_iff.mp hF d hd).le

theorem _root_.MvPolynomial.IsWeightedHomogeneous.degreeLE {F : MvPolynomial ι K}
    {β : NatOrdinal} (hF : IsWeightedHomogeneous wt F β) : DegreeLE wt F β :=
  fun _ hd ↦ (hF (mem_support_iff.mp hd)).le

theorem DegreeLE.mul {F G : MvPolynomial ι K} {β β' : NatOrdinal} (hF : DegreeLE wt F β)
    (hG : DegreeLE wt G β') : DegreeLE wt (F * G) (β + β') := by
  classical
  intro d hd
  obtain ⟨d1, hd1, d2, hd2, rfl⟩ := Finset.mem_add.mp (support_mul F G hd)
  rw [map_add]
  exact add_le_add (hF d1 hd1) (hG d2 hd2)

theorem DegreeLE.mul_degreeLT {F G : MvPolynomial ι K} {β β' : NatOrdinal} (hF : DegreeLE wt F β)
    (hG : DegreeLT wt G β') : DegreeLT wt (F * G) (β + β') := by
  classical
  rw [degreeLT_iff] at hG ⊢
  intro d hd
  obtain ⟨d1, hd1, d2, hd2, rfl⟩ := Finset.mem_add.mp (support_mul F G hd)
  rw [map_add]
  exact add_lt_add_of_le_of_lt (hF d1 hd1) (hG d2 hd2)

theorem DegreeLT.mul_degreeLE {F G : MvPolynomial ι K} {β β' : NatOrdinal} (hF : DegreeLT wt F β)
    (hG : DegreeLE wt G β') : DegreeLT wt (F * G) (β + β') := by
  classical
  rw [degreeLT_iff] at hF ⊢
  intro d hd
  obtain ⟨d1, hd1, d2, hd2, rfl⟩ := Finset.mem_add.mp (support_mul F G hd)
  rw [map_add]
  exact add_lt_add_of_lt_of_le (hF d1 hd1) (hG d2 hd2)

theorem DegreeLT.mul {F G : MvPolynomial ι K} {β β' : NatOrdinal} (hF : DegreeLT wt F β)
    (hG : DegreeLT wt G β') : DegreeLT wt (F * G) (β + β') :=
  hF.mul_degreeLE hG.degreeLE

/-! ### The calculus of `pol` -/

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
  {α : NatOrdinal} (hinj : ∀ β < α, InjectiveAt K wt x β)
include hinj

theorem pol_zero : σ.pol hx α (0 : Series K) = 0 :=
  σ.pol_eq_zero_of_mem hx hinj (Ideal.zero_mem _)

/-- `pol` depends only on the class modulo `J`. -/
theorem pol_congr {u u' : Series K} (hu : ordinalValue u < ω^ α) (h : toGerm u = toGerm u') :
    σ.pol hx α u = σ.pol hx α u' := by
  have hu' : ordinalValue u' < ω^ α := by
    rwa [← ordinalValue_eq_of_sub_mem_negativeMonomialIdeal (toGerm_eq_toGerm_iff.mp h)]
  exact (σ.pol_eq_of_toGerm_aeval_eq hx hinj hu' (σ.pol_degreeLT hx α u)
    (by rw [σ.toGerm_aeval_pol hx hu, h])).symm

theorem pol_sum {ι' : Type*} (s : Finset ι') (f : ι' → Series K)
    (h : ∀ i ∈ s, ordinalValue (f i) < ω^ α) :
    σ.pol hx α (∑ i ∈ s, f i) = ∑ i ∈ s, σ.pol hx α (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact σ.pol_zero hx hinj
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      σ.pol_add hx hinj (h a (Finset.mem_insert_self a s))
        (ordinalValue_sum_lt s f (NatOrdinal.wpow_pos α) fun i hi ↦
          h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)]

/-- `pol` of a scalar multiple. -/
theorem pol_C_mul (k : K) {u : Series K} (hu : ordinalValue u < ω^ α) :
    σ.pol hx α ((HahnSeries.Nonpositive.C : K →+* Series K) k * u) =
      C k * σ.pol hx α u := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [map_zero, zero_mul, map_zero, zero_mul]; exact σ.pol_zero hx hinj
  refine σ.pol_eq_of_toGerm_aeval_eq hx hinj (by rwa [ordinalValue_C_mul hk]) ?_ ?_
  · rw [C_mul', degreeLT_iff]
    exact fun d hd ↦ degreeLT_iff.mp (σ.pol_degreeLT hx α u) d (support_smul hd)
  · rw [map_mul, aeval_C, HahnSeries.Nonpositive.algebraMap_apply, map_mul, map_mul,
      σ.toGerm_aeval_pol hx hu]

/-- `pol` of a product whose polynomial has degree below `α`, together with the ordinal value
bound on the product. -/
theorem pol_mul {u u' : Series K} (hu : ordinalValue u < ω^ α) (hu' : ordinalValue u' < ω^ α)
    (hFG : DegreeLT wt (σ.pol hx α u * σ.pol hx α u') α) :
    ordinalValue (u * u') < ω^ α ∧ σ.pol hx α (u * u') = σ.pol hx α u * σ.pol hx α u' := by
  have hgerm : toGerm (aeval σ.lift (σ.pol hx α u * σ.pol hx α u')) = toGerm (u * u') := by
    rw [map_mul, map_mul, σ.toGerm_aeval_pol hx hu, σ.toGerm_aeval_pol hx hu', map_mul]
  have hval : ordinalValue (u * u') < ω^ α := by
    rw [← ordinalValue_eq_of_sub_mem_negativeMonomialIdeal (toGerm_eq_toGerm_iff.mp hgerm)]
    exact σ.ordinalValue_aeval_lt_of_degreeLT hFG
  exact ⟨hval, σ.pol_eq_of_toGerm_aeval_eq hx hinj hval hFG hgerm⟩

/-- A series of ordinal value below `ω^α'`, `α' ≤ α`, has polynomial of degree below `α'`. -/
theorem pol_degreeLT_of_lt {α' : NatOrdinal} (hα' : α' ≤ α) {u : Series K}
    (hu : ordinalValue u < ω^ α') : DegreeLT wt (σ.pol hx α u) α' := by
  obtain ⟨F, hF, hFu⟩ := σ.exists_degreeLT_toGerm_aeval_eq hx α' u hu
  rw [σ.pol_eq_of_toGerm_aeval_eq hx hinj (hu.trans_le (NatOrdinal.wpow_le_wpow.mpr hα'))
    (hF.mono hα') hFu]
  exact hF

/-- A series of ordinal value below `ω^(β+1)`, `β < α`, has polynomial of degree at most `β`. -/
theorem pol_degreeLE {β : NatOrdinal} (hβ : β < α) {u : Series K}
    (hu : ordinalValue u < ω^ (β + 1)) : DegreeLE wt (σ.pol hx α u) β :=
  degreeLT_add_one_iff_degreeLE.mp (σ.pol_degreeLT_of_lt hx hinj (Order.add_one_le_of_lt hβ) hu)

/-- The polynomial of the translated truncation of a constant at a cutoff `γ < 0` is zero. -/
theorem pol_translatedTruncation_C (k : K) {γ : ℝ} (hγ : γ < 0) :
    σ.pol hx α (translatedTruncation
      (((HahnSeries.Nonpositive.C : K →+* Series K) k : Series K) : K⟦ℝ⟧) γ) = 0 := by
  rw [HahnSeries.Nonpositive.coe_C, translatedTruncation_C_of_neg k hγ]
  exact σ.pol_zero hx hinj

end Lifts

/-! ### The convolution formula over an enlarged index set -/

/-- The cutoffs of Berarducci's index set lie in `[γ, 0]` for nonpositive series. -/
theorem mem_Icc_of_mem_convolutionIndex {u v : Series K} {γ β : ℝ}
    (h : β ∈ convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) γ) : β ∈ Set.Icc γ 0 := by
  rw [mem_convolutionIndex] at h
  have h1 : β ≤ 0 := closure_minimal (HahnSeries.Nonpositive.support_subset u) isClosed_Iic h.1
  have h2 : γ - β ≤ 0 :=
    closure_minimal (HahnSeries.Nonpositive.support_subset v) isClosed_Iic h.2
  exact ⟨by linarith, h1⟩

/-- The germ convolution formula over a finite set containing every cutoff whose germ product
is nonzero; omitted zero terms do not need to be listed. -/
theorem germAt_mul_of_support_subset (u v : Series K) (γ : ℝ) {S : Finset ℝ}
    (hS : ∀ ξ : ℝ,
      germAt (u : K⟦ℝ⟧) ξ * germAt (v : K⟦ℝ⟧) (γ - ξ) ≠ 0 → ξ ∈ S) :
    germAt ((u : K⟦ℝ⟧) * (v : K⟦ℝ⟧)) γ =
      ∑ ξ ∈ S, germAt (u : K⟦ℝ⟧) ξ * germAt (v : K⟦ℝ⟧) (γ - ξ) := by
  classical
  rw [germAt_mul]
  calc
    ∑ ξ ∈ convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) γ,
        germAt (u : K⟦ℝ⟧) ξ * germAt (v : K⟦ℝ⟧) (γ - ξ) =
        ∑ ξ ∈ convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) γ ∩ S,
          germAt (u : K⟦ℝ⟧) ξ * germAt (v : K⟦ℝ⟧) (γ - ξ) := by
      symm
      refine Finset.sum_subset Finset.inter_subset_left fun ξ hξ hnot ↦ ?_
      by_contra hne
      exact hnot (Finset.mem_inter.mpr ⟨hξ, hS ξ hne⟩)
    _ = ∑ ξ ∈ S, germAt (u : K⟦ℝ⟧) ξ * germAt (v : K⟦ℝ⟧) (γ - ξ) := by
      refine Finset.sum_subset Finset.inter_subset_right fun ξ hξ hnot ↦ ?_
      have hI : ξ ∉ convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) γ :=
        fun hi ↦ hnot (Finset.mem_inter.mpr ⟨hi, hξ⟩)
      rw [mem_convolutionIndex, not_and_or] at hI
      rcases hI with h | h
      · rw [germAt_eq_zero_of_not_mem_closure_support h, zero_mul]
      · rw [germAt_eq_zero_of_not_mem_closure_support h, mul_zero]

/-- Berarducci's convolution formula [Ber00, Lem. 7.5] summed over any finite set of cutoffs
containing his index set: the extra terms vanish. -/
theorem germAt_mul_of_subset (u v : Series K) (γ : ℝ) {S : Finset ℝ}
    (hS : convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) γ ⊆ S) :
    germAt ((u : K⟦ℝ⟧) * (v : K⟦ℝ⟧)) γ =
      ∑ β ∈ S, germAt (u : K⟦ℝ⟧) β * germAt (v : K⟦ℝ⟧) (γ - β) := by
  apply germAt_mul_of_support_subset u v γ
  intro ξ hξ
  by_contra hξS
  have hξI : ξ ∉ convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) γ :=
    fun hi ↦ hξS (hS hi)
  rw [mem_convolutionIndex, not_and_or] at hξI
  rcases hξI with h | h
  · exact hξ (by rw [germAt_eq_zero_of_not_mem_closure_support h, zero_mul])
  · exact hξ (by rw [germAt_eq_zero_of_not_mem_closure_support h, mul_zero])

/-! ### The convolution formula, read in polynomials -/

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
  {α : NatOrdinal} (hinj : ∀ β < α, InjectiveAt K wt x β)
include hinj

/-- **The convolution formula, read in polynomials** (cf. [Ber00, Lem. 7.5]). For `u, v` of ordinal
value below `ω^(β_u+1)`, `ω^(β_v+1)` with `β_u, β_v < α` and `β_u ⊕ β_v ≤ α`, there is `ε > 0` such
that for all `γ ∈ (-ε, 0)`: `pol((uv)^{|γ}) = ∑_ξ pol(u^{|ξ}) · pol(v^{|γ-ξ})`, the sum over any
finite set of cutoffs `ξ` (the Lean binder `β`) containing Berarducci's index set and contained in
`[γ, 0]`. -/
@[blueprint "lem:polynomial-convolution-formula"
  (phase := "Translated truncations")
  (title := "Convolution formula for polynomial representatives")
  (statement := /--
    Let $K$ be a field. Let $(x_i)_{i\in I}$ be a minimal homogeneous generating system of
    $\widehat{\mathrm P}$, with $x_i\in\mathrm P_{w_i}$, and choose series
    $b_i$ representing the $x_i$. Assume that evaluation at $(x_i)$ is
    injective in every weighted degree below $\alpha<\omega_1$. For every
    series $a$ with $v_J(a)<\omega^\alpha$, write
    $\operatorname{pol}_{<\alpha}(a)$ for the unique polynomial whose
    monomials have weight below $\alpha$ and such that
    \[
      a\equiv \operatorname{pol}_{<\alpha}(a)(b_i)\pmod J.
    \]

    Let $u,v\in K((\mathbb R^{\le0}))$ satisfy
    \[
      v_J(u)<\omega^{\beta+1},\qquad
      v_J(v)<\omega^{\beta'+1},\qquad
      \beta,\beta'<\alpha,\qquad \beta\oplus\beta'\le\alpha.
    \]
    For $\gamma\in\mathbb R$, put
    \[
      C_\gamma(u,v)=\{\xi\in\mathrm{cl}(\operatorname{supp}(u)):
        \gamma-\xi\in\mathrm{cl}(\operatorname{supp}(v))\}.
    \]
    Then there is $\varepsilon>0$ such that, for every
    $\gamma\in(-\varepsilon,0)$ and every finite
    $S$ with $C_\gamma(u,v)\subseteq S\subseteq[\gamma,0]$,
    \[
      \operatorname{pol}_{<\alpha}((uv)^{|\gamma})
      =\sum_{\xi\in S}
        \operatorname{pol}_{<\alpha}(u^{|\xi})
        \operatorname{pol}_{<\alpha}(v^{|\gamma-\xi}).
    \]
  -/)
  (proof := /--
  By \ref{lem:truncation-drop}, choose one interval on which the translated truncations of
  $u$, $v$, and $uv$ have the required lower ordinal values. By
  \ref{prop:polynomial-representative-exists} and
  \ref{prop:polynomial-evaluation-ordinal-value}, their degree-$<\alpha$
  polynomial representatives exist and are unique.

  Fix $\gamma$ in this interval and $\xi\in S$. Since $\gamma<0$ and
  $\gamma\le\xi\le0$, at least one of $\xi$ and $\gamma-\xi$ is negative. Its translated
  truncation has polynomial weight strictly below $\beta$ or $\beta'$, while the other has
  weight at most the corresponding ordinal. Hence the product has weight strictly below
  $\beta\oplus\beta'\le\alpha$.

  \ref{lem:convolution-formula} gives the displayed identity modulo $J$ over
  $C_\gamma(u,v)$. Every additional term indexed by $S$ vanishes modulo $J$. Uniqueness of the
  polynomial representatives turns this congruence into the asserted polynomial identity.
  -/)]
theorem exists_forall_pol_translatedTruncation_mul {u v : Series K} {βu βv : NatOrdinal}
    (hu : ordinalValue u < ω^ (βu + 1)) (hv : ordinalValue v < ω^ (βv + 1))
    (hβu : βu < α) (hβv : βv < α) (hsum : βu + βv ≤ α) :
    ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 → ∀ S : Finset ℝ,
      convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) γ ⊆ S → (S : Set ℝ) ⊆ Set.Icc γ 0 →
      σ.pol hx α (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ) =
        ∑ β ∈ S, σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) β) *
          σ.pol hx α (translatedTruncation (v : K⟦ℝ⟧) (γ - β)) := by
  obtain ⟨εu, hεu, hdropu⟩ := exists_forall_ordinalValue_translatedTruncation_lt hu
  obtain ⟨εv, hεv, hdropv⟩ := exists_forall_ordinalValue_translatedTruncation_lt hv
  have huv : ordinalValue (u * v) < ω^ (βu + βv + 1) := ordinalValue_mul_lt_wpow_add_one hu hv
  obtain ⟨εuv, hεuv, hdropuv⟩ := exists_forall_ordinalValue_translatedTruncation_lt huv
  have hβuα : βu + 1 ≤ α := Order.add_one_le_of_lt hβu
  have hβvα : βv + 1 ≤ α := Order.add_one_le_of_lt hβv
  refine ⟨min εu (min εv εuv), lt_min hεu (lt_min hεv hεuv), fun γ hγε hγ0 S hS hSIcc ↦ ?_⟩
  have hγu : -εu < γ := by
    have := min_le_left εu (min εv εuv); linarith
  have hγv : -εv < γ := by
    have := (min_le_right εu (min εv εuv)).trans (min_le_left εv εuv); linarith
  have hγuv : -εuv < γ := by
    have := (min_le_right εu (min εv εuv)).trans (min_le_right εv εuv); linarith
  -- the ordinal value of the translated truncation of the product
  have hprod : ordinalValue (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ) < ω^ α :=
    (hdropuv γ hγuv hγ0).trans_le (NatOrdinal.wpow_le_wpow.mpr hsum)
  -- each term of the convolution sum
  have hterm : ∀ β ∈ S,
      ordinalValue (translatedTruncation (u : K⟦ℝ⟧) β) < ω^ α ∧
      ordinalValue (translatedTruncation (v : K⟦ℝ⟧) (γ - β)) < ω^ α ∧
      DegreeLT wt (σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) β) *
        σ.pol hx α (translatedTruncation (v : K⟦ℝ⟧) (γ - β))) α := by
    intro β hβ
    obtain ⟨hγβ, hβ0⟩ := hSIcc hβ
    -- the first factor
    have hfirst : (ordinalValue (translatedTruncation (u : K⟦ℝ⟧) β) < ω^ α ∧
        DegreeLE wt (σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) β)) βu) ∧
        (β < 0 → ordinalValue (translatedTruncation (u : K⟦ℝ⟧) β) < ω^ βu ∧
          DegreeLT wt (σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) β)) βu) := by
      rcases eq_or_lt_of_le hβ0 with rfl | hβneg
      · rw [translatedTruncation_zero]
        exact ⟨⟨hu.trans_le (NatOrdinal.wpow_le_wpow.mpr hβuα), σ.pol_degreeLE hx hinj hβu hu⟩,
          fun h ↦ absurd h (lt_irrefl 0)⟩
      · have hlt := hdropu β (by linarith) hβneg
        exact ⟨⟨hlt.trans_le (NatOrdinal.wpow_le_wpow.mpr hβu.le),
          (σ.pol_degreeLT_of_lt hx hinj hβu.le hlt).degreeLE⟩,
          fun _ ↦ ⟨hlt, σ.pol_degreeLT_of_lt hx hinj hβu.le hlt⟩⟩
    -- the second factor
    have hsecond : (ordinalValue (translatedTruncation (v : K⟦ℝ⟧) (γ - β)) < ω^ α ∧
        DegreeLE wt (σ.pol hx α (translatedTruncation (v : K⟦ℝ⟧) (γ - β))) βv) ∧
        (γ - β < 0 → ordinalValue (translatedTruncation (v : K⟦ℝ⟧) (γ - β)) < ω^ βv ∧
          DegreeLT wt (σ.pol hx α (translatedTruncation (v : K⟦ℝ⟧) (γ - β))) βv) := by
      rcases eq_or_lt_of_le (sub_nonpos.mpr hγβ) with h0 | hneg
      · rw [h0, translatedTruncation_zero]
        exact ⟨⟨hv.trans_le (NatOrdinal.wpow_le_wpow.mpr hβvα), σ.pol_degreeLE hx hinj hβv hv⟩,
          fun h ↦ absurd h (lt_irrefl 0)⟩
      · have hlt := hdropv (γ - β) (by linarith) hneg
        exact ⟨⟨hlt.trans_le (NatOrdinal.wpow_le_wpow.mpr hβv.le),
          (σ.pol_degreeLT_of_lt hx hinj hβv.le hlt).degreeLE⟩,
          fun _ ↦ ⟨hlt, σ.pol_degreeLT_of_lt hx hinj hβv.le hlt⟩⟩
    refine ⟨hfirst.1.1, hsecond.1.1, ?_⟩
    -- at least one cutoff is negative, as `γ < 0`
    rcases lt_or_eq_of_le hβ0 with hβneg | hβzero
    · exact ((hfirst.2 hβneg).2.mul_degreeLE hsecond.1.2).mono hsum
    · have hneg : γ - β < 0 := by rw [hβzero, sub_zero]; exact hγ0
      exact (hfirst.1.2.mul_degreeLT (hsecond.2 hneg).2).mono hsum
  -- the translated truncation of the product is congruent modulo `J` to the convolution sum
  have hgerm : toGerm (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ) =
      toGerm (∑ β ∈ S, translatedTruncation (u : K⟦ℝ⟧) β *
        translatedTruncation (v : K⟦ℝ⟧) (γ - β)) := by
    rw [← germAt_apply, Subring.coe_mul, germAt_mul_of_subset u v γ hS, map_sum]
    simp only [germAt_apply, map_mul]
  rw [σ.pol_congr hx hinj hprod hgerm,
    σ.pol_sum hx hinj S _ fun β hβ ↦ (σ.pol_mul hx hinj (hterm β hβ).1 (hterm β hβ).2.1
      (hterm β hβ).2.2).1]
  exact Finset.sum_congr rfl fun β hβ ↦
    (σ.pol_mul hx hinj (hterm β hβ).1 (hterm β hβ).2.1 (hterm β hβ).2.2).2


/-- At a fixed cutoff, the polynomial convolution formula may be summed over any finite set
containing all nonzero germ products, provided the product truncation and all listed factors have
ordinal value below `ω^α` and each listed polynomial product has degree below `α`. -/
theorem pol_translatedTruncation_mul_eq_sum_of_nonzero_terms {u v : Series K} {γ : ℝ} {S : Finset ℝ}
    (hS : ∀ ξ : ℝ,
      germAt (u : K⟦ℝ⟧) ξ * germAt (v : K⟦ℝ⟧) (γ - ξ) ≠ 0 → ξ ∈ S)
    (hprod : ordinalValue (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ) < ω^ α)
    (hterm : ∀ β ∈ S,
      ordinalValue (translatedTruncation (u : K⟦ℝ⟧) β) < ω^ α ∧
      ordinalValue (translatedTruncation (v : K⟦ℝ⟧) (γ - β)) < ω^ α ∧
      DegreeLT wt (σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) β) *
        σ.pol hx α (translatedTruncation (v : K⟦ℝ⟧) (γ - β))) α) :
    σ.pol hx α (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ) =
      ∑ β ∈ S, σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) β) *
        σ.pol hx α (translatedTruncation (v : K⟦ℝ⟧) (γ - β)) := by
  have hgerm : toGerm (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ) =
      toGerm (∑ β ∈ S, translatedTruncation (u : K⟦ℝ⟧) β *
        translatedTruncation (v : K⟦ℝ⟧) (γ - β)) := by
    rw [← germAt_apply, Subring.coe_mul, germAt_mul_of_support_subset u v γ hS, map_sum]
    simp only [germAt_apply, map_mul]
  rw [σ.pol_congr hx hinj hprod hgerm,
    σ.pol_sum hx hinj S _ fun β hβ ↦ (σ.pol_mul hx hinj (hterm β hβ).1 (hterm β hβ).2.1
      (hterm β hβ).2.2).1]
  exact Finset.sum_congr rfl fun β hβ ↦
    (σ.pol_mul hx hinj (hterm β hβ).1 (hterm β hβ).2.1 (hterm β hβ).2.2).2

/-- **The convolution formula at a fixed cutoff.** If the translated truncation of the product and
every term of the convolution sum at `γ` have ordinal value below `ω^α`, and each term's polynomial
has degree below `α`, then the polynomial of `(uv)^{|γ}` is the convolution sum of polynomials. -/
theorem pol_translatedTruncation_mul_eq_sum {u v : Series K} {γ : ℝ} {S : Finset ℝ}
    (hS : convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) γ ⊆ S)
    (hprod : ordinalValue (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ) < ω^ α)
    (hterm : ∀ β ∈ S,
      ordinalValue (translatedTruncation (u : K⟦ℝ⟧) β) < ω^ α ∧
      ordinalValue (translatedTruncation (v : K⟦ℝ⟧) (γ - β)) < ω^ α ∧
      DegreeLT wt (σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) β) *
        σ.pol hx α (translatedTruncation (v : K⟦ℝ⟧) (γ - β))) α) :
    σ.pol hx α (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) γ) =
      ∑ β ∈ S, σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) β) *
        σ.pol hx α (translatedTruncation (v : K⟦ℝ⟧) (γ - β)) := by
  refine σ.pol_translatedTruncation_mul_eq_sum_of_nonzero_terms hx hinj ?_ hprod hterm
  intro ξ hξ
  by_contra hξS
  have hξI : ξ ∉ convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) γ :=
    fun hi ↦ hξS (hS hi)
  rw [mem_convolutionIndex, not_and_or] at hξI
  rcases hξI with h | h
  · exact hξ (by rw [germAt_eq_zero_of_not_mem_closure_support h, zero_mul])
  · exact hξ (by rw [germAt_eq_zero_of_not_mem_closure_support h, mul_zero])

end Lifts

end Berarducci
