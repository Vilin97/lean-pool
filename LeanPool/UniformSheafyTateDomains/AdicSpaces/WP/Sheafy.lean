/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.CoeffLocalization
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.MvTateAlgebraTopology
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Chart
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyRing
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyEndpoints
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RelativeStandardRefinement
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructurePresheafBundled

/-!
# `𝒜` is (strongly) sheafy ([WP] §6.5, thm:parity-strongly-sheafy)

The two `IsSheafy` fields (finite rational covers: topological embedding + gluing)
are produced by the finite-head Čech argument:

1. Push the covering data into one head: scale entries into the unit ball, choose
   integral Bezout relations, approximate by head elements (density,
   `exists_head_approx`) and apply the small perturbation lemma — none of this
   changes the rational subsets or the section rings ([WP] proof of
   thm:parity-strongly-sheafy, first two paragraphs).
2. The pushed data are rational in the head `P_M` (apply the coefficient retraction
   `ρ_M` to the Bezout relation), and the corresponding rational subsets COVER
   `Spa(P_M, P_M°)` — via the split surjection
   `Spa(E,E°) → Spa(P_M,P_M°)` induced by the isometric pair
   `P_M → E → P_M` ([WP], "We verify that the `V_i` cover", eq:split-spectrum-map;
   the paper warns: do NOT identify `U` with the maximal-pair spectrum).
3. The head is sheafy (Wedhorn 8.28(b), `isSheafy_WPHead`); its Čech equalizer
   isomorphism has a BOUNDED inverse (closed range + open mapping — the no-Baire
   route `isInducing_of_closedRange_of_topNilpUnit` of `WedhornBanachTheorem.lean`,
   at the normed model `QHead`); gluing then proceeds coefficientwise with uniform
   norm control, and the glued family is again null
   ([WP] eq:head-cech, eq:coefficientwise-gluing-bound).

**Strong sheafiness**: the whole construction is uniform in the weight `w`; the Tate
extension `𝒜⟨V_1,…,V_s⟩` is the weighted-parity algebra at the shifted weight
(`shiftWeight`), so `isSheafy_WPA` applied at `shiftWeight w s` gives sheafiness of
every finite Tate extension ([WP] eq:strong-sheafy-decomposition: "the preceding
proof applies verbatim").  The bridge to the project's own Tate-extension
(`restrictedMvPowerSeriesSubring`) is `tateExtEquiv`.
-/

@[expose] public section

@[expose] public section

namespace WeightedParity

open ValuationSpectrum FiniteJetOver

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ)

variable {K w} in
/-- A common head stage for every datum of a finite rational covering
(shared W21/W22 infrastructure: `nonempty_headModelData_all` + a `Finset.sup`
of the thresholds). -/
theorem exists_common_headModel_stage (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational) :
    ∃ M : ℕ, (∃ (DHb : RationalLocData (WPHead K w M)) (hDHb : DHb.IsRational),
        rationalOpen (liftDatum DHb hDHb).T (liftDatum DHb hDHb).s =
          rationalOpen C.base.T C.base.s) ∧
      ∀ D ∈ C.covers,
        ∃ (DH : RationalLocData (WPHead K w M)) (hDH : DH.IsRational),
          rationalOpen (liftDatum DH hDH).T (liftDatum DH hDH).s =
            rationalOpen D.T D.s := by
  classical
  obtain ⟨Nb, hb⟩ := nonempty_headModelData_all ϖ hK₀ C.base hC.base
  choose Np hp using fun (D : { D : RationalLocData (WPA K w) // D ∈ C.covers }) =>
    nonempty_headModelData_all ϖ hK₀ D.1 (hC.piece D.2)
  set M : ℕ := max Nb (C.covers.attach.sup Np) with hM_def
  refine ⟨M, hb M (by rw [hM_def]; exact le_max_left _ _), fun D hD => ?_⟩
  refine hp ⟨D, hD⟩ M ?_
  rw [hM_def]
  exact le_trans (Finset.le_sup (Finset.mem_attach _ ⟨D, hD⟩))
    (le_max_right _ _)

variable {K w} in
theorem rhoHead_continuous (M : ℕ) :
    Continuous (rhoHead K w M) :=
  AddMonoidHomClass.continuous_of_bound (rhoHead K w M) 1 fun f => by
    rw [one_mul]
    exact norm_rhoHead_le (K := K) (w := w) (N := M) f

variable {K w} in
/-- Norm bound extraction for power-bounded elements of `𝒜` (topological
boundedness at the unit ball against a scaling constant). -/
theorem norm_bound_of_isPowerBounded {a : WPA K w}
    (ha : TopologicalRing.IsPowerBounded a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C := by
  obtain ⟨V, hV, hSV⟩ := ha (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  have h1 : (0 : ℝ) < ‖constA K w c‖ := by rw [norm_constA]; exact hc0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ0
    (by rw [norm_constA]; exact hc1 : ‖constA K w c‖ < 1)
  have hnc : ‖constA K w c ^ k‖ = ‖constA K w c‖ ^ k := by
    rw [← map_pow, norm_constA, norm_pow, norm_constA]
  refine ⟨1 / ‖constA K w c‖ ^ k, by positivity, fun n => ?_⟩
  have hmem : a ^ n * constA K w c ^ k ∈ Metric.ball (0 : WPA K w) 1 := by
    refine hSV (Set.mul_mem_mul ⟨n, rfl⟩ (hball ?_))
    rw [Metric.mem_ball, dist_zero_right, hnc]
    exact hk
  rw [Metric.mem_ball, dist_zero_right] at hmem
  have hval : ‖a ^ n * constA K w c ^ k‖ = ‖constA K w c‖ ^ k * ‖a ^ n‖ := by
    rw [show constA K w c ^ k = constA K w (c ^ k) from by rw [map_pow],
      mul_comm (a ^ n), norm_constA_mul]
    rw [show ‖constA K w c‖ ^ k = ‖c‖ ^ k from by rw [norm_constA],
      norm_pow]
  rw [hval] at hmem
  rw [le_div_iff₀ (by positivity)]
  calc ‖a ^ n‖ * ‖constA K w c‖ ^ k = ‖constA K w c‖ ^ k * ‖a ^ n‖ := by ring
    _ ≤ 1 := hmem.le

variable {K w} in
/-- `rhoHead` sends power-bounded elements to power-bounded elements. -/
theorem isPowerBounded_rhoHead {a : WPA K w} (M : ℕ)
    (ha : TopologicalRing.IsPowerBounded a) :
    TopologicalRing.IsPowerBounded (rhoHead K w M a) := by
  obtain ⟨C, hC0, hC⟩ := norm_bound_of_isPowerBounded ha
  refine isPowerBounded_of_forall_norm_le hC0 fun n => ?_
  rw [← map_pow]
  exact le_trans (norm_rhoHead_le (K := K) (w := w) (N := M) _) (hC n)

variable {K w} in
theorem plus_le_comap_rhoHead (M : ℕ) :
    ((WPA K w)⁺ : Subring (WPA K w)) ≤
      ((WPHead K w M)⁺ : Subring (WPHead K w M)).comap (rhoHead K w M) :=
  fun _ ha => isPowerBounded_rhoHead M ha

variable {K w} in
theorem comap_rhoHead_mem_spa (M : ℕ) {v : Spv (WPHead K w M)}
    (hv : v ∈ Spa (WPHead K w M) ((WPHead K w M)⁺)) :
    ValuationSpectrum.comap (rhoHead K w M) v ∈ Spa (WPA K w) ((WPA K w)⁺) :=
  comap_mem_spa (rhoHead_continuous M) (plus_le_comap_rhoHead M) hv

variable {K w} in
open scoped Classical in
/-- Membership transfer along the `rhoHead` pullback: a head point lies in a head
datum's rational subset iff its pullback lies in the lifted datum's ([WP]
1156–1218, realized by the retraction instead of the split surjection — the
project's models are `𝒜`-global). -/
theorem comap_rhoHead_mem_iff (M : ℕ) (DH : RationalLocData (WPHead K w M))
    (hDH : DH.IsRational) (v : Spv (WPHead K w M))
    (hv : v ∈ Spa (WPHead K w M) ((WPHead K w M)⁺)) :
    ValuationSpectrum.comap (rhoHead K w M) v ∈
      rationalOpen (liftDatum DH hDH).T (liftDatum DH hDH).s ↔
      v ∈ rationalOpen DH.T DH.s := by
  constructor
  · rintro ⟨-, hT, hs0⟩
    refine ⟨hv, fun t ht => ?_, fun hc => ?_⟩
    · have h1 := hT (headIncl K w M t) (by
        rw [show (liftDatum DH hDH).T = DH.T.image (headIncl K w M) from rfl]
        exact Finset.mem_image_of_mem _ ht)
      rw [show (liftDatum DH hDH).s = headIncl K w M DH.s from rfl] at h1
      rw [comap_vle,
        show rhoHead K w M (headIncl K w M t) = t from
          rhoHead_headIncl (K := K) (w := w) (N := M) t,
        show rhoHead K w M (headIncl K w M DH.s) = DH.s from
          rhoHead_headIncl (K := K) (w := w) (N := M) DH.s] at h1
      exact h1
    · refine hs0 ?_
      rw [show (liftDatum DH hDH).s = headIncl K w M DH.s from rfl, comap_vle,
        map_zero,
        show rhoHead K w M (headIncl K w M DH.s) = DH.s from
          rhoHead_headIncl (K := K) (w := w) (N := M) DH.s]
      exact hc
  · rintro ⟨-, hT, hs0⟩
    refine ⟨comap_rhoHead_mem_spa M hv, fun t' ht' => ?_, fun hc => ?_⟩
    · rw [show (liftDatum DH hDH).T = DH.T.image (headIncl K w M) from rfl]
        at ht'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      rw [show (liftDatum DH hDH).s = headIncl K w M DH.s from rfl, comap_vle,
        show rhoHead K w M (headIncl K w M t) = t from
          rhoHead_headIncl (K := K) (w := w) (N := M) t,
        show rhoHead K w M (headIncl K w M DH.s) = DH.s from
          rhoHead_headIncl (K := K) (w := w) (N := M) DH.s]
      exact hT t ht
    · refine hs0 ?_
      rw [show (liftDatum DH hDH).s = headIncl K w M DH.s from rfl, comap_vle,
        map_zero,
        show rhoHead K w M (headIncl K w M DH.s) = DH.s from
          rhoHead_headIncl (K := K) (w := w) (N := M) DH.s] at hc
      exact hc

variable {K w} in
/-- `headIncl` is continuous (it is isometric). -/
theorem headIncl_continuous (M : ℕ) : Continuous (headIncl K w M) :=
  (AddMonoidHomClass.isometry_of_norm (headIncl K w M)
    (fun x => norm_headIncl (K := K) (w := w) (N := M) x)).continuous

variable {K w} in
/-- Norm bound extraction for power-bounded elements of the head
(the `norm_bound_of_isPowerBounded` mirror at `P_M`). -/
theorem norm_bound_of_isPowerBounded_head {M : ℕ} {a : WPHead K w M}
    (ha : TopologicalRing.IsPowerBounded a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C := by
  obtain ⟨V, hV, hSV⟩ := ha (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  have h1 : (0 : ℝ) < ‖constHead K w M c‖ := by
    rw [norm_constHead]; exact hc0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ0
    (by rw [norm_constHead]; exact hc1 : ‖constHead K w M c‖ < 1)
  have hnc : ‖constHead K w M c ^ k‖ = ‖constHead K w M c‖ ^ k := by
    rw [← map_pow, norm_constHead, norm_pow, norm_constHead]
  refine ⟨1 / ‖constHead K w M c‖ ^ k, by positivity, fun n => ?_⟩
  have hmem : a ^ n * constHead K w M c ^ k ∈
      Metric.ball (0 : WPHead K w M) 1 := by
    refine hSV (Set.mul_mem_mul ⟨n, rfl⟩ (hball ?_))
    rw [Metric.mem_ball, dist_zero_right, hnc]
    exact hk
  rw [Metric.mem_ball, dist_zero_right] at hmem
  have hval : ‖a ^ n * constHead K w M c ^ k‖ =
      ‖constHead K w M c‖ ^ k * ‖a ^ n‖ := by
    rw [show constHead K w M c ^ k = constHead K w M (c ^ k) from by
        rw [map_pow],
      mul_comm (a ^ n), norm_constHead_mul]
    rw [show ‖constHead K w M c‖ ^ k = ‖c‖ ^ k from by rw [norm_constHead],
      norm_pow]
  rw [hval] at hmem
  rw [le_div_iff₀ (by positivity)]
  calc ‖a ^ n‖ * ‖constHead K w M c‖ ^ k
      = ‖constHead K w M c‖ ^ k * ‖a ^ n‖ := by ring
    _ ≤ 1 := hmem.le

variable {K w} in
/-- `headIncl` sends power-bounded elements to power-bounded elements. -/
theorem isPowerBounded_headIncl {M : ℕ} {a : WPHead K w M}
    (ha : TopologicalRing.IsPowerBounded a) :
    TopologicalRing.IsPowerBounded (headIncl K w M a) := by
  obtain ⟨C, hC0, hC⟩ := norm_bound_of_isPowerBounded_head ha
  refine isPowerBounded_of_forall_norm_le hC0 fun n => ?_
  rw [← map_pow, norm_headIncl]
  exact hC n

variable {K w} in
theorem plus_le_comap_headIncl (M : ℕ) :
    ((WPHead K w M)⁺ : Subring (WPHead K w M)) ≤
      ((WPA K w)⁺ : Subring (WPA K w)).comap (headIncl K w M) :=
  fun _ ha => isPowerBounded_headIncl ha

variable {K w} in
theorem comap_headIncl_mem_spa (M : ℕ) {v : Spv (WPA K w)}
    (hv : v ∈ Spa (WPA K w) ((WPA K w)⁺)) :
    ValuationSpectrum.comap (headIncl K w M) v ∈
      Spa (WPHead K w M) ((WPHead K w M)⁺) :=
  comap_mem_spa (headIncl_continuous M) (plus_le_comap_headIncl M) hv

variable {K w} in
open scoped Classical in
/-- Membership in a lifted datum's rational subset is head-membership of the
`headIncl`-restriction (the counterpart of `comap_rhoHead_mem_iff` at an
arbitrary `𝒜`-point). -/
theorem mem_liftDatum_iff (M : ℕ) (DH : RationalLocData (WPHead K w M))
    (hDH : DH.IsRational) (v : Spv (WPA K w))
    (hv : v ∈ Spa (WPA K w) ((WPA K w)⁺)) :
    v ∈ rationalOpen (liftDatum DH hDH).T (liftDatum DH hDH).s ↔
      ValuationSpectrum.comap (headIncl K w M) v ∈
        rationalOpen DH.T DH.s := by
  constructor
  · rintro ⟨-, hT, hs0⟩
    refine ⟨comap_headIncl_mem_spa M hv, fun t ht => ?_, fun hc => ?_⟩
    · rw [comap_vle]
      have h1 := hT (headIncl K w M t) (by
        rw [show (liftDatum DH hDH).T = DH.T.image (headIncl K w M) from rfl]
        exact Finset.mem_image_of_mem _ ht)
      rw [show (liftDatum DH hDH).s = headIncl K w M DH.s from rfl] at h1
      exact h1
    · refine hs0 ?_
      rw [show (liftDatum DH hDH).s = headIncl K w M DH.s from rfl]
      rw [comap_vle, map_zero] at hc
      exact hc
  · rintro ⟨-, hT, hs0⟩
    refine ⟨hv, fun t' ht' => ?_, fun hc => ?_⟩
    · rw [show (liftDatum DH hDH).T = DH.T.image (headIncl K w M) from rfl]
        at ht'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      have h1 := hT t ht
      rw [comap_vle] at h1
      rw [show (liftDatum DH hDH).s = headIncl K w M DH.s from rfl]
      exact h1
    · refine hs0 ?_
      rw [comap_vle, map_zero]
      rw [show (liftDatum DH hDH).s = headIncl K w M DH.s from rfl] at hc
      exact hc

variable {K w} in
open scoped Classical in
/-- Lifting is monotone on rational subsets: a head-level inclusion of
rational opens lifts to the `𝒜`-level (the bridge that turns head refinements
of pushed pieces into `𝒜`-refinements, [WP] 1156–1218). -/
theorem liftDatum_mono {M : ℕ} (DH DH' : RationalLocData (WPHead K w M))
    (hDH : DH.IsRational) (hDH' : DH'.IsRational)
    (hsub : rationalOpen DH'.T DH'.s ⊆ rationalOpen DH.T DH.s) :
    rationalOpen (liftDatum DH' hDH').T (liftDatum DH' hDH').s ⊆
      rationalOpen (liftDatum DH hDH).T (liftDatum DH hDH).s := by
  intro v hv
  have hvspa : v ∈ Spa (WPA K w) ((WPA K w)⁺) := rationalOpen_subset_spa hv
  exact (mem_liftDatum_iff M DH hDH v hvspa).mpr
    (hsub ((mem_liftDatum_iff M DH' hDH' v hvspa).mp hv))

variable {K w} in
open scoped Classical in
/-- The product (intersection) datum of two rational head data (the
`interDatum` mirror at `P_M`; [WP] 1156–1218 "the intersections are again
rational"). -/
noncomputable def interDatumHead {M : ℕ}
    (DH₁ DH₂ : RationalLocData (WPHead K w M))
    (h₁ : DH₁.IsRational) (h₂ : DH₂.IsRational) :
    RationalLocData (WPHead K w M) where
  P := DH₁.P
  T := (insert DH₁.s DH₁.T ×ˢ insert DH₂.s DH₂.T).image fun p => p.1 * p.2
  s := DH₁.s * DH₂.s
  hopen := genPiece_hopen DH₁.P
    ((insert DH₁.s DH₁.T ×ˢ insert DH₂.s DH₂.T).image fun p => p.1 * p.2)
    (DH₁.s * DH₂.s)
    (FiniteJet.span_mul_image_eq_top (FiniteJet.span_insert_eq_top DH₁.s h₁.span_eq_top)
      (FiniteJet.span_insert_eq_top DH₂.s h₂.span_eq_top))

variable {K w} in
open scoped Classical in
theorem interDatumHead_isRational {M : ℕ}
    {DH₁ DH₂ : RationalLocData (WPHead K w M)}
    (h₁ : DH₁.IsRational) (h₂ : DH₂.IsRational) :
    (interDatumHead DH₁ DH₂ h₁ h₂).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (FiniteJet.span_mul_image_eq_top (FiniteJet.span_insert_eq_top DH₁.s h₁.span_eq_top)
      (FiniteJet.span_insert_eq_top DH₂.s h₂.span_eq_top))

variable {K w} in
open scoped Classical in
/-- The intersection formula for the head product datum. -/
theorem rationalOpen_interDatumHead {M : ℕ}
    (DH₁ DH₂ : RationalLocData (WPHead K w M))
    (h₁ : DH₁.IsRational) (h₂ : DH₂.IsRational) :
    rationalOpen (interDatumHead DH₁ DH₂ h₁ h₂).T
        (interDatumHead DH₁ DH₂ h₁ h₂).s =
      rationalOpen DH₁.T DH₁.s ∩ rationalOpen DH₂.T DH₂.s := by
  ext v
  constructor
  · rintro ⟨hspa, hvle, hs0⟩
    have hs₁0 : ¬ v.vle DH₁.s 0 := fun h0 => hs0 (by
      have := v.mul_vle_mul_left h0 DH₂.s
      rwa [zero_mul] at this)
    have hs₂0 : ¬ v.vle DH₂.s 0 := fun h0 => hs0 (by
      have := v.mul_vle_mul_left h0 DH₁.s
      rw [zero_mul, mul_comm DH₂.s DH₁.s] at this
      exact this)
    refine ⟨⟨hspa, fun t ht => ?_, hs₁0⟩, ⟨hspa, fun t ht => ?_, hs₂0⟩⟩
    · have hpair : t * DH₂.s ∈ (interDatumHead DH₁ DH₂ h₁ h₂).T :=
        Finset.mem_image.mpr ⟨(t, DH₂.s), Finset.mem_product.mpr
          ⟨Finset.mem_insert_of_mem ht, Finset.mem_insert_self _ _⟩, rfl⟩
      exact v.vle_mul_cancel hs₂0 (hvle _ hpair)
    · have hpair : DH₁.s * t ∈ (interDatumHead DH₁ DH₂ h₁ h₂).T :=
        Finset.mem_image.mpr ⟨(DH₁.s, t), Finset.mem_product.mpr
          ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ht⟩, rfl⟩
      have h' := hvle _ hpair
      rw [show DH₁.s * t = t * DH₁.s from mul_comm _ _,
        show (interDatumHead DH₁ DH₂ h₁ h₂).s = DH₂.s * DH₁.s from
          mul_comm _ _] at h'
      exact v.vle_mul_cancel hs₁0 h'
  · rintro ⟨⟨hspa, hvle₁, hs₁0⟩, ⟨-, hvle₂, hs₂0⟩⟩
    have hvle₁' : ∀ t₁ ∈ insert DH₁.s DH₁.T, v.vle t₁ DH₁.s := by
      intro t₁ ht₁
      rcases Finset.mem_insert.mp ht₁ with h | h
      · subst h; exact (v.vle_total _ _).elim id id
      · exact hvle₁ t₁ h
    have hvle₂' : ∀ t₂ ∈ insert DH₂.s DH₂.T, v.vle t₂ DH₂.s := by
      intro t₂ ht₂
      rcases Finset.mem_insert.mp ht₂ with h | h
      · subst h; exact (v.vle_total _ _).elim id id
      · exact hvle₂ t₂ h
    refine ⟨hspa, fun t' ht' => ?_, fun h0 => ?_⟩
    · obtain ⟨⟨t₁, t₂⟩, hmem, rfl⟩ := Finset.mem_image.mp ht'
      obtain ⟨ht₁, ht₂⟩ := Finset.mem_product.mp hmem
      have ha := v.mul_vle_mul_left (hvle₁' t₁ ht₁) t₂
      have hb := v.mul_vle_mul_left (hvle₂' t₂ ht₂) DH₁.s
      rw [mul_comm t₂ DH₁.s, mul_comm DH₂.s DH₁.s] at hb
      exact v.vle_trans ha hb
    · rw [show (interDatumHead DH₁ DH₂ h₁ h₂).s = DH₁.s * DH₂.s from rfl,
        show (0 : WPHead K w M) = 0 * DH₂.s from (zero_mul _).symm] at h0
      exact hs₁0 (v.vle_mul_cancel hs₂0 h0)

variable {K w} in
/-- A common-stage system of head data for a whole covering, with the
rational-subset identifications — the carrier consumed by the embedding and
gluing fields (shared W21/W22 infrastructure; [WP] 1156–1218). -/
structure PushedHeadData (C : RationalCoveringData (WPA K w)) where
  /-- The common head stage. -/
  M : ℕ
  /-- The base head datum. -/
  DHb : RationalLocData (WPHead K w M)
  hDHb : DHb.IsRational
  hopenb : rationalOpen (liftDatum DHb hDHb).T (liftDatum DHb hDHb).s =
    rationalOpen C.base.T C.base.s
  /-- The per-piece head data. -/
  DHp : ↥C.covers → RationalLocData (WPHead K w M)
  hDHp : ∀ D, (DHp D).IsRational
  hopenp : ∀ D, rationalOpen (liftDatum (DHp D) (hDHp D)).T
    (liftDatum (DHp D) (hDHp D)).s = rationalOpen (D : ↥C.covers).1.T
      (D : ↥C.covers).1.s

variable {K w} in
theorem nonempty_pushedHeadData (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational) :
    Nonempty (PushedHeadData C) := by
  classical
  obtain ⟨M, ⟨DHb, hDHb, hopenb⟩, hp⟩ :=
    exists_common_headModel_stage ϖ hK₀ C hC
  choose DHp hDHp hopenp using fun (D : ↥C.covers) => hp D.1 D.2
  exact ⟨⟨M, DHb, hDHb, hopenb, DHp, hDHp, hopenp⟩⟩

variable {K w} in
open scoped Classical in
/-- The head covering data associated to a pushed system. -/
noncomputable def PushedHeadData.cover {C : RationalCoveringData (WPA K w)}
    (P : PushedHeadData C) : RationalCoveringData (WPHead K w P.M) where
  base := P.DHb
  covers := C.covers.attach.image P.DHp
  hsubset := by
    intro DH' hDH'
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hDH'
    intro v hv
    have hvspa : v ∈ Spa (WPHead K w P.M) ((WPHead K w P.M)⁺) := hv.1
    have h1 := (comap_rhoHead_mem_iff P.M (P.DHp D) (P.hDHp D) v hvspa).mpr hv
    rw [P.hopenp D] at h1
    have h2 := C.hsubset D.1 D.2 h1
    rw [← P.hopenb] at h2
    exact (comap_rhoHead_mem_iff P.M P.DHb P.hDHb v hvspa).mp h2
  hcover := by
    intro v hv
    have hvspa : v ∈ Spa (WPHead K w P.M) ((WPHead K w P.M)⁺) := hv.1
    have h1 := (comap_rhoHead_mem_iff P.M P.DHb P.hDHb v hvspa).mpr hv
    rw [P.hopenb] at h1
    obtain ⟨D, hD, hmem⟩ := C.hcover _ h1
    refine ⟨P.DHp ⟨D, hD⟩,
      Finset.mem_image_of_mem _ (Finset.mem_attach _ _), ?_⟩
    have h2 : ValuationSpectrum.comap (rhoHead K w P.M) v ∈
        rationalOpen (liftDatum (P.DHp ⟨D, hD⟩) (P.hDHp ⟨D, hD⟩)).T
          (liftDatum (P.DHp ⟨D, hD⟩) (P.hDHp ⟨D, hD⟩)).s := by
      rw [P.hopenp ⟨D, hD⟩]
      exact hmem
    exact (comap_rhoHead_mem_iff P.M (P.DHp ⟨D, hD⟩) (P.hDHp ⟨D, hD⟩) v
      hvspa).mp h2

variable {K w} in
open scoped Classical in
theorem PushedHeadData.cover_isRational {C : RationalCoveringData (WPA K w)}
    (P : PushedHeadData C) : P.cover.IsRational := by
  refine ⟨P.hDHb, ?_⟩
  intro DH' hDH'
  obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hDH'
  exact P.hDHp D

variable {K w} in
open scoped Classical in
theorem PushedHeadData.piece_subset {C : RationalCoveringData (WPA K w)}
    (P : PushedHeadData C) (D : ↥C.covers) :
    rationalOpen (P.DHp D).T (P.DHp D).s ⊆
      rationalOpen P.DHb.T P.DHb.s :=
  P.cover.hsubset (P.DHp D)
    (Finset.mem_image_of_mem _ (Finset.mem_attach _ _))

variable {K w} in
open scoped Classical in
/-- The head-level restriction between graph models along a pushed covering
piece (the `headLocEquiv`-conjugated restriction map;
[WP] eq:cover-coefficientwise's coefficient hom). -/
noncomputable def qRestrict {C : RationalCoveringData (WPA K w)}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (P : PushedHeadData C) (D : ↥C.covers) :
    QHead P.DHb →+* QHead (P.DHp D) :=
  ((headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).toRingHom.comp
    (restrictionMapHom P.DHb (P.DHp D) (P.piece_subset D))).comp
    (headLocEquiv ϖ hK₀ P.DHb P.hDHb).symm.toRingHom

variable {K w} in
open scoped Classical in
/-- `qRestrict` matches the head constants (the generator law of the
naturality square). -/
theorem qRestrict_headConst {C : RationalCoveringData (WPA K w)}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (P : PushedHeadData C) (D : ↥C.covers) (x : WPHead K w P.M) :
    qRestrict ϖ hK₀ P D (headConst P.DHb x) =
      headConst (P.DHp D) x := by
  have h1 : (headLocEquiv ϖ hK₀ P.DHb P.hDHb).symm (headConst P.DHb x) =
      P.DHb.canonicalMap x := by
    have h2 : headLocEquiv ϖ hK₀ P.DHb P.hDHb (P.DHb.canonicalMap x) =
        headConst P.DHb x := by
      rw [show headLocEquiv ϖ hK₀ P.DHb P.hDHb (P.DHb.canonicalMap x) =
        headLocFwd ϖ P.DHb P.hDHb (P.DHb.canonicalMap x) from rfl,
        show P.DHb.canonicalMap x = P.DHb.coeRingHom
          (algebraMap (WPHead K w P.M) (Localization.Away P.DHb.s) x) from rfl,
        headLocFwd_coe, headLocFwdAlg_algebraMap]
    rw [← h2, RingEquiv.symm_apply_apply]
  show headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)
    (restrictionMapHom P.DHb (P.DHp D) (P.piece_subset D)
      ((headLocEquiv ϖ hK₀ P.DHb P.hDHb).symm (headConst P.DHb x))) =
    headConst (P.DHp D) x
  rw [h1, restrictionMapHom_canonicalMap_generic]
  rw [show headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)
      ((P.DHp D).canonicalMap x) =
    headLocFwd ϖ (P.DHp D) (P.hDHp D) ((P.DHp D).canonicalMap x) from rfl,
    show (P.DHp D).canonicalMap x = (P.DHp D).coeRingHom
      (algebraMap (WPHead K w P.M) (Localization.Away (P.DHp D).s) x)
      from rfl,
    headLocFwd_coe, headLocFwdAlg_algebraMap]

variable {K w} in
/-- Scalar scaling of the graph-model quotient norm: the easy half
(submultiplicativity + the nonexpansive constants). -/
theorem norm_qscale_le {M : ℕ} (DH : RationalLocData (WPHead K w M)) (c : K)
    (q : QHead DH) :
    ‖headConst DH (constHead K w M c) * q‖ ≤ ‖c‖ * ‖q‖ := by
  refine le_trans (norm_mul_le _ _) ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg q)
  refine le_trans (norm_headConst_le DH _) ?_
  exact le_of_eq (by rw [norm_constHead])

variable {K w} in
/-- Exact scalar scaling of the graph-model quotient norm. -/
theorem norm_qscale {M : ℕ} (DH : RationalLocData (WPHead K w M)) {c : K}
    (hc0 : 0 < ‖c‖) (q : QHead DH) :
    ‖headConst DH (constHead K w M c) * q‖ = ‖c‖ * ‖q‖ := by
  have hcne : c ≠ 0 := fun h => by
    rw [h, norm_zero] at hc0
    exact lt_irrefl 0 hc0
  refine le_antisymm (norm_qscale_le DH c q) ?_
  have h1 := norm_qscale_le DH c⁻¹ (headConst DH (constHead K w M c) * q)
  rw [← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hcne, map_one,
    map_one, one_mul, norm_inv] at h1
  calc ‖c‖ * ‖q‖
      ≤ ‖c‖ * (‖c‖⁻¹ * ‖headConst DH (constHead K w M c) * q‖) :=
        mul_le_mul_of_nonneg_left h1 hc0.le
    _ = ‖headConst DH (constHead K w M c) * q‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc0), one_mul]

variable {K w} in
open scoped Classical in
theorem qRestrict_continuous {C : RationalCoveringData (WPA K w)}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (P : PushedHeadData C) (D : ↥C.covers) :
    Continuous (qRestrict ϖ hK₀ P D) := by
  rw [qRestrict, RingHom.coe_comp, RingHom.coe_comp]
  refine Continuous.comp (Continuous.comp ?_ ?_) ?_
  · exact headLocEquiv_continuous ϖ hK₀ (P.DHp D) (P.hDHp D)
  · letI : UniformSpace (Localization.Away P.DHb.s) := P.DHb.uniformSpace
    letI : IsTopologicalRing (Localization.Away P.DHb.s) :=
      P.DHb.isTopologicalRing
    letI : IsUniformAddGroup (Localization.Away P.DHb.s) :=
      P.DHb.isUniformAddGroup
    exact UniformSpace.Completion.continuous_extension
  · exact headLocEquiv_symm_continuous ϖ hK₀ P.DHb P.hDHb

variable {K w} in
open scoped Classical in
/-- The head restriction is bounded (continuity at `0` + the exact
nonarchimedean window scaling with `ℤ`-powers of the window constant). -/
theorem qRestrict_bound {C : RationalCoveringData (WPA K w)}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (P : PushedHeadData C) (D : ↥C.covers) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ q : QHead P.DHb,
      ‖qRestrict ϖ hK₀ P D q‖ ≤ Cb * ‖q‖ := by
  classical
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  have hcne : c ≠ 0 := fun h => by
    rw [h, norm_zero] at hc0
    exact lt_irrefl 0 hc0
  have hcRne : ‖c‖ ≠ 0 := ne_of_gt hc0
  have hcont := (qRestrict_continuous ϖ hK₀ P D).tendsto 0
  rw [map_zero] at hcont
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp
    (hcont (Metric.ball_mem_nhds 0 one_pos))
  refine ⟨1 / (‖c‖ * δ), by positivity, fun q => ?_⟩
  rcases eq_or_lt_of_le (norm_nonneg q) with hq0 | hq0
  · rw [show q = 0 from by rw [← norm_eq_zero]; exact hq0.symm, map_zero,
      norm_zero, norm_zero, mul_zero]
  have hinv1 : (1 : ℝ) < ‖c‖⁻¹ := (one_lt_inv₀ hc0).mpr hc1
  obtain ⟨n, hn⟩ := exists_mem_Ico_zpow
    (x := ‖q‖ / δ) (by positivity) hinv1
  rw [Set.mem_Ico] at hn
  -- upper: ‖c‖^(n+1)·‖q‖ < δ
  have hupper : ‖c‖ ^ (n + 1 : ℤ) * ‖q‖ < δ := by
    have h2 := hn.2
    rw [div_lt_iff₀ hδ0] at h2
    have h3 := mul_lt_mul_of_pos_left h2 (zpow_pos hc0 (n + 1))
    rw [show ‖c‖ ^ (n + 1 : ℤ) * ((‖c‖⁻¹ : ℝ) ^ (n + 1 : ℤ) * δ) =
      (‖c‖ * ‖c‖⁻¹) ^ (n + 1 : ℤ) * δ from by
        rw [mul_zpow, mul_assoc],
      mul_inv_cancel₀ hcRne, one_zpow, one_mul] at h3
    exact h3
  -- lower: δ·‖c‖ ≤ ‖c‖^(n+1)·‖q‖
  have hlower : δ * ‖c‖ ≤ ‖c‖ ^ (n + 1 : ℤ) * ‖q‖ := by
    have h2 := hn.1
    rw [le_div_iff₀ hδ0] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt (zpow_pos hc0 (n + 1)))
    rw [show ‖c‖ ^ (n + 1 : ℤ) * ((‖c‖⁻¹ : ℝ) ^ (n : ℤ) * δ) =
      ‖c‖ ^ (n + 1 : ℤ) * (‖c‖ ^ (n : ℤ))⁻¹ * δ from by
        rw [inv_zpow, mul_assoc],
      show ‖c‖ ^ (n + 1 : ℤ) * (‖c‖ ^ (n : ℤ))⁻¹ =
        ‖c‖ ^ (n + 1 - n : ℤ) from by
        rw [zpow_sub₀ hcRne, div_eq_mul_inv],
      show (n + 1 - n : ℤ) = 1 from by ring,
      zpow_one] at h3
    calc δ * ‖c‖ = ‖c‖ * δ := by ring
      _ ≤ ‖c‖ ^ (n + 1 : ℤ) * ‖q‖ := h3
  -- the scaled element
  set a : K := c ^ (n + 1 : ℤ) with ha_def
  have hna : ‖a‖ = ‖c‖ ^ (n + 1 : ℤ) := by rw [ha_def, norm_zpow]
  have hna0 : 0 < ‖a‖ := by rw [hna]; exact zpow_pos hc0 _
  have hmem : ‖qRestrict ϖ hK₀ P D
      (headConst P.DHb (constHead K w P.M a) * q)‖ < 1 := by
    have h4 : headConst P.DHb (constHead K w P.M a) * q ∈
        Metric.ball (0 : QHead P.DHb) δ := by
      rw [Metric.mem_ball, dist_zero_right, norm_qscale P.DHb hna0 q, hna]
      exact hupper
    have h5 := hball h4
    rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at h5
    exact h5
  rw [map_mul, qRestrict_headConst,
    norm_qscale (P.DHp D) hna0 _, hna] at hmem
  -- extract the bound
  have hpow : (0 : ℝ) < ‖c‖ ^ (n + 1 : ℤ) := zpow_pos hc0 _
  have h6 : ‖qRestrict ϖ hK₀ P D q‖ < (‖c‖ ^ (n + 1 : ℤ))⁻¹ :=
    calc ‖qRestrict ϖ hK₀ P D q‖ = (‖c‖ ^ (n + 1 : ℤ))⁻¹ *
          (‖c‖ ^ (n + 1 : ℤ) * ‖qRestrict ϖ hK₀ P D q‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpow), one_mul]
      _ < (‖c‖ ^ (n + 1 : ℤ))⁻¹ * 1 :=
          mul_lt_mul_of_pos_left hmem (by positivity)
      _ = (‖c‖ ^ (n + 1 : ℤ))⁻¹ := mul_one _
  refine le_trans h6.le ?_
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity : (0:ℝ) < ‖c‖ * δ)]
  calc (‖c‖ ^ (n + 1 : ℤ))⁻¹ * (‖c‖ * δ)
      ≤ (‖c‖ ^ (n + 1 : ℤ))⁻¹ * (‖c‖ ^ (n + 1 : ℤ) * ‖q‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖c‖ * δ = δ * ‖c‖ := by ring
          _ ≤ ‖c‖ ^ (n + 1 : ℤ) * ‖q‖ := hlower
    _ = ‖q‖ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpow), one_mul]

section MapC

variable {P Q : Type*} [NormedCommRing P] [IsUltrametricDist P]
  [NormedCommRing Q] [IsUltrametricDist Q] {ρP : TwistElem P} {ρQ' : TwistElem Q}
  {w' : ℕ → ℕ} {N' : ℕ}

/-- The `C`-bounded coefficientwise map of null families (`TailC0.map` for
bounded — not necessarily nonexpansive — coefficient homs). -/
noncomputable def TailC0.mapC (φ : P →+* Q) {Cb : ℝ}
    (hφ : ∀ p, ‖φ p‖ ≤ Cb * ‖p‖) (hρ : φ ρP.val = ρQ'.val) :
    TailC0 w' N' P ρP →+* TailC0 w' N' Q ρQ' where
  toFun x := ⟨fun μ => φ (x.1 μ), by
    refine Filter.Tendsto.squeeze tendsto_const_nhds ?_
      (fun μ => norm_nonneg _) (fun μ => hφ (x.1 μ))
    have h2 := (x.2).const_mul Cb
    rwa [mul_zero] at h2⟩
  map_one' := by
    refine Subtype.ext (funext fun μ => ?_)
    show φ ((1 : TailC0 w' N' P ρP).1 μ) = (1 : TailC0 w' N' Q ρQ').1 μ
    rw [TailC0.one_val, TailC0.one_val]
    split_ifs
    · exact map_one φ
    · exact map_zero φ
  map_mul' x y := by
    refine Subtype.ext (funext fun τ => ?_)
    show φ ((x * y).1 τ) = _
    rw [TailC0.mul_val, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun p _ => ?_)
      (TailC0.mul_val _ _ τ).symm
    rw [map_mul, map_mul, map_pow, hρ]
  map_zero' := by
    refine Subtype.ext (funext fun μ => ?_)
    show φ ((0 : TailC0 w' N' P ρP).1 μ) = (0 : TailC0 w' N' Q ρQ').1 μ
    rw [show ((0 : TailC0 w' N' P ρP)).1 μ = 0 from rfl,
      show ((0 : TailC0 w' N' Q ρQ')).1 μ = 0 from rfl]
    exact map_zero φ
  map_add' x y := by
    refine Subtype.ext (funext fun μ => ?_)
    show φ ((x + y).1 μ) = _
    rw [show (x + y).1 μ = x.1 μ + y.1 μ from rfl, map_add]
    rfl

theorem TailC0.mapC_val (φ : P →+* Q) {Cb : ℝ}
    (hφ : ∀ p, ‖φ p‖ ≤ Cb * ‖p‖) (hρ : φ ρP.val = ρQ'.val)
    (x : TailC0 w' N' P ρP) (μ : TailIdx N') :
    (TailC0.mapC φ hφ hρ x).1 μ = φ (x.1 μ) := rfl

end MapC

variable {K w} in
open scoped Classical in
theorem PushedHeadData.lift_subset {C : RationalCoveringData (WPA K w)}
    (P : PushedHeadData C) (D : ↥C.covers) :
    rationalOpen (liftDatum (P.DHp D) (P.hDHp D)).T
      (liftDatum (P.DHp D) (P.hDHp D)).s ⊆
      rationalOpen (liftDatum P.DHb P.hDHb).T (liftDatum P.DHb P.hDHb).s := by
  rw [P.hopenp D, P.hopenb]
  exact C.hsubset D.1 D.2

variable {K w} in
theorem restrictionMapHom_coe_wpa (D D' : RationalLocData (WPA K w))
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (l : Localization.Away D.s) :
    restrictionMapHom D D' h (D.coeRingHom l) = restrictionMapAlg D D' h l := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe
    (restrictionMapAlg D D' h) (restrictionMapAlg_continuous D D' h) l

variable {K w} in
open scoped Classical in
theorem qRestrict_rhoQ {C : RationalCoveringData (WPA K w)}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (P : PushedHeadData C) (D : ↥C.covers) :
    qRestrict ϖ hK₀ P D (rhoQ P.DHb).val = (rhoQ (P.DHp D)).val := by
  rw [show (rhoQ P.DHb).val = headConst P.DHb (WaHead K w P.M) from rfl,
    qRestrict_headConst]
  rfl

/-- The `mapC` norm bound: the coefficient bound passes to the sup norm. -/
theorem TailC0.norm_mapC_le {P Q : Type*} [NormedCommRing P]
    [IsUltrametricDist P] [NormedCommRing Q] [IsUltrametricDist Q]
    {ρP : TwistElem P} {ρQ' : TwistElem Q} {w' : ℕ → ℕ} {N' : ℕ}
    (φ : P →+* Q) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hφ : ∀ p, ‖φ p‖ ≤ Cb * ‖p‖) (hρ : φ ρP.val = ρQ'.val)
    (x : TailC0 w' N' P ρP) :
    ‖TailC0.mapC (ρP := ρP) (ρQ' := ρQ') φ hφ hρ x‖ ≤ Cb * ‖x‖ := by
  rw [TailC0.norm_eq_iSup_coeff]
  refine ciSup_le fun μ => ?_
  rw [show TailC0.coeff μ (TailC0.mapC (ρP := ρP) (ρQ' := ρQ') φ hφ hρ x) =
    φ (x.1 μ) from rfl]
  refine le_trans (hφ (x.1 μ)) ?_
  exact mul_le_mul_of_nonneg_left (TailC0.norm_coeff_le x μ) hCb

variable {K w} in
open scoped Classical in
/-- **The bundled naturality square** ([WP] eq:cover-coefficientwise): the model
transports of the restriction map are coefficientwise `qRestrict`. -/
theorem coeffLoc_restriction_square {C : RationalCoveringData (WPA K w)}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (P : PushedHeadData C) (D : ↥C.covers) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hb : ∀ q, ‖qRestrict ϖ hK₀ P D q‖ ≤ Cb * ‖q‖) :
    (TailC0.mapC (qRestrict ϖ hK₀ P D) hb
        (qRestrict_rhoQ ϖ hK₀ P D)).comp
      (coeffLocEquiv ϖ hK₀ P.DHb P.hDHb).toRingHom =
    (coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).toRingHom.comp
      (restrictionMapHom (liftDatum P.DHb P.hDHb)
        (liftDatum (P.DHp D) (P.hDHp D)) (P.lift_subset D)) := by
  classical
  letI := (liftDatum P.DHb P.hDHb).uniformSpace
  have hdense : DenseRange (⇑(liftDatum P.DHb P.hDHb).coeRingHom) :=
    @UniformSpace.Completion.denseRange_coe _
      (liftDatum P.DHb P.hDHb).uniformSpace
  -- the algebraic-layer identity
  have halg : (TailC0.mapC (qRestrict ϖ hK₀ P D) hb
      (qRestrict_rhoQ ϖ hK₀ P D)).comp
        (coeffFwdAlg ϖ P.DHb P.hDHb) =
      (coeffFwd ϖ (P.DHp D) (P.hDHp D)).comp
        (restrictionMapAlg (liftDatum P.DHb P.hDHb)
          (liftDatum (P.DHp D) (P.hDHp D)) (P.lift_subset D)) := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers (liftDatum P.DHb P.hDHb).s) ?_
    ext f
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      RingHom.comp_apply, coeffFwdAlg_algebraMap]
    rw [show restrictionMapAlg (liftDatum P.DHb P.hDHb)
        (liftDatum (P.DHp D) (P.hDHp D)) (P.lift_subset D)
        (algebraMap (WPA K w)
          (Localization.Away (liftDatum P.DHb P.hDHb).s) f) =
      (liftDatum (P.DHp D) (P.hDHp D)).canonicalMap f from by
        rw [← restrictionMapHom_coe_wpa]
        exact restrictionMapHom_canonicalMap_generic _ _ _ f]
    rw [show (liftDatum (P.DHp D) (P.hDHp D)).canonicalMap f =
      (liftDatum (P.DHp D) (P.hDHp D)).coeRingHom
        (algebraMap (WPA K w)
          (Localization.Away (liftDatum (P.DHp D) (P.hDHp D)).s) f) from rfl,
      coeffFwd_coe, coeffFwdAlg_algebraMap]
    refine Subtype.ext (funext fun μ => ?_)
    show qRestrict ϖ hK₀ P D ((coeffBase P.DHb f).1 μ) =
      (coeffBase (P.DHp D) f).1 μ
    rw [show (coeffBase P.DHb f).1 μ =
      headConst P.DHb ((wpaTailEquiv (K := K) (w := w) (N := P.M) f).1 μ)
      from rfl, qRestrict_headConst]
    rfl
  -- lift to the completions by density
  refine RingHom.ext fun z => ?_
  have hfun : ⇑((TailC0.mapC (qRestrict ϖ hK₀ P D) hb
      (qRestrict_rhoQ ϖ hK₀ P D)).comp
        (coeffLocEquiv ϖ hK₀ P.DHb P.hDHb).toRingHom) =
      ⇑((coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).toRingHom.comp
        (restrictionMapHom (liftDatum P.DHb P.hDHb)
          (liftDatum (P.DHp D) (P.hDHp D)) (P.lift_subset D))) := by
    refine hdense.equalizer ?_ ?_ ?_
    · rw [RingHom.coe_comp]
      refine Continuous.comp ?_ ?_
      · exact AddMonoidHomClass.continuous_of_bound
          (TailC0.mapC (qRestrict ϖ hK₀ P D) hb
            (qRestrict_rhoQ ϖ hK₀ P D)) Cb
          (TailC0.norm_mapC_le _ hCb _ _)
      · exact coeffLocEquiv_continuous ϖ hK₀ P.DHb P.hDHb
    · rw [RingHom.coe_comp]
      refine Continuous.comp ?_ ?_
      · exact coeffLocEquiv_continuous ϖ hK₀ (P.DHp D) (P.hDHp D)
      · letI : UniformSpace (Localization.Away (liftDatum P.DHb P.hDHb).s) :=
          (liftDatum P.DHb P.hDHb).uniformSpace
        letI : IsTopologicalRing
            (Localization.Away (liftDatum P.DHb P.hDHb).s) :=
          (liftDatum P.DHb P.hDHb).isTopologicalRing
        letI : IsUniformAddGroup
            (Localization.Away (liftDatum P.DHb P.hDHb).s) :=
          (liftDatum P.DHb P.hDHb).isUniformAddGroup
        exact UniformSpace.Completion.continuous_extension
    · funext l
      show TailC0.mapC (qRestrict ϖ hK₀ P D) hb (qRestrict_rhoQ ϖ hK₀ P D)
        (coeffLocEquiv ϖ hK₀ P.DHb P.hDHb
          ((liftDatum P.DHb P.hDHb).coeRingHom l)) =
        coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)
          (restrictionMapHom (liftDatum P.DHb P.hDHb)
            (liftDatum (P.DHp D) (P.hDHp D)) (P.lift_subset D)
            ((liftDatum P.DHb P.hDHb).coeRingHom l))
      rw [show coeffLocEquiv ϖ hK₀ P.DHb P.hDHb
          ((liftDatum P.DHb P.hDHb).coeRingHom l) =
        coeffFwd ϖ P.DHb P.hDHb
          ((liftDatum P.DHb P.hDHb).coeRingHom l) from rfl, coeffFwd_coe]
      rw [restrictionMapHom_coe_wpa]
      exact RingHom.congr_fun halg l
  exact congrFun hfun z

variable {K w} in
open scoped Classical in
/-- The head-level restriction between graph models along a pushed covering
piece (the `headLocEquiv`-conjugated restriction map;
[WP] eq:cover-coefficientwise's coefficient hom). -/
noncomputable def qRestrictP {M : ℕ}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH DH' : RationalLocData (WPHead K w M)) (hDH : DH.IsRational)
    (hDH' : DH'.IsRational)
    (hsub : rationalOpen DH'.T DH'.s ⊆ rationalOpen DH.T DH.s) :
    QHead DH →+* QHead DH' :=
  ((headLocEquiv ϖ hK₀ DH' hDH').toRingHom.comp
    (restrictionMapHom DH DH' hsub)).comp
    (headLocEquiv ϖ hK₀ DH hDH).symm.toRingHom


variable {K w} in
open scoped Classical in
/-- `qRestrict` matches the head constants (the generator law of the
naturality square). -/
theorem qRestrictP_headConst {M : ℕ}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH DH' : RationalLocData (WPHead K w M)) (hDH : DH.IsRational)
    (hDH' : DH'.IsRational)
    (hsub : rationalOpen DH'.T DH'.s ⊆ rationalOpen DH.T DH.s) (x : WPHead K w M) :
    qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub (headConst DH x) =
      headConst DH' x := by
  have h1 : (headLocEquiv ϖ hK₀ DH hDH).symm (headConst DH x) =
      DH.canonicalMap x := by
    have h2 : headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap x) =
        headConst DH x := by
      rw [show headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap x) =
        headLocFwd ϖ DH hDH (DH.canonicalMap x) from rfl,
        show DH.canonicalMap x = DH.coeRingHom
          (algebraMap (WPHead K w M) (Localization.Away DH.s) x) from rfl,
        headLocFwd_coe, headLocFwdAlg_algebraMap]
    rw [← h2, RingEquiv.symm_apply_apply]
  show headLocEquiv ϖ hK₀ DH' hDH'
    (restrictionMapHom DH DH' hsub
      ((headLocEquiv ϖ hK₀ DH hDH).symm (headConst DH x))) =
    headConst DH' x
  rw [h1, restrictionMapHom_canonicalMap_generic]
  rw [show headLocEquiv ϖ hK₀ DH' hDH'
      (DH'.canonicalMap x) =
    headLocFwd ϖ DH' hDH' (DH'.canonicalMap x) from rfl,
    show DH'.canonicalMap x = DH'.coeRingHom
      (algebraMap (WPHead K w M) (Localization.Away DH'.s) x)
      from rfl,
    headLocFwd_coe, headLocFwdAlg_algebraMap]


variable {K w} in
open scoped Classical in
theorem qRestrictP_continuous {M : ℕ}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH DH' : RationalLocData (WPHead K w M)) (hDH : DH.IsRational)
    (hDH' : DH'.IsRational)
    (hsub : rationalOpen DH'.T DH'.s ⊆ rationalOpen DH.T DH.s) :
    Continuous (qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub) := by
  rw [qRestrictP, RingHom.coe_comp, RingHom.coe_comp]
  refine Continuous.comp (Continuous.comp ?_ ?_) ?_
  · exact headLocEquiv_continuous ϖ hK₀ DH' hDH'
  · letI : UniformSpace (Localization.Away DH.s) := DH.uniformSpace
    letI : IsTopologicalRing (Localization.Away DH.s) :=
      DH.isTopologicalRing
    letI : IsUniformAddGroup (Localization.Away DH.s) :=
      DH.isUniformAddGroup
    exact UniformSpace.Completion.continuous_extension
  · exact headLocEquiv_symm_continuous ϖ hK₀ DH hDH

variable {K w} in
open scoped Classical in
/-- The head restriction is bounded (continuity at `0` + the exact
nonarchimedean window scaling with `ℤ`-powers of the window constant). -/
theorem qRestrictP_bound {M : ℕ}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH DH' : RationalLocData (WPHead K w M)) (hDH : DH.IsRational)
    (hDH' : DH'.IsRational)
    (hsub : rationalOpen DH'.T DH'.s ⊆ rationalOpen DH.T DH.s) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ q : QHead DH,
      ‖qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub q‖ ≤ Cb * ‖q‖ := by
  classical
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  have hcne : c ≠ 0 := fun h => by
    rw [h, norm_zero] at hc0
    exact lt_irrefl 0 hc0
  have hcRne : ‖c‖ ≠ 0 := ne_of_gt hc0
  have hcont := (qRestrictP_continuous ϖ hK₀ DH DH' hDH hDH' hsub).tendsto 0
  rw [map_zero] at hcont
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp
    (hcont (Metric.ball_mem_nhds 0 one_pos))
  refine ⟨1 / (‖c‖ * δ), by positivity, fun q => ?_⟩
  rcases eq_or_lt_of_le (norm_nonneg q) with hq0 | hq0
  · rw [show q = 0 from by rw [← norm_eq_zero]; exact hq0.symm, map_zero,
      norm_zero, norm_zero, mul_zero]
  have hinv1 : (1 : ℝ) < ‖c‖⁻¹ := (one_lt_inv₀ hc0).mpr hc1
  obtain ⟨n, hn⟩ := exists_mem_Ico_zpow
    (x := ‖q‖ / δ) (by positivity) hinv1
  rw [Set.mem_Ico] at hn
  -- upper: ‖c‖^(n+1)·‖q‖ < δ
  have hupper : ‖c‖ ^ (n + 1 : ℤ) * ‖q‖ < δ := by
    have h2 := hn.2
    rw [div_lt_iff₀ hδ0] at h2
    have h3 := mul_lt_mul_of_pos_left h2 (zpow_pos hc0 (n + 1))
    rw [show ‖c‖ ^ (n + 1 : ℤ) * ((‖c‖⁻¹ : ℝ) ^ (n + 1 : ℤ) * δ) =
      (‖c‖ * ‖c‖⁻¹) ^ (n + 1 : ℤ) * δ from by
        rw [mul_zpow, mul_assoc],
      mul_inv_cancel₀ hcRne, one_zpow, one_mul] at h3
    exact h3
  -- lower: δ·‖c‖ ≤ ‖c‖^(n+1)·‖q‖
  have hlower : δ * ‖c‖ ≤ ‖c‖ ^ (n + 1 : ℤ) * ‖q‖ := by
    have h2 := hn.1
    rw [le_div_iff₀ hδ0] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt (zpow_pos hc0 (n + 1)))
    rw [show ‖c‖ ^ (n + 1 : ℤ) * ((‖c‖⁻¹ : ℝ) ^ (n : ℤ) * δ) =
      ‖c‖ ^ (n + 1 : ℤ) * (‖c‖ ^ (n : ℤ))⁻¹ * δ from by
        rw [inv_zpow, mul_assoc],
      show ‖c‖ ^ (n + 1 : ℤ) * (‖c‖ ^ (n : ℤ))⁻¹ =
        ‖c‖ ^ (n + 1 - n : ℤ) from by
        rw [zpow_sub₀ hcRne, div_eq_mul_inv],
      show (n + 1 - n : ℤ) = 1 from by ring,
      zpow_one] at h3
    calc δ * ‖c‖ = ‖c‖ * δ := by ring
      _ ≤ ‖c‖ ^ (n + 1 : ℤ) * ‖q‖ := h3
  -- the scaled element
  set a : K := c ^ (n + 1 : ℤ) with ha_def
  have hna : ‖a‖ = ‖c‖ ^ (n + 1 : ℤ) := by rw [ha_def, norm_zpow]
  have hna0 : 0 < ‖a‖ := by rw [hna]; exact zpow_pos hc0 _
  have hmem : ‖qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub
      (headConst DH (constHead K w M a) * q)‖ < 1 := by
    have h4 : headConst DH (constHead K w M a) * q ∈
        Metric.ball (0 : QHead DH) δ := by
      rw [Metric.mem_ball, dist_zero_right, norm_qscale DH hna0 q, hna]
      exact hupper
    have h5 := hball h4
    rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at h5
    exact h5
  rw [map_mul, qRestrictP_headConst,
    norm_qscale DH' hna0 _, hna] at hmem
  -- extract the bound
  have hpow : (0 : ℝ) < ‖c‖ ^ (n + 1 : ℤ) := zpow_pos hc0 _
  have h6 : ‖qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub q‖ < (‖c‖ ^ (n + 1 : ℤ))⁻¹ :=
    calc ‖qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub q‖ = (‖c‖ ^ (n + 1 : ℤ))⁻¹ *
          (‖c‖ ^ (n + 1 : ℤ) * ‖qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub q‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpow), one_mul]
      _ < (‖c‖ ^ (n + 1 : ℤ))⁻¹ * 1 :=
          mul_lt_mul_of_pos_left hmem (by positivity)
      _ = (‖c‖ ^ (n + 1 : ℤ))⁻¹ := mul_one _
  refine le_trans h6.le ?_
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity : (0:ℝ) < ‖c‖ * δ)]
  calc (‖c‖ ^ (n + 1 : ℤ))⁻¹ * (‖c‖ * δ)
      ≤ (‖c‖ ^ (n + 1 : ℤ))⁻¹ * (‖c‖ ^ (n + 1 : ℤ) * ‖q‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖c‖ * δ = δ * ‖c‖ := by ring
          _ ≤ ‖c‖ ^ (n + 1 : ℤ) * ‖q‖ := hlower
    _ = ‖q‖ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpow), one_mul]


variable {K w} in
open scoped Classical in
theorem qRestrictP_rhoQ {M : ℕ}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH DH' : RationalLocData (WPHead K w M)) (hDH : DH.IsRational)
    (hDH' : DH'.IsRational)
    (hsub : rationalOpen DH'.T DH'.s ⊆ rationalOpen DH.T DH.s) :
    qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub (rhoQ DH).val = (rhoQ DH').val := by
  rw [show (rhoQ DH).val = headConst DH (WaHead K w M) from rfl,
    qRestrictP_headConst]
  rfl


variable {K w} in
open scoped Classical in
/-- **The bundled naturality square** ([WP] eq:cover-coefficientwise): the model
transports of the restriction map are coefficientwise `qRestrict`. -/
theorem coeffLoc_restriction_squareP {M : ℕ}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH DH' : RationalLocData (WPHead K w M)) (hDH : DH.IsRational)
    (hDH' : DH'.IsRational)
    (hsub : rationalOpen DH'.T DH'.s ⊆ rationalOpen DH.T DH.s)
    (hlift : rationalOpen (liftDatum DH' hDH').T (liftDatum DH' hDH').s ⊆
      rationalOpen (liftDatum DH hDH).T (liftDatum DH hDH).s) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hb : ∀ q, ‖qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub q‖ ≤ Cb * ‖q‖) :
    (TailC0.mapC (qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub) hb
        (qRestrictP_rhoQ ϖ hK₀ DH DH' hDH hDH' hsub)).comp
      (coeffLocEquiv ϖ hK₀ DH hDH).toRingHom =
    (coeffLocEquiv ϖ hK₀ DH' hDH').toRingHom.comp
      (restrictionMapHom (liftDatum DH hDH)
        (liftDatum DH' hDH') hlift) := by
  classical
  letI := (liftDatum DH hDH).uniformSpace
  have hdense : DenseRange (⇑(liftDatum DH hDH).coeRingHom) :=
    @UniformSpace.Completion.denseRange_coe _
      (liftDatum DH hDH).uniformSpace
  -- the algebraic-layer identity
  have halg : (TailC0.mapC (qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub) hb
      (qRestrictP_rhoQ ϖ hK₀ DH DH' hDH hDH' hsub)).comp
        (coeffFwdAlg ϖ DH hDH) =
      (coeffFwd ϖ DH' hDH').comp
        (restrictionMapAlg (liftDatum DH hDH)
          (liftDatum DH' hDH') hlift) := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers (liftDatum DH hDH).s) ?_
    ext f
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      RingHom.comp_apply, coeffFwdAlg_algebraMap]
    rw [show restrictionMapAlg (liftDatum DH hDH)
        (liftDatum DH' hDH') hlift
        (algebraMap (WPA K w)
          (Localization.Away (liftDatum DH hDH).s) f) =
      (liftDatum DH' hDH').canonicalMap f from by
        rw [← restrictionMapHom_coe_wpa]
        exact restrictionMapHom_canonicalMap_generic _ _ _ f]
    rw [show (liftDatum DH' hDH').canonicalMap f =
      (liftDatum DH' hDH').coeRingHom
        (algebraMap (WPA K w)
          (Localization.Away (liftDatum DH' hDH').s) f) from rfl,
      coeffFwd_coe, coeffFwdAlg_algebraMap]
    refine Subtype.ext (funext fun μ => ?_)
    show qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub ((coeffBase DH f).1 μ) =
      (coeffBase DH' f).1 μ
    rw [show (coeffBase DH f).1 μ =
      headConst DH ((wpaTailEquiv (K := K) (w := w) (N := M) f).1 μ)
      from rfl, qRestrictP_headConst]
    rfl
  -- lift to the completions by density
  refine RingHom.ext fun z => ?_
  have hfun : ⇑((TailC0.mapC (qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub) hb
      (qRestrictP_rhoQ ϖ hK₀ DH DH' hDH hDH' hsub)).comp
        (coeffLocEquiv ϖ hK₀ DH hDH).toRingHom) =
      ⇑((coeffLocEquiv ϖ hK₀ DH' hDH').toRingHom.comp
        (restrictionMapHom (liftDatum DH hDH)
          (liftDatum DH' hDH') hlift)) := by
    refine hdense.equalizer ?_ ?_ ?_
    · rw [RingHom.coe_comp]
      refine Continuous.comp ?_ ?_
      · exact AddMonoidHomClass.continuous_of_bound
          (TailC0.mapC (qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub) hb
            (qRestrictP_rhoQ ϖ hK₀ DH DH' hDH hDH' hsub)) Cb
          (TailC0.norm_mapC_le _ hCb _ _)
      · exact coeffLocEquiv_continuous ϖ hK₀ DH hDH
    · rw [RingHom.coe_comp]
      refine Continuous.comp ?_ ?_
      · exact coeffLocEquiv_continuous ϖ hK₀ DH' hDH'
      · letI : UniformSpace (Localization.Away (liftDatum DH hDH).s) :=
          (liftDatum DH hDH).uniformSpace
        letI : IsTopologicalRing
            (Localization.Away (liftDatum DH hDH).s) :=
          (liftDatum DH hDH).isTopologicalRing
        letI : IsUniformAddGroup
            (Localization.Away (liftDatum DH hDH).s) :=
          (liftDatum DH hDH).isUniformAddGroup
        exact UniformSpace.Completion.continuous_extension
    · funext l
      show TailC0.mapC (qRestrictP ϖ hK₀ DH DH' hDH hDH' hsub) hb (qRestrictP_rhoQ ϖ hK₀ DH DH' hDH hDH' hsub)
        (coeffLocEquiv ϖ hK₀ DH hDH
          ((liftDatum DH hDH).coeRingHom l)) =
        coeffLocEquiv ϖ hK₀ DH' hDH'
          (restrictionMapHom (liftDatum DH hDH)
            (liftDatum DH' hDH') hlift
            ((liftDatum DH hDH).coeRingHom l))
      rw [show coeffLocEquiv ϖ hK₀ DH hDH
          ((liftDatum DH hDH).coeRingHom l) =
        coeffFwd ϖ DH hDH
          ((liftDatum DH hDH).coeRingHom l) from rfl, coeffFwd_coe]
      rw [restrictionMapHom_coe_wpa]
      exact RingHom.congr_fun halg l
  exact congrFun hfun z


variable {K w} in
open scoped Classical in
/-- **The pushed head covering** ([WP] 1156–1218): a rational covering of `𝒜`
with common-stage head data transfers to a rational covering on the head, with
subset and covering properties by the `rhoHead` pullback. -/
theorem exists_pushedHeadCover (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational) :
    ∃ (M : ℕ) (C' : RationalCoveringData (WPHead K w M)), C'.IsRational := by
  classical
  obtain ⟨M, ⟨DHb, hDHb, hopenb⟩, hp⟩ :=
    exists_common_headModel_stage ϖ hK₀ C hC
  choose DHp hDHp hopenp using fun (D : ↥C.covers) => hp D.1 D.2
  refine ⟨M, ⟨DHb, C.covers.attach.image DHp, ?_, ?_⟩, ?_, ?_⟩
  · -- hsubset
    intro DH' hDH'
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hDH'
    intro v hv
    have hvspa : v ∈ Spa (WPHead K w M) ((WPHead K w M)⁺) := hv.1
    have h1 := (comap_rhoHead_mem_iff M (DHp D) (hDHp D) v hvspa).mpr hv
    rw [hopenp D] at h1
    have h2 := C.hsubset D.1 D.2 h1
    rw [← hopenb] at h2
    exact (comap_rhoHead_mem_iff M DHb hDHb v hvspa).mp h2
  · -- hcover
    intro v hv
    have hvspa : v ∈ Spa (WPHead K w M) ((WPHead K w M)⁺) := hv.1
    have h1 := (comap_rhoHead_mem_iff M DHb hDHb v hvspa).mpr hv
    rw [hopenb] at h1
    obtain ⟨D, hD, hmem⟩ := C.hcover _ h1
    refine ⟨DHp ⟨D, hD⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), ?_⟩
    have h2 : ValuationSpectrum.comap (rhoHead K w M) v ∈
        rationalOpen (liftDatum (DHp ⟨D, hD⟩) (hDHp ⟨D, hD⟩)).T
          (liftDatum (DHp ⟨D, hD⟩) (hDHp ⟨D, hD⟩)).s := by
      rw [hopenp ⟨D, hD⟩]
      exact hmem
    exact (comap_rhoHead_mem_iff M (DHp ⟨D, hD⟩) (hDHp ⟨D, hD⟩) v hvspa).mp h2
  · -- base rational
    exact hDHb
  · -- pieces rational
    intro DH' hDH'
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hDH'
    exact hDHp D

variable {K w} in
open scoped Classical in
/-- The piece model of a section: transport to the lifted datum (equal opens)
and take the coefficientwise model ([WP] 1156–1218). -/
noncomputable def pieceModel {C : RationalCoveringData (WPA K w)}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (P : PushedHeadData C) (D : ↥C.covers) (x : presheafValue D.1) :
    TailC0 w P.M (QHead (P.DHp D)) (rhoQ (P.DHp D)) :=
  coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)
    (restrictionMapHom D.1 (liftDatum (P.DHp D) (P.hDHp D))
      (P.hopenp D).le x)

variable {K w} in
open scoped Classical in
/-- **The pushed Čech compatibility** ([WP] 1156–1218): the per-coefficient
head sections of a compatible family are compatible on the pushed covering —
factor an arbitrary `D₃` through the rational head intersection, then compare
there via the naturality square and the `𝒜`-level compatibility at the lifted
intersection. -/
theorem pushedCompat_head {C : RationalCoveringData (WPA K w)}
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (P : PushedHeadData C)
    (f : ∀ D : ↥C.covers, presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData (WPA K w))
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂))
    (μ : TailIdx P.M) (D₁ D₂ : ↥C.covers)
    (D₃ : RationalLocData (WPHead K w P.M))
    (h₃₁ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (P.DHp D₁).T (P.DHp D₁).s)
    (h₃₂ : rationalOpen D₃.T D₃.s ⊆
      rationalOpen (P.DHp D₂).T (P.DHp D₂).s) :
    restrictionMap (P.DHp D₁) D₃ h₃₁
      ((headLocEquiv ϖ hK₀ (P.DHp D₁) (P.hDHp D₁)).symm
        (TailC0.coeff μ (pieceModel ϖ hK₀ P D₁ (f D₁)))) =
    restrictionMap (P.DHp D₂) D₃ h₃₂
      ((headLocEquiv ϖ hK₀ (P.DHp D₂) (P.hDHp D₂)).symm
        (TailC0.coeff μ (pieceModel ϖ hK₀ P D₂ (f D₂)))) := by
  classical
  set I := interDatumHead (P.DHp D₁) (P.DHp D₂) (P.hDHp D₁) (P.hDHp D₂)
    with hI
  have hIrat : I.IsRational :=
    interDatumHead_isRational (P.hDHp D₁) (P.hDHp D₂)
  have hIopen := rationalOpen_interDatumHead (P.DHp D₁) (P.DHp D₂)
    (P.hDHp D₁) (P.hDHp D₂)
  have hsubI₁ : rationalOpen I.T I.s ⊆
      rationalOpen (P.DHp D₁).T (P.DHp D₁).s := by
    rw [hI, hIopen]; exact Set.inter_subset_left
  have hsubI₂ : rationalOpen I.T I.s ⊆
      rationalOpen (P.DHp D₂).T (P.DHp D₂).s := by
    rw [hI, hIopen]; exact Set.inter_subset_right
  have h₃I : rationalOpen D₃.T D₃.s ⊆ rationalOpen I.T I.s := by
    rw [hI, hIopen]; exact Set.subset_inter h₃₁ h₃₂
  have hlift₁ : rationalOpen (liftDatum I hIrat).T (liftDatum I hIrat).s ⊆
      rationalOpen (liftDatum (P.DHp D₁) (P.hDHp D₁)).T
        (liftDatum (P.DHp D₁) (P.hDHp D₁)).s :=
    liftDatum_mono (P.DHp D₁) I (P.hDHp D₁) hIrat hsubI₁
  have hlift₂ : rationalOpen (liftDatum I hIrat).T (liftDatum I hIrat).s ⊆
      rationalOpen (liftDatum (P.DHp D₂) (P.hDHp D₂)).T
        (liftDatum (P.DHp D₂) (P.hDHp D₂)).s :=
    liftDatum_mono (P.DHp D₂) I (P.hDHp D₂) hIrat hsubI₂
  -- the lifted-intersection restrictions of the two sections agree
  have hxeq : restrictionMapHom (liftDatum (P.DHp D₁) (P.hDHp D₁))
      (liftDatum I hIrat) hlift₁
      (restrictionMapHom D₁.1 (liftDatum (P.DHp D₁) (P.hDHp D₁))
        (P.hopenp D₁).le (f D₁)) =
    restrictionMapHom (liftDatum (P.DHp D₂) (P.hDHp D₂))
      (liftDatum I hIrat) hlift₂
      (restrictionMapHom D₂.1 (liftDatum (P.DHp D₂) (P.hDHp D₂))
        (P.hopenp D₂).le (f D₂)) := by
    have hc₁ := congr_fun (restrictionMap_comp D₁.1
      (liftDatum (P.DHp D₁) (P.hDHp D₁)) (liftDatum I hIrat)
      (P.hopenp D₁).le hlift₁) (f D₁)
    have hc₂ := congr_fun (restrictionMap_comp D₂.1
      (liftDatum (P.DHp D₂) (P.hDHp D₂)) (liftDatum I hIrat)
      (P.hopenp D₂).le hlift₂) (f D₂)
    simp only [Function.comp_apply] at hc₁ hc₂
    rw [show restrictionMapHom (liftDatum (P.DHp D₁) (P.hDHp D₁))
        (liftDatum I hIrat) hlift₁
        (restrictionMapHom D₁.1 (liftDatum (P.DHp D₁) (P.hDHp D₁))
          (P.hopenp D₁).le (f D₁)) =
      restrictionMap D₁.1 (liftDatum I hIrat)
        (hlift₁.trans (P.hopenp D₁).le) (f D₁) from hc₁]
    rw [show restrictionMapHom (liftDatum (P.DHp D₂) (P.hDHp D₂))
        (liftDatum I hIrat) hlift₂
        (restrictionMapHom D₂.1 (liftDatum (P.DHp D₂) (P.hDHp D₂))
          (P.hopenp D₂).le (f D₂)) =
      restrictionMap D₂.1 (liftDatum I hIrat)
        (hlift₂.trans (P.hopenp D₂).le) (f D₂) from hc₂]
    exact hcompat D₁ D₂ (liftDatum I hIrat)
      (hlift₁.trans (P.hopenp D₁).le) (hlift₂.trans (P.hopenp D₂).le)
  -- the head-restriction of a piece coefficient is the model coefficient of
  -- the lifted restriction (one side of the naturality square)
  have hside : ∀ (D : ↥C.covers)
      (hsubI : rationalOpen I.T I.s ⊆
        rationalOpen (P.DHp D).T (P.DHp D).s)
      (hlift : rationalOpen (liftDatum I hIrat).T (liftDatum I hIrat).s ⊆
        rationalOpen (liftDatum (P.DHp D) (P.hDHp D)).T
          (liftDatum (P.DHp D) (P.hDHp D)).s),
      restrictionMapHom (P.DHp D) I hsubI
        ((headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).symm
          (TailC0.coeff μ (pieceModel ϖ hK₀ P D (f D)))) =
      (headLocEquiv ϖ hK₀ I hIrat).symm
        (TailC0.coeff μ (coeffLocEquiv ϖ hK₀ I hIrat
          (restrictionMapHom (liftDatum (P.DHp D) (P.hDHp D))
            (liftDatum I hIrat) hlift
            (restrictionMapHom D.1 (liftDatum (P.DHp D) (P.hDHp D))
              (P.hopenp D).le (f D))))) := by
    intro D hsubI hlift
    obtain ⟨Cb, hCb0, hb⟩ := qRestrictP_bound ϖ hK₀ (P.DHp D) I
      (P.hDHp D) hIrat hsubI
    have hsq := RingHom.congr_fun
      (coeffLoc_restriction_squareP ϖ hK₀ (P.DHp D) I (P.hDHp D) hIrat
        hsubI hlift hCb0.le hb)
      (restrictionMapHom D.1 (liftDatum (P.DHp D) (P.hDHp D))
        (P.hopenp D).le (f D))
    have h2 := congrArg (fun t => TailC0.coeff μ t) hsq
    have h3 : qRestrictP ϖ hK₀ (P.DHp D) I (P.hDHp D) hIrat hsubI
        (TailC0.coeff μ (pieceModel ϖ hK₀ P D (f D))) =
      TailC0.coeff μ (coeffLocEquiv ϖ hK₀ I hIrat
        (restrictionMapHom (liftDatum (P.DHp D) (P.hDHp D))
          (liftDatum I hIrat) hlift
          (restrictionMapHom D.1 (liftDatum (P.DHp D) (P.hDHp D))
            (P.hopenp D).le (f D)))) := h2.trans rfl
    have h4 := congrArg (headLocEquiv ϖ hK₀ I hIrat).symm h3
    rw [show (headLocEquiv ϖ hK₀ I hIrat).symm
        (qRestrictP ϖ hK₀ (P.DHp D) I (P.hDHp D) hIrat hsubI
          (TailC0.coeff μ (pieceModel ϖ hK₀ P D (f D)))) =
      (headLocEquiv ϖ hK₀ I hIrat).symm
        ((headLocEquiv ϖ hK₀ I hIrat)
          (restrictionMapHom (P.DHp D) I hsubI
            ((headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).symm
              (TailC0.coeff μ (pieceModel ϖ hK₀ P D (f D))))))
      from rfl, RingEquiv.symm_apply_apply] at h4
    exact h4
  have hs₁ := hside D₁ hsubI₁ hlift₁
  have hs₂ := hside D₂ hsubI₂ hlift₂
  rw [hxeq] at hs₁
  -- factor the D₃ restrictions through I
  have hfac₁ := congrFun (restrictionMap_comp (P.DHp D₁) I D₃ hsubI₁ h₃I)
    ((headLocEquiv ϖ hK₀ (P.DHp D₁) (P.hDHp D₁)).symm
      (TailC0.coeff μ (pieceModel ϖ hK₀ P D₁ (f D₁))))
  have hfac₂ := congrFun (restrictionMap_comp (P.DHp D₂) I D₃ hsubI₂ h₃I)
    ((headLocEquiv ϖ hK₀ (P.DHp D₂) (P.hDHp D₂)).symm
      (TailC0.coeff μ (pieceModel ϖ hK₀ P D₂ (f D₂))))
  simp only [Function.comp_apply] at hfac₁ hfac₂
  rw [← hfac₁, ← hfac₂]
  exact congrArg (restrictionMap I D₃ h₃I) (hs₁.trans hs₂.symm)

variable {K w} in
open scoped Classical in
/-- **Separation for `𝒜`** ([WP] 1135–1155): a section vanishing on all pieces
vanishes — walk the model coefficients through the naturality square and apply
the head separation on the pushed covering. -/
theorem productRestrictionSub_injective_WPA (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational) :
    Function.Injective (productRestrictionSub (WPA K w) C) := by
  classical
  intro x y hxy
  set z := x - y with hz
  have hres : ∀ D : ↥C.covers,
      restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) z = 0 := by
    intro D
    have hDx := congrFun hxy D
    rw [hz, map_sub,
      show restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) x =
        productRestrictionSub (WPA K w) C x D from rfl,
      show restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) y =
        productRestrictionSub (WPA K w) C y D from rfl, hDx, sub_self]
  obtain ⟨P⟩ := nonempty_pushedHeadData ϖ hK₀ C hC
  haveI hSheafHead : ValuationSpectrum.IsSheafy (WPHead K w P.M) :=
    isSheafy_WPHead (w := w) (N := P.M) ϖ hK₀
  set eb := restrictionEquiv C.base (liftDatum P.DHb P.hDHb) P.hopenb with heb
  set zb := coeffLocEquiv ϖ hK₀ P.DHb P.hDHb (eb z) with hzb
  have hcoeff : ∀ (μ : TailIdx P.M) (D : ↥C.covers),
      qRestrict ϖ hK₀ P D (TailC0.coeff μ zb) = 0 := by
    intro μ D
    obtain ⟨Cb, hCb0, hbD⟩ := qRestrict_bound ϖ hK₀ P D
    have hzero : restrictionMapHom (liftDatum P.DHb P.hDHb)
        (liftDatum (P.DHp D) (P.hDHp D)) (P.lift_subset D) (eb z) = 0 := by
      have hc1 := congr_fun (restrictionMap_comp C.base
        (liftDatum P.DHb P.hDHb) (liftDatum (P.DHp D) (P.hDHp D))
        P.hopenb.le (P.lift_subset D)) z
      have hc2 := congr_fun (restrictionMap_comp C.base D.1
        (liftDatum (P.DHp D) (P.hDHp D)) (C.hsubset D.1 D.2)
        (P.hopenp D).le) z
      rw [show eb z = restrictionMapHom C.base (liftDatum P.DHb P.hDHb)
        P.hopenb.le z from rfl]
      rw [show restrictionMapHom (liftDatum P.DHb P.hDHb)
          (liftDatum (P.DHp D) (P.hDHp D)) (P.lift_subset D)
          (restrictionMapHom C.base (liftDatum P.DHb P.hDHb)
            P.hopenb.le z) =
        restrictionMap C.base (liftDatum (P.DHp D) (P.hDHp D))
          ((P.lift_subset D).trans P.hopenb.le) z from hc1]
      rw [show restrictionMap C.base (liftDatum (P.DHp D) (P.hDHp D))
          ((P.lift_subset D).trans P.hopenb.le) z =
        restrictionMapHom D.1 (liftDatum (P.DHp D) (P.hDHp D))
          (P.hopenp D).le
          (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) z)
        from hc2.symm]
      rw [hres D, map_zero]
    have hsq := RingHom.congr_fun
      (coeffLoc_restriction_square ϖ hK₀ P D hCb0.le hbD) (eb z)
    rw [RingHom.comp_apply, RingHom.comp_apply, hzero, map_zero] at hsq
    have h2 := congrArg (fun t => TailC0.coeff μ t) hsq
    exact h2.trans rfl
  have hqz : ∀ μ : TailIdx P.M, TailC0.coeff μ zb = 0 := by
    intro μ
    set pμ := (headLocEquiv ϖ hK₀ P.DHb P.hDHb).symm (TailC0.coeff μ zb)
      with hpμ
    have hpres : ∀ D' : ↥(P.cover.covers),
        restrictionMapHom P.cover.base D'.1
          (P.cover.hsubset D'.1 D'.2) pμ = 0 := by
      rintro ⟨D', hD'⟩
      obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hD'
      have h3 := hcoeff μ D
      rw [qRestrict, RingHom.comp_apply, RingHom.comp_apply] at h3
      have h5 := congrArg
        (headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).symm h3
      rw [show (headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).symm
          ((headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).toRingHom
            (restrictionMapHom P.DHb (P.DHp D) (P.piece_subset D)
              ((headLocEquiv ϖ hK₀ P.DHb P.hDHb).symm.toRingHom
                (TailC0.coeff μ zb)))) =
        restrictionMapHom P.DHb (P.DHp D) (P.piece_subset D)
          ((headLocEquiv ϖ hK₀ P.DHb P.hDHb).symm.toRingHom
            (TailC0.coeff μ zb)) from
        RingEquiv.symm_apply_apply _ _, map_zero] at h5
      exact h5
    have h6 : productRestrictionSub (WPHead K w P.M) P.cover pμ =
        productRestrictionSub (WPHead K w P.M) P.cover 0 := by
      funext D'
      rw [show productRestrictionSub (WPHead K w P.M) P.cover pμ D' =
        restrictionMapHom P.cover.base D'.1
          (P.cover.hsubset D'.1 D'.2) pμ from rfl, hpres D',
        show productRestrictionSub (WPHead K w P.M) P.cover 0 D' =
          restrictionMapHom P.cover.base D'.1
            (P.cover.hsubset D'.1 D'.2) 0 from rfl, map_zero]
    have h7 := ValuationSpectrum.IsSheafy.separationSub
      (A := WPHead K w P.M) P.cover P.cover_isRational h6
    have h7' : pμ = (0 : presheafValue P.DHb) := h7
    have h8 := congrArg (headLocEquiv ϖ hK₀ P.DHb P.hDHb) h7'
    rw [hpμ] at h8
    rw [RingEquiv.apply_symm_apply, map_zero] at h8
    exact h8
  have hzb0 : zb = 0 := by
    refine Subtype.ext (funext fun μ => ?_)
    exact hqz μ
  have hz0 : z = 0 := by
    have h10 : coeffLocEquiv ϖ hK₀ P.DHb P.hDHb (eb z) = 0 := by
      rw [← hzb]
      exact hzb0
    have h11 := congrArg (coeffLocEquiv ϖ hK₀ P.DHb P.hDHb).symm h10
    rw [RingEquiv.symm_apply_apply, map_zero] at h11
    have h12 := congrArg
      (restrictionEquiv C.base (liftDatum P.DHb P.hDHb) P.hopenb).symm h11
    rw [show (restrictionEquiv C.base (liftDatum P.DHb P.hDHb)
        P.hopenb).symm (eb z) =
      (restrictionEquiv C.base (liftDatum P.DHb P.hDHb) P.hopenb).symm
        (restrictionEquiv C.base (liftDatum P.DHb P.hDHb) P.hopenb z)
      from rfl, RingEquiv.symm_apply_apply, map_zero] at h12
    exact h12
  rw [hz] at hz0
  exact sub_eq_zero.mp hz0

variable {K w} in
/-- The gluing half of the sheaf condition for `𝒜` (the `gluing_JetA` shape,
`FJP/Over/SheafTransfer.lean:376`; [WP] proof of thm:parity-strongly-sheafy,
coefficientwise Čech gluing with the head bound `C`). -/
theorem gluing_WPA (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational)
    (f : ∀ D : ↥C.covers, presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData (WPA K w))
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ D : ↥C.covers,
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by
  classical
  obtain ⟨P⟩ := nonempty_pushedHeadData ϖ hK₀ C hC
  haveI hSheafHead : ValuationSpectrum.IsSheafy (WPHead K w P.M) :=
    isSheafy_WPHead (w := w) (N := P.M) ϖ hK₀
  -- the pushed per-coefficient families ([WP] eq:head-cech)
  set g : TailIdx P.M → ∀ D' : ↥(P.cover.covers), presheafValue D'.1 :=
    fun μ D' => (Finset.mem_image.mp D'.2).choose_spec.2 ▸
      ((headLocEquiv ϖ hK₀ (P.DHp (Finset.mem_image.mp D'.2).choose)
          (P.hDHp (Finset.mem_image.mp D'.2).choose)).symm
        (TailC0.coeff μ (pieceModel ϖ hK₀ P
          (Finset.mem_image.mp D'.2).choose
          (f (Finset.mem_image.mp D'.2).choose)))) with hg
  have hgres : ∀ (μ : TailIdx P.M) (D' : ↥(P.cover.covers))
      (D₃ : RationalLocData (WPHead K w P.M))
      (h₃ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D'.1.T D'.1.s),
      restrictionMap D'.1 D₃ h₃ (g μ D') =
        restrictionMap (P.DHp (Finset.mem_image.mp D'.2).choose) D₃
          (by rw [(Finset.mem_image.mp D'.2).choose_spec.2]; exact h₃)
          ((headLocEquiv ϖ hK₀ (P.DHp (Finset.mem_image.mp D'.2).choose)
              (P.hDHp (Finset.mem_image.mp D'.2).choose)).symm
            (TailC0.coeff μ (pieceModel ϖ hK₀ P
              (Finset.mem_image.mp D'.2).choose
              (f (Finset.mem_image.mp D'.2).choose)))) := by
    intro μ D' D₃ h₃
    show restrictionMap D'.1 D₃ h₃
      ((Finset.mem_image.mp D'.2).choose_spec.2 ▸ _) = _
    rw [restrictionMap_cast _ _ (Finset.mem_image.mp D'.2).choose_spec.2]
    have hcomp := congrFun (restrictionMap_comp
      (P.DHp (Finset.mem_image.mp D'.2).choose) D'.1 D₃
      (by rw [(Finset.mem_image.mp D'.2).choose_spec.2]) h₃)
      ((headLocEquiv ϖ hK₀ (P.DHp (Finset.mem_image.mp D'.2).choose)
          (P.hDHp (Finset.mem_image.mp D'.2).choose)).symm
        (TailC0.coeff μ (pieceModel ϖ hK₀ P
          (Finset.mem_image.mp D'.2).choose
          (f (Finset.mem_image.mp D'.2).choose))))
    simp only [Function.comp_apply] at hcomp
    exact hcomp
  -- per-μ vertex gluing at the head
  have hglue : ∀ μ : TailIdx P.M, ∃ q : presheafValue P.cover.base,
      ∀ D' : ↥(P.cover.covers),
        restrictionMap P.cover.base D'.1 (P.cover.hsubset D'.1 D'.2) q =
          g μ D' :=
    fun μ => ValuationSpectrum.IsSheafy.gluing (A := WPHead K w P.M)
      P.cover P.cover_isRational (g μ) (by
        intro D₁' D₂' D₃ h₃₁ h₃₂
        rw [hgres μ D₁' D₃ h₃₁, hgres μ D₂' D₃ h₃₂]
        exact pushedCompat_head ϖ hK₀ P f hcompat μ _ _ D₃ _ _)
  choose q hq using hglue
  set q2 : TailIdx P.M → presheafValue P.DHb := fun μ => q μ with hq2def
  have hq2 : ∀ (μ : TailIdx P.M) (D' : ↥(P.cover.covers)),
      restrictionMap (D := P.DHb) D'.1 (P.cover.hsubset D'.1 D'.2) (q2 μ) =
        g μ D' := hq
  -- the value of the pushed family at a canonical piece index
  have hmemp : ∀ d : ↥C.covers, P.DHp d ∈ P.cover.covers := fun d =>
    Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
  have hgd : ∀ (μ : TailIdx P.M) (d : ↥C.covers),
      g μ ⟨P.DHp d, hmemp d⟩ =
        (headLocEquiv ϖ hK₀ (P.DHp d) (P.hDHp d)).symm
          (TailC0.coeff μ (pieceModel ϖ hK₀ P d (f d))) := by
    intro μ d
    have hself := hgres μ ⟨P.DHp d, hmemp d⟩ (P.DHp d) (subset_refl _)
    rw [congrFun (restrictionMap_id (P.DHp d)) _] at hself
    simp only [id_eq] at hself
    rw [hself]
    have hpc := pushedCompat_head ϖ hK₀ P f hcompat μ
      (Finset.mem_image.mp (hmemp d)).choose d (P.DHp d)
      (by rw [(Finset.mem_image.mp (hmemp d)).choose_spec.2])
      (subset_refl _)
    rw [hpc, congrFun (restrictionMap_id (P.DHp d)) _]
    simp only [id_eq]
  -- nullity of the glued family, via the inducing head embedding
  have hembed : Topology.IsEmbedding
      (productRestrictionSub (WPHead K w P.M) P.cover) :=
    ValuationSpectrum.IsSheafy.embedding (A := WPHead K w P.M)
      P.cover P.cover_isRational
  have hq0 : Filter.Tendsto q Filter.cofinite (nhds 0) := by
    rw [hembed.isInducing.tendsto_nhds_iff]
    have h0img : productRestrictionSub (WPHead K w P.M) P.cover 0 = 0 :=
      funext fun D' => map_zero _
    rw [h0img]
    rw [tendsto_pi_nhds]
    intro D'
    refine Filter.Tendsto.congr
      (f₁ := fun μ => g μ D') (fun μ => (hq μ D').symm) ?_
    -- the fixed-piece family tends to 0
    have hcast : ∀ μ, g μ D' =
        restrictionMap (P.DHp (Finset.mem_image.mp D'.2).choose) D'.1
          (by rw [(Finset.mem_image.mp D'.2).choose_spec.2])
          ((headLocEquiv ϖ hK₀ (P.DHp (Finset.mem_image.mp D'.2).choose)
              (P.hDHp (Finset.mem_image.mp D'.2).choose)).symm
            (TailC0.coeff μ (pieceModel ϖ hK₀ P
              (Finset.mem_image.mp D'.2).choose
              (f (Finset.mem_image.mp D'.2).choose)))) := by
      intro μ
      have hself := hgres μ D' D'.1 (subset_refl _)
      rw [congrFun (restrictionMap_id D'.1) _] at hself
      simp only [id_eq] at hself
      exact hself
    refine Filter.Tendsto.congr (fun μ => (hcast μ).symm) ?_
    have hnull : Filter.Tendsto
        (fun μ => TailC0.coeff μ (pieceModel ϖ hK₀ P
          (Finset.mem_image.mp D'.2).choose
          (f (Finset.mem_image.mp D'.2).choose)))
        Filter.cofinite (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact (pieceModel ϖ hK₀ P (Finset.mem_image.mp D'.2).choose
        (f (Finset.mem_image.mp D'.2).choose)).2
    have hsymm0 := ((headLocEquiv_symm_continuous ϖ hK₀
      (P.DHp (Finset.mem_image.mp D'.2).choose)
      (P.hDHp (Finset.mem_image.mp D'.2).choose)).tendsto 0).comp hnull
    rw [map_zero] at hsymm0
    have hres0 := ((restrictionMapHom_continuous
      (P.DHp (Finset.mem_image.mp D'.2).choose) D'.1
      (by rw [(Finset.mem_image.mp D'.2).choose_spec.2])).tendsto 0).comp
      hsymm0
    rw [map_zero] at hres0
    exact hres0
  -- assemble the base model element
  have hq'0 : Filter.Tendsto q2 Filter.cofinite (nhds 0) := hq0
  set Z : TailC0 w P.M (QHead P.DHb) (rhoQ P.DHb) :=
    ⟨fun μ => headLocEquiv ϖ hK₀ P.DHb P.hDHb (q2 μ), by
      have h1 := ((headLocEquiv_continuous ϖ hK₀ P.DHb P.hDHb).tendsto
        0).comp hq'0
      rw [map_zero] at h1
      have h2 := h1.norm
      rwa [norm_zero] at h2⟩ with hZ
  set x : presheafValue C.base :=
    (restrictionEquiv C.base (liftDatum P.DHb P.hDHb) P.hopenb).symm
      ((coeffLocEquiv ϖ hK₀ P.DHb P.hDHb).symm Z) with hx
  refine ⟨x, fun D => ?_⟩
  -- the base model of x is Z
  have hebx : coeffLocEquiv ϖ hK₀ P.DHb P.hDHb
      (restrictionMapHom C.base (liftDatum P.DHb P.hDHb) P.hopenb.le x) =
      Z := by
    rw [hx]
    rw [show restrictionMapHom C.base (liftDatum P.DHb P.hDHb) P.hopenb.le
        ((restrictionEquiv C.base (liftDatum P.DHb P.hDHb) P.hopenb).symm
          ((coeffLocEquiv ϖ hK₀ P.DHb P.hDHb).symm Z)) =
      (restrictionEquiv C.base (liftDatum P.DHb P.hDHb) P.hopenb)
        ((restrictionEquiv C.base (liftDatum P.DHb P.hDHb) P.hopenb).symm
          ((coeffLocEquiv ϖ hK₀ P.DHb P.hDHb).symm Z)) from rfl,
      RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  -- coefficientwise comparison of the piece models
  obtain ⟨Cb, hCb0, hb⟩ := qRestrict_bound ϖ hK₀ P D
  have hsq := RingHom.congr_fun
    (coeffLoc_restriction_square ϖ hK₀ P D hCb0.le hb)
    (restrictionMapHom C.base (liftDatum P.DHb P.hDHb) P.hopenb.le x)
  -- identify the right-hand side with the piece model of the restriction
  have hcomp₁ := congr_fun (restrictionMap_comp C.base
    (liftDatum P.DHb P.hDHb) (liftDatum (P.DHp D) (P.hDHp D))
    P.hopenb.le (P.lift_subset D)) x
  have hcomp₂ := congr_fun (restrictionMap_comp C.base D.1
    (liftDatum (P.DHp D) (P.hDHp D)) (C.hsubset D.1 D.2)
    (P.hopenp D).le) x
  simp only [Function.comp_apply] at hcomp₁ hcomp₂
  have hpm : pieceModel ϖ hK₀ P D
      (restrictionMap C.base D.1 (C.hsubset D.1 D.2) x) =
      TailC0.mapC (qRestrict ϖ hK₀ P D) hb (qRestrict_rhoQ ϖ hK₀ P D) Z := by
    rw [← hebx]
    rw [show TailC0.mapC (qRestrict ϖ hK₀ P D) hb (qRestrict_rhoQ ϖ hK₀ P D)
        (coeffLocEquiv ϖ hK₀ P.DHb P.hDHb
          (restrictionMapHom C.base (liftDatum P.DHb P.hDHb)
            P.hopenb.le x)) =
      coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)
        (restrictionMapHom (liftDatum P.DHb P.hDHb)
          (liftDatum (P.DHp D) (P.hDHp D)) (P.lift_subset D)
          (restrictionMapHom C.base (liftDatum P.DHb P.hDHb)
            P.hopenb.le x)) from hsq]
    rw [show restrictionMapHom (liftDatum P.DHb P.hDHb)
        (liftDatum (P.DHp D) (P.hDHp D)) (P.lift_subset D)
        (restrictionMapHom C.base (liftDatum P.DHb P.hDHb)
          P.hopenb.le x) =
      restrictionMap C.base (liftDatum (P.DHp D) (P.hDHp D))
        ((P.lift_subset D).trans P.hopenb.le) x from hcomp₁]
    rw [show restrictionMap C.base (liftDatum (P.DHp D) (P.hDHp D))
        ((P.lift_subset D).trans P.hopenb.le) x =
      restrictionMapHom D.1 (liftDatum (P.DHp D) (P.hDHp D))
        (P.hopenp D).le
        (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) x)
      from hcomp₂.symm]
    rfl
  -- the coefficients of mapC Z are the piece coefficients of f D
  have hcoeffs : ∀ μ : TailIdx P.M,
      qRestrict ϖ hK₀ P D (TailC0.coeff μ Z) =
        TailC0.coeff μ (pieceModel ϖ hK₀ P D (f D)) := by
    intro μ
    have hrq : restrictionMap (D := P.DHb) (P.DHp D)
        (P.cover.hsubset (P.DHp D) (hmemp D)) (q2 μ) =
        (headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).symm
          (TailC0.coeff μ (pieceModel ϖ hK₀ P D (f D))) := by
      rw [hq2 μ ⟨P.DHp D, hmemp D⟩]
      exact hgd μ D
    have h5 := congrArg (headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)) hrq
    rw [RingEquiv.apply_symm_apply] at h5
    rw [show qRestrict ϖ hK₀ P D (TailC0.coeff μ Z) =
      (headLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D))
        (restrictionMapHom P.DHb (P.DHp D) (P.piece_subset D)
          ((headLocEquiv ϖ hK₀ P.DHb P.hDHb).symm
            (headLocEquiv ϖ hK₀ P.DHb P.hDHb (q2 μ)))) from rfl,
      RingEquiv.symm_apply_apply]
    exact h5
  -- conclude: the piece models agree, hence the sections agree
  have hpmeq : pieceModel ϖ hK₀ P D
      (restrictionMap C.base D.1 (C.hsubset D.1 D.2) x) =
      pieceModel ϖ hK₀ P D (f D) := by
    rw [hpm]
    refine Subtype.ext (funext fun μ => ?_)
    exact hcoeffs μ
  have h6 := congrArg (coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).symm hpmeq
  rw [show (coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).symm
      (pieceModel ϖ hK₀ P D
        (restrictionMap C.base D.1 (C.hsubset D.1 D.2) x)) =
    restrictionMapHom D.1 (liftDatum (P.DHp D) (P.hDHp D)) (P.hopenp D).le
      (restrictionMap C.base D.1 (C.hsubset D.1 D.2) x) from by
      rw [show (coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).symm
          (pieceModel ϖ hK₀ P D
            (restrictionMap C.base D.1 (C.hsubset D.1 D.2) x)) =
        (coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).symm
          (coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)
            (restrictionMapHom D.1 (liftDatum (P.DHp D) (P.hDHp D))
              (P.hopenp D).le
              (restrictionMap C.base D.1 (C.hsubset D.1 D.2) x)))
        from rfl, RingEquiv.symm_apply_apply],
    show (coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).symm
      (pieceModel ϖ hK₀ P D (f D)) =
    restrictionMapHom D.1 (liftDatum (P.DHp D) (P.hDHp D)) (P.hopenp D).le
      (f D) from by
      rw [show (coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).symm
          (pieceModel ϖ hK₀ P D (f D)) =
        (coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)).symm
          (coeffLocEquiv ϖ hK₀ (P.DHp D) (P.hDHp D)
            (restrictionMapHom D.1 (liftDatum (P.DHp D) (P.hDHp D))
              (P.hopenp D).le (f D))) from rfl,
        RingEquiv.symm_apply_apply]] at h6
  exact (restrictionEquiv D.1 (liftDatum (P.DHp D) (P.hDHp D))
    (P.hopenp D)).injective h6

variable {K w} in
/-- The embedding half of the sheaf condition for `𝒜` (the
`productRestrictionSub_isEmbedding_JetA` shape, `FJP/Over/SheafTransfer.lean:667`). -/
theorem productRestrictionSub_isEmbedding_WPA (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational) :
    Topology.IsEmbedding (productRestrictionSub (WPA K w) C) := by
  classical
  refine ⟨?_, productRestrictionSub_injective_WPA ϖ hK₀ C hC⟩
  letI instModPiD : ∀ D : ↥C.covers, Module (WPA K w) (presheafValue D.1) :=
    fun D => RingHom.toModule (RationalLocData.canonicalMap D.1)
  letI instModBase : Module (WPA K w) (presheafValue C.base) :=
    RingHom.toModule (RationalLocData.canonicalMap C.base)
  letI instModPi : Module (WPA K w) (∀ D : ↥C.covers, presheafValue D.1) :=
    Pi.module _ _ _
  let rho : presheafValue C.base →ₗ[WPA K w]
      (∀ D : ↥C.covers, presheafValue D.1) :=
    { toFun := productRestrictionSub (WPA K w) C
      map_add' := fun x y => by
        funext D
        exact map_add (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) x y
      map_smul' := fun a x => by
        funext D
        show restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)
            ((RationalLocData.canonicalMap C.base) a * x) =
          (RationalLocData.canonicalMap D.1) a *
            restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) x
        rw [map_mul]
        congr 1
        exact productRestriction_comp_canonicalMap (A := WPA K w) C a D.1 D.2 }
  have hrange : (LinearMap.range rho :
      Set (∀ D : ↥C.covers, presheafValue D.1)) =
      sectionEqualizer (WPA K w) C := by
    ext s
    constructor
    · rintro ⟨x, rfl⟩
      exact productRestrictionSub_mem_sectionEqualizer (WPA K w) C x
    · intro hs
      obtain ⟨x, hx⟩ := gluing_WPA ϖ hK₀ C hC s hs
      exact ⟨x, funext fun D => hx D⟩
  have hclosed : IsClosed
      (LinearMap.range rho : Set (∀ D : ↥C.covers, presheafValue D.1)) := by
    rw [hrange]; exact sectionEqualizer_isClosed (WPA K w) C
  haveI : (uniformity (presheafValue C.base)).IsCountablyGenerated :=
    presheafValue_uniformity_isCountablyGenerated (A := WPA K w) C.base
  haveI : ∀ D : ↥C.covers,
      (uniformity (presheafValue D.1)).IsCountablyGenerated :=
    fun D => presheafValue_uniformity_isCountablyGenerated (A := WPA K w) D.1
  haveI : ContinuousSMul (WPA K w) (presheafValue C.base) :=
    ⟨continuous_mul.comp (((canonicalMap_continuous C.base).comp
      continuous_fst).prodMk continuous_snd)⟩
  haveI : ∀ D : ↥C.covers, ContinuousSMul (WPA K w) (presheafValue D.1) :=
    fun D => ⟨continuous_mul.comp
      (((canonicalMap_continuous D.1).comp continuous_fst).prodMk
        continuous_snd)⟩
  haveI : ContinuousSMul (WPA K w)
      (∀ D : ↥C.covers, presheafValue D.1) := inferInstance
  have hrho_cont : Continuous rho :=
    continuous_pi fun D =>
      restrictionMapHom_continuous C.base D.1 (C.hsubset D.1 D.2)
  have hinj : Function.Injective (rho : presheafValue C.base → _) :=
    fun x y h => productRestrictionSub_injective_WPA ϖ hK₀ C hC h
  obtain ⟨u, hu⟩ :=
    (inferInstance : IsTateRing (WPA K w)).exists_topologicallyNilpotent_unit
  exact @isInducing_of_closedRange_of_topNilpUnit (WPA K w) _ _
    (presheafValue C.base) _ instModBase _ _ _ _ _
    (∀ D : ↥C.covers, presheafValue D.1) _ instModPi _ _ _ _ _ _
    u hu u.isUnit rho hrho_cont hinj hclosed

variable {K w} in
/-- **`𝒜` is sheafy** — the finite-rational-cover form
([WP] thm:parity-strongly-sheafy; the `isSheafy_JetA` assembly,
`FJP/Over/SheafTransfer.lean:730`). -/
theorem isSheafy_WPA (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ValuationSpectrum.IsSheafy (WPA K w) where
  embedding := fun C hC => productRestrictionSub_isEmbedding_WPA ϖ hK₀ C hC
  gluing := fun C hC f hcompat => gluing_WPA ϖ hK₀ C hC f hcompat

/-- The distinguished ring of integral elements: the power-bounded subring
(the `finiteJetPlus` pattern, `FJP/Over/SheafyEndpoints.lean:87`). -/
noncomputable def wpPlus : RingOfIntegralElements (WPA K w) :=
  ⟨((WPA K w)⁺ : Subring (WPA K w)), inferInstance⟩

variable {K w} in
/-- **Pair-level sheafiness** ([WP] thm 6.2 (2), one pair; the
`finiteJet_isSheafyFor` pivot, `FJP/Over/SheafyEndpoints.lean:95`). -/
theorem wp_isSheafyFor (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsSheafyFor (WPA K w) (wpPlus K w) := by
  classical
  letI := (wpPlus K w).toPlusSubring
  haveI : IsRingOfIntegralElements ((WPA K w)⁺ : Subring (WPA K w)) :=
    (wpPlus K w).2
  haveI : HasLocLiftPowerBounded (WPA K w) := hasLocLiftPowerBounded_faithful
  haveI : ValuationSpectrum.IsSheafy (WPA K w) := isSheafy_WPA ϖ hK₀
  show IsLimitSheaf (WPA K w)
  exact isLimitSheaf_of_isSheafy

variable {K w} in
/-- **All-pairs sheafiness** (via the unconditional `A⁺`-independence
`isSheafyFor_iff_isSheafyComplete`). -/
theorem wp_isSheafyComplete (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsSheafyComplete (WPA K w) :=
  (isSheafyFor_iff_isSheafyComplete (wpPlus K w)).mp (wp_isSheafyFor ϖ hK₀)

variable {K w} in
theorem wp_isSheafyFor_all (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (Bplus : RingOfIntegralElements (WPA K w)) :
    IsSheafyFor (WPA K w) Bplus :=
  wp_isSheafyComplete ϖ hK₀ Bplus

variable {K w} in
/-- The genuine all-open structure presheaf of `Spa(𝒜, B⁺)` is a sheaf, for every
valid `B⁺` (the `finiteJet_structurePresheaf_isSheaf_all` shape,
`FJP/Over/SheafyEndpoints.lean:213`). -/
theorem wp_structurePresheaf_isSheaf_all (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (Bplus : RingOfIntegralElements (WPA K w)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((WPA K w)⁺ : Subring (WPA K w)) := Bplus.2
    haveI : HasLocLiftPowerBounded (WPA K w) := hasLocLiftPowerBounded_faithful
    (ValuationSpectrum.structurePresheaf (WPA K w)).IsSheaf :=
  isSheafyFor_structurePresheaf_isSheaf Bplus (wp_isSheafyFor_all ϖ hK₀ Bplus)

/-! ### Strong sheafiness ([WP] thm:parity-strongly-sheafy, last paragraph) -/

variable {K w} in
/-- Sheafiness of every shifted-weight algebra — the Tate extensions in the concrete
model ([WP] eq:strong-sheafy-decomposition: "the preceding proof applies verbatim").
This is `isSheafy_WPA` at the shifted weight; recorded as its own statement because
it is the mathematical content of strong sheafiness. -/
theorem isSheafy_WPA_shiftWeight (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (s : ℕ) :
    ValuationSpectrum.IsSheafy (WPA K (shiftWeight w s)) :=
  isSheafy_WPA ϖ hK₀

/-- The forward slot map of the Tate-extension bridge. -/
def slotTo (s : ℕ) (n : ℕ) : Fin s ⊕ ℕ :=
  if h : 1 ≤ n ∧ n ≤ s then Sum.inl ⟨n - 1, by omega⟩
  else if n = 0 then Sum.inr 0 else Sum.inr (n - s)

/-- The inverse slot map. -/
def slotInv (s : ℕ) : Fin s ⊕ ℕ → ℕ
  | Sum.inl i => i.1 + 1
  | Sum.inr m => if m = 0 then 0 else m + s

/-- The interleaving slot bijection of the Tate-extension bridge: `0 ↦ inr 0`,
`i ∈ [1..s] ↦ inl (i−1)`, `n > s ↦ inr (n−s)` (the exponent-side realization of
`shiftWeight`: the freed slots `1..s` carry the new Tate variables). -/
def slotEquiv (s : ℕ) : ℕ ≃ (Fin s ⊕ ℕ) where
  toFun := slotTo s
  invFun := slotInv s
  left_inv n := by
    simp only [slotTo]
    split_ifs with h1 h2
    · show n - 1 + 1 = n
      omega
    · show (if (0 : ℕ) = 0 then 0 else 0 + s) = n
      rw [if_pos rfl]
      omega
    · show (if n - s = 0 then 0 else n - s + s) = n
      rw [if_neg (by omega)]
      omega
  right_inv x := by
    rcases x with i | m
    · show slotTo s (i.1 + 1) = Sum.inl i
      simp only [slotTo]
      rw [dif_pos ⟨by omega, by have := i.2; omega⟩]
      congr 1
    · by_cases hm : m = 0
      · subst hm
        show slotTo s (if (0 : ℕ) = 0 then 0 else 0 + s) = Sum.inr 0
        rw [if_pos rfl]
        simp [slotTo]
      · show slotTo s (if m = 0 then 0 else m + s) = Sum.inr m
        rw [if_neg hm]
        simp only [slotTo]
        rw [dif_neg (by omega), if_neg (by omega)]
        congr 1
        omega

variable {K} in
/-- Stage 1 of the Tate-extension bridge: the ambient flatten
`(MvPowerSeries ℕ K)⟦Fin s⟧ ≅ K⟦Fin s ⊕ ℕ⟧ ≅ K⟦ℕ⟧` (Xia `sumAlgEquiv` +
mathlib `renameEquiv` along `slotEquiv`). -/
noncomputable def tateExtAmbient (s : ℕ) :
    MvPowerSeries (Fin s) (MvPowerSeries ℕ K) ≃+* MvPowerSeries ℕ K :=
  ((MvPowerSeries.sumAlgEquiv (Fin s) ℕ K).symm.trans
    (MvPowerSeries.renameEquiv K (slotEquiv s).symm)).toRingEquiv

variable {K} in
/-- Coefficients of the ambient flatten: transport the exponent through
`slotEquiv` and read the nested coefficient. -/
theorem tateExtAmbient_coeff (s : ℕ)
    (F : MvPowerSeries (Fin s) (MvPowerSeries ℕ K)) (u : ℕ →₀ ℕ) :
    MvPowerSeries.coeff u (tateExtAmbient (K := K) s F) =
      MvPowerSeries.coeff
        (Finsupp.comapDomain Sum.inr (Finsupp.equivMapDomain (slotEquiv s) u)
          Sum.inr_injective.injOn)
        (MvPowerSeries.coeff
          (Finsupp.comapDomain Sum.inl (Finsupp.equivMapDomain (slotEquiv s) u)
            Sum.inl_injective.injOn) F) := by
  have hu : u = Finsupp.embDomain (slotEquiv s).symm.toEmbedding
      (Finsupp.equivMapDomain (slotEquiv s) u) := by
    rw [Finsupp.embDomain_eq_mapDomain,
      show (⇑((slotEquiv s).symm.toEmbedding) : (Fin s ⊕ ℕ) → ℕ) =
        ⇑(slotEquiv s).symm from rfl,
      ← Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.equivMapDomain_trans,
      Equiv.self_trans_symm, Finsupp.equivMapDomain_refl]
  show MvPowerSeries.coeff u
    (MvPowerSeries.rename (⇑((slotEquiv s).symm.toEmbedding))
      ((MvPowerSeries.sumAlgEquiv (Fin s) ℕ K).symm F)) = _
  conv_lhs => rw [hu]
  rw [MvPowerSeries.coeff_embDomain_rename]
  rfl

variable {K w} in
/-- The coefficient-value hom `𝒜 → K⟦U⟧` (two subtype layers). -/
noncomputable def wpaVal : WPA K w →+* MvPowerSeries ℕ K :=
  ((MvPowerSeries.isSubring (R := K) (fun _ : ℕ => (1 : ℝ))).subtype).comp
    ((wpSupport K w).subtype)

variable {K w} in
theorem wpaVal_injective : Function.Injective (wpaVal (K := K) (w := w)) := by
  intro a b hab
  have h1 : a.1.1 = b.1.1 := hab
  exact Subtype.ext (Subtype.ext h1)

variable {K w} in
/-- The flatten hom on the nested Tate extension (stage 2 of the bridge). -/
noncomputable def tateExtToFlat (s : ℕ) :
    ↥(restrictedMvPowerSeriesSubring s (WPA K w)) →+* MvPowerSeries ℕ K :=
  ((tateExtAmbient (K := K) s).toRingHom.comp
    (MvPowerSeries.map (wpaVal (K := K) (w := w)))).comp
    (restrictedMvPowerSeriesSubring s (WPA K w)).subtype

variable {K w} in
theorem tateExtToFlat_injective (s : ℕ) :
    Function.Injective (tateExtToFlat (K := K) (w := w) s) := by
  rw [tateExtToFlat, RingHom.coe_comp, RingHom.coe_comp]
  refine Function.Injective.comp (Function.Injective.comp ?_ ?_) ?_
  · exact (tateExtAmbient (K := K) s).injective
  · exact MvPowerSeries.map_injective (wpaVal_injective (K := K) (w := w))
  · exact Subring.subtype_injective _

variable {K w} in
/-- Coefficients of the flatten hom: nested coefficient values at the
slot-transported exponent. -/
theorem tateExtToFlat_coeff (s : ℕ)
    (F : ↥(restrictedMvPowerSeriesSubring s (WPA K w))) (u : ℕ →₀ ℕ) :
    MvPowerSeries.coeff u (tateExtToFlat (K := K) (w := w) s F) =
      MvPowerSeries.coeff
        (Finsupp.comapDomain Sum.inr (Finsupp.equivMapDomain (slotEquiv s) u)
          Sum.inr_injective.injOn)
        (wpaVal (K := K) (w := w)
          (MvPowerSeries.coeff
            (Finsupp.comapDomain Sum.inl
              (Finsupp.equivMapDomain (slotEquiv s) u)
              Sum.inl_injective.injOn) F.1)) := by
  rw [show tateExtToFlat (K := K) (w := w) s F =
    tateExtAmbient (K := K) s
      (MvPowerSeries.map (wpaVal (K := K) (w := w)) F.1) from rfl,
    tateExtAmbient_coeff, MvPowerSeries.coeff_map]

/-- The `inr`-pull of a flat exponent through the slot bijection. -/
noncomputable def slotInr (s : ℕ) (u : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.comapDomain Sum.inr (Finsupp.equivMapDomain (slotEquiv s) u)
    Sum.inr_injective.injOn

theorem slotInr_apply (s : ℕ) (u : ℕ →₀ ℕ) (m : ℕ) :
    slotInr s u m = u (if m = 0 then 0 else m + s) := by
  rw [slotInr, Finsupp.comapDomain_apply, Finsupp.equivMapDomain_apply]
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl]
    rfl
  · rw [if_neg hm]
    show u ((slotEquiv s).symm (Sum.inr m)) = u (m + s)
    congr 1
    show slotInv s (Sum.inr m) = m + s
    simp only [slotInv]
    rw [if_neg hm]

theorem slotInr_zero_apply (s : ℕ) (u : ℕ →₀ ℕ) : slotInr s u 0 = u 0 := by
  rw [slotInr_apply, if_pos rfl]

/-- The parity weight at the shifted weight is computed by the `inr`-pull
(the freed slots `1..s` have weight `0`). -/
theorem wpWeight_shiftWeight_eq (w : ℕ → ℕ) (s : ℕ) (u : ℕ →₀ ℕ) :
    wpWeight (shiftWeight w s) u = wpWeight w (slotInr s u) := by
  classical
  have hL : wpWeight (shiftWeight w s) u =
      ∑ n ∈ u.support.filter (fun n => u n % 2 = 1 ∧ s < n), w (n - s) := by
    rw [wpWeight, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h1 : u n % 2 = 1 ∧ n ≠ 0
    · rw [if_pos h1]
      by_cases h2 : s < n
      · rw [if_pos ⟨h1.1, h2⟩]
        show (if n ≤ s then 0 else w (n - s)) = w (n - s)
        rw [if_neg (by omega)]
      · rw [if_neg (fun hc => h2 hc.2)]
        show (if n ≤ s then 0 else w (n - s)) = 0
        rw [if_pos (by omega)]
    · rw [if_neg h1, if_neg (fun hc => h1 ⟨hc.1, by omega⟩)]
  have hR : wpWeight w (slotInr s u) =
      ∑ m ∈ (slotInr s u).support.filter
        (fun m => slotInr s u m % 2 = 1 ∧ m ≠ 0), w m := by
    rw [wpWeight, Finset.sum_filter]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun n => n - s) (fun m => m + s) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    have hv : slotInr s u (n - s) = u n := by
      rw [slotInr_apply, if_neg (by omega),
        show n - s + s = n from by omega]
    refine ⟨Finsupp.mem_support_iff.mpr ?_, ?_, by omega⟩
    · rw [hv]
      exact Finsupp.mem_support_iff.mp hn.1
    · rw [hv]
      exact hn.2.1
  · intro m hm
    rw [Finset.mem_filter] at hm ⊢
    have hv : slotInr s u m = u (m + s) := by
      rw [slotInr_apply, if_neg hm.2.2]
    refine ⟨Finsupp.mem_support_iff.mpr ?_, ?_, by omega⟩
    · rw [← hv]
      exact Finsupp.mem_support_iff.mp hm.1
    · rw [← hv]
      exact hm.2.1
  · intro n hn
    rw [Finset.mem_filter] at hn
    omega
  · intro m hm
    rw [Finset.mem_filter] at hm
    omega
  · intro n _
    rfl

/-- Membership transport for the support condition along the slot bijection. -/
theorem wpMem_shiftWeight_iff (w : ℕ → ℕ) (s : ℕ) (u : ℕ →₀ ℕ) :
    WPMem (shiftWeight w s) u ↔ WPMem w (slotInr s u) := by
  rw [WPMem, WPMem, wpWeight_shiftWeight_eq, slotInr_zero_apply]

/-- The `inl`-pull of a flat exponent through the slot bijection. -/
noncomputable def slotInl (s : ℕ) (u : ℕ →₀ ℕ) : Fin s →₀ ℕ :=
  Finsupp.comapDomain Sum.inl (Finsupp.equivMapDomain (slotEquiv s) u)
    Sum.inl_injective.injOn

/-- A flat exponent is determined by its two slot pulls. -/
theorem slot_ext (s : ℕ) {u₁ u₂ : ℕ →₀ ℕ} (hl : slotInl s u₁ = slotInl s u₂)
    (hr : slotInr s u₁ = slotInr s u₂) : u₁ = u₂ := by
  have h1 : Finsupp.equivMapDomain (slotEquiv s) u₁ =
      Finsupp.equivMapDomain (slotEquiv s) u₂ := by
    refine Finsupp.ext fun x => ?_
    rcases x with i | m
    · have := congrArg (fun v => v i) hl
      simpa [slotInl, Finsupp.comapDomain_apply] using this
    · have := congrArg (fun v => v m) hr
      simpa [slotInr, Finsupp.comapDomain_apply] using this
  have h2 := congrArg (Finsupp.equivMapDomain (slotEquiv s).symm) h1
  rwa [← Finsupp.equivMapDomain_trans, ← Finsupp.equivMapDomain_trans,
    Equiv.self_trans_symm, Finsupp.equivMapDomain_refl,
    Finsupp.equivMapDomain_refl] at h2

variable {K w} in
/-- The flatten hom lands in the shifted-weight support: coefficients vanish off
`WPMem (shiftWeight w s)` (the support condition of the nested `𝒜`-coefficient,
transported along the slot bijection). -/
theorem tateExtToFlat_support (s : ℕ)
    (F : ↥(restrictedMvPowerSeriesSubring s (WPA K w))) (u : ℕ →₀ ℕ)
    (hu : ¬ WPMem (shiftWeight w s) u) :
    MvPowerSeries.coeff u (tateExtToFlat (K := K) (w := w) s F) = 0 := by
  rw [tateExtToFlat_coeff]
  have hX := (MvPowerSeries.coeff
    (Finsupp.comapDomain Sum.inl (Finsupp.equivMapDomain (slotEquiv s) u)
      Sum.inl_injective.injOn) F.1).2
  exact hX (slotInr s u)
    (fun hc => hu ((wpMem_shiftWeight_iff w s u).mpr hc))

variable {K w} in
/-- The flatten hom is Gauss-restricted at radius 1 (joint cofiniteness of the
nested coefficient families: outer nullity of the `𝒜`-coefficients, inner
Gauss-nullity of each, glued along the slot split). -/
theorem tateExtToFlat_isRestrictedGauss (s : ℕ)
    (F : ↥(restrictedMvPowerSeriesSubring s (WPA K w))) :
    MvPowerSeries.IsRestrictedGauss (fun _ : ℕ => (1 : ℝ))
      (tateExtToFlat (K := K) (w := w) s F) := by
  classical
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  rw [Filter.eventually_cofinite]
  have hT : {t : Fin s →₀ ℕ |
      ε ≤ ‖(MvPowerSeries.coeff t F.1 : WPA K w)‖}.Finite := by
    have h2 : MvPowerSeries.IsRestricted F.1 := F.2
    have h3 := Metric.tendsto_nhds.mp h2 ε hε
    rw [Filter.eventually_cofinite] at h3
    refine h3.subset fun t ht => ?_
    rw [Set.mem_setOf_eq] at ht ⊢
    intro hc
    rw [dist_zero_right] at hc
    linarith
  have hper : ∀ t : Fin s →₀ ℕ, {u : ℕ →₀ ℕ | slotInl s u = t ∧
      ε ≤ ‖MvPowerSeries.coeff (slotInr s u)
        ((MvPowerSeries.coeff t F.1 : WPA K w)).1.1‖}.Finite := by
    intro t
    have h4 : {v : ℕ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff v
        ((MvPowerSeries.coeff t F.1 : WPA K w)).1.1‖}.Finite := by
      have h5 := ((MvPowerSeries.coeff t F.1 : WPA K w)).1.2
      have h6 := Metric.tendsto_nhds.mp h5 ε hε
      rw [Filter.eventually_cofinite] at h6
      refine h6.subset fun v hv => ?_
      rw [Set.mem_setOf_eq] at hv ⊢
      intro hc
      rw [dist_zero_right,
        show (v.prod fun _ k => (1 : ℝ) ^ k) = 1 from by simp, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hc
      linarith
    refine Set.Finite.of_finite_image (f := fun u => slotInr s u)
      (h4.subset ?_) ?_
    · rintro _ ⟨u, ⟨hul, hur⟩, rfl⟩
      exact hur
    · intro u₁ h₁ u₂ h₂ hr
      rw [Set.mem_setOf_eq] at h₁ h₂
      exact slot_ext s (h₁.1.trans h₂.1.symm) hr
  refine Set.Finite.subset (Set.Finite.biUnion hT fun t _ => hper t) ?_
  intro u hu
  rw [Set.mem_setOf_eq] at hu
  have hbig : ε ≤ ‖MvPowerSeries.coeff u
      (tateExtToFlat (K := K) (w := w) s F)‖ := by
    by_contra hc
    push_neg at hc
    refine hu ?_
    rw [dist_zero_right,
      show (u.prod fun _ k => (1 : ℝ) ^ k) = 1 from by simp, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hc
  rw [tateExtToFlat_coeff] at hbig
  have hbig' : ε ≤ ‖MvPowerSeries.coeff (slotInr s u)
      ((MvPowerSeries.coeff (slotInl s u) F.1 : WPA K w)).1.1‖ := hbig
  refine Set.mem_biUnion (x := slotInl s u) ?_ ?_
  · show ε ≤ ‖(MvPowerSeries.coeff (slotInl s u) F.1 : WPA K w)‖
    refine le_trans hbig' ?_
    exact norm_coeffA_le (K := K) (w := w) _ _
  · rw [Set.mem_setOf_eq]
    exact ⟨rfl, hbig'⟩

/-- Recombine slot parts into a flat exponent. -/
noncomputable def slotRecomb (s : ℕ) (t : Fin s →₀ ℕ) (v : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.equivMapDomain (slotEquiv s).symm
    (Finsupp.sumFinsuppEquivProdFinsupp.symm (t, v))

theorem equivMapDomain_slotRecomb (s : ℕ) (t : Fin s →₀ ℕ) (v : ℕ →₀ ℕ) :
    Finsupp.equivMapDomain (slotEquiv s) (slotRecomb s t v) =
      Finsupp.sumFinsuppEquivProdFinsupp.symm (t, v) := by
  rw [slotRecomb, ← Finsupp.equivMapDomain_trans, Equiv.symm_trans_self,
    Finsupp.equivMapDomain_refl]

theorem slotInl_slotRecomb (s : ℕ) (t : Fin s →₀ ℕ) (v : ℕ →₀ ℕ) :
    slotInl s (slotRecomb s t v) = t := by
  refine Finsupp.ext fun i => ?_
  rw [slotInl, Finsupp.comapDomain_apply, equivMapDomain_slotRecomb]
  exact Finsupp.sumFinsuppEquivProdFinsupp_symm_inl _ i

theorem slotInr_slotRecomb (s : ℕ) (t : Fin s →₀ ℕ) (v : ℕ →₀ ℕ) :
    slotInr s (slotRecomb s t v) = v := by
  refine Finsupp.ext fun m => ?_
  rw [slotInr, Finsupp.comapDomain_apply, equivMapDomain_slotRecomb]
  exact Finsupp.sumFinsuppEquivProdFinsupp_symm_inr _ m

theorem slotRecomb_slots (s : ℕ) (u : ℕ →₀ ℕ) :
    slotRecomb s (slotInl s u) (slotInr s u) = u :=
  slot_ext s (slotInl_slotRecomb s _ _) (slotInr_slotRecomb s _ _)

variable {K w} in
/-- The flatten hom, corestricted to the shifted-weight algebra. -/
noncomputable def tateExtToWPA (s : ℕ) :
    ↥(restrictedMvPowerSeriesSubring s (WPA K w)) →+* WPA K (shiftWeight w s) where
  toFun F := ⟨⟨tateExtToFlat (K := K) (w := w) s F,
      tateExtToFlat_isRestrictedGauss s F⟩,
    fun u hu => tateExtToFlat_support s F u hu⟩
  map_one' := Subtype.ext (Subtype.ext (map_one
    (tateExtToFlat (K := K) (w := w) s)))
  map_mul' F G := Subtype.ext (Subtype.ext (map_mul
    (tateExtToFlat (K := K) (w := w) s) F G))
  map_zero' := Subtype.ext (Subtype.ext (map_zero
    (tateExtToFlat (K := K) (w := w) s)))
  map_add' F G := Subtype.ext (Subtype.ext (map_add
    (tateExtToFlat (K := K) (w := w) s) F G))

variable {K w} in
theorem tateExtToWPA_injective (s : ℕ) :
    Function.Injective (tateExtToWPA (K := K) (w := w) s) := by
  intro F G hFG
  refine tateExtToFlat_injective (K := K) (w := w) s ?_
  have h1 := congrArg (fun z : WPA K (shiftWeight w s) => z.1.1) hFG
  exact h1

variable {K w} in
/-- The value-level coefficient family of a shifted-weight element is null. -/
theorem shiftg_coeff_null (s : ℕ) (g : WPA K (shiftWeight w s)) :
    Filter.Tendsto (fun u : ℕ →₀ ℕ => MvPowerSeries.coeff u g.1.1)
      Filter.cofinite (nhds 0) := by
  have hg : Filter.Tendsto (fun u : ℕ →₀ ℕ =>
      ‖MvPowerSeries.coeff u g.1.1‖ * u.prod fun _ k => (1 : ℝ) ^ k)
      Filter.cofinite (nhds 0) := g.1.2
  rw [show (fun u : ℕ →₀ ℕ => ‖MvPowerSeries.coeff u g.1.1‖ *
      u.prod fun _ k => (1 : ℝ) ^ k) =
    (fun u : ℕ →₀ ℕ => ‖MvPowerSeries.coeff u g.1.1‖) from
    funext fun u => by simp] at hg
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hg

variable {K w} in
/-- The unflatten of a shifted-weight element: the `t`-th coefficient in `𝒜`. -/
noncomputable def unflattenCoeff (s : ℕ) (g : WPA K (shiftWeight w s))
    (t : Fin s →₀ ℕ) : WPA K w :=
  ⟨⟨fun v => MvPowerSeries.coeff (slotRecomb s t v) g.1.1, by
      have hinj : Function.Injective (fun v => slotRecomb s t v) := by
        intro v₁ v₂ hv
        have h1 := congrArg (slotInr s) hv
        rwa [slotInr_slotRecomb, slotInr_slotRecomb] at h1
      have hfib := (shiftg_coeff_null s g).comp hinj.tendsto_cofinite
      show Filter.Tendsto (fun v : ℕ →₀ ℕ =>
        ‖MvPowerSeries.coeff (slotRecomb s t v) g.1.1‖ *
          v.prod fun _ k => (1 : ℝ) ^ k) Filter.cofinite (nhds 0)
      rw [show (fun v : ℕ →₀ ℕ =>
          ‖MvPowerSeries.coeff (slotRecomb s t v) g.1.1‖ *
            v.prod fun _ k => (1 : ℝ) ^ k) =
        (fun v : ℕ →₀ ℕ =>
          ‖MvPowerSeries.coeff (slotRecomb s t v) g.1.1‖) from
        funext fun v => by simp]
      exact tendsto_zero_iff_norm_tendsto_zero.mp hfib⟩,
    fun v hv => by
      refine g.2 (slotRecomb s t v) ?_
      intro hc
      have h2 := (wpMem_shiftWeight_iff w s (slotRecomb s t v)).mp hc
      rw [slotInr_slotRecomb] at h2
      exact hv h2⟩

variable {K w} in
theorem unflatten_isRestricted (s : ℕ) (g : WPA K (shiftWeight w s)) :
    MvPowerSeries.IsRestricted
      (fun t : Fin s →₀ ℕ => unflattenCoeff (K := K) (w := w) s g t) := by
  classical
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  rw [Filter.eventually_cofinite]
  have hε2 : 0 < ε / 2 := by linarith
  have hg : {u : ℕ →₀ ℕ |
      ε / 2 ≤ ‖MvPowerSeries.coeff u g.1.1‖}.Finite := by
    have h6 := Metric.tendsto_nhds.mp (shiftg_coeff_null s g) (ε / 2) hε2
    rw [Filter.eventually_cofinite] at h6
    refine h6.subset fun u hu => ?_
    rw [Set.mem_setOf_eq] at hu ⊢
    intro hc
    rw [dist_zero_right] at hc
    linarith
  refine Set.Finite.subset (hg.image (slotInl s)) ?_
  intro t ht
  rw [Set.mem_setOf_eq] at ht
  have hnorm : ε ≤ ‖unflattenCoeff (K := K) (w := w) s g t‖ := by
    by_contra hc
    push_neg at hc
    refine ht ?_
    rw [dist_zero_right]
    exact hc
  -- extract a fiber witness ≥ ε/2
  have hwit : ∃ v : ℕ →₀ ℕ,
      ε / 2 ≤ ‖MvPowerSeries.coeff (slotRecomb s t v) g.1.1‖ := by
    by_contra hc
    push_neg at hc
    have hle : ‖unflattenCoeff (K := K) (w := w) s g t‖ ≤ ε / 2 := by
      rw [norm_eq_iSup_coeffA]
      refine ciSup_le fun v => ?_
      exact (hc v).le
    linarith
  obtain ⟨v, hv⟩ := hwit
  refine ⟨slotRecomb s t v, ?_, ?_⟩
  · rw [Set.mem_setOf_eq]
    exact hv
  · exact slotInl_slotRecomb s t v

variable {K w} in
theorem tateExtToWPA_surjective (s : ℕ) :
    Function.Surjective (tateExtToWPA (K := K) (w := w) s) := by
  classical
  intro g
  refine ⟨⟨fun t => unflattenCoeff (K := K) (w := w) s g t,
    unflatten_isRestricted s g⟩, ?_⟩
  refine Subtype.ext (Subtype.ext ?_)
  refine MvPowerSeries.ext fun u => ?_
  show MvPowerSeries.coeff u (tateExtToFlat (K := K) (w := w) s
    ⟨fun t => unflattenCoeff (K := K) (w := w) s g t,
      unflatten_isRestricted s g⟩) = MvPowerSeries.coeff u g.1.1
  rw [tateExtToFlat_coeff]
  show MvPowerSeries.coeff (slotRecomb s (slotInl s u) (slotInr s u)) g.1.1 =
    MvPowerSeries.coeff u g.1.1
  rw [slotRecomb_slots]

variable {K w} in
/-- The bridge between the project's Tate extension of `𝒜` and the shifted-weight
weighted-parity algebra: `𝒜⟨V_1,…,V_s⟩ ≅ WPA (shiftWeight w s)` (Fubini + reindex
of restricted power series; nested-vs-flat plumbing). -/
noncomputable def tateExtEquiv (s : ℕ) :
    ↥(restrictedMvPowerSeriesSubring s (WPA K w)) ≃+* WPA K (shiftWeight w s) :=
  RingEquiv.ofBijective (tateExtToWPA (K := K) (w := w) s)
    ⟨tateExtToWPA_injective s, tateExtToWPA_surjective s⟩

variable {K w} in
/-- **W24b forward continuity**: the Tate-extension flatten is continuous from
the canonical mv-Tate-algebra topology to the Gauss topology — every basis
neighbourhood maps into a norm ball, coefficientwise through the pair of
definition's `isAdic` cofinality (no norm characterization of the opaque
principal pair is needed). -/
theorem tateExtToWPA_continuous (s : ℕ) :
    @Continuous _ _ (MvTateAlgebra.mvTateAlgebraTopology' (A := WPA K w) s) _
      (⇑(tateExtToWPA (K := K) (w := w) s)) := by
  classical
  letI := MvTateAlgebra.mvTateAlgebraTopology' (A := WPA K w) s
  haveI hTR : IsTopologicalRing
      ↥(restrictedMvPowerSeriesSubring s (WPA K w)) :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing (A := WPA K w) s
  refine continuous_of_tendsto_nhds_zero
    (tateExtToWPA (K := K) (w := w) s) ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  set P₀ := (IsTateRing.principalPair (WPA K w)).toPairOfDefinition with hP₀
  obtain ⟨k, -, hk⟩ := P₀.hasBasis_nhds_zero.mem_iff.mp
    (Metric.ball_mem_nhds (0 : WPA K w)
      (by positivity : (0 : ℝ) < ε / 2))
  refine Filter.eventually_of_mem
    ((MvTateAlgebra.mvTateAlgBasis' (A := WPA K w) s).hasBasis_nhds_zero.mem_of_mem
      (i := k) trivial) fun y hy => ?_
  rw [dist_zero_right]
  have hcoeff : ∀ u : ℕ →₀ ℕ,
      ‖coeffA K (shiftWeight w s) u
        (tateExtToWPA (K := K) (w := w) s y)‖ ≤ ε / 2 := by
    intro u
    have h1 : coeffA K (shiftWeight w s) u
        (tateExtToWPA (K := K) (w := w) s y) =
        MvPowerSeries.coeff (slotInr s u)
          (wpaVal (K := K) (w := w)
            (MvPowerSeries.coeff (slotInl s u) y.val)) :=
      tateExtToFlat_coeff s y u
    rw [h1]
    refine le_trans
      (norm_coeffA_le K w (slotInr s u)
        (MvPowerSeries.coeff (slotInl s u) y.val)) ?_
    obtain ⟨b, hbk, hbeq⟩ := MvTateAlgebra.mvTateAlgNhd_coeff_mem s P₀ k hy (slotInl s u)
    have hmem : MvPowerSeries.coeff (slotInl s u) y.val ∈
        Subtype.val '' ((P₀.I ^ k : Ideal P₀.A₀) : Set P₀.A₀) :=
      ⟨b, hbk, hbeq⟩
    have h2 := hk hmem
    rw [Metric.mem_ball, dist_zero_right] at h2
    exact h2.le
  have hnorm : ‖tateExtToWPA (K := K) (w := w) s y‖ ≤ ε / 2 := by
    rw [norm_eq_iSup_coeffA]
    exact Real.iSup_le hcoeff (by positivity)
  linarith

variable {K w} in
/-- **W24b backward continuity**: the inverse of the Tate-extension flatten is
continuous from the Gauss topology to the canonical mv-Tate-algebra topology —
each basis target absorbs a norm ball through the openness of the ideal-power
images, coefficientwise via the slot recombination. -/
theorem tateExtEquiv_symm_continuous (s : ℕ) :
    @Continuous _ _ _ (MvTateAlgebra.mvTateAlgebraTopology' (A := WPA K w) s)
      (⇑(tateExtEquiv (K := K) (w := w) s).symm) := by
  classical
  letI := MvTateAlgebra.mvTateAlgebraTopology' (A := WPA K w) s
  haveI hTR : IsTopologicalRing
      ↥(restrictedMvPowerSeriesSubring s (WPA K w)) :=
    MvTateAlgebra.mvTateAlgebraTopology'_isTopologicalRing (A := WPA K w) s
  refine continuous_of_tendsto_nhds_zero
    (tateExtEquiv (K := K) (w := w) s).symm ?_
  rw [(MvTateAlgebra.mvTateAlgBasis' (A := WPA K w) s).hasBasis_nhds_zero.tendsto_right_iff]
  rintro k -
  set P₀ := (IsTateRing.principalPair (WPA K w)).toPairOfDefinition with hP₀
  obtain ⟨ε, hε0, hball⟩ := Metric.mem_nhds_iff.mp
    (P₀.hasBasis_nhds_zero.mem_of_mem (i := k) trivial)
  refine Filter.eventually_of_mem
    (Metric.ball_mem_nhds (0 : WPA K (shiftWeight w s)) hε0) fun F hF => ?_
  rw [Metric.mem_ball, dist_zero_right] at hF
  set G := (tateExtEquiv (K := K) (w := w) s).symm F with hGdef
  have hGF : tateExtToWPA (K := K) (w := w) s G = F :=
    (tateExtEquiv (K := K) (w := w) s).apply_symm_apply F
  have hcl : ∀ l : Fin s →₀ ℕ, ∃ b : P₀.A₀, b ∈ P₀.I ^ k ∧
      (b : WPA K w) = MvPowerSeries.coeff l G.val := by
    intro l
    have hnl : ‖MvPowerSeries.coeff l G.val‖ < ε := by
      have h2 : ∀ v : ℕ →₀ ℕ,
          coeffA K w v (MvPowerSeries.coeff l G.val) =
          coeffA K (shiftWeight w s) (slotRecomb s l v) F := by
        intro v
        have h3 := tateExtToFlat_coeff s G (slotRecomb s l v)
        have h4 : Finsupp.comapDomain Sum.inl
            (Finsupp.equivMapDomain (slotEquiv s) (slotRecomb s l v))
            Sum.inl_injective.injOn = l := slotInl_slotRecomb s l v
        have h5 : Finsupp.comapDomain Sum.inr
            (Finsupp.equivMapDomain (slotEquiv s) (slotRecomb s l v))
            Sum.inr_injective.injOn = v := slotInr_slotRecomb s l v
        rw [h4, h5] at h3
        have h6 : coeffA K (shiftWeight w s) (slotRecomb s l v)
            (tateExtToWPA (K := K) (w := w) s G) =
            MvPowerSeries.coeff v
              (wpaVal (K := K) (w := w)
                (MvPowerSeries.coeff l G.val)) := h3
        rw [hGF] at h6
        exact h6.symm
      rw [norm_eq_iSup_coeffA]
      refine lt_of_le_of_lt
        (Real.iSup_le (fun v => ?_) (norm_nonneg F)) hF
      rw [h2 v]
      exact norm_coeffA_le K (shiftWeight w s) (slotRecomb s l v) F
    have hmem := hball (by
      rw [Metric.mem_ball, dist_zero_right]; exact hnl)
    obtain ⟨b, hbk, hbeq⟩ := hmem
    exact ⟨b, hbk, hbeq⟩
  have hpair : G ∈ MvTateAlgebra.mvPairSubring s P₀ := by
    intro l
    obtain ⟨b, hbk, hbeq⟩ := hcl l
    rw [← hbeq]
    exact b.2
  exact MvTateAlgebra.mvTateAlgNhd_of_coeff_mem_principal s P₀ k
    (IsTateRing.principalPair (WPA K w)).π
    (IsTateRing.principalPair (WPA K w)).I_eq_span
    (IsTateRing.principalPair (WPA K w)).π_isUnit hpair hcl

variable {K w} in
/-- **W24b: the Tate-extension flatten is a bicontinuous ring equivalence**
for the canonical mv-Tate-algebra topology ([WP]
eq:strong-sheafy-decomposition at the topological level). -/
theorem tateExtEquiv_bicontinuous (s : ℕ) :
    @Continuous _ _ (MvTateAlgebra.mvTateAlgebraTopology' (A := WPA K w) s) _
      (⇑(tateExtEquiv (K := K) (w := w) s)) ∧
    @Continuous _ _ _ (MvTateAlgebra.mvTateAlgebraTopology' (A := WPA K w) s)
      (⇑(tateExtEquiv (K := K) (w := w) s).symm) :=
  ⟨tateExtToWPA_continuous s, tateExtEquiv_symm_continuous s⟩

-- The topological refinement of `tateExtEquiv` (bicontinuity for the project's
-- Tate-algebra topology on `restrictedMvPowerSeriesSubring`, cf.
-- `MvTateAlgebraTopology`) is specified at ticket level; the bare subtype carries no
-- `TopologicalSpace` instance, so the statement needs the `mvTateAlgebraTopology'`
-- `letI` and is deferred to execution.

variable {K w} in
/-- **Strong sheafiness** ([WP] thm 6.2 (2): "(𝒜,𝒜°) is strongly sheafy"): for every
`s`, the weighted-parity model of the Tate extension `𝒜⟨V_1,…,V_s⟩` is sheafy for
every valid ring of integral elements.  Combined with the identification
`tateExtEquiv` this is the statement in the project's own Tate-extension
vocabulary. -/
theorem wp_stronglySheafy (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (s : ℕ) :
    IsSheafyComplete (WPA K (shiftWeight w s)) :=
  wp_isSheafyComplete ϖ hK₀

end WeightedParity
