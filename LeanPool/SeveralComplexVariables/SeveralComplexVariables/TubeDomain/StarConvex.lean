/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HolomorphicConvexity.Thullen
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.TubeDomain.Disc
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.TubeDomain.Gluing

/-!
# The maximal star-convex extension tube and Bochner's theorem for star-convex bases

Fix a Banach space `F`, a base `Ω ⊆ ℝⁿ` and a point `p`. The star-convex open sets `A` with
respect to `p` such that every `F`-valued holomorphic function on the tube over `Ω` extends
holomorphically to the tube over `A`, agreeing with it near the real point `p`, form a family
closed under unions: the union `maxStar` again has the extension property, because two members
meet in a star-convex set whose tube is connected. The maximal tube is convex. Indeed, for two
points `t₁, t₂` of `maxStar`, the scaled triangles with vertex `p` lie in `maxStar` by an
induction on the scale: on a slightly smaller triangle every point lies on a parabolic analytic
disc with boundary over the two sides through `p`, so by the disc hull lemma and Thullen's
continuation lemma every function continues to a ball of a uniform radius, these local
continuations glue along the convex triangle, and maximality absorbs the enlarged tube.

Consequently, for an open star-convex base, every holomorphic function on the tube extends to
the tube over the convex hull. This is part (a) of [Hörmander][Hormander1973]'s proof of
Bochner's theorem.

References: [Hörmander][Hormander1973] §2.5, Theorem 2.5.10 (a); [Scheidemann][Scheidemann2005]
§6.3, Theorem 6.3.1, Step 1.

## Main definitions

* `TubeExtends`: Every `F`-valued holomorphic function on the tube over `Ω` extends holomorphically
  to the tube over `A`, agreeing with the original near the real point `p`.
* `starFamily`: The family of open star-convex extension bases.
* `maxStar`: The maximal star-convex extension base.

## Main results

* `maxStar_maximal`: **Maximality.** An open star-convex base to which every function on the maximal
  tube extends is contained in the maximal base.
* `exists_local_continuation_tri`: **Local continuation on a shrunken triangle.** If the tube over
  the triangle of scale `a` lies in the tube over `A` and balls of radius `δ` around the two sides
  through `p` lie in the tube over `A`, then every function holomorphic on the tube over `A`
  continues to the ball of radius `δ` around each point of the tube over the triangle of a smaller
  scale `b`.
* `thickening_tri_subset_of_maximal`: **One step of the triangle induction.** Under maximality, the
  `δ`-thickening of the tube over the triangle of a smaller scale is absorbed into `A`.
* `tri_subset_of_maximal`: **The triangle lemma.** Under maximality, the full triangle with vertex
  `p` and two points of `A` lies in `A`.
* `convex_maxStar`: **The maximal star-convex extension base is convex.**
* `exists_extension_tubeDomain_convexHull_of_starConvex`: **Bochner's tube theorem for star-convex
  bases.** Every Banach-valued holomorphic function on the tube over an open star-convex base
  extends to the tube over the convex hull.

## References

* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace SeveralComplexVariables

namespace BochnerTube

variable {n : ℕ} (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Every `F`-valued holomorphic function on the tube over `Ω` extends holomorphically to the tube
over `A`, agreeing with the original near the real point `p`. -/
@[expose] def TubeExtends (Ω A : Set (Fin n → ℝ)) (p : Fin n → ℝ) : Prop :=
  ∀ f : (Fin n → ℂ) → F, AnalyticOnNhd ℂ f (tubeDomain Ω) →
    ∃ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain A) ∧ g =ᶠ[𝓝 (ofRealPi p)] f

/-- The family of open star-convex extension bases. -/
@[expose] def starFamily (Ω : Set (Fin n → ℝ)) (p : Fin n → ℝ) : Set (Set (Fin n → ℝ)) :=
  {A | IsOpen A ∧ StarConvex ℝ p A ∧ TubeExtends F Ω A p}

/-- The maximal star-convex extension base. -/
@[expose] def maxStar (Ω : Set (Fin n → ℝ)) (p : Fin n → ℝ) : Set (Fin n → ℝ) :=
  ⋃₀ starFamily F Ω p

variable {F}

section Family

variable {Ω : Set (Fin n → ℝ)} {p : Fin n → ℝ}

omit [CompleteSpace F] in
/-- The maximal base is open. -/
theorem isOpen_maxStar : IsOpen (maxStar F Ω p) := isOpen_sUnion fun _ hA => hA.1

omit [CompleteSpace F] in
/-- The maximal base is star-convex with respect to `p`. -/
theorem starConvex_maxStar : StarConvex ℝ p (maxStar F Ω p) :=
  starConvex_sUnion fun _ hA => hA.2.1

omit [CompleteSpace F] in
/-- Members of the family lie in the maximal base. -/
theorem subset_maxStar_of_mem {A : Set (Fin n → ℝ)} (hA : A ∈ starFamily F Ω p) :
    A ⊆ maxStar F Ω p := subset_sUnion_of_mem hA

omit [CompleteSpace F] in
/-- A ball around `p` inside `Ω` belongs to the family. -/
theorem ball_mem_starFamily {r : ℝ} (hr0 : 0 < r) (hr : ball p r ⊆ Ω) :
    ball p r ∈ starFamily F Ω p :=
  ⟨isOpen_ball, (convex_ball p r).starConvex (mem_ball_self hr0),
    fun f hf => ⟨f, hf.mono (tubeDomain_mono hr), EventuallyEq.rfl⟩⟩

omit [CompleteSpace F] in
/-- The center lies in the maximal base when a ball around it lies in `Ω`. -/
theorem mem_maxStar_of_ball {r : ℝ} (hr0 : 0 < r) (hr : ball p r ⊆ Ω) : p ∈ maxStar F Ω p :=
  subset_maxStar_of_mem (ball_mem_starFamily hr0 hr) (mem_ball_self hr0)

/-- The tube over a star-convex set containing its center is preconnected. -/
theorem isPreconnected_tubeDomain_of_starConvex {A : Set (Fin n → ℝ)} (hA : StarConvex ℝ p A)
    (hp : p ∈ A) : IsPreconnected (tubeDomain A) :=
  isPreconnected_tubeDomain (hA.isPathConnected hp).isConnected.isPreconnected

omit [CompleteSpace F] in
/-- Two extensions agreeing with a function near `p` agree on the tube over the intersection of
star-convex bases. -/
theorem eqOn_of_starConvex {A B : Set (Fin n → ℝ)} (hA : StarConvex ℝ p A)
    (hB : StarConvex ℝ p B) {f g₁ g₂ : (Fin n → ℂ) → F}
    (hg₁ : AnalyticOnNhd ℂ g₁ (tubeDomain A)) (hg₂ : AnalyticOnNhd ℂ g₂ (tubeDomain B))
    (h₁ : g₁ =ᶠ[𝓝 (ofRealPi p)] f) (h₂ : g₂ =ᶠ[𝓝 (ofRealPi p)] f) :
    EqOn g₁ g₂ (tubeDomain (A ∩ B)) := by
  rcases (A ∩ B).eq_empty_or_nonempty with he | hne
  · rw [he, tubeDomain_empty]
    exact fun _ h => h.elim
  have hp : p ∈ A ∩ B := (hA.inter hB).mem hne
  exact (hg₁.mono (tubeDomain_mono inter_subset_left)).eqOn_of_preconnected_of_eventuallyEq
    (hg₂.mono (tubeDomain_mono inter_subset_right))
    (isPreconnected_tubeDomain_of_starConvex (hA.inter hB) hp)
    (ofRealPi_mem_tubeDomain.mpr hp) (h₁.trans h₂.symm)

omit [CompleteSpace F] in
/-- The maximal base has the extension property. -/
theorem tubeExtends_maxStar (hp : p ∈ maxStar F Ω p) : TubeExtends F Ω (maxStar F Ω p) p := by
  classical
  intro f hf
  have hchoice : ∀ A : Set (Fin n → ℝ), A ∈ starFamily F Ω p →
      ∃ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain A) ∧ g =ᶠ[𝓝 (ofRealPi p)] f :=
    fun A hA => hA.2.2 f hf
  choose! g hga hgf using hchoice
  let G : (Fin n → ℂ) → F := fun z =>
    if hz : ∃ A ∈ starFamily F Ω p, z ∈ tubeDomain A then g (Classical.choose hz) z else 0
  have hG : ∀ A ∈ starFamily F Ω p, ∀ z ∈ tubeDomain A, G z = g A z := by
    intro A hA z hz
    have hex : ∃ A ∈ starFamily F Ω p, z ∈ tubeDomain A := ⟨A, hA, hz⟩
    simp only [G]
    split_ifs
    obtain ⟨hA', hz'⟩ := Classical.choose_spec hex
    exact eqOn_of_starConvex hA'.2.1 hA.2.1 (hga _ hA') (hga A hA) (hgf _ hA') (hgf A hA)
      ⟨hz', hz⟩
  obtain ⟨A₀, hA₀, hpA₀⟩ := mem_sUnion.mp hp
  refine ⟨G, ?_, ?_⟩
  · intro z hz
    obtain ⟨A, hA, hzA⟩ := mem_sUnion.mp hz
    have : G =ᶠ[𝓝 z] g A :=
      eventuallyEq_of_mem ((isOpen_tubeDomain hA.1).mem_nhds hzA) fun w hw => hG A hA w hw
    exact (hga A hA z hzA).congr this.symm
  · have : G =ᶠ[𝓝 (ofRealPi p)] g A₀ :=
      eventuallyEq_of_mem ((isOpen_tubeDomain hA₀.1).mem_nhds (ofRealPi_mem_tubeDomain.mpr hpA₀))
        fun w hw => hG A₀ hA₀ w hw
    exact this.trans (hgf A₀ hA₀)

omit [CompleteSpace F] in
/-- **Maximality.** An open star-convex base to which every function on the maximal tube
extends is contained in the maximal base. -/
theorem maxStar_maximal (hp : p ∈ maxStar F Ω p) {B : Set (Fin n → ℝ)} (hB : IsOpen B)
    (hBs : StarConvex ℝ p B)
    (hext : ∀ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain (maxStar F Ω p)) →
      ∃ G : (Fin n → ℂ) → F, AnalyticOnNhd ℂ G (tubeDomain B) ∧
        EqOn G g (tubeDomain (maxStar F Ω p))) :
    B ⊆ maxStar F Ω p := by
  apply subset_maxStar_of_mem
  refine ⟨hB, hBs, fun f hf => ?_⟩
  obtain ⟨g, hg, hgf⟩ := tubeExtends_maxStar hp f hf
  obtain ⟨G, hG, hGg⟩ := hext g hg
  refine ⟨G, hG, ?_⟩
  have : G =ᶠ[𝓝 (ofRealPi p)] g :=
    eventuallyEq_of_mem ((isOpen_tubeDomain isOpen_maxStar).mem_nhds
      (ofRealPi_mem_tubeDomain.mpr hp)) hGg
  exact this.trans hgf

omit [CompleteSpace F] in
open scoped Classical in
/-- Piecewise gluing of holomorphic functions on tubes over an open union, agreeing on the
intersection. -/
theorem analyticOnNhd_ite_tubeDomain {A B : Set (Fin n → ℝ)} (hA : IsOpen A) (hB : IsOpen B)
    {g h : (Fin n → ℂ) → F}
    (hg : AnalyticOnNhd ℂ g (tubeDomain A)) (hh : AnalyticOnNhd ℂ h (tubeDomain B))
    (heq : EqOn g h (tubeDomain (A ∩ B))) :
    AnalyticOnNhd ℂ (fun z => if z ∈ tubeDomain A then g z else h z) (tubeDomain (A ∪ B)) := by
  classical
  intro z hz
  rw [tubeDomain_union] at hz
  rcases hz with hzA | hzB
  · have : (fun z => if z ∈ tubeDomain A then g z else h z) =ᶠ[𝓝 z] g :=
      eventuallyEq_of_mem ((isOpen_tubeDomain hA).mem_nhds hzA) fun w hw => by simp [hw]
    exact (hg z hzA).congr this.symm
  · have : (fun z => if z ∈ tubeDomain A then g z else h z) =ᶠ[𝓝 z] h := by
      refine eventuallyEq_of_mem ((isOpen_tubeDomain hB).mem_nhds hzB) fun w hw => ?_
      by_cases hwA : w ∈ tubeDomain A
      · simp only [hwA, ite_true]
        exact heq ⟨hwA, hw⟩
      · simp only [hwA, ite_false]
    exact (hh z hzB).congr this.symm

end Family

section Triangle

variable {A : Set (Fin n → ℝ)} {p t₁ t₂ : Fin n → ℝ}

/-- **Local continuation on a shrunken triangle.** If the tube over the triangle of scale `a`
lies in the tube over `A` and balls of radius `δ` around the two sides through `p` lie in the
tube over `A`, then every function holomorphic on the tube over `A` continues to the ball of
radius `δ` around each point of the tube over the triangle of a smaller scale `b`. -/
theorem exists_local_continuation_tri (hA : IsOpen A) {a : ℝ} (ha1 : a ≤ 1)
    (htri : tri p t₁ t₂ a ⊆ A) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ w ∈ tubeDomain (segment ℝ p t₁ ∪ segment ℝ p t₂), ball w δ ⊆ tubeDomain A)
    {b : ℝ} (hba : b ≤ a) (hlt : b = 0 ∨ b < a)
    {g : (Fin n → ℂ) → F} (hg : AnalyticOnNhd ℂ g (tubeDomain A)) :
    ∀ ζ ∈ tubeDomain (tri p t₁ t₂ b), ∃ k : (Fin n → ℂ) → F,
      AnalyticOnNhd ℂ k (ball ζ δ) ∧ k =ᶠ[𝓝 ζ] g := by
  intro ζ hζ
  obtain ⟨u, v, huv, hvb, hre⟩ := mem_tubeDomain.mp hζ
  rcases huv.lt_or_eq with hlt' | heq
  · have hv0 : 0 < v := (abs_nonneg u).trans_lt hlt'
    have hbpos : 0 < b := hv0.trans_le hvb
    have hba' : b < a := by
      rcases hlt with h | h
      · exact absurd h hbpos.ne'
      · exact h
    have ha : 0 < a := hbpos.trans hba'
    set s₁ : Fin n → ℝ := p + a • (t₁ - p) with hs₁
    set s₂ : Fin n → ℝ := p + a • (t₂ - p) with hs₂
    have htri' : tri p s₁ s₂ 1 ⊆ A := by rw [← tri_scale p t₁ t₂ ha]; exact htri
    have huv' : |u / a| < v / a := by
      rw [abs_div, abs_of_pos ha]
      exact div_lt_div_of_pos_right hlt' ha
    have hv1 : v / a < 1 := (div_lt_one ha).mpr (hvb.trans_lt hba')
    obtain ⟨c, hc0, -, hreg, hdisc⟩ := exists_parabolaDisc_of_lt p s₁ s₂ huv' hv1 (imPi ζ)
    have hζeq : parabolaDisc p s₁ s₂ c (imPi ζ) ((u / a : ℝ) : ℂ) = ζ := by
      rw [hdisc, hs₁, hs₂, triPt_scale p t₁ t₂ ha.ne', ← hre]
      exact ofRealPi_rePi_add_I_smul_ofRealPi_imPi ζ
    have hhull := parabolaDisc_mem_holomorphicHull p s₁ s₂ htri' hc0 (imPi ζ) (subset_closure hreg)
    rw [hζeq] at hhull
    have hK : IsCompact (parabolaDisc p s₁ s₂ c (imPi ζ) '' frontier (parabolaRegion c)) :=
      isCompact_image_frontier_parabolaRegion p s₁ s₂ hc0 _
    have hKS : parabolaDisc p s₁ s₂ c (imPi ζ) '' frontier (parabolaRegion c) ⊆
        tubeDomain (segment ℝ p t₁ ∪ segment ℝ p t₂) := by
      refine (parabolaDisc_frontier_subset p s₁ s₂ hc0 _).trans (tubeDomain_mono ?_)
      exact union_subset_union (segment_scaled_subset p ha.le ha1 t₁)
        (segment_scaled_subset p ha.le ha1 t₂)
    have hball : ∀ w ∈ parabolaDisc p s₁ s₂ c (imPi ζ) '' frontier (parabolaRegion c),
        ball w δ ⊆ tubeDomain A := fun w hw => hS w (hKS hw)
    exact exists_continuation_ball_of_mem_holomorphicHull (isOpen_tubeDomain hA) hK
      (fun w hw => hball w hw (mem_ball_self hδ)) hδ hball hhull hg
  · have hmem : ζ ∈ tubeDomain (segment ℝ p t₁ ∪ segment ℝ p t₂) := by
      rw [mem_tubeDomain, hre]
      exact triPt_mem_union_segment p t₁ t₂ heq (hvb.trans (hba.trans ha1))
    exact ⟨g, hg.mono (hS ζ hmem), EventuallyEq.rfl⟩

/-- **One step of the triangle induction.** Under maximality, the `δ`-thickening of the tube
over the triangle of a smaller scale is absorbed into `A`. -/
theorem thickening_tri_subset_of_maximal (hA : IsOpen A) (hAs : StarConvex ℝ p A) (hp : p ∈ A)
    (hmax : ∀ B : Set (Fin n → ℝ), IsOpen B → StarConvex ℝ p B →
      (∀ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain A) →
        ∃ G : (Fin n → ℂ) → F, AnalyticOnNhd ℂ G (tubeDomain B) ∧ EqOn G g (tubeDomain A)) →
      B ⊆ A)
    {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ w ∈ tubeDomain (segment ℝ p t₁ ∪ segment ℝ p t₂), ball w δ ⊆ tubeDomain A)
    {a b : ℝ} (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hba : b ≤ a) (hlt : b = 0 ∨ b < a)
    (htri : tri p t₁ t₂ a ⊆ A) : thickening δ (tri p t₁ t₂ b) ⊆ A := by
  classical
  set L := tri p t₁ t₂ b with hL
  set N := thickening δ L with hN
  have hLconv : Convex ℝ L := convex_tri p t₁ t₂ b
  have hpL : p ∈ L := mem_tri_self p t₁ t₂ hb0
  have hLA : L ⊆ A := (tri_mono p t₁ t₂ hba).trans htri
  have hNo : IsOpen N := isOpen_thickening
  have hNc : Convex ℝ N := hLconv.thickening δ
  have hpN : p ∈ N := self_subset_thickening hδ L hpL
  have hNs : StarConvex ℝ p N := hNc.starConvex hpN
  have hTN : tubeDomain N ⊆ ⋃ ζ ∈ tubeDomain L, ball ζ δ := by
    intro z hz
    rw [mem_tubeDomain, hN, Metric.mem_thickening_iff] at hz
    obtain ⟨y, hy, hdist⟩ := hz
    refine mem_iUnion₂.mpr ⟨ofRealPi y + I • ofRealPi (imPi z), ?_, ?_⟩
    · rw [mem_tubeDomain, rePi_add, rePi_ofRealPi, rePi_I_smul_ofRealPi, add_zero]
      exact hy
    · rw [mem_ball, dist_eq_norm]
      have hz := ofRealPi_rePi_add_I_smul_ofRealPi_imPi z
      have : z - (ofRealPi y + I • ofRealPi (imPi z)) = ofRealPi (rePi z - y) := by
        rw [ofRealPi_sub]
        nth_rewrite 1 [← hz]
        abel
      rw [this, norm_ofRealPi, ← dist_eq_norm]
      exact hdist
  have hsub : A ∪ N ⊆ A := by
    refine hmax (A ∪ N) (hA.union hNo) (hAs.union hNs) fun g hg => ?_
    have hloc := exists_local_continuation_tri hA ha1 htri hδ hS hba hlt hg
    obtain ⟨H, hHa, hHg⟩ := exists_glue_of_local_continuations (isOpen_tubeDomain hA)
      (convex_tubeDomain hLconv) (tubeDomain_mono hLA) hg hδ hloc
    have hHN : AnalyticOnNhd ℂ H (tubeDomain N) := hHa.mono hTN
    have hAN : EqOn H g (tubeDomain (A ∩ N)) := by
      have hpAN : p ∈ A ∩ N := ⟨hp, hpN⟩
      exact (hHN.mono (tubeDomain_mono inter_subset_right)).eqOn_of_preconnected_of_eventuallyEq
        (hg.mono (tubeDomain_mono inter_subset_left))
        (isPreconnected_tubeDomain_of_starConvex (hAs.inter hNs) hpAN)
        (ofRealPi_mem_tubeDomain.mpr hpAN) (hHg _ (ofRealPi_mem_tubeDomain.mpr hpL))
    refine ⟨fun z => if z ∈ tubeDomain A then g z else H z, ?_, fun z hz => by simp [hz]⟩
    exact analyticOnNhd_ite_tubeDomain hA hNo hg hHN (fun z hz => (hAN hz).symm)
  exact subset_union_right.trans hsub

/-- A triangle with vanishing direction vectors is the vertex. -/
theorem tri_subset_of_dirs_zero {b : ℝ} {B : Set (Fin n → ℝ)}
    (h1 : triDir₁ p t₁ t₂ = 0) (h2 : triDir₂ p t₁ t₂ = 0) (hpB : p ∈ B) :
    tri p t₁ t₂ b ⊆ B := by
  rintro x ⟨u, v, -, -, rfl⟩
  simpa [triPt, h1, h2] using hpB

/-- One scale step in the triangle lemma: a slightly larger scaled triangle still lies in `A`. -/
theorem tri_subset_scale_step_of_maximal (hA : IsOpen A) (hAs : StarConvex ℝ p A) (hp : p ∈ A)
    (hmax : ∀ B : Set (Fin n → ℝ), IsOpen B → StarConvex ℝ p B →
      (∀ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain A) →
        ∃ G : (Fin n → ℂ) → F, AnalyticOnNhd ℂ G (tubeDomain B) ∧ EqOn G g (tubeDomain A)) →
      B ⊆ A)
    {δ D ε δ₁ a a' : ℝ} (hδ : 0 < δ) (hDpos : 0 < D)
    (hD : D = ‖triDir₁ p t₁ t₂‖ + ‖triDir₂ p t₁ t₂‖)
    (hS : ∀ w ∈ tubeDomain (segment ℝ p t₁ ∪ segment ℝ p t₂), ball w δ ⊆ tubeDomain A)
    (hδ₁ : δ₁ = δ / (4 * D)) (hε : ε = min (1 / 2) (δ / (4 * D)))
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (htri : tri p t₁ t₂ a ⊆ A)
    (ha'δ : a' ≤ a + δ₁) :
    tri p t₁ t₂ a' ⊆ A := by
  set b : ℝ := (1 - ε) * a
  have hεle : ε ≤ 1 / 2 := by rw [hε]; exact min_le_left _ _
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hε1 : 0 ≤ 1 - ε := sub_nonneg.mpr (hεle.trans (by norm_num))
  have hb0 : 0 ≤ b := mul_nonneg hε1 ha0
  have hba : b ≤ a := mul_le_of_le_one_left ha0 (by linarith)
  have hlt : b = 0 ∨ b < a := by
    rcases ha0.lt_or_eq with h | h
    · right; exact mul_lt_of_lt_one_left h (by linarith)
    · left; dsimp [b]; rw [← h, mul_zero]
  have hthick := thickening_tri_subset_of_maximal hA hAs hp hmax hδ hS ha1 hb0 hba hlt htri
  rintro x ⟨u, v, huv, hva', rfl⟩
  by_cases hvb : v ≤ b
  · exact hthick (self_subset_thickening hδ _ ⟨u, v, huv, hvb, rfl⟩)
  · push Not at hvb
    have hv0 : 0 < v := hb0.trans_lt hvb
    set μ : ℝ := b / v
    have hμ0 : 0 ≤ μ := div_nonneg hb0 hv0.le
    have hμ1 : μ ≤ 1 := (div_le_one hv0).mpr hvb.le
    have hμv : μ * v = b := div_mul_cancel₀ b hv0.ne'
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨triPt p t₁ t₂ (μ * u) (μ * v), ⟨μ * u, μ * v, ?_, ?_, rfl⟩, ?_⟩
    · rw [abs_mul, abs_of_nonneg hμ0]
      exact mul_le_mul_of_nonneg_left huv hμ0
    · rw [hμv]
    · rw [dist_eq_norm]
      have hdiff : triPt p t₁ t₂ u v - triPt p t₁ t₂ (μ * u) (μ * v) =
          ((1 - μ) * u) • triDir₁ p t₁ t₂ + ((1 - μ) * v) • triDir₂ p t₁ t₂ := by
        simp only [triPt]
        module
      have h1 : v - b ≤ (a' - a) + ε * a := by
        dsimp [b]
        nlinarith [hva']
      have h2 : (a' - a) + ε * a ≤ δ₁ + ε := by nlinarith
      have hεD : ε ≤ δ / (4 * D) := by rw [hε]; exact min_le_right _ _
      calc ‖triPt p t₁ t₂ u v - triPt p t₁ t₂ (μ * u) (μ * v)‖
          = ‖((1 - μ) * u) • triDir₁ p t₁ t₂ + ((1 - μ) * v) • triDir₂ p t₁ t₂‖ := by rw [hdiff]
        _ ≤ ‖((1 - μ) * u) • triDir₁ p t₁ t₂‖ + ‖((1 - μ) * v) • triDir₂ p t₁ t₂‖ :=
            norm_add_le _ _
        _ = (1 - μ) * |u| * ‖triDir₁ p t₁ t₂‖ + (1 - μ) * v * ‖triDir₂ p t₁ t₂‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
              abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - μ), abs_of_pos hv0]
        _ ≤ (1 - μ) * v * ‖triDir₁ p t₁ t₂‖ + (1 - μ) * v * ‖triDir₂ p t₁ t₂‖ := by
            gcongr
        _ = (v - b) * D := by rw [hD, ← hμv]; ring
        _ ≤ (δ₁ + ε) * D := mul_le_mul_of_nonneg_right (h1.trans h2) hDpos.le
        _ ≤ (δ / (4 * D) + δ / (4 * D)) * D :=
            mul_le_mul_of_nonneg_right (add_le_add (le_of_eq hδ₁) hεD) hDpos.le
        _ = δ / 2 := by field_simp; ring
        _ < δ := half_lt_self hδ

/-- **The triangle lemma.** Under maximality, the full triangle with vertex `p` and two
points of `A` lies in `A`. -/
theorem tri_subset_of_maximal (hA : IsOpen A) (hAs : StarConvex ℝ p A) (hp : p ∈ A)
    (hmax : ∀ B : Set (Fin n → ℝ), IsOpen B → StarConvex ℝ p B →
      (∀ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain A) →
        ∃ G : (Fin n → ℂ) → F, AnalyticOnNhd ℂ G (tubeDomain B) ∧ EqOn G g (tubeDomain A)) →
      B ⊆ A)
    (ht₁ : t₁ ∈ A) (ht₂ : t₂ ∈ A) : tri p t₁ t₂ 1 ⊆ A := by
  have hS_sub : segment ℝ p t₁ ∪ segment ℝ p t₂ ⊆ A :=
    union_subset (hAs.segment_subset ht₁) (hAs.segment_subset ht₂)
  have hS_cpt : IsCompact (segment ℝ p t₁ ∪ segment ℝ p t₂) := by
    refine IsCompact.union ?_ ?_ <;>
      · rw [segment_eq_image']
        exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hδA⟩ := hS_cpt.exists_thickening_subset_open hA hS_sub
  have hS : ∀ w ∈ tubeDomain (segment ℝ p t₁ ∪ segment ℝ p t₂), ball w δ ⊆ tubeDomain A :=
    fun w hw => ball_subset_tubeDomain
      ((ball_subset_thickening (E := segment ℝ p t₁ ∪ segment ℝ p t₂) (x := rePi w) hw δ).trans hδA)
  set D : ℝ := ‖triDir₁ p t₁ t₂‖ + ‖triDir₂ p t₁ t₂‖ with hD
  have hD0 : 0 ≤ D := by positivity
  rcases hD0.lt_or_eq with hDpos | hDzero
  swap
  · have h1 : triDir₁ p t₁ t₂ = 0 :=
      norm_eq_zero.mp (by linarith [norm_nonneg (triDir₁ p t₁ t₂), norm_nonneg (triDir₂ p t₁ t₂)])
    have h2 : triDir₂ p t₁ t₂ = 0 :=
      norm_eq_zero.mp (by linarith [norm_nonneg (triDir₁ p t₁ t₂), norm_nonneg (triDir₂ p t₁ t₂)])
    exact tri_subset_of_dirs_zero h1 h2 hp
  set δ₁ : ℝ := δ / (4 * D)
  set ε : ℝ := min (1 / 2) (δ / (4 * D))
  have hδ₁ : 0 < δ₁ := by positivity
  have hind : ∀ k : ℕ, tri p t₁ t₂ (min 1 (k * δ₁)) ⊆ A := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, zero_mul, min_eq_right zero_le_one, tri_zero]
      simpa using hp
    | succ k ih =>
      have hk0 : (0 : ℝ) ≤ k * δ₁ := by positivity
      refine tri_subset_scale_step_of_maximal hA hAs hp hmax hδ hDpos hD hS rfl rfl
        (le_min zero_le_one hk0) (min_le_left _ _) ih ?_
      rcases le_or_gt 1 (k * δ₁) with h | h
      · rw [min_eq_left h]
        exact le_add_of_le_of_nonneg (min_le_left _ _) hδ₁.le
      · rw [min_eq_right h.le]
        push_cast
        refine (min_le_right _ _).trans ?_
        rw [add_mul, one_mul]
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / δ₁)
  have hk1 : 1 ≤ k * δ₁ := by
    rw [div_le_iff₀ hδ₁] at hk
    linarith
  have := hind k
  rwa [min_eq_left hk1] at this

end Triangle

section Convex

variable {Ω : Set (Fin n → ℝ)} {p : Fin n → ℝ}

/-- **The maximal star-convex extension base is convex.** -/
theorem convex_maxStar (hp : p ∈ maxStar F Ω p) : Convex ℝ (maxStar F Ω p) := by
  rw [convex_iff_segment_subset]
  intro t₁ ht₁ t₂ ht₂
  exact (segment_subset_tri p t₁ t₂).trans (tri_subset_of_maximal isOpen_maxStar starConvex_maxStar
    hp (fun _ hB hBs hext => maxStar_maximal hp hB hBs hext) ht₁ ht₂)

end Convex

end BochnerTube

open BochnerTube

section Convex

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {Ω : Set (Fin n → ℝ)} {p : Fin n → ℝ}

/-- **Bochner's tube theorem for star-convex bases.** Every Banach-valued holomorphic function
on the tube over an open star-convex base extends to the tube over the convex hull. -/
theorem exists_extension_tubeDomain_convexHull_of_starConvex (hΩ : IsOpen Ω)
    (hs : StarConvex ℝ p Ω) (hp : p ∈ Ω) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f (tubeDomain Ω)) :
    ∃ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (tubeDomain (convexHull ℝ Ω)) ∧
      EqOn g f (tubeDomain Ω) := by
  have hΩmem : Ω ∈ starFamily F Ω p := ⟨hΩ, hs, fun f hf => ⟨f, hf, EventuallyEq.rfl⟩⟩
  have hΩsub : Ω ⊆ maxStar F Ω p := subset_maxStar_of_mem hΩmem
  have hpm : p ∈ maxStar F Ω p := hΩsub hp
  have hconv : convexHull ℝ Ω ⊆ maxStar F Ω p := convexHull_min hΩsub (convex_maxStar hpm)
  obtain ⟨g, hg, hgf⟩ := tubeExtends_maxStar hpm f hf
  refine ⟨g, hg.mono (tubeDomain_mono hconv), ?_⟩
  exact (hg.mono (tubeDomain_mono hΩsub)).eqOn_of_preconnected_of_eventuallyEq hf
    (isPreconnected_tubeDomain_of_starConvex hs hp) (ofRealPi_mem_tubeDomain.mpr hp) hgf

end Convex

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
