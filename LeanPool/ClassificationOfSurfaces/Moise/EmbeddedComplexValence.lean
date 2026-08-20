/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.Brouwer
import LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteTriangulation
import LeanPool.ClassificationOfSurfaces.Surface
import LeanPool.ClassificationOfSurfaces.Topology.InvarianceOfDomain

/-!
# Edge valence of a triangle complex embedded in a surface

An abstract finite family of triangles can embed in a surface only if at most two maximal
triangles meet along any two-vertex edge.  The proof is the local invariance-of-domain argument
used implicitly in Moise's gluing theorem: two pages around an edge already form a planar
neighborhood, so a third page approaching the same edge would have to enter their open image.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open InvarianceOfDomain

private theorem max_pos_add_max_neg_eq_abs (x : ℝ) :
    max x 0 + max (-x) 0 = |x| := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), add_zero,
      abs_of_nonneg hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), zero_add,
      abs_of_nonpos hx']

private theorem max_pos_sub_max_neg_eq_self (x : ℝ) :
    max x 0 - max (-x) 0 = x := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), zero_sub,
      neg_neg]

section

variable {S : Type*} [TopologicalSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]

/-- Two triangles meeting along an edge give an open neighborhood of the embedded edge midpoint
whose realizations have no weight away from the four vertices of those two triangles. -/
private theorem exists_pair_pages_open_neighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) (ι : GeometricRealization V F → S)
    (hι : _root_.Topology.IsEmbedding ι) (t u : Finset V) (htF : t ∈ F) (huF : u ∈ F)
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (htc : t = insert c {a, b}) (hud : u = insert d {a, b}) :
    ∃ edgeMid : GeometricRealization V F, ∃ W : Set S,
      W ∈ nhds (ι edgeMid) ∧
        edgeMid.1 = (1 / 2 : ℝ) • Pi.single a 1 + (1 / 2 : ℝ) • Pi.single b 1 ∧
        ∀ y : GeometricRealization V F, ι y ∈ W → ∀ k : V,
          k ≠ a → k ≠ b → k ≠ c → k ≠ d → y.1 k = 0 := by
  let O : Set Plane := {x | |x 0| < 1 / 4 ∧ |x 1| < 1 / 4}
  have hOopen : IsOpen O := by
    have h0 : Continuous (fun x : Plane ↦ |x 0|) := by fun_prop
    have h1 : Continuous (fun x : Plane ↦ |x 1|) := by fun_prop
    exact (isOpen_lt h0 continuous_const).inter (isOpen_lt h1 continuous_const)
  let weight (x : Plane) : V → ℝ :=
    (1 / 2 - x 0) • Pi.single a 1 +
      (1 / 2 + x 0 - |x 1|) • Pi.single b 1 +
      max (x 1) 0 • Pi.single c 1 + max (-x 1) 0 • Pi.single d 1
  have weight_a (x : Plane) : weight x a = 1 / 2 - x 0 := by
    simp [weight, hab, hac, had]
  have weight_b (x : Plane) : weight x b = 1 / 2 + x 0 - |x 1| := by
    simp [weight, hab, hbc, hbd]
  have weight_c (x : Plane) : weight x c = max (x 1) 0 := by
    simp [weight, hac, hbc, hcd]
  have weight_d (x : Plane) : weight x d = max (-x 1) 0 := by
    simp [weight, had, hbd, hcd]
  have weight_other (x : Plane) {z : V}
      (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) (hzd : z ≠ d) : weight x z = 0 := by
    simp [weight, hza, hzb, hzc, hzd]
  have sum_pi_single (q : V) : ∑ z, Pi.single q (1 : ℝ) z = 1 := by
    rw [Fintype.sum_eq_single q]
    · simp
    · intro z hz
      exact Pi.single_eq_of_ne hz 1
  have weight_nonneg (x : O) (z : V) : 0 ≤ weight x.1 z := by
    by_cases hza : z = a
    · subst z
      rw [weight_a]
      linarith [(abs_lt.mp x.2.1).2]
    by_cases hzb : z = b
    · subst z
      rw [weight_b]
      linarith [(abs_lt.mp x.2.1).1, x.2.2]
    by_cases hzc : z = c
    · subst z
      rw [weight_c]
      exact le_max_right _ _
    by_cases hzd : z = d
    · subst z
      rw [weight_d]
      exact le_max_right _ _
    rw [weight_other _ hza hzb hzc hzd]
  have weight_sum (x : Plane) : ∑ z, weight x z = 1 := by
    simp_rw [weight, Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.smul_sum,
      sum_pi_single a, sum_pi_single b, sum_pi_single c, sum_pi_single d]
    simp only [smul_eq_mul, mul_one]
    linarith [max_pos_add_max_neg_eq_abs (x 1)]
  have weight_supported (x : O) : ∃ s ∈ F, ∀ z ∉ s, weight x.1 z = 0 := by
    by_cases hx : 0 ≤ x.1 1
    · refine ⟨t, htF, ?_⟩
      intro z hzt
      have hza : z ≠ a := fun h ↦ hzt (h ▸ by simp [htc])
      have hzb : z ≠ b := fun h ↦ hzt (h ▸ by simp [htc])
      have hzc : z ≠ c := fun h ↦ hzt (h ▸ by simp [htc])
      by_cases hzd : z = d
      · subst z
        rw [weight_d, max_eq_right (neg_nonpos.mpr hx)]
      · exact weight_other _ hza hzb hzc hzd
    · have hx' : x.1 1 ≤ 0 := le_of_not_ge hx
      refine ⟨u, huF, ?_⟩
      intro z hzu
      have hza : z ≠ a := fun h ↦ hzu (h ▸ by simp [hud])
      have hzb : z ≠ b := fun h ↦ hzu (h ▸ by simp [hud])
      have hzd : z ≠ d := fun h ↦ hzu (h ▸ by simp [hud])
      by_cases hzc : z = c
      · subst z
        rw [weight_c, max_eq_right hx']
      · exact weight_other _ hza hzb hzc hzd
  let fan : O → GeometricRealization V F := fun x ↦
    ⟨weight x.1, ⟨weight_nonneg x, weight_sum x.1⟩, weight_supported x⟩
  have fan_continuous : Continuous fan := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro z
    change Continuous fun x : O ↦ weight x.1 z
    simp only [weight, Pi.add_apply, Pi.smul_apply]
    fun_prop
  have fan_injective : Function.Injective fan := by
    intro x y hxy
    apply Subtype.ext
    apply PiLp.ext
    intro i
    have hval : weight x.1 = weight y.1 := congrArg Subtype.val hxy
    fin_cases i
    · change x.1 (0 : Fin 2) = y.1 (0 : Fin 2)
      have ha := congrFun hval a
      rw [weight_a, weight_a] at ha
      linarith
    · change x.1 (1 : Fin 2) = y.1 (1 : Fin 2)
      have hc := congrFun hval c
      have hd := congrFun hval d
      rw [weight_c, weight_c] at hc
      rw [weight_d, weight_d] at hd
      linarith [max_pos_sub_max_neg_eq_self (x.1 1),
        max_pos_sub_max_neg_eq_self (y.1 1)]
  let pairMap : O → S := fun x ↦ ι (fan x)
  have pairOpen : IsOpen (Set.range pairMap) :=
    isOpen_range_of_isOpen_of_continuous_injective
      (modelWithCornersEuclideanHalfSpace 2) hOopen pairMap
        (hι.continuous.comp fan_continuous) (hι.injective.comp fan_injective)
  let zeroO : O := ⟨0, by simp [O]⟩
  have midpoint_weight : weight zeroO.1 =
      (1 / 2 : ℝ) • Pi.single a 1 + (1 / 2 : ℝ) • Pi.single b 1 := by
    funext z
    by_cases hza : z = a
    · subst z
      simp [weight, zeroO, hab, had]
    by_cases hzb : z = b
    · subst z
      simp [weight, zeroO, hab, hbd]
    simp [weight, zeroO, hza, hzb]
  let edgeMid : GeometricRealization V F := fan zeroO
  refine ⟨edgeMid, Set.range pairMap, pairOpen.mem_nhds ⟨zeroO, rfl⟩, ?_, ?_⟩
  · exact midpoint_weight
  · intro y hy k hka hkb hkc hkd
    obtain ⟨x, hx⟩ := hy
    have hsource : fan x = y := hι.injective hx
    have hk := congrFun (congrArg Subtype.val hsource) k
    change weight x.1 k = y.1 k at hk
    rw [weight_other _ hka hkb hkc hkd] at hk
    exact hk.symm

/-- A finite family of abstract triangles carried by an embedded barycentric realization in a
surface has edge valence at most two. -/
theorem edge_valence_le_two_of_isEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V))
    (hcard : ∀ t ∈ F, t.card = 3)
    (ι : GeometricRealization V F → S)
    (hι : _root_.Topology.IsEmbedding ι)
    (e : Finset V) (hecard : e.card = 2) :
    (F.filter fun t ↦ e ⊆ t).card ≤ 2 := by
  classical
  by_contra hnot
  have hthree : 2 < (F.filter fun t ↦ e ⊆ t).card := by omega
  obtain ⟨t, u, v, ht, hu, hv, htu, htv, huv⟩ :=
    Finset.two_lt_card_iff.mp hthree
  have htF : t ∈ F := (Finset.mem_filter.mp ht).1
  have huF : u ∈ F := (Finset.mem_filter.mp hu).1
  have hvF : v ∈ F := (Finset.mem_filter.mp hv).1
  have het : e ⊆ t := (Finset.mem_filter.mp ht).2
  have heu : e ⊆ u := (Finset.mem_filter.mp hu).2
  have hev : e ⊆ v := (Finset.mem_filter.mp hv).2
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp hecard
  have extra_vertex
      (s : Finset V) (hsF : s ∈ F) (hes : e ⊆ s) :
      ∃ c : V, c ∉ e ∧ s = insert c e := by
    have hdiffcard : (s \ e).card = 1 := by
      rw [Finset.card_sdiff_of_subset hes, hcard s hsF, hecard]
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hdiffcard
    refine ⟨c, ?_, ?_⟩
    · have hcMem : c ∈ s \ e := by rw [hc]; simp
      exact (Finset.mem_sdiff.mp hcMem).2
    · symm
      rw [← Finset.sdiff_union_of_subset hes, hc]
      simp
  obtain ⟨c, hce, htc⟩ := extra_vertex t htF het
  obtain ⟨d, hde, hud⟩ := extra_vertex u huF heu
  obtain ⟨k, hke, hvk⟩ := extra_vertex v hvF hev
  have hac : a ≠ c := by
    intro h
    apply hce
    rw [← h]
    simp [he]
  have hbc : b ≠ c := by
    intro h
    apply hce
    rw [← h]
    simp [he]
  have had : a ≠ d := by
    intro h
    apply hde
    rw [← h]
    simp [he]
  have hbd : b ≠ d := by
    intro h
    apply hde
    rw [← h]
    simp [he]
  have hak : a ≠ k := by
    intro h
    apply hke
    rw [← h]
    simp [he]
  have hbk : b ≠ k := by
    intro h
    apply hke
    rw [← h]
    simp [he]
  have hcd : c ≠ d := by
    intro h
    apply htu
    rw [htc, hud, h]
  have hck : c ≠ k := by
    intro h
    apply htv
    rw [htc, hvk, h]
  have hdk : d ≠ k := by
    intro h
    apply huv
    rw [hud, hvk, h]
  have sum_pi_single (q : V) :
      ∑ z, Pi.single q (1 : ℝ) z = 1 := by
    rw [Fintype.sum_eq_single q]
    · simp
    · intro z hz
      exact Pi.single_eq_of_ne hz 1
  obtain ⟨edgeMid, W, hedgeOpen, midpoint_weight, hWsupport⟩ :=
    exists_pair_pages_open_neighborhood F ι hι t u htF huF a b c d hab hac hbc had hbd
      hcd (by simpa [he] using htc) (by simpa [he] using hud)
  let thirdWeight (r : Set.Icc (0 : ℝ) 1) : V → ℝ :=
    ((1 - r.1) / 2) • Pi.single a 1 +
      ((1 - r.1) / 2) • Pi.single b 1 +
      r.1 • Pi.single k 1
  have third_nonneg (r : Set.Icc (0 : ℝ) 1) (z : V) :
      0 ≤ thirdWeight r z := by
    have hcoef : 0 ≤ (1 - r.1) / 2 := by
      exact div_nonneg (sub_nonneg.mpr r.2.2) (by norm_num)
    by_cases hza : z = a
    · subst z
      simpa [thirdWeight, hab, hak] using hcoef
    by_cases hzb : z = b
    · subst z
      simpa [thirdWeight, hab, hbk] using hcoef
    by_cases hzk : z = k
    · subst z
      simpa [thirdWeight, hak, hbk] using r.2.1
    simp [thirdWeight, hza, hzb, hzk]
  have third_sum (r : Set.Icc (0 : ℝ) 1) :
      ∑ z, thirdWeight r z = 1 := by
    simp_rw [thirdWeight, Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.smul_sum, ← Finset.smul_sum, ← Finset.smul_sum]
    rw [sum_pi_single a, sum_pi_single b, sum_pi_single k]
    ring
  have third_supported (r : Set.Icc (0 : ℝ) 1) :
      ∃ s ∈ F, ∀ z ∉ s, thirdWeight r z = 0 := by
    refine ⟨v, hvF, ?_⟩
    intro z hzv
    have hza : z ≠ a := fun h ↦ hzv (h ▸ hev (by simp [he]))
    have hzb : z ≠ b := fun h ↦ hzv (h ▸ hev (by simp [he]))
    have hzk : z ≠ k := fun h ↦ hzv (h ▸ by
      rw [hvk]
      exact Finset.mem_insert_self _ _)
    simp [thirdWeight, hza, hzb, hzk]
  let third : Set.Icc (0 : ℝ) 1 → GeometricRealization V F :=
    fun r ↦
      ⟨thirdWeight r, ⟨third_nonneg r, third_sum r⟩,
        third_supported r⟩
  have third_continuous : Continuous third := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro z
    change Continuous fun r : Set.Icc (0 : ℝ) 1 ↦ thirdWeight r z
    simp only [thirdWeight, Pi.add_apply, Pi.smul_apply]
    fun_prop
  let zeroIcc : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
  have third_zero : third zeroIcc = edgeMid := by
    apply Subtype.ext
    change thirdWeight zeroIcc = edgeMid.1
    rw [midpoint_weight]
    funext z
    simp [thirdWeight, zeroIcc]
  have hpre :
      (ι ∘ third) ⁻¹' W ∈ nhds zeroIcc := by
    have hcont : Continuous (ι ∘ third) :=
      hι.continuous.comp third_continuous
    apply hcont.continuousAt
    change W ∈ nhds (ι (third zeroIcc))
    rw [third_zero]
    exact hedgeOpen
  obtain ⟨G, hGsub, hGopen, hzeroG⟩ :=
    _root_.mem_nhds_iff.mp hpre
  obtain ⟨ε, hεpos, hεball⟩ :=
    Metric.isOpen_iff.mp hGopen zeroIcc hzeroG
  let r₀ : ℝ := min (ε / 2) (1 / 2)
  have hr₀pos : 0 < r₀ := lt_min (half_pos hεpos) (by norm_num)
  have hr₀one : r₀ ≤ 1 := by
    exact (min_le_right _ _).trans (by norm_num)
  let r : Set.Icc (0 : ℝ) 1 := ⟨r₀, le_of_lt hr₀pos, hr₀one⟩
  have hrzero : r ≠ zeroIcc := by
    intro h
    have : r₀ = 0 := congrArg Subtype.val h
    linarith
  have hrG : r ∈ G := by
    apply hεball
    change dist r zeroIcc < ε
    rw [Subtype.dist_eq, Real.dist_eq]
    change |r₀ - 0| < ε
    rw [sub_zero, abs_of_pos hr₀pos]
    exact (min_le_left _ _).trans_lt (half_lt_self hεpos)
  have hrPair : ι (third r) ∈ W :=
    hGsub hrG
  have hkThird : thirdWeight r k = r₀ := by
    simp [thirdWeight, r, hak, hbk]
  have hkZero := hWsupport (third r) hrPair k
    (Ne.symm hak) (Ne.symm hbk) (Ne.symm hck) (Ne.symm hdk)
  change thirdWeight r k = 0 at hkZero
  rw [hkThird] at hkZero
  linarith

end

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
