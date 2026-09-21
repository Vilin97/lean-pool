/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.CantorBendixson
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixsonReconstruction
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.PWOAddition
public import Mathlib.Topology.Instances.Real.Lemmas

import Mathlib.SetTheory.Ordinal.FixedPoint
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneContinuity
import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Closed real well-orders

A closed well-ordered subset of the reals is canonically homeomorphic to its ordinal index
space. Closing a well-order below a strict supremum inserts at most one limit point before each
original point; in particular it preserves a nonzero additively principal order type.
-/

open Filter Order Set Topology
open Ordinal

public noncomputable section

namespace Set.IsPWO

variable {s : Set ℝ} (hs : s.IsPWO)

private def enumReal (s : Set ℝ) [WellFoundedLT s] :
    Iio (Ordinal.type (· < · : s → s → Prop)) → ℝ :=
  fun i ↦ (Ordinal.enum (· < · : s → s → Prop) i).1

private theorem enumReal_strictMono (s : Set ℝ) [WellFoundedLT s] : StrictMono (enumReal s) := by
  intro i j hij
  exact (Ordinal.enum_lt_enum (r := (· < · : s → s → Prop))).mpr hij

private theorem exists_enumReal_ge_of_isSuccLimit [WellFoundedLT s] (hc : IsClosed s)
    {i : Iio (Ordinal.type (· < · : s → s → Prop))} (hi : IsSuccLimit i.1)
    {b : ℝ} (hb : b < enumReal s i) :
    ∃ j < i, b ≤ enumReal s j := by
  let A : Set ℝ := enumReal s '' Iio i
  have hAne : A.Nonempty := by
    let j : Iio (Ordinal.type (· < · : s → s → Prop)) :=
      ⟨0, hi.bot_lt.trans i.2⟩
    exact ⟨enumReal s j, ⟨j, hi.bot_lt, rfl⟩⟩
  have hAbdd : BddAbove A := by
    refine ⟨enumReal s i, ?_⟩
    rintro _ ⟨j, hji, rfl⟩
    exact (enumReal_strictMono s hji).le
  have hAs : A ⊆ s := by
    rintro _ ⟨j, _, rfl⟩
    exact (Ordinal.enum (· < · : s → s → Prop) j).2
  have hsupmem : sSup A ∈ s := hc.closure_subset
    (closure_mono hAs (csSup_mem_closure hAne hAbdd))
  have hsup_le : sSup A ≤ enumReal s i := csSup_le hAne fun _ hx ↦ by
    obtain ⟨j, hji, rfl⟩ := hx
    exact (enumReal_strictMono s hji).le
  have hsup_eq : sSup A = enumReal s i := by
    apply le_antisymm hsup_le
    by_contra hnot
    have hlt : sSup A < enumReal s i := lt_of_not_ge hnot
    let k : Iio (Ordinal.type (· < · : s → s → Prop)) :=
      ⟨Ordinal.typein (· < · : s → s → Prop) ⟨sSup A, hsupmem⟩,
        Ordinal.typein_lt_type _ _⟩
    have hki : k < i := by
      apply (Ordinal.enum_lt_enum (r := (· < · : s → s → Prop))).mp
      have hk : Ordinal.enum (· < · : s → s → Prop) k = ⟨sSup A, hsupmem⟩ := by
        simp [k]
      rw [hk]
      exact hlt
    have hsucc : k.1 + 1 < i.1 := hi.succ_lt hki
    let j : Iio (Ordinal.type (· < · : s → s → Prop)) :=
      ⟨k.1 + 1, hsucc.trans i.2⟩
    have hjA : enumReal s j ∈ A := ⟨j, hsucc, rfl⟩
    have hkj : k < j := Order.lt_succ k.1
    have hsup_lt : sSup A < enumReal s j := by
      have := enumReal_strictMono s hkj
      simpa [k, enumReal] using this
    exact (not_lt_of_ge (le_csSup hAbdd hjA)) hsup_lt
  by_contra! hnone
  have hub : b ∈ upperBounds A := by
    rintro _ ⟨j, hji, rfl⟩
    exact (hnone j hji).le
  have hle : enumReal s i ≤ b := by
    rw [← hsup_eq]
    exact (isLUB_csSup hAne hAbdd).2 hub
  exact (not_lt_of_ge hle) hb

private theorem nhdsWithin_Ici_eq_pure
    {T : Ordinal} (i : Iio T) : 𝓝[Set.Ici i] i = pure i := by
  apply le_antisymm
  · rw [le_pure_iff]
    have hopen : IsOpen {j : Iio T | j.1 < i.1 + 1} :=
      isOpen_Iio.preimage continuous_subtype_val
    have hmem : {j : Iio T | j.1 < i.1 + 1} ∈ 𝓝 i :=
      hopen.mem_nhds (Order.lt_succ i.1)
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨_, hmem, ?_⟩
    intro j hj
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    exact le_antisymm (Order.lt_succ_iff.mp hj.1) hj.2
  · exact pure_le_nhdsWithin (mem_Ici.mpr le_rfl)

private theorem continuousAt_enumReal_of_not_isSuccLimit [WellFoundedLT s]
    {i : Iio (Ordinal.type (· < · : s → s → Prop))} (hi : ¬IsSuccLimit i.1) :
    ContinuousAt (enumReal s) i := by
  have hopenOrdinal : IsOpen ({i.1} : Set Ordinal) :=
    SuccOrder.isOpen_singleton_iff.mpr hi
  have hopen : IsOpen ({i} : Set (Iio (Ordinal.type (· < · : s → s → Prop)))) := by
    rw [show ({i} : Set (Iio (Ordinal.type (· < · : s → s → Prop)))) =
        (fun j : Iio (Ordinal.type (· < · : s → s → Prop)) ↦ j.1) ⁻¹' {i.1} by
      ext j
      exact Subtype.ext_iff]
    exact hopenOrdinal.preimage continuous_subtype_val
  change Tendsto (enumReal s) (𝓝 i) (𝓝 (enumReal s i))
  rw [(isOpen_singleton_iff_nhds_eq_pure i).mp hopen]
  exact pure_le_nhds _

private theorem continuous_enumReal [WellFoundedLT s] (hc : IsClosed s) :
    Continuous (enumReal s) := by
  rw [continuous_iff_continuousAt]
  intro i
  by_cases hi : IsSuccLimit i.1
  · apply continuousAt_iff_continuous_left_right.mpr
    constructor
    · apply StrictMonoOn.continuousWithinAt_left_of_exists_between
        (s := Set.univ) ((enumReal_strictMono s).strictMonoOn Set.univ) univ_mem
      intro b hb
      obtain ⟨j, hji, hbj⟩ := exists_enumReal_ge_of_isSuccLimit hc hi hb
      exact ⟨j, mem_univ _, hbj, enumReal_strictMono s hji⟩
    · change Tendsto (enumReal s) (𝓝[Set.Ici i] i) (𝓝 (enumReal s i))
      rw [nhdsWithin_Ici_eq_pure]
      exact pure_le_nhds _
  · exact continuousAt_enumReal_of_not_isSuccLimit hi

private def enumRealOrderIso (s : Set ℝ) [WellFoundedLT s] :
    Iio (Ordinal.type (· < · : s → s → Prop)) ≃o s :=
  OrderIso.ofRelIsoLT (Ordinal.enum (· < · : s → s → Prop))

private theorem continuous_typeinReal [WellFoundedLT s] :
    Continuous (enumRealOrderIso s).symm := by
  let t : TopologicalSpace (Iio (Ordinal.type (· < · : s → s → Prop))) := inferInstance
  have ht : t = Preorder.topology (Iio (Ordinal.type (· < · : s → s → Prop))) :=
    OrderTopology.topology_eq_generate_intervals
  change @Continuous s (Iio (Ordinal.type (· < · : s → s → Prop))) _ t
    (enumRealOrderIso s).symm
  rw [ht, continuous_generateFrom_iff]
  rintro u ⟨a, rfl | rfl⟩
  · rw [show (enumRealOrderIso s).symm ⁻¹' Ioi a =
        Subtype.val ⁻¹' Ioi ((enumRealOrderIso s) a).1 by
      ext x
      change a < (enumRealOrderIso s).symm x ↔ (enumRealOrderIso s) a < x
      constructor
      · intro h
        have h' := (enumRealOrderIso s).strictMono h
        rw [(enumRealOrderIso s).apply_symm_apply] at h'
        exact h'
      · intro h
        have h' := (enumRealOrderIso s).symm.strictMono h
        rw [(enumRealOrderIso s).symm_apply_apply] at h'
        exact h']
    exact isOpen_Ioi.preimage continuous_subtype_val
  · rw [show (enumRealOrderIso s).symm ⁻¹' Iio a =
        Subtype.val ⁻¹' Iio ((enumRealOrderIso s) a).1 by
      ext x
      change (enumRealOrderIso s).symm x < a ↔ x < (enumRealOrderIso s) a
      constructor
      · intro h
        have h' := (enumRealOrderIso s).strictMono h
        rw [(enumRealOrderIso s).apply_symm_apply] at h'
        exact h'
      · intro h
        have h' := (enumRealOrderIso s).symm.strictMono h
        rw [(enumRealOrderIso s).symm_apply_apply] at h'
        exact h']
    exact isOpen_Iio.preimage continuous_subtype_val

/-- The canonical enumeration of a closed real well-order is a homeomorphism from its ordinal
index space. -/
def homeomorphIioType [WellFoundedLT s] (hc : IsClosed s) :
    Iio (Ordinal.type (· < · : s → s → Prop)) ≃ₜ s :=
  Homeomorph.mk (enumRealOrderIso s).toEquiv
    (Continuous.subtype_mk (continuous_enumReal hc) _)
    continuous_typeinReal

end Set.IsPWO
universe u

namespace Set

variable {s : Set ℝ}

private theorem exists_mem_Ioc_of_mem_closure' (hs : s.IsPWO) {x y : ℝ}
    (hx : x ∈ closure s) (hy : y < x) :
    ∃ b ∈ s, y < b ∧ b ≤ x := by
  by_contra! hn
  have habove : ∀ b ∈ s, y < b → x < b := fun b hb hyb ↦ hn b hb hyb
  let v := s ∩ Ioi x
  have hv : v.IsWF := hs.isWF.mono inter_subset_left
  have hne : v.Nonempty := by
    obtain ⟨b, hby, hbs⟩ := mem_closure_iff_nhds.mp hx (Ioi y) (Ioi_mem_nhds hy)
    exact ⟨b, hbs, habove b hbs hby⟩
  let m := hv.min hne
  have hm : m ∈ v := hv.min_mem hne
  obtain ⟨b, hb, hbs⟩ := mem_closure_iff_nhds.mp hx (Ioo y m) (Ioo_mem_nhds hy hm.2)
  exact (not_lt_of_ge (hv.min_le hne ⟨hbs, habove b hbs hb.1⟩)) hb.2

variable {z : ℝ}

private def strictClosure : Set ℝ := closure s ∩ Iio z

private theorem exists_support_above (hz : IsLUB s z)
    (x : strictClosure (s := s) (z := z)) :
    ∃ y ∈ s, x.1 < y := by
  obtain ⟨y, hy, hxy, -⟩ := hz.exists_between x.2.2
  exact ⟨y, hy, hxy⟩

private def upperSupport (x : strictClosure (s := s) (z := z)) : Set ℝ := s ∩ Ici x.1

private theorem upperSupport_nonempty (hz : IsLUB s z)
    (x : strictClosure (s := s) (z := z)) :
    (upperSupport (s := s) (z := z) x).Nonempty := by
  obtain ⟨y, hy, hxy⟩ := exists_support_above hz x
  exact ⟨y, hy, hxy.le⟩

private noncomputable def ceiling (hs : s.IsPWO) (hz : IsLUB s z)
    (x : strictClosure (s := s) (z := z)) : ℝ :=
  (hs.isWF.mono (s := upperSupport (s := s) (z := z) x) inter_subset_left).min
    (upperSupport_nonempty hz x)

private theorem ceiling_mem (hs : s.IsPWO) (hz : IsLUB s z)
    (x : strictClosure (s := s) (z := z)) :
    ceiling hs hz x ∈ s ∩ Ici x.1 :=
  (hs.isWF.mono (s := upperSupport (s := s) (z := z) x) inter_subset_left).min_mem
    (upperSupport_nonempty hz x)

private theorem ceiling_le_of_mem (hs : s.IsPWO) (hz : IsLUB s z)
    (x : strictClosure (s := s) (z := z)) {y : ℝ}
    (hy : y ∈ s) (hxy : x.1 ≤ y) :
    ceiling hs hz x ≤ y :=
  (hs.isWF.mono (s := upperSupport (s := s) (z := z) x) inter_subset_left).min_le
    (upperSupport_nonempty hz x) ⟨hy, hxy⟩

private theorem ceiling_eq_self_of_mem (hs : s.IsPWO) (hz : IsLUB s z)
    (x : strictClosure (s := s) (z := z))
    (hx : x.1 ∈ s) :
    ceiling hs hz x = x.1 :=
  le_antisymm (ceiling_le_of_mem hs hz x hx le_rfl) (ceiling_mem hs hz x).2

private noncomputable def closureEmbedding (hs : s.IsPWO) (hz : IsLUB s z) :
    strictClosure (s := s) (z := z) → s ×ₗ Fin 2 := by
  classical
  exact fun x ↦
    ⟨⟨ceiling hs hz x, (ceiling_mem hs hz x).1⟩,
      if x.1 ∈ s then (1 : Fin 2) else 0⟩

private theorem closureEmbedding_strictMono (hs : s.IsPWO) (hz : IsLUB s z) :
    StrictMono (closureEmbedding hs hz) := by
  intro x y hxy
  have hceil : ceiling hs hz x ≤ ceiling hs hz y :=
    ceiling_le_of_mem hs hz x (ceiling_mem hs hz y).1
      ((show x.1 ≤ y.1 from hxy.le).trans (ceiling_mem hs hz y).2)
  by_cases hlt : ceiling hs hz x < ceiling hs hz y
  · rw [Prod.Lex.lt_iff]
    exact Or.inl hlt
  · have heq : ceiling hs hz x = ceiling hs hz y := le_antisymm hceil (not_lt.mp hlt)
    have hxnot : x.1 ∉ s := by
      intro hxs
      have hxceil := ceiling_eq_self_of_mem hs hz x hxs
      have hy_le : y.1 ≤ ceiling hs hz y := (ceiling_mem hs hz y).2
      have hyx : y.1 ≤ x.1 := by
        rw [← hxceil, heq]
        exact hy_le
      exact (not_le_of_gt hxy) hyx
    have hys : y.1 ∈ s := by
      by_contra hynot
      obtain ⟨b, hbs, hxb, hby⟩ :=
        exists_mem_Ioc_of_mem_closure' hs y.2.1 hxy
      have hb_lt : b < y.1 := lt_of_le_of_ne hby fun h ↦ hynot (h ▸ hbs)
      have hceilb : ceiling hs hz x ≤ b := ceiling_le_of_mem hs hz x hbs hxb.le
      have hyceil : y.1 ≤ ceiling hs hz y := (ceiling_mem hs hz y).2
      have : ceiling hs hz y < ceiling hs hz y :=
        heq.symm.le.trans_lt (hceilb.trans_lt (hb_lt.trans_le hyceil))
      exact (lt_irrefl _ this)
    rw [Prod.Lex.lt_iff]
    refine Or.inr ⟨Subtype.ext heq, ?_⟩
    simp only [closureEmbedding, hxnot, hys, ↓reduceIte]
    change (0 : Fin 2) < 1
    simp

private theorem strictClosure_orderType_le_two_mul (hs : s.IsPWO) (hz : IsLUB s z) :
    ((hs.closure.mono (s := strictClosure (s := s) (z := z))
      inter_subset_left).orderType) ≤
      2 * hs.orderType := by
  let ht := hs.closure.mono (s := strictClosure (s := s) (z := z)) inter_subset_left
  letI : WellFoundedLT (strictClosure (s := s) (z := z)) := ⟨ht.isWF⟩
  letI : WellFoundedLT s := ⟨hs.isWF⟩
  let e : strictClosure (s := s) (z := z) ↪o s ×ₗ Fin 2 :=
    OrderEmbedding.ofStrictMono (closureEmbedding hs hz)
      (closureEmbedding_strictMono hs hz)
  calc
    ht.orderType = typeLT (strictClosure (s := s) (z := z)) :=
      ht.orderType_eq_typeLT_of_orderIso (OrderIso.refl _)
    _ ≤ typeLT (s ×ₗ Fin 2) := e.ltEmbedding.ordinal_type_le
    _ = 2 * hs.orderType := by
      change Ordinal.type (Prod.Lex (fun a b : s ↦ a < b)
        (fun a b : Fin 2 ↦ a < b)) = _
      rw [Ordinal.type_prod_lex, Ordinal.type_fin]
      exact congrArg (2 * ·) (hs.orderType_eq_typeLT_of_orderIso (OrderIso.refl s)).symm

private theorem strictClosure_orderType_eq_of_two_mul (hs : s.IsPWO) (hz : IsLUB s z)
    (hzn : z ∉ s) (habsorb : 2 * hs.orderType = hs.orderType) :
    (hs.closure.mono (s := strictClosure (s := s) (z := z))
      inter_subset_left).orderType = hs.orderType := by
  let ht := hs.closure.mono (s := strictClosure (s := s) (z := z)) inter_subset_left
  apply le_antisymm
  · simpa only [habsorb] using strictClosure_orderType_le_two_mul hs hz
  · apply hs.orderType_mono ht
    intro x hx
    refine ⟨subset_closure hx, ?_⟩
    exact lt_of_le_of_ne (hz.1 hx) fun h ↦ hzn (h ▸ hx)

private theorem strictClosure_orderType_eq_opow (hs : s.IsPWO) (hz : IsLUB s z)
    (hzn : z ∉ s) {a : Ordinal} (ha : a ≠ 0)
    (htype : hs.orderType = omega0 ^ a) :
    (hs.closure.mono (s := strictClosure (s := s) (z := z))
      inter_subset_left).orderType = omega0 ^ a := by
  have habsorb : 2 * hs.orderType = hs.orderType := by
    rw [htype, mul_eq_right_iff_opow_omega0_dvd]
    have h2 : (2 : Ordinal) ^ omega0 = omega0 := natCast_opow_omega0 (by norm_num)
    rw [h2]
    have hle : (1 : Ordinal) ≤ a := by
      simpa using Order.succ_le_of_lt (pos_iff_ne_zero.mpr ha)
    simpa only [opow_one] using opow_dvd_opow omega0 hle
  exact (strictClosure_orderType_eq_of_two_mul hs hz hzn habsorb).trans htype

private theorem mem_cantorBendixson_top_Iio_iff {T : Ordinal.{0}} (i : Iio T)
    (a : Ordinal.{0}) :
    i ∈ ((⊤ : TopologicalSpace.Closeds (Iio T)).cantorBendixson a : Set (Iio T)) ↔
      i.1 ∈ ((⊤ : TopologicalSpace.Closeds Ordinal).cantorBendixson a : Set Ordinal) := by
  let f : Iio T → Ordinal := Subtype.val
  have hf : Topology.IsOpenEmbedding f := isOpen_Iio.isOpenEmbedding_subtypeVal
  have himage := hf.image_cantorBendixson_top_eq a
  constructor
  · intro hi
    have hm : f i ∈ f ''
        ((⊤ : TopologicalSpace.Closeds (Iio T)).cantorBendixson a : Set (Iio T)) :=
      ⟨i, hi, rfl⟩
    exact ((Set.ext_iff.mp himage (f i)).mp hm).1
  · intro hi
    have hm : f i ∈
        ((⊤ : TopologicalSpace.Closeds Ordinal).cantorBendixson a : Set Ordinal) ∩
          range f := ⟨hi, mem_range_self i⟩
    obtain ⟨j, hj, hji⟩ := (Set.ext_iff.mp himage (f i)).mpr hm
    exact hf.injective hji ▸ hj

/-- If a real well-order has order type `ω ^ a` and a strict supremum, that supremum has
Cantor–Bendixson rank `a` in the closure. -/
@[blueprint "lem:cantor-bendixson-rank-of-strict-supremum"
  (phase := "Cantor–Bendixson ranks of supports")
  (title := "Cantor--Bendixson rank at a strict supremum")
  (statement := /--
    Let $S\subseteq\mathbb R$ be well ordered and let $z$ be its least upper
    bound, with $z\notin S$. If $\alpha\ne0$ and
    $\operatorname{ot}(S)=\omega^\alpha$, then
    \[
      \operatorname{rk}_{\mathrm{CB},\mathrm{cl}(S)}(z)=\alpha.
    \]
  -/)
  (proof := /--
  The closure of $S$ is again well ordered. Its increasing enumeration is a
  homeomorphism from an ordinal interval, and the strict initial segment below
  $z$ still has order type $\omega^\alpha$. In an ordinal interval, the
  $\alpha$-th Cantor--Bendixson derivative contains the point indexed by
  $\omega^\alpha$, while the $(\alpha+1)$-st derivative does not. Transport
  these two statements through the homeomorphism to the closure of $S$.
  -/)]
theorem IsPWO.cantorBendixsonRank_closure_eq_of_orderType_eq_opow
    (hs : s.IsPWO) (hz : IsLUB s z) (hzn : z ∉ s) {a : Ordinal} (ha : a ≠ 0)
    (htype : hs.orderType = omega0 ^ a) :
    TopologicalSpace.Closeds.cantorBendixsonRank
      (⟨(_root_.closure s), isClosed_closure⟩ : TopologicalSpace.Closeds ℝ)
      (Set.IsPWO.closure hs) z = a := by
  obtain ⟨y, hy, -, -⟩ := hz.exists_between (sub_lt_self z one_pos)
  have hzc : z ∈ _root_.closure s := hz.mem_closure ⟨y, hy⟩
  let S : TopologicalSpace.Closeds ℝ := ⟨(_root_.closure s), isClosed_closure⟩
  let C : Set ℝ := _root_.closure s
  let hc : C.IsPWO := hs.closure
  letI : WellFoundedLT C := ⟨hc.isWF⟩
  let T : Ordinal := Ordinal.type (· < · : C → C → Prop)
  let i : Iio T :=
    ⟨Ordinal.typein (· < · : C → C → Prop) ⟨z, hzc⟩,
      Ordinal.typein_lt_type _ _⟩
  have hi : i.1 = omega0 ^ a := by
    rw [← strictClosure_orderType_eq_opow hs hz hzn ha htype]
    exact (hc.orderType_inter_Iio_eq_typein hzc).symm
  let e := Set.IsPWO.homeomorphIioType (s := C) isClosed_closure
  have hei : e i = ⟨z, hzc⟩ := by
    apply Subtype.ext
    simp [e, Set.IsPWO.homeomorphIioType, Set.IsPWO.enumRealOrderIso,
      i]
  have hsource :
      i ∈ ((⊤ : TopologicalSpace.Closeds (Iio T)).cantorBendixson a : Set (Iio T)) := by
    rw [mem_cantorBendixson_top_Iio_iff, Ordinal.cantorBendixson_top_eq,
      if_neg ha, hi, Ordinal.mem_positivePrincipalMultiples]
    exact ⟨1, zero_lt_one, by simp⟩
  have hsourceSucc :
      i ∉ ((⊤ : TopologicalSpace.Closeds (Iio T)).cantorBendixson (a + 1) :
        Set (Iio T)) := by
    have hsucc : a + 1 ≠ 0 := (add_pos_of_right zero_lt_one a).ne'
    rw [mem_cantorBendixson_top_Iio_iff, Ordinal.cantorBendixson_top_eq,
      if_neg hsucc, hi, Ordinal.mem_positivePrincipalMultiples]
    rintro ⟨q, hq, heq⟩
    have hle : omega0 ^ (a + 1) ≤ omega0 ^ (a + 1) * q :=
      by simpa using mul_le_mul_right (one_le_iff_pos.mpr hq) (omega0 ^ (a + 1))
    have hlt : omega0 ^ a < omega0 ^ (a + 1) :=
      (opow_lt_opow_iff_right one_lt_omega0).mpr (Order.lt_succ a)
    exact (not_le_of_gt hlt) (hle.trans_eq heq)
  have heTop : e '' (Set.univ : Set (Iio T)) = (Set.univ : Set C) := by
    ext x
    simp
  have hsub : ⟨z, hzc⟩ ∈
      ((⊤ : TopologicalSpace.Closeds C).cantorBendixson a : Set C) := by
    rw [← hei]
    exact (e.mem_cantorBendixson_iff ⊤ ⊤ heTop i a).mpr hsource
  have hsubSucc : ⟨z, hzc⟩ ∉
      ((⊤ : TopologicalSpace.Closeds C).cantorBendixson (a + 1) : Set C) := by
    rw [← hei]
    exact fun h ↦ hsourceSucc ((e.mem_cantorBendixson_iff ⊤ ⊤ heTop i (a + 1)).mp h)
  let j : C → ℝ := Subtype.val
  have hj : Topology.IsClosedEmbedding j := isClosed_closure.isClosedEmbedding_subtypeVal
  let J : TopologicalSpace.Closeds ℝ :=
    ⟨j '' ((⊤ : TopologicalSpace.Closeds C) : Set C),
      hj.isClosedMap _ (TopologicalSpace.Closeds.isClosed ⊤)⟩
  have hJS : J = S := by
    apply SetLike.coe_injective
    ext x
    simp [J, S, j, C]
  have hambient : z ∈ (S.cantorBendixson a : Set ℝ) := by
    have hstage := hj.image_cantorBendixson_eq ⊤ a
    have hzJ : z ∈ (J.cantorBendixson a : Set ℝ) := by
      rw [← hstage]
      exact ⟨⟨z, hzc⟩, hsub, rfl⟩
    rwa [hJS] at hzJ
  have hambientSucc : z ∉ (S.cantorBendixson (a + 1) : Set ℝ) := by
    have hstage := hj.image_cantorBendixson_eq ⊤ (a + 1)
    intro hzS
    have hzJ : z ∈ (J.cantorBendixson (a + 1) : Set ℝ) := by
      rwa [hJS]
    rw [← hstage] at hzJ
    obtain ⟨x, hx, hxz⟩ := hzJ
    change x.1 = z at hxz
    have hxeq : x = ⟨z, hzc⟩ := Subtype.ext hxz
    exact hsubSucc (hxeq ▸ hx)
  exact (S.cantorBendixsonRank_eq_iff (Set.IsPWO.closure hs) hzc a).mpr
      ⟨hambient, hambientSucc⟩

end Set
