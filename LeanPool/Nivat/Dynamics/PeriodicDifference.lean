/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Dynamics.OrbitClosure
public import LeanPool.Nivat.Core.Lattice
public import LeanPool.Nivat.Core.BoundedDifferences
public import LeanPool.Nivat.Algebra.Action
public import LeanPool.Nivat.Algebra.ProductDifferences
public import Mathlib.Tactic.Ring

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# A period tangent to a vanishing half-plane

This module proves Proposition 3.5 (`prop:tangent-period`) and Corollary 3.6
(`cor:periodic-difference`) of `paper/nivat.tex`. Transverse differences are
injective on configurations vanishing below some normal threshold. Cancelling
them from a product annihilator leaves only tangent directions; a common
multiple and Lemma 3.4 then give a period.

The main results are `exists_tangent_period_of_nonzero_annihilator` and
`periodic_difference_of_nonzero_annihilator`. The latter combines the tangent
period with Lemma 3.1 and the pattern inheritance of Section 1.1.
-/

@[expose] public section

namespace Nivat.Dynamics

open Nivat.Algebra

/-- The additive normal coordinate `ν · z` used in Proposition 3.5 (`prop:tangent-period`). -/
def normalHom (ν : ℝ × ℝ) : Lattice →+ ℝ where
  toFun z := ν.1 * (z.1 : ℝ) + ν.2 * (z.2 : ℝ)
  map_zero' := by simp
  map_add' z u := by dsimp; push_cast; ring

/-- The vanishing space `V_ν` in Proposition 3.5 (`prop:tangent-period`): a configuration vanishes
below some normal threshold, which may depend on the configuration. -/
def ZeroBelow (ν : ℝ × ℝ) (d : Configuration ℚ) : Prop :=
  ∃ B : ℝ, ∀ z : Lattice, normalHom ν z < B → d z = 0

/-- The vanishing space `V_ν` is preserved by every shift after adjusting its threshold, as
required for transverse cancellation in Proposition 3.5 (`prop:tangent-period`). -/
theorem ZeroBelow.shift {ν : ℝ × ℝ} {d : Configuration ℚ} (hd : ZeroBelow ν d)
    (h : Lattice) : ZeroBelow ν (shift h d) := by
  obtain ⟨B, hB⟩ := hd
  refine ⟨B - normalHom ν h, ?_⟩
  intro z hz
  exact hB (z + h) (by rw [map_add]; linarith)

/-- The vanishing space `V_ν` is closed under subtraction, using the smaller of the two thresholds
in Proposition 3.5 (`prop:tangent-period`). -/
theorem ZeroBelow.sub {ν : ℝ × ℝ} {d e : Configuration ℚ}
    (hd : ZeroBelow ν d) (he : ZeroBelow ν e) : ZeroBelow ν (d - e) := by
  obtain ⟨B, hB⟩ := hd
  obtain ⟨C, hC⟩ := he
  refine ⟨min B C, ?_⟩
  intro z hz
  change d z - e z = 0
  rw [hB z (hz.trans_le (min_le_left _ _)), hC z (hz.trans_le (min_le_right _ _)), sub_self]

/-- Every directional difference preserves the vanishing space `V_ν` of Proposition 3.5
(`prop:tangent-period`). -/
theorem ZeroBelow.difference {ν : ℝ × ℝ} {d : Configuration ℚ} (hd : ZeroBelow ν d)
    (h : Lattice) : ZeroBelow ν (difference h d) := (hd.shift h).sub hd

/-- A periodic configuration in `V_ν` is zero when its period has positive normal coordinate: each
orbit reaches the vanishing half-plane. This is the injectivity argument of Proposition 3.5
(`prop:tangent-period`). -/
theorem zero_of_zeroBelow_periodic_pos {ν : ℝ × ℝ} {d : Configuration ℚ}
    (hd : ZeroBelow ν d) (h : Lattice) (hpos : 0 < normalHom ν h)
    (hp : IsPeriod d h) : d = 0 := by
  obtain ⟨B, hB⟩ := hd
  funext z
  obtain ⟨n, hn⟩ := exists_int_gt ((normalHom ν z - B) / normalHom ν h)
  have hineq : normalHom ν z - B < (n : ℝ) * normalHom ν h :=
    (div_lt_iff₀ hpos).mp hn
  have hzero : d (z + (-n) • h) = 0 := by
    apply hB
    rw [map_add, map_zsmul]
    simp only [zsmul_eq_mul, Int.cast_neg]
    linarith
  exact ((hp.zsmul (-n)) z).symm.trans hzero

/-- A transverse difference has trivial kernel on `V_ν`, for either sign of its normal coordinate.
This is the cancellation principle of Proposition 3.5 (`prop:tangent-period`). -/
theorem zero_of_zeroBelow_difference {ν : ℝ × ℝ} {d : Configuration ℚ}
    (hd : ZeroBelow ν d) (h : Lattice) (htrans : normalHom ν h ≠ 0)
    (hdiff : difference h d = 0) : d = 0 := by
  have hp := (difference_eq_zero_iff h d).mp hdiff
  rcases lt_or_gt_of_ne htrans with hneg | hpos
  · apply zero_of_zeroBelow_periodic_pos hd (-h) _ hp.neg
    simpa only [map_neg, neg_pos] using hneg
  · exact zero_of_zeroBelow_periodic_pos hd h hpos hp

/-- Finite-pattern language inclusion transports each Laurent annihilator, by evaluating its
translated finite support. This is equation `eq:inheritance` in Section 1.1, used in Corollary
3.6 (`cor:periodic-difference`). -/
theorem act_eq_zero_of_origin_language (c x : Configuration ℚ)
    (hx : ∀ D : Finset Lattice, patternAt x D 0 ∈ patterns c D)
    (f : Laurent) (hf : act f c = 0) : act f x = 0 := by
  classical
  funext z
  let D := f.coeff.support.image (fun h : Lattice => z + h)
  obtain ⟨u, hu⟩ := hx D
  have heq (h : Lattice) (hh : h ∈ f.coeff.support) : x (z + h) = c (z + h + u) := by
    have hp := congrFun hu (⟨z + h, Finset.mem_image.mpr ⟨h, hh, rfl⟩⟩ : D)
    simpa only [patternAt, add_zero] using hp.symm
  have hv := congrFun hf (z + u)
  rw [act_apply] at hv ⊢
  change f.coeff.sum (fun h r => r * x (z + h)) = 0
  calc
    _ = f.coeff.sum (fun h r => r * c (z + u + h)) := by
      apply Finset.sum_congr rfl
      intro h hh
      dsimp only
      rw [heq h hh, add_right_comm z h u]
    _ = 0 := hv

/-- The Laurent product of directional difference factors appearing in Proposition 3.5
(`prop:tangent-period`), including any repeated directions. -/
noncomputable def differenceProduct (hs : List Lattice) : Laurent :=
  (hs.map (fun h => monomial h - 1)).prod

/-- The empty product of difference factors is the identity, so cancelling every factor forces the
configuration to vanish in Proposition 3.5 (`prop:tangent-period`). -/
@[simp] theorem differenceProduct_nil : differenceProduct [] = 1 := rfl

/-- Prepending a direction multiplies its difference factor into the product used in Proposition
3.5 (`prop:tangent-period`). -/
@[simp] theorem differenceProduct_cons (h : Lattice) (hs : List Lattice) :
    differenceProduct (h :: hs) = (monomial h - 1) * differenceProduct hs := rfl

/-- The action of a product beginning with a direction is that directional difference of the
remaining action, as used in Proposition 3.5 (`prop:tangent-period`). -/
theorem act_differenceProduct_cons (h : Lattice) (hs : List Lattice)
    (d : Configuration ℚ) :
    act (differenceProduct (h :: hs)) d = difference h (act (differenceProduct hs) d) := by
  rw [differenceProduct_cons, act_mul, act_difference]

/-- A finite product of difference operators preserves `V_ν`, which justifies iterated
cancellation in Proposition 3.5 (`prop:tangent-period`). -/
theorem ZeroBelow.act_differenceProduct {ν : ℝ × ℝ} {d : Configuration ℚ}
    (hd : ZeroBelow ν d) (hs : List Lattice) : ZeroBelow ν (act (differenceProduct hs) d) := by
  induction hs with
  | nil => simpa using hd
  | cons h hs ih => rw [act_differenceProduct_cons]; exact ih.difference h

/-- Every transverse factor can be cancelled from an annihilating product on `V_ν`, retaining
tangential factors with their multiplicities. This is the first step of Proposition 3.5
(`prop:tangent-period`). -/
theorem cancel_transverse_factors {ν : ℝ × ℝ} (hs : List Lattice)
    (d : Configuration ℚ) (hd : ZeroBelow ν d)
    (hprod : act (differenceProduct hs) d = 0) :
    act (differenceProduct (hs.filter (fun h => normalHom ν h = 0))) d = 0 := by
  classical
  induction hs generalizing d with
  | nil => simpa using hprod
  | cons h hs ih =>
    rw [act_differenceProduct_cons] at hprod
    by_cases htangent : normalHom ν h = 0
    · simp only [List.filter_cons, htangent, decide_true, ite_true, act_differenceProduct_cons]
      rw [← act_difference_comm]
      apply ih (difference h d) (hd.difference h)
      rwa [act_difference_comm]
    · simp only [List.filter_cons, htangent, decide_false]
      exact ih d hd (zero_of_zeroBelow_difference (hd.act_differenceProduct hs) h htangent hprod)

/-- The normal coordinate in an integer lattice basis is the linear combination of its two basis
values, as used for coordinate normalization in Proposition 3.5 (`prop:tangent-period`). -/
theorem normal_in_basis (ν : ℝ × ℝ) (e : Lattice ≃+ Lattice) (z : Lattice) :
    normalHom ν (e z) = (z.1 : ℝ) * normalHom ν (e (1, 0)) +
      (z.2 : ℝ) * normalHom ν (e (0, 1)) := by
  rw [lattice_addEquiv_coordinates, map_add, map_zsmul, map_zsmul]
  simp only [zsmul_eq_mul]

/-- A tangential nonzero lattice vector and a nonzero normal admit an integer lattice basis whose
first vector is tangent and whose second vector has positive normal coordinate. This is the
basis choice in Proposition 3.5 (`prop:tangent-period`). -/
theorem exists_oriented_tangent_basis (ν : ℝ × ℝ) (hν : ν ≠ 0)
    (h : Lattice) (hh : h ≠ 0) (htangent : normalHom ν h = 0) :
    ∃ e : Lattice ≃+ Lattice, normalHom ν (e (1, 0)) = 0 ∧
      0 < normalHom ν (e (0, 1)) := by
  obtain ⟨q, hq, e, he⟩ := exists_lattice_basis_for_nonzero h hh
  have hcol₁ : normalHom ν (e (1, 0)) = 0 := by
    have hnormal : normalHom ν (e ((q : ℤ), 0)) = 0 := he ▸ htangent
    rw [normal_in_basis] at hnormal
    simp only [Int.cast_natCast, Int.cast_zero, zero_mul, add_zero] at hnormal
    exact (mul_eq_zero.mp hnormal).resolve_left (by exact_mod_cast (Nat.ne_of_gt hq))
  have hcol₂ : normalHom ν (e (0, 1)) ≠ 0 := by
    intro hz
    have hall (z : Lattice) : normalHom ν z = 0 := by
      have h := normal_in_basis ν e (e.symm z)
      simpa only [e.apply_symm_apply, hcol₁, hz, mul_zero, add_zero] using h
    have hν₁ : ν.1 = 0 := by simpa [normalHom] using hall (1, 0)
    have hν₂ : ν.2 = 0 := by simpa [normalHom] using hall (0, 1)
    exact hν (Prod.ext hν₁ hν₂)
  rcases lt_or_gt_of_ne hcol₂ with hneg | hpos
  · let flip : Lattice ≃+ Lattice :=
      AddEquiv.prodCongr (AddEquiv.refl ℤ) (AddEquiv.neg ℤ)
    refine ⟨flip.trans e, ?_, ?_⟩
    · exact hcol₁
    · change 0 < normalHom ν (e (0, -1))
      rw [normal_in_basis]
      simpa only [Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul, zero_add,
        neg_one_mul, neg_pos] using hneg
  · exact ⟨e, hcol₁, hpos⟩

/-- Tangential lattice vectors have zero transverse coordinate in an oriented tangent basis, as
used in Proposition 3.5 (`prop:tangent-period`). -/
theorem tangent_coordinate_zero (ν : ℝ × ℝ) (e : Lattice ≃+ Lattice)
    (hcol₁ : normalHom ν (e (1, 0)) = 0) (hcol₂ : 0 < normalHom ν (e (0, 1)))
    (h : Lattice) (htangent : normalHom ν h = 0) : (e.symm h).2 = 0 := by
  have hnormal := normal_in_basis ν e (e.symm h)
  rw [e.apply_symm_apply, htangent, hcol₁, mul_zero, zero_add] at hnormal
  have hz : ((e.symm h).2 : ℝ) = 0 :=
    (mul_eq_zero.mp hnormal.symm).resolve_right (ne_of_gt hcol₂)
  exact_mod_cast hz

/-- An annihilating product of directional differences implies a repeated difference in any common
multiple of those directions. This is the operator-divisibility step of Proposition 3.5
(`prop:tangent-period`). -/
theorem iterate_difference_eq_zero_of_common_multiple (hs : List Lattice) (H : Lattice)
    (hcommon : ∀ h ∈ hs, ∃ k : ℤ, H = k • h) (d : Configuration ℚ)
    (hprod : act (differenceProduct hs) d = 0) :
    (difference H)^[hs.length] d = 0 := by
  induction hs generalizing d with
  | nil => simpa using hprod
  | cons h hs ih =>
    have htail : act (differenceProduct hs) (difference H d) = 0 := by
      rw [act_difference_comm]
      apply (difference_eq_zero_iff H _).mpr
      obtain ⟨k, hk⟩ := hcommon h (by simp)
      rw [hk]
      apply IsPeriod.zsmul
      apply (difference_eq_zero_iff h _).mp
      simpa only [act_differenceProduct_cons] using hprod
    have hpow := ih (fun v hv => hcommon v (by simp [hv])) (difference H d) htail
    simpa only [List.length_cons, Function.iterate_succ_apply] using hpow

/-- Finitely many nonzero integer directions on a basis line have a common nonzero integer
multiple, obtained from the product of their first coordinates in Proposition 3.5
(`prop:tangent-period`). -/
theorem exists_common_multiple_on_basis_line (e : Lattice ≃+ Lattice) (hs : List Lattice)
    (hnonzero : ∀ h ∈ hs, h ≠ 0) (hline : ∀ h ∈ hs, (e.symm h).2 = 0) :
    ∃ K : ℤ, K ≠ 0 ∧ ∀ h ∈ hs, ∃ k : ℤ, e (K, 0) = k • h := by
  let coord : Lattice → ℤ := fun h => (e.symm h).1
  have hcoord : ∀ h ∈ hs, coord h ≠ 0 := by
    intro h hh hz
    have hezero : e.symm h = 0 := Prod.ext hz (hline h hh)
    apply hnonzero h hh
    have heq := congrArg e hezero
    simpa only [e.apply_symm_apply, map_zero] using heq
  let K := (hs.map coord).prod
  have hK : K ≠ 0 := by
    dsimp [K]
    induction hs with
    | nil => simp
    | cons h hs ih =>
      simp only [List.map_cons, List.prod_cons]
      apply mul_ne_zero (hcoord h (by simp))
      exact ih (fun v hv => hnonzero v (by simp [hv]))
        (fun v hv => hline v (by simp [hv])) (fun v hv => hcoord v (by simp [hv]))
  refine ⟨K, hK, ?_⟩
  intro h hh
  have hdiv : coord h ∣ K := List.dvd_prod (List.mem_map.mpr ⟨h, hh, rfl⟩)
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨k, ?_⟩
  calc
    e (K, 0) = e (k • e.symm h) := by
      congr 1
      apply Prod.ext
      · change K = k * (e.symm h).1
        simpa only [coord, mul_comm] using hk
      · change 0 = k * (e.symm h).2
        rw [hline h hh, mul_zero]
    _ = k • h := by rw [map_zsmul, e.apply_symm_apply]

/-- A finite-range rational configuration annihilated by a nonempty product of tangential
differences has a positive period on that basis line. This is the final use of Lemma 3.4
(`lem:repeated`) in Proposition 3.5 (`prop:tangent-period`). -/
theorem periodic_of_tangential_product (e : Lattice ≃+ Lattice) (hs : List Lattice)
    (hne : hs ≠ []) (hnonzero : ∀ h ∈ hs, h ≠ 0)
    (hline : ∀ h ∈ hs, (e.symm h).2 = 0) (d : Configuration ℚ) (hd : FiniteRange d)
    (hprod : act (differenceProduct hs) d = 0) :
    ∃ q : ℕ, 0 < q ∧ IsPeriod d (e ((q : ℤ), 0)) := by
  obtain ⟨K, hK, hcommon⟩ := exists_common_multiple_on_basis_line e hs hnonzero hline
  have hpower := iterate_difference_eq_zero_of_common_multiple hs (e (K, 0)) hcommon d hprod
  have hperiod : IsPeriod d (e (K, 0)) := (difference_eq_zero_iff _ _).mp
    (difference_eq_zero_of_iterate d hd (e (K, 0)) hs.length (List.length_pos_iff.mpr hne) hpower)
  refine ⟨K.natAbs, Int.natAbs_pos.mpr hK, ?_⟩
  rw [Int.natCast_natAbs]
  rcases lt_or_gt_of_ne hK with hneg | hpos
  · rw [abs_of_neg hneg]
    have he : e (-K, 0) = -(e (K, 0)) := by simpa using e.map_neg (K, 0)
    rw [he]
    exact hperiod.neg
  · rwa [abs_of_pos hpos]

/-- Proposition 3.5 (`prop:tangent-period`): a nonzero finite-range rational configuration with a
nonzero annihilator and vanishing on a half-plane has a positive period in a primitive tangent
direction. The returned lattice basis also orients the transverse coordinate toward the
positive half-plane. -/
theorem exists_tangent_period_of_nonzero_annihilator (d : Configuration ℚ)
    (hd : FiniteRange d) (hdne : d ≠ 0) (ν : ℝ × ℝ) (hν : ν ≠ 0)
    (hbelow : ∀ z : Lattice, normalHom ν z < 0 → d z = 0)
    (f : Laurent) (hf : f ≠ 0) (hann : act f d = 0) :
    ∃ e : Lattice ≃+ Lattice, ∃ q : ℕ, 0 < q ∧
      normalHom ν (e (1, 0)) = 0 ∧ 0 < normalHom ν (e (0, 1)) ∧
      IsPeriod d (e ((q : ℤ), 0)) := by
  classical
  obtain ⟨hs, _hhs, hdirs, hprod⟩ :=
    exists_product_differences_of_annihilator hd hdne hf hann
  have hdV : ZeroBelow ν d := ⟨0, hbelow⟩
  let tangents := hs.filter (fun h => normalHom ν h = 0)
  have htprod : act (differenceProduct tangents) d = 0 :=
    cancel_transverse_factors hs d hdV hprod
  have htne : tangents ≠ [] := by
    intro h
    rw [h, differenceProduct_nil, act_one] at htprod
    exact hdne htprod
  have htnonzero : ∀ h ∈ tangents, h ≠ 0 := by
    intro h hh
    exact hdirs h (List.mem_filter.mp hh).1
  have httangent : ∀ h ∈ tangents, normalHom ν h = 0 := by
    intro h hh
    exact of_decide_eq_true (List.mem_filter.mp hh).2
  obtain ⟨h, hh⟩ := List.exists_mem_of_ne_nil tangents htne
  obtain ⟨e, he₁, he₂⟩ := exists_oriented_tangent_basis ν hν h (htnonzero h hh) (httangent h hh)
  have hline : ∀ h ∈ tangents, (e.symm h).2 = 0 := by
    intro h hh
    exact tangent_coordinate_zero ν e he₁ he₂ h (httangent h hh)
  obtain ⟨q, hq, hperiod⟩ := periodic_of_tangential_product e tangents htne htnonzero hline
    d hd htprod
  exact ⟨e, q, hq, he₁, he₂, hperiod⟩

/-- Corollary 3.6 (`cor:periodic-difference`): a nonperiodic finite-range rational configuration
with a nonzero annihilator yields a nonzero periodic difference of two configurations in its
pattern language, vanishing on the negative rows of a primitive lattice basis. -/
theorem periodic_difference_of_nonzero_annihilator (c : Configuration ℚ)
    (hc : FiniteRange c) (hn : ¬ Periodic c) (f : Laurent) (hf : f ≠ 0)
    (hann : act f c = 0) :
    ∃ x y : Configuration ℚ, ∃ e : Lattice ≃+ Lattice, ∃ q : ℕ,
      FiniteRange x ∧ FiniteRange y ∧
      (∀ D : Finset Lattice, patternAt x D 0 ∈ patterns c D) ∧
      (∀ D : Finset Lattice, patternAt y D 0 ∈ patterns c D) ∧
      x - y ≠ 0 ∧ 0 < q ∧ IsPeriod (x - y) (e ((q : ℤ), 0)) ∧
      ∀ b : ℤ, b < 0 → ∀ a : ℤ, (x - y) (e (a, b)) = 0 := by
  obtain ⟨x, y, ν, hxfin, hyfin, hν, hzero, hxlang, hylang, hhalf⟩ :=
    halfPlane_pair_of_finiteRange_not_periodic c hc hn
  have hdne : x - y ≠ 0 := by
    intro h
    exact hzero (sub_eq_zero.mp (congrFun h 0))
  have hdhalf : ∀ z : Lattice, normalHom ν z < 0 → (x - y) z = 0 := by
    intro z hz
    exact sub_eq_zero.mpr (hhalf z hz)
  have hνne : ν ≠ 0 := by
    intro hz
    simp [hz] at hν
  have hdann : act f (x - y) = 0 := by
    rw [act_config_sub, act_eq_zero_of_origin_language c x hxlang f hann,
      act_eq_zero_of_origin_language c y hylang f hann, sub_self]
  obtain ⟨e, q, hq, he₁, he₂, hperiod⟩ :=
    exists_tangent_period_of_nonzero_annihilator (x - y) (hxfin.sub hyfin)
      hdne ν hνne hdhalf f hf hdann
  refine ⟨x, y, e, q, hxfin, hyfin, hxlang, hylang, hdne, hq, hperiod, ?_⟩
  intro b hb a
  apply hdhalf
  rw [normal_in_basis, he₁, mul_zero, zero_add]
  exact mul_neg_of_neg_of_pos (by exact_mod_cast hb) he₂

end Nivat.Dynamics
