/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Connected.PathConnected

/-!
# Tube domains: definition and elementary geometry

The tube over a real base consists of complex points whose real parts belong to that base. This
file contains the definition, the real and imaginary coordinate projections, and elementary
facts: tubes over open, convex or preconnected bases are open, convex or preconnected, tubes are
invariant under imaginary translations, and sup-norm balls around a point of a tube lie in the
tube when the corresponding real ball lies in the base.

References: [Scheidemann][Scheidemann2005] §6.1; [Hörmander][Hormander1973] §2.5, Definition
2.5.9.

## Notation

`tubeDomain Ω` is the set of points of `ι → ℂ` whose real parts lie in `Ω`. `rePi`, `imPi`, and
`ofRealPi` are the real-part, imaginary-part, and complexification maps.

## Main results

`isOpen_tubeDomain`, `convex_tubeDomain`, and `isPreconnected_tubeDomain` transport openness,
convexity, and preconnectedness from the base. `tubeDomain_union` and `tubeDomain_inter` commute
with unions and intersections. `ball_subset_tubeDomain` places a sup-norm ball in the tube when
the corresponding real ball lies in the base.

## References

* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Filter Complex
open scoped Topology

namespace SeveralComplexVariables

variable {ι : Type*}

/-- The tube over a real coordinate set; imaginary coordinates are unrestricted. -/
@[expose] def tubeDomain (Ω : Set (ι → ℝ)) : Set (ι → ℂ) :=
  {z | (fun i => (z i).re) ∈ Ω}

/-- The real part of a complex coordinate vector. -/
@[expose] def rePi (z : ι → ℂ) : ι → ℝ := fun i => (z i).re

/-- The imaginary part of a complex coordinate vector. -/
@[expose] def imPi (z : ι → ℂ) : ι → ℝ := fun i => (z i).im

/-- A real coordinate vector as a complex coordinate vector. -/
@[expose] def ofRealPi (x : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ)

/-- Membership in a tube is membership of the real part in the base. -/
theorem mem_tubeDomain {Ω : Set (ι → ℝ)} {z : ι → ℂ} : z ∈ tubeDomain Ω ↔ rePi z ∈ Ω := Iff.rfl

/-- The real part of a real vector is the vector. -/
@[simp] theorem rePi_ofRealPi (x : ι → ℝ) : rePi (ofRealPi x) = x := by
  funext i; simp [rePi, ofRealPi]

/-- A real vector has zero imaginary part. -/
@[simp] theorem imPi_ofRealPi (x : ι → ℝ) : imPi (ofRealPi x) = 0 := by
  funext i; simp [imPi, ofRealPi]

/-- The real part is additive. -/
@[simp] theorem rePi_add (z w : ι → ℂ) : rePi (z + w) = rePi z + rePi w := by
  funext i; simp [rePi]

/-- The real part respects differences. -/
@[simp] theorem rePi_sub (z w : ι → ℂ) : rePi (z - w) = rePi z - rePi w := by
  funext i; simp [rePi]

/-- A purely imaginary vector has zero real part. -/
@[simp] theorem rePi_I_smul_ofRealPi (y : ι → ℝ) : rePi (I • ofRealPi y) = 0 := by
  funext i; simp [rePi, ofRealPi]

/-- The real part commutes with real scalars. -/
@[simp] theorem rePi_real_smul (t : ℝ) (z : ι → ℂ) : rePi (t • z) = t • rePi z := by
  funext i; simp [rePi, Complex.real_smul]

/-- Complexification is additive. -/
theorem ofRealPi_add (x y : ι → ℝ) : ofRealPi (x + y) = ofRealPi x + ofRealPi y := by
  funext i; simp [ofRealPi]

/-- Complexification respects differences. -/
theorem ofRealPi_sub (x y : ι → ℝ) : ofRealPi (x - y) = ofRealPi x - ofRealPi y := by
  funext i; simp [ofRealPi]

/-- Complexification commutes with real scalars. -/
theorem ofRealPi_smul (t : ℝ) (x : ι → ℝ) : ofRealPi (t • x) = t • ofRealPi x := by
  funext i; simp [ofRealPi, Complex.real_smul]

/-- The complexification of zero is zero. -/
@[simp] theorem ofRealPi_zero : ofRealPi (0 : ι → ℝ) = 0 := by
  funext i; simp [ofRealPi]

/-- Real and imaginary parts recover a complex coordinate vector. -/
theorem ofRealPi_rePi_add_I_smul_ofRealPi_imPi (z : ι → ℂ) :
    ofRealPi (rePi z) + I • ofRealPi (imPi z) = z := by
  funext i
  simp only [Pi.add_apply, ofRealPi, rePi, imPi, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]
  exact Complex.re_add_im (z i)

/-- A real point belongs to a tube exactly when it belongs to the base. -/
@[simp] theorem ofReal_mem_tubeDomain {Ω : Set (ι → ℝ)} {x : ι → ℝ} :
    (fun i => (x i : ℂ)) ∈ tubeDomain Ω ↔ x ∈ Ω := by simp [tubeDomain]

/-- A real vector lies in a tube exactly when it lies in the base. -/
@[simp] theorem ofRealPi_mem_tubeDomain {Ω : Set (ι → ℝ)} {x : ι → ℝ} :
    ofRealPi x ∈ tubeDomain Ω ↔ x ∈ Ω := ofReal_mem_tubeDomain

/-- Tubes are invariant under imaginary translations. -/
theorem add_I_smul_ofRealPi_mem_tubeDomain {Ω : Set (ι → ℝ)} {z : ι → ℂ} (y : ι → ℝ) :
    z + I • ofRealPi y ∈ tubeDomain Ω ↔ z ∈ tubeDomain Ω := by
  simp [mem_tubeDomain]

/-- Tubes are monotone in their real bases. -/
theorem tubeDomain_mono {Ω Ξ : Set (ι → ℝ)} (h : Ω ⊆ Ξ) : tubeDomain Ω ⊆ tubeDomain Ξ :=
  fun _ hz => h hz

/-- Tubes commute with intersections of bases. -/
theorem tubeDomain_inter (Ω Ξ : Set (ι → ℝ)) :
    tubeDomain (Ω ∩ Ξ) = tubeDomain Ω ∩ tubeDomain Ξ := rfl

/-- Tubes commute with unions of bases. -/
theorem tubeDomain_union (Ω Ξ : Set (ι → ℝ)) :
    tubeDomain (Ω ∪ Ξ) = tubeDomain Ω ∪ tubeDomain Ξ := rfl

/-- Tubes commute with unions of families of bases. -/
theorem tubeDomain_sUnion (S : Set (Set (ι → ℝ))) :
    tubeDomain (⋃₀ S) = ⋃ Ω ∈ S, tubeDomain Ω := by
  ext z; simp [mem_tubeDomain]

/-- The tube over the empty base is empty. -/
@[simp] theorem tubeDomain_empty : tubeDomain (∅ : Set (ι → ℝ)) = ∅ := rfl

/-- The tube over the whole real space is the whole complex space. -/
@[simp] theorem tubeDomain_univ : tubeDomain (univ : Set (ι → ℝ)) = univ := rfl

/-- A nonempty real base has a nonempty tube. -/
theorem nonempty_tubeDomain {Ω : Set (ι → ℝ)} (h : Ω.Nonempty) : (tubeDomain Ω).Nonempty := by
  obtain ⟨x, hx⟩ := h
  exact ⟨fun i => (x i : ℂ), ofReal_mem_tubeDomain.mpr hx⟩

/-- The real-part projection is continuous. -/
@[fun_prop] theorem continuous_rePi : Continuous (rePi : (ι → ℂ) → ι → ℝ) := by
  unfold rePi; fun_prop

/-- The imaginary-part projection is continuous. -/
@[fun_prop] theorem continuous_imPi : Continuous (imPi : (ι → ℂ) → ι → ℝ) := by
  unfold imPi; fun_prop

/-- Complexification is continuous. -/
@[fun_prop] theorem continuous_ofRealPi : Continuous (ofRealPi : (ι → ℝ) → ι → ℂ) := by
  unfold ofRealPi; fun_prop

/-- The tube over an open base is open. -/
theorem isOpen_tubeDomain {Ω : Set (ι → ℝ)} (ho : IsOpen Ω) : IsOpen (tubeDomain Ω) :=
  ho.preimage (by fun_prop)

/-- Real convexity of the base implies real convexity of its tube. -/
theorem convex_tubeDomain {Ω : Set (ι → ℝ)} (hc : Convex ℝ Ω) : Convex ℝ (tubeDomain Ω) := by
  intro x hx y hy a b ha hb hab
  have h := hc hx hy ha hb hab
  simpa [tubeDomain, Pi.smul_def, Pi.add_def, smul_eq_mul] using h

/-- Every tube is contained in the tube over the convex hull of its base. -/
theorem tubeDomain_subset_convexHull_base (Ω : Set (ι → ℝ)) :
    tubeDomain Ω ⊆ tubeDomain (convexHull ℝ Ω) := tubeDomain_mono (_root_.subset_convexHull ℝ Ω)

/-- A tube is the image of the product of its base with the imaginary coordinate space. -/
theorem tubeDomain_eq_image (Ω : Set (ι → ℝ)) :
    tubeDomain Ω = (fun p : (ι → ℝ) × (ι → ℝ) => ofRealPi p.1 + I • ofRealPi p.2) ''
      (Ω ×ˢ univ) := by
  ext z
  constructor
  · intro hz
    refine ⟨(rePi z, imPi z), ⟨hz, mem_univ _⟩, ?_⟩
    exact ofRealPi_rePi_add_I_smul_ofRealPi_imPi z
  · rintro ⟨⟨x, y⟩, ⟨hx, -⟩, rfl⟩
    simpa [mem_tubeDomain] using hx

/-- The tube over a preconnected base is preconnected. -/
theorem isPreconnected_tubeDomain {Ω : Set (ι → ℝ)} (h : IsPreconnected Ω) :
    IsPreconnected (tubeDomain Ω) := by
  rw [tubeDomain_eq_image]
  exact (h.prod isPreconnected_univ).image _ (by fun_prop : Continuous fun p : (ι → ℝ) × (ι → ℝ) =>
    ofRealPi p.1 + I • ofRealPi p.2).continuousOn

section Norms

variable [Fintype ι]

/-- Complexification preserves the supremum norm. -/
theorem norm_ofRealPi (x : ι → ℝ) : ‖ofRealPi x‖ = ‖x‖ := by
  simp [ofRealPi, Pi.norm_def]

/-- The real part does not increase the supremum norm. -/
theorem norm_rePi_le (z : ι → ℂ) : ‖rePi z‖ ≤ ‖z‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  exact (Complex.abs_re_le_norm (z i)).trans (norm_le_pi_norm z i)

/-- A sup-norm ball around a point of a tube lies in the tube when the real ball around its real
part lies in the base. -/
theorem ball_subset_tubeDomain {Ω : Set (ι → ℝ)} {z : ι → ℂ} {r : ℝ}
    (h : Metric.ball (rePi z) r ⊆ Ω) : Metric.ball z r ⊆ tubeDomain Ω := by
  intro w hw
  apply h
  rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
  show ‖rePi w - rePi z‖ < r
  rw [← rePi_sub]
  exact (norm_rePi_le _).trans_lt hw

end Norms

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
