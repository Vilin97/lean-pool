/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Topology

/-!
# Reinhardt sets

`IsReinhardt` expresses invariance under independent rotations of the complex coordinates.
`IsCompleteReinhardt` additionally permits independent shrinking of their moduli. Both are
properties of sets: openness, connectedness and nonemptiness are separate hypotheses.
Completeness here is unrelated to metric completeness. A nonempty complete Reinhardt set
contains the origin and is path connected, without an openness assumption.

`logarithmicImage` is the inverse image of a set under coordinatewise real exponentiation,
viewed in complex coordinates. `IsLogarithmicallyConvex` asks for this real set to be convex.
For complete Reinhardt sets, logarithmic image commutes with taking the interior; both
completeness and logarithmic convexity are preserved by taking interiors.

The centre is the origin in the specified coordinates. To express the property about `a`, apply
the predicate to `{z | a + z ∈ U}`. Arbitrary complex linear changes of coordinates need not
preserve either property. These definitions and results also allow empty coordinate types; no
finiteness assumption is needed for the basic geometry in the product topology.

References: [Korevaar–Wiegerinck][KorevaarWiegerinck2017], Definitions 2.3.2 and 2.3.4;
[Lebl][Lebl2026], Section 1.2; [Boas][Boas2013] (2013), Sections 2.1--2.2. Polydisc examples are
provided in `SeveralComplexVariables.Polydisc`.

## Main definitions

* `IsReinhardt`: A set is Reinhardt if membership is preserved by independent coordinate rotations.
* `IsCompleteReinhardt`: A set is complete Reinhardt if membership is preserved by decreasing
  coordinate moduli.
* `logarithmicImage`: The logarithmic image uses the positive real slice, avoiding logarithms at
  zero.
* `IsLogarithmicallyConvex`: Logarithmic convexity means convexity of the logarithmic image.

## Main results

* `IsCompleteReinhardt.isReinhardt`: Every complete Reinhardt set is Reinhardt.
* `IsCompleteReinhardt.isPathConnected`: Every nonempty complete Reinhardt set is path connected in
  the product topology.
* `IsCompleteReinhardt.interior`: The interior of a complete Reinhardt set is complete Reinhardt.
* `IsCompleteReinhardt.logarithmicImage_interior`: For complete Reinhardt sets, logarithmic image
  commutes with taking the interior.
* `IsLogarithmicallyConvex.interior`: The interior of a complete logarithmically convex Reinhardt
  set is logarithmically convex.
* `isOpen_logarithmicImage`: The logarithmic image of an open set is open.

## References

* [H. P. Boas, *Lecture Notes on Several Complex Variables*][Boas2013]
* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
* [J. Lebl, *Tasty Bits of Several Complex Variables: A Whirlwind Tour of the Subject*][Lebl2026]
-/

public noncomputable section

open Filter Set
open scoped Topology

namespace SeveralComplexVariables

variable {ι : Type*} {U V : Set (ι → ℂ)}

/-- A set is Reinhardt if membership is preserved by independent coordinate rotations. The centre is
zero; openness, connectedness and nonemptiness are not required. -/
@[expose] def IsReinhardt (U : Set (ι → ℂ)) : Prop :=
  ∀ ⦃z⦄, z ∈ U → ∀ ⦃w⦄, (∀ i, ‖w i‖ = ‖z i‖) → w ∈ U

/-- A set is complete Reinhardt if membership is preserved by decreasing coordinate moduli. This
includes rotations and allows zero coordinates; no topological hypotheses are imposed. -/
@[expose] def IsCompleteReinhardt (U : Set (ι → ℂ)) : Prop :=
  ∀ ⦃z⦄, z ∈ U → ∀ ⦃w⦄, (∀ i, ‖w i‖ ≤ ‖z i‖) → w ∈ U

/-- The empty set is Reinhardt. -/
@[simp] theorem isReinhardt_empty : IsReinhardt (∅ : Set (ι → ℂ)) :=
  fun _ hz => hz.elim

/-- The whole coordinate space is Reinhardt. -/
@[simp] theorem isReinhardt_univ : IsReinhardt (univ : Set (ι → ℂ)) :=
  fun _ _ _ _ => mem_univ _

/-- The empty set is complete Reinhardt. -/
@[simp] theorem isCompleteReinhardt_empty : IsCompleteReinhardt (∅ : Set (ι → ℂ)) :=
  fun _ hz => hz.elim

/-- The whole coordinate space is complete Reinhardt. -/
@[simp] theorem isCompleteReinhardt_univ : IsCompleteReinhardt (univ : Set (ι → ℂ)) :=
  fun _ _ _ _ => mem_univ _

/-- Every complete Reinhardt set is Reinhardt. -/
theorem IsCompleteReinhardt.isReinhardt (hU : IsCompleteReinhardt U) : IsReinhardt U :=
  fun _ hz _ hw => hU hz (fun i => (hw i).le)

/-- With no coordinates, every set is complete Reinhardt. -/
theorem isCompleteReinhardt_of_isEmpty [IsEmpty ι] (U : Set (ι → ℂ)) :
    IsCompleteReinhardt U := by
  intro z hz w _
  simpa only [Subsingleton.elim w z] using hz

/-- Intersections preserve Reinhardt symmetry. -/
theorem IsReinhardt.inter (hU : IsReinhardt U) (hV : IsReinhardt V) :
    IsReinhardt (U ∩ V) :=
  fun _ hz _ hw => ⟨hU hz.1 hw, hV hz.2 hw⟩

/-- Unions preserve Reinhardt symmetry, without any connectedness requirement. -/
theorem IsReinhardt.union (hU : IsReinhardt U) (hV : IsReinhardt V) :
    IsReinhardt (U ∪ V) :=
  fun _ hz _ hw => hz.elim (fun h => Or.inl (hU h hw)) (fun h => Or.inr (hV h hw))

/-- Arbitrary unions of Reinhardt sets are Reinhardt. -/
theorem isReinhardt_iUnion {κ : Sort*} {S : κ → Set (ι → ℂ)}
    (hS : ∀ k, IsReinhardt (S k)) : IsReinhardt (⋃ k, S k) := by
  intro z hz w hw
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨k, hS k hk hw⟩

/-- Intersections preserve the complete Reinhardt property. -/
theorem IsCompleteReinhardt.inter (hU : IsCompleteReinhardt U)
    (hV : IsCompleteReinhardt V) : IsCompleteReinhardt (U ∩ V) :=
  fun _ hz _ hw => ⟨hU hz.1 hw, hV hz.2 hw⟩

/-- Unions preserve the complete Reinhardt property. -/
theorem IsCompleteReinhardt.union (hU : IsCompleteReinhardt U)
    (hV : IsCompleteReinhardt V) : IsCompleteReinhardt (U ∪ V) :=
  fun _ hz _ hw => hz.elim (fun h => Or.inl (hU h hw)) (fun h => Or.inr (hV h hw))

/-- Arbitrary unions of complete Reinhardt sets are complete Reinhardt. -/
theorem isCompleteReinhardt_iUnion {κ : Sort*} {S : κ → Set (ι → ℂ)}
    (hS : ∀ k, IsCompleteReinhardt (S k)) : IsCompleteReinhardt (⋃ k, S k) := by
  intro z hz w hw
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨k, hS k hk hw⟩

/-- Multiplying each coordinate by a complex number of modulus one preserves a Reinhardt set. -/
theorem IsReinhardt.mul_mem (hU : IsReinhardt U) {z : ι → ℂ} (hz : z ∈ U)
    {a : ι → ℂ} (ha : ∀ i, ‖a i‖ = 1) : (fun i => a i * z i) ∈ U :=
  hU hz (fun i => by simp [ha i])

/-- Independent complex contractions preserve a complete Reinhardt set. -/
theorem IsCompleteReinhardt.mul_mem (hU : IsCompleteReinhardt U) {z : ι → ℂ}
    (hz : z ∈ U) {a : ι → ℂ} (ha : ∀ i, ‖a i‖ ≤ 1) : (fun i => a i * z i) ∈ U := by
  apply hU hz
  intro i
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha i)

/-- A nonempty complete Reinhardt set contains the origin. -/
theorem IsCompleteReinhardt.zero_mem (hU : IsCompleteReinhardt U) (hne : U.Nonempty) :
    0 ∈ U := by
  obtain ⟨z, hz⟩ := hne
  exact hU hz (fun i => by simp)

/-- A complete Reinhardt set is star-convex about the origin, including when it is empty. -/
theorem IsCompleteReinhardt.starConvex (hU : IsCompleteReinhardt U) :
    StarConvex ℝ (0 : ι → ℂ) U := by
  intro z hz a b ha hb hab
  simp only [smul_zero, zero_add]
  apply hU hz
  intro i
  change ‖b • z i‖ ≤ ‖z i‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

/-- Every nonempty complete Reinhardt set is path connected in the product topology. -/
theorem IsCompleteReinhardt.isPathConnected (hU : IsCompleteReinhardt U)
    (hne : U.Nonempty) : IsPathConnected U :=
  hU.starConvex.isPathConnected (hU.zero_mem hne)

/-- Every nonempty complete Reinhardt set is connected. -/
theorem IsCompleteReinhardt.isConnected (hU : IsCompleteReinhardt U)
    (hne : U.Nonempty) : IsConnected U :=
  (hU.isPathConnected hne).isConnected

/-- Complete Reinhardt sets are preconnected; this statement also covers the empty set. -/
theorem IsCompleteReinhardt.isPreconnected (hU : IsCompleteReinhardt U) :
    IsPreconnected U := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · exact isPreconnected_empty
  · exact (hU.isConnected hne).isPreconnected

/-- The logarithmic image uses the positive real slice, avoiding logarithms at zero. For a Reinhardt
set this is its usual image under coordinatewise log modulus. -/
@[expose] def logarithmicImage (U : Set (ι → ℂ)) : Set (ι → ℝ) :=
  {x | (fun i => (Real.exp (x i) : ℂ)) ∈ U}

/-- Logarithmic convexity means convexity of the logarithmic image. Reinhardt symmetry,
completeness, openness and nonemptiness remain separate hypotheses. -/
@[expose] def IsLogarithmicallyConvex (U : Set (ι → ℂ)) : Prop :=
  Convex ℝ (logarithmicImage U)

/-- Membership of the logarithmic image is membership of the exponential coordinate vector. -/
@[simp] theorem mem_logarithmicImage {x : ι → ℝ} :
    x ∈ logarithmicImage U ↔ (fun i => (Real.exp (x i) : ℂ)) ∈ U := Iff.rfl

/-- The empty set is logarithmically convex. -/
@[simp] theorem isLogarithmicallyConvex_empty :
    IsLogarithmicallyConvex (∅ : Set (ι → ℂ)) := convex_empty

/-- The whole coordinate space is logarithmically convex. -/
@[simp] theorem isLogarithmicallyConvex_univ :
    IsLogarithmicallyConvex (univ : Set (ι → ℂ)) := convex_univ

/-- Intersections preserve logarithmic convexity. -/
theorem IsLogarithmicallyConvex.inter (hU : IsLogarithmicallyConvex U)
    (hV : IsLogarithmicallyConvex V) : IsLogarithmicallyConvex (U ∩ V) :=
  Convex.inter hU hV

/-- The logarithmic image of an open set is open. -/
theorem isOpen_logarithmicImage (hU : IsOpen U) : IsOpen (logarithmicImage U) :=
  hU.preimage (continuous_pi fun i => Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_apply i)))

/-- The interior of a complete Reinhardt set is complete Reinhardt. The proof also handles points on
coordinate hyperplanes, where coordinate contractions need not be open maps. -/
theorem IsCompleteReinhardt.interior (hU : IsCompleteReinhardt U) :
    IsCompleteReinhardt (_root_.interior U) := by
  classical
  intro z hz w hw
  let f : (ι → ℂ) → (ι → ℂ) := fun v i =>
    if z i = 0 then v i else (max ‖z i‖ ‖v i‖ / ‖z i‖) • z i
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    dsimp [f]
    split_ifs
    · exact continuous_apply i
    · exact ((continuous_const.max (continuous_apply i).norm).div_const _).smul continuous_const
  have hfw : f w = z := by
    ext i
    dsimp [f]
    split_ifs with hi
    · have hwi : w i = 0 := norm_eq_zero.mp (le_antisymm
        (by simpa [hi] using hw i) (norm_nonneg _))
      simp [hi, hwi]
    · simp [max_eq_left (hw i), norm_ne_zero_iff.mpr hi]
  have hnorm (v : ι → ℂ) (i : ι) : ‖v i‖ ≤ ‖f v i‖ := by
    dsimp [f]
    split_ifs with hi
    · exact le_rfl
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (le_max_of_le_left (norm_nonneg _)) (norm_nonneg _)),
        div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hi)]
      exact le_max_right _ _
  apply mem_interior_iff_mem_nhds.mpr
  have hn : ∀ᶠ v in 𝓝 w, f v ∈ _root_.interior U :=
    (hf.continuousAt : ContinuousAt f w) (by simpa [hfw] using isOpen_interior.mem_nhds hz)
  filter_upwards [hn] with v hv
  exact hU (interior_subset hv) (hnorm v)

/-- For complete Reinhardt sets, logarithmic image commutes with taking the interior. -/
theorem IsCompleteReinhardt.logarithmicImage_interior (hU : IsCompleteReinhardt U) :
    logarithmicImage (_root_.interior U) = _root_.interior (logarithmicImage U) := by
  apply Subset.antisymm
  · exact (isOpen_logarithmicImage isOpen_interior).subset_interior_iff.mpr
      (fun x hx => (interior_subset hx : (fun i => (Real.exp (x i) : ℂ)) ∈ U))
  · intro x hx
    change (fun i => (Real.exp (x i) : ℂ)) ∈ _root_.interior U
    let z : ι → ℂ := fun i => Real.exp (x i)
    have hc : ContinuousAt (fun w : ι → ℂ => fun i => Real.log ‖w i‖) z := by
      apply continuousAt_pi.mpr
      intro i
      apply (continuousAt_apply i z).norm.log
      simp [z, Real.exp_ne_zero]
    have heq : (fun i => Real.log ‖z i‖) = x := by
      ext i
      simp [z]
    have hn : ∀ᶠ w in 𝓝 z, (fun i => Real.log ‖w i‖) ∈ logarithmicImage U :=
      hc (by simpa [heq] using mem_interior_iff_mem_nhds.mp hx)
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hn] with w hw
    apply hU hw
    intro i
    by_cases hi : ‖w i‖ = 0
    · simp [hi]
    · simp [Real.exp_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hi))]

/-- The interior of a complete logarithmically convex Reinhardt set is logarithmically convex. -/
theorem IsLogarithmicallyConvex.interior (hU : IsLogarithmicallyConvex U)
    (hc : IsCompleteReinhardt U) : IsLogarithmicallyConvex (_root_.interior U) := by
  unfold IsLogarithmicallyConvex
  rw [hc.logarithmicImage_interior]
  exact (show Convex ℝ (logarithmicImage U) from hU).interior

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
