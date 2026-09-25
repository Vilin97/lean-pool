/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Kernel All Orders Open

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped Topology
open CKN.Foundation.Parabolic


/-!
# Iterated derivatives on an open subset of space

On an open set the global iterated Fréchet derivative agrees with the derivative
computed within the set, so it only depends on the values of the function there
and inherits differentiability and continuity from `ContDiffOn`.  These are the
local-to-global bridges used by the all-order kernel estimates of
`cor:CZ-harmonic`.
-/

noncomputable section

namespace CKN.Foundation.Heat

/-- Iterated derivatives at a point of an open set only depend on the function there. -/
theorem iteratedFDeriv_eq_of_eqOn_isOpen {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : Vec3 → F} {U : Set Vec3} (hU : IsOpen U) (hfg : Set.EqOn f g U) (n : ℕ)
    {x : Vec3} (hx : x ∈ U) :
    iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  exact (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hU hx).symm.trans
    ((iteratedFDerivWithin_congr hfg hx n).trans
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hU hx))

/-- A function of order `n + 1` on an open set has a differentiable `n`-th derivative there. -/
theorem differentiableAt_iteratedFDeriv_of_isOpen {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Vec3 → F} {U : Set Vec3} (hU : IsOpen U) (n : ℕ)
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f U) {x : Vec3} (hx : x ∈ U) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x := by
  have hdiff : DifferentiableOn ℝ (iteratedFDerivWithin ℝ n f U) U :=
    hf.differentiableOn_iteratedFDerivWithin (m := n)
      (by exact_mod_cast Nat.lt_succ_self n) hU.uniqueDiffOn
  have hdiff' : DifferentiableOn ℝ (iteratedFDeriv ℝ n f) U :=
    hdiff.congr fun y hy => (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hU hy).symm
  exact hdiff'.differentiableAt (hU.mem_nhds hx)

/-- A function of order `n` on an open set has a continuous `n`-th derivative there. -/
theorem continuousOn_iteratedFDeriv_of_isOpen {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Vec3 → F} {U : Set Vec3} (hU : IsOpen U) (n : ℕ)
    (hf : ContDiffOn ℝ (n : ℕ) f U) :
    ContinuousOn (iteratedFDeriv ℝ n f) U := by
  have hcont : ContinuousOn (iteratedFDerivWithin ℝ n f U) U :=
    hf.continuousOn_iteratedFDerivWithin (m := n) le_rfl hU.uniqueDiffOn
  exact hcont.congr (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hU).symm

end CKN.Foundation.Heat
