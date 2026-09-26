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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetGraphKoszul
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetRings

/-!
# Strict Milnor squares ([FJP] §4, the abstract interface)

The [FJP] machine — Prop 4.5 (strict localization), Lemma 4.6/5.1 (naturality),
Lemma 5.2 (sheafiness transfer), Lemma 4.1 (Tate extension) — is parametric over a
*strict Milnor square* of affinoid `k`-algebras (fjp.txt:571-585):

> "A strict Milnor square will mean a strict pullback square in the sense of Section 1
> for which C → D is a strict surjection. Its topological content is the
> bounded-denominator datum (4.2a) below. For compact bookkeeping in the proof, first
> record the equivalent norm constants κ, ρ ≥ 1:
> d ∈ D ⟹ ∃ c ∈ C : c ↦ d, ‖c‖ ≤ κ‖d‖,            (4.1)
> (b, c) ∈ B ×_D C ⟹ ‖(b,c)‖_R ≤ ρ max{‖b‖_B, ‖c‖_C}. (4.2)"

This file defines the bundled interface `StrictMilnorSquare` (M9a). The finiteness
data on the comparison vertices is exactly what the d = 2 §4 proofs consumed (T30x):
noetherian graph pods and noetherian unit-ball pods. All four square maps are
norm-nonincreasing — the paper's operative normalization ("For the finite-jet square
both may be taken equal to one", and Gauss norms keep every instance in this class);
generalizing to merely bounded maps is a recorded non-goal for M9.

The abstract machine (M9a) lives in this folder:
* `Milnor/Localization.lean` — Prop 4.5: `S.localize` (port of
  `FiniteJetStrictLocalization`).
* `Milnor/Naturality.lean` — Lemma 4.6/5.1: the (4.21) identifications (port of the
  graph-bridge layer).
* `Milnor/Transfer.lean` — Lemma 5.2: `S.isSheafy_R` (port of
  `FiniteJetSheafTransfer`).
* `Milnor/TateExtension.lean` — Lemma 4.1: `S.tateExtend`.
-/

@[expose] public section

open ValuationSpectrum

universe u

/-- **A strict Milnor square of complete ultrametric normed `k`-algebras**
([FJP] §4, fjp.txt:571-585). `R = B ×_D C` strictly, with `ρC : C → D` a strict
surjection.

Fields group as: the four carriers with their analytic structure; the four
norm-nonincreasing square maps and the commutation; the (4.1) κ-lift; the (4.2)
ρ-recovery of `R` from compatible pairs (existence, uniqueness, norm bound); and the
affinoid finiteness data of the comparison vertices in the form the §4 machine
consumes (noetherian graph pods and unit-ball pods, [FJP] Prop 4.5's "assume B, C, D
are affinoid k-algebras"). -/
structure StrictMilnorSquare (k : Type u) [NontriviallyNormedField k]
    [IsUltrametricDist k] [CompleteSpace k] where
  /-- The pullback corner `R = B ×_D C`. -/
  R : Type u
  /-- The disc-side comparison vertex. -/
  B : Type u
  /-- The Laurent-side comparison vertex. -/
  C : Type u
  /-- The overlap vertex. -/
  D : Type u
  [instRingR : NormedCommRing R]
  [instRingB : NormedCommRing B]
  [instRingC : NormedCommRing C]
  [instRingD : NormedCommRing D]
  [instUltraR : IsUltrametricDist R]
  [instUltraB : IsUltrametricDist B]
  [instUltraC : IsUltrametricDist C]
  [instUltraD : IsUltrametricDist D]
  [instAlgR : NormedAlgebra k R]
  [instAlgB : NormedAlgebra k B]
  [instAlgC : NormedAlgebra k C]
  [instAlgD : NormedAlgebra k D]
  [instCompleteR : CompleteSpace R]
  [instCompleteB : CompleteSpace B]
  [instCompleteC : CompleteSpace C]
  [instCompleteD : CompleteSpace D]
  [instNormOneR : NormOneClass R]
  [instNormOneB : NormOneClass B]
  [instNormOneC : NormOneClass C]
  [instNormOneD : NormOneClass D]
  /-- `jB : R → B` (the disc-side projection of the pullback). -/
  jB : R →+* B
  /-- `iC : R → C` (the Laurent-side projection). -/
  iC : R →+* C
  /-- `ρB : B → D`. -/
  ρB : B →+* D
  /-- `ρC : C → D` — the strict surjection of the square. -/
  ρC : C →+* D
  /-- The square commutes. -/
  square_comm : ρB.comp jB = ρC.comp iC
  jB_norm_le : ∀ r, ‖jB r‖ ≤ ‖r‖
  iC_norm_le : ∀ r, ‖iC r‖ ≤ ‖r‖
  ρB_norm_le : ∀ b, ‖ρB b‖ ≤ ‖b‖
  ρC_norm_le : ∀ c, ‖ρC c‖ ≤ ‖c‖
  /-- The κ-constant of (4.1). -/
  κ : ℝ
  one_le_κ : 1 ≤ κ
  /-- **(4.1)**: `ρC` is a strict surjection with lifting constant `κ`. -/
  exists_lift : ∀ d : D, ∃ c : C, ρC c = d ∧ ‖c‖ ≤ κ * ‖d‖
  /-- The ρ-constant of (4.2). -/
  ρ : ℝ
  one_le_ρ : 1 ≤ ρ
  /-- **(4.2), existence**: every compatible pair glues. -/
  exists_glue : ∀ b c, ρB b = ρC c → ∃ r : R, jB r = b ∧ iC r = c
  /-- **(4.2), uniqueness**: `R ↪ B ⊕ C`. -/
  pair_injective : ∀ r : R, jB r = 0 → iC r = 0 → r = 0
  /-- **(4.2), norm recovery**: `‖r‖ ≤ ρ · max ‖jB r‖ ‖iC r‖`. -/
  norm_le_pair : ∀ r : R, ‖r‖ ≤ ρ * max ‖jB r‖ ‖iC r‖
  /-- Affinoid finiteness of the comparison vertices, in consumed form:
  noetherian graph pods (from strong noetherianity, [FJP] Prop 4.5's affinoid
  hypothesis via Lemma 4.2's presentation argument). -/
  pods_noetherian_B : ∀ m : ℕ, IsNoetherianRing (FiniteJet.GraphKoszul.P B m)
  pods_noetherian_C : ∀ m : ℕ, IsNoetherianRing (FiniteJet.GraphKoszul.P C m)
  pods_noetherian_D : ∀ m : ℕ, IsNoetherianRing (FiniteJet.GraphKoszul.P D m)
  /-- Noetherian unit-ball pods (the Wedhorn-closedness input of the §4 chase;
  d = 2 supplier: T303's `isNoetherianRing_unitBall_of_section`). -/
  unitBall_pods_noetherian_B : ∀ m : ℕ, IsNoetherianRing (FiniteJet.unitBall (FiniteJet.GraphKoszul.P B m))
  unitBall_pods_noetherian_C : ∀ m : ℕ, IsNoetherianRing (FiniteJet.unitBall (FiniteJet.GraphKoszul.P C m))
  unitBall_pods_noetherian_D : ∀ m : ℕ, IsNoetherianRing (FiniteJet.unitBall (FiniteJet.GraphKoszul.P D m))

namespace StrictMilnorSquare

variable {k : Type u} [NontriviallyNormedField k] [IsUltrametricDist k] [CompleteSpace k]
variable (S : StrictMilnorSquare k)

attribute [instance] instRingR instRingB instRingC instRingD
  instUltraR instUltraB instUltraC instUltraD
  instAlgR instAlgB instAlgC instAlgD
  instCompleteR instCompleteB instCompleteC instCompleteD
  instNormOneR instNormOneB instNormOneC instNormOneD

/-- The compatible-pair recovery is unique (immediate from `pair_injective`). -/
theorem glue_unique {b : S.B} {c : S.C} {r r' : S.R}
    (hr : S.jB r = b ∧ S.iC r = c) (hr' : S.jB r' = b ∧ S.iC r' = c) : r = r' := by
  have h1 : S.jB (r - r') = 0 := by rw [map_sub, hr.1, hr'.1, sub_self]
  have h2 : S.iC (r - r') = 0 := by rw [map_sub, hr.2, hr'.2, sub_self]
  have := S.pair_injective _ h1 h2
  exact sub_eq_zero.mp this

end StrictMilnorSquare
