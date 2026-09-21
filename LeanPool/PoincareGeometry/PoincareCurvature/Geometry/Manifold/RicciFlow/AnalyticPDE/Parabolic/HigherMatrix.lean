/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherFunctionSpace
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.MatrixC0Alpha
/-!
# Higher parabolic Holder matrix handoffs

This module connects the coordinate `C^{2+α,1+α/2}` norm-ball layer to the
matrix-valued `C^{0,α}` closure estimates used by the Ricci-DeTurck schematic
RHS.  It proves no Schauder estimate; it only records that higher entry controls
are strong enough to supply the primitive `C^{0,α}` hypotheses.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal BigOperators Matrix.Norms.Elementwise

namespace RicciFlow
namespace AnalyticPDE

/-- Coordinate direction in a finite coordinate model. -/
def parabolicCoordinateUnitVector (n : Type*) [DecidableEq n] (i : n) : n → ℝ :=
  Pi.single i 1

/-- Read a first spatial derivative in an arbitrary spatial direction. -/
def firstDerivativeVectorReadout {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : X) :
    (X →L[ℝ] E) →L[ℝ] E :=
  (ContinuousLinearMap.apply ℝ E) v

@[simp]
theorem firstDerivativeVectorReadout_apply {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : X) (L : X →L[ℝ] E) :
    firstDerivativeVectorReadout (X := X) (E := E) v L = L v :=
  rfl

/-- Read a second spatial derivative in two arbitrary spatial directions. -/
def secondDerivativeVectorReadout {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v w : X) :
    (X →L[ℝ] (X →L[ℝ] E)) →L[ℝ] E :=
  (firstDerivativeVectorReadout (X := X) (E := E) w).comp
    ((ContinuousLinearMap.apply ℝ (X →L[ℝ] E)) v)

@[simp]
theorem secondDerivativeVectorReadout_apply {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v w : X)
    (B : X →L[ℝ] (X →L[ℝ] E)) :
    secondDerivativeVectorReadout (X := X) (E := E) v w B = B v w :=
  rfl

/-- Operator norm of the first-derivative arbitrary-vector readout. -/
def firstDerivativeVectorReadoutOpNorm {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (v : X) : ℝ :=
  ContinuousLinearMap.opNorm
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := (X →L[ℝ] ℝ)) (F := ℝ)
    (firstDerivativeVectorReadout (X := X) (E := ℝ) v)

/-- Operator norm of the second-derivative arbitrary-vector readout. -/
def secondDerivativeVectorReadoutOpNorm {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (v w : X) : ℝ :=
  ContinuousLinearMap.opNorm
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := (X →L[ℝ] (X →L[ℝ] ℝ))) (F := ℝ)
    (secondDerivativeVectorReadout (X := X) (E := ℝ) v w)

/-- First-derivative coefficient radii obtained by reading a finite family of spatial
directions from metric-entry second jets. -/
def firstDerivativeVectorRadius {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ι → X) (R : ι → ι → ℝ) : ι → ι → ι → ℝ :=
  fun a i j => firstDerivativeVectorReadoutOpNorm (X := X) (v a) * R i j

theorem firstDerivativeVectorRadius_nonneg {X ι : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ι → X) {R : ι → ι → ℝ} (hR : ∀ i j, 0 ≤ R i j) :
    ∀ a i j, 0 ≤ firstDerivativeVectorRadius (X := X) v R a i j := by
  intro a i j
  exact mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (hR i j)

/-- Second-derivative coefficient radii obtained by reading a finite family of spatial
directions from metric-entry second jets. -/
def secondDerivativeVectorRadius {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ι → X) (R : ι → ι → ℝ) : ι → ι → ι → ι → ℝ :=
  fun a b i j => secondDerivativeVectorReadoutOpNorm (X := X) (v a) (v b) * R i j

theorem secondDerivativeVectorRadius_nonneg {X ι : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ι → X) {R : ι → ι → ℝ} (hR : ∀ i j, 0 ≤ R i j) :
    ∀ a b i j, 0 ≤ secondDerivativeVectorRadius (X := X) v R a b i j := by
  intro a b i j
  exact mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (hR i j)

/-- Read a first spatial derivative in one coordinate direction. -/
def firstDerivativeCoordinateReadout {n E : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (i : n) :
    ((n → ℝ) →L[ℝ] E) →L[ℝ] E :=
  (ContinuousLinearMap.apply ℝ E) (parabolicCoordinateUnitVector n i)

@[simp]
theorem firstDerivativeCoordinateReadout_apply {n E : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (i : n)
    (L : (n → ℝ) →L[ℝ] E) :
    firstDerivativeCoordinateReadout (n := n) (E := E) i L =
      L (parabolicCoordinateUnitVector n i) :=
  rfl

/-- Read a second spatial derivative in two coordinate directions. -/
def secondDerivativeCoordinateReadout {n E : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (i j : n) :
    ((n → ℝ) →L[ℝ] ((n → ℝ) →L[ℝ] E)) →L[ℝ] E :=
  (firstDerivativeCoordinateReadout (n := n) (E := E) j).comp
    ((ContinuousLinearMap.apply ℝ ((n → ℝ) →L[ℝ] E)) (parabolicCoordinateUnitVector n i))

@[simp]
theorem secondDerivativeCoordinateReadout_apply {n E : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (i j : n)
    (B : (n → ℝ) →L[ℝ] ((n → ℝ) →L[ℝ] E)) :
    secondDerivativeCoordinateReadout (n := n) (E := E) i j B =
      B (parabolicCoordinateUnitVector n i) (parabolicCoordinateUnitVector n j) :=
  rfl

/-- Operator norm of the first-derivative coordinate readout. -/
def firstDerivativeCoordinateReadoutOpNorm {n : Type*} [Fintype n] [DecidableEq n]
    (i : n) : ℝ :=
  ContinuousLinearMap.opNorm
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := ((n → ℝ) →L[ℝ] ℝ)) (F := ℝ)
    (firstDerivativeCoordinateReadout (n := n) (E := ℝ) i)

/-- Operator norm of the second-derivative coordinate readout. -/
def secondDerivativeCoordinateReadoutOpNorm {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n) : ℝ :=
  ContinuousLinearMap.opNorm
    (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := ((n → ℝ) →L[ℝ] ((n → ℝ) →L[ℝ] ℝ))) (F := ℝ)
    (secondDerivativeCoordinateReadout (n := n) (E := ℝ) i j)

/-- First-derivative coefficient radii obtained by reading coordinate directions from
metric-entry second jets. -/
def firstDerivativeCoordinateRadius {n : Type*} [Fintype n] [DecidableEq n]
    (R : n → n → ℝ) : n → n → n → ℝ :=
  fun a i j => firstDerivativeCoordinateReadoutOpNorm (n := n) a * R i j

/-- Second-derivative coefficient radii obtained by reading coordinate directions from
metric-entry second jets. -/
def secondDerivativeCoordinateRadius {n : Type*} [Fintype n] [DecidableEq n]
    (R : n → n → ℝ) : n → n → n → n → ℝ :=
  fun a b i j => secondDerivativeCoordinateReadoutOpNorm (n := n) a b * R i j

@[simp]
theorem firstDerivativeVectorRadius_coordinateUnitVector {n : Type*} [Fintype n]
    [DecidableEq n] (R : n → n → ℝ) :
    firstDerivativeVectorRadius (X := n → ℝ) (parabolicCoordinateUnitVector n) R =
      firstDerivativeCoordinateRadius (n := n) R :=
  rfl

@[simp]
theorem secondDerivativeVectorRadius_coordinateUnitVector {n : Type*} [Fintype n]
    [DecidableEq n] (R : n → n → ℝ) :
    secondDerivativeVectorRadius (X := n → ℝ) (parabolicCoordinateUnitVector n) R =
      secondDerivativeCoordinateRadius (n := n) R :=
  rfl

theorem firstDerivativeCoordinateRadius_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {R : n → n → ℝ} (hR : ∀ i j, 0 ≤ R i j) :
    ∀ a i j, 0 ≤ firstDerivativeCoordinateRadius (n := n) R a i j := by
  simpa using
    (firstDerivativeVectorRadius_nonneg (X := n → ℝ)
      (parabolicCoordinateUnitVector n) hR)

theorem secondDerivativeCoordinateRadius_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {R : n → n → ℝ} (hR : ∀ i j, 0 ≤ R i j) :
    ∀ a b i j, 0 ≤ secondDerivativeCoordinateRadius (n := n) R a b i j := by
  simpa using
    (secondDerivativeVectorRadius_nonneg (X := n → ℝ)
      (parabolicCoordinateUnitVector n) hR)

namespace ParabolicC0AlphaNormLe

variable {X E F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {N α : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}

/-- A continuous linear map preserves a single-radius parabolic `C^{0,α}` bound, stated with
`ContinuousLinearMap.opNorm` so it can be used for iterated operator-valued spaces without
typeclass search for the normed structure on the map space. -/
theorem continuousLinearMap_opNorm (L : E →L[ℝ] F)
    (hu : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe (ContinuousLinearMap.opNorm L * N) α
      (fun z => L (u z)) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  refine ⟨ContinuousLinearMap.opNorm L * B,
    mul_nonneg (ContinuousLinearMap.opNorm_nonneg L) hB,
    ContinuousLinearMap.opNorm L * H,
    mul_nonneg (ContinuousLinearMap.opNorm_nonneg L) hH, ?_, ?_⟩
  · calc
      ContinuousLinearMap.opNorm L * B + ContinuousLinearMap.opNorm L * H =
          ContinuousLinearMap.opNorm L * (B + H) := by ring
      _ ≤ ContinuousLinearMap.opNorm L * N :=
          mul_le_mul_of_nonneg_left hsum (ContinuousLinearMap.opNorm_nonneg L)
  · constructor
    · intro z hz
      calc
        ‖L (u z)‖ ≤ ContinuousLinearMap.opNorm L * ‖u z‖ :=
          ContinuousLinearMap.le_opNorm L (u z)
        _ ≤ ContinuousLinearMap.opNorm L * B :=
          mul_le_mul_of_nonneg_left (hctrl.bounded hz) (ContinuousLinearMap.opNorm_nonneg L)
    · intro p hp q hq
      calc
        ‖L (u p) - L (u q)‖ = ‖L (u p - u q)‖ := by rw [← map_sub]
        _ ≤ ContinuousLinearMap.opNorm L * ‖u p - u q‖ :=
          ContinuousLinearMap.le_opNorm L (u p - u q)
        _ ≤ ContinuousLinearMap.opNorm L * (H * parabolicDistance p q ^ α) :=
          mul_le_mul_of_nonneg_left (hctrl.holder hp hq) (ContinuousLinearMap.opNorm_nonneg L)
        _ = (ContinuousLinearMap.opNorm L * H) * parabolicDistance p q ^ α := by ring

end ParabolicC0AlphaNormLe

/-- Continuous linear insertion of one matrix entry. -/
def matrixSingleContinuousLinearMap {m n A : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NormedAddCommGroup A] [NormedSpace ℝ A]
    (i : m) (j : n) : A →L[ℝ] Matrix m n A :=
  (ContinuousLinearMap.single ℝ (fun _ : m => n → A) i).comp
    (ContinuousLinearMap.single ℝ (fun _ : n => A) j)

@[simp]
theorem matrixSingleContinuousLinearMap_apply {m n A : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NormedAddCommGroup A] [NormedSpace ℝ A]
    (i : m) (j : n) (a : A) :
    matrixSingleContinuousLinearMap (m := m) (n := n) (A := A) i j a =
      Matrix.single i j a := by
  ext i' j'
  change (Pi.single i (Pi.single j a) : m → n → A) i' j' = Matrix.single i j a i' j'
  by_cases hi : i' = i
  · subst i'
    by_cases hj : j' = j
    · subst j'
      simp [Matrix.single]
    · simp [Matrix.single, hj, Ne.symm hj]
  · simp [Matrix.single, hi, Ne.symm hi]

namespace ParabolicC2AlphaNormLe

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise higher parabolic control packages as matrix-valued value-level `C^{0,α}`
control, with the matrix radius the sum of the entry radii. -/
theorem matrix_c0AlphaNormLe_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {N : m → n → ℝ} {M : ℝ × X → Matrix m n A}
    (h : ∀ i j, ParabolicC2AlphaNormLe (N i j) α (fun z => M z i j) s) :
    ParabolicC0AlphaNormLe (∑ i, ∑ j, N i j) α M s :=
  ParabolicC0AlphaNormLe.matrix_of_entries
    (X := X) (α := α) (s := s) fun i j => (h i j).value_c0AlphaNormLe_self

/-- A matrix-valued higher parabolic norm ball projects to each entry as a value-level
`C^{0,α}` norm ball with the same radius. -/
theorem matrix_apply {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {N : ℝ} {M : ℝ × X → Matrix m n A}
    (h : ParabolicC2AlphaNormLe N α M s) (i : m) (j : n) :
    ParabolicC0AlphaNormLe N α (fun z => M z i j) s :=
  h.value_c0AlphaNormLe_self.matrix_apply i j

/-- A matrix-valued higher parabolic norm ball projects to each entry as a full higher
parabolic norm ball. -/
theorem matrix_apply_c2AlphaNormLe {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {N : ℝ} {M : ℝ × X → Matrix m n A}
    (h : ParabolicC2AlphaNormLe N α M s) (i : m) (j : n) :
    ParabolicC2AlphaNormLe
      (continuousLinearMapRadius (X := X) (E := Matrix m n A)
        ((ContinuousLinearMap.proj j : (n → A) →L[ℝ] A).comp
          (ContinuousLinearMap.proj i : Matrix m n A →L[ℝ] n → A)) * N) α
      (fun z : ℝ × X => M z i j) s := by
  let L : Matrix m n A →L[ℝ] A :=
    (ContinuousLinearMap.proj j : (n → A) →L[ℝ] A).comp
      (ContinuousLinearMap.proj i : Matrix m n A →L[ℝ] n → A)
  have hport := h.continuousLinearMap L
  simp [L] at hport ⊢
  exact hport

/-- Entrywise full higher parabolic controls assemble into a matrix-valued full higher
parabolic norm ball by inserting entries and summing them. -/
theorem matrix_c2AlphaNormLe_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NormedAddCommGroup A] [NormedSpace ℝ A]
    {N : m → n → ℝ} {M : ℝ × X → Matrix m n A}
    (h : ∀ i j, ParabolicC2AlphaNormLe (N i j) α (fun z => M z i j) s) :
    ParabolicC2AlphaNormLe
      (∑ p : m × n,
        continuousLinearMapRadius (X := X) (E := A)
          (matrixSingleContinuousLinearMap (m := m) (n := n) (A := A) p.1 p.2) *
          N p.1 p.2) α M s := by
  classical
  let L : m × n → A →L[ℝ] Matrix m n A := fun p =>
    matrixSingleContinuousLinearMap (m := m) (n := n) (A := A) p.1 p.2
  have hsum := finset_sum (X := X) (E := Matrix m n A) (α := α) (s := s)
    (S := Finset.univ)
    (N := fun p : m × n =>
      continuousLinearMapRadius (X := X) (E := A) (L p) * N p.1 p.2)
    (u := fun p z => L p (M z p.1 p.2)) ?_
  · have hfun :
        (fun z : ℝ × X => ∑ p : m × n, L p (M z p.1 p.2)) = M := by
      funext z
      calc
        (∑ p : m × n, L p (M z p.1 p.2))
            = ∑ p : m × n, Matrix.single p.1 p.2 (M z p.1 p.2) := by
                apply Finset.sum_congr rfl
                intro p _hp
                simp [L]
        _ = M z := by
                rw [← Finset.univ_product_univ, Finset.sum_product]
                exact (Matrix.matrix_eq_sum_single (M z)).symm
    simpa [hfun] using hsum
  · intro p _hp
    exact (h p.1 p.2).continuousLinearMap (L p)

/-- Entrywise full higher parabolic controls for a matrix difference assemble into a
matrix-valued full higher parabolic difference bound. -/
theorem matrix_sub_c2AlphaNormLe_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NormedAddCommGroup A] [NormedSpace ℝ A]
    {R : m → n → ℝ} {M N : ℝ × X → Matrix m n A}
    (h : ∀ i j, ParabolicC2AlphaNormLe (R i j) α
      (fun z => M z i j - N z i j) s) :
    ParabolicC2AlphaNormLe
      (∑ p : m × n,
        continuousLinearMapRadius (X := X) (E := A)
          (matrixSingleContinuousLinearMap (m := m) (n := n) (A := A) p.1 p.2) *
          R p.1 p.2) α
      (fun z : ℝ × X => M z - N z) s := by
  classical
  simpa [Pi.sub_apply] using
    matrix_c2AlphaNormLe_of_entries (X := X) (α := α) (s := s)
      (N := R) (M := fun z : ℝ × X => M z - N z) h

/-- Finite Pi-valued value-level `C^{0,α}` control from entrywise higher parabolic
single-radius controls. -/
theorem pi_c0AlphaNormLe_of_entries {ι A : Type*} [Fintype ι]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {N : ι → ℝ} {u : ℝ × X → ι → A}
    (h : ∀ i, ParabolicC2AlphaNormLe (N i) α (fun z => u z i) s) :
    ParabolicC0AlphaNormLe (∑ i, N i) α u s :=
  ParabolicC0AlphaNormLe.pi (X := X) (α := α) (s := s)
    (N := N) (u := u) fun i => (h i).value_c0AlphaNormLe_self

/-- The exported single-radius `C^{0,α}` constant for the primitive-input schematic
Ricci-DeTurck matrix estimate after higher entry controls are projected to value-level controls. -/
def ricciDeTurckSchematicMatrixBoundConst {n : Type*} [Fintype n] [DecidableEq n]
    (δ : ℝ) (R : n → n → ℝ) (RD : n → n → n → ℝ)
    (RH : n → n → n → n → ℝ) : ℝ :=
  ((∑ i : n, ∑ j : n,
      (ParabolicC0AlphaOn.matrixInvTwoIndexContractEntryBoundConst
          (𝕜 := ℝ) δ R RH i j +
        ParabolicC0AlphaOn.christoffelQuadraticRicciEntryBoundConst
          (fun a b c =>
            ParabolicC0AlphaOn.matrixInvChristoffelEntryBoundConst
              (𝕜 := ℝ) δ R RD a b c)
          i j)) +
    (∑ i : n, ∑ j : n,
      (ParabolicC0AlphaOn.matrixInvTwoIndexContractEntryHolderConst
          (𝕜 := ℝ) δ R R RH RH i j +
        ParabolicC0AlphaOn.christoffelQuadraticRicciEntryHolderConst
          (fun a b c =>
            ParabolicC0AlphaOn.matrixInvChristoffelEntryBoundConst
              (𝕜 := ℝ) δ R RD a b c)
          (fun a b c =>
            ParabolicC0AlphaOn.matrixInvChristoffelEntryHolderConst
              (𝕜 := ℝ) δ R R RD RD a b c)
          i j)))

/-- Entrywise higher primitive metric, first-derivative, and second-derivative controls feed
the existing quantitative schematic Ricci-DeTurck RHS `C^{0,α}` estimate. -/
theorem ricciDeTurckSchematicMatrix_of_entries {n : Type*} [Fintype n] [DecidableEq n]
    {R : n → n → ℝ} {RD : n → n → n → ℝ}
    {RH : n → n → n → n → ℝ} {δ : ℝ}
    {M : ℝ × X → Matrix n n ℝ}
    {D : ℝ × X → n → n → n → ℝ}
    {H : ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ a b, ParabolicC2AlphaNormLe (R a b) α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC2AlphaNormLe (RD a b c) α (fun z => D z a b c) s)
    (hH : ∀ a b i j, ParabolicC2AlphaNormLe (RH a b i j) α
      (fun z => H z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaNormLe
      (ricciDeTurckSchematicMatrixBoundConst (n := n) δ R RD RH)
      α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M z) (D z) (H z)) s := by
  exact ParabolicC0AlphaNormLe.ricciDeTurck_schematic_of_entries
    (M := M) (D := D) (H := H) (R := R) (RD := RD) (RH := RH) (δ := δ)
    (fun a b => (hM a b).value_c0AlphaNormLe_self)
    (fun a b c => (hD a b c).value_c0AlphaNormLe_self)
    (fun a b i j => (hH a b i j).value_c0AlphaNormLe_self)
    hδpos hdet

/-- Finite-family direct schematic Ricci-DeTurck RHS `C^{0,α}` estimates from entrywise higher
primitive controls. -/
theorem ricciDeTurckSchematicMatrix_family_of_entries {κ n : Type*}
    [Fintype n] [DecidableEq n]
    {R : κ → n → n → ℝ} {RD : κ → n → n → n → ℝ}
    {RH : κ → n → n → n → n → ℝ} {δ : ℝ}
    {M : κ → ℝ × X → Matrix n n ℝ}
    {D : κ → ℝ × X → n → n → n → ℝ}
    {H : κ → ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ r a b, ParabolicC2AlphaNormLe (R r a b) α (fun z => M r z a b) s)
    (hD : ∀ r a b c, ParabolicC2AlphaNormLe (RD r a b c) α
      (fun z => D r z a b c) s)
    (hH : ∀ r a b i j, ParabolicC2AlphaNormLe (RH r a b i j) α
      (fun z => H r z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ∀ r, ParabolicC0AlphaNormLe
      (ricciDeTurckSchematicMatrixBoundConst (n := n) δ (R r) (RD r) (RH r))
      α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M r z) (D r z) (H r z)) s := by
  intro r
  exact ricciDeTurckSchematicMatrix_of_entries
    (X := X) (α := α) (s := s) (δ := δ)
    (R := R r) (RD := RD r) (RH := RH r)
    (M := M r) (D := D r) (H := H r)
    (hM r) (hD r) (hH r) hδpos (hdet r)

/-- Pi-valued finite-family direct schematic Ricci-DeTurck RHS `C^{0,α}` estimate from entrywise
higher primitive controls. -/
theorem ricciDeTurckSchematicMatrix_pi_family_of_entries {κ n : Type*}
    [Fintype κ] [Fintype n] [DecidableEq n]
    {R : κ → n → n → ℝ} {RD : κ → n → n → n → ℝ}
    {RH : κ → n → n → n → n → ℝ} {δ : ℝ}
    {M : κ → ℝ × X → Matrix n n ℝ}
    {D : κ → ℝ × X → n → n → n → ℝ}
    {H : κ → ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ r a b, ParabolicC2AlphaNormLe (R r a b) α (fun z => M r z a b) s)
    (hD : ∀ r a b c, ParabolicC2AlphaNormLe (RD r a b c) α
      (fun z => D r z a b c) s)
    (hH : ∀ r a b i j, ParabolicC2AlphaNormLe (RH r a b i j) α
      (fun z => H r z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ParabolicC0AlphaNormLe
      (∑ r, ricciDeTurckSchematicMatrixBoundConst (n := n) δ (R r) (RD r) (RH r))
      α
      (fun z : ℝ × X => fun r : κ =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M r z) (D r z) (H r z)) s :=
  ParabolicC0AlphaNormLe.pi (X := X) (α := α) (s := s)
    (N := fun r =>
      ricciDeTurckSchematicMatrixBoundConst (n := n) δ (R r) (RD r) (RH r))
    (u := fun z : ℝ × X => fun r : κ =>
      ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M r z) (D r z) (H r z))
    (ricciDeTurckSchematicMatrix_family_of_entries
      (X := X) (α := α) (s := s) (δ := δ)
      (R := R) (RD := RD) (RH := RH) (M := M) (D := D) (H := H)
      hM hD hH hδpos hdet)
/-- A metric with entrywise higher parabolic control supplies its own first- and
second-derivative primitive arrays by reading chosen second jets against a finite family of
spatial directions.  This removes the separate `D`/`H` primitive hypotheses for the direct
schematic Ricci-DeTurck `C^{0,α}` estimate on any normed spatial model. -/
theorem exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions {n : Type*}
    [Fintype n] [DecidableEq n] (v : n → X)
    {R : n → n → ℝ} {δ : ℝ} {s : Set (ℝ × X)}
    {M : ℝ × X → Matrix n n ℝ}
    (hM : ∀ i j, ParabolicC2AlphaNormLe (R i j) α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ∃ J : ∀ i j, ParabolicSecondJet (fun z : ℝ × X => M z i j) s,
      ParabolicC0AlphaNormLe
        (ricciDeTurckSchematicMatrixBoundConst (n := n) δ R
          (firstDerivativeVectorRadius (X := X) v R)
          (secondDerivativeVectorRadius (X := X) v R))
        α
        (fun z : ℝ × X =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M z)
            (fun a i j => (J i j).spaceDeriv z (v a))
            (fun a b i j => (J i j).spaceSecondDeriv z (v a) (v b))) s := by
  classical
  choose J Nu hNu Nx hNx Nxx hNxx Nt hNt hsum hMval hJx hJxx hJt using hM
  refine ⟨J, ?_⟩
  have hM0 : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => M z i j) s := by
    intro i j
    have hNu_le : Nu i j ≤ R i j := by
      linarith [hNu i j, hNx i j, hNxx i j, hNt i j, hsum i j]
    exact (hMval i j).mono_const hNu_le
  have hD : ∀ a i j,
      ParabolicC0AlphaNormLe (firstDerivativeVectorRadius (X := X) v R a i j) α
        (fun z : ℝ × X => (J i j).spaceDeriv z (v a)) s := by
    intro a i j
    have hNx_le : Nx i j ≤ R i j := by
      linarith [hNu i j, hNx i j, hNxx i j, hNt i j, hsum i j]
    have hspace : ParabolicC0AlphaNormLe (R i j) α (J i j).spaceDeriv s :=
      (hJx i j).mono_const hNx_le
    have hx :=
      hspace.continuousLinearMap_opNorm
        (firstDerivativeVectorReadout (X := X) (E := ℝ) (v a))
    simpa [firstDerivativeVectorRadius, firstDerivativeVectorReadoutOpNorm] using hx
  have hH : ∀ a b i j,
      ParabolicC0AlphaNormLe (secondDerivativeVectorRadius (X := X) v R a b i j) α
        (fun z : ℝ × X => (J i j).spaceSecondDeriv z (v a) (v b)) s := by
    intro a b i j
    have hNxx_le : Nxx i j ≤ R i j := by
      linarith [hNu i j, hNx i j, hNxx i j, hNt i j, hsum i j]
    have hsecond : ParabolicC0AlphaNormLe (R i j) α (J i j).spaceSecondDeriv s :=
      (hJxx i j).mono_const hNxx_le
    have hxx :=
      hsecond.continuousLinearMap_opNorm
        (secondDerivativeVectorReadout (X := X) (E := ℝ) (v a) (v b))
    simpa [secondDerivativeVectorRadius, secondDerivativeVectorReadoutOpNorm] using hxx
  simpa [ricciDeTurckSchematicMatrixBoundConst] using
    (ParabolicC0AlphaNormLe.ricciDeTurck_schematic_of_entries
      (X := X) (α := α) (s := s) (𝕜 := ℝ) (δ := δ)
      (R := R) (RD := firstDerivativeVectorRadius (X := X) v R)
      (RH := secondDerivativeVectorRadius (X := X) v R)
      (M := M)
      (D := fun z a i j => (J i j).spaceDeriv z (v a))
      (H := fun z a b i j => (J i j).spaceSecondDeriv z (v a) (v b))
      hM0 hD hH hδpos hdet)
/-- Finite-family version of
`exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions`, packaged as one
Pi-valued `C^{0,α}` estimate for the family of schematic Ricci-DeTurck RHS fields. -/
theorem exists_secondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries_directions
    {κ n : Type*} [Fintype κ] [Fintype n] [DecidableEq n] (v : n → X)
    {R : κ → n → n → ℝ} {δ : ℝ} {s : Set (ℝ × X)}
    {M : κ → ℝ × X → Matrix n n ℝ}
    (hM : ∀ r i j, ParabolicC2AlphaNormLe (R r i j) α (fun z => M r z i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ∃ J : ∀ r i j, ParabolicSecondJet (fun z : ℝ × X => M r z i j) s,
      ParabolicC0AlphaNormLe
        (∑ r, ricciDeTurckSchematicMatrixBoundConst (n := n) δ (R r)
          (firstDerivativeVectorRadius (X := X) v (R r))
          (secondDerivativeVectorRadius (X := X) v (R r)))
        α
        (fun z : ℝ × X => fun r : κ =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M r z)
            (fun a i j => (J r i j).spaceDeriv z (v a))
            (fun a b i j => (J r i j).spaceSecondDeriv z (v a) (v b))) s := by
  classical
  choose J hJ using fun r =>
    exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions
      (X := X) (α := α) (v := v) (R := R r) (δ := δ) (s := s) (M := M r)
      (hM r) hδpos (hdet r)
  refine ⟨J, ?_⟩
  exact ParabolicC0AlphaNormLe.pi (X := X) (α := α) (s := s)
    (N := fun r =>
      ricciDeTurckSchematicMatrixBoundConst (n := n) δ (R r)
        (firstDerivativeVectorRadius (X := X) v (R r))
        (secondDerivativeVectorRadius (X := X) v (R r)))
    (u := fun z : ℝ × X => fun r : κ =>
      ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M r z)
        (fun a i j => (J r i j).spaceDeriv z (v a))
        (fun a b i j => (J r i j).spaceSecondDeriv z (v a) (v b)))
    hJ
/-- Finite-family version of
`exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions` where each family
member has its own finite direction frame. -/
theorem exists_secondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries_family_directions
    {κ n : Type*} [Fintype κ] [Fintype n] [DecidableEq n] (v : κ → n → X)
    {R : κ → n → n → ℝ} {δ : ℝ} {s : Set (ℝ × X)}
    {M : κ → ℝ × X → Matrix n n ℝ}
    (hM : ∀ r i j, ParabolicC2AlphaNormLe (R r i j) α (fun z => M r z i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ∃ J : ∀ r i j, ParabolicSecondJet (fun z : ℝ × X => M r z i j) s,
      ParabolicC0AlphaNormLe
        (∑ r, ricciDeTurckSchematicMatrixBoundConst (n := n) δ (R r)
          (firstDerivativeVectorRadius (X := X) (v r) (R r))
          (secondDerivativeVectorRadius (X := X) (v r) (R r)))
        α
        (fun z : ℝ × X => fun r : κ =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M r z)
            (fun a i j => (J r i j).spaceDeriv z (v r a))
            (fun a b i j => (J r i j).spaceSecondDeriv z (v r a) (v r b))) s := by
  classical
  choose J hJ using fun r =>
    exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions
      (X := X) (α := α) (v := v r) (R := R r) (δ := δ) (s := s) (M := M r)
      (hM r) hδpos (hdet r)
  refine ⟨J, ?_⟩
  exact ParabolicC0AlphaNormLe.pi (X := X) (α := α) (s := s)
    (N := fun r =>
      ricciDeTurckSchematicMatrixBoundConst (n := n) δ (R r)
        (firstDerivativeVectorRadius (X := X) (v r) (R r))
        (secondDerivativeVectorRadius (X := X) (v r) (R r)))
    (u := fun z : ℝ × X => fun r : κ =>
      ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M r z)
        (fun a i j => (J r i j).spaceDeriv z (v r a))
        (fun a b i j => (J r i j).spaceSecondDeriv z (v r a) (v r b)))
    hJ
/-- A metric with entrywise higher parabolic control supplies its own coordinate first- and
second-derivative primitive arrays through chosen second jets.  This removes the separate
`D`/`H` primitive hypotheses for the direct schematic Ricci-DeTurck `C^{0,α}` estimate when the
spatial model is the finite coordinate space `n → ℝ`. -/
theorem exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries {n : Type*}
    [Fintype n] [DecidableEq n]
    {R : n → n → ℝ} {δ : ℝ} {s : Set (ℝ × (n → ℝ))}
    {M : ℝ × (n → ℝ) → Matrix n n ℝ}
    (hM : ∀ i j, ParabolicC2AlphaNormLe (R i j) α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ∃ J : ∀ i j, ParabolicSecondJet (fun z : ℝ × (n → ℝ) => M z i j) s,
      ParabolicC0AlphaNormLe
        (ricciDeTurckSchematicMatrixBoundConst (n := n) δ R
          (firstDerivativeCoordinateRadius (n := n) R)
          (secondDerivativeCoordinateRadius (n := n) R))
        α
        (fun z : ℝ × (n → ℝ) =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M z)
            (fun a i j => (J i j).spaceDeriv z (parabolicCoordinateUnitVector n a))
            (fun a b i j =>
              (J i j).spaceSecondDeriv z
                (parabolicCoordinateUnitVector n a) (parabolicCoordinateUnitVector n b))) s := by
  classical
  choose J Nu hNu Nx hNx Nxx hNxx Nt hNt hsum hMval hJx hJxx hJt using hM
  refine ⟨J, ?_⟩
  have hM0 : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => M z i j) s := by
    intro i j
    have hNu_le : Nu i j ≤ R i j := by
      linarith [hNu i j, hNx i j, hNxx i j, hNt i j, hsum i j]
    exact (hMval i j).mono_const hNu_le
  have hD : ∀ a i j,
      ParabolicC0AlphaNormLe (firstDerivativeCoordinateRadius (n := n) R a i j) α
        (fun z : ℝ × (n → ℝ) =>
          (J i j).spaceDeriv z (parabolicCoordinateUnitVector n a)) s := by
    intro a i j
    have hNx_le : Nx i j ≤ R i j := by
      linarith [hNu i j, hNx i j, hNxx i j, hNt i j, hsum i j]
    have hspace : ParabolicC0AlphaNormLe (R i j) α (J i j).spaceDeriv s :=
      (hJx i j).mono_const hNx_le
    have hx :=
      hspace.continuousLinearMap_opNorm
        (firstDerivativeCoordinateReadout (n := n) (E := ℝ) a)
    simpa [firstDerivativeCoordinateRadius, firstDerivativeCoordinateReadoutOpNorm] using hx
  have hH : ∀ a b i j,
      ParabolicC0AlphaNormLe (secondDerivativeCoordinateRadius (n := n) R a b i j) α
        (fun z : ℝ × (n → ℝ) =>
          (J i j).spaceSecondDeriv z
            (parabolicCoordinateUnitVector n a) (parabolicCoordinateUnitVector n b)) s := by
    intro a b i j
    have hNxx_le : Nxx i j ≤ R i j := by
      linarith [hNu i j, hNx i j, hNxx i j, hNt i j, hsum i j]
    have hsecond : ParabolicC0AlphaNormLe (R i j) α (J i j).spaceSecondDeriv s :=
      (hJxx i j).mono_const hNxx_le
    have hxx :=
      hsecond.continuousLinearMap_opNorm
        (secondDerivativeCoordinateReadout (n := n) (E := ℝ) a b)
    simpa [secondDerivativeCoordinateRadius, secondDerivativeCoordinateReadoutOpNorm] using hxx
  simpa [ricciDeTurckSchematicMatrixBoundConst] using
    (ParabolicC0AlphaNormLe.ricciDeTurck_schematic_of_entries
      (X := n → ℝ) (α := α) (s := s) (𝕜 := ℝ) (δ := δ)
      (R := R) (RD := firstDerivativeCoordinateRadius (n := n) R)
      (RH := secondDerivativeCoordinateRadius (n := n) R)
      (M := M)
      (D := fun z a i j => (J i j).spaceDeriv z (parabolicCoordinateUnitVector n a))
      (H := fun z a b i j =>
        (J i j).spaceSecondDeriv z
          (parabolicCoordinateUnitVector n a) (parabolicCoordinateUnitVector n b))
      hM0 hD hH hδpos hdet)
/-- Finite-family version of
`exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries`, packaged as one Pi-valued
`C^{0,α}` estimate for the family of schematic Ricci-DeTurck coordinate RHS fields. -/
theorem exists_secondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries
    {κ n : Type*} [Fintype κ] [Fintype n] [DecidableEq n]
    {R : κ → n → n → ℝ} {δ : ℝ} {s : Set (ℝ × (n → ℝ))}
    {M : κ → ℝ × (n → ℝ) → Matrix n n ℝ}
    (hM : ∀ r i j, ParabolicC2AlphaNormLe (R r i j) α (fun z => M r z i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × (n → ℝ)⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ∃ J : ∀ r i j, ParabolicSecondJet (fun z : ℝ × (n → ℝ) => M r z i j) s,
      ParabolicC0AlphaNormLe
        (∑ r, ricciDeTurckSchematicMatrixBoundConst (n := n) δ (R r)
          (firstDerivativeCoordinateRadius (n := n) (R r))
          (secondDerivativeCoordinateRadius (n := n) (R r)))
        α
        (fun z : ℝ × (n → ℝ) => fun r : κ =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M r z)
            (fun a i j => (J r i j).spaceDeriv z (parabolicCoordinateUnitVector n a))
            (fun a b i j =>
              (J r i j).spaceSecondDeriv z
                (parabolicCoordinateUnitVector n a) (parabolicCoordinateUnitVector n b))) s := by
  classical
  choose J hJ using fun r =>
    exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries
      (α := α) (R := R r) (δ := δ) (s := s) (M := M r)
      (hM r) hδpos (hdet r)
  refine ⟨J, ?_⟩
  exact ParabolicC0AlphaNormLe.pi (X := n → ℝ) (α := α) (s := s)
    (N := fun r =>
      ricciDeTurckSchematicMatrixBoundConst (n := n) δ (R r)
        (firstDerivativeCoordinateRadius (n := n) (R r))
        (secondDerivativeCoordinateRadius (n := n) (R r)))
    (u := fun z : ℝ × (n → ℝ) => fun r : κ =>
      ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M r z)
        (fun a i j => (J r i j).spaceDeriv z (parabolicCoordinateUnitVector n a))
        (fun a b i j =>
          (J r i j).spaceSecondDeriv z
            (parabolicCoordinateUnitVector n a) (parabolicCoordinateUnitVector n b)))
    hJ

/-- Entrywise higher parabolic difference controls with radii linear in a shared scalar give a
pointwise matrix-norm difference bound with the summed entry radius. -/
theorem matrix_norm_sub_le_sum_mul_of_entries {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {R : ℝ} {K : m → n → ℝ} {M N : ℝ × X → Matrix m n ℝ}
    (hK : ∀ i j, 0 ≤ K i j) (hR : 0 ≤ R)
    (h : ∀ i j, ParabolicC2AlphaNormLe (K i j * R) α
      (fun z => M z i j - N z i j) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    ‖M z - N z‖ ≤ (∑ i, ∑ j, K i j) * R := by
  have hsum_nonneg : 0 ≤ ∑ i, ∑ j, K i j :=
    Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hK i j
  have htarget_nonneg : 0 ≤ (∑ i, ∑ j, K i j) * R :=
    mul_nonneg hsum_nonneg hR
  refine (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun j => ?_
  have hentry : ‖M z i j - N z i j‖ ≤ K i j * R := by
    simpa [dist_eq_norm] using (h i j).dist_le_of_sub hz
  have hentry_le_sum : K i j ≤ ∑ i, ∑ j, K i j := by
    have hentry_le_row : K i j ≤ ∑ j, K i j :=
      Finset.single_le_sum (fun j' _hj' => hK i j') (Finset.mem_univ j)
    have hrow_le_sum : (∑ j, K i j) ≤ ∑ i, ∑ j, K i j :=
      Finset.single_le_sum
        (fun i' _hi' => Finset.sum_nonneg fun j' _hj' => hK i' j')
        (Finset.mem_univ i)
    exact hentry_le_row.trans hrow_le_sum
  exact hentry.trans (mul_le_mul_of_nonneg_right hentry_le_sum hR)

private theorem entry_le_triple_sum {n : Type*} [Fintype n] [DecidableEq n]
    {K : n → n → n → ℝ} (hK : ∀ a b c, 0 ≤ K a b c) (a b c : n) :
    K a b c ≤ ∑ a, ∑ b, ∑ c, K a b c := by
  have hentry_le_c : K a b c ≤ ∑ c, K a b c :=
    Finset.single_le_sum (fun c' _hc' => hK a b c') (Finset.mem_univ c)
  have hc_le_b : (∑ c, K a b c) ≤ ∑ b, ∑ c, K a b c :=
    Finset.single_le_sum
      (fun b' _hb' => Finset.sum_nonneg fun c' _hc' => hK a b' c')
      (Finset.mem_univ b)
  have hb_le_a : (∑ b, ∑ c, K a b c) ≤ ∑ a, ∑ b, ∑ c, K a b c :=
    Finset.single_le_sum
      (fun a' _ha' =>
        Finset.sum_nonneg fun b' _hb' =>
          Finset.sum_nonneg fun c' _hc' => hK a' b' c')
      (Finset.mem_univ a)
  exact hentry_le_c.trans (hc_le_b.trans hb_le_a)

/-- Linear-radius bounded schematic Ricci-DeTurck RHS difference estimate from higher parabolic
primitive controls.  This is the `C⁰` readout form of the higher matrix Lipschitz estimate: the
entrywise higher difference balls are summed into matrix/array primitive difference constants
before the existing pointwise schematic RHS bound is applied. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_higher_primitive_normLe
    {n : Type*} [Fintype n] [DecidableEq n]
    {δ R : ℝ} {KM : n → n → ℝ} {KD : n → n → n → ℝ}
    {KH : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {M N : ℝ × X → Matrix n n ℝ}
    {D E : ℝ × X → n → n → n → ℝ}
    {H K : ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : ∀ a b, 0 ≤ KM a b) (hKD : ∀ a b c, 0 ≤ KD a b c)
    (hKH : ∀ a b i j, 0 ≤ KH a b i j) (hR : 0 ≤ R)
    (hM : ∀ a b, ParabolicC2AlphaNormLe (C a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC2AlphaNormLe (C a b) α (fun z => N z a b) s)
    (hD : ∀ a b c, ParabolicC2AlphaNormLe (DB a b c) α (fun z => D z a b c) s)
    (hE : ∀ a b c, ParabolicC2AlphaNormLe (DB a b c) α (fun z => E z a b c) s)
    (hK : ∀ a b i j, ParabolicC2AlphaNormLe (HB a b i j) α
      (fun z => K z a b i j) s)
    (hMdiff : ∀ a b, ParabolicC2AlphaNormLe (KM a b * R) α
      (fun z => M z a b - N z a b) s)
    (hDdiff : ∀ a b c, ParabolicC2AlphaNormLe (KD a b c * R) α
      (fun z => D z a b c - E z a b c) s)
    (hHdiff : ∀ a b i j, ParabolicC2AlphaNormLe (KH a b i j * R) α
      (fun z => H z a b i j - K z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicBoundedWith
      (ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ C DB HB
          (∑ a, ∑ b, KM a b)
          (∑ a, ∑ b, ∑ c, KD a b c)
          (fun i j => ∑ a, ∑ b, KH a b i j) * R)
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s := by
  have hKMsum : 0 ≤ ∑ a, ∑ b, KM a b :=
    Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM a b
  have hKDsum : 0 ≤ ∑ a, ∑ b, ∑ c, KD a b c :=
    Finset.sum_nonneg fun a _ha =>
      Finset.sum_nonneg fun b _hb => Finset.sum_nonneg fun c _hc => hKD a b c
  have hKHsum : ∀ i j, 0 ≤ ∑ a, ∑ b, KH a b i j := fun i j =>
    Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKH a b i j
  have hMbound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖M z a b‖ ≤ C a b := by
    intro z hz a b
    exact (hM a b).norm_le hz
  have hNbound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖N z a b‖ ≤ C a b := by
    intro z hz a b
    exact (hN a b).norm_le hz
  have hDbound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖D z a b c‖ ≤ DB a b c := by
    intro z hz a b c
    exact (hD a b c).norm_le hz
  have hEbound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖E z a b c‖ ≤ DB a b c := by
    intro z hz a b c
    exact (hE a b c).norm_le hz
  have hKbound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j, ‖K z a b i j‖ ≤ HB a b i j := by
    intro z hz a b i j
    exact (hK a b i j).norm_le hz
  have hMdiff_bound : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      ‖M z - N z‖ ≤ (∑ a, ∑ b, KM a b) * R := by
    intro z hz
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := KM) (M := M) (N := N)
      hKM hR hMdiff hz
  have hDdiff_bound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ (∑ a, ∑ b, ∑ c, KD a b c) * R := by
    intro z hz a b c
    have hentry : ‖D z a b c - E z a b c‖ ≤ KD a b c * R := by
      simpa [dist_eq_norm] using (hDdiff a b c).dist_le_of_sub hz
    exact hentry.trans (mul_le_mul_of_nonneg_right (entry_le_triple_sum hKD a b c) hR)
  have hHdiff_bound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
      ‖((fun a b => H z a b i j) : Matrix n n ℝ) -
          ((fun a b => K z a b i j) : Matrix n n ℝ)‖ ≤
        (∑ a, ∑ b, KH a b i j) * R := by
    intro z hz i j
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := fun a b => KH a b i j)
      (M := fun z : ℝ × X => (fun a b => H z a b i j))
      (N := fun z : ℝ × X => (fun a b => K z a b i j))
      (fun a b => hKH a b i j) hR (fun a b => hHdiff a b i j) hz
  exact ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius
    (X := X) (s := s) (δ := δ) (R := R)
    (KM := ∑ a, ∑ b, KM a b)
    (KD := ∑ a, ∑ b, ∑ c, KD a b c)
    (KH := fun i j => ∑ a, ∑ b, KH a b i j)
    (C := C) (DB := DB) (HB := HB)
    (M := M) (N := N) (D := D) (E := E) (H := H) (K := K)
    hDB hHB hMbound hNbound hDbound hEbound hKbound hKDsum hR
    hMdiff_bound hDdiff_bound hHdiff_bound hδpos hdetM hdetN

/-- Linear-radius bounded schematic Ricci-DeTurck RHS difference estimate from higher primitive
controls with coarser exported constants. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_higher_primitive_normLe_of_le
    {n : Type*} [Fintype n] [DecidableEq n]
    {δ R KM KD : ℝ} {KH : n → n → ℝ}
    {KM0 : n → n → ℝ} {KD0 : n → n → n → ℝ}
    {KH0 : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {M N : ℝ × X → Matrix n n ℝ}
    {D E : ℝ × X → n → n → n → ℝ}
    {H K : ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM0_nonneg : ∀ a b, 0 ≤ KM0 a b)
    (hKD0_nonneg : ∀ a b c, 0 ≤ KD0 a b c)
    (hKH0_nonneg : ∀ a b i j, 0 ≤ KH0 a b i j)
    (hKM_le : (∑ a, ∑ b, KM0 a b) ≤ KM)
    (hKD_le : (∑ a, ∑ b, ∑ c, KD0 a b c) ≤ KD)
    (hKH_le : ∀ i j, (∑ a, ∑ b, KH0 a b i j) ≤ KH i j)
    (hR : 0 ≤ R)
    (hM : ∀ a b, ParabolicC2AlphaNormLe (C a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC2AlphaNormLe (C a b) α (fun z => N z a b) s)
    (hD : ∀ a b c, ParabolicC2AlphaNormLe (DB a b c) α (fun z => D z a b c) s)
    (hE : ∀ a b c, ParabolicC2AlphaNormLe (DB a b c) α (fun z => E z a b c) s)
    (hK : ∀ a b i j, ParabolicC2AlphaNormLe (HB a b i j) α
      (fun z => K z a b i j) s)
    (hMdiff : ∀ a b, ParabolicC2AlphaNormLe (KM0 a b * R) α
      (fun z => M z a b - N z a b) s)
    (hDdiff : ∀ a b c, ParabolicC2AlphaNormLe (KD0 a b c * R) α
      (fun z => D z a b c - E z a b c) s)
    (hHdiff : ∀ a b i j, ParabolicC2AlphaNormLe (KH0 a b i j * R) α
      (fun z => H z a b i j - K z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicBoundedWith
      (ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ C DB HB KM KD KH * R)
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s := by
  have hbase :
      ParabolicBoundedWith
        (ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C DB HB
            (∑ a, ∑ b, KM0 a b)
            (∑ a, ∑ b, ∑ c, KD0 a b c)
            (fun i j => ∑ a, ∑ b, KH0 a b i j) * R)
        (fun z : ℝ × X =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
            ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s :=
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_higher_primitive_normLe
      (X := X) (α := α) (s := s) (δ := δ) (R := R)
      (KM := KM0) (KD := KD0) (KH := KH0)
      (C := C) (DB := DB) (HB := HB)
      (M := M) (N := N) (D := D) (E := E) (H := H) (K := K)
      hDB hHB hKM0_nonneg hKD0_nonneg hKH0_nonneg hR
      hM hN hD hE hK hMdiff hDdiff hHdiff hδpos hdetM hdetN
  exact hbase.mono_const
    (mul_le_mul_of_nonneg_right
      (ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_mono
        (𝕜 := ℝ) hδpos hDB hHB hKM_le hKD_le hKH_le)
      hR)

/-- Compact-coordinate readout Lipschitz bridge for a state-space vector field that agrees with
the schematic Ricci-DeTurck RHS on the state set.  The analytic input remains the higher primitive
entry control; the output is the finite compact-family readout used by parabolic chart estimates. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_higher_primitive_normLe
    {ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {δ : ℝ} {KM : n → n → ℝ} {KD : n → n → n → ℝ}
    {KH : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : ∀ a b, 0 ≤ KM a b) (hKD : ∀ a b c, 0 ≤ KD a b c)
    (hKH : ∀ a b i j, 0 ≤ KH a b i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z) (D u z) (H u z)) :
    LipschitzOnWith
      ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ C DB HB
          (∑ a, ∑ b, KM a b)
          (∑ a, ∑ b, ∑ c, KD a b c)
          (fun i j => ∑ a, ∑ b, KH a b i j),
        ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
          (𝕜 := ℝ) hδpos hDB hHB
          (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM a b)
          (Finset.sum_nonneg fun a _ha =>
            Finset.sum_nonneg fun b _hb =>
              Finset.sum_nonneg fun c _hc => hKD a b c)
          (fun i j =>
            Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb => hKH a b i j)⟩
      (fun u : Y =>
        parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u))
      stateSet := by
  refine parabolicC0AlphaSubmodule.lipschitzOnWith_toCompactCoordFamily_of_bounded_sub
    (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
    Kdom hKdom hα ?_
  intro u hu v hv
  have hraw :
      ParabolicBoundedWith
        (ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C DB HB
            (∑ a, ∑ b, KM a b)
            (∑ a, ∑ b, ∑ c, KD a b c)
            (fun i j => ∑ a, ∑ b, KH a b i j) * dist u v)
        (fun z : ℝ × X =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
              (M u z) (D u z) (H u z) -
            ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
              (M v z) (D v z) (H v z)) s :=
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_higher_primitive_normLe
      (X := X) (α := α) (s := s) (δ := δ) (R := dist u v)
      (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
      (M := M u) (N := M v) (D := D u) (E := D v) (H := H u) (K := H v)
      hDB hHB hKM hKD hKH dist_nonneg
      (hM hu) (hM hv) (hD hu) (hD hv) (hH hv)
      (hMdiff hu hv) (hDdiff hu hv) (hHdiff hu hv)
      hδpos (hdet hu) (hdet hv)
  intro z hz
  have hport := hraw hz
  simp [hAeq hu z, hAeq hv z] at hport ⊢
  exact hport

/-- Compact-coordinate readout Lipschitz bridge from higher primitive controls with coarser
exported constants.  Entrywise higher difference controls may use sharp constants, while the
finite compact readout is stated with any larger primitive constants. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_higher_primitive_normLe_of_le
    {ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {δ KM KD : ℝ} {KH : n → n → ℝ}
    {KM0 : n → n → ℝ} {KD0 : n → n → n → ℝ}
    {KH0 : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM0_nonneg : ∀ a b, 0 ≤ KM0 a b)
    (hKD0_nonneg : ∀ a b c, 0 ≤ KD0 a b c)
    (hKH0_nonneg : ∀ a b i j, 0 ≤ KH0 a b i j)
    (hKM_nonneg : 0 ≤ KM) (hKD_nonneg : 0 ≤ KD)
    (hKH_nonneg : ∀ i j, 0 ≤ KH i j)
    (hKM_le : (∑ a, ∑ b, KM0 a b) ≤ KM)
    (hKD_le : (∑ a, ∑ b, ∑ c, KD0 a b c) ≤ KD)
    (hKH_le : ∀ i j, (∑ a, ∑ b, KH0 a b i j) ≤ KH i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z) (D u z) (H u z)) :
    LipschitzOnWith
      ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ C DB HB KM KD KH,
        ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
          (𝕜 := ℝ) hδpos hDB hHB hKM_nonneg hKD_nonneg hKH_nonneg⟩
      (fun u : Y =>
        parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u))
      stateSet := by
  refine parabolicC0AlphaSubmodule.lipschitzOnWith_toCompactCoordFamily_of_bounded_sub
    (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
    Kdom hKdom hα ?_
  intro u hu v hv
  have hraw :
      ParabolicBoundedWith
        (ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C DB HB KM KD KH * dist u v)
        (fun z : ℝ × X =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
              (M u z) (D u z) (H u z) -
            ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
              (M v z) (D v z) (H v z)) s := by
    exact
      ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_higher_primitive_normLe_of_le
        (X := X) (α := α) (s := s) (δ := δ) (R := dist u v)
        (KM0 := KM0) (KD0 := KD0) (KH0 := KH0)
        (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
        (M := M u) (N := M v) (D := D u) (E := D v) (H := H u) (K := H v)
        hDB hHB hKM0_nonneg hKD0_nonneg hKH0_nonneg hKM_le hKD_le hKH_le
        dist_nonneg (hM hu) (hM hv) (hD hu) (hD hv) (hH hv)
        (hMdiff hu hv) (hDdiff hu hv) (hHdiff hu hv)
        hδpos (hdet hu) (hdet hv)
  intro z hz
  have hport := hraw hz
  simp [hAeq hu z, hAeq hv z] at hport ⊢
  exact hport

/-- Linear finite-cover readout version of
`ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_higher_primitive_normLe`.
This is definitionally the same compact-coordinate map, packaged as the linear readout used by
finite-product Banach chart handoffs. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamilyLinearMap_of_higher_primitive_normLe
    {ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {δ : ℝ} {KM : n → n → ℝ} {KD : n → n → n → ℝ}
    {KH : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : ∀ a b, 0 ≤ KM a b) (hKD : ∀ a b c, 0 ≤ KD a b c)
    (hKH : ∀ a b i j, 0 ≤ KH a b i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z) (D u z) (H u z)) :
    LipschitzOnWith
      ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ C DB HB
          (∑ a, ∑ b, KM a b)
          (∑ a, ∑ b, ∑ c, KD a b c)
          (fun i j => ∑ a, ∑ b, KH a b i j),
        ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
          (𝕜 := ℝ) hδpos hDB hHB
          (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM a b)
          (Finset.sum_nonneg fun a _ha =>
            Finset.sum_nonneg fun b _hb =>
              Finset.sum_nonneg fun c _hc => hKD a b c)
          (fun i j =>
            Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb => hKH a b i j)⟩
      (fun u : Y =>
        parabolicC0AlphaSubmodule.toCompactCoordFamilyLinearMap
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u))
      stateSet := by
  simpa using
    ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_higher_primitive_normLe
      (X := X) (α := α) (s := s) Kdom hKdom hα
      (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
      (stateSet := stateSet) (A := A) (M := M) (D := D) (H := H)
      hDB hHB hKM hKD hKH hM hD hH hMdiff hDdiff hHdiff hδpos hdet hAeq

/-- Linear finite-cover readout bridge from higher primitive controls with coarser exported
constants.  This is the linear-readout companion to
`ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_higher_primitive_normLe_of_le`. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamilyLinearMap_of_higher_primitive_normLe_of_le
    {ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {δ KM KD : ℝ} {KH : n → n → ℝ}
    {KM0 : n → n → ℝ} {KD0 : n → n → n → ℝ}
    {KH0 : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM0_nonneg : ∀ a b, 0 ≤ KM0 a b)
    (hKD0_nonneg : ∀ a b c, 0 ≤ KD0 a b c)
    (hKH0_nonneg : ∀ a b i j, 0 ≤ KH0 a b i j)
    (hKM_nonneg : 0 ≤ KM) (hKD_nonneg : 0 ≤ KD)
    (hKH_nonneg : ∀ i j, 0 ≤ KH i j)
    (hKM_le : (∑ a, ∑ b, KM0 a b) ≤ KM)
    (hKD_le : (∑ a, ∑ b, ∑ c, KD0 a b c) ≤ KD)
    (hKH_le : ∀ i j, (∑ a, ∑ b, KH0 a b i j) ≤ KH i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z) (D u z) (H u z)) :
    LipschitzOnWith
      ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ C DB HB KM KD KH,
        ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
          (𝕜 := ℝ) hδpos hDB hHB hKM_nonneg hKD_nonneg hKH_nonneg⟩
      (fun u : Y =>
        parabolicC0AlphaSubmodule.toCompactCoordFamilyLinearMap
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u))
      stateSet := by
  simpa using
    ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_higher_primitive_normLe_of_le
      (X := X) (α := α) (s := s) Kdom hKdom hα
      (KM0 := KM0) (KD0 := KD0) (KH0 := KH0)
      (KM := KM) (KD := KD) (KH := KH)
      (C := C) (DB := DB) (HB := HB)
      (stateSet := stateSet) (A := A) (M := M) (D := D) (H := H)
      hDB hHB hKM0_nonneg hKD0_nonneg hKH0_nonneg
      hKM_nonneg hKD_nonneg hKH_nonneg hKM_le hKD_le hKH_le
      hM hD hH hMdiff hDdiff hHdiff hδpos hdet hAeq

/-- Pointwise compact-coordinate distance estimate for the schematic Ricci-DeTurck RHS readout
from higher primitive controls with exact summed primitive constants. -/
theorem ricciDeTurckSchematicMatrix_compactCoord_dist_le_of_higher_primitive_normLe
    {ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {δ : ℝ} {KM : n → n → ℝ} {KD : n → n → n → ℝ}
    {KH : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : ∀ a b, 0 ≤ KM a b) (hKD : ∀ a b c, 0 ≤ KD a b c)
    (hKH : ∀ a b i j, 0 ≤ KH a b i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z) (D u z) (H u z)) :
    ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i (z : Kdom i),
      dist
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u) i z)
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A v) i z)
        ≤ ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C DB HB
            (∑ a, ∑ b, KM a b)
            (∑ a, ∑ b, ∑ c, KD a b c)
            (fun i j => ∑ a, ∑ b, KH a b i j) * dist u v := by
  have hLip :
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C DB HB
            (∑ a, ∑ b, KM a b)
            (∑ a, ∑ b, ∑ c, KD a b c)
            (fun i j => ∑ a, ∑ b, KH a b i j),
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos hDB hHB
            (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM a b)
            (Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb =>
              Finset.sum_nonneg fun c _hc => hKD a b c)
            (fun i j =>
              Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb => hKH a b i j)⟩
        (fun u : Y =>
          parabolicC0AlphaSubmodule.toCompactCoordFamily
            (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
            Kdom hKdom hα (A u))
        stateSet :=
    ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_higher_primitive_normLe
      (X := X) (α := α) (s := s) Kdom hKdom hα
      (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
      (stateSet := stateSet) (A := A) (M := M) (D := D) (H := H)
      hDB hHB hKM hKD hKH hM hD hH hMdiff hDdiff hHdiff hδpos hdet hAeq
  exact (parabolicC0AlphaSubmodule.forall_compactCoord_dist_le_of_toCompactCoordFamily_lipschitzOnWith
      (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
      Kdom hKdom hα hLip)

/-- Finite-family pointwise compact-coordinate distance estimates for schematic Ricci-DeTurck RHS
readouts from higher primitive controls with exact summed primitive constants. -/
theorem ricciDeTurckSchematicMatrix_compactCoord_dist_le_family_of_higher_primitive_normLe
    {κ ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {δ : ℝ} {KM : κ → n → n → ℝ} {KD : κ → n → n → n → ℝ}
    {KH : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : κ → Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r a b, 0 ≤ KM r a b)
    (hKD : ∀ r a b c, 0 ≤ KD r a b c)
    (hKH : ∀ r a b i j, 0 ≤ KH r a b i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A r u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M r u z) (D r u z) (H r u z)) :
    ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i (z : Kdom i),
      dist
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A r u) i z)
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A r v) i z)
        ≤ ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r) (DB r) (HB r)
            (∑ a, ∑ b, KM r a b)
            (∑ a, ∑ b, ∑ c, KD r a b c)
            (fun i j => ∑ a, ∑ b, KH r a b i j) * dist u v := by
  intro r
  exact ricciDeTurckSchematicMatrix_compactCoord_dist_le_of_higher_primitive_normLe
    (X := X) (α := α) (s := s) Kdom hKdom hα
    (KM := KM r) (KD := KD r) (KH := KH r)
    (C := C r) (DB := DB r) (HB := HB r)
    (stateSet := stateSet) (A := A r) (M := M r) (D := D r) (H := H r)
    (hDB r) (hHB r) (hKM r) (hKD r) (hKH r)
    (hM r) (hD r) (hH r) (hMdiff r) (hDdiff r) (hHdiff r)
    hδpos (hdet r) (hAeq r)

/-- Finite-family pointwise compact-coordinate distance estimates with one shared exact summed
schematic RHS constant across all family members. -/
theorem ricciDeTurckSchematicMatrix_compactCoord_dist_le_pi_family_of_higher_primitive_normLe
    {κ ι Y n : Type*} [Fintype κ] [Fintype ι] [PseudoMetricSpace Y]
    [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {δ : ℝ} {KM : κ → n → n → ℝ} {KD : κ → n → n → n → ℝ}
    {KH : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : κ → Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r a b, 0 ≤ KM r a b)
    (hKD : ∀ r a b c, 0 ≤ KD r a b c)
    (hKH : ∀ r a b i j, 0 ≤ KH r a b i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A r u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M r u z) (D r u z) (H r u z)) :
    ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ r i (z : Kdom i),
      dist
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A r u) i z)
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A r v) i z)
        ≤ (∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r) (DB r) (HB r)
            (∑ a, ∑ b, KM r a b)
            (∑ a, ∑ b, ∑ c, KD r a b c)
            (fun i j => ∑ a, ∑ b, KH r a b i j)) * dist u v := by
  let Kcoord : κ → ℝ := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ (C r) (DB r) (HB r)
      (∑ a, ∑ b, KM r a b)
      (∑ a, ∑ b, ∑ c, KD r a b c)
      (fun i j => ∑ a, ∑ b, KH r a b i j)
  have hKcoord_nonneg : ∀ r, 0 ≤ Kcoord r := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
      (𝕜 := ℝ) hδpos (hDB r) (hHB r)
      (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM r a b)
      (Finset.sum_nonneg fun a _ha =>
        Finset.sum_nonneg fun b _hb =>
        Finset.sum_nonneg fun c _hc => hKD r a b c)
      (fun i j =>
        Finset.sum_nonneg fun a _ha =>
        Finset.sum_nonneg fun b _hb => hKH r a b i j)
  intro u hu v hv r i z
  have hr :
      dist
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A r u) i z)
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A r v) i z)
        ≤ Kcoord r * dist u v := by
    simpa [Kcoord] using
      (ricciDeTurckSchematicMatrix_compactCoord_dist_le_family_of_higher_primitive_normLe
        (X := X) (α := α) (s := s) Kdom hKdom hα
        (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
        (stateSet := stateSet) (A := A) (M := M) (D := D) (H := H)
        hDB hHB hKM hKD hKH hM hD hH hMdiff hDdiff hHdiff hδpos hdet hAeq
        r hu hv i z)
  have hr_le_sum : Kcoord r ≤ ∑ r, Kcoord r :=
    Finset.single_le_sum (fun r' _hr' => hKcoord_nonneg r') (Finset.mem_univ r)
  exact hr.trans (mul_le_mul_of_nonneg_right hr_le_sum dist_nonneg)

/-- Fixed-time spatial readout estimate for the schematic Ricci-DeTurck RHS from higher primitive
controls with exact summed primitive constants, after the time-space compact pieces cover the
requested time slices. -/
theorem ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_of_higher_primitive_normLe
    {η ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    {δ : ℝ} {KM : n → n → ℝ} {KD : n → n → n → ℝ}
    {KH : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : ∀ a b, 0 ≤ KM a b) (hKD : ∀ a b c, 0 ≤ KD a b c)
    (hKH : ∀ a b i j, 0 ≤ KH a b i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z) (D u z) (H u z))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A u (τ, x.1)) (A v (τ, x.1)) ≤
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
              (𝕜 := ℝ) δ C DB HB
              (∑ a, ∑ b, KM a b)
              (∑ a, ∑ b, ∑ c, KD a b c)
              (fun i j => ∑ a, ∑ b, KH a b i j) * dist u v := by
  refine parabolicC0AlphaSubmodule.forall_timeSlice_spatial_dist_le_of_forall_compactCoord_dist_le
    (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _ u => A u)
    (K := ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ C DB HB
      (∑ a, ∑ b, KM a b)
      (∑ a, ∑ b, ∑ c, KD a b c)
      (fun i j => ∑ a, ∑ b, KH a b i j)) ?_ hcover
  intro _τ _hτ
  exact ricciDeTurckSchematicMatrix_compactCoord_dist_le_of_higher_primitive_normLe
    (X := X) (α := α) (s := s) Kdom hKdom hα
    (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
    (stateSet := stateSet) (A := A) (M := M) (D := D) (H := H)
    hDB hHB hKM hKD hKH hM hD hH hMdiff hDdiff hHdiff hδpos hdet hAeq

/-- Finite-family fixed-time spatial readout estimates for the schematic Ricci-DeTurck RHS from
higher primitive controls with exact summed primitive constants. -/
theorem ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_family_of_higher_primitive_normLe
    {κ η ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    {δ : ℝ} {KM : κ → n → n → ℝ} {KD : κ → n → n → n → ℝ}
    {KH : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : κ → Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r a b, 0 ≤ KM r a b)
    (hKD : ∀ r a b c, 0 ≤ KD r a b c)
    (hKH : ∀ r a b i j, 0 ≤ KH r a b i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A r u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M r u z) (D r u z) (H r u z))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ r τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A r u (τ, x.1)) (A r v (τ, x.1)) ≤
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
              (𝕜 := ℝ) δ (C r) (DB r) (HB r)
              (∑ a, ∑ b, KM r a b)
              (∑ a, ∑ b, ∑ c, KD r a b c)
              (fun i j => ∑ a, ∑ b, KH r a b i j) * dist u v := by
  intro r
  exact ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_of_higher_primitive_normLe
    (X := X) (α := α) (s := s) Kdom hKdom hα Kx
    (timeSet := timeSet)
    (KM := KM r) (KD := KD r) (KH := KH r)
    (C := C r) (DB := DB r) (HB := HB r)
    (stateSet := stateSet) (A := A r) (M := M r) (D := D r) (H := H r)
    (hDB r) (hHB r) (hKM r) (hKD r) (hKH r)
    (hM r) (hD r) (hH r) (hMdiff r) (hDdiff r) (hHdiff r)
    hδpos (hdet r) (hAeq r) hcover

/-- Finite-family fixed-time spatial readout estimates with one shared exact summed schematic RHS
constant across all family members. -/
theorem ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_pi_family_of_higher_primitive_normLe
    {κ η ι Y n : Type*} [Fintype κ] [Fintype ι] [PseudoMetricSpace Y]
    [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    {δ : ℝ} {KM : κ → n → n → ℝ} {KD : κ → n → n → n → ℝ}
    {KH : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : κ → Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r a b, 0 ≤ KM r a b)
    (hKD : ∀ r a b c, 0 ≤ KD r a b c)
    (hKH : ∀ r a b i j, 0 ≤ KH r a b i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A r u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M r u z) (D r u z) (H r u z))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ r i (x : Kx i),
        dist (A r u (τ, x.1)) (A r v (τ, x.1)) ≤
          (∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
              (𝕜 := ℝ) δ (C r) (DB r) (HB r)
              (∑ a, ∑ b, KM r a b)
              (∑ a, ∑ b, ∑ c, KD r a b c)
              (fun i j => ∑ a, ∑ b, KH r a b i j)) * dist u v := by
  intro τ hτ u hu v hv r i x
  refine parabolicC0AlphaSubmodule.forall_timeSlice_spatial_dist_le_of_forall_compactCoord_dist_le
    (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _ u => A r u)
    (K := (∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ (C r) (DB r) (HB r)
      (∑ a, ∑ b, KM r a b)
      (∑ a, ∑ b, ∑ c, KD r a b c)
      (fun i j => ∑ a, ∑ b, KH r a b i j))) ?_ hcover τ hτ hu hv i x
  intro _τ _hτ u hu v hv j z
  exact ricciDeTurckSchematicMatrix_compactCoord_dist_le_pi_family_of_higher_primitive_normLe
      (X := X) (α := α) (s := s) Kdom hKdom hα
      (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
      (stateSet := stateSet) (A := A) (M := M) (D := D) (H := H)
      hDB hHB hKM hKD hKH hM hD hH hMdiff hDdiff hHdiff hδpos hdet hAeq
      hu hv r j z

/-- Pointwise compact-coordinate distance estimate for the schematic Ricci-DeTurck RHS readout
from higher primitive controls with coarser exported constants.  This is the shape consumed by
preferred-cover chart constructors after the compact readout has been unpacked. -/
theorem ricciDeTurckSchematicMatrix_compactCoord_dist_le_of_higher_primitive_normLe_of_le
    {ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {δ KM KD : ℝ} {KH : n → n → ℝ}
    {KM0 : n → n → ℝ} {KD0 : n → n → n → ℝ}
    {KH0 : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM0_nonneg : ∀ a b, 0 ≤ KM0 a b)
    (hKD0_nonneg : ∀ a b c, 0 ≤ KD0 a b c)
    (hKH0_nonneg : ∀ a b i j, 0 ≤ KH0 a b i j)
    (hKM_nonneg : 0 ≤ KM) (hKD_nonneg : 0 ≤ KD)
    (hKH_nonneg : ∀ i j, 0 ≤ KH i j)
    (hKM_le : (∑ a, ∑ b, KM0 a b) ≤ KM)
    (hKD_le : (∑ a, ∑ b, ∑ c, KD0 a b c) ≤ KD)
    (hKH_le : ∀ i j, (∑ a, ∑ b, KH0 a b i j) ≤ KH i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z) (D u z) (H u z)) :
    ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i (z : Kdom i),
      dist
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u) i z)
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A v) i z)
        ≤ ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C DB HB KM KD KH * dist u v := by
  have hLip :
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C DB HB KM KD KH,
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos hDB hHB hKM_nonneg hKD_nonneg hKH_nonneg⟩
        (fun u : Y =>
          parabolicC0AlphaSubmodule.toCompactCoordFamily
            (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
            Kdom hKdom hα (A u))
        stateSet :=
    ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_higher_primitive_normLe_of_le
      (X := X) (α := α) (s := s) Kdom hKdom hα
      (KM0 := KM0) (KD0 := KD0) (KH0 := KH0)
      (KM := KM) (KD := KD) (KH := KH)
      (C := C) (DB := DB) (HB := HB)
      (stateSet := stateSet) (A := A) (M := M) (D := D) (H := H)
      hDB hHB hKM0_nonneg hKD0_nonneg hKH0_nonneg
      hKM_nonneg hKD_nonneg hKH_nonneg hKM_le hKD_le hKH_le
      hM hD hH hMdiff hDdiff hHdiff hδpos hdet hAeq
  exact (parabolicC0AlphaSubmodule.forall_compactCoord_dist_le_of_toCompactCoordFamily_lipschitzOnWith
      (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
      Kdom hKdom hα hLip)

/-- Finite-family pointwise compact-coordinate distance estimates for schematic Ricci-DeTurck RHS
readouts from higher primitive controls with coarser exported constants. -/
theorem ricciDeTurckSchematicMatrix_compactCoord_dist_le_family_of_higher_primitive_normLe_of_le
    {κ ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {δ : ℝ} {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {KM0 : κ → n → n → ℝ} {KD0 : κ → n → n → n → ℝ}
    {KH0 : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : κ → Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM0_nonneg : ∀ r a b, 0 ≤ KM0 r a b)
    (hKD0_nonneg : ∀ r a b c, 0 ≤ KD0 r a b c)
    (hKH0_nonneg : ∀ r a b i j, 0 ≤ KH0 r a b i j)
    (hKM_nonneg : ∀ r, 0 ≤ KM r) (hKD_nonneg : ∀ r, 0 ≤ KD r)
    (hKH_nonneg : ∀ r i j, 0 ≤ KH r i j)
    (hKM_le : ∀ r, (∑ a, ∑ b, KM0 r a b) ≤ KM r)
    (hKD_le : ∀ r, (∑ a, ∑ b, ∑ c, KD0 r a b c) ≤ KD r)
    (hKH_le : ∀ r i j, (∑ a, ∑ b, KH0 r a b i j) ≤ KH r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A r u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M r u z) (D r u z) (H r u z)) :
    ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i (z : Kdom i),
      dist
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A r u) i z)
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A r v) i z)
        ≤ ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r) * dist u v := by
  intro r
  exact ricciDeTurckSchematicMatrix_compactCoord_dist_le_of_higher_primitive_normLe_of_le
    (X := X) (α := α) (s := s) Kdom hKdom hα
    (KM0 := KM0 r) (KD0 := KD0 r) (KH0 := KH0 r)
    (KM := KM r) (KD := KD r) (KH := KH r)
    (C := C r) (DB := DB r) (HB := HB r)
    (stateSet := stateSet) (A := A r) (M := M r) (D := D r) (H := H r)
    (hDB r) (hHB r) (hKM0_nonneg r) (hKD0_nonneg r) (hKH0_nonneg r)
    (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)
    (hKM_le r) (hKD_le r) (hKH_le r)
    (hM r) (hD r) (hH r) (hMdiff r) (hDdiff r) (hHdiff r)
    hδpos (hdet r) (hAeq r)

/-- Finite-family pointwise compact-coordinate distance estimates with one shared summed
schematic RHS constant across all family members. -/
theorem ricciDeTurckSchematicMatrix_compactCoord_dist_le_pi_family_of_higher_primitive_normLe_of_le
    {κ ι Y n : Type*} [Fintype κ] [Fintype ι] [PseudoMetricSpace Y]
    [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {δ : ℝ} {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {KM0 : κ → n → n → ℝ} {KD0 : κ → n → n → n → ℝ}
    {KH0 : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : κ → Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM0_nonneg : ∀ r a b, 0 ≤ KM0 r a b)
    (hKD0_nonneg : ∀ r a b c, 0 ≤ KD0 r a b c)
    (hKH0_nonneg : ∀ r a b i j, 0 ≤ KH0 r a b i j)
    (hKM_nonneg : ∀ r, 0 ≤ KM r) (hKD_nonneg : ∀ r, 0 ≤ KD r)
    (hKH_nonneg : ∀ r i j, 0 ≤ KH r i j)
    (hKM_le : ∀ r, (∑ a, ∑ b, KM0 r a b) ≤ KM r)
    (hKD_le : ∀ r, (∑ a, ∑ b, ∑ c, KD0 r a b c) ≤ KD r)
    (hKH_le : ∀ r i j, (∑ a, ∑ b, KH0 r a b i j) ≤ KH r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A r u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M r u z) (D r u z) (H r u z)) :
    ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ r i (z : Kdom i),
      dist
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A r u) i z)
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A r v) i z)
        ≤ (∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r)) * dist u v := by
  let Kcoord : κ → ℝ := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r)
  have hKcoord_nonneg : ∀ r, 0 ≤ Kcoord r := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
      (𝕜 := ℝ) hδpos (hDB r) (hHB r)
      (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)
  intro u hu v hv r i z
  have hr :
      dist
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A r u) i z)
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A r v) i z)
        ≤ Kcoord r * dist u v := by
    simpa [Kcoord] using
      (ricciDeTurckSchematicMatrix_compactCoord_dist_le_family_of_higher_primitive_normLe_of_le
        (X := X) (α := α) (s := s) Kdom hKdom hα
        (KM0 := KM0) (KD0 := KD0) (KH0 := KH0)
        (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
        (stateSet := stateSet) (A := A) (M := M) (D := D) (H := H)
        hDB hHB hKM0_nonneg hKD0_nonneg hKH0_nonneg
        hKM_nonneg hKD_nonneg hKH_nonneg hKM_le hKD_le hKH_le
        hM hD hH hMdiff hDdiff hHdiff hδpos hdet hAeq r hu hv i z)
  have hr_le_sum : Kcoord r ≤ ∑ r, Kcoord r :=
    Finset.single_le_sum (fun r' _hr' => hKcoord_nonneg r') (Finset.mem_univ r)
  exact hr.trans (mul_le_mul_of_nonneg_right hr_le_sum dist_nonneg)

/-- Fixed-time spatial readout estimate for the schematic Ricci-DeTurck RHS from higher primitive
controls with coarser exported constants, after the time-space compact pieces cover the requested
time slices. -/
theorem ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_of_higher_primitive_normLe_of_le
    {η ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    {δ KM KD : ℝ} {KH : n → n → ℝ}
    {KM0 : n → n → ℝ} {KD0 : n → n → n → ℝ}
    {KH0 : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM0_nonneg : ∀ a b, 0 ≤ KM0 a b)
    (hKD0_nonneg : ∀ a b c, 0 ≤ KD0 a b c)
    (hKH0_nonneg : ∀ a b i j, 0 ≤ KH0 a b i j)
    (hKM_nonneg : 0 ≤ KM) (hKD_nonneg : 0 ≤ KD)
    (hKH_nonneg : ∀ i j, 0 ≤ KH i j)
    (hKM_le : (∑ a, ∑ b, KM0 a b) ≤ KM)
    (hKD_le : (∑ a, ∑ b, ∑ c, KD0 a b c) ≤ KD)
    (hKH_le : ∀ i j, (∑ a, ∑ b, KH0 a b i j) ≤ KH i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z) (D u z) (H u z))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A u (τ, x.1)) (A v (τ, x.1)) ≤
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
              (𝕜 := ℝ) δ C DB HB KM KD KH * dist u v := by
  refine parabolicC0AlphaSubmodule.forall_timeSlice_spatial_dist_le_of_forall_compactCoord_dist_le
    (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _ u => A u)
    (K := ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ C DB HB KM KD KH) ?_ hcover
  intro _τ _hτ
  exact ricciDeTurckSchematicMatrix_compactCoord_dist_le_of_higher_primitive_normLe_of_le
    (X := X) (α := α) (s := s) Kdom hKdom hα
    (KM0 := KM0) (KD0 := KD0) (KH0 := KH0)
    (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
    (stateSet := stateSet) (A := A) (M := M) (D := D) (H := H)
    hDB hHB hKM0_nonneg hKD0_nonneg hKH0_nonneg
    hKM_nonneg hKD_nonneg hKH_nonneg hKM_le hKD_le hKH_le
    hM hD hH hMdiff hDdiff hHdiff hδpos hdet hAeq

/-- Finite-family fixed-time spatial readout estimates for the schematic Ricci-DeTurck RHS from
higher primitive controls with coarser exported constants. -/
theorem ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_family_of_higher_primitive_normLe_of_le
    {κ η ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    {δ : ℝ} {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {KM0 : κ → n → n → ℝ} {KD0 : κ → n → n → n → ℝ}
    {KH0 : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : κ → Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM0_nonneg : ∀ r a b, 0 ≤ KM0 r a b)
    (hKD0_nonneg : ∀ r a b c, 0 ≤ KD0 r a b c)
    (hKH0_nonneg : ∀ r a b i j, 0 ≤ KH0 r a b i j)
    (hKM_nonneg : ∀ r, 0 ≤ KM r) (hKD_nonneg : ∀ r, 0 ≤ KD r)
    (hKH_nonneg : ∀ r i j, 0 ≤ KH r i j)
    (hKM_le : ∀ r, (∑ a, ∑ b, KM0 r a b) ≤ KM r)
    (hKD_le : ∀ r, (∑ a, ∑ b, ∑ c, KD0 r a b c) ≤ KD r)
    (hKH_le : ∀ r i j, (∑ a, ∑ b, KH0 r a b i j) ≤ KH r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A r u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M r u z) (D r u z) (H r u z))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ r τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A r u (τ, x.1)) (A r v (τ, x.1)) ≤
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
              (𝕜 := ℝ) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r) * dist u v := by
  intro r
  exact ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_of_higher_primitive_normLe_of_le
    (X := X) (α := α) (s := s) Kdom hKdom hα Kx
    (timeSet := timeSet)
    (KM0 := KM0 r) (KD0 := KD0 r) (KH0 := KH0 r)
    (KM := KM r) (KD := KD r) (KH := KH r)
    (C := C r) (DB := DB r) (HB := HB r)
    (stateSet := stateSet) (A := A r) (M := M r) (D := D r) (H := H r)
    (hDB r) (hHB r) (hKM0_nonneg r) (hKD0_nonneg r) (hKH0_nonneg r)
    (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)
    (hKM_le r) (hKD_le r) (hKH_le r)
    (hM r) (hD r) (hH r) (hMdiff r) (hDdiff r) (hHdiff r)
    hδpos (hdet r) (hAeq r) hcover

/-- Finite-family fixed-time spatial readout estimates with one shared coarser schematic RHS
constant across all family members. -/
theorem ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_pi_family_of_higher_primitive_normLe_of_le
    {κ η ι Y n : Type*} [Fintype κ] [Fintype ι] [PseudoMetricSpace Y]
    [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    {δ : ℝ} {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {KM0 : κ → n → n → ℝ} {KD0 : κ → n → n → n → ℝ}
    {KH0 : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : κ → Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM0_nonneg : ∀ r a b, 0 ≤ KM0 r a b)
    (hKD0_nonneg : ∀ r a b c, 0 ≤ KD0 r a b c)
    (hKH0_nonneg : ∀ r a b i j, 0 ≤ KH0 r a b i j)
    (hKM_nonneg : ∀ r, 0 ≤ KM r) (hKD_nonneg : ∀ r, 0 ≤ KD r)
    (hKH_nonneg : ∀ r i j, 0 ≤ KH r i j)
    (hKM_le : ∀ r, (∑ a, ∑ b, KM0 r a b) ≤ KM r)
    (hKD_le : ∀ r, (∑ a, ∑ b, ∑ c, KD0 r a b c) ≤ KD r)
    (hKH_le : ∀ r i j, (∑ a, ∑ b, KH0 r a b i j) ≤ KH r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A r u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M r u z) (D r u z) (H r u z))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ r i (x : Kx i),
        dist (A r u (τ, x.1)) (A r v (τ, x.1)) ≤
          (∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
              (𝕜 := ℝ) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r)) *
            dist u v := by
  intro τ hτ u hu v hv r i x
  refine parabolicC0AlphaSubmodule.forall_timeSlice_spatial_dist_le_of_forall_compactCoord_dist_le
    (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _ u => A r u)
    (K := (∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r))) ?_ hcover
    τ hτ hu hv i x
  intro _τ _hτ u hu v hv j z
  exact ricciDeTurckSchematicMatrix_compactCoord_dist_le_pi_family_of_higher_primitive_normLe_of_le
      (X := X) (α := α) (s := s) Kdom hKdom hα
      (KM0 := KM0) (KD0 := KD0) (KH0 := KH0)
      (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
      (stateSet := stateSet) (A := A) (M := M) (D := D) (H := H)
      hDB hHB hKM0_nonneg hKD0_nonneg hKH0_nonneg
      hKM_nonneg hKD_nonneg hKH_nonneg hKM_le hKD_le hKH_le
      hM hD hH hMdiff hDdiff hHdiff hδpos hdet hAeq hu hv r j z

/-- Higher parabolic entry controls supply the primitive entrywise hypotheses for the
single-radius schematic Ricci-DeTurck RHS difference estimate. -/
theorem ricciDeTurckSchematicMatrix_sub_entrywise_of_entries {n : Type*}
    [Fintype n] [DecidableEq n]
    {R Rd : n → n → ℝ} {RD RDd : n → n → n → ℝ}
    {RH RHd : n → n → n → n → ℝ} {δ : ℝ}
    {M N : ℝ × X → Matrix n n ℝ}
    {D E : ℝ × X → n → n → n → ℝ}
    {H K : ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ a b, ParabolicC2AlphaNormLe (R a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC2AlphaNormLe (R a b) α (fun z => N z a b) s)
    (hMdiff : ∀ a b, ParabolicC2AlphaNormLe (Rd a b) α
      (fun z => M z a b - N z a b) s)
    (hD : ∀ a b c, ParabolicC2AlphaNormLe (RD a b c) α (fun z => D z a b c) s)
    (hE : ∀ a b c, ParabolicC2AlphaNormLe (RD a b c) α (fun z => E z a b c) s)
    (hDdiff : ∀ a b c, ParabolicC2AlphaNormLe (RDd a b c) α
      (fun z => D z a b c - E z a b c) s)
    (hK : ∀ a b i j, ParabolicC2AlphaNormLe (RH a b i j) α
      (fun z => K z a b i j) s)
    (hHdiff : ∀ a b i j, ParabolicC2AlphaNormLe (RHd a b i j) α
      (fun z => H z a b i j - K z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.ricciDeTurckSchematicEntrywiseSubBoundConst
          (𝕜 := ℝ) δ R Rd RD RDd RH RHd +
        ParabolicC0AlphaOn.ricciDeTurckSchematicEntrywiseSubHolderConst
          (𝕜 := ℝ) δ R R Rd Rd RD RD RDd RDd RH RH RHd RHd)
      α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s := by
  exact ParabolicC0AlphaNormLe.ricciDeTurckSchematicMatrix_sub_entrywise_of_entries
    (M := M) (N := N) (D := D) (E := E) (H := H) (K := K)
    (R := R) (Rd := Rd) (RD := RD) (RDd := RDd) (RH := RH) (RHd := RHd)
    (fun a b => (hM a b).value_c0AlphaNormLe_self)
    (fun a b => (hN a b).value_c0AlphaNormLe_self)
    (fun a b => (hMdiff a b).value_c0AlphaNormLe_self)
    (fun a b c => (hD a b c).value_c0AlphaNormLe_self)
    (fun a b c => (hE a b c).value_c0AlphaNormLe_self)
    (fun a b c => (hDdiff a b c).value_c0AlphaNormLe_self)
    (fun a b i j => (hK a b i j).value_c0AlphaNormLe_self)
    (fun a b i j => (hHdiff a b i j).value_c0AlphaNormLe_self)
    hδpos hdetM hdetN

/-- State-space Lipschitz bridge for the schematic Ricci-DeTurck RHS from higher parabolic
primitive controls.  Uniform higher norm balls give the pointwise primitive bounds, while
pairwise higher norm balls with radii linear in `dist u v` give the primitive difference
estimates consumed by the existing matrix `C^{0,α}` Lipschitz theorem. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_of_higher_primitive_normLe
    {Y n : Type*} [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    {δ : ℝ} {KM : n → n → ℝ} {KD : n → n → n → ℝ}
    {KH : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : ∀ a b, 0 ≤ KM a b) (hKD : ∀ a b c, 0 ≤ KD a b c)
    (hKH : ∀ a b i j, 0 ≤ KH a b i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C DB HB
            (∑ a, ∑ b, KM a b)
            (∑ a, ∑ b, ∑ c, KD a b c)
            (fun i j => ∑ a, ∑ b, KH a b i j),
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos hDB hHB
            (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM a b)
            (Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb =>
                Finset.sum_nonneg fun c _hc => hKD a b c)
            (fun i j =>
              Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb => hKH a b i j)⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M u z) (D u z) (H u z))
        stateSet := by
  have hKMsum : 0 ≤ ∑ a, ∑ b, KM a b :=
    Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM a b
  have hKDsum : 0 ≤ ∑ a, ∑ b, ∑ c, KD a b c :=
    Finset.sum_nonneg fun a _ha =>
      Finset.sum_nonneg fun b _hb => Finset.sum_nonneg fun c _hc => hKD a b c
  have hKHsum : ∀ i j, 0 ≤ ∑ a, ∑ b, KH a b i j := fun i j =>
    Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKH a b i j
  have hMbound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b,
      ‖M u z a b‖ ≤ C a b := by
    intro u hu z hz a b
    exact (hM hu a b).norm_le hz
  have hDbound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D u z a b c‖ ≤ DB a b c := by
    intro u hu z hz a b c
    exact (hD hu a b c).norm_le hz
  have hHbound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j,
      ‖H u z a b i j‖ ≤ HB a b i j := by
    intro u hu z hz a b i j
    exact (hH hu a b i j).norm_le hz
  have hMdiff_bound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s →
        ‖M u z - M v z‖ ≤ (∑ a, ∑ b, KM a b) * dist u v := by
    intro u hu v hv z hz
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := KM) (M := M u) (N := M v)
      hKM dist_nonneg (hMdiff hu hv) hz
  have hDdiff_bound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
        ‖D u z a b c - D v z a b c‖ ≤
          (∑ a, ∑ b, ∑ c, KD a b c) * dist u v := by
    intro u hu v hv z hz a b c
    have hentry : ‖D u z a b c - D v z a b c‖ ≤ KD a b c * dist u v := by
      simpa [dist_eq_norm] using (hDdiff hu hv a b c).dist_le_of_sub hz
    exact hentry.trans
      (mul_le_mul_of_nonneg_right (entry_le_triple_sum hKD a b c) dist_nonneg)
  have hHdiff_bound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
        ‖((fun a b => H u z a b i j) : Matrix n n ℝ) -
          ((fun a b => H v z a b i j) : Matrix n n ℝ)‖ ≤
            (∑ a, ∑ b, KH a b i j) * dist u v := by
    intro u hu v hv z hz i j
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := fun a b => KH a b i j)
      (M := fun z : ℝ × X => (fun a b => H u z a b i j))
      (N := fun z : ℝ × X => (fun a b => H v z a b i j))
      (fun a b => hKH a b i j) dist_nonneg (fun a b => hHdiff hu hv a b i j) hz
  exact ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix_lipschitzOnWith_of_primitive_dist_le
    (X := X) (s := s) (δ := δ) (C := C) (DB := DB) (HB := HB)
    (KM := ∑ a, ∑ b, KM a b)
    (KD := ∑ a, ∑ b, ∑ c, KD a b c)
    (KH := fun i j => ∑ a, ∑ b, KH a b i j)
    (stateSet := stateSet) (M := M) (D := D) (H := H)
    hDB hHB hKMsum hKDsum hKHsum
    hMbound hDbound hHbound hMdiff_bound hDdiff_bound hHdiff_bound hδpos hdet

/-- State-space Lipschitz bridge for the schematic Ricci-DeTurck RHS when the first- and
second-derivative primitives are read from caller-supplied second jets of the metric entries.
Unique-differentiability of the time and spatial slices transports the higher norm-ball controls
to those chosen jets. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_of_metric_entries_directions_of_unique
    {Y n : Type*} [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (ξ : n → X)
    {δ : ℝ} {C KM : n → n → ℝ} {stateSet : Set Y}
    {M : Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M u z i j) s)
    (hC : ∀ i j, 0 ≤ C i j) (hKM : ∀ i j, 0 ≤ KM i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C i j) α (fun z => M u z i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM i j * dist u v) α
        (fun z => M u z i j - M v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C
            (firstDerivativeVectorRadius (X := X) ξ C)
            (secondDerivativeVectorRadius (X := X) ξ C)
            (∑ i, ∑ j, KM i j)
            (∑ a, ∑ i, ∑ j, firstDerivativeVectorRadius (X := X) ξ KM a i j)
            (fun i j => ∑ a, ∑ b,
              secondDerivativeVectorRadius (X := X) ξ KM a b i j),
          by
            exact ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
              (𝕜 := ℝ) hδpos
              (firstDerivativeVectorRadius_nonneg (X := X) ξ hC)
              (secondDerivativeVectorRadius_nonneg (X := X) ξ hC)
              (Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hKM i j)
              (Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun i _hi =>
                  Finset.sum_nonneg fun j _hj =>
                    firstDerivativeVectorRadius_nonneg (X := X) ξ hKM a i j)
              (fun i j =>
                Finset.sum_nonneg fun a _ha =>
                  Finset.sum_nonneg fun b _hb =>
                    secondDerivativeVectorRadius_nonneg (X := X) ξ hKM a b i j)⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M u z)
          (fun a i j => (J u i j).spaceDeriv z (ξ a))
          (fun a b i j => (J u i j).spaceSecondDeriv z (ξ a) (ξ b)))
        stateSet := by
  have hDB_nonneg :
      ∀ a i j, 0 ≤ firstDerivativeVectorRadius (X := X) ξ C a i j :=
    firstDerivativeVectorRadius_nonneg (X := X) ξ hC
  have hHB_nonneg :
      ∀ a b i j, 0 ≤ secondDerivativeVectorRadius (X := X) ξ C a b i j :=
    secondDerivativeVectorRadius_nonneg (X := X) ξ hC
  have hKMsum : 0 ≤ ∑ i, ∑ j, KM i j :=
    Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hKM i j
  have hKDentry_nonneg :
      ∀ a i j, 0 ≤ firstDerivativeVectorRadius (X := X) ξ KM a i j :=
    firstDerivativeVectorRadius_nonneg (X := X) ξ hKM
  have hKDsum :
      0 ≤ ∑ a, ∑ i, ∑ j, firstDerivativeVectorRadius (X := X) ξ KM a i j :=
    Finset.sum_nonneg fun a _ha =>
      Finset.sum_nonneg fun i _hi =>
        Finset.sum_nonneg fun j _hj => hKDentry_nonneg a i j
  have hKHentry_nonneg :
      ∀ a b i j, 0 ≤ secondDerivativeVectorRadius (X := X) ξ KM a b i j :=
    secondDerivativeVectorRadius_nonneg (X := X) ξ hKM
  have hKHsum :
      ∀ i j, 0 ≤ ∑ a, ∑ b, secondDerivativeVectorRadius (X := X) ξ KM a b i j :=
    fun i j =>
      Finset.sum_nonneg fun a _ha =>
        Finset.sum_nonneg fun b _hb => hKHentry_nonneg a b i j
  refine ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix_lipschitzOnWith_of_primitive_dist_le
    (X := X) (s := s) (δ := δ) (C := C)
    (DB := firstDerivativeVectorRadius (X := X) ξ C)
    (HB := secondDerivativeVectorRadius (X := X) ξ C)
    (KM := ∑ i, ∑ j, KM i j)
    (KD := ∑ a, ∑ i, ∑ j, firstDerivativeVectorRadius (X := X) ξ KM a i j)
    (KH := fun i j => ∑ a, ∑ b,
      secondDerivativeVectorRadius (X := X) ξ KM a b i j)
    (stateSet := stateSet) (M := M)
    (D := fun u z a i j => (J u i j).spaceDeriv z (ξ a))
    (H := fun u z a b i j => (J u i j).spaceSecondDeriv z (ξ a) (ξ b))
    hDB_nonneg hHB_nonneg hKMsum hKDsum hKHsum ?_ ?_ ?_ ?_ ?_ ?_ hδpos hdet
  · intro u hu z hz i j
    exact (hM hu i j).norm_le hz
  · intro u hu z hz a i j
    have hctrl := (hM hu i j).secondJet_c0AlphaNormLe_self_of_unique
      (J u i j) htime hspace
    have hread := hctrl.2.1.continuousLinearMap
      (firstDerivativeVectorReadout (X := X) (E := ℝ) (ξ a))
    have hport := hread.norm_le hz
    simp [firstDerivativeVectorRadius, firstDerivativeVectorReadoutOpNorm] at hport ⊢
    exact hport
  · intro u hu z hz a b i j
    have hctrl := (hM hu i j).secondJet_c0AlphaNormLe_self_of_unique
      (J u i j) htime hspace
    have hread := hctrl.2.2.1.continuousLinearMap
      (secondDerivativeVectorReadout (X := X) (E := ℝ) (ξ a) (ξ b))
    have hport := hread.norm_le hz
    simp [secondDerivativeVectorRadius, secondDerivativeVectorReadoutOpNorm] at hport ⊢
    exact hport
  · intro u hu v hv z hz
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := KM) (M := M u) (N := M v)
      hKM dist_nonneg (hMdiff hu hv) hz
  · intro u hu v hv z hz a i j
    have hctrl := (hMdiff hu hv i j).secondJet_sub_c0AlphaNormLe_self_of_unique
      (J u i j) (J v i j) htime hspace
    have hread := hctrl.2.1.continuousLinearMap
      (firstDerivativeVectorReadout (X := X) (E := ℝ) (ξ a))
    have hentry :
        ‖(J u i j).spaceDeriv z (ξ a) - (J v i j).spaceDeriv z (ξ a)‖ ≤
          firstDerivativeVectorRadius (X := X) ξ KM a i j * dist u v := by
      have hport := hread.norm_le hz
      simp [firstDerivativeVectorRadius, firstDerivativeVectorReadoutOpNorm, mul_assoc] at hport ⊢
      exact hport
    exact hentry.trans
      (mul_le_mul_of_nonneg_right
        (entry_le_triple_sum hKDentry_nonneg a i j) dist_nonneg)
  · intro u hu v hv z hz i j
    have htarget_nonneg :
        0 ≤ (∑ a, ∑ b, secondDerivativeVectorRadius (X := X) ξ KM a b i j) *
          dist u v :=
      mul_nonneg (hKHsum i j) dist_nonneg
    refine (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun b => ?_
    have hctrl := (hMdiff hu hv i j).secondJet_sub_c0AlphaNormLe_self_of_unique
      (J u i j) (J v i j) htime hspace
    have hread := hctrl.2.2.1.continuousLinearMap
      (secondDerivativeVectorReadout (X := X) (E := ℝ) (ξ a) (ξ b))
    have hentry :
        ‖(J u i j).spaceSecondDeriv z (ξ a) (ξ b) -
          (J v i j).spaceSecondDeriv z (ξ a) (ξ b)‖ ≤
          secondDerivativeVectorRadius (X := X) ξ KM a b i j * dist u v := by
      have hport := hread.norm_le hz
      simp [secondDerivativeVectorRadius, secondDerivativeVectorReadoutOpNorm,
        Pi.sub_apply, mul_assoc] at hport ⊢
      exact hport
    have hentry_le_sum :
        secondDerivativeVectorRadius (X := X) ξ KM a b i j ≤
          ∑ a, ∑ b, secondDerivativeVectorRadius (X := X) ξ KM a b i j := by
      have hentry_le_b :
          secondDerivativeVectorRadius (X := X) ξ KM a b i j ≤
            ∑ b, secondDerivativeVectorRadius (X := X) ξ KM a b i j :=
        Finset.single_le_sum (fun b' _hb' => hKHentry_nonneg a b' i j)
          (Finset.mem_univ b)
      have hb_le_a :
          (∑ b, secondDerivativeVectorRadius (X := X) ξ KM a b i j) ≤
            ∑ a, ∑ b, secondDerivativeVectorRadius (X := X) ξ KM a b i j :=
        Finset.single_le_sum
          (fun a' _ha' => Finset.sum_nonneg fun b' _hb' => hKHentry_nonneg a' b' i j)
          (Finset.mem_univ a)
      exact hentry_le_b.trans hb_le_a
    exact hentry.trans (mul_le_mul_of_nonneg_right hentry_le_sum dist_nonneg)

/-- Coordinate-space version of
`ricciDeTurckSchematicMatrix_lipschitzOnWith_of_metric_entries_directions_of_unique`.
The first- and second-derivative primitive radii are stated with the coordinate-radius API. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_of_metric_entries_of_unique
    {Y n : Type*} [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    {s : Set (ℝ × (n → ℝ))}
    {δ : ℝ} {C KM : n → n → ℝ} {stateSet : Set Y}
    {M : Y → ℝ × (n → ℝ) → Matrix n n ℝ}
    (J : ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × (n → ℝ) => M u z i j) s)
    (hC : ∀ i j, 0 ≤ C i j) (hKM : ∀ i j, 0 ≤ KM i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C i j) α (fun z => M u z i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM i j * dist u v) α
        (fun z => M u z i j - M v z i j) s)
    (htime : ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖) :
    ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C
            (firstDerivativeCoordinateRadius (n := n) C)
            (secondDerivativeCoordinateRadius (n := n) C)
            (∑ i, ∑ j, KM i j)
            (∑ a, ∑ i, ∑ j, firstDerivativeCoordinateRadius (n := n) KM a i j)
            (fun i j => ∑ a, ∑ b,
              secondDerivativeCoordinateRadius (n := n) KM a b i j),
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos
            (firstDerivativeCoordinateRadius_nonneg hC)
            (secondDerivativeCoordinateRadius_nonneg hC)
            (Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hKM i j)
            (Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun i _hi =>
                Finset.sum_nonneg fun j _hj =>
                  firstDerivativeCoordinateRadius_nonneg hKM a i j)
            (fun i j =>
              Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb =>
                  secondDerivativeCoordinateRadius_nonneg hKM a b i j)⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M u z)
          (fun a i j => (J u i j).spaceDeriv z (parabolicCoordinateUnitVector n a))
          (fun a b i j => (J u i j).spaceSecondDeriv z
            (parabolicCoordinateUnitVector n a) (parabolicCoordinateUnitVector n b)))
        stateSet := by
  simpa using
    ricciDeTurckSchematicMatrix_lipschitzOnWith_of_metric_entries_directions_of_unique
      (X := n → ℝ) (α := α) (s := s)
      (ξ := parabolicCoordinateUnitVector n)
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (M := M) J hC hKM hM hMdiff htime hspace hδpos hdet

/-- Finite-family state-space Lipschitz bridge for the schematic Ricci-DeTurck RHS when each
family member reads first- and second-derivative primitives from its own supplied metric-entry
second jets and finite direction family. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_metric_entries_family_directions_of_unique
    {κ Y n : Type*} [Fintype κ] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (ξ : κ → n → X)
    {δ : ℝ} {C KM : κ → n → n → ℝ} {stateSet : Set Y}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ r : κ, ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M r u z i j) s)
    (hC : ∀ r i j, 0 ≤ C r i j) (hKM : ∀ r i j, 0 ≤ KM r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C r i j) α (fun z => M r u z i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM r i j * dist u v) α
        (fun z => M r u z i j - M r v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ r ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r)
            (firstDerivativeVectorRadius (X := X) (ξ r) (C r))
            (secondDerivativeVectorRadius (X := X) (ξ r) (C r))
            (∑ i, ∑ j, KM r i j)
            (∑ a, ∑ i, ∑ j,
              firstDerivativeVectorRadius (X := X) (ξ r) (KM r) a i j)
            (fun i j => ∑ a, ∑ b,
              secondDerivativeVectorRadius (X := X) (ξ r) (KM r) a b i j),
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos
            (firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
            (secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
            (Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hKM r i j)
            (Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun i _hi =>
                Finset.sum_nonneg fun j _hj =>
                  firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r) a i j)
            (fun i j =>
              Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb =>
                  secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r) a b i j)⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z)
          (fun a i j => (J r u i j).spaceDeriv z (ξ r a))
          (fun a b i j => (J r u i j).spaceSecondDeriv z (ξ r a) (ξ r b)))
        stateSet := by
  intro r z hz
  exact ricciDeTurckSchematicMatrix_lipschitzOnWith_of_metric_entries_directions_of_unique
    (X := X) (α := α) (s := s) (ξ r)
    (δ := δ) (C := C r) (KM := KM r) (stateSet := stateSet)
    (M := M r) (J r) (hC r) (hKM r) (hM r) (hMdiff r)
    htime hspace hδpos (hdet r) hz

/-- Pi-valued finite-family state-space Lipschitz bridge for chosen-jet schematic
Ricci-DeTurck RHS coordinates.  The exported Lipschitz constant is the finite sum of the
memberwise chosen-jet schematic constants. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_pi_family_of_metric_entries_family_directions_of_unique
    {κ Y n : Type*} [Fintype κ] [DecidableEq κ] [PseudoMetricSpace Y]
    [Fintype n] [DecidableEq n]
    (ξ : κ → n → X)
    {δ : ℝ} {C KM : κ → n → n → ℝ} {stateSet : Set Y}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ r : κ, ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M r u z i j) s)
    (hC : ∀ r i j, 0 ≤ C r i j) (hKM : ∀ r i j, 0 ≤ KM r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C r i j) α (fun z => M r u z i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM r i j * dist u v) α
        (fun z => M r u z i j - M r v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r)
            (firstDerivativeVectorRadius (X := X) (ξ r) (C r))
            (secondDerivativeVectorRadius (X := X) (ξ r) (C r))
            (∑ i, ∑ j, KM r i j)
            (∑ a, ∑ i, ∑ j,
              firstDerivativeVectorRadius (X := X) (ξ r) (KM r) a i j)
            (fun i j => ∑ a, ∑ b,
              secondDerivativeVectorRadius (X := X) (ξ r) (KM r) a b i j),
          Finset.sum_nonneg fun r _hr =>
            ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
              (𝕜 := ℝ) hδpos
              (firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
              (secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
              (Finset.sum_nonneg fun i _hi =>
                Finset.sum_nonneg fun j _hj => hKM r i j)
              (Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun i _hi =>
                  Finset.sum_nonneg fun j _hj =>
                    firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r) a i j)
              (fun i j =>
                Finset.sum_nonneg fun a _ha =>
                  Finset.sum_nonneg fun b _hb =>
                    secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r)
                      a b i j)⟩
        (fun u : Y => fun r =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M r u z)
            (fun a i j => (J r u i j).spaceDeriv z (ξ r a))
            (fun a b i j => (J r u i j).spaceSecondDeriv z (ξ r a) (ξ r b)))
        stateSet := by
  intro z hz
  let Kcoord : κ → ℝ := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ (C r)
      (firstDerivativeVectorRadius (X := X) (ξ r) (C r))
      (secondDerivativeVectorRadius (X := X) (ξ r) (C r))
      (∑ i, ∑ j, KM r i j)
      (∑ a, ∑ i, ∑ j,
        firstDerivativeVectorRadius (X := X) (ξ r) (KM r) a i j)
      (fun i j => ∑ a, ∑ b,
        secondDerivativeVectorRadius (X := X) (ξ r) (KM r) a b i j)
  have hKcoord_nonneg : ∀ r, 0 ≤ Kcoord r := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
      (𝕜 := ℝ) hδpos
      (firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
      (secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
      (Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hKM r i j)
      (Finset.sum_nonneg fun a _ha =>
        Finset.sum_nonneg fun i _hi =>
          Finset.sum_nonneg fun j _hj =>
            firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r) a i j)
      (fun i j =>
        Finset.sum_nonneg fun a _ha =>
          Finset.sum_nonneg fun b _hb =>
            secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r) a b i j)
  have hcoord : ∀ r,
      LipschitzOnWith
        ⟨Kcoord r, hKcoord_nonneg r⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z)
          (fun a i j => (J r u i j).spaceDeriv z (ξ r a))
          (fun a b i j => (J r u i j).spaceSecondDeriv z (ξ r a) (ξ r b)))
        stateSet := by
    intro r
    exact ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_metric_entries_family_directions_of_unique
      (X := X) (α := α) (s := s) ξ
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (M := M) J hC hKM hM hMdiff htime hspace hδpos hdet r hz
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hsum_nonneg : 0 ≤ ∑ r, Kcoord r :=
    Finset.sum_nonneg fun r _hr => hKcoord_nonneg r
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hsum_nonneg dist_nonneg)).2 fun r => ?_
  have hr := (hcoord r).dist_le_mul u hu v hv
  have hr_le_sum : Kcoord r ≤ ∑ r, Kcoord r :=
    Finset.single_le_sum (fun r' _hr' => hKcoord_nonneg r') (Finset.mem_univ r)
  have hentry :
      ‖ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z)
          (fun a i j => (J r u i j).spaceDeriv z (ξ r a))
          (fun a b i j => (J r u i j).spaceSecondDeriv z (ξ r a) (ξ r b)) -
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r v z)
          (fun a i j => (J r v i j).spaceDeriv z (ξ r a))
          (fun a b i j => (J r v i j).spaceSecondDeriv z (ξ r a) (ξ r b))‖ ≤
        Kcoord r * dist u v := by
    have hport := hr
    simp [dist_eq_norm] at hport ⊢
    exact hport
  exact hentry.trans (mul_le_mul_of_nonneg_right hr_le_sum dist_nonneg)

/-- Compact-coordinate readout Lipschitz bridge for the schematic Ricci-DeTurck RHS when the
first- and second-derivative primitives are read from caller-supplied metric-entry second jets.
This packages the pointwise chosen-jet state-space estimate into the finite compact-family
readout used by local parabolic chart models. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_metric_entries_directions_of_unique
    {ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (ξ : n → X)
    {δ : ℝ} {C KM : n → n → ℝ} {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M u z i j) s)
    (hC : ∀ i j, 0 ≤ C i j) (hKM : ∀ i j, 0 ≤ KM i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C i j) α (fun z => M u z i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM i j * dist u v) α
        (fun z => M u z i j - M v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z)
        (fun a i j => (J u i j).spaceDeriv z (ξ a))
        (fun a b i j => (J u i j).spaceSecondDeriv z (ξ a) (ξ b))) :
    LipschitzOnWith
      ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ C
          (firstDerivativeVectorRadius (X := X) ξ C)
          (secondDerivativeVectorRadius (X := X) ξ C)
          (∑ i, ∑ j, KM i j)
          (∑ a, ∑ i, ∑ j, firstDerivativeVectorRadius (X := X) ξ KM a i j)
          (fun i j => ∑ a, ∑ b,
            secondDerivativeVectorRadius (X := X) ξ KM a b i j),
        ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
          (𝕜 := ℝ) hδpos
          (firstDerivativeVectorRadius_nonneg (X := X) ξ hC)
          (secondDerivativeVectorRadius_nonneg (X := X) ξ hC)
          (Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hKM i j)
          (Finset.sum_nonneg fun a _ha =>
            Finset.sum_nonneg fun i _hi =>
              Finset.sum_nonneg fun j _hj =>
                firstDerivativeVectorRadius_nonneg (X := X) ξ hKM a i j)
          (fun i j =>
            Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb =>
                secondDerivativeVectorRadius_nonneg (X := X) ξ hKM a b i j)⟩
      (fun u : Y =>
        parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u))
      stateSet := by
  refine parabolicC0AlphaSubmodule.lipschitzOnWith_toCompactCoordFamily_of_bounded_sub
    (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
    Kdom hKdom hα ?_
  intro u hu v hv z hz
  have hLipz :=
    ricciDeTurckSchematicMatrix_lipschitzOnWith_of_metric_entries_directions_of_unique
      (X := X) (α := α) (s := s) ξ
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (M := M) J hC hKM hM hMdiff htime hspace hδpos hdet hz
  have hdist := hLipz.dist_le_mul u hu v hv
  simpa [dist_eq_norm, hAeq hu z, hAeq hv z] using hdist

/-- Linear finite-cover readout version of
`ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_metric_entries_directions_of_unique`.
This is the same compact-coordinate map, packaged through the linear readout used by finite
product Banach chart handoffs. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamilyLinearMap_of_metric_entries_directions_of_unique
    {ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (ξ : n → X)
    {δ : ℝ} {C KM : n → n → ℝ} {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M u z i j) s)
    (hC : ∀ i j, 0 ≤ C i j) (hKM : ∀ i j, 0 ≤ KM i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C i j) α (fun z => M u z i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM i j * dist u v) α
        (fun z => M u z i j - M v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z)
        (fun a i j => (J u i j).spaceDeriv z (ξ a))
        (fun a b i j => (J u i j).spaceSecondDeriv z (ξ a) (ξ b))) :
    LipschitzOnWith
      ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ C
          (firstDerivativeVectorRadius (X := X) ξ C)
          (secondDerivativeVectorRadius (X := X) ξ C)
          (∑ i, ∑ j, KM i j)
          (∑ a, ∑ i, ∑ j, firstDerivativeVectorRadius (X := X) ξ KM a i j)
          (fun i j => ∑ a, ∑ b,
            secondDerivativeVectorRadius (X := X) ξ KM a b i j),
        ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
          (𝕜 := ℝ) hδpos
          (firstDerivativeVectorRadius_nonneg (X := X) ξ hC)
          (secondDerivativeVectorRadius_nonneg (X := X) ξ hC)
          (Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hKM i j)
          (Finset.sum_nonneg fun a _ha =>
            Finset.sum_nonneg fun i _hi =>
              Finset.sum_nonneg fun j _hj =>
                firstDerivativeVectorRadius_nonneg (X := X) ξ hKM a i j)
          (fun i j =>
            Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb =>
                secondDerivativeVectorRadius_nonneg (X := X) ξ hKM a b i j)⟩
      (fun u : Y =>
        parabolicC0AlphaSubmodule.toCompactCoordFamilyLinearMap
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u))
      stateSet := by
  simpa using
    ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_metric_entries_directions_of_unique
      (X := X) (α := α) (s := s) Kdom hKdom hα ξ
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (A := A) (M := M) J hC hKM hM hMdiff htime hspace hδpos hdet hAeq

/-- Pointwise compact-coordinate distance estimate for the chosen-jet schematic Ricci-DeTurck
RHS readout.  This is the memberwise compact-coordinate form of
`ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_metric_entries_directions_of_unique`. -/
theorem ricciDeTurckSchematicMatrix_compactCoord_dist_le_of_metric_entries_directions_of_unique
    {ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (ξ : n → X)
    {δ : ℝ} {C KM : n → n → ℝ} {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M u z i j) s)
    (hC : ∀ i j, 0 ≤ C i j) (hKM : ∀ i j, 0 ≤ KM i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C i j) α (fun z => M u z i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM i j * dist u v) α
        (fun z => M u z i j - M v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z)
        (fun a i j => (J u i j).spaceDeriv z (ξ a))
        (fun a b i j => (J u i j).spaceSecondDeriv z (ξ a) (ξ b))) :
    ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i (z : Kdom i),
      dist
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u) i z)
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A v) i z)
        ≤ ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C
            (firstDerivativeVectorRadius (X := X) ξ C)
            (secondDerivativeVectorRadius (X := X) ξ C)
            (∑ i, ∑ j, KM i j)
            (∑ a, ∑ i, ∑ j, firstDerivativeVectorRadius (X := X) ξ KM a i j)
            (fun i j => ∑ a, ∑ b,
              secondDerivativeVectorRadius (X := X) ξ KM a b i j) * dist u v := by
  have hLip :=
    ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_metric_entries_directions_of_unique
      (X := X) (α := α) (s := s) Kdom hKdom hα ξ
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (A := A) (M := M) J hC hKM hM hMdiff htime hspace hδpos hdet hAeq
  exact (parabolicC0AlphaSubmodule.forall_compactCoord_dist_le_of_toCompactCoordFamily_lipschitzOnWith
      (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
      Kdom hKdom hα hLip)

/-- Fixed-time spatial readout estimate for the chosen-jet schematic Ricci-DeTurck RHS after the
time-space compact pieces cover the requested spatial slices. -/
theorem ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_of_metric_entries_directions_of_unique
    {η ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    (ξ : n → X)
    {timeSet : Set ℝ}
    {δ : ℝ} {C KM : n → n → ℝ} {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M u z i j) s)
    (hC : ∀ i j, 0 ≤ C i j) (hKM : ∀ i j, 0 ≤ KM i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C i j) α (fun z => M u z i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM i j * dist u v) α
        (fun z => M u z i j - M v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z)
        (fun a i j => (J u i j).spaceDeriv z (ξ a))
        (fun a b i j => (J u i j).spaceSecondDeriv z (ξ a) (ξ b)))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A u (τ, x.1)) (A v (τ, x.1)) ≤
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
              (𝕜 := ℝ) δ C
              (firstDerivativeVectorRadius (X := X) ξ C)
              (secondDerivativeVectorRadius (X := X) ξ C)
              (∑ i, ∑ j, KM i j)
              (∑ a, ∑ i, ∑ j, firstDerivativeVectorRadius (X := X) ξ KM a i j)
              (fun i j => ∑ a, ∑ b,
                secondDerivativeVectorRadius (X := X) ξ KM a b i j) * dist u v := by
  refine parabolicC0AlphaSubmodule.forall_timeSlice_spatial_dist_le_of_forall_compactCoord_dist_le
    (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _ u => A u)
    (K := ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ C
      (firstDerivativeVectorRadius (X := X) ξ C)
      (secondDerivativeVectorRadius (X := X) ξ C)
      (∑ i, ∑ j, KM i j)
      (∑ a, ∑ i, ∑ j, firstDerivativeVectorRadius (X := X) ξ KM a i j)
      (fun i j => ∑ a, ∑ b,
        secondDerivativeVectorRadius (X := X) ξ KM a b i j)) ?_ hcover
  intro _τ _hτ
  exact ricciDeTurckSchematicMatrix_compactCoord_dist_le_of_metric_entries_directions_of_unique
    (X := X) (α := α) (s := s) Kdom hKdom hα ξ
    (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
    (A := A) (M := M) J hC hKM hM hMdiff htime hspace hδpos hdet hAeq

/-- Fixed-time spatial readout estimate for the chosen-jet schematic Ricci-DeTurck RHS when the
time-space compact pieces cover all time-space. -/
theorem ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_of_metric_entries_directions_of_unique_ofCover
    {η ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    (ξ : n → X)
    {timeSet : Set ℝ}
    {δ : ℝ} {C KM : n → n → ℝ} {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M u z i j) s)
    (hC : ∀ i j, 0 ≤ C i j) (hKM : ∀ i j, 0 ≤ KM i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C i j) α (fun z => M u z i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM i j * dist u v) α
        (fun z => M u z i j - M v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z)
        (fun a i j => (J u i j).spaceDeriv z (ξ a))
        (fun a b i j => (J u i j).spaceSecondDeriv z (ξ a) (ξ b)))
    (hcover : (⋃ j, (Kdom j : Set (ℝ × X))) = Set.univ) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A u (τ, x.1)) (A v (τ, x.1)) ≤
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
              (𝕜 := ℝ) δ C
              (firstDerivativeVectorRadius (X := X) ξ C)
              (secondDerivativeVectorRadius (X := X) ξ C)
              (∑ i, ∑ j, KM i j)
              (∑ a, ∑ i, ∑ j, firstDerivativeVectorRadius (X := X) ξ KM a i j)
              (fun i j => ∑ a, ∑ b,
                secondDerivativeVectorRadius (X := X) ξ KM a b i j) * dist u v := by
  have hcoverSlices : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X)) :=
    parabolicC0AlphaSubmodule.timeSlice_spatial_cover_of_iUnion_eq_univ
      (X := X) Kdom Kx (timeSet := timeSet) hcover
  exact
    ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_of_metric_entries_directions_of_unique
      (X := X) (α := α) (s := s) Kdom hKdom hα Kx ξ
      (timeSet := timeSet) (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (A := A) (M := M) J hC hKM hM hMdiff htime hspace hδpos hdet hAeq
      hcoverSlices

/-- Pi-valued compact-coordinate readout Lipschitz bridge for a finite family of chosen-jet
schematic Ricci-DeTurck RHS coordinates.  This is the finite-product version consumed by chart
handoffs whose compact readout values are finite families of matrices. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_pi_family_of_metric_entries_family_directions_of_unique
    {κ ι Y n : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (ξ : κ → n → X)
    {δ : ℝ} {C KM : κ → n → n → ℝ} {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (κ → Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ r : κ, ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M r u z i j) s)
    (hC : ∀ r i j, 0 ≤ C r i j) (hKM : ∀ r i j, 0 ≤ KM r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C r i j) α (fun z => M r u z i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM r i j * dist u v) α
        (fun z => M r u z i j - M r v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = fun r =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z)
          (fun a i j => (J r u i j).spaceDeriv z (ξ r a))
          (fun a b i j => (J r u i j).spaceSecondDeriv z (ξ r a) (ξ r b))) :
    LipschitzOnWith
      ⟨∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ (C r)
          (firstDerivativeVectorRadius (X := X) (ξ r) (C r))
          (secondDerivativeVectorRadius (X := X) (ξ r) (C r))
          (∑ i, ∑ j, KM r i j)
          (∑ a, ∑ i, ∑ j,
            firstDerivativeVectorRadius (X := X) (ξ r) (KM r) a i j)
          (fun i j => ∑ a, ∑ b,
            secondDerivativeVectorRadius (X := X) (ξ r) (KM r) a b i j),
        Finset.sum_nonneg fun r _hr =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos
            (firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
            (secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
            (Finset.sum_nonneg fun i _hi =>
              Finset.sum_nonneg fun j _hj => hKM r i j)
            (Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun i _hi =>
                Finset.sum_nonneg fun j _hj =>
                  firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r) a i j)
            (fun i j =>
              Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb =>
                  secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r) a b i j)⟩
      (fun u : Y =>
        parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := κ → Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u))
      stateSet := by
  refine parabolicC0AlphaSubmodule.lipschitzOnWith_toCompactCoordFamily_of_bounded_sub
    (X := X) (E := κ → Matrix n n ℝ) (α := α) (s := s)
    Kdom hKdom hα ?_
  intro u hu v hv z hz
  have hLipz :=
    ricciDeTurckSchematicMatrix_lipschitzOnWith_pi_family_of_metric_entries_family_directions_of_unique
      (X := X) (α := α) (s := s) ξ
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (M := M) J hC hKM hM hMdiff htime hspace hδpos hdet hz
  have hdist := hLipz.dist_le_mul u hu v hv
  simpa [dist_eq_norm, hAeq hu z, hAeq hv z] using hdist

/-- Linear finite-cover readout version of
`ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_pi_family_of_metric_entries_family_directions_of_unique`. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamilyLinearMap_pi_family_of_metric_entries_family_directions_of_unique
    {κ ι Y n : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (ξ : κ → n → X)
    {δ : ℝ} {C KM : κ → n → n → ℝ} {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (κ → Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ r : κ, ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M r u z i j) s)
    (hC : ∀ r i j, 0 ≤ C r i j) (hKM : ∀ r i j, 0 ≤ KM r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C r i j) α (fun z => M r u z i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM r i j * dist u v) α
        (fun z => M r u z i j - M r v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = fun r =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z)
          (fun a i j => (J r u i j).spaceDeriv z (ξ r a))
          (fun a b i j => (J r u i j).spaceSecondDeriv z (ξ r a) (ξ r b))) :
    LipschitzOnWith
      ⟨∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ (C r)
          (firstDerivativeVectorRadius (X := X) (ξ r) (C r))
          (secondDerivativeVectorRadius (X := X) (ξ r) (C r))
          (∑ i, ∑ j, KM r i j)
          (∑ a, ∑ i, ∑ j,
            firstDerivativeVectorRadius (X := X) (ξ r) (KM r) a i j)
          (fun i j => ∑ a, ∑ b,
            secondDerivativeVectorRadius (X := X) (ξ r) (KM r) a b i j),
        Finset.sum_nonneg fun r _hr =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos
            (firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
            (secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
            (Finset.sum_nonneg fun i _hi =>
              Finset.sum_nonneg fun j _hj => hKM r i j)
            (Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun i _hi =>
                Finset.sum_nonneg fun j _hj =>
                  firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r) a i j)
            (fun i j =>
              Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb =>
                  secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r) a b i j)⟩
      (fun u : Y =>
        parabolicC0AlphaSubmodule.toCompactCoordFamilyLinearMap
          (X := X) (E := κ → Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u))
      stateSet := by
  simpa using
    ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_pi_family_of_metric_entries_family_directions_of_unique
      (X := X) (α := α) (s := s) Kdom hKdom hα ξ
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (A := A) (M := M) J hC hKM hM hMdiff htime hspace hδpos hdet hAeq

/-- Pointwise compact-coordinate distance estimate for Pi-valued chosen-jet schematic
Ricci-DeTurck RHS readouts. -/
theorem ricciDeTurckSchematicMatrix_compactCoord_dist_le_pi_family_of_metric_entries_family_directions_of_unique
    {κ ι Y n : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (ξ : κ → n → X)
    {δ : ℝ} {C KM : κ → n → n → ℝ} {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (κ → Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ r : κ, ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M r u z i j) s)
    (hC : ∀ r i j, 0 ≤ C r i j) (hKM : ∀ r i j, 0 ≤ KM r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C r i j) α (fun z => M r u z i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM r i j * dist u v) α
        (fun z => M r u z i j - M r v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = fun r =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z)
          (fun a i j => (J r u i j).spaceDeriv z (ξ r a))
          (fun a b i j => (J r u i j).spaceSecondDeriv z (ξ r a) (ξ r b))) :
    ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i (z : Kdom i),
      dist
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := κ → Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u) i z)
        (parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := κ → Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A v) i z)
        ≤ (∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r)
            (firstDerivativeVectorRadius (X := X) (ξ r) (C r))
            (secondDerivativeVectorRadius (X := X) (ξ r) (C r))
            (∑ i, ∑ j, KM r i j)
            (∑ a, ∑ i, ∑ j,
              firstDerivativeVectorRadius (X := X) (ξ r) (KM r) a i j)
            (fun i j => ∑ a, ∑ b,
              secondDerivativeVectorRadius (X := X) (ξ r) (KM r) a b i j)) *
          dist u v := by
  have hLip :=
    ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_pi_family_of_metric_entries_family_directions_of_unique
      (X := X) (α := α) (s := s) Kdom hKdom hα ξ
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (A := A) (M := M) J hC hKM hM hMdiff htime hspace hδpos hdet hAeq
  exact (parabolicC0AlphaSubmodule.forall_compactCoord_dist_le_of_toCompactCoordFamily_lipschitzOnWith
      (X := X) (E := κ → Matrix n n ℝ) (α := α) (s := s)
      Kdom hKdom hα hLip)

/-- Fixed-time spatial readout estimate for Pi-valued chosen-jet schematic Ricci-DeTurck RHS
fields after the time-space compact pieces cover the requested spatial slices. -/
theorem ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_pi_family_of_metric_entries_family_directions_of_unique
    {κ η ι Y n : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    (ξ : κ → n → X)
    {timeSet : Set ℝ}
    {δ : ℝ} {C KM : κ → n → n → ℝ} {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (κ → Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ r : κ, ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M r u z i j) s)
    (hC : ∀ r i j, 0 ≤ C r i j) (hKM : ∀ r i j, 0 ≤ KM r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C r i j) α (fun z => M r u z i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM r i j * dist u v) α
        (fun z => M r u z i j - M r v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = fun r =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z)
          (fun a i j => (J r u i j).spaceDeriv z (ξ r a))
          (fun a b i j => (J r u i j).spaceSecondDeriv z (ξ r a) (ξ r b)))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A u (τ, x.1)) (A v (τ, x.1)) ≤
          (∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
              (𝕜 := ℝ) δ (C r)
              (firstDerivativeVectorRadius (X := X) (ξ r) (C r))
              (secondDerivativeVectorRadius (X := X) (ξ r) (C r))
              (∑ i, ∑ j, KM r i j)
              (∑ a, ∑ i, ∑ j,
                firstDerivativeVectorRadius (X := X) (ξ r) (KM r) a i j)
              (fun i j => ∑ a, ∑ b,
                secondDerivativeVectorRadius (X := X) (ξ r) (KM r) a b i j)) *
            dist u v := by
  refine parabolicC0AlphaSubmodule.forall_timeSlice_spatial_dist_le_of_forall_compactCoord_dist_le
    (X := X) (E := κ → Matrix n n ℝ) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _ u => A u)
    (K := ∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ (C r)
      (firstDerivativeVectorRadius (X := X) (ξ r) (C r))
      (secondDerivativeVectorRadius (X := X) (ξ r) (C r))
      (∑ i, ∑ j, KM r i j)
      (∑ a, ∑ i, ∑ j,
        firstDerivativeVectorRadius (X := X) (ξ r) (KM r) a i j)
      (fun i j => ∑ a, ∑ b,
        secondDerivativeVectorRadius (X := X) (ξ r) (KM r) a b i j)) ?_ hcover
  intro _τ _hτ
  exact ricciDeTurckSchematicMatrix_compactCoord_dist_le_pi_family_of_metric_entries_family_directions_of_unique
    (X := X) (α := α) (s := s) Kdom hKdom hα ξ
    (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
    (A := A) (M := M) J hC hKM hM hMdiff htime hspace hδpos hdet hAeq

/-- Fixed-time spatial readout estimate for Pi-valued chosen-jet schematic Ricci-DeTurck RHS
fields when the time-space compact pieces cover all time-space. -/
theorem ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_pi_family_of_metric_entries_family_directions_of_unique_ofCover
    {κ η ι Y n : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    (ξ : κ → n → X)
    {timeSet : Set ℝ}
    {δ : ℝ} {C KM : κ → n → n → ℝ} {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (κ → Matrix n n ℝ) α s}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    (J : ∀ r : κ, ∀ u : Y, ∀ i j,
      ParabolicSecondJet (fun z : ℝ × X => M r u z i j) s)
    (hC : ∀ r i j, 0 ≤ C r i j) (hKM : ∀ r i j, 0 ≤ KM r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C r i j) α (fun z => M r u z i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM r i j * dist u v) α
        (fun z => M r u z i j - M r v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = fun r =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z)
          (fun a i j => (J r u i j).spaceDeriv z (ξ r a))
          (fun a b i j => (J r u i j).spaceSecondDeriv z (ξ r a) (ξ r b)))
    (hcover : (⋃ j, (Kdom j : Set (ℝ × X))) = Set.univ) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A u (τ, x.1)) (A v (τ, x.1)) ≤
          (∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
              (𝕜 := ℝ) δ (C r)
              (firstDerivativeVectorRadius (X := X) (ξ r) (C r))
              (secondDerivativeVectorRadius (X := X) (ξ r) (C r))
              (∑ i, ∑ j, KM r i j)
              (∑ a, ∑ i, ∑ j,
                firstDerivativeVectorRadius (X := X) (ξ r) (KM r) a i j)
              (fun i j => ∑ a, ∑ b,
                secondDerivativeVectorRadius (X := X) (ξ r) (KM r) a b i j)) *
            dist u v := by
  have hcoverSlices : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X)) :=
    parabolicC0AlphaSubmodule.timeSlice_spatial_cover_of_iUnion_eq_univ
      (X := X) Kdom Kx (timeSet := timeSet) hcover
  exact
    ricciDeTurckSchematicMatrix_timeSlice_spatial_dist_le_pi_family_of_metric_entries_family_directions_of_unique
      (X := X) (α := α) (s := s) Kdom hKdom hα Kx ξ
      (timeSet := timeSet) (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (A := A) (M := M) J hC hKM hM hMdiff htime hspace hδpos hdet hAeq
      hcoverSlices

/-- State-space Lipschitz bridge from higher parabolic primitive controls with coarser exported
constants.  Entrywise higher difference controls may be proved with sharper constants; the
resulting schematic RHS Lipschitz constant is formed from any larger primitive constants accepted
by the existing matrix `C^{0,α}` theorem. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_of_higher_primitive_normLe_of_le
    {Y n : Type*} [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    {δ KM KD : ℝ} {KH : n → n → ℝ}
    {KM0 : n → n → ℝ} {KD0 : n → n → n → ℝ}
    {KH0 : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM0_nonneg : ∀ a b, 0 ≤ KM0 a b)
    (hKD0_nonneg : ∀ a b c, 0 ≤ KD0 a b c)
    (hKH0_nonneg : ∀ a b i j, 0 ≤ KH0 a b i j)
    (hKM_nonneg : 0 ≤ KM) (hKD_nonneg : 0 ≤ KD)
    (hKH_nonneg : ∀ i j, 0 ≤ KH i j)
    (hKM_le : (∑ a, ∑ b, KM0 a b) ≤ KM)
    (hKD_le : (∑ a, ∑ b, ∑ c, KD0 a b c) ≤ KD)
    (hKH_le : ∀ i j, (∑ a, ∑ b, KH0 a b i j) ≤ KH i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C DB HB KM KD KH,
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos hDB hHB hKM_nonneg hKD_nonneg hKH_nonneg⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M u z) (D u z) (H u z))
        stateSet := by
  have hKD0sum : 0 ≤ ∑ a, ∑ b, ∑ c, KD0 a b c :=
    Finset.sum_nonneg fun a _ha =>
      Finset.sum_nonneg fun b _hb =>
        Finset.sum_nonneg fun c _hc => hKD0_nonneg a b c
  have hMbound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b,
      ‖M u z a b‖ ≤ C a b := by
    intro u hu z hz a b
    exact (hM hu a b).norm_le hz
  have hDbound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D u z a b c‖ ≤ DB a b c := by
    intro u hu z hz a b c
    exact (hD hu a b c).norm_le hz
  have hHbound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j,
      ‖H u z a b i j‖ ≤ HB a b i j := by
    intro u hu z hz a b i j
    exact (hH hu a b i j).norm_le hz
  have hMdiff_bound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s →
        ‖M u z - M v z‖ ≤ (∑ a, ∑ b, KM0 a b) * dist u v := by
    intro u hu v hv z hz
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := KM0) (M := M u) (N := M v)
      hKM0_nonneg dist_nonneg (hMdiff hu hv) hz
  have hDdiff_bound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
        ‖D u z a b c - D v z a b c‖ ≤
          (∑ a, ∑ b, ∑ c, KD0 a b c) * dist u v := by
    intro u hu v hv z hz a b c
    have hentry : ‖D u z a b c - D v z a b c‖ ≤ KD0 a b c * dist u v := by
      simpa [dist_eq_norm] using (hDdiff hu hv a b c).dist_le_of_sub hz
    exact hentry.trans
      (mul_le_mul_of_nonneg_right (entry_le_triple_sum hKD0_nonneg a b c) dist_nonneg)
  have hHdiff_bound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
        ‖((fun a b => H u z a b i j) : Matrix n n ℝ) -
          ((fun a b => H v z a b i j) : Matrix n n ℝ)‖ ≤
            (∑ a, ∑ b, KH0 a b i j) * dist u v := by
    intro u hu v hv z hz i j
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := fun a b => KH0 a b i j)
      (M := fun z : ℝ × X => (fun a b => H u z a b i j))
      (N := fun z : ℝ × X => (fun a b => H v z a b i j))
      (fun a b => hKH0_nonneg a b i j) dist_nonneg
      (fun a b => hHdiff hu hv a b i j) hz
  exact ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix_lipschitzOnWith_of_primitive_dist_le_of_le
    (X := X) (s := s) (δ := δ) (C := C) (DB := DB) (HB := HB)
    (KM0 := ∑ a, ∑ b, KM0 a b)
    (KD0 := ∑ a, ∑ b, ∑ c, KD0 a b c)
    (KH0 := fun i j => ∑ a, ∑ b, KH0 a b i j)
    (KM := KM) (KD := KD) (KH := KH)
    (stateSet := stateSet) (M := M) (D := D) (H := H)
    hDB hHB hKM_nonneg hKD_nonneg hKH_nonneg hKM_le hKD_le hKH_le hKD0sum
    hMbound hDbound hHbound hMdiff_bound hDdiff_bound hHdiff_bound hδpos hdet

/-- Finite-family state-space Lipschitz bridge from higher parabolic primitive controls to the
schematic Ricci-DeTurck RHS coordinates. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_higher_primitive_normLe
    {κ Y n : Type*} [Fintype κ] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    {δ : ℝ} {KM : κ → n → n → ℝ} {KD : κ → n → n → n → ℝ}
    {KH : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r a b, 0 ≤ KM r a b) (hKD : ∀ r a b c, 0 ≤ KD r a b c)
    (hKH : ∀ r a b i j, 0 ≤ KH r a b i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ r ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r) (DB r) (HB r)
            (∑ a, ∑ b, KM r a b)
            (∑ a, ∑ b, ∑ c, KD r a b c)
            (fun i j => ∑ a, ∑ b, KH r a b i j),
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos (hDB r) (hHB r)
            (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM r a b)
            (Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb =>
                Finset.sum_nonneg fun c _hc => hKD r a b c)
            (fun i j =>
              Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb => hKH r a b i j)⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z) (D r u z) (H r u z))
        stateSet := by
  intro r z hz
  exact ricciDeTurckSchematicMatrix_lipschitzOnWith_of_higher_primitive_normLe
    (X := X) (α := α) (s := s) (δ := δ)
    (KM := KM r) (KD := KD r) (KH := KH r)
    (C := C r) (DB := DB r) (HB := HB r)
    (stateSet := stateSet) (M := M r) (D := D r) (H := H r)
    (hDB r) (hHB r) (hKM r) (hKD r) (hKH r)
    (hM r) (hD r) (hH r) (hMdiff r) (hDdiff r) (hHdiff r)
    hδpos (hdet r) hz

/-- Pi-valued finite-family state-space Lipschitz bridge from higher parabolic primitive
controls.  The Lipschitz constant is the finite sum of the coordinate schematic constants, so the
whole family can be consumed as one finite-product coordinate readout. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_pi_family_of_higher_primitive_normLe
    {κ Y n : Type*} [Fintype κ] [DecidableEq κ] [PseudoMetricSpace Y]
    [Fintype n] [DecidableEq n]
    {δ : ℝ} {KM : κ → n → n → ℝ} {KD : κ → n → n → n → ℝ}
    {KH : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r a b, 0 ≤ KM r a b) (hKD : ∀ r a b c, 0 ≤ KD r a b c)
    (hKH : ∀ r a b i j, 0 ≤ KH r a b i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r) (DB r) (HB r)
            (∑ a, ∑ b, KM r a b)
            (∑ a, ∑ b, ∑ c, KD r a b c)
            (fun i j => ∑ a, ∑ b, KH r a b i j),
          Finset.sum_nonneg fun r _hr =>
            ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
              (𝕜 := ℝ) hδpos (hDB r) (hHB r)
              (Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb => hKM r a b)
              (Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb =>
                  Finset.sum_nonneg fun c _hc => hKD r a b c)
              (fun i j =>
                Finset.sum_nonneg fun a _ha =>
                  Finset.sum_nonneg fun b _hb => hKH r a b i j)⟩
        (fun u : Y => fun r =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M r u z) (D r u z) (H r u z))
        stateSet := by
  intro z hz
  let Kcoord : κ → ℝ := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ (C r) (DB r) (HB r)
      (∑ a, ∑ b, KM r a b)
      (∑ a, ∑ b, ∑ c, KD r a b c)
      (fun i j => ∑ a, ∑ b, KH r a b i j)
  have hKcoord_nonneg : ∀ r, 0 ≤ Kcoord r := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
      (𝕜 := ℝ) hδpos (hDB r) (hHB r)
      (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM r a b)
      (Finset.sum_nonneg fun a _ha =>
        Finset.sum_nonneg fun b _hb =>
          Finset.sum_nonneg fun c _hc => hKD r a b c)
      (fun i j =>
        Finset.sum_nonneg fun a _ha =>
          Finset.sum_nonneg fun b _hb => hKH r a b i j)
  have hcoord : ∀ r,
      LipschitzOnWith
        ⟨Kcoord r, hKcoord_nonneg r⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z) (D r u z) (H r u z))
        stateSet := by
    intro r
    exact ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_higher_primitive_normLe
      (X := X) (α := α) (s := s) (δ := δ)
      (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
      (stateSet := stateSet) (M := M) (D := D) (H := H)
      hDB hHB hKM hKD hKH hM hD hH hMdiff hDdiff hHdiff hδpos hdet r hz
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hsum_nonneg : 0 ≤ ∑ r, Kcoord r :=
    Finset.sum_nonneg fun r _hr => hKcoord_nonneg r
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hsum_nonneg dist_nonneg)).2 fun r => ?_
  have hr := (hcoord r).dist_le_mul u hu v hv
  have hr_le_sum : Kcoord r ≤ ∑ r, Kcoord r :=
    Finset.single_le_sum (fun r' _hr' => hKcoord_nonneg r') (Finset.mem_univ r)
  have hentry :
      ‖ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z) (D r u z) (H r u z) -
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r v z) (D r v z) (H r v z)‖ ≤ Kcoord r * dist u v := by
    have hport := hr
    simp [dist_eq_norm] at hport ⊢
    exact hport
  exact hentry.trans (mul_le_mul_of_nonneg_right hr_le_sum dist_nonneg)

/-- Finite-family state-space Lipschitz bridge from higher primitive controls with coarser
exported constants for each family member. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_higher_primitive_normLe_of_le
    {κ Y n : Type*} [Fintype κ] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    {δ : ℝ} {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {KM0 : κ → n → n → ℝ} {KD0 : κ → n → n → n → ℝ}
    {KH0 : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM0_nonneg : ∀ r a b, 0 ≤ KM0 r a b)
    (hKD0_nonneg : ∀ r a b c, 0 ≤ KD0 r a b c)
    (hKH0_nonneg : ∀ r a b i j, 0 ≤ KH0 r a b i j)
    (hKM_nonneg : ∀ r, 0 ≤ KM r) (hKD_nonneg : ∀ r, 0 ≤ KD r)
    (hKH_nonneg : ∀ r i j, 0 ≤ KH r i j)
    (hKM_le : ∀ r, (∑ a, ∑ b, KM0 r a b) ≤ KM r)
    (hKD_le : ∀ r, (∑ a, ∑ b, ∑ c, KD0 r a b c) ≤ KD r)
    (hKH_le : ∀ r i j, (∑ a, ∑ b, KH0 r a b i j) ≤ KH r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ r ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r),
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos (hDB r) (hHB r)
            (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z) (D r u z) (H r u z))
        stateSet := by
  intro r z hz
  exact ricciDeTurckSchematicMatrix_lipschitzOnWith_of_higher_primitive_normLe_of_le
    (X := X) (α := α) (s := s) (δ := δ)
    (KM0 := KM0 r) (KD0 := KD0 r) (KH0 := KH0 r)
    (KM := KM r) (KD := KD r) (KH := KH r)
    (C := C r) (DB := DB r) (HB := HB r)
    (stateSet := stateSet) (M := M r) (D := D r) (H := H r)
    (hDB r) (hHB r) (hKM0_nonneg r) (hKD0_nonneg r) (hKH0_nonneg r)
    (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)
    (hKM_le r) (hKD_le r) (hKH_le r)
    (hM r) (hD r) (hH r) (hMdiff r) (hDdiff r) (hHdiff r)
    hδpos (hdet r) hz

/-- Pi-valued finite-family state-space Lipschitz bridge from higher primitive controls with
coarser exported constants. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_pi_family_of_higher_primitive_normLe_of_le
    {κ Y n : Type*} [Fintype κ] [DecidableEq κ] [PseudoMetricSpace Y]
    [Fintype n] [DecidableEq n]
    {δ : ℝ} {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {KM0 : κ → n → n → ℝ} {KD0 : κ → n → n → n → ℝ}
    {KH0 : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM0_nonneg : ∀ r a b, 0 ≤ KM0 r a b)
    (hKD0_nonneg : ∀ r a b c, 0 ≤ KD0 r a b c)
    (hKH0_nonneg : ∀ r a b i j, 0 ≤ KH0 r a b i j)
    (hKM_nonneg : ∀ r, 0 ≤ KM r) (hKD_nonneg : ∀ r, 0 ≤ KD r)
    (hKH_nonneg : ∀ r i j, 0 ≤ KH r i j)
    (hKM_le : ∀ r, (∑ a, ∑ b, KM0 r a b) ≤ KM r)
    (hKD_le : ∀ r, (∑ a, ∑ b, ∑ c, KD0 r a b c) ≤ KD r)
    (hKH_le : ∀ r i j, (∑ a, ∑ b, KH0 r a b i j) ≤ KH r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r),
          Finset.sum_nonneg fun r _hr =>
            ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
              (𝕜 := ℝ) hδpos (hDB r) (hHB r)
              (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)⟩
        (fun u : Y => fun r =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M r u z) (D r u z) (H r u z))
        stateSet := by
  intro z hz
  let Kcoord : κ → ℝ := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r)
  have hKcoord_nonneg : ∀ r, 0 ≤ Kcoord r := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
      (𝕜 := ℝ) hδpos (hDB r) (hHB r)
      (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)
  have hcoord : ∀ r,
      LipschitzOnWith
        ⟨Kcoord r, hKcoord_nonneg r⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z) (D r u z) (H r u z))
        stateSet := by
    intro r
    exact ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_higher_primitive_normLe_of_le
      (X := X) (α := α) (s := s) (δ := δ)
      (KM0 := KM0) (KD0 := KD0) (KH0 := KH0)
      (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
      (stateSet := stateSet) (M := M) (D := D) (H := H)
      hDB hHB hKM0_nonneg hKD0_nonneg hKH0_nonneg
      hKM_nonneg hKD_nonneg hKH_nonneg hKM_le hKD_le hKH_le
      hM hD hH hMdiff hDdiff hHdiff hδpos hdet r hz
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hsum_nonneg : 0 ≤ ∑ r, Kcoord r :=
    Finset.sum_nonneg fun r _hr => hKcoord_nonneg r
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hsum_nonneg dist_nonneg)).2 fun r => ?_
  have hr := (hcoord r).dist_le_mul u hu v hv
  have hr_le_sum : Kcoord r ≤ ∑ r, Kcoord r :=
    Finset.single_le_sum (fun r' _hr' => hKcoord_nonneg r') (Finset.mem_univ r)
  have hentry :
      ‖ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z) (D r u z) (H r u z) -
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r v z) (D r v z) (H r v z)‖ ≤ Kcoord r * dist u v := by
    have hport := hr
    simp [dist_eq_norm] at hport ⊢
    exact hport
  exact hentry.trans (mul_le_mul_of_nonneg_right hr_le_sum dist_nonneg)

end ParabolicC2AlphaNormLe

namespace ParabolicC2AlphaOn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise higher parabolic membership packages as matrix-valued `C^{0,α}` membership. -/
theorem matrix_c0AlphaOn_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {M : ℝ × X → Matrix m n A}
    (h : ∀ i j, ParabolicC2AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α M s :=
  ParabolicC0AlphaOn.matrix_of_entries fun i j => (h i j).c0AlphaOn

/-- A matrix-valued higher parabolic function projects to each entry as a higher parabolic
function. -/
theorem matrix_apply_c2AlphaOn {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {M : ℝ × X → Matrix m n A}
    (h : ParabolicC2AlphaOn α M s) (i : m) (j : n) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => M z i j) s := by
  let L : Matrix m n A →L[ℝ] A :=
    (ContinuousLinearMap.proj j : (n → A) →L[ℝ] A).comp
      (ContinuousLinearMap.proj i : Matrix m n A →L[ℝ] n → A)
  have hport := h.continuousLinearMap L
  simp [L] at hport ⊢
  exact hport

/-- Entrywise higher parabolic membership assembles into matrix-valued higher parabolic
membership. -/
theorem matrix_c2AlphaOn_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NormedAddCommGroup A] [NormedSpace ℝ A]
    {M : ℝ × X → Matrix m n A}
    (h : ∀ i j, ParabolicC2AlphaOn α (fun z => M z i j) s) :
    ParabolicC2AlphaOn α M s := by
  classical
  choose N _hN hN using h
  exact of_normLe (ParabolicC2AlphaNormLe.matrix_c2AlphaNormLe_of_entries
    (X := X) (α := α) (s := s) (N := N) (M := M) hN)

/-- Entrywise higher parabolic membership for a matrix difference assembles into
matrix-valued higher parabolic membership. -/
theorem matrix_sub_c2AlphaOn_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NormedAddCommGroup A] [NormedSpace ℝ A]
    {M N : ℝ × X → Matrix m n A}
    (h : ∀ i j, ParabolicC2AlphaOn α (fun z => M z i j - N z i j) s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => M z - N z) s := by
  classical
  simpa [Pi.sub_apply] using
    matrix_c2AlphaOn_of_entries (X := X) (α := α) (s := s)
      (M := fun z : ℝ × X => M z - N z) h

/-- Finite Pi-valued value-level `C^{0,α}` membership from coordinatewise higher parabolic
membership. -/
theorem pi_c0AlphaOn_of_entries {ι A : Type*} [Fintype ι]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {u : ℝ × X → ι → A}
    (h : ∀ i, ParabolicC2AlphaOn α (fun z => u z i) s) :
    ParabolicC0AlphaOn α u s :=
  ParabolicC0AlphaOn.pi fun i => (h i).c0AlphaOn

/-- Direct higher-regularity handoff for the schematic Ricci-DeTurck coordinate RHS.  Higher
primitive controls provide the value-level `C^{0,α}` hypotheses of the matrix closure theorem. -/
theorem ricciDeTurckSchematicMatrix_c0AlphaOn_of_entries {n : Type*}
    [Fintype n] [DecidableEq n] {δ : ℝ}
    {M : ℝ × X → Matrix n n ℝ}
    {D : ℝ × X → n → n → n → ℝ}
    {H : ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ a b, ParabolicC2AlphaOn α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC2AlphaOn α (fun z => D z a b c) s)
    (hH : ∀ a b i j, ParabolicC2AlphaOn α (fun z => H z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M z) (D z) (H z)) s := by
  have hport := (ParabolicC0AlphaOn.ricciDeTurck_schematic
      (M := M) (D := D) (H := H)
      (fun a b => (hM a b).c0AlphaOn)
      (fun a b c => (hD a b c).c0AlphaOn)
      (fun a b i j => (hH a b i j).c0AlphaOn)
      hδpos hdet)
  simp [ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix] at hport ⊢
  exact hport

/-- Finite-family direct higher-regularity handoff for schematic Ricci-DeTurck RHS coordinates. -/
theorem ricciDeTurckSchematicMatrix_c0AlphaOn_family_of_entries {κ n : Type*}
    [Fintype n] [DecidableEq n] {δ : ℝ}
    {M : κ → ℝ × X → Matrix n n ℝ}
    {D : κ → ℝ × X → n → n → n → ℝ}
    {H : κ → ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ r a b, ParabolicC2AlphaOn α (fun z => M r z a b) s)
    (hD : ∀ r a b c, ParabolicC2AlphaOn α (fun z => D r z a b c) s)
    (hH : ∀ r a b i j, ParabolicC2AlphaOn α (fun z => H r z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ∀ r, ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M r z) (D r z) (H r z)) s := by
  intro r
  exact ricciDeTurckSchematicMatrix_c0AlphaOn_of_entries
    (M := M r) (D := D r) (H := H r)
    (hM r) (hD r) (hH r) hδpos (hdet r)

/-- Pi-valued finite-family direct higher-regularity handoff for schematic Ricci-DeTurck RHS
coordinates. -/
theorem ricciDeTurckSchematicMatrix_c0AlphaOn_pi_family_of_entries {κ n : Type*}
    [Fintype κ] [Fintype n] [DecidableEq n] {δ : ℝ}
    {M : κ → ℝ × X → Matrix n n ℝ}
    {D : κ → ℝ × X → n → n → n → ℝ}
    {H : κ → ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ r a b, ParabolicC2AlphaOn α (fun z => M r z a b) s)
    (hD : ∀ r a b c, ParabolicC2AlphaOn α (fun z => D r z a b c) s)
    (hH : ∀ r a b i j, ParabolicC2AlphaOn α (fun z => H r z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X => fun r : κ =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M r z) (D r z) (H r z)) s :=
  ParabolicC0AlphaOn.pi fun r =>
    ricciDeTurckSchematicMatrix_c0AlphaOn_family_of_entries
      (M := M) (D := D) (H := H) hM hD hH hδpos hdet r
/-- Qualitative higher-regularity version of
`exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions`: entrywise higher
membership of a metric supplies chosen second jets whose finite-direction derivative arrays make
the schematic Ricci-DeTurck RHS `C^{0,α}`. -/
theorem exists_secondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_of_metric_entries_directions
    {n : Type*} [Fintype n] [DecidableEq n] (v : n → X)
    {δ : ℝ} {s : Set (ℝ × X)}
    {M : ℝ × X → Matrix n n ℝ}
    (hM : ∀ i j, ParabolicC2AlphaOn α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ∃ J : ∀ i j, ParabolicSecondJet (fun z : ℝ × X => M z i j) s,
      ParabolicC0AlphaOn α
        (fun z : ℝ × X =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M z)
            (fun a i j => (J i j).spaceDeriv z (v a))
            (fun a b i j => (J i j).spaceSecondDeriv z (v a) (v b))) s := by
  classical
  choose R _hR_nonneg hR using hM
  rcases
    ParabolicC2AlphaNormLe.exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions
      (X := X) (α := α) (v := v) (R := R) (δ := δ) (s := s) (M := M)
      hR hδpos hdet with
    ⟨J, hJ⟩
  exact ⟨J, hJ.c0AlphaOn⟩
/-- Pi-valued finite-family qualitative higher-regularity version of
`exists_secondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries_directions`. -/
theorem exists_secondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_pi_family_of_metric_entries_directions
    {κ n : Type*} [Fintype κ] [Fintype n] [DecidableEq n] (v : n → X)
    {δ : ℝ} {s : Set (ℝ × X)}
    {M : κ → ℝ × X → Matrix n n ℝ}
    (hM : ∀ r i j, ParabolicC2AlphaOn α (fun z => M r z i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ∃ J : ∀ r i j, ParabolicSecondJet (fun z : ℝ × X => M r z i j) s,
      ParabolicC0AlphaOn α
        (fun z : ℝ × X => fun r : κ =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M r z)
            (fun a i j => (J r i j).spaceDeriv z (v a))
            (fun a b i j => (J r i j).spaceSecondDeriv z (v a) (v b))) s := by
  classical
  choose J hJ using fun r =>
    exists_secondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_of_metric_entries_directions
      (X := X) (α := α) (v := v) (δ := δ) (s := s) (M := M r) (hM r)
      hδpos (hdet r)
  refine ⟨J, ?_⟩
  exact ParabolicC0AlphaOn.pi hJ
/-- Pi-valued finite-family qualitative higher-regularity version of
`exists_secondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries_family_directions`. -/
theorem exists_secondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_pi_family_of_metric_entries_family_directions
    {κ n : Type*} [Fintype κ] [Fintype n] [DecidableEq n] (v : κ → n → X)
    {δ : ℝ} {s : Set (ℝ × X)}
    {M : κ → ℝ × X → Matrix n n ℝ}
    (hM : ∀ r i j, ParabolicC2AlphaOn α (fun z => M r z i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ∃ J : ∀ r i j, ParabolicSecondJet (fun z : ℝ × X => M r z i j) s,
      ParabolicC0AlphaOn α
        (fun z : ℝ × X => fun r : κ =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M r z)
            (fun a i j => (J r i j).spaceDeriv z (v r a))
            (fun a b i j => (J r i j).spaceSecondDeriv z (v r a) (v r b))) s := by
  classical
  choose J hJ using fun r =>
    exists_secondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_of_metric_entries_directions
      (X := X) (α := α) (v := v r) (δ := δ) (s := s) (M := M r) (hM r)
      hδpos (hdet r)
  refine ⟨J, ?_⟩
  exact ParabolicC0AlphaOn.pi hJ
/-- Qualitative higher-regularity version of
`exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries`: entrywise higher membership of a
finite-coordinate metric supplies chosen second jets whose coordinate derivative arrays make the
schematic Ricci-DeTurck RHS `C^{0,α}`. -/
theorem exists_secondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_of_metric_entries
    {n : Type*} [Fintype n] [DecidableEq n]
    {δ : ℝ} {s : Set (ℝ × (n → ℝ))}
    {M : ℝ × (n → ℝ) → Matrix n n ℝ}
    (hM : ∀ i j, ParabolicC2AlphaOn α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ∃ J : ∀ i j, ParabolicSecondJet (fun z : ℝ × (n → ℝ) => M z i j) s,
      ParabolicC0AlphaOn α
        (fun z : ℝ × (n → ℝ) =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M z)
            (fun a i j => (J i j).spaceDeriv z (parabolicCoordinateUnitVector n a))
            (fun a b i j =>
              (J i j).spaceSecondDeriv z
                (parabolicCoordinateUnitVector n a) (parabolicCoordinateUnitVector n b))) s := by
  classical
  choose R _hR_nonneg hR using hM
  rcases
    ParabolicC2AlphaNormLe.exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries
      (α := α) (R := R) (δ := δ) (s := s) (M := M) hR hδpos hdet with
    ⟨J, hJ⟩
  exact ⟨J, hJ.c0AlphaOn⟩
/-- Pi-valued finite-family qualitative higher-regularity version of
`exists_secondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries`. -/
theorem exists_secondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_pi_family_of_metric_entries
    {κ n : Type*} [Fintype κ] [Fintype n] [DecidableEq n]
    {δ : ℝ} {s : Set (ℝ × (n → ℝ))}
    {M : κ → ℝ × (n → ℝ) → Matrix n n ℝ}
    (hM : ∀ r i j, ParabolicC2AlphaOn α (fun z => M r z i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × (n → ℝ)⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ∃ J : ∀ r i j, ParabolicSecondJet (fun z : ℝ × (n → ℝ) => M r z i j) s,
      ParabolicC0AlphaOn α
        (fun z : ℝ × (n → ℝ) => fun r : κ =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M r z)
            (fun a i j => (J r i j).spaceDeriv z (parabolicCoordinateUnitVector n a))
            (fun a b i j =>
              (J r i j).spaceSecondDeriv z
                (parabolicCoordinateUnitVector n a) (parabolicCoordinateUnitVector n b))) s := by
  classical
  choose J hJ using fun r =>
    exists_secondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_of_metric_entries
      (α := α) (δ := δ) (s := s) (M := M r) (hM r) hδpos (hdet r)
  refine ⟨J, ?_⟩
  exact ParabolicC0AlphaOn.pi hJ

end ParabolicC2AlphaOn

namespace parabolicC2AlphaSubmodule

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Coordinate projection from a matrix-valued higher parabolic submodule. -/
def matrixApplyLinearMap {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A] (i : m) (j : n) :
    parabolicC2AlphaSubmodule X (Matrix m n A) α s →ₗ[ℝ]
      parabolicC2AlphaSubmodule X A α s :=
  continuousLinearMap (X := X) (E := Matrix m n A) (α := α) (s := s)
    ((ContinuousLinearMap.proj j : (n → A) →L[ℝ] A).comp
      (ContinuousLinearMap.proj i : Matrix m n A →L[ℝ] n → A))

@[simp]
theorem matrixApplyLinearMap_apply {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A] (i : m) (j : n)
    (u : parabolicC2AlphaSubmodule X (Matrix m n A) α s) (z : ℝ × X) :
    matrixApplyLinearMap (X := X) (α := α) (s := s) i j u z = u z i j :=
  rfl

/-- The noncanonical chosen second jet of a matrix entry. -/
noncomputable def chosenMatrixEntrySecondJet {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A] (i : m) (j : n)
    (u : parabolicC2AlphaSubmodule X (Matrix m n A) α s) :
    ParabolicSecondJet (fun z : ℝ × X => u z i j) s :=
  chosenSecondJet (X := X) (E := A) (α := α) (s := s)
    (matrixApplyLinearMap (X := X) (α := α) (s := s) i j u)
/-- Quantitative chosen-entry-jet handoff for the schematic Ricci-DeTurck RHS.

Under unique-differentiability of the time and spatial slices, the higher norm-ball controls
for the metric entries transport to the deterministic `chosenMatrixEntrySecondJet` fields, so the
existing primitive-input schematic RHS estimate can be used without an existential jet family. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions_of_unique
    {n : Type*} [Fintype n] [DecidableEq n] (v : n → X)
    {R : n → n → ℝ} {δ : ℝ}
    (M : parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hM : ∀ i j, ParabolicC2AlphaNormLe (R i j) α (fun z : ℝ × X => M z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaNormLe
      (ParabolicC2AlphaNormLe.ricciDeTurckSchematicMatrixBoundConst (n := n) δ R
        (firstDerivativeVectorRadius (X := X) v R)
        (secondDerivativeVectorRadius (X := X) v R))
      α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j M).spaceDeriv
              z (v a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := X) (α := α) (s := s) i j M).spaceSecondDeriv z (v a) (v b))) s := by
  have hM0 : ∀ i j, ParabolicC0AlphaNormLe (R i j) α
      (fun z : ℝ × X => M z i j) s := by
    intro i j
    exact (hM i j).value_c0AlphaNormLe_self
  have hD : ∀ a i j, ParabolicC0AlphaNormLe
      (firstDerivativeVectorRadius (X := X) v R a i j) α
      (fun z : ℝ × X =>
        (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j M).spaceDeriv
          z (v a)) s := by
    intro a i j
    have hctrl := (hM i j).secondJet_c0AlphaNormLe_self_of_unique
      (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j M) htime hspace
    have hread := hctrl.2.1.continuousLinearMap_opNorm
      (firstDerivativeVectorReadout (X := X) (E := ℝ) (v a))
    simpa [firstDerivativeVectorRadius, firstDerivativeVectorReadoutOpNorm] using hread
  have hH : ∀ a b i j, ParabolicC0AlphaNormLe
      (secondDerivativeVectorRadius (X := X) v R a b i j) α
      (fun z : ℝ × X =>
        (chosenMatrixEntrySecondJet
          (X := X) (α := α) (s := s) i j M).spaceSecondDeriv z (v a) (v b)) s := by
    intro a b i j
    have hctrl := (hM i j).secondJet_c0AlphaNormLe_self_of_unique
      (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j M) htime hspace
    have hread := hctrl.2.2.1.continuousLinearMap_opNorm
      (secondDerivativeVectorReadout (X := X) (E := ℝ) (v a) (v b))
    simpa [secondDerivativeVectorRadius, secondDerivativeVectorReadoutOpNorm] using hread
  simpa [ParabolicC2AlphaNormLe.ricciDeTurckSchematicMatrixBoundConst] using
    (ParabolicC0AlphaNormLe.ricciDeTurck_schematic_of_entries
      (X := X) (α := α) (s := s) (𝕜 := ℝ) (δ := δ)
      (R := R) (RD := firstDerivativeVectorRadius (X := X) v R)
      (RH := secondDerivativeVectorRadius (X := X) v R)
      (M := fun z : ℝ × X => M z)
      (D := fun z a i j =>
        (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j M).spaceDeriv z (v a))
      (H := fun z a b i j =>
        (chosenMatrixEntrySecondJet
          (X := X) (α := α) (s := s) i j M).spaceSecondDeriv z (v a) (v b))
      hM0 hD hH hδpos hdet)

/-- Coordinate-space version of
`chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions_of_unique`. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_of_metric_entries_of_unique
    {n : Type*} [Fintype n] [DecidableEq n]
    {R : n → n → ℝ} {δ : ℝ} {s : Set (ℝ × (n → ℝ))}
    (M : parabolicC2AlphaSubmodule (n → ℝ) (Matrix n n ℝ) α s)
    (hM : ∀ i j,
      ParabolicC2AlphaNormLe (R i j) α (fun z : ℝ × (n → ℝ) => M z i j) s)
    (htime : ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaNormLe
      (ParabolicC2AlphaNormLe.ricciDeTurckSchematicMatrixBoundConst (n := n) δ R
        (firstDerivativeCoordinateRadius (n := n) R)
        (secondDerivativeCoordinateRadius (n := n) R))
      α
      (fun z : ℝ × (n → ℝ) =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet (X := n → ℝ) (α := α) (s := s) i j M).spaceDeriv
              z (parabolicCoordinateUnitVector n a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := n → ℝ) (α := α) (s := s) i j M).spaceSecondDeriv z
                (parabolicCoordinateUnitVector n a) (parabolicCoordinateUnitVector n b))) s := by
  simpa using
    chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions_of_unique
      (X := n → ℝ) (α := α) (s := s) (parabolicCoordinateUnitVector n)
      (R := R) (δ := δ) M hM htime hspace hδpos hdet
/-- Pi-valued finite-family quantitative chosen-entry-jet handoff for the schematic
Ricci-DeTurck RHS with family-dependent direction readouts. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries_family_directions_of_unique
    {κ n : Type*} [Fintype κ] [Fintype n] [DecidableEq n] (v : κ → n → X)
    {R : κ → n → n → ℝ} {δ : ℝ}
    (M : κ → parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hM : ∀ r i j, ParabolicC2AlphaNormLe (R r i j) α
      (fun z : ℝ × X => M r z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ParabolicC0AlphaNormLe
      (∑ r, ParabolicC2AlphaNormLe.ricciDeTurckSchematicMatrixBoundConst
        (n := n) δ (R r)
        (firstDerivativeVectorRadius (X := X) (v r) (R r))
        (secondDerivativeVectorRadius (X := X) (v r) (R r)))
      α
      (fun z : ℝ × X => fun r : κ =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M r)).spaceDeriv
              z (v r a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := X) (α := α) (s := s) i j (M r)).spaceSecondDeriv
                z (v r a) (v r b))) s := by
  exact ParabolicC0AlphaNormLe.pi (X := X) (α := α) (s := s)
    (N := fun r =>
      ParabolicC2AlphaNormLe.ricciDeTurckSchematicMatrixBoundConst
        (n := n) δ (R r)
        (firstDerivativeVectorRadius (X := X) (v r) (R r))
        (secondDerivativeVectorRadius (X := X) (v r) (R r)))
    (u := fun z : ℝ × X => fun r : κ =>
      ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M r z)
        (fun a i j =>
          (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M r)).spaceDeriv
            z (v r a))
        (fun a b i j =>
          (chosenMatrixEntrySecondJet
            (X := X) (α := α) (s := s) i j (M r)).spaceSecondDeriv
              z (v r a) (v r b)))
    fun r =>
      chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions_of_unique
        (X := X) (α := α) (s := s) (v r)
        (R := R r) (δ := δ) (M r) (hM r) htime hspace hδpos (hdet r)

/-- Pi-valued finite-family quantitative chosen-entry-jet handoff with one shared finite
direction family. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries_directions_of_unique
    {κ n : Type*} [Fintype κ] [Fintype n] [DecidableEq n] (v : n → X)
    {R : κ → n → n → ℝ} {δ : ℝ}
    (M : κ → parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hM : ∀ r i j, ParabolicC2AlphaNormLe (R r i j) α
      (fun z : ℝ × X => M r z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ParabolicC0AlphaNormLe
      (∑ r, ParabolicC2AlphaNormLe.ricciDeTurckSchematicMatrixBoundConst
        (n := n) δ (R r)
        (firstDerivativeVectorRadius (X := X) v (R r))
        (secondDerivativeVectorRadius (X := X) v (R r)))
      α
      (fun z : ℝ × X => fun r : κ =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M r)).spaceDeriv
              z (v a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := X) (α := α) (s := s) i j (M r)).spaceSecondDeriv
                z (v a) (v b))) s := by
  simpa using
    chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries_family_directions_of_unique
      (X := X) (α := α) (s := s) (v := fun _ => v)
      (R := R) (δ := δ) M hM htime hspace hδpos hdet

/-- Coordinate-space Pi-valued finite-family quantitative chosen-entry-jet handoff. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries_of_unique
    {κ n : Type*} [Fintype κ] [Fintype n] [DecidableEq n]
    {R : κ → n → n → ℝ} {δ : ℝ} {s : Set (ℝ × (n → ℝ))}
    (M : κ → parabolicC2AlphaSubmodule (n → ℝ) (Matrix n n ℝ) α s)
    (hM : ∀ r i j, ParabolicC2AlphaNormLe (R r i j) α
      (fun z : ℝ × (n → ℝ) => M r z i j) s)
    (htime : ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × (n → ℝ)⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ParabolicC0AlphaNormLe
      (∑ r, ParabolicC2AlphaNormLe.ricciDeTurckSchematicMatrixBoundConst
        (n := n) δ (R r)
        (firstDerivativeCoordinateRadius (n := n) (R r))
        (secondDerivativeCoordinateRadius (n := n) (R r)))
      α
      (fun z : ℝ × (n → ℝ) => fun r : κ =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet
              (X := n → ℝ) (α := α) (s := s) i j (M r)).spaceDeriv
                z (parabolicCoordinateUnitVector n a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := n → ℝ) (α := α) (s := s) i j (M r)).spaceSecondDeriv z
                (parabolicCoordinateUnitVector n a) (parabolicCoordinateUnitVector n b))) s := by
  simpa using
    chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries_directions_of_unique
      (X := n → ℝ) (α := α) (s := s) (parabolicCoordinateUnitVector n)
      (R := R) (δ := δ) M hM htime hspace hδpos hdet

/-- State-space Lipschitz bridge for the chosen-entry-jet schematic Ricci-DeTurck RHS.

This specializes
`ParabolicC2AlphaNormLe.ricciDeTurckSchematicMatrix_lipschitzOnWith_of_metric_entries_directions_of_unique`
to the deterministic `chosenMatrixEntrySecondJet` supplied by the higher parabolic submodule,
removing the separate caller-supplied second-jet family from downstream chart estimates. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_lipschitzOnWith_of_metric_entries_directions_of_unique
    {Y n : Type*} [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (ξ : n → X)
    {δ : ℝ} {C KM : n → n → ℝ} {stateSet : Set Y}
    (M : Y → parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hC : ∀ i j, 0 ≤ C i j) (hKM : ∀ i j, 0 ≤ KM i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C i j) α (fun z : ℝ × X => M u z i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM i j * dist u v) α
        (fun z : ℝ × X => M u z i j - M v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C
            (firstDerivativeVectorRadius (X := X) ξ C)
            (secondDerivativeVectorRadius (X := X) ξ C)
            (∑ i, ∑ j, KM i j)
            (∑ a, ∑ i, ∑ j, firstDerivativeVectorRadius (X := X) ξ KM a i j)
            (fun i j => ∑ a, ∑ b,
              secondDerivativeVectorRadius (X := X) ξ KM a b i j),
          by
            exact ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
              (𝕜 := ℝ) hδpos
              (firstDerivativeVectorRadius_nonneg (X := X) ξ hC)
              (secondDerivativeVectorRadius_nonneg (X := X) ξ hC)
              (Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hKM i j)
              (Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun i _hi =>
                  Finset.sum_nonneg fun j _hj =>
                    firstDerivativeVectorRadius_nonneg (X := X) ξ hKM a i j)
              (fun i j =>
                Finset.sum_nonneg fun a _ha =>
                  Finset.sum_nonneg fun b _hb =>
                    secondDerivativeVectorRadius_nonneg (X := X) ξ hKM a b i j)⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M u z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M u)).spaceDeriv
              z (ξ a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := X) (α := α) (s := s) i j (M u)).spaceSecondDeriv z (ξ a) (ξ b)))
        stateSet := by
  intro z hz
  exact
    ParabolicC2AlphaNormLe.ricciDeTurckSchematicMatrix_lipschitzOnWith_of_metric_entries_directions_of_unique
      (X := X) (α := α) (s := s) ξ
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (M := fun u z => M u z)
      (J := fun u i j => chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M u))
      hC hKM hM hMdiff htime hspace hδpos hdet hz

/-- Coordinate-space version of
`chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_lipschitzOnWith_of_metric_entries_directions_of_unique`. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_lipschitzOnWith_of_metric_entries_of_unique
    {Y n : Type*} [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    {δ : ℝ} {C KM : n → n → ℝ} {stateSet : Set Y}
    {s : Set (ℝ × (n → ℝ))}
    (M : Y → parabolicC2AlphaSubmodule (n → ℝ) (Matrix n n ℝ) α s)
    (hC : ∀ i j, 0 ≤ C i j) (hKM : ∀ i j, 0 ≤ KM i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C i j) α (fun z : ℝ × (n → ℝ) => M u z i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM i j * dist u v) α
        (fun z : ℝ × (n → ℝ) => M u z i j - M v z i j) s)
    (htime : ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖) :
    ∀ ⦃z : ℝ × (n → ℝ)⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C
            (firstDerivativeCoordinateRadius (n := n) C)
            (secondDerivativeCoordinateRadius (n := n) C)
            (∑ i, ∑ j, KM i j)
            (∑ a, ∑ i, ∑ j, firstDerivativeCoordinateRadius (n := n) KM a i j)
            (fun i j => ∑ a, ∑ b,
              secondDerivativeCoordinateRadius (n := n) KM a b i j),
          by
            exact ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
              (𝕜 := ℝ) hδpos
              (firstDerivativeCoordinateRadius_nonneg (n := n) hC)
              (secondDerivativeCoordinateRadius_nonneg (n := n) hC)
              (Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hKM i j)
              (Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun i _hi =>
                  Finset.sum_nonneg fun j _hj =>
                    firstDerivativeCoordinateRadius_nonneg (n := n) hKM a i j)
              (fun i j =>
                Finset.sum_nonneg fun a _ha =>
                  Finset.sum_nonneg fun b _hb =>
                    secondDerivativeCoordinateRadius_nonneg (n := n) hKM a b i j)⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M u z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet (X := n → ℝ) (α := α) (s := s) i j (M u)).spaceDeriv
              z (parabolicCoordinateUnitVector n a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := n → ℝ) (α := α) (s := s) i j (M u)).spaceSecondDeriv z
                (parabolicCoordinateUnitVector n a) (parabolicCoordinateUnitVector n b)))
        stateSet := by
  simpa using
    chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_lipschitzOnWith_of_metric_entries_directions_of_unique
      (X := n → ℝ) (α := α) (s := s) (parabolicCoordinateUnitVector n)
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      M hC hKM hM hMdiff htime hspace hδpos hdet

/-- Finite-family state-space Lipschitz bridge for deterministic matrix-entry chosen jets and
family-dependent direction readouts. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_metric_entries_family_directions_of_unique
    {κ Y n : Type*} [Fintype κ] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (ξ : κ → n → X)
    {δ : ℝ} {C KM : κ → n → n → ℝ} {stateSet : Set Y}
    (M : κ → Y → parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hC : ∀ r i j, 0 ≤ C r i j) (hKM : ∀ r i j, 0 ≤ KM r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C r i j) α (fun z : ℝ × X => M r u z i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM r i j * dist u v) α
        (fun z : ℝ × X => M r u z i j - M r v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ r ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r)
            (firstDerivativeVectorRadius (X := X) (ξ r) (C r))
            (secondDerivativeVectorRadius (X := X) (ξ r) (C r))
            (∑ i, ∑ j, KM r i j)
            (∑ a, ∑ i, ∑ j,
              firstDerivativeVectorRadius (X := X) (ξ r) (KM r) a i j)
            (fun i j => ∑ a, ∑ b,
              secondDerivativeVectorRadius (X := X) (ξ r) (KM r) a b i j),
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos
            (firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
            (secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
            (Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hKM r i j)
            (Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun i _hi =>
                Finset.sum_nonneg fun j _hj =>
                  firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r) a i j)
            (fun i j =>
              Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb =>
                  secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r) a b i j)⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M r u)).spaceDeriv
              z (ξ r a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := X) (α := α) (s := s) i j (M r u)).spaceSecondDeriv
                z (ξ r a) (ξ r b)))
        stateSet := by
  intro r z hz
  exact
    ParabolicC2AlphaNormLe.ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_metric_entries_family_directions_of_unique
      (X := X) (α := α) (s := s) ξ
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (M := fun r u z => M r u z)
      (J := fun r u i j =>
        chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M r u))
      hC hKM hM hMdiff htime hspace hδpos hdet r hz

/-- Pi-valued finite-family state-space Lipschitz bridge for deterministic matrix-entry chosen
jets. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_lipschitzOnWith_pi_family_of_metric_entries_family_directions_of_unique
    {κ Y n : Type*} [Fintype κ] [DecidableEq κ] [PseudoMetricSpace Y]
    [Fintype n] [DecidableEq n]
    (ξ : κ → n → X)
    {δ : ℝ} {C KM : κ → n → n → ℝ} {stateSet : Set Y}
    (M : κ → Y → parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hC : ∀ r i j, 0 ≤ C r i j) (hKM : ∀ r i j, 0 ≤ KM r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C r i j) α (fun z : ℝ × X => M r u z i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM r i j * dist u v) α
        (fun z : ℝ × X => M r u z i j - M r v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r)
            (firstDerivativeVectorRadius (X := X) (ξ r) (C r))
            (secondDerivativeVectorRadius (X := X) (ξ r) (C r))
            (∑ i, ∑ j, KM r i j)
            (∑ a, ∑ i, ∑ j,
              firstDerivativeVectorRadius (X := X) (ξ r) (KM r) a i j)
            (fun i j => ∑ a, ∑ b,
              secondDerivativeVectorRadius (X := X) (ξ r) (KM r) a b i j),
          Finset.sum_nonneg fun r _hr =>
            ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
              (𝕜 := ℝ) hδpos
              (firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
              (secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hC r))
              (Finset.sum_nonneg fun i _hi =>
                Finset.sum_nonneg fun j _hj => hKM r i j)
              (Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun i _hi =>
                  Finset.sum_nonneg fun j _hj =>
                    firstDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r) a i j)
              (fun i j =>
                Finset.sum_nonneg fun a _ha =>
                  Finset.sum_nonneg fun b _hb =>
                    secondDerivativeVectorRadius_nonneg (X := X) (ξ r) (hKM r)
                      a b i j)⟩
        (fun u : Y => fun r =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M r u z)
            (fun a i j =>
              (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j
                (M r u)).spaceDeriv z (ξ r a))
            (fun a b i j =>
              (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j
                (M r u)).spaceSecondDeriv z (ξ r a) (ξ r b)))
        stateSet := by
  intro z hz
  exact
    ParabolicC2AlphaNormLe.ricciDeTurckSchematicMatrix_lipschitzOnWith_pi_family_of_metric_entries_family_directions_of_unique
      (X := X) (α := α) (s := s) ξ
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (M := fun r u z => M r u z)
      (J := fun r u i j =>
        chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M r u))
      hC hKM hM hMdiff htime hspace hδpos hdet hz

/-- Compact-coordinate readout Lipschitz bridge for deterministic matrix-entry chosen jets. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_metric_entries_directions_of_unique
    {ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (ξ : n → X)
    {δ : ℝ} {C KM : n → n → ℝ} {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    (M : Y → parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hC : ∀ i j, 0 ≤ C i j) (hKM : ∀ i j, 0 ≤ KM i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C i j) α (fun z : ℝ × X => M u z i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM i j * dist u v) α
        (fun z : ℝ × X => M u z i j - M v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z)
        (fun a i j =>
          (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M u)).spaceDeriv
            z (ξ a))
        (fun a b i j =>
          (chosenMatrixEntrySecondJet
            (X := X) (α := α) (s := s) i j (M u)).spaceSecondDeriv z (ξ a) (ξ b))) :
    LipschitzOnWith
      ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ C
          (firstDerivativeVectorRadius (X := X) ξ C)
          (secondDerivativeVectorRadius (X := X) ξ C)
          (∑ i, ∑ j, KM i j)
          (∑ a, ∑ i, ∑ j, firstDerivativeVectorRadius (X := X) ξ KM a i j)
          (fun i j => ∑ a, ∑ b,
            secondDerivativeVectorRadius (X := X) ξ KM a b i j),
        ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
          (𝕜 := ℝ) hδpos
          (firstDerivativeVectorRadius_nonneg (X := X) ξ hC)
          (secondDerivativeVectorRadius_nonneg (X := X) ξ hC)
          (Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hKM i j)
          (Finset.sum_nonneg fun a _ha =>
            Finset.sum_nonneg fun i _hi =>
              Finset.sum_nonneg fun j _hj =>
                firstDerivativeVectorRadius_nonneg (X := X) ξ hKM a i j)
          (fun i j =>
            Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb =>
                secondDerivativeVectorRadius_nonneg (X := X) ξ hKM a b i j)⟩
      (fun u : Y =>
        parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u))
      stateSet := by
  simpa using
    ParabolicC2AlphaNormLe.ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_metric_entries_directions_of_unique
      (X := X) (α := α) (s := s) Kdom hKdom hα ξ
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (A := A) (M := fun u z => M u z)
      (J := fun u i j =>
        chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M u))
      hC hKM hM hMdiff htime hspace hδpos hdet hAeq

/-- Linear finite-cover readout version of
`chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_metric_entries_directions_of_unique`. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamilyLinearMap_of_metric_entries_directions_of_unique
    {ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (ξ : n → X)
    {δ : ℝ} {C KM : n → n → ℝ} {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    (M : Y → parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hC : ∀ i j, 0 ≤ C i j) (hKM : ∀ i j, 0 ≤ KM i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (C i j) α (fun z : ℝ × X => M u z i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i j,
      ParabolicC2AlphaNormLe (KM i j * dist u v) α
        (fun z : ℝ × X => M u z i j - M v z i j) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z)
        (fun a i j =>
          (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M u)).spaceDeriv
            z (ξ a))
        (fun a b i j =>
          (chosenMatrixEntrySecondJet
            (X := X) (α := α) (s := s) i j (M u)).spaceSecondDeriv z (ξ a) (ξ b))) :
    LipschitzOnWith
      ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ C
          (firstDerivativeVectorRadius (X := X) ξ C)
          (secondDerivativeVectorRadius (X := X) ξ C)
          (∑ i, ∑ j, KM i j)
          (∑ a, ∑ i, ∑ j, firstDerivativeVectorRadius (X := X) ξ KM a i j)
          (fun i j => ∑ a, ∑ b,
            secondDerivativeVectorRadius (X := X) ξ KM a b i j),
        ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
          (𝕜 := ℝ) hδpos
          (firstDerivativeVectorRadius_nonneg (X := X) ξ hC)
          (secondDerivativeVectorRadius_nonneg (X := X) ξ hC)
          (Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hKM i j)
          (Finset.sum_nonneg fun a _ha =>
            Finset.sum_nonneg fun i _hi =>
              Finset.sum_nonneg fun j _hj =>
                firstDerivativeVectorRadius_nonneg (X := X) ξ hKM a i j)
          (fun i j =>
            Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb =>
                secondDerivativeVectorRadius_nonneg (X := X) ξ hKM a b i j)⟩
      (fun u : Y =>
        parabolicC0AlphaSubmodule.toCompactCoordFamilyLinearMap
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u))
      stateSet := by
  simpa using
    chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_metric_entries_directions_of_unique
      (X := X) (α := α) (s := s) Kdom hKdom hα ξ
      (δ := δ) (C := C) (KM := KM) (stateSet := stateSet)
      (A := A) M hC hKM hM hMdiff htime hspace hδpos hdet hAeq
/-- A matrix-valued higher parabolic submodule element supplies a deterministic
chosen-entry-jet schematic Ricci-DeTurck RHS.  This is the noncanonical chosen-jet counterpart
of the existential qualitative matrix handoff. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_of_directions
    {n : Type*} [Fintype n] [DecidableEq n] (v : n → X)
    {δ : ℝ} (M : parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j M).spaceDeriv
              z (v a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := X) (α := α) (s := s) i j M).spaceSecondDeriv z (v a) (v b))) s := by
  have hM : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × X => M z i j) s := by
    intro i j
    exact (matrixApplyLinearMap (X := X) (α := α) (s := s) i j M).2.c0AlphaOn
  have hD : ∀ a i j, ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j M).spaceDeriv
          z (v a)) s := by
    intro a i j
    have hbase :
        ParabolicC0AlphaOn α
          (chosenMatrixEntrySecondJet
            (X := X) (α := α) (s := s) i j M).spaceDeriv s :=
      chosenSecondJet_spaceDeriv_c0AlphaOn
        (X := X) (E := ℝ) (α := α) (s := s)
        (matrixApplyLinearMap (X := X) (α := α) (s := s) i j M)
    simpa [chosenMatrixEntrySecondJet, firstDerivativeVectorReadout] using
      hbase.continuousLinearMap (firstDerivativeVectorReadout (X := X) (E := ℝ) (v a))
  have hH : ∀ a b i j, ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (chosenMatrixEntrySecondJet
          (X := X) (α := α) (s := s) i j M).spaceSecondDeriv z (v a) (v b)) s := by
    intro a b i j
    have hbase :
        ParabolicC0AlphaOn α
          (chosenMatrixEntrySecondJet
            (X := X) (α := α) (s := s) i j M).spaceSecondDeriv s :=
      chosenSecondJet_spaceSecondDeriv_c0AlphaOn
        (X := X) (E := ℝ) (α := α) (s := s)
        (matrixApplyLinearMap (X := X) (α := α) (s := s) i j M)
    simpa [chosenMatrixEntrySecondJet, secondDerivativeVectorReadout] using
      hbase.continuousLinearMap
        (secondDerivativeVectorReadout (X := X) (E := ℝ) (v a) (v b))
  have hport := (ParabolicC0AlphaOn.ricciDeTurck_schematic
      (X := X) (α := α) (s := s) (𝕜 := ℝ)
      (M := fun z : ℝ × X => M z)
      (D := fun z a i j =>
        (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j M).spaceDeriv z (v a))
      (H := fun z a b i j =>
        (chosenMatrixEntrySecondJet
          (X := X) (α := α) (s := s) i j M).spaceSecondDeriv z (v a) (v b))
      hM hD hH hδpos hdet)
  simp [ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix] at hport ⊢
  exact hport

/-- Finite-family form of
`chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_of_directions`
with one shared direction family. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_family_of_directions
    {κ n : Type*} [Fintype n] [DecidableEq n] (v : n → X)
    {δ : ℝ} (M : κ → parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ∀ r, ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M r)).spaceDeriv
              z (v a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := X) (α := α) (s := s) i j (M r)).spaceSecondDeriv
                z (v a) (v b))) s := by
  intro r
  exact chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_of_directions
    (X := X) (α := α) (s := s) v (M r) hδpos (hdet r)

/-- Pi-valued finite-family form of the chosen-entry-jet schematic RHS handoff with one shared
direction family. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_pi_family_of_directions
    {κ n : Type*} [Fintype κ] [Fintype n] [DecidableEq n] (v : n → X)
    {δ : ℝ} (M : κ → parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X => fun r : κ =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M r)).spaceDeriv
              z (v a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := X) (α := α) (s := s) i j (M r)).spaceSecondDeriv
                z (v a) (v b))) s :=
  ParabolicC0AlphaOn.pi fun r =>
    chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_family_of_directions
      (X := X) (α := α) (s := s) v M hδpos hdet r

/-- Finite-family form of the chosen-entry-jet schematic RHS handoff with family-dependent
direction readouts. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_family_of_family_directions
    {κ n : Type*} [Fintype n] [DecidableEq n] (v : κ → n → X)
    {δ : ℝ} (M : κ → parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ∀ r, ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M r)).spaceDeriv
              z (v r a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := X) (α := α) (s := s) i j (M r)).spaceSecondDeriv
                z (v r a) (v r b))) s := by
  intro r
  exact chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_of_directions
    (X := X) (α := α) (s := s) (v r) (M r) hδpos (hdet r)

/-- Pi-valued finite-family form of the chosen-entry-jet schematic RHS handoff with
family-dependent direction readouts. -/
theorem chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_pi_family_of_family_directions
    {κ n : Type*} [Fintype κ] [Fintype n] [DecidableEq n] (v : κ → n → X)
    {δ : ℝ} (M : κ → parabolicC2AlphaSubmodule X (Matrix n n ℝ) α s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X => fun r : κ =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r z)
          (fun a i j =>
            (chosenMatrixEntrySecondJet (X := X) (α := α) (s := s) i j (M r)).spaceDeriv
              z (v r a))
          (fun a b i j =>
            (chosenMatrixEntrySecondJet
              (X := X) (α := α) (s := s) i j (M r)).spaceSecondDeriv
                z (v r a) (v r b))) s :=
  ParabolicC0AlphaOn.pi fun r =>
    chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_family_of_family_directions
      (X := X) (α := α) (s := s) v M hδpos hdet r

/-- Assemble matrix-valued higher parabolic submodule elements from their entries. -/
def matrixOfEntriesLinearMap {m n A : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NormedAddCommGroup A] [NormedSpace ℝ A] :
    (m → n → parabolicC2AlphaSubmodule X A α s) →ₗ[ℝ]
      parabolicC2AlphaSubmodule X (Matrix m n A) α s where
  toFun u := ⟨fun z i j => u i j z,
    ParabolicC2AlphaOn.matrix_c2AlphaOn_of_entries
      (X := X) (α := α) (s := s) fun i j => (u i j).2⟩
  map_add' := by
    intro u v
    ext z i j
    rfl
  map_smul' := by
    intro c u
    ext z i j
    rfl

@[simp]
theorem matrixOfEntriesLinearMap_apply {m n A : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NormedAddCommGroup A] [NormedSpace ℝ A]
    (u : m → n → parabolicC2AlphaSubmodule X A α s) (z : ℝ × X)
    (i : m) (j : n) :
    matrixOfEntriesLinearMap (X := X) (α := α) (s := s) u z i j = u i j z :=
  rfl

end parabolicC2AlphaSubmodule

end AnalyticPDE
end RicciFlow
