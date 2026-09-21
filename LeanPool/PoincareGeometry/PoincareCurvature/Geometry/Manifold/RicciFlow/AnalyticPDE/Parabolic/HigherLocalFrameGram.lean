/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherMatrix
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.LocalFrameGram
/-!
# Higher parabolic local-frame Gram bridges

This module specializes the higher parabolic matrix second-jet readout layer to local-frame
Gram matrices.  It keeps the higher dependency out of `LocalFrameGram.lean`, while exposing a
proof interface where the first- and second-derivative primitive arrays are chosen from second
jets of the Gram entries.
-/

@[expose] public noncomputable section

open Bundle FiberBundle Set
open scoped Bundle Manifold ContDiff Topology NNReal BigOperators Matrix.Norms.Elementwise

namespace RicciFlow
namespace AnalyticPDE
namespace ParabolicC2AlphaNormLe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [ChartedSpace H E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable [IsManifold I 2 E]
variable [RiemannianBundle (TangentSpace I : E → Type _)]
variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : E → Type _)]

local notation "TE" => (TangentSpace I : E → Type _)
/-- Compact local-frame Gram bridge with second-jet primitive arrays.  On a normed-vector
chart model, entrywise `C^{2+α,1+α/2}` control of the Gram matrix supplies chosen second jets.
Reading those jets along the local-frame basis vectors gives the first- and second-derivative
arrays used by the schematic Ricci-DeTurck RHS estimate.  The compact local-frame determinant
lower bound is chosen internally. -/
theorem exists_secondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TE]
    [ContMDiffVectorBundle 2 E TE I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TE → E)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × E)} {α : ℝ} {R : ι → ι → ℝ}
    (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × E⦄, z ∈ K → z.2 ∈ e.baseSet)
    (hG : ∀ i j,
      ParabolicC2AlphaNormLe (R i j) α
        (fun z : ℝ × E =>
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) i j) K) :
    ∃ J : ∀ i j,
        ParabolicSecondJet
          (fun z : ℝ × E =>
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) i j) K,
      ∃ δ > 0,
        (∀ ⦃z : ℝ × E⦄, z ∈ K →
          δ ≤ ‖(show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
        ParabolicC0AlphaNormLe
          (ricciDeTurckSchematicMatrixBoundConst (n := ι) δ R
            (firstDerivativeVectorRadius (X := E) (fun a : ι => b a) R)
            (secondDerivativeVectorRadius (X := E) (fun a : ι => b a) R))
          α
          (fun z : ℝ × E =>
            ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (fun a i j => (J i j).spaceDeriv z (b a))
              (fun a c i j => (J i j).spaceSecondDeriv z (b a) (b c))) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  rcases
    ParabolicC2AlphaNormLe.exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions
      (X := E) (α := α) (v := fun a : ι => b a) (R := R) (δ := δ) (s := K)
      (M := fun z : ℝ × E =>
        (show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
      hG hδpos hdet with
    ⟨J, hJ⟩
  exact ⟨J, δ, hδpos, hdet, hJ⟩
/-- Quantitative deterministic chosen-entry-jet compact local-frame Gram bridge.  Under
unique-differentiability of the time and spatial slices, the entrywise higher norm-ball controls
transport to the noncanonical chosen entry jets of the assembled Gram matrix. -/
theorem chosenMatrixEntrySecondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_of_entries_of_timeSpace_isCompact_of_unique
    [IsContMDiffRiemannianBundle I 2 E TE]
    [ContMDiffVectorBundle 2 E TE I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TE → E)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × E)} {α : ℝ} {R : ι → ι → ℝ}
    (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × E⦄, z ∈ K → z.2 ∈ e.baseSet)
    (hG : ∀ i j,
      ParabolicC2AlphaNormLe (R i j) α
        (fun z : ℝ × E =>
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) i j) K)
    (htime : ∀ ⦃z : ℝ × E⦄, z ∈ K →
      UniqueDiffWithinAt ℝ (timeSliceDomain K z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × E⦄, z ∈ K →
      UniqueDiffWithinAt ℝ (spaceSliceDomain K z.1) z.2) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × E⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      (let G : parabolicC2AlphaSubmodule E (Matrix ι ι ℝ) α K :=
        ⟨fun z : ℝ × E =>
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2),
          ParabolicC2AlphaOn.matrix_c2AlphaOn_of_entries
            (X := E) (α := α) (s := K)
            (fun i j => ParabolicC2AlphaOn.of_normLe (hG i j))⟩
       ParabolicC0AlphaNormLe
        (ricciDeTurckSchematicMatrixBoundConst (n := ι) δ R
          (firstDerivativeVectorRadius (X := E) (fun a : ι => b a) R)
          (secondDerivativeVectorRadius (X := E) (fun a : ι => b a) R))
        α
        (fun z : ℝ × E =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
            (fun a i j =>
              (parabolicC2AlphaSubmodule.chosenMatrixEntrySecondJet
                (X := E) (α := α) (s := K) i j G).spaceDeriv z (b a))
            (fun a c i j =>
              (parabolicC2AlphaSubmodule.chosenMatrixEntrySecondJet
                (X := E) (α := α) (s := K) i j G).spaceSecondDeriv z (b a) (b c))) K) := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  let G : parabolicC2AlphaSubmodule E (Matrix ι ι ℝ) α K :=
    ⟨fun z : ℝ × E =>
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2),
      ParabolicC2AlphaOn.matrix_c2AlphaOn_of_entries
        (X := E) (α := α) (s := K)
        (fun i j => ParabolicC2AlphaOn.of_normLe (hG i j))⟩
  have hG_norm : ∀ i j,
      ParabolicC2AlphaNormLe (R i j) α (fun z : ℝ × E => G z i j) K := by
    intro i j
    simpa [G] using hG i j
  refine ⟨δ, hδpos, hdet, ?_⟩
  simpa [G] using
    parabolicC2AlphaSubmodule.chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions_of_unique
      (X := E) (α := α) (s := K) (v := fun a : ι => b a)
      (R := R) (δ := δ) G hG_norm htime hspace hδpos hdet
/-- Finite-family compact local-frame Gram bridge with second-jet primitive arrays.  One compact
Gram determinant lower bound is shared across the finite frame family, while each family member
reads its chosen second jets along its own local-frame basis. -/
theorem exists_secondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_pi_family_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TE]
    [ContMDiffVectorBundle 2 E TE I]
    {ρ : Type*} [Fintype ρ]
    (e : ρ → Trivialization E (TotalSpace.proj : TotalSpace E TE → E))
    [∀ r, MemTrivializationAtlas (e r)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ρ → Module.Basis ι ℝ E)
    {K : Set (ℝ × E)} {α : ℝ} {R : ρ → ι → ι → ℝ}
    (hK : IsCompact K)
    (hKbase : ∀ r ⦃z : ℝ × E⦄, z ∈ K → z.2 ∈ (e r).baseSet)
    (hG : ∀ r i j,
      ParabolicC2AlphaNormLe (R r i j) α
        (fun z : ℝ × E =>
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2) i j) K) :
    ∃ J : ∀ r i j,
        ParabolicSecondJet
          (fun z : ℝ × E =>
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2) i j) K,
      ∃ δ > 0,
        (∀ r ⦃z : ℝ × E⦄, z ∈ K →
          δ ≤ ‖(show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2).det‖) ∧
        ParabolicC0AlphaNormLe
          (∑ r, ricciDeTurckSchematicMatrixBoundConst (n := ι) δ (R r)
            (firstDerivativeVectorRadius (X := E) (fun a : ι => b r a) (R r))
            (secondDerivativeVectorRadius (X := E) (fun a : ι => b r a) (R r)))
          α
          (fun z : ℝ × E => fun r : ρ =>
            ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2)
              (fun a i j => (J r i j).spaceDeriv z (b r a))
              (fun a c i j => (J r i j).spaceSecondDeriv z (b r a) (b r c))) K := by
  rcases
    ParabolicC0AlphaOn.localFrameGramMatrix_det_family_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  rcases
    ParabolicC2AlphaNormLe.exists_secondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries_family_directions
      (X := E) (α := α) (v := fun r a => b r a) (R := R) (δ := δ) (s := K)
      (M := fun r z =>
        (show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2))
      hG hδpos hdet with
    ⟨J, hJ⟩
  exact ⟨J, δ, hδpos, hdet, hJ⟩
/-- Quantitative deterministic chosen-entry-jet finite-family compact local-frame Gram bridge.
The compact determinant lower bound is shared across the frame family, while each assembled
Gram matrix reads its chosen entry jets along its own local-frame basis. -/
theorem chosenMatrixEntrySecondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_pi_family_of_entries_of_timeSpace_isCompact_of_unique
    [IsContMDiffRiemannianBundle I 2 E TE]
    [ContMDiffVectorBundle 2 E TE I]
    {ρ : Type*} [Fintype ρ]
    (e : ρ → Trivialization E (TotalSpace.proj : TotalSpace E TE → E))
    [∀ r, MemTrivializationAtlas (e r)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ρ → Module.Basis ι ℝ E)
    {K : Set (ℝ × E)} {α : ℝ} {R : ρ → ι → ι → ℝ}
    (hK : IsCompact K)
    (hKbase : ∀ r ⦃z : ℝ × E⦄, z ∈ K → z.2 ∈ (e r).baseSet)
    (hG : ∀ r i j,
      ParabolicC2AlphaNormLe (R r i j) α
        (fun z : ℝ × E =>
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2) i j) K)
    (htime : ∀ ⦃z : ℝ × E⦄, z ∈ K →
      UniqueDiffWithinAt ℝ (timeSliceDomain K z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × E⦄, z ∈ K →
      UniqueDiffWithinAt ℝ (spaceSliceDomain K z.1) z.2) :
    ∃ δ > 0,
      (∀ r ⦃z : ℝ × E⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2).det‖) ∧
      (let G : ρ → parabolicC2AlphaSubmodule E (Matrix ι ι ℝ) α K :=
        fun r =>
          ⟨fun z : ℝ × E =>
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2),
            ParabolicC2AlphaOn.matrix_c2AlphaOn_of_entries
              (X := E) (α := α) (s := K)
              (fun i j => ParabolicC2AlphaOn.of_normLe (hG r i j))⟩
       ParabolicC0AlphaNormLe
        (∑ r, ricciDeTurckSchematicMatrixBoundConst (n := ι) δ (R r)
          (firstDerivativeVectorRadius (X := E) (fun a : ι => b r a) (R r))
          (secondDerivativeVectorRadius (X := E) (fun a : ι => b r a) (R r)))
        α
        (fun z : ℝ × E => fun r : ρ =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2)
            (fun a i j =>
              (parabolicC2AlphaSubmodule.chosenMatrixEntrySecondJet
                (X := E) (α := α) (s := K) i j (G r)).spaceDeriv z (b r a))
            (fun a c i j =>
              (parabolicC2AlphaSubmodule.chosenMatrixEntrySecondJet
                (X := E) (α := α) (s := K) i j (G r)).spaceSecondDeriv
                  z (b r a) (b r c))) K) := by
  rcases
    ParabolicC0AlphaOn.localFrameGramMatrix_det_family_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  let G : ρ → parabolicC2AlphaSubmodule E (Matrix ι ι ℝ) α K :=
    fun r =>
      ⟨fun z : ℝ × E =>
        (show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2),
        ParabolicC2AlphaOn.matrix_c2AlphaOn_of_entries
          (X := E) (α := α) (s := K)
          (fun i j => ParabolicC2AlphaOn.of_normLe (hG r i j))⟩
  have hG_norm : ∀ r i j,
      ParabolicC2AlphaNormLe (R r i j) α (fun z : ℝ × E => G r z i j) K := by
    intro r i j
    simpa [G] using hG r i j
  refine ⟨δ, hδpos, hdet, ?_⟩
  simpa [G] using
    parabolicC2AlphaSubmodule.chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_pi_family_of_metric_entries_family_directions_of_unique
      (X := E) (α := α) (s := K) (v := fun r a => b r a)
      (R := R) (δ := δ) G hG_norm htime hspace hδpos hdet

end ParabolicC2AlphaNormLe

namespace ParabolicC2AlphaOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [ChartedSpace H E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable [IsManifold I 2 E]
variable [RiemannianBundle (TangentSpace I : E → Type _)]
variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : E → Type _)]

local notation "TE" => (TangentSpace I : E → Type _)
/-- Qualitative compact local-frame Gram bridge with second-jet primitive arrays.  This is the
membership-only version of
`ParabolicC2AlphaNormLe.exists_secondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_of_entries_of_timeSpace_isCompact`. -/
theorem exists_secondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_c0AlphaOn_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TE]
    [ContMDiffVectorBundle 2 E TE I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TE → E)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × E)} {α : ℝ}
    (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × E⦄, z ∈ K → z.2 ∈ e.baseSet)
    (hG : ∀ i j,
      ParabolicC2AlphaOn α
        (fun z : ℝ × E =>
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) i j) K) :
    ∃ J : ∀ i j,
        ParabolicSecondJet
          (fun z : ℝ × E =>
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) i j) K,
      ∃ δ > 0,
        (∀ ⦃z : ℝ × E⦄, z ∈ K →
          δ ≤ ‖(show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
        ParabolicC0AlphaOn α
          (fun z : ℝ × E =>
            ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (fun a i j => (J i j).spaceDeriv z (b a))
              (fun a c i j => (J i j).spaceSecondDeriv z (b a) (b c))) K := by
  classical
  choose R _hR_nonneg hR using hG
  rcases
    ParabolicC2AlphaNormLe.exists_secondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_of_entries_of_timeSpace_isCompact
      (I := I) e b (K := K) (α := α) (R := R) hK hKbase hR with
    ⟨J, δ, hδpos, hdet, hJ⟩
  exact ⟨J, δ, hδpos, hdet, hJ.c0AlphaOn⟩
/-- Deterministic chosen-entry-jet compact local-frame Gram bridge.  Entrywise qualitative
higher regularity assembles the Gram matrix into the higher submodule, then reads the
noncanonical chosen entry jets along the local-frame basis. -/
theorem chosenMatrixEntrySecondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_c0AlphaOn_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TE]
    [ContMDiffVectorBundle 2 E TE I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TE → E)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × E)} {α : ℝ}
    (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × E⦄, z ∈ K → z.2 ∈ e.baseSet)
    (hG : ∀ i j,
      ParabolicC2AlphaOn α
        (fun z : ℝ × E =>
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) i j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × E⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      (let G : parabolicC2AlphaSubmodule E (Matrix ι ι ℝ) α K :=
        ⟨fun z : ℝ × E =>
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2),
          matrix_c2AlphaOn_of_entries (X := E) (α := α) (s := K) hG⟩
       ParabolicC0AlphaOn α
        (fun z : ℝ × E =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
            (fun a i j =>
              (parabolicC2AlphaSubmodule.chosenMatrixEntrySecondJet
                (X := E) (α := α) (s := K) i j G).spaceDeriv z (b a))
            (fun a c i j =>
              (parabolicC2AlphaSubmodule.chosenMatrixEntrySecondJet
                (X := E) (α := α) (s := K) i j G).spaceSecondDeriv z (b a) (b c))) K) := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  let G : parabolicC2AlphaSubmodule E (Matrix ι ι ℝ) α K :=
    ⟨fun z : ℝ × E =>
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2),
      matrix_c2AlphaOn_of_entries (X := E) (α := α) (s := K) hG⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  simpa [G] using
    parabolicC2AlphaSubmodule.chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_of_directions
      (X := E) (α := α) (s := K) (v := fun a : ι => b a) G hδpos hdet
/-- Finite-family deterministic chosen-entry-jet compact local-frame Gram bridge.  The compact
determinant lower bound is shared across the frame family, while each assembled higher matrix
submodule reads its own chosen entry jets along its own basis. -/
theorem chosenMatrixEntrySecondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_c0AlphaOn_pi_family_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TE]
    [ContMDiffVectorBundle 2 E TE I]
    {ρ : Type*} [Fintype ρ]
    (e : ρ → Trivialization E (TotalSpace.proj : TotalSpace E TE → E))
    [∀ r, MemTrivializationAtlas (e r)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ρ → Module.Basis ι ℝ E)
    {K : Set (ℝ × E)} {α : ℝ}
    (hK : IsCompact K)
    (hKbase : ∀ r ⦃z : ℝ × E⦄, z ∈ K → z.2 ∈ (e r).baseSet)
    (hG : ∀ r i j,
      ParabolicC2AlphaOn α
        (fun z : ℝ × E =>
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2) i j) K) :
    ∃ δ > 0,
      (∀ r ⦃z : ℝ × E⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2).det‖) ∧
      (let G : ρ → parabolicC2AlphaSubmodule E (Matrix ι ι ℝ) α K :=
        fun r =>
          ⟨fun z : ℝ × E =>
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2),
            matrix_c2AlphaOn_of_entries (X := E) (α := α) (s := K) (hG r)⟩
       ParabolicC0AlphaOn α
        (fun z : ℝ × E => fun r : ρ =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2)
            (fun a i j =>
              (parabolicC2AlphaSubmodule.chosenMatrixEntrySecondJet
                (X := E) (α := α) (s := K) i j (G r)).spaceDeriv z (b r a))
            (fun a c i j =>
              (parabolicC2AlphaSubmodule.chosenMatrixEntrySecondJet
                (X := E) (α := α) (s := K) i j (G r)).spaceSecondDeriv
                  z (b r a) (b r c))) K) := by
  rcases
    ParabolicC0AlphaOn.localFrameGramMatrix_det_family_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  let G : ρ → parabolicC2AlphaSubmodule E (Matrix ι ι ℝ) α K :=
    fun r =>
      ⟨fun z : ℝ × E =>
        (show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2),
        matrix_c2AlphaOn_of_entries (X := E) (α := α) (s := K) (hG r)⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  simpa [G] using
    parabolicC2AlphaSubmodule.chosenMatrixEntrySecondJet_ricciDeTurckSchematicMatrix_c0AlphaOn_pi_family_of_family_directions
      (X := E) (α := α) (s := K) (v := fun r a => b r a) G hδpos hdet
/-- Qualitative finite-family compact local-frame Gram bridge with second-jet primitive arrays.
This is the membership-only version of
`ParabolicC2AlphaNormLe.exists_secondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_pi_family_of_entries_of_timeSpace_isCompact`. -/
theorem exists_secondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_c0AlphaOn_pi_family_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TE]
    [ContMDiffVectorBundle 2 E TE I]
    {ρ : Type*} [Fintype ρ]
    (e : ρ → Trivialization E (TotalSpace.proj : TotalSpace E TE → E))
    [∀ r, MemTrivializationAtlas (e r)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ρ → Module.Basis ι ℝ E)
    {K : Set (ℝ × E)} {α : ℝ}
    (hK : IsCompact K)
    (hKbase : ∀ r ⦃z : ℝ × E⦄, z ∈ K → z.2 ∈ (e r).baseSet)
    (hG : ∀ r i j,
      ParabolicC2AlphaOn α
        (fun z : ℝ × E =>
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2) i j) K) :
    ∃ J : ∀ r i j,
        ParabolicSecondJet
          (fun z : ℝ × E =>
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2) i j) K,
      ∃ δ > 0,
        (∀ r ⦃z : ℝ × E⦄, z ∈ K →
          δ ≤ ‖(show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2).det‖) ∧
        ParabolicC0AlphaOn α
          (fun z : ℝ × E => fun r : ρ =>
            ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2)
              (fun a i j => (J r i j).spaceDeriv z (b r a))
              (fun a c i j => (J r i j).spaceSecondDeriv z (b r a) (b r c))) K := by
  classical
  choose R _hR_nonneg hR using hG
  rcases
    ParabolicC2AlphaNormLe.exists_secondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_pi_family_of_entries_of_timeSpace_isCompact
      (I := I) e b (K := K) (α := α) (R := R) hK hKbase hR with
    ⟨J, δ, hδpos, hdet, hJ⟩
  exact ⟨J, δ, hδpos, hdet, hJ.c0AlphaOn⟩

end ParabolicC2AlphaOn
end AnalyticPDE
end RicciFlow
