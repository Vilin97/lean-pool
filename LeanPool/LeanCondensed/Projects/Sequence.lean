/-
Copyright (c) 2026 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.Module
import Mathlib.Topology.Category.LightProfinite.Sequence
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Common
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Spectral.Prespectral

/-!
# The split short exact sequence associated to `ℕ∪{∞}`

This file constructs `P R`, the cokernel of the inclusion of the
condensed free `R`-module on the singleton into the one on `ℕ∪{∞}`, and
shows that the associated short complex is a split short exact sequence.
-/

open CategoryTheory Limits LightProfinite OnePoint

namespace LightCondensed

noncomputable section

variable (R : Type _) [CommRing R]

/-- The inclusion `PUnit ↪ ℕ∪{∞}` sending the point to `∞`. -/
def ι : LightProfinite.of PUnit.{1} ⟶ ℕ∪{∞} :=
  (ConcreteCategory.ofHom ⟨fun _ ↦ ∞, continuous_const⟩)

/-- The retraction witnessing that `ι : PUnit → ℕ∪{∞}` is a split mono. -/
def ι_split : SplitMono ι where
  retraction := (ConcreteCategory.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩)
  id := rfl

/-- The map induced by `ι` between the free condensed `R`-modules. -/
def P_map :
    (free R).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶ (free R).obj (ℕ∪{∞}).toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free R).map ι

/-- The cokernel of `P_map`. -/
def P : LightCondMod R := cokernel (P_map R)

/-- The canonical projection to `P R`. -/
def P_proj : (free R).obj (ℕ∪{∞}).toCondensed ⟶ P R := cokernel.π _

/-- The short complex `P_map → P_proj` whose middle term is the free condensed
module on `ℕ∪{∞}`. -/
def PSequence : ShortComplex (LightCondMod R) :=
  ShortComplex.mk (P_map R) (P_proj R) (cokernel.condition _)

lemma PSequence_exact : (PSequence R).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_
    (SplitMono.mono ((ι_split).map (lightProfiniteToLightCondSet ⋙ free R)))
    coequalizer.π_epi
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  exact kernel.condition (P_proj R)

/-- A splitting of `PSequence`. -/
def PSequence_split : (PSequence R).Splitting :=
  ShortComplex.Splitting.ofExactOfRetraction _
    (PSequence_exact R).exact _
    ((ι_split).map (lightProfiniteToLightCondSet ⋙ free R)).id
    coequalizer.π_epi

/-- A section to the cokernel projection. -/
def P_proj_split : SplitEpi (P_proj R) where
  section_ := (PSequence_split R).s
  id := (PSequence_split R).s_g

/-- `P R` is a retract of the free condensed module on `ℕ∪{∞}`. -/
def P_retract : Retract (P R) ((free R).obj (ℕ∪{∞}).toCondensed) where
  i := _
  r := _
  retract := (PSequence_split R).s_g

/-- Universal property of `P R`: induce a map out of `P R` from a map out of
the free module on `ℕ∪{∞}` that kills `P_map`. -/
def P_homMk (A : LightCondMod R) (f : (free R).obj (ℕ∪{∞}).toCondensed ⟶ A)
    (hf : P_map R ≫ f = 0) : P R ⟶ A := cokernel.desc _ f hf

end

end LightCondensed
