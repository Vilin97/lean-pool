/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.CanonicalConfiguration
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopCells
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.Model
/-!
# The finite Fox--Neuwirth top-cell model

For a prime number `p`, the model in this file is a finite disjoint union of closed
`(p - 1)`-simplices indexed by one-block barred permutations.  A point consists of a top
Fox--Neuwirth symbol together with barycentric coordinates indexed by the labels.  The associated
configuration uses the barycentric coordinate as first coordinate and the permutation rank as
second coordinate.  The second coordinates are pairwise distinct, so this is always a labelled
configuration.

This module supplies the concrete compact equivariant configuration model required at the end of
the finite model. The oriented mod-`p` cycle obtained by gluing boundary faces is constructed in
the chain modules.
-/

namespace NRR

open scoped BigOperators

variable {p : ℕ}

/-- One-block Fox--Neuwirth symbols, using the canonical top-cell type. -/
abbrev FoxNeuwirthTopCell (p : ℕ) := BarredPermutation.TopCell p

namespace FoxNeuwirthTopCell

/-- The identity order with no bars. -/
def identity (p : ℕ) : FoxNeuwirthTopCell p :=
  ⟨⟨1, ∅⟩, rfl⟩

instance : Nonempty (FoxNeuwirthTopCell p) := ⟨identity p⟩

noncomputable instance : MetricSpace (FoxNeuwirthTopCell p) :=
  MetricSpace.induced
    (fun c => ((Fintype.equivFin (FoxNeuwirthTopCell p)) c).val)
    (fun _ _ h => (Fintype.equivFin (FoxNeuwirthTopCell p)).injective (Fin.ext h))
    inferInstance

/-- Relabelling preserves the one-block condition. -/
def relabel (σ : Equiv.Perm (Fin p))
    (c : FoxNeuwirthTopCell p) : FoxNeuwirthTopCell p :=
  ⟨c.1.relabel σ, by simpa using c.2⟩

@[simp] theorem relabel_val
    (σ : Equiv.Perm (Fin p)) (c : FoxNeuwirthTopCell p) :
    (relabel σ c).1 = c.1.relabel σ :=
  rfl

@[simp] theorem relabel_one (c : FoxNeuwirthTopCell p) :
    relabel 1 c = c := by
  apply Subtype.ext
  simp [relabel]

theorem relabel_mul
    (σ τ : Equiv.Perm (Fin p)) (c : FoxNeuwirthTopCell p) :
    relabel (σ * τ) c = relabel σ (relabel τ c) := by
  apply Subtype.ext
  exact BarredPermutation.relabel_mul σ τ c.1

@[simp] theorem prime_smul_val
    (hp : Nat.Prime p) (g : PrimeSymmetry p)
    (c : FoxNeuwirthTopCell p) :
    (g • c : FoxNeuwirthTopCell p).1 =
      c.1.relabel (PrimeSymmetry.toPerm p g) :=
  rfl

end FoxNeuwirthTopCell

/-- Barycentric coordinates on a top-dimensional Fox--Neuwirth cell. -/
def FoxNeuwirthWeights (p : ℕ) :=
  ↥(stdSimplex ℝ (Fin p))

namespace FoxNeuwirthWeights

noncomputable instance : MetricSpace (FoxNeuwirthWeights p) :=
  MetricSpace.induced Subtype.val Subtype.val_injective inferInstance

instance : CoeFun (FoxNeuwirthWeights p) (fun _ => Fin p → ℝ) :=
  ⟨fun w => w.1⟩

@[simp] theorem nonneg (w : FoxNeuwirthWeights p) (i : Fin p) :
    0 ≤ w i :=
  w.2.1 i

@[simp] theorem sum_eq_one (w : FoxNeuwirthWeights p) :
    ∑ i, w i = 1 :=
  w.2.2

/-- Relabel barycentric coordinates by the established `σ.symm` convention. -/
def relabel (σ : Equiv.Perm (Fin p))
    (w : FoxNeuwirthWeights p) : FoxNeuwirthWeights p :=
  ⟨fun i => w (σ.symm i), by
    constructor
    · intro i
      exact w.nonneg (σ.symm i)
    · simpa [Equiv.sum_comp] using w.sum_eq_one⟩

@[simp] theorem relabel_apply
    (σ : Equiv.Perm (Fin p)) (w : FoxNeuwirthWeights p) (i : Fin p) :
    relabel σ w i = w (σ.symm i) :=
  rfl

@[simp] theorem relabel_one (w : FoxNeuwirthWeights p) :
    relabel 1 w = w := by
  apply Subtype.ext
  funext i
  have hi : (1 : Equiv.Perm (Fin p)).symm i = i :=
    (1 : Equiv.Perm (Fin p)).symm_apply_apply i
  exact congrArg (fun j => (w j : ℝ)) hi

theorem relabel_mul
    (σ τ : Equiv.Perm (Fin p)) (w : FoxNeuwirthWeights p) :
    relabel (σ * τ) w = relabel σ (relabel τ w) := by
  apply Subtype.ext
  funext i
  rfl

instance primeSymmetryAction (p : Nat) :
    MulAction (PrimeSymmetry p) (FoxNeuwirthWeights p) where
  smul g w := relabel (PrimeSymmetry.toPerm p g) w
  one_smul w := relabel_one w
  mul_smul g h w := by
    exact relabel_mul (PrimeSymmetry.toPerm p g)
      (PrimeSymmetry.toPerm p h) w

@[simp] theorem prime_smul_apply
    (p : Nat) (g : PrimeSymmetry p)
    (w : FoxNeuwirthWeights p) (i : Fin p) :
    (g • w) i = w ((PrimeSymmetry.toPerm p g).symm i) :=
  rfl

/-- Coordinate relabelling is continuous. -/
theorem continuous_relabel (σ : Equiv.Perm (Fin p)) :
    Continuous fun w : FoxNeuwirthWeights p => relabel σ w := by
  rw [continuous_induced_rng]
  exact continuous_pi fun i =>
    (continuous_apply (σ.symm i)).comp continuous_subtype_val

end FoxNeuwirthWeights

/-- Concrete finite polyhedron used as the prime configuration model. -/
def FoxNeuwirthTopCellModelPoint (p : ℕ) :=
  FoxNeuwirthTopCell p × FoxNeuwirthWeights p

namespace FoxNeuwirthTopCellModelPoint

noncomputable instance : CompactSpace (FoxNeuwirthWeights p) :=
  isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin p))

noncomputable instance : CompactSpace (FoxNeuwirthTopCell p) :=
  Finite.compactSpace

noncomputable instance : MetricSpace (FoxNeuwirthTopCellModelPoint p) :=
  inferInstanceAs (MetricSpace (FoxNeuwirthTopCell p × FoxNeuwirthWeights p))

noncomputable instance : CompactSpace (FoxNeuwirthTopCellModelPoint p) :=
  inferInstanceAs (CompactSpace (FoxNeuwirthTopCell p × FoxNeuwirthWeights p))

theorem nonempty (hp : Nat.Prime p) : Nonempty (FoxNeuwirthTopCellModelPoint p) :=
  ⟨FoxNeuwirthTopCell.identity p,
    ⟨fun _ => (p : ℝ)⁻¹, by
      constructor
      · intro i; positivity
      · simp [Finset.sum_const, hp.ne_zero]⟩⟩

instance (p : Nat) :
    MulAction (PrimeSymmetry p) (FoxNeuwirthTopCellModelPoint p) where
  smul g z := (g • z.1, g • z.2)
  one_smul z := by
    apply Prod.ext
    · exact one_smul _ z.1
    · exact one_smul _ z.2
  mul_smul g h z := by
    apply Prod.ext
    · exact mul_smul g h z.1
    · exact mul_smul g h z.2

/-- The labelled point associated with a top-cell symbol and barycentric coordinates. -/
noncomputable def site
    (z : FoxNeuwirthTopCellModelPoint p) (i : Fin p) : E2 :=
  !₂[z.2 i, ((z.1.1.rank i).1 : ℝ)]

@[simp] theorem site_x
    (z : FoxNeuwirthTopCellModelPoint p) (i : Fin p) :
    z.site i 0 = z.2 i := by
  simp [site]

@[simp] theorem site_y
    (z : FoxNeuwirthTopCellModelPoint p) (i : Fin p) :
    z.site i 1 = ((z.1.1.rank i).1 : ℝ) := by
  simp [site]

/-- The second coordinate records the permutation rank, hence the site map is injective. -/
theorem site_injective (z : FoxNeuwirthTopCellModelPoint p) :
    Function.Injective z.site := by
  intro i j hij
  apply z.1.1.rank.injective
  apply Fin.ext
  have hy : ((z.1.1.rank i).1 : ℝ) = ((z.1.1.rank j).1 : ℝ) := by
    simpa [site] using congrArg (fun q : E2 => q 1) hij
  exact_mod_cast hy

/-- Embedded labelled configuration. -/
noncomputable def toConfig
    (z : FoxNeuwirthTopCellModelPoint p) : Config p :=
  ⟨z.site, z.site_injective⟩

@[simp] theorem toConfig_pts
    (z : FoxNeuwirthTopCellModelPoint p) (i : Fin p) :
    z.toConfig.pts i = z.site i :=
  rfl

/-- Relabelling the model point relabels its configuration. -/
theorem toConfig_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry p)
    (z : FoxNeuwirthTopCellModelPoint p) :
    (g • z).toConfig = g • z.toConfig := by
  apply Subtype.ext
  funext i
  ext j
  fin_cases j
  · change z.2 ((PrimeSymmetry.toPerm p g).symm i) = _
    rfl
  · change (((z.1.1.rank ((PrimeSymmetry.toPerm p g).symm i)).1 : ℕ) : ℝ) = _
    rfl

/-- The configuration map is continuous. -/
theorem continuous_toConfig :
    Continuous (toConfig : FoxNeuwirthTopCellModelPoint p → Config p) := by
  rw [continuous_induced_rng]
  exact continuous_pi fun i => by
    change Continuous fun z : FoxNeuwirthTopCellModelPoint p =>
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm
        !₂[z.2 i, ((z.1.1.rank i).1 : ℝ)]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous.comp
    rw [continuous_pi_iff]
    intro j
    fin_cases j
    · exact (continuous_apply i).comp
        ((continuous_subtype_val : Continuous (Subtype.val :
          FoxNeuwirthWeights p → (Fin p → ℝ))).comp continuous_snd)
    · exact ((continuous_of_discreteTopology :
        Continuous fun c : FoxNeuwirthTopCell p =>
          ((c.1.rank i).1 : ℝ)).comp continuous_fst)

/-- Equivariant reference map: first-coordinate vector with its diagonal part removed. -/
noncomputable def reference
    (hp : Nat.Prime p)
    (z : FoxNeuwirthTopCellModelPoint p) : ZeroSum p :=
  coordinateDeviation hp.pos z.2.1

/-- The reference map is continuous. -/
theorem continuous_reference (hp : Nat.Prime p) :
    Continuous (reference hp : FoxNeuwirthTopCellModelPoint p → ZeroSum p) := by
  exact (coordinateDeviation hp.pos).continuous_of_finiteDimensional.comp
    continuous_subtype_val |>.comp continuous_snd

/-- The reference map is equivariant. -/
theorem reference_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry p)
    (z : FoxNeuwirthTopCellModelPoint p) :
    reference hp (g • z) = g • reference hp z := by
  change coordinateDeviation hp.pos (g • z.2.1) = _
  exact coordinateDeviation_prime_smul hp z.2.1 g

/-- Group actions on the finite-cell model are continuous. -/
theorem continuous_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry p) :
    Continuous fun z : FoxNeuwirthTopCellModelPoint p => g • z := by
  exact
    ((continuous_of_discreteTopology.comp continuous_fst).prodMk
      ((FoxNeuwirthWeights.continuous_relabel
        (PrimeSymmetry.toPerm p g)).comp continuous_snd))

end FoxNeuwirthTopCellModelPoint

/-- The concrete compact equivariant model produced by the Fox--Neuwirth top-cell atlas. -/
noncomputable def foxNeuwirthTopCellModel
    (hp : Nat.Prime p) : PrimeConfigurationModel hp := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Nonempty (FoxNeuwirthTopCellModelPoint p) := by
    exact ⟨FoxNeuwirthTopCell.identity p,
      ⟨fun _ => (p : ℝ)⁻¹, by
        constructor
        · intro i; positivity
        · simp [Finset.sum_const, hp.ne_zero]⟩⟩
  exact
    { Point := FoxNeuwirthTopCellModelPoint p
      continuous_smul := FoxNeuwirthTopCellModelPoint.continuous_smul hp
      toConfig :=
        ⟨FoxNeuwirthTopCellModelPoint.toConfig,
          FoxNeuwirthTopCellModelPoint.continuous_toConfig⟩
      toConfig_equivariant := by
        intro g z
        exact FoxNeuwirthTopCellModelPoint.toConfig_smul hp g z
      reference :=
        ⟨FoxNeuwirthTopCellModelPoint.reference hp,
          FoxNeuwirthTopCellModelPoint.continuous_reference hp⟩
      reference_equivariant := by
        intro g z
        exact FoxNeuwirthTopCellModelPoint.reference_smul hp g z }

/-- The construction gives a concrete compact prime configuration model for every prime. -/
theorem foxNeuwirthTopCellModel_nonempty
    (hp : Nat.Prime p) :
    Nonempty (PrimeConfigurationModel hp) := by
  exact ⟨foxNeuwirthTopCellModel hp⟩

end NRR
