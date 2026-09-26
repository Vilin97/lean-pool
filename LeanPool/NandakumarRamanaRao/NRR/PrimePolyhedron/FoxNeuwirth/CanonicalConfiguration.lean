/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.BarredPermutation
public import LeanPool.NandakumarRamanaRao.NRR.ConfigurationSpace

/-!
# Canonical configurations of barred permutations

Every barred permutation has a concrete labelled planar configuration: the first coordinate is the
block number and the second coordinate is the permutation rank.  This realizes every
Fox--Neuwirth symbol by an actual collision-free configuration and is equivariant for relabelling.
-/

@[expose] public section

namespace NRR

variable {p : ℕ}

namespace BarredPermutation

/-- Discrete topology on the finite set of barred permutations. -/
instance : TopologicalSpace (BarredPermutation p) := ⊥

instance : DiscreteTopology (BarredPermutation p) := ⟨rfl⟩

/-- Canonical point assigned to a label in a barred-permutation stratum. -/
noncomputable def canonicalPoint (c : BarredPermutation p) (i : Fin p) : E2 :=
  !₂[(c.blockIndex i : ℝ), ((c.rank i).1 : ℝ)]

@[simp] theorem canonicalPoint_x
    (c : BarredPermutation p) (i : Fin p) :
    c.canonicalPoint i 0 = (c.blockIndex i : ℝ) := by
  simp [canonicalPoint]

@[simp] theorem canonicalPoint_y
    (c : BarredPermutation p) (i : Fin p) :
    c.canonicalPoint i 1 = ((c.rank i).1 : ℝ) := by
  simp [canonicalPoint]

theorem canonicalPoint_injective (c : BarredPermutation p) :
    Function.Injective c.canonicalPoint := by
  intro i j hij
  apply c.rank.injective
  apply Fin.ext
  have hy : ((c.rank i).1 : ℝ) = ((c.rank j).1 : ℝ) := by
    simpa [canonicalPoint] using congrArg (fun x : E2 => x 1) hij
  exact_mod_cast hy

/-- Concrete configuration representing the stratum symbol. -/
noncomputable def canonicalConfig (c : BarredPermutation p) : Config p :=
  ⟨c.canonicalPoint, c.canonicalPoint_injective⟩

@[simp] theorem canonicalConfig_pts
    (c : BarredPermutation p) (i : Fin p) :
    c.canonicalConfig.pts i = c.canonicalPoint i :=
  rfl

theorem canonicalConfig_relabel
    (σ : Equiv.Perm (Fin p)) (c : BarredPermutation p) :
    (c.relabel σ).canonicalConfig =
      Config.relabel σ c.canonicalConfig := by
  apply Subtype.ext
  funext i
  apply WithLp.ofLp_injective 2
  funext j
  fin_cases j
  · rfl
  · rfl

/-- The finite canonical-configuration map is continuous for the discrete domain topology. -/
noncomputable def canonicalConfigMap :
    C(BarredPermutation p, Config p) where
  toFun := canonicalConfig
  continuous_toFun := continuous_of_discreteTopology

end BarredPermutation

end NRR
