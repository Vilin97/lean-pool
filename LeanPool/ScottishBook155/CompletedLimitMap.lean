/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.NormedDirectLimit

/-!
# Coherent nonlinear maps on completed normed direct limits

A coherent family of nonexpansive maps between two isometric directed
systems induces a nonexpansive map between their completed normed direct
limits. Linearity of the stage maps is neither assumed nor used.
-/

namespace ScottishBook155

open scoped NNReal

universe u

namespace CompletedLimitMap

variable {ι : Type u} [LinearOrder ι] [Nonempty ι]
variable (M N : ι → Type u)
variable [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]
variable [∀ i, NormedAddCommGroup (N i)] [∀ i, NormedSpace ℝ (N i)]
variable (eM : ∀ i j : ι, i ≤ j → M i →ₗᵢ[ℝ] M j)
variable (eN : ∀ i j : ι, i ≤ j → N i →ₗᵢ[ℝ] N j)
variable [DirectedSystem M (eM · · ·)] [DirectedSystem N (eN · · ·)]

noncomputable local instance : DecidableEq ι := Classical.decEq ι

local instance sourceLinearDirectedSystem :
    DirectedSystem M (NormedDirectLimit.linearMap M eM · · ·) where
  map_self {i} x := DirectedSystem.map_self (f := (eM · · ·)) x
  map_map {k j i} hij hjk x :=
    DirectedSystem.map_map (f := (eM · · ·)) hij hjk x

local instance targetLinearDirectedSystem :
    DirectedSystem N (NormedDirectLimit.linearMap N eN · · ·) where
  map_self {i} x := DirectedSystem.map_self (f := (eN · · ·)) x
  map_map {k j i} hij hjk x :=
    DirectedSystem.map_map (f := (eN · · ·)) hij hjk x

abbrev Source := NormedDirectLimit.Carrier M eM
abbrev Target := NormedDirectLimit.Carrier N eN
abbrev CompletedSource := NormedDirectLimit.CompletedCarrier M eM
abbrev CompletedTarget := NormedDirectLimit.CompletedCarrier N eN

variable (V : ∀ i, M i → N i)

/-- Equal source representatives have equal images in the target direct
limit. -/
theorem target_of_eq_of_source_of_eq {i j : ι} {x : M i} {y : M j}
    (hV : ∀ i j (hij : i ≤ j) x,
      V j (eM i j hij x) = eN i j hij (V i x))
    (h : NormedDirectLimit.of M eM i x = NormedDirectLimit.of M eM j y) :
    NormedDirectLimit.of N eN i (V i x) =
      NormedDirectLimit.of N eN j (V j y) := by
  let k := max i j
  have hik : i ≤ k := le_max_left _ _
  have hjk : j ≤ k := le_max_right _ _
  change Module.DirectLimit.of ℝ ι M (NormedDirectLimit.linearMap M eM) i x =
    Module.DirectLimit.of ℝ ι M (NormedDirectLimit.linearMap M eM) j y at h
  have hk : Module.DirectLimit.of ℝ ι M (NormedDirectLimit.linearMap M eM) k
        (eM i k hik x) =
      Module.DirectLimit.of ℝ ι M (NormedDirectLimit.linearMap M eM) k
        (eM j k hjk y) := by
    change NormedDirectLimit.of M eM k (eM i k hik x) =
      NormedDirectLimit.of M eM k (eM j k hjk y)
    rw [NormedDirectLimit.of_f, NormedDirectLimit.of_f]
    exact h
  obtain ⟨l, hkl, heq⟩ := Module.DirectLimit.exists_eq_of_of_eq hk
  have himage : eN k l hkl (eN i k hik (V i x)) =
      eN k l hkl (eN j k hjk (V j y)) := by
    rw [← hV i k hik, ← hV j k hjk]
    rw [← hV k l hkl, ← hV k l hkl]
    change eM k l hkl (eM i k hik x) =
      eM k l hkl (eM j k hjk y) at heq
    exact congrArg (V l) heq
  change Module.DirectLimit.of ℝ ι N (NormedDirectLimit.linearMap N eN) i (V i x) =
    Module.DirectLimit.of ℝ ι N (NormedDirectLimit.linearMap N eN) j (V j y)
  calc
    Module.DirectLimit.of ℝ ι N (NormedDirectLimit.linearMap N eN) i (V i x) =
        Module.DirectLimit.of ℝ ι N (NormedDirectLimit.linearMap N eN) l
          (eN k l hkl (eN i k hik (V i x))) := by
            change NormedDirectLimit.of N eN i (V i x) =
              NormedDirectLimit.of N eN l (eN k l hkl (eN i k hik (V i x)))
            rw [NormedDirectLimit.of_f, NormedDirectLimit.of_f]
    _ = Module.DirectLimit.of ℝ ι N (NormedDirectLimit.linearMap N eN) l
        (eN k l hkl (eN j k hjk (V j y))) := congrArg _ himage
    _ = Module.DirectLimit.of ℝ ι N (NormedDirectLimit.linearMap N eN) j
        (V j y) := by
          change NormedDirectLimit.of N eN l
              (eN k l hkl (eN j k hjk (V j y))) =
            NormedDirectLimit.of N eN j (V j y)
          rw [NormedDirectLimit.of_f, NormedDirectLimit.of_f]

/-- The coherent map on the algebraic source direct limit. -/
noncomputable def algebraicMap (z : Source M eM) : Target N eN :=
  NormedDirectLimit.of N eN (NormedDirectLimit.reprIndex M eM z)
    (V _ (NormedDirectLimit.reprValue M eM z))

theorem algebraicMap_of
    (hV : ∀ i j (hij : i ≤ j) x,
      V j (eM i j hij x) = eN i j hij (V i x))
    (i : ι) (x : M i) :
    algebraicMap M N eM eN V
        (Module.DirectLimit.of ℝ ι M
          (NormedDirectLimit.linearMap M eM) i x) =
      Module.DirectLimit.of ℝ ι N
        (NormedDirectLimit.linearMap N eN) i (V i x) := by
  apply target_of_eq_of_source_of_eq M N eM eN V hV
  exact NormedDirectLimit.repr_spec M eM _

theorem algebraicMap_dist_le
    (hV : ∀ i j (hij : i ≤ j) x,
      V j (eM i j hij x) = eN i j hij (V i x))
    (hLip : ∀ i x y, dist (V i x) (V i y) ≤ dist x y)
    (z w : Source M eM) :
    dist (algebraicMap M N eM eN V z)
        (algebraicMap M N eM eN V w) ≤ dist z w := by
  obtain ⟨i, x, y, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
  rw [algebraicMap_of M N eM eN V hV,
    algebraicMap_of M N eM eN V hV]
  change dist (NormedDirectLimit.of N eN i (V i x))
      (NormedDirectLimit.of N eN i (V i y)) ≤
    dist (NormedDirectLimit.of M eM i x) (NormedDirectLimit.of M eM i y)
  rw [(NormedDirectLimit.of N eN i).isometry.dist_eq,
    (NormedDirectLimit.of M eM i).isometry.dist_eq]
  exact hLip i x y

theorem algebraicMap_lipschitz
    (hV : ∀ i j (hij : i ≤ j) x,
      V j (eM i j hij x) = eN i j hij (V i x))
    (hLip : ∀ i x y, dist (V i x) (V i y) ≤ dist x y) :
    LipschitzWith 1 (algebraicMap M N eM eN V) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa using algebraicMap_dist_le M N eM eN V hV hLip z w

/-- The coherent nonexpansive map extended to the completed normed direct
limits. -/
noncomputable def completedMap
    (hV : ∀ i j (hij : i ≤ j) x,
      V j (eM i j hij x) = eN i j hij (V i x))
    (hLip : ∀ i x y, dist (V i x) (V i y) ≤ dist x y) :
    CompletedSource M eM → CompletedTarget N eN :=
  UniformSpace.Completion.extension
    (((↑) : Target N eN → CompletedTarget N eN) ∘
      algebraicMap M N eM eN V)

theorem completedMap_lipschitz
    (hV : ∀ i j (hij : i ≤ j) x,
      V j (eM i j hij x) = eN i j hij (V i x))
    (hLip : ∀ i x y, dist (V i x) (V i y) ≤ dist x y) :
    LipschitzWith 1 (completedMap M N eM eN V hV hLip) := by
  simpa only [completedMap, one_mul] using
    (UniformSpace.Completion.coe_isometry.lipschitz.comp
      (algebraicMap_lipschitz M N eM eN V hV hLip)).completion_extension

theorem completedMap_completedOf
    (hV : ∀ i j (hij : i ≤ j) x,
      V j (eM i j hij x) = eN i j hij (V i x))
    (hLip : ∀ i x y, dist (V i x) (V i y) ≤ dist x y)
    (i : ι) (x : M i) :
    completedMap M N eM eN V hV hLip
        (NormedDirectLimit.completedOf M eM i x) =
      NormedDirectLimit.completedOf N eN i (V i x) := by
  change UniformSpace.Completion.extension
      (((↑) : Target N eN → CompletedTarget N eN) ∘
        algebraicMap M N eM eN V)
      (↑(NormedDirectLimit.of M eM i x)) =
    (↑(NormedDirectLimit.of N eN i (V i x)))
  rw [UniformSpace.Completion.extension_coe
    (UniformSpace.Completion.coe_isometry.lipschitz.comp
      (algebraicMap_lipschitz M N eM eN V hV hLip)).uniformContinuous]
  exact congrArg ((↑) : Target N eN → CompletedTarget N eN)
    (algebraicMap_of M N eM eN V hV i x)

end CompletedLimitMap

end ScottishBook155
