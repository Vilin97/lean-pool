/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.FiniteModel
import Mathlib.Tactic.FinCases

/-!
# First-row symmetry reduction

The normalized zeroth row splits the remaining labels into `{2,3,4}` and
`{5,6,7}`.  Permuting within those blocks reduces the 35 possible first rows
to seven canonical orbits.  The small table below records an explicit forward
and inverse permutation for every row.
-/

namespace Erdos97Octagon.RawIncidence

/-- The seven canonical first-row masks, in certificate order. -/
def canonicalRowMask : Fin 7 → UInt64 :=
  ![29, 45, 101, 225, 60, 108, 228]

/-- All first-row masks in the lexicographic search order. -/
def rowOneMask : Fin 35 → UInt64 := ![
  29, 45, 77, 141, 53, 85, 149, 101, 165, 197, 57, 89, 153, 105, 169, 201,
  113, 177, 209, 225, 60, 92, 156, 108, 172, 204, 116, 180, 212, 228, 120,
  184, 216, 232, 240
]

/-- All second-row masks in the lexicographic search order. -/
def rowTwoMask : Fin 35 → UInt64 := ![
  27, 43, 75, 139, 51, 83, 147, 99, 163, 195, 57, 89, 153, 105, 169, 201,
  113, 177, 209, 225, 58, 90, 154, 106, 170, 202, 114, 178, 210, 226, 120,
  184, 216, 232, 240
]

private theorem rowOneOptions_eq :
    (rowOptions 1).reverse = List.ofFn (fun index => packedRow (rowOneMask index)) := by
  decide

private theorem rowTwoOptions_eq :
    (rowOptions 2).reverse = List.ofFn (fun index => packedRow (rowTwoMask index)) := by
  decide

/-- Every legal first row has one of the 35 explicit masks. -/
theorem exists_rowOneIndex (Q : OctagonIncidence) :
    ∃ index : Fin 35, Q.targets 1 = packedRow (rowOneMask index) := by
  have hmem : Q.targets 1 ∈ (rowOptions 1).reverse := by
    simpa using target_row_mem_rowOptions Q 1
  rw [rowOneOptions_eq, List.mem_ofFn] at hmem
  obtain ⟨index, hindex⟩ := hmem
  exact ⟨index, hindex.symm⟩

/-- Every legal second row has one of the 35 explicit masks. -/
theorem exists_rowTwoIndex (Q : OctagonIncidence) :
    ∃ index : Fin 35, Q.targets 2 = packedRow (rowTwoMask index) := by
  have hmem : Q.targets 2 ∈ (rowOptions 2).reverse := by
    simpa using target_row_mem_rowOptions Q 2
  rw [rowTwoOptions_eq, List.mem_ofFn] at hmem
  obtain ⟨index, hindex⟩ := hmem
  exact ⟨index, hindex.symm⟩

/-- One explicit permutation taking a first row to a canonical orbit. -/
structure RowSymmetryCertificate where
  /-- Index of the canonical first-row orbit. -/
  orbit : Fin 7
  /-- Packed code for the forward vertex permutation. -/
  forwardCode : UInt64
  /-- Packed code for the inverse vertex permutation. -/
  inverseCode : UInt64

/-- Mathematical validity of a row-symmetry certificate. -/
def RowSymmetryCertificate.Valid
    (certificate : RowSymmetryCertificate) (sourceMask : UInt64) : Prop :=
  let forward := decodeMap certificate.forwardCode
  let inverse := decodeMap certificate.inverseCode
  (∀ vertex, inverse (forward vertex) = vertex) ∧
    (∀ vertex, forward (inverse vertex) = vertex) ∧
    forward 0 = 0 ∧ forward 1 = 1 ∧
    (∀ vertex, vertex ∈ standardTargets ↔ forward vertex ∈ standardTargets) ∧
    ∀ vertex, vertex ∈ packedRow sourceMask ↔
      forward vertex ∈ packedRow (canonicalRowMask certificate.orbit)

instance instDecidableRowSymmetryCertificateValid
    (certificate : RowSymmetryCertificate) (sourceMask : UInt64) :
    Decidable (certificate.Valid sourceMask) := by
  unfold RowSymmetryCertificate.Valid
  infer_instance

/-- The 35 explicit orbit certificates, aligned with `rowOneMask`. -/
def rowSymmetryCertificate : Fin 35 → RowSymmetryCertificate := ![
  { orbit := 0, forwardCode := 16434824, inverseCode := 16434824 },
  { orbit := 1, forwardCode := 16434824, inverseCode := 16434824 },
  { orbit := 1, forwardCode := 16205448, inverseCode := 16205448 },
  { orbit := 1, forwardCode := 12535432, inverseCode := 14141064 },
  { orbit := 1, forwardCode := 16431240, inverseCode := 16431240 },
  { orbit := 1, forwardCode := 16201864, inverseCode := 16201864 },
  { orbit := 1, forwardCode := 12531848, inverseCode := 14137480 },
  { orbit := 2, forwardCode := 16434824, inverseCode := 16434824 },
  { orbit := 2, forwardCode := 14599816, inverseCode := 14599816 },
  { orbit := 2, forwardCode := 14141064, inverseCode := 12535432 },
  { orbit := 1, forwardCode := 16430344, inverseCode := 16427208 },
  { orbit := 1, forwardCode := 16200968, inverseCode := 16197832 },
  { orbit := 1, forwardCode := 12530952, inverseCode := 14133448 },
  { orbit := 2, forwardCode := 16434376, inverseCode := 16434376 },
  { orbit := 2, forwardCode := 14599368, inverseCode := 14599368 },
  { orbit := 2, forwardCode := 14140616, inverseCode := 12534984 },
  { orbit := 2, forwardCode := 16427208, inverseCode := 16430344 },
  { orbit := 2, forwardCode := 14592200, inverseCode := 14595336 },
  { orbit := 2, forwardCode := 14133448, inverseCode := 12530952 },
  { orbit := 3, forwardCode := 16434824, inverseCode := 16434824 },
  { orbit := 4, forwardCode := 16434824, inverseCode := 16434824 },
  { orbit := 4, forwardCode := 16205448, inverseCode := 16205448 },
  { orbit := 4, forwardCode := 12535432, inverseCode := 14141064 },
  { orbit := 5, forwardCode := 16434824, inverseCode := 16434824 },
  { orbit := 5, forwardCode := 14599816, inverseCode := 14599816 },
  { orbit := 5, forwardCode := 14141064, inverseCode := 12535432 },
  { orbit := 5, forwardCode := 16431240, inverseCode := 16431240 },
  { orbit := 5, forwardCode := 14596232, inverseCode := 14596232 },
  { orbit := 5, forwardCode := 14137480, inverseCode := 12531848 },
  { orbit := 6, forwardCode := 16434824, inverseCode := 16434824 },
  { orbit := 5, forwardCode := 16430344, inverseCode := 16427208 },
  { orbit := 5, forwardCode := 14595336, inverseCode := 14592200 },
  { orbit := 5, forwardCode := 14136584, inverseCode := 12527816 },
  { orbit := 6, forwardCode := 16434376, inverseCode := 16434376 },
  { orbit := 6, forwardCode := 16427208, inverseCode := 16430344 }
]

/-- Kernel audit of all 35 explicit symmetry certificates. -/
theorem rowSymmetryCertificate_valid (index : Fin 35) :
    (rowSymmetryCertificate index).Valid (rowOneMask index) := by
  fin_cases index <;> decide

/-- Decode a valid row-symmetry certificate as a vertex equivalence. -/
def RowSymmetryCertificate.toEquiv
    (certificate : RowSymmetryCertificate) {sourceMask : UInt64}
    (hvalid : certificate.Valid sourceMask) : Vertex ≃ Vertex where
  toFun := decodeMap certificate.forwardCode
  invFun := decodeMap certificate.inverseCode
  left_inv := hvalid.1
  right_inv := hvalid.2.1

private theorem map_eq_of_membership
    (equivalence : Vertex ≃ Vertex) (source target : Finset Vertex)
    (hmembership : ∀ vertex, vertex ∈ source ↔ equivalence vertex ∈ target) :
    source.map equivalence.toEmbedding = target := by
  ext vertex
  rw [Finset.mem_map]
  constructor
  · rintro ⟨preimage, hsource, rfl⟩
    exact (hmembership preimage).mp hsource
  · intro htarget
    refine ⟨equivalence.symm vertex, ?_, by simp⟩
    exact (hmembership (equivalence.symm vertex)).mpr (by simpa using htarget)

/-- Relabel a normalized system so that row one is one of seven canonical rows. -/
theorem canonicalize_rowOne
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q) (hN : Q.Normalized)
    (index : Fin 35) (hrow : Q.targets 1 = packedRow (rowOneMask index)) :
    ∃ orbit : Fin 7, ∃ p' : Vertex → Plane, ∃ Q' : OctagonIncidence,
      ConvexIndependent ℝ p' ∧ Realises p' Q' ∧ Q'.Normalized ∧
        Q'.PairSparse ∧ Q'.Balanced ∧
        Q'.targets 1 = packedRow (canonicalRowMask orbit) := by
  let certificate := rowSymmetryCertificate index
  have hvalid : certificate.Valid (rowOneMask index) :=
    rowSymmetryCertificate_valid index
  let equivalence := certificate.toEquiv hvalid
  have hzero : equivalence 0 = 0 := by
    simpa [equivalence, RowSymmetryCertificate.toEquiv] using hvalid.2.2.1
  have hone : equivalence 1 = 1 := by
    simpa [equivalence, RowSymmetryCertificate.toEquiv] using hvalid.2.2.2.1
  have hzeroSymm : equivalence.symm 0 = 0 := by
    apply equivalence.injective
    simp [hzero]
  have honeSymm : equivalence.symm 1 = 1 := by
    apply equivalence.injective
    simp [hone]
  have hmapStandard :
      standardTargets.map equivalence.toEmbedding = standardTargets :=
    map_eq_of_membership equivalence standardTargets standardTargets (by
      intro vertex
      simpa [equivalence, RowSymmetryCertificate.toEquiv] using
        hvalid.2.2.2.2.1 vertex)
  have hmapRow :
      (packedRow (rowOneMask index)).map equivalence.toEmbedding =
        packedRow (canonicalRowMask certificate.orbit) :=
    map_eq_of_membership equivalence (packedRow (rowOneMask index))
      (packedRow (canonicalRowMask certificate.orbit)) (by
        intro vertex
        simpa [equivalence, RowSymmetryCertificate.toEquiv] using
          hvalid.2.2.2.2.2 vertex)
  let p' := relabelPoints p equivalence
  let Q' := Q.relabel equivalence
  have hC' : ConvexIndependent ℝ p' := convexIndependent_relabel hC equivalence
  have hR' : Realises p' Q' := realises_relabel hR equivalence
  have hN' : Q'.Normalized := by
    change (Q.targets (equivalence.symm 0)).map equivalence.toEmbedding = standardTargets
    rw [hzeroSymm, hN, hmapStandard]
  have hrow' : Q'.targets 1 = packedRow (canonicalRowMask certificate.orbit) := by
    change (Q.targets (equivalence.symm 1)).map equivalence.toEmbedding = _
    rw [honeSymm, hrow, hmapRow]
  have hSparse' : Q'.PairSparse := pairSparse_of_realises hC' Q' hR'
  refine ⟨certificate.orbit, p', Q', hC', hR', hN', hSparse',
    Q'.balanced_of_pairSparse hSparse', hrow'⟩

end Erdos97Octagon.RawIncidence
