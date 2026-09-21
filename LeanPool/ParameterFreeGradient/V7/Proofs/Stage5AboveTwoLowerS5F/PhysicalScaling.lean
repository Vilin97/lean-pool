/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.CompletedTrace

namespace V7.Stage5AboveTwoLowerS5F

noncomputable def physicalForward (x0 : Point d) (R rT : ℝ) (z : Point d) : Point d :=
  x0 + (R / rT) • z

noncomputable def physicalBackward (x0 : Point d) (R rT : ℝ) (x : Point d) : Point d :=
  (rT / R) • (x - x0)

lemma physicalForward_backward (x0 : Point d) {R rT : ℝ}
    (hR : 0 < R) (hrT : 0 < rT) (x : Point d) :
    physicalForward x0 R rT (physicalBackward x0 R rT x) = x := by
  unfold physicalForward physicalBackward
  have hscale : (R / rT) * (rT / R) = 1 := by field_simp
  rw [smul_smul, hscale, one_smul]
  module

lemma physicalBackward_forward (x0 : Point d) {R rT : ℝ}
    (hR : 0 < R) (hrT : 0 < rT) (z : Point d) :
    physicalBackward x0 R rT (physicalForward x0 R rT z) = z := by
  unfold physicalForward physicalBackward
  have hscale : (rT / R) * (R / rT) = 1 := by field_simp
  rw [show x0 + (R / rT) • z - x0 = (R / rT) • z by module,
    smul_smul, hscale, one_smul]

noncomputable def physicalOracle (x0 : Point d) (L R rT : ℝ)
    (bar : PairOracle d) : PairOracle d :=
  { value := fun x => (L * R ^ (2 : ℕ) / rT ^ (2 : ℕ)) *
      bar.value (physicalBackward x0 R rT x)
    gradient := fun x => (L * R / rT) •
      bar.gradient (physicalBackward x0 R rT x) }

noncomputable def physicalObservation (x0 : Point d) (L R rT : ℝ)
    (obs : Observation d) : Observation d :=
  { point := physicalForward x0 R rT obs.point
    value := (L * R ^ (2 : ℕ) / rT ^ (2 : ℕ)) * obs.value
    gradient := (L * R / rT) • obs.gradient }

lemma physicalObservation_observe (x0 : Point d) {L R rT : ℝ}
    (hR : 0 < R) (hrT : 0 < rT) (bar : PairOracle d) (z : Point d) :
    physicalObservation x0 L R rT (bar.observe z) =
      (physicalOracle x0 L R rT bar).observe (physicalForward x0 R rT z) := by
  rw [O3.Observation.mk.injEq]
  simp [physicalObservation, physicalOracle, O3.PairOracle.observe,
    physicalBackward_forward x0 hR hrT]

noncomputable def normalizedAdversaryAlgorithm (x0 : Point d) (L R rT : ℝ)
    (algorithm : DeterministicExactPairAlgorithm d) :
    DeterministicExactPairAlgorithm d :=
  { nextQuery := fun _ trace =>
      physicalBackward x0 R rT
        (algorithm.nextQuery x0 (trace.map (physicalObservation x0 L R rT)))
    output := fun _ trace =>
      physicalBackward x0 R rT
        (algorithm.output x0 (trace.map (physicalObservation x0 L R rT))) }

noncomputable def physicalTrace (x0 : Point d) (L R rT : ℝ)
    (trace : List (Observation d)) : List (Observation d) :=
  trace.map (physicalObservation x0 L R rT)

lemma physicalTrace_take (x0 : Point d) (L R rT : ℝ)
    (trace : List (Observation d)) (t : ℕ) :
    (physicalTrace x0 L R rT trace).take t =
      physicalTrace x0 L R rT (trace.take t) := by
  induction trace generalizing t with
  | nil => simp [physicalTrace]
  | cons a tail ih =>
      cases t with
      | zero => simp [physicalTrace]
      | succ t => simp [physicalTrace, ih]

lemma physicalTrace_generated (x0 : Point d) {L R rT : ℝ}
    (hR : 0 < R) (hrT : 0 < rT)
    (algorithm : DeterministicExactPairAlgorithm d) (unitTrace : List (Observation d))
    (hgenerated : GeneratedBy
      (normalizedAdversaryAlgorithm x0 L R rT algorithm) 0 unitTrace) :
    GeneratedBy algorithm x0 (physicalTrace x0 L R rT unitTrace) := by
  intro t ht
  have htUnit : t < unitTrace.length := by
    simpa [physicalTrace] using ht
  have hu := hgenerated t htUnit
  have hget : (physicalTrace x0 L R rT unitTrace).get ⟨t, ht⟩ =
      physicalObservation x0 L R rT (unitTrace.get ⟨t, htUnit⟩) := by
    simp [physicalTrace]
  rw [hget]
  change physicalForward x0 R rT (unitTrace.get ⟨t, htUnit⟩).point = _
  rw [hu]
  split_ifs with ht0
  · subst t
    simp [physicalForward]
  · change physicalForward x0 R rT
        (physicalBackward x0 R rT
          (algorithm.nextQuery x0
            ((unitTrace.take t).map (physicalObservation x0 L R rT)))) = _
    rw [physicalForward_backward x0 hR hrT]
    congr 2
    rw [physicalTrace_take]
    rfl

lemma physicalTrace_exact (x0 : Point d) {L R rT : ℝ}
    (hR : 0 < R) (hrT : 0 < rT) (bar : PairOracle d)
    (trace : List (Observation d)) (hexact : TraceExact bar trace) :
    TraceExact (physicalOracle x0 L R rT bar)
      (physicalTrace x0 L R rT trace) := by
  intro obs hobs
  simp only [physicalTrace, List.mem_map] at hobs
  rcases hobs with ⟨barObs, hbarObs, rfl⟩
  rw [hexact barObs hbarObs]
  exact physicalObservation_observe x0 hR hrT bar barObs.point

lemma physicalTrace_head_point (x0 : Point d) {L R rT : ℝ}
    (trace : List (Observation d))
    (hhead : trace.head?.map O3.Observation.point = some (0 : Point d)) :
    (physicalTrace x0 L R rT trace).head?.map O3.Observation.point = some x0 := by
  unfold physicalTrace
  rw [List.head?_map]
  rcases h : trace.head? with _ | obs
  · simp [h] at hhead
  · have hpoint : obs.point = 0 := by simpa [h] using hhead
    simp [h, physicalObservation, hpoint, physicalForward]

end V7.Stage5AboveTwoLowerS5F
