/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.FiniteModel
import LeanPool.Erdos97ConvexOctagon.Obstructions
import LeanPool.Erdos97ConvexOctagon.ResidualObstructions

/-! # Erdős 97 convex-octagon formalization: Certificates -/

namespace Erdos97Octagon

namespace RawIncidence

/-- A finite witness emitted by the obstruction classifier. -/
inductive Certificate where
  | k4 (root : Vertex) (component : List Vertex) (a b c d : Vertex)
  | hubPentagon (root : Vertex) (component : List Vertex) (o a b c d e : Vertex)
  | sharedThree (a b q1 q2 q3 : Vertex)
  | cycleStrip (root : Vertex) (component : List Vertex) (o x1 x2 x3 x4 x5 x6 : Vertex)
  | residual (payload : UInt64)
  deriving DecidableEq

/-- The two obstruction shapes that remain valid when incidences are added. -/
inductive PrefixCertificate where
  | k4 (root : Vertex) (component : List Vertex) (a b c d : Vertex)
  | sharedThree (a b q1 q2 q3 : Vertex)
  deriving DecidableEq

/-- Regard a monotone prefix witness as a general obstruction certificate. -/
def PrefixCertificate.toCertificate : PrefixCertificate → Certificate
  | .k4 root component a b c d => .k4 root component a b c d
  | .sharedThree a b q1 q2 q3 => .sharedThree a b q1 q2 q3

/-- Validate the tail of an ordered mutual-edge spanning tree. -/
def extendsTreeB
    (R : RawIncidence) (reached : Finset Vertex) : List Vertex → Bool
  | [] => true
  | v :: todo =>
      decide (v ∉ reached) &&
        decide (∃ u ∈ reached, v ∈ R u ∧ u ∈ R v) &&
        extendsTreeB R (insert v reached) todo

/-- Check that the listed vertices form an ordered mutual-edge spanning tree. -/
def componentTreeB (R : RawIncidence) (root : Vertex) : List Vertex → Bool
  | [] => false
  | first :: rest => decide (first = root) && extendsTreeB R {root} rest

/-- A selected edge whose selecting endpoint occurs in a validated tree. -/
def TreeLabelledEdge (R : RawIncidence) (component : List Vertex) (a b : Vertex) : Prop :=
  (a ∈ component ∧ b ∈ R a) ∨ (b ∈ component ∧ a ∈ R b)

instance (R : RawIncidence) (component : List Vertex) (a b : Vertex) :
    Decidable (TreeLabelledEdge R component a b) := by
  unfold TreeLabelledEdge
  infer_instance

/-- The class number stored in a residual-isomorphism payload. -/
def payloadClass (payload : UInt64) : ℕ :=
  (payload &&& 15).toNat

/-- The forward permutation stored in a residual-isomorphism payload. -/
def payloadForwardCode (payload : UInt64) : UInt64 :=
  (payload >>> 4) &&& 0xffffff

/-- The inverse permutation stored in a residual-isomorphism payload. -/
def payloadInverseCode (payload : UInt64) : UInt64 :=
  (payload >>> 28) &&& 0xffffff

/-- Decode one three-bit entry of a packed permutation. -/
def decodeMap (code : UInt64) (v : Vertex) : Vertex :=
  Fin.ofNat 8 (((code >>> UInt64.ofNat (3 * v.val)) &&& 7).toNat)

/-- The mathematical proposition checked for each emitted finite witness. -/
def Certificate.Valid (R : RawIncidence) : Certificate → Prop
  | .k4 root component a b c d =>
      componentTreeB R root component = true ∧ [a, b, c, d].Nodup ∧
        TreeLabelledEdge R component a b ∧ TreeLabelledEdge R component a c ∧
        TreeLabelledEdge R component a d ∧ TreeLabelledEdge R component b c ∧
        TreeLabelledEdge R component b d ∧ TreeLabelledEdge R component c d
  | .hubPentagon root component o a b c d e =>
      componentTreeB R root component = true ∧ [o, a, b, c, d, e].Nodup ∧
        TreeLabelledEdge R component o a ∧ TreeLabelledEdge R component o b ∧
        TreeLabelledEdge R component o c ∧ TreeLabelledEdge R component o d ∧
        TreeLabelledEdge R component o e ∧ TreeLabelledEdge R component a b ∧
        TreeLabelledEdge R component b c ∧ TreeLabelledEdge R component c d ∧
        TreeLabelledEdge R component d e ∧ TreeLabelledEdge R component e a
  | .sharedThree a b q1 q2 q3 =>
      a ≠ b ∧ q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3 ∧
        q1 ∈ R a ∧ q2 ∈ R a ∧ q3 ∈ R a ∧
        q1 ∈ R b ∧ q2 ∈ R b ∧ q3 ∈ R b
  | .cycleStrip root component o x1 x2 x3 x4 x5 x6 =>
      componentTreeB R root component = true ∧ [o, x1, x2, x3, x4, x5, x6].Nodup ∧
        TreeLabelledEdge R component o x1 ∧ TreeLabelledEdge R component o x2 ∧
        TreeLabelledEdge R component o x6 ∧ TreeLabelledEdge R component x1 x2 ∧
        TreeLabelledEdge R component x1 x3 ∧ TreeLabelledEdge R component x2 x3 ∧
        TreeLabelledEdge R component x2 x4 ∧ TreeLabelledEdge R component x3 x4 ∧
        TreeLabelledEdge R component x3 x5 ∧ TreeLabelledEdge R component x4 x5 ∧
        TreeLabelledEdge R component x4 x6 ∧ TreeLabelledEdge R component x5 x6
  | .residual payload =>
      let classIndex := payloadClass payload
      let forward := decodeMap (payloadForwardCode payload)
      let inverse := decodeMap (payloadInverseCode payload)
      classIndex < 13 ∧
        (∀ v, inverse (forward v) = v) ∧
        (∀ v, forward (inverse v) = v) ∧
        ∀ v w, w ∈ R v ↔
          forward w ∈ (residualRepresentative (Fin.ofNat 13 classIndex)).targets (forward v)

instance (R : RawIncidence) (certificate : Certificate) :
    Decidable (certificate.Valid R) := by
  cases certificate <;> simp only [Certificate.Valid] <;> infer_instance

private def residualValidB (R : RawIncidence) (payload : UInt64) : Bool :=
  let classIndex := payloadClass payload
  let forward := decodeMap (payloadForwardCode payload)
  let inverse := decodeMap (payloadInverseCode payload)
  decide (classIndex < 13) &&
    (List.finRange 8).all (fun v => decide (inverse (forward v) = v)) &&
    (List.finRange 8).all (fun v => decide (forward (inverse v) = v)) &&
    (List.finRange 8).all (fun v =>
      (List.finRange 8).all (fun w => decide (w ∈ R v ↔
        forward w ∈
          (residualRepresentative (Fin.ofNat 13 classIndex)).targets (forward v))))

/-- Kernel-check the mathematical content of an emitted witness. -/
def Certificate.validB (R : RawIncidence) : Certificate → Bool
  | .residual payload => residualValidB R payload
  | certificate => decide (certificate.Valid R)

/-- The Boolean validator implies the mathematical certificate predicate. -/
theorem Certificate.valid_of_validB
    {R : RawIncidence} {certificate : Certificate}
    (hvalid : certificate.validB R = true) : certificate.Valid R := by
  cases certificate with
  | residual payload =>
      simp only [Certificate.validB, residualValidB, Bool.and_eq_true] at hvalid
      rcases hvalid with ⟨⟨⟨hclass, hleft⟩, hright⟩, hedges⟩
      refine ⟨of_decide_eq_true hclass, ?_, ?_, ?_⟩
      · intro v
        exact of_decide_eq_true ((List.all_eq_true.mp hleft) v (List.mem_finRange v))
      · intro v
        exact of_decide_eq_true ((List.all_eq_true.mp hright) v (List.mem_finRange v))
      · intro v w
        have hv := (List.all_eq_true.mp hedges) v (List.mem_finRange v)
        exact of_decide_eq_true ((List.all_eq_true.mp hv) w (List.mem_finRange w))
  | k4 root component a b c d => exact of_decide_eq_true hvalid
  | hubPentagon root component o a b c d e => exact of_decide_eq_true hvalid
  | sharedThree a b q1 q2 q3 => exact of_decide_eq_true hvalid
  | cycleStrip root component o x1 x2 x3 x4 x5 x6 => exact of_decide_eq_true hvalid

/-- One incidence table extends another when it contains every selected edge. -/
def Extends (R S : RawIncidence) : Prop :=
  ∀ centre target, target ∈ R centre → target ∈ S centre

private theorem extendsTreeB_mono {R S : RawIncidence} (hRS : Extends R S) :
    ∀ reached todo, extendsTreeB R reached todo = true →
      extendsTreeB S reached todo = true := by
  intro reached todo
  induction todo generalizing reached with
  | nil => simp [extendsTreeB]
  | cons v todo ih =>
      intro htree
      simp only [extendsTreeB, Bool.and_eq_true, decide_eq_true_eq] at htree ⊢
      rcases htree with ⟨⟨hv, u, hu, hvu, huv⟩, hrest⟩
      exact ⟨⟨hv, u, hu, hRS u v hvu, hRS v u huv⟩,
        ih (insert v reached) hrest⟩

private theorem componentTreeB_mono {R S : RawIncidence} (hRS : Extends R S)
    {root component} (htree : componentTreeB R root component = true) :
    componentTreeB S root component = true := by
  cases component with
  | nil => simp [componentTreeB] at htree
  | cons first rest =>
      simp only [componentTreeB, Bool.and_eq_true] at htree ⊢
      exact ⟨htree.1, extendsTreeB_mono hRS {root} rest htree.2⟩

private theorem treeLabelledEdge_mono {R S : RawIncidence} (hRS : Extends R S)
    {component a b} (hedge : TreeLabelledEdge R component a b) :
    TreeLabelledEdge S component a b := by
  rcases hedge with ⟨ha, hab⟩ | ⟨hb, hba⟩
  · exact Or.inl ⟨ha, hRS a b hab⟩
  · exact Or.inr ⟨hb, hRS b a hba⟩

/-- A prefix certificate remains valid in every incidence extension. -/
theorem PrefixCertificate.valid_mono
    {R S : RawIncidence} {certificate : PrefixCertificate}
    (hRS : Extends R S) (hvalid : certificate.toCertificate.Valid R) :
    certificate.toCertificate.Valid S := by
  cases certificate with
  | k4 root component a b c d =>
      simp only [PrefixCertificate.toCertificate, Certificate.Valid] at hvalid ⊢
      rcases hvalid with ⟨htree, hnodup, hab, hac, had, hbc, hbd, hcd⟩
      exact ⟨componentTreeB_mono hRS htree, hnodup,
        treeLabelledEdge_mono hRS hab, treeLabelledEdge_mono hRS hac,
        treeLabelledEdge_mono hRS had, treeLabelledEdge_mono hRS hbc,
        treeLabelledEdge_mono hRS hbd, treeLabelledEdge_mono hRS hcd⟩
  | sharedThree a b q1 q2 q3 =>
      simp only [PrefixCertificate.toCertificate, Certificate.Valid] at hvalid ⊢
      rcases hvalid with ⟨hab, h12, h13, h23, ha1, ha2, ha3, hb1, hb2, hb3⟩
      exact ⟨hab, h12, h13, h23, hRS a q1 ha1, hRS a q2 ha2,
        hRS a q3 ha3, hRS b q1 hb1, hRS b q2 hb2, hRS b q3 hb3⟩

private theorem extendsTree_sameComponent
    (Q : OctagonIncidence) (root : Vertex) :
    ∀ (reached : Finset Vertex) (todo : List Vertex),
      (∀ v ∈ reached, Q.SameComponent root v) →
      extendsTreeB Q.targets reached todo = true →
      ∀ v ∈ todo, Q.SameComponent root v := by
  intro reached todo
  induction todo generalizing reached with
  | nil => simp
  | cons v todo ih =>
      intro hreach htree
      simp only [extendsTreeB, Bool.and_eq_true, decide_eq_true_eq] at htree
      obtain ⟨u, hu, huv⟩ := htree.1.2
      have hv : Q.SameComponent root v := (hreach u hu).tail huv
      have hreach' : ∀ w ∈ insert v reached, Q.SameComponent root w := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hv
        · exact hreach w hw
      have htodo := ih (insert v reached) hreach' htree.2
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hv
      · exact htodo w hw

/-- Every vertex in a validated ordered tree belongs to the root component. -/
theorem componentTree_sameComponent
    (Q : OctagonIncidence) {root : Vertex} {component : List Vertex}
    (htree : componentTreeB Q.targets root component = true)
    {v : Vertex} (hv : v ∈ component) :
    Q.SameComponent root v := by
  cases component with
  | nil => simp [componentTreeB] at htree
  | cons first rest =>
      simp only [componentTreeB, Bool.and_eq_true, decide_eq_true_eq] at htree
      have hfirst : first = root := htree.1
      subst first
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Relation.ReflTransGen.refl
      · apply extendsTree_sameComponent Q root {root} rest
          (fun w hw => by
            have : w = root := by simpa using hw
            subst w
            exact Relation.ReflTransGen.refl) htree.2 v hv

/-- Every tree-labelled checker edge is a genuine component-radius edge. -/
theorem treeLabelledEdge_sound
    (Q : OctagonIncidence) {root : Vertex} {component : List Vertex}
    (htree : componentTreeB Q.targets root component = true)
    {a b : Vertex} (h : TreeLabelledEdge Q.targets component a b) :
    Q.LabelledEdge root a b := by
  rcases h with ⟨ha, hab⟩ | ⟨hb, hba⟩
  · exact Or.inl ⟨componentTree_sameComponent Q htree ha, hab⟩
  · exact Or.inr ⟨componentTree_sameComponent Q htree hb, hba⟩

private theorem finOfNat_eq_of_lt {n a : ℕ} [NeZero n] (h : a < n) :
    Fin.ofNat n a = ⟨a, h⟩ := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt h]

private theorem residual_relabel_eq
    (Q : OctagonIncidence) (payload : UInt64)
    (hvalid : (Certificate.residual payload).Valid Q.targets) :
    ∃ classIndex : Fin 13, ∃ e : Vertex ≃ Vertex,
      Q.relabel e = residualRepresentative classIndex := by
  simp only [Certificate.Valid] at hvalid
  let classIndex : Fin 13 := ⟨payloadClass payload, hvalid.1⟩
  let forward := decodeMap (payloadForwardCode payload)
  let inverse := decodeMap (payloadInverseCode payload)
  let e : Vertex ≃ Vertex := Equiv.mk forward inverse
    (left_inv := hvalid.2.1) (right_inv := hvalid.2.2.1)
  have hright (x : Vertex) : forward (inverse x) = x := hvalid.2.2.1 x
  refine ⟨classIndex, e, ?_⟩
  apply OctagonIncidence.ext
  funext v
  ext w
  have hedge := hvalid.2.2.2 (e.symm v) (e.symm w)
  have hindex : Fin.ofNat 13 (payloadClass payload) = classIndex :=
    finOfNat_eq_of_lt hvalid.1
  change w ∈ (Q.targets (e.symm v)).map e.toEmbedding ↔
    w ∈ (residualRepresentative classIndex).targets v
  rw [Finset.mem_map]
  constructor
  · rintro ⟨x, hx, hxw⟩
    have hxeq : x = e.symm w := by
      apply e.injective
      simpa using hxw
    subst x
    have := hedge.mp hx
    change forward (inverse w) ∈
      (residualRepresentative (Fin.ofNat 13 (payloadClass payload))).targets
        (forward (inverse v)) at this
    rw [hright w, hright v, hindex] at this
    exact this
  · intro hw
    refine ⟨e.symm w, ?_, by simp⟩
    apply hedge.mpr
    change forward (inverse w) ∈
      (residualRepresentative (Fin.ofNat 13 (payloadClass payload))).targets
        (forward (inverse v))
    rw [hright w, hright v, hindex]
    exact hw

/-- Every validated finite witness contradicts a convex planar realisation. -/
theorem Certificate.not_convex_realises
    {Q : OctagonIncidence} (certificate : Certificate)
    (hvalid : certificate.Valid Q.targets)
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p) (hR : Realises p Q) :
    False := by
  cases certificate with
  | k4 root component a b c d =>
      simp only [Certificate.Valid] at hvalid
      rcases hvalid with ⟨htree, hnodup, hab, hac, hadge, hbc, hbd, hcd⟩
      have had : a ≠ d := by
        intro had
        subst d
        simp at hnodup
      exact no_labelled_k4 hC.injective hR had
        (treeLabelledEdge_sound Q htree hab)
        (treeLabelledEdge_sound Q htree hac)
        (treeLabelledEdge_sound Q htree hadge)
        (treeLabelledEdge_sound Q htree hbc)
        (treeLabelledEdge_sound Q htree hbd)
        (treeLabelledEdge_sound Q htree hcd)
  | hubPentagon root component o a b c d e =>
      simp only [Certificate.Valid] at hvalid
      rcases hvalid with
        ⟨htree, _hnodup, hoa, hob, hoc, hod, hoe, hab, hbc, hcd, hde, hea⟩
      exact no_labelled_hub_pentagon hC.injective hR
        (treeLabelledEdge_sound Q htree hoa)
        (treeLabelledEdge_sound Q htree hob)
        (treeLabelledEdge_sound Q htree hoc)
        (treeLabelledEdge_sound Q htree hod)
        (treeLabelledEdge_sound Q htree hoe)
        (treeLabelledEdge_sound Q htree hab)
        (treeLabelledEdge_sound Q htree hbc)
        (treeLabelledEdge_sound Q htree hcd)
        (treeLabelledEdge_sound Q htree hde)
        (treeLabelledEdge_sound Q htree hea)
  | sharedThree a b q1 q2 q3 =>
      simp only [Certificate.Valid] at hvalid
      exact no_three_shared_targets hC hR hvalid.1 hvalid.2.1
        hvalid.2.2.1 hvalid.2.2.2.1 hvalid.2.2.2.2.1
        hvalid.2.2.2.2.2.1 hvalid.2.2.2.2.2.2.1
        hvalid.2.2.2.2.2.2.2.1 hvalid.2.2.2.2.2.2.2.2.1
        hvalid.2.2.2.2.2.2.2.2.2
  | cycleStrip root component o x1 x2 x3 x4 x5 x6 =>
      simp only [Certificate.Valid] at hvalid
      rcases hvalid with
        ⟨htree, _hnodup, e01, e02, e06, e12, e13, e23, e24, e34, e35, e45, e46, e56⟩
      exact no_labelled_cycle_square_strip hC.injective hR
        (treeLabelledEdge_sound Q htree e01)
        (treeLabelledEdge_sound Q htree e02)
        (treeLabelledEdge_sound Q htree e06)
        (treeLabelledEdge_sound Q htree e12)
        (treeLabelledEdge_sound Q htree e13)
        (treeLabelledEdge_sound Q htree e23)
        (treeLabelledEdge_sound Q htree e24)
        (treeLabelledEdge_sound Q htree e34)
        (treeLabelledEdge_sound Q htree e35)
        (treeLabelledEdge_sound Q htree e45)
        (treeLabelledEdge_sound Q htree e46)
        (treeLabelledEdge_sound Q htree e56)
  | residual payload =>
      obtain ⟨classIndex, e, he⟩ := residual_relabel_eq Q payload hvalid
      have hC' := convexIndependent_relabel hC e
      have hR' := realises_relabel hR e
      rw [he] at hR'
      exact residualRepresentative_not_convex_realises classIndex hC' hR'

end RawIncidence

end Erdos97Octagon
