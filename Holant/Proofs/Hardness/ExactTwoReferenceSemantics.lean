import Holant.Proofs.Hardness.ExactTwoReferenceEvaluation
import Holant.Proofs.Hardness.PairedPinsSemantics
import Holant.Proofs.Hardness.SelfDualPinObstruction

/-! Full actual-network semantics of shared-reference
pinning. A nonempty cycle gives the all01 plus all10 partitions. For self-dual
original q these are equal by global bit complement, yielding exactly factor2.
The empty cycle is identity, including the empty closed graph's value1. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceSemantics
open Holant Holant.Complexity
open ExactTwoReferenceRaw ExactTwoReferenceValidation
open scoped BigOperators
namespace V
export ExactTwoReferenceEvaluation (sourceTable targetTable read4 branch_sum zero_value)
end V
namespace Choice
export UniversalPairReduction.Surgery.Choice (table weight evaluate rowValue denote_eq_evaluate)
end Choice
namespace PP
export PairedPinsSemantics (targetSignatures pin)
end PP
namespace SD
export SelfDualPinObstruction (flip flipEquiv SelfDual assignment_flip nativeX_self_dual)
end SD
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

def sourceSignatures (q : Signature K 4) (phase : Bool) :=
  PP.targetSignatures (s:=1) (a:=fun _=>4) (fun _ : Fin 1=>q) (PP.pin phase) (PP.pin (!phase))
def targetSignatures (q : Signature K 4) (i : Fin 2) : Signature K (targetArity i.val) :=
  if i.val<1 then q else ExactTwoSignatures.E

 theorem pin_product (phase a b : Bool) :
    PP.pin (K:=K) phase a*PP.pin (!phase) b=ExactTwoReferenceColours.pinValue phase a b := by
  cases phase <;> cases a <;> cases b <;>
    simp [PP.pin,ExactTwoReferenceColours.pinValue]

 theorem source_table (q : Signature K 4) (phase : Bool) (label : ℕ) (hl : label<2) (bits : List Bool) :
    Choice.table (sourceSignatures q phase) label bits=V.sourceTable q phase label bits := by
  interval_cases label
  · rfl
  · change PP.pin phase (bits.getD 0 false)*PP.pin (!phase) (bits.getD 1 false)=_
    exact pin_product phase _ _

 theorem target_table (q : Signature K 4) (label : ℕ) (hl : label<2) (bits : List Bool) :
    Choice.table (targetSignatures q) label bits=V.targetTable q label bits := by
  interval_cases label <;> rfl

 theorem weight_eq (F G : UniversalPairReduction.Surgery.Choice.Table K) (c : ℕ → Bool)
    (rows : List RawVertex) (h : ∀v∈rows,F v.1 (v.2.map (UniversalPairReduction.Surgery.Choice.bit c))=
      G v.1 (v.2.map (UniversalPairReduction.Surgery.Choice.bit c))) :
    Choice.weight F c rows=Choice.weight G c rows := by
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  exact h

 theorem source_value {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (q : Signature K 4) (phase : Bool) :
    (r.realize hr (sourceSignatures q phase) (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0=
      Choice.evaluate (V.sourceTable q phase) r.edges.length r.vertices := by
  rw [Choice.denote_eq_evaluate]
  apply Finset.sum_congr rfl
  intro c _
  apply weight_eq
  intro v hv
  exact source_table q phase v.1 (source_row hr v hv).1 _

 theorem target_value {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (q : Signature K 4) :
    ((raw r).realize (wellFormed hr) (targetSignatures q) (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0=
      Choice.evaluate (V.targetTable q) (raw r).edges.length (raw r).vertices := by
  rw [Choice.denote_eq_evaluate]
  apply Finset.sum_congr rfl
  intro c _
  apply weight_eq
  intro v hv
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hv
  exact target_table q _ ((wellFormed hr).1 i).1 _

/-- Before symmetry is used, exactly the two globally coherent orientations
remain. Arbitrary old q weights are retained, including cancellations. -/
theorem denote_two_branches {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (hm : 0<count r) (q : Signature K 4) :
    ((raw r).realize (wellFormed hr) (targetSignatures q) (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0=
      (r.realize hr (sourceSignatures q false) (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0+
      (r.realize hr (sourceSignatures q true) (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0 := by
  rw [target_value hr q,source_value hr q false,source_value hr q true]
  exact V.branch_sum hr hm q

def flippedVertices {n : ℕ} (N : Network K n) : Network K n where
  shape := N.shape
  vertex v x := N.vertex v (SD.flip x)
  edge := N.edge

/-- Actual closed-network variable substitution; this does not assume the
original vertex tensors themselves are self-dual. -/
theorem denote_flipped_closed (N : Network K 0)
    (he : ∀e a b,N.edge e (!a) (!b)=N.edge e a b) :
    (flippedVertices N).denote Fin.elim0=N.denote Fin.elim0 := by
  unfold Network.denote
  apply Fintype.sum_equiv (SD.flipEquiv (Fin N.shape.edges × Bool))
  intro z
  change ((∏v,N.vertex v (SD.flip (N.shape.assignment Fin.elim0 z v)))*
    ∏e,N.edge e (z (e,false)) (z (e,true)))=
      ((∏v,N.vertex v (N.shape.assignment Fin.elim0 (SD.flip z) v))*
        ∏e,N.edge e (!(z (e,false))) (!(z (e,true))))
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    congr 1
    have h := SD.assignment_flip N.shape Fin.elim0 z v
    have hx : SD.flip (Fin.elim0 : Fin 0 → Bool)=Fin.elim0 := by
      funext i
      exact Fin.elim0 i
    rw [hx] at h
    exact h.symm
  · apply Finset.prod_congr rfl
    intro e _
    exact (he e _ _).symm

 theorem source_flip (q : Signature K 4) (hq : SD.SelfDual q)
    (i : Fin 2) (x : Fin (sourceArity i.val) → Bool) :
    sourceSignatures q false i (SD.flip x)=sourceSignatures q true i x := by
  fin_cases i
  · change (Fin 4 → Bool) at x
    change q (SD.flip x)=q x
    exact hq x
  · change (Fin 2 → Bool) at x
    change PP.pin false (!(x 0))*PP.pin true (!(x 1))=PP.pin true (x 0)*PP.pin false (x 1)
    cases h0 : x 0 <;> cases h1 : x 1 <;> simp [PP.pin,h0,h1]

 theorem phase_values {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (q : Signature K 4) (hq : SD.SelfDual q) :
    (r.realize hr (sourceSignatures q true) (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0=
      (r.realize hr (sourceSignatures q false) (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0 := by
  let N := r.realize hr (sourceSignatures q false) (fun _ : Fin 1=>Signature.disequality)
  have hden : (r.realize hr (sourceSignatures q true) (fun _ : Fin 1=>Signature.disequality)).denote=
      (flippedVertices N).denote := by
    apply Network.denote_congr
    · intro v x
      exact (source_flip q hq (r.signatureLabel hr v) x).symm
    · intro e a b
      rfl
  rw [congrFun hden Fin.elim0]
  apply denote_flipped_closed N
  intro e a b
  exact SD.nativeX_self_dual a b

/-- Full target-validator and exact factor identity are derived from the
original input. No supplied target denotation, coherence or compiler is input. -/
theorem denote_factor {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (q : Signature K 4) (hq : SD.SelfDual q) :
    ((raw r).realize (wellFormed hr) (targetSignatures q) (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0=
      (if count r=0 then 1 else 2)*
        (r.realize hr (sourceSignatures q false) (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0 := by
  by_cases hm : count r=0
  · rw [target_value hr q,source_value hr q false,if_pos hm,one_mul]
    exact V.zero_value hr hm q
  · have hp : 0<count r := Nat.pos_of_ne_zero hm
    rw [denote_two_branches hr hp q,phase_values hr q hq,if_neg hm,two_mul]

/-- Literal singleton uniform EXACT2 instantiation of the full factor theorem. -/
theorem exactTwo_factor {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity) :
    ((raw r).realize (wellFormed hr) (targetSignatures (ExactTwoSignatures.q (K:=K)))
      (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0=
      (if count r=0 then 1 else 2)*
        (r.realize hr (sourceSignatures ExactTwoSignatures.q false)
          (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0 :=
  denote_factor hr ExactTwoSignatures.q ExactTwoSignatures.q_self_dual

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceSemantics
