import Holant.Proofs.Hardness.PositiveDynamicStageSeriesRecords
import Holant.Proofs.Hardness.PositiveDynamicParameters
import Holant.Proofs.Hardness.ThreeModeQueries
import Holant.Proofs.Hardness.ThreeModeGraphEvaluation

/-! Input-dependent positive dynamic graph queries. The original label stream
is counted once; only label 1 is expanded. All retained label-0 rows keep their
original ports, while the marked rows receive literal fully inlined original-q
records, rather than a staged signature in the oracle dictionary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueries
open Holant Holant.Complexity Computability BinaryCompose FixedFieldMachines FixedGadgetSubstitution RawClosedNetwork
namespace Q
export ExactTwoChainQueries (arity Input TargetInput sourceEncoding targetEncoding)
end Q
namespace R
export PositiveDynamicStageSeriesRecords (records valid boundary counts denote)
end R
namespace A
export ThreeModeAnnihilator (rootIndices rootIndices_length_le)
end A
namespace G
export ThreeModeGraphEvaluation (sourceValue targetValue targetSignatures kernels)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

def count (r : Q.Input) : ℕ := occurrences 1 r.val

def countComputes : Computes Q.sourceEncoding
    ThreeModeProgrammeRoots.unary count :=
  Compiler.occurrencesComputes 2 1 Q.arity 1

def templates (n k i : ℕ) : Template :=
  if i=1 then R.records 0 0 n k else identityTemplate Q.arity i

@[simp] theorem templates_original (n k : ℕ) :
    templates n k 0=identityTemplate Q.arity 0 := by simp [templates]

@[simp] theorem templates_marked (n k : ℕ) :
    templates n k 1=R.records 0 0 n k := by simp [templates]

theorem template_hypotheses (n k : ℕ) : ∀i<2,
    (templates n k i).WellFormed 1 1 Q.arity ∧
      (templates n k i).boundary=Q.arity i := by
  intro i hi
  interval_cases i
  · exact ⟨identityTemplate_wellFormed Q.arity (0 : Fin 1),rfl⟩
  · exact ⟨R.valid Q.arity (0 : Fin 1) rfl (0 : Fin 1) n k,R.boundary 0 0 n k⟩

theorem template_arity (n k : ℕ) : sourceArity (templates n k)=Q.arity := by
  funext i
  by_cases h : i=1
  · subst i
    exact R.boundary 0 0 n k
  · simp [sourceArity,templates,h,identityTemplate]

/-- An executable row expansion with dynamic, literal templates. -/
def raw (n k : ℕ) (r : Q.Input) : RawClosedNetwork := replace (templates n k) r.val

theorem raw_valid (n k : ℕ) (r : Q.Input) : (raw n k r).WellFormed 1 1 Q.arity :=
  replace_wellFormed _ _ r.property (template_hypotheses n k)

def stageValue (n k : ℕ) (r : Q.Input) : Q.TargetInput := ⟨raw n k r,raw_valid n k r⟩

/-- The stage length is derived from the actual original marked occurrences. -/
def value (d : PositiveDynamicParameters.Data) (x : ℕ × Q.Input) : Q.TargetInput :=
  stageValue (d.length (count x.2)) x.1 x.2

def sampleCount (r : Q.Input) : ℕ := (A.rootIndices (count r)).length+1

def sampleCountComputes : Computes Q.sourceEncoding ThreeModeProgrammeRoots.unary sampleCount :=
  countComputes.andThen ThreeModeProgrammeRoots.queryCountComputes

def queries (d : PositiveDynamicParameters.Data) (r : Q.Input) : List Q.TargetInput :=
  (List.range (sampleCount r)).map (fun k=>value d (k,r))

@[simp] theorem query_count (d : PositiveDynamicParameters.Data) (r : Q.Input) :
    (queries d r).length=sampleCount r := by simp [queries]

theorem query_count_le (d : PositiveDynamicParameters.Data) (r : Q.Input) :
    (queries d r).length≤(count r+1)^2+1 := by
  rw [query_count]
  exact Nat.add_le_add_right (A.rootIndices_length_le (count r)) 1

theorem query_valid (d : PositiveDynamicParameters.Data) (r : Q.Input)
    (q : Q.TargetInput) (_hq : q∈queries d r) : q.val.WellFormed 1 1 Q.arity := q.property

/-- Every unmarked original row is preserved exactly, including its ordered
external endpoints. In particular, original q is never replaced by staged q. -/
theorem unmarked_row (n k offset : ℕ) (r : Q.Input) (v : Fin r.val.vertices.length)
    (hv : (r.val.vertices.get v).1≠1) :
    (templates n k (r.val.vertices.get v).1).placeVertices offset
      (r.val.vertices.get v).2=[r.val.vertices.get v] := by
  simp only [templates,hv,ite_false]
  exact Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence.identity_place
    Q.arity _ _ (r.property.1 v).2

theorem expandRows_unchanged (n k offset : ℕ) (rs : List RawVertex)
    (hr : ∀row∈rs, row.1≠1 ∧ row.2.length=Q.arity row.1) :
    expandRows (templates n k) offset rs=⟨rs,[]⟩ := by
  induction rs generalizing offset with
  | nil => rfl
  | cons row rs ih =>
    obtain ⟨hlabel,hlen⟩ := hr row (by simp)
    have ht := ih (offset+(templates n k row.1).edges.length)
      (by intro r h; exact hr r (by simp [h]))
    simp only [expandRows,ht]
    have hp := Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence.identity_place
      Q.arity row offset hlen
    simp only [templates,hlabel,ite_false,identityTemplate] at hp ⊢
    rw [hp]
    rfl

/-- With no marked E occurrences, the sole oracle query is byte-for-byte the
original graph, not a positive-chain replacement of its q rows. -/
theorem raw_zero (n k : ℕ) (r : Q.Input) (hm : count r=0) : raw n k r=r.val := by
  have hnone : ∀row∈r.val.vertices, row.1≠1 := by
    have hfilter : (r.val.vertices.filter (fun row=>row.1==1))=[] :=
      List.length_eq_zero_iff.mp hm
    intro row hrow he
    have : row∈r.val.vertices.filter (fun row=>row.1==1) := by simp [hrow,he]
    simp [hfilter] at this
  have h := expandRows_unchanged n k r.val.edges.length r.val.vertices
    (by
      intro row hrow
      obtain ⟨v,rfl⟩ := List.mem_iff_get.mp hrow
      exact ⟨hnone _ (List.get_mem _ v),(r.property.1 v).2⟩)
  simp only [raw,replace,h,List.append_nil]

@[simp] theorem sampleCount_zero (r : Q.Input) (hm : count r=0) : sampleCount r=1 := by
  simp [sampleCount,hm,ThreeModeAnnihilator.rootIndices]

theorem queries_zero (d : PositiveDynamicParameters.Data) (r : Q.Input) (hm : count r=0) :
    (queries d r).map Subtype.val=[r.val] := by
  simp [queries,sampleCount_zero r hm,value,stageValue,raw_zero _ _ r hm]

section Semantics
variable {K : Type} [Field K] [CharZero K] (a b c : K)

def sequenceSignatures (n k : ℕ) (i : Fin 2) : Signature K (Q.arity i.val) :=
  if i.val=1 then ThreeModeSignatures.spectral
    ((PositiveDynamicStage.A a b n)^(k+1))
    ((PositiveDynamicStage.B a b n+PositiveDynamicStage.C c n)^(k+1))
    ((PositiveDynamicStage.B a b n-PositiveDynamicStage.C c n)^(k+1))
  else ThreeModeSignatures.original a b c

theorem local_identity (n k : ℕ) (hn : 0<n) (i : Fin 2) :
    (⟨(templates n k i.val).boundary,
      ((templates n k i.val).network (template_hypotheses n k i.val i.isLt).1
        (G.targetSignatures a b c) (G.kernels (K:=K))).denote⟩ : AnySignature K)=
      ⟨Q.arity i.val,(if i.val=1 then (1 : K) else 1) • sequenceSignatures a b c n k i⟩ := by
  fin_cases i
  · change (⟨4,((identityTemplate Q.arity 0).network
        (identityTemplate_wellFormed Q.arity (0 : Fin 1))
        (G.targetSignatures a b c) (G.kernels (K:=K))).denote⟩ : AnySignature K)=
      ⟨4,(1 : K) • ThreeModeSignatures.original a b c⟩
    simp only [one_smul]
    apply congrArg (fun f : Signature K 4=>(⟨4,f⟩ : AnySignature K))
    exact identityTemplate_denote Q.arity (0 : Fin 1) (G.targetSignatures a b c) G.kernels
  · simp only [templates,ite_true,one_smul,sequenceSignatures]
    have h := R.denote Q.arity (0 : Fin 1) rfl (0 : Fin 1) a b c n k hn
      (G.targetSignatures a b c) G.kernels rfl rfl
    exact Sigma.ext (R.boundary 0 0 n k) h

theorem stageValue_value (n k : ℕ) (hn : 0<n) (r : Q.Input) :
    G.targetValue a b c (stageValue n k r)=
      (r.val.realize r.property (sequenceSignatures a b c n k) G.kernels).denote Fin.elim0 := by
  obtain ⟨hq,he⟩ := Holant.LocalDrafts.BinaryInterpolation.RawPolynomial.replacement_same_arity
    r.val r.property (sequenceSignatures a b c n k) G.kernels 1 (templates n k)
    (fun i hi=>(template_hypotheses n k i hi).1) (template_arity n k)
    (G.targetSignatures a b c) 1 (local_identity a b c n k hn)
  simpa only [G.targetValue,stageValue,raw,one_pow,one_mul] using he

theorem value_value (d : PositiveDynamicParameters.Data) (r : Q.Input) (k : ℕ) :
    G.targetValue a b c (value d (k,r))=
      (r.val.realize r.property
        (sequenceSignatures a b c (d.length (count r)) k) G.kernels).denote Fin.elim0 :=
  stageValue_value a b c _ _ (d.length_pos _) r

end Semantics
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueries
