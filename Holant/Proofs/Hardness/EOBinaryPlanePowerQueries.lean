import Holant.Proofs.Hardness.EOBinaryPlaneGramAccess
import Holant.Proofs.Hardness.ExactTwoChainQueries
import Holant.Proofs.BinaryInterpolation.RawPolynomial

/-! Positive Hadamard powers use the existing variable-length two-edge-chain
machine. Its exact original-record row writer is reused; the new theorem proves
its contraction for an arbitrary binary lift, without an EXACT2 hypothesis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePowerQueries
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace B
export EOBinaryPlaneCore (lift)
end B
namespace C
export ExactTwoChain (series series_denote network)
end C
namespace T
export ExactTwoChainTemplate (shapeTemplate series_shape_independent compile)
end T
namespace Q
export ExactTwoChainQueries (arity Input TargetInput value computes variableEncoding targetEncoding)
end Q
namespace R
export ExactTwoChainRecords (explicitTemplate compile_eq valid)
end R
namespace V
export RealDenseSignTwistStageAccess (value)
end V
namespace M
export EOBinaryPlaneGramAccess (value)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
variable {K : Type} [Field K]

def network (f : Signature K 2) : ℕ→Network K 4
  | 0=>Network.corolla (B.lift f)
  | k+1=>C.series (network f k) (Network.corolla (B.lift f))

theorem series_lift (N M : Network K 4) (f g : Signature K 2)
    (hN : N.denote=B.lift f) (hM : M.denote=B.lift g) :
    (C.series N M).denote=B.lift (fun z=>f z*g z) := by
  funext x
  rw [C.series_denote,hN,hM]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [B.lift,h0,h1,h2,h3]

theorem network_denote (f : Signature K 2) (k : ℕ) :
    (network f k).denote=B.lift (fun z=>f z^(k+1)) := by
  induction k with
  | zero=>simp [network,Network.denote_corolla]
  | succ k ih=>
      rw [network,series_lift _ _ _ _ ih (Network.denote_corolla _)]
      simp only [pow_succ]

theorem signature (f : Signature K 2) (k : ℕ) (v : Fin (network f k).shape.vertices) :
    (⟨(network f k).shape.arity v,(network f k).vertex v⟩ : AnySignature K)=⟨4,B.lift f⟩ := by
  induction k with
  | zero=>rfl
  | succ k ih=>
      change (⟨(Network.tensorFinite (network f k) (Network.corolla (B.lift f))).arity (finSumFinEquiv.symm v),
        (Network.tensorFinite (network f k) (Network.corolla (B.lift f))).vertex (finSumFinEquiv.symm v)⟩ : AnySignature K)=_
      cases finSumFinEquiv.symm v with
      | inl v=>exact ih v
      | inr v=>rfl

theorem native (f : Signature K 2) (k : ℕ) : ∀e,(network f k).edge e=Signature.disequality := by
  induction k with
  | zero=>intro e; exact Fin.elim0 e
  | succ k ih=>
      intro e
      refine Fin.cases rfl (fun e=>?_) e
      refine Fin.cases rfl (fun e=>?_) e
      change Sum.elim (network f k).edge (Network.corolla (B.lift f)).edge
        (finSumFinEquiv.symm e)=Signature.disequality
      cases finSumFinEquiv.symm e with
      | inl e=>exact ih e
      | inr e=>exact Fin.elim0 e

theorem shape_eq (f : Signature K 2) (k : ℕ) :
    (network f k).shape=(C.network (K:=ℚ) k).shape := by
  induction k with
  | zero=>rfl
  | succ k ih=>exact T.series_shape_independent _ _ _ _ ih rfl

def labels (f : Signature K 2) (k : ℕ) : Labelling (network f k).shape 1 1 Q.arity where
  vertex _:=0
  vertex_arity v:=(congrArg Sigma.fst (signature f k v)).symm
  edge _:=0

theorem template_eq (f : Signature K 2) (k : ℕ) :
    R.explicitTemplate 0 0 k=(labels f k).template := by
  rw [←R.compile_eq,T.compile]
  have h : (labels f k).template=T.shapeTemplate (network f k).shape 0 0 := by
    simp [T.shapeTemplate,Labelling.template,labels]
  rw [h,shape_eq]

theorem template_denote (f : Signature K 2) (k : ℕ) :
    ((R.explicitTemplate 0 0 k).network (R.valid Q.arity (0 : Fin 1) rfl (0 : Fin 1) k)
      (fun _ : Fin 1=>B.lift f) (fun _ : Fin 1=>Signature.disequality)).denote=
      B.lift (fun z=>f z^(k+1)) := by
  have h := Holant.Complexity.BinaryInterpolation.Chains.template_denote_heq _ _
    (R.valid Q.arity (0 : Fin 1) rfl (0 : Fin 1) k) (labels f k).wellFormed
    (template_eq f k) (fun _ : Fin 1=>B.lift f) (fun _ : Fin 1=>Signature.disequality)
  apply (eq_of_heq h).trans
  rw [←network_denote f k]
  apply Labelling.denote_template_of_labels
  · intro v x
    change B.lift f (fun i=>x (Fin.cast (congrArg Sigma.fst (signature f k v)).symm i))=
      (network f k).vertex v x
    apply Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
    exact (signature f k v).symm
  · intro e x y
    exact congrFun₂ (native f k e).symm x y

theorem local_identity (f : Signature K 2) (k : ℕ) (i : Fin 2) :
    (⟨(ExactTwoChainOccurrence.templates Q.arity 1 0 0 k i.val).boundary,
      ((ExactTwoChainOccurrence.templates Q.arity 1 0 0 k i.val).network
        (ExactTwoChainQueries.template_hypotheses k i.val i.isLt).1
        (fun _ : Fin 1=>B.lift f) (fun _ : Fin 1=>Signature.disequality)).denote⟩ : AnySignature K)=
      ⟨Q.arity i.val,(if i.val=1 then (1 : K) else 1) •
        EOBinaryPlaneGramGraph.palette f (fun z=>f z^(k+1)) i⟩ := by
  fin_cases i
  · change (⟨4,((identityTemplate Q.arity 0).network
        (identityTemplate_wellFormed Q.arity (0 : Fin 1))
        (fun _ : Fin 1=>B.lift f) (fun _ : Fin 1=>Signature.disequality)).denote⟩ : AnySignature K)=
        ⟨4,(1 : K) • B.lift f⟩
    rw [one_smul]
    apply congrArg (fun h : Signature K 4=>(⟨4,h⟩ : AnySignature K))
    exact identityTemplate_denote Q.arity (0 : Fin 1) (fun _=>B.lift f)
      (fun _ : Fin 1=>Signature.disequality)
  · change (⟨4,((R.explicitTemplate 0 0 k).network
        (R.valid Q.arity (0 : Fin 1) rfl (0 : Fin 1) k)
        (fun _ : Fin 1=>B.lift f) (fun _ : Fin 1=>Signature.disequality)).denote⟩ : AnySignature K)=
        ⟨4,(1 : K) • B.lift (fun z=>f z^(k+1))⟩
    rw [one_smul,template_denote]

/-- Exact semantics of the existing finite machine's variable-k query, with
no scalar correction and no target-table programme supplied by a caller. -/
theorem query_value (f : Signature K 2) (r : Q.Input) (k : ℕ) :
    V.value (B.lift f) (Q.value (k,r))=M.value f (fun z=>f z^(k+1)) r := by
  obtain ⟨hq,he⟩ := Holant.LocalDrafts.BinaryInterpolation.RawPolynomial.replacement_same_arity
    r.val r.property (EOBinaryPlaneGramGraph.palette f (fun z=>f z^(k+1)))
    (fun _ : Fin 1=>Signature.disequality) 1 (ExactTwoChainOccurrence.templates Q.arity 1 0 0 k)
    (fun i hi=>(ExactTwoChainQueries.template_hypotheses k i hi).1)
    (ExactTwoChainQueries.template_arity k) (fun _ : Fin 1=>B.lift f) (1 : K) (local_identity f k)
  simpa +unfoldPartialApp only [V.value,M.value,Q.value,ExactTwoChainOccurrence.raw_eq_replace,RealDenseSignTwistStageAccess.signatures,
    RealDenseSignTwistStageAccess.kernels,one_pow,one_mul] using he

/-- The raw-record graph compiler is one machine taking the unary exponent
as input. It is not a nonuniform selection of one compiler per exponent. -/
abbrev queryComputes := ExactTwoChainQueries.computes

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePowerQueries
