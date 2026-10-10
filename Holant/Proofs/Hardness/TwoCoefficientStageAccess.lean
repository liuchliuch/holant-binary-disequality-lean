import Holant.Proofs.Hardness.TwoCoefficientStage
import Holant.Proofs.Hardness.ExactTwoChainControlled
import Holant.Proofs.Algorithms.ControlledReduction

/-! Real all-occurrence access from the selected two-coefficient stage to
ORIGINAL weighted q, in one fixed original field presentation throughout.
The template is built from the actual1/2/4-copy network, all labels are
original q and native X, and the answer programme is the literal copier. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientStageAccess
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end Q
namespace N
export TwoCoefficientStage (network denote signature arity native counts bounded_counts)
end N
namespace D
export TwoCoefficientData (stage)
end D
namespace S
export TwoCoefficientSignatures (weighted)
end S
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (signature_cast_apply)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (a b : K)

def signatures (i : Fin 1) : Signature K (Q.arity i.val) := S.weighted a b
def kernels (_ : Fin 1) : Kernel K := Signature.disequality

def value (r : Q.TargetInput) : K :=
  (r.val.realize r.property (signatures a b) kernels).denote Fin.elim0

def tables : ExactSignatureTables d 1 1 Q.arity where
  vertex i x:=F.decode.symm (signatures a b i x)
  edge i x y:=F.decode.symm (kernels i x y)

theorem evaluate (r : Q.TargetInput) : (tables F a b).evaluate F r=value a b r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,tables,LinearEquiv.apply_symm_apply]
  rfl

def outputBound : PolynomialOutputBound Q.targetEncoding F.encoding (value a b) where
  bound:=((tables F a b).outputBound F).bound
  length_le r:=by rw [←evaluate F a b r]; exact ((tables F a b).outputBound F).length_le r

def labels (k : ℕ) : Labelling (N.network a b k).shape 1 1 Q.arity where
  vertex _:=0
  vertex_arity v:=(N.arity a b k v).symm
  edge _:=0

def template (k : ℕ) : Template := (labels a b k).template

theorem valid (k : ℕ) : (template a b k).WellFormed 1 1 Q.arity := (labels a b k).wellFormed

theorem template_denote (k : ℕ) :
    ((template a b k).network (valid a b k) (signatures a b) kernels).denote=
      S.weighted (D.stage a b k).1 (D.stage a b k).2 := by
  rw [←N.denote a b k]
  apply Labelling.denote_template_of_labels
  · intro v x
    change S.weighted a b (fun i=>x (Fin.cast (N.arity a b k v).symm i))=(N.network a b k).vertex v x
    apply C.signature_cast_apply
    exact (N.signature a b k v).symm
  · intro e x y
    exact congrFun₂ (N.native a b k e).symm x y

def templates (k : ℕ) (_ : ℕ) : Template := template a b k

theorem hypotheses (k : ℕ) : ∀i<1,
    (templates a b k i).WellFormed 1 1 Q.arity ∧ (templates a b k i).boundary=Q.arity i :=
  fun _ _=>⟨valid a b k,rfl⟩

def query (k : ℕ) : Q.TargetInput → Q.TargetInput :=
  Compiler.value 1 1 Q.arity (templates a b k) 1 Q.arity (hypotheses a b k)

def queryComputes (k : ℕ) : Computes Q.targetEncoding Q.targetEncoding (query a b k) :=
  Compiler.computes 1 1 Q.arity (templates a b k) 1 Q.arity (hypotheses a b k)

theorem query_value (k : ℕ) (r : Q.TargetInput) :
    value a b (query a b k r)=value (D.stage a b k).1 (D.stage a b k).2 r := by
  have hp := replacement_partition (templates a b k) r.val r.property
    (fun i hi=>(hypotheses a b k i hi).1)
    (signatures (D.stage a b k).1 (D.stage a b k).2) (signatures a b) kernels
    (fun _ : Fin 1=>(1 : K)) (fun i=>by
      simpa only [templates, signatures, one_smul] using template_denote a b k)
  simpa only [value, query, Compiler.value, Finset.prod_const_one,one_mul] using hp

/-- Explicit finite macro writer plus the same-presentation answer copier. -/
def source (k : ℕ) : LengthControlledOracleReduction Q.targetEncoding F.encoding
    Q.targetEncoding F.encoding (value (D.stage a b k).1 (D.stage a b k).2) (value a b) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq (queryComputes a b k)
    (identityComputes F.encoding) (outputBound F a b)
    (value (D.stage a b k).1 (D.stage a b k).2) (fun r=>(query_value a b k r).symm)

theorem template_original_labels (k : ℕ) (row : LocalVertex) (hr : row∈(template a b k).vertices) : row.1=0 := by
  rw [template,Labelling.template] at hr
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hr
  rfl

theorem template_native_labels (k : ℕ) (e : ℕ) (he : e∈(template a b k).edges) : e=0 := by
  rw [template,Labelling.template] at he
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp he
  rfl

theorem template_counts (k : ℕ) :
    (template a b k).vertices.length=2^k ∧ (template a b k).edges.length+2=2^(k+1) := by
  simpa only [template,Labelling.template,List.length_ofFn] using N.counts a b k

def outputs (k : ℕ) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Q.targetEncoding F.encoding (value a b) oracle) (r : Q.TargetInput) :
    (source F a b k).reduction.machine.OutputsInTime oracle (Q.targetEncoding.encode r)
      (F.encoding.encode (value (D.stage a b k).1 (D.stage a b k).2 r))
      ((source F a b k).reduction.time.eval (Q.targetEncoding.encode r).length) :=
  (source F a b k).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientStageAccess
