import Holant.Proofs.Hardness.ExactTwoChainRawCorrectness
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.Batch
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Bounds
import Holant.Complexity.OracleBatch.ReductionTrace

/-! Full validated all-occurrence batch for E interpolation. Input has literal
labels[original q,E], both arity4. Every actual oracle query contains q only.
For index i≤m, each E becomes i+2 q copies, so the pencil parameter is2^(i+1).
The code and all m+1 queries are physically emitted from the original graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainQueries
open Holant Holant.Complexity Computability BinaryCompose FixedFieldMachines
open FixedGadgetSubstitution RawClosedNetwork
namespace O
export ExactTwoChainOccurrence (templates raw raw_eq_replace inputEncoding rawComputes)
end O
namespace R
export ExactTwoChainRecords (valid explicitTemplate)
end R
namespace BQ
export Holant.Complexity.BinaryInterpolation.Chains.Compiler.BoundedQueries
  (Input inputEncoding sourceComputes indexComputes input_length_bound)
end BQ
namespace Batch
export Holant.Complexity.BinaryInterpolation.Chains.Compiler.Batch
  (samples samplesComputes samples_length)
end Batch
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

def arity (_ : ℕ) : ℕ := 4
abbrev Input := ExactSignatureTables.Input 2 1 arity
abbrev TargetInput := ExactSignatureTables.Input 1 1 arity
abbrev sourceEncoding := validatedEncoding 2 1 arity
abbrev targetEncoding := validatedEncoding 1 1 arity
abbrev variableEncoding := O.inputEncoding 2 1 arity

theorem template_hypotheses (k : ℕ) : ∀i<2,
    (O.templates arity 1 0 0 k i).WellFormed 1 1 arity ∧
      (O.templates arity 1 0 0 k i).boundary=arity i := by
  intro i hi
  interval_cases i
  · simp only [O.templates,show (0 : ℕ)≠1 by decide,ite_false]
    exact ⟨identityTemplate_wellFormed arity (0 : Fin 1),rfl⟩
  · simp only [O.templates,ite_true]
    exact ⟨R.valid arity (0 : Fin 1) rfl (0 : Fin 1) k,rfl⟩

theorem template_arity (k : ℕ) : sourceArity (O.templates arity 1 0 0 k)=arity := by
  funext i
  by_cases h : i=1 <;> simp [sourceArity,O.templates,R.explicitTemplate,identityTemplate,arity,h]

theorem raw_valid (x : ℕ × Input) : (O.raw 2 1 arity 1 0 0 x).WellFormed 1 1 arity := by
  rw [O.raw_eq_replace]
  exact replace_wellFormed _ _ x.2.property (template_hypotheses x.1)

def value (x : ℕ × Input) : TargetInput := ⟨O.raw 2 1 arity 1 0 0 x,raw_valid x⟩

def computes : Computes variableEncoding targetEncoding value :=
  recode (O.rawComputes 2 1 arity 1 0 0) id (fun _=>rfl) (fun _=>rfl)

abbrev Sample := BQ.Input 2 1 arity 1
abbrev sampleEncoding := BQ.inputEncoding 2 1 arity 1

def sample (x : Sample) : TargetInput := value (x.2.val+1,x.1)

def sampleComputes : Computes sampleEncoding targetEncoding sample :=
  (pairComputes
    ((BQ.indexComputes 2 1 arity 1).andThen
      Holant.Complexity.BinaryInterpolation.Chains.Compiler.successorComputes)
    (BQ.sourceComputes 2 1 arity 1)).andThen computes

def queries (r : Input) : List TargetInput := Batch.samples 2 1 arity 1 sample r

def queriesComputes : Computes sourceEncoding (framedListEncoding targetEncoding) queries :=
  Batch.samplesComputes 2 1 arity 1 targetEncoding sample sampleComputes

theorem query_count (r : Input) : (queries r).length=occurrences 1 r.val+1 :=
  Batch.samples_length 2 1 arity 1 sample r

abbrev codeEncoding := Holant.OneHot.StackProgram.codeEncoding BinaryInterpolation.WeightCompiler.labels

def code (r : Input) := BinaryInterpolation.WeightCompiler.reference true (occurrences 1 r.val)

def codeComputes : Computes sourceEncoding codeEncoding code :=
  (FixedGadgetSubstitution.Compiler.occurrencesComputes 2 1 arity 1).andThen
    (BinaryInterpolation.WeightCompiler.computes true)

def preprocessing (r : Input) := (queries r,code r)

def pre : Computes sourceEncoding (OracleBatch.contextEncoding targetEncoding codeEncoding) preprocessing :=
  pairComputes queriesComputes codeComputes

theorem sample_input_bound (x : Sample) :
    (sampleEncoding.encode x).length≤3*(sourceEncoding.encode x.1).length+1 :=
  BQ.input_length_bound 2 1 arity 1 x

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainQueries
