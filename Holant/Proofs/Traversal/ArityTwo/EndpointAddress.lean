import Holant.Proofs.Traversal.ArityTwo.EndpointEmission


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.EndpointAddress
open Holant Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
noncomputable section
variable (s b : ℕ) (arity : ℕ → ℕ)

def sideWord : Computes encodingBoolBool Frame.wordEncoding
    (fun bit => List.replicate bit.toNat true) :=
  FiniteRecode.computes _ _ _ 1 (fun bit => by cases bit <;> decide)

def candidate (x : EndpointEmission.Scan s b arity) : List Bool :=
  List.replicate (2*x.2.val+x.1.2.2.toNat) true

def candidateComputes : Computes (EndpointEmission.scanEncoding s b arity) Frame.wordEncoding
    (candidate s b arity) :=
  congrComputes (joinComputes
    (joinComputes
      ((EndpointEmission.indexComputes s b arity).andThen (encodeComputes UnaryBinary.unaryEncoding))
      ((EndpointEmission.indexComputes s b arity).andThen (encodeComputes UnaryBinary.unaryEncoding)))
    ((EndpointEmission.sideComputes s b arity).andThen sideWord))
    (fun x => by
      change (List.replicate x.2.val true ++ List.replicate x.2.val true) ++
        List.replicate x.1.2.2.toNat true = _
      rw [← List.replicate_add, ← List.replicate_add]
      simp only [candidate, two_mul])

def chunk (x : EndpointEmission.Scan s b arity) :=
  if x.2.val = x.1.2.1.val then candidate s b arity x else []

def chunkComputes : Computes (EndpointEmission.scanEncoding s b arity) Frame.wordEncoding
    (chunk s b arity) :=
  congrComputes (ifComputes (EndpointEmission.matchesComputes s b arity)
    (candidateComputes s b arity)
    (constantComputes (EndpointEmission.scanEncoding s b arity) Frame.wordEncoding []))
    (fun _ => by simp [chunk])

def value (x : RawPortQuery.Input s b arity) := 2*x.2.1.val+x.2.2.toNat

def computes : Computes (RawPortQuery.encoding s b arity) UnaryBinary.unaryEncoding
    (value s b arity) := by
  let scan := (EndpointEmission.prepare s b arity).andThen
    (ContextFlatMap.computes (RawPortQuery.encoding s b arity)
      (fun x => OccurrenceLabel.unaryPortEncoding x.1.val.edges.length)
      (chunk s b arity) (chunkComputes s b arity))
  refine recode scan id (fun _ => rfl) ?_
  intro x
  have h := EndpointEmission.select_flatMap (fun e => candidate s b arity ⟨x,e⟩) x.2.1
    (List.finRange x.1.val.edges.length) (List.nodup_finRange _) (by simp)
  simpa [ContextFlatMap.value, Frame.wordEncoding, chunk,candidate,value,UnaryBinary.unaryEncoding,Fin.ext_iff] using h

theorem value_lt (x : RawPortQuery.Input s b arity) : value s b arity x < 2*x.1.val.edges.length := by
  have he := x.2.1.isLt
  cases hb : x.2.2 <;> simp [value, hb] <;> omega

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.EndpointAddress
