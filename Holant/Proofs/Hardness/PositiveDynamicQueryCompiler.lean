import Holant.Proofs.Hardness.PositiveDynamicQueryLocalRows
import Holant.Proofs.Hardness.PositiveDynamicQueries

/-! The original graph drives both dynamic loop lengths. Every marked row is
expanded once by the nested writer; unmarked rows are copied verbatim. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueryCompiler
open Holant Holant.Complexity Computability BinaryCompose FixedFieldMachines
open GraphPreprocessing FixedGadgetSubstitution RawClosedNetwork
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
namespace Q
export PositiveDynamicQueries (count countComputes)
export ExactTwoChainQueries (arity Input TargetInput sourceEncoding targetEncoding)
end Q
namespace O
export ExactTwoChainOccurrence (Input inputEncoding Query queryEncoding contextComputes
  lengthComputes sourceComputes originalRowComputes before beforeComputes marked markedComputes
  allRowsComputes repeatEdgesComputes multiplyComputes binaryDouble unaryDouble)
end O
namespace L
export PositiveDynamicQueryLocalRows (LocalInput localEncoding innerInput placedRows rowsComputes)
end L
namespace WC
export BinaryInterpolation.WeightCompiler (multiplyUnaryComputes successorComputes)
end WC
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
abbrev unary := UnaryBinary.unaryEncoding
abbrev Input := O.Input 2 1 Q.arity
abbrev inputEncoding := O.inputEncoding 2 1 Q.arity
abbrev Query := O.Query 2 1 Q.arity
abbrev queryEncoding := O.queryEncoding 2 1 Q.arity

def unaryAdd : Computes (pairEncoding unary unary) unary (fun x=>x.1+x.2) :=
  recode (joinComputes
    ((Wiring.firstComputes unary unary).andThen (encodeComputes unary))
    ((Wiring.secondComputes unary unary).andThen (encodeComputes unary))) id
    (fun _=>rfl) (fun x=>by
      change List.replicate x.1 true ++ List.replicate x.2 true=List.replicate (x.1+x.2) true
      exact (List.replicate_add _ _ _).symm)

variable (d : PositiveDynamicParameters.Data)

def predecessor (r : Q.Input) : ℕ := d.constant*Q.count r+(d.constant-1)

def predecessorComputes : Computes Q.sourceEncoding unary (predecessor d) :=
  (pairComputes ((pairComputes (constantComputes Q.sourceEncoding unary d.constant)
    Q.countComputes).andThen WC.multiplyUnaryComputes)
    (constantComputes Q.sourceEncoding unary (d.constant-1))).andThen unaryAdd

theorem predecessor_length (r : Q.Input) : predecessor d r+1=d.length (Q.count r) := by
  have h := d.constant_spec.1
  rw [d.length_linear]
  unfold predecessor
  omega

def edgeCount (x : Input) : ℕ := 2*(predecessor d x.2*(x.1+1)+x.1)

def edgeCountComputes : Computes inputEncoding unary (edgeCount d) := by
  let p := (Wiring.secondComputes unary Q.sourceEncoding).andThen (predecessorComputes d)
  let k := Wiring.firstComputes unary Q.sourceEncoding
  exact ((pairComputes ((pairComputes p (k.andThen WC.successorComputes)).andThen
    WC.multiplyUnaryComputes) k).andThen unaryAdd).andThen O.unaryDouble

def offset (x : Query) : ℕ :=
  x.1.2.val.edges.length+edgeCount d x.1*O.before 2 1 Q.arity 1 x

def offsetComputes : Computes queryEncoding encodingNatBool (offset d) :=
  (pairComputes
    (((O.sourceComputes 2 1 Q.arity).andThen (FixedGadgetSubstitution.Compiler.edgeCountComputes 2 1 Q.arity)).andThen UnaryBinary.computes)
    ((pairComputes (((O.contextComputes 2 1 Q.arity).andThen (edgeCountComputes d)).andThen UnaryBinary.computes)
      ((O.beforeComputes 2 1 Q.arity 1).andThen UnaryBinary.computes)).andThen O.multiplyComputes)).andThen addComputes

def placement (x : Query) : L.LocalInput :=
  (predecessor d x.1.2,(x.1.1,(offset d x,(x.1.2.val.vertices.get x.2).2)))

def placementComputes : Computes queryEncoding L.localEncoding (placement d) :=
  pairComputes ((O.sourceComputes 2 1 Q.arity).andThen (predecessorComputes d))
    (pairComputes (O.lengthComputes 2 1 Q.arity)
      (pairComputes (offsetComputes d)
        ((O.originalRowComputes 2 1 Q.arity).andThen
          (recode (Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding))
            id (fun _=>rfl) (fun _=>rfl)))))

def rows (x : Query) : List RawVertex :=
  if O.marked 2 1 Q.arity 1 x then L.placedRows 0 (placement d x)
  else [x.1.2.val.vertices.get x.2]

def rowChunkComputes : Computes queryEncoding Frame.wordEncoding
    (fun x=>entries vertexEncoding (rows d x)) := by
  let yes := ((placementComputes d).andThen (L.rowsComputes 0)).andThen (entriesComputes vertexEncoding)
  let no := (O.originalRowComputes 2 1 Q.arity).andThen (entryComputes vertexEncoding)
  refine congrComputes (ifComputes (O.markedComputes 2 1 Q.arity 1) yes no) ?_
  intro x
  cases h : O.marked 2 1 Q.arity 1 x <;> simp [rows,h,entries]

def edgeRows (x : Query) : List ℕ :=
  if O.marked 2 1 Q.arity 1 x then List.replicate (edgeCount d x.1) 0 else []

def edgeChunkComputes : Computes queryEncoding Frame.wordEncoding
    (fun x=>entries encodingNatBool (edgeRows d x)) := by
  let yes := ((((O.contextComputes 2 1 Q.arity).andThen (edgeCountComputes d)).andThen
    (O.repeatEdgesComputes 0)).andThen (entriesComputes encodingNatBool))
  let no := constantComputes queryEncoding Frame.wordEncoding []
  refine congrComputes (ifComputes (O.markedComputes 2 1 Q.arity 1) yes no) ?_
  intro x
  cases h : O.marked 2 1 Q.arity 1 x <;> simp [edgeRows,h,entries]

def vertices (x : Input) : List RawVertex :=
  (List.finRange x.2.val.vertices.length).flatMap (fun i=>rows d ⟨x,i⟩)

def edges (x : Input) : List ℕ :=
  x.2.val.edges++(List.finRange x.2.val.vertices.length).flatMap (fun i=>edgeRows d ⟨x,i⟩)

def verticesComputes : Computes inputEncoding (framedListEncoding vertexEncoding) (vertices d) := by
  let run := O.allRowsComputes 2 1 Q.arity _ (rowChunkComputes d)
  refine recode (joinComputes run (constantComputes inputEncoding Frame.wordEncoding [false]))
    id (fun _=>rfl) ?_
  intro x
  have h := entries_append_encode vertexEncoding (vertices d x) []
  simpa only [vertices,entries,List.flatMap_assoc,List.append_nil,framedListEncode,
    framedListEncoding,Frame.wordEncoding,id_eq,Function.comp_def] using h

def edgesComputes : Computes inputEncoding (framedListEncoding encodingNatBool) (edges d) := by
  let original := (((Wiring.secondComputes unary Q.sourceEncoding).andThen
    (FixedGadgetSubstitution.Compiler.edgesComputes 2 1 Q.arity)).andThen (entriesComputes encodingNatBool))
  let added := O.allRowsComputes 2 1 Q.arity _ (edgeChunkComputes d)
  refine recode (joinComputes (joinComputes original added)
    (constantComputes inputEncoding Frame.wordEncoding [false])) id (fun _=>rfl) ?_
  intro x
  have h := entries_append_encode encodingNatBool (edges d x) []
  simpa only [edges,entries,List.flatMap_assoc,List.flatMap_append,List.append_nil,
    framedListEncode,framedListEncoding,Frame.wordEncoding,id_eq,Function.comp_def] using h

def raw (x : Input) : RawClosedNetwork := ⟨vertices d x,edges d x⟩

def rawComputes : Computes inputEncoding encoding (raw d) :=
  recode (pairComputes (verticesComputes d) (edgesComputes d)) id (fun _=>rfl) (fun _=>rfl)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueryCompiler
