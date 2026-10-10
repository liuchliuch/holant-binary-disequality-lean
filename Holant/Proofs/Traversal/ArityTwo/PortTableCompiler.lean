import Holant.Proofs.Traversal.ArityTwo.PortInstruction


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortTableCompiler
open Holant Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (s b : ℕ) (arity : ℕ → ℕ) {A : Type}
variable (labels : (i : Fin s) → Signature A (arity i.val))
variable (edges : Fin b → Kernel A) (codec : Encoding A Bool)
abbrev Input := FixedGadgetSubstitution.Compiler.Input s b arity
abbrev encoding := RawClosedNetwork.validatedEncoding s b arity

def endpointRecord (side : Bool) (x : EdgeWord.Input s b arity) :=
  PortInstruction.record s b arity labels edges codec (EdgeWord.atSide side x)

def endpointComputes (side : Bool) :
    Computes (EdgeWord.inputEncoding s b arity) PortInstruction.recordEncoding
      (endpointRecord s b arity labels edges codec side) :=
  (EdgeWord.queryComputes s b arity side).andThen (PortInstruction.computes s b arity labels edges codec)

def chunk (x : EdgeWord.Input s b arity) : List Bool :=
  entry PortInstruction.recordEncoding (endpointRecord s b arity labels edges codec false x) ++
    entry PortInstruction.recordEncoding (endpointRecord s b arity labels edges codec true x)

def chunkComputes : Computes (EdgeWord.inputEncoding s b arity) Frame.wordEncoding
    (chunk s b arity labels edges codec) :=
  joinComputes
    ((endpointComputes s b arity labels edges codec false).andThen (entryComputes PortInstruction.recordEncoding))
    ((endpointComputes s b arity labels edges codec true).andThen (entryComputes PortInstruction.recordEncoding))

def value (r : Input s b arity) : List PortInstruction.Record :=
  (List.finRange r.val.edges.length).flatMap (fun e =>
    [endpointRecord s b arity labels edges codec false ⟨r,e⟩,
      endpointRecord s b arity labels edges codec true ⟨r,e⟩])

def computes : Computes (encoding s b arity) (framedListEncoding PortInstruction.recordEncoding)
    (value s b arity labels edges codec) := by
  let scanned := (Holant.LocalDrafts.Tractability.ProductMachine.RawCompiler.allEdgesPrepare s b arity).andThen
    (ContextFlatMap.computes (encoding s b arity)
      (fun r => OccurrenceLabel.unaryPortEncoding r.val.edges.length)
      (chunk s b arity labels edges codec) (chunkComputes s b arity labels edges codec))
  refine recode (joinComputes scanned
    (constantComputes (encoding s b arity) Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro r
  have h := entries_append_encode PortInstruction.recordEncoding (value s b arity labels edges codec r) []
  simpa [Frame.wordEncoding,ContextFlatMap.value,value,chunk,entries,List.flatMap_assoc,List.flatMap_append,framedListEncoding,
    framedListEncode,List.append_assoc] using h

theorem length (r : Input s b arity) : (value s b arity labels edges codec r).length = 2*r.val.edges.length := by
  simp [value,List.length_flatMap,Nat.mul_comm]

theorem two_rows_get {B : Type} (n : ℕ) (f : Fin n → Bool → B) (e : Fin n) (side : Bool) :
    ((List.finRange n).flatMap (fun i => [f i false,f i true])).get
      ⟨2*e.val+side.toNat,by
        have he := e.isLt
        have hl : ((List.finRange n).flatMap (fun i => [f i false,f i true])).length = 2*n := by
          simp [List.length_flatMap,Nat.mul_comm]
        rw [hl]
        cases side <;> simp <;> omega⟩ = f e side := by
  induction n with
  | zero => exact Fin.elim0 e
  | succ n ih =>
    induction e using Fin.cases with
    | zero => cases side <;> simp [List.finRange_succ,List.get_eq_getElem]
    | succ e =>
      have h := ih (fun i bit => f i.succ bit) e
      have he : 2 * e.succ.val + side.toNat = (2 * e.val + side.toNat) + 2 := by simp [Fin.val_succ]; omega
      simpa only [List.finRange_succ,List.flatMap_cons,List.flatMap_map,Function.comp_apply,
        List.append_assoc,List.cons_append,List.nil_append,List.get_eq_getElem,he,
        Nat.add_succ,Nat.add_zero,List.getElem_cons_succ] using h

theorem get_endpoint (r : Input s b arity) (e : Fin r.val.edges.length) (side : Bool) :
    (value s b arity labels edges codec r).get
      ⟨2*e.val+side.toNat,by
        rw [length]
        exact EndpointAddress.value_lt s b arity ⟨r,e,side⟩⟩ =
      PortInstruction.record s b arity labels edges codec ⟨r,e,side⟩ :=
  two_rows_get _ (fun e side => PortInstruction.record s b arity labels edges codec ⟨r,e,side⟩) e side

theorem inFP : InFP (encoding s b arity) (framedListEncoding PortInstruction.recordEncoding)
    (value s b arity labels edges codec) := (computes s b arity labels edges codec).inFP

theorem output_length (r : Input s b arity) :
    ((framedListEncoding PortInstruction.recordEncoding).encode
      (value s b arity labels edges codec r)).length ≤
      (computes s b arity labels edges codec).outputBound.bound.eval
        (RawClosedNetwork.encoding.encode r.val).length :=
  (computes s b arity labels edges codec).outputBound.length_le r

theorem primitive_bound (r : Input s b arity) :
    let w := computes s b arity labels edges codec
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes s b arity labels edges codec) r

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortTableCompiler
