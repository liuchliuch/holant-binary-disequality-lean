import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualContext
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionExecution

/-! The genuine selected unary original cut ID is serialized and physically
rearranged with its retained raw graph/root query. No guessed cut or value-only
label reconstruction is involved. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CycleQuery
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (ResidualContext.Query s b arity) Bool where
  encode x := (pairEncoding (RawRootReach.inputEncoding s b arity) UnaryBinary.unaryEncoding).encode
    (ResidualContext.original x,(ResidualContext.edge x.1).val)
  decode bits := do
    let (q,e) ← (pairEncoding (RawRootReach.inputEncoding s b arity) UnaryBinary.unaryEncoding).decode bits
    if he : e<q.1.val.edges.length then
      let data : ResidualContext.Data s b arity := ⟨q.1,⟨e,he⟩⟩
      if hu : ResidualContext.Unused data then some ⟨⟨data,hu⟩,q.2⟩ else none
    else none
  decode_encode x := by
    rw [(pairEncoding (RawRootReach.inputEncoding s b arity) UnaryBinary.unaryEncoding).decode_encode]
    simp only [Option.bind_eq_bind,Option.bind_some]
    dsimp only [ResidualContext.original,ResidualContext.edge,ResidualContext.source]
    rw [dif_pos (ResidualContext.edge x.1).isLt]
    rw [dif_pos x.1.property]

def words := pairEncoding Frame.wordEncoding Frame.wordEncoding
noncomputable def wireComputes : Computes (pairEncoding words Frame.wordEncoding) (pairEncoding words Frame.wordEncoding)
    (fun x : (List Bool × List Bool) × List Bool => ((x.1.1,x.2),x.1.2)) :=
  pairComputes (pairComputes ((Wiring.firstComputes words Frame.wordEncoding).andThen
    (Wiring.firstComputes Frame.wordEncoding Frame.wordEncoding)) (Wiring.secondComputes words Frame.wordEncoding))
    ((Wiring.firstComputes words Frame.wordEncoding).andThen (Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding))
abbrev wireMachine := pairMachine (pairMachine (Wiring.firstMachine.compose Wiring.firstMachine) secondMachine)
  (Wiring.firstMachine.compose secondMachine)
@[simp] theorem wire_machine : wireComputes.machine=wireMachine := rfl
noncomputable def serializeComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (pairEncoding words Frame.wordEncoding)
      (fun x => ((RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val,List.replicate x.2.val true),encodeNat (ResidualContext.edge x.1).val)) :=
  recode (rightMapComputes (RawRootReach.inputEncoding s b arity) UnaryBinary.computes)
    (fun x => (ResidualContext.original x,(ResidualContext.edge x.1).val)) (fun _ => rfl) (fun _ => rfl)
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (ResidualContext.queryEncoding s b arity) id :=
  recode ((serializeComputes s b arity).andThen wireComputes) id (fun _ => rfl) (fun _ => rfl)
abbrev machine := (rightMapMachine UnaryBinary.machine).compose wireMachine
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine := rfl
theorem inFP : InFP (inputEncoding s b arity) (ResidualContext.queryEncoding s b arity) id := (computes s b arity).inFP

theorem input_length (x : ResidualContext.Query s b arity) :
    ((inputEncoding s b arity).encode x).length≤7*((RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length+1) := by
  have h := RawRootReach.input_length_le_original (ResidualContext.original x)
  have hc := (ResidualContext.source x.1).val.counts_le_encoded_length
  have he := (ResidualContext.edge x.1).isLt
  change (ResidualContext.edge x.1).val<(ResidualContext.source x.1).val.edges.length at he
  change (Holant.Algebraic.frame ((RawRootReach.inputEncoding s b arity).encode (ResidualContext.original x))++
    List.replicate (ResidualContext.edge x.1).val true).length≤_
  simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  change _≤3*((RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length+1) at h
  omega
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CycleQuery
