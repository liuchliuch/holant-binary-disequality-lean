import Holant.Proofs.Traversal.ArityTwo.EndpointAddress


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortInstruction
open Holant Holant.Complexity Computability Holant.OneHot.StackProgram
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (s b : ℕ) (arity : ℕ → ℕ) {A : Type}
variable (labels : (i : Fin s) → Signature A (arity i.val))
variable (edges : Fin b → Kernel A) (codec : Encoding A Bool)
abbrev Query := RawPortQuery.Input s b arity
abbrev encoding := RawPortQuery.encoding s b arity

def exitPort (x : Query s b arity) : x.1.val.Ports arity :=
  (PortWalk.other x.1.val (RawPortQuery.port s b arity x)).getD (RawPortQuery.port s b arity x)

def exitQuery (x : Query s b arity) : Query s b arity :=
  ⟨x.1,x.1.val.route x.1.property (exitPort s b arity x)⟩

def exitEndpointComputes : Computes (encoding s b arity) RawClosedNetwork.endpointEncoding
    (fun x => RawPortQuery.endpoint s b arity (exitQuery s b arity x)) := by
  refine congrComputes (ifComputes (MatrixEmission.degreeComputes s b arity 2)
    (RawPortQuery.outgoingComputes s b arity) (RawPortQuery.endpointComputes s b arity)) ?_
  intro x
  have he : RawPortQuery.endpoint s b arity (exitQuery s b arity x) =
      x.1.val.portEndpoint x.1.property (exitPort s b arity x) := rfl
  change (if decide (PortWalk.degree (arity := arity) x.1.val (RawPortQuery.port s b arity x).1 = 2) = true
    then RawPortQuery.outgoing s b arity x else RawPortQuery.endpoint s b arity x) = _
  rw [he]
  cases ho : PortWalk.other x.1.val (RawPortQuery.port s b arity x) with
  | none =>
    have hd := (PortWalk.other_none_iff x.1.val (RawPortQuery.port s b arity x)).mp ho
    have hx : exitPort s b arity x = RawPortQuery.port s b arity x := by
      unfold exitPort; rw [ho]; rfl
    rw [hx]
    simpa only [hd, decide_false, Bool.false_eq_true, if_false] using
      (RawPortQuery.endpoint_at s b arity x).symm
  | some q =>
    have hd := (PortWalk.other_some x.1.val (RawPortQuery.port s b arity x) q ho).2.2
    have hx : exitPort s b arity x = q := by unfold exitPort; rw [ho]; rfl
    rw [hx]
    simpa only [hd, decide_true, if_true] using RawPortQuery.outgoing_at s b arity x q ho

def exitComputes : Computes (encoding s b arity) (encoding s b arity) (exitQuery s b arity) :=
  recode (pairComputes (RawPortQuery.sourceComputes s b arity) (exitEndpointComputes s b arity))
    id (fun _ => rfl) (fun _ => rfl)

def nextQuery (x : Query s b arity) : Query s b arity :=
  ⟨x.1,(exitQuery s b arity x).2.1,!(exitQuery s b arity x).2.2⟩

def nextComputes : Computes (encoding s b arity) (encoding s b arity) (nextQuery s b arity) :=
  recode (pairComputes (RawPortQuery.sourceComputes s b arity)
    ((exitEndpointComputes s b arity).andThen RawPortQuery.flipComputes))
    id (fun _ => rfl) (fun _ => rfl)

def binaryWord (x : Query s b arity) :=
  EndpointEmission.value s b arity edges codec (exitQuery s b arity x) ++
    MatrixEmission.vertexPortWord s b arity labels codec x

def binaryComputes : Computes (encoding s b arity) Frame.wordEncoding
    (binaryWord s b arity labels edges codec) :=
  joinComputes ((exitComputes s b arity).andThen (EndpointEmission.computes s b arity edges codec))
    (MatrixEmission.vertexPortComputes s b arity labels codec)

/-- Fields: terminal flag, physical unary continuation address, emitted code
entries. There is no bytecode list terminator inside an instruction payload. -/
abbrev Record := Bool × (ℕ × List Bool)
def recordEncoding : Encoding Record Bool :=
  pairEncoding encodingBoolBool (pairEncoding UnaryBinary.unaryEncoding Frame.wordEncoding)

def record (x : Query s b arity) : Record :=
  (decide (PortWalk.degree (arity := arity) x.1.val (RawPortQuery.port s b arity x).1 = 1),
    EndpointAddress.value s b arity (nextQuery s b arity x),
    if PortWalk.degree (arity := arity) x.1.val (RawPortQuery.port s b arity x).1 = 1 then
      MatrixEmission.unaryWord s b arity labels codec (RawPortQuery.vertexQuery s b arity x)
    else binaryWord s b arity labels edges codec x)

def computes : Computes (encoding s b arity) recordEncoding (record s b arity labels edges codec) :=
  congrComputes (pairComputes (MatrixEmission.degreeComputes s b arity 1)
    (pairComputes ((nextComputes s b arity).andThen (EndpointAddress.computes s b arity))
      (ifComputes (MatrixEmission.degreeComputes s b arity 1)
        (MatrixEmission.unaryPortComputes s b arity labels codec)
        (binaryComputes s b arity labels edges codec))))
    (fun _ => by simp [record])

theorem next_port (x : Query s b arity) :
    RawPortQuery.port s b arity (nextQuery s b arity x) =
      PortWalk.cross x.1.val x.1.property (exitPort s b arity x) := rfl

theorem binary_exact (x : Query s b arity) (q : x.1.val.Ports arity)
    (hq : PortWalk.other x.1.val (RawPortQuery.port s b arity x) = some q) :
    binaryWord s b arity labels edges codec x =
      MatrixEmission.word codec
        (matrixStep (Descriptors.edgeTable x.1.val x.1.property
          (fun e => edges (x.1.val.edgeLabel x.1.property e)) q) ++
        matrixStep (Descriptors.binaryTable x.1.val
          (fun v => labels (x.1.val.signatureLabel x.1.property v)) (RawPortQuery.port s b arity x))) := by
  rw [binaryWord,MatrixEmission.vertexPort_exact s b arity labels codec x
    (PortWalk.other_some x.1.val (RawPortQuery.port s b arity x) q hq).2.2]
  simp [EndpointEmission.value,exitQuery,exitPort,hq,Descriptors.edgeTable,
    MatrixEmission.word,entries,List.flatMap_append]

theorem continuation_bound (x : Query s b arity) :
    (record s b arity labels edges codec x).2.1 < 2*x.1.val.edges.length :=
  EndpointAddress.value_lt s b arity (nextQuery s b arity x)

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortInstruction
