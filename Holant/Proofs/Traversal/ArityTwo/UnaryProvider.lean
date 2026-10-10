import Holant.Proofs.Traversal.ArityTwo.RunComposition


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.UnaryProvider
open Holant Holant.Complexity Computability Holant.OneHot.StackProgram
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open PortWalk Descriptors
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (s b : ℕ) (arity : ℕ → ℕ) {A : Type}
variable (labels : (i : Fin s) → Signature A (arity i.val))
variable (edges : Fin b → Kernel A) (codec : Encoding A Bool)
variable (hd : ∀ i : Fin s, arity i.val ≤ 2)

abbrev Input := {x : RawRootReach.Input s b arity // degree (arity := arity) x.1.val x.2 = 1}
def encoding := RunComposition.restricted (RawRootReach.inputEncoding s b arity)
  (fun x => degree (arity := arity) x.1.val x.2 = 1)
def first (x : Input s b arity) := RootPort.first x.val (by rw [x.property]; omega)
def vertex (x : Input s b arity) := ActionTableMeaning.vertex x.val.1.val x.val.1.property labels
def edge (x : Input s b arity) := ActionTableMeaning.edge x.val.1.val x.val.1.property edges
def tailMatrices (x : Input s b arity) :=
  pathMatrices x.val.1.val x.val.1.property (vertex s b arity labels x) (edge s b arity edges x)
    (walk x.val.1.val x.val.1.property (2*x.val.1.val.edges.length+1) [first s b arity x]
      (cross x.val.1.val x.val.1.property (first s b arity x))).1

def tailWord (x : Input s b arity) : List Bool :=
  ((tailMatrices s b arity labels edges x).map (fun mr => MatrixEmission.word codec
    ([.literal (mr.2 true),.literal (mr.2 false)] ++ transferCode mr.1))).getD []

def endpointQuery (opposite : Bool) (x : Input s b arity) :=
  RootPort.query x.val (by rw [x.property]; omega) opposite

def endpointComputes (opposite : Bool) : Computes (encoding s b arity) (RawPortQuery.encoding s b arity)
    (endpointQuery s b arity opposite) :=
  recode (RawBytecodeMachine.endpointWordComputes s b arity opposite) Subtype.val (fun _ => rfl)
    (fun x => RootPort.prepared x.val _ opposite)

def prepareComputes : Computes (encoding s b arity) Frame.wordEncoding
    (fun x => RawBytecodeMachine.endpointWord s b arity true x.val) :=
  recode (RawBytecodeMachine.endpointWordComputes s b arity true) Subtype.val (fun _ => rfl) (fun _ => rfl)

def tailComputes : Computes (encoding s b arity) Frame.wordEncoding (tailWord s b arity labels edges codec) :=
  RunComposition.computes (prepareComputes s b arity)
    (ActionTableCompiler.machine s b arity labels edges codec false [])
    (ActionTableCompiler.timePolynomial s b arity labels edges codec false []) (by
      intro x
      have hg : ∀ v, degree (arity := arity) x.val.1.val v ≤ 2 := fun v => hd (x.val.1.val.signatureLabel x.val.1.property v)
      obtain ⟨ms,right,hm,t,ht,hr⟩ := WalkCodeExpansion.path_execution
        x.val.1.val x.val.1.property labels edges codec hg (first s b arity x) x.property
      have hout : tailWord s b arity labels edges codec x =
          MatrixEmission.word codec ([.literal (right true),.literal (right false)] ++ transferCode ms) := by
        simp [tailWord,tailMatrices,vertex,edge,hm]
      rw [← hout] at hr
      have hin := RootPort.prepared x.val (show 0 < degree (arity := arity) x.val.1.val x.val.2 by rw [x.property]; omega) true
      exact ⟨t,by simpa [hin,RootPort.query,first] using ht,by simpa [hin,RootPort.query,first,StackProtocol.RunsExactly, StackProtocol.Cfg, Turing.FinTM2.Cfg, ActionTableCompiler.machine, Machine.computer, Turing.FinTM2.step] using hr⟩)

def value (x : Input s b arity) : List Bool :=
  tailWord s b arity labels edges codec x ++
    EndpointEmission.value s b arity edges codec (endpointQuery s b arity false x) ++
    MatrixEmission.word codec (dotCode (unaryTable x.val.1.val (vertex s b arity labels x) x.val.2))

def computes : Computes (encoding s b arity) Frame.wordEncoding (value s b arity labels edges codec) :=
  joinComputes (joinComputes (tailComputes s b arity labels edges codec hd)
    ((endpointComputes s b arity false).andThen (EndpointEmission.computes s b arity edges codec)))
    (recode (RawBytecodeMachine.dotWordComputes s b arity labels codec) Subtype.val (fun _ => rfl) (fun _ => rfl))

theorem computes_machine : (computes s b arity labels edges codec hd).machine =
    RawBytecodeMachine.pathMachine s b arity labels edges codec := by
  simp only [computes, joinComputes, RunComposition.andThen_machine, pairComputes_machine,
    tailComputes, RunComposition.computes, prepareComputes, endpointComputes, recode,
    RawBytecodeMachine.pathMachine, RawBytecodeMachine.join, WordJoin.computes]

include hd in
theorem value_original (x : Input s b arity) :
    ∃ c, pathFrom x.val.1.val x.val.1.property (vertex s b arity labels x) (edge s b arity edges x)
        x.val.2 x.property = some c ∧ value s b arity labels edges codec x = MatrixEmission.word codec c.code := by
  let r := x.val.1.val
  let h := x.val.1.property
  let p := first s b arity x
  have hg : ∀ v, degree (arity := arity) r v ≤ 2 := fun v => hd (r.signatureLabel h v)
  obtain ⟨q,hq,_⟩ := (path_completion r h hg p x.property).1
  have ht := walk_trace r h (2*r.edges.length+1) [p] (cross r h p) (walk_not_exhausted r h _ _)
  rw [hq] at ht
  obtain ⟨ms,right,hm⟩ := pathMatrices_trace r h (vertex s b arity labels x) (edge s b arity edges x) hg ht
  let E := edgeTable r h (edge s b arity edges x) p
  refine ⟨.path (unaryTable r (vertex s b arity labels x) x.val.2) (E::ms) right,?_,?_⟩
  · change (match (walk r h (2*r.edges.length+1) [p] (cross r h p)).2 with
      | .terminal _ => (pathMatrices r h (vertex s b arity labels x) (edge s b arity edges x)
          (walk r h (2*r.edges.length+1) [p] (cross r h p)).1).bind
          (fun t => some (Component.path (unaryTable r (vertex s b arity labels x) x.val.2) (E::t.1) t.2))
      | _ => none) = _
    rw [hq, hm]
    rfl
  · have hw : tailMatrices s b arity labels edges x = some (ms,right) := hm
    simp only [value,tailWord,hw,Option.map_some,Option.getD_some]
    simp [vertex,edge,p,first,endpointQuery,RootPort.query,
      ActionTableMeaning.query,EndpointEmission.value,Component.code,pathCode,transferCode,E,
      edgeTable,MatrixEmission.word,entries,List.flatMap_append,List.append_assoc,r,h,ActionTableMeaning.edge]

theorem primitive_bound (x : Input s b arity) :
    let w := computes s b arity labels edges codec hd
    primitiveCost w.machine (w.outputs x).steps
      (some (Turing.initList w.machine.computer ((encoding s b arity).encode x))) ≤
        (primitivePolynomial w).eval ((encoding s b arity).encode x).length :=
  computes_primitive_cost (computes s b arity labels edges codec hd) x

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.UnaryProvider
