import Holant.Proofs.Traversal.ArityTwo.UnaryProvider


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.CycleProvider
open Holant Holant.Complexity Computability Holant.OneHot.StackProgram
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open PortWalk Descriptors
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (s b : ℕ) (arity : ℕ → ℕ) {A : Type}
variable (labels : (i : Fin s) → Signature A (arity i.val))
variable (edges : Fin b → Kernel A) (codec : Encoding A Bool)
variable (hd : ∀ i : Fin s, arity i.val ≤ 2)

def Property (x : RawRootReach.Input s b arity) : Prop :=
  degree (arity := arity) x.1.val x.2 = 2 ∧
    ∀ v, (x.1.val.graph x.1.property).label v = (x.1.val.graph x.1.property).label x.2 → degree (arity := arity) x.1.val v ≠ 1
abbrev Input := {x : RawRootReach.Input s b arity // Property s b arity x}
def encoding := RunComposition.restricted (RawRootReach.inputEncoding s b arity) (Property s b arity)

def first (x : Input s b arity) := RootPort.first x.val (by rw [x.property.1]; omega)
def vertex (x : Input s b arity) := ActionTableMeaning.vertex x.val.1.val x.val.1.property labels
def edge (x : Input s b arity) := ActionTableMeaning.edge x.val.1.val x.val.1.property edges
def matrices (x : Input s b arity) :=
  cycleMatrices x.val.1.val x.val.1.property (vertex s b arity labels x) (edge s b arity edges x)
    (walk x.val.1.val x.val.1.property (2*x.val.1.val.edges.length+1) [] (first s b arity x)).1

def transferWord (base : List Bool) (x : Input s b arity) :=
  ((matrices s b arity labels edges x).map (fun ms => base ++ MatrixEmission.word codec (transferCode ms))).getD []

def prepareComputes : Computes (encoding s b arity) Frame.wordEncoding
    (fun x => RawBytecodeMachine.endpointWord s b arity false x.val) :=
  recode (RawBytecodeMachine.endpointWordComputes s b arity false) Subtype.val (fun _ => rfl) (fun _ => rfl)

def transferComputes (base : List Bool) : Computes (encoding s b arity) Frame.wordEncoding
    (transferWord s b arity labels edges codec base) :=
  RunComposition.computes (prepareComputes s b arity)
    (ActionTableCompiler.machine s b arity labels edges codec true base)
    (ActionTableCompiler.timePolynomial s b arity labels edges codec true base) (by
      intro x
      have hg : ∀ v, degree (arity := arity) x.val.1.val v ≤ 2 := fun v => hd (x.val.1.val.signatureLabel x.val.1.property v)
      obtain ⟨ms,hm,t,ht,hr⟩ := WalkCodeExpansion.cycle_execution
        x.val.1.val x.val.1.property labels edges codec hg (first s b arity x)
        x.property.1 x.property.2 base
      have hout : transferWord s b arity labels edges codec base x =
          base ++ MatrixEmission.word codec (transferCode ms) := by
        simp [transferWord,matrices,vertex,edge,hm]
      rw [← hout] at hr
      have hin := RootPort.prepared x.val (show 0 < degree (arity := arity) x.val.1.val x.val.2 by rw [x.property.1]; omega) false
      exact ⟨t,by simpa [hin,RootPort.query,first] using ht,by simpa [hin,RootPort.query,first,StackProtocol.RunsExactly, StackProtocol.Cfg, Turing.FinTM2.Cfg, ActionTableCompiler.machine, Machine.computer, Turing.FinTM2.step] using hr⟩)

def columnWord (bit : Bool) (x : Input s b arity) :=
  transferWord s b arity labels edges codec (RawBytecodeMachine.basisWord codec bit) x ++
    MatrixEmission.word codec [if bit then .erase 0 else .erase 1]

def columnComputes (bit : Bool) : Computes (encoding s b arity) Frame.wordEncoding
    (columnWord s b arity labels edges codec bit) :=
  joinComputes (transferComputes s b arity labels edges codec hd (RawBytecodeMachine.basisWord codec bit))
    (constantComputes (encoding s b arity) Frame.wordEncoding
      (MatrixEmission.word codec [if bit then .erase 0 else .erase 1]))

def value (x : Input s b arity) :=
  columnWord s b arity labels edges codec false x ++ columnWord s b arity labels edges codec true x ++
    MatrixEmission.word codec [.add]

def computes : Computes (encoding s b arity) Frame.wordEncoding (value s b arity labels edges codec) :=
  joinComputes (joinComputes (columnComputes s b arity labels edges codec hd false)
    (columnComputes s b arity labels edges codec hd true))
    (constantComputes (encoding s b arity) Frame.wordEncoding (MatrixEmission.word codec [.add]))

theorem computes_machine : (computes s b arity labels edges codec hd).machine =
    RawBytecodeMachine.cycleMachine s b arity labels edges codec := by
  simp only [computes, columnComputes, joinComputes, RunComposition.andThen_machine,
    pairComputes_machine, transferComputes, RunComposition.computes, prepareComputes, recode,
    RawBytecodeMachine.cycleMachine, RawBytecodeMachine.columnMachine,
    RawBytecodeMachine.join, WordJoin.computes, constantComputes, Frame.wordEncoding, id_eq]

include hd in
theorem value_original (x : Input s b arity) :
    ∃ c, cycleFrom x.val.1.val x.val.1.property (vertex s b arity labels x) (edge s b arity edges x)
        x.val.2 x.property.1 = some c ∧ value s b arity labels edges codec x = MatrixEmission.word codec c.code := by
  let r := x.val.1.val
  let h := x.val.1.property
  let p := first s b arity x
  have hg : ∀ v, degree (arity := arity) r v ≤ 2 := fun v => hd (r.signatureLabel h v)
  have hc := cycle_completion r h hg p x.property.1 x.property.2
  have ht := walk_trace r h (2*r.edges.length+1) [] p (walk_not_exhausted r h [] p)
  rw [hc.1] at ht
  obtain ⟨ms,hm⟩ := cycleMatrices_trace r h (vertex s b arity labels x) (edge s b arity edges x) ht
  obtain ⟨tail,hlist,_⟩ := cycle_cross_departures r h hg p x.property.1 x.property.2
  have hlen := cycleMatrices_length r h (vertex s b arity labels x) (edge s b arity edges x) _ ms hm
  have hne : ms ≠ [] := by intro he; rw [he,hlist] at hlen; simp at hlen
  obtain ⟨M,rest,rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨.cycle M rest,?_,?_⟩
  · change (match (walk r h (2*r.edges.length+1) [] p).2 with
      | .repeated q => if q = p then
          (cycleMatrices r h (vertex s b arity labels x) (edge s b arity edges x)
            (walk r h (2*r.edges.length+1) [] p).1).bind (fun ms =>
              match ms with | [] => none | M::tail => some (Component.cycle M tail))
        else none
      | _ => none) = _
    rw [hc.1]
    simp only [↓reduceIte, hm, Option.bind_some]
  · have hw : matrices s b arity labels edges x = some (M::rest) := hm
    simp only [value,columnWord,transferWord,hw,Option.map_some,Option.getD_some]
    simp [RawBytecodeMachine.basisWord,Component.code,cycleCode,columnCode,
      MatrixEmission.word,entries,List.flatMap_append,List.append_assoc]

theorem primitive_bound (x : Input s b arity) :
    let w := computes s b arity labels edges codec hd
    primitiveCost w.machine (w.outputs x).steps
      (some (Turing.initList w.machine.computer ((encoding s b arity).encode x))) ≤
        (primitivePolynomial w).eval ((encoding s b arity).encode x).length :=
  computes_primitive_cost (computes s b arity labels edges codec hd) x

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.CycleProvider
