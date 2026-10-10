import Holant.Proofs.Recognition.RuntimeKTable
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeTensorBasisSemantics

/-! Runtime prescribed-K inverse polynomial table compiler. Literal I and
sqrt(2) addresses are bound by the original-root assembler; no free matrix
coordinates are consumed. This permits literal A/P template rows to reserve
their existing matrix coordinates independently. The input address table is a
syntax primitive; an end-to-end original-family assembler remains separate. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis (Layout layoutEncoding)
open RationalTensorMachine (Word Row wordEncoding rowEncoding tableEncoding)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev EntryInput := Layout × (Bool × Bool)
abbrev bitPairEncoding := pairEncoding encodingBoolBool encodingBoolBool
abbrev entryEncoding := pairEncoding layoutEncoding bitPairEncoding
abbrev Input := Layout × (Word × List Row)
abbrev RowInput := Layout × (Word × Row)
abbrev tailEncoding := pairEncoding wordEncoding tableEncoding
abbrev encoding := pairEncoding layoutEncoding tailEncoding
abbrev rowTailEncoding := pairEncoding wordEncoding rowEncoding
abbrev rowInputEncoding := pairEncoding layoutEncoding rowTailEncoding

def entry (r : EntryInput) : RationalSparseMachine.Poly := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.entry ((false,false),r.1) r.2.2 r.2.1
def factors (r : RowInput) : List RationalSparseMachine.Poly := (List.range r.2.1.length).map
  (fun j => entry (r.1,r.2.1.getD j false,r.2.2.1.getD j false))
def row (r : RowInput) : RationalSparseMachine.Poly := RationalSparseMachine.mul
  (RationalSparseMachine.product r.1.1 (factors r)) (RationalSparseMachine.variable r.1.1 r.2.2.2)
def vertex (r : Input) : RationalSparseMachine.Poly := r.2.2.flatMap (fun t => row (r.1,r.2.1,t))

def entryExecutes : Executes entryEncoding RationalSparseMachine.encoding entry := by
  let l := RuntimeTensorRows.fst layoutEncoding bitPairEncoding
  let ab := RuntimeTensorRows.snd layoutEncoding bitPairEncoding
  let a := ab.comp (RuntimeTensorRows.fst encodingBoolBool encodingBoolBool)
  let b := ab.comp (RuntimeTensorRows.snd encodingBoolBool encodingBoolBool)
  let base := (RuntimeTensorRows.const entryEncoding bitPairEncoding (false,false)).pair l
  let cell (x y : Bool) := base.comp (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.entryExecutes y x)
  let raw := RuntimeTensorRows.choose entryEncoding RationalSparseMachine.encoding a
    (RuntimeTensorRows.choose entryEncoding RationalSparseMachine.encoding b (cell true true) (cell true false))
    (RuntimeTensorRows.choose entryEncoding RationalSparseMachine.encoding b (cell false true) (cell false false))
  exact raw.congr (by rintro ⟨l,a,b⟩; cases a <;> cases b <;> rfl)

def layout := Wiring.firstComputes layoutEncoding rowTailEncoding
def width := layout.andThen (Wiring.firstComputes encodingNatBool (pairEncoding encodingNatBool encodingNatBool))
def tail := Wiring.secondComputes layoutEncoding rowTailEncoding
def outputWord := tail.andThen (Wiring.firstComputes wordEncoding rowEncoding)
def tableRow := tail.andThen (Wiring.secondComputes wordEncoding rowEncoding)
def sourceWord := tableRow.andThen (Wiring.firstComputes wordEncoding encodingNatBool)
def address := tableRow.andThen (Wiring.secondComputes wordEncoding encodingNatBool)

def factorExecutes : Executes (pairEncoding rowInputEncoding encodingNatBool) RationalSparseMachine.encoding
    (fun p => entry (p.1.1,p.1.2.1.getD p.2 false,p.1.2.2.1.getD p.2 false)) := by
  let r := Wiring.firstComputes rowInputEncoding encodingNatBool
  let j := Wiring.secondComputes rowInputEncoding encodingNatBool
  let x := (Executes.ofComputes (pairComputes (r.andThen outputWord) j)).comp
    (NegativeCertificateMachine.Lists.lookup encodingBoolBool false)
  let y := (Executes.ofComputes (pairComputes (r.andThen sourceWord) j)).comp
    (NegativeCertificateMachine.Lists.lookup encodingBoolBool false)
  exact ((Executes.ofComputes (r.andThen layout)).pair (x.pair y)).comp entryExecutes

def factorsExecutes : Executes rowInputEncoding RationalSparseMachine.familyEncoding factors := by
  let count := (outputWord.andThen (WireLists.lengthComputes encodingBoolBool)).andThen UnaryBinary.computes
  exact NegativeCertificateMachine.Lists.map rowInputEncoding encodingNatBool RationalSparseMachine.encoding
    ((Executes.ofComputes count).comp RationalInputMachine.Programs.range)
    (fun r j => entry (r.1,r.2.1.getD j false,r.2.2.1.getD j false)) factorExecutes

def rowExecutes : Executes rowInputEncoding RationalSparseMachine.encoding row := by
  let tensor := ((Executes.ofComputes width).pair factorsExecutes).comp RationalSparseMachine.productExecutes
  let coefficient := (Executes.ofComputes (pairComputes width address)).comp RationalSparseMachine.variableExecutes
  exact (tensor.pair coefficient).comp RationalSparseMachine.mulExecutes

def executes : Executes encoding RationalSparseMachine.encoding vertex := by
  let l := Wiring.firstComputes layoutEncoding tailEncoding
  let rest := Wiring.secondComputes layoutEncoding tailEncoding
  let x := rest.andThen (Wiring.firstComputes wordEncoding tableEncoding)
  let ts := rest.andThen (Wiring.secondComputes wordEncoding tableEncoding)
  let ctx := Wiring.firstComputes encoding rowEncoding
  let t := Wiring.secondComputes encoding rowEncoding
  let prep := pairComputes (ctx.andThen l) (pairComputes (ctx.andThen x) t)
  let cell := (Executes.ofComputes prep).comp rowExecutes
  let rows := NegativeCertificateMachine.Lists.map encoding rowEncoding RationalSparseMachine.encoding
    (Executes.ofComputes ts) (fun r t => row (r.1,r.2.1,t)) cell
  exact (rows.comp (Executes.ofComputes (WireLists.flatten RationalSparseMachine.termEncoding))).congr
    (fun r => by simp only [vertex,List.flatMap_def,Function.comp_apply])

def typedEntry {v : ℕ} (imaginary sqrt : Fin v) (a b : Bool) : Sparse.Poly v 1 :=
  _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.typedEntry false false imaginary sqrt b a
def wireRow {n v : ℕ} (t : (Fin n → Bool) × Fin v) : Row := (List.ofFn t.1,t.2.val)
def typedRow {n v : ℕ} (imaginary sqrt : Fin v) (x : Fin n → Bool)
    (t : (Fin n → Bool) × Fin v) : Sparse.Poly v 1 :=
  Sparse.mul RationalCompiler.data (SparseTransform.product RationalCompiler.data
    (List.ofFn (fun j => typedEntry imaginary sqrt (x j) (t.1 j))))
    (SparseTransform.variableCode RationalCompiler.data t.2)
def typedVertex {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (x : Fin n → Bool) : Sparse.Poly v 1 :=
  SymbolicInputTable.vertex RationalCompiler.data (typedEntry imaginary sqrt)
    (fun y => SparseTransform.variableCode RationalCompiler.data (address y)) x

theorem entry_wire {v : ℕ} (imaginary sqrt : Fin v) (a b : Bool) :
    entry ((v,imaginary.val,sqrt.val),a,b)=RationalInputMachine.rowWire (typedEntry imaginary sqrt a b) :=
  _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis.entry_wire false false imaginary sqrt b a

theorem factors_wire {n v : ℕ} (imaginary sqrt : Fin v) (x y : Fin n → Bool) (j : Fin v) :
    factors ((v,imaginary.val,sqrt.val),List.ofFn x,wireRow (y,j))=
      (List.ofFn (fun k => typedEntry imaginary sqrt (x k) (y k))).map RationalInputMachine.rowWire := by
  unfold factors wireRow
  simp only [List.length_ofFn,List.map_ofFn]
  rw [RuntimeTensorRowsSoundness.map_range_eq_ofFn]
  simp only [PositiveCertificateMachine.getD_ofFn,entry_wire,Function.comp_def]

theorem row_wire {n v : ℕ} (imaginary sqrt : Fin v) (x : Fin n → Bool)
    (t : (Fin n → Bool) × Fin v) :
    row ((v,imaginary.val,sqrt.val),List.ofFn x,wireRow t)=
      RationalInputMachine.rowWire (typedRow imaginary sqrt x t) := by
  unfold row
  rw [factors_wire,RationalSparseMachine.product_wire]
  change RationalSparseMachine.mul _ (RationalSparseMachine.variable v t.2.val)=_
  rw [RationalSparseMachine.variable_wire,RationalSparseMachine.mul_wire]
  rfl

theorem vertex_wire {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (x : Fin n → Bool) :
    vertex ((v,imaginary.val,sqrt.val),List.ofFn x,
      (SparseTransform.allWords n).map (fun y => wireRow (y,address y)))=
      RationalInputMachine.rowWire (typedVertex imaginary sqrt address x) := by
  simp only [vertex,List.flatMap_map,Function.comp_def,row_wire,typedVertex,SymbolicInputTable.vertex,
    typedRow,SparseTransform.total,RationalInputMachine.rowWire,List.map_flatten,List.map_map,List.flatMap_def]

theorem entry_eval {v : ℕ} (imaginary sqrt : Fin v) (z : Fin v → AlgebraicComplex)
    (hi : z imaginary=imaginaryUnit) (hs : z sqrt=sqrtTwo) (a b : Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ AlgebraicComplex) z
      (typedEntry imaginary sqrt a b)=Signature.equality a b := by
  rw [typedEntry,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.typedEntry_eval (algebraMap ℚ AlgebraicComplex) z false false imaginary sqrt b a]
  cases a <;> cases b <;> simp [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.entryValue,Signature.equality]

theorem vertex_eval {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (f : Signature AlgebraicComplex n) (z : Fin v → AlgebraicComplex)
    (hi : z imaginary=imaginaryUnit) (hs : z sqrt=sqrtTwo) (hf : ∀y,z (address y)=f y)
    (x : Fin n → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ AlgebraicComplex) z
      (typedVertex imaginary sqrt address x)=f x := by
  unfold typedVertex
  rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.compilerData,SymbolicInputTable.variable_vertex_eval _ _ _ _ _ _ hf]
  simp only [entry_eval imaginary sqrt z hi hs]
  exact congrFun (Signature.coordinateAction_equality f) x


theorem flipped_transpose_inverse (a b : Bool) :
    (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.basis false false).matrix b a=Signature.equality a b := by
  rw [←_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.entryValue_basis]
  cases a <;> cases b <;> simp [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.entryValue,Signature.equality]

theorem entry_eval_map {E : Type*} [Field E] [Algebra ℚ E] (ψ : AlgebraicComplex →+* E)
    {v : ℕ} (imaginary sqrt : Fin v) (z : Fin v → E)
    (hi : z imaginary=ψ imaginaryUnit) (hs : z sqrt=ψ sqrtTwo) (a b : Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ E) z
      (typedEntry imaginary sqrt a b)=ψ (Signature.equality a b) := by
  rw [typedEntry,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.typedEntry_basis_map ψ z false false imaginary sqrt hi hs,
    flipped_transpose_inverse]

theorem vertex_eval_map {E : Type*} [Field E] [Algebra ℚ E] (ψ : AlgebraicComplex →+* E)
    {n v : ℕ} (imaginary sqrt : Fin v) (address : (Fin n → Bool) → Fin v)
    (f : Signature AlgebraicComplex n) (z : Fin v → E)
    (hi : z imaginary=ψ imaginaryUnit) (hs : z sqrt=ψ sqrtTwo) (hf : ∀y,z (address y)=ψ (f y))
    (x : Fin n → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ E) z
      (typedVertex imaginary sqrt address x)=ψ (f x) := by
  unfold typedVertex
  rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.compilerData,SymbolicInputTable.variable_vertex_eval _ _ _ _ _ _ hf]
  simp only [entry_eval_map ψ imaginary sqrt z hi hs]
  simpa [Signature.coordinateAction,Signature.equality] using
    congrFun (Signature.coordinateAction_equality (fun y=>ψ (f y))) x

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeKTable
