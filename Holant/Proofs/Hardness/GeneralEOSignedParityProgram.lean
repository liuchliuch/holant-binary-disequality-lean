import Holant.Proofs.Hardness.GeneralEOSignedParityComponents
import Holant.Proofs.Hardness.BinaryCSPProgrammeScan
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootReach
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.FirstTrueGraph

/-! Physical parity double-cover preprocessing. Every original parity link emits
its two literal graph edges. Bounded reachability and the least-true-bit scan
compute component names; no component labels or certificates enter the tape. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedParityProgram
open Computability Holant Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
namespace S
export GeneralEOSignedParityComponents (Links vertex graph label scope signs Good)
end S
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists
  (mapComputes flatten lengthComputes succComputes getD)
end W
namespace B
export Holant.LocalDrafts.Tractability.ProductMachine.Bytecode (flatMap)
end B
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
abbrev unary := UnaryBinary.unaryEncoding
abbrev natLinkEncoding := pairEncoding (pairEncoding unary unary) encodingBoolBool
abbrev linkEncoding (n : ℕ) := pairEncoding
  (pairEncoding (OccurrenceLabel.unaryPortEncoding n) (OccurrenceLabel.unaryPortEncoding n)) encodingBoolBool
abbrev Input := Σ n : ℕ, S.Links n
abbrev inputEncoding := sigmaEncoding unary (fun n => framedListEncoding (linkEncoding n))
abbrev RootInput := Σ x : Input, Fin x.1 × Bool
abbrev rootEncoding := sigmaEncoding inputEncoding
  (fun x => pairEncoding (OccurrenceLabel.unaryPortEncoding x.1) encodingBoolBool)
abbrev rawInputEncoding := pairEncoding unary (framedListEncoding natLinkEncoding)
abbrev rawRootEncoding := pairEncoding rawInputEncoding (pairEncoding unary encodingBoolBool)

def fields (x : Input) : ℕ × List ((ℕ × ℕ) × Bool) :=
  (x.1,x.2.map fun q => ((q.1.1.val,q.1.2.val),q.2))
def rootFields (x : RootInput) : (ℕ × List ((ℕ × ℕ) × Bool)) × (ℕ × Bool) :=
  (fields x.1,(x.2.1.val,x.2.2))

theorem links_encode {n : ℕ} (xs : S.Links n) :
    (framedListEncoding natLinkEncoding).encode
      (xs.map fun q => ((q.1.1.val,q.1.2.val),q.2)) =
    (framedListEncoding (linkEncoding n)).encode xs := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    change true :: Algebraic.frame _ ++ _ = true :: Algebraic.frame _ ++ _
    change framedListEncode _ _ = framedListEncode _ _ at ih
    rw [ih]
    rfl

def fieldsComputes : Computes inputEncoding rawInputEncoding fields :=
  recode (identityComputes rawInputEncoding) fields
    (fun x => by simp only [rawInputEncoding,pairEncoding_encode,inputEncoding,sigmaEncoding,
      fields,links_encode]) (fun _ => rfl)

def rootFieldsComputes : Computes rootEncoding rawRootEncoding rootFields :=
  recode (pairComputes
    ((Wiring.firstComputes inputEncoding (pairEncoding unary encodingBoolBool)).andThen fieldsComputes)
    (Wiring.secondComputes inputEncoding (pairEncoding unary encodingBoolBool)))
    (fun x => (x.1,(x.2.1.val,x.2.2))) (fun _ => rfl) (fun _ => rfl)

/-- Unary doubling is a physical copy and append. -/
def twiceComputes : Computes unary unary (fun n => n*2) :=
  recode (joinComputes (encodeComputes unary) (encodeComputes unary)) id (fun _ => rfl)
    (fun n => by simp only [unary,UnaryBinary.unaryEncoding,Frame.wordEncoding,id_eq,Nat.mul_two,←List.replicate_add])

def bitComputes : Computes encodingBoolBool unary (fun b => if b then 1 else 0) :=
  FiniteRecode.computes encodingBoolBool unary (fun b => if b then 1 else 0) 1
    (fun b => by cases b <;> decide)

def vertexComputes : Computes (pairEncoding unary encodingBoolBool) unary
    (fun q => q.1*2 + if q.2 then 1 else 0) :=
  recode (joinComputes
    (((Wiring.firstComputes unary encodingBoolBool).andThen twiceComputes).andThen (encodeComputes unary))
    (((Wiring.secondComputes unary encodingBoolBool).andThen bitComputes).andThen (encodeComputes unary)))
    id (fun _ => rfl) (fun q => by simp only [unary,UnaryBinary.unaryEncoding,Frame.wordEncoding,id_eq,Function.comp_def,←List.replicate_add])

def negateComputes : Computes encodingBoolBool encodingBoolBool Bool.not :=
  FiniteRecode.computes encodingBoolBool encodingBoolBool Bool.not 1 (fun b => by cases b <;> decide)

def terminatedComputes : Computes unary Frame.wordEncoding ReachRound.unary :=
  congrComputes (joinComputes (encodeComputes unary)
    (constantComputes unary Frame.wordEncoding [false])) (fun _ => rfl)

def edgeBits (q : (ℕ × ℕ) × Bool) : List Bool :=
  ReachRound.unary (q.1.1*2) ++ ReachRound.unary (q.1.2*2 + if q.2 then 1 else 0) ++
    ReachRound.unary (q.1.1*2+1) ++ ReachRound.unary (q.1.2*2 + if !q.2 then 1 else 0)

def edgeBitsComputes : Computes natLinkEncoding Frame.wordEncoding edgeBits := by
  let ends := Wiring.firstComputes (pairEncoding unary unary) encodingBoolBool
  let left := ends.andThen (Wiring.firstComputes unary unary)
  let right := ends.andThen (Wiring.secondComputes unary unary)
  let sign := Wiring.secondComputes (pairEncoding unary unary) encodingBoolBool
  let a := (left.andThen twiceComputes).andThen terminatedComputes
  let b := ((pairComputes right sign).andThen vertexComputes).andThen terminatedComputes
  let c := ((left.andThen twiceComputes).andThen W.succComputes).andThen terminatedComputes
  let d := ((pairComputes right (sign.andThen negateComputes)).andThen vertexComputes).andThen terminatedComputes
  exact congrComputes (joinComputes (joinComputes (joinComputes a b) c) d) (fun _ => rfl)

def edgesComputes : Computes inputEncoding Frame.wordEncoding
    (fun x => OriginalCoefficient.NeighborScan.edgeBits (S.graph x.2).edges) := by
  let raw := (fieldsComputes.andThen (Wiring.secondComputes unary (framedListEncoding natLinkEncoding))).andThen
    (B.flatMap natLinkEncoding edgeBits edgeBitsComputes)
  refine congrComputes raw ?_
  intro x
  simp only [fields,List.flatMap_map,Function.comp_def]
  change _ = ((S.graph x.2).edges.map (fun e => (e.1.val,e.2.val))).flatMap _
  simp only [GeneralEOSignedParityComponents.graph,List.map_flatMap,List.flatMap_assoc]
  apply List.flatMap_congr
  intro q hq
  cases h : q.2 <;> simp [edgeBits,GeneralEOSignedParityComponents.vertex,finProdFinEquiv,
    List.append_assoc,Nat.mul_comm,Nat.add_comm]

def sizeComputes : Computes inputEncoding unary (fun x => x.1*2) :=
  (fieldsComputes.andThen (Wiring.firstComputes unary (framedListEncoding natLinkEncoding))).andThen twiceComputes

def prepared (x : RootInput) : OriginalCoefficient.RootReach.Input :=
  ⟨⟨x.1.1*2,S.vertex x.2.1 x.2.2⟩,(S.graph x.1.2).edges⟩

def prepareComputes : Computes rootEncoding OriginalCoefficient.RootReach.inputEncoding prepared := by
  let ctx := Wiring.firstComputes rawInputEncoding (pairEncoding unary encodingBoolBool)
  let n := (ctx.andThen (Wiring.firstComputes unary (framedListEncoding natLinkEncoding))).andThen twiceComputes
  let root := (Wiring.secondComputes rawInputEncoding (pairEncoding unary encodingBoolBool)).andThen vertexComputes
  let fields := rootFieldsComputes.andThen (pairComputes n root)
  let edges : Computes rootEncoding Frame.wordEncoding
      (fun x => OriginalCoefficient.NeighborScan.edgeBits (S.graph x.1.2).edges) :=
    recode ((Wiring.firstComputes inputEncoding (pairEncoding unary encodingBoolBool)).andThen edgesComputes)
      (fun x => (x.1,(x.2.1.val,x.2.2))) (fun _ => rfl) (fun _ => rfl)
  exact recode (pairComputes fields edges) id (fun _ => rfl)
    (fun x => by
      cases h : x.2.2 <;> simp [prepared,GeneralEOSignedParityComponents.vertex,
        OriginalCoefficient.RootReach.inputEncoding,OriginalCoefficient.RootBitmap.inputEncoding,
        OriginalCoefficient.NeighborScan.edgeEncoding,OccurrenceLabel.unaryPortEncoding,
        rootFields,GeneralEOSignedParityProgram.fields,finProdFinEquiv,h,Nat.mul_comm,Nat.add_comm,
        sigmaEncoding,UnaryBinary.unaryEncoding,Frame.wordEncoding])

def reached (x : RootInput) : OriginalCoefficient.FirstTrue.Input :=
  OriginalCoefficient.FirstTrue.graphInput (S.graph x.1.2) (S.vertex x.2.1 x.2.2)

def reachComputes : Computes rootEncoding OriginalCoefficient.FirstTrue.inputEncoding reached :=
  recode (prepareComputes.andThen OriginalCoefficient.RootReach.computes) id
    (fun _ => rfl) (fun _ => rfl)

/-- Actual double-cover graph traversal followed by the physical first-bit scan. -/
def labelComputes : Computes rootEncoding unary
    (fun x => (S.label x.1.2 x.2.1 x.2.2).val) :=
  congrComputes (reachComputes.andThen OriginalCoefficient.FirstTrue.computes)
    (fun x => OriginalCoefficient.FirstTrue.graph_value (S.graph x.1.2) (S.vertex x.2.1 x.2.2))


/-- The dependent finite range uses the actual range writer and carries no
runtime bound certificate. The bound is a theorem about the emitted bytes. -/
theorem finList_encode {n : ℕ} (xs : List (Fin n)) :
    (framedListEncoding (OccurrenceLabel.unaryPortEncoding n)).encode xs =
      (framedListEncoding unary).encode (xs.map Fin.val) := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
    change true :: Algebraic.frame _ ++ _ = true :: Algebraic.frame _ ++ _
    change framedListEncode _ _ = framedListEncode _ _ at ih
    rw [ih]
    rfl

theorem finRange_encode (n : ℕ) :
    (framedListEncoding (OccurrenceLabel.unaryPortEncoding n)).encode (List.finRange n) =
      (framedListEncoding unary).encode (List.range n) := by
  rw [finList_encode]
  congr 1
  apply List.ext_getElem <;> simp

def tabulate {A C : Type} (ea : Encoding A Bool) (ec : Encoding C Bool)
    (size : A → ℕ) (count : Computes ea unary size)
    (f : (a : A) → Fin (size a) → C)
    (cell : Computes (sigmaEncoding ea (fun a => OccurrenceLabel.unaryPortEncoding (size a))) ec
      (fun x => f x.1 x.2)) :
    Computes ea (framedListEncoding ec) (fun a => (List.finRange (size a)).map (f a)) := by
  let eb := fun a => OccurrenceLabel.unaryPortEncoding (size a)
  let prepare : Computes ea (OriginalCoefficient.ContextFlatMap.inputEncoding ea eb)
      (fun a => ⟨a,List.finRange (size a)⟩) :=
    recode (pairComputes (identityComputes ea) (count.andThen ComponentSelection.UnaryRange.computes))
      id (fun _ => rfl) (fun a => by
        simp only [OriginalCoefficient.ContextFlatMap.inputEncoding,sigmaEncoding,pairEncoding_encode,
          eb,finRange_encode,Function.comp_def,id_eq])
  let worker := cell.andThen (entryComputes ec)
  let run := prepare.andThen (OriginalCoefficient.ContextFlatMap.computes ea eb
    (fun x => entry ec (f x.1 x.2)) worker)
  refine recode (joinComputes run (constantComputes ea Frame.wordEncoding [false]))
    id (fun _ => rfl) ?_
  intro a
  have h := entries_append_encode ec ((List.finRange (size a)).map (f a)) []
  simpa only [OriginalCoefficient.ContextFlatMap.value,entries,List.flatMap_map,
    Function.comp_def,List.append_nil,framedListEncode,Frame.wordEncoding,framedListEncoding,id_eq] using h

abbrev IndexInput := Σ x : Input, Fin x.1
abbrev indexEncoding := sigmaEncoding inputEncoding (fun x => OccurrenceLabel.unaryPortEncoding x.1)

def atBit (b : Bool) : Computes indexEncoding rootEncoding (fun x => (⟨x.1,x.2,b⟩ : RootInput)) :=
  recode (pairComputes (Wiring.firstComputes inputEncoding unary)
    (pairComputes (Wiring.secondComputes inputEncoding unary)
      (constantComputes (pairEncoding inputEncoding unary) encodingBoolBool b)))
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

def labelAtComputes (b : Bool) : Computes indexEncoding unary
    (fun x => (S.label x.1.2 x.2 b).val) := (atBit b).andThen labelComputes

def signsComputes : Computes indexEncoding encodingBoolBool
    (fun x => S.signs x.1.2 x.2) :=
  (pairComputes ((labelAtComputes true).andThen UnaryBinary.computes)
    ((labelAtComputes false).andThen UnaryBinary.computes)).andThen Endpoints.lessComputes

def scopeComputes : Computes indexEncoding unary
    (fun x => (S.scope x.1.2 x.2).val) :=
  congrComputes (ifComputes signsComputes (labelAtComputes true) (labelAtComputes false))
    (fun x => by
      simp only [GeneralEOSignedParityComponents.signs,GeneralEOSignedParityComponents.scope]
      by_cases h : S.label x.1.2 x.2 true < S.label x.1.2 x.2 false
      · simp [h,min_eq_right (le_of_lt h)]
      · simp [h,min_eq_left (le_of_not_gt h)])

def countComputes : Computes inputEncoding unary Sigma.fst :=
  fieldsComputes.andThen (Wiring.firstComputes unary (framedListEncoding natLinkEncoding))

def scopes (x : Input) : List ℕ := (List.finRange x.1).map (fun i => (S.scope x.2 i).val)
def signs (x : Input) : List Bool := (List.finRange x.1).map (S.signs x.2)

def scopesComputes : Computes inputEncoding (framedListEncoding unary) scopes :=
  tabulate inputEncoding unary Sigma.fst countComputes (fun x i => (S.scope x.2 i).val) scopeComputes

def signListComputes : Computes inputEncoding (framedListEncoding encodingBoolBool) signs :=
  tabulate inputEncoding encodingBoolBool Sigma.fst countComputes (fun x i => S.signs x.2 i) signsComputes

def badComputes : Computes indexEncoding encodingBoolBool
    (fun x => decide (S.label x.1.2 x.2 false = S.label x.1.2 x.2 true)) :=
  congrComputes ((pairComputes ((labelAtComputes false).andThen UnaryBinary.computes)
    ((labelAtComputes true).andThen UnaryBinary.computes)).andThen Endpoints.equalComputes)
    (fun x => by simp only [Fin.ext_iff,Function.comp_def,id_eq])

def badFlags (x : Input) : List Bool :=
  (List.finRange x.1).map (fun i => decide (S.label x.2 i false = S.label x.2 i true))

def badFlagsComputes : Computes inputEncoding (framedListEncoding encodingBoolBool) badFlags :=
  tabulate inputEncoding encodingBoolBool Sigma.fst countComputes
    (fun x i => decide (S.label x.2 i false = S.label x.2 i true)) badComputes

def andFoldComputes : Computes (framedListEncoding encodingBoolBool) encodingBoolBool
    (fun xs => xs.foldl Bool.and true) :=
  Holant.LocalDrafts.Tractability.AffineMachine.FiniteFold.computes
    encodingBoolBool encodingBoolBool 1 Bool.and true (fun b => by cases b <;> rfl)

def noBadComputes : Computes (framedListEncoding encodingBoolBool) encodingBoolBool
    (fun xs => (xs.map Bool.not).foldl Bool.and true) :=
  (W.mapComputes encodingBoolBool encodingBoolBool Bool.not negateComputes).andThen andFoldComputes

theorem fold_and (xs : List Bool) (b : Bool) : xs.foldl Bool.and b = (b && xs.all id) := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons,ih]; cases b <;> cases x <;> simp

local instance goodDecidable (x : Input) : Decidable (S.Good x.2) := by
  unfold GeneralEOSignedParityComponents.Good
  infer_instance

def goodComputes : Computes inputEncoding encodingBoolBool (fun x => decide (S.Good x.2)) :=
  congrComputes (badFlagsComputes.andThen noBadComputes) (fun x => by
    dsimp only [Function.comp_def]
    rw [fold_and]
    apply Bool.eq_iff_iff.mpr
    simp [badFlags,GeneralEOSignedParityComponents.Good])

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedParityProgram
