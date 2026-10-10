import Holant.Proofs.Hardness.GeneralEOSinglePinAmplificationValidation
import Holant.Proofs.Hardness.PairedPinsCompiler

/-! Actual finite Boolean-stack compiler for the anchored DEQ4 graph.
The original pin count drives tabulation and every endpoint is read or emitted
by existing finite list and integer machines. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationCompiler
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open GeneralEOSinglePinAmplificationRaw
namespace P
export PairedPinsCompiler
  (rowEncoding endpointEncoding rowsEncoding portsEncoding edgesEncoding rawEncoding cellEncoding
   rowsComputes edgesComputes portsComputes singletonRow pinTest oldRowsComputes contextComputes indexComputes)
end P
set_option backward.isDefEq.respectTransparency false
private theorem filter_rows {A : Type} (p : A → Bool) (xs : List A) :
    xs.flatMap (fun x=>if p x then [x] else [])=xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h,ih]

def keepPin (s : ℕ) : Computes P.rowEncoding P.rowsEncoding (fun r=>if r.1=s then [r] else []) :=
  congrComputes (ifComputes (P.pinTest s false) P.singletonRow
    (constantComputes P.rowEncoding P.rowsEncoding [])) (fun r=>by simp)

def pinRowsComputes (s : ℕ) : Computes P.rawEncoding P.rowsEncoding (pinRows s) :=
  congrComputes (P.rowsComputes.andThen
    (AccessPrograms.flatMap P.rowEncoding P.rowEncoding _ (keepPin s)))
    (fun r=>by simpa [pinRows,Bool.beq_eq_decide_eq] using
      filter_rows (fun v : RawVertex=>decide (v.1=s)) r.vertices)

def countComputes (s : ℕ) : Computes P.rawEncoding UnaryBinary.unaryEncoding (count s) :=
  (pinRowsComputes s).andThen (WireLists.lengthComputes P.rowEncoding)

def oldEdgeCount : Computes P.rawEncoding UnaryBinary.unaryEncoding (fun r=>r.edges.length) :=
  P.edgesComputes.andThen (WireLists.lengthComputes encodingNatBool)

def selectedRow (s : ℕ) : Computes P.cellEncoding P.rowEncoding
    (fun x=>(pinRows s x.1).getD x.2 (0,[])) :=
  AccessPrograms.get P.rowEncoding (0,[]) (P.contextComputes.andThen (pinRowsComputes s)) P.indexComputes

def oldEndpoint (s k : ℕ) : Computes P.cellEncoding P.endpointEncoding
    (fun x=>((pinRows s x.1).getD x.2 (0,[])).2.getD k (0,false)) :=
  AccessPrograms.get P.endpointEncoding (0,false) ((selectedRow s).andThen P.portsComputes)
    (constantComputes P.cellEncoding UnaryBinary.unaryEncoding k)


def refIndex (back : Bool) : Computes P.cellEncoding UnaryBinary.unaryEncoding
    (fun x => if back then x.2 else x.2+1) := by
  cases back
  · exact P.indexComputes.andThen WireLists.succComputes
  · exact P.indexComputes

def freshEndpoint (back : Bool) : Computes P.cellEncoding P.endpointEncoding
    (fun x => (x.1.edges.length+(if back then x.2 else x.2+1),back)) :=
  recode (pairComputes
    (((pairComputes (P.contextComputes.andThen oldEdgeCount) (refIndex back)).andThen
      AccessPrograms.unaryAdd).andThen UnaryBinary.computes)
    (constantComputes P.cellEncoding encodingBoolBool back)) id (fun _ => rfl) (fun _ => rfl)

def portCell (s : ℕ) (x : RawClosedNetwork×ℕ) : Fin 4 → RawEndpoint :=
  ![((pinRows s x.1).getD x.2 (0,[])).2.getD 0 (0,false),
    ((pinRows s x.1).getD x.2 (0,[])).2.getD 1 (0,false),
    (x.1.edges.length+x.2,true),(x.1.edges.length+(x.2+1),false)]

def portCellComputes (s : ℕ) (k : Fin 4) :
    Computes P.cellEncoding P.endpointEncoding (fun x => portCell s x k) :=
  Fin.cases (oldEndpoint s 0) (Fin.cases (oldEndpoint s 1)
    (Fin.cases (freshEndpoint true) (Fin.cases (freshEndpoint false) (fun i => Fin.elim0 i)))) k

def portsComputes (s j : ℕ) : Computes P.cellEncoding P.portsEncoding (fun x => (row s j x.1 x.2).2) :=
  congrComputes (fixedListComputes P.cellEncoding P.endpointEncoding (portCell s)
    (portCellComputes s) [0,1,2,3]) (fun x => by simp [row,reference_succ,portCell,Nat.add_assoc])

def rowComputes (s j : ℕ) : Computes P.cellEncoding P.rowEncoding (fun x => row s j x.1 x.2) :=
  recode (pairComputes (constantComputes P.cellEncoding encodingNatBool j) (portsComputes s j))
    id (fun _ => rfl) (fun _ => rfl)

def rowsComputes (s j : ℕ) : Computes P.rawEncoding P.rowsEncoding (rows s j) :=
  WireLists.tabulate P.rawEncoding P.rowEncoding (count s) (countComputes s) (row s j) (rowComputes s j)

def anchorEndpoint (s : ℕ) (back : Bool) : Computes P.rawEncoding P.endpointEncoding
    (fun r => if back then (r.edges.length+count s r,true) else (r.edges.length,false)) := by
  cases back
  · exact recode (pairComputes (oldEdgeCount.andThen UnaryBinary.computes)
      (constantComputes P.rawEncoding encodingBoolBool false)) id (fun _ => rfl) (fun _ => rfl)
  · exact recode (pairComputes
      (((pairComputes oldEdgeCount (countComputes s)).andThen AccessPrograms.unaryAdd).andThen UnaryBinary.computes)
      (constantComputes P.rawEncoding encodingBoolBool true)) id (fun _ => rfl) (fun _ => rfl)

def anchorPortsComputes (s : ℕ) : Computes P.rawEncoding P.portsEncoding (fun r => reference s r 0) :=
  congrComputes (fixedListComputes P.rawEncoding P.endpointEncoding
      (fun (r : RawClosedNetwork) (b : Bool) => if b then (r.edges.length+count s r,true) else (r.edges.length,false))
      (anchorEndpoint s) [true,false]) (fun r => (reference_zero s r).symm)

def anchorComputes (s : ℕ) : Computes P.rawEncoding P.rowEncoding (anchor s) :=
  recode (pairComputes (constantComputes P.rawEncoding encodingNatBool s) (anchorPortsComputes s))
    id (fun _ => rfl) (fun _ => rfl)

def verticesComputes (s j : ℕ) : Computes P.rawEncoding P.rowsEncoding (fun r => (raw s j r).vertices) := by
  let head := (anchorComputes s).andThen P.singletonRow
  let tail := (pairComputes head (rowsComputes s j)).andThen (WireLists.append P.rowEncoding)
  exact (pairComputes (P.oldRowsComputes s) tail).andThen (WireLists.append P.rowEncoding)

def freshEdgesComputes (s : ℕ) : Computes P.rawEncoding P.edgesEncoding
    (fun r => List.replicate (count s r+1) 0) :=
  ((countComputes s).andThen WireLists.succComputes).andThen (WireLists.replicate encodingNatBool 0)

def edgesComputes (s j : ℕ) : Computes P.rawEncoding P.edgesEncoding (fun r => (raw s j r).edges) :=
  (pairComputes P.edgesComputes (freshEdgesComputes s)).andThen (WireLists.append encodingNatBool)

def computes (s j : ℕ) : Computes P.rawEncoding P.rawEncoding (raw s j) :=
  recode (pairComputes (verticesComputes s j) (edgesComputes s j)) id (fun _ => rfl) (fun _ => rfl)

variable {s j : ℕ} {a : ℕ → ℕ}
abbrev Input := ExactSignatureTables.Input (s+1) 1 (UniversalPairReduction.extendedArity s a)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (UniversalPairReduction.extendedArity s a)

def query (hj : j<s) (ha : a j=4) (r : Input (s:=s) (a:=a)) : UniversalPairReduction.Input s a :=
  ⟨raw s j r.val,GeneralEOSinglePinAmplificationValidation.wellFormed r.property hj ha,
    by rw [GeneralEOSinglePinAmplificationValidation.pin_count _ hj]⟩

def queryComputes (hj : j<s) (ha : a j=4) : Computes (inputEncoding (s:=s) (a:=a))
    (UniversalPairReduction.inputEncoding s a) (query hj ha) :=
  recode (computes s j) Subtype.val (fun _ => rfl) (fun _ => rfl)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationCompiler
