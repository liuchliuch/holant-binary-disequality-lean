import Holant.Proofs.Hardness.ExactTwoReferenceValidation
import Holant.Proofs.Hardness.PairedPinsCompiler

/-! Physical single-cycle reference compiler.
Original records are scanned by the existing finite filter programs. Actual
pin count drives tabulation; ordered original ports use physical getD lookup;
reference indices use a tested zero branch, unary predecessor and addition.
All fresh labels are materialized by physical replication. No raw graph map,
list callback, count certificate or output bound is a new machine primitive. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceCompiler
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open ExactTwoReferenceRaw
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

def keepPin : Computes P.rowEncoding P.rowsEncoding (fun r=>if r.1=1 then [r] else []) :=
  congrComputes (ifComputes (P.pinTest 1 false) P.singletonRow
    (constantComputes P.rowEncoding P.rowsEncoding [])) (fun r=>by simp)

def pinRowsComputes : Computes P.rawEncoding P.rowsEncoding pinRows :=
  congrComputes (P.rowsComputes.andThen
    (AccessPrograms.flatMap P.rowEncoding P.rowEncoding _ keepPin))
    (fun r=>by simpa [pinRows,Bool.beq_eq_decide_eq] using
      filter_rows (fun v : RawVertex=>decide (v.1=1)) r.vertices)

def countComputes : Computes P.rawEncoding UnaryBinary.unaryEncoding count :=
  pinRowsComputes.andThen (WireLists.lengthComputes P.rowEncoding)

def oldEdgeCount : Computes P.rawEncoding UnaryBinary.unaryEncoding (fun r=>r.edges.length) :=
  P.edgesComputes.andThen (WireLists.lengthComputes encodingNatBool)

def selectedRow : Computes P.cellEncoding P.rowEncoding
    (fun x=>(pinRows x.1).getD x.2 (0,[])) :=
  AccessPrograms.get P.rowEncoding (0,[]) (P.contextComputes.andThen pinRowsComputes) P.indexComputes

def oldEndpoint (k : ℕ) : Computes P.cellEncoding P.endpointEncoding
    (fun x=>((pinRows x.1).getD x.2 (0,[])).2.getD k (0,false)) :=
  AccessPrograms.get P.endpointEncoding (0,false) (selectedRow.andThen P.portsComputes)
    (constantComputes P.cellEncoding UnaryBinary.unaryEncoding k)

def indexZero : Computes P.cellEncoding encodingBoolBool (fun x=>decide (x.2=0)) :=
  (pairComputes P.indexComputes (constantComputes P.cellEncoding UnaryBinary.unaryEncoding 0)).andThen
    (equalComputes UnaryBinary.unaryEncoding)

/-- Both branches execute a real unary pop; m=1/i=0 produces predecessor0. -/
def previousComputes : Computes P.cellEncoding UnaryBinary.unaryEncoding
    (fun x=>previous (count x.1) x.2) :=
  congrComputes ((ifComputes indexZero (P.contextComputes.andThen countComputes) P.indexComputes).andThen
    Endpoints.unaryPredecessorComputes)
    (fun x=>by by_cases h : x.2=0 <;> simp [previous,h])

def refIndex (back : Bool) : Computes P.cellEncoding UnaryBinary.unaryEncoding
    (fun x=>if back then previous (count x.1) x.2 else x.2) := by
  cases back
  · exact P.indexComputes
  · exact previousComputes

def freshEndpoint (back : Bool) : Computes P.cellEncoding P.endpointEncoding
    (fun x=>(x.1.edges.length+(if back then previous (count x.1) x.2 else x.2),back)) :=
  recode (pairComputes
    (((pairComputes (P.contextComputes.andThen oldEdgeCount) (refIndex back)).andThen
      AccessPrograms.unaryAdd).andThen UnaryBinary.computes)
    (constantComputes P.cellEncoding encodingBoolBool back)) id (fun _=>rfl) (fun _=>rfl)

def portCell (x : RawClosedNetwork×ℕ) : Fin 4 → RawEndpoint :=
  ![((pinRows x.1).getD x.2 (0,[])).2.getD 0 (0,false),
    ((pinRows x.1).getD x.2 (0,[])).2.getD 1 (0,false),
    (x.1.edges.length+previous (count x.1) x.2,true),
    (x.1.edges.length+x.2,false)]

def portCellComputes (j : Fin 4) : Computes P.cellEncoding P.endpointEncoding (fun x=>portCell x j) := by
  exact Fin.cases (oldEndpoint 0) (Fin.cases (oldEndpoint 1)
    (Fin.cases (freshEndpoint true) (Fin.cases (freshEndpoint false) (fun i=>Fin.elim0 i)))) j

def portsComputes : Computes P.cellEncoding P.portsEncoding (fun x=>(row x.1 x.2).2) :=
  fixedListComputes P.cellEncoding P.endpointEncoding portCell portCellComputes [0,1,2,3]

def rowComputes : Computes P.cellEncoding P.rowEncoding (fun x=>row x.1 x.2) :=
  recode (pairComputes (constantComputes P.cellEncoding encodingNatBool 1) portsComputes)
    id (fun _=>rfl) (fun _=>rfl)

def rowsComputes : Computes P.rawEncoding P.rowsEncoding rows :=
  WireLists.tabulate P.rawEncoding P.rowEncoding count countComputes row rowComputes

def verticesComputes : Computes P.rawEncoding P.rowsEncoding (fun r=>(raw r).vertices) :=
  (pairComputes (P.oldRowsComputes 1) rowsComputes).andThen (WireLists.append P.rowEncoding)

def freshEdgesComputes : Computes P.rawEncoding P.edgesEncoding (fun r=>List.replicate (count r) 0) :=
  countComputes.andThen (WireLists.replicate encodingNatBool 0)

def edgesComputes : Computes P.rawEncoding P.edgesEncoding (fun r=>(raw r).edges) :=
  (pairComputes P.edgesComputes freshEdgesComputes).andThen (WireLists.append encodingNatBool)

/-- Total finite Boolean-stack programme on the original raw serialization. -/
def computes : Computes P.rawEncoding P.rawEncoding raw :=
  recode (pairComputes verticesComputes edgesComputes) id (fun _=>rfl) (fun _=>rfl)

abbrev Input := {r : RawClosedNetwork // r.WellFormed 2 1 sourceArity}
abbrev TargetInput := {r : RawClosedNetwork // r.WellFormed 2 1 targetArity}
abbrev sourceEncoding := RawClosedNetwork.validatedEncoding 2 1 sourceArity
abbrev targetEncoding := RawClosedNetwork.validatedEncoding 2 1 targetArity

def query (r : Input) : TargetInput := ⟨raw r.val,ExactTwoReferenceValidation.wellFormed r.property⟩

def queryComputes : Computes sourceEncoding targetEncoding query :=
  recode computes Subtype.val (fun _=>rfl) (fun _=>rfl)

def inputCountComputes : Computes sourceEncoding UnaryBinary.unaryEncoding (fun r=>count r.val) :=
  recode countComputes Subtype.val (fun _=>rfl) (fun _=>rfl)

attribute [local irreducible] computes queryComputes

def outputs (r : RawClosedNetwork) : TM2OutputsInTime computes.machine.computer (P.rawEncoding.encode r)
    (some (P.rawEncoding.encode (raw r))) (computes.time.eval (P.rawEncoding.encode r).length) :=
  computes.outputs r

theorem output_parses (r : Input) : targetEncoding.decode (P.rawEncoding.encode (raw r.val))=some (query r) :=
  targetEncoding.decode_encode (query r)

theorem zero_query (r : Input) (hm : count r.val=0) : (query r).val=r.val :=
  ExactTwoReferenceValidation.zero_raw r.property hm

theorem output_length (r : RawClosedNetwork) :
    (P.rawEncoding.encode (raw r)).length≤computes.outputBound.bound.eval (P.rawEncoding.encode r).length :=
  computes.outputBound.length_le r

theorem primitive_cost (r : RawClosedNetwork) :
    primitiveCost computes.machine (computes.outputs r).steps
      (some (initList computes.machine.computer (P.rawEncoding.encode r)))≤
      (primitivePolynomial computes).eval (P.rawEncoding.encode r).length :=
  computes_primitive_cost computes r

theorem prefix_storage (r : RawClosedNetwork) (t : ℕ) (ht : t≤(computes.outputs r).steps)
    (z : computes.machine.Config)
    (hr : (fun q=>q.bind computes.machine.computer.step)^[t]
      (some (initList computes.machine.computer (P.rawEncoding.encode r)))=some z) :
    stackSize z.stk≤(P.rawEncoding.encode r).length+
      computes.time.eval (P.rawEncoding.encode r).length*computes.machine.primitiveBudget := by
  have hs := computes.machine.run_size_le _ z t hr
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _
    (ht.trans (computes.outputs r).steps_le_m)) _)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceCompiler
