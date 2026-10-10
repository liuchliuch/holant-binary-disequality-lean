import Holant.Proofs.Counting.UnitPerfectMatchingHolant.Compiler
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Combinators
import Holant.Proofs.Tractability.AffineMachine.WireLists
import Holant.Complexity.FixedFieldMachines.PrimitiveCost


noncomputable section
namespace Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Programs
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.Complexity.BinaryInterpolation.WeightCompiler
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation

/-- Exact iteration for arbitrary installed machine configurations. -/
abbrev RunsExactly {α : Type} (step : α → Option α) (a b : α) (steps : ℕ) : Prop :=
  (fun c => c.bind step)^[steps] (some a) = some b

def vertices : Computes unitEncoding unary (fun g : UnitInput => g.val.1) :=
  recode (Wiring.firstComputes unary (framedListEncoding unitEdgeEncoding))
    Subtype.val (fun _ => rfl) (fun _ => rfl)
def edgeList : Computes unitEncoding (framedListEncoding unitEdgeEncoding)
    (fun g : UnitInput => g.val.2) :=
  recode (Wiring.secondComputes unary (framedListEncoding unitEdgeEncoding))
    Subtype.val (fun _ => rfl) (fun _ => rfl)
def edgeCount : Computes unitEncoding unary (fun g : UnitInput => g.val.2.length) :=
  edgeList.andThen (WireLists.lengthComputes unitEdgeEncoding)

abbrev Context := UnitInput × Bool
def contextEncoding := pairEncoding unitEncoding encodingBoolBool
abbrev Row := Context × ℕ
def rowEncoding := pairEncoding contextEncoding unary
abbrev Slot := Row × ℕ
def slotEncoding := pairEncoding rowEncoding unary

def contextGraph : Computes contextEncoding unitEncoding (fun x : Context => x.1) :=
  Wiring.firstComputes _ _
def contextSide : Computes contextEncoding encodingBoolBool (fun x : Context => x.2) :=
  Wiring.secondComputes _ _
def rowContext : Computes rowEncoding contextEncoding (fun x : Row => x.1) :=
  Wiring.firstComputes _ _
def rowIndex : Computes rowEncoding unary (fun x : Row => x.2) := Wiring.secondComputes _ _
def slotRow : Computes slotEncoding rowEncoding (fun x : Slot => x.1) := Wiring.firstComputes _ _
def slotIndex : Computes slotEncoding unary (fun x : Slot => x.2) := Wiring.secondComputes _ _
def slotSide : Computes slotEncoding encodingBoolBool (fun x : Slot => x.1.1.2) :=
  slotRow.andThen (rowContext.andThen contextSide)
def rowEdges : Computes rowEncoding unary (fun x : Row => x.1.1.val.2.length) :=
  rowContext.andThen (contextGraph.andThen edgeCount)

def edgeAt : Computes slotEncoding unitEdgeEncoding
    (fun x : Slot => x.1.1.1.val.2.getD x.2 ((0,0),(0,0))) :=
  (pairComputes (slotRow.andThen (rowContext.andThen (contextGraph.andThen edgeList)))
    slotIndex).andThen (WireLists.getD unitEdgeEncoding ((0,0),(0,0)))
def endpointPair : Computes slotEncoding (pairEncoding encodingNatBool encodingNatBool)
    (fun x : Slot => (x.1.1.1.val.2.getD x.2 ((0,0),(0,0))).2) :=
  edgeAt.andThen (Wiring.secondComputes (pairEncoding encodingNatBool encodingNatBool)
    (pairEncoding encodingNatBool encodingNatBool))
def leftEndpoint : Computes slotEncoding encodingNatBool
    (fun x : Slot => (x.1.1.1.val.2.getD x.2 ((0,0),(0,0))).2.1) :=
  endpointPair.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
def rightEndpoint : Computes slotEncoding encodingNatBool
    (fun x : Slot => (x.1.1.1.val.2.getD x.2 ((0,0),(0,0))).2.2) :=
  endpointPair.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)
def originalEndpoint : Computes slotEncoding encodingNatBool
    (fun x : Slot => Compiler.endpoint x.1.1.1 x.1.1.2 x.2) :=
  ifComputes slotSide rightEndpoint leftEndpoint
def belongs : Computes slotEncoding encodingBoolBool
    (fun x : Slot => decide (Compiler.endpoint x.1.1.1 x.1.1.2 x.2=x.1.2)) :=
  (pairComputes originalEndpoint ((slotRow.andThen rowIndex).andThen UnaryBinary.computes)).andThen
    (equalComputes encodingNatBool)
def edgeEnd : Computes slotEncoding RawClosedNetwork.endpointEncoding
    (fun x : Slot => (x.2,x.1.1.2)) :=
  recode (pairComputes (slotIndex.andThen UnaryBinary.computes) slotSide)
    id (fun _ => rfl) (fun _ => rfl)
def portEntry : Computes slotEncoding Frame.wordEncoding
    (fun x : Slot => if Compiler.endpoint x.1.1.1 x.1.1.2 x.2=x.1.2
      then entry RawClosedNetwork.endpointEncoding (x.2,x.1.1.2) else []) :=
  congrComputes (ifComputes belongs
    (edgeEnd.andThen (entryComputes RawClosedNetwork.endpointEncoding))
    (constantComputes slotEncoding Frame.wordEncoding [])) (fun _ => by simp)

def portEntries : Computes rowEncoding Frame.wordEncoding
    (fun x : Row => entries RawClosedNetwork.endpointEncoding (Compiler.ports x.1.1 x.1.2 x.2)) :=
  congrComputes (rangeWordsComputes rowEncoding (fun x : Row => x.1.1.val.2.length) rowEdges
    (fun x : Slot => if Compiler.endpoint x.1.1.1 x.1.1.2 x.2=x.1.2
      then entry RawClosedNetwork.endpointEncoding (x.2,x.1.1.2) else []) portEntry)
    (fun x => by
      unfold Compiler.ports entries
      rw [List.flatMap_assoc]
      congr 1
      funext i
      by_cases h : Compiler.endpoint x.1.1 x.1.2 i=x.2 <;> simp [h,entry])

/-- The returned list contains precisely the original occurrence positions,
in their original order. Endpoint equality never merges two records. -/
def ports : Computes rowEncoding (framedListEncoding RawClosedNetwork.endpointEncoding)
    (fun x : Row => Compiler.ports x.1.1 x.1.2 x.2) :=
  recode (joinComputes portEntries (constantComputes rowEncoding Frame.wordEncoding [false]))
    id (fun _ => rfl) (fun x => by
      simpa only [Frame.wordEncoding,framedListEncoding,framedListEncode,List.append_nil,id_eq] using
        entries_append_encode RawClosedNetwork.endpointEncoding (Compiler.ports x.1.1 x.1.2 x.2) [])
def degree : Computes rowEncoding unary
    (fun x : Row => (Compiler.ports x.1.1 x.1.2 x.2).length) :=
  ports.andThen (WireLists.lengthComputes RawClosedNetwork.endpointEncoding)

def sidePorts (b : Bool) : Computes unitEncoding
    (framedListEncoding (framedListEncoding RawClosedNetwork.endpointEncoding))
    (fun g : UnitInput => (List.range g.val.1).map (fun r => Compiler.ports g b r)) :=
  congrComputes ((pairComputes (identityComputes unitEncoding)
    (constantComputes unitEncoding encodingBoolBool b)).andThen
    (WireLists.tabulate contextEncoding (framedListEncoding RawClosedNetwork.endpointEncoding)
      (fun x : Context => x.1.val.1) (contextGraph.andThen vertices)
      (fun x r => Compiler.ports x.1 x.2 r) ports)) (fun _ => rfl)
/-- Uniform WHOLE original row/column incidence-table emitter. -/
def allPorts : Computes unitEncoding
    (framedListEncoding (framedListEncoding RawClosedNetwork.endpointEncoding))
    (fun g : UnitInput => (Compiler.nodes g).map (fun p => Compiler.ports g p.1 p.2)) :=
  congrComputes ((pairComputes (sidePorts false) (sidePorts true)).andThen
    (WireLists.append (framedListEncoding RawClosedNetwork.endpointEncoding)))
    (fun g => by simp [Compiler.nodes,List.map_map,Function.comp_def])
def degreeRow : Computes (framedListEncoding RawClosedNetwork.endpointEncoding)
    RawClosedNetwork.vertexEncoding (fun ps => (ps.length,ps)) :=
  recode (pairComputes
    ((WireLists.lengthComputes RawClosedNetwork.endpointEncoding).andThen UnaryBinary.computes)
    (identityComputes (framedListEncoding RawClosedNetwork.endpointEncoding)))
    id (fun _ => rfl) (fun _ => rfl)
def virtualRows : Computes unitEncoding (framedListEncoding RawClosedNetwork.vertexEncoding)
    (fun g : UnitInput => (Compiler.virtual g).vertices) :=
  congrComputes (allPorts.andThen
    (WireLists.mapComputes (framedListEncoding RawClosedNetwork.endpointEncoding)
      RawClosedNetwork.vertexEncoding (fun ps => (ps.length,ps)) degreeRow))
    (fun g => by simp [Compiler.virtual,List.map_map,Function.comp_def])
def originalEdges : Computes unitEncoding (framedListEncoding encodingNatBool)
    (fun g : UnitInput => List.replicate g.val.2.length 0) :=
  edgeCount.andThen (WireLists.replicate encodingNatBool 0)

/-- This is the exact virtual graph, produced from original bytes by real
programs. Its varying degree labels are NOT the fixed target alphabet.
The still-missing backend must emit the same actual degreeTemplate graft. -/
def virtualComputes : Computes unitEncoding RawClosedNetwork.encoding Compiler.virtual :=
  recode (pairComputes virtualRows originalEdges) id (fun _ => rfl) (fun _ => rfl)
def isolated : Computes rowEncoding encodingBoolBool
    (fun x : Row => (Compiler.ports x.1.1 x.1.2 x.2).isEmpty) :=
  congrComputes ((pairComputes degree (constantComputes rowEncoding unary 0)).andThen
    (equalComputes unary)) (fun x => by
      cases h : Compiler.ports x.1.1 x.1.2 x.2 <;> simp [h])

def sideZeros (b : Bool) : Computes unitEncoding (framedListEncoding encodingBoolBool)
    (fun g : UnitInput => (List.range g.val.1).map (fun r => (Compiler.ports g b r).isEmpty)) :=
  congrComputes ((pairComputes (identityComputes unitEncoding)
    (constantComputes unitEncoding encodingBoolBool b)).andThen
    (WireLists.tabulate contextEncoding encodingBoolBool (fun x : Context => x.1.val.1)
      (contextGraph.andThen vertices) (fun x r => (Compiler.ports x.1 x.2 r).isEmpty) isolated))
    (fun _ => rfl)
def zeroFlags (g : UnitInput) : List Bool :=
  (List.range g.val.1).map (fun r => (Compiler.ports g false r).isEmpty) ++
    (List.range g.val.1).map (fun r => (Compiler.ports g true r).isEmpty)
def flags : Computes unitEncoding (framedListEncoding encodingBoolBool) zeroFlags :=
  (pairComputes (sideZeros false) (sideZeros true)).andThen (WireLists.append encodingBoolBool)
def orFold : Computes (framedListEncoding encodingBoolBool) encodingBoolBool
    (fun xs => xs.foldl (fun a b => a || b) false) :=
  FiniteFold.computes encodingBoolBool encodingBoolBool 1 (fun a b => a || b) false
    (fun b => by cases b <;> rfl)
theorem fold_or_value (xs : List Bool) (a : Bool) :
    xs.foldl (fun a b => a || b) a=(a || xs.any id) := by
  induction xs generalizing a with
  | nil => cases a <;> rfl
  | cons b xs ih => rw [List.foldl_cons,ih]; cases a <;> cases b <;> simp

/-- Retain the legacy unparenthesized statement as originally parsed. -/
theorem fold_or (xs : List Bool) (a : Bool) :
    xs.foldl (fun a b => a || b) a=a || xs.any id := by
  rw [fold_or_value]
  cases a <;> cases h : xs.any id <;> simp [h]

/-- A true finite controller for all original row/column degree-zero tests.
It runs over the same graph and fields read by the incidence emitter. -/
def zero : Computes unitEncoding encodingBoolBool Compiler.zeroTest :=
  congrComputes (flags.andThen orFold) (fun g => by
    change (zeroFlags g).foldl (fun a b => a || b) false=Compiler.zeroTest g
    rw [fold_or_value]
    simp [zeroFlags,Compiler.zeroTest,Compiler.nodes,List.any_map,Function.comp_def])

theorem ports_execution (x : Row) : RunsExactly ports.machine.computer.step
    (initList ports.machine.computer (rowEncoding.encode x))
    (haltList ports.machine.computer
      ((framedListEncoding RawClosedNetwork.endpointEncoding).encode (Compiler.ports x.1.1 x.1.2 x.2)))
    (ports.outputs x).steps := (ports.outputs x).evals_in_steps
theorem virtual_execution (g : UnitInput) : RunsExactly virtualComputes.machine.computer.step
    (initList virtualComputes.machine.computer (unitEncoding.encode g))
    (haltList virtualComputes.machine.computer (RawClosedNetwork.encoding.encode (Compiler.virtual g)))
    (virtualComputes.outputs g).steps := (virtualComputes.outputs g).evals_in_steps
theorem virtual_time (g : UnitInput) :
    (virtualComputes.outputs g).steps≤virtualComputes.time.eval (unitEncoding.encode g).length :=
  (virtualComputes.outputs g).steps_le_m
theorem virtual_primitive (g : UnitInput) :
    primitiveCost virtualComputes.machine (virtualComputes.outputs g).steps
      (some (initList virtualComputes.machine.computer (unitEncoding.encode g)))≤
        (primitivePolynomial virtualComputes).eval (unitEncoding.encode g).length :=
  computes_primitive_cost virtualComputes g
theorem virtual_storage (g : UnitInput) (t : ℕ) (c : virtualComputes.machine.Config)
    (ht : t≤virtualComputes.time.eval (unitEncoding.encode g).length)
    (hr : RunsExactly virtualComputes.machine.computer.step
      (initList virtualComputes.machine.computer (unitEncoding.encode g)) c t) :
    stackSize c.stk≤virtualComputes.outputBound.bound.eval (unitEncoding.encode g).length := by
  have h := virtualComputes.machine.run_size_le _ _ _ hr
  rw [Machine.size_init] at h
  exact h.trans (by
    simpa only [Computes.outputBound,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.add_le_add_left (Nat.mul_le_mul_right virtualComputes.machine.primitiveBudget ht)
        (unitEncoding.encode g).length)
theorem zero_execution (g : UnitInput) : RunsExactly zero.machine.computer.step
    (initList zero.machine.computer (unitEncoding.encode g))
    (haltList zero.machine.computer (encodingBoolBool.encode (Compiler.zeroTest g)))
    (zero.outputs g).steps := (zero.outputs g).evals_in_steps
theorem zero_time (g : UnitInput) : (zero.outputs g).steps≤zero.time.eval (unitEncoding.encode g).length :=
  (zero.outputs g).steps_le_m
theorem zero_primitive (g : UnitInput) : primitiveCost zero.machine (zero.outputs g).steps
    (some (initList zero.machine.computer (unitEncoding.encode g)))≤
      (primitivePolynomial zero).eval (unitEncoding.encode g).length := computes_primitive_cost zero g
theorem zero_storage (g : UnitInput) (t : ℕ) (c : zero.machine.Config)
    (ht : t≤zero.time.eval (unitEncoding.encode g).length)
    (hr : RunsExactly zero.machine.computer.step (initList zero.machine.computer (unitEncoding.encode g)) c t) :
    stackSize c.stk≤zero.outputBound.bound.eval (unitEncoding.encode g).length := by
  have h := zero.machine.run_size_le _ _ _ hr
  rw [Machine.size_init] at h
  exact h.trans (by
    simpa only [Computes.outputBound,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.add_le_add_left (Nat.mul_le_mul_right zero.machine.primitiveBudget ht) (unitEncoding.encode g).length)

end Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Programs
