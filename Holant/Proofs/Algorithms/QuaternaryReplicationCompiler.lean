import Holant.Proofs.Algorithms.QuaternaryReplicationMachine
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Compile
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Endpoints
import Holant.Proofs.Reductions.ControlledCap
import Holant.Complexity.OracleReductionCompose


noncomputable section
namespace Holant.LocalDrafts.MainChain.QuaternaryReplicationCompiler
open Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient RawClosedNetwork
open FixedGadgetSubstitution.Compiler
open QuaternaryReplicationMachine
set_option backward.isDefEq.respectTransparency false

def carrierZero (m t : ℕ) : RawEndpoint := (m+(2*t-1),false)
def carrierOne (m t : ℕ) : RawEndpoint := (m+2*t,t==0)

theorem expand_carrier (s j m : ℕ) (rows : List RawVertex) :
    (expand s j m rows).zeroPort=carrierZero m (count s rows) ∧
    (expand s j m rows).onePort=carrierOne m (count s rows) := by
  induction rows with
  | nil => simp [expand,carrierZero,carrierOne]
  | cons row rows ih =>
      by_cases h : row.1=s
      · simp only [expand,if_pos h,graft,count_cons,if_pos h]
        rw [expand_next]
        constructor
        · apply Prod.ext <;> simp [carrierZero] <;> omega
        · apply Prod.ext <;> simp [carrierOne] <;> omega
      · simpa [expand,h,count_cons] using ih

def twoRows (j m t : ℕ) (ports : List RawEndpoint) : List RawVertex :=
  [(j,[(m+1+2*t,true),carrierOne m t,ports.getD 1 (0,false),ports.getD 3 (0,false)]),
   (j,[(m+1+2*t+1,true),carrierZero m t,ports.getD 0 (0,false),ports.getD 2 (0,false)])]

def emitRow (s j m t : ℕ) (row : RawVertex) : List RawVertex :=
  if row.1=s then twoRows j m t row.2 else [row]

theorem expand_body (s j m : ℕ) (rows : List RawVertex) :
    (expand s j m rows).body=(List.finRange rows.length).flatMap
      (fun i => emitRow s j m (count s (rows.drop (i.val+1))) (rows.get i)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.length_cons,List.finRange_succ,List.flatMap_cons,List.flatMap_map,
        Function.comp_def,Fin.val_zero,Fin.val_succ,List.get_eq_getElem,
        List.getElem_cons_zero,List.getElem_cons_succ,List.drop_succ_cons,List.drop_zero]
      by_cases h : row.1=s
      · simp only [expand,if_pos h,emitRow,if_pos h,twoRows,graft,List.cons_append,List.nil_append]
        rw [expand_next,(expand_carrier s j m rows).1,(expand_carrier s j m rows).2,ih]
        rfl
      · simpa only [expand,if_neg h,emitRow,if_neg h,List.cons_append,List.nil_append,List.get_eq_getElem] using
          congrArg (List.cons row) ih

theorem count_append (s : ℕ) (xs ys : List RawVertex) :
    count s (xs++ys)=count s xs+count s ys := by simp [count,List.filter_append]

variable (s : ℕ) (a : ℕ → ℕ)
abbrev RowQuery := FixedGadgetSubstitution.Compiler.Query (s+1) 1 (squareArity s a)
abbrev rowEncoding := queryEncoding (s+1) 1 (squareArity s a)
abbrev sourceEncoding := validatedEncoding (s+1) 1 (squareArity s a)
def suffix (x : RowQuery s a) : ℕ := count s (x.1.val.vertices.drop (x.2.val+1))

theorem suffix_sub (x : RowQuery s a) : suffix s a x=
    count s x.1.val.vertices -
      (prefixWeight (s+1) 1 (squareArity s a) (fun i => if i=s then 1 else 0) x+
        if (x.1.val.vertices.get x.2).1=s then 1 else 0) := by
  have he : x.1.val.vertices=
      x.1.val.vertices.take x.2.val ++
        (x.1.val.vertices.get x.2 :: x.1.val.vertices.drop (x.2.val+1)) := by
    rw [List.cons_get_drop_succ,List.take_append_drop]
  have hc := congrArg (count s) he
  rw [count_append,count_cons] at hc
  unfold suffix prefixWeight
  rw [indicator_sum]
  change count s _=count s _-(count s _+_)
  omega

/-- Add and subtract the actual binary integers produced by two machines. -/
def add {A : Type} {e : Encoding A Bool} {f g : A → ℕ}
    (u : Computes e encodingNatBool f) (v : Computes e encodingNatBool g) :
    Computes e encodingNatBool (fun x => f x+g x) := (pairComputes u v).andThen addComputes
def sub {A : Type} {e : Encoding A Bool} {f g : A → ℕ}
    (u : Computes e encodingNatBool f) (v : Computes e encodingNatBool g) :
    Computes e encodingNatBool (fun x => f x-g x) := (pairComputes u v).andThen
      UniversalPairReduction.SmoothingCompiler.Endpoints.subtractComputes

def suffixComputes : Computes (rowEncoding s a) encodingNatBool (suffix s a) := by
  let total := ((sourceComputes (s+1) 1 (squareArity s a)).andThen
    (QuaternaryReplicationMachine.countComputes s a)).andThen UnaryBinary.computes
  let before :=  (prefixWeightComputes (s+1) 1 (squareArity s a)
    (fun i => if i=s then 1 else 0)).andThen UnaryBinary.computes
  let current := labelRecodeComputes (s+1) 1 (squareArity s a) encodingNatBool
    (fun i => if i.val=s then 1 else 0)
  exact congrComputes (sub total (add before current)) (fun x => (suffix_sub s a x).symm)

section Building
variable {A : Type} (e : Encoding A Bool) (m t : A → ℕ)
variable (wm : Computes e encodingNatBool m) (wt : Computes e encodingNatBool t)

def zeroComputes : Computes e endpointEncoding (fun x => carrierZero (m x) (t x)) :=
  recode (pairComputes (add wm (sub (add wt wt) (constantComputes e encodingNatBool 1)))
    (constantComputes e encodingBoolBool false)) id (fun _ => rfl)
      (fun x => by simp [carrierZero,two_mul,endpointEncoding,framedProductEncoding])
def oneComputes : Computes e endpointEncoding (fun x => carrierOne (m x) (t x)) :=
  recode (pairComputes (add wm (add wt wt))
    ((pairComputes wt (constantComputes e encodingNatBool 0)).andThen
      UniversalPairReduction.SmoothingCompiler.Endpoints.equalComputes))
    id (fun _ => rfl) (fun x => by
      have hb : decide (t x=0) = (t x==0) := by
        by_cases h : t x=0 <;> simp [h]
      simp [carrierOne,two_mul,endpointEncoding,framedProductEncoding,hb])
def freshComputes (d : ℕ) : Computes e endpointEncoding
    (fun x => (m x+1+2*t x+d,true)) :=
  recode (pairComputes
    (add (add (add wm (constantComputes e encodingNatBool 1)) (add wt wt))
      (constantComputes e encodingNatBool d))
    (constantComputes e encodingBoolBool true)) id (fun _ => rfl)
      (fun x => by simp [two_mul,endpointEncoding,framedProductEncoding])
def headComputes (s : ℕ) : Computes e vertexEncoding
    (fun x => (s,[carrierZero (m x) (t x),carrierOne (m x) (t x)])) := by
  let ports := fixedListComputes e endpointEncoding
    (fun x (b : Bool) => if b then carrierOne (m x) (t x) else carrierZero (m x) (t x))
    (fun b => by
      cases b with
      | false => exact zeroComputes e m t wm wt
      | true => exact oneComputes e m t wm wt)
    [false,true]
  exact recode (pairComputes (constantComputes e encodingNatBool s) ports)
    id (fun _ => rfl) (fun _ => rfl)
end Building

def rowEdgeComputes : Computes (rowEncoding s a) encodingNatBool
    (fun x => x.1.val.edges.length) :=
  ((sourceComputes (s+1) 1 (squareArity s a)).andThen
    (edgeCountComputes (s+1) 1 (squareArity s a))).andThen UnaryBinary.computes
def portsComputes : Computes (rowEncoding s a) (framedListEncoding endpointEncoding)
    (fun x => (x.1.val.vertices.get x.2).2) :=
  (originalRowComputes (s+1) 1 (squareArity s a)).andThen
    (recode (Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding))
      id (fun _ => rfl) (fun _ => rfl))

/-- The four fixed slots are emitted in ORIGINAL q port order, including
the reversed carrier attachment. Padding agrees with raw.graft's getD. -/
def twoRowsComputes (j : ℕ) : Computes (rowEncoding s a) (framedListEncoding vertexEncoding)
    (fun x => twoRows j x.1.val.edges.length (suffix s a x) (x.1.val.vertices.get x.2).2) := by
  let e := rowEncoding s a
  let m := fun x : RowQuery s a => x.1.val.edges.length
  let t := suffix s a
  let wm := rowEdgeComputes s a
  let wt := suffixComputes s a
  let endpoint (b : Bool) (i : Fin 4) (x : RowQuery s a) : RawEndpoint :=
    if i.val=0 then (m x+1+2*t x+(if b then 1 else 0),true)
    else if i.val=1 then (if b then carrierZero (m x) (t x) else carrierOne (m x) (t x))
    else (x.1.val.vertices.get x.2).2.getD
      (if i.val=2 then (if b then 0 else 1) else (if b then 2 else 3)) (0,false)
  have ep (b : Bool) (i : Fin 4) : Computes e endpointEncoding (endpoint b i) := by
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_
      (fun i => Fin.cases ?_ (fun i => Fin.elim0 i) i) i) i) i
    · exact freshComputes e m t wm wt (if b then 1 else 0)
    · cases b
      · exact oneComputes e m t wm wt
      · exact zeroComputes e m t wm wt
    · exact (portsComputes s a).andThen (getDComputes endpointEncoding (if b then 0 else 1) (0,false))
    · exact (portsComputes s a).andThen (getDComputes endpointEncoding (if b then 2 else 3) (0,false))
  let rows (x : RowQuery s a) (b : Bool) : RawVertex :=
    (j,(List.finRange 4).map (fun i => endpoint b i x))
  have wr (b : Bool) : Computes e vertexEncoding (fun x => rows x b) :=
    recode (pairComputes (constantComputes e encodingNatBool j)
      (fixedListComputes e endpointEncoding (fun x i => endpoint b i x) (ep b) (List.finRange 4)))
      id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (fixedListComputes e vertexEncoding rows wr [false,true])
    (fun x => by simp [rows,endpoint,twoRows,m,t,List.finRange_succ])

def rowChunk (j : ℕ) (x : RowQuery s a) : List Bool :=
  entries vertexEncoding (emitRow s j x.1.val.edges.length (suffix s a x)
    (x.1.val.vertices.get x.2))
def rowChunkComputes (j : ℕ) : Computes (rowEncoding s a) Frame.wordEncoding (rowChunk s a j) := by
  let original := (originalRowComputes (s+1) 1 (squareArity s a)).andThen (entryComputes vertexEncoding)
  let expanded := (twoRowsComputes s a j).andThen (entriesComputes vertexEncoding)
  apply congrComputes (chooseComputes (rowEncoding s a) Frame.wordEncoding (s+1)
    (sourceLabel (s+1) 1 (squareArity s a))
    (fun x i => if i.val=s then entries vertexEncoding
      (twoRows j x.1.val.edges.length (suffix s a x) (x.1.val.vertices.get x.2).2)
      else entry vertexEncoding (x.1.val.vertices.get x.2))
    (labelRecodeComputes (s+1) 1 (squareArity s a) UnaryBinary.unaryEncoding Fin.val)
    (fun i => by
      by_cases hi : i.val=s
      · exact congrComputes expanded (fun x => by simp [hi])
      · exact congrComputes original (fun x => by simp [hi])))
  intro x
  by_cases h : (x.1.val.vertices.get x.2).1=s <;>
    simp only [List.get_eq_getElem] at h <;>
    simp [rowChunk,emitRow,sourceLabel,entries,h]

def verticesComputes (j : ℕ) : Computes (sourceEncoding s a) (framedListEncoding vertexEncoding)
    (fun r => (raw s j r.val).vertices) := by
  let head := (headComputes (sourceEncoding s a) (fun r => r.val.edges.length)
    (fun r => count s r.val.vertices)
    ((edgeCountComputes (s+1) 1 (squareArity s a)).andThen UnaryBinary.computes)
    ((QuaternaryReplicationMachine.countComputes s a).andThen UnaryBinary.computes) s).andThen
      (entryComputes vertexEncoding)
  let body := allRowsFlatMapComputes (s+1) 1 (squareArity s a) _ (rowChunkComputes s a j)
  refine recode (joinComputes (joinComputes head body)
    (constantComputes (sourceEncoding s a) Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro r
  change (_++_)++[false]=framedListEncode vertexEncoding (raw s j r.val).vertices
  have hb : (List.finRange r.val.vertices.length).flatMap (fun i => rowChunk s a j ⟨r,i⟩)=
      entries vertexEncoding (expand s j r.val.edges.length r.val.vertices).body := by
    rw [expand_body,entries_flatMap]
    rfl
  have hz := (expand_carrier s j r.val.edges.length r.val.vertices).1
  have ho := (expand_carrier s j r.val.edges.length r.val.vertices).2
  dsimp only [id_eq,Function.comp_def]
  rw [hb]
  have h := entries_append_encode vertexEncoding
    ((s,[carrierZero r.val.edges.length (count s r.val.vertices),
      carrierOne r.val.edges.length (count s r.val.vertices)])::
        (expand s j r.val.edges.length r.val.vertices).body) []
  simpa [raw,emitted,hz,ho,entries,List.flatMap_cons,List.append_assoc,framedListEncode] using h

/-- Edge emission traverses every original row again. Each square contributes
exactly two zero edge labels, and the initial carrier contributes one. -/
def edgesComputes : Computes (sourceEncoding s a) (framedListEncoding encodingNatBool)
    (fun r => (raw s 0 r.val).edges) := by
  let old := (FixedGadgetSubstitution.Compiler.edgesComputes (s+1) 1 (squareArity s a)).andThen
    (entriesComputes encodingNatBool)
  let added := allRowsFlatMapComputes (s+1) 1 (squareArity s a) _
    (labelRecodeComputes (s+1) 1 (squareArity s a) Frame.wordEncoding
      (fun i => entries encodingNatBool (if i.val=s then [0,0] else [])))
  let initial := constantComputes (sourceEncoding s a) Frame.wordEncoding (entry encodingNatBool 0)
  refine recode (joinComputes (joinComputes (joinComputes old initial) added)
    (constantComputes (sourceEncoding s a) Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro r
  have hc (rows : List RawVertex) :
      rows.flatMap (fun row => if row.1=s then [0,0] else [])=List.replicate (2*count s rows) 0 := by
    induction rows with
    | nil => rfl
    | cons row rows ih =>
        by_cases h : row.1=s <;> simp [List.flatMap_cons,h,count_cons,ih,
          Nat.mul_add,List.replicate_add]
  have ha : (List.finRange r.val.vertices.length).flatMap (fun i =>
      entries encodingNatBool (if (r.val.vertices.get i).1=s then [0,0] else []))=
      entries encodingNatBool (List.replicate (2*count s r.val.vertices) 0) := by
    rw [←entries_flatMap]
    have he := congrArg (fun rows : List RawVertex => rows.flatMap
      (fun row => if row.1=s then [0,0] else [])) (all_rows (s+1) 1 (squareArity s a) r)
    rw [List.flatMap_map] at he
    rw [he,hc]
  change ((entries encodingNatBool r.val.edges++entry encodingNatBool 0)++_)++[false]=_
  dsimp only [id_eq,sourceLabel]
  rw [ha]
  have he := entries_append_encode encodingNatBool
    (r.val.edges++(0::List.replicate (2*count s r.val.vertices) 0)) []
  simpa [raw,entries,List.flatMap_append,List.flatMap_cons,entry,
    List.append_assoc,List.replicate_add,framedListEncode,framedListEncoding] using he

/-- Same bytes as the original raw function, including vertex order. -/
def rawComputes (j : ℕ) : Computes (sourceEncoding s a) RawClosedNetwork.encoding
    (fun r => raw s j r.val) :=
  recode (pairComputes (verticesComputes s a j) (edgesComputes s a))
    id (fun _ => rfl) (fun _ => rfl)

def queryComputes (j : Fin s) (hj : a j.val=4) :
    Computes (sourceEncoding s a) (UniversalPairReduction.inputEncoding s a)
      (QuaternaryReplicationMachine.query j hj) :=
  recode (rawComputes s a j.val) id (fun _ => rfl) (fun _ => rfl)

def prepared (j : Fin s) (hj : a j.val=4) :
    Computes (sourceEncoding s a)
      (pairEncoding (UniversalPairReduction.inputEncoding s a) UnaryBinary.unaryEncoding)
      (fun r => (QuaternaryReplicationMachine.query j hj r,count s r.val.vertices)) :=
  pairComputes (queryComputes s a j hj) (QuaternaryReplicationMachine.countComputes s a)

/-- Runtime and primitive instruction cost come from actual finite programs,
not the separately proved query-length estimate. -/
theorem query_primitive_bound (j : Fin s) (hj : a j.val=4)
    (r : QuaternaryReplicationMachine.Input s a) :
    primitiveCost (queryComputes s a j hj).machine ((queryComputes s a j hj).outputs r).steps
      (some (Turing.initList (queryComputes s a j hj).machine.computer
        ((sourceEncoding s a).encode r)))≤
      (primitivePolynomial (queryComputes s a j hj)).eval ((sourceEncoding s a).encode r).length :=
  computes_primitive_cost (queryComputes s a j hj) r

section Caller
variable (G : (i : Fin s) → Holant.Signature Holant.Tractable.AlgebraicComplex (a i.val))
variable (j : Fin s) {q : Holant.Signature Holant.Tractable.AlgebraicComplex 4}
variable (hj : (⟨a j.val,G j⟩ : Holant.AnySignature Holant.Tractable.AlgebraicComplex)=⟨4,q⟩)
variable (P : QuaternaryEqualityTerminal.PureStep q)

abbrev field := UniversalPairReduction.Source.field G
abbrev presentation := UniversalPairReduction.Source.presentation G (QuaternaryEqualityTerminal.algebraic G)
abbrev originalTables := UniversalPairReduction.Source.tables G (QuaternaryEqualityTerminal.algebraic G)

/-- Tables for the actual at-most-one target, in the old family field.
Only the answer-length proof uses this unrestricted table presentation. -/
def deltaTables : ExactSignatureTables (Module.finrank ℚ (field s a G)) (s+1) 1
    (UniversalPairReduction.extendedArity s a) where
  vertex i x := (presentation s a G).decode.symm
    (UniversalPairReduction.BinaryFamily.signatures
      (UniversalPairReduction.ValueJoins.signatures (presentation s a G) (originalTables s a G))
      UniversalPairReduction.BinaryTable.delta i x)
  edge := (originalTables s a G).edge

theorem delta_tables_value (r : UniversalPairReduction.Input s a) :
    (deltaTables s a G).evaluate (presentation s a G) ⟨r.val,r.property.1⟩=
      UniversalPairReduction.Source.sourceValue G (QuaternaryEqualityTerminal.algebraic G) r := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  have hn := UniversalPairReduction.Source.native_tables G (QuaternaryEqualityTerminal.algebraic G)
  simp only [deltaTables,LinearEquiv.apply_symm_apply]
  have he : (fun i x y => (presentation s a G).decode ((originalTables s a G).edge i x y))=
      (fun _ : Fin 1 => Holant.Signature.disequality) := funext fun i => funext fun x => funext (hn i x)
  rw [he]
  rfl

def deltaAnswerBound : PolynomialOutputBound (UniversalPairReduction.inputEncoding s a)
    (presentation s a G).encoding
    (UniversalPairReduction.Source.sourceValue G (QuaternaryEqualityTerminal.algebraic G)) where
  bound := (deltaTables s a G).outputPolynomial (presentation s a G)
  length_le r := by
    have h := (deltaTables s a G).output_length_le (presentation s a G) ⟨r.val,r.property.1⟩
    rw [delta_tables_value s a G r] at h
    exact h

/-- The source is actual square Holant, not an opaque postprocessed oracle.
No correctness or time field is supplied by a caller: all are produced above. -/
def controlled (P : QuaternaryEqualityTerminal.PureStep q) : LengthControlledOracleReduction (sourceEncoding s a)
    (presentation s a G).encoding (UniversalPairReduction.inputEncoding s a)
    (presentation s a G).encoding (squareFieldValue G)
    (UniversalPairReduction.Source.sourceValue G (QuaternaryEqualityTerminal.algebraic G)) := by
  let C := Holant.LocalDrafts.Hardness.ControlledCap.controlledContext
    (prepared s a j (congrArg Sigma.fst hj)) (QuaternaryReplicationMachine.correction G j)
    (deltaAnswerBound s a G)
  refine {
    reduction := {
      machine := C.reduction.machine
      time := C.reduction.time
      correct := ?_ }
    targetOutput := C.targetOutput
    queryBound := C.queryBound
    safeQuery := C.safeQuery }
  intro oracle ho r
  have run := C.reduction.correct oracle ho r
  have heq : UniversalPairReduction.Source.sourceValue G (QuaternaryEqualityTerminal.algebraic G)
      (QuaternaryReplicationMachine.query j (congrArg Sigma.fst hj) r) *
        (QuaternaryReplicationMachine.scale G j)⁻¹^count s r.val.vertices = squareFieldValue G r := by
    rw [query_value_field G j hj P,ScalarPower.cancel_scale_power _ _ (scale_nonzero G j hj P)]
  change C.reduction.machine.OutputsInTime oracle ((sourceEncoding s a).encode r)
    ((presentation s a G).encoding.encode (_ * _)) _ at run
  rw [heq] at run
  exact run

/-- This inlines the existing one-pair program into the controlled caller.
It does NOT use an unrestricted PolyTimeOracleReduction transitivity law. -/
def reduction : PolyTimeOracleReduction (sourceEncoding s a) (presentation s a G).encoding
    (validatedEncoding s 1 a) (presentation s a G).encoding (squareFieldValue G)
    (UniversalPairReduction.Source.targetValue G (QuaternaryEqualityTerminal.algebraic G)) :=
  (controlled s a G j hj P).compose (QuaternaryEqualityTerminal.onePair G)

theorem caller_atMostOne : UniversalPairReduction.ThreeQuery.AtMostQueries
    (controlled s a G j hj P).reduction.machine 1 := by
  exact UniversalPairReduction.SmoothingCompiler.ContextCount.atMostOne
      (prepared s a j (congrArg Sigma.fst hj)).machine
      (QuaternaryReplicationMachine.correction G j).machine

/-- The exact callee that is inlined retains its existing actual-prefix
three-query certificate; repeated equal queries are still counted separately. -/
theorem callee_atMostThree : UniversalPairReduction.ThreeQuery.AtMostQueries
    (QuaternaryEqualityTerminal.onePair G).machine 3 :=
  QuaternaryEqualityTerminal.onePair_queries G

private theorem queries_le_steps (m : OracleMachine) (oracle : List Bool → List Bool)
    (c : m.Cfg) (n : ℕ) : UniversalPairReduction.ThreeQuery.queryCount m oracle c n≤n := by
  induction n generalizing c with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      simp only [UniversalPairReduction.ThreeQuery.queryCount]
      cases hs : m.step oracle c with
      | none => exact Nat.zero_le _
      | some d =>
          have hc : UniversalPairReduction.ThreeQuery.queryCost m c≤1 := by
            unfold UniversalPairReduction.ThreeQuery.queryCost
            cases c.l with
            | none => exact Nat.zero_le _
            | some l => cases hp : m.program l <;> simp [hp]
          exact (Nat.add_le_add hc (ih d)).trans (by omega)

/-- Actual external queries along the completed composed run have this
polynomial budget. This does not pretend that a separate sharp ≤3 theorem
for arbitrary prefixes of the composed inliner has already been proved. -/
theorem completed_query_budget (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (validatedEncoding s 1 a) (presentation s a G).encoding
      (UniversalPairReduction.Source.targetValue G (QuaternaryEqualityTerminal.algebraic G)) oracle)
    (r : QuaternaryReplicationMachine.Input s a) :
    UniversalPairReduction.ThreeQuery.queryCount (reduction s a G j hj P).machine oracle
      ((reduction s a G j hj P).machine.init ((sourceEncoding s a).encode r))
      ((reduction s a G j hj P).correct oracle ho r).steps≤
      (reduction s a G j hj P).time.eval ((sourceEncoding s a).encode r).length :=
  (queries_le_steps _ _ _ _).trans ((reduction s a G j hj P).correct oracle ho r).steps_le_m

/-- Actual caller queries have polynomially bounded ANSWERS, inherited from
the exact Holant table rather than from the compiler's output-length bound. -/
theorem intermediate_answer_length (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (UniversalPairReduction.inputEncoding s a) (presentation s a G).encoding
      (UniversalPairReduction.Source.sourceValue G (QuaternaryEqualityTerminal.algebraic G)) oracle)
    (r : QuaternaryReplicationMachine.Input s a) (t : ℕ)
    (c : (controlled s a G j hj P).reduction.machine.Cfg)
    (hr : (controlled s a G j hj P).reduction.machine.run oracle
      ((sourceEncoding s a).encode r) t=some c)
    (hc : (controlled s a G j hj P).reduction.machine.IsQuery c) :
    (oracle (c.stk (controlled s a G j hj P).reduction.machine.queryStack)).length≤
      ((controlled s a G j hj P).targetOutput.bound.comp
        (controlled s a G j hj P).queryBound).eval ((sourceEncoding s a).encode r).length :=
  (controlled s a G j hj P).answer_length_le oracle ho r t c hr hc

end Caller
end Holant.LocalDrafts.MainChain.QuaternaryReplicationCompiler
