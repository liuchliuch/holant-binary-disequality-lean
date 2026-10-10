import Holant.Proofs.Tetrahedral.EvenCSPReduction.Compilation
import Holant.Proofs.Tetrahedral.EvenCSPReduction.Semantics
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Lists
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Prefix
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Endpoints

/-! Uniform Boolean-stack scans of the original CSP
records. Every unbounded traversal below is ContextFlatMap's actual finite
machine; the callback is composed from existing proved finite machines and
the explicit two-token half counter. RecordsIdentity.raw_eq supplies exact
ordered graph identity with Compilation.query. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
namespace Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Program
open Holant Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing GraphPreprocessing.OriginalCoefficient
open FixedGadgetSubstitution Holant.OneHot.StackProgram.GraphLabelEncoding
open RawClosedNetwork
open scoped BigOperators
namespace Scan
variable {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)

abbrev encoding := sigmaEncoding ea (fun _ => framedListEncoding eb)
abbrev itemEncoding := sigmaEncoding ea (fun _ => eb)

theorem tokens (xs : List B) (f : B → ℕ) :
    xs.flatMap (fun b => List.replicate (f b) true)=
      List.replicate ((xs.map f).sum) true := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
      simp only [Function.comp_def,id_eq,List.flatMap_cons,List.map_cons,List.sum_cons,ih,List.replicate_add]

/-- Counting scans emit one physical token per accepted original record. -/
def countIf (test : A × B → Bool) (x : Σ _ : A,List B) : ℕ :=
  ((x.2.map (fun b => if test (x.1,b) then 1 else 0)).sum)

def countComputes (test : A × B → Bool)
    (w : Computes (pairEncoding ea eb) encodingBoolBool test) :
    Computes (encoding ea eb) UnaryBinary.unaryEncoding (countIf test) := by
  let provider : Computes (itemEncoding ea eb) Frame.wordEncoding
      (fun x => if test (x.1,x.2) then [true] else []) :=
    recode (UniversalPairReduction.SmoothingCompiler.Endpoints.selectComputes
      (pairEncoding ea eb) Frame.wordEncoding test (fun _ => [true]) (fun _ => [])
      w (constantComputes _ _ [true]) (constantComputes _ _ []))
      (fun x => (x.1,x.2)) (fun _ => rfl) (fun _ => rfl)
  exact recode (ContextFlatMap.computes ea (fun _ => eb) _ provider) id
    (fun _ => rfl) (fun x => by
      change x.2.flatMap (fun b => if test (x.1,b) then [true] else [])=
        List.replicate (countIf test x) true
      dsimp only [Function.comp_def,id_eq,countIf]
      rw [← tokens]
      congr 1
      funext b
      cases test (x.1,b) <;> rfl)

/-- List length is read from actual element frames, rather than metadata. -/
def lengthComputes : Computes (framedListEncoding eb) UnaryBinary.unaryEncoding List.length := by
  let test : Computes (pairEncoding Frame.wordEncoding eb) encodingBoolBool (fun _ => true) :=
    constantComputes _ _ true
  let prepare : Computes (framedListEncoding eb) (encoding Frame.wordEncoding eb)
      (fun xs => (⟨[],xs⟩ : Σ _ : List Bool,List B)) :=
    recode (pairComputes (constantComputes _ Frame.wordEncoding [])
      (identityComputes (framedListEncoding eb))) id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (prepare.andThen (countComputes Frame.wordEncoding eb _ test))
    (fun xs => by simp [countIf])

/-- The context and its list are physically paired before the scan. -/
def fromComputes {C : Type} (ec : Encoding C Bool) (context : C → A)
    (items : C → List B) (u : Computes ec ea context)
    (v : Computes ec (framedListEncoding eb) items)
    (f : (Σ _ : A,B) → List Bool)
    (provider : Computes (itemEncoding ea eb) Frame.wordEncoding f) :
    Computes ec Frame.wordEncoding (fun c => (items c).flatMap (fun b => f ⟨context c,b⟩)) := by
  let prepare : Computes ec (encoding ea eb)
      (fun c => (⟨context c,items c⟩ : Σ _ : A,List B)) :=
    recode (pairComputes u v) id (fun _ => rfl) (fun _ => rfl)
  exact prepare.andThen (ContextFlatMap.computes ea (fun _ => eb) f provider)

end Scan

namespace Half
open Turing

/-- Exactly two physical pops pay for every output token. -/
abbrev machine : Machine where
  K := Fin 2
  input := 0
  output := 1
  Label := Unit
  main := ()
  State := Option Bool
  initial := none
  program _ := .pop 0 (fun _ b => b) (.branch Option.isSome
    (.pop 0 (fun _ b => b) (.branch Option.isSome
      (.push 1 (fun _ => true) (.load (fun _ => none) (.goto (fun _ => ())))) .halt)) .halt)

def config (tokens output : List Bool) : machine.Config :=
  ⟨some (),none,![tokens,output]⟩
def Runs (x y : machine.Config) (n : ℕ) : Prop :=
  (fun c => c.bind machine.computer.step)^[n] (some x)=some y

theorem pair_step (b c : Bool) (tokens output : List Bool) :
    machine.computer.step (config (b::c::tokens) output)=
      some (config tokens (true::output)) := by
  dsimp [machine,config,FinTM2.step,TM2.step,TM2.stepAux]
  simp only [Bool.cond_true,Bool.cond_false,Function.update_self,List.head?_cons,List.head?_nil,Option.isSome_some,Option.isSome_none,List.tail_cons,List.tail_nil]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem empty_step (output : List Bool) :
    machine.computer.step (config [] output)=some (haltList machine.computer output) := by
  rw [Machine.halt_eq]
  dsimp [machine,config,FinTM2.step,TM2.step,TM2.stepAux]
  simp only [Bool.cond_true,Bool.cond_false,Function.update_self,List.head?_cons,List.head?_nil,Option.isSome_some,Option.isSome_none,List.tail_cons,List.tail_nil]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem singleton_step (b : Bool) (output : List Bool) :
    machine.computer.step (config [b] output)=some (haltList machine.computer output) := by
  rw [Machine.halt_eq]
  dsimp [machine,config,FinTM2.step,TM2.step,TM2.stepAux]
  simp only [Bool.cond_true,Bool.cond_false,Function.update_self,List.head?_cons,List.head?_nil,Option.isSome_some,Option.isSome_none,List.tail_cons,List.tail_nil]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem initial (tokens : List Bool) : config tokens []=initList machine.computer tokens := by
  rw [Machine.init_eq]
  dsimp only [Function.comp_def,id_eq,config,machine]
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Exact halt, with no residual input or scratch tape. -/
theorem exact_run (n : ℕ) (output : List Bool) :
    (fun c => c.bind machine.computer.step)^[n/2+1]
      (some (config (List.replicate n true) output))=
      some (haltList machine.computer (List.replicate (n/2) true ++ output)) := by
  induction n using Nat.strong_induction_on generalizing output with
  | h n ih =>
    cases n with
    | zero => exact empty_step output
    | succ n =>
      cases n with
      | zero => exact singleton_step true output
      | succ n =>
        have hn : (n+1+1)/2+1=(n/2+1)+1 := by omega
        rw [hn,Function.iterate_succ_apply]
        simp only [Function.comp_def,id_eq,List.replicate_succ,pair_step,Option.bind_some]
        rw [ih n (by omega) (true::output)]
        congr 2
        have hn' : (n+1+1)/2=n/2+1 := by omega
        rw [hn',List.replicate_add]
        simp only [Function.comp_def,id_eq,List.replicate_one,List.append_assoc,List.singleton_append]

def computes : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding (fun n => n/2) where
  machine := machine
  time := Polynomial.X+1
  outputs n := {
    steps := n/2+1
    evals_in_steps := by
      change (fun c : Option machine.Config => c.bind machine.computer.step)^[n/2+1]
        (some (initList machine.computer (List.replicate n true)))=
          some (haltList machine.computer (List.replicate (n/2) true))
      simpa only [List.append_nil,initial] using exact_run n []
    steps_le_m := by simp only [Function.comp_def,id_eq,UnaryBinary.unaryEncoding,List.length_replicate,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]; omega }
end Half

namespace Records
variable (s : ℕ) (a : ℕ → ℕ)
abbrev inputEncoding := Raw.validatedEncoding s a
abbrev Row := Σr : Raw.Input s a,Fin r.val.factors.length
abbrev rowEncoding := sigmaEncoding (inputEncoding s a)
  (fun r => OccurrenceLabel.unaryPortEncoding r.val.factors.length)
abbrev Variable := Σr : Raw.Input s a,Fin r.val.variables
abbrev variableEncoding := sigmaEncoding (inputEncoding s a)
  (fun r => OccurrenceLabel.unaryPortEncoding r.val.variables)

def variablesComputes : Computes (inputEncoding s a) UnaryBinary.unaryEncoding
    (fun r => r.val.variables) :=
  recode (Wiring.firstComputes UnaryBinary.unaryEncoding (framedListEncoding Raw.factorEncoding))
    (fun r => (r.val.variables,r.val.factors)) (fun _ => rfl) (fun _ => rfl)
def factorsComputes : Computes (inputEncoding s a) (framedListEncoding Raw.factorEncoding)
    (fun r => r.val.factors) :=
  recode (Wiring.secondComputes UnaryBinary.unaryEncoding (framedListEncoding Raw.factorEncoding))
    (fun r => (r.val.variables,r.val.factors)) (fun _ => rfl) (fun _ => rfl)
def rowsCountComputes : Computes (inputEncoding s a) UnaryBinary.unaryEncoding
    (fun r => r.val.factors.length) :=
  (factorsComputes s a).andThen (Scan.lengthComputes Raw.factorEncoding)

def rowSourceComputes : Computes (rowEncoding s a) (inputEncoding s a) (fun x => x.1) :=
  recode (Wiring.firstComputes (inputEncoding s a) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
def rowIndexComputes : Computes (rowEncoding s a) UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  recode (Wiring.secondComputes (inputEncoding s a) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
def variableSourceComputes : Computes (variableEncoding s a) (inputEncoding s a) (fun x => x.1) :=
  recode (Wiring.firstComputes (inputEncoding s a) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
def variableIndexComputes : Computes (variableEncoding s a) UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  recode (Wiring.secondComputes (inputEncoding s a) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

def rowComputes : Computes (rowEncoding s a) Raw.factorEncoding
    (fun x => x.1.val.factors.get x.2) := by
  let prepare : Computes (rowEncoding s a) (ParentRowSelect.inputEncoding Raw.factorEncoding)
      (fun x => ⟨x.1.val.factors,x.2⟩) :=
    recode (pairComputes ((rowSourceComputes s a).andThen (factorsComputes s a))
      (rowIndexComputes s a)) id (fun _ => rfl) (fun _ => rfl)
  exact prepare.andThen (ParentRowSelect.computes Raw.factorEncoding)

def rowsComputes : Computes (inputEncoding s a)
    (ContextFlatMap.inputEncoding (inputEncoding s a)
      (fun r => OccurrenceLabel.unaryPortEncoding r.val.factors.length))
    (fun r => ⟨r,List.finRange r.val.factors.length⟩) :=
  recode (pairComputes (identityComputes (inputEncoding s a))
    ((rowsCountComputes s a).andThen ComponentSelection.UnaryRange.computes)) id
    (fun _ => rfl) (fun r => by
      change frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _)=_
      rw [←Compiler.finRange_values,Compiler.finListEncoding]
      rfl)

def variableListComputes : Computes (inputEncoding s a)
    (ContextFlatMap.inputEncoding (inputEncoding s a)
      (fun r => OccurrenceLabel.unaryPortEncoding r.val.variables))
    (fun r => ⟨r,List.finRange r.val.variables⟩) :=
  recode (pairComputes (identityComputes (inputEncoding s a))
    ((variablesComputes s a).andThen ComponentSelection.UnaryRange.computes)) id
    (fun _ => rfl) (fun r => by
      change frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _)=_
      rw [←Compiler.finRange_values,Compiler.finListEncoding]
      rfl)

def rowsFlatMap (f : Row s a → List Bool)
    (w : Computes (rowEncoding s a) Frame.wordEncoding f) :
    Computes (inputEncoding s a) Frame.wordEncoding
      (fun r => (List.finRange r.val.factors.length).flatMap (fun i => f ⟨r,i⟩)) :=
  (rowsComputes s a).andThen (ContextFlatMap.computes (inputEncoding s a)
    (fun r => OccurrenceLabel.unaryPortEncoding r.val.factors.length) f w)

def variablesFlatMap (f : Variable s a → List Bool)
    (w : Computes (variableEncoding s a) Frame.wordEncoding f) :
    Computes (inputEncoding s a) Frame.wordEncoding
      (fun r => (List.finRange r.val.variables).flatMap (fun i => f ⟨r,i⟩)) :=
  (variableListComputes s a).andThen (ContextFlatMap.computes (inputEncoding s a)
    (fun r => OccurrenceLabel.unaryPortEncoding r.val.variables) f w)
end Records

namespace Indexed
variable {C : Type} (ec : Encoding C Bool) (count : C → ℕ)
abbrev Input := Σc : C,Fin (count c)
abbrev encoding := sigmaEncoding ec (fun c => OccurrenceLabel.unaryPortEncoding (count c))
def context : Computes (encoding ec count) ec (fun x => x.1) :=
  recode (Wiring.firstComputes ec UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
def index : Computes (encoding ec count) UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  recode (Wiring.secondComputes ec UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
def all (w : Computes ec UnaryBinary.unaryEncoding count) :
    Computes ec (ContextFlatMap.inputEncoding ec
      (fun c => OccurrenceLabel.unaryPortEncoding (count c)))
      (fun c => ⟨c,List.finRange (count c)⟩) :=
  recode (pairComputes (identityComputes ec)
    (w.andThen ComponentSelection.UnaryRange.computes)) id
    (fun _ => rfl) (fun c => by
      change frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _)=_
      rw [←Compiler.finRange_values,Compiler.finListEncoding]
      rfl)
def flatMap (w : Computes ec UnaryBinary.unaryEncoding count)
    (f : Input count → List Bool) (provider : Computes (encoding ec count) Frame.wordEncoding f) :
    Computes ec Frame.wordEncoding
      (fun c => (List.finRange (count c)).flatMap (fun i => f ⟨c,i⟩)) :=
  (all ec count w).andThen (ContextFlatMap.computes ec
    (fun c => OccurrenceLabel.unaryPortEncoding (count c)) f provider)
def sum (w : Computes ec UnaryBinary.unaryEncoding count)
    (weight : Input count → ℕ)
    (provider : Computes (encoding ec count) UnaryBinary.unaryEncoding weight) :
    Computes ec UnaryBinary.unaryEncoding (fun c => ∑i : Fin (count c),weight ⟨c,i⟩) :=
  recode (flatMap ec count w _ (provider.andThen (Compiler.encodeComputes UnaryBinary.unaryEncoding)))
    id (fun _ => rfl) (fun c => by
      change (List.finRange (count c)).flatMap
        (fun i => List.replicate (weight ⟨c,i⟩) true)=_
      rw [Scan.tokens]
      apply congrArg (fun n => List.replicate n true)
      rw [←List.ofFn_eq_map,List.sum_ofFn])
end Indexed

namespace Arithmetic
open UniversalPairReduction.SmoothingCompiler.Endpoints
variable {C : Type} {ec : Encoding C Bool} {f g : C → ℕ}
def add (u : Computes ec encodingNatBool f) (v : Computes ec encodingNatBool g) :
    Computes ec encodingNatBool (fun c => f c+g c) :=
  (pairComputes u v).andThen Compiler.addComputes
def subtract (u : Computes ec encodingNatBool f) (v : Computes ec encodingNatBool g) :
    Computes ec encodingNatBool (fun c => f c-g c) :=
  (pairComputes u v).andThen subtractComputes
def equal (u : Computes ec encodingNatBool f) (v : Computes ec encodingNatBool g) :
    Computes ec encodingBoolBool (fun c => decide (f c=g c)) :=
  (pairComputes u v).andThen equalComputes
def less (u : Computes ec encodingNatBool f) (v : Computes ec encodingNatBool g) :
    Computes ec encodingBoolBool (fun c => decide (f c<g c)) :=
  (pairComputes u v).andThen lessComputes
def unaryAdd (u : Computes ec UnaryBinary.unaryEncoding f)
    (v : Computes ec UnaryBinary.unaryEncoding g) :
    Computes ec UnaryBinary.unaryEncoding (fun c => f c+g c) :=
  recode (Compiler.joinComputes (u.andThen (Compiler.encodeComputes UnaryBinary.unaryEncoding))
    (v.andThen (Compiler.encodeComputes UnaryBinary.unaryEncoding))) id
    (fun _ => rfl) (fun c => by simp only [Function.comp_def,id_eq,Frame.wordEncoding,UnaryBinary.unaryEncoding,List.replicate_add])
def choose {D : Type} (ed : Encoding D Bool) (test : C → Bool) (yes no : C → D)
    (wt : Computes ec encodingBoolBool test) (wy : Computes ec ed yes) (wn : Computes ec ed no) :
    Computes ec ed (fun c => if test c then yes c else no c) :=
  selectComputes ec ed test yes no wt wy wn
end Arithmetic

namespace Counts
variable (s : ℕ) (a : ℕ → ℕ)
abbrev Context := Raw.Input s a × ℕ
abbrev encoding := pairEncoding (Raw.validatedEncoding s a) encodingNatBool
def sourceComputes : Computes (encoding s a) (Raw.validatedEncoding s a) Prod.fst :=
  Wiring.firstComputes _ _
def addressComputes : Computes (encoding s a) encodingNatBool Prod.snd :=
  Wiring.secondComputes _ _

def rowDegree (x : ℕ × Factor) := (x.2.2.filter (fun j => j==x.1)).length
def rowDegreeComputes : Computes (pairEncoding encodingNatBool Raw.factorEncoding)
    UnaryBinary.unaryEncoding rowDegree := by
  let context := Wiring.firstComputes encodingNatBool Raw.factorEncoding
  let ports := (Wiring.secondComputes encodingNatBool Raw.factorEncoding).andThen
    (Wiring.secondComputes encodingNatBool (framedListEncoding encodingNatBool))
  let prepare : Computes (pairEncoding encodingNatBool Raw.factorEncoding)
      (Scan.encoding encodingNatBool encodingNatBool)
      (fun x => ⟨x.1,x.2.2⟩) :=
    recode (pairComputes context ports) id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (prepare.andThen (Scan.countComputes encodingNatBool encodingNatBool
    (fun x => decide (x.2=x.1))
    (congrComputes UniversalPairReduction.SmoothingCompiler.Endpoints.equalComputes
      (fun x => by simp only [Function.comp_def,id_eq,eq_comm])))) (fun x => by
    change ((x.2.2.map (fun j => if decide (j=x.1) then 1 else 0)).sum)=
      (x.2.2.filter (fun j => j==x.1)).length
    induction x.2.2 with
    | nil => rfl
    | cons j js ih =>
        simp only [decide_eq_true_eq] at ih
        by_cases h : j=x.1 <;> simp [h,ih,Nat.add_comm])

def degreeComputes : Computes (encoding s a) UnaryBinary.unaryEncoding
    (fun x => x.1.val.degree x.2) := by
  let row : Computes (Scan.itemEncoding encodingNatBool Raw.factorEncoding)
      Frame.wordEncoding (fun x => List.replicate (rowDegree (x.1,x.2)) true) :=
    recode (rowDegreeComputes.andThen (Compiler.encodeComputes UnaryBinary.unaryEncoding))
      (fun x => (x.1,x.2)) (fun _ => rfl) (fun _ => rfl)
  let run := Scan.fromComputes encodingNatBool Raw.factorEncoding (encoding s a)
    Prod.snd (fun x => x.1.val.factors) (addressComputes s a)
    ((sourceComputes s a).andThen (Records.factorsComputes s a)) _ row
  refine recode run id (fun _ => rfl) (fun x => ?_)
  change x.1.val.factors.flatMap (fun row => List.replicate (rowDegree (x.2,row)) true)=
    List.replicate (x.1.val.degree x.2) true
  rw [Scan.tokens]
  apply congrArg (fun n => List.replicate n true)
  symm
  unfold Raw.degree Raw.occurrences Raw.portList Raw.address
  rw [List.filter_flatMap,List.length_flatMap]
  have inner (v : Fin x.1.val.factors.length) :
      (((List.finRange (x.1.val.factors.get v).2.length).map
        (fun j => (⟨v,j⟩ : x.1.val.Ports))).filter
        (fun p => (x.1.val.factors.get p.1).2.get p.2==x.2)).length=
        rowDegree (x.2,x.1.val.factors.get v) := by
    rw [List.filter_map,List.length_map]
    change ((List.finRange _).filter (fun j => (x.1.val.factors.get v).2.get j==x.2)).length=
      ((x.1.val.factors.get v).2.filter (fun j => j==x.2)).length
    conv_rhs => rw [←List.map_get_finRange (x.1.val.factors.get v).2,
      List.filter_map,List.length_map]
    rfl
  simp_rw [inner]
  simpa only [List.map_map,Function.comp_def] using
    congrArg (fun rows => (rows.map (fun row => rowDegree (x.2,row))).sum)
      (List.map_get_finRange x.1.val.factors)

def variableContextComputes : Computes (Records.variableEncoding s a) (encoding s a)
    (fun x => (x.1,x.2.val)) :=
  pairComputes (Records.variableSourceComputes s a)
    ((Records.variableIndexComputes s a).andThen UnaryBinary.computes)
def variableDegreeComputes : Computes (Records.variableEncoding s a) UnaryBinary.unaryEncoding
    (fun x => x.1.val.degree x.2.val) :=
  (variableContextComputes s a).andThen (degreeComputes s a)

def nodes (d : ℕ) := if d=0 then 1 else if d=2 then 0 else d/2-1
def edges (d : ℕ) := if d=0 then 2 else if d=2 then 1 else d+(d/2-2)
def nodesComputes : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding nodes := by
  let d := UnaryBinary.computes
  let zero := Arithmetic.equal d (constantComputes _ encodingNatBool 0)
  let two := Arithmetic.equal d (constantComputes _ encodingNatBool 2)
  let high := Half.computes.andThen UniversalPairReduction.SmoothingCompiler.Endpoints.unaryPredecessorComputes
  exact congrComputes (Arithmetic.choose UnaryBinary.unaryEncoding _ _ _ zero
    (constantComputes _ _ 1) (Arithmetic.choose UnaryBinary.unaryEncoding _ _ _ two
      (constantComputes _ _ 0) high)) (fun d => by simp only [Function.comp_def,id_eq,nodes,decide_eq_true_eq])
def edgesComputes : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding edges := by
  let d := UnaryBinary.computes
  let zero := Arithmetic.equal d (constantComputes _ encodingNatBool 0)
  let two := Arithmetic.equal d (constantComputes _ encodingNatBool 2)
  let internal := (Half.computes.andThen UniversalPairReduction.SmoothingCompiler.Endpoints.unaryPredecessorComputes).andThen
    UniversalPairReduction.SmoothingCompiler.Endpoints.unaryPredecessorComputes
  let high := Arithmetic.unaryAdd (identityComputes UnaryBinary.unaryEncoding) internal
  exact congrComputes (Arithmetic.choose UnaryBinary.unaryEncoding _ _ _ zero
    (constantComputes _ _ 2) (Arithmetic.choose UnaryBinary.unaryEncoding _ _ _ two
      (constantComputes _ _ 1) high)) (fun d => by simp only [Function.comp_def,id_eq,edges,decide_eq_true_eq,Nat.sub_sub])

def cellNodesComputes : Computes (Records.variableEncoding s a) UnaryBinary.unaryEncoding
    (fun x => (Compilation.cell x.1 x.2).vertices) :=
  congrComputes ((variableDegreeComputes s a).andThen nodesComputes)
    (fun x => (Cells.make_counts _ (x.1.property.2.2 x.2.val x.2.isLt)).1.symm)
def cellEdgesComputes : Computes (Records.variableEncoding s a) UnaryBinary.unaryEncoding
    (fun x => (Compilation.cell x.1 x.2).edges) :=
  congrComputes ((variableDegreeComputes s a).andThen edgesComputes)
    (fun x => (Cells.make_counts _ (x.1.property.2.2 x.2.val x.2.isLt)).2.symm)
def totalEdgesComputes : Computes (Raw.validatedEncoding s a) UnaryBinary.unaryEncoding Compilation.edgeCount :=
  Indexed.sum (Raw.validatedEncoding s a) (fun r => r.val.variables)
    (Records.variablesComputes s a) _ (cellEdgesComputes s a)
end Counts

namespace Ports
variable (s : ℕ) (a : ℕ → ℕ)
abbrev Input := Indexed.Input (fun x : Records.Row s a => (x.1.val.factors.get x.2).2.length)
abbrev encoding := Indexed.encoding (Records.rowEncoding s a)
  (fun x : Records.Row s a => (x.1.val.factors.get x.2).2.length)
def rowComputes : Computes (encoding s a) (Records.rowEncoding s a) (fun p => p.1) :=
  Indexed.context _ _
def indexComputes : Computes (encoding s a) UnaryBinary.unaryEncoding (fun p => p.2.val) :=
  Indexed.index _ _
def sourceComputes : Computes (encoding s a) (Raw.validatedEncoding s a) (fun p => p.1.1) :=
  (rowComputes s a).andThen (Records.rowSourceComputes s a)
def rowIndexComputes : Computes (encoding s a) UnaryBinary.unaryEncoding (fun p => p.1.2.val) :=
  (rowComputes s a).andThen (Records.rowIndexComputes s a)
def rowPortsComputes : Computes (Records.rowEncoding s a) (framedListEncoding encodingNatBool)
    (fun x => (x.1.val.factors.get x.2).2) :=
  (Records.rowComputes s a).andThen (Wiring.secondComputes encodingNatBool (framedListEncoding encodingNatBool))
def rowPortCountComputes : Computes (Records.rowEncoding s a) UnaryBinary.unaryEncoding
    (fun x => (x.1.val.factors.get x.2).2.length) :=
  (rowPortsComputes s a).andThen (Scan.lengthComputes encodingNatBool)
def addressComputes : Computes (encoding s a) encodingNatBool
    (fun p => (p.1.1.val.factors.get p.1.2).2.get p.2) := by
  let prepare : Computes (encoding s a) (ParentRowSelect.inputEncoding encodingNatBool)
      (fun p => ⟨(p.1.1.val.factors.get p.1.2).2,p.2⟩) :=
    recode (pairComputes ((rowComputes s a).andThen (rowPortsComputes s a))
      (indexComputes s a)) id (fun _ => rfl) (fun _ => rfl)
  exact prepare.andThen (ParentRowSelect.computes encodingNatBool)
def rawPort (p : Input s a) : p.1.1.val.Ports := ⟨p.1.2,p.2⟩
def variableContextComputes : Computes (encoding s a) (Counts.encoding s a)
    (fun p => (p.1.1,p.1.1.val.address (rawPort s a p))) :=
  pairComputes (sourceComputes s a) (addressComputes s a)
def degreeComputes : Computes (encoding s a) UnaryBinary.unaryEncoding
    (fun p => p.1.1.val.degree (p.1.1.val.address (rawPort s a p))) :=
  (variableContextComputes s a).andThen (Counts.degreeComputes s a)
end Ports

namespace Traversal
variable {C : Type} {s : ℕ} {a : ℕ → ℕ} (ec : Encoding C Bool)
variable (source : C → Raw.Input s a)
abbrev Row := Indexed.Input (fun c => (source c).val.factors.length)
abbrev rowEncoding := Indexed.encoding ec (fun c => (source c).val.factors.length)
def selected (x : Row source) : Records.Row s a := ⟨source x.1,x.2⟩
def selectedComputes (w : Computes ec (Raw.validatedEncoding s a) source) :
    Computes (rowEncoding ec source) (Records.rowEncoding s a) (selected source) :=
  recode (pairComputes ((Indexed.context ec _).andThen w) (Indexed.index ec _))
    id (fun _ => rfl) (fun _ => rfl)
abbrev Port := Indexed.Input (fun x : Row source => ((source x.1).val.factors.get x.2).2.length)
abbrev portEncoding := Indexed.encoding (rowEncoding ec source)
  (fun x : Row source => ((source x.1).val.factors.get x.2).2.length)
def original (p : Port source) : (source p.1.1).val.Ports := ⟨p.1.2,p.2⟩
def selectedPort (p : Port source) : Ports.Input s a := ⟨selected source p.1,p.2⟩
def selectedPortComputes (w : Computes ec (Raw.validatedEncoding s a) source) :
    Computes (portEncoding ec source) (Ports.encoding s a) (selectedPort source) :=
  recode (pairComputes ((Indexed.context (rowEncoding ec source) _).andThen
    (selectedComputes ec source w)) (Indexed.index (rowEncoding ec source) _))
    id (fun _ => rfl) (fun _ => rfl)
def contextComputes : Computes (portEncoding ec source) ec (fun p => p.1.1) :=
  (Indexed.context (rowEncoding ec source) _).andThen (Indexed.context ec _)
def rowIndexComputes : Computes (portEncoding ec source) UnaryBinary.unaryEncoding (fun p => p.1.2.val) :=
  (Indexed.context (rowEncoding ec source) _).andThen (Indexed.index ec _)
def portIndexComputes : Computes (portEncoding ec source) UnaryBinary.unaryEncoding (fun p => p.2.val) :=
  Indexed.index (rowEncoding ec source) _

/-- Two nested bounded physical traversals preserve original row/slot order. -/
def flatMap (w : Computes ec (Raw.validatedEncoding s a) source)
    (f : Port source → List Bool)
    (provider : Computes (portEncoding ec source) Frame.wordEncoding f) :
    Computes ec Frame.wordEncoding (fun c =>
      (List.finRange (source c).val.factors.length).flatMap (fun v =>
        (List.finRange ((source c).val.factors.get v).2.length).flatMap
          (fun j => f ⟨⟨c,v⟩,j⟩))) :=
  Indexed.flatMap ec _ (w.andThen (Records.rowsCountComputes s a)) _
    (Indexed.flatMap (rowEncoding ec source) _
      ((selectedComputes ec source w).andThen (Ports.rowPortCountComputes s a)) f provider)

/-- Finite histogram computed by the SAME original incidence scan. -/
def count (w : Computes ec (Raw.validatedEncoding s a) source)
    (test : Port source → Bool)
    (wt : Computes (portEncoding ec source) encodingBoolBool test) :
    Computes ec UnaryBinary.unaryEncoding (fun c =>
      ∑v : Fin (source c).val.factors.length,
        ∑j : Fin ((source c).val.factors.get v).2.length,
          if test ⟨⟨c,v⟩,j⟩ then 1 else 0) := by
  let provider := Arithmetic.choose Frame.wordEncoding test (fun _ => [true]) (fun _ => []) wt
    (constantComputes (portEncoding ec source) Frame.wordEncoding [true])
    (constantComputes (portEncoding ec source) Frame.wordEncoding [])
  refine recode (flatMap ec source w _ provider) id (fun _ => rfl) (fun c => ?_)
  change (List.finRange _).flatMap (fun v => (List.finRange _).flatMap
    (fun j => if test ⟨⟨c,v⟩,j⟩ then [true] else []))=List.replicate _ true
  have hi (v : Fin (source c).val.factors.length) :
      (List.finRange ((source c).val.factors.get v).2.length).flatMap
        (fun j => if test ⟨⟨c,v⟩,j⟩ then [true] else [])=
        List.replicate (∑j,if test ⟨⟨c,v⟩,j⟩ then 1 else 0) true := by
    calc
      _ = (List.finRange _).flatMap (fun j => List.replicate
          (if test ⟨⟨c,v⟩,j⟩ then 1 else 0) true) := by
            congr 1; funext j; cases test ⟨⟨c,v⟩,j⟩ <;> rfl
      _ = _ := by rw [Scan.tokens,←List.ofFn_eq_map,List.sum_ofFn]
  simp_rw [hi]
  rw [Scan.tokens,←List.ofFn_eq_map,List.sum_ofFn]
end Traversal

namespace Ordinal
variable {B : Type} [DecidableEq B]
theorem sorted_filter_index (before : B → B → Prop) [DecidableRel before]
    (asym : ∀x y,before x y → ¬before y x) (xs : List B)
    (hs : xs.Pairwise before) (test : B → Bool) (p : B) (hp : p∈xs) (ht : test p=true) :
    (xs.filter test).idxOf p=(xs.filter (fun q => test q && decide (before q p))).length := by
  induction xs with
  | nil => simp at hp
  | cons q qs ih =>
    obtain ⟨hq,hqs⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp hp with h|hp
    · subst q
      have hz : qs.filter (fun q => test q && decide (before q p))=[] := by
        apply List.filter_eq_nil_iff.mpr
        intro q hq'
        simp [asym p q (hq q hq')]
      have hn : ¬before p p := fun h => asym p p h h
      simp [ht,hn,hz]
    · have hqp := hq p hp
      have hne : q≠p := by intro h; subst q; exact asym p p hqp hqp
      have hi := ih hqs hp
      cases hqt : test q <;> simp [hqt,hqp,List.idxOf_cons_ne _ hne,hi]

variable {s : ℕ} {a : ℕ → ℕ}
def before (r : Raw.Input s a) (p q : r.val.Ports) : Prop :=
  p.1.val<q.1.val ∨ (p.1.val=q.1.val ∧ p.2.val<q.2.val)
instance (r : Raw.Input s a) : DecidableRel (before r) := fun p q => by unfold before; infer_instance
theorem asymmetric (r : Raw.Input s a) : ∀p q,before r p q → ¬before r q p := by
  intro p q hp hq
  unfold before at *
  omega
theorem portList_sorted (r : Raw.Input s a) : r.val.portList.Pairwise (before r) := by
  unfold Raw.portList
  apply List.pairwise_flatMap.mpr
  constructor
  · intro v hv
    apply List.pairwise_map.mpr
    exact (List.pairwise_lt_finRange _).imp (fun {j k} h => Or.inr ⟨rfl,h⟩)
  · apply (List.pairwise_lt_finRange _).imp
    intro v w hvw p hp q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
    exact Or.inl hvw
theorem grouping_count (r : Raw.Input s a) (p : r.val.Ports) :
    ((Raw.grouping r) p).2.val=
      ∑v : Fin r.val.factors.length,∑j : Fin (r.val.factors.get v).2.length,
        if r.val.address ⟨v,j⟩=r.val.address p ∧ before r ⟨v,j⟩ p then 1 else 0 := by
  rw [Raw.grouping_ordinal]
  have h := sorted_filter_index (before r) (asymmetric r) r.val.portList
    (portList_sorted r) (fun q => r.val.address q==r.val.address p) p
    (r.val.portList_complete p) (by simp)
  change (r.val.portList.filter _).idxOf p=_
  rw [h]
  unfold Raw.portList
  rw [List.filter_flatMap,List.length_flatMap]
  have count {D : Type} (xs : List D) (test : D → Bool) :
      (xs.filter test).length=(xs.map (fun b => if test b then 1 else 0)).sum := by
    induction xs with
    | nil => rfl
    | cons b bs ih => cases h : test b <;> simp [h,ih,Nat.add_comm]
  simp_rw [List.filter_map,List.length_map,count]
  simp only [Function.comp_def,id_eq,←List.ofFn_eq_map,List.sum_ofFn,beq_iff_eq,Bool.and_eq_true,decide_eq_true_eq]
end Ordinal

namespace Boolean
variable {C : Type} {ec : Encoding C Bool} {f g : C → Bool}
def combine (op : Bool → Bool → Bool) (u : Computes ec encodingBoolBool f)
    (v : Computes ec encodingBoolBool g) :
    Computes ec encodingBoolBool (fun c => op (f c) (g c)) :=
  (pairComputes u v).andThen (FiniteRecode.computes
    (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
    (fun p => op p.1 p.2) 4 (fun p => by rcases p with ⟨b,c⟩; cases b <;> cases c <;> decide))
end Boolean

namespace Ordinal
variable (s : ℕ) (a : ℕ → ℕ)
def computes : Computes (Ports.encoding s a) UnaryBinary.unaryEncoding
    (fun p => ((Raw.grouping p.1.1) (Ports.rawPort s a p)).2.val) := by
  let ec := Ports.encoding s a
  let src : Ports.Input s a → Raw.Input s a := fun p => p.1.1
  let ctx := Traversal.contextComputes ec src
  let selected := Traversal.selectedPortComputes ec src (Ports.sourceComputes s a)
  let qaddr := selected.andThen (Ports.addressComputes s a)
  let paddr := ctx.andThen (Ports.addressComputes s a)
  let qrow := (Traversal.rowIndexComputes ec src).andThen UnaryBinary.computes
  let prow := (ctx.andThen (Ports.rowIndexComputes s a)).andThen UnaryBinary.computes
  let qslot := (Traversal.portIndexComputes ec src).andThen UnaryBinary.computes
  let pslot := (ctx.andThen (Ports.indexComputes s a)).andThen UnaryBinary.computes
  let same := Arithmetic.equal qaddr paddr
  let prior := Boolean.combine Bool.or (Arithmetic.less qrow prow)
    (Boolean.combine Bool.and (Arithmetic.equal qrow prow) (Arithmetic.less qslot pslot))
  let test := Boolean.combine Bool.and same prior
  exact congrComputes (Traversal.count ec src (Ports.sourceComputes s a) _ test)
    (fun p => by
      rw [grouping_count]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Function.comp_def,id_eq,Ordinal.before,Traversal.original,Traversal.selectedPort,Ports.rawPort,
        Traversal.selected,Raw.address,decide_eq_true_eq,Bool.and_eq_true,Bool.or_eq_true]
      rfl)
end Ordinal

namespace Offset
variable (s : ℕ) (a : ℕ → ℕ)
def value (x : Counts.Context s a) : ℕ :=
  ∑i : Fin x.1.val.variables,if i.val<x.2 then (Compilation.cell x.1 i).edges else 0
abbrev Input := Indexed.Input (fun x : Counts.Context s a => x.1.val.variables)
abbrev encoding := Indexed.encoding (Counts.encoding s a)
  (fun x : Counts.Context s a => x.1.val.variables)
def selectedComputes : Computes (encoding s a) (Records.variableEncoding s a)
    (fun x => (⟨x.1.1,x.2⟩ : Records.Variable s a)) :=
  recode (pairComputes ((Indexed.context (Counts.encoding s a) (fun x : Counts.Context s a => x.1.val.variables)).andThen (Counts.sourceComputes s a))
    (Indexed.index (Counts.encoding s a) (fun x : Counts.Context s a => x.1.val.variables))) id (fun _ => rfl) (fun _ => rfl)
def computes : Computes (Counts.encoding s a) UnaryBinary.unaryEncoding (value s a) := by
  let count := (Counts.sourceComputes s a).andThen (Records.variablesComputes s a)
  let target := (Indexed.context (Counts.encoding s a) (fun x : Counts.Context s a => x.1.val.variables)).andThen (Counts.addressComputes s a)
  let index := (Indexed.index (Counts.encoding s a) (fun x : Counts.Context s a => x.1.val.variables)).andThen UnaryBinary.computes
  let chosen := Arithmetic.choose UnaryBinary.unaryEncoding _ _ _ (Arithmetic.less index target)
    ((selectedComputes s a).andThen (Counts.cellEdgesComputes s a))
    (constantComputes (encoding s a) UnaryBinary.unaryEncoding 0)
  exact congrComputes (Indexed.sum (Counts.encoding s a) _ count _ chosen)
    (fun x => by simp only [Function.comp_def,id_eq,value,decide_eq_true_eq])

theorem sum_prefix {n : ℕ} (f : Fin n → ℕ) (i : Fin n) :
    (∑j : Fin n,if j.val < i.val then f j else 0)=
      ∑j : Fin i.val,f (Fin.castLE i.isLt.le j) := by
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => Fin.castLE i.isLt.le j)
  · intro j hj; simp only [Function.comp_def,id_eq,Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_castLE]; exact j.isLt
  · intro j hj k hk he; exact Fin.ext (congrArg (fun x : Fin n => x.val) he)
  · intro j hj
    exact ⟨⟨j.val,(Finset.mem_filter.mp hj).2⟩,Finset.mem_univ _,Fin.ext rfl⟩
  · intro j hj; rfl

theorem edge_index (r : Raw.Input s a) (i : Fin r.val.variables) (e : Fin (Compilation.cell r i).edges) :
    (Compilation.edgeIndex r ⟨i,e⟩).val=value s a (r,i.val)+e.val := by
  rw [Compilation.edge_index_value,value,sum_prefix]
end Offset

namespace Literal
def endpoint {n : ℕ} (p : Fin n × Bool) : RawEndpoint := (p.1.val,p.2)
def outer (d j : ℕ) : RawEndpoint :=
  if d=2 then (0,decide (j=1)) else (j,false)
def zeroRow (j : ℕ) : RawEndpoint :=
  if j<2 then (1,decide (j=1)) else (0,decide (j=3))
def row (d v j : ℕ) : RawEndpoint :=
  if d=0 then zeroRow j else
    match EqualityTree.literalPort (d/2-2) v j with
    | .inl i => (i,true)
    | .inr (e,b) => (d+e,b)

private theorem cast_vertices {m n : ℕ} (C : Cells.Cell m) (h : m=n) :
    (C.cast h).vertices=C.vertices := by subst n; rfl
private theorem cast_outer {m n : ℕ} (C : Cells.Cell m) (h : m=n) (j : Fin n) :
    endpoint ((C.cast h).ports (.inl j))=endpoint (C.ports (.inl (Fin.cast h.symm j))) := by
  subst n; rfl
private theorem cast_row {m n : ℕ} (C : Cells.Cell m) (h : m=n)
    (v : Fin (C.cast h).vertices) (j : Fin 4) :
    endpoint ((C.cast h).ports (.inr (v,j)))=
      endpoint (C.ports (.inr (Fin.cast (cast_vertices C h) v,j))) := by
  subst n; rfl

theorem zero_row (v : Fin 1) (j : Fin 4) :
    endpoint (Cells.zero.ports (.inr (v,j)))=zeroRow j.val := by
  have hv : v=0 := Subsingleton.elim _ _
  subst v
  fin_cases j <;> rfl

theorem make_outer (d : ℕ) (hd : Even d) (j : Fin d) :
    endpoint ((Cells.make d hd).ports (.inl j))=outer d j.val := by
  change endpoint ((Cells.make d hd).ports.toFun (.inl j)) = _
  by_cases h0 : d=0
  · subst d; exact Fin.elim0 j
  · by_cases h2 : d=2
    · subst d
      fin_cases j <;> rfl
    · have hm : Cells.make d hd = (Cells.chain (d/2-2)).cast (Cells.high_degree d hd h0 h2) := by
        simp only [Cells.make,dif_neg h0,dif_neg h2]
      rw [hm]
      change endpoint (((Cells.chain (d/2-2)).cast (Cells.high_degree d hd h0 h2)).ports (.inl j)) = _
      rw [cast_outer]
      change (j.val,false)=outer d j.val
      simp only [outer,if_neg h2]

private theorem chain_row (t : ℕ) (v : Fin (t+1)) (j : Fin 4) :
    endpoint (Cells.chainPorts t (.inr (v,j)))=
      match EqualityTree.literalPort t v.val j.val with
      | .inl i => (i,true)
      | .inr (e,b) => (2*t+4+e,b) := by
  have h := EqualityTree.embed_port t ⟨v,j⟩
  change endpoint (match EqualityTree.port t ⟨v,j⟩ with
    | .inl i => (finSumFinEquiv (.inl i),true)
    | .inr (e,b) => (finSumFinEquiv (.inr e),b))=_
  rw [←h]
  cases EqualityTree.port t ⟨v,j⟩ <;> rfl

theorem make_row (d : ℕ) (hd : Even d) (v : Fin (Cells.make d hd).vertices) (j : Fin 4) :
    endpoint ((Cells.make d hd).ports (.inr (v,j)))=row d v.val j.val := by
  change endpoint ((Cells.make d hd).ports.toFun (.inr (v,j))) = _
  by_cases h0 : d=0
  · subst d
    exact zero_row v j
  · by_cases h2 : d=2
    · subst d
      exact Fin.elim0 v
    · have hm : Cells.make d hd = (Cells.chain (d/2-2)).cast (Cells.high_degree d hd h0 h2) := by
        simp only [Cells.make,dif_neg h0,dif_neg h2]
      revert v
      rw [hm]
      intro v
      change endpoint (((Cells.chain (d/2-2)).cast (Cells.high_degree d hd h0 h2)).ports (.inr (v,j))) = _
      rw [cast_row]
      change endpoint (Cells.chainPorts _ (.inr (_,j)))=row d v.val j.val
      rw [chain_row]
      have hh := Cells.high_degree d hd h0 h2
      simp only [Function.comp_def,id_eq,row,if_neg h0,Fin.val_cast]
      cases hp : EqualityTree.literalPort (d/2-2) v.val j.val with
      | inl i => rfl
      | inr q => exact congrArg (fun n => (n+q.1,q.2)) hh

variable {s : ℕ} {a : ℕ → ℕ}
def originalEndpoint (p : Ports.Input s a) : RawEndpoint :=
  let i := p.1.1.val.address (Ports.rawPort s a p)
  let e := outer (p.1.1.val.degree i) ((Raw.grouping p.1.1) (Ports.rawPort s a p)).2.val
  (Offset.value s a (p.1.1,i)+e.1,e.2)
def extraEndpoint (x : Records.Variable s a)
    (v : Fin (Compilation.cell x.1 x.2).vertices) (j : Fin 4) : RawEndpoint :=
  let e := row (x.1.val.degree x.2.val) v.val j.val
  (Offset.value s a (x.1,x.2.val)+e.1,e.2)

theorem original_route (p : Ports.Input s a) :
    endpoint (ClosedLabelling.closedPortEquiv (Compilation.shape p.1.1)
      ((Compilation.portEnumeration p.1.1).symm (.inl (Ports.rawPort s a p))))=
      originalEndpoint p := by
  rw [Compilation.original_route]
  dsimp only [Function.comp_def,id_eq,endpoint]
  rw [Offset.edge_index]
  have he := make_outer _ (p.1.1.property.2.2 _ ((Raw.grouping p.1.1) _).1.isLt)
    ((Raw.grouping p.1.1) (Ports.rawPort s a p)).2
  exact congrArg (fun e : RawEndpoint =>
    (Offset.value s a (p.1.1,((Raw.grouping p.1.1) (Ports.rawPort s a p)).1.val)+e.1,e.2)) he

theorem extra_route (x : Records.Variable s a)
    (v : Fin (Compilation.cell x.1 x.2).vertices) (j : Fin 4) :
    endpoint (ClosedLabelling.closedPortEquiv (Compilation.shape x.1)
      ((Compilation.portEnumeration x.1).symm (.inr ⟨x.2,(v,j)⟩)))=
      extraEndpoint x v j := by
  rw [Compilation.extra_route]
  dsimp only [Function.comp_def,id_eq,endpoint]
  rw [Offset.edge_index]
  have he := make_row _ (x.1.property.2.2 x.2.val x.2.isLt) v j
  unfold extraEndpoint
  rw [←he]
  rfl
end Literal

namespace Emit
variable (s : ℕ) (a : ℕ → ℕ) (j4 : Fin s)
def endpointComputes {C : Type} {ec : Encoding C Bool} {edgeId : C → ℕ} {side : C → Bool}
    (u : Computes ec encodingNatBool edgeId) (v : Computes ec encodingBoolBool side) :
    Computes ec endpointEncoding (fun c => (edgeId c,side c)) :=
  recode (pairComputes u v) id (fun _ => rfl) (fun _ => rfl)

/-- Original row endpoints use actual stable occurrence numbers. -/
def originalEndpointComputes : Computes (Ports.encoding s a) endpointEncoding Literal.originalEndpoint := by
  let degree := (Ports.degreeComputes s a).andThen UnaryBinary.computes
  let ordinal := (Ordinal.computes s a).andThen UnaryBinary.computes
  let offset := ((Ports.variableContextComputes s a).andThen (Offset.computes s a)).andThen UnaryBinary.computes
  let two := Arithmetic.equal degree (constantComputes _ encodingNatBool 2)
  let edge := Arithmetic.choose encodingNatBool _ _ _ two offset (Arithmetic.add offset ordinal)
  let side := Arithmetic.choose encodingBoolBool _ _ _ two
    (Arithmetic.equal ordinal (constantComputes _ encodingNatBool 1)) (constantComputes _ encodingBoolBool false)
  exact congrComputes (endpointComputes edge side) (fun p => by
    unfold Literal.originalEndpoint Literal.outer
    split_ifs <;> simp_all only [Function.comp_def,id_eq,decide_eq_true_eq,if_pos,if_neg,Nat.add_zero] <;> rfl)

def originalRow (x : Records.Row s a) : RawVertex :=
  ((x.1.val.factors.get x.2).1,List.ofFn (fun j => Literal.originalEndpoint (⟨x,j⟩ : Ports.Input s a)))
def originalRowComputes : Computes (Records.rowEncoding s a) vertexEncoding (originalRow s a) := by
  let ports := Indexed.flatMap (Records.rowEncoding s a) _ (Ports.rowPortCountComputes s a) _
    ((originalEndpointComputes s a).andThen (Compiler.entryComputes endpointEncoding))
  let portList : Computes (Records.rowEncoding s a) (framedListEncoding endpointEncoding)
      (fun x => List.ofFn (fun j => Literal.originalEndpoint (⟨x,j⟩ : Ports.Input s a))) :=
    recode (Compiler.joinComputes ports (constantComputes _ Frame.wordEncoding [false])) id
      (fun _ => rfl) (fun x => by
        change (List.finRange _).flatMap (fun j => Compiler.entry endpointEncoding
          (Literal.originalEndpoint ⟨x,j⟩)) ++ [false]=_
        have h := Compiler.entries_append_encode endpointEncoding
          ((List.finRange (x.1.val.factors.get x.2).2.length).map
            (fun j => Literal.originalEndpoint (⟨x,j⟩ : Ports.Input s a))) []
        simpa only [Compiler.entries,List.ofFn_eq_map,List.flatMap_map,Function.comp_def,List.append_nil,
          framedListEncoding,framedListEncode] using h)
  let label := (Records.rowComputes s a).andThen
    (Wiring.firstComputes encodingNatBool (framedListEncoding encodingNatBool))
  exact recode (pairComputes label portList) id (fun _ => rfl) (fun _ => rfl)

abbrev Node := Indexed.Input (fun x : Records.Variable s a => (Compilation.cell x.1 x.2).vertices)
abbrev nodeEncoding := Indexed.encoding (Records.variableEncoding s a)
  (fun x : Records.Variable s a => (Compilation.cell x.1 x.2).vertices)
def nodeContextComputes : Computes (nodeEncoding s a) (Records.variableEncoding s a) (fun x => x.1) :=
  Indexed.context _ _
def nodeIndexComputes : Computes (nodeEncoding s a) UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  Indexed.index _ _

/-- Four finite pieces of syntax implement the stored Eq4 slot order. -/
def extraEndpointComputes (j : Fin 4) : Computes (nodeEncoding s a) endpointEncoding
    (fun x => Literal.extraEndpoint x.1 x.2 j) := by
  let ec := nodeEncoding s a
  let context := nodeContextComputes s a
  let degreeUnary := context.andThen (Counts.variableDegreeComputes s a)
  let degree := degreeUnary.andThen UnaryBinary.computes
  let offset := ((context.andThen (Counts.variableContextComputes s a)).andThen
    (Offset.computes s a)).andThen UnaryBinary.computes
  let vertex := (nodeIndexComputes s a).andThen UnaryBinary.computes
  let t := ((degreeUnary.andThen Half.computes).andThen
    UniversalPairReduction.SmoothingCompiler.Endpoints.unaryPredecessorComputes).andThen
    (UniversalPairReduction.SmoothingCompiler.Endpoints.unaryPredecessorComputes.andThen UnaryBinary.computes)
  let fixed (n : ℕ) := constantComputes ec encodingNatBool n
  let side (b : Bool) := constantComputes ec encodingBoolBool b
  let internal := Arithmetic.add (Arithmetic.add offset degree) vertex
  let high : Computes ec endpointEncoding (fun x =>
      let e := match EqualityTree.literalPort (x.1.1.val.degree x.1.2.val/2-2) x.2.val j.val with
        | .inl i => (i,true)
        | .inr (e,b) => (x.1.1.val.degree x.1.2.val+e,b)
      (Offset.value s a (x.1.1,x.1.2.val)+e.1,e.2)) := by
    by_cases h0 : j.val=0
    · let isFirst := Arithmetic.equal vertex (fixed 0)
      let previous := Arithmetic.add (Arithmetic.add offset degree) (Arithmetic.subtract vertex (fixed 1))
      exact congrComputes (Arithmetic.choose endpointEncoding _ _ _ isFirst
        (endpointComputes offset (side true)) (endpointComputes previous (side true)))
        (fun x => by simp [EqualityTree.literalPort,h0]; split_ifs <;> simp_all [Nat.add_assoc])
    · by_cases h1 : j.val=1
      · exact congrComputes (endpointComputes
          (Arithmetic.add offset (Arithmetic.add (Arithmetic.add vertex vertex) (fixed 1))) (side true))
          (fun x => by simp [EqualityTree.literalPort,h0,h1]; congr 1; omega)
      · by_cases h2 : j.val=2
        · exact congrComputes (endpointComputes
            (Arithmetic.add offset (Arithmetic.add (Arithmetic.add vertex vertex) (fixed 2))) (side true))
            (fun x => by simp [EqualityTree.literalPort,h0,h1,h2]; congr 1; omega)
        · let isLast := Arithmetic.equal vertex t
          let last := Arithmetic.add offset (Arithmetic.add (Arithmetic.add t t) (fixed 3))
          exact congrComputes (Arithmetic.choose endpointEncoding _ _ _ isLast
            (endpointComputes last (side true)) (endpointComputes internal (side false)))
            (fun x => by
              simp [EqualityTree.literalPort,h0,h1,h2,Nat.sub_sub,Function.comp_def]
              split_ifs <;> simp_all [Nat.add_assoc] <;> omega)
  let zero := endpointComputes (Arithmetic.add offset (fixed (Literal.zeroRow j.val).1))
    (side (Literal.zeroRow j.val).2)
  exact congrComputes (Arithmetic.choose endpointEncoding _ _ _
    (Arithmetic.equal degree (fixed 0)) zero high)
    (fun x => by unfold Literal.extraEndpoint Literal.row; split_ifs <;> simp_all)

def extraRow (x : Node s a) : RawVertex :=
  (j4.val,List.ofFn (fun j => Literal.extraEndpoint x.1 x.2 j))
def extraRowComputes : Computes (nodeEncoding s a) vertexEncoding (extraRow s a j4) := by
  let ports := Compiler.fixedListComputes (nodeEncoding s a) endpointEncoding
    (fun x j => Literal.extraEndpoint x.1 x.2 j) (extraEndpointComputes s a) (List.finRange 4)
  exact recode (pairComputes (constantComputes (nodeEncoding s a) encodingNatBool j4.val)
    (congrComputes ports (fun x => List.ofFn_eq_map.symm))) id (fun _ => rfl) (fun _ => rfl)

def originalVertices (r : Raw.Input s a) : List RawVertex :=
  (List.finRange r.val.factors.length).map (fun v => originalRow s a ⟨r,v⟩)
def extraVertices (r : Raw.Input s a) : List RawVertex :=
  (List.finRange r.val.variables).flatMap (fun i =>
    (List.finRange (Compilation.cell r i).vertices).map (fun v => extraRow s a j4 ⟨⟨r,i⟩,v⟩))
def vertices (r : Raw.Input s a) := originalVertices s a r ++ extraVertices s a j4 r
def raw (r : Raw.Input s a) : RawClosedNetwork :=
  ⟨vertices s a j4 r,List.replicate (Compilation.edgeCount r) 0⟩

def originalEntriesComputes : Computes (Raw.validatedEncoding s a) Frame.wordEncoding
    (fun r => Compiler.entries vertexEncoding (originalVertices s a r)) :=
  congrComputes (Records.rowsFlatMap s a _ ((originalRowComputes s a).andThen
    (Compiler.entryComputes vertexEncoding))) (fun r => by
      simp only [Function.comp_def,id_eq,originalVertices,Compiler.entries,List.flatMap_map,Function.comp_def])
def extraEntriesComputes : Computes (Raw.validatedEncoding s a) Frame.wordEncoding
    (fun r => Compiler.entries vertexEncoding (extraVertices s a j4 r)) := by
  let node := (extraRowComputes s a j4).andThen (Compiler.entryComputes vertexEncoding)
  let block := Indexed.flatMap (Records.variableEncoding s a) _ (Counts.cellNodesComputes s a) _ node
  exact congrComputes (Records.variablesFlatMap s a _ block) (fun r => by
    simp only [Function.comp_def,id_eq,extraVertices,Compiler.entries,List.flatMap_assoc,List.flatMap_map,Function.comp_def])
def verticesComputes : Computes (Raw.validatedEncoding s a) (framedListEncoding vertexEncoding)
    (vertices s a j4) :=
  recode (Compiler.joinComputes (Compiler.joinComputes (originalEntriesComputes s a)
    (extraEntriesComputes s a j4)) (constantComputes _ Frame.wordEncoding [false])) id
    (fun _ => rfl) (fun r => by
      change (Compiler.entries vertexEncoding (originalVertices s a r) ++
        Compiler.entries vertexEncoding (extraVertices s a j4 r)) ++ [false]=_
      have h : Compiler.entries vertexEncoding (originalVertices s a r) ++
          Compiler.entries vertexEncoding (extraVertices s a j4 r)=Compiler.entries vertexEncoding (vertices s a j4 r) := by
        simp only [Function.comp_def,id_eq,vertices,Compiler.entries,List.flatMap_append]
      rw [h]
      simpa only [List.append_nil,framedListEncoding,framedListEncode] using
        Compiler.entries_append_encode vertexEncoding (vertices s a j4 r) [])
def edgesComputes : Computes (Raw.validatedEncoding s a) (framedListEncoding encodingNatBool)
    (fun r => List.replicate (Compilation.edgeCount r) 0) := by
  let tokens := Indexed.flatMap (Raw.validatedEncoding s a) Compilation.edgeCount
    (Counts.totalEdgesComputes s a) (fun _ => Compiler.entry encodingNatBool 0)
    (constantComputes (Indexed.encoding (Raw.validatedEncoding s a) Compilation.edgeCount)
      Frame.wordEncoding (Compiler.entry encodingNatBool 0))
  exact recode (Compiler.joinComputes tokens (constantComputes _ Frame.wordEncoding [false])) id
    (fun _ => rfl) (fun r => by
      change (List.finRange _).flatMap (fun _ => Compiler.entry encodingNatBool 0) ++ [false]=_
      have h : (List.finRange (Compilation.edgeCount r)).map (fun _ => (0 : ℕ))=
          List.replicate (Compilation.edgeCount r) 0 := by simp only [Function.comp_def,id_eq,List.map_const',List.length_finRange]
      have he := Compiler.entries_append_encode encodingNatBool
        ((List.finRange (Compilation.edgeCount r)).map (fun _ => (0 : ℕ))) []
      rw [←h]
      simpa only [Compiler.entries,List.flatMap_map,Function.comp_def,id_eq,List.append_nil,framedListEncoding,framedListEncode] using he)
def rawComputes : Computes (Raw.validatedEncoding s a) RawClosedNetwork.encoding (raw s a j4) :=
  recode (pairComputes (verticesComputes s a j4) (edgesComputes s a)) id
    (fun _ => rfl) (fun _ => rfl)
end Emit

namespace RecordsIdentity
variable {D : Type}
private theorem sigma_castSucc {m : ℕ} (n : Fin (m+1) → ℕ)
    (i : Fin m) (j : Fin (n i.castSucc)) :
    (finSigmaFinEquiv ⟨i.castSucc,j⟩ : Fin (∑k,n k))=
      Fin.cast (Fin.sum_univ_castSucc n).symm
        (Fin.castAdd (n (Fin.last m))
          (finSigmaFinEquiv (n:=fun i => n i.castSucc) ⟨i,j⟩)) := by
  apply Fin.ext
  simp only [Function.comp_def,id_eq,finSigmaFinEquiv_apply,Fin.val_castSucc,Fin.val_cast,Fin.val_castAdd]
  congr 1
private theorem sigma_last {m : ℕ} (n : Fin (m+1) → ℕ) (j : Fin (n (Fin.last m))) :
    (finSigmaFinEquiv ⟨Fin.last m,j⟩ : Fin (∑k,n k))=
      Fin.cast (Fin.sum_univ_castSucc n).symm
        (Fin.natAdd (∑i : Fin m,n i.castSucc) j) := by
  apply Fin.ext
  simp only [Function.comp_def,id_eq,finSigmaFinEquiv_apply,Fin.val_last,Fin.val_cast,Fin.val_natAdd]
  congr 1

/-- This is ordered list equality, stronger than a permutation of rows. -/
theorem sigma_rows {m : ℕ} (n : Fin m → ℕ) (f : Fin (∑i,n i) → D) :
    List.ofFn f=(List.finRange m).flatMap (fun i =>
      List.ofFn (fun j : Fin (n i) => f (finSigmaFinEquiv ⟨i,j⟩))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_congr (Fin.sum_univ_castSucc n) f,List.ofFn_add]
    rw [ih (fun i : Fin m => n i.castSucc)]
    rw [List.finRange_succ_last,List.flatMap_append,List.flatMap_map,List.flatMap_singleton]
    congr 1
    · congr 1
      funext i
      congr 1
      funext j
      rw [sigma_castSucc]
      rfl
    · congr 1
      funext j
      rw [sigma_last]

theorem sum_rows {m n : ℕ} (f : Fin (m+n) → D) :
    List.ofFn f=List.ofFn (fun i : Fin m => f (finSumFinEquiv (.inl i))) ++
      List.ofFn (fun j : Fin n => f (finSumFinEquiv (.inr j))) := by
  rw [List.ofFn_add]
  rfl

variable {s : ℕ} {a : ℕ → ℕ} {K : Type*} [CommSemiring K]
variable (G : (i : Fin s) → Signature K (a i.val)) (j4 : Fin s)
variable (h4 : (⟨a j4.val,G j4⟩ : AnySignature K)=
  ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
def storedRow (r : Raw.Input s a) (v : Fin (Compilation.vertexCount r)) : RawVertex :=
  (((Compilation.labelling r G j4 h4).vertex v).val,
    List.ofFn (fun j => Literal.endpoint (ClosedLabelling.closedPortEquiv (Compilation.shape r) ⟨v,j⟩)))

theorem original_row (r : Raw.Input s a) (v : Fin r.val.factors.length) :
    storedRow G j4 h4 r (Compilation.vertexIndex r (.inl v))=Emit.originalRow s a ⟨r,v⟩ := by
  apply Prod.ext
  · simp only [Function.comp_def,id_eq,storedRow,Compilation.labelling,Equiv.symm_apply_apply,Sum.elim_inl]
    rfl
  · change List.ofFn (fun j => Literal.endpoint (ClosedLabelling.closedPortEquiv
      (Compilation.shape r) ⟨Compilation.vertexIndex r (.inl v),j⟩))=_
    rw [List.ofFn_congr (Compilation.original_arity r v)]
    congr 1
    funext j
    rw [←Compilation.original_ordered_port]
    exact Literal.original_route (⟨⟨r,v⟩,j⟩ : Ports.Input s a)

theorem extra_row (r : Raw.Input s a) (i : Fin r.val.variables)
    (v : Fin (Compilation.cell r i).vertices) :
    storedRow G j4 h4 r (Compilation.vertexIndex r (.inr ⟨i,v⟩))=
      Emit.extraRow s a j4 ⟨⟨r,i⟩,v⟩ := by
  apply Prod.ext
  · simp only [Function.comp_def,id_eq,storedRow,Compilation.labelling,Equiv.symm_apply_apply,Sum.elim_inr]
    rfl
  · change List.ofFn (fun j => Literal.endpoint (ClosedLabelling.closedPortEquiv
      (Compilation.shape r) ⟨Compilation.vertexIndex r (.inr ⟨i,v⟩),j⟩))=_
    rw [List.ofFn_congr (Compilation.extra_arity r i v)]
    congr 1
    funext j
    rw [←Compilation.extra_ordered_port]
    exact Literal.extra_route ⟨r,i⟩ v j

private theorem raw_ext {r q : RawClosedNetwork}
    (vertices : r.vertices=q.vertices) (edges : r.edges=q.edges) : r=q := by
  cases r
  cases q
  cases vertices
  cases edges
  rfl

/-- The machine's emitted bytes are exactly the existing validated query,
including its original zero-loop order and all nullary rows. -/
theorem raw_eq (r : Raw.Input s a) : Emit.raw s a j4 r=Compilation.raw r G j4 h4 := by
  apply raw_ext
  · symm
    change List.ofFn (storedRow G j4 h4 r)=Emit.vertices s a j4 r
    rw [sum_rows,sigma_rows (fun i : Fin r.val.variables => (Compilation.cell r i).vertices)]
    change List.ofFn (fun v => storedRow G j4 h4 r (Compilation.vertexIndex r (.inl v))) ++
      (List.finRange r.val.variables).flatMap (fun i => List.ofFn (fun v =>
        storedRow G j4 h4 r (Compilation.vertexIndex r (.inr ⟨i,v⟩))))=_
    simp_rw [original_row,extra_row]
    simp only [Function.comp_def,id_eq,Emit.vertices,Emit.originalVertices,Emit.extraVertices,List.ofFn_eq_map]
  · change List.replicate (Compilation.edgeCount r) 0=List.ofFn (fun _ : Fin (Compilation.edgeCount r) => (0 : ℕ))
    simp
end RecordsIdentity

section Query
variable {s : ℕ} {a : ℕ → ℕ} {K : Type*} [CommSemiring K]
variable (G : (i : Fin s) → Signature K (a i.val)) (j4 : Fin s)
variable (h4 : (⟨a j4.val,G j4⟩ : AnySignature K)=
  ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)

/-- Uniform raw CSP bits to the SAME existing ordered ordinary Eq4 graph.
Only G's real Eq4 row is mathematical input at this generic internal layer;
Source supplies it internally from the actual original-family anchor. -/
def computes : Computes (Raw.validatedEncoding s a) (RawClosedNetwork.validatedEncoding s 1 a)
    (fun r => Compilation.query r G j4 h4) :=
  recode (Emit.rawComputes s a j4) id (fun _ => rfl) (fun r =>
    congrArg RawClosedNetwork.encoding.encode (RecordsIdentity.raw_eq G j4 h4 r))

def bitBound := (computes G j4 h4).outputBound
def primitiveBound := primitivePolynomial (computes G j4 h4)
theorem output_bits (r : Raw.Input s a) :
    ((RawClosedNetwork.validatedEncoding s 1 a).encode (Compilation.query r G j4 h4)).length≤
      (bitBound G j4 h4).bound.eval ((Raw.validatedEncoding s a).encode r).length :=
  (computes G j4 h4).outputBound.length_le r
theorem primitive_cost (r : Raw.Input s a) :
    primitiveCost (computes G j4 h4).machine ((computes G j4 h4).outputs r).steps
      (some (Turing.initList (computes G j4 h4).machine.computer ((Raw.validatedEncoding s a).encode r)))≤
      (primitiveBound G j4 h4).eval ((Raw.validatedEncoding s a).encode r).length :=
  computes_primitive_cost (computes G j4 h4) r
end Query
end Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Program
end
