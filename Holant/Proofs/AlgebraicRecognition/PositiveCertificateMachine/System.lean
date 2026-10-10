import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.RightFold


namespace Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.SystemMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
open Holant.LocalDrafts.Tractability.AffineMachine

def powers (c : List ℚ) (x : List (List ℚ)) (ns : List ℕ) : List (List ℚ) :=
  Coordinates.tab ns.length (fun i => Coordinates.powerAt c (x.getD i []) (ns.getD i 0))
def product (c : List ℚ) (vs : List (List ℚ)) : List ℚ :=
  vs.foldr (Coordinates.mul c) (Coordinates.unit c.length)
abbrev Context := List ℚ × (List (List ℚ) × List (List ℚ))
abbrev contextEncoding := pairEncoding coordinatesEncoding (pairEncoding vectorsEncoding vectorsEncoding)
def term (a : Context) (t : Term) : List ℚ :=
  Coordinates.mul a.1 (a.2.1.getD t.1 []) (product a.1 (powers a.1 a.2.2 t.2))
def equation (a : Context) (e : Equation) : List ℚ :=
  Coordinates.sum a.1.length (e.map (term a))
def check (a : Context) (s : System) : Bool := s.all (fun e => Coordinates.isZero (equation a e))

theorem powers_ofFn {d n : ℕ} (c : PowerArithmetic.Vector d)
    (x : Fin n → PowerArithmetic.Vector d) (ns : Fin n → ℕ) :
    powers (List.ofFn c) (List.ofFn (fun i => List.ofFn (x i))) (List.ofFn ns) =
      List.ofFn (fun i => List.ofFn (FixedSystem.powerCode (PowerArithmetic.data c) (x i) (ns i))) := by
  simp only [powers,List.length_ofFn,Coordinates.tab_ofFn,getD_ofFn,Coordinates.powerAt_ofFn]

theorem product_ofFn {d n : ℕ} (c : PowerArithmetic.Vector d)
    (v : Fin n → PowerArithmetic.Vector d) :
    product (List.ofFn c) (List.ofFn (fun i => List.ofFn (v i))) =
      List.ofFn (FixedSystem.productCode (PowerArithmetic.data c) n v) := by
  induction n with
  | zero => simp [product,FixedSystem.productCode,PowerArithmetic.data]
  | succ n ih =>
    rw [List.ofFn_succ (f := fun i => List.ofFn (v i))]
    change Coordinates.mul (List.ofFn c) (List.ofFn (v 0))
      (product (List.ofFn c) (List.ofFn (fun i => List.ofFn (Fin.tail v i)))) = _
    rw [ih,Coordinates.mul_ofFn]
    rfl

theorem term_ofFn {d m n : ℕ} (c : PowerArithmetic.Vector d)
    (coeff : Fin m → PowerArithmetic.Vector d) (x : Fin n → PowerArithmetic.Vector d)
    (t : EncodedSystem.Term m n) :
    term (List.ofFn c,List.ofFn (fun i => List.ofFn (coeff i)),List.ofFn (fun i => List.ofFn (x i)))
      (encodeTerm t) = List.ofFn (FixedSystem.evalTerm (PowerArithmetic.data c) x (coeff t.1,t.2)) := by
  simp only [term,encodeTerm,getD_ofFn,powers_ofFn,product_ofFn,Coordinates.mul_ofFn,FixedSystem.evalTerm]

theorem equation_ofFn {d m n : ℕ} (c : PowerArithmetic.Vector d)
    (coeff : Fin m → PowerArithmetic.Vector d) (x : Fin n → PowerArithmetic.Vector d)
    (e : EncodedSystem.Equation m n) :
    equation (List.ofFn c,List.ofFn (fun i => List.ofFn (coeff i)),List.ofFn (fun i => List.ofFn (x i)))
      (e.map encodeTerm) =
      List.ofFn (FixedSystem.evalEquation (PowerArithmetic.data c) x (EncodedSystem.materialize coeff e)) := by
  induction e with
  | nil => simp [equation,Coordinates.sum,Coordinates.zero,EncodedSystem.materialize,FixedSystem.evalEquation,
      Coordinates.tab_ofFn]
  | cons t ts ih =>
    simp only [List.map_cons,equation,Coordinates.sum_cons,term_ofFn,List.length_ofFn] at *
    rw [ih,Coordinates.add_ofFn]
    rfl

theorem check_ofFn {d m n : ℕ} (c : PowerArithmetic.Vector d)
    (coeff : Fin m → PowerArithmetic.Vector d) (x : Fin n → PowerArithmetic.Vector d)
    (s : EncodedSystem.System m n) :
    check (List.ofFn c,List.ofFn (fun i => List.ofFn (coeff i)),List.ofFn (fun i => List.ofFn (x i)))
      (encodeSystem s) =
      FixedSystem.checkSystem (PowerArithmetic.data c) (s.map (EncodedSystem.materialize coeff)) x := by
  simp only [check,encodeSystem,List.all_map,Function.comp_def,equation_ofFn,Coordinates.isZero_ofFn,
    CommonFieldCheck.zero,FixedSystem.checkSystem]

noncomputable section
abbrev powersEncoding := pairEncoding (pairEncoding coordinatesEncoding vectorsEncoding) naturalsEncoding

def powerCell : Executes (pairEncoding powersEncoding UnaryBinary.unaryEncoding) coordinatesEncoding
    (fun p => Coordinates.powerAt p.1.1.1 (p.1.1.2.getD p.2 []) (p.1.2.getD p.2 0)) := by
  let p := Wiring.firstComputes powersEncoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes powersEncoding UnaryBinary.unaryEncoding
  let cx := p.andThen (Wiring.firstComputes (pairEncoding coordinatesEncoding vectorsEncoding) naturalsEncoding)
  let c := cx.andThen (Wiring.firstComputes coordinatesEncoding vectorsEncoding)
  let x := cx.andThen (Wiring.secondComputes coordinatesEncoding vectorsEncoding)
  let ns := p.andThen (Wiring.secondComputes (pairEncoding coordinatesEncoding vectorsEncoding) naturalsEncoding)
  let v := AccessPrograms.get coordinatesEncoding [] x i
  let n := AccessPrograms.get encodingNatBool 0 ns i
  exact (Executes.ofComputes (pairComputes (pairComputes c v) n)).comp Multiplication.powerAt

def powersExecutes : Executes powersEncoding vectorsEncoding (fun p => powers p.1.1 p.1.2 p.2) :=
  Executes.tabulate powersEncoding coordinatesEncoding (fun p => p.2.length)
    ((Wiring.secondComputes (pairEncoding coordinatesEncoding vectorsEncoding) naturalsEncoding).andThen
      (WireLists.lengthComputes encodingNatBool)) _ powerCell

def productExecutes : Executes (pairEncoding coordinatesEncoding vectorsEncoding) coordinatesEncoding
    (fun p => product p.1 p.2) := by
  let c := Wiring.firstComputes coordinatesEncoding vectorsEncoding
  let vs := Wiring.secondComputes coordinatesEncoding vectorsEncoding
  let prepare := Executes.ofComputes (pairComputes c (pairComputes vs (c.andThen Companion.unit)))
  exact prepare.comp (RightFold.executes coordinatesEncoding coordinatesEncoding coordinatesEncoding
    Coordinates.mul [] Multiplication.mul)

abbrev termInputEncoding := pairEncoding contextEncoding termEncoding
def termExecutes : Executes termInputEncoding coordinatesEncoding (fun p => term p.1 p.2) := by
  let a := Wiring.firstComputes contextEncoding termEncoding
  let t := Wiring.secondComputes contextEncoding termEncoding
  let c := a.andThen (Wiring.firstComputes coordinatesEncoding (pairEncoding vectorsEncoding vectorsEncoding))
  let rest := a.andThen (Wiring.secondComputes coordinatesEncoding (pairEncoding vectorsEncoding vectorsEncoding))
  let coeff := rest.andThen (Wiring.firstComputes vectorsEncoding vectorsEncoding)
  let x := rest.andThen (Wiring.secondComputes vectorsEncoding vectorsEncoding)
  let index := t.andThen (Wiring.firstComputes encodingNatBool naturalsEncoding)
  let ns := t.andThen (Wiring.secondComputes encodingNatBool naturalsEncoding)
  let unary := (Executes.ofComputes index).comp RightFold.binaryToUnary
  let coefficient := ((Executes.ofComputes coeff).pair unary).comp
    (Executes.ofComputes (WireLists.getD coordinatesEncoding []))
  let ps := (Executes.ofComputes (pairComputes (pairComputes c x) ns)).comp powersExecutes
  let prod := ((Executes.ofComputes c).pair ps).comp productExecutes
  exact ((Executes.ofComputes c).pair (coefficient.pair prod)).comp Multiplication.mul

abbrev equationInputEncoding := pairEncoding contextEncoding equationEncoding
def equationExecutes : Executes equationInputEncoding coordinatesEncoding (fun p => equation p.1 p.2) := by
  let terms := Executes.mapList contextEncoding termEncoding coordinatesEncoding term termExecutes
  let n := ((Wiring.firstComputes contextEncoding equationEncoding).andThen
    (Wiring.firstComputes coordinatesEncoding (pairEncoding vectorsEncoding vectorsEncoding))).andThen
      (WireLists.lengthComputes rationalEncoding)
  exact ((Executes.ofComputes n).pair terms).comp Companion.sum

def systemExecutes : Executes (pairEncoding contextEncoding systemEncoding) encodingBoolBool
    (fun p => check p.1 p.2) :=
  ((Executes.mapList contextEncoding equationEncoding encodingBoolBool
    (fun a e => Coordinates.isZero (equation a e))
    (equationExecutes.comp (Executes.ofComputes CoordinatePrimitives.zero))).comp
      (Executes.ofComputes CoordinatePrimitives.allTrue)).congr
        (fun p => by simp only [check,List.all_map,Function.comp_def,id_eq])

end
end Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.SystemMachine
