import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.System


namespace Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.Guard
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
open Holant.LocalDrafts.Tractability.AffineMachine

def sub (c u v : List ℚ) : List ℚ := Coordinates.add c.length u (Coordinates.scale (-1) v)
def value (c : List ℚ) (x : List (List ℚ)) : List ℚ :=
  sub c (Coordinates.mul c (x.getD 4 [])
    (sub c (Coordinates.mul c (x.getD 0 []) (x.getD 3 []))
      (Coordinates.mul c (x.getD 1 []) (x.getD 2 [])))) (Coordinates.unit c.length)
def check (c : List ℚ) (x : List (List ℚ)) : Bool := Coordinates.isZero (value c x)

theorem sub_ofFn {d : ℕ} (c u v : PowerArithmetic.Vector d) :
    sub (List.ofFn c) (List.ofFn u) (List.ofFn v) = List.ofFn (u-v) := by
  simp only [sub,List.length_ofFn,Coordinates.scale_ofFn,Coordinates.add_ofFn,
    neg_one_smul,sub_eq_add_neg]

theorem check_ofFn {d k : ℕ} (c : PowerArithmetic.Vector d) (x : MatrixWitness.Candidate d k) :
    check (List.ofFn c) (List.ofFn (fun i => List.ofFn (x i))) = MatrixWitness.checkGuard c x := by
  have hx (i : Fin 5) : (List.ofFn (fun j => List.ofFn (x j))).getD i.val [] =
      List.ofFn (x (Fin.castAdd k i)) := getD_ofFn _ (Fin.castAdd k i) []
  have h0 : (List.ofFn (fun j => List.ofFn (x j))).getD 0 [] =
      List.ofFn (x (Fin.castAdd k (0 : Fin 5))) := hx (0 : Fin 5)
  have h1 : (List.ofFn (fun j => List.ofFn (x j))).getD 1 [] =
      List.ofFn (x (Fin.castAdd k (1 : Fin 5))) := hx (1 : Fin 5)
  have h2 : (List.ofFn (fun j => List.ofFn (x j))).getD 2 [] =
      List.ofFn (x (Fin.castAdd k (2 : Fin 5))) := hx (2 : Fin 5)
  have h3 : (List.ofFn (fun j => List.ofFn (x j))).getD 3 [] =
      List.ofFn (x (Fin.castAdd k (3 : Fin 5))) := hx (3 : Fin 5)
  have h4 : (List.ofFn (fun j => List.ofFn (x j))).getD 4 [] =
      List.ofFn (x (Fin.castAdd k (4 : Fin 5))) := hx (4 : Fin 5)
  simp only [check,value,h0,h1,h2,h3,h4,
    List.length_ofFn,Coordinates.mul_ofFn,sub_ofFn,Coordinates.unit_ofFn,Coordinates.isZero_ofFn]
  rfl

noncomputable section
def subComputes : Computes Multiplication.encoding coordinatesEncoding (fun p => sub p.1 p.2.1 p.2.2) := by
  let c := Wiring.firstComputes coordinatesEncoding Companion.shiftEncoding
  let rest := Wiring.secondComputes coordinatesEncoding Companion.shiftEncoding
  let u := rest.andThen (Wiring.firstComputes coordinatesEncoding coordinatesEncoding)
  let v := rest.andThen (Wiring.secondComputes coordinatesEncoding coordinatesEncoding)
  let neg := (pairComputes (constantComputes Multiplication.encoding rationalEncoding (-1)) v).andThen
    CoordinatePrimitives.scale
  exact (pairComputes c (pairComputes u neg)).andThen CoordinatePrimitives.addUsingRelation

abbrev encoding := pairEncoding coordinatesEncoding vectorsEncoding
def executes : Executes encoding encodingBoolBool (fun p => check p.1 p.2) := by
  let c := Executes.ofComputes (Wiring.firstComputes coordinatesEncoding vectorsEncoding)
  let xs := Wiring.secondComputes coordinatesEncoding vectorsEncoding
  let x (i : ℕ) := Executes.ofComputes (AccessPrograms.get coordinatesEncoding [] xs
    (constantComputes encoding UnaryBinary.unaryEncoding i))
  let p03 := (c.pair ((x 0).pair (x 3))).comp Multiplication.mul
  let p12 := (c.pair ((x 1).pair (x 2))).comp Multiplication.mul
  let det := (c.pair (p03.pair p12)).comp (Executes.ofComputes subComputes)
  let zdet := (c.pair ((x 4).pair det)).comp Multiplication.mul
  let one := c.comp (Executes.ofComputes Companion.unit)
  exact ((c.pair (zdet.pair one)).comp (Executes.ofComputes subComputes)).comp
    (Executes.ofComputes CoordinatePrimitives.zero)
end
end Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.Guard
