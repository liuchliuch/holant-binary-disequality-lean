import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.RationalInputMachine.Correspondence
import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.RightFold
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.SparsePrograms


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalSparseMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Term := RationalInputMachine.Term
abbrev Poly := RationalInputMachine.Row
abbrev termEncoding := RationalInputMachine.termEncoding
abbrev encoding := RationalInputMachine.rowEncoding
abbrev familyEncoding := RationalInputMachine.bodyEncoding
abbrev pairEncoding := FixedFieldMachines.pairEncoding encoding encoding

def neg (p : Poly) : Poly := p.map (fun t => (t.1,-t.2))
def sub (p q : Poly) : Poly := p ++ neg q
def termProduct (t u : Term) : Term :=
  (NegativeCertificateMachine.addExponent t.1 u.1,t.2*u.2)
def mul (p q : Poly) : Poly := p.flatMap (fun t => q.map (termProduct t))
def one (n : ℕ) : Poly := [(RationalInputMachine.zero n,1)]
def «variable» (n j : ℕ) : Poly := [(RationalInputMachine.hit n j,1)]
def product (n : ℕ) (ps : List Poly) : Poly := ps.foldr mul (one n)

theorem termProduct_wire {n : ℕ} (a b : Sparse.Term n 1) :
    termProduct (RationalInputMachine.termWire a) (RationalInputMachine.termWire b) =
      RationalInputMachine.termWire (a.1+b.1,RationalCompiler.data.mulCode a.2 b.2) := by
  apply Prod.ext
  · exact NegativeCertificateMachine.addExponent_ofFn a.1 b.1
  · simp [termProduct,RationalInputMachine.termWire,ArithmeticData.mulCode,
      RationalCompiler.data,Fin.sum_univ_succ]

theorem mul_wire {n : ℕ} (p q : Sparse.Poly n 1) :
    mul (RationalInputMachine.rowWire p) (RationalInputMachine.rowWire q) =
      RationalInputMachine.rowWire (Sparse.mul RationalCompiler.data p q) := by
  simp only [mul,RationalInputMachine.rowWire,Sparse.mul,Sparse.termMul,
    List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def,termProduct_wire]

theorem neg_wire {n : ℕ} (p : Sparse.Poly n 1) :
    neg (RationalInputMachine.rowWire p)=RationalInputMachine.rowWire (Sparse.neg p) := by
  simp only [neg,RationalInputMachine.rowWire,Sparse.neg,List.map_map,
    RationalInputMachine.termWire,Pi.neg_apply,Function.comp_def]

theorem sub_wire {n : ℕ} (p q : Sparse.Poly n 1) :
    sub (RationalInputMachine.rowWire p) (RationalInputMachine.rowWire q) =
      RationalInputMachine.rowWire (Sparse.sub p q) := by
  rw [sub,neg_wire]
  simp only [Sparse.sub,Sparse.add,RationalInputMachine.rowWire,List.map_append]

theorem one_wire (n : ℕ) : one n=RationalInputMachine.rowWire (Sparse.one (v:=n) RationalCompiler.data) := by
  simp [one,RationalInputMachine.zero,RationalInputMachine.rowWire,
    RationalInputMachine.termWire,Sparse.one,RationalCompiler.data]
  exact (List.ofFn_const n (0 : ℕ)).symm

theorem variable_wire {n : ℕ} (j : Fin n) :
    «variable» n j.val=RationalInputMachine.rowWire (SparseTransform.variableCode RationalCompiler.data j) := by
  simp [«variable»,RationalInputMachine.hit_ofFn,RationalInputMachine.rowWire,
    RationalInputMachine.termWire,SparseTransform.variableCode,RationalCompiler.data,
    EncodedGuard.hit]
  rfl

theorem product_wire {n : ℕ} (ps : List (Sparse.Poly n 1)) :
    product n (ps.map RationalInputMachine.rowWire) =
      RationalInputMachine.rowWire (SparseTransform.product RationalCompiler.data ps) := by
  induction ps with
  | nil => exact one_wire n
  | cons p ps ih =>
    change mul (RationalInputMachine.rowWire p) (product n (ps.map RationalInputMachine.rowWire)) = _
    rw [ih,mul_wire]
    rfl

noncomputable section

def addComputes : Computes pairEncoding encoding (fun p : Poly × Poly => p.1++p.2) :=
  WireLists.append termEncoding

def negComputes : Computes encoding encoding neg :=
  WireLists.mapComputes termEncoding termEncoding (fun t : Term => (t.1,-t.2))
    (pairComputes
      (Wiring.firstComputes NegativeCertificateMachine.exponentEncoding rationalEncoding)
      ((Wiring.secondComputes NegativeCertificateMachine.exponentEncoding rationalEncoding).andThen
        Holant.LocalDrafts.TraversalCompletion.RationalLP.Comparison.rationalNegate))

def subComputes : Computes pairEncoding encoding (fun p : Poly × Poly => sub p.1 p.2) :=
  (pairComputes (Wiring.firstComputes encoding encoding)
    ((Wiring.secondComputes encoding encoding).andThen negComputes)).andThen addComputes

def termComputes : Computes (FixedFieldMachines.pairEncoding termEncoding termEncoding)
    termEncoding (fun p : Term × Term => termProduct p.1 p.2) := by
  let a := Wiring.firstComputes termEncoding termEncoding
  let b := Wiring.secondComputes termEncoding termEncoding
  let exponent := Wiring.firstComputes NegativeCertificateMachine.exponentEncoding rationalEncoding
  let coefficient := Wiring.secondComputes NegativeCertificateMachine.exponentEncoding rationalEncoding
  exact pairComputes
    ((pairComputes (a.andThen exponent) (b.andThen exponent)).andThen
      NegativeCertificateMachine.SparsePrograms.addExponents)
    (ComplexIsolation.CertificateMachine.Scalars.mul (a.andThen coefficient) (b.andThen coefficient))

def rowComputes : Executes (FixedFieldMachines.pairEncoding encoding termEncoding) encoding
    (fun p => p.1.map (termProduct p.2)) := by
  let prepare := Executes.ofComputes (Wiring.swapComputes encoding termEncoding)
  exact prepare.comp (Executes.mapList termEncoding termEncoding termEncoding
    termProduct (Executes.ofComputes termComputes))

def mulExecutes : Executes pairEncoding encoding (fun p : Poly × Poly => mul p.1 p.2) := by
  let left := Wiring.firstComputes encoding encoding
  let right := Wiring.secondComputes encoding encoding
  let cell := Wiring.firstComputes pairEncoding termEncoding
  let term := Wiring.secondComputes pairEncoding termEncoding
  let row := (Executes.ofComputes (pairComputes (cell.andThen right) term)).comp rowComputes
  let rows := NegativeCertificateMachine.Lists.map pairEncoding termEncoding encoding
    (Executes.ofComputes left) (fun p t => p.2.map (termProduct t)) row
  exact (rows.comp (Executes.ofComputes (WireLists.flatten termEncoding))).congr
    (fun p => by simp only [mul,List.flatMap_def])

def oneExecutes : Executes encodingNatBool encoding one :=
  ((RationalInputMachine.Programs.zero).pair
    (Executes.ofComputes (constantComputes encodingNatBool rationalEncoding 1))).comp
      (Executes.ofComputes (NegativeCertificateMachine.Lists.singleton termEncoding))

def variableExecutes : Executes (FixedFieldMachines.pairEncoding encodingNatBool encodingNatBool)
    encoding (fun p : ℕ × ℕ => «variable» p.1 p.2) :=
  (RationalInputMachine.Programs.hit.pair
    (Executes.ofComputes (constantComputes _ rationalEncoding 1))).comp
      (Executes.ofComputes (NegativeCertificateMachine.Lists.singleton termEncoding))

def productExecutes : Executes (FixedFieldMachines.pairEncoding encodingNatBool familyEncoding)
    encoding (fun p : ℕ × List Poly => product p.1 p.2) := by
  let inputEncoding := FixedFieldMachines.pairEncoding encodingNatBool familyEncoding
  let n := Wiring.firstComputes encodingNatBool familyEncoding
  let ps := Wiring.secondComputes encodingNatBool familyEncoding
  let seed := (Executes.ofComputes n).comp oneExecutes
  let prepare := (Executes.ofComputes n).pair ((Executes.ofComputes ps).pair seed)
  let cell := (Executes.ofComputes
    (Wiring.secondComputes encodingNatBool pairEncoding)).comp mulExecutes
  exact prepare.comp (PositiveCertificateMachine.RightFold.executes
    encodingNatBool encoding encoding (fun _ a b => mul a b) [] cell)

end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalSparseMachine
