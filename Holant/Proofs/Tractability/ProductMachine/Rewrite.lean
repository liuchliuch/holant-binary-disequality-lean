import Holant.Proofs.Tractability.ProductMachine.Templates
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Combinators
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Endpoints


namespace Holant.LocalDrafts.Tractability.ProductMachine.Rewrite

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
open Templates (Record recordEncoding)

def get (r : Record) : Fin 5 → ℕ := ![r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2]

noncomputable def getComputes (i : Fin 5) : Computes recordEncoding encodingNatBool (fun r => get r i) := by
  let n := encodingNatBool
  let p := pairEncoding n n
  let q := pairEncoding n p
  let r := pairEncoding n q
  let a := Wiring.secondComputes n r
  let b := a.andThen (Wiring.secondComputes n q)
  let c := b.andThen (Wiring.secondComputes n p)
  refine Fin.cases ?_ (fun i => ?_) i
  · exact Wiring.firstComputes n r
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact a.andThen (Wiring.firstComputes n q)
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact b.andThen (Wiring.firstComputes n p)
      · refine Fin.cases ?_ (fun i => ?_) i
        · exact c.andThen (Wiring.firstComputes n n)
        · exact Fin.cases (c.andThen (Wiring.secondComputes n n)) (fun j => Fin.elim0 j) i

abbrev Pivot := ℕ × Bool
abbrev pivotEncoding := RawClosedNetwork.endpointEncoding
def inputEncoding := pairEncoding pivotEncoding recordEncoding

def address (p : Pivot) (i : ℕ) : ℕ := if i = 0 then p.1 - 1 else i - 1
def flipAt (p : Pivot) (i : ℕ) : Bool := (i == 0) && p.2

theorem decide_zero (n : ℕ) : decide (n=0) = (n == 0) := by
  cases n <;> rfl

def record (p : Pivot) (r : Record) : Record :=
  if r.1 = 1 then
    (1, address p r.2.1,
      (if flipAt p r.2.1 then r.2.2.2.1 else r.2.2.1),
      (if flipAt p r.2.1 then r.2.2.1 else r.2.2.2.1), 0)
  else if r.1 = 2 then
    (2, address p r.2.1, address p r.2.2.1,
      (Bool.xor (Bool.xor (r.2.2.2.1 != 0) (flipAt p r.2.1)) (flipAt p r.2.2.1)).toNat, 0)
  else r

noncomputable def predComputes : Computes encodingNatBool encodingNatBool (fun n => n - 1) :=
  (pairComputes (identityComputes encodingNatBool)
    (constantComputes encodingNatBool encodingNatBool 1)).andThen Endpoints.subtractComputes

noncomputable def boolPairComputes (f : Bool × Bool → Bool) :
    Computes (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool f :=
  FiniteRecode.computes _ _ f 4 (fun x => by rcases x with ⟨a,b⟩; cases a <;> cases b <;> decide)

noncomputable def negComputes : Computes encodingBoolBool encodingBoolBool Bool.not :=
  FiniteRecode.computes _ _ Bool.not 1 (fun b => by cases b <;> decide)

noncomputable def field (i : Fin 5) : Computes inputEncoding encodingNatBool (fun x => get x.2 i) :=
  (Wiring.secondComputes pivotEncoding recordEncoding).andThen (getComputes i)

noncomputable def constant (n : ℕ) := constantComputes inputEncoding encodingNatBool n

noncomputable def equals (i : Fin 5) (n : ℕ) :
    Computes inputEncoding encodingBoolBool (fun x => decide (get x.2 i = n)) :=
  (pairComputes (field i) (constant n)).andThen Endpoints.equalComputes

noncomputable def contextBit : Computes inputEncoding encodingBoolBool (fun x => x.1.2) :=
  (Wiring.firstComputes pivotEncoding recordEncoding).andThen Endpoint.endBitComputes

noncomputable def contextIndex : Computes inputEncoding encodingNatBool (fun x => x.1.1) :=
  (Wiring.firstComputes pivotEncoding recordEncoding).andThen Endpoint.edgeComputes

noncomputable def addressComputes (i : Fin 5) :
    Computes inputEncoding encodingNatBool (fun x => address x.1 (get x.2 i)) :=
  congrComputes (ifComputes (equals i 0) (contextIndex.andThen predComputes)
    ((field i).andThen predComputes)) (fun x => by simp [address])

noncomputable def flipComputes (i : Fin 5) :
    Computes inputEncoding encodingBoolBool (fun x => flipAt x.1 (get x.2 i)) :=
  congrComputes ((pairComputes (equals i 0) contextBit).andThen
    (boolPairComputes (fun p => p.1 && p.2)))
      (fun x => by simp only [flipAt,decide_zero,Function.comp_def])

noncomputable def parityComputes : Computes inputEncoding encodingNatBool
    (fun x => (Bool.xor (Bool.xor (get x.2 3 != 0) (flipAt x.1 (get x.2 1)))
      (flipAt x.1 (get x.2 2))).toNat) := by
  let old := (equals 3 0).andThen negComputes
  let first := (pairComputes old (flipComputes 1)).andThen (boolPairComputes (fun p => Bool.xor p.1 p.2))
  exact congrComputes (((pairComputes first (flipComputes 2)).andThen
    (boolPairComputes (fun p => Bool.xor p.1 p.2))).andThen Endpoint.bitComputes)
    (fun x => by simp only [decide_zero]; rfl)

/-- Every candidate is a real finite program, selected by physically decoded tags. -/
noncomputable def computes : Computes inputEncoding recordEncoding (fun x => record x.1 x.2) := by
  let unary := pairComputes (constant 1) (pairComputes (addressComputes 1)
    (pairComputes (ifComputes (flipComputes 1) (field 3) (field 2))
      (pairComputes (ifComputes (flipComputes 1) (field 2) (field 3)) (constant 0))))
  let link := pairComputes (constant 2) (pairComputes (addressComputes 1)
    (pairComputes (addressComputes 2) (pairComputes parityComputes (constant 0))))
  exact congrComputes (ifComputes (equals 0 1) unary
    (ifComputes (equals 0 2) link (Wiring.secondComputes pivotEncoding recordEncoding)))
    (fun x => by
      by_cases h1 : x.2.1=1 <;> by_cases h2 : x.2.1=2 <;>
        simp [record,get,h1,h2])

noncomputable def listComputes :
    Computes (pairEncoding pivotEncoding (framedListEncoding recordEncoding))
      (framedListEncoding recordEncoding) (fun x => x.2.map (record x.1)) :=
  mapListComputes pivotEncoding recordEncoding recordEncoding record computes

theorem list_primitive_bound (x : Pivot × List Record) :
    primitiveCost listComputes.machine (listComputes.outputs x).steps
      (some (Turing.initList listComputes.machine.computer
        ((pairEncoding pivotEncoding (framedListEncoding recordEncoding)).encode x))) ≤
      (primitivePolynomial listComputes).eval
        ((pairEncoding pivotEncoding (framedListEncoding recordEncoding)).encode x).length :=
  computes_primitive_cost listComputes x

end Holant.LocalDrafts.Tractability.ProductMachine.Rewrite
