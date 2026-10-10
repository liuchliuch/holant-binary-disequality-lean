import Holant.Complexity.UniversalPairReduction.Smoothing
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Dispatch
import Holant.Complexity.BinaryArithmetic.EncodedComparison
import Holant.Complexity.BinaryArithmetic.EncodedSubtraction
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordCompare

/-! Actual binary endpoint remapping. Comparison and subtraction reuse their
finite Boolean-stack programs, with physical reversal of the operands. All
projections, copies, selections and compositions carry their machine bounds. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Endpoints
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler RawClosedNetwork
open GraphPreprocessing.OriginalCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev natPairEncoding := pairEncoding encodingNatBool encodingNatBool

abbrev comparisonMachine : Machine where
  K := BinaryArithmetic.EncodedComparison.computer.K
  input := BinaryArithmetic.EncodedComparison.computer.k₀
  output := BinaryArithmetic.EncodedComparison.computer.k₁
  Label := BinaryArithmetic.EncodedComparison.computer.Λ
  main := BinaryArithmetic.EncodedComparison.computer.main
  State := BinaryArithmetic.EncodedComparison.computer.σ
  initial := BinaryArithmetic.EncodedComparison.computer.initialState
  program := BinaryArithmetic.EncodedComparison.computer.m

abbrev subtractionMachine : Machine where
  K := BinaryArithmetic.EncodedSubtraction.computer.K
  input := BinaryArithmetic.EncodedSubtraction.computer.k₀
  output := BinaryArithmetic.EncodedSubtraction.computer.k₁
  Label := BinaryArithmetic.EncodedSubtraction.computer.Λ
  main := BinaryArithmetic.EncodedSubtraction.computer.main
  State := BinaryArithmetic.EncodedSubtraction.computer.σ
  initial := BinaryArithmetic.EncodedSubtraction.computer.initialState
  program := BinaryArithmetic.EncodedSubtraction.computer.m

noncomputable def prepareArithmeticComputes :
    Computes natPairEncoding BinaryArithmetic.EncodedAddition.inputEncoding id :=
  recode (pairComputes
    ((Wiring.firstComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
    ((Wiring.secondComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool)))
    id (fun _ => rfl) (fun _ => rfl)

noncomputable def encodedComparisonComputes :
    Computes BinaryArithmetic.EncodedComparison.inputEncoding encodingBoolBool
      (fun p => decide (p.1 < p.2)) where
  machine := comparisonMachine
  time := BinaryArithmetic.EncodedComparison.comparisonPolyTime.time
  outputs p := by
    have h := BinaryArithmetic.EncodedComparison.comparisonPolyTime.outputsFun p
    change TM2OutputsInTime comparisonMachine.computer
      (List.map id (BinaryArithmetic.EncodedComparison.inputEncoding.encode p))
      (some (List.map id (encodingBoolBool.encode (decide (p.1 < p.2))))) _ at h
    simpa only [List.map_id] using h

noncomputable def encodedSubtractionComputes :
    Computes BinaryArithmetic.EncodedSubtraction.inputEncoding encodingNatBool
      (fun p => p.1 - p.2) where
  machine := subtractionMachine
  time := BinaryArithmetic.EncodedSubtraction.subtractionPolyTime.time
  outputs p := by
    have h := BinaryArithmetic.EncodedSubtraction.subtractionPolyTime.outputsFun p
    change TM2OutputsInTime subtractionMachine.computer
      (List.map id (BinaryArithmetic.EncodedSubtraction.inputEncoding.encode p))
      (some (List.map id (encodingNatBool.encode (p.1 - p.2)))) _ at h
    simpa only [List.map_id] using h

noncomputable def lessComputes : Computes natPairEncoding encodingBoolBool
    (fun p => decide (p.1 < p.2)) :=
  prepareArithmeticComputes.andThen encodedComparisonComputes

noncomputable def subtractComputes : Computes natPairEncoding encodingNatBool
    (fun p => p.1 - p.2) :=
  prepareArithmeticComputes.andThen encodedSubtractionComputes

noncomputable def equalComputes : Computes natPairEncoding encodingBoolBool
    (fun p => decide (p.1 = p.2)) :=
  recode WordCompare.computes (fun p => (encodingNatBool.encode p.1,encodingNatBool.encode p.2))
    (fun _ => rfl) (fun p => by
      simp [WordCompare.value, encodingNatBool.encode_injective.eq_iff])

noncomputable def boolNatComputes : Computes encodingBoolBool encodingNatBool Bool.toNat :=
  FiniteRecode.computes encodingBoolBool encodingNatBool Bool.toNat 1 (fun b => by cases b <;> decide)

/-- Remove an edge ID with binary comparison and a binary subtraction of zero or one. -/
noncomputable def lowerEdgeComputes : Computes natPairEncoding encodingNatBool
    (fun x => Smoothing.lowerEdge x.1 x.2) :=
  congrComputes ((pairComputes (Wiring.secondComputes encodingNatBool encodingNatBool)
    (lessComputes.andThen boolNatComputes)).andThen subtractComputes)
    (fun x => by by_cases h : x.1 < x.2 <;> simp [Smoothing.lowerEdge,h])

/-- A two-candidate indexed selection, using the actual finite list selector. -/
noncomputable def selectComputes {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)
    (test : A → Bool) (yes no : A → B)
    (wt : Computes ea encodingBoolBool test) (wy : Computes ea eb yes) (wn : Computes ea eb no) :
    Computes ea eb (fun x => if test x then yes x else no x) := by
  let label (x : A) : Fin 2 := ⟨(test x).toNat,by cases test x <;> decide⟩
  let family (x : A) (i : Fin 2) := if i.val = 0 then no x else yes x
  let index : Computes ea UnaryBinary.unaryEncoding (fun x => (label x).val) :=
    wt.andThen (FiniteRecode.computes encodingBoolBool UnaryBinary.unaryEncoding Bool.toNat
      1 (fun b => by cases b <;> decide))
  let candidates : ∀ i, Computes ea eb (fun x => family x i) := by
    intro i
    by_cases h : i.val = 0
    · exact congrComputes wn (fun x => by simp only [family,if_pos h])
    · exact congrComputes wy (fun x => by simp only [family,if_neg h])
  exact congrComputes (chooseComputes ea eb 2 label family index candidates)
    (fun x => by cases h : test x <;> simp [family,label,h])

noncomputable def edgeComputes : Computes endpointEncoding encodingNatBool Prod.fst :=
  recode (Wiring.firstComputes encodingNatBool encodingBoolBool) id (fun _ => rfl) (fun _ => rfl)

noncomputable def orientationComputes : Computes endpointEncoding encodingBoolBool Prod.snd :=
  recode (Wiring.secondComputes encodingNatBool encodingBoolBool) id (fun _ => rfl) (fun _ => rfl)

abbrev removeLoopInputEncoding := pairEncoding encodingNatBool endpointEncoding

/-- A loop deletion preserves the endpoint orientation and lowers its binary ID. -/
noncomputable def removeLoopEndpointComputes : Computes removeLoopInputEncoding endpointEncoding
    (fun x => Smoothing.removeLoopEndpoint x.1 x.2) :=
  recode (pairComputes
    ((pairComputes (Wiring.firstComputes encodingNatBool endpointEncoding)
      ((Wiring.secondComputes encodingNatBool endpointEncoding).andThen edgeComputes)).andThen lowerEdgeComputes)
    ((Wiring.secondComputes encodingNatBool endpointEncoding).andThen orientationComputes))
    id (fun _ => rfl) (fun _ => rfl)

abbrev spliceInputEncoding := pairEncoding endpointEncoding (pairEncoding endpointEncoding endpointEncoding)

noncomputable def firstComputes : Computes spliceInputEncoding endpointEncoding (fun x => x.1) :=
  Wiring.firstComputes endpointEncoding (pairEncoding endpointEncoding endpointEncoding)
noncomputable def secondComputes : Computes spliceInputEncoding endpointEncoding (fun x => x.2.1) :=
  (Wiring.secondComputes endpointEncoding (pairEncoding endpointEncoding endpointEncoding)).andThen
    (Wiring.firstComputes endpointEncoding endpointEncoding)
noncomputable def currentComputes : Computes spliceInputEncoding endpointEncoding (fun x => x.2.2) :=
  (Wiring.secondComputes endpointEncoding (pairEncoding endpointEncoding endpointEncoding)).andThen
    (Wiring.secondComputes endpointEncoding endpointEncoding)

/-- Redirect the second edge to the first endpoint, then delete the second edge ID. -/
noncomputable def spliceEndpointComputes : Computes spliceInputEncoding endpointEncoding
    (fun x => Smoothing.spliceEndpoint x.1 x.2.1 x.2.2) := by
  let sameId := (pairComputes (currentComputes.andThen edgeComputes)
    (secondComputes.andThen edgeComputes)).andThen equalComputes
  let chosen := selectComputes spliceInputEncoding endpointEncoding
    (fun x => decide (x.2.2.1 = x.2.1.1)) (fun x => x.1) (fun x => x.2.2)
    sameId firstComputes currentComputes
  exact congrComputes ((pairComputes (secondComputes.andThen edgeComputes) chosen).andThen
    removeLoopEndpointComputes) (fun x => by
      by_cases h : x.2.2.1 = x.2.1.1 <;>
        simp [Smoothing.spliceEndpoint,Smoothing.removeLoopEndpoint,h])

/-- A single physical pop computes truncated unary predecessor. -/
abbrev unaryPredecessorMachine : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  program _ := .pop () (fun _ _ => ()) .halt

noncomputable def unaryPredecessorComputes :
    Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding (fun n => n-1) where
  machine := unaryPredecessorMachine
  time := 1
  outputs n := {
    steps := 1
    evals_in_steps := by
      change unaryPredecessorMachine.computer.step
        (initList unaryPredecessorMachine.computer (UnaryBinary.unaryEncoding.encode n)) =
        some (haltList unaryPredecessorMachine.computer (UnaryBinary.unaryEncoding.encode (n-1)))
      cases n <;> simp [initList,haltList,UnaryBinary.unaryEncoding,
        unaryPredecessorMachine,FinTM2.step,TM2.step,TM2.stepAux,List.replicate_succ]
      funext k
      cases k
      simp
    steps_le_m := by simp }

end Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Endpoints
