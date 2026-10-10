import Holant.Proofs.Algorithms.TransformRecognition.OriginalAllocatedPackingMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalCatalogueMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.ProductAllocationMachine
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Family := OriginalCatalogueMachine.Family
abbrev familyEncoding := OriginalCatalogueMachine.familyEncoding
abbrev numbersEncoding := framedListEncoding encodingNatBool
abbrev PrefixInput := Family × ℕ
abbrev prefixEncoding := pairEncoding familyEncoding encodingNatBool

def blockSize (n : ℕ) : ℕ := n+n+1
def sizes (xs : Family) : List ℕ := xs.map (fun v => blockSize v.1)
def count (xs : Family) : ℕ := (sizes xs).sum+5
def prefixSize (p : PrefixInput) : ℕ :=
  ((List.range p.2).map (fun j => blockSize (p.1.getD j (0,[])).1)).sum
def scalarAddress (p : PrefixInput) : ℕ := 5+prefixSize p
def unaryPair (p : ℕ × ℕ) : ℕ × ℕ := (p.1+1+(p.2+p.2),p.1+1+(p.2+p.2)+1)

noncomputable section

def sumExecutes : Executes numbersEncoding encodingNatBool List.sum := by
  let prepare := Executes.ofComputes (pairComputes (constantComputes numbersEncoding encodingBoolBool false)
    (pairComputes (identityComputes numbersEncoding) (constantComputes numbersEncoding encodingNatBool 0)))
  let add := (Wiring.secondComputes encodingBoolBool (pairEncoding encodingNatBool encodingNatBool)).andThen
    RationalInputMachine.Programs.add
  exact (prepare.comp (PositiveCertificateMachine.RightFold.executes encodingBoolBool encodingNatBool
    encodingNatBool (fun _ x acc => x+acc) 0 (Executes.ofComputes add))).congr
      (fun xs => by simp only [List.sum_eq_foldr, id_eq])

def blockComputes : Computes encodingNatBool encodingNatBool blockSize :=
  ((pairComputes (identityComputes encodingNatBool) (identityComputes encodingNatBool)).andThen
    RationalInputMachine.Programs.add).andThen RationalInputMachine.Programs.successor

def sizesComputes : Computes familyEncoding numbersEncoding sizes :=
  WireLists.mapComputes OriginalFamilyPackingMachine.vertexEncoding encodingNatBool
    (fun v => blockSize v.1) ((Wiring.firstComputes encodingNatBool CommonFieldMachine.rootsEncoding).andThen blockComputes)

def countExecutes : Executes familyEncoding encodingNatBool count :=
  (((Executes.ofComputes sizesComputes).comp sumExecutes).pair
    (Executes.ofComputes (constantComputes familyEncoding encodingNatBool 5))).comp
      (Executes.ofComputes RationalInputMachine.Programs.add)

def prefixCell : Executes (pairEncoding prefixEncoding encodingNatBool) encodingNatBool
    (fun p : PrefixInput × ℕ => blockSize (p.1.1.getD p.2 (0,[])).1) := by
  let xs := (Wiring.firstComputes prefixEncoding encodingNatBool).andThen
    (Wiring.firstComputes familyEncoding encodingNatBool)
  let j := Wiring.secondComputes prefixEncoding encodingNatBool
  let record := (Executes.ofComputes (pairComputes xs j)).comp
    (NegativeCertificateMachine.Lists.lookup OriginalFamilyPackingMachine.vertexEncoding (0,[]))
  exact record.comp (Executes.ofComputes
    ((Wiring.firstComputes encodingNatBool CommonFieldMachine.rootsEncoding).andThen blockComputes))

def prefixExecutes : Executes prefixEncoding encodingNatBool prefixSize :=
  (NegativeCertificateMachine.Lists.map prefixEncoding encodingNatBool encodingNatBool
    ((Executes.ofComputes (Wiring.secondComputes familyEncoding encodingNatBool)).comp RationalInputMachine.Programs.range)
    (fun p j => blockSize (p.1.getD j (0,[])).1) prefixCell).comp sumExecutes

def scalarExecutes : Executes prefixEncoding encodingNatBool scalarAddress :=
  ((Executes.ofComputes (constantComputes prefixEncoding encodingNatBool 5)).pair prefixExecutes).comp
    (Executes.ofComputes RationalInputMachine.Programs.add)

def unaryComputes : Computes (pairEncoding encodingNatBool encodingNatBool)
    (pairEncoding encodingNatBool encodingNatBool) unaryPair := by
  let scalar := Wiring.firstComputes encodingNatBool encodingNatBool
  let j := Wiring.secondComputes encodingNatBool encodingNatBool
  let twice := (pairComputes j j).andThen RationalInputMachine.Programs.add
  let left := (pairComputes (scalar.andThen RationalInputMachine.Programs.successor) twice).andThen
    RationalInputMachine.Programs.add
  exact pairComputes left (left.andThen RationalInputMachine.Programs.successor)
end

theorem unary_distinct (scalar j : ℕ) : (unaryPair (scalar,j)).1≠(unaryPair (scalar,j)).2 := by
  simp only [unaryPair]
  omega

theorem unary_after_scalar (scalar j : ℕ) : scalar<(unaryPair (scalar,j)).1 := by
  simp only [unaryPair]
  omega

end Holant.LocalDrafts.MainChain.TransformRecognition.ProductAllocationMachine
