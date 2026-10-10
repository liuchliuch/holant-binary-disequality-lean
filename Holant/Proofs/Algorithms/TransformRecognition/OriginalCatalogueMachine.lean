import Holant.Proofs.Algorithms.TransformRecognition.OriginalFamilyPackingMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalCatalogueMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Family := List OriginalFamilyPackingMachine.Vertex
abbrev Key := ℕ × RationalTensorMachine.Word
abbrev familyEncoding := OriginalFamilyPackingMachine.familyEncoding
abbrev keyEncoding := pairEncoding encodingNatBool RationalTensorMachine.wordEncoding
abbrev keysEncoding := framedListEncoding keyEncoding
def extended (xs : Family) : Family := xs ++ [(2,[])]
def atVertex (xs : Family) (i : ℕ) : List Key :=
  (RationalTableMachine.words ((extended xs).getD i (0,[])).1).map (fun x => (i,x))
def catalogue (xs : Family) : List Key := (List.range (xs.length+1)).flatMap (atVertex xs)

def bitmap (k : Key) (xs : List Key) : List Bool := xs.map (fun a => decide (k=a)) ++ [true]
def scanInput (p : Key × List Key) : OriginalCoefficient.FirstTrue.Input :=
  ⟨bitmap p.1 p.2,by simp [bitmap]⟩
theorem bitmap_index (k : Key) (xs : List Key) : (bitmap k xs).findIdx id=xs.idxOf k := by
  induction xs with
  | nil => simp [bitmap]
  | cons a xs ih =>
    by_cases h : a=k
    · subst a; simp [bitmap,List.findIdx_cons]
    · have h' : k≠a := Ne.symm h
      simpa [bitmap,List.findIdx_cons,List.idxOf_cons,h,h'] using congrArg Nat.succ ih

noncomputable section
def extendedComputes : Computes familyEncoding familyEncoding extended :=
  (pairComputes (identityComputes familyEncoding)
    (constantComputes familyEncoding familyEncoding [(2,[])])).andThen
      (WireLists.append OriginalFamilyPackingMachine.vertexEncoding)

def vertexExecutes : Executes (pairEncoding familyEncoding encodingNatBool) keysEncoding
    (fun p : Family × ℕ => atVertex p.1 p.2) := by
  let xs := Wiring.firstComputes familyEncoding encodingNatBool
  let i := Wiring.secondComputes familyEncoding encodingNatBool
  let record := (Executes.ofComputes (pairComputes (xs.andThen extendedComputes) i)).comp
    (NegativeCertificateMachine.Lists.lookup OriginalFamilyPackingMachine.vertexEncoding (0,[]))
  let arity := record.comp (Executes.ofComputes
    (Wiring.firstComputes encodingNatBool CommonFieldMachine.rootsEncoding))
  let words := arity.comp RationalTableMachine.wordsExecutes
  let cell := pairComputes
    ((Wiring.firstComputes (pairEncoding familyEncoding encodingNatBool) RationalTensorMachine.wordEncoding).andThen i)
    (Wiring.secondComputes (pairEncoding familyEncoding encodingNatBool) RationalTensorMachine.wordEncoding)
  exact NegativeCertificateMachine.Lists.map (pairEncoding familyEncoding encodingNatBool)
    RationalTensorMachine.wordEncoding keyEncoding words (fun p x => (p.2,x)) (Executes.ofComputes cell)

def executes : Executes familyEncoding keysEncoding catalogue := by
  let count := ((WireLists.lengthComputes OriginalFamilyPackingMachine.vertexEncoding).andThen
    UnaryBinary.computes).andThen RationalInputMachine.Programs.successor
  let families := NegativeCertificateMachine.Lists.map familyEncoding encodingNatBool keysEncoding
    ((Executes.ofComputes count).comp RationalInputMachine.Programs.range) atVertex vertexExecutes
  exact (families.comp (Executes.ofComputes (WireLists.flatten keyEncoding))).congr
    (fun xs => by simp only [catalogue,List.flatMap_def,Function.comp_apply,id_eq])

abbrev lookupEncoding := pairEncoding keyEncoding keysEncoding
def bitmapComputes : Computes lookupEncoding (framedListEncoding encodingBoolBool)
    (fun p : Key × List Key => p.2.map (fun a => decide (p.1=a))) :=
  mapListComputes keyEncoding keyEncoding encodingBoolBool
    (fun k a => decide (k=a)) (equalComputes keyEncoding)
def prepareLookup : Computes lookupEncoding OriginalCoefficient.FirstTrue.inputEncoding scanInput :=
  recode (joinComputes (bitmapComputes.andThen RationalInputMachine.FirstIndex.rawBits)
    (constantComputes lookupEncoding Frame.wordEncoding [true])) id (fun _ => rfl) (fun _ => rfl)
def indexComputes : Computes lookupEncoding encodingNatBool (fun p : Key × List Key => p.2.idxOf p.1) :=
  congrComputes ((prepareLookup.andThen OriginalCoefficient.FirstTrue.computes).andThen UnaryBinary.computes)
    (fun p => bitmap_index p.1 p.2)

end

abbrev AddressInput := ℕ × (List Key × Key)
abbrev addressTailEncoding := pairEncoding keysEncoding keyEncoding
abbrev addressEncoding := pairEncoding encodingNatBool addressTailEncoding
def address (r : AddressInput) : ℕ := 5+r.1+r.2.1.idxOf r.2.2

noncomputable def addressComputes : Computes addressEncoding encodingNatBool address := by
  let q := Wiring.firstComputes encodingNatBool addressTailEncoding
  let tail := Wiring.secondComputes encodingNatBool addressTailEncoding
  let keys := tail.andThen (Wiring.firstComputes keysEncoding keyEncoding)
  let key := tail.andThen (Wiring.secondComputes keysEncoding keyEncoding)
  let i := (pairComputes key keys).andThen indexComputes
  let base := (pairComputes (constantComputes addressEncoding encodingNatBool 5) q).andThen
    RationalInputMachine.Programs.add
  exact (pairComputes base i).andThen RationalInputMachine.Programs.add

theorem address_present (q : ℕ) (xs : List Key) (k : Key) (hk : k ∈ xs) :
    address (q,xs,k) < 5+q+xs.length := by
  have hi := List.idxOf_lt_length_iff.mpr hk
  change 5+q+xs.idxOf k < 5+q+xs.length
  omega

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalCatalogueMachine
