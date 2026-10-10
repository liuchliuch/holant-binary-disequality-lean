import Holant.Proofs.Tractability.AffineMachine.AccessPrograms
import Holant.Complexity.FixedFieldMachines.Concrete
import Holant.Complexity.BinaryInterpolation.DivisionStack

/-! A physical adjacent-difference filter. The vector is stored as a framed list,
so this does not mistake the eight-cell bytecode window for random access.
Every dynamic index, list traversal and field operation has an actual finite
Boolean-stack compiler. All arithmetic retains the original fixed-field codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeFilter
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

def difference (root : K) (ys : List K) : List K :=
  (List.range (ys.length-1)).map (fun k => ys.getD (k+1) 0-root*ys.getD k 0)

@[simp] theorem difference_length (root : K) (ys : List K) :
    (difference root ys).length=ys.length-1 := by simp [difference]

/-- Remaining roots, current answer vector, desired eigenvalue, denominator. -/
abbrev State (K : Type) := (List K × List K) × (K × K)

def step (s : State K) : State K :=
  if s.1.1=[] then s else
    ((s.1.1.tail,difference (s.1.1.getD 0 0) s.1.2),
      (s.2.1,s.2.2*(s.2.1-s.1.1.getD 0 0)))

@[simp] theorem step_nil (ys : List K) (desired den : K) :
    step (([],ys),(desired,den))=(([],ys),(desired,den)) := by simp [step]

@[simp] theorem step_cons (r : K) (rs ys : List K) (desired den : K) :
    step ((r::rs,ys),(desired,den))=
      ((rs,difference r ys),(desired,den*(desired-r))) := by simp [step]

abbrev listEncoding (F : FixedField K n) := framedListEncoding F.encoding
abbrev vectorsEncoding (F : FixedField K n) := pairEncoding (listEncoding F) (listEncoding F)
abbrev scalarsEncoding (F : FixedField K n) := pairEncoding F.encoding F.encoding
abbrev encoding (F : FixedField K n) := pairEncoding (vectorsEncoding F) (scalarsEncoding F)

def tailList (ys : List K) : List K :=
  (List.range (ys.length-1)).map (fun k => ys.getD (k+1) 0)

@[simp] theorem tailList_eq (ys : List K) : tailList ys=ys.tail := by
  apply List.ext_getElem
  · simp [tailList]
  · intro i hi hj
    simp only [tailList,List.getElem_map,List.getElem_range]
    rw [List.getD_eq_getElem]
    · simp
    · simp only [tailList,List.length_map,List.length_range] at hi
      omega

variable (F : FixedField K n)

/-- Field subtraction is assembled from canonical addition and multiplication. -/
def subtraction : Computes (scalarsEncoding F) F.encoding (fun p : K×K => p.1-p.2) :=
  congrComputes ((pairComputes (Wiring.firstComputes F.encoding F.encoding)
    ((pairComputes (constantComputes (scalarsEncoding F) F.encoding (-1))
      (Wiring.secondComputes F.encoding F.encoding)).andThen (Concrete.fieldMultiplication F))).andThen
      (Concrete.fieldAddition F)) (fun p => by dsimp; ring)

def tailComputes : Computes (listEncoding F) (listEncoding F) List.tail := by
  let old := Wiring.firstComputes (listEncoding F) UnaryBinary.unaryEncoding
  let k := Wiring.secondComputes (listEncoding F) UnaryBinary.unaryEncoding
  exact congrComputes (WireLists.tabulate (listEncoding F) F.encoding
    (fun ys : List K => ys.length-1)
    ((WireLists.lengthComputes F.encoding).andThen Endpoints.unaryPredecessorComputes)
    (fun ys k => ys.getD (k+1) 0)
    (AccessPrograms.get F.encoding 0 old (k.andThen WireLists.succComputes))) tailList_eq

abbrev differenceEncoding := pairEncoding F.encoding (listEncoding F)

def differenceComputes : Computes (differenceEncoding F) (listEncoding F)
    (fun p : K×List K => difference p.1 p.2) := by
  let context := Wiring.firstComputes (differenceEncoding F) UnaryBinary.unaryEncoding
  let root := context.andThen (Wiring.firstComputes F.encoding (listEncoding F))
  let ys := context.andThen (Wiring.secondComputes F.encoding (listEncoding F))
  let k := Wiring.secondComputes (differenceEncoding F) UnaryBinary.unaryEncoding
  let first := AccessPrograms.get F.encoding 0 ys k
  let second := AccessPrograms.get F.encoding 0 ys (k.andThen WireLists.succComputes)
  let product := (pairComputes root first).andThen (Concrete.fieldMultiplication F)
  exact WireLists.tabulate (differenceEncoding F) F.encoding
    (fun p : K×List K => p.2.length-1)
    (((Wiring.secondComputes F.encoding (listEncoding F)).andThen
      (WireLists.lengthComputes F.encoding)).andThen Endpoints.unaryPredecessorComputes)
    (fun p k => p.2.getD (k+1) 0-p.1*p.2.getD k 0)
    ((pairComputes second product).andThen (subtraction F))

def vectors : Computes (encoding F) (vectorsEncoding F) (fun s : State K => s.1) :=
  Wiring.firstComputes _ _
def scalars : Computes (encoding F) (scalarsEncoding F) (fun s : State K => s.2) :=
  Wiring.secondComputes _ _
def roots : Computes (encoding F) (listEncoding F) (fun s : State K => s.1.1) :=
  (vectors F).andThen (Wiring.firstComputes _ _)
def answers : Computes (encoding F) (listEncoding F) (fun s : State K => s.1.2) :=
  (vectors F).andThen (Wiring.secondComputes _ _)
def desired : Computes (encoding F) F.encoding (fun s : State K => s.2.1) :=
  (scalars F).andThen (Wiring.firstComputes _ _)
def denominator : Computes (encoding F) F.encoding (fun s : State K => s.2.2) :=
  (scalars F).andThen (Wiring.secondComputes _ _)
def headRoot : Computes (encoding F) F.encoding (fun s : State K => s.1.1.getD 0 0) :=
  (roots F).andThen (getDComputes F.encoding 0 0)

def nextComputes : Computes (encoding F) (encoding F)
    (fun s : State K => ((s.1.1.tail,difference (s.1.1.getD 0 0) s.1.2),
      (s.2.1,s.2.2*(s.2.1-s.1.1.getD 0 0)))) :=
  pairComputes (pairComputes ((roots F).andThen (tailComputes F))
    ((pairComputes (headRoot F) (answers F)).andThen (differenceComputes F)))
    (pairComputes (desired F)
      ((pairComputes (denominator F)
        ((pairComputes (desired F) (headRoot F)).andThen (subtraction F))).andThen
          (Concrete.fieldMultiplication F)))

/-- One fixed finite controller round, including the empty-root fixed point. -/
def computes : Computes (encoding F) (encoding F) step := by
  classical
  exact congrComputes (ifComputes
    ((pairComputes (roots F) (constantComputes (encoding F) (listEncoding F) [])).andThen
      (equalComputes (listEncoding F)))
    (identityComputes (encoding F)) (nextComputes F)) (fun s => by simp [step])

/-- The last operation is genuine canonical field division. -/
def finishComputes : Computes (encoding F) F.encoding
    (fun s : State K => s.1.2.getD 0 0/s.2.2) :=
  (pairComputes ((answers F).andThen (getDComputes F.encoding 0 0))
    (denominator F)).andThen (fieldDivisionComputes F)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeFilter
