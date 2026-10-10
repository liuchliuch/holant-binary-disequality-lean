import Holant.Proofs.Hardness.ThreeModeAnnihilatorEnumeration
import Holant.Proofs.Tractability.AffineMachine.WireLists
import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.Unary
import Holant.Complexity.FixedFieldMachines.ScalarPower.Correction

/-! Actual finite unary-grid and original-field root preprocessing. Every
subtraction, range, field power, multiplication, list frame and delimiter is
emitted by an existing physical finite machine, composed below. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeProgrammeRoots
open Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
namespace U
export Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Unary
  (subtractComputes addComputes successorComputes)
end U
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists
  (tabulate flatten lengthComputes)
end W
namespace A
export ThreeModeAnnihilator (rootIndices mode)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
abbrev unary := UnaryBinary.unaryEncoding
abbrev pairUnary := pairEncoding unary unary
abbrev rootEncoding := pairEncoding unary pairUnary

def firstUnary : Computes pairUnary unary (fun x=>x.1) := Wiring.firstComputes unary unary
def secondUnary : Computes pairUnary unary (fun x=>x.2) := Wiring.secondComputes unary unary

def rowPairComputes : Computes pairUnary pairUnary (fun x=>(x.2,x.1+1-x.2)) :=
  pairComputes secondUnary
    ((pairComputes (firstUnary.andThen U.successorComputes) secondUnary).andThen U.subtractComputes)

def rowComputes : Computes unary (framedListEncoding pairUnary)
    (fun s=>(List.range (s+2)).map (fun i=>(i,s+1-i))) :=
  W.tabulate unary pairUnary (fun s=>s+2)
    (U.successorComputes.andThen U.successorComputes) _ rowPairComputes

/-- Exact nested unary enumeration of the triangular unwanted grid. -/
def indicesComputes : Computes unary (framedListEncoding pairUnary) A.rootIndices := by
  let nested := W.tabulate unary (framedListEncoding pairUnary) id (identityComputes unary)
    (fun _ s=>(List.range (s+2)).map (fun i=>(i,s+1-i)))
    (secondUnary.andThen rowComputes)
  exact congrComputes (nested.andThen (W.flatten pairUnary)) (fun _=>rfl)

def degreeComputes : Computes unary unary (fun m=>(A.rootIndices m).length) :=
  indicesComputes.andThen (W.lengthComputes pairUnary)

def queryCountComputes : Computes unary unary (fun m=>(A.rootIndices m).length+1) :=
  degreeComputes.andThen U.successorComputes

def rootM : Computes rootEncoding unary (fun x=>x.1) := Wiring.firstComputes unary pairUnary
def rootPair : Computes rootEncoding pairUnary (fun x=>x.2) := Wiring.secondComputes unary pairUnary
def rootI : Computes rootEncoding unary (fun x=>x.2.1) := rootPair.andThen firstUnary
def rootJ : Computes rootEncoding unary (fun x=>x.2.2) := rootPair.andThen secondUnary

def rootExponent : Computes rootEncoding unary (fun x=>x.1-x.2.1-x.2.2) :=
  (pairComputes ((pairComputes rootM rootI).andThen U.subtractComputes) rootJ).andThen
    U.subtractComputes

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (lam mu nu : K)

def powerComputes (u : K) : Computes unary F.encoding (fun n=>u^n) :=
  congrComputes (ScalarPower.computes F (F.decode.symm u)) (fun _=>by simp)

/-- Fixed original-field constants; no ambient answer recoding occurs. -/
def rootComputes : Computes rootEncoding F.encoding (fun x=>A.mode x.1 lam mu nu x.2) :=
  (pairComputes
    ((pairComputes (rootExponent.andThen (powerComputes F lam))
      (rootI.andThen (powerComputes F mu))).andThen (Concrete.fieldMultiplication F))
    (rootJ.andThen (powerComputes F nu))).andThen (Concrete.fieldMultiplication F)

def roots (m : ℕ) : List K := (A.rootIndices m).map (A.mode m lam mu nu)

def rootsComputes : Computes unary (framedListEncoding F.encoding) (roots lam mu nu) :=
  (pairComputes (identityComputes unary) indicesComputes).andThen
    (UniversalPairReduction.SmoothingCompiler.mapListComputes unary pairUnary F.encoding
      (fun m ij=>A.mode m lam mu nu ij) (rootComputes F lam mu nu))

/-- Root vector and desired eigenvalue supplied to the actual finite filter. -/
def preprocessing (m : ℕ) : List K × K := (roots lam mu nu m,lam^m)
def preprocessingComputes : Computes unary
    (pairEncoding (framedListEncoding F.encoding) F.encoding) (preprocessing lam mu nu) :=
  pairComputes (rootsComputes F lam mu nu) (powerComputes F lam)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeProgrammeRoots
