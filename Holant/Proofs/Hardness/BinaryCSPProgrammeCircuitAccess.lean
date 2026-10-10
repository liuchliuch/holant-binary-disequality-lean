import Holant.Proofs.Hardness.BinaryCSPProgrammeStars
import Holant.Proofs.Hardness.BinaryThreeSupportCodeGraph

/-! Physical prefix sums and reverse variable references for signed circuit
compilation. All loop lengths are unary tape words; arbitrarily large binary
references are compared/subtracted as binary words and never padded to unary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeCircuitAccess
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open BinaryCSPProgrammeCore FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.RemoteWork.CountingBridge
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate lengthComputes getD)
end W
namespace U
export Holant.LocalDrafts.CountingHardness.VerifierCompiler.Stateful.CapacityFrontend.Unary
  (subtractComputes addComputes)
end U
namespace C
export BinaryThreeSupportCodeGraph (fresh start resolve)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

def takeComputes {A : Type} (e : Encoding A Bool) (default : A) :
    Computes (pairEncoding (framedListEncoding e) unary) (framedListEncoding e) (fun x => x.1.take x.2) := by
  let source := pairEncoding (framedListEncoding e) unary
  let xs := Wiring.firstComputes (framedListEncoding e) unary
  let n := Wiring.secondComputes (framedListEncoding e) unary
  let len := xs.andThen (W.lengthComputes e)
  let test := (pairComputes (len.andThen UnaryBinary.computes) (n.andThen UnaryBinary.computes)).andThen
    Endpoints.lessComputes
  let count := congrComputes (ifComputes test len n) (fun x => by
    change (if decide (x.1.length<x.2) then x.1.length else x.2)=min x.2 x.1.length
    by_cases h : x.1.length<x.2 <;> simp [h,Nat.min_def] <;> omega)
  let array := (Wiring.firstComputes source unary).andThen xs
  let index := Wiring.secondComputes source unary
  refine congrComputes (W.tabulate source e (fun x => min x.2 x.1.length) count
    (fun x i => x.1.getD i default) ((pairComputes array index).andThen (W.getD e default))) ?_
  intro x
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hin : i<x.1.length := by simp only [List.length_map,List.length_range] at hi; omega
    simp [List.getD_eq_getElem,hin]

abbrev rowsEncoding := framedListEncoding Circuit.rowEncoding
abbrev pairNat := pairEncoding encodingNatBool encodingNatBool
abbrev baseEncoding := pairEncoding rowsEncoding unary
abbrev startEncoding := pairEncoding baseEncoding unary
abbrev resolveEncoding := pairEncoding startEncoding encodingNatBool

def tagComputes : Computes Circuit.rowEncoding encodingNatBool Prod.fst :=
  recode (Wiring.firstComputes encodingNatBool pairNat) id (fun _ => rfl) (fun _ => rfl)

def freshComputes : Computes Circuit.rowEncoding unary C.fresh := by
  let test := (pairComputes tagComputes (constantComputes Circuit.rowEncoding encodingNatBool 2)).andThen
    Endpoints.lessComputes
  exact congrComputes (ifComputes test (constantComputes Circuit.rowEncoding unary 2)
    (constantComputes Circuit.rowEncoding unary 10)) (fun _ => by simp [C.fresh])

def sumFreshComputes : Computes rowsEncoding unary (fun rs => (rs.map C.fresh).sum) :=
  recode (VerifierCircuit.Stateful.Indexed.flatMapComputes Circuit.rowEncoding
    (fun r => unary.encode (C.fresh r)) (freshComputes.andThen (encodeComputes unary)))
    id (fun _ => rfl) (fun rs => by
      change rs.flatMap (fun r => List.replicate (C.fresh r) true)=List.replicate (rs.map C.fresh).sum true
      induction rs with
      | nil => rfl
      | cons r rs ih => simp only [List.flatMap_cons,List.map_cons,List.sum_cons,ih,List.replicate_add])

def startComputes : Computes startEncoding unary (fun x => C.start x.1.1 x.1.2 x.2) := by
  let ctx := Wiring.firstComputes baseEncoding unary
  let rs := ctx.andThen (Wiring.firstComputes rowsEncoding unary)
  let offset := ctx.andThen (Wiring.secondComputes rowsEncoding unary)
  let t := Wiring.secondComputes baseEncoding unary
  let before := (pairComputes rs t).andThen (takeComputes Circuit.rowEncoding (0,(0,0)))
  exact (pairComputes offset (before.andThen sumFreshComputes)).andThen U.addComputes

def resolveComputes : Computes resolveEncoding encodingNatBool
    (fun x => C.resolve x.1.1.1 id x.1.1.2 x.1.2 x.2) := by
  let ctx := Wiring.firstComputes startEncoding encodingNatBool
  let base := ctx.andThen (Wiring.firstComputes baseEncoding unary)
  let t := ctx.andThen (Wiring.secondComputes baseEncoding unary)
  let u := Wiring.secondComputes startEncoding encodingNatBool
  let tb := t.andThen UnaryBinary.computes
  let test := (pairComputes u tb).andThen Endpoints.lessComputes
  let bounded := (pairComputes t u).andThen Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access.boundedUnary
  let before := t.andThen Endpoints.unaryPredecessorComputes
  let index := (pairComputes before bounded).andThen U.subtractComputes
  let yes := ((pairComputes base index).andThen startComputes).andThen UnaryBinary.computes
  let no := (pairComputes u tb).andThen Endpoints.subtractComputes
  refine congrComputes (ifComputes test yes no) ?_
  intro x
  change (if decide (x.2<x.1.2) then C.start x.1.1.1 x.1.1.2 (x.1.2-1-min x.1.2 x.2)
    else x.2-x.1.2)=C.resolve x.1.1.1 id x.1.1.2 x.1.2 x.2
  by_cases h : x.2<x.1.2
  · simp [C.resolve,h,Nat.min_eq_right (Nat.le_of_lt h)]
  · simp [C.resolve,h]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeCircuitAccess
