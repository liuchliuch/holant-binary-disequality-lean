import Holant.Proofs.Tractability.EOEvaluation.EOConditionCertificate.Pairings
import Holant.Proofs.Algorithms.TransformRecognition.OriginalFamilyInput
import Holant.Proofs.Tractability.AffineMachine.AccessPrograms
import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.PhysicalSearch.Source


namespace Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate.Descriptors
open Turing Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition

abbrev Word (n : ℕ) := Fin n → Bool
abbrev words := SparseTransform.allWords

def restriction {n : ℕ} (p : OrientedPerfectPairing n) (input : Word n → RootCode) :
    Word p.count → RootCode := fun z => input (p.word z)
def dense {n : ℕ} (input : Word n → RootCode) : List RootCode :=
  (words n).map input
def restrictionRows {n : ℕ} (p : OrientedPerfectPairing n) (input : Word n → RootCode) :
    List RootCode := dense (restriction p input)

theorem restriction_represents {n : ℕ} (p : OrientedPerfectPairing n)
    (input : Word n → RootCode) (f : Signature AlgebraicComplex n)
    (hf : ∀ x, (input x).Represents (f x : ℂ)) (z : Word p.count) :
    (restriction p input z).Represents (p.restrict f z : ℂ) := hf (p.word z)

def addresses {n : ℕ} (p : OrientedPerfectPairing n) : List ℕ :=
  (words p.count).map (fun z => (words n).idxOf (p.word z))
def copied (addresses : List ℕ) (input : List RootCode) : List RootCode :=
  addresses.map (fun j => input.getD j (RationalRootCode.code 0))

theorem dense_lookup {n : ℕ} (input : Word n → RootCode) (x : Word n) :
    (dense input).getD ((words n).idxOf x) (RationalRootCode.code 0)=input x := by
  have hx := SparseTransform.mem_allWords x
  rw [dense,List.getD_eq_getElem _ _ (by simpa using List.idxOf_lt_length_iff.mpr hx)]
  simp only [List.getElem_map,List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hx)]

theorem copied_exact {n : ℕ} (p : OrientedPerfectPairing n) (input : Word n → RootCode) :
    copied (addresses p) (dense input)=restrictionRows p input := by
  change ((words p.count).map (fun z => (words n).idxOf (p.word z))).map
    (fun j => (dense input).getD j (RationalRootCode.code 0)) =
    (words p.count).map (fun z => input (p.word z))
  rw [List.map_map]
  congr 1
  funext z
  exact dense_lookup input (p.word z)

abbrev rootEncoding := ComplexIsolation.CertificateMachine.rootEncoding
abbrev rootsEncoding := framedListEncoding rootEncoding
noncomputable section

/-- Fixed addresses are program constants; each original variable-length root
descriptor is physically looked up, framed and copied by the old programs. -/
def copyComputes : (as : List ℕ) → Computes rootsEncoding rootsEncoding (copied as)
  | [] => constantComputes rootsEncoding rootsEncoding []
  | j::js => by
      let head := AccessPrograms.get rootEncoding (RationalRootCode.code 0)
        (identityComputes rootsEncoding) (constantComputes rootsEncoding UnaryBinary.unaryEncoding j)
      let chunk := head.andThen (entryComputes rootEncoding)
      let tail := (copyComputes js).andThen (encodeComputes rootsEncoding)
      exact recode (joinComputes chunk tail) id (fun _ => rfl) (fun input => by
        change entry rootEncoding (input.getD j (RationalRootCode.code 0)) ++
          framedListEncode rootEncoding (copied js input) = framedListEncode rootEncoding (copied (j::js) input)
        rfl)

def restrictionComputes {n : ℕ} (p : OrientedPerfectPairing n) := copyComputes (addresses p)
def restriction_output {n : ℕ} (p : OrientedPerfectPairing n) (input : Word n → RootCode) :
    TM2OutputsInTime (restrictionComputes p).machine.computer
      (rootsEncoding.encode (dense input)) (some (rootsEncoding.encode (restrictionRows p input)))
      ((restrictionComputes p).time.eval (rootsEncoding.encode (dense input)).length) := by
  simpa only [copied_exact] using (restrictionComputes p).outputs (dense input)

theorem restriction_primitives {n : ℕ} (p : OrientedPerfectPairing n) (input : List RootCode) :
    primitiveCost (restrictionComputes p).machine ((restrictionComputes p).outputs input).steps
      (some (initList (restrictionComputes p).machine.computer (rootsEncoding.encode input))) ≤
      (primitivePolynomial (restrictionComputes p)).eval (rootsEncoding.encode input).length :=
  computes_primitive_cost (restrictionComputes p) input

theorem restriction_bytes {n : ℕ} (p : OrientedPerfectPairing n) (input : List RootCode) :
    (rootsEncoding.encode (copied (addresses p) input)).length ≤
      (restrictionComputes p).outputBound.bound.eval (rootsEncoding.encode input).length :=
  (restrictionComputes p).outputBound.length_le input

def zero (c : RootCode) (hc : ReturnedRootBranchSelection.Valid c) : Bool :=
  ReturnedRootBranchSelection.zeroList c [0,1] hc

theorem zero_iff (c : RootCode) (hc : ReturnedRootBranchSelection.Valid c)
    (z : ℂ) (hz : c.Represents z) : zero c hc=true ↔ z=0 := by
  simpa [zero,Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.BranchConsumers.decodeList,List.range_succ] using
    ReturnedRootBranchSelection.zeroList_iff c [0,1] hc z hz

/-- The actual unbounded structural controller supplies this root comparison;
the stopping height and zero answer are not inputs. No polynomial bound. -/
theorem zero_outputs (c : RootCode) (hc : ReturnedRootBranchSelection.Valid c) :
    ∃ height, Nonempty (TM2OutputsInTime
      ReturnedRootBranchSelection.PhysicalSearch.Source.listMachine.computer
      (ReturnedRootBranchSelection.PhysicalSearch.Source.listInputEncoding.encode (c,[0,1]))
      (some (encodingBoolBool.encode (zero c hc)))
      (ReturnedRootBranchSelection.PhysicalSearch.Source.listBound height (c,[0,1]) (zero c hc))) :=
  ReturnedRootBranchSelection.PhysicalSearch.Source.list_source_outputs (c,[0,1]) hc

end
end Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate.Descriptors
