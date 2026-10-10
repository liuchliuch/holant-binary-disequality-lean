import Holant.Proofs.Algorithms.TransformRecognition.OriginalFamilyPackingSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAllocatedPackingMachine
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Input := OriginalFamilyPackingMachine.Input × ℕ
abbrev encoding := pairEncoding OriginalFamilyPackingMachine.encoding encodingNatBool

def base (r : Input) : ℕ := 5+r.2
def width (r : Input) : ℕ := base r+(OriginalFamilyPackingMachine.original r.1).length+3
def addresses (r : Input) : List ℕ :=
  (List.range ((OriginalFamilyPackingMachine.original r.1).length+2)).map (fun j => base r+j)

noncomputable section
def source := Wiring.firstComputes OriginalFamilyPackingMachine.encoding encodingNatBool
def parameters := Wiring.secondComputes OriginalFamilyPackingMachine.encoding encodingNatBool
def baseComputes : Computes encoding encodingNatBool base :=
  (pairComputes (constantComputes encoding encodingNatBool 5) parameters).andThen RationalInputMachine.Programs.add

def widthComputes : Computes encoding encodingNatBool width :=
  (pairComputes ((pairComputes baseComputes (source.andThen OriginalFamilyPackingMachine.originalsCount)).andThen
    RationalInputMachine.Programs.add) (constantComputes encoding encodingNatBool 3)).andThen RationalInputMachine.Programs.add

def addressCell : Executes (pairEncoding encoding encodingNatBool) encodingNatBool
    (fun p : Input × ℕ => base p.1+p.2) :=
  Executes.ofComputes ((pairComputes
    ((Wiring.firstComputes encoding encodingNatBool).andThen baseComputes)
    (Wiring.secondComputes encoding encodingNatBool)).andThen RationalInputMachine.Programs.add)

def addressesExecutes : Executes encoding RationalInputMachine.addressesEncoding addresses :=
  NegativeCertificateMachine.Lists.map encoding encodingNatBool encodingNatBool
    ((Executes.ofComputes (source.andThen OriginalFamilyPackingMachine.rootCount)).comp RationalInputMachine.Programs.range)
    (fun r j => base r+j) addressCell
end

variable {s : ℕ} (arity : Fin s → ℕ)
theorem width_source (input : OriginalFamilyInput.Input arity) (disequality : Bool) (q : ℕ) :
    width (OriginalFamilyPackingSource.fromSource arity input disequality,q) =
      OriginalVariableLayout.Width (OriginalAffineSystem.Entries arity) q := by
  simp only [width,base,OriginalFamilyPackingSource.original_length,
    OriginalVariableLayout.Width,OriginalVariableLayout.Extra]
  omega

theorem addresses_source (input : OriginalFamilyInput.Input arity) (disequality : Bool) (q : ℕ) :
    addresses (OriginalFamilyPackingSource.fromSource arity input disequality,q) =
      List.ofFn (fun i => (OriginalVariableLayout.binding (OriginalAffineSystem.Entries arity) q i).val) := by
  unfold addresses
  rw [OriginalFamilyPackingSource.original_length]
  change CommonFieldMachine.Coordinates.tab (OriginalAffineSystem.Entries arity+2) (fun j => 5+q+j) = _
  rw [CommonFieldMachine.Coordinates.tab_ofFn]
  congr 1
  funext i
  exact (OriginalFamilyPackingSource.binding_value _ _ i).symm

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAllocatedPackingMachine
