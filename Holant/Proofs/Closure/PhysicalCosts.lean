import Holant.Proofs.Closure.Interface
import Holant.Proofs.Closure.PhysicalKernel

/-! Actual execution-prefix costs for the same finite controlled oracle machine.
The construction adds no machine annotation or extra oracle. Query words are
related to reachable query configurations before their lengths are charged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Complexity Computability

namespace PhysicalProgramme
variable {α β γ δ : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool}
  {f : α → β} {g : γ → δ}

def primitivePolynomial (r : LengthControlledOracleReduction ea eb ec ed f g) :
    Polynomial ℕ := PhysicalKernel.primitivePolynomial r

def transcriptPolynomial (r : LengthControlledOracleReduction ea eb ec ed f g) :
    Polynomial ℕ := PhysicalKernel.transcriptPolynomial r

def storagePolynomial (r : LengthControlledOracleReduction ea eb ec ed f g) :
    Polynomial ℕ := PhysicalKernel.storagePolynomial r

/-- Produces all physical fields by induction over the actual machine. The
machine, clock, encodings and correctness certificate are literally unchanged. -/
def ofControlled (r : LengthControlledOracleReduction ea eb ec ed f g) :
    PhysicalProgramme ea eb ec ed f g where
  controlled := r
  primitiveBound := primitivePolynomial r
  transcriptBitBound := transcriptPolynomial r
  storageBound := storagePolynomial r
  primitives := PhysicalKernel.primitives r
  transcriptBits := PhysicalKernel.transcriptBits r
  storage := PhysicalKernel.storage r

@[simp] theorem ofControlled_controlled
    (r : LengthControlledOracleReduction ea eb ec ed f g) :
    (ofControlled r).controlled = r := rfl

@[simp] theorem ofControlled_machine
    (r : LengthControlledOracleReduction ea eb ec ed f g) :
    (ofControlled r).controlled.reduction.machine = r.reduction.machine := rfl

@[simp] theorem ofControlled_time
    (r : LengthControlledOracleReduction ea eb ec ed f g) :
    (ofControlled r).controlled.reduction.time = r.reduction.time := rfl

def refl (ea : Encoding α Bool) (eb : Encoding β Bool) (f : α → β)
    (hOutput : PolynomialOutputBound ea eb f) : PhysicalProgramme ea eb ea eb f f :=
  ofControlled (lengthControlled_refl ea eb f hOutput)

end PhysicalProgramme
end Holant.LocalDrafts.RemoteWork.StableClosureV2
