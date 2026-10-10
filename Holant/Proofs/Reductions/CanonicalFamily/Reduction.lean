import Holant.Proofs.Reductions.CanonicalFamily.Scalars
import Holant.Proofs.Algorithms.TraceQueryControl


noncomputable section
namespace Holant.LocalDrafts.Hardness.CanonicalFamily
open Holant.Tractable
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.MainChain
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hn : ∀ i, G i ≠ 0)

def forwardPre (r : Input (s:=s) (a:=a)) := ([forwardQuery G r],forwardFactor G hn r)
def forwardPreComputes : Computes (sourceEncoding (s:=s) (a:=a))
    (OracleBatch.contextEncoding (keyEncoding G) (sourcePresentation G).encoding) (forwardPre G hn) :=
  pairComputes (fixedListComputes (sourceEncoding (s:=s) (a:=a)) (keyEncoding G)
    (fun r (_ : Unit) => forwardQuery G r) (fun _ => forwardComputes G) [()]) (forwardFactorComputes G hn)

def forwardPost (p : List (keyField G) × sourceField G) : sourceField G :=
  p.2 * embedding G hn (p.1.getD 0 0)
def forwardPostComputes : Computes
    (OracleBatch.contextEncoding (keyPresentation G).encoding (sourcePresentation G).encoding)
    (sourcePresentation G).encoding (forwardPost G hn) := by
  let answer := ((Wiring.firstComputes (framedListEncoding (keyPresentation G).encoding)
    (sourcePresentation G).encoding).andThen (getDComputes (keyPresentation G).encoding 0 0)).andThen
      (embedComputes G hn)
  let factor := Wiring.secondComputes (framedListEncoding (keyPresentation G).encoding)
    (sourcePresentation G).encoding
  exact (pairComputes factor answer).andThen (Concrete.fieldMultiplication (sourcePresentation G))
theorem forward_recovery (r : Input (s:=s) (a:=a)) :
    sourceValue G r = forwardPost G hn (OracleBatch.answers (keyValue G) (forwardPre G hn r)) :=
  forward_field_value G hn r

def forward : LengthControlledOracleReduction
    (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
    (keyEncoding G) (keyPresentation G).encoding (sourceValue G) (keyValue G) := by
  have he : sourceValue G = fun r => forwardPost G hn (OracleBatch.answers (keyValue G) (forwardPre G hn r)) :=
    funext (forward_recovery G hn)
  rw [he]
  exact TraceQueryControl.controlledBatch (forwardPreComputes G hn) (forwardPostComputes G hn)
    ((keyTables G).outputBound (keyPresentation G))

def backwardPre (r : KeyInput G) := ([backwardQuery G r],(backwardFactor G hn r)⁻¹)
def backwardPreComputes : Computes (keyEncoding G)
    (OracleBatch.contextEncoding (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding)
    (backwardPre G hn) :=
  pairComputes (fixedListComputes (keyEncoding G) (sourceEncoding (s:=s) (a:=a))
    (fun r (_ : Unit) => backwardQuery G r) (fun _ => backwardComputes G) [()])
    (backwardInverseComputes G hn)

def backwardPost (p : List (sourceField G) × sourceField G) : keyField G :=
  (embedding G hn).toLinearMap.leftInverse (p.2 * p.1.getD 0 0)
def backwardPostComputes : Computes
    (OracleBatch.contextEncoding (sourcePresentation G).encoding (sourcePresentation G).encoding)
    (keyPresentation G).encoding (backwardPost G hn) := by
  let answer := (Wiring.firstComputes (framedListEncoding (sourcePresentation G).encoding)
    (sourcePresentation G).encoding).andThen (getDComputes (sourcePresentation G).encoding 0 0)
  let factor := Wiring.secondComputes (framedListEncoding (sourcePresentation G).encoding)
    (sourcePresentation G).encoding
  exact ((pairComputes factor answer).andThen (Concrete.fieldMultiplication (sourcePresentation G))).andThen
    (retractComputes G hn)
theorem backward_recovery (r : KeyInput G) :
    keyValue G r = backwardPost G hn (OracleBatch.answers (sourceValue G) (backwardPre G hn r)) := by
  change keyValue G r = (embedding G hn).toLinearMap.leftInverse
    ((backwardFactor G hn r)⁻¹ * sourceValue G (backwardQuery G r))
  rw [backward_cancel]
  exact (FieldCodec.retract_embedding (embedding G hn) (keyValue G r)).symm

def backward : LengthControlledOracleReduction
    (keyEncoding G) (keyPresentation G).encoding
    (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding (keyValue G) (sourceValue G) := by
  have he : keyValue G = fun r => backwardPost G hn (OracleBatch.answers (sourceValue G) (backwardPre G hn r)) :=
    funext (backward_recovery G hn)
  rw [he]
  exact TraceQueryControl.controlledBatch (backwardPreComputes G hn) (backwardPostComputes G hn)
    ((sourceTables G).outputBound (sourcePresentation G))

include hn in
theorem equivalent :
    OracleReducible (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
      (keyEncoding G) (keyPresentation G).encoding (sourceValue G) (keyValue G) ∧
    OracleReducible (keyEncoding G) (keyPresentation G).encoding
      (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding (keyValue G) (sourceValue G) :=
  ⟨⟨(forward G hn).reduction⟩,⟨(backward G hn).reduction⟩⟩

end Holant.LocalDrafts.Hardness.CanonicalFamily
