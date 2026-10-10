import Holant.Proofs.Algorithms.FieldCodec
import Holant.Proofs.Algorithms.ControlledReduction


namespace Holant.LocalDrafts.MainChain.FieldTransport
open Computability Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose
noncomputable section

variable {α K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]
    {n m : ℕ} (F : FixedField K n) (G : FixedField L m)
    (φ : K →ₐ[ℚ] L) (ea : Encoding α Bool) (f : α → K)
    (hf : PolynomialOutputBound ea F.encoding f)

/-- The actual conversion program's output bound is composed with the original
evaluation bound; no constant-size answer convention is introduced. -/
def embeddedOutput : PolynomialOutputBound ea G.encoding (fun x => φ (f x)) where
  bound := (FieldCodec.outputBound F G φ.toLinearMap).bound.comp hf.bound
  length_le x := by
    have h := (FieldCodec.outputBound F G φ.toLinearMap).length_le (f x)
    exact h.trans (by simpa only [Polynomial.eval_comp] using
      (natPolynomial_eval_mono (FieldCodec.outputBound F G φ.toLinearMap).bound
        (hf.length_le x)))

/-- Query the original function and encode its embedded value. -/
def toOriginal : LengthControlledOracleReduction ea G.encoding ea F.encoding
    (fun x => φ (f x)) f :=
  controlledOneQueryOfEq (identityComputes ea) (FieldCodec.computes F G φ.toLinearMap)
    hf (fun x => φ (f x)) (fun _ => rfl)

/-- Query the common-field value and recover its unique original-field answer
using the constructed linear retraction. The query word is unchanged. -/
def fromOriginal : LengthControlledOracleReduction ea F.encoding ea G.encoding
    f (fun x => φ (f x)) :=
  controlledOneQueryOfEq (identityComputes ea) (FieldCodec.retractComputes F G φ)
    (embeddedOutput F G φ ea f hf) f
    (fun x => (FieldCodec.retract_embedding φ (f x)).symm)

include hf in
theorem equivalent :
    OracleReducible ea G.encoding ea F.encoding (fun x => φ (f x)) f ∧
    OracleReducible ea F.encoding ea G.encoding f (fun x => φ (f x)) :=
  ⟨⟨(toOriginal F G φ ea f hf).reduction⟩,
    ⟨(fromOriginal F G φ ea f hf).reduction⟩⟩

end
end Holant.LocalDrafts.MainChain.FieldTransport
