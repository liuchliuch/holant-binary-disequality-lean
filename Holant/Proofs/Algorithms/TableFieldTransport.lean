import Holant.Proofs.Algorithms.FieldTransport
import Holant.Complexity.EncodedHolantOutputSize
import Holant.NetworkAlgebra


namespace Holant.LocalDrafts.MainChain.TableFieldTransport
open Computability Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]
    {n m s b : ℕ} {arity : ℕ → ℕ}
    (F : FixedField K n) (G : FixedField L m) (φ : K →ₐ[ℚ] L)
    (T : ExactSignatureTables n s b arity)

def mapTables : ExactSignatureTables m s b arity where
  vertex i x := G.decode.symm (φ (F.decode (T.vertex i x)))
  edge i x y := G.decode.symm (φ (F.decode (T.edge i x y)))

theorem evaluate_map (r : ExactSignatureTables.Input s b arity) :
    (mapTables F G φ T).evaluate G r = φ (T.evaluate F r) := by
  rw [ExactSignatureTables.evaluate_eq_decoded, ExactSignatureTables.evaluate_eq_decoded]
  have h := Network.denote_map φ.toRingHom
    (r.val.realize r.property (fun i x => F.decode (T.vertex i x))
      (fun i x y => F.decode (T.edge i x y))) Fin.elim0
  simpa only [mapTables, LinearEquiv.apply_symm_apply, Network.map,
    RawClosedNetwork.realize, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h

/-- An oracle with the original coefficient codec answers the common-field
problem through a real output-conversion machine. -/
def toOriginal : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s b arity) G.encoding
    (RawClosedNetwork.validatedEncoding s b arity) F.encoding
    ((mapTables F G φ T).evaluate G) (T.evaluate F) :=
  controlledOneQueryOfEq
    (identityComputes (RawClosedNetwork.validatedEncoding s b arity))
    (FieldCodec.computes F G φ.toLinearMap) (T.outputBound F)
    ((mapTables F G φ T).evaluate G) (evaluate_map F G φ T)

/-- Every target answer is proved to be in the embedded original field by the
network identity; the total linear decoder returns its original coordinates. -/
def fromOriginal : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s b arity) F.encoding
    (RawClosedNetwork.validatedEncoding s b arity) G.encoding
    (T.evaluate F) ((mapTables F G φ T).evaluate G) :=
  controlledOneQueryOfEq
    (identityComputes (RawClosedNetwork.validatedEncoding s b arity))
    (FieldCodec.retractComputes F G φ) ((mapTables F G φ T).outputBound G)
    (T.evaluate F) (fun r => by
      rw [evaluate_map]
      exact (FieldCodec.retract_embedding φ (T.evaluate F r)).symm)

theorem equivalent :
    OracleReducible (RawClosedNetwork.validatedEncoding s b arity) G.encoding
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      ((mapTables F G φ T).evaluate G) (T.evaluate F) ∧
    OracleReducible (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      (RawClosedNetwork.validatedEncoding s b arity) G.encoding
      (T.evaluate F) ((mapTables F G φ T).evaluate G) :=
  ⟨⟨(toOriginal F G φ T).reduction⟩, ⟨(fromOriginal F G φ T).reduction⟩⟩

end
end Holant.LocalDrafts.MainChain.TableFieldTransport
