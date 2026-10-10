import Holant.Complexity.BinaryCompose.Identity
import Holant.Holographic
import Holant.Proofs.Algorithms.ControlledReduction
import Holant.Proofs.Algorithms.ReductionToFP
import Holant.Complexity.EncodedHolantOutputSize


namespace Holant.LocalDrafts.MainChain.HolographicTransport
open Computability Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [Algebra ℚ K] {d s b : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s b arity) (M N : Kernel K)

def tables : ExactSignatureTables d s b arity where
  vertex i x := F.decode.symm (Signature.coordinateAction (fun _ => N)
    (fun y => F.decode (T.vertex i y)) x)
  edge i x y := F.decode.symm (Kernel.pullback (fun a b => F.decode (T.edge i a b)) M x y)

/-- Local inverse cancellation is applied to the actual parsed network. This
retains zero values, nullary factors, self-loops and repeated endpoint pairs. -/
theorem value_eq (hMN : Kernel.mul M N = Signature.equality)
    (r : ExactSignatureTables.Input s b arity) :
    (tables F T M N).evaluate F r = T.evaluate F r := by
  rw [ExactSignatureTables.evaluate_eq_decoded, ExactSignatureTables.evaluate_eq_decoded]
  have h := congrFun (Network.denote_holographicTransform
    (r.val.realize r.property (fun i x => F.decode (T.vertex i x))
      (fun i x y => F.decode (T.edge i x y))) M N hMN) Fin.elim0
  convert h using 1 <;>
    simp only [tables, LinearEquiv.apply_symm_apply, Network.holographicTransform,
      RawClosedNetwork.realize]
  congr 1

/-- The input compiler is the real identity machine: the basis is fixed table
data, not an uncharged operation on a varying algebraic input. -/
def toTransformed (hMN : Kernel.mul M N = Signature.equality) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      (T.evaluate F) ((tables F T M N).evaluate F) :=
  controlledOneQueryOfEq (identityComputes (RawClosedNetwork.validatedEncoding s b arity))
    (identityComputes F.encoding) ((tables F T M N).outputBound F) (T.evaluate F)
    (fun r => (value_eq F T M N hMN r).symm)

def fromTransformed (hMN : Kernel.mul M N = Signature.equality) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      ((tables F T M N).evaluate F) (T.evaluate F) :=
  controlledOneQueryOfEq (identityComputes (RawClosedNetwork.validatedEncoding s b arity))
    (identityComputes F.encoding) (T.outputBound F) ((tables F T M N).evaluate F)
    (value_eq F T M N hMN)

/-- Integration with a branch's implemented evaluator; this does not assert
that any unimplemented tractable branch has such an evaluator. -/
def computes (hMN : Kernel.mul M N = Signature.equality)
    (a : Computes (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      ((tables F T M N).evaluate F)) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) F.encoding (T.evaluate F) :=
  ReductionToFP.computes (toTransformed F T M N hMN) a

end
end Holant.LocalDrafts.MainChain.HolographicTransport
