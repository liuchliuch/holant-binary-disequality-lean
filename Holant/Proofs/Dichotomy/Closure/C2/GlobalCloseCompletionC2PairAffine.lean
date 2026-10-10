import Holant.Proofs.Dichotomy.Closure.Product.GlobalCloseCompletionProductAncestorAffine
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryPair
import Holant.Proofs.Hardness.EOBinaryPlaneTract

/-! Literal affine witnesses for the finite fourth-root equality-pair
residual. These are class proofs, with the original coefficients retained;
no unary or analytic bit flip is declared to be a physical graph resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2PairAffine
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (pair symmetric)
end P
namespace M
export GeneralEOAffinePlaneChain (binary bitIndex)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def flipPairs (x : Fin 4→Bool) : Fin 4→Bool := ![x 0,!(x 1),x 2,!(x 3)]

theorem flipPairs_affine : IsAffineMap flipPairs := by unfold IsAffineMap; decide

theorem pair_affine {f : Signature AlgebraicComplex 2} (hf : Affine f) : Affine (P.pair f) := by
  have h := (EOBinaryPlaneTract.affine_lift hf).precompose flipPairs flipPairs_affine
  convert h using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [P.pair,EOBinaryPlaneCore.lift,flipPairs,h0,h1,h2,h3]

def parity (x : Fin 2→Bool) : Fin 1→Bool := fun _=>x 0 ^^ x 1

theorem parity_affine : IsAffineMap parity := by unfold IsAffineMap; decide

theorem binary_fourth (a d : AlgebraicComplex) (ha : a≠0) (fourth : a^4=d^4) :
    Affine (M.binary (P.symmetric a d)) := by
  have h := (GlobalCloseCompletionProductAncestorAffine.unary_of_equal_fourth_powers
    (0 : Fin 1) a d ha fourth).precompose parity parity_affine
  convert h using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [M.binary,M.bitIndex,P.symmetric,parity,h0,h1]

theorem diagonal_affine (a : AlgebraicComplex) : Affine (M.binary (P.symmetric a 0)) := by
  have h := (Holant.Tractable.SymmetricBinaryPullback.affine_diagonal_of_fourth_power_eq
    1 1 one_ne_zero rfl).scale a
  convert h using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [M.binary,M.bitIndex,P.symmetric,kernelSignature,Holant.Tractable.SymmetricBinaryPullback.diagonal,h0,h1]

def flipSecond (x : Fin 2→Bool) : Fin 2→Bool := ![x 0,!(x 1)]

theorem flipSecond_affine : IsAffineMap flipSecond := by unfold IsAffineMap; decide

theorem anti_affine (d : AlgebraicComplex) : Affine (M.binary (P.symmetric 0 d)) := by
  have h := (diagonal_affine d).precompose flipSecond flipSecond_affine
  convert h using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [M.binary,M.bitIndex,P.symmetric,flipSecond,h0,h1]

theorem pair_zero_left (d : AlgebraicComplex) : Affine (P.pair (M.binary (P.symmetric 0 d))) :=
  pair_affine (anti_affine d)
theorem pair_zero_right (a : AlgebraicComplex) : Affine (P.pair (M.binary (P.symmetric a 0))) :=
  pair_affine (diagonal_affine a)
theorem pair_fourth (a d : AlgebraicComplex) (ha : a≠0) (fourth : a^4=d^4) :
    Affine (P.pair (M.binary (P.symmetric a d))) := pair_affine (binary_fourth a d ha fourth)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2PairAffine
end
