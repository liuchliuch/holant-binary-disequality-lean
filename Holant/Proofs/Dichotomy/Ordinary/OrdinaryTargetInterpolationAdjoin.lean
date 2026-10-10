import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationFamily
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationDiagonal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationChain

/-! Adjoin any fixed diagonal target by actual positive-chain interpolation
from a single old-alphabet diagonal macro of infinite ratio. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationAdjoin
open Holant Holant.Algebraic Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation Holant.Complexity.BinaryInterpolation.Chains
open Holant.LocalDrafts.BinaryInterpolation Holant.Certificates.MatchingContractionClosure
namespace M
export OrdinaryTargetInterpolationMachine (Data)
end M
namespace R
export OrdinaryTargetInterpolationRecovery (G kernels S)
end R
namespace F
export OrdinaryTargetInterpolationFamily (signatures tables old_literal new_literal controlled)
end F
namespace D
export OrdinaryTargetInterpolationDiagonal (diagonal pencil)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {n s b : ℕ} {arity : ℕ→ℕ}
variable (field : FixedField K n) (T : ExactSignatureTables n s b arity)
variable (g : Template) (valid : g.WellFormed s b arity) (binary : g.boundary=2)
variable (edge : Fin b) (a c target : K)
def data : M.Data field T where
  template := g
  valid := valid
  binary := binary
  edge := edge
  gamma := a
  rho := c/a
  target := target
abbrev d := data field T g valid binary edge a c target
variable (ordinary : R.kernels (field:=field) (T:=T) edge=Signature.equality)
variable (hmacro : (⟨g.boundary,(g.network valid (R.G (field:=field) (T:=T))
  (R.kernels (field:=field) (T:=T))).denote⟩ : AnySignature K)=
  ⟨2,binarySignature (D.diagonal a c)⟩)
include ordinary hmacro in
theorem chain (ha : a≠0) (k : ℕ) :
    ((explicitTemplate s edge.val k).network
      (explicitTemplate_wellFormed (PhysicalQueries.A (s:=s) arity g) PhysicalQueries.newLabel
        (PhysicalQueries.new_arity (s:=s) arity g binary) edge k)
      (R.S (d field T g valid binary edge a c target))
      (R.kernels (field:=field) (T:=T))).denote =
      binarySignature (a^(k+1) • (D.diagonal 1 0+(c/a)^(k+1) • D.diagonal 0 1)) := by
  have h := OrdinaryTargetInterpolationChain.explicitTemplate_denote_I
    (PhysicalQueries.A (s:=s) arity g) (PhysicalQueries.newLabel (s:=s))
    (PhysicalQueries.new_arity (s:=s) arity g binary) edge k (D.diagonal a c)
    (OriginalTables.tables g valid (R.G (field:=field) (T:=T))
      (R.kernels (field:=field) (T:=T))) (R.kernels (field:=field) (T:=T))
    ((OriginalTables.tables_new g valid (R.G (field:=field) (T:=T))
      (R.kernels (field:=field) (T:=T))).trans hmacro) ordinary
  exact h.trans (congrArg binarySignature (D.pencil a c ha (k+1)))

abbrev signatures := F.signatures (d field T g valid binary edge a c target)
  (D.diagonal 1 0) (D.diagonal 0 1)
abbrev tables := F.tables (d field T g valid binary edge a c target)
  (D.diagonal 1 0) (D.diagonal 0 1)

/-- The new literal is the requested diagonal, with no projective scalar. -/
theorem new_literal :
    (⟨PhysicalQueries.A (s:=s) arity g s,
      signatures field T g valid binary edge a c target PhysicalQueries.newLabel⟩ : AnySignature K)=
      ⟨2,binarySignature (D.diagonal 1 target)⟩ := by
  have h := F.new_literal (d field T g valid binary edge a c target) (D.diagonal 1 0) (D.diagonal 0 1)
  refine h.trans ?_
  apply congrArg (fun B : Binary (K:=K)=>(⟨2,binarySignature B⟩ : AnySignature K))
  ext x y
  cases x <;> cases y <;> simp [D.diagonal,data,d]


def controlled (ha : a≠0) (hc : c≠0) (infinite : ∀k : ℕ,0<k→(c/a)^k≠1) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (s+1) b (PhysicalQueries.A (s:=s) arity g)) field.encoding
      (RawClosedNetwork.validatedEncoding s b arity) field.encoding
      ((tables field T g valid binary edge a c target).evaluate field) (T.evaluate field) :=
  F.controlled (d field T g valid binary edge a c target) (D.diagonal 1 0) (D.diagonal 0 1)
    (chain field T g valid binary edge a c target ordinary hmacro ha) ha
    (OrdinaryNegativeBinaryUnsignedInterpolationFormulas.nodes_injective (c/a) (div_ne_zero hc ha) infinite)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationAdjoin
end
