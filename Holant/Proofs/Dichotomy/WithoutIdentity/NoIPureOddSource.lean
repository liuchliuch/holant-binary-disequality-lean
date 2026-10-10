import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeLiteral
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureOddFace
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureOddSmall
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoReduce
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureEqualitySource

/-! A pure quaternary equality and both genuine native pins eliminate every
non-parity row. All contractions are physical and the final hardness arm is
controlled at the exact original native-X target. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureOddSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace O
export NativeAntiTargetSource (Output)
end O
namespace P
export NoIPurePinProjection (pin)
end P
namespace W
export NoIPureChargeTwoWords (row)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
section Generic
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (arity i.val))
variable (pins : Bool→O.Output H 1) (pinsForm : ∀bit,(pins bit).network.denote=P.pin bit)
variable (Q : O.Output H 4) (p q : K) (pn : p≠0) (qn : q≠0)
variable (qform : Q.network.denote=NoIPureEqualityCap.pure p q)

include pinsForm pn qn qform in
theorem unary {n : ℕ} (N : O.Output H n) (mixed : ¬NoIPureOddFace.UniformParity N.network.denote) :
    ∃U : O.Output H 1,U.network.denote (fun _=>false)≠0 ∧ U.network.denote (fun _=>true)≠0 := by
  obtain ⟨m,odd,positive,R,mask,a,b,an,bn,nonzero,form⟩:=NoIPureOddFace.source H pins pinsForm N mixed
  have rf:R.network.denote=W.row mask a b:=form
  let S:=NoIPureChargeTwoReduce.produce H Q p q pn qn qform R mask a b an bn rf nonzero
  have parity:Odd S.arity:=by
    obtain ⟨k,hk⟩:=odd
    have eqn:=S.charge
    unfold charge at eqn
    refine ⟨S.arity/2,?_⟩
    omega
  exact NoIPureOddSmall.source H Q p q pn qn qform S.graph S.mask S.left S.right
    S.left_nonzero S.right_nonzero S.form parity S.small


end Generic

section Original
variable {s degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (J : (i : Fin s)→Signature L (arity i.val)) (F : FixedField L degree)
variable (pins : Bool→O.Output J 1) (pinsForm : ∀bit,(pins bit).network.denote=P.pin bit)
variable (Q : O.Output J 4) (p q : L) (pn : p≠0) (qn : q≠0)
variable (qform : Q.network.denote=NoIPureEqualityCap.pure p q)

include pinsForm pn qn qform in
theorem classified {n : ℕ} (N : O.Output J n) (mixed : ¬NoIPureOddFace.UniformParity N.network.denote) :
    Tract (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient L J)) ∨
      (NoISuppliedIdentityConsumer.target L J F).Hard := by
  obtain ⟨U,top,bottom⟩:=unary J pins pinsForm Q p q pn qn qform N mixed
  exact NoIPureEqualitySource.unary_classified L J F Q U p q pn qn qform top bottom

include pinsForm pn qn qform in
theorem family : (∀j,NoIPureOddFace.UniformParity (J j)) ∨
    Tract (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient L J)) ∨
      (NoISuppliedIdentityConsumer.target L J F).Hard := by
  classical
  by_cases all:∀j,NoIPureOddFace.UniformParity (J j)
  · exact Or.inl all
  · push_neg at all
    obtain ⟨j,bad⟩:=all
    exact Or.inr (classified L J F pins pinsForm Q p q pn qn qform (literal J j)
      (by simpa only [literal_value] using bad))
end Original


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureOddSource
end
