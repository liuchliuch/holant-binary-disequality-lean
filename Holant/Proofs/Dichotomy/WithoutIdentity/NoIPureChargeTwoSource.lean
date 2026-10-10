import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoFace
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoSmall
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureOddSource

/-! A charge-two support difference supplies a genuine nonsingular native
diagonal source. The non-parity alternative is also consumed internally.
Pure Eq4 and the two native pins are actual labelled graphs throughout. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace O
export NativeAntiTargetSource (Output)
end O
namespace P
export NoIPurePinProjection (pin)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
section Generic
variable {K : Type} [Field K] [Algebra ℚ K] {size : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin size)→Signature K (arity i.val))
variable (pins : Bool→O.Output H 1) (pinsForm : ∀bit,(pins bit).network.denote=P.pin bit)
variable (Q : O.Output H 4) (p q : K) (pn : p≠0) (qn : q≠0)
variable (qform : Q.network.denote=NoIPureEqualityCap.pure p q)
include pinsForm pn qn qform in
theorem binary {n : ℕ} (N : O.Output H n)
    (mixed : ∃x y,N.network.denote x≠0 ∧ N.network.denote y≠0 ∧ ((weight x : ℤ)-weight y)%4=2) :
    ∃B : O.Output H 2,B.network.denote (fun _=>false)≠0 ∧ B.network.denote (fun _=>true)≠0 := by
  classical
  by_cases parity : NoIPureOddFace.UniformParity N.network.denote
  · obtain ⟨m,positive,R,mask,u,v,un,vn,charge,form⟩:=
      NoIPureChargeTwoFace.source H pins pinsForm N parity mixed
    let reduced:=NoIPureChargeTwoReduce.produce H Q p q pn qn qform R mask u v un vn form
      (by rw [charge];norm_num)
    have small : NoIPureChargeTwoReduce.Reduced H 2 := charge ▸ reduced
    exact NoIPureChargeTwoSmall.source H small
  · obtain ⟨U,top,bottom⟩:=NoIPureOddSource.unary H pins pinsForm Q p q pn qn qform N parity
    refine ⟨GlobalCloseCompletionComplementQ4Templates.tensor H (m:=1) (n:=1) U U,?_,?_⟩
    · change (Holant.Complexity.BinaryInterpolation.Chains.tensor U.network U.network).denote (fun _=>false)≠0
      rw [Holant.Complexity.BinaryInterpolation.Chains.tensor_denote]
      exact mul_ne_zero top top
    · change (Holant.Complexity.BinaryInterpolation.Chains.tensor U.network U.network).denote (fun _=>true)≠0
      rw [Holant.Complexity.BinaryInterpolation.Chains.tensor_denote]
      exact mul_ne_zero bottom bottom
end Generic

section Original
variable {size degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin size)→Signature L (arity i.val)) (F : FixedField L degree)
variable (pins : Bool→O.Output H 1) (pinsForm : ∀bit,(pins bit).network.denote=P.pin bit)
variable (Q : O.Output H 4) (p q : L) (pn : p≠0) (qn : q≠0)
variable (qform : Q.network.denote=NoIPureEqualityCap.pure p q)
variable {n : ℕ} (N : O.Output H n)
variable (mixed : ∃x y,N.network.denote x≠0 ∧ N.network.denote y≠0 ∧ ((weight x : ℤ)-weight y)%4=2)

def data : NoISuppliedIdentityData.Data L H F := by
  classical
  apply Classical.choice
  obtain ⟨B,top,bottom⟩:=binary H pins pinsForm Q p q pn qn qform N mixed
  exact ⟨NoIPureEqualitySource.cofactor L H F Q B p q pn qn qform top bottom⟩

include pinsForm pn qn qform N mixed in
theorem classified :
    Tract (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient L H)) ∨
      (NoISuppliedIdentityConsumer.target L H F).Hard :=
  NoISuppliedIdentityConsumer.tract_or_hard L H F (data L H F pins pinsForm Q p q pn qn qform N mixed)
end Original


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoSource
end
