import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureUniformFour
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoSource

/-! The precise remaining pure-equality support case. Every failure of a
single weight class modulo four is consumed by a physical odd or charge-two
source, preserving the full table and its exact native oracle target. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoFamily
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false


theorem pair {K : Type*} [Zero K] {n : ℕ} (f : Signature K n)
    (parity : NoIPureOddFace.UniformParity f) (mixed : ¬UniformFour f) :
    ∃x y,f x≠0 ∧ f y≠0 ∧ ((weight x : ℤ)-weight y)%4=2 := by
  classical
  unfold UniformFour at mixed
  push_neg at mixed
  obtain ⟨x,y,hx,hy,different⟩:=mixed
  obtain ⟨b,uniform⟩:=parity
  have same:= (uniform x hx).trans (uniform y hy).symm
  have hp : (weight x%2=1)↔(weight y%2=1):=decide_eq_decide.mp same
  exact ⟨x,y,hx,hy,by omega⟩

variable {size degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin size)→Signature L (arity i.val)) (F : FixedField L degree)
variable (pins : Bool→NativeAntiTargetSource.Output H 1)
variable (pinsForm : ∀bit,(pins bit).network.denote=NoIPurePinProjection.pin bit)
variable (Q : NativeAntiTargetSource.Output H 4) (p q : L) (pn : p≠0) (qn : q≠0)
variable (qform : Q.network.denote=NoIPureEqualityCap.pure p q)

include pinsForm pn qn qform in
theorem classified {n : ℕ} (N : NativeAntiTargetSource.Output H n)
    (mixed : ¬UniformFour N.network.denote) :
    Tract (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient L H)) ∨
      (NoISuppliedIdentityConsumer.target L H F).Hard := by
  classical
  by_cases parity : NoIPureOddFace.UniformParity N.network.denote
  · exact NoIPureChargeTwoSource.classified L H F pins pinsForm Q p q pn qn qform N
      (pair N.network.denote parity mixed)
  · exact NoIPureOddSource.classified L H F pins pinsForm Q p q pn qn qform N parity

include pinsForm pn qn qform in
theorem family : (∀j,UniformFour (H j)) ∨
    Tract (familyAction sourceKBasis (GlobalCloseCompletionUnaryDescentSource.ambient L H)) ∨
      (NoISuppliedIdentityConsumer.target L H F).Hard := by
  classical
  by_cases all:∀j,UniformFour (H j)
  · exact Or.inl all
  · push_neg at all
    obtain ⟨j,bad⟩:=all
    exact Or.inr (classified L H F pins pinsForm Q p q pn qn qform (NoIPureOddSource.literal H j)
      (by simpa only [NoIPureOddSource.literal_value] using bad))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoFamily
end
