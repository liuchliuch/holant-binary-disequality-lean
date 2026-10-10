import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralUnsignedBinary
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralThreeSupport
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralEvenAntiResources
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! A supported pair whose coordinatewise meet or join is absent gives a
literal unsigned binary restriction: three support points imply direct
hardness, and two opposite support points supply an actual even anti block. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralSupportSplit
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
export OrdinaryNegativeXUniversalResource (EvenBad)
end B
namespace P
export NoXGeneralUnsignedBinary (meet join pairPorts pair_values restrict restrict_value anti_of_two_zeros)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s n : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'

def EvenAnti : Prop := ∃row : B.Block (s:=src.size) (b:=src.b) 2,∃v w : src.K,
  v≠0 ∧ w≠0 ∧ row.signature src.H=NoXWeightedAntiSigned.anti v w

variable (row : B.Block (s:=src.size) (b:=src.b) n) (x y : Fin n→Bool)
variable (hx : row.signature src.H x≠0) (hy : row.signature src.H y≠0)
variable (hole : row.signature src.H (P.meet x y)=0 ∨ row.signature src.H (P.join x y)=0)

include hx hy hole in
theorem anti_or_hard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G ∨ EvenAnti G src := by
  classical
  let q:=P.restrict row (P.pairPorts x y)
  have vals := P.pair_values x y
  have h00 : q.signature src.H ![false,false]=row.signature src.H (P.meet x y) := by
    rw [P.restrict_value,vals.1]
  have h01 : q.signature src.H ![false,true]=row.signature src.H y := by
    rw [P.restrict_value,vals.2.1]
  have h10 : q.signature src.H ![true,false]=row.signature src.H x := by
    rw [P.restrict_value,vals.2.2.1]
  have h11 : q.signature src.H ![true,true]=row.signature src.H (P.join x y) := by
    rw [P.restrict_value,vals.2.2.2]
  have live01 : q.signature src.H ![false,true]≠0 := by rwa [h01]
  have live10 : q.signature src.H ![true,false]≠0 := by rwa [h10]
  by_cases bottom : q.signature src.H ![false,false]=0
  · by_cases top : q.signature src.H ![true,true]=0
    · exact Or.inr ⟨q,q.signature src.H ![false,true],q.signature src.H ![true,false],
        live01,live10,P.anti_of_two_zeros _ bottom top⟩
    · left
      apply NoIOrdinaryRaw.NoXGeneralThreeSupport.EvenBlock.countingHard G src q.rows q.balanced (false,false) bottom
      intro u v ne
      change q.signature src.H ![u,v]≠0
      cases u <;> cases v
      · exact False.elim (ne rfl)
      · exact live01
      · exact live10
      · exact top
  · have top : q.signature src.H ![true,true]=0 := by
      rcases hole with h|h
      · exact False.elim (bottom (h00.trans h))
      · exact h11.trans h
    left
    apply NoIOrdinaryRaw.NoXGeneralThreeSupport.EvenBlock.countingHard G src q.rows q.balanced (true,true) top
    intro u v ne
    change q.signature src.H ![u,v]≠0
    cases u <;> cases v
    · exact bottom
    · exact live01
    · exact live10
    · exact False.elim (ne rfl)

variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
include negative hx hy hole in
theorem hard_of_even (bad : B.EvenBad src.H) : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  rcases anti_or_hard G src row x y hx hy hole with hard|⟨antiRow,v,w,hv,hw,lit⟩
  · exact hard
  · exact NoIOrdinaryRaw.NoXGeneralEvenAntiResources.hard_of_even G src antiRow v w hv hw lit negative bad

include negative in
theorem meet_join_of_noHard (bad : B.EvenBad src.H) (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G)
    (hx : row.signature src.H x≠0) (hy : row.signature src.H y≠0) :
    row.signature src.H (P.meet x y)≠0 ∧ row.signature src.H (P.join x y)≠0 := by
  constructor
  · intro zero
    exact noHard (hard_of_even G src row x y hx hy (Or.inl zero) negative bad)
  · intro zero
    exact noHard (hard_of_even G src row x y hx hy (Or.inr zero) negative bad)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralSupportSplit
end
