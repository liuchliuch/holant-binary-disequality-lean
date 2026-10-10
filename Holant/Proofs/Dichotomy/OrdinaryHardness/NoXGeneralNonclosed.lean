import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLatticeSupport
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSupportSplit

/-! A non-affine support in any actual even block gives original-oracle
hardness without a supplied anti row. Missing meets or joins produce either
three support points or a usable even anti; the remaining finite lattice
has a missing relative complement, exposed by an unsigned interval minor. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralNonclosed
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace C
export GeneralEONegativeClosedSupport (Closed)
end C
namespace N
export NoXGeneralEvenAntiNonclosed (resource_nonclosed binary binary_nonaffine binary_nonproduct)
end N
namespace P
export NoXGeneralUnsignedBinary (meet join restrict restrict_value)
end P
namespace L
export NoXGeneralLatticeSupport (Below extrema relative ternary_of_relative chainPorts chain_values)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (row : B.Block (s:=src.size) (b:=src.b) n)
variable (nonclosed : ¬C.Closed (fun x=>(row.signature src.H x : AlgebraicComplex)))

include nonclosed in
theorem hard_of_anti (anti : NoXGeneralSupportSplit.EvenAnti G src) :
    NoXWeightedAntiResourcesOriginal.Hard G := by
  obtain ⟨antiRow,v,w,hv,hw,lit⟩ := anti
  exact NoXGeneralEvenAntiBinary.countingHard G src
    (N.binary src.K src.H row nonclosed antiRow) antiRow v w hv hw lit
    (N.binary_nonaffine src.K src.H row nonclosed antiRow v w hv hw lit)
    (N.binary_nonproduct src.K src.H row nonclosed antiRow v w hv hw lit)

include nonclosed in
theorem countingHard : NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  let R : (Fin n→Bool)→Prop := fun x=>row.signature src.H x≠0
  have failed := N.resource_nonclosed src.K src.H row nonclosed
  have split (x y : Fin n→Bool) (hx : R x) (hy : R y)
      (hole : row.signature src.H (P.meet x y)=0 ∨ row.signature src.H (P.join x y)=0) :
      NoXWeightedAntiResourcesOriginal.Hard G := by
    rcases NoXGeneralSupportSplit.anti_or_hard G src row x y hx hy hole with hard|anti
    · exact hard
    · exact hard_of_anti G src row nonclosed anti
  by_cases hm : ∀x y,R x→R y→R (P.meet x y)
  · by_cases hj : ∀x y,R x→R y→R (P.join x y)
    · have nonempty : ∃x,R x := by
        by_contra hh
        push Not at hh
        apply failed
        intro x y z hx _ _
        exact False.elim (hh x hx)
      obtain ⟨lo,hi,hlo,hhi,bounds⟩ := L.extrema R hm hj nonempty
      have missing : ∃mid,R mid ∧ ¬R (L.relative lo hi mid) := by
        by_contra hh
        push Not at hh
        exact failed (L.ternary_of_relative R hm hj lo hi bounds hh)
      obtain ⟨mid,hmid,hole⟩ := missing
      let q:=P.restrict row (L.chainPorts lo mid hi)
      have vals:=L.chain_values lo mid hi (bounds mid hmid).1 (bounds mid hmid).2
      have zero : q.signature src.H ![false,true]=0 := by
        rw [P.restrict_value,vals.2.1]
        exact not_ne_iff.mp hole
      apply NoXGeneralThreeSupport.EvenBlock.countingHard G src q.rows q.balanced (false,true) zero
      intro u v ne
      change q.signature src.H ![u,v]≠0
      rw [P.restrict_value]
      cases u <;> cases v
      · rwa [vals.1]
      · exact False.elim (ne rfl)
      · rwa [vals.2.2.1]
      · rwa [vals.2.2.2]
    · push Not at hj
      obtain ⟨x,y,hx,hy,hole⟩ := hj
      exact split x y hx hy (Or.inr (not_ne_iff.mp hole))
  · push Not at hm
    obtain ⟨x,y,hx,hy,hole⟩ := hm
    exact split x y hx hy (Or.inl (not_ne_iff.mp hole))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralNonclosed
end
