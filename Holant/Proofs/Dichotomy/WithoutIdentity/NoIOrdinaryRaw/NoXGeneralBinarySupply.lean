import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLowerBinary
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralNonclosed
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralEvenAntiResources
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralSupportSplit
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Actual even non-Affine/non-Product resources yield original hardness or
an actual unsigned bad binary. Support, lower words, and the finite extraction
are selected internally; no signed row or binary anti is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralBinarySupply
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace C
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
end C
namespace L
export NoXGeneralLatticeSupport (Below extrema)
end L
namespace P
export NoXGeneralUnsignedBinary (meet join)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s m n : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (first : B.Block (s:=src.size) (b:=src.b) m) (second : B.Block (s:=src.size) (b:=src.b) n)
variable (nonaffine : ¬Affine (fun x=>(first.signature src.H x : AlgebraicComplex)))
variable (nonproduct : ¬Product (fun x=>(second.signature src.H x : AlgebraicComplex)))
variable (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G)

include nonaffine nonproduct noHard in
theorem meet_join {r : ℕ} (row : B.Block (s:=src.size) (b:=src.b) r) (x y : Fin r→Bool)
    (hx : (row.signature src.H x : AlgebraicComplex)≠0)
    (hy : (row.signature src.H y : AlgebraicComplex)≠0) :
    (row.signature src.H (P.meet x y) : AlgebraicComplex)≠0 ∧
    (row.signature src.H (P.join x y) : AlgebraicComplex)≠0 := by
  have hx' : row.signature src.H x≠0 := fun hz=>hx (congrArg (fun c : src.K=>(c : AlgebraicComplex)) hz)
  have hy' : row.signature src.H y≠0 := fun hz=>hy (congrArg (fun c : src.K=>(c : AlgebraicComplex)) hz)
  have close (hole : row.signature src.H (P.meet x y)=0 ∨ row.signature src.H (P.join x y)=0) : False := by
    rcases NoIOrdinaryRaw.NoXGeneralSupportSplit.anti_or_hard G src row x y hx' hy' hole with hard|⟨anti,v,w,hv,hw,lit⟩
    · exact noHard hard
    · exact noHard (NoIOrdinaryRaw.NoXGeneralEvenAntiResources.countingHard G src first second anti v w hv hw lit nonaffine nonproduct)
  exact ⟨fun hz=>close (Or.inl (Subtype.ext hz)),fun hz=>close (Or.inr (Subtype.ext hz))⟩

include noHard in
theorem closed {r : ℕ} (row : B.Block (s:=src.size) (b:=src.b) r) :
    C.Closed (fun x=>(row.signature src.H x : AlgebraicComplex)) := by
  by_contra bad
  exact noHard (NoIOrdinaryRaw.NoXGeneralNonclosed.countingHard G src row bad)

include nonaffine nonproduct noHard in
theorem exists_binary : ∃row : B.Block (s:=src.size) (b:=src.b) 2,
    (¬Affine (fun x=>(row.signature src.H x : AlgebraicComplex))) ∧
    ¬Product (fun x=>(row.signature src.H x : AlgebraicComplex)) := by
  classical
  have firstLive : ∃x,(first.signature src.H x : AlgebraicComplex)≠0 := by
    by_contra h
    push Not at h
    exact nonaffine (Or.inl (funext h))
  have secondLive : ∃x,(second.signature src.H x : AlgebraicComplex)≠0 := by
    by_contra h
    push Not at h
    exact nonproduct (Or.inl (funext h))
  have h1:=meet_join G src first second nonaffine nonproduct noHard first
  have h2:=meet_join G src first second nonaffine nonproduct noHard second
  obtain ⟨lo,_,hlo,_,leftBounds⟩ := L.extrema (fun x=>(first.signature src.H x : AlgebraicComplex)≠0)
    (fun x y hx hy=>(h1 x y hx hy).1) (fun x y hx hy=>(h1 x y hx hy).2) firstLive
  obtain ⟨hi,_,hhi,_,rightBounds⟩ := L.extrema (fun x=>(second.signature src.H x : AlgebraicComplex)≠0)
    (fun x y hx hy=>(h2 x y hx hy).1) (fun x y hx hy=>(h2 x y hx hy).2) secondLive
  exact NoXGeneralLowerBinary.exists_binary src.K src.H first second lo hi
    (fun x hx=>(leftBounds x hx).1) (fun x hx=>(rightBounds x hx).1) hlo hhi
    (closed G src noHard first) (closed G src noHard second) nonaffine nonproduct

include nonaffine nonproduct in
theorem binary_or_hard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G ∨
    ∃row : B.Block (s:=src.size) (b:=src.b) 2,
      (¬Affine (fun x=>(row.signature src.H x : AlgebraicComplex))) ∧
      ¬Product (fun x=>(row.signature src.H x : AlgebraicComplex)) := by
  classical
  by_cases hard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G
  · exact Or.inl hard
  · exact Or.inr (exists_binary G src first second nonaffine nonproduct hard)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralBinarySupply
end
