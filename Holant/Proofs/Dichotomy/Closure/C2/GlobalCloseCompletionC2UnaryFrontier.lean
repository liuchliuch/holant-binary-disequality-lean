import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2FlatFrontier
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OddDescent
import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopUnaryCurrent

/-! The retained nonflat odd base reduces to an actual unary. Every larger
odd minimum triggers the same real, strictly decreasing factor-catalogue
restart. The unary source is instantiated exactly; its genuine isotropic and
nonisotropic residuals are exposed by Completion, never assumed terminal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2UnaryFrontier
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace F
export GlobalCloseCompletionRetainedFlatLeaf (Predicate)
end F
namespace R
export GlobalCloseCompletionRetainedPredicateLeaf (Minimum)
end R
namespace S
export GlobalCloseCompletionC2FlatRestart (Output)
end S
namespace O
export GlobalCloseCompletionStopOrdinarySource (family table)
end O
namespace U
export GlobalCloseCompletionStopUnaryCurrent (Completion complete)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (torsion : ResidualTorsion P.family) (hI : RetainsIdentity P.family)
variable (M : R.Minimum G P (F.Predicate G))

include torsion hI in
theorem odd_base (odd : Odd M.signature.1) : M.signature.1=1 ∨ Nonempty (S.Output G P M) := by
  classical
  by_cases one : M.signature.1=1
  · exact Or.inl one
  generalize literal : M.signature=q at odd one
  obtain ⟨n,f⟩ := q
  dsimp at odd one
  have bad : ¬F.Predicate G ⟨n,f⟩ := literal ▸ M.bad
  have positive := GlobalCloseCompletionC2FlatNonzero.positive (ClosurePhysicalBridge.complexEmbedding G) f bad
  have nonzero := GlobalCloseCompletionC2FlatNonzero.nonzero (ClosurePhysicalBridge.complexEmbedding G) f bad
  have three : 3≤n := by obtain ⟨k,hk⟩ := odd;omega
  obtain ⟨m,rfl⟩ : ∃m,n=m+3 := ⟨n-3,by omega⟩
  have retained : (⟨m+3,f⟩ : AnySignature (OI.K G))∈P.family := literal ▸ M.retained
  obtain ⟨q,actual,badQ⟩ := GlobalCloseCompletionC2OddDescent.smaller P.family torsion hI
    (ClosurePhysicalBridge.complexEmbedding G) f (Gadget.realizes_of_mem P.family .disequality f retained) nonzero odd
  have nonzeroQ := GlobalCloseCompletionC2FlatNonzero.nonzero (ClosurePhysicalBridge.complexEmbedding G) q badQ
  refine Or.inr ⟨⟨⟨m+1,q⟩,nonzeroQ,by change 0<m+1;omega,actual,badQ,?_⟩⟩
  simp only [literal]
  omega

theorem unary_source (one : M.signature.1=1) :
    ∃u : Signature (OI.K G) 1,∃retained : (⟨1,u⟩ : AnySignature (OI.K G))∈P.family,
      Nonempty (U.Completion G P u retained) := by
  generalize literal : M.signature=q at one
  obtain ⟨n,u⟩ := q
  dsimp at one
  subst n
  have retained : (⟨1,u⟩ : AnySignature (OI.K G))∈P.family := literal ▸ M.retained
  exact ⟨u,retained,⟨U.complete G P u retained⟩⟩

variable (cardTwo : Nat.card (completeGroup P.family torsion)=2)
variable (c : OI.K G) (hc : c≠0)
variable (actualRM : Gadget.Realizes P.family .disequality (c • GlobalCloseCompletionC2RMActual.rm))

include torsion hI cardTwo hc actualRM in
theorem frontier : Tract (O.family G P) ∨ NoXWeightedAntiSquares.Hard G ∨
    GlobalCloseCompletionC2OrdinaryPairOutcome.HasEq4 (O.table G P) ∨
    ∃M : R.Minimum G P (F.Predicate G),M.signature.1=1 ∨ Nonempty (S.Output G P M) := by
  rcases GlobalCloseCompletionC2FlatFrontier.frontier G P torsion hI cardTwo c hc actualRM with tract|hard|anchor|⟨M,odd|decrease⟩
  · exact Or.inl tract
  · exact Or.inr (Or.inl hard)
  · exact Or.inr (Or.inr (Or.inl anchor))
  · exact Or.inr (Or.inr (Or.inr ⟨M,odd_base G P torsion hI M odd⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨M,Or.inr decrease⟩))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2UnaryFrontier
end
