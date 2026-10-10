import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicHigherField
import Holant.ReedMuller.MatchingConsistency.Source

/-! Actual current cyclic I/X cards give the full fixed-representative deck.
Matching factors may be arbitrary nonsingular I/X-span matrices; this is not
the stronger literal C2 matching hypothesis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicHigherDeck
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain
open Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open ClosureSourceRows RingHomRealization
namespace CF
export GlobalCloseCompletionCyclicHigherField (actual_span matching_map)
end CF
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false

def representatives : FixedIXRepresentatives where
  kernel p := originalC2Binary p
  scale _ := 1
  scale_ne_zero _ := one_ne_zero
  exact := by
    intro p
    cases p <;> ext a b <;> simp [originalC2Binary,X,Signature.equality,Matrix.one_apply]

def Deck (G : Set (Binary (K:=ℂ))) {m : ℕ} (f : Signature ℂ (m+2)) : Prop :=
  ∀e : Equiv.Perm (Fin (m+2)),∀p : Bool,
    MatchingOrZero G (Signature.contract (originalC2Binary p) (Tensor.reindex e.symm f))

theorem Deck.canonical {G : Set (Binary (K:=ℂ))} {m : ℕ} {f : Signature ℂ (m+2)}
    (deck : Deck G f) : CanonicalMatchingDeck G representatives f := by
  intro i j _hij p
  exact deck (Holant.Dihedral.CompatibleClosure.pairOrder i j) p

theorem Deck.reindex {G : Set (Binary (K:=ℂ))} {m : ℕ} {f : Signature ℂ (m+2)}
    (deck : Deck G f) (e : Equiv.Perm (Fin (m+2))) : Deck G (Tensor.reindex e f) := by
  intro q p
  exact deck (q.trans e.symm) p

theorem matching_smul {I : Type*} {G : Set (Binary (K:=ℂ))} {f : Tensor ℂ I}
    (matching : MatchingOrZero G f) (c : ℂ) : MatchingOrZero G (c • f) := by
  by_cases hc : c=0
  · left
    simp [hc]
  rcases matching with rfl|⟨M,valid,nonzero,rfl⟩
  · left
    simp
  · right
    refine ⟨⟨M.edges,M.ports,M.matrix,c*M.scalar⟩,valid,mul_ne_zero hc nonzero,?_⟩
    funext x
    simp only [Presentation.tensor,productValue,Pi.smul_apply,smul_eq_mul,mul_assoc]

theorem Deck.smul {G : Set (Binary (K:=ℂ))} {m : ℕ} {f : Signature ℂ (m+2)}
    (deck : Deck G f) (c : ℂ) : Deck G (c • f) := by
  intro e p
  have he : Tensor.reindex e.symm (c • f)=c • Tensor.reindex e.symm f := rfl
  rw [he]
  have hc : Signature.contract (originalC2Binary p) (c • Tensor.reindex e.symm f)=
      c • Signature.contract (originalC2Binary p) (Tensor.reindex e.symm f) := by
    funext w
    simp only [Signature.contract,Pi.smul_apply,smul_eq_mul,Fintype.sum_bool]
    ring
  rw [hc]
  exact matching_smul (deck e p) c

theorem identity_map {K : Type*} [Field K] (phi : K→+*ℂ) {F : SignatureFamily K}
    (hI : RetainsIdentity F) : RetainsIdentity (mapFamily phi F) := by
  refine ⟨_,hI,?_⟩
  apply congrArg (fun f : Signature ℂ 2=>(⟨2,f⟩ : AnySignature ℂ))
  funext x
  simp [RingHomRealization.mapAny,RingHomRealization.mapSignature,Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature,Signature.equality]

variable {K : Type*} [Field K] [NumberField K]
variable (F : SignatureFamily K) (torsion : ResidualTorsion F) (hI : RetainsIdentity F)
variable (phi : K→+*ℂ)

include hI in
theorem current_deck {m : ℕ} (f : Signature K (m+2))
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    Deck (actualTransfers (mapFamily phi F)) (RingHomRealization.mapSignature phi f) := by
  intro e p
  rw [←GlobalCloseCompletionC2SixPortCurrent.map_contract]
  exact CF.matching_map phi F _
    (DeckContraction.orderedClosure_matching F torsion hI f stable e _
      (GlobalCloseCompletionC2CurrentComplement.kernel_member F torsion hI p))

variable (cyclic : IsCyclic (completeGroup (mapFamily phi F)
  (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)))
include torsion hI cyclic in
theorem current_consistent {m : ℕ} (f : Signature K (m+2)) (nonzero : f≠0) (higher : 6≤m+2)
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    Consistent (Holant.ReedMuller.CoefficientAtlas.walsh (RingHomRealization.mapSignature phi f)) := by
  have hn : RingHomRealization.mapSignature phi f≠0 := by
    intro zero
    apply nonzero
    funext x
    have hz : phi (f x)=0 := congrFun zero x
    exact phi.injective (hz.trans (map_zero phi).symm)
  exact source_matching_consistency
    (actualTransfers_projectiveMatrixGroup _ (actualTransfers_nonempty _)
      (ClosureFieldBridgeGroups.mappedTorsion phi F torsion))
    (CF.actual_span _ (ClosureFieldBridgeGroups.mappedTorsion phi F torsion) (identity_map phi hI) cyclic)
    representatives _ hn higher (current_deck F torsion hI phi f stable).canonical


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicHigherDeck
end
