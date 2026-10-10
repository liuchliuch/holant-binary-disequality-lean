import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0CurrentSource
import Holant.Proofs.Closure.ClosureCyclicCurrentBinaryPrime
import Holant.OpenNetworkComposition.ProjectiveSubstitution

/-! The q4 source retention is a genuine open-gadget extension when its
current raw deck is matching. Every nonzero binary root is nonsingular and
prime, so the actually saved factor tree has only that same root leaf.
Consequently no independent factor oracle enters the retained source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0RetainedRealizes
open Holant Holant.Tractable Holant.Algebraic
open Holant.OpenNetworkComposition
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace C
export GlobalCloseCompletionA0CurrentSource (retained)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

private theorem prime_leaves {L : Type*} [Field L] {f : AnySignature L}
    (hp : Prime f) (T : FactorTree f) : T.leaves={f} := by
  cases T with
  | leaf => rfl
  | split split => exact (hp.2 ⟨_,_,⟨split⟩⟩).elim

include stable in
theorem root_prime (k : FullDeckIndex P.family torsion q) : Prime (fullDeckRoot P.family torsion q k).1 := by
  cases k with
  | inl j =>
    apply ClosureCyclicCurrent.nonsingular_binary_prime
    change Matrix.det (actualRepresentative P.family torsion j)≠0
    exact (actualRepresentative_actual P.family torsion j).2
  | inr k =>
    apply ClosureCyclicCurrent.nonsingular_binary_prime
    exact (ClosureSourceRows.matching_binary_zero_or_nonsingular (actualTransfers P.family)
      (actualTransfers_projectiveMatrixGroup P.family (actualTransfers_nonempty P.family) torsion)
      (rawCard P.family torsion q k.val) (stable _ (Or.inr ⟨k.val,rfl⟩))).resolve_left k.property

include core literal in
theorem root_actual (k : FullDeckIndex P.family torsion q) :
    Gadget.Realizes P.family .disequality (fullDeckRoot P.family torsion q k).1.2 :=
  (deckRootDirect G P torsion q core literal k).realizes

include stable in
theorem member_actual (f : AnySignature (OI.K G))
    (hf : f∈(C.retained G P torsion q core literal).family) : Gadget.Realizes P.family .disequality f.2 := by
  classical
  rw [ProgrammeRetained.palette_family] at hf
  rcases hf with old | batch
  · exact Gadget.realizes_of_mem P.family .disequality _ old
  · obtain ⟨k,_hk,root | leaf⟩ := (mem_batchCarrier _ _ f).mp batch
    · subst f
      exact root_actual G P torsion q core literal k
    · rw [prime_leaves (root_prime G P torsion q stable k) (fullDeckRoot P.family torsion q k).2] at leaf
      have he : f=(fullDeckRoot P.family torsion q k).1 := Multiset.mem_singleton.mp leaf
      subst f
      exact root_actual G P torsion q core literal k

include stable in
theorem backward {n : ℕ} (f : Signature (OI.K G) n)
    (actual : Gadget.Realizes (C.retained G P torsion q core literal).family .disequality f) :
    Gadget.RealizesUpTo P.family .disequality f := by
  obtain ⟨network,labels,native,denote⟩ := OrdinaryNormalization.realizes_exists_ordinary
    (C.retained G P torsion q core literal).equality actual
  rw [←denote]
  exact Holant.OpenNetworkComposition.realizes_network_upTo P.family network
    (fun v => member_actual G P torsion q core literal stable _ (labels v)) native (by norm_num)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0RetainedRealizes
end
