import Holant.OpenNetworkComposition.ProjectiveSubstitution
import Holant.Proofs.FiniteGroups.Stabilization.DirectScalars

/-! Open networks with the exact effective edge X B X are projectively
native-X realizable when B is an actual binary and literal I is retained.
Every closure attaches that same actual B; no analytic edge is a free oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0KernelRealizes
open Holant
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.OpenNetworkComposition
open Holant.OpenNetworkComposition.ProjectiveSubstitution
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
universe u v w z
variable {K : Type u} [Field K]

variable (B : Binary (K:=K))

abbrev edge : Kernel K := (X * B * X : Matrix Bool Bool K)

theorem edge_kernel : edge B=Kernel.mul (Kernel.mul Signature.disequality B) Signature.disequality := by
  funext b c
  cases b <;> cases c <;> simp [edge,Matrix.mul_apply,X,Kernel.mul_apply,Signature.disequality]

theorem contract_exact {n : ℕ} (F : SignatureFamily K) (hI : RetainsIdentity F)
    (hB : Gadget.Realizes F .disequality (binarySignature B))
    (q : Signature K (n+2)) (hq : Gadget.Realizes F .disequality q) :
    Gadget.Realizes F .disequality (Signature.contract (edge B) q) := by
  have hs := realizes_splice F q _ hq hB (1 : Fin (n+2))
  have hc := realizes_contract_exact_of_identity F hI _ hs
  rw [close_splice_table] at hc
  exact hc

theorem contract_upTo {n : ℕ} (F : SignatureFamily K) (hI : RetainsIdentity F)
    (hB : Gadget.Realizes F .disequality (binarySignature B))
    (q : Signature K (n+2)) (hq : Gadget.RealizesUpTo F .disequality q) :
    Gadget.RealizesUpTo F .disequality (Signature.contract (edge B) q) := by
  obtain ⟨c,hc,hq⟩ := hq
  refine ⟨c,hc,?_⟩
  have h := contract_exact B F hI hB (fun x => c*q x) hq
  convert h using 1
  funext x
  simp only [Signature.contract,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  ring

private theorem contractPair_ordered {P : Type*} [DecidableEq P] (u v : P) (huv : u≠v)
    {n : ℕ} (r : Remaining u v ≃ Fin n) (f : Tensor K P) :
    Tensor.reindex r (contractPair u v (edge B) f)=
      Signature.contract (edge B) (Tensor.reindex (pairOrder u v huv r).symm f) := by
  funext x
  unfold Tensor.reindex contractPair Signature.contract
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 2
  funext i
  obtain ⟨j,rfl⟩ := (pairOrder u v huv r).surjective i
  rw [Equiv.symm_apply_apply]
  cases j using Fin.cases with
  | zero => simp [insertPair_first huv]
  | succ j =>
    cases j using Fin.cases with
    | zero => simp [insertPair_second]
    | succ j =>
      rw [pairOrder_tail,insertPair_other (r.symm j).property.1 (r.symm j).property.2]
      simp

private theorem actual_contractPair {P : Type*} [Fintype P] [DecidableEq P]
    {F : SignatureFamily K} {f : Tensor K P} (hI : RetainsIdentity F)
    (hB : Gadget.Realizes F .disequality (binarySignature B)) (hf : Actual F f)
    (u v : P) (huv : u≠v) : Actual F (contractPair u v (edge B) f) := by
  let r := Fintype.equivFin (Remaining u v)
  refine ⟨Fintype.card (Remaining u v),r,?_⟩
  rw [contractPair_ordered B u v huv r]
  exact contract_upTo B F hI hB _ (hf.ordered (pairOrder u v huv r).symm)

private theorem actual_closeCollection {P : Type v} [Fintype P] [DecidableEq P]
    {Q : Type w} {E : Type z} [Fintype E] [DecidableEq E]
    {F : SignatureFamily K} {f : Tensor K P} (hI : RetainsIdentity F)
    (hB : Gadget.Realizes F .disequality (binarySignature B)) (hf : Actual F f)
    (p : CollectionPorts P Q E) : Actual F (contractCollection p (fun _ => (edge B)) f) := by
  classical
  have aux : ∀ k : ℕ, ∀ (E : Type z) [Fintype E] [DecidableEq E], Fintype.card E=k →
      ∀ (P : Type v) [Fintype P] [DecidableEq P] (Q : Type w),
      ∀ p : CollectionPorts P Q E, ∀ f : Tensor K P,
      Actual F f → Actual F (contractCollection p (fun _ => (edge B)) f) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro E _ _ hk P _ _ Q p f hf
      rcases isEmpty_or_nonempty E with hE | hE
      · let : IsEmpty E := hE
        rw [contractCollection_empty]
        exact hf.reindex (emptyBoundary p).symm
      · obtain ⟨e⟩ := hE
        rw [contractCollection_step p (fun _ => (edge B)) f e]
        have hl : Fintype.card (OtherEdges e)<k := by rw [←hk]; exact otherEdges_card_lt e
        exact ih _ hl (OtherEdges e) rfl _ Q (collectionTailPorts p e) _
          (actual_contractPair B hI hB hf _ _ (collection_pair_distinct p e))
  exact aux _ E rfl P Q p f hf

private theorem network_eq_collection {n : ℕ} (N : Network K n)
    (he : ∀e,N.edge e=(edge B)) :
    N.denote=contractCollection N.shape.ports.symm (fun _ => (edge B))
      (fun x : (Σv,Fin (N.shape.arity v)) → Bool => ∏v,N.vertex v (fun i => x ⟨v,i⟩)) := by
  classical
  funext x
  unfold Network.denote contractCollection
  symm
  apply Fintype.sum_equiv (endpointAssignments (Fin N.shape.edges))
  intro y
  have ha (v : Fin N.shape.vertices) :
      (fun i => collectionAssignment N.shape.ports.symm x y ⟨v,i⟩)=
        N.shape.assignment x (endpointAssignments (Fin N.shape.edges) y) v := by
    funext i
    unfold collectionAssignment NetworkShape.assignment
    simp only [Equiv.symm_symm]
    cases N.shape.ports ⟨v,i⟩ with
    | inl j => rfl
    | inr e => rfl
  simp only [ha,he,kernelProduct,endpointAssignments]
  exact mul_comm _ _

theorem network_upTo {n : ℕ} (F : SignatureFamily K) (hI : RetainsIdentity F)
    (hB : Gadget.Realizes F .disequality (binarySignature B))
    (N : Network K n) (hv : ∀v,Gadget.RealizesUpTo F .disequality (N.vertex v))
    (he : ∀e,N.edge e=(edge B)) : Gadget.RealizesUpTo F .disequality N.denote := by
  rw [network_eq_collection B N he]
  exact (actual_closeCollection B hI hB
    (Actual.vertexProduct F N.shape.vertices N.shape.arity N.vertex hv) N.shape.ports.symm).realizesUpTo

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0KernelRealizes
end
