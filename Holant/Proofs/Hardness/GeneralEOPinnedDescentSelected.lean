import Holant.Proofs.Hardness.GeneralEOPinnedDescentCore
import Holant.Proofs.Hardness.GeneralEOPinnedDescentLabels

/-! Literal original labels and exact graph receipts for the finite selected
EO descent. Existing source occurrences are counted with multiplicity, including
both actual source copies in a cancellation branch. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentSelected
open Holant Holant.Complexity FixedGadgetSubstitution
namespace C
export GeneralEOPinnedDescentCore (Branch choice slice10 slice01 tail_balanced branchNetwork network)
end C
namespace L
export GeneralEOPinnedDescentLabels
  (pinnedLabels signedLabels pinned_exact signed_exact pinned_native signed_native
   pinned_count signed_count pinned_vertices signed_vertices pinned_edges signed_edges)
end L
namespace N
export GeneralEOPinnedDescentNetwork (directed01 pairing bank_vertices)
end N
namespace LN
export LabelledNetwork (Exact count contract exact_contract count_contract)
end LN
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {n s : ℕ} {arity : ℕ → ℕ}

def copies : C.Branch → ℕ
  | .signedAlpha | .signedBeta => 2
  | _ => 1

def pins (n : ℕ) : C.Branch → ℕ
  | .pin10 | .pin01 => 1
  | .loop => 0
  | .signedAlpha | .signedBeta => n/2

def addedEdges (n : ℕ) : C.Branch → ℕ
  | .pin10 | .pin01 => 2
  | .loop => 1
  | .signedAlpha | .signedBeta => n+2

private theorem pair_count (w : Fin n → Bool) (hw : 2*weight w=n) :
    (N.pairing w hw).count=n/2 := by
  have h := GeneralEOPinnedDescentNetwork.PC.twice_count
    (GeneralEOPinnedDescentNetwork.singletonData w hw)
  change 2*(N.pairing w hw).count=n at h
  omega

variable (G : (i : Fin s) → Signature K (arity i.val))
variable (S : Network K (n+2)) (SL : Labelling S.shape s 1 arity)
variable (j : Fin s) (hj : (⟨arity j.val,G j⟩ : AnySignature K)=⟨2,N.directed01⟩)
variable (he : Signature.CentralSupport S.denote)
variable (a b c : Fin n → Bool) (ha : C.slice10 S a ≠ 0) (hb : C.slice10 S b ≠ 0)

def branchLabels : (t : C.Branch) → Labelling (C.branchNetwork S he a b ha hb t).shape s 1 arity
  | .pin10 => L.pinnedLabels G S SL j hj true
  | .pin01 => L.pinnedLabels G S SL j hj false
  | .loop => LN.contract S SL 0 Signature.disequality
  | .signedAlpha => L.signedLabels G S SL j hj a (C.tail_balanced S he true a ha)
  | .signedBeta => L.signedLabels G S SL j hj b (C.tail_balanced S he true b hb)

def labels : Labelling (C.network S he a b c ha hb).shape s 1 arity :=
  branchLabels G S SL j hj he a b ha hb (C.choice (C.slice10 S) (C.slice01 S) a b c)

variable (hL : LN.Exact G S SL)

include hL in
theorem branch_exact (t : C.Branch) :
    LN.Exact G (C.branchNetwork S he a b ha hb t) (branchLabels G S SL j hj he a b ha hb t) := by
  cases t
  · exact L.pinned_exact G S SL j hj hL true
  · exact L.pinned_exact G S SL j hj hL false
  · exact LN.exact_contract G S SL hL 0 Signature.disequality
  · exact L.signed_exact G S SL j hj hL a (C.tail_balanced S he true a ha)
  · exact L.signed_exact G S SL j hj hL b (C.tail_balanced S he true b hb)

include hL in
theorem exact : LN.Exact G (C.network S he a b c ha hb) (labels G S SL j hj he a b c ha hb) :=
  branch_exact G S SL j hj he a b ha hb hL _

theorem branch_count (t : C.Branch) (k : Fin s) :
    LN.count (branchLabels G S SL j hj he a b ha hb t) k=
      copies t*LN.count SL k+(if j=k then pins n t else 0) := by
  cases t
  · simpa [branchLabels,copies,pins] using L.pinned_count G S SL j hj true k
  · simpa [branchLabels,copies,pins] using L.pinned_count G S SL j hj false k
  · simp [branchLabels,copies,pins,LN.count_contract]
  · simpa [branchLabels,copies,pins,pair_count] using
      L.signed_count G S SL j hj a (C.tail_balanced S he true a ha) k
  · simpa [branchLabels,copies,pins,pair_count] using
      L.signed_count G S SL j hj b (C.tail_balanced S he true b hb) k

theorem count (k : Fin s) :
    LN.count (labels G S SL j hj he a b c ha hb) k=
      copies (C.choice (C.slice10 S) (C.slice01 S) a b c)*LN.count SL k+
        (if j=k then pins n (C.choice (C.slice10 S) (C.slice01 S) a b c) else 0) :=
  branch_count G S SL j hj he a b ha hb _ k

theorem branch_vertices (t : C.Branch) :
    (C.branchNetwork S he a b ha hb t).shape.vertices=
      copies t*S.shape.vertices+pins n t := by
  cases t
  · simpa [C.branchNetwork,copies,pins] using L.pinned_vertices S true
  · simpa [C.branchNetwork,copies,pins] using L.pinned_vertices S false
  · simp [C.branchNetwork,copies,pins]
  · simpa [C.branchNetwork,copies,pins,pair_count] using
      L.signed_vertices S a (C.tail_balanced S he true a ha)
  · simpa [C.branchNetwork,copies,pins,pair_count] using
      L.signed_vertices S b (C.tail_balanced S he true b hb)

theorem vertices : (C.network S he a b c ha hb).shape.vertices=
    copies (C.choice (C.slice10 S) (C.slice01 S) a b c)*S.shape.vertices+
      pins n (C.choice (C.slice10 S) (C.slice01 S) a b c) :=
  branch_vertices S he a b ha hb _

theorem branch_edges (t : C.Branch) :
    (C.branchNetwork S he a b ha hb t).shape.edges=
      copies t*S.shape.edges+addedEdges n t := by
  cases t
  · simpa [C.branchNetwork,copies,addedEdges] using L.pinned_edges S true
  · simpa [C.branchNetwork,copies,addedEdges] using L.pinned_edges S false
  · simp [C.branchNetwork,copies,addedEdges]
  · simpa [C.branchNetwork,copies,addedEdges,Nat.add_assoc] using
      L.signed_edges S a (C.tail_balanced S he true a ha)
  · simpa [C.branchNetwork,copies,addedEdges,Nat.add_assoc] using
      L.signed_edges S b (C.tail_balanced S he true b hb)

theorem edges : (C.network S he a b c ha hb).shape.edges=
    copies (C.choice (C.slice10 S) (C.slice01 S) a b c)*S.shape.edges+
      addedEdges n (C.choice (C.slice10 S) (C.slice01 S) a b c) :=
  branch_edges S he a b ha hb _

variable (hn : ∀e,S.edge e=Signature.disequality)

include hn in
theorem branch_native (t : C.Branch) :
    ∀e,(C.branchNetwork S he a b ha hb t).edge e=Signature.disequality := by
  cases t
  · exact L.pinned_native S hn true
  · exact L.pinned_native S hn false
  · intro e
    exact Fin.cases rfl (fun e => hn e) e
  · exact L.signed_native S hn a (C.tail_balanced S he true a ha)
  · exact L.signed_native S hn b (C.tail_balanced S he true b hb)

include hn in
theorem native : ∀e,(C.network S he a b c ha hb).edge e=Signature.disequality :=
  branch_native S he a b ha hb hn _

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentSelected
