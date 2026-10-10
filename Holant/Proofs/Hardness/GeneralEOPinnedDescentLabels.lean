import Holant.Proofs.Hardness.GeneralEOPinnedDescentOperations

/-! Literal label propagation and exact occurrence receipts for the physical
pin and cancellation branches. The source may already be an arbitrary graph
over the original family and directed 01; recursion never promotes its tensor
to a new free resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentLabels
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace O
export GeneralEOPinnedDescentOperations (front rotate cap extracted pinned signed)
end O
namespace N
export GeneralEOPinnedDescentNetwork
  (reboundary reboundaryLabels plugLabels plug_exact plug_count bank bankLabels bank_exact bank_count
   pairing bank_vertices bank_edges directed01)
end N
namespace P
export Holant.ReedMuller.TwoChart.NetworkPlug (vertices edges native_edges)
end P
namespace LN
export LabelledNetwork (Exact count)
end LN
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] {n s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val))
variable (S : Network K (n+2)) (L : Labelling S.shape s 1 a)
variable (j : Fin s) (hj : (⟨a j.val,G j⟩ : AnySignature K)=⟨2,N.directed01⟩)

def capLabels (B : Network K 2) (BL : Labelling B.shape s 1 a) :
    Labelling (O.cap B S).shape s 1 a :=
  N.plugLabels B (N.reboundary S O.front) BL (N.reboundaryLabels S L O.front) _

def extractedLabels (w : Fin n → Bool) (hw : 2*weight w=n) :
    Labelling (O.extracted S w hw).shape s 1 a :=
  N.plugLabels (N.bank w hw) (N.reboundary S O.rotate)
    (N.bankLabels w hw j (congrArg Sigma.fst hj)) (N.reboundaryLabels S L O.rotate) _

def pinnedLabels (u : Bool) : Labelling (O.pinned S u).shape s 1 a :=
  capLabels S L _ (N.bankLabels (![u,!u] : Fin 2 → Bool) (by cases u <;> decide)
    j (congrArg Sigma.fst hj))

def signedLabels (w : Fin n → Bool) (hw : 2*weight w=n) :
    Labelling (O.signed S w hw).shape s 1 a :=
  capLabels S L _ (extractedLabels G S L j hj w hw)

variable (he : LN.Exact G S L)

include he in
theorem cap_exact (B : Network K 2) (BL : Labelling B.shape s 1 a) (hB : LN.Exact G B BL) :
    LN.Exact G (O.cap B S) (capLabels S L B BL) :=
  N.plug_exact G _ _ _ _ hB he _

include he in
theorem extracted_exact (w : Fin n → Bool) (hw : 2*weight w=n) :
    LN.Exact G (O.extracted S w hw) (extractedLabels G S L j hj w hw) :=
  N.plug_exact G (N.bank w hw) (N.reboundary S O.rotate)
    (N.bankLabels w hw j (congrArg Sigma.fst hj)) (N.reboundaryLabels S L O.rotate)
    (N.bank_exact G w hw j hj) he (fun _ => Signature.disequality)

include he in
theorem pinned_exact (u : Bool) :
    LN.Exact G (O.pinned S u) (pinnedLabels G S L j hj u) :=
  cap_exact G S L he _ _ (N.bank_exact G _ _ j hj)

include he in
theorem signed_exact (w : Fin n → Bool) (hw : 2*weight w=n) :
    LN.Exact G (O.signed S w hw) (signedLabels G S L j hj w hw) :=
  cap_exact G S L he _ _ (extracted_exact G S L j hj he w hw)

theorem cap_count (B : Network K 2) (BL : Labelling B.shape s 1 a) (k : Fin s) :
    LN.count (capLabels S L B BL) k=LN.count BL k+LN.count L k :=
  N.plug_count _ _ _ _ _ _

theorem extracted_count (w : Fin n → Bool) (hw : 2*weight w=n) (k : Fin s) :
    LN.count (extractedLabels G S L j hj w hw) k=
      (if j=k then (N.pairing w hw).count else 0)+LN.count L k := by
  rw [extractedLabels,N.plug_count,N.bank_count]
  rfl

private theorem two_pair_count (u : Bool) :
    (N.pairing (![u,!u] : Fin 2 → Bool) (by cases u <;> decide)).count=1 := by
  have h := GeneralEOPinnedDescentNetwork.PC.twice_count
    (GeneralEOPinnedDescentNetwork.singletonData (![u,!u] : Fin 2 → Bool) (by cases u <;> decide))
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0<2) h

theorem pinned_count (u : Bool) (k : Fin s) :
    LN.count (pinnedLabels G S L j hj u) k=LN.count L k+(if j=k then 1 else 0) := by
  rw [pinnedLabels,cap_count,N.bank_count,two_pair_count]
  omega

theorem signed_count (w : Fin n → Bool) (hw : 2*weight w=n) (k : Fin s) :
    LN.count (signedLabels G S L j hj w hw) k=
      2*LN.count L k+(if j=k then (N.pairing w hw).count else 0) := by
  rw [signedLabels,cap_count,extracted_count]
  omega

theorem pinned_vertices (u : Bool) : (O.pinned S u).shape.vertices=S.shape.vertices+1 := by
  change (O.cap (N.bank (![u,!u]) _) S).shape.vertices=_
  rw [O.cap,P.vertices]
  change (N.pairing (![u,!u] : Fin 2 → Bool) (by cases u <;> decide)).count+S.shape.vertices=S.shape.vertices+1
  rw [two_pair_count]
  omega

theorem pinned_edges (u : Bool) : (O.pinned S u).shape.edges=S.shape.edges+2 := by
  rw [O.pinned,O.cap,P.edges,N.bank_edges]
  simp [N.reboundary]

theorem extracted_vertices (w : Fin n → Bool) (hw : 2*weight w=n) :
    (O.extracted S w hw).shape.vertices=(N.pairing w hw).count+S.shape.vertices := by
  rw [O.extracted,P.vertices]
  rfl

theorem extracted_edges (w : Fin n → Bool) (hw : 2*weight w=n) :
    (O.extracted S w hw).shape.edges=S.shape.edges+n := by
  rw [O.extracted,P.edges,N.bank_edges]
  simp [N.reboundary]

theorem signed_vertices (w : Fin n → Bool) (hw : 2*weight w=n) :
    (O.signed S w hw).shape.vertices=2*S.shape.vertices+(N.pairing w hw).count := by
  rw [O.signed,O.cap,P.vertices,extracted_vertices]
  change (N.pairing w hw).count+S.shape.vertices+S.shape.vertices=_
  omega

theorem signed_edges (w : Fin n → Bool) (hw : 2*weight w=n) :
    (O.signed S w hw).shape.edges=2*S.shape.edges+n+2 := by
  rw [O.signed,O.cap,P.edges,extracted_edges]
  change S.shape.edges+n+S.shape.edges+2=_
  omega

variable (hn : ∀e,S.edge e=Signature.disequality)

include hn in
theorem cap_native (B : Network K 2) (hB : ∀e,B.edge e=Signature.disequality) :
    ∀e,(O.cap B S).edge e=Signature.disequality := P.native_edges _ _ hB hn

include hn in
theorem extracted_native (w : Fin n → Bool) (hw : 2*weight w=n) :
    ∀e,(O.extracted S w hw).edge e=Signature.disequality :=
  P.native_edges _ _ (fun e => Fin.elim0 e) hn

include hn in
theorem pinned_native (u : Bool) : ∀e,(O.pinned S u).edge e=Signature.disequality :=
  cap_native S hn _ (fun e => Fin.elim0 e)

include hn in
theorem signed_native (w : Fin n → Bool) (hw : 2*weight w=n) :
    ∀e,(O.signed S w hw).edge e=Signature.disequality :=
  cap_native S hn _ (extracted_native S hn w hw)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentLabels
