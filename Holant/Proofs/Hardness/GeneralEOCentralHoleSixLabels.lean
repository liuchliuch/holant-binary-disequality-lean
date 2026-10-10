import Holant.Proofs.Hardness.GeneralEOCentralHoleSix
import Holant.Proofs.Hardness.GeneralEOPinnedDescentSelected

/-! Original-family labels and graph receipts for the six-port endpoint.
The pin is an explicitly identified family entry; it is never a free resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleSixLabels
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
namespace R
export GeneralEOCentralHoleSix
  (alpha beta gamma delta epsilon zeta q1001 q0110 q1010 q0101 middle lastPair
   reboundary_central middle_alpha middle_beta firstOutput Branch select branchNetwork output)
end R
namespace N
export GeneralEOPinnedDescentNetwork (reboundary reboundaryLabels directed01)
end N
namespace L
export GeneralEOPinnedDescentLabels
  (pinnedLabels pinned_exact pinned_native pinned_count pinned_vertices pinned_edges)
end L
namespace C
export GeneralEOPinnedDescentCore (Branch choice slice10 slice01)
end C
namespace S
export GeneralEOPinnedDescentSelected (labels exact native count vertices edges copies pins addedEdges)
end S
namespace LN
export LabelledNetwork (Exact count)
end LN
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (arity i.val))
variable (T : Network K 6) (TL : Labelling T.shape s 1 arity)
variable (j : Fin s) (hj : (⟨arity j.val,G j⟩ : AnySignature K)=⟨2,N.directed01⟩)
variable (he : Signature.CentralSupport T.denote)
variable (ha : T.denote R.alpha ≠ 0) (hb : T.denote R.beta ≠ 0)
variable (hc : T.denote R.gamma ≠ 0)

include ha in
private theorem middleHa : C.slice10 (N.reboundary T R.middle) R.q1001 ≠ 0 := by
  change (N.reboundary T R.middle).denote R.alpha ≠ 0
  simpa using ha

include hc in
private theorem middleHb : C.slice10 (N.reboundary T R.middle) R.q0110 ≠ 0 := by
  change (N.reboundary T R.middle).denote R.beta ≠ 0
  simpa using hc

def branchLabels : (t : R.Branch) → Labelling (R.branchNetwork T he ha hb hc t).shape s 1 arity
  | .firstPair => S.labels G T TL j hj he R.q1001 R.q0110 R.q1010 ha hb
  | .middlePair => S.labels G (N.reboundary T R.middle) (N.reboundaryLabels T TL R.middle)
      j hj (R.reboundary_central T he R.middle) R.q1001 R.q0110 R.q1010
      (middleHa T ha) (middleHb T hc)
  | .lastPair => L.pinnedLabels G (N.reboundary T R.lastPair)
      (N.reboundaryLabels T TL R.lastPair) j hj false

def labels : Labelling (R.output T he ha hb hc).shape s 1 arity :=
  branchLabels G T TL j hj he ha hb hc (R.select T)

variable (hL : LN.Exact G T TL)

include hL in
theorem branch_exact (t : R.Branch) :
    LN.Exact G (R.branchNetwork T he ha hb hc t) (branchLabels G T TL j hj he ha hb hc t) := by
  cases t
  · exact S.exact G T TL j hj he R.q1001 R.q0110 R.q1010 ha hb hL
  · exact S.exact G (N.reboundary T R.middle) (N.reboundaryLabels T TL R.middle)
      j hj (R.reboundary_central T he R.middle) R.q1001 R.q0110 R.q1010
      (middleHa T ha) (middleHb T hc) hL
  · exact L.pinned_exact G (N.reboundary T R.lastPair) (N.reboundaryLabels T TL R.lastPair)
      j hj hL false

include hL in
theorem exact : LN.Exact G (R.output T he ha hb hc) (labels G T TL j hj he ha hb hc) :=
  branch_exact G T TL j hj he ha hb hc hL (R.select T)

variable (hn : ∀e,T.edge e=Signature.disequality)

include hn in
theorem branch_native (t : R.Branch) :
    ∀e,(R.branchNetwork T he ha hb hc t).edge e=Signature.disequality := by
  cases t
  · exact S.native T he R.q1001 R.q0110 R.q1010 ha hb hn
  · exact S.native (N.reboundary T R.middle) (R.reboundary_central T he R.middle)
      R.q1001 R.q0110 R.q1010 (middleHa T ha) (middleHb T hc) hn
  · exact L.pinned_native (N.reboundary T R.lastPair) hn false

include hn in
theorem native : ∀e,(R.output T he ha hb hc).edge e=Signature.disequality :=
  branch_native T he ha hb hc hn (R.select T)

/-- The physical operation after the explicit choice of an original port pair. -/
def operation : R.Branch → C.Branch
  | .firstPair => C.choice (C.slice10 T) (C.slice01 T) R.q1001 R.q0110 R.q1010
  | .middlePair =>
    C.choice (C.slice10 (N.reboundary T R.middle)) (C.slice01 (N.reboundary T R.middle))
      R.q1001 R.q0110 R.q1010
  | .lastPair => .pin01

def branch : C.Branch := operation T (R.select T)

theorem branch_count (t : R.Branch) (k : Fin s) :
    LN.count (branchLabels G T TL j hj he ha hb hc t) k =
      S.copies (operation T t)*LN.count TL k+(if j=k then S.pins 4 (operation T t) else 0) := by
  cases t
  · exact S.count G T TL j hj he R.q1001 R.q0110 R.q1010 ha hb k
  · exact S.count G (N.reboundary T R.middle) (N.reboundaryLabels T TL R.middle)
      j hj (R.reboundary_central T he R.middle) R.q1001 R.q0110 R.q1010
      (middleHa T ha) (middleHb T hc) k
  · change LN.count (L.pinnedLabels G (N.reboundary T R.lastPair)
        (N.reboundaryLabels T TL R.lastPair) j hj false) k =
      1*LN.count TL k+(if j=k then 1 else 0)
    rw [one_mul]
    exact L.pinned_count G (N.reboundary T R.lastPair) (N.reboundaryLabels T TL R.lastPair)
      j hj false k

theorem count (k : Fin s) :
    LN.count (labels G T TL j hj he ha hb hc) k =
      S.copies (branch T)*LN.count TL k+(if j=k then S.pins 4 (branch T) else 0) :=
  branch_count G T TL j hj he ha hb hc (R.select T) k

theorem branch_vertices (t : R.Branch) :
    (R.branchNetwork T he ha hb hc t).shape.vertices =
      S.copies (operation T t)*T.shape.vertices+S.pins 4 (operation T t) := by
  cases t
  · exact S.vertices T he R.q1001 R.q0110 R.q1010 ha hb
  · exact S.vertices (N.reboundary T R.middle) (R.reboundary_central T he R.middle)
      R.q1001 R.q0110 R.q1010 (middleHa T ha) (middleHb T hc)
  · simpa [R.branchNetwork,operation,S.copies,S.pins,N.reboundary] using
      L.pinned_vertices (N.reboundary T R.lastPair) false

theorem vertices :
    (R.output T he ha hb hc).shape.vertices =
      S.copies (branch T)*T.shape.vertices+S.pins 4 (branch T) :=
  branch_vertices T he ha hb hc (R.select T)

theorem branch_edges (t : R.Branch) :
    (R.branchNetwork T he ha hb hc t).shape.edges =
      S.copies (operation T t)*T.shape.edges+S.addedEdges 4 (operation T t) := by
  cases t
  · exact S.edges T he R.q1001 R.q0110 R.q1010 ha hb
  · exact S.edges (N.reboundary T R.middle) (R.reboundary_central T he R.middle)
      R.q1001 R.q0110 R.q1010 (middleHa T ha) (middleHb T hc)
  · simpa [R.branchNetwork,operation,S.copies,S.addedEdges,N.reboundary] using
      L.pinned_edges (N.reboundary T R.lastPair) false

theorem edges :
    (R.output T he ha hb hc).shape.edges =
      S.copies (branch T)*T.shape.edges+S.addedEdges 4 (branch T) :=
  branch_edges T he ha hb hc (R.select T)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleSixLabels
