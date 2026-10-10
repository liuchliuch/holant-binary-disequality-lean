import Holant.Proofs.Hardness.GeneralEOCentralHoleRepeated
import Holant.Proofs.Hardness.GeneralEOPinnedDescentSelected

/-! Original labelled provenance through the repeated-pattern hole step. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleRepeatedLabels
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Classical
set_option backward.isDefEq.respectTransparency false
namespace R
export GeneralEOCentralHoleRepeated (double output swapped swapPairs Branch select branchNetwork)
end R
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace N
export GeneralEOPinnedDescentNetwork (reboundaryLabels directed01)
end N
namespace L
export GeneralEOPinnedDescentLabels
  (pinnedLabels pinned_exact pinned_native pinned_count pinned_vertices pinned_edges)
end L
namespace C
export GeneralEOPinnedDescentCore (choice slice10 slice01)
end C
namespace S
export GeneralEOPinnedDescentSelected (labels exact native count vertices edges copies pins addedEdges)
end S
namespace LN
export LabelledNetwork (Exact count)
end LN
variable {K : Type*} [Field K] {n s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (arity i.val))
variable (T : Network K (n+4)) (TL : Labelling T.shape s 1 arity)
variable (j : Fin s) (hj : (⟨arity j.val,G j⟩ : AnySignature K)=⟨2,N.directed01⟩)
variable (he : Signature.CentralSupport T.denote) (a b c : Fin n → Bool)
variable (ha : T.denote (R.double true true a) ≠ 0)
variable (hb : T.denote (R.double true true b) ≠ 0)

def branchLabels : (t : R.Branch) → Labelling (R.branchNetwork T he a b c ha hb t).shape s 1 arity
  | .descent => S.labels G T TL j hj he (O.word true false a) (O.word true false b)
      (O.word false true c) ha hb
  | .pinFirst => L.pinnedLabels G T TL j hj true
  | .pinSecond => L.pinnedLabels G (R.swapped T) (N.reboundaryLabels T TL R.swapPairs) j hj false

def labels : Labelling (R.output T he a b c ha hb).shape s 1 arity :=
  branchLabels G T TL j hj he a b c ha hb (R.select T a b c)

variable (hL : LN.Exact G T TL)

include hL in
theorem branch_exact (t : R.Branch) : LN.Exact G (R.branchNetwork T he a b c ha hb t)
    (branchLabels G T TL j hj he a b c ha hb t) := by
  cases t
  · exact S.exact G T TL j hj he _ _ _ ha hb hL
  · exact L.pinned_exact G T TL j hj hL true
  · exact L.pinned_exact G (R.swapped T) (N.reboundaryLabels T TL R.swapPairs) j hj hL false

include hL in
theorem exact : LN.Exact G (R.output T he a b c ha hb)
    (labels G T TL j hj he a b c ha hb) :=
  branch_exact G T TL j hj he a b c ha hb hL _

variable (hn : ∀e,T.edge e=Signature.disequality)

include hn in
theorem branch_native (t : R.Branch) : ∀e,(R.branchNetwork T he a b c ha hb t).edge e=Signature.disequality := by
  cases t
  · exact S.native T he _ _ _ ha hb hn
  · exact L.pinned_native T hn true
  · exact L.pinned_native (R.swapped T) hn false

include hn in
theorem native : ∀e,(R.output T he a b c ha hb).edge e=Signature.disequality :=
  branch_native T he a b c ha hb hn _

def branch := C.choice (C.slice10 T) (C.slice01 T)
  (O.word true false a) (O.word true false b) (O.word false true c)

theorem branch_count (t : R.Branch) (k : Fin s) :
    LN.count (branchLabels G T TL j hj he a b c ha hb t) k =
      match t with
      | .descent => S.copies (branch T a b c)*LN.count TL k+
          (if j=k then S.pins (n+2) (branch T a b c) else 0)
      | .pinFirst | .pinSecond => LN.count TL k+(if j=k then 1 else 0) := by
  cases t
  · exact S.count G T TL j hj he _ _ _ ha hb k
  · exact L.pinned_count G T TL j hj true k
  · exact L.pinned_count G (R.swapped T) (N.reboundaryLabels T TL R.swapPairs) j hj false k

theorem count (k : Fin s) :
    LN.count (labels G T TL j hj he a b c ha hb) k =
      match R.select T a b c with
      | .descent => S.copies (branch T a b c)*LN.count TL k+
          (if j=k then S.pins (n+2) (branch T a b c) else 0)
      | .pinFirst | .pinSecond => LN.count TL k+(if j=k then 1 else 0) :=
  branch_count G T TL j hj he a b c ha hb _ k

theorem vertices :
    (R.output T he a b c ha hb).shape.vertices =
      if T.denote (R.double true false (tripleXor a b c))=0 then
        S.copies (branch T a b c)*T.shape.vertices+S.pins (n+2) (branch T a b c)
      else T.shape.vertices+1 := by
  classical
  unfold R.output R.select
  split_ifs
  · exact S.vertices T he _ _ _ ha hb
  · exact L.pinned_vertices T true
  · exact L.pinned_vertices (R.swapped T) false

theorem edges :
    (R.output T he a b c ha hb).shape.edges =
      if T.denote (R.double true false (tripleXor a b c))=0 then
        S.copies (branch T a b c)*T.shape.edges+S.addedEdges (n+2) (branch T a b c)
      else T.shape.edges+2 := by
  classical
  unfold R.output R.select
  split_ifs
  · exact S.edges T he _ _ _ ha hb
  · exact L.pinned_edges T true
  · exact L.pinned_edges (R.swapped T) false

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleRepeatedLabels
