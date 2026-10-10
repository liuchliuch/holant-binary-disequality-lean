import Holant.OpenNetworkComposition.OrdinaryTensor
import Holant.OpenNetworkComposition.OrdinaryFreeTensor
import Holant.OpenNetworkComposition.FreeOrdinaryTensor
import Holant.OpenNetworkComposition.FreeFreeSemantics
import Holant.OpenNetworkComposition.OfOpen

/-! Sufficient native-X closure: join exactly one boundary of each of TWO
DISJOINT actual gadgets. This does not assert self-contraction or unrestricted
substitution, which could create an unrepresented wire-only circle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition
variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- Arbitrary actual gadgets, including free stubs and disconnected scalar
components, admit this single disjoint native-X connection in original order. -/
theorem realizes_splice (family : SignatureFamily K) (q : Signature K n) (C : Signature K 2)
    (hq : Gadget.Realizes family .disequality q) (hC : Gadget.Realizes family .disequality C)
    (i : Fin n) : Gadget.Realizes family .disequality (spliceTensor q C i) := by
  classical
  obtain ⟨L,hvL,heL,htL⟩ := hq
  obtain ⟨R,hvR,heR,htR⟩ := hC
  let l := FiniteNetwork.ofOpen L
  let r := FiniteNetwork.ofOpen R
  have hl : l.tensor=q := (FiniteNetwork.ofOpen_tensor L).trans htL
  have hr : r.tensor=C := (FiniteNetwork.ofOpen_tensor R).trans htR
  have vl : ∀v,(⟨l.shape.arity v,l.vertex v⟩ : AnySignature K)∈family := hvL
  have vr : ∀v,(⟨r.shape.arity v,r.vertex v⟩ : AnySignature K)∈family := hvR
  have el : ∀e,l.edge e=.disequality := heL
  have er : ∀e,r.edge e=.disequality := heR
  rw [← hl,← hr]
  cases hleft : l.shape.boundary i with
  | inl pL => cases hright : r.shape.boundary 1 with
    | inl pR => exact Ordinary.realizes_splice l r i pL pR hleft hright family vl vr el er
    | inr fR => exact OrdinaryFree.realizes_splice l r fR i pL hleft hright family vl vr el er
  | inr fL => cases hright : r.shape.boundary 1 with
    | inl pR => exact FreeOrdinary.realizes_splice l r fL i pR hleft hright family vl vr el er
    | inr fR => exact FreeFree.realizes_splice l r fL fR i hleft hright family vl vr el er

end Holant.OpenNetworkComposition
