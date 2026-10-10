import Holant.OpenNetworkComposition.ProjectiveContractionWire
import Holant.OpenNetworkComposition.ProjectiveContractionBoundary

/-! The three ordered self-closing specializations of isolated-wire deletion.
A circle contributes precisely 2; the two through-wire cases contribute 1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.ProjectiveContraction.Wire
variable {K V F E : Type*} {n : ℕ}
variable (N : FiniteNetwork K V F E (n+2)) (f g : F)
    (hop : N.shape.ends ((N.shape.freeEdge f).1,!(N.shape.freeEdge f).2)=.inr g)

variable [Fintype V] [Fintype F] [Fintype E] [CommSemiring K]

def circleNetwork (h0 : N.shape.boundary 0=.inr f) (h1 : N.shape.boundary 1=.inr g) :=
  network N f g hop 0 1 h0 h1 tailBoundary tailBoundary_range

theorem circle_tensor (h0 : N.shape.boundary 0=.inr f) (h1 : N.shape.boundary 1=.inr g)
    (he : ∀e,N.edge e=.disequality) :
    Signature.contract Signature.disequality N.tensor=
      fun x => 2*(circleNetwork N f g hop h0 h1).tensor x := by
  funext x
  unfold Signature.contract
  simp_rw [tensor_factor N f g hop 0 1 h0 h1 tailBoundary tailBoundary_range he]
  simp only [Fin.cons_zero,Fin.cons_one,tailBoundary_fill]
  simp [Signature.disequality,circleNetwork,two_mul]

def firstNetwork (q : Fin n) (h0 : N.shape.boundary 0=.inr f)
    (hq : N.shape.boundary q.succ.succ=.inr g) :=
  network N f g hop 0 q.succ.succ h0 hq (moveFirstBoundary q) (moveFirstBoundary_range q)

theorem first_tensor (q : Fin n) (h0 : N.shape.boundary 0=.inr f)
    (hq : N.shape.boundary q.succ.succ=.inr g) (he : ∀e,N.edge e=.disequality) :
    Signature.contract Signature.disequality N.tensor=(firstNetwork N f g hop q h0 hq).tensor := by
  funext x
  unfold Signature.contract
  simp_rw [tensor_factor N f g hop 0 q.succ.succ h0 hq
    (moveFirstBoundary q) (moveFirstBoundary_range q) he]
  simp only [Fin.cons_zero,Fin.cons_succ]
  have hf (a : Bool) := moveFirstBoundary_fill q a x
  simp only [moveFirstBoundary_apply] at hf
  cases hx : x q
  · simp only [hx] at hf
    simp [Signature.disequality,hx,hf,firstNetwork]
  · simp only [hx] at hf
    simp [Signature.disequality,hx,hf,firstNetwork]

def secondNetwork (q : Fin n) (h1 : N.shape.boundary 1=.inr f)
    (hq : N.shape.boundary q.succ.succ=.inr g) :=
  network N f g hop 1 q.succ.succ h1 hq (moveSecondBoundary q) (moveSecondBoundary_range q)

theorem second_tensor (q : Fin n) (h1 : N.shape.boundary 1=.inr f)
    (hq : N.shape.boundary q.succ.succ=.inr g) (he : ∀e,N.edge e=.disequality) :
    Signature.contract Signature.disequality N.tensor=(secondNetwork N f g hop q h1 hq).tensor := by
  funext x
  unfold Signature.contract
  simp_rw [tensor_factor N f g hop 1 q.succ.succ h1 hq
    (moveSecondBoundary q) (moveSecondBoundary_range q) he]
  simp only [Fin.cons_one,Fin.cons_succ]
  have hf (b : Bool) := moveSecondBoundary_fill q b x
  simp only [moveSecondBoundary_apply] at hf
  cases hx : x q
  · simp only [hx] at hf
    simp [Signature.disequality,hx,hf,secondNetwork]
  · simp only [hx] at hf
    simp [Signature.disequality,hx,hf,secondNetwork]

include hop in
theorem realizes_first (q : Fin n) (h0 : N.shape.boundary 0=.inr f)
    (hq : N.shape.boundary q.succ.succ=.inr g) (family : SignatureFamily K)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family)
    (he : ∀e,N.edge e=.disequality) :
    Gadget.Realizes family .disequality (Signature.contract Signature.disequality N.tensor) := by
  rw [first_tensor N f g hop q h0 hq he]
  exact realizes_network N f g hop 0 q.succ.succ h0 hq
    (moveFirstBoundary q) (moveFirstBoundary_range q) family hv he

include hop in
theorem realizes_second (q : Fin n) (h1 : N.shape.boundary 1=.inr f)
    (hq : N.shape.boundary q.succ.succ=.inr g) (family : SignatureFamily K)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family)
    (he : ∀e,N.edge e=.disequality) :
    Gadget.Realizes family .disequality (Signature.contract Signature.disequality N.tensor) := by
  rw [second_tensor N f g hop q h1 hq he]
  exact realizes_network N f g hop 1 q.succ.succ h1 hq
    (moveSecondBoundary q) (moveSecondBoundary_range q) family hv he

end Holant.OpenNetworkComposition.ProjectiveContraction.Wire
