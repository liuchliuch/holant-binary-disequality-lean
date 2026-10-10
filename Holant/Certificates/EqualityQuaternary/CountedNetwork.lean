import Holant.Certificates.EqualityQuaternary.PhysicalFlip
import Holant.Certificates.FourthRootOdd.NetworkTools

/-! Exact original-q accounting for ordinary native networks. Tensoring,
reordering and closing boundaries preserve every old labelled occurrence.
Only literal equality is permitted in addition to the original q. -/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Counted
open Holant Holant.Marked Holant.Tractable
open Holant.Certificates.FourthRootOdd
set_option backward.isDefEq.respectTransparency false

def copies {n : ℕ} (N : Network Scalar n) : ℕ :=
  ∑ v : Fin N.shape.vertices, if N.shape.arity v=4 then 1 else 0

def Allowed (q : Signature Scalar 4) {n : ℕ} (N : Network Scalar n) : Prop :=
  (∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature Scalar)=⟨4,q⟩ ∨
    (⟨N.shape.arity v,N.vertex v⟩ : AnySignature Scalar)=⟨2,kernelSignature Signature.equality⟩) ∧
  ∀ e,N.edge e=Signature.disequality

def input (q : Signature Scalar 4) : Network Scalar 4 := singleVertexNetwork q
def equality : Network Scalar 2 := singleVertexNetwork (kernelSignature Signature.equality)

theorem input_allowed (q : Signature Scalar 4) : Allowed q (input q) :=
  ⟨fun _ => Or.inl rfl,fun e => Fin.elim0 e⟩
theorem equality_allowed (q : Signature Scalar 4) : Allowed q equality :=
  ⟨fun _ => Or.inr rfl,fun e => Fin.elim0 e⟩
@[simp] theorem input_copies (q : Signature Scalar 4) : copies (input q)=1 := by
  simp [copies,input,singleVertexNetwork]
@[simp] theorem equality_copies : copies equality=0 := by simp [copies,equality,singleVertexNetwork]
@[simp] theorem input_denote (q : Signature Scalar 4) : (input q).denote=q := singleVertexNetwork_denote q
@[simp] theorem equality_denote : equality.denote=kernelSignature Signature.equality := singleVertexNetwork_denote _

theorem Allowed.reorder {q : Signature Scalar 4} {n : ℕ} {N : Network Scalar n}
    (h : Allowed q N) (p : Equiv.Perm (Fin n)) : Allowed q (reorderNetwork N p) := h
theorem Allowed.contract {q : Signature Scalar 4} {n : ℕ} {N : Network Scalar (n+2)}
    (h : Allowed q N) : Allowed q (N.contract Signature.disequality) := by
  refine ⟨h.1,?_⟩
  intro e
  exact Fin.cases rfl h.2 e

theorem Allowed.tensor {q : Signature Scalar 4} {m n : ℕ}
    {L : Network Scalar m} {R : Network Scalar n} (hL : Allowed q L) (hR : Allowed q R) :
    Allowed q (L.tensor R) := by
  constructor
  · intro v
    change (⟨_,(Network.tensorFinite L R).vertex
      ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)⟩ : AnySignature Scalar)=_ ∨
      (⟨_,(Network.tensorFinite L R).vertex
      ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)⟩ : AnySignature Scalar)=_
    cases (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v with
    | inl v => exact hL.1 v
    | inr v => exact hR.1 v
  · intro e
    change (Network.tensorFinite L R).edge
      ((Fintype.equivFin (Fin L.shape.edges ⊕ Fin R.shape.edges)).symm e)=_
    cases (Fintype.equivFin (Fin L.shape.edges ⊕ Fin R.shape.edges)).symm e with
    | inl e => exact hL.2 e
    | inr e => exact hR.2 e

@[simp] theorem reorder_copies {n : ℕ} (N : Network Scalar n) (p : Equiv.Perm (Fin n)) :
    copies (reorderNetwork N p)=copies N := rfl
@[simp] theorem contract_copies {n : ℕ} (N : Network Scalar (n+2)) (E : Mat) :
    copies (N.contract E)=copies N := rfl

@[simp] theorem tensor_copies {m n : ℕ} (L : Network Scalar m) (R : Network Scalar n) :
    copies (L.tensor R)=copies L+copies R := by
  classical
  let f : Fin L.shape.vertices ⊕ Fin R.shape.vertices → ℕ :=
    fun v => if (Sum.elim L.shape.arity R.shape.arity v)=4 then 1 else 0
  change (∑ v, f ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v))=_
  rw [(Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm.sum_comp]
  rw [Fintype.sum_sum_type]
  rfl

theorem Allowed.realizes {q : Signature Scalar 4} {n : ℕ} {N : Network Scalar n}
    (h : Allowed q N) (F : SignatureFamily Scalar)
    (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F) :
    Gadget.Realizes F .disequality N.denote := by
  apply Gadget.realizes_network
  · intro v
    rcases h.1 v with he | he
    · rwa [he]
    · rwa [he]
  · exact h.2

end Holant.Certificates.EqualityQuaternary.Counted
