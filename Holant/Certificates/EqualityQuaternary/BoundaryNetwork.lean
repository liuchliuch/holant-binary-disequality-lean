import Holant.Certificates.EqualityQuaternary.C2FirstFlip
import Holant.Certificates.EqualityQuaternary.CoordinatePrimality
import Holant.Certificates.OctahedralSeparator.TensorTransport
import Holant.Dihedral.CompatibleClosure.ActualReindex

/-! Actual arbitrary binary attachments on one original-q network.
Every attachment adds one binary vertex, no original-q copy, and one native
edge. Reordering changes boundary incidence alone.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Boundary
open Holant Holant.Marked Holant.Tractable
open Holant.Projective.CyclicDressing
open Holant.Certificates.FourthRootOdd
set_option backward.isDefEq.respectTransparency false

def Native {n : ℕ} (N : Network Scalar n) : Prop := ∀ e,N.edge e=Signature.disequality
def CoreLabels (q : Signature Scalar 4) {n : ℕ} (N : Network Scalar n) : Prop :=
  ∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature Scalar)=⟨4,q⟩ ∨ N.shape.arity v=2

def attachFirst (N : Network Scalar 4) (B : Mat) : Network Scalar 4 :=
  (reorderNetwork (N.tensor (singleVertexNetwork (kernelSignature B))) C2.flipWiring.symm).contract Signature.disequality

theorem attachFirst_denote (N : Network Scalar 4) (B : Mat) :
    (attachFirst N B).denote=onePort N.denote 0 B := by
  rw [attachFirst,Network.denote_contract,reorderNetwork_denote,Network.denote_tensor,
    singleVertexNetwork_denote,onePort_eq_splice]
  funext w
  simp only [Signature.contract_disequality,Tensor.reindex_apply,Signature.tensor_apply]
  have hl0 := C2.flip_left_word false w
  have hl1 := C2.flip_left_word true w
  have hr0 := C2.flip_right_word false w
  have hr1 := C2.flip_right_word true w
  simp only [Bool.not_false,Bool.not_true] at hl0 hl1 hr0 hr1
  rw [hl0,hl1,hr0,hr1]
  simp [OpenNetworkComposition.spliceTensor,Signature.disequality,kernelSignature,update_word4]
  ring

def attach (N : Network Scalar 4) (i : Fin 4) (B : Mat) : Network Scalar 4 :=
  reorderNetwork (attachFirst (reorderNetwork N (Equiv.swap 0 i)) B) (Equiv.swap 0 i)

theorem onePort_swap (q : Signature Scalar 4) (i : Fin 4) (B : Mat) :
    Tensor.reindex (Equiv.swap 0 i) (onePort (Tensor.reindex (Equiv.swap 0 i) q) 0 B)=onePort q i B := by
  rw [onePort,OctahedralSeparator.reindex_action]
  have hq : Tensor.reindex (Equiv.swap 0 i) (Tensor.reindex (Equiv.swap 0 i) q)=q := by
    rw [Tensor.reindex_trans]
    simp
  rw [hq]
  unfold onePort
  congr 1
  funext j
  simp only [show (Equiv.swap (0 : Fin 4) i).symm=Equiv.swap 0 i from rfl]
  have he : (Equiv.swap (0 : Fin 4) i) j=0 ↔ j=i := by
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    simp
  simp only [he]

theorem attach_denote (N : Network Scalar 4) (i : Fin 4) (B : Mat) :
    (attach N i B).denote=onePort N.denote i B := by
  rw [attach,reorderNetwork_denote,attachFirst_denote,reorderNetwork_denote,onePort_swap]

theorem attach_copies (N : Network Scalar 4) (i : Fin 4) (B : Mat) :
    Counted.copies (attach N i B)=Counted.copies N := by
  simp only [attach,attachFirst,Counted.reorder_copies,Counted.contract_copies,Counted.tensor_copies]
  have hz : Counted.copies (singleVertexNetwork (kernelSignature B))=0 := by
    simp [Counted.copies,singleVertexNetwork]
  rw [hz,Nat.add_zero]

theorem attachFirst_native {N : Network Scalar 4} (h : Native N) (B : Mat) : Native (attachFirst N B) := by
  intro e
  refine Fin.cases rfl (fun e => ?_) e
  change (Network.tensorFinite N (singleVertexNetwork (kernelSignature B))).edge
    ((Fintype.equivFin (Fin N.shape.edges ⊕ Fin 0)).symm e)=_
  cases (Fintype.equivFin (Fin N.shape.edges ⊕ Fin 0)).symm e with
  | inl e => exact h e
  | inr e => exact Fin.elim0 e

theorem attach_native {N : Network Scalar 4} (h : Native N) (i : Fin 4) (B : Mat) : Native (attach N i B) :=
  attachFirst_native h B

theorem attachFirst_labels {q : Signature Scalar 4} {N : Network Scalar 4}
    (h : CoreLabels q N) (B : Mat) : CoreLabels q (attachFirst N B) := by
  intro v
  change (⟨_,(Network.tensorFinite N (singleVertexNetwork (kernelSignature B))).vertex
    ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin 1)).symm v)⟩ : AnySignature Scalar)=_ ∨
    (Network.tensorFinite N (singleVertexNetwork (kernelSignature B))).arity
      ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin 1)).symm v)=2
  cases (Fintype.equivFin (Fin N.shape.vertices ⊕ Fin 1)).symm v with
  | inl v => exact h v
  | inr v => exact Or.inr rfl

theorem attach_labels {q : Signature Scalar 4} {N : Network Scalar 4}
    (h : CoreLabels q N) (i : Fin 4) (B : Mat) : CoreLabels q (attach N i B) :=
  attachFirst_labels (N:=reorderNetwork N (Equiv.swap 0 i)) h B

def flipLastTwo (N : Network Scalar 4) : Network Scalar 4 :=
  attach (attach N 2 Signature.equality) 3 Signature.equality

theorem flipLastTwo_denote (N : Network Scalar 4) :
    (flipLastTwo N).denote=Flip.value N.denote ![false,false,true,true] := by
  rw [flipLastTwo,attach_denote,attach_denote]
  funext w
  have hc (q : Signature Scalar 4) (i : Fin 4) : onePort q i Signature.equality w=
      q (Function.update w i (!(w i))) := by
    have hs : scale (1 : Scalar) Signature.disequality=Signature.disequality := by funext a b; simp [scale]
    have hh := Holant.Marked.SupportAtlas.one_flip_action q 1 i w
    rw [hs] at hh
    simpa [onePort] using hh
  rw [hc]
  have hs : scale (1 : Scalar) Signature.disequality=Signature.disequality := by funext a b; simp [scale]
  have hh := Holant.Marked.SupportAtlas.one_flip_action N.denote 1 2 (Function.update w 3 (!(w 3)))
  rw [hs] at hh
  simp only [onePort,Kernel.equality_mul,one_mul] at hh ⊢
  rw [hh]
  apply congrArg N.denote
  funext i
  fin_cases i <;> simp [Flip.value,Holant.Marked.SupportAtlas.xorWord]

theorem flipLastTwo_copies (N : Network Scalar 4) : Counted.copies (flipLastTwo N)=Counted.copies N := by
  simp [flipLastTwo,attach_copies]

end Holant.Certificates.EqualityQuaternary.Boundary
