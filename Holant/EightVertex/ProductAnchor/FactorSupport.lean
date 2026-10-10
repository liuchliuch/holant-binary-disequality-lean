import Holant.EightVertex.ProductAnchor.FactorEquality
import Holant.EightVertex.ProductAnchor.DenseClassification

namespace Holant.EightVertex.ProductAnchor
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def constantBlocks (D : TensorDecomposition Scalar 4) (b : Fin D.count → Bool) : Word4 :=
  fun p => b (D.ports.symm p).1

@[simp] theorem constantBlocks_ports (D : TensorDecomposition Scalar 4)
    (b : Fin D.count → Bool) (i : Fin D.count) (j : Fin (D.arity i)) :
    constantBlocks D b (D.ports ⟨i,j⟩)=b i := by simp [constantBlocks]

theorem constantBlocks_injective (D : TensorDecomposition Scalar 4)
    (hp : ∀ i,0<D.arity i) : Function.Injective (constantBlocks D) := by
  intro b c h
  funext i
  simpa using congrFun h (D.ports ⟨i,⟨0,hp i⟩⟩)

theorem constantBlocks_nonzero (D : TensorDecomposition Scalar 4)
    (he : ∀ i,D.factor i (fun _ => false)≠0 ∧ D.factor i (fun _ => true)≠0)
    (b : Fin D.count → Bool) : D.value (constantBlocks D b)≠0 := by
  unfold TensorDecomposition.value
  apply mul_ne_zero D.scale.ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simp only [constantBlocks_ports]
  cases b i
  · exact (he i).1
  · exact (he i).2

theorem constantBlocks_of_nonzero (D : TensorDecomposition Scalar 4)
    (hp : ∀ i,0<D.arity i)
    (hf : ∀ i y,D.factor i y =
      (if y=(fun _ => false) then D.factor i (fun _ => false) else 0) +
      (if y=(fun _ => true) then D.factor i (fun _ => true) else 0))
    (x : Word4) (hx : D.value x≠0) : ∃ b,x=constantBlocks D b := by
  have hn (i : Fin D.count) : D.factor i (fun k => x (D.ports ⟨i,k⟩))≠0 :=
    Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).2 i (Finset.mem_univ i)
  have hc (i : Fin D.count) :
      (fun k => x (D.ports ⟨i,k⟩))=(fun _ => false) ∨
      (fun k => x (D.ports ⟨i,k⟩))=(fun _ => true) := by
    by_contra h
    have h' := not_or.mp h
    exact hn i (by rw [hf]; simp [h'.1,h'.2])
  refine ⟨fun i => x (D.ports ⟨i,⟨0,hp i⟩⟩),?_⟩
  funext p
  obtain ⟨⟨i,k⟩,rfl⟩ := D.ports.surjective p
  rw [constantBlocks_ports]
  rcases hc i with h | h
  · exact (congrFun h k).trans (congrFun h ⟨0,hp i⟩).symm
  · exact (congrFun h k).trans (congrFun h ⟨0,hp i⟩).symm

theorem TwoWeightedEqualities.support_card {q : Signature Scalar 4} (h : TwoWeightedEqualities q) :
    ((Finset.univ : Finset Word4).filter fun x => q x≠0).card=4 := by
  classical
  obtain ⟨D,hc,ha,rfl,he,hf⟩ := h
  have hp : ∀ i,0<D.arity i := fun i => by rw [ha i]; decide
  have hs : ((Finset.univ : Finset Word4).filter fun x => D.value x≠0)=
      Finset.univ.image (constantBlocks D) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨b,hb⟩ := constantBlocks_of_nonzero D hp hf x hx
      exact ⟨b,hb.symm⟩
    · rintro ⟨b,rfl⟩
      exact constantBlocks_nonzero D he b
  rw [hs,Finset.card_image_of_injective _ (constantBlocks_injective D hp)]
  simp [hc]

end
end Holant.EightVertex.ProductAnchor
