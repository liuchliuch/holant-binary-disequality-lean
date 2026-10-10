import Holant.Certificates.FourthRootOdd.EqualityLoopNetwork

/-! The literal series-I support flip. It is an ordinary tensor product and
one native contraction, with the equality vertex retained as a resource. -/
namespace Holant.Certificates.FourthRootOdd
open Holant
set_option backward.isDefEq.respectTransparency false

def seriesEquiv : Equiv.Perm (Fin 4) where
  toFun := ![1,2,0,3]
  invFun := ![2,0,1,3]
  left_inv := by decide
  right_inv := by decide

variable {K : Type*} [CommSemiring K]
def flipSecond (f : Signature K 2) : Signature K 2 := fun x => f ![x 0,!(x 1)]
noncomputable def seriesEquality (N : Network K 2) : Network K 2 :=
  (reorderNetwork (N.tensor (singleVertexNetwork equalitySignature)) seriesEquiv.symm).contract
    Signature.disequality

theorem series_left_word (u v : Bool) (x : Fin 2 → Bool) :
    (fun i : Fin 2 => Fin.cons (α := fun _ : Fin 4 => Bool) u (Fin.cons v x)
      (seriesEquiv.symm (Fin.castAdd 2 i)))=![x 0,u] := by
  funext i
  fin_cases i <;> rfl
theorem series_right_word (u v : Bool) (x : Fin 2 → Bool) :
    (fun i : Fin 2 => Fin.cons (α := fun _ : Fin 4 => Bool) u (Fin.cons v x)
      (seriesEquiv.symm (Fin.natAdd 2 i)))=![v,x 1] := by
  funext i
  fin_cases i <;> rfl

theorem seriesEquality_denote (N : Network K 2) :
    (seriesEquality N).denote=flipSecond N.denote := by
  rw [seriesEquality,Network.denote_contract,reorderNetwork_denote,Network.denote_tensor,
    singleVertexNetwork_denote]
  funext x
  simp only [Signature.contract_disequality,Tensor.reindex_apply,Signature.tensor_apply,
    series_left_word,series_right_word]
  cases hx : x 1 <;> simp [equalitySignature,Signature.equality,flipSecond,hx]

theorem seriesEquality_realizes (N : Network K 2) (F : SignatureFamily K)
    (hN : ∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈F)
    (hE : ∀ e,N.edge e=Signature.disequality)
    (hI : (⟨2,equalitySignature⟩ : AnySignature K)∈F) :
    Gadget.Realizes F .disequality (flipSecond N.denote) := by
  rw [←seriesEquality_denote]
  apply Gadget.realizes_network
  · intro v
    change (⟨_,(Network.tensorFinite N (singleVertexNetwork equalitySignature)).vertex
      ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin 1)).symm v)⟩ : AnySignature K)∈F
    cases (Fintype.equivFin (Fin N.shape.vertices ⊕ Fin 1)).symm v with
    | inl v => exact hN v
    | inr v => exact hI
  · intro e
    refine Fin.cases rfl (fun e => ?_) e
    change (Network.tensorFinite N (singleVertexNetwork equalitySignature)).edge
      ((Fintype.equivFin (Fin N.shape.edges ⊕ Fin 0)).symm e)=Signature.disequality
    cases (Fintype.equivFin (Fin N.shape.edges ⊕ Fin 0)).symm e with
    | inl e => exact hE e
    | inr e => exact Fin.elim0 e

theorem flipped_nativeContract_realizes (f : Signature K 4) (p : Fin 6) :
    Gadget.Realizes (loopResources f) .disequality (flipSecond (nativeContract f p)) := by
  have h := seriesEquality_realizes (nativeLoopNetwork f p) (loopResources f)
    (by intro v; change (⟨4,f⟩ : AnySignature K)∈loopResources f; simp [loopResources])
    (by intro e; change Fin 1 at e; have he : e=0 := Subsingleton.elim _ _; subst e; rfl)
    (by simp [loopResources])
  rwa [nativeLoopNetwork_denote] at h

end Holant.Certificates.FourthRootOdd
