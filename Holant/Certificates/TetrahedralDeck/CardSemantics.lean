import Holant.Certificates.TetrahedralDeck.AncestorSemantics

/-! Exact source contractions with the original selected-pair orientation and
increasing residual order, interpreted from the integral finite checker. -/
namespace Holant.Certificates.TetrahedralDeck
open Holant Holant.Certificates.TwelveLoops Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def card (s : Fin 3) (p : Fin 15) (k : Fin 12) : FourTensor :=
  Signature.contract (actualKernel k) (Tensor.reindex (portOrder p).symm (TetrahedralAffine.complexAncestor s))

theorem six_vector_cons (a b : Bool) (x : Word) :
    (![a,b,x 0,x 1,x 2,x 3] : SixWord) = Fin.cons a (Fin.cons b x) := by
  funext i
  fin_cases i <;> rfl

theorem card_apply (s : Fin 3) (p : Fin 15) (k : Fin 12) (x : Word) :
    card s p k x = ∑ a : Bool, ∑ b : Bool,
      actualKernel k a b*TetrahedralAffine.complexAncestor s (join p a b x) := by
  unfold card Signature.contract Tensor.reindex
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  unfold join
  rw [six_vector_cons]
  rfl

theorem embed_gCard (s : Fin 3) (p : Fin 15) (k : Fin 12) (x : Word) :
    embed (gCard s p k x) = 4*card s p k x := by
  rw [card_apply]
  simp [gCard,embed_add,embed_mul,embed_gKernel,embed_gAncestor,Fintype.sum_bool]
  ring

theorem embed_gMatch (r : Fin 3) (u v : Fin 12) (x : Word) :
    embed (gMatch r u v x) = matchingProduct r (actualKernel u) (actualKernel v) x := by
  fin_cases r <;> simp [gMatch,matchingProduct,P0,P1,P2,embed_mul,embed_gKernel]

end
end Holant.Certificates.TetrahedralDeck
