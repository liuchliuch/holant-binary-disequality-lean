import Holant.Certificates.FourthRootOdd.TwoCopyNetwork


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.TwoCopyKernels
open Holant.Certificates.FourthRootOdd
noncomputable section

theorem first_word (p : Fin 6) (u r v t : Bool) (x : Fin 4 → Bool) :
    (fun i : Fin 4 => fourPrefix u r v t x ((copyEquiv p).symm (Fin.castAdd 4 i))) =
      insertPair p u v (firstHalf x) := by
  funext i
  fin_cases p <;> fin_cases i <;> rfl

theorem second_word (p : Fin 6) (u r v t : Bool) (x : Fin 4 → Bool) :
    (fun i : Fin 4 => fourPrefix u r v t x ((copyEquiv p).symm (Fin.natAdd 4 i))) =
      insertPair p r t (secondHalf x) := by
  funext i
  fin_cases p <;> fin_cases i <;> rfl

variable {K : Type*} [CommSemiring K]

def contraction (f g : Signature K 4) (p : Fin 6)
    (A B : Bool → Bool → K) : Signature K 4 := fun x =>
  ∑ u : Bool, ∑ v : Bool, ∑ r : Bool, ∑ t : Bool,
    A u r * B v t * f (insertPair p u v (firstHalf x)) *
      g (insertPair p r t (secondHalf x))

def network (f g : Signature K 4) (p : Fin 6)
    (A B : Bool → Bool → K) : Network K 4 :=
  ((reorderNetwork ((singleVertexNetwork f).tensor (singleVertexNetwork g))
    (copyEquiv p).symm).contract A).contract B

/-- The four sums run over the actual two edge incidences, rather than over
an assumed replacement signature. The two vertices may be different. -/
theorem network_denote (f g : Signature K 4) (p : Fin 6)
    (A B : Bool → Bool → K) : (network f g p A B).denote = contraction f g p A B := by
  rw [network, Network.denote_contract, Network.denote_contract,
    reorderNetwork_denote, Network.denote_tensor, singleVertexNetwork_denote,
    singleVertexNetwork_denote]
  funext x
  simp only [Signature.contract, Tensor.reindex_apply, Signature.tensor_apply]
  change (∑ v : Bool, ∑ t : Bool, B v t *
    (∑ u : Bool, ∑ r : Bool, A u r *
      (f (fun i => fourPrefix u r v t x ((copyEquiv p).symm (Fin.castAdd 4 i))) *
       g (fun i => fourPrefix u r v t x ((copyEquiv p).symm (Fin.natAdd 4 i)))))) = _
  simp only [first_word, second_word]
  simp only [contraction,Fintype.sum_bool]
  ring

def diagonal (a b : K) : Bool → Bool → K := fun u v =>
  if u = v then (if u then b else a) else 0

theorem diagonal_equality (f g : Signature K 4) (p : Fin 6) (a b : K)
    (x : Fin 4 → Bool) :
    contraction f g p (diagonal a b) Signature.equality x =
      a * f (insertPair p false false (firstHalf x)) *
        g (insertPair p false false (secondHalf x)) +
      a * f (insertPair p false true (firstHalf x)) *
        g (insertPair p false true (secondHalf x)) +
      b * f (insertPair p true false (firstHalf x)) *
        g (insertPair p true false (secondHalf x)) +
      b * f (insertPair p true true (firstHalf x)) *
        g (insertPair p true true (secondHalf x)) := by
  simp only [contraction,Fintype.sum_bool,diagonal,Signature.equality]
  norm_num
  ac_rfl

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.TwoCopyKernels
