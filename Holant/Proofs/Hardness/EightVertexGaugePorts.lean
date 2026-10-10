import Holant.Proofs.Hardness.EightVertexGaugeTwoRowPencil

/-! Port selection for the actual two-row test. A permutation moves boundary
occurrences, never the original vertex label. The coefficient reindexing below
is a proved semantic equality and does not authorize new unary resources. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePorts
open Holant
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
open EightVertexGaugeTwoRowAlgebra EightVertexGaugeTwoRowPencil
open scoped BigOperators
variable {K : Type} [Field K]

theorem weighted_reindex (a : K) (u : Fin 4 → K) (e : Equiv.Perm (Fin 4)) :
    Tensor.reindex e (weighted a u) = weighted a (fun i => u (e.symm i)) := by
  funext x
  change weighted a u (fun i => x (e i)) = _
  rw [weighted_value,weighted_value]
  have hw : weight (fun i => x (e i)) = weight x :=
    Equiv.sum_comp e (fun i => if x i then 1 else 0)
  have hp : (∏ i, if x (e i) then u i else 1) =
      ∏ i, if x i then u (e.symm i) else 1 := by
    simpa only [Equiv.symm_apply_apply] using
      Equiv.prod_comp e (fun i => if x i then u (e.symm i) else 1)
  rw [hw,hp]

theorem onPorts_output (a b : K) (u v : Fin 4 → K)
    (e f : Equiv.Perm (Fin 4)) (cross : Bool) :
    (EightVertexGaugeTwoRowNetwork.onPorts (weighted a u) (weighted b v) e f cross).denote =
      output a b (fun i => u (e.symm i)) (fun i => v (f.symm i)) cross := by
  rw [EightVertexGaugeTwoRowNetwork.onPorts_denote,weighted_reindex,weighted_reindex,
    network_output]

theorem onPorts_output_realizes (a b : K) (u v : Fin 4 → K)
    (e f : Equiv.Perm (Fin 4)) (cross : Bool) (F : SignatureFamily K)
    (hM : (⟨4,weighted a u⟩ : AnySignature K) ∈ F)
    (hN : (⟨4,weighted b v⟩ : AnySignature K) ∈ F) :
    Gadget.Realizes F .disequality
      (output a b (fun i => u (e.symm i)) (fun i => v (f.symm i)) cross) := by
  rw [← onPorts_output]
  exact EightVertexGaugeTwoRowNetwork.onPorts_realizes _ _ e f cross F hM hN

/-- Three incidence charts select original internal pairs 01,02,03. -/
def zeroPair (i : Fin 3) : Equiv.Perm (Fin 4) where
  toFun := ![![2,3,0,1],![2,0,3,1],![2,0,1,3]] i
  invFun := ![![2,3,0,1],![1,3,0,2],![1,2,0,3]] i
  left_inv := by fin_cases i <;> decide
  right_inv := by fin_cases i <;> decide

/-- If these three NEW physical rows each possess their own safe complete
phase deck, all four original port weights have the same fourth power.
The deck hypothesis is explicit and is not inherited from the original row. -/
theorem all_fourth_of_three_decks {m : ℕ} (hm : 3 ≤ m) (a : ℂ) (u : Fin 4 → ℂ)
    (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0)
    (decks : ∀ i : Fin 3, Holant.Marked.SupportAtlas.SafeDeck m 1
      (EightVertexGaugeTwoRowNetwork.onPorts (weighted a u) (weighted a u)
        (zeroPair i) (zeroPair i) true).denote) :
    ∀ i j, u i ^ 4 = u j ^ 4 := by
  have h (i : Fin 3) :
      u ((zeroPair i).symm 2) ^ 4 = u ((zeroPair i).symm 3) ^ 4 := by
    apply self_crossed_safe_fourth hm a (fun k => u ((zeroPair i).symm k)) ha
      (fun k => hu _)
    simpa only [onPorts_output] using decks i
  have h01 : u 0 ^ 4 = u 1 ^ 4 := by simpa [zeroPair] using h 0
  have h02 : u 0 ^ 4 = u 2 ^ 4 := by simpa [zeroPair] using h 1
  have h03 : u 0 ^ 4 = u 3 ^ 4 := by simpa [zeroPair] using h 2
  have h0 (i : Fin 4) : u i ^ 4 = u 0 ^ 4 := by
    fin_cases i
    · rfl
    · exact h01.symm
    · exact h02.symm
    · exact h03.symm
  intro i j
  exact (h0 i).trans (h0 j).symm

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePorts
end
