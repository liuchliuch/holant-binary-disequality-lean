import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Nodes

/-! The exponential expansion may be indexed by all colorings of the marked
vertices. Recovery still uses only the polynomial-sized exponent box; no
coloring is enumerated by the eventual oracle programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ColoredRecovery
open scoped BigOperators
namespace A
export GlobalCloseCompletionComplementQ4Annihilator (annihilator moment moment_sum root nonzero)
end A
namespace B
export GlobalCloseCompletionComplementQ4Nodes (Box Separated node admissible separation)
end B
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K V : Type} [Field K] [Fintype V] [DecidableEq V]

def histogram (color : V→Fin 4) : B.Box (Fintype.card V):=fun i=>
  ⟨(Finset.univ.filter (fun x=>color x=i)).card,
    Nat.lt_succ_of_le (Finset.card_le_card (Finset.filter_subset _ _))⟩

theorem histogram_total (color : V→Fin 4) :
    (∑i,(histogram color i).val)=Fintype.card V := by
  have total:=Finset.card_eq_sum_card_fiberwise
    (s:=Finset.univ) (t:=Finset.univ) (f:=color) (fun _ _=>Finset.mem_univ _)
  simpa only [histogram,Finset.card_univ] using total.symm

theorem histogram_product (v : Fin 4→K) (color : V→Fin 4) :
    (∏i,v i^(histogram color i).val)=∏x,v (color x) := by
  have product:=Finset.prod_fiberwise' (Finset.univ : Finset V) color v
  simpa only [Finset.prod_const,histogram] using product

theorem histogram_foreign (j : Fin 4) (color : V→Fin 4) (foreign : color≠fun _=>j) :
    ∃i,i≠j ∧ (histogram color i).val≠0 := by
  classical
  obtain ⟨x,hx⟩:=Function.ne_iff.mp foreign
  refine ⟨color x,hx,?_⟩
  apply Nat.ne_of_gt
  exact Finset.card_pos.mpr ⟨x,by simp⟩

theorem node_color (v : Fin 4→K) (j : Fin 4) (color : V→Fin 4) (foreign : color≠fun _=>j) :
    B.node v j (Fintype.card V) (histogram color)=∏x,v (color x) := by
  classical
  rw [B.node,if_pos (show B.admissible (Fintype.card V) j (histogram color) from
    ⟨histogram_total color,histogram_foreign j color foreign⟩),histogram_product]

theorem unwanted_root (v : Fin 4→K) (j : Fin 4) (color : V→Fin 4) (foreign : color≠fun _=>j) :
    (A.annihilator (B.node v j (Fintype.card V))).eval (∏x,v (color x))=0 := by
  rw [←node_color v j color foreign]
  exact A.root _ _

theorem isolate (v : Fin 4→K) (j : Fin 4) (coefficients : (V→Fin 4)→K) :
    A.moment (A.annihilator (B.node v j (Fintype.card V)))
      (fun k=>∑color,coefficients color*(∏x,v (color x))^k)=
      coefficients (fun _=>j)*v j^(Fintype.card V)*
        (A.annihilator (B.node v j (Fintype.card V))).eval (v j^(Fintype.card V)) := by
  classical
  rw [A.moment_sum]
  rw [Finset.sum_eq_single (fun _ : V=>j)]
  · simp only [Finset.prod_const,Finset.card_univ]
  · intro color _ foreign
    rw [unwanted_root v j color foreign,mul_zero]
  · simp

theorem recover (v : Fin 4→K) (j : Fin 4) (separated : B.Separated v j)
    (coefficients : (V→Fin 4)→K) :
    A.moment (A.annihilator (B.node v j (Fintype.card V)))
      (fun k=>∑color,coefficients color*(∏x,v (color x))^k) /
      (v j^(Fintype.card V)*∏m,(v j^(Fintype.card V)-B.node v j (Fintype.card V) m))=
      coefficients (fun _=>j) := by
  rw [isolate,←GlobalCloseCompletionComplementQ4Annihilator.evaluation,mul_assoc]
  exact mul_div_cancel_right₀ _ (mul_ne_zero (pow_ne_zero _ separated.1)
    (A.nonzero _ _ (B.separation v j separated _)))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ColoredRecovery
end
