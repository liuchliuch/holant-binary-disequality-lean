import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4NetworkRecovery
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Differences

/-! A four-loop exponent list and successive differences recover the exact
desired network. The only sample list contains positive physical powers;
the proof supplies its spectral expansion rather than requesting it. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4DifferenceRecovery
open Holant
open scoped BigOperators
namespace B
export GlobalCloseCompletionComplementQ4Nodes (Box node Separated separation)
end B
namespace C
export GlobalCloseCompletionComplementQ4ColoredRecovery (histogram node_color)
end C
namespace N
export GlobalCloseCompletionComplementQ4NetworkRecovery (network coefficient powers pure)
end N
namespace D
export GlobalCloseCompletionComplementQ4Differences
  (samples processList process_samples process_sum process_exp factor factor_zero factor_nonzero)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def box (n : ℕ) : List (B.Box n):=
  (List.finRange (n+1)).flatMap fun a=>(List.finRange (n+1)).flatMap fun b=>
    (List.finRange (n+1)).flatMap fun c=>(List.finRange (n+1)).map fun d=>![a,b,c,d]

theorem mem_box (n : ℕ) (m : B.Box n) : m∈box n := by
  simp only [box,List.mem_flatMap,List.mem_finRange,true_and,List.mem_map]
  refine ⟨m 0,m 1,m 2,m 3,?_⟩
  funext i
  fin_cases i <;> rfl

theorem box_length (n : ℕ) : (box n).length=(n+1)^4 := by
  simp [box,List.length_flatMap]
  ring

def roots (v : Fin 4→K) (j : Fin 4) (n : ℕ) : List K:=(box n).map (B.node v j n)
theorem roots_length (v : Fin 4→K) (j : Fin 4) (n : ℕ) : (roots v j n).length=(n+1)^4 := by
  simp [roots,box_length]
theorem root_member (v : Fin 4→K) (j : Fin 4) (n : ℕ) (m : B.Box n) : B.node v j n m∈roots v j n:=
  List.mem_map.mpr ⟨m,mem_box n m,rfl⟩
theorem root_separate (v : Fin 4→K) (j : Fin 4) (separated : B.Separated v j) (n : ℕ) :
    ∀z∈roots v j n,v j^n≠z := by
  intro z member
  obtain ⟨m,_,rfl⟩:=List.mem_map.mp member
  exact B.separation v j separated n m

variable {n : ℕ} (original : Network K n) (marked : Finset (Fin original.shape.vertices))
variable (basis : Fin 4→(v : Fin original.shape.vertices)→Signature K (original.shape.arity v))

theorem isolate (v : Fin 4→K) (j : Fin 4) (x : Fin n→Bool) :
    D.processList (roots v j (Fintype.card marked))
      (D.samples (fun k=>(N.network original marked basis (fun i=>v i^(k+1))).denote x) 0
        ((roots v j (Fintype.card marked)).length+1))=
      [(Holant.Complexity.BinaryInterpolation.rightNetwork original marked (basis j)).denote x*
        v j^(Fintype.card marked)*D.factor (roots v j (Fintype.card marked)) (v j^(Fintype.card marked))] := by
  classical
  rw [D.process_samples]
  have sampleForm : (fun k=>(N.network original marked basis (fun i=>v i^(k+1))).denote x)=
      fun k=>∑color : marked→Fin 4,N.coefficient original marked basis x color*(∏p : marked,v (color p))^(k+1) := by
    funext k
    exact N.powers original marked basis v (k+1) x
  rw [sampleForm,D.process_sum]
  simp only [D.process_exp,Nat.zero_add,pow_one]
  congr 1
  rw [Finset.sum_eq_single (fun _ : marked=>j)]
  · simp only [N.pure,Finset.prod_const,Finset.card_univ]
  · intro color _ foreign
    have member : (∏p : marked,v (color p))∈roots v j (Fintype.card marked) := by
      rw [←C.node_color v j color foreign]
      exact root_member v j _ _
    rw [D.factor_zero _ _ member,mul_zero]
  · simp

theorem recover (v : Fin 4→K) (j : Fin 4) (separated : B.Separated v j) (x : Fin n→Bool) :
    (D.processList (roots v j (Fintype.card marked))
      (D.samples (fun k=>(N.network original marked basis (fun i=>v i^(k+1))).denote x) 0
        ((roots v j (Fintype.card marked)).length+1))).headD 0 /
      (v j^(Fintype.card marked)*D.factor (roots v j (Fintype.card marked)) (v j^(Fintype.card marked)))=
      (Holant.Complexity.BinaryInterpolation.rightNetwork original marked (basis j)).denote x := by
  rw [isolate]
  simp only [List.headD_cons]
  rw [mul_assoc,mul_div_cancel_right₀ _ (mul_ne_zero (pow_ne_zero _ separated.1)
    (D.factor_nonzero _ _ (root_separate v j separated _)))]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4DifferenceRecovery
end
