import Holant.Complexity.UniversalPairReduction.Surgery.Weights
import Holant.Complexity.UniversalPairReduction.BinaryTable
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

/-! Exact elimination in the original native-X edge-choice sum. Distinct-edge
smoothing has no scalar; a deleted self-loop contributes the exact off-diagonal
trace of the removed binary, giving one for Delta and two for X. -/
namespace Holant.Complexity.UniversalPairReduction.Surgery.Choice
open Smoothing
open scoped BigOperators
variable {K : Type*} [CommSemiring K]

 theorem evaluate_splice (F : Table K) (m label : ℕ) (p q : RawEndpoint) (rows : List RawVertex)
    (hp : p.1<m) (hq : q.1<m) (hne : p.1≠q.1)
    (hr : ∀row∈rows,∀r∈row.2,r.1<m ∧ r≠p ∧ r≠q)
    (hF : ∀a b,F label [a,b]=Signature.disequality a b) :
    evaluate F m ((label,[p,q])::rows) =
      evaluate F (m-1) (mapRows (spliceEndpoint p q) rows) := by
  classical
  letI : Fintype (Fin (m-1) → Bool) := inferInstance
  letI : Fintype (Bool × (Fin (m-1) → Bool)) := inferInstance
  unfold evaluate
  rw [←(splitEdge m q.1 hq).symm.sum_comp,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  have hext (d : Bool) := weight_extend_split F m q.1 hq d c ((label,[p,q])::rows) (by
    intro row hrow r hrr
    rcases List.mem_cons.mp hrow with rfl|hrow
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hrr
      rcases hrr with rfl|rfl <;> assumption
    · exact (hr row hrow r hrr).1)
  simp_rw [hext,weight_cons]
  simp only [rowValue,List.map_cons,List.map_nil,hF]
  simp_rw [native_selector p q (extend c) _ hne]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact weight_splice F p q (extend c) rows hne (fun row hrow r hrr => (hr row hrow r hrr).2)

 theorem evaluate_loop (F : Table K) (m label e : ℕ) (he : e<m) (side : Bool)
    (B : BinaryTable K) (rows : List RawVertex)
    (hr : ∀row∈rows,∀p∈row.2,p.1<m ∧ p.1≠e)
    (hF : ∀a b,F label [a,b]=B a b) :
    evaluate F m ((label,[(e,side),(e,!side)])::rows) =
      (B false true+B true false)*evaluate F (m-1) (mapRows (removeLoopEndpoint e) rows) := by
  classical
  letI : Fintype (Fin (m-1) → Bool) := inferInstance
  letI : Fintype (Bool × (Fin (m-1) → Bool)) := inferInstance
  unfold evaluate
  rw [←(splitEdge m e he).symm.sum_comp,Fintype.sum_prod_type,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  have hext (d : Bool) := weight_extend_split F m e he d c
      ((label,[(e,side),(e,!side)])::rows) (by
    intro row hrow p hp
    rcases List.mem_cons.mp hrow with rfl|hrow
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl|rfl <;> exact he
    · exact (hr row hrow p hp).1)
  simp_rw [hext,weight_cons]
  simp only [rowValue,List.map_cons,List.map_nil,hF]
  simp_rw [weight_loop F e _ (extend c) rows (fun row hrow p hp => (hr row hrow p hp).2)]
  cases side <;> simp [bit,restore,Fintype.sum_bool,add_mul,add_comm]

end Holant.Complexity.UniversalPairReduction.Surgery.Choice
