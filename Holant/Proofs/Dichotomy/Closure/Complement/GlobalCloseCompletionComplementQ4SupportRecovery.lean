import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4DifferenceRecovery
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ZeroExtrapolation

/-! Exponent-zero recovery for any four nonzero rates. The marked basis rows
may be zero, so replacing zero eigenvalues by rate one and zero basis rows
extracts the spectral support projector without a separation assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4SupportRecovery
open Holant
open scoped BigOperators
namespace B
export GlobalCloseCompletionComplementQ4Nodes (Box)
export GlobalCloseCompletionComplementQ4DifferenceRecovery (box mem_box box_length)
end B
namespace C
export GlobalCloseCompletionComplementQ4ColoredRecovery (histogram histogram_total histogram_product)
end C
namespace N
export GlobalCloseCompletionComplementQ4NetworkRecovery (network coefficient powers expansion)
end N
namespace D
export GlobalCloseCompletionComplementQ4Differences (processList samples factor)
export GlobalCloseCompletionComplementQ4ZeroExtrapolation (zeroed recover)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K]

def node (v : Fin 4→K) (n : ℕ) (m : B.Box n) : K:=
  if (∑i,(m i).val)=n then ∏i,v i^(m i).val else 1
def roots (v : Fin 4→K) (n : ℕ) : List K:=(B.box n).map (node v n)
theorem roots_length (v : Fin 4→K) (n : ℕ) : (roots v n).length=(n+1)^4 := by
  simp [roots,B.box_length]
theorem node_nonzero (v : Fin 4→K) (nonzero : ∀i,v i≠0) (n : ℕ) (m : B.Box n) : node v n m≠0 := by
  unfold node
  split_ifs
  · exact Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (nonzero i))
  · exact one_ne_zero
theorem roots_nonzero (v : Fin 4→K) (nonzero : ∀i,v i≠0) (n : ℕ) : ∀z∈roots v n,z≠0 := by
  intro z member
  obtain ⟨m,_,rfl⟩:=List.mem_map.mp member
  exact node_nonzero v nonzero n m
theorem color_member {V : Type} [Fintype V] [DecidableEq V] (v : Fin 4→K) (color : V→Fin 4) :
    (∏x,v (color x))∈roots v (Fintype.card V) := by
  have value : node v (Fintype.card V) (C.histogram color)=∏x,v (color x) := by
    rw [node,if_pos (C.histogram_total color),C.histogram_product]
  exact List.mem_map.mpr ⟨C.histogram color,B.mem_box _ _,value⟩

variable {n : ℕ} (original : Network K n) (marked : Finset (Fin original.shape.vertices))
variable (basis : Fin 4→(v : Fin original.shape.vertices)→Signature K (original.shape.arity v))

theorem recover (v : Fin 4→K) (nonzero : ∀i,v i≠0) (x : Fin n→Bool) :
    -(D.processList (roots v (Fintype.card marked))
      (D.samples (D.zeroed (fun k=>(N.network original marked basis (fun i=>v i^k)).denote x))
        0 ((roots v (Fintype.card marked)).length+1))).headD 0 /
      D.factor (roots v (Fintype.card marked)) 0=
      (N.network original marked basis (fun _=>1)).denote x := by
  classical
  have result:=D.recover (roots v (Fintype.card marked)) (fun color : marked→Fin 4=>∏p : marked,v (color p))
    (N.coefficient original marked basis x) (color_member v) (roots_nonzero v nonzero _)
  simpa only [N.powers,N.expansion,Finset.prod_pow,Finset.prod_const_one,mul_one] using result

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4SupportRecovery
end
