import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinarySquare

/-! Exact ordinary two-copy parity-block square, with the actual crossed
wire order corrected by swapping the right copy's first two ports. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SignedSixSquare
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (series seriesLabels series_exact series_ordinary)
end P
namespace C
export BinaryInterpolation.Chains (reindex reindex_denote tensor_denote)
end C
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
namespace M
export GeneralEOAffinePlaneChain (seriesOrder)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val))

abbrev square (N : Macro H 4) := GlobalCloseCompletionC2OrdinarySquare.square H N
open Holant.LocalDrafts.Hardness.EightVertexNonexception

def signed (b c d : K) : Signature K 4 := table ⟨0,b,c,d,d,c,-b,0⟩

theorem square_table (N : Macro H 4) (a b c d e f g h : K)
    (form : N.network.denote=table ⟨a,b,c,d,e,f,g,h⟩) :
    (square H N).network.denote=table ⟨a^2+b*g,b*(a+h),c^2+d*e,d*(c+f),e*(c+f),f^2+d*e,g*(a+h),h^2+b*g⟩ := by
  funext x
  change (P.series N.network (C.reindex N.network (Equiv.swap 0 1))).denote x=_
  rw [P.series,Network.denote_contract_equality,Network.denote_contract_equality,
    Network.denote_contract_equality,C.reindex_denote,C.tensor_denote,C.reindex_denote,form]
  have eval (u v w z : Bool) :
      Tensor.reindex M.seriesOrder ((table ⟨a,b,c,d,e,f,g,h⟩).tensor
        (Tensor.reindex (Equiv.swap 0 1) (table ⟨a,b,c,d,e,f,g,h⟩)))
        (Fin.cons u (Fin.cons v (Fin.cons w (Fin.cons z x))))=
      table ⟨a,b,c,d,e,f,g,h⟩ ![x 0,x 1,u,w]*table ⟨a,b,c,d,e,f,g,h⟩ ![v,z,x 2,x 3] := by
    simp only [Tensor.reindex_apply,Signature.tensor_apply]
    congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl
  rw [eval,eval,eval,eval]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [table,h0,h1,h2,h3] <;> ring

theorem square_signed (N : Macro H 4) (b c d : K) (form : N.network.denote=signed b c d) :
    (square H N).network.denote=T.normal (-b^2) 0 (c^2+d^2) (2*c*d) := by
  rw [square_table H N 0 b c d d c (-b) 0 form]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [T.normal,table,h0,h1,h2,h3] <;> ring

theorem swap_signed (b c d : K) : Tensor.reindex (Equiv.swap 1 2) (signed b c d)=table ⟨0,c,b,d,d,-b,c,0⟩ := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,Equiv.swap_apply_def,signed,table,h0,h1,h2,h3]

theorem swap_last (b c d : K) : Tensor.reindex (Equiv.swap 2 3) (signed b c d)=signed b d c := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,Equiv.swap_apply_def,signed,table,h0,h1,h2,h3]

def side (N : Macro H 4) : Macro H 4 := N.reindex (Equiv.swap 1 2)
def other (N : Macro H 4) : Macro H 4 := (N.reindex (Equiv.swap 2 3)).reindex (Equiv.swap 1 2)

theorem side_square (N : Macro H 4) (b c d : K) (form : N.network.denote=signed b c d) :
    (square H (side H N)).network.denote=T.normal (c^2) 0 (b^2+d^2) 0 := by
  have h : (side H N).network.denote=table ⟨0,c,b,d,d,-b,c,0⟩ := by
    rw [side,Macro.reindex_denote,form,swap_signed]
  rw [square_table H (side H N) 0 c b d d (-b) c 0 h]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [T.normal,table,h0,h1,h2,h3] <;> ring

theorem other_square (N : Macro H 4) (b c d : K) (form : N.network.denote=signed b c d) :
    (square H (other H N)).network.denote=T.normal (d^2) 0 (b^2+c^2) 0 := by
  exact side_square H (N.reindex (Equiv.swap 2 3)) b d c
    (by rw [Macro.reindex_denote,form,swap_last])


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SignedSixSquare
end
