import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZGraph
import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZAction
import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZSymmetry

/-! Genuine GHZ symmetrization: an actual prime ternary in the GHZ orbit
has an actual symmetric prime ternary over exactly the same original labels.
The exceptional zero triangles return the already symmetric original row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZSource
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
namespace T
export GlobalCloseCompletionTernaryGHZCore (ghz triangle cyclic)
export GlobalCloseCompletionTernaryGHZAction (det triangle_prime)
export GlobalCloseCompletionTernaryGHZSymmetry (symmetric values)
end T
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (reindex reindex_denote)
end M
namespace G
export GlobalCloseCompletionTernaryGHZGraph (triangle value)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable {H : (i : Fin s)→Signature K (a i.val)}
variable (phi : K→+*AlgebraicComplex)

def rotatePorts : Equiv.Perm (Fin 3) where
  toFun:=![1,2,0]
  invFun:=![2,0,1]
  left_inv:=by decide
  right_inv:=by decide

def rotate (N : M.Macro H 3) : M.Macro H 3 := N.reindex rotatePorts

theorem rotate_value (N : M.Macro H 3) :
    (rotate N).network.denote=(fun x=>N.network.denote (T.cyclic x)) := by
  rw [rotate,M.reindex_denote]
  funext x
  change N.network.denote (fun i=>x (rotatePorts i))=N.network.denote (T.cyclic x)
  congr 1
  funext i
  fin_cases i <;> rfl

theorem map_triangle (f : Signature K 3) :
    RingHomRealization.mapSignature phi (T.triangle f)=T.triangle (RingHomRealization.mapSignature phi f) := by
  funext x
  simp only [RingHomRealization.mapSignature,T.triangle,map_sum,map_mul]

theorem rotate_ghz (N : M.Macro H 3) (A B C : InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote=T.ghz A.matrix B.matrix C.matrix) :
    RingHomRealization.mapSignature phi (rotate N).network.denote=T.ghz C.matrix A.matrix B.matrix := by
  funext x
  rw [RingHomRealization.mapSignature,rotate_value]
  have he:=congrFun form (T.cyclic x)
  change phi (N.network.denote (T.cyclic x))=_ at he
  rw [he]
  simp [T.ghz,T.cyclic,Fintype.sum_bool]
  ring

def Good (A B : InvertibleKernel) : Prop :=
  ((Matrix.of A.matrix).transpose*(Matrix.of B.matrix)) false false≠0 ∨
    ((Matrix.of A.matrix).transpose*(Matrix.of B.matrix)) true true≠0

private theorem triangle_output (N : M.Macro H 3) (A B C : InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote=T.ghz A.matrix B.matrix C.matrix)
    (good : Good B C) :
    ∃Q : M.Macro H 3,Prime (⟨3,RingHomRealization.mapSignature phi Q.network.denote⟩ : AnySignature AlgebraicComplex) ∧
      ∃v : Fin 4→AlgebraicComplex,RingHomRealization.mapSignature phi Q.network.denote=T.symmetric v := by
  refine ⟨G.triangle N,?_,?_⟩
  · rw [G.value,map_triangle,form]
    exact T.triangle_prime A B C good
  · refine ⟨T.values (T.triangle (T.ghz A.matrix B.matrix C.matrix)),?_⟩
    rw [G.value,map_triangle,form]
    exact GlobalCloseCompletionTernaryGHZSymmetry.triangle _

theorem produce (N : M.Macro H 3) (A B C : InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote=T.ghz A.matrix B.matrix C.matrix)
    (prime : Prime (⟨3,RingHomRealization.mapSignature phi N.network.denote⟩ : AnySignature AlgebraicComplex)) :
    ∃Q : M.Macro H 3,Prime (⟨3,RingHomRealization.mapSignature phi Q.network.denote⟩ : AnySignature AlgebraicComplex) ∧
      ∃v : Fin 4→AlgebraicComplex,RingHomRealization.mapSignature phi Q.network.denote=T.symmetric v := by
  classical
  by_cases bc : Good B C
  · exact triangle_output phi N A B C form bc
  by_cases ab : Good A B
  · exact triangle_output phi (rotate N) C A B (rotate_ghz phi N A B C form) ab
  by_cases ca : Good C A
  · exact triangle_output phi (rotate (rotate N)) B C A
      (rotate_ghz phi (rotate N) C A B (rotate_ghz phi N A B C form)) ca
  have zero (U V : InvertibleKernel) (bad : ¬Good U V) : ∀t,((Matrix.of U.matrix).transpose*(Matrix.of V.matrix)) t t=0 := by
    intro t
    cases t
    · exact not_ne_iff.mp ((not_or.mp bad).1)
    · exact not_ne_iff.mp ((not_or.mp bad).2)
  refine ⟨N,prime,T.values (T.ghz A.matrix B.matrix C.matrix),?_⟩
  rw [form]
  exact GlobalCloseCompletionTernaryGHZSymmetry.exception A.matrix B.matrix C.matrix
    (T.det A) (T.det B) (T.det C) (zero A B ab) (zero B C bc) (zero C A ca)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZSource
end
