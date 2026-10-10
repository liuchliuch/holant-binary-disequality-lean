import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesCore
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDiagonalCorrection
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesCaps

/-! Literal table transport and one-port diagonal correction retain every
original paired-row coefficient and every ordinary internal edge. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesRelabel
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
namespace C
export GlobalCloseCompletionUnaryDiagonalCorrection (correct correct_value labels exact ordinary)
end C
namespace P
export GlobalCloseCompletionPairedSeriesCore (row)
export GlobalCloseCompletionPairedSeriesCaps (transposePorts transpose_value)
end P
namespace D
export OrdinaryTargetInterpolationDiagonal (diagonal)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] {s t n : ℕ} {a b : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (J : (i : Fin t)→Signature K (b i.val))
variable (old : Fin s→Fin t)
variable (literal : ∀i,(⟨b (old i).val,J (old i)⟩ : AnySignature K)=⟨a i.val,H i⟩)

def relabel (N : M.Macro H n) : M.Macro J n where
  network:=N.network
  labels:={vertex v:=old (N.labels.vertex v)
           vertex_arity v:=(congrArg Sigma.fst (literal (N.labels.vertex v))).trans (N.labels.vertex_arity v)
           edge:=N.labels.edge}
  exact:=fun v=>(literal (N.labels.vertex v)).trans (N.exact v)
  edges:=N.edges

def correct (N : M.Macro H 4) (Q : M.Macro H 2) : M.Macro H 4 :=
  let T:=N.reindex P.transposePorts
  { network:=C.correct T.network Q.network
    labels:=C.labels T.network Q.network T.labels Q.labels
    exact:=C.exact H T.network Q.network T.labels Q.labels T.exact Q.exact
    edges:=C.ordinary T.network Q.network T.edges Q.edges }

theorem correct_value (N : M.Macro H 4) (Q : M.Macro H 2) (B : Matrix Bool Bool K) (u v : K)
    (hN : N.network.denote=P.row B) (hQ : Q.network.denote=binarySignature (D.diagonal u v)) :
    (correct H N Q).network.denote=P.row (B*D.diagonal u v) := by
  funext x
  rw [correct,C.correct_value,P.transpose_value N B hN,hQ]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [P.row,D.diagonal,binarySignature,Matrix.mul_apply,Matrix.transpose_apply,h0,h1,h2,h3]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesRelabel
end
