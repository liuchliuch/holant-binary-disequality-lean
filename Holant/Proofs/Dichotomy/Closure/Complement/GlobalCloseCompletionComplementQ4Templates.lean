import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Series
import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeGraphOperations

/-! Every positive Bell-series sample is a real native-X macro with the
same original dictionary. Its labels, scalar-free denotation, template and
linear vertex/edge growth are preserved through every series connection. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Templates
open Holant Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace S
export GlobalCloseCompletionComplementQ4Series (ofSpectrum connected_spectrum)
end S
namespace G
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowNetwork (connect order)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {r : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (b i.val))


def connect (N M : A.Output H 4) : A.Output H 4:=
  contract H (n:=4) (contract H (n:=6) (reindex H (n:=8) (tensor H (m:=4) (n:=4) N M) (G.order false)))
theorem connect_network (N M : A.Output H 4) :
    (connect H N M).network=G.connect N.network M.network false:=rfl
theorem connect_vertices (N M : A.Output H 4) :
    (connect H N M).network.shape.vertices=N.network.shape.vertices+M.network.shape.vertices:=rfl
theorem connect_edges (N M : A.Output H 4) :
    (connect H N M).network.shape.edges=N.network.shape.edges+M.network.shape.edges+2:=by
  change (N.network.shape.edges+M.network.shape.edges+1)+1=_
  omega

def power (N : A.Output H 4) : ℕ→A.Output H 4
  | 0=>N
  | k+1=>connect H (power N k) N

theorem value [CharZero K] (N : A.Output H 4) (v : Fin 4→K)
    (form : N.network.denote=S.ofSpectrum v) (k : ℕ) :
    (power H N k).network.denote=S.ofSpectrum (fun i=>v i^(k+1)) := by
  induction k with
  | zero=>simpa [power] using form
  | succ k ih=>
    rw [power,connect_network,S.connected_spectrum _ _ _ _ ih form]
    congr 1
    funext i
    exact (pow_succ (v i) (k+1)).symm

theorem vertices (N : A.Output H 4) (k : ℕ) :
    (power H N k).network.shape.vertices=(k+1)*N.network.shape.vertices := by
  induction k with
  | zero=>simp [power]
  | succ k ih=>rw [power,connect_vertices,ih];ring
theorem edges (N : A.Output H 4) (k : ℕ) :
    (power H N k).network.shape.edges=(k+1)*N.network.shape.edges+2*k := by
  induction k with
  | zero=>simp [power]
  | succ k ih=>rw [power,connect_edges,ih];ring

def template (N : A.Output H 4) (k : ℕ) : Template:=(power H N k).labels.template
theorem valid (N : A.Output H 4) (k : ℕ) : (template H N k).WellFormed r 1 b:=
  (power H N k).labels.wellFormed
theorem boundary (N : A.Output H 4) (k : ℕ) : (template H N k).boundary=4:=rfl
theorem template_value [CharZero K] (N : A.Output H 4) (v : Fin 4→K)
    (form : N.network.denote=S.ofSpectrum v) (k : ℕ) :
    ((template H N k).network (valid H N k) H (fun _ : Fin 1=>Signature.disequality)).denote=
      S.ofSpectrum (fun i=>v i^(k+1)) :=
  (A.template_exact H (power H N k)).trans (value H N v form k)
theorem template_vertices (N : A.Output H 4) (k : ℕ) :
    (template H N k).vertices.length=(k+1)*N.network.shape.vertices:=
  (power H N k).labels.vertices_length.trans (vertices H N k)
theorem template_edges (N : A.Output H 4) (k : ℕ) :
    (template H N k).edges.length=(k+1)*N.network.shape.edges+2*k:=
  (power H N k).labels.edges_length.trans (edges H N k)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Templates
end
