import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationPolynomial
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationScale
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4SupportBasis

/-! Exhaustive actual three-chart reduction. A genuine redundant K4 output
or an explicit paired-square source survives, with the unchanged native table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationReduction
open Holant
namespace S
export GlobalCloseCompletionComplementQ4Series (row spectrum ofSpectrum reconstruct)
end S
namespace A
export GlobalCloseCompletionComplementQ4ClassificationAlgebra (outerLeft outerRight middle Paired)
end A
namespace P
export GlobalCloseCompletionComplementQ4ClassificationPolynomial (output_value)
end P
namespace C
export GlobalCloseCompletionComplementQ4ClassificationCircuit (output)
end C
namespace T
export GlobalCloseCompletionComplementQ4Templates (reindex)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

theorem swap_bd (a b c d : K) : Tensor.reindex (Equiv.swap 1 3) (S.row a b c d)=S.row a d c b := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,Equiv.swap_apply_def,S.row,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3]
theorem swap_cd (a b c d : K) : Tensor.reindex (Equiv.swap 2 3) (S.row a b c d)=S.row a b d c := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,Equiv.swap_apply_def,S.row,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3]
theorem swap_bc (a b c d : K) : Tensor.reindex (Equiv.swap 1 2) (S.row a b c d)=S.row a c b d := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,Equiv.swap_apply_def,S.row,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3]

variable [Algebra ℚ K] {size : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin size)→Signature K (arity i.val))

structure RedundantOutput where
  graph : NativeAntiTargetSource.Output H 4
  a : K
  b : K
  c : K
  value : graph.network.denote=S.row a b c c
  determinant : a^2≠b^2

theorem alternatives (N : NativeAntiTargetSource.Output H 4) (a b c d : K)
    (form : N.network.denote=S.row a b c d) (ha : a≠0) (hb : b≠0) (hd : d≠0) :
    A.Paired (b/a) (c/a) (d/a) ∨ Nonempty (RedundantOutput H) := by
  rcases GlobalCloseCompletionComplementQ4ClassificationScale.alternatives a b c d ha hb hd with
    paired|⟨u,v,w,chart,live⟩
  · exact Or.inl paired
  · right
    have select : ∃M : NativeAntiTargetSource.Output H 4,M.network.denote=S.row a u v w := by
      rcases chart with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
      · exact ⟨N,form⟩
      · refine ⟨T.reindex H N (Equiv.swap 1 3),?_⟩
        change (Holant.Complexity.BinaryInterpolation.Chains.reindex N.network (Equiv.swap 1 3)).denote=_
        rw [Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,form,swap_bd]
      · refine ⟨T.reindex H N (Equiv.swap 2 3),?_⟩
        change (Holant.Complexity.BinaryInterpolation.Chains.reindex N.network (Equiv.swap 2 3)).denote=_
        rw [Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,form,swap_cd]
    obtain ⟨M,hm⟩:=select
    exact ⟨⟨C.output H M,A.outerLeft a u v w,A.outerRight a u v w,A.middle a u v w,
      P.output_value H M a u v w hm,live⟩⟩

namespace RedundantOutput
variable {H} (O : RedundantOutput H)
def rates : Fin 4→K:=S.spectrum O.a O.b O.c O.c
theorem spectral : O.graph.network.denote=S.ofSpectrum O.rates := by
  rw [rates,S.reconstruct,O.value]
theorem first : O.rates 0≠0 := by
  intro z
  apply O.determinant
  change O.a+O.b=0 at z
  linear_combination (O.a-O.b)*z
theorem second : O.rates 1≠0 := by
  intro z
  apply O.determinant
  change O.b-O.a=0 at z
  linear_combination -(O.a+O.b)*z
theorem third (live : O.c≠0) : O.rates 2≠0 := by
  change O.c+O.c≠0
  rw [←two_mul]
  exact mul_ne_zero (by norm_num) live
theorem fourth : O.rates 3=0 := by change O.c-O.c=0;ring

theorem support (live : O.c≠0) :
    S.ofSpectrum (GlobalCloseCompletionComplementQ4SupportBasis.support O.rates)=S.row 0 1 ((2:K)⁻¹) ((2:K)⁻¹) :=
  GlobalCloseCompletionComplementQ4SupportBasis.rank_three O.rates O.first O.second (O.third live) O.fourth
end RedundantOutput


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationReduction
end
