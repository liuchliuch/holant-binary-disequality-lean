import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationPaired
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationReduction
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Source

/-! A paired-square row is normalized only by actual ordered-port
permutations. Its original scalar stays in the spectrum. Real signs give the
literal dense equal-products support row via the complete native compiler. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4PairedSource
open Holant Holant.Algebraic
namespace S
export GlobalCloseCompletionComplementQ4Series (row spectrum ofSpectrum reconstruct)
end S
namespace A
export GlobalCloseCompletionComplementQ4ClassificationAlgebra (Paired)
export GlobalCloseCompletionComplementQ4ClassificationScale (normalized row_smul)
export GlobalCloseCompletionComplementQ4ClassificationPaired (signed support_scale real_support)
end A
namespace R
export GlobalCloseCompletionComplementQ4ClassificationReduction (swap_bd swap_cd swap_bc)
end R
namespace T
export GlobalCloseCompletionComplementQ4Templates (reindex)
end T
namespace E
export GlobalCloseCompletionComplementQ4Source (Extension support)
end E
namespace U
export GlobalCloseCompletionComplementQ4SupportBasis (support)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {size degree : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin size)→Signature K (arity i.val))

structure Normal (a : K) where
  graph : NativeAntiTargetSource.Output H 4
  r : K
  s : K
  t : K
  fourth : r^4=1
  sign : s^2=1
  live : t≠0
  value : graph.network.denote=a • S.row 1 r t (s*r*t)

variable (N : NativeAntiTargetSource.Output H 4) (a b c d : K)
variable (form : N.network.denote=S.row a b c d) (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0)
variable (paired : A.Paired (b/a) (c/a) (d/a))

include form ha hb hc hd paired in
theorem exists_normal : Nonempty (Normal H a) := by
  rcases paired with ⟨fourth,squares⟩|⟨fourth,squares⟩|⟨fourth,squares⟩
  · obtain ⟨sign,hs,eqn⟩:=A.signed (b/a) (d/a) (c/a) squares
    refine ⟨⟨T.reindex H N (Equiv.swap 2 3),b/a,sign,d/a,fourth,hs,div_ne_zero hd ha,?_⟩⟩
    change (Holant.Complexity.BinaryInterpolation.Chains.reindex N.network _).denote=_
    rw [Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,form,R.swap_cd,A.normalized a b d c ha,eqn]
  · obtain ⟨sign,hs,eqn⟩:=A.signed (c/a) (d/a) (b/a) squares
    refine ⟨⟨T.reindex H (T.reindex H N (Equiv.swap 1 2)) (Equiv.swap 2 3),
      c/a,sign,d/a,fourth,hs,div_ne_zero hd ha,?_⟩⟩
    change (Holant.Complexity.BinaryInterpolation.Chains.reindex
      (Holant.Complexity.BinaryInterpolation.Chains.reindex N.network _) _).denote=_
    rw [Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,
      Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,form,R.swap_bc,R.swap_cd,A.normalized a c d b ha,eqn]
  · obtain ⟨sign,hs,eqn⟩:=A.signed (d/a) (c/a) (b/a) squares
    refine ⟨⟨T.reindex H N (Equiv.swap 1 3),d/a,sign,c/a,fourth,hs,div_ne_zero hc ha,?_⟩⟩
    change (Holant.Complexity.BinaryInterpolation.Chains.reindex N.network _).denote=_
    rw [Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,form,R.swap_bd,A.normalized a d c b ha,eqn]

def produce : Normal H a:=Classical.choice (exists_normal H N a b c d form ha hb hc hd paired)

theorem spectrum_scale (z : K) (v : Fin 4→K) :
    S.ofSpectrum (fun i=>z*v i)=z • S.ofSpectrum v := by
  rw [S.ofSpectrum,S.ofSpectrum,A.row_smul]
  congr 1 <;> ring

namespace Normal
variable {H a} (P : Normal H a)
def rates : Fin 4→K:=fun i=>a*S.spectrum 1 P.r P.t (P.s*P.r*P.t) i
theorem spectral : P.graph.network.denote=S.ofSpectrum P.rates := by
  change P.graph.network.denote=S.ofSpectrum (fun i=>a*S.spectrum 1 P.r P.t (P.s*P.r*P.t) i)
  rw [spectrum_scale,S.reconstruct,P.value]

def real (F : FixedField K degree) (ha : a≠0) (hr : P.r^2=1) :
    E.Extension H F (S.row (P.r/2) (1/2) ((P.s*P.r)/2) (1/2)) := by
  have value : S.ofSpectrum (U.support P.rates)=S.row (P.r/2) (1/2) ((P.s*P.r)/2) (1/2) := by
    change S.ofSpectrum (U.support (fun i=>a*S.spectrum 1 P.r P.t (P.s*P.r*P.t) i))=_
    rw [A.support_scale a ha,A.real_support P.r P.s P.t hr P.sign P.live]
  rw [←value]
  exact E.support H F P.graph P.rates P.spectral
end Normal


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4PairedSource
end
