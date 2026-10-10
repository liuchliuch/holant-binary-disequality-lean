import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryNoInteractions
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryCaps

/-! The all-unary zero-cap case is selected from the original coefficient
test and saved small factor trees. Interactions touching the capped port
vanish identically; all other interactions are the unchanged original minor. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryNoInteractionCaps
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
namespace N
export GlobalCloseCompletionUnaryNoInteractions (NoInteractions of_tree)
end N
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor double double_comm cap_minor)
end I
namespace P
export GlobalCloseCompletionUnaryPinnedProduct (single cap cap_origin UnaryProduct)
end P
namespace B
export GlobalCloseCompletionUnaryBinaryFactor (pair)
export GlobalCloseCompletionUnaryBinaryCaps (pair_bottom pair_single_first pair_single_second)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

theorem cap_first_pair (f : Signature K n) (i j : Fin n) (different : i≠j) (a b : Bool) :
    P.cap i f (B.pair i j a b)=f (B.pair i j false b) := by
  unfold P.cap
  congr 1
  funext k
  by_cases hi : k=i
  · subst k
    simp [B.pair,Function.update,different]
  · by_cases hj : k=j
    · subst k
      simp [B.pair,Function.update,hi]
    · simp [B.pair,Function.update,hi,hj]

theorem cap_self_minor (f : Signature K n) (i j : Fin n) (different : i≠j) :
    I.minor (P.cap i f) i j=0 := by
  unfold I.minor
  rw [←B.pair_bottom i j,←B.pair_single_first i j different,←B.pair_single_second i j]
  change P.cap i f (B.pair i j false false)*P.cap i f (B.pair i j true true)-
    P.cap i f (B.pair i j true false)*P.cap i f (B.pair i j false true)=0
  rw [cap_first_pair f i j different,cap_first_pair f i j different,
    cap_first_pair f i j different,cap_first_pair f i j different]
  ring

theorem minor_comm (f : Signature K n) (i j : Fin n) : I.minor f i j=I.minor f j i := by
  unfold I.minor
  rw [I.double_comm]
  ring

theorem cap_noInteractions (f : Signature K n) (none : N.NoInteractions f) (k : Fin n) :
    N.NoInteractions (P.cap k f) := by
  intro i j different
  by_cases ik : i=k
  · subst i
    exact cap_self_minor f k j different
  by_cases jk : j=k
  · subst j
    rw [minor_comm]
    exact cap_self_minor f k i different.symm
  rw [I.cap_minor f i j k ik jk]
  exact none i j different

theorem unary_caps (f : Signature K n) (origin : f (fun _=>false)≠0)
    (none : N.NoInteractions f)
    (trees : ∀i,FactorTree (⟨n,P.cap i f⟩ : AnySignature K))
    (small : ∀i,∀g∈(trees i).leaves,g.1≤2) : ∀i,P.UnaryProduct (P.cap i f) := by
  intro i
  exact N.of_tree (trees i) (small i) (by simpa only [P.cap_origin] using origin)
    (cap_noInteractions f none i)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryNoInteractionCaps
end
