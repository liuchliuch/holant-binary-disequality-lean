import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBitFlipPins
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPortOrder

/-! An actual prime graph with one supported-word mask. Reordering moves the
same physical graph and mask together; the analytic zero pivot and anchored
minor identities remain exact. No bit flip is an available gate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinNormalized
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.FinitePGL2.Stabilization
namespace F
export GlobalCloseCompletionUnaryBitFlip (value word value_twice prime word_zero)
export GlobalCloseCompletionUnaryBitFlipPins (reindex_flip)
end F
namespace O
export GlobalCloseCompletionUnaryPortOrder (output denote prime minor_reindex)
end O
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] {r n : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (a i.val))

structure Data (n : ℕ) where
  actual : NoXOrdinaryGraphAdjoin.Output H n
  mask : Fin n→Bool
  pivot : actual.network.denote mask≠0
  prime : Prime (⟨n,actual.network.denote⟩ : AnySignature K)

variable {H}

def Data.value (D : Data H n) : Signature K n := F.value D.mask D.actual.network.denote

theorem Data.origin (D : Data H n) : D.value (fun _=>false)≠0 := by
  simpa only [Data.value,F.value,F.word_zero] using D.pivot

theorem Data.value_prime (D : Data H n) : Prime (⟨n,D.value⟩ : AnySignature K) :=
  F.prime D.mask D.actual.network.denote D.prime

def Data.reindex (D : Data H n) (e : Equiv.Perm (Fin n)) : Data H n where
  actual:=O.output H D.actual e.symm
  mask:=fun i=>D.mask (e i)
  pivot:=by
    rw [O.denote]
    simpa only [Tensor.reindex,Equiv.apply_symm_apply] using D.pivot
  prime:=O.prime H D.actual e.symm D.prime

theorem Data.reindex_value (D : Data H n) (e : Equiv.Perm (Fin n)) :
    (D.reindex e).value=Tensor.reindex e.symm D.value := by
  change F.value (fun i=>D.mask (e i)) (O.output H D.actual e.symm).network.denote=_
  rw [O.denote]
  simpa only [Equiv.symm_symm,Data.value] using (F.reindex_flip e.symm D.mask D.actual.network.denote).symm

theorem Data.reindex_minor (D : Data H n) (e : Equiv.Perm (Fin n)) (i j : Fin n) :
    I.minor (D.reindex e).value i j=I.minor D.value (e i) (e j) := by
  rw [Data.reindex_value,O.minor_reindex]
  rfl

variable (H)

def ofPrime (N : NoXOrdinaryGraphAdjoin.Output H n) (prime : Prime (⟨n,N.network.denote⟩ : AnySignature K)) : Data H n := by
  classical
  have e : ∃x,N.network.denote x≠0 := by
    by_contra none
    push Not at none
    exact prime.1 (funext none)
  exact ⟨N,Classical.choose e,Classical.choose_spec e,prime⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinNormalized
end
