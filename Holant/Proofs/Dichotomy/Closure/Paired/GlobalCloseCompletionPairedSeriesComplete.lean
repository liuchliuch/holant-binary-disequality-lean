import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesEqualized
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesAlgebra

/-! Universal paired-quaternary source, with its actual pin0 scalar and the
complete old alphabet retained. All preparation, scalar inverse and binary
interpolation cases are proved internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesComplete
open Holant Holant.Algebraic
namespace P
export GlobalCloseCompletionPairedSeriesCore (row power power_denote)
end P
namespace R
export GlobalCloseCompletionPairedSeriesReceipt (Receipt actual compose)
export GlobalCloseCompletionPairedSeriesRelabel (relabel)
end R
namespace N
export GlobalCloseCompletionPairedSeriesNormalize (E normalized value diagonal nonsingular)
end N
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)
variable (phi : K→+*ℂ) (Q : M.Macro H 4) (B : Matrix Bool Bool K)
variable (hQ : Q.network.denote=P.row B) (det : B.det≠0)
variable (U : M.Macro H 1) (c : K) (hc : c≠0)
variable (h0 : U.network.denote (fun _=>false)=c) (h1 : U.network.denote (fun _=>true)=0)

def produce : R.Receipt H F := by
  classical
  apply Classical.choice
  rcases GlobalCloseCompletionPairedSeriesAlgebra.prepare B det with done|prepare
  · obtain ⟨k,hk,d,hd,he⟩:=done
    apply Nonempty.intro
    exact R.actual H F (P.power Q (k-1)) d hd
      (GlobalCloseCompletionPairedSeriesTrace.power_eq4 Q B hQ k hk d he)
  · obtain ⟨k,hk,ha,hd⟩:=prepare
    let Qk:=P.power Q (k-1)
    have qk : Qk.network.denote=P.row (B^k) := by
      simpa only [Nat.sub_add_cancel hk] using P.power_denote Q B hQ (k-1)
    have dk : (B^k).det≠0 := by rw [Matrix.det_pow];exact pow_ne_zero _ det
    let E:=N.E H F Qk (B^k) qk ha hd
    let NN:=N.normalized H F Qk (B^k) qk ha hd
    let UU:=R.relabel H E.table E.old E.old_literal U
    let BB:=(B^k)*E.inverse
    have hn : NN.network.denote=P.row BB:=N.value H F Qk (B^k) qk ha hd
    have same : BB true true=BB false false :=
      (N.diagonal H F Qk (B^k) qk ha hd true).trans (N.diagonal H F Qk (B^k) qk ha hd false).symm
    have nz : BB false false≠0 := fun hz=>E.nonzero
      ((N.diagonal H F Qk (B^k) qk ha hd false).symm.trans hz)
    let D:=GlobalCloseCompletionPairedSeriesEqualized.produce E.table F NN BB hn same
      (N.nonsingular H F Qk (B^k) qk ha hd dk) phi nz UU c hc h0 h1
    apply Nonempty.intro
    exact R.compose H F E.table E.old E.old_literal E.source D

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesComplete
end
