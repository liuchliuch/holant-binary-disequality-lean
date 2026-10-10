import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesSelectedCap
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesReceipt
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesTrace

/-! An arbitrary nonsingular equal-diagonal paired row and an actual pin0
produce a scalar Eq4 source, internally selecting every finite/infinite case. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesEqualized
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.Certificates.MatchingContractionClosure
namespace P
export GlobalCloseCompletionPairedSeriesCore (row power power_denote)
end P
namespace R
export GlobalCloseCompletionPairedSeriesReceipt (Receipt actual)
end R
namespace T
export GlobalCloseCompletionPairedSeriesTarget (table arity old old_literal label literal source)
end T
namespace C
export GlobalCloseCompletionPairedSeriesCases (choose diagonal_scalar fourth_scalar)
export GlobalCloseCompletionPairedSeriesChoice (Infinite)
end C
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (row row_denote)
end M
namespace L
export GlobalCloseCompletionPairedSeriesRelabel (relabel correct correct_value)
end L
namespace Tr
export GlobalCloseCompletionPairedSeriesTrace (square power_eq4)
end Tr
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)
variable (N : M.Macro H 4) (B : Matrix Bool Bool K) (hN : N.network.denote=P.row B)
variable (same : B true true=B false false) (det : B.det≠0)

def nonperiodic (Q : M.Macro H 2) (u v : K) (hu : u≠0) (hv : v≠0)
    (infinite : C.Infinite (v/u))
    (form : Q.network.denote=binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal u v)) : R.Receipt H F := by
  let J:=T.table H F Q u v (-1)
  let NN:=L.relabel H J T.old (T.old_literal H F Q u v (-1)) N
  let ZZ : M.Macro J 2:=M.row T.label
    (binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal 1 (-1))) (T.literal H F Q u v (-1))
  let corrected:=L.correct J NN ZZ
  have hc : corrected.network.denote=P.row (B*OrdinaryTargetInterpolationDiagonal.diagonal 1 (-1)) :=
    L.correct_value J NN ZZ B 1 (-1) hN (M.row_denote _ _ _)
  exact {
    count:=s+1
    b:=T.arity H Q
    table:=J
    old:=T.old
    old_literal:=T.old_literal H F Q u v (-1)
    graph:=P.power corrected 1
    scalar:=B.det
    nonzero:=det
    value:=by simpa using Tr.power_eq4 corrected _ hc 2 (by decide) B.det (Tr.square B same)
    source:=T.source H F Q u v (-1) hu hv infinite form }

variable (phi : K→+*ℂ) (nonzero : B false false≠0)
variable (U : M.Macro H 1) (c : K) (hc : c≠0)
variable (h0 : U.network.denote (fun _=>false)=c) (h1 : U.network.denote (fun _=>true)=0)
def produce : R.Receipt H F := by
  classical
  apply Classical.choice
  rcases C.choose phi B nonzero same det with diagonal|anti|cap
  · apply Nonempty.intro
    exact R.actual H F N (B false false) nonzero (by
      rw [hN,C.diagonal_scalar B same diagonal.1 diagonal.2,
        GlobalCloseCompletionPairedSeriesCore.smul,GlobalCloseCompletionPairedSeriesCore.identity]
      simp)
  · obtain ⟨power,hpower⟩:=C.fourth_scalar B det anti.1 anti.2
    apply Nonempty.intro
    exact R.actual H F (P.power N 3) _ hpower
      (Tr.power_eq4 N B hN 4 (by decide) _ power)
  · obtain ⟨Q,u,v,hu,hv,hi,hQ⟩:=GlobalCloseCompletionPairedSeriesSelectedCap.produce U N c hc h0 h1 B hN cap
    apply Nonempty.intro
    exact nonperiodic H F N B hN same det Q u v hu hv hi hQ

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesEqualized
end
