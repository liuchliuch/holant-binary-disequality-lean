import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffinePhaseSource

/-! An arbitrary actual real-line nonaffine pure-parity row gives a genuine
quaternary or a strict complete-factor restart, using the actual H6 and RM8
resources. Norm, support and phase alternatives are all derived internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineRealDescent
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open GlobalCloseCompletionKleinHigherNonaffinePhaseFaceSource
namespace U
export GlobalCloseCompletionKleinHigherNonaffinePhaseUnequal (source scale_unequal not_uniform)
end U
namespace A
export GlobalCloseCompletionKleinH6GateAlgebra (action action_scale map_action)
end A
namespace H
export GlobalCloseCompletionKleinH6GateActual (actual mapped scale_affine_iff)
end H
namespace N
export GlobalCloseCompletionKleinHigherNonaffineNormSource (UniformSquares uniform_or_continue complexEmbedding)
end N
namespace L
export GlobalCloseCompletionRetainedPredicateLeaf (Minimum)
end L
namespace R
export GlobalCloseCompletionRetainedPredicateRestart (finalPalette)
end R
namespace B
export GlobalCloseCompletionKleinAffineLeaf (IsAffine)
end B
namespace RH
export RingHomRealization (mapSignature)
end RH
namespace RM
export GlobalCloseCompletionC2RMActual (rm)
end RM
namespace F
export GlobalCloseCompletionKleinHigherNonaffineFullParity (normal)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 16384
set_option Elab.async false

variable {s : ℕ} {ar : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (ar i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem source {n : ℕ}
    (cH : OI.K G) (h6Nonzero : cH≠0)
    (h6Actual : Gadget.Realizes P.family .disequality (cH • GlobalCloseCompletionKleinH6RMBell.core))
    (cRM : OI.K G) (rmNonzero : cRM≠0)
    (rmActual : Gadget.Realizes P.family .disequality (cRM • RM.rm))
    (old : L.Minimum G P (B.IsAffine G))
    (f : Signature (OI.K G) (n+3)) (actual : Gadget.Realizes P.family .disequality f)
    (bad : ¬Affine (RH.mapSignature (ClosureSourceRows.embedding G) f))
    (bound : n+3≤old.signature.1)
    (pure : GlobalCloseCompletionProductAncestorParity.PureParity f)
    (r : Signature ℝ (n+3)) (c : ℂ) (hc : c≠0)
    (normal : RH.mapSignature (N.complexEmbedding G) f=fun x=>c*(r x:ℂ)) :
    Nonempty (GlobalCloseCompletionKleinQuaternaryRestart.D.Output G P) ∨
      ∃q : Signature (OI.K G) (n+3),∃nonzero : q≠0,
        ∃actualQ : Gadget.Realizes P.family .disequality q,
        ∃new : L.Minimum G (R.finalPalette G P ⟨n+3,q⟩ nonzero (by change 0<n+3;omega) actualQ) (B.IsAffine G),
          new.signature.1<old.signature.1 := by
  rcases N.uniform_or_continue G P torsion cardinal noncyclic standard (n:=n+1) (by omega)
    cRM rmNonzero rmActual old f actual bad bound r c hc normal with uniform|continuation
  · exact GlobalCloseCompletionKleinHigherNonaffinePhaseSource.source G P torsion cardinal noncyclic standard
      cH h6Nonzero h6Actual cRM rmNonzero rmActual old f actual bad bound pure uniform r c hc normal
  · exact continuation

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineRealDescent
end
