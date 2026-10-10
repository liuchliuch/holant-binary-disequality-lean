import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockAffineXOriginal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonclosedSupportEvenOriginal

/-! Arbitrary two-even-resource endpoint with no support-closure hypotheses.
A nonclosed trace produces an actual three-supported binary. If both supports
are closed, their shifted tensor supplies the hard binary. Both branches use
only the original table's literal Eq4, pins, and X and retain original fields. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockResourcesXOriginal
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export GlobalCloseCompletionEq4FullSource (count arity table)
export GlobalCloseCompletionEq4CSPSource (field)
end S
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe)
export OrdinaryNegativeMixedBlockSource (trace)
end D
namespace C
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
end C
namespace A
export OrdinaryNegativeMixedBlockAffineXOriginal (source)
end A
namespace N
export OrdinaryNegativeNonclosedSupportEvenOriginal (source)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s m n k l : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (o : GlobalCloseCompletionEq4Graph.Output G P)
local instance : Algebra ℚ (S.field G P o) := (S.field G P o).algebra'
variable (first : D.Recipe (u:=1) (s:=S.count G P)
  (a:=fun _=>m+k) (b:=S.arity G P o))
variable (second : D.Recipe (u:=1) (s:=S.count G P)
  (a:=fun _=>n+l) (b:=S.arity G P o))
variable (ha : ¬Affine (fun x=>(D.trace (S.table G P o) k first 0 x : AlgebraicComplex)))
variable (hp : ¬Product (fun x=>(D.trace (S.table G P o) l second 0 x : AlgebraicComplex)))
variable (hfirst : D.EvenRecipe first) (hsecond : D.EvenRecipe second)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) := by
  classical
  by_cases hf : C.Closed (fun x=>(D.trace (S.table G P o) k first 0 x : AlgebraicComplex))
  · by_cases hg : C.Closed (fun x=>(D.trace (S.table G P o) l second 0 x : AlgebraicComplex))
    · exact A.source G P o first second hf hg ha hp hfirst hsecond w
    · exact N.source G P o second hg hsecond w
  · exact N.source G P o first hf hfirst w

include ha hp hfirst hsecond in
theorem countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) := by
  intro α ea count w
  exact ⟨(source G P o first second ha hp hfirst hsecond w).controlled.reduction⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockResourcesXOriginal
end
