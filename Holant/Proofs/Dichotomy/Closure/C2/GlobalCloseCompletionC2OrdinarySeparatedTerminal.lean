import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinarySeparated
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryLift

/-! Unconditional whole-family tractability-or-hardness for the ordinary
separating C2 q4 branch with an endpoint and two live mixed coefficients.
All old signatures survive both the Eq4/pin and scalar-X installations. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinarySeparatedTerminal
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export GlobalCloseCompletionC2OrdinarySeparated (Input data family old_included)
end S
namespace L
export GlobalCloseCompletionC2OrdinaryLift (Input classified)
end L
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
variable (D : S.Input G) (ha : D.a≠0) (hc : D.c≠0) (hd : D.d≠0)
local instance : Algebra ℚ D.K := D.K.algebra'

def input : L.Input G (S.data G D) where
  network := D.graph.map D.K.subtype
  uses := by
    intro v
    apply S.old_included G D
    exact ⟨D.labels.vertex v,congrArg (RingHomRealization.mapAny D.K.subtype) (D.exact v)⟩
  ordinary := by
    intro e
    funext b c
    change D.K.subtype (D.graph.edge e b c)=Signature.equality b c
    rw [D.ordinary]
    cases b <;> cases c <;> rfl
  a := (D.a : AlgebraicComplex)
  b := (D.b0 : AlgebraicComplex)
  c := (D.c : AlgebraicComplex)
  d := (D.d : AlgebraicComplex)
  aNonzero := by intro zero; exact ha (Subtype.ext zero)
  cNonzero := by intro zero; exact hc (Subtype.ext zero)
  dNonzero := by intro zero; exact hd (Subtype.ext zero)
  form := by
    funext x
    rw [Network.denote_map,D.form]
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3] <;> rfl

include ha hc hd in
theorem classified : Tract (S.family G D) ∨
    Holant.LocalDrafts.CountingHardness.WitnessCountingHard
      (OriginalForestSource.inputEncoding (s:=s) (arity:=arity)) (OriginalForestSource.presentation G).encoding
      (OriginalForestSource.value G) := by
  rcases L.classified G (S.data G D) (input G D ha hc hd) with tract|hard
  · exact Or.inl (tract.mono_family (S.old_included G D))
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinarySeparatedTerminal
end
