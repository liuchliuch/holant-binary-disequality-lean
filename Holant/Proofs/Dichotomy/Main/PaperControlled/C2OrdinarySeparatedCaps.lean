import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinarySeparatedTerminal

/-! A separating graph supplies Eq4 while any retained same-dictionary q4
with three appropriate live entries supplies the real scalar-X cap path.
The two graphs may have different original-port permutations. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinarySeparatedCaps
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace S
export GlobalCloseCompletionC2OrdinarySeparated (Input data family old_included)
end S
namespace L
export PaperControlled.C2OrdinaryLift (Input classified)
end L
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val)) (D : S.Input G)
local instance : Algebra ℚ D.K := D.K.algebra'
variable (N : Macro D.H 4) (a b c d : D.K) (ha : a≠0) (hc : c≠0) (hd : d≠0)
variable (form : N.network.denote=T.normal a b c d)

def input : L.Input G (S.data G D) where
  network := N.network.map D.K.subtype
  uses := by
    intro v
    apply S.old_included G D
    exact ⟨N.labels.vertex v,congrArg (RingHomRealization.mapAny D.K.subtype) (N.exact v)⟩
  ordinary := by
    intro e
    funext u v
    change D.K.subtype (N.network.edge e u v)=Signature.equality u v
    rw [N.edges]
    cases u <;> cases v <;> rfl
  a := (a : AlgebraicComplex)
  b := (b : AlgebraicComplex)
  c := (c : AlgebraicComplex)
  d := (d : AlgebraicComplex)
  aNonzero := by intro zero; exact ha (Subtype.ext zero)
  cNonzero := by intro zero; exact hc (Subtype.ext zero)
  dNonzero := by intro zero; exact hd (Subtype.ext zero)
  form := by
    funext x
    rw [Network.denote_map,form]
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3] <;> rfl

include N a b c d ha hc hd form in
theorem classified : Tract (S.family G D) ∨
    PaperControlledHardness.Original G := by
  rcases L.classified G (S.data G D) (input G D N a b c d ha hc hd form) with tract|hard
  · exact Or.inl (tract.mono_family (S.old_included G D))
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinarySeparatedCaps
end
