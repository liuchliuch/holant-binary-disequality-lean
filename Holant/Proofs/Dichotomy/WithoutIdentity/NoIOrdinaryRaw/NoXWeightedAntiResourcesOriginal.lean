import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiAffineSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiNonclosedSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Arbitrary two actual even resources, one non-Affine and one non-Product,
produce a genuine unchanged-original-G counting source. A full weighted
antidiagonal suffices; neither a literal-X label nor support closure is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export NoIOrdinaryRaw.GenericOrdinarySource (count arity table field presentation eq4Label pinLabel
  eq4_literal pin_literal ordinarySource)
end S
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe)
export OrdinaryNegativeMixedBlockSource (trace)
end D
namespace C
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
end C
namespace A
export NoXWeightedAntiAffineSource (source)
end A
namespace N
export NoXWeightedAntiNonclosedSource (source)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s m n k l : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ (S.field G src) := (S.field G src).algebra'
variable (antiLabel : Fin (S.count G src)) (v w : S.field G src)
variable (hv : v≠0) (hw : w≠0)
variable (ha_lit : (⟨S.arity G src antiLabel.val,S.table G src antiLabel⟩ : AnySignature (S.field G src))=
  ⟨2,NoXWeightedAntiSigned.anti v w⟩)
variable (first : D.Recipe (u:=1) (s:=S.count G src)
  (a:=fun _=>m+k) (b:=S.arity G src))
variable (second : D.Recipe (u:=1) (s:=S.count G src)
  (a:=fun _=>n+l) (b:=S.arity G src))
variable (ha : ¬Affine (fun x=>(D.trace (S.table G src) k first 0 x : AlgebraicComplex)))
variable (hp : ¬Product (fun x=>(D.trace (S.table G src) l second 0 x : AlgebraicComplex)))
variable (hfirst : D.EvenRecipe first) (hsecond : D.EvenRecipe second)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (witness : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    G.inputEncoding
    G.outputEncoding count G.value := by
  classical
  apply PhysicalProgramme.ofControlled
  apply Programme.compose (g:=((StableHigherCurrentEvenCSPSource.tables
    (S.presentation G src) (S.table G src)).evaluate (S.presentation G src))) ?_ (S.ordinarySource G src)
  by_cases hf : C.Closed (fun x=>(D.trace (S.table G src) k first 0 x : AlgebraicComplex))
  · by_cases hg : C.Closed (fun x=>(D.trace (S.table G src) l second 0 x : AlgebraicComplex))
    · exact A.source (S.field G src) (S.presentation G src) (S.table G src)
        first second hf hg ha hp antiLabel v w hv hw ha_lit
        (S.eq4Label G src) (S.pinLabel G src false) (S.pinLabel G src true)
        (S.pin_literal G src false) (S.eq4_literal G src) (S.pin_literal G src true)
        hfirst hsecond witness
    · exact N.source (S.field G src) (S.presentation G src) (S.table G src)
        second hg antiLabel v w hv hw ha_lit
        (S.eq4Label G src) (S.pinLabel G src false) (S.pinLabel G src true)
        (S.pin_literal G src false) (S.eq4_literal G src) (S.pin_literal G src true)
        hsecond witness
  · exact N.source (S.field G src) (S.presentation G src) (S.table G src)
      first hf antiLabel v w hv hw ha_lit
      (S.eq4Label G src) (S.pinLabel G src false) (S.pinLabel G src true)
      (S.pin_literal G src false) (S.eq4_literal G src) (S.pin_literal G src true)
      hfirst witness

abbrev Hard : Prop := NoIOrdinaryRaw.Target.Hard G

include hv hw ha_lit ha hp hfirst hsecond in
theorem countingHard : Hard G := by
  intro α ea count witness
  exact ⟨(source G src antiLabel v w hv hw ha_lit first second ha hp hfirst hsecond witness).controlled⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
end
