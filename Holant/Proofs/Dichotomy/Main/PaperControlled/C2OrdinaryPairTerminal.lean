import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryPairOutcome
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryAnchorX

/-! A nonsingular actual symmetric ordinary pair, retained X, and the genuine
whole-source reduction close the entire old ordinary dictionary. Finite
periods supply Eq4 and pins; infinite periods use the actual Ising programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryPairTerminal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open OrdinaryNegativeCubicGadgets
namespace P
export PaperControlled.C2OrdinaryPairOutcome (HasEq4 eq4_or_hard_to)
end P
namespace S
export GlobalCloseCompletionKleinOrdinaryPair (pair symmetric)
end S
namespace M
export GeneralEOAffinePlaneChain (binary)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))

structure Input : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  F : letI : Algebra ℚ K := K.algebra'; FixedField K degree
  count : ℕ
  b : ℕ→ℕ
  H : (i : Fin count)→Signature K (b i.val)
  graph : Macro H 4
  xLabel : Fin count
  xLiteral : (⟨b xLabel.val,H xLabel⟩ : AnySignature K)=⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩
  a : K
  d : K
  form : graph.network.denote=S.pair (M.binary (S.symmetric a d))
  determinant : a^2≠d^2
  toOriginal : letI : Algebra ℚ K := K.algebra'; LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=arity)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G)

variable (D : Input G)
local instance : Algebra ℚ D.K := D.K.algebra'

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin D.count=>
  RingHomRealization.mapAny D.K.subtype (⟨D.b i.val,D.H i⟩ : AnySignature D.K)

def anchor (N : Macro D.H 4) (c : D.K) (nonzero : c≠0)
    (form : N.network.denote=c • Holant.EightVertex.ProductAnchor.equalityFour) :
    GlobalCloseCompletionOrdinaryAnchorInput.Input G where
  K := D.K
  degree := D.degree
  F := D.F
  count := D.count
  b := D.b
  H := D.H
  graph := N.network
  labels := N.labels
  exact := N.exact
  ordinary := N.edges
  scalar := c
  nonzero := nonzero
  denote := form
  toOriginal := D.toOriginal

theorem classified : Tract (family G D) ∨
    PaperControlledHardness.Hard
      (OriginalForestSource.inputEncoding (s:=s) (arity:=arity)) (OriginalForestSource.presentation G).encoding
      (OriginalForestSource.value G) := by
  let phi : D.K→+*ℂ := (algebraicClosure ℚ ℂ).subtype.comp D.K.subtype
  rcases P.eq4_or_hard_to D.F D.H phi D.graph D.xLabel D.xLiteral D.a D.d D.form D.determinant
    (OriginalForestSource.inputEncoding (s:=s) (arity:=arity)) (OriginalForestSource.presentation G).encoding
    (OriginalForestSource.value G) D.toOriginal with ⟨N,c,hc,form⟩|hard
  · exact PaperControlled.C2OrdinaryAnchorX.classified G (anchor G D N c hc form) D.xLabel D.xLiteral
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryPairTerminal
end
