import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryNativeAccess
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryAttach
import Holant.Proofs.Hardness.BinaryIsingCountingSource

/-! A real ordinary symmetric pair and a retained literal X row implement
the genuine native Ising counting source. The two opposite-port flips are
actual X vertices, and native query edges are physically subdivided. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryPairIsing
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open OrdinaryNegativeCubicGadgets
namespace A
export GlobalCloseCompletionKleinOrdinaryAttach (attach attach_denote labels exact ordinary)
end A
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (pair symmetric)
end P
namespace M
export GeneralEOAffinePlaneChain (binary bitIndex)
end M
namespace O
export Holant.Certificates.EqualityQuaternary.Klein.Orbit (site)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {degree s : ℕ} {arity : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (arity i.val))
variable (N : Macro H 4) (j : Fin s)
variable (literal : (⟨arity j.val,H j⟩ : AnySignature K)=⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩)

def attachMacro (D : Macro H 4) (i : Fin 4) : Macro H 4 where
  network := A.attach D.network i X
  labels := A.labels H D.network D.labels j X literal i
  exact := A.exact H D.network D.labels j X literal i D.exact
  edges := A.ordinary D.network i X D.edges

def graphMacro : Macro H 4 := attachMacro H j literal (attachMacro H j literal N 1) 3

theorem graph_denote (a d : K) (form : N.network.denote=P.pair (M.binary (P.symmetric a d))) :
    (graphMacro H N j literal).network.denote=EOBinaryPlaneCore.lift (BinaryIsingWeights.table a d) := by
  change (A.attach (A.attach N.network 1 X) 3 X).denote=_
  rw [A.attach_denote,A.attach_denote,form]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [O.site,X,Signature.disequality,Function.update,P.pair,M.binary,M.bitIndex,P.symmetric,
      EOBinaryPlaneCore.lift,BinaryIsingWeights.table,BinaryIsingWeights.interaction,h0,h1,h2,h3]

def xMacro : Macro H 2 := Macro.row j (fun x=>Signature.disequality (x 0) (x 1)) literal

variable (a d : K) (form : N.network.denote=P.pair (M.binary (P.symmetric a d)))
variable (ha : a≠0) (hd : d≠0) (infinite : ∀n : ℕ,0<n→(d/a)^n≠1)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding count
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) :=
  Programme.compose
    (BinaryIsingCountingSource.source F (graphMacro H N j literal).network.denote a d
      (graph_denote H N j literal a d form) ha hd (fun n hn=>infinite (2*n) (by omega)) w)
    (GlobalCloseCompletionC2OrdinaryNativeAccess.source F H (graphMacro H N j literal) (xMacro H j literal)
      (Macro.row_denote j _ literal))

include literal form ha hd infinite in
theorem countingHard : PaperControlledHardness.Hard
    (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) := by
  intro α ea count w
  exact ⟨(source F H N j literal a d form ha hd infinite w)⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryPairIsing
end
