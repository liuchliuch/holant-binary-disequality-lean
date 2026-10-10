import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddPinGraph
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralGraphAnti
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalMixedProjectionCore
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! The noncanonical ternary parity coset gives an actual full anti by
pinning its first exposed port to zero. No coordinate flip is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralOddTernaryAnti
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export OrdinaryNegativeXUniversalResource (OddResource)
end D
namespace C
export NoXReciprocalMixedProjectionCore (logical)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 32768
set_option Elab.async false
section Semantics
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (row : D.OddResource (s:=s) b 3)
variable (sign : Fin 3→Bool)
variable (support : ∀z,row.ambient H z≠0 ↔ C.logical sign z 2=(C.logical sign z 0 ^^ C.logical sign z 1))
variable (noncanonical : sign 2≠(sign 0 ^^ sign 1))
include support noncanonical in
theorem binary_support (x : Fin 2→Bool) : row.signature H (Fin.cons false x)≠0 ↔ x 0≠x 1 := by
  have h:=support (Fin.cons false x)
  have hc : row.signature H (Fin.cons false x)≠0 ↔ row.ambient H (Fin.cons false x)≠0 := by
    exact Subtype.coe_ne_coe.symm
  rw [hc,h]
  change (sign 2 ^^ x 1)=((sign 0 ^^ false) ^^ (sign 1 ^^ x 0)) ↔ x 0≠x 1
  cases h0 : sign 0 <;> cases h1 : sign 1 <;> cases h2 : sign 2 <;>
    cases hx : x 0 <;> cases hy : x 1 <;> simp_all

include support noncanonical in
theorem left_nonzero : row.signature H ![false,false,true]≠0 := by
  exact (binary_support H row sign support noncanonical ![false,true]).mpr (by decide)

include support noncanonical in
theorem right_nonzero : row.signature H ![false,true,false]≠0 := by
  exact (binary_support H row sign support noncanonical ![true,false]).mpr (by decide)

include support noncanonical in
theorem anti : (fun x=>row.signature H (Fin.cons false x))=
    NoXWeightedAntiSigned.anti (row.signature H ![false,false,true]) (row.signature H ![false,true,false]) := by
  funext x
  have hx : x=![x 0,x 1] := by funext i;fin_cases i <;> rfl
  rw [hx]
  cases h0 : x 0 <;> cases h1 : x 1
  · change row.signature H (Fin.cons false ![false,false])=0
    have h:= (binary_support H row sign support noncanonical ![false,false]).not
    simpa only [not_ne_iff] using h.mpr (by decide)
  · rfl
  · rfl
  · change row.signature H (Fin.cons false ![true,true])=0
    have h:= (binary_support H row sign support noncanonical ![true,true]).not
    simpa only [not_ne_iff] using h.mpr (by decide)

end Semantics

section Terminal
variable {r : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (row : D.OddResource (s:=src.size) src.b 3) (sign : Fin 3→Bool)
variable (support : ∀z,row.ambient src.H z≠0 ↔ C.logical sign z 2=(C.logical sign z 0 ^^ C.logical sign z 1))
variable (noncanonical : sign 2≠(sign 0 ^^ sign 1))
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
include support noncanonical negative in
theorem countingHard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  let graph:=NoXGeneralOddPinGraph.output src.H src.e (src.p false) (src.p true)
    src.he (src.hp false) (src.hp true) row false
  apply NoIOrdinaryRaw.NoXGeneralGraphAnti.countingHard G src graph
    (row.signature src.H ![false,false,true]) (row.signature src.H ![false,true,false])
    (left_nonzero src.H row sign support noncanonical) (right_nonzero src.H row sign support noncanonical)
    _ negative
  calc graph.network.denote=(fun x=>row.signature src.H (Fin.cons false x)) :=
      funext (NoXGeneralOddPinGraph.value src.H src.e (src.p false) (src.p true)
        src.he (src.hp false) (src.hp true) row false)
    _= _ := anti src.H row sign support noncanonical
end Terminal

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralOddTernaryAnti
end
