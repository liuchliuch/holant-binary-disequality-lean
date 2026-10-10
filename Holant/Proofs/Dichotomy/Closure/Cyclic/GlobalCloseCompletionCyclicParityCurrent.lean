import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicSixActual
import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicEvenCurrent

/-! The physical six-port source is a real ordinary Eq4 anchor for the full
retained family. The exact scalar is recovered in the ordinary table's own
coefficient field, and every old row survives the actual saturation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicParityCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace O
export GlobalCloseCompletionStopOrdinarySource (field table)
end O
namespace E
export GlobalCloseCompletionC2OrdinaryPairOutcome (HasEq4)
end E
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
namespace S
export GlobalCloseCompletionCyclicSixActual (even4 current_actual)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
local instance : Algebra ℚ (O.field G P) := (O.field G P).algebra'

theorem retained_anchor (c : OI.K G) (hc : c≠0)
    (retained : (⟨4,c • S.even4⟩ : AnySignature (OI.K G))∈P.family) : E.HasEq4 (O.table G P) := by
  obtain ⟨N,equation⟩ := GlobalCloseCompletionC2QuaternaryCurrent.source_row G P (c • S.even4) retained
  let d : AlgebraicComplex := (ClosureSourceRows.embedding G) c
  have native : RingHomRealization.mapSignature (ClosureSourceRows.embedding G) (c • S.even4)=T.normal d d d d := by
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp [RingHomRealization.mapSignature,S.even4,T.normal,
        Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3,d]
  have form : RingHomRealization.mapSignature (O.field G P).subtype N.network.denote=
      (2*d) • Holant.EightVertex.ProductAnchor.equalityFour := by
    rw [equation,native,GlobalCloseCompletionC2KNormal.sourceK_normal]
    have values : (d+d+d+d)/2=2*d ∧ (-d-d+d+d)/2=0 ∧ (-d+d-d+d)/2=0 ∧ (-d+d+d-d)/2=0 := by
      constructor
      · ring
      constructor
      · ring
      constructor <;> ring
    rw [values.1,values.2.1,values.2.2.1,values.2.2.2]
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
        Holant.EightVertex.ProductAnchor.equalityFour,Fin.forall_fin_succ,h0,h1,h2,h3]
  let e : O.field G P := N.network.denote (fun _=>false)
  have pivot : (O.field G P).subtype e=2*d := by
    have h := congrFun form (fun _=>false)
    simpa [RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.equalityFour] using h
  have de : d≠0 := (map_ne_zero (ClosureSourceRows.embedding G)).mpr hc
  refine ⟨N,e,?_,?_⟩
  · intro zero
    have h := pivot
    rw [zero,map_zero] at h
    exact (mul_ne_zero (by norm_num : (2:AlgebraicComplex)≠0) de) h.symm
  · funext x
    apply (O.field G P).subtype.injective
    have h := congrFun form x
    change (O.field G P).subtype (N.network.denote x)=
      (O.field G P).subtype (e*Holant.EightVertex.ProductAnchor.equalityFour (K:=O.field G P) x)
    rw [map_mul,pivot]
    have eq4map : (O.field G P).subtype (Holant.EightVertex.ProductAnchor.equalityFour (K:=O.field G P) x)=
        Holant.EightVertex.ProductAnchor.equalityFour (K:=AlgebraicComplex) x := by
      simp [Holant.EightVertex.ProductAnchor.equalityFour]
    rw [eq4map]
    exact h

theorem actual_anchor (c : OI.K G) (hc : c≠0)
    (actual : Gadget.Realizes P.family .disequality (c • S.even4)) :
    ∃Q : Palette G,P.family⊆Q.family ∧ E.HasEq4 (O.table G Q) := by
  have nonzero : (c • S.even4 : Signature (OI.K G) 4)≠0 := by
    intro zero
    have h := congrFun zero (fun _=>false)
    exact hc (by simpa [S.even4] using h)
  let Q := ProgrammeSaturation.palette G P (⟨4,c • S.even4⟩ : AnySignature (OI.K G)) nonzero (by change 0<4;decide) actual
  exact ⟨Q,ProgrammeSaturation.retains_old G P _ _ _ _,retained_anchor G Q c hc
    (ProgrammeSaturation.retains_output G P _ _ _ _)⟩

theorem six_anchor (torsion : ResidualTorsion P.family)
    (cyclic : IsCyclic (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
    (f : Signature (OI.K G) 6) (retained : (⟨6,f⟩ : AnySignature (OI.K G))∈P.family)
    (prime : Prime (⟨6,f⟩ : AnySignature (OI.K G)))
    (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    ∃Q : Palette G,P.family⊆Q.family ∧ E.HasEq4 (O.table G Q) := by
  obtain ⟨c,hc,actual⟩ := S.current_actual P.family torsion P.equality
    (ClosurePhysicalBridge.complexEmbedding G) cyclic f retained prime stable
  exact actual_anchor G P c hc actual


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicParityCurrent
end
