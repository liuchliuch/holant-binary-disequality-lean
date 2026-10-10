import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCurrent
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralTerminals
import Holant.EightVertex.ProductAnchor.GeneralizedEquality

/-! A prepared actual-current O q4 produces an original-field prime even
endpoint and a controlled whole-current source to the unchanged original G.
The marked row, image planes, harmonic parameter, physical binaries, and all
multipliers are produced internally, never supplied as successful premises. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralEndpointCurrent
open Holant Holant.Algebraic Holant.Tractable Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts Holant.Certificates
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionOctahedralGeometry
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient
namespace D
export GlobalCloseCompletionOctahedralDressing (Tensor ψ mappedSignature)
end D
namespace T
export GlobalCloseCompletionOctahedralTerminals (target target_endpoint from_canonical)
end T
namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (tau : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (same : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family tau q,MatchingOrZero (actualTransfers P.family) f)

structure Output where
  form : Form
  group_eq : group (ClosureSourceRows.embedding G) P.family tau=Coordinates.Models.group form
  tensor : D.Tensor G P
  scalar : ℂ
  nonzero : scalar≠0
  coefficients : RingHomRealization.mapSignature (D.ψ G) tensor.table=scalar • T.target form
  endpoint : Holant.EightVertex.ProductAnchor.EndpointEven (D.mappedSignature G tensor.table)
  current : CurrentSignatureAccess G P ⟨4,tensor.table⟩

private theorem mapped_endpoint (f : Form) (R : D.Tensor G P) (c : ℂ) (hc : c≠0)
    (equation : RingHomRealization.mapSignature (D.ψ G) R.table=c • T.target f) :
    Holant.EightVertex.ProductAnchor.EndpointEven (D.mappedSignature G R.table) := by
  have he := T.target_endpoint f
  have h0 : R.table (fun _=>false)≠0 := by
    apply (map_ne_zero (D.ψ G)).mp
    change RingHomRealization.mapSignature (D.ψ G) R.table (fun _=>false)≠0
    rw [equation]
    exact mul_ne_zero hc he.1
  have h1 : R.table (fun _=>true)≠0 := by
    apply (map_ne_zero (D.ψ G)).mp
    change RingHomRealization.mapSignature (D.ψ G) R.table (fun _=>true)≠0
    rw [equation]
    exact mul_ne_zero hc he.2.1
  have odd (x : Fin 4→Bool) (hx : Holant.weight x%2=1) : R.table x=0 := by
    apply (D.ψ G).injective
    change RingHomRealization.mapSignature (D.ψ G) R.table x=(D.ψ G) 0
    rw [map_zero,equation]
    change c*T.target f x=0
    rw [he.2.2 x hx,mul_zero]
  exact ⟨(map_ne_zero (ClosureSourceRows.embedding G)).mpr h0,
    (map_ne_zero (ClosureSourceRows.embedding G)).mpr h1,
    fun x hx=>by change (ClosureSourceRows.embedding G) (R.table x)=0; rw [odd x hx,map_zero]⟩

include core same stable in
theorem produce
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G) P.family tau)
      (.platonic .octahedral)) : Nonempty (Output G P tau) := by
  obtain ⟨f,hf,deck,ranks⟩ := GlobalCloseCompletionOctahedralCurrent.produce
    G P tau q core same stable semantic
  have retained : (⟨4,q⟩ : AnySignature (OI.K G))∈P.family := same ▸ core.retained
  let initial : D.Tensor G P := ⟨q,Gadget.realizes_of_mem P.family .disequality q retained,
    ClosureSourceRows.core_ambient_prime G P q core same⟩
  obtain ⟨canonical,c,hc,he⟩ := GlobalCloseCompletionOctahedralNormalized.canonical
    G P tau f hf initial (ranks (Equiv.refl _)).1 (ranks (Equiv.refl _)).2
  obtain ⟨terminal,d,hd,ht⟩ := T.from_canonical G P tau f hf canonical c hc he
  exact ⟨⟨f,hf,terminal,d,hd,ht,mapped_endpoint G P f terminal d hd ht,
    currentSignatureAccess G P ⟨4,terminal.table⟩ terminal.actual⟩⟩

variable (base : Palette G)
variable {S U : GeneratedGroupWorklist.Active G base}
variable {trace : GeneratedGroupWorklist.Trace G base S U}
variable {o : CurrentOccurrences.Id G U.source.palette}
variable (receipt : GeneratedGroupWorklist.PreparationReceipt G base trace o)
variable (four : (CurrentOccurrences.savedLeaf G U.source.palette o).1.1=4)

include receipt four in
theorem prepared
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
      U.source.palette.family U.ready.torsion) (.platonic .octahedral)) :
    Nonempty (Output G U.source.palette U.ready.torsion) :=
  produce G U.source.palette U.ready.torsion
    (Q.table G base four) (Q.minimum G base four) (Q.minimum_literal G base four)
    (Q.matching G base receipt four) semantic


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralEndpointCurrent
end
