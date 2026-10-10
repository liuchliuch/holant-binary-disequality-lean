import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryUniversalSelector
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDescentSource
import Holant.Proofs.Closure.ClosureFactorTreeFieldMap
import Holant.Proofs.FiniteGroups.Stabilization.MatchingStability

/-! Whole-family source selection before unary descent. Failure of the
literal criterion selects a nonbinary prime leaf of an actual retained row.
A live origin lets the retained zero pin realize that leaf physically;
a zero origin already supplies the other selector exit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryWholeFamilySelector
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace W
export GlobalCloseCompletionUnaryUniversalSelector (Produced produce)
end W
namespace F
export GlobalCloseCompletionUnaryFactorCaps (exists_leaf)
end F
namespace D
export GlobalCloseCompletionUnaryDescentSource (ambient mapped)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
variable (H : (i : Fin r)→Signature L (b i.val))

def row (i : Fin r) : NoXOrdinaryGraphAdjoin.Output H (b i.val) where
  network:=Network.corolla (H i)
  labels:={vertex _:=i,vertex_arity _:=rfl,edge e:=Fin.elim0 e}
  exact _:=rfl
  ordinary e:=Fin.elim0 e

theorem row_value (i : Fin r) : (row L H i).network.denote=H i := Network.denote_corolla _

def tree (i : Fin r) (nonzero : H i≠0) : FactorTree (⟨b i.val,(row L H i).network.denote⟩ : AnySignature L) :=
  Classical.choice (exists_factorTree _ (by rwa [row_value]))

theorem small_tract
    (small : ∀i,0<b i.val→∀h : H i≠0,∀g∈(tree L H i h).leaves,g.1≤2) :
    Tract (D.ambient L H) := by
  refine ⟨(Set.finite_range (fun i : Fin r=>(⟨b i.val,D.mapped L H i⟩ : AnySignature AlgebraicComplex))).subset
    (fun _ h=>h.1),Or.inr (Or.inr (Or.inl ?_))⟩
  rintro f ⟨⟨i,rfl⟩,positive,nonzero⟩
  have hi : H i≠0 := by
    intro zero
    apply nonzero
    funext x
    change L.subtype (H i x)=0
    simp [zero]
  let t:=tree L H i hi
  have tiny : ∀g∈(ClosureFactorTreeFieldMap.tree L.subtype t).leaves,g.1=1 ∨ g.1=2 := by
    intro g member
    rw [ClosureFactorTreeFieldMap.leaves] at member
    obtain ⟨v,hv,rfl⟩:=Multiset.mem_map.mp member
    have hp:=t.leaf_positive positive v hv
    have hs:=small i positive hi v hv
    change v.1=1 ∨ v.1=2
    omega
  right
  have h:=ClosureSmallArity.small_tree (ClosureFactorTreeFieldMap.tree L.subtype t) tiny
  change Signature.TensorClosure (fun n _=>n=1 ∨ n=2)
    (RingHomRealization.mapSignature L.subtype (row L H i).network.denote) at h
  rw [row_value] at h
  exact h

theorem large_exists (negative : ¬Tract (D.ambient L H)) :
    ∃i,∃positive : 0<b i.val,∃nonzero : H i≠0,∃g∈(tree L H i nonzero).leaves,3≤g.1 := by
  classical
  by_contra none
  apply negative
  apply small_tract L H
  intro i positive nonzero g member
  by_contra bound
  exact none ⟨i,positive,nonzero,g,member,by omega⟩

variable (U : NoXOrdinaryGraphAdjoin.Output H 1)
variable (scalar : L) (scalarNonzero : scalar≠0)
variable (pin0 : U.network.denote (fun _=>false)=scalar)
variable (pin1 : U.network.denote (fun _=>true)=0)
variable (negative : ¬Tract (D.ambient L H))
include scalarNonzero pin0 pin1 negative in
theorem exists_produced : Nonempty (W.Produced H) := by
  obtain ⟨i,positive,nonzero,g,member,large⟩:=large_exists L H negative
  let N:=row L H i
  by_cases origin : N.network.denote (fun _=>false)≠0
  · obtain ⟨V,pv,ov,c,hc,form⟩:=F.exists_leaf H U N scalar scalarNonzero pin0 pin1 origin
      (tree L H i nonzero) g member
    exact ⟨W.produce H U scalar scalarNonzero pin0 pin1 g.1 V large pv⟩
  · exact ⟨.zeroOrigin N positive (by rwa [show N.network.denote=H i from row_value L H i])
      (not_not.mp origin)⟩

def produce : W.Produced H :=
  Classical.choice (exists_produced L H U scalar scalarNonzero pin0 pin1 negative)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryWholeFamilySelector
end
