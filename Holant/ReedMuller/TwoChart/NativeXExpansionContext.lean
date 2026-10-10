import Holant.ReedMuller.TwoChart.NativeXExpansion

/-! The phase-free one-copy source context can use literal I and RM signatures
only: each literal X signature is realized by I-X-I inside the actual network.
Native X remains an edge tensor, never a retained signature assumption. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
attribute [local instance] Classical.propDecidable
variable {n m : ℕ}

/-- Literal I and literal RM only. X is supplied exclusively by native edges. -/
def algebraicIRMFamily : SignatureFamily AlgebraicComplex := {f |
  f=⟨2,fun x => Signature.equality (x 0) (x 1)⟩ ∨ f=⟨8,algebraicRM⟩}

namespace NativeXExpansion

theorem kept_resource (N : Network AlgebraicComplex m) (v : Kept N)
    (hv : (⟨N.shape.arity v.1,N.vertex v.1⟩ : AnySignature AlgebraicComplex)∈algebraicNativeFamily) :
    (⟨N.shape.arity v.1,N.vertex v.1⟩ : AnySignature AlgebraicComplex)∈algebraicIRMFamily := by
  rcases hv with hi|hx|hr
  · exact Or.inl hi
  · exact (v.2 hx).elim
  · exact Or.inr hr

/-- The original input vertex survives unchanged when its arity differs from
binary. Every other surviving vertex is I or RM; every replacement vertex is I. -/
theorem one_input_occurrence (g : Signature AlgebraicComplex n) (N : Network AlgebraicComplex m)
    (hn : n≠2) (hN : OneInputOccurrence algebraicNativeFamily g N) :
    OneInputOccurrence algebraicIRMFamily g (expand N) := by
  obtain ⟨v,hv,hrest⟩ := hN
  have hvX : ¬IsX N v := by
    intro hx
    exact hn (congrArg Sigma.fst (hv.symm.trans hx))
  let u : Kept N := ⟨v,hvX⟩
  let E := vertexEquiv N
  refine ⟨E (.inl u),(kept_label N u).trans hv,?_⟩
  intro w hw
  obtain ⟨q,rfl⟩ := E.surjective w
  cases q with
  | inl t =>
    rw [kept_label]
    apply kept_resource N t
    apply hrest
    intro htv
    have htu : t=u := Subtype.ext htv
    exact hw (congrArg E (congrArg Sum.inl htu))
  | inr t =>
    rw [replacement_label]
    exact Or.inl rfl

/-- All resources in the expanded one-copy network are the original g, I, RM. -/
theorem one_input_resources (g : Signature AlgebraicComplex n) (N : Network AlgebraicComplex m)
    (hn : n≠2) (hN : OneInputOccurrence algebraicNativeFamily g N) :
    ∀v,(⟨(expand N).shape.arity v,(expand N).vertex v⟩ : AnySignature AlgebraicComplex)∈
      insert (⟨n,g⟩ : AnySignature AlgebraicComplex) algebraicIRMFamily :=
  (one_input_occurrence g N hn hN).vertex_mem

end NativeXExpansion

/-- Genuine ordinary-network source bridge, with the same boundary signature,
scalar and single original g occurrence, native X edges, literal I/RM resources
only, and uniform quadratic vertex/edge bounds. -/
theorem one_copy_flat_IRM_context_realization
    (k : ℕ) (hnm : n+m=2*k) (hn : 10≤n) (g : Signature AlgebraicComplex n)
    (C : Signature AlgebraicComplex (n+m))
    (hf : Flat (fun x => (C x:ℂ))) :
    ∃(N : Network AlgebraicComplex m) (s : AlgebraicComplex),s≠0 ∧
      OneInputOccurrence algebraicIRMFamily g N ∧
      (∀e,N.edge e=Signature.disequality) ∧
      (∀b,N.denote b=s*∑x : Word n,g x*C (Fin.addCases x b)) ∧
      N.shape.vertices≤2+40*k^2+10*k ∧ N.shape.edges≤1+52*k^2+9*k+n := by
  obtain ⟨N,s,hs,hv,he,hd,hvs,hes⟩ := one_copy_flat_context_realization k hnm g C hf
  refine ⟨NativeXExpansion.expand N,s,hs,
    NativeXExpansion.one_input_occurrence g N (by omega) hv,
    NativeXExpansion.native_edges N he,?_,?_,?_⟩
  · intro b
    rw [NativeXExpansion.denote_expand]
    exact hd b
  · have hb := NativeXExpansion.vertex_bound N
    omega
  · have hb := NativeXExpansion.edge_bound N
    omega

end
end Holant.ReedMuller.TwoChart
