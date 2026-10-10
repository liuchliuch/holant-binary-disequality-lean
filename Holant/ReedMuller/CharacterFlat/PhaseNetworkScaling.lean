import Holant.ReedMuller.CharacterFlat.PhaseNetwork

/-! Replace each literal ordered Bell occurrence by one fixed actual nonzero
representative. Every vertex is retained, and the scalar is the product of the
representatives' occurrence scalars, not a free supply of rescaled gates. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Exactly the retained RM tensor and the four fixed ordered Bell tensors. -/
def retainedFamily (κ : ZMod 2 → ZMod 2 → ℂ) : SignatureFamily ℂ :=
  {f | f=⟨8,rmCore⟩ ∨ ∃ d l,f=⟨2,κ d l • bellSignature d l⟩}

def literalFamily : SignatureFamily ℂ :=
  {f | f=⟨8,rmCore⟩ ∨ ∃ d l,f=⟨2,bellSignature d l⟩}

namespace PhaseNetwork
open GenerationNetwork
variable {n : ℕ}

@[simp] theorem bell_zero_zero : bellSignature 0 0=
    (fun x : Fin 2 → Bool => Signature.equality (x 0) (x 1)) := by
  funext x
  simp [bellSignature,bellKernel,parityKernel_zero]

@[simp] theorem bell_one_zero : bellSignature 1 0=
    (fun x : Fin 2 → Bool => Signature.disequality (x 0) (x 1)) := by
  funext x
  simp [bellSignature,bellKernel,parityKernel_one]

theorem nativeFamily_subset_literal : nativeFamily⊆literalFamily := by
  intro f hf
  rcases hf with hi | hx | hr
  · right
    exact ⟨0,0,by simpa only [bell_zero_zero] using hi⟩
  · right
    exact ⟨1,0,by simpa only [bell_one_zero] using hx⟩
  · exact Or.inl hr

theorem attach_vertex_mem (N : Network ℂ n) (l : BinaryVector n)
    (hN : ∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈literalFamily) :
    ∀ v,(⟨(attach N l).shape.arity v,(attach N l).vertex v⟩ : AnySignature ℂ)∈literalFamily := by
  intro v
  change (⟨(finite N l).arity ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin n)).symm v),
    (finite N l).vertex ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin n)).symm v)⟩ : AnySignature ℂ)∈_
  cases (Fintype.equivFin (Fin N.shape.vertices ⊕ Fin n)).symm v with
  | inl v => exact hN v
  | inr i => exact Or.inr ⟨1,l i,rfl⟩

def rescale (N : Network ℂ n) (c : Fin N.shape.vertices → ℂ) : Network ℂ n where
  shape := N.shape
  vertex := fun v => c v • N.vertex v
  edge := N.edge

theorem denote_rescale (N : Network ℂ n) (c : Fin N.shape.vertices → ℂ) :
    (rescale N c).denote=(∏ v,c v) • N.denote := by
  funext x
  simp only [rescale,Network.denote,Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

private def scaleAny (c : ℂ) (f : AnySignature ℂ) : AnySignature ℂ := ⟨f.1,c • f.2⟩

theorem literal_rescale_mem (κ : ZMod 2 → ZMod 2 → ℂ) (hκ : ∀ d l,κ d l≠0)
    (f : Signature ℂ n) (hf : (⟨n,f⟩ : AnySignature ℂ)∈literalFamily) :
    ∃ c : ℂ,c≠0 ∧ (⟨n,c • f⟩ : AnySignature ℂ)∈retainedFamily κ := by
  rcases hf with hr | ⟨d,l,hb⟩
  · exact ⟨1,one_ne_zero,Or.inl (by simpa only [one_smul] using hr)⟩
  · refine ⟨κ d l,hκ d l,Or.inr ⟨d,l,?_⟩⟩
    exact congrArg (scaleAny (κ d l)) hb

/-- Only existing vertex occurrences change labels. The graph, port order,
edge labels and both size measures are unchanged. -/
theorem rescale_to_retained (κ : ZMod 2 → ZMod 2 → ℂ) (hκ : ∀ d l,κ d l≠0)
    (N : Network ℂ n)
    (hN : ∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈literalFamily)
    (he : ∀ e,N.edge e=Signature.disequality) :
    ∃ (M : Network ℂ n) (q : ℂ),q≠0 ∧
      (∀ v,(⟨M.shape.arity v,M.vertex v⟩ : AnySignature ℂ)∈retainedFamily κ) ∧
      (∀ e,M.edge e=Signature.disequality) ∧ M.denote=q • N.denote ∧
      M.shape.vertices=N.shape.vertices ∧ M.shape.edges=N.shape.edges := by
  have hlocal : ∀ v,∃ c : ℂ,c≠0 ∧
      (⟨N.shape.arity v,c • N.vertex v⟩ : AnySignature ℂ)∈retainedFamily κ :=
    fun v => literal_rescale_mem κ hκ (N.vertex v) (hN v)
  choose c hc hm using hlocal
  refine ⟨rescale N c,∏ v,c v,?_,hm,he,denote_rescale N c,rfl,rfl⟩
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => hc v)

end PhaseNetwork
end
end Holant.ReedMuller.CharacterFlat
