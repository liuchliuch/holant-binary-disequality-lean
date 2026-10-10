import Holant.ReedMuller.CharacterFlat.PhaseNetworkScaling

/-! Source Lemma 7.20, item 2: the retained literal RM tensor and any fixed
nonzero representative of each of the four ordered Bell tensors realize every
nonzero character-flat signature projectively, with explicit graph size. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open PhaseNetwork

theorem source_character_network_literal (k : ℕ) (a : BinaryVector (2*k))
    (D : BinaryCode (2*k)) (hD : SelfDual D) (ell : Character (2*k)) :
    ∃ N : Network ℂ (2*k),
      (∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈literalFamily) ∧
      (∀ e,N.edge e=Signature.disequality) ∧ N.denote=signature 1 a D ell ∧
      N.shape.vertices≤20*k^2+7*k ∧ N.shape.edges≤32*k^2+6*k := by
  obtain ⟨N,hv,he,hd,_,hvs,hes⟩ := source_flat_network_native k a D hD
  refine ⟨attach N (coefficients ell),?_,attach_native N _ he,
    denote_attach_flat N a D hd ell,?_,?_⟩
  · exact attach_vertex_mem N _ (fun v => nativeFamily_subset_literal (hv v))
  · rw [attach_vertices]
    omega
  · rw [attach_edges]
    omega

private theorem normalize_scalar {n : ℕ} (c : ℂˣ) (a : BinaryVector n)
    (D : BinaryCode n) (ell : Character n) :
    signature 1 a D ell=(c : ℂ)⁻¹ • signature c a D ell := by
  funext x
  simp only [signature,value,Pi.smul_apply,smul_eq_mul]
  split_ifs
  · rw [one_mul,←mul_assoc,inv_mul_cancel₀ c.ne_zero,one_mul]
  · simp

/-- Actual ordinary-boundary native-X realization from fixed representatives.
The existential scalar records all Bell-occurrence scalars and the input
signature's normalization, and is proved nonzero. Arity zero is included. -/
theorem source_character_network_converse
    (κ : ZMod 2 → ZMod 2 → ℂ) (hκ : ∀ d l,κ d l≠0)
    (k : ℕ) (f : Signature ℂ (2*k)) (hf : NonzeroFlat f) :
    ∃ (N : Network ℂ (2*k)) (c : ℂ),c≠0 ∧
      (∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈retainedFamily κ) ∧
      (∀ e,N.edge e=Signature.disequality) ∧ N.denote=c • f ∧ N.denote≠0 ∧
      N.shape.vertices≤20*k^2+7*k ∧ N.shape.edges≤32*k^2+6*k := by
  have hfn := nonzeroFlat_nonzero f hf
  obtain ⟨c,a,D,ell,hD,rfl⟩ := hf
  obtain ⟨N,hv,he,hd,hvs,hes⟩ := source_character_network_literal k a D hD ell
  obtain ⟨M,q,hq,hmv,hme,hmd,hmvs,hmes⟩ := rescale_to_retained κ hκ N hv he
  have hs : q*(c : ℂ)⁻¹≠0 := mul_ne_zero hq (inv_ne_zero c.ne_zero)
  have hmd' : M.denote=(q*(c : ℂ)⁻¹) • signature c a D ell := by
    rw [hmd,hd,normalize_scalar c a D ell,smul_smul]
  refine ⟨M,q*(c : ℂ)⁻¹,hs,hmv,hme,hmd',?_,?_,?_⟩
  · rw [hmd']
    exact smul_ne_zero hs hfn
  · omega
  · omega

/-- The source's CFlat-plus-nonzero premise implies the substantive converse. -/
theorem source_character_network_converse_of_CFlat
    (κ : ZMod 2 → ZMod 2 → ℂ) (hκ : ∀ d l,κ d l≠0)
    (k : ℕ) (f : Signature ℂ (2*k)) (hf : CFlat f) (hn : f≠0) :
    ∃ (N : Network ℂ (2*k)) (c : ℂ),c≠0 ∧
      (∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈retainedFamily κ) ∧
      (∀ e,N.edge e=Signature.disequality) ∧ N.denote=c • f ∧ N.denote≠0 ∧
      N.shape.vertices≤20*k^2+7*k ∧ N.shape.edges≤32*k^2+6*k := by
  exact source_character_network_converse κ hκ k f (hf.resolve_left hn)

/-- Native gadget consumer form, with precisely the supplied actual resources. -/
theorem source_character_network_realizes
    (κ : ZMod 2 → ZMod 2 → ℂ) (hκ : ∀ d l,κ d l≠0)
    (k : ℕ) (f : Signature ℂ (2*k)) (hf : NonzeroFlat f) :
    Gadget.RealizesUpTo (retainedFamily κ) .disequality f := by
  obtain ⟨N,c,hc,hv,he,hd,_,_,_⟩ := source_character_network_converse κ hκ k f hf
  refine ⟨c,hc,?_⟩
  have hr := Gadget.realizes_network N (retainedFamily κ) .disequality hv he
  rw [hd] at hr
  exact hr

end
end Holant.ReedMuller.CharacterFlat
