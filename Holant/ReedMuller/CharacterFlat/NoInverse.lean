import Holant.ReedMuller.CharacterFlat.Bell

/-! Source Corollary 7.21. The literal four-term H6 table has supported words
whose differences have odd intersection, excluding every affine self-dual
support and hence every pure RM/ordered-Bell native-X network. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

def hCore : Signature ℂ 6 := fun x =>
  bellKernel 0 0 (x 0) (x 1)*bellKernel 0 0 (x 2) (x 3)*bellKernel 0 0 (x 4) (x 5)+
  bellKernel 0 1 (x 0) (x 1)*bellKernel 1 1 (x 2) (x 3)*bellKernel 1 0 (x 4) (x 5)+
  bellKernel 1 0 (x 0) (x 1)*bellKernel 0 1 (x 2) (x 3)*bellKernel 1 1 (x 4) (x 5)+
  bellKernel 1 1 (x 0) (x 1)*bellKernel 1 0 (x 2) (x 3)*bellKernel 0 1 (x 4) (x 5)

def zeroSix : Fin 6 → Bool := ![false,false,false,false,false,false]
def firstPair : Fin 6 → Bool := ![true,true,false,false,false,false]
def crossingPair : Fin 6 → Bool := ![true,false,true,false,false,false]

theorem hCore_zero : hCore zeroSix=1 := by
  norm_num [hCore,zeroSix,bellKernel,parityKernel,sign,intSign,bit,boolEquiv] <;> decide
theorem hCore_first : hCore firstPair=1 := by
  norm_num [hCore,firstPair,bellKernel,parityKernel,sign,intSign,bit,boolEquiv] <;> decide
theorem hCore_crossing : hCore crossingPair = -1 := by
  norm_num [hCore,crossingPair,bellKernel,parityKernel,sign,intSign,bit,boolEquiv] <;> decide

theorem nonzeroFlat_support_orthogonal {n : ℕ} (f : Signature ℂ n) (hf : NonzeroFlat f)
    (u v : BinaryVector n) (h0 : f (wordVector 0)≠0)
    (hu : f (wordVector u)≠0) (hv : f (wordVector v)≠0) : dot u v=0 := by
  obtain ⟨c,a,D,ell,hD,rfl⟩ := hf
  have hm (x : BinaryVector n) : signature c a D ell (wordVector x)≠0 ↔ x-a∈D := by
    simp only [signature,vector_word]
    exact value_nonzero_iff c c.ne_zero a D ell x
  have hz := (hm 0).mp h0
  have hdu : u∈D := by
    have H := D.sub_mem ((hm u).mp hu) hz
    simpa using H
  have hdv : v∈D := by
    have H := D.sub_mem ((hm v).mp hv) hz
    simpa using H
  exact (hD u).mp hdu v hdv

/-- Literal source H6, not an arbitrary table assigned an abstract obstruction. -/
theorem hCore_not_character_flat : ¬CFlat hCore := by
  intro h
  have hn : hCore≠0 := by intro hz;have H:=congrFun hz zeroSix;rw [hCore_zero] at H;exact one_ne_zero H
  have hf := h.resolve_left hn
  have h0 : hCore (wordVector 0)≠0 := by
    have he : (wordVector (0:BinaryVector 6))=zeroSix := by decide
    rw [he,hCore_zero];exact one_ne_zero
  have hu : hCore (wordVector (vectorWord firstPair))≠0 := by
    rw [word_vector,hCore_first];exact one_ne_zero
  have hv : hCore (wordVector (vectorWord crossingPair))≠0 := by
    rw [word_vector,hCore_crossing];norm_num
  have H := nonzeroFlat_support_orthogonal hCore hf (vectorWord firstPair) (vectorWord crossingPair) h0 hu hv
  have hc : dot (vectorWord firstPair) (vectorWord crossingPair)=1 := by decide
  rw [hc] at H
  exact one_ne_zero H

/-- No nonzero proportional copy of the source H6 is a pure Pauli/RM boundary. -/
theorem source_no_pure_pauli_inverse (N : Network ℂ 6)
    (hv : ∀ v,SourcePrimitive (N.vertex v)) (he : ∀ e,N.edge e=Signature.disequality)
    (c : ℂ) (hc : c≠0) : N.denote≠c • hCore := by
  intro h
  have hf := source_character_network_forward N hv he
  rw [h] at hf
  have H := CharacterFlat.CFlat.smul (c • hCore) hf c⁻¹
  rw [smul_smul,inv_mul_cancel₀ hc,one_smul] at H
  exact hCore_not_character_flat H

end
end Holant.ReedMuller.CharacterFlat
