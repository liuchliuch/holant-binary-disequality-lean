import Holant.Certificates.AffineReference.FullEvenCertificate
import Holant.Certificates.AffineReference.FullEvenSemantics

namespace Holant.Certificates.AffineReference
open Holant Holant.Tractable Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def weightedEquality (r : AlgebraicComplex) : Signature AlgebraicComplex 2 :=
  fun x => if x 0=x 1 then if x 0 then r else 1 else 0

 def equalCopiesTensor (c r : AlgebraicComplex) (b : Fin 3) : Signature AlgebraicComplex 4 :=
  fun x => c * Tensor.reindex (portEquiv (initialPair b))
    (Signature.tensor (weightedEquality r) (weightedEquality r)) x

 theorem equalCopiesTensor_entries (c r : AlgebraicComplex) (b : Fin 3) (x : Fin 4 → Bool) :
    equalCopiesTensor c r b x=
      if x (blockPair b).1=x (blockPair b).2 ∧ x (blockComplement b).1=x (blockComplement b).2 then
        c * ((if x (blockPair b).1 then r else 1)*(if x (blockComplement b).1 then r else 1)) else 0 := by
  fin_cases b <;> simp [equalCopiesTensor,Tensor.reindex,Signature.tensor_apply,weightedEquality,
    portEquiv,portOrder,initialPair,blockPair,blockComplement] <;> split_ifs <;> simp_all

 theorem algEmbed_equalProduct (c : Gaussian) (r : Fin 4) (b : Fin 3) (x : Fin 4 → Bool) :
    algEmbed (equalProductTable c r b x)=equalCopiesTensor (algEmbed c) (algEmbed (fourthRoot r)) b x := by
  rw [equalCopiesTensor_entries]
  unfold equalProductTable
  split
  · rw [algEmbed_mul,algEmbed_mul]
    congr 2 <;> split <;> simp [algEmbed]
  · exact algEmbed_zero

/-- Literal support-four product of two identical nonsingular weighted
binary equalities, with its actual nonzero scalar and ordered pairing. -/
 def EqualCopiesProduct (q : Signature AlgebraicComplex 4) : Prop :=
  ∃ (c r : AlgebraicComplex) (b : Fin 3),c≠0 ∧ r≠0 ∧ r^4=1 ∧ q=equalCopiesTensor c r b

 theorem even_product_exit (p : EvenParameters) (e b : Fin 3) (r : Fin 4)
    (h : ValidEvenWitness p (.product e b r)) :
    EqualCopiesProduct (crossedCopies (evenAlg p) e) ∧
      Gadget.Realizes ({⟨4,evenAlg p⟩} : SignatureFamily AlgebraicComplex) .disequality
        (crossedCopies (evenAlg p) e) := by
  refine ⟨?_,crossedCopies_realizes _ _⟩
  refine ⟨algEmbed (crossedTable p e (fun _ => false)),algEmbed (fourthRoot r),b,
    (not_congr (algEmbed_zero_iff _)).mpr h.1,?_,?_,?_⟩
  · rw [algEmbed_fourthRoot]
    exact fourthRootPhase_ne_zero _
  · rw [algEmbed_fourthRoot]
    exact fourthRootPhase_pow_four _
  · funext x
    rw [←algEmbed_crossedTable,h.2 x,algEmbed_equalProduct]

/-- Complete A.5(iii) classification from the actual affine predicate, full
support and canonical normalization. The 512-table restriction is derived. -/
 theorem full_even_reference_exits (h : Signature AlgebraicComplex 4) (ha : Affine h)
    (hs : ∀ x,h x≠0 ↔ evenWord x=true) (h0 : h (fun _ => false)=1) :
    EightVertex.ProductAnchor.DenseForm h ∨
    (∃ e : Fin 6,
      (Matrix.of (fun a b : Bool => ((nativeContract (K := AlgebraicComplex) h e ![a,b] : AlgebraicComplex) : ℂ))).rank=1 ∧
      Gadget.Realizes ({⟨4,h⟩} : SignatureFamily AlgebraicComplex) .disequality (nativeContract h e)) ∨
    ∃ e : Fin 3,EqualCopiesProduct (crossedCopies h e) ∧
      Gadget.Realizes ({⟨4,h⟩} : SignatureFamily AlgebraicComplex) .disequality (crossedCopies h e) := by
  obtain ⟨p,rfl⟩ := full_even_coverage h ha hs h0
  have hv := evenWitness_valid p
  cases hw : evenWitness p with
  | dense u m => exact Or.inl (even_dense_exit p u m (hw ▸ hv))
  | rankOne e => exact Or.inr (Or.inl ⟨e,even_rank_one_exit p e (hw ▸ hv)⟩)
  | product e b r => exact Or.inr (Or.inr ⟨e,even_product_exit p e b r (hw ▸ hv)⟩)

end
end Holant.Certificates.AffineReference
