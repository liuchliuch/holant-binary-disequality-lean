import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramCertificate
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinStandardMatchingAffine

/-! Every actual canonical Pauli q4 matching has an exact two-factor integer
normal form in its original ports. A proportional real table recovers a real
nonzero coefficient by taking the real part of this literal equality. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramMatching
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace C
export GlobalCloseCompletionKleinGramCertificate (pauli product)
end C
namespace K
export Holant.Certificates.EqualityQuaternary.Klein (E basisQ matrix embed_apply)
end K
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem pauli_integer (k : Fin 4) (a b : Bool) :
    K.E .standard k a b=(C.pauli k a b : AlgebraicComplex) := by
  fin_cases k <;> cases a <;> cases b <;>
    norm_num [K.E,K.basisQ,K.matrix,K.embed_apply,QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one,C.pauli]

theorem canonical_product (q : Signature AlgebraicComplex 4)
    (matching : ClosureKleinCurrent.CanonicalMatching .standard q) (nonzero : q≠0) :
    ∃p : Equiv.Perm (Fin 4),∃a b : Fin 4,∃c : AlgebraicComplex,c≠0 ∧
      ∀x,q x=c*(C.product p a b x : AlgebraicComplex) := by
  rcases matching with zero|⟨M,labels,hc,matrices,literal⟩
  · exact (nonzero zero).elim
  rcases M with ⟨edges,ports,matrix,scalar⟩
  have card := Fintype.card_congr ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at card
  have he : edges=2 := by omega
  subst edges
  change ∀e : Fin 2,matrix e=K.E .standard (labels e) at matrices
  let p : Equiv.Perm (Fin 4) := finProdFinEquiv.symm.trans
    ((Equiv.prodCongr (Equiv.refl (Fin 2)) finTwoEquiv).trans ports)
  refine ⟨p,labels 0,labels 1,scalar,hc,?_⟩
  intro x
  rw [literal]
  simp only [Presentation.tensor,productValue,Fin.prod_univ_two,matrices,pauli_integer,C.product,Int.cast_mul]
  rfl

theorem real_product (q : Signature AlgebraicComplex 4)
    (matching : ClosureKleinCurrent.CanonicalMatching .standard q) (nonzero : q≠0)
    (r : Signature ℝ 4) (scale : ℂ) (scale_ne : scale≠0)
    (equation : ∀x,(q x:ℂ)=scale*(r x:ℂ)) :
    ∃p : Equiv.Perm (Fin 4),∃a b : Fin 4,∃c : ℝ,c≠0 ∧ ∀x,r x=c*(C.product p a b x : ℝ) := by
  obtain ⟨p,a,b,c,hc,literal⟩ := canonical_product q matching nonzero
  let d : ℂ := (c:ℂ)/scale
  have real (x : Fin 4→Bool) : r x=d.re*(C.product p a b x : ℝ) := by
    have h := equation x
    rw [literal] at h
    have h' : (r x:ℂ)=d*(C.product p a b x : ℂ) := by
      change (r x:ℂ)=((c:ℂ)/scale)*(C.product p a b x : ℂ)
      change (c:ℂ)*(C.product p a b x : ℂ)=scale*(r x:ℂ) at h
      apply mul_left_cancel₀ scale_ne
      calc
        scale*(r x:ℂ)=(c:ℂ)*(C.product p a b x : ℂ) := h.symm
        _=scale*(((c:ℂ)/scale)*(C.product p a b x : ℂ)) := by field_simp
    have re := congrArg Complex.re h'
    simpa using re
  refine ⟨p,a,b,d.re,?_,real⟩
  intro zero
  apply nonzero
  funext x
  apply Subtype.ext
  change (q x:ℂ)=0
  rw [equation,real,zero,zero_mul,Complex.ofReal_zero,mul_zero]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramMatching
end
