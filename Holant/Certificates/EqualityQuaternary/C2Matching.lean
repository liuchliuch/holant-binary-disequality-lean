import Holant.Certificates.EqualityQuaternary.C2MixedFactor

/-! Necessary Walsh support facts are derived from genuine original-port
C2 matching products. No matching normal form is assumed in the input. -/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.C2
open Holant Holant.Marked Holant.Tractable
open Holant.Projective.CyclicQuaternary
open Holant.Projective.CyclicQuaternary.Physical hiding Scalar Mat
open Holant.Projective.CyclicPhasePencil (diagonal)
set_option backward.isDefEq.respectTransparency false

def group : Set Mat := {B | ∃ p c, c≠0 ∧ B=scale c (binary p)}

theorem matching_walsh_form {q : Signature Scalar 4} (h : GroupMatching group q) :
    ∃ (p : (Fin 2 ⊕ Fin 2) ≃ Fin 4) (s t : Bool) (d : Scalar), d≠0 ∧ ∀ w,
      walsh q w = d * diagonal 1 (sign s) (w (p (.inl 0))) (w (p (.inl 1))) *
        diagonal 1 (sign t) (w (p (.inr 0))) (w (p (.inr 1))) := by
  obtain ⟨p,A,⟨s,a,ha,rfl⟩,B,⟨t,b,hb,rfl⟩,c,hc,hq⟩ := h
  have hf : (fun x : Fin 2 → Bool => c*kernelSignature (scale a (binary s)) x)=
      kernelSignature (scale (c*a) (binary s)) := by funext x; simp [kernelSignature,scale,mul_assoc]
  have hform : walsh q = Tensor.reindex p (Tensor.tensor
      (kernelSignature (scale (c*a/2) (diagonal 1 (sign s))))
      (kernelSignature (scale (b/2) (diagonal 1 (sign t))))) := by
    rw [hq,hf,walsh,Mixed.binary_factor_action]
    change Tensor.reindex p (Tensor.tensor (walsh _) (walsh _))=_
    rw [walshBinary_signature,walshBinary_signature,walsh_binary_scale,walsh_binary_scale]
  refine ⟨p,s,t,(c*a/2)*(b/2),?_,?_⟩
  · exact mul_ne_zero (div_ne_zero (mul_ne_zero hc ha) (by norm_num))
      (div_ne_zero hb (by norm_num))
  · intro w
    rw [hform]
    simp only [Tensor.reindex,Tensor.tensor,kernelSignature,scale]
    ring

theorem matching_walsh_endpoint {q : Signature Scalar 4} (h : GroupMatching group q) :
    endpoint0 (walsh q)≠0 := by
  obtain ⟨p,s,t,d,hd,hv⟩ := matching_walsh_form h
  simpa [endpoint0,hv,diagonal] using hd

theorem matching_walsh_square {q : Signature Scalar 4} (h : GroupMatching group q) (w : Word) :
    walsh q w=0 ∨ (walsh q w)^2=(endpoint0 (walsh q))^2 := by
  obtain ⟨p,s,t,d,_,hv⟩ := matching_walsh_form h
  rw [hv]
  have he : endpoint0 (walsh q)=d := by simp [endpoint0,hv,diagonal]
  rw [he]
  cases s <;> cases t <;> cases h0 : w (p (.inl 0)) <;> cases h1 : w (p (.inl 1)) <;>
    cases h2 : w (p (.inr 0)) <;> cases h3 : w (p (.inr 1)) <;>
    simp [diagonal,sign,h0,h1,h2,h3]

def mixedWord (p : (Fin 2 ⊕ Fin 2) ≃ Fin 4) : Word :=
  fun i => Sum.elim (fun _ => true) (fun _ => false) (p.symm i)

theorem matching_walsh_interior {q : Signature Scalar 4} (h : GroupMatching group q) :
    ∃ w : Word, w≠(fun _ => false) ∧ w≠(fun _ => true) ∧ walsh q w≠0 := by
  obtain ⟨p,s,t,d,hd,hv⟩ := matching_walsh_form h
  refine ⟨mixedWord p,?_,?_,?_⟩
  · intro hh
    have := congrFun hh (p (.inl 0))
    simpa [mixedWord] using this
  · intro hh
    have := congrFun hh (p (.inr 0))
    simpa [mixedWord] using this
  · rw [hv]
    cases s <;> cases t <;> simp [mixedWord,diagonal,sign,hd]

def firstWord (i : Fin 3) : Word := join i false true true false false

private theorem separates : ∀ (i j : Fin 3) (r s : Fin 4), i≠j →
    firstWord i r=firstWord i s → firstWord j r=firstWord j s → r=s := by decide

theorem matching_one_block {q : Signature Scalar 4} (h : GroupMatching group q)
    (i j : Fin 3) (hi : (coordinates (walsh q) i).1≠0)
    (hj : (coordinates (walsh q) j).1≠0) : i=j := by
  obtain ⟨p,s,t,d,_,hv⟩ := matching_walsh_form h
  have same (k : Fin 3) (hk : (coordinates (walsh q) k).1≠0) :
      firstWord k (p (.inl 0))=firstWord k (p (.inl 1)) := by
    by_contra hh
    apply hk
    change walsh q (firstWord k)=0
    rw [hv]
    simp [diagonal,hh]
  by_contra hn
  have hpos := separates i j (p (.inl 0)) (p (.inl 1)) hn (same i hi) (same j hj)
  have hbad := p.injective hpos
  simpa using hbad

end Holant.Certificates.EqualityQuaternary.C2
