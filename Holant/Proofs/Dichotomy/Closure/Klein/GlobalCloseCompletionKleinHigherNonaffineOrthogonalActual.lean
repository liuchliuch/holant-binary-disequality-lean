import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2RadonActual
import Holant.Platonic.StabilizerShortening.AffineTools

/-! Every finite RM orthogonal-coordinate program acts on an actual original
row through a genuine same-field graph. Its nonzero scalar is retained and
nonaffinity is transported in both directions. No prime-preservation claim is
made: a transformed proper factor remains an explicit next-stage obligation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineOrthogonalActual
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffinePatching
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerShortening
namespace A
export GlobalCloseCompletionC2RadonActual (complexEmbedding resource_actual descend_upTo)
end A
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace B
export GlobalCloseCompletionC2BitTranslateActual (identity)
end B
namespace RH
export RingHomRealization (mapSignature mapFamily)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

private theorem algebraic_complex_iff {n : ℕ} (f : Signature AlgebraicComplex n) :
    ComplexAffine (fun x=>(f x:ℂ)) ↔ Affine f := by
  constructor
  · rintro ⟨c,g,affine,equation⟩
    by_cases zero : f=0
    · rw [zero];exact affine_zero n
    obtain ⟨x,hx⟩ : ∃x,f x≠0 := by by_contra! none;exact zero (funext none)
    have gx : g x≠0 := by
      intro h
      have hh := equation x
      rw [h,ZeroMemClass.coe_zero,mul_zero] at hh
      exact hx (Subtype.ext hh)
    have cg : (g x:ℂ)≠0 := by exact_mod_cast gx
    have scalar : c=((f x/g x:AlgebraicComplex):ℂ) := by
      push_cast
      exact (eq_div_iff cg).mpr (equation x).symm
    have same : f=fun y=>(f x/g x)*g y := by
      funext y
      apply Subtype.ext
      push_cast
      have scalar' := scalar
      push_cast at scalar'
      rw [←scalar']
      exact equation y
    rw [same]
    exact affine.scale _
  · exact complexAffine_of_affine

def action {K : Type*} {n : ℕ} (p : GenerationProgram n) (f : Signature K n) : Signature K n :=
  fun x=>f (wordVector (p.inverse.word (vectorWord x)))

theorem action_inverse {K : Type*} {n : ℕ} (p : GenerationProgram n) (f : Signature K n) :
    action p.inverse (action p f)=f := by
  funext x
  simp only [action,vector_word,GenerationProgram.inverse_inverse,GenerationProgram.word_inverse,word_vector]

theorem action_affine {n : ℕ} (p : GenerationProgram n) (f : Signature AlgebraicComplex n)
    (affine : Affine f) : Affine (action p f) := by
  have h := affine.precompose (affineBoolean 0 p.inverse.linear) (affineBoolean_isAffine _ _)
  change Affine (fun x=>f (wordVector (p.inverse.word (vectorWord x))))
  simpa only [affineBoolean,zero_add,GenerationProgram.linear_apply] using h

theorem action_affine_iff {n : ℕ} (p : GenerationProgram n) (f : Signature AlgebraicComplex n) :
    Affine (action p f) ↔ Affine f := by
  constructor
  · intro h
    have hh := action_affine p.inverse _ h
    rwa [action_inverse] at hh
  · exact action_affine p f

theorem action_complex {n : ℕ} (p : GenerationProgram n) (f : Signature ℂ n)
    (affine : ComplexAffine f) : ComplexAffine (action p f) := by
  have h := affine_complex_precompose affine (affineBoolean 0 p.inverse.linear) (affineBoolean_isAffine _ _)
  change ComplexAffine (fun x=>f (wordVector (p.inverse.word (vectorWord x))))
  simpa only [affineBoolean,zero_add,GenerationProgram.linear_apply] using h

theorem action_complex_iff {n : ℕ} (p : GenerationProgram n) (f : Signature ℂ n) :
    ComplexAffine (action p f) ↔ ComplexAffine f := by
  constructor
  · intro h
    have hh := action_complex p.inverse _ h
    rwa [action_inverse] at hh
  · exact action_complex p f

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
variable (phi : K→+*AlgebraicComplex) (F : SignatureFamily K)
variable (hI : (⟨2,B.identity⟩ : AnySignature K)∈F)
variable (c : K) (hc : c≠0) (rmActual : Gadget.Realizes F .disequality (c • R.rm))
variable (f : Signature K (n+2)) (actual : Gadget.Realizes F .disequality f)

include hI hc rmActual actual in
theorem program_actual (p : GenerationProgram (n+2)) :
    ∃q : Signature K (n+2),∃d : ℂ,d≠0 ∧ Gadget.Realizes F .disequality q ∧
      RH.mapSignature (A.complexEmbedding phi) q=d • action p (RH.mapSignature (A.complexEmbedding phi) f) ∧
      (Affine (RH.mapSignature phi q) ↔ Affine (RH.mapSignature phi f)) := by
  let g := RH.mapSignature (A.complexEmbedding phi) f
  let N := oneCopy p g
  have uses : Uses (radonFamily g) N := oneCopy_uses (radonFamily g) p g
    (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl)))
  have edge := oneCopy_edges p g
  have nativeUses := uses_native (radonFamily g) N uses edge
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))
  have network := OpenNetworkComposition.realizesUpTo_network (RH.mapFamily (A.complexEmbedding phi) F)
    (GenerationNetwork.native N)
    (fun v=>A.resource_actual phi F hI c hc rmActual f actual _ (nativeUses v))
    (fun _=>rfl) (by norm_num)
  rw [native_denote_of_edges N edge] at network
  have value : N.denote=action p g := by funext x;exact oneCopy_denote p g x
  rw [value] at network
  obtain ⟨q,d,hd,actualQ,equation⟩ := A.descend_upTo phi F _ network
  refine ⟨q,d,hd,actualQ,equation,?_⟩
  rw [←algebraic_complex_iff (RH.mapSignature phi q),←algebraic_complex_iff (RH.mapSignature phi f)]
  change ComplexAffine (RH.mapSignature (A.complexEmbedding phi) q) ↔ ComplexAffine g
  rw [equation]
  exact (affine_complex_scale_iff d hd (action p g)).trans (action_complex_iff p g)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineOrthogonalActual
end
