import Holant.Tractable.SymmetricBinaryPullback.LocalAffine

/-! Both literal unary pins force any shared local-affine basis to be
monomial. The actual ordinary edge then restricts its two nonzero entries to
an eighth-root ratio. Genuine higher-arity local-affine rows remain allowed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorLocalBasis
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

/-- A full unary cannot satisfy both supported local twists. -/
theorem localAffine_unary_zero (u : Signature AlgebraicComplex 1) (hu : LocalAffine u) :
    u ![false]=0 ∨ u ![true]=0 := by
  by_cases h0 : u ![false]=0
  · exact Or.inl h0
  by_cases h1 : u ![true]=0
  · exact Or.inr h1
  exfalso
  have a0 := hu ![false] h0
  have a1 := hu ![true] h1
  have p0 := a0.fourth_power_eq ![false] ![true]
    (by simpa [localTwist_apply,Fin.prod_univ_one] using h0)
    (by simpa [localTwist_apply,Fin.prod_univ_one] using h1)
  have p1 := a1.fourth_power_eq ![false] ![true]
    (by simpa [localTwist_apply,Fin.prod_univ_one] using h0)
    (by simpa [localTwist_apply,Fin.prod_univ_one] using mul_ne_zero zetaEight_ne_zero h1)
  have hp0 : u ![false]^4=u ![true]^4 := by
    simpa [localTwist_apply,Fin.prod_univ_one] using p0
  have hp1 : u ![false]^4= -u ![true]^4 := by
    simpa [localTwist_apply,Fin.prod_univ_one,mul_pow] using p1
  have hz : u ![true]^4=0 := by linear_combination (hp1-hp0)/2
  exact pow_ne_zero 4 h1 hz

def pin (b : Bool) : Signature AlgebraicComplex 1 := fun x=>if x 0=b then 1 else 0

theorem pin_action (B : InvertibleKernel) (b : Bool) (x : Fin 1 → Bool) :
    B.action (pin b) x=B.matrix (x 0) b := by
  unfold InvertibleKernel.action Signature.coordinateAction
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp only [Fin.prod_univ_one,Equiv.funUnique_symm_apply,pin]
  cases b <;> simp

def Monomial (M : Kernel AlgebraicComplex) : Prop :=
  (M false true=0 ∧ M true false=0) ∨ (M false false=0 ∧ M true true=0)

theorem monomial_of_pins (B : InvertibleKernel)
    (h0 : LocalAffine (B.action (pin false))) (h1 : LocalAffine (B.action (pin true))) : Monomial B.matrix := by
  have z0 := localAffine_unary_zero _ h0
  have z1 := localAffine_unary_zero _ h1
  simp only [pin_action,Matrix.cons_val_zero] at z0 z1
  have hn := determinant_ne_zero B
  rcases z0 with h00|h10 <;> rcases z1 with h01|h11
  · exact False.elim (hn (by simp [determinant,h00,h01]))
  · exact Or.inr ⟨h00,h11⟩
  · exact Or.inl ⟨h01,h10⟩
  · exact False.elim (hn (by simp [determinant,h10,h11]))

theorem monomial_of_inverse (B : InvertibleKernel) (h : Monomial B.inverse) : Monomial B.matrix := by
  have hn := determinant_ne_zero B.symm
  change determinant B.inverse≠0 at hn
  rcases h with ⟨h01,h10⟩|⟨h00,h11⟩
  · have hd : B.inverse false false*B.inverse true true≠0 := by simpa [determinant,h01,h10] using hn
    obtain ⟨h00,h11⟩ := mul_ne_zero_iff.mp hd
    have he01 := congrFun (congrFun B.inverse_matrix false) true
    have he10 := congrFun (congrFun B.inverse_matrix true) false
    simp [Kernel.mul_apply,h01,h10,Signature.equality] at he01 he10
    exact Or.inl ⟨he01.resolve_left h00,he10.resolve_left h11⟩
  · have hd : B.inverse false true*B.inverse true false≠0 := by
      intro hz
      exact hn (by simp [determinant,h00,h11,hz])
    obtain ⟨h01,h10⟩ := mul_ne_zero_iff.mp hd
    have he11 := congrFun (congrFun B.inverse_matrix false) true
    have he00 := congrFun (congrFun B.inverse_matrix true) false
    simp [Kernel.mul_apply,h00,h11,Signature.equality] at he11 he00
    exact Or.inr ⟨he00.resolve_left h10,he11.resolve_left h01⟩

theorem common_basis_monomial {H : SignatureFamily AlgebraicComplex} (B : InvertibleKernel)
    (h0 : (⟨1,pin false⟩ : AnySignature AlgebraicComplex)∈H)
    (h1 : (⟨1,pin true⟩ : AnySignature AlgebraicComplex)∈H)
    (hB : IsCommonBasis localAffineClass H B) : Monomial B.matrix ∧ Monomial B.inverse := by
  have hi : Monomial B.inverse := monomial_of_pins B.symm (hB.2 _ h0) (hB.2 _ h1)
  exact ⟨monomial_of_inverse B hi,hi⟩

private theorem diagonal_nonzero (B : InvertibleKernel) (h01 : B.matrix false true=0)
    (h10 : B.matrix true false=0) : B.matrix false false≠0 ∧ B.matrix true true≠0 := by
  apply mul_ne_zero_iff.mp
  simpa [determinant,h01,h10] using determinant_ne_zero B

private theorem antidiagonal_nonzero (B : InvertibleKernel) (h00 : B.matrix false false=0)
    (h11 : B.matrix true true=0) : B.matrix false true≠0 ∧ B.matrix true false≠0 := by
  apply mul_ne_zero_iff.mp
  intro hz
  exact determinant_ne_zero B (by simp [determinant,h00,h11,hz])

/-- The common edge's own local-affine certificate forces an eighth-root
ratio; this is stronger than the sixteenth-root condition from Eq4 alone. -/
theorem common_basis_normal_form {H : SignatureFamily AlgebraicComplex} (B : InvertibleKernel)
    (h0 : (⟨1,pin false⟩ : AnySignature AlgebraicComplex)∈H)
    (h1 : (⟨1,pin true⟩ : AnySignature AlgebraicComplex)∈H)
    (hB : IsCommonBasis localAffineClass H B) :
    ∃c d : AlgebraicComplex,c≠0 ∧ d≠0 ∧ c^8=d^8 ∧
      (B.matrix=diagonal c d ∨ B.matrix=antidiagonal c d) := by
  have hE : LocalAffine (kernelSignature (Kernel.pullback Signature.equality B.matrix)) := hB.1
  rcases (common_basis_monomial B h0 h1 hB).1 with ⟨h01,h10⟩|⟨h00,h11⟩
  · obtain ⟨hc,hd⟩ := diagonal_nonzero B h01 h10
    have he : B.matrix=diagonal (B.matrix false false) (B.matrix true true) := by
      funext a b
      cases a <;> cases b <;> simp [diagonal,h01,h10]
    have edge : Kernel.pullback Signature.equality B.matrix=
        diagonal (B.matrix false false^2) (B.matrix true true^2) := by
      funext a b
      cases a <;> cases b <;> simp [Kernel.pullback,Kernel.mul_apply,Kernel.transpose,h01,h10,diagonal,pow_two]
    rw [edge] at hE
    have aff := hE (fun _=>false) (by simpa [kernelSignature,diagonal] using pow_ne_zero 2 hc)
    rw [localTwist_false] at aff
    have hp := aff.fourth_power_eq (fun _=>false) (fun _=>true)
      (by simpa [kernelSignature,diagonal] using pow_ne_zero 2 hc)
      (by simpa [kernelSignature,diagonal] using pow_ne_zero 2 hd)
    refine ⟨_,_,hc,hd,?_,Or.inl he⟩
    simpa only [kernelSignature,diagonal,ite_true,Bool.false_eq_true,ite_false,←pow_mul] using hp
  · obtain ⟨hc,hd⟩ := antidiagonal_nonzero B h00 h11
    have he : B.matrix=antidiagonal (B.matrix false true) (B.matrix true false) := by
      funext a b
      cases a <;> cases b <;> simp [antidiagonal,h00,h11]
    have edge : Kernel.pullback Signature.equality B.matrix=
        diagonal (B.matrix true false^2) (B.matrix false true^2) := by
      funext a b
      cases a <;> cases b <;> simp [Kernel.pullback,Kernel.mul_apply,Kernel.transpose,h00,h11,diagonal,pow_two]
    rw [edge] at hE
    have aff := hE (fun _=>false) (by simpa [kernelSignature,diagonal] using pow_ne_zero 2 hd)
    rw [localTwist_false] at aff
    have hp := aff.fourth_power_eq (fun _=>true) (fun _=>false)
      (by simpa [kernelSignature,diagonal] using pow_ne_zero 2 hc)
      (by simpa [kernelSignature,diagonal] using pow_ne_zero 2 hd)
    refine ⟨_,_,hc,hd,?_,Or.inr he⟩
    simpa only [kernelSignature,diagonal,ite_true,Bool.false_eq_true,ite_false,←pow_mul] using hp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorLocalBasis
