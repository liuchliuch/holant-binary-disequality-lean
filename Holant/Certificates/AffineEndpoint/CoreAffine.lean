import Holant.Certificates.AffineEndpoint.CoreCovariance

/-! The six affine-preserving cores and exhaustive reduction of the other
literal source cores to the two base cores by exact covariance. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem coreAction_identity (f : Signature AlgebraicComplex n) : coreAction (.inl 0) f=f := by
  have hm : coreMatrix (.inl 0)=Signature.equality := by
    rw [core_identity]
    funext x y
    cases x <;> cases y <;> simp [Signature.equality]
  simp [coreAction,hm]

 theorem coreAction_flip (f : Signature AlgebraicComplex n) :
    coreAction (.inl 1) f=fun x => f (complementWord x) := by
  simp only [coreAction,core_flip,coordinateAction_disequality]

 theorem coreAction_identity_affine {f : Signature AlgebraicComplex n} (hf : Affine f) :
    Affine (coreAction (.inl 0) f) := by simpa only [coreAction_identity] using hf

 theorem coreAction_flip_affine {f : Signature AlgebraicComplex n} (hf : Affine f) :
    Affine (coreAction (.inl 1) f) := by
  rw [coreAction_flip]
  apply hf.precompose
  intro x y
  funext k
  simp only [complementWord,xor_apply,origin]
  cases x k <;> cases y k <;> rfl

 theorem coreAction_hadamard_zero (f : Signature AlgebraicComplex n) :
    coreAction (numberedCore 2) f=walsh f := by
  have hm : coreMatrix (numberedCore 2)=hadamard := by
    change coreMatrix (.inr (.inl 0))=hadamard
    rw [core_hadamard]
    funext x y
    cases x <;> cases y <;> simp [algMat,hadamard]
  rw [coreAction,hm]
  rfl

 theorem coreAction_hadamard_even_affine (j : Fin 4) {f : Signature AlgebraicComplex n}
    (hf : Affine f) : Affine (coreAction (.inr (.inl ⟨2*j.val,by omega⟩)) f) := by
  rw [coreAction_hadamard_even,coreAction_hadamard_zero]
  exact walsh_affine _ (phaseTwist_affine j hf)

 theorem six_cores_affine (k : Fin 18)
    (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=4 ∨ k=6 ∨ k=8)
    {f : Signature AlgebraicComplex n} (hf : Affine f) :
    Affine (coreAction (numberedCore k) f) := by
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · exact coreAction_identity_affine hf
  · exact coreAction_flip_affine hf
  · exact coreAction_hadamard_even_affine 0 hf
  · exact coreAction_hadamard_even_affine 1 hf
  · exact coreAction_hadamard_even_affine 2 hf
  · exact coreAction_hadamard_even_affine 3 hf

/-- Every literal source core either preserves the actual affine class or
has exactly one of the two base actions after a fourth-root input twist and
an optional global output complement. -/
 theorem coreAction_affine_or_base (k : CoreIndex) {f : Signature AlgebraicComplex n}
    (hf : Affine f) :
    Affine (coreAction k f) ∨ ∃ (b : Bool) (j : Fin 4) (c : Bool),
      coreAction k f = fun x =>
        coreAction (numberedCore (baseCore b)) (phaseTwist j f)
          (if c then complementWord x else x) := by
  rcases k with i|i|⟨j,c⟩
  · fin_cases i
    · exact Or.inl (coreAction_identity_affine hf)
    · exact Or.inl (coreAction_flip_affine hf)
  · fin_cases i
    · exact Or.inl (coreAction_hadamard_even_affine 0 hf)
    · exact Or.inr ⟨false,0,false,coreAction_hadamard_odd 0 f⟩
    · exact Or.inl (coreAction_hadamard_even_affine 1 hf)
    · exact Or.inr ⟨false,1,false,coreAction_hadamard_odd 1 f⟩
    · exact Or.inl (coreAction_hadamard_even_affine 2 hf)
    · exact Or.inr ⟨false,2,false,coreAction_hadamard_odd 2 f⟩
    · exact Or.inl (coreAction_hadamard_even_affine 3 hf)
    · exact Or.inr ⟨false,3,false,coreAction_hadamard_odd 3 f⟩
  · cases c
    · exact Or.inr ⟨true,j,false,coreAction_mixed_positive j f⟩
    · exact Or.inr ⟨true,j,true,coreAction_mixed_negative j f⟩

end
end Holant.Certificates.AffineEndpoint
