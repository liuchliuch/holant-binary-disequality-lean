import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionRecipe
import Holant.ReedMuller.AffinePatching.ReconstructionSupport

/-! An actual affine Boolean retraction onto the internally obtained linear
support. It extends an arbitrary sparse nonaffine row to a full nonaffine row,
while retaining the literal finite support equations needed to recover it. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionRetraction
open Holant Holant.Tractable
namespace S
export GeneralEOPairedFamilyExtractionSupport (origin xor XorClosed)
end S
namespace A
export TwoTranslate (IsAffineMap)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ} (f : Signature AlgebraicComplex n)
variable (h0 : f S.origin≠0) (hx : S.XorClosed f)

include h0 hx in
theorem exists_retraction : ∃(E : AffineSystem n) (p : (Fin n → Bool) → (Fin n → Bool)),
    A.IsAffineMap p ∧ p S.origin=S.origin ∧
    (∀x,f (p x)≠0) ∧ (∀x,f x≠0 → p x=x) ∧ (∀x,E.Holds x ↔ f x≠0) := by
  obtain ⟨E,p,hp,hfull,hfix,hE⟩ :=
    Holant.ReedMuller.AffinePatching.exists_support_retraction f S.origin h0
      (fun x y z hfx hfy hfz => hx (S.xor x y) z (hx x y hfx hfy) hfz)
  exact ⟨E,p,hp,hfix S.origin h0,hfull,hfix,hE⟩

def system : AffineSystem n := Classical.choose (exists_retraction f h0 hx)
def retraction : (Fin n → Bool) → (Fin n → Bool) :=
  Classical.choose (Classical.choose_spec (exists_retraction f h0 hx))

theorem spec : A.IsAffineMap (retraction f h0 hx) ∧
    retraction f h0 hx S.origin=S.origin ∧
    (∀x,f (retraction f h0 hx x)≠0) ∧
    (∀x,f x≠0 → retraction f h0 hx x=x) ∧
    (∀x,(system f h0 hx).Holds x ↔ f x≠0) :=
  Classical.choose_spec (Classical.choose_spec (exists_retraction f h0 hx))

def full : Signature AlgebraicComplex n := fun x=>f (retraction f h0 hx x)

theorem full_nonzero (x : Fin n → Bool) : full f h0 hx x≠0 := (spec f h0 hx).2.2.1 x

theorem retraction_xor (x y : Fin n → Bool) :
    retraction f h0 hx (S.xor x y)=S.xor (retraction f h0 hx x) (retraction f h0 hx y) := by
  have h := (spec f h0 hx).1 x y
  have hz : retraction f h0 hx (AffinePhase.origin n)=AffinePhase.origin n := (spec f h0 hx).2.1
  rw [hz] at h
  have he (a b : Fin n → Bool) : S.xor a b=AffinePhase.xor a b := by funext j; rfl
  rw [he,he]
  simpa only [AffinePhase.xor_origin] using h

theorem recover (x : Fin n → Bool) :
    (if (system f h0 hx).Holds x then full f h0 hx x else 0)=f x := by
  by_cases hf : f x=0
  · simp only [(spec f h0 hx).2.2.2.2 x,hf,ne_eq,not_true_eq_false,ite_false]
  · simp only [(spec f h0 hx).2.2.2.2 x,ne_eq,hf,not_false_eq_true,ite_true]
    exact congrArg f ((spec f h0 hx).2.2.2.1 x hf)

theorem full_not_affine (ha : ¬Affine f) : ¬Affine (full f h0 hx) := by
  intro h
  have hh := h.restrict (system f h0 hx)
  have he : (fun x => if (system f h0 hx).Holds x then full f h0 hx x else 0)=f :=
    funext (recover f h0 hx)
  exact ha (he ▸ hh)

theorem full_fourth (hp : GeneralEOPairedFamilyExtractionWeight.CommonFourthSupport f)
    (x : Fin n → Bool) : (full f h0 hx x)^4=(full f h0 hx S.origin)^4 := by
  change f (retraction f h0 hx x)^4=f (retraction f h0 hx S.origin)^4
  rw [(spec f h0 hx).2.1]
  exact hp _ ((spec f h0 hx).2.2.1 x)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionRetraction
