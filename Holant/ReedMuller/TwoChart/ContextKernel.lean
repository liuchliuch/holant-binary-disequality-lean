import Holant.ReedMuller.TwoChart.LocalizedOutput
import Holant.ReedMuller.TwoChart.RelationFiber
import Holant.ReedMuller.CharacterRecognition.Algebra

/-! The literal algebraic localizer tensor, with its exact translated sign.
Its complex character-flat form is proved directly from the relation code. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n m : ℕ}

/-- The algebraic sign of χ(x−p), on precisely the original-coordinate
relation (x−p,y)=(s+j,φ(s)). -/
def contextKernel (S J : BinaryCode n) (phi : S ≃ₗ[ZMod 2] BinaryVector m)
    (p : BinaryVector n) (chi : Character n) : Signature AlgebraicComplex (n+m) :=
  fun z => if vectorWord z-joinVector p 0∈relationCode S J phi then
    fourthRootPhase (evenLift (chi (leftVector (vectorWord z)-p))) else 0

@[simp] theorem vectorWord_addCases (x : Word n) (y : Word m) :
    vectorWord (Fin.addCases x y)=joinVector (vectorWord x) (vectorWord y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [vectorWord,joinVector]

theorem contextKernel_join (S J : BinaryCode n) (phi : S ≃ₗ[ZMod 2] BinaryVector m)
    (p : BinaryVector n) (chi : Character n) (x : Word n) (y : Word m) :
    contextKernel S J phi p chi (Fin.addCases x y)=
      if joinVector (vectorWord x) (vectorWord y)-joinVector p 0∈relationCode S J phi then
        fourthRootPhase (evenLift (chi (vectorWord x-p))) else 0 := by
  simp only [contextKernel,vectorWord_addCases,left_join]

/-- The canonical supported input/output pair has coefficient exactly one. -/
theorem contextKernel_at_shift (S J : BinaryCode n)
    (phi : S ≃ₗ[ZMod 2] BinaryVector m) (p : BinaryVector n) (chi : Character n) :
    contextKernel S J phi p chi (Fin.addCases (wordVector p) (wordVector 0))=1 := by
  simp [contextKernel_join]

/-- A coefficient vanishes exactly outside its genuine isotropic fiber. -/
theorem contextKernel_zero_iff (S J : BinaryCode n)
    (phi : S ≃ₗ[ZMod 2] BinaryVector m) (p : BinaryVector n) (chi : Character n)
    (x : Word n) (y : Word m) :
    contextKernel S J phi p chi (Fin.addCases x y)=0 ↔
      vectorWord x-p-(phi.symm (vectorWord y)).val∉J := by
  rw [contextKernel_join,relation_coset_iff]
  split_ifs with h
  · constructor
    · intro hz
      exact False.elim (fourthRootPhase_ne_zero _ hz)
    · intro hn
      exact False.elim (hn h)
  · simp [h]

/-- Translating the sign contributes the explicit nonzero scalar sign(−χ(p)). -/
theorem contextKernel_complex (S J : BinaryCode n) (phi : S ≃ₗ[ZMod 2] BinaryVector m)
    (p : BinaryVector n) (chi : Character n) :
    (fun z => (contextKernel S J phi p chi z:ℂ))=
      signature (sign (-chi p)) (joinVector p 0) (relationCode S J phi)
        (chi.comp leftLinear) := by
  funext z
  unfold contextKernel signature value
  split_ifs
  · change CharacterRecognition.root (evenLift (chi (leftVector (vectorWord z)-p)))=_
    rw [CharacterRecognition.root_evenLift,map_sub,sub_eq_add_neg,sign_add]
    simp only [LinearMap.comp_apply,leftLinear_apply]
    exact mul_comm _ _
  · rfl

theorem contextKernel_nonzeroFlat (S J : BinaryCode n)
    (phi : S ≃ₗ[ZMod 2] BinaryVector m)
    (hphi : ∀s t : S,dot (phi s) (phi t)=dot s.val t.val)
    (hJ : ∀j∈J,∀k∈J,dot j k=0)
    (horth : ∀s∈S,∀j∈J,dot s j=0)
    (hdim : m+2*Module.finrank (ZMod 2) J=n)
    (p : BinaryVector n) (chi : Character n) :
    NonzeroFlat (fun z => (contextKernel S J phi p chi z:ℂ)) := by
  refine ⟨Units.mk0 (sign (-chi p)) (sign_nonzero _),joinVector p 0,
    relationCode S J phi,chi.comp leftLinear,
    relationCode_selfDual S J phi hphi hJ horth hdim,?_⟩
  exact contextKernel_complex S J phi p chi

variable {F : RadonAccess.RadonFrame n} {C₀ C₁ : Chart (n-2)}

def LocalizingData.context (L : LocalizingData F C₀ C₁) :
    Signature AlgebraicComplex (n+L.outputSize) :=
  contextKernel L.space L.isotropic L.coordinates L.shift L.character

theorem LocalizingData.context_nonzeroFlat (L : LocalizingData F C₀ C₁) :
    NonzeroFlat (fun z => (L.context z:ℂ)) :=
  contextKernel_nonzeroFlat L.space L.isotropic L.coordinates L.isometry
    L.selfOrthogonal L.orthogonal L.halfDimension L.shift L.character

theorem LocalizingData.context_ne_zero (L : LocalizingData F C₀ C₁) : L.context≠0 := by
  intro hz
  have hn := nonzeroFlat_nonzero _ L.context_nonzeroFlat
  apply hn
  funext z
  simp [hz]

end
end Holant.ReedMuller.TwoChart
