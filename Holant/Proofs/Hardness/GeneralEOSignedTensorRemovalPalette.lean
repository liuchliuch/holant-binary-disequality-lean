import Holant.Proofs.Hardness.GeneralOddHigherResidueQuaternaryMacro

/-! Literal palette transport for scalar macro removal. Equality of full
arity functions and ordered signature rows preserves the input codec, command
stream and every length/control certificate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedTensorRemovalPalette
open Computability Holant Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K]
variable {d s : ℕ} (F : FixedField K d)

abbrev value {ar : ℕ→ℕ} (H : (i : Fin s)→Signature K (ar i.val))
    (q : ExactSignatureTables.Input s 1 ar) : K :=
  (q.val.realize q.property H (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0

def revalue {α β γ δ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ed : Encoding δ Bool} {f f' : α→β} {g : γ→δ}
    (r : LengthControlledOracleReduction ea eb ec ed f g) (h : ∀x,f x=f' x) :
    LengthControlledOracleReduction ea eb ec ed f' g where
  reduction := {
    machine := r.reduction.machine
    time := r.reduction.time
    correct := fun oracle ho x => by rw [←h x]; exact r.reduction.correct oracle ho x }
  targetOutput := r.targetOutput
  queryBound := r.queryBound
  safeQuery := r.safeQuery

/-- No relabeling, field equality or extra oracle query occurs in this step. -/
def retype {ar br : ℕ→ℕ} (h : ar=br)
    (H : (i : Fin s)→Signature K (ar i.val))
    (J : (i : Fin s)→Signature K (br i.val))
    (rows : ∀i,(⟨ar i.val,H i⟩ : AnySignature K)=⟨br i.val,J i⟩)
    {γ δ : Type} {ec : Encoding γ Bool} {ed : Encoding δ Bool} {g : γ→δ}
    (r : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding s 1 ar)
      F.encoding ec ed (value H) g) :
    LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding s 1 br)
      F.encoding ec ed (value J) g := by
  subst br
  have he : H=J := by
    funext i
    exact eq_of_heq (Sigma.mk.inj_iff.mp (rows i)).2
  subst J
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedTensorRemovalPalette
