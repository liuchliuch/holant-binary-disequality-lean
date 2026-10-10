import Holant.Proofs.Hardness.EOBinaryConjugateProgramme
import Holant.Proofs.Hardness.EOBinaryPlanePositiveCounting
import Holant.Proofs.Hardness.EOBinaryPlaneCandidateFull
import Holant.Proofs.Hardness.EOBinaryPlaneCandidateAccess

/-! Complete same-original-field source for a nonexceptional full binary
plane. The five-choice coefficient producer, positive Gram source, conjugate
interpolation, and physical candidate replacement are all composed here. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFullSupportKernelSource
open Holant Holant.Algebraic Holant.Complexity Computability
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
namespace P
export EOBinaryPlanePositive (candidate choice Good exceptional choice_good)
end P
namespace G
export EOBinaryPlaneGram (determinant)
end G
namespace N
export EOBinaryPlaneFullSupportImages (table table_image)
end N
namespace A
export EOBinaryPlaneCandidateGadgets (output)
end A
namespace V
export RealDenseSignTwistStageAccess (value)
end V
namespace Q
export ExactTwoChainQueries (targetEncoding)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] [StarRing L]
variable {d e : ℕ} (F : FixedField K d) (E : FixedField L e)
variable (into : K→ₐ[ℚ]L) (ambient : L→+*ℂ) (hstar : ∀x,ambient (star x)=star (ambient x))
variable (f : Signature K 2)

def image : Signature ℂ 2 := fun z=>ambient (into (f z))
def a : ℂ := image into ambient f ![false,false]
def b : ℂ := image into ambient f ![false,true]
def c : ℂ := image into ambient f ![true,false]
def dval : ℂ := image into ambient f ![true,true]
def kind : Fin 5 := P.choice (a into ambient f) (b into ambient f) (c into ambient f) (dval into ambient f)
def chosen : Signature K 2 := A.output f (kind into ambient f)
def positive : Signature ℝ 2 := P.candidate (a into ambient f) (b into ambient f)
  (c into ambient f) (dval into ambient f) (kind into ambient f)
def gram : Signature L 2 := N.table into.toRingHom f (kind into ambient f)

variable (hf : ∀z,f z≠0)
variable (hd : G.determinant (a into ambient f) (b into ambient f) (c into ambient f) (dval into ambient f)≠0)
variable (he : ¬P.exceptional (a into ambient f) (b into ambient f) (c into ambient f) (dval into ambient f))

include hf in
theorem image_full : ∀z,image into ambient f z≠0 := by
  intro z hz
  apply hf z
  apply into.injective
  apply ambient.injective
  change ambient (into (f z))=ambient (into 0)
  simpa only [image,map_zero] using hz

include hf he in
omit [StarRing L] in
theorem chosen_full : ∀z,chosen into ambient f z≠0 :=
  EOBinaryPlaneCandidateFull.selected_mapped_full (ambient.comp into.toRingHom) f hf he

include hf hd he in
theorem positive_good : P.Good (positive into ambient f) :=
  P.choice_good _ _ _ _ (image_full into ambient f hf _) (image_full into ambient f hf _)
    (image_full into ambient f hf _) hd he

include hstar in
theorem gram_image : ∀z,ambient (gram into ambient f z)=(positive into ambient f z : ℂ) :=
  congrFun (N.table_image into.toRingHom ambient hstar f (kind into ambient f))

variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    Q.targetEncoding F.encoding count (V.value (EOBinaryPlaneCore.lift f)) := by
  let p := EOBinaryPlanePositiveCounting.source E (gram into ambient f) ambient (positive into ambient f)
    (positive_good into ambient f hf hd he) (gram_image into ambient hstar f) w
  have hp : BinaryCSPProgrammeNative.targetValue E (EOBinaryPlaneCore.lift (gram into ambient f))=
      V.value (EOBinaryPlaneCore.lift (gram into ambient f)) :=
    EOBinaryPlanePositiveSource.native_eq E _
  rw [hp] at p
  let g := EOBinaryPlaneGramAccess.source E (fun z=>into (chosen into ambient f z))
    (fun z=>star (into (chosen into ambient f z)))
  let m := EOBinaryConjugateProgramme.controlled F E into (chosen into ambient f)
    (chosen_full into ambient f hf he)
  let a := EOBinaryPlaneCandidateAccess.source F f (kind into ambient f)
  exact C.composeControlled (C.composeControlled (C.composeControlled p g) m) a

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFullSupportKernelSource
