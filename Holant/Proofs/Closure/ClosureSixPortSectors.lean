import Holant.Proofs.Closure.ClosureSixPortComplementary
import Holant.Proofs.Closure.ClosureRootPencilClassification

/-! NEW UNVERIFIED closed sector producer from the actual ordered root deck.
The fixed ruling and binary classification are internally constructed. Zero
sectors remain in the genuine proportional branch for separate Z/* assembly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Projective

inductive SectorClassification (m : ℕ) (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool)
  | proportional (dependent : DependentEndpoints (sliceSix h e p false) (sliceSix h e p true))
  | complementary (data : ComplementarySector m h e p)

def complementaryOfClassification {m : ℕ} (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (C : ClosureRootPencil.Complementary m (sliceSix h e p false) (sliceSix h e p true)) :
    ComplementarySector m h e p where
  ports := C.ruling.ports
  fixed := C.ruling.fixed
  rooted := C.ruling.fixedRoot
  parity := C.parity
  orientation := C.orientation
  coefficient := C.coefficient
  nonzero := C.coefficient_nonzero
  endpoints := by
    intro a x
    have endpoint := congrFun (C.endpoint a) x
    cases a <;> simpa only [Bool.false_eq_true,ite_false,ite_true,ClosureRootPencil.pairTensor] using endpoint

/-- Variable dependence lifts to genuine dependence of the WHOLE raw
endpoints, preserving the same fixed binary, order and scalar. -/
theorem ruling_endpoint_dependent {m : ℕ} {U V : Signature ℂ 4} (R : ClosureRootPencil.Ruling m U V)
    (relation : BinaryProportional R.variable0 R.variable1) : DependentEndpoints U V := by
  rcases (binaryProportional_iff _ _).mp relation with ⟨c,he⟩ | ⟨c,he⟩
  · left
    refine ⟨c,?_⟩
    funext x
    have e0 := congrFun R.endpoint0 x
    have e1 := congrFun R.endpoint1 x
    change V x = c * U x
    rw [e0,e1,he]
    simp only [ClosureRootPencil.pairTensor,Pi.smul_apply,smul_eq_mul]
    ring
  · right
    refine ⟨c,?_⟩
    funext x
    have e0 := congrFun R.endpoint0 x
    have e1 := congrFun R.endpoint1 x
    change U x = c * V x
    rw [e0,e1,he]
    simp only [ClosureRootPencil.pairTensor,Pi.smul_apply,smul_eq_mul]
    ring

/-- No sector type, support atlas, alignment or desired factor is supplied. -/
def classifySector {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ 6) (deck : OrderedRootDeck m h)
    (e : Equiv.Perm (Fin 6)) (p : Bool) : SectorClassification m h e p := by
  let classification := ClosureRootPencil.fromRootMatching hm
    (sliceSix h e p false) (sliceSix h e p true) (by
      intro t ht
      have same : ClosureRootPencil.pencil (sliceSix h e p false) (sliceSix h e p true) t =
          phaseCard h e p t := by funext x; rfl
      rw [same]
      exact deck e p t ht)
  cases classification with
  | proportional R relation => exact .proportional (ruling_endpoint_dependent R relation)
  | complementary C => exact .complementary (complementaryOfClassification h e p C)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
