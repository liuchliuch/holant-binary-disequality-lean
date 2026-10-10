import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixCrossCoordinates
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixFiniteCertificate
import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist

/-! The verified finite Bell certificate classifies the actual anchored real
source. Its two reducible outputs carry explicit proper tensor splits. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixRealClassification
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
namespace F
export GlobalCloseCompletionKleinSixFiniteForms (tensor factor_first factor_second h6_first h6_second flip swapBlocks)
end F
namespace C
export GlobalCloseCompletionKleinSixBellCoordinates (Normal)
end C
namespace Rec
export GlobalCloseCompletionKleinSixReconstruction (form phasePack)
end Rec
namespace X
export GlobalCloseCompletionKleinSixCrossCoordinates (order safe)
end X
namespace D
export GlobalCloseCompletionKleinSixFiniteData (allowed)
end D
namespace H
export GlobalCloseCompletionKleinH6RMBell (core)
end H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def firstOrder : Equiv.Perm (Fin 6) where
  toFun := ![2,3,0,1,4,5]
  invFun := ![2,3,0,1,4,5]
  left_inv := by decide
  right_inv := by decide

def secondOrder : Equiv.Perm (Fin 6) where
  toFun := ![4,5,0,1,2,3]
  invFun := ![2,3,4,5,0,1]
  left_inv := by decide
  right_inv := by decide

variable {K : Type*} [Field K]

theorem first_split (s : Fin 8) (d : K) :
    ∃a b : AnySignature K,Nonempty (ProperSplit ⟨6,d • F.tensor 1 2 3 s⟩ a b) := by
  refine ⟨⟨2,fun x=>Signature.equality (x 0) (x 1)⟩,
    ⟨4,fun x=>d*F.tensor 1 2 3 s ![x 0,x 1,false,false,x 2,x 3]⟩,⟨?_⟩⟩
  refine {
    left_pos := by norm_num
    right_pos := by norm_num
    ports := (finSumFinEquiv (m:=2) (n:=4)).trans firstOrder
    scale := 1
    equation := ?_ }
  funext x
  change d*F.tensor 1 2 3 s x=1*(Signature.equality (x 2) (x 3)*
    (d*F.tensor 1 2 3 s ![x 0,x 1,false,false,x 4,x 5]))
  rw [F.factor_first s x]
  ring

theorem second_split (s : Fin 8) (d : K) :
    ∃a b : AnySignature K,Nonempty (ProperSplit ⟨6,d • F.tensor 4 8 12 s⟩ a b) := by
  refine ⟨⟨2,fun x=>Signature.equality (x 0) (x 1)⟩,
    ⟨4,fun x=>d*F.tensor 4 8 12 s ![x 0,x 1,x 2,x 3,false,false]⟩,⟨?_⟩⟩
  refine {
    left_pos := by norm_num
    right_pos := by norm_num
    ports := (finSumFinEquiv (m:=2) (n:=4)).trans secondOrder
    scale := 1
    equation := ?_ }
  funext x
  change d*F.tensor 4 8 12 s x=1*(Signature.equality (x 4) (x 5)*
    (d*F.tensor 4 8 12 s ![x 0,x 1,x 2,x 3,false,false]))
  rw [F.factor_second s x]
  ring

theorem classify (f : Signature ℝ 6) (R : C.Normal f) (anchor : R.label 0=0)
    (cross : ∀j : Fin 4,Nonempty (C.Normal (Tensor.reindex (X.order j) f))) :
    (∃a b : AnySignature ℝ,Nonempty (ProperSplit ⟨6,f⟩ a b)) ∨
    ∃p : Equiv.Perm (Fin 6),∃d : ℝ,d≠0 ∧ f=d • Tensor.reindex p H.core := by
  have o01 := R.orthogonal 0 1 (by decide)
  have o02 := R.orthogonal 0 2 (by decide)
  have o03 := R.orthogonal 0 3 (by decide)
  have o12 := R.orthogonal 1 2 (by decide)
  have o13 := R.orthogonal 1 3 (by decide)
  have o23 := R.orthogonal 2 3 (by decide)
  rw [anchor] at o01 o02 o03
  have probes (j k : Fin 4) : GlobalCloseCompletionKleinSixPacked.safe
      (GlobalCloseCompletionKleinSixFiniteData.card (R.label 1) (R.label 2) (R.label 3)
        (Rec.phasePack R.phase) j k)=true := by
    obtain ⟨T⟩ := cross j
    exact X.safe f R anchor j T k
  have accepted : GlobalCloseCompletionKleinSixPacked.accepted
      (R.label 1) (R.label 2) (R.label 3) (Rec.phasePack R.phase)=true := by
    simp only [GlobalCloseCompletionKleinSixPacked.accepted,o01,o02,o03,o12,o13,o23,
      Bool.true_and,probes,implies_true,decide_true]
  have allowed := GlobalCloseCompletionKleinSixFiniteCertificate.certificate _ _ _ _ accepted
  have form := Rec.form f R anchor
  rcases allowed with ⟨h1,h2,h3⟩|⟨h1,h2,h3⟩|⟨h1,h2,h3⟩|⟨h1,h2,h3⟩
  · left
    rw [h1,h2,h3] at form
    rw [form]
    exact first_split _ _
  · left
    rw [h1,h2,h3] at form
    rw [form]
    exact second_split _ _
  · right
    refine ⟨F.flip (Rec.phasePack R.phase),R.scale/2,div_ne_zero R.scale_nonzero (by norm_num),?_⟩
    rwa [h1,h2,h3,F.h6_first] at form
  · right
    refine ⟨(F.flip (Rec.phasePack R.phase)).trans F.swapBlocks,R.scale/2,
      div_ne_zero R.scale_nonzero (by norm_num),?_⟩
    rwa [h1,h2,h3,F.h6_second] at form


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixRealClassification
end
