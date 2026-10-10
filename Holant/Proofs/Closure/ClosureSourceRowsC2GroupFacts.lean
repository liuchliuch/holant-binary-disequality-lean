import Holant.Proofs.FiniteGroups.Stabilization.DirectScalars

/-! Light extraction of unchanged generic actual-I/native-X key facts.
No physical row, retained catalogue or Interface dependency is imported. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.OpenNetworkComposition
variable {L : Type*} [Field L]

theorem identity_actual (F : SignatureFamily L) (hI : RetainsIdentity F) :
    ActualNonsingular F (1 : Binary (K:=L)) := by
  refine ⟨?_,by simp⟩
  have hr := Gadget.realizes_of_mem F .disequality OrdinaryNormalization.identitySignature hI
  have he : OrdinaryNormalization.identitySignature =
      Holant.Projective.BoundedTorsion.binarySignature (1 : Binary (K:=L)) := by
    funext x
    simp [OrdinaryNormalization.identitySignature,Holant.Projective.BoundedTorsion.binarySignature,
      Matrix.one_apply,Signature.equality]
  exact he ▸ hr

def markedKey (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) : completeGroup F torsion := by
  let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (X : Binary (K:=L)) det_X_ne_zero
  refine ⟨pglMk L U, U, ?_, rfl⟩
  refine ⟨(1 : Binary (K:=L)),identity_actual F hI,1,one_ne_zero,?_⟩
  change X = 1 • transfer (1 : Binary (K:=L))
  simp [transfer]

@[simp] theorem markedKey_class (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) :
    pglToProjectiveClass (markedKey F torsion hI).val = projectiveClass (X : Binary (K:=L)) := rfl

theorem markedKey_ne_one (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) : markedKey F torsion hI ≠ 1 := by
  intro he
  have hc := congrArg (fun j : completeGroup F torsion => pglToProjectiveClass j.val) he
  change projectiveClass (X : Binary (K:=L)) = projectiveClass (1 : Binary (K:=L)) at hc
  obtain ⟨c,_,hm⟩ := projectiveClass_eq_iff.mp hc
  have hoff := congrFun (congrFun hm false) true
  simpa [X,Matrix.smul_apply,Matrix.one_apply,Signature.disequality] using hoff

theorem representative_marked (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) :
    ∃ c : L, c ≠ 0 ∧ actualRepresentative F torsion (markedKey F torsion hI) =
      c • (1 : Binary (K:=L)) := by
  have hp := (actualRepresentative_class F torsion (markedKey F torsion hI)).trans
    (markedKey_class F torsion hI)
  obtain ⟨c,hc,he⟩ := projectiveClass_eq_iff.mp hp
  refine ⟨c,hc,?_⟩
  have hh := congrArg (fun B : Binary (K:=L) => B * X) he
  simpa only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using hh

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
