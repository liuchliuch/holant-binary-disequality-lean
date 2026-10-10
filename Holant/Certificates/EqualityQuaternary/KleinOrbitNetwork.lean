import Holant.Certificates.EqualityQuaternary.KleinOrbitProgram

/-! Every exotic normalization word is an actual one-original-q network.
Its binary labels are the caller's fixed actual representatives; the exact
recorded scalar of the analytic comparison remains explicit.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein.Orbit
open Holant Holant.Marked Holant.Tractable
open Holant.Projective.CyclicDressing
open Holant.Certificates.FourthRootOdd
set_option backward.isDefEq.respectTransparency false

def netAct {F : SignatureFamily Scalar} (reps : Representatives F .exotic) : Op → Network Scalar 4 → Network Scalar 4
  | .dress i j,N => Boundary.attach N i (reps.matrix (auxiliary j))
  | .swap i,N => reorderNetwork N (swapPorts i)
def netRun {F : SignatureFamily Scalar} (reps : Representatives F .exotic) : List Op → Network Scalar 4 → Network Scalar 4
  | [],N => N
  | op::ops,N => netRun reps ops (netAct reps op N)

theorem netAct_denote {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (op : Op) (N : Network Scalar 4) :
    (netAct reps op N).denote=actualAct reps op N.denote := by
  cases op with
  | dress i j => exact Boundary.attach_denote N i _
  | swap i => exact reorderNetwork_denote N _

theorem netRun_denote {F : SignatureFamily Scalar} (reps : Representatives F .exotic)
    (ops : List Op) (N : Network Scalar 4) : (netRun reps ops N).denote=actualRun reps ops N.denote := by
  induction ops generalizing N with
  | nil => rfl
  | cons op ops ih => rw [netRun,ih,netAct_denote]; rfl

theorem netAct_copies {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (op : Op) (N : Network Scalar 4) :
    Counted.copies (netAct reps op N)=Counted.copies N := by
  cases op with
  | dress i j => exact Boundary.attach_copies N i _
  | swap i => rfl

theorem netRun_copies {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (ops : List Op) (N : Network Scalar 4) :
    Counted.copies (netRun reps ops N)=Counted.copies N := by
  induction ops generalizing N with
  | nil => rfl
  | cons op ops ih => rw [netRun,ih,netAct_copies]

theorem netAct_native {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (op : Op)
    {N : Network Scalar 4} (h : Boundary.Native N) : Boundary.Native (netAct reps op N) := by
  cases op with
  | dress i j => exact Boundary.attach_native h i _
  | swap i => exact h

theorem netRun_native {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (ops : List Op)
    {N : Network Scalar 4} (h : Boundary.Native N) : Boundary.Native (netRun reps ops N) := by
  induction ops generalizing N with
  | nil => exact h
  | cons op ops ih => exact ih (netAct_native reps op h)

theorem netAct_labels {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (op : Op)
    {q : Signature Scalar 4} {N : Network Scalar 4} (h : Boundary.CoreLabels q N) :
    Boundary.CoreLabels q (netAct reps op N) := by
  cases op with
  | dress i j => exact Boundary.attach_labels h i _
  | swap i => exact h

theorem netRun_labels {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (ops : List Op)
    {q : Signature Scalar 4} {N : Network Scalar 4} (h : Boundary.CoreLabels q N) :
    Boundary.CoreLabels q (netRun reps ops N) := by
  induction ops generalizing N with
  | nil => exact h
  | cons op ops ih => exact ih (netAct_labels reps op h)

theorem actualAct_realizes {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (op : Op)
    {q : Signature Scalar 4} (h : Gadget.Realizes F .disequality q) :
    Gadget.Realizes F .disequality (actualAct reps op q) := by
  cases op with
  | dress i j => exact realizes_onePort F q _ h (reps.actual _) i
  | swap i => exact Dihedral.CompatibleClosure.realizes_reindex F .disequality q h (swapPorts i).symm

theorem actualRun_realizes {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (ops : List Op)
    {q : Signature Scalar 4} (h : Gadget.Realizes F .disequality q) :
    Gadget.Realizes F .disequality (actualRun reps ops q) := by
  induction ops generalizing q with
  | nil => exact h
  | cons op ops ih => exact ih (actualAct_realizes reps op h)

theorem actualRun_prime {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (ops : List Op)
    {q : Signature Scalar 4} (h : TensorPrime q) : TensorPrime (actualRun reps ops q) := by
  rw [actualRun_scale]
  exact prime_smul (run_prime h ops) _ (programScalar_ne_zero reps ops)

end Holant.Certificates.EqualityQuaternary.Klein.Orbit
