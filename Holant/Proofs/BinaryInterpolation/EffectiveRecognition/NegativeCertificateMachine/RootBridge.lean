import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.DefectProgram


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.RootBridge
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open ComplexIsolation.CertificateMachine
open CommonFieldMachine
open Holant.LocalDrafts.Tractability.AffineMachine

def relationCode (c : List ℚ) : RationalPolynomialCode :=
  (c.length,1)::Coordinates.tab c.length (fun i => (i,-c.getD i 0))

theorem relationCode_ofFn {d : ℕ} (c : PowerArithmetic.Vector d) :
    relationCode (List.ofFn c) = CommonPrimitive.relationCode c := by
  simp [relationCode,CommonPrimitive.relationCode,Coordinates.tab_ofFn,getD_ofFn]

noncomputable def relationTerm : Computes (pairEncoding coordinatesEncoding UnaryBinary.unaryEncoding)
    ComplexIsolation.CertificateMachine.termEncoding (fun p => (p.2,-p.1.getD p.2 0)) := by
  let c := Wiring.firstComputes coordinatesEncoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes coordinatesEncoding UnaryBinary.unaryEncoding
  let q := (AccessPrograms.get rationalEncoding 0 c i).andThen
    Holant.LocalDrafts.TraversalCompletion.RationalLP.Comparison.rationalNegate
  exact pairComputes (i.andThen UnaryBinary.computes) q

noncomputable def relationComputes : Computes coordinatesEncoding
    ComplexIsolation.CertificateMachine.polynomialEncoding relationCode := by
  let n := WireLists.lengthComputes rationalEncoding
  let leading := (pairComputes (n.andThen UnaryBinary.computes)
    (constantComputes coordinatesEncoding rationalEncoding 1)).andThen
      (Lists.singleton ComplexIsolation.CertificateMachine.termEncoding)
  let tail := WireLists.tabulate coordinatesEncoding ComplexIsolation.CertificateMachine.termEncoding
    List.length n (fun c i => (i,-c.getD i 0)) relationTerm
  exact congrComputes ((pairComputes leading tail).andThen
    (WireLists.append ComplexIsolation.CertificateMachine.termEncoding)) (fun c => rfl)

def sourceBox (t : ComplexIsolation.Certificate) : RationalBox :=
  ⟨⟨t.center.1,t.radius⟩,⟨t.center.2,t.radius⟩⟩

theorem sourceBox_eq (t : ComplexIsolation.Certificate) :
    sourceBox t = RationalBox.ofRectangle t.rectangle := by
  cases t
  simp only [sourceBox,RationalBox.ofRectangle,ComplexIsolation.Certificate.rectangle,
    RationalBall.ofEndpoints]
  congr 2 <;> ring

noncomputable def boxComputes : Computes ComplexIsolation.CertificateMachine.certificateEncoding
    CommonFieldMachine.boxEncoding sourceBox := by
  let c := ComplexIsolation.CertificateMachine.centerComputes
  let r := ComplexIsolation.CertificateMachine.radiusComputes
  let w := pairComputes (pairComputes (Scalars.real c) r) (pairComputes (Scalars.imag c) r)
  exact recode w id (fun _ => rfl) (fun _ => rfl)

noncomputable def boxEqual : Computes encoding encodingBoolBool
    (fun r => decide (r.field.box=RationalBox.ofRectangle r.certificate.rectangle)) :=
  congrComputes ((pairComputes Access.source (Access.certificate.andThen boxComputes)).andThen
    (equalComputes CommonFieldMachine.boxEncoding)) (fun r => by
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,decide_eq_true_eq,sourceBox_eq])

noncomputable def rootExecutes : Executes encoding encodingBoolBool
    (fun r => r.certificate.check (relationCode r.field.relation)) := by
  let supplied := ComplexIsolation.CertificateMachine.computes
  let root : Executes ComplexIsolation.CertificateMachine.inputEncoding encodingBoolBool
      (fun p => p.2.check p.1) :=
    ⟨supplied.machine,fun p => supplied.time (ComplexIsolation.CertificateMachine.inputEncoding.encode p).length,
      supplied.outputs⟩
  exact (Executes.ofComputes (pairComputes (Access.relation.andThen relationComputes) Access.certificate)).comp root

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.RootBridge
