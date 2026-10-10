import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine.Catalogue


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

namespace Programs
noncomputable section
variable {A B C : Type} {ea : Encoding A Bool}

def cross (eb : Encoding B Bool) (ec : Encoding C Bool)
    {f : A → List B} {g : A → List C}
    (u : Executes ea (framedListEncoding eb) f) (v : Executes ea (framedListEncoding ec) g) :
    Executes ea (framedListEncoding (pairEncoding eb ec))
      (fun a => ComplexIsolation.RootSearchDriver.cross (f a) (g a)) :=
  (Executes.pair u v).comp (Executes.ofComputes (ComplexIsolation.RootSearchDriver.crossComputes eb ec))

def vectorLists (eb : Encoding B Bool) {f : A → List B} {n : A → ℕ}
    (u : Executes ea (framedListEncoding eb) f) (count : Executes ea encodingNatBool n) :
    Executes ea (framedListEncoding (framedListEncoding eb))
      (fun a => StructuralListMachine.exactLength (f a) (n a)) :=
  (Executes.pair count u).comp (StructuralListMachine.exactExecutes eb)

def bounded (eb : Encoding B Bool) {f : A → List B} {h : A → ℕ}
    (u : Executes ea (framedListEncoding eb) f) (height : Executes ea encodingNatBool h) :
    Executes ea (framedListEncoding (framedListEncoding eb))
      (fun a => StructuredCatalogue.lists (f a) (h a)) :=
  (Executes.pair u height).comp (StructuralListMachine.boundedExecutes eb)

def successor : Executes encodingNatBool encodingNatBool (fun n => n+1) :=
  (StructuralListMachine.ofFinite ComplexIsolation.RootSearchDriver.Height.binaryToUnary).comp
    (Executes.ofComputes (WireLists.succComputes.andThen UnaryBinary.computes))

def naturals : Executes encodingNatBool (framedListEncoding encodingNatBool) StructuredCatalogue.naturals :=
  Executes.congr ((StructuralListMachine.ofFinite ComplexIsolation.RootSearchDriver.Height.binaryToUnary).comp
    (Executes.ofComputes ((WireLists.succComputes.andThen ComponentSelection.UnaryRange.computes).andThen
      (WireLists.mapComputes UnaryBinary.unaryEncoding encodingNatBool id UnaryBinary.computes))))
        (fun h => by simp only [Function.comp_apply,id_eq,StructuredCatalogue.naturals,List.map_id])

def rationals : Executes encodingNatBool (framedListEncoding rationalEncoding) StructuredCatalogue.rationals :=
  (StructuralListMachine.ofFinite ComplexIsolation.RootSearchDriver.Height.computes).comp
    (Executes.ofComputes ComplexIsolation.RootSearchDriver.rationalsComputes)

def polynomials : Executes encodingNatBool
    (framedListEncoding ComplexIsolation.CertificateMachine.polynomialEncoding) StructuredCatalogue.polynomials :=
  bounded ComplexIsolation.CertificateMachine.termEncoding (cross encodingNatBool rationalEncoding naturals rationals)
    (Executes.ofComputes (identityComputes encodingNatBool))

def ball : Computes (pairEncoding rationalEncoding rationalEncoding) CommonFieldMachine.ballEncoding
    (fun p => (⟨p.1,p.2⟩ : RationalBall)) :=
  recode (identityComputes (pairEncoding rationalEncoding rationalEncoding)) id (fun _ => rfl) (fun _ => rfl)

def balls : Executes encodingNatBool (framedListEncoding CommonFieldMachine.ballEncoding) StructuredCatalogue.balls :=
  (cross rationalEncoding rationalEncoding rationals rationals).comp
    (Executes.ofComputes (WireLists.mapComputes (pairEncoding rationalEncoding rationalEncoding)
      CommonFieldMachine.ballEncoding _ ball))

def box : Computes (pairEncoding CommonFieldMachine.ballEncoding CommonFieldMachine.ballEncoding)
    CommonFieldMachine.boxEncoding (fun p => (⟨p.1,p.2⟩ : RationalBox)) :=
  recode (identityComputes (pairEncoding CommonFieldMachine.ballEncoding CommonFieldMachine.ballEncoding))
    id (fun _ => rfl) (fun _ => rfl)

def boxes : Executes encodingNatBool (framedListEncoding CommonFieldMachine.boxEncoding) StructuredCatalogue.boxes :=
  (cross CommonFieldMachine.ballEncoding CommonFieldMachine.ballEncoding balls balls).comp
    (Executes.ofComputes (WireLists.mapComputes
      (pairEncoding CommonFieldMachine.ballEncoding CommonFieldMachine.ballEncoding)
        CommonFieldMachine.boxEncoding _ box))

def certificates : Executes encodingNatBool
    (framedListEncoding ComplexIsolation.CertificateMachine.certificateEncoding)
    ComplexIsolation.RootSearchDriver.certificates :=
  StructuralListMachine.ofFinite ComplexIsolation.RootSearchDriver.generationComputes

end
end Programs

namespace Access
noncomputable section
def coefficients : Computes encoding encodingNatBool Request.coefficients :=
  recode (Wiring.firstComputes encodingNatBool tailEncoding) Request.wire (fun _ => rfl) (fun _ => rfl)
def tail : Computes encoding tailEncoding (fun r => (r.variables,r.targets,r.equations,r.height)) :=
  recode (Wiring.secondComputes encodingNatBool tailEncoding) Request.wire (fun _ => rfl) (fun _ => rfl)
def «variables» : Computes encoding encodingNatBool Request.variables :=
  tail.andThen (Wiring.firstComputes encodingNatBool contextEncoding)
def context : Computes encoding contextEncoding (fun r => (r.targets,r.equations,r.height)) :=
  tail.andThen (Wiring.secondComputes encodingNatBool contextEncoding)
def targets : Computes encoding CommonFieldMachine.rootsEncoding Request.targets :=
  context.andThen (Wiring.firstComputes CommonFieldMachine.rootsEncoding lastEncoding)
def last : Computes encoding lastEncoding (fun r => (r.equations,r.height)) :=
  context.andThen (Wiring.secondComputes CommonFieldMachine.rootsEncoding lastEncoding)
def equations : Computes encoding NegativeCertificateMachine.systemEncoding Request.equations :=
  last.andThen (Wiring.firstComputes NegativeCertificateMachine.systemEncoding encodingNatBool)
def height : Computes encoding encodingNatBool Request.height :=
  last.andThen (Wiring.secondComputes NegativeCertificateMachine.systemEncoding encodingNatBool)
def count : Computes encoding encodingNatBool (fun r => r.equations.length) :=
  (equations.andThen (WireLists.lengthComputes NegativeCertificateMachine.equationEncoding)).andThen
    UnaryBinary.computes
def request : Computes degreeEncoding encoding (fun p => p.1) :=
  Wiring.firstComputes encoding encodingNatBool
def degree : Computes degreeEncoding encodingNatBool (fun p => p.2) :=
  Wiring.secondComputes encoding encodingNatBool
end
end Access

namespace Generation
noncomputable section
def height : Executes degreeEncoding encodingNatBool (fun p => p.1.height) :=
  Executes.ofComputes (Access.request.andThen Access.height)
def dimension : Executes degreeEncoding encodingNatBool (fun p => p.2+1) :=
  (Executes.ofComputes Access.degree).comp Programs.successor
def relations : Executes degreeEncoding (framedListEncoding CommonFieldMachine.coordinatesEncoding)
    (fun p => NegativeCatalogueMachine.relations p.2 p.1.height) :=
  Programs.vectorLists rationalEncoding (height.comp Programs.rationals) dimension
def exponents : Executes degreeEncoding (framedListEncoding NegativeCertificateMachine.exponentEncoding)
    (fun p => StructuralListMachine.exactLength (StructuredCatalogue.naturals p.1.height) p.1.variables) :=
  Programs.vectorLists encodingNatBool (height.comp Programs.naturals)
    (Executes.ofComputes (Access.request.andThen Access.variables))
def expressions : Executes degreeEncoding (framedListEncoding CommonFieldMachine.expressionsEncoding)
    (fun p => NegativeCatalogueMachine.expressions p.1.coefficients p.1.height) :=
  Programs.vectorLists ComplexIsolation.CertificateMachine.polynomialEncoding (height.comp Programs.polynomials)
    (Executes.ofComputes (Access.request.andThen Access.coefficients))
def multipliers : Executes degreeEncoding (framedListEncoding NegativeCertificateMachine.polyEncoding)
    (fun p => NegativeCatalogueMachine.multipliers p.1.variables p.2 p.1.height) :=
  Programs.bounded NegativeCertificateMachine.termEncoding
    (Programs.cross NegativeCertificateMachine.exponentEncoding CommonFieldMachine.coordinatesEncoding
      exponents relations) height
def multiplierVectors : Executes degreeEncoding
    (framedListEncoding NegativeCertificateMachine.multipliersEncoding)
    (fun p => StructuralListMachine.exactLength
      (NegativeCatalogueMachine.multipliers p.1.variables p.2 p.1.height) p.1.equations.length) :=
  Programs.vectorLists NegativeCertificateMachine.polyEncoding multipliers
    (Executes.ofComputes (Access.request.andThen Access.count))
def payloads : Executes degreeEncoding (framedListEncoding payloadEncoding)
    (fun p => NegativeCatalogueMachine.payloads
      p.1.coefficients p.1.variables p.1.equations.length p.2 p.1.height) :=
  Programs.cross CommonFieldMachine.coordinatesEncoding payloadCertEncoding relations
    (Programs.cross ComplexIsolation.CertificateMachine.certificateEncoding payloadBoxEncoding
      (height.comp Programs.certificates)
      (Programs.cross CommonFieldMachine.boxEncoding payloadLastEncoding (height.comp Programs.boxes)
        (Programs.cross CommonFieldMachine.expressionsEncoding NegativeCertificateMachine.multipliersEncoding
          expressions multiplierVectors)))
end
end Generation

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine
