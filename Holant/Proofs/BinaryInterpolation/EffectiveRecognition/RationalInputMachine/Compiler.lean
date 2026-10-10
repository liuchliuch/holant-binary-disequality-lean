import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.RationalInputMachine.Programs


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

namespace Compiler
noncomputable section
def bodyTerm : Computes (pairEncoding encoding termEncoding) NegativeCertificateMachine.sourceTermEncoding
    (fun p => RationalInputMachine.bodyTerm p.1.original.length (coefficients p.1.body) p.2) := by
  let r := Wiring.firstComputes encoding termEncoding
  let t := Wiring.secondComputes encoding termEncoding
  let q := t.andThen (Wiring.secondComputes NegativeCertificateMachine.exponentEncoding rationalEncoding)
  let cs := r.andThen Access.coefficients
  let index := (pairComputes q cs).andThen FirstIndex.computes
  let shifted := (pairComputes (r.andThen Access.count) index).andThen Programs.add
  exact pairComputes shifted (t.andThen (Wiring.firstComputes NegativeCertificateMachine.exponentEncoding rationalEncoding))

def row : Computes (pairEncoding encoding rowEncoding) NegativeCertificateMachine.equationEncoding
    (fun p => p.2.map (RationalInputMachine.bodyTerm p.1.original.length (coefficients p.1.body))) :=
  mapListComputes encoding termEncoding NegativeCertificateMachine.sourceTermEncoding
    (fun r t => RationalInputMachine.bodyTerm r.original.length (coefficients r.body) t) bodyTerm

def bodyRows : Computes encoding NegativeCertificateMachine.systemEncoding RationalInputMachine.bodyRows :=
  AccessPrograms.map rowEncoding NegativeCertificateMachine.equationEncoding Access.body
    (fun r p => p.map (RationalInputMachine.bodyTerm r.original.length (coefficients r.body))) row

abbrev bindingEncoding := pairEncoding encoding encodingNatBool
def binding : Executes bindingEncoding NegativeCertificateMachine.equationEncoding
    (fun p => RationalInputMachine.binding p.1 p.2) := by
  let r := Wiring.firstComputes encoding encodingNatBool
  let i := Wiring.secondComputes encoding encodingNatBool
  let n := Executes.ofComputes (r.andThen Access.variables)
  let zero := n.comp Programs.zero
  let j := (Executes.ofComputes (pairComputes (r.andThen Access.addresses) i)).comp
    (NegativeCertificateMachine.Lists.lookup encodingNatBool 0)
  let exponent := (Executes.pair n j).comp Programs.hit
  let first := Executes.pair (Executes.ofComputes i) zero
  let second := Executes.pair (Executes.ofComputes (r.andThen Access.negative)) exponent
  exact Programs.consExec NegativeCertificateMachine.sourceTermEncoding first
    (second.comp (Executes.ofComputes (NegativeCertificateMachine.Lists.singleton
      NegativeCertificateMachine.sourceTermEncoding)))

def bindings : Executes encoding NegativeCertificateMachine.systemEncoding RationalInputMachine.bindings :=
  NegativeCertificateMachine.Lists.map encoding encodingNatBool NegativeCertificateMachine.equationEncoding
    ((Executes.ofComputes Access.count).comp Programs.range) RationalInputMachine.binding binding

def guard : Executes encoding NegativeCertificateMachine.equationEncoding RationalInputMachine.guard := by
  let n := Executes.ofComputes Access.variables
  let m := Executes.ofComputes Access.count
  let neg := Executes.ofComputes Access.negative
  let first := Executes.pair m (n.comp (Programs.triple 4 0 3))
  let second := Executes.pair neg (n.comp (Programs.triple 4 1 2))
  let third := Executes.pair neg (n.comp Programs.zero)
  exact Programs.consExec NegativeCertificateMachine.sourceTermEncoding first
    (Programs.consExec NegativeCertificateMachine.sourceTermEncoding second
      (third.comp (Executes.ofComputes (NegativeCertificateMachine.Lists.singleton
        NegativeCertificateMachine.sourceTermEncoding))))

def targets : Computes encoding CommonFieldMachine.rootsEncoding RationalInputMachine.targets :=
  (pairComputes Access.original (Access.coefficients.andThen
    (WireLists.mapComputes rationalEncoding ComplexIsolation.CertificateMachine.rootEncoding
      RationalRootCode.code Programs.rootCode))).andThen
        (WireLists.append ComplexIsolation.CertificateMachine.rootEncoding)

def count : Computes encoding encodingNatBool
    (fun r => r.original.length+(coefficients r.body).length) :=
  (pairComputes Access.count ((Access.coefficients.andThen
    (WireLists.lengthComputes rationalEncoding)).andThen UnaryBinary.computes)).andThen Programs.add

def equations : Executes encoding NegativeCertificateMachine.systemEncoding
    (fun r => RationalInputMachine.guard r :: (RationalInputMachine.bindings r ++ RationalInputMachine.bodyRows r)) :=
  Programs.consExec NegativeCertificateMachine.equationEncoding guard
    ((Executes.pair bindings (Executes.ofComputes bodyRows)).comp
      (Executes.ofComputes (WireLists.append NegativeCertificateMachine.equationEncoding)))

def executes : Executes encoding NegativeCatalogueMachine.encoding request := by
  let assembled := Executes.pair (Executes.ofComputes count)
    (Executes.pair (Executes.ofComputes Access.variables)
      (Executes.pair (Executes.ofComputes targets)
        (Executes.pair equations (Executes.ofComputes (constantComputes encoding encodingNatBool 0)))))
  exact Executes.recode assembled id (fun _ => rfl) (fun _ => rfl)
end
end Compiler

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine
