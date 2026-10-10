import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.Access


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.DefectProgram
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open CommonFieldMachine
open Holant.LocalDrafts.Tractability.AffineMachine

abbrev tableEncoding := framedListEncoding coordinatesEncoding
noncomputable def coordinatesExecutes : Executes encoding tableEncoding
    (fun r => coordinates r.field.relation r.field.expressions) :=
  (Executes.ofComputes (pairComputes Access.relation Access.expressions)).comp
    (Executes.mapList coordinatesEncoding ComplexIsolation.CertificateMachine.polynomialEncoding
      coordinatesEncoding Coordinates.reduce CommonFieldMachine.PolynomialEvaluation.reduce)

noncomputable def materializeCell : Executes (pairEncoding tableEncoding sourceTermEncoding) termEncoding
    (fun p => (p.2.2,p.1.getD p.2.1 [])) := by
  let a := Wiring.firstComputes tableEncoding sourceTermEncoding
  let t := Wiring.secondComputes tableEncoding sourceTermEncoding
  let i := t.andThen (Wiring.firstComputes encodingNatBool exponentEncoding)
  let exps := t.andThen (Wiring.secondComputes encodingNatBool exponentEncoding)
  let coeff := (Executes.ofComputes (pairComputes a i)).comp (Lists.lookup coordinatesEncoding [])
  exact Executes.pair (Executes.ofComputes exps) coeff

noncomputable def materializeExecutes : Executes (pairEncoding tableEncoding equationEncoding) polyEncoding
    (fun p => materialize p.1 p.2) :=
  Executes.mapList tableEncoding sourceTermEncoding termEncoding
    (fun a t => (t.2,a.getD t.1 [])) materializeCell

noncomputable def productAt : Executes (pairEncoding encoding UnaryBinary.unaryEncoding) polyEncoding
    (fun p => mul p.1.field.relation (p.1.multipliers.getD p.2 [])
      (materialize (coordinates p.1.field.relation p.1.field.expressions)
        (p.1.equations.getD p.2 []))) := by
  let r := Wiring.firstComputes encoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes encoding UnaryBinary.unaryEncoding
  let H := AccessPrograms.get polyEncoding [] (r.andThen Access.multipliers) i
  let e := AccessPrograms.get equationEncoding [] (r.andThen Access.equations) i
  let table := (Executes.ofComputes r).comp coordinatesExecutes
  let material := (Executes.pair table (Executes.ofComputes e)).comp materializeExecutes
  let prepare := Executes.pair (Executes.ofComputes (r.andThen Access.relation))
    (Executes.pair (Executes.ofComputes H) material)
  exact prepare.comp SparsePrograms.mulExecutes

noncomputable def negativeOne : Executes encoding polyEncoding
    (fun r => [(List.replicate r.variables 0,
      Coordinates.scale (-1) (Coordinates.unit r.field.relation.length))]) := by
  let exps := ((Executes.ofComputes Access.variables).comp Lists.toUnary).comp
    (Executes.ofComputes (WireLists.replicate encodingNatBool 0))
  let unit := Access.relation.andThen CommonFieldMachine.Companion.unit
  let negative := (pairComputes (constantComputes encoding rationalEncoding (-1)) unit).andThen
    CommonFieldMachine.CoordinatePrimitives.scale
  exact (Executes.pair exps (Executes.ofComputes negative)).comp
    (Executes.ofComputes (Lists.singleton termEncoding))

def value (r : Input) : Poly := defect r.variables r.field.relation r.field.expressions r.equations r.multipliers
noncomputable def executes : Executes encoding polyEncoding value := by
  let count := Access.equations.andThen (WireLists.lengthComputes equationEncoding)
  let products := Executes.tabulate encoding polyEncoding (fun r => r.equations.length) count
    (fun r i => mul r.field.relation (r.multipliers.getD i [])
      (materialize (coordinates r.field.relation r.field.expressions) (r.equations.getD i []))) productAt
  let flat := products.comp (Executes.ofComputes (WireLists.flatten termEncoding))
  exact (Executes.pair flat negativeOne).comp (Executes.ofComputes (WireLists.append termEncoding))

noncomputable def zeroExecutes : Executes encoding encodingBoolBool
    (fun r => zeroCoefficients r.field.relation.length (value r)) :=
  (Executes.pair (Executes.ofComputes (Access.relation.andThen (WireLists.lengthComputes rationalEncoding)))
    executes).comp SparsePrograms.zeroExecutes

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.DefectProgram
