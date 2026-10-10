import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.Lists


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.SparsePrograms
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open CommonFieldMachine
open Holant.LocalDrafts.Tractability.AffineMachine

abbrev exponentPairEncoding := pairEncoding exponentEncoding exponentEncoding
noncomputable def addExponentCell : Computes (pairEncoding exponentPairEncoding UnaryBinary.unaryEncoding)
    encodingNatBool (fun p => p.1.1.getD p.2 0+p.1.2.getD p.2 0) := by
  let p := Wiring.firstComputes exponentPairEncoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes exponentPairEncoding UnaryBinary.unaryEncoding
  let a := p.andThen (Wiring.firstComputes exponentEncoding exponentEncoding)
  let b := p.andThen (Wiring.secondComputes exponentEncoding exponentEncoding)
  exact ((pairComputes (AccessPrograms.get encodingNatBool 0 a i)
    (AccessPrograms.get encodingNatBool 0 b i)).andThen Endpoints.prepareArithmeticComputes).andThen
      BinaryCompose.additionComputes

noncomputable def addExponents : Computes exponentPairEncoding exponentEncoding (fun p => addExponent p.1 p.2) :=
  WireLists.tabulate exponentPairEncoding encodingNatBool (fun p => p.1.length)
    ((Wiring.firstComputes exponentEncoding exponentEncoding).andThen (WireLists.lengthComputes encodingNatBool))
    (fun p i => p.1.getD i 0+p.2.getD i 0) addExponentCell

abbrev productCellEncoding := pairEncoding (pairEncoding coordinatesEncoding termEncoding) termEncoding
noncomputable def productCell : Executes productCellEncoding termEncoding
    (fun p => termProduct p.1.1 p.1.2 p.2) := by
  let ct := Wiring.firstComputes (pairEncoding coordinatesEncoding termEncoding) termEncoding
  let c := ct.andThen (Wiring.firstComputes coordinatesEncoding termEncoding)
  let t := ct.andThen (Wiring.secondComputes coordinatesEncoding termEncoding)
  let u := Wiring.secondComputes (pairEncoding coordinatesEncoding termEncoding) termEncoding
  let exps := (pairComputes (t.andThen (Wiring.firstComputes exponentEncoding coordinatesEncoding))
    (u.andThen (Wiring.firstComputes exponentEncoding coordinatesEncoding))).andThen addExponents
  let coeff := (Executes.ofComputes (pairComputes c
    (pairComputes (t.andThen (Wiring.secondComputes exponentEncoding coordinatesEncoding))
      (u.andThen (Wiring.secondComputes exponentEncoding coordinatesEncoding))))).comp Multiplication.mul
  exact Executes.pair (Executes.ofComputes exps) coeff

abbrev rowEncoding := pairEncoding (pairEncoding coordinatesEncoding termEncoding) polyEncoding
noncomputable def row : Executes rowEncoding polyEncoding
    (fun p => p.2.map (termProduct p.1.1 p.1.2)) :=
  Executes.mapList (pairEncoding coordinatesEncoding termEncoding) termEncoding termEncoding
    (fun ct u => termProduct ct.1 ct.2 u) productCell

abbrev mulEncoding := pairEncoding coordinatesEncoding (pairEncoding polyEncoding polyEncoding)
noncomputable def mulExecutes : Executes mulEncoding polyEncoding (fun p => mul p.1 p.2.1 p.2.2) := by
  let c := Wiring.firstComputes coordinatesEncoding (pairEncoding polyEncoding polyEncoding)
  let pq := Wiring.secondComputes coordinatesEncoding (pairEncoding polyEncoding polyEncoding)
  let p := pq.andThen (Wiring.firstComputes polyEncoding polyEncoding)
  let arg := Wiring.firstComputes mulEncoding termEncoding
  let t := Wiring.secondComputes mulEncoding termEncoding
  let c' := arg.andThen c
  let q' := (arg.andThen pq).andThen (Wiring.secondComputes polyEncoding polyEncoding)
  let rowProgram := (Executes.ofComputes (pairComputes (pairComputes c' t) q')).comp row
  let rows := Lists.map mulEncoding termEncoding polyEncoding (Executes.ofComputes p)
    (fun p t => p.2.2.map (termProduct p.1 t)) rowProgram
  exact Executes.congr (rows.comp (Executes.ofComputes (WireLists.flatten termEncoding)))
    (fun p => by simp [mul,List.flatMap_def])

abbrev coefficientEncoding := pairEncoding UnaryBinary.unaryEncoding (pairEncoding polyEncoding exponentEncoding)
noncomputable def mask : Computes (pairEncoding coefficientEncoding termEncoding) coordinatesEncoding
    (fun p => if p.2.1=p.1.2.2 then p.2.2 else Coordinates.zero p.1.1) := by
  let arg := Wiring.firstComputes coefficientEncoding termEncoding
  let t := Wiring.secondComputes coefficientEncoding termEncoding
  let d := arg.andThen (Wiring.firstComputes UnaryBinary.unaryEncoding (pairEncoding polyEncoding exponentEncoding))
  let key := (arg.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding
    (pairEncoding polyEncoding exponentEncoding))).andThen (Wiring.secondComputes polyEncoding exponentEncoding)
  let exp := t.andThen (Wiring.firstComputes exponentEncoding coordinatesEncoding)
  let coeff := t.andThen (Wiring.secondComputes exponentEncoding coordinatesEncoding)
  let eq := (pairComputes exp key).andThen (equalComputes exponentEncoding)
  let zero : Computes (pairEncoding coefficientEncoding termEncoding) coordinatesEncoding
      (fun p => Coordinates.zero p.1.1) := congrComputes (d.andThen (WireLists.replicate rationalEncoding 0))
    (fun p => by simp [Coordinates.zero,Coordinates.tab])
  exact congrComputes (ifComputes eq coeff zero) (fun p => by simp)

noncomputable def coefficientExecutes : Executes coefficientEncoding coordinatesEncoding
    (fun p => coefficient p.1 p.2.1 p.2.2) := by
  let d := Wiring.firstComputes UnaryBinary.unaryEncoding (pairEncoding polyEncoding exponentEncoding)
  let p := (Wiring.secondComputes UnaryBinary.unaryEncoding (pairEncoding polyEncoding exponentEncoding)).andThen
    (Wiring.firstComputes polyEncoding exponentEncoding)
  let masked := AccessPrograms.map termEncoding coordinatesEncoding p
    (fun p t => if t.1=p.2.2 then t.2 else Coordinates.zero p.1) mask
  exact (Executes.ofComputes (pairComputes d masked)).comp Companion.sum

abbrev zeroEncoding := pairEncoding UnaryBinary.unaryEncoding polyEncoding
noncomputable def zeroCell : Executes (pairEncoding zeroEncoding termEncoding) encodingBoolBool
    (fun p => Coordinates.isZero (coefficient p.1.1 p.1.2 p.2.1)) := by
  let arg := Wiring.firstComputes zeroEncoding termEncoding
  let t := Wiring.secondComputes zeroEncoding termEncoding
  let d := arg.andThen (Wiring.firstComputes UnaryBinary.unaryEncoding polyEncoding)
  let p := arg.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding polyEncoding)
  let a := t.andThen (Wiring.firstComputes exponentEncoding coordinatesEncoding)
  exact ((Executes.ofComputes (pairComputes d (pairComputes p a))).comp coefficientExecutes).comp
    (Executes.ofComputes CoordinatePrimitives.zero)

noncomputable def zeroExecutes : Executes zeroEncoding encodingBoolBool (fun p => zeroCoefficients p.1 p.2) := by
  let values := Lists.map zeroEncoding termEncoding encodingBoolBool
    (Executes.ofComputes (Wiring.secondComputes UnaryBinary.unaryEncoding polyEncoding))
    (fun p t => Coordinates.isZero (coefficient p.1 p.2 t.1)) zeroCell
  exact Executes.congr (values.comp (Executes.ofComputes CoordinatePrimitives.allTrue))
    (fun p => by simp [zeroCoefficients,List.all_map])

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.SparsePrograms
