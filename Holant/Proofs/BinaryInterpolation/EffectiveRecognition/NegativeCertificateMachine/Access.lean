import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.SparsePrograms


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.Access
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open CommonFieldMachine (Executes)
open Holant.LocalDrafts.Tractability.AffineMachine

abbrev certEncoding := ComplexIsolation.CertificateMachine.certificateEncoding
abbrev systemTailEncoding := pairEncoding systemEncoding multipliersEncoding
abbrev certificateTailEncoding := pairEncoding certEncoding systemTailEncoding
abbrev fieldTailEncoding := pairEncoding CommonFieldMachine.requestEncoding certificateTailEncoding
abbrev dimensionsTailEncoding := pairEncoding encodingNatBool fieldTailEncoding

noncomputable def coefficients : Computes encoding encodingNatBool Input.coefficients :=
  recode (Wiring.firstComputes encodingNatBool dimensionsTailEncoding) Input.wire (fun _ => rfl) (fun _ => rfl)
noncomputable def tail : Computes encoding dimensionsTailEncoding
    (fun r => (r.variables,r.field,r.certificate,r.equations,r.multipliers)) :=
  recode (Wiring.secondComputes encodingNatBool dimensionsTailEncoding) Input.wire (fun _ => rfl) (fun _ => rfl)
noncomputable def «variables» : Computes encoding encodingNatBool Input.variables :=
  tail.andThen (Wiring.firstComputes encodingNatBool fieldTailEncoding)
noncomputable def fieldTail : Computes encoding fieldTailEncoding
    (fun r => (r.field,r.certificate,r.equations,r.multipliers)) :=
  tail.andThen (Wiring.secondComputes encodingNatBool fieldTailEncoding)
noncomputable def field : Computes encoding CommonFieldMachine.requestEncoding Input.field :=
  fieldTail.andThen (Wiring.firstComputes CommonFieldMachine.requestEncoding certificateTailEncoding)
noncomputable def certTail : Computes encoding certificateTailEncoding
    (fun r => (r.certificate,r.equations,r.multipliers)) :=
  fieldTail.andThen (Wiring.secondComputes CommonFieldMachine.requestEncoding certificateTailEncoding)
noncomputable def certificate : Computes encoding certEncoding Input.certificate :=
  certTail.andThen (Wiring.firstComputes certEncoding systemTailEncoding)
noncomputable def systemTail : Computes encoding systemTailEncoding (fun r => (r.equations,r.multipliers)) :=
  certTail.andThen (Wiring.secondComputes certEncoding systemTailEncoding)
noncomputable def equations : Computes encoding systemEncoding Input.equations :=
  systemTail.andThen (Wiring.firstComputes systemEncoding multipliersEncoding)
noncomputable def multipliers : Computes encoding multipliersEncoding Input.multipliers :=
  systemTail.andThen (Wiring.secondComputes systemEncoding multipliersEncoding)
noncomputable def relation := field.andThen CommonFieldMachine.FamilyMachine.relation
noncomputable def expressions := field.andThen CommonFieldMachine.FamilyMachine.expressions
noncomputable def source := field.andThen CommonFieldMachine.FamilyMachine.source
noncomputable def dimension := field.andThen CommonFieldMachine.FamilyMachine.dimension

abbrev sizesEncoding := pairEncoding encodingNatBool encodingNatBool
noncomputable def sourceCell : Computes (pairEncoding sizesEncoding sourceTermEncoding) encodingBoolBool
    (fun p => sourceShape p.1.1 p.1.2 p.2) := by
  let mn := Wiring.firstComputes sizesEncoding sourceTermEncoding
  let t := Wiring.secondComputes sizesEncoding sourceTermEncoding
  let m := mn.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
  let n := mn.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)
  let i := t.andThen (Wiring.firstComputes encodingNatBool exponentEncoding)
  let length := ((t.andThen (Wiring.secondComputes encodingNatBool exponentEncoding)).andThen
    (WireLists.lengthComputes encodingNatBool)).andThen UnaryBinary.computes
  exact congrComputes (AccessPrograms.bool Bool.and ((pairComputes i m).andThen Endpoints.lessComputes)
    (AccessPrograms.eqNat length n)) (fun p => by simp [sourceShape])

noncomputable def termCell : Computes (pairEncoding sizesEncoding termEncoding) encodingBoolBool
    (fun p => termShape p.1.1 p.1.2 p.2) := by
  let nd := Wiring.firstComputes sizesEncoding termEncoding
  let t := Wiring.secondComputes sizesEncoding termEncoding
  let n := nd.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
  let d := nd.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)
  let ne := ((t.andThen (Wiring.firstComputes exponentEncoding CommonFieldMachine.coordinatesEncoding)).andThen
    (WireLists.lengthComputes encodingNatBool)).andThen UnaryBinary.computes
  let nc := ((t.andThen (Wiring.secondComputes exponentEncoding CommonFieldMachine.coordinatesEncoding)).andThen
    (WireLists.lengthComputes rationalEncoding)).andThen UnaryBinary.computes
  exact congrComputes (AccessPrograms.bool Bool.and (AccessPrograms.eqNat ne n)
    (AccessPrograms.eqNat nc d)) (fun p => by simp [termShape])

noncomputable def allList {A : Type} (e : Encoding A Bool) (f : ℕ × ℕ → A → Bool)
    (cell : Computes (pairEncoding sizesEncoding e) encodingBoolBool (fun p => f p.1 p.2)) :
    Computes (pairEncoding sizesEncoding (framedListEncoding e)) encodingBoolBool
      (fun p => p.2.all (f p.1)) :=
  congrComputes ((mapListComputes sizesEncoding e encodingBoolBool f cell).andThen
    CommonFieldMachine.CoordinatePrimitives.allTrue) (fun p => by simp [List.all_map])

noncomputable def shape : Computes encoding encodingBoolBool Input.shape := by
  let common := field.andThen CommonFieldMachine.FamilyMachine.shape
  let nt := ((field.andThen CommonFieldMachine.FamilyMachine.targets).andThen
    (WireLists.lengthComputes ComplexIsolation.CertificateMachine.rootEncoding)).andThen UnaryBinary.computes
  let nh := (multipliers.andThen (WireLists.lengthComputes polyEncoding)).andThen UnaryBinary.computes
  let ns := (equations.andThen (WireLists.lengthComputes equationEncoding)).andThen UnaryBinary.computes
  let lengths := AccessPrograms.bool Bool.and (AccessPrograms.eqNat nt coefficients) (AccessPrograms.eqNat nh ns)
  let sourceEquation := allList sourceTermEncoding (fun mn t => sourceShape mn.1 mn.2 t) sourceCell
  let sourceSystem := allList equationEncoding (fun mn e => e.all (sourceShape mn.1 mn.2)) sourceEquation
  let sourceGood := (pairComputes (pairComputes coefficients «variables») equations).andThen sourceSystem
  let multiplierPoly := allList termEncoding (fun nd t => termShape nd.1 nd.2 t) termCell
  let multiplierList := allList polyEncoding (fun nd p => p.all (termShape nd.1 nd.2)) multiplierPoly
  let multiplierGood := (pairComputes (pairComputes «variables» dimension) multipliers).andThen multiplierList
  exact congrComputes (AccessPrograms.bool Bool.and common (AccessPrograms.bool Bool.and lengths
    (AccessPrograms.bool Bool.and sourceGood multiplierGood)))
    (fun r => by simp only [Input.shape,Bool.decide_and,Function.comp_apply,id_eq])

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.Access
