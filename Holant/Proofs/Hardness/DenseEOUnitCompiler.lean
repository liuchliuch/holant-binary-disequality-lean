import Holant.Proofs.Hardness.DenseEOUnitTemplates
import Holant.Proofs.Hardness.SparseUnitValue
import Holant.Proofs.Hardness.PairedPinsExpansionBalance
import Holant.Proofs.Hardness.PairedPinsControlled
import Holant.Proofs.Reductions.ControlledCap

/-! Full pin-free ONE/TWO reduction into q+literal01, with actual physical
count test, macro expansion, complementary-pin merge and scale correction.
Only original q coefficients and its fixed field presentation enter. No UA,
PureStep, Ready or original-family evaluator is an input or dependency. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.DenseEOUnitCompiler
open Holant Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open DenseEOUnitLocal
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace U
export DenseEOUnitLocal (scale unit)
end U
namespace V
export SparseUnitValue (Input encoding arity palette value count0 count1 zero_of_unbalanced)
end V
namespace Labels
export DenseEOUnitLabels (arity palette template template_valid template_pin_count)
end Labels
namespace PC
export PairedPinsControlled (sourceTables targetTables sourceValue targetValue)
end PC
namespace Pair
export PairedPinsValidated (query inputEncoding targetEncoding)
end Pair

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M : Signature K 4)
abbrev original (_ : Fin 1) : Signature K 4 := M
abbrev pins := PairedPinsSemantics.pin (K:=K)
abbrev edges : Fin 1 → Kernel K := fun _=>Signature.disequality
abbrev sourceTables := PC.sourceTables F (a:=fun _=>4) (original M) (pins false) (pins true) edges
abbrev targetTables := PC.targetTables F (a:=fun _=>4) (original M) (pins false) (pins true) edges
abbrev targetValue := PC.targetValue F (a:=fun _=>4) (original M) (pins false) (pins true) edges
abbrev targetEncoding := Pair.targetEncoding 1 1 (fun _=>4)
abbrev TargetInput := ExactSignatureTables.Input 2 1 (PairedPinsRaw.targetArity 1 (fun _=>4))

def templates (i : ℕ) : Template := Labels.template M (i==0)

def templateHypotheses : ∀i<2,(templates M i).WellFormed 3 1 Labels.arity ∧
    (templates M i).boundary=V.arity i :=
  fun i _ => ⟨Labels.template_valid M (i==0),rfl⟩

def expanded : V.Input → ExactSignatureTables.Input 3 1 Labels.arity :=
  Compiler.value 2 1 V.arity (templates M) 3 Labels.arity (templateHypotheses M)

def expandedComputes : Computes V.encoding (RawClosedNetwork.validatedEncoding 3 1 Labels.arity) (expanded M) :=
  Compiler.computes 2 1 V.arity (templates M) 3 Labels.arity (templateHypotheses M)

theorem template_profile (i : ℕ) (hi : i<2) (b : Bool) :
    ((templates M i).vertices.filter (fun row=>row.1=1+b.toNat)).length=
      if i=0 then (if b then 2 else 3) else (if b then 3 else 2) := by
  have h := Labels.template_pin_count M (i==0) b
  have hh : i=0 ∨ i=1 := by omega
  rcases hh with rfl|rfl <;> cases b <;> simpa [templates] using h

theorem expanded_balanced (r : V.Input) (hb : V.count0 r=V.count1 r) :
    PairedPinsRaw.Balanced 1 (expanded M r).val := by
  apply PairedPinsExpansionBalance.balanced (templates M) (templateHypotheses M) (template_profile M) r
  exact hb

def scales (i : Fin 2) : K :=
  (if i.val=0 then U.scale M true else 1)*(if i.val=1 then U.scale M false else 1)

variable (hM : EOSupport M) (hs : NonzeroMiddle M)
include hM hs in
theorem local_value (i : Fin 2) :
    ((templates M i.val).network (templateHypotheses M i.val i.isLt).1 (Labels.palette M) edges).denote=
      scales M i • V.palette (K:=K) i := by
  fin_cases i
  · simpa [templates,scales,U.unit,SparseUnitLocal.unit,SparseUnitValue.palette,edges] using
      DenseEOUnitTemplates.unit_denote M hM true
  · simpa [templates,scales,U.unit,SparseUnitLocal.unit,SparseUnitValue.palette,edges] using
      DenseEOUnitTemplates.unit_denote M hM false

include hM hs in
theorem expanded_value (r : V.Input) :
    (sourceTables F M).evaluate F (expanded M r)=
      (U.scale M true^V.count0 r*U.scale M false^V.count1 r)*(V.value r : K) := by
  have hr : r.val.WellFormed 2 1 (FixedGadgetSubstitution.sourceArity (templates M)) := r.property
  have h := replacement_partition (templates M) r.val hr
    (fun i hi=>(templateHypotheses M i hi).1) (V.palette (K:=K)) (Labels.palette M) edges
    (scales M) (local_value M hM hs)
  have hc : (∏v,scales M (r.val.signatureLabel hr v))=
      U.scale M true^V.count0 r*U.scale M false^V.count1 r := by
    simp only [scales,RawClosedNetwork.signatureLabel]
    rw [Finset.prod_mul_distrib,scale_product,scale_product]
    rfl
  rw [hc] at h
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [sourceTables,PC.sourceTables,LinearEquiv.apply_symm_apply]
  exact h

abbrev unary := UnaryBinary.unaryEncoding
abbrev countsEncoding := pairEncoding unary unary

def countsComputes : Computes V.encoding countsEncoding (fun r=>(V.count0 r,V.count1 r)) :=
  pairComputes (Compiler.occurrencesComputes 2 1 V.arity 0) (Compiler.occurrencesComputes 2 1 V.arity 1)

def balanceTest : Computes V.encoding encodingBoolBool (fun r=>decide (V.count0 r=V.count1 r)) :=
  countsComputes.andThen (UniversalPairReduction.SmoothingCompiler.equalComputes unary)

def emptyTarget : TargetInput :=
  ⟨⟨[],[]⟩,⟨(fun v=>Fin.elim0 v),(fun e=>Fin.elim0 e),List.Perm.refl []⟩⟩

def balancedInput (r : V.Input) (hb : V.count0 r=V.count1 r) : PairedPinsValidated.Input 1 1 (fun _=>4) :=
  ⟨(expanded M r).val,(expanded M r).property,expanded_balanced M r hb⟩

def query (r : V.Input) : TargetInput :=
  if h : V.count0 r=V.count1 r then Pair.query (balancedInput M r h) else emptyTarget

def rawExpandedComputes : Computes V.encoding RawClosedNetwork.encoding (fun r=>(expanded M r).val) :=
  recode (expandedComputes M) id (fun _=>rfl) (fun _=>rfl)

def rawQueryComputes : Computes V.encoding RawClosedNetwork.encoding (fun r=>(query M r).val) := by
  let run : Computes V.encoding RawClosedNetwork.encoding (fun r =>
      if decide (V.count0 r=V.count1 r) then PairedPinsRaw.raw 1 (expanded M r).val else ⟨[],[]⟩) :=
    ifComputes balanceTest ((rawExpandedComputes M).andThen (PairedPinsCompiler.computes 1))
      (constantComputes V.encoding RawClosedNetwork.encoding ⟨[],[]⟩)
  exact congrComputes run (fun r=>by by_cases h : V.count0 r=V.count1 r <;>
      simp [query,h,emptyTarget,PairedPinsValidated.query,balancedInput])

def queryComputes : Computes V.encoding targetEncoding (query M) :=
  recode (rawQueryComputes M) id (fun _=>rfl) (fun _=>rfl)

include hM hs in
theorem balanced_query_value (r : V.Input) (hb : V.count0 r=V.count1 r) :
    targetValue F M (query M r)=
      (U.scale M true^V.count0 r*U.scale M false^V.count1 r)*(V.value r : K) := by
  rw [query,dif_pos hb]
  exact (PairedPinsControlled.query_value F (a:=fun _=>4) (original M)
    (pins false) (pins true) edges (balancedInput M r hb)).trans (expanded_value F M hM hs r)

abbrev correctionEncoding := pairEncoding F.encoding countsEncoding

def corrected (p : K×(ℕ×ℕ)) : K := (p.1*(U.scale M true)⁻¹^p.2.1)*(U.scale M false)⁻¹^p.2.2

def correctionInputComputes : Computes (correctionEncoding F)
    (pairEncoding (pairEncoding F.encoding unary) unary) (fun p : K×(ℕ×ℕ)=>((p.1,p.2.1),p.2.2)) :=
  pairComputes
    (pairComputes (Wiring.firstComputes F.encoding countsEncoding)
      ((Wiring.secondComputes F.encoding countsEncoding).andThen (Wiring.firstComputes unary unary)))
    ((Wiring.secondComputes F.encoding countsEncoding).andThen (Wiring.secondComputes unary unary))

def correctionComputes : Computes (correctionEncoding F) F.encoding (corrected M) :=
  congrComputes (((correctionInputComputes F).andThen
    (leftMapComputes unary (ScalarPower.correction F (U.scale M true)))).andThen
      (ScalarPower.correction F (U.scale M false))) (fun _=>rfl)

def post (p : K×(ℕ×ℕ)) : K := if p.2.1=p.2.2 then corrected M p else 0

def postComputes : Computes (correctionEncoding F) F.encoding (post M) := by
  let run : Computes (correctionEncoding F) F.encoding (fun p : K×(ℕ×ℕ)=>
      if decide (p.2.1=p.2.2) then corrected M p else 0) :=
    ifComputes ((Wiring.secondComputes F.encoding countsEncoding).andThen
      (UniversalPairReduction.SmoothingCompiler.equalComputes unary))
      (correctionComputes F M) (constantComputes (correctionEncoding F) F.encoding 0)
  exact congrComputes run (fun p=>by simp [post])

def pre (r : V.Input) := (query M r,(V.count0 r,V.count1 r))
def preComputes : Computes V.encoding (pairEncoding targetEncoding countsEncoding) (pre M) :=
  pairComputes (queryComputes M) countsComputes

include hM hs in
theorem answer_recovery (r : V.Input) :
    post M (targetValue F M (query M r),(V.count0 r,V.count1 r))=(V.value r : K) := by
  by_cases hb : V.count0 r=V.count1 r
  · rw [post,if_pos hb]
    change (targetValue F M (query M r)*(U.scale M true)⁻¹^V.count0 r)*(U.scale M false)⁻¹^V.count1 r=_
    rw [balanced_query_value F M hM hs r hb,
      mul_assoc (U.scale M true^V.count0 r) (U.scale M false^V.count1 r) (V.value r : K),
      ScalarPower.cancel_scale_power (U.scale M true) _ (DenseEOUnitLocal.scale_nonzero M hs true),
      ScalarPower.cancel_scale_power (U.scale M false) _ (DenseEOUnitLocal.scale_nonzero M hs false)]
  · rw [post,if_neg hb,V.zero_of_unbalanced r hb]

/-- Closed physical source from literal coefficient conditions and an actual
fixed presentation. The final q+01 source retains the supplied fixed q field. -/
def controlled : LengthControlledOracleReduction V.encoding F.encoding targetEncoding F.encoding
    (V.value (K:=K)) (targetValue F M) :=
  Holant.LocalDrafts.Hardness.ControlledCap.controlledContextOfEq
    (preComputes M) (postComputes F M) ((targetTables F M).outputBound F)
    (V.value (K:=K)) (fun r=>(answer_recovery F M hM hs r).symm)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.DenseEOUnitCompiler
