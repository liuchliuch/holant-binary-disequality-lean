import Holant.Proofs.Hardness.PositiveBoundarySignatures
import Holant.Proofs.Hardness.ExactTwoChainControlled
import Holant.Proofs.Reductions.ControlledCap
import Holant.Proofs.Platonic.PhysicalCostComposition
import Holant.NetworkAlgebra

/-! Actual positive-boundary [original q,H] interpolation to the original q.
Every H is replaced by a positive original-q chain. The geometric normalization
uses nu=b-a, which may be negative; only the proof coordinates are normalized.
Original unmarked q rows are left intact. The original H occurrence scan drives
an actual c^(-m) field programme in the unchanged field answer presentation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveBoundaryInterpolation
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines OracleBatch BinaryInterpolation FixedGadgetSubstitution
open scoped BigOperators
namespace Q
export ExactTwoChainQueries (arity Input TargetInput value sample queries sourceEncoding targetEncoding)
end Q
namespace RP
export Holant.LocalDrafts.BinaryInterpolation.RawPolynomial
  (pencil right replacement_same_arity recover)
end RP
namespace S
export ThreeModeSignatures (original)
export PositiveBoundarySignatures (H J)
end S
namespace M
export ExactTwoChainMachine (Data values interpolatedValue pre machine timePolynomial execution reduction)
end M
namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable (a b c : K)

def targetSignatures (i : Fin 1) : Signature K (Q.arity i.val) := S.original a b c
def sourceSignatures (i : Fin 2) : Signature K (Q.arity i.val) := if i.val=1 then c • S.H else S.original a b c
def literalSignatures (i : Fin 2) : Signature K (Q.arity i.val) := if i.val=1 then S.H else S.original a b c
def leftSignatures (i : Fin 2) : Signature K (Q.arity i.val) := if i.val=1 then (b-a) • S.J else S.original a b c
def kernels (_ : Fin 1) : Kernel K := Signature.disequality

def scaledValue (r : Q.Input) : K :=
  (r.val.realize r.property (sourceSignatures a b c) kernels).denote Fin.elim0

def sourceValue (r : Q.Input) : K :=
  (r.val.realize r.property (literalSignatures a b c) kernels).denote Fin.elim0

def targetValue (r : Q.TargetInput) : K :=
  (r.val.realize r.property (targetSignatures a b c) kernels).denote Fin.elim0

def nodes (m : ℕ) := WeightFormulas.nodes true (c/(b-a)) m
def scales (m : ℕ) := WeightFormulas.scales (b-a) m

variable (hc : c=a+b) (hc0 : c≠0) (hnu : b-a≠0)
  (hinf : ∀n : ℕ,0<n → (c/(b-a))^n≠1)

include hc0 hnu hinf in
theorem nodes_injective (m : ℕ) : Function.Injective (nodes a b c m) := by
  apply geometric_nodes_injective (c/(b-a)) (div_ne_zero hc0 hnu)
  exact hinf

include hnu in
theorem scales_nonzero (m : ℕ) (i : Fin (m+1)) : scales a b m i≠0 :=
  pow_ne_zero _ hnu

include hc hnu in
theorem local_identity (k : ℕ) (i : Fin 2) :
    (⟨(ExactTwoChainOccurrence.templates Q.arity 1 0 0 k i.val).boundary,
      ((ExactTwoChainOccurrence.templates Q.arity 1 0 0 k i.val).network
        (ExactTwoChainQueries.template_hypotheses k i.val i.isLt).1
        (targetSignatures a b c) (kernels (K:=K))).denote⟩ : AnySignature K)=
      ⟨Q.arity i.val,(if i.val=1 then (b-a)^k else 1) •
        RP.pencil (sourceSignatures a b c) (leftSignatures a b c) (sourceSignatures a b c) 1 ((c/(b-a))^k) i⟩ := by
  fin_cases i
  · change (⟨4,((identityTemplate Q.arity 0).network
        (identityTemplate_wellFormed Q.arity (0 : Fin 1)) (targetSignatures a b c) (kernels (K:=K))).denote⟩ : AnySignature K)=
        ⟨4,(1 : K) • S.original a b c⟩
    simp only [one_smul]
    apply congrArg (fun f : Signature K 4=>(⟨4,f⟩ : AnySignature K))
    exact identityTemplate_denote Q.arity (0 : Fin 1) (targetSignatures a b c) kernels
  · change (⟨4,((ExactTwoChainRecords.explicitTemplate 0 0 k).network
        (ExactTwoChainRecords.valid Q.arity (0 : Fin 1) rfl (0 : Fin 1) k)
        (targetSignatures a b c) (kernels (K:=K))).denote⟩ : AnySignature K)=
        ⟨4,(b-a)^k • ((b-a) • S.J+(c/(b-a))^k • (c • S.H))⟩
    apply congrArg (fun f : Signature K 4=>(⟨4,f⟩ : AnySignature K))
    exact (ThreeModeChain.denote Q.arity (0 : Fin 1) rfl (0 : Fin 1) a b c k
      (targetSignatures a b c) kernels rfl rfl).trans (PositiveBoundarySignatures.normalized a b c hc hnu k)

include hc hnu in
theorem query_value (r : Q.Input) (k : ℕ) :
    targetValue a b c (Q.value (k,r))=(b-a)^(k*occurrences 1 r.val)*
      (r.val.realize r.property
        (RP.pencil (sourceSignatures a b c) (leftSignatures a b c) (sourceSignatures a b c) 1 ((c/(b-a))^k))
        kernels).denote Fin.elim0 := by
  obtain ⟨hq,he⟩ := RP.replacement_same_arity r.val r.property
    (RP.pencil (sourceSignatures a b c) (leftSignatures a b c) (sourceSignatures a b c) 1 ((c/(b-a))^k))
    kernels 1 (ExactTwoChainOccurrence.templates Q.arity 1 0 0 k)
    (fun i hi=>(ExactTwoChainQueries.template_hypotheses k i hi).1)
    (ExactTwoChainQueries.template_arity k) (targetSignatures a b c) ((b-a)^k) (local_identity a b c hc hnu k)
  simpa only [targetValue,Q.value,ExactTwoChainOccurrence.raw_eq_replace,←pow_mul] using he

def values (r : Q.Input) (i : Fin (occurrences 1 r.val+1)) : K := targetValue a b c (Q.sample ⟨r,i⟩)
def denominators (r : Q.Input) : Fin (occurrences 1 r.val+1) → K :=
  queryDenominator (nodes a b c (occurrences 1 r.val)) (scales a b (occurrences 1 r.val))

include hc0 hnu hinf in
theorem denominator_nonzero (r : Q.Input) : BinaryInterpolation.commonDenominator (denominators a b c r)≠0 :=
  commonDenominator_ne_zero _ (queryDenominator_ne_zero _ _
    (nodes_injective a b c hc0 hnu hinf _) (scales_nonzero a b hnu _))

include hc hc0 hnu hinf in
theorem quotient_correct (r : Q.Input) :
    commonNumerator (denominators a b c r) (values a b c r)/BinaryInterpolation.commonDenominator (denominators a b c r)=scaledValue a b c r := by
  rw [denominators,←recover_normalized_common _ _ _ (nodes_injective a b c hc0 hnu hinf _) (scales_nonzero a b hnu _)]
  have he : (fun i : Fin (occurrences 1 r.val+1)=>values a b c r i/(scales a b _ i)^occurrences 1 r.val)=
      (fun i=>(r.val.realize r.property
        (RP.pencil (sourceSignatures a b c) (leftSignatures a b c) (sourceSignatures a b c) 1 (nodes a b c _ i)) kernels).denote Fin.elim0) := by
    funext i
    rw [values,Q.sample,query_value a b c hc hnu]
    simp only [nodes,scales,WeightFormulas.nodes,WeightFormulas.scales,ite_true,pow_mul]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (scales_nonzero a b hnu _ i))
  rw [he,RP.recover r.val r.property (sourceSignatures a b c) (leftSignatures a b c) (sourceSignatures a b c)
    kernels 1 _ (nodes_injective a b c hc0 hnu hinf _)]
  have hr : RP.right (s:=2) (arity:=Q.arity) (sourceSignatures a b c) (sourceSignatures a b c) 1=sourceSignatures a b c := by
    funext i x
    simp [RP.right]
  rw [hr]
  rfl

/-- Exactly one factor c for each original H label1, including zero occurrences. -/
theorem scaled_value (r : Q.Input) : scaledValue a b c r=c^occurrences 1 r.val*sourceValue a b c r := by
  let N := r.val.realize r.property (literalSignatures a b c) (kernels (K:=K))
  let scale : Fin N.shape.vertices → K := fun j=>if (r.val.vertices.get j).1=1 then c else 1
  have he : (N.scaleVertices scale).denote=(r.val.realize r.property (sourceSignatures a b c) kernels).denote := by
    apply Network.denote_congr (r.val.shape r.property)
    · intro j x
      by_cases hj : (r.val.vertices.get j).1=1 <;>
        simp_all [N,scale,Network.scaleVertices,RawClosedNetwork.realize,RawClosedNetwork.signatureLabel,
          sourceSignatures,literalSignatures,Pi.smul_apply,smul_eq_mul]
    · intro j x y
      rfl
  have hp := N.denote_scaleVertices scale Fin.elim0
  rw [he] at hp
  change scaledValue a b c r=(∏j : Fin r.val.vertices.length,if (r.val.vertices.get j).1=1 then c else 1)*sourceValue a b c r at hp
  simpa only [scale_product] using hp

variable {d : ℕ} (F : FixedField K d)

def targetTables : ExactSignatureTables d 1 1 Q.arity where
  vertex i x := F.decode.symm (targetSignatures a b c i x)
  edge i x y := F.decode.symm (kernels i x y)

def scaledTables : ExactSignatureTables d 2 1 Q.arity where
  vertex i x := F.decode.symm (sourceSignatures a b c i x)
  edge i x y := F.decode.symm (kernels i x y)

theorem target_evaluate (r : Q.TargetInput) : (targetTables a b c F).evaluate F r=targetValue a b c r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,targetTables,LinearEquiv.apply_symm_apply]
  rfl

theorem scaled_evaluate (r : Q.Input) : (scaledTables a b c F).evaluate F r=scaledValue a b c r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,scaledTables,LinearEquiv.apply_symm_apply]
  rfl

def data : M.Data F (targetTables a b c F) where
  gamma := b-a
  rho := c/(b-a)
  geometric := true

theorem values_eq (r : Q.Input) (i : Fin (occurrences 1 r.val+1)) :
    M.values (data a b c F) r i=values a b c r i := target_evaluate a b c F _

include hc hc0 hnu hinf in
theorem value_correct (r : Q.Input) : M.interpolatedValue (data a b c F) r=scaledValue a b c r := by
  have he : M.values (data a b c F) r=values a b c r := funext (values_eq a b c F r)
  change commonNumerator _ (M.values (data a b c F) r)/BinaryInterpolation.commonDenominator _=scaledValue a b c r
  rw [he]
  exact quotient_correct a b c hc hc0 hnu hinf r

def targetOutput : PolynomialOutputBound Q.targetEncoding F.encoding (targetValue a b c) where
  bound := ((targetTables a b c F).outputBound F).bound
  length_le r := by
    rw [←target_evaluate a b c F r]
    exact ((targetTables a b c F).outputBound F).length_le r

def scaledOutput : PolynomialOutputBound Q.sourceEncoding F.encoding (scaledValue a b c) where
  bound := ((scaledTables a b c F).outputBound F).bound
  length_le r := by
    rw [←scaled_evaluate a b c F r]
    exact ((scaledTables a b c F).outputBound F).length_le r

def scaledSource : LengthControlledOracleReduction Q.sourceEncoding F.encoding Q.targetEncoding F.encoding
    (scaledValue a b c) (targetValue a b c) where
  reduction := {
    machine := M.machine (data a b c F)
    time := M.timePolynomial (data a b c F)
    correct oracle ho r := by
      have ho' : RepresentsOracle Q.targetEncoding F.encoding ((targetTables a b c F).evaluate F) oracle := by
        intro q
        rw [target_evaluate]
        exact ho q
      rw [←value_correct a b c hc hc0 hnu hinf F r]
      exact (M.reduction (data a b c F)).correct oracle ho' r }
  targetOutput := targetOutput a b c F
  queryBound := (M.pre (data a b c F)).outputBound.bound
  safeQuery oracle ho r t cfg hr hq := by
    have ho' : RepresentsOracle Q.targetEncoding F.encoding ((targetTables a b c F).evaluate F) oracle := by
      intro q
      rw [target_evaluate]
      exact ho q
    obtain ⟨n,_,ht⟩ := M.execution (data a b c F) oracle ho' r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t cfg hr hq
    obtain ⟨q,hmem,he⟩ := List.mem_map.mp hm
    exact ⟨q,he.symm,(member_length_le _ _ hm).trans (query_context_length_le (M.pre (data a b c F)) r).1⟩

def correctionPre : Computes Q.sourceEncoding
    (pairEncoding Q.sourceEncoding GraphPreprocessing.UnaryBinary.unaryEncoding)
    (fun r : Q.Input=>(r,occurrences 1 r.val)) :=
  pairComputes (identityComputes Q.sourceEncoding) (Compiler.occurrencesComputes 2 1 Q.arity 1)

/-- Real original-input occurrence scan, one intermediate query, and scalar-power decoder. -/
def correctionSource : LengthControlledOracleReduction Q.sourceEncoding F.encoding Q.sourceEncoding F.encoding
    (sourceValue a b c) (scaledValue a b c) :=
  Holant.LocalDrafts.Hardness.ControlledCap.controlledContextOfEq correctionPre (ScalarPower.correction F c)
    (scaledOutput a b c F) (sourceValue a b c) (by
      intro r
      change sourceValue a b c r=scaledValue a b c r*(c⁻¹)^occurrences 1 r.val
      rw [scaled_value,ScalarPower.cancel_scale_power c _ hc0])

/-- The final endpoint is literal H, rather than cH. Both reductions use the same F bytes. -/
def source : LengthControlledOracleReduction Q.sourceEncoding F.encoding Q.targetEncoding F.encoding
    (sourceValue a b c) (targetValue a b c) :=
  Compose.composeControlled (correctionSource a b c hc0 F) (scaledSource a b c hc hc0 hnu hinf F)

def outputs (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Q.targetEncoding F.encoding (targetValue a b c) oracle) (r : Q.Input) :
    (source a b c hc hc0 hnu hinf F).reduction.machine.OutputsInTime oracle (Q.sourceEncoding.encode r)
      (F.encoding.encode (sourceValue a b c r))
      ((source a b c hc hc0 hnu hinf F).reduction.time.eval (Q.sourceEncoding.encode r).length) :=
  (source a b c hc hc0 hnu hinf F).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveBoundaryInterpolation
