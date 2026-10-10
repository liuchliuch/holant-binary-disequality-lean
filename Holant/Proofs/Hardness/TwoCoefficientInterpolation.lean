import Holant.Proofs.Hardness.TwoCoefficientChain
import Holant.Proofs.Hardness.ExactTwoChainControlled
import Holant.Proofs.Reductions.ControlledCap
import Holant.Proofs.Platonic.PhysicalCostComposition
import Holant.NetworkAlgebra

/-! Same-field physical interpolation from [aE+bB,E] to aE+bB. The existing
four-port query compiler and field interpreter are retained verbatim. The
internally counted original E occurrences drive a real a^(-m) answer correction.
This intermediate factory takes a non-root-of-unity proof; its outer finite
escape producer derives that proof internally for the original coefficients. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientInterpolation
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
export TwoCoefficientSignatures (weighted)
export ExactTwoSignatures (E B)
end S
namespace D
export TwoCoefficientData (ratio InfiniteRatio)
end D
namespace M
export ExactTwoChainMachine (Data values interpolatedValue pre machine timePolynomial execution reduction)
end M
namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable (u v : K)

def targetSignatures (i : Fin 1) : Signature K (Q.arity i.val) := S.weighted u v
def sourceSignatures (i : Fin 2) : Signature K (Q.arity i.val) := if i.val=1 then u • S.E else S.weighted u v
def literalSignatures (i : Fin 2) : Signature K (Q.arity i.val) := if i.val=1 then S.E else S.weighted u v
def leftSignatures (i : Fin 2) : Signature K (Q.arity i.val) := if i.val=1 then v • S.B else S.weighted u v
def kernels (_ : Fin 1) : Kernel K := Signature.disequality

def scaledValue (r : Q.Input) : K :=
  (r.val.realize r.property (sourceSignatures u v) kernels).denote Fin.elim0

def sourceValue (r : Q.Input) : K :=
  (r.val.realize r.property (literalSignatures u v) kernels).denote Fin.elim0

def targetValue (r : Q.TargetInput) : K :=
  (r.val.realize r.property (targetSignatures u v) kernels).denote Fin.elim0

def nodes (m : ℕ) := WeightFormulas.nodes true (u/(2*v)) m
def scales (m : ℕ) := WeightFormulas.scales (2*v) m

variable (hu : u≠0) (hv : v≠0) (hinf : D.InfiniteRatio (u,v))

include hu hv hinf in
theorem nodes_injective (m : ℕ) : Function.Injective (nodes u v m) := by
  apply geometric_nodes_injective (u/(2*v)) (div_ne_zero hu (mul_ne_zero (by norm_num) hv))
  exact hinf

include hv in
theorem scales_nonzero (m : ℕ) (i : Fin (m+1)) : scales v m i≠0 :=
  pow_ne_zero _ (mul_ne_zero (by norm_num) hv)

include hv in
theorem local_identity (k : ℕ) (i : Fin 2) :
    (⟨(ExactTwoChainOccurrence.templates Q.arity 1 0 0 k i.val).boundary,
      ((ExactTwoChainOccurrence.templates Q.arity 1 0 0 k i.val).network
        (ExactTwoChainQueries.template_hypotheses k i.val i.isLt).1
        (targetSignatures u v) (kernels (K:=K))).denote⟩ : AnySignature K)=
      ⟨Q.arity i.val,(if i.val=1 then (2*v)^k else 1) •
        RP.pencil (sourceSignatures u v) (leftSignatures u v) (sourceSignatures u v) 1 ((u/(2*v))^k) i⟩ := by
  fin_cases i
  · change (⟨4,((identityTemplate Q.arity 0).network
        (identityTemplate_wellFormed Q.arity (0 : Fin 1)) (targetSignatures u v) (kernels (K:=K))).denote⟩ : AnySignature K)=
        ⟨4,(1 : K) • S.weighted u v⟩
    simp only [one_smul]
    apply congrArg (fun f : Signature K 4=>(⟨4,f⟩ : AnySignature K))
    exact identityTemplate_denote Q.arity (0 : Fin 1) (targetSignatures u v) kernels
  · change (⟨4,((ExactTwoChainRecords.explicitTemplate 0 0 k).network
        (ExactTwoChainRecords.valid Q.arity (0 : Fin 1) rfl (0 : Fin 1) k)
        (targetSignatures u v) (kernels (K:=K))).denote⟩ : AnySignature K)=
        ⟨4,(2*v)^k • (v • S.B+(u/(2*v))^k • (u • S.E))⟩
    apply congrArg (fun f : Signature K 4=>(⟨4,f⟩ : AnySignature K))
    exact (TwoCoefficientChain.denote Q.arity (0 : Fin 1) rfl (0 : Fin 1) u v k
      (targetSignatures u v) kernels rfl rfl).trans (TwoCoefficientChain.normalized u v hv k)

include hv in
theorem query_value (r : Q.Input) (k : ℕ) :
    targetValue u v (Q.value (k,r))=(2*v)^(k*occurrences 1 r.val)*
      (r.val.realize r.property
        (RP.pencil (sourceSignatures u v) (leftSignatures u v) (sourceSignatures u v) 1 ((u/(2*v))^k))
        kernels).denote Fin.elim0 := by
  obtain ⟨hq,he⟩ := RP.replacement_same_arity r.val r.property
    (RP.pencil (sourceSignatures u v) (leftSignatures u v) (sourceSignatures u v) 1 ((u/(2*v))^k))
    kernels 1 (ExactTwoChainOccurrence.templates Q.arity 1 0 0 k)
    (fun i hi=>(ExactTwoChainQueries.template_hypotheses k i hi).1)
    (ExactTwoChainQueries.template_arity k) (targetSignatures u v) ((2*v)^k) (local_identity u v hv k)
  simpa only [targetValue,Q.value,ExactTwoChainOccurrence.raw_eq_replace,←pow_mul] using he

def values (r : Q.Input) (i : Fin (occurrences 1 r.val+1)) : K := targetValue u v (Q.sample ⟨r,i⟩)
def denominators (r : Q.Input) : Fin (occurrences 1 r.val+1) → K :=
  queryDenominator (nodes u v (occurrences 1 r.val)) (scales v (occurrences 1 r.val))

include hu hv hinf in
theorem denominator_nonzero (r : Q.Input) : BinaryInterpolation.commonDenominator (denominators u v r)≠0 :=
  commonDenominator_ne_zero _ (queryDenominator_ne_zero _ _
    (nodes_injective u v hu hv hinf _) (scales_nonzero v hv _))

include hu hv hinf in
theorem quotient_correct (r : Q.Input) :
    commonNumerator (denominators u v r) (values u v r)/BinaryInterpolation.commonDenominator (denominators u v r)=scaledValue u v r := by
  rw [denominators,←recover_normalized_common _ _ _ (nodes_injective u v hu hv hinf _) (scales_nonzero v hv _)]
  have he : (fun i : Fin (occurrences 1 r.val+1)=>values u v r i/(scales v _ i)^occurrences 1 r.val)=
      (fun i=>(r.val.realize r.property
        (RP.pencil (sourceSignatures u v) (leftSignatures u v) (sourceSignatures u v) 1 (nodes u v _ i)) kernels).denote Fin.elim0) := by
    funext i
    rw [values,Q.sample,query_value u v hv]
    simp only [nodes,scales,WeightFormulas.nodes,WeightFormulas.scales,ite_true,pow_mul]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (scales_nonzero v hv _ i))
  rw [he,RP.recover r.val r.property (sourceSignatures u v) (leftSignatures u v) (sourceSignatures u v)
    kernels 1 _ (nodes_injective u v hu hv hinf _)]
  have hr : RP.right (s:=2) (arity:=Q.arity) (sourceSignatures u v) (sourceSignatures u v) 1=sourceSignatures u v := by
    funext i x
    simp [RP.right]
  rw [hr]
  rfl

/-- Exactly one factor u for each original label1, including zero occurrences. -/
theorem scaled_value (r : Q.Input) : scaledValue u v r=u^occurrences 1 r.val*sourceValue u v r := by
  let N := r.val.realize r.property (literalSignatures u v) (kernels (K:=K))
  let c : Fin N.shape.vertices → K := fun j=>if (r.val.vertices.get j).1=1 then u else 1
  have he : (N.scaleVertices c).denote=(r.val.realize r.property (sourceSignatures u v) kernels).denote := by
    apply Network.denote_congr (r.val.shape r.property)
    · intro j x
      by_cases hj : (r.val.vertices.get j).1=1 <;>
        simp_all [N,c,Network.scaleVertices,RawClosedNetwork.realize,RawClosedNetwork.signatureLabel,
          sourceSignatures,literalSignatures,Pi.smul_apply,smul_eq_mul]
    · intro j x y
      rfl
  have hp := N.denote_scaleVertices c Fin.elim0
  rw [he] at hp
  change scaledValue u v r=(∏j : Fin r.val.vertices.length,if (r.val.vertices.get j).1=1 then u else 1)*sourceValue u v r at hp
  simpa only [scale_product] using hp

variable {d : ℕ} (F : FixedField K d)

def targetTables : ExactSignatureTables d 1 1 Q.arity where
  vertex i x := F.decode.symm (targetSignatures u v i x)
  edge i x y := F.decode.symm (kernels i x y)

def scaledTables : ExactSignatureTables d 2 1 Q.arity where
  vertex i x := F.decode.symm (sourceSignatures u v i x)
  edge i x y := F.decode.symm (kernels i x y)

theorem target_evaluate (r : Q.TargetInput) : (targetTables u v F).evaluate F r=targetValue u v r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,targetTables,LinearEquiv.apply_symm_apply]
  rfl

theorem scaled_evaluate (r : Q.Input) : (scaledTables u v F).evaluate F r=scaledValue u v r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,scaledTables,LinearEquiv.apply_symm_apply]
  rfl

def data : M.Data F (targetTables u v F) where
  gamma := 2*v
  rho := u/(2*v)
  geometric := true

theorem values_eq (r : Q.Input) (i : Fin (occurrences 1 r.val+1)) :
    M.values (data u v F) r i=values u v r i := target_evaluate u v F _

include hu hv hinf in
theorem value_correct (r : Q.Input) : M.interpolatedValue (data u v F) r=scaledValue u v r := by
  have he : M.values (data u v F) r=values u v r := funext (values_eq u v F r)
  change commonNumerator _ (M.values (data u v F) r)/BinaryInterpolation.commonDenominator _=scaledValue u v r
  rw [he]
  exact quotient_correct u v hu hv hinf r

def targetOutput : PolynomialOutputBound Q.targetEncoding F.encoding (targetValue u v) where
  bound := ((targetTables u v F).outputBound F).bound
  length_le r := by
    rw [←target_evaluate u v F r]
    exact ((targetTables u v F).outputBound F).length_le r

def scaledOutput : PolynomialOutputBound Q.sourceEncoding F.encoding (scaledValue u v) where
  bound := ((scaledTables u v F).outputBound F).bound
  length_le r := by
    rw [←scaled_evaluate u v F r]
    exact ((scaledTables u v F).outputBound F).length_le r

def scaledSource : LengthControlledOracleReduction Q.sourceEncoding F.encoding Q.targetEncoding F.encoding
    (scaledValue u v) (targetValue u v) where
  reduction := {
    machine := M.machine (data u v F)
    time := M.timePolynomial (data u v F)
    correct oracle ho r := by
      have ho' : RepresentsOracle Q.targetEncoding F.encoding ((targetTables u v F).evaluate F) oracle := by
        intro q
        rw [target_evaluate]
        exact ho q
      rw [←value_correct u v hu hv hinf F r]
      exact (M.reduction (data u v F)).correct oracle ho' r }
  targetOutput := targetOutput u v F
  queryBound := (M.pre (data u v F)).outputBound.bound
  safeQuery oracle ho r t c hr hq := by
    have ho' : RepresentsOracle Q.targetEncoding F.encoding ((targetTables u v F).evaluate F) oracle := by
      intro q
      rw [target_evaluate]
      exact ho q
    obtain ⟨n,_,ht⟩ := M.execution (data u v F) oracle ho' r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t c hr hq
    obtain ⟨q,hmem,he⟩ := List.mem_map.mp hm
    exact ⟨q,he.symm,(member_length_le _ _ hm).trans (query_context_length_le (M.pre (data u v F)) r).1⟩

def correctionPre : Computes Q.sourceEncoding
    (pairEncoding Q.sourceEncoding GraphPreprocessing.UnaryBinary.unaryEncoding)
    (fun r : Q.Input=>(r,occurrences 1 r.val)) :=
  pairComputes (identityComputes Q.sourceEncoding) (Compiler.occurrencesComputes 2 1 Q.arity 1)

/-- Real original-input occurrence scan, one intermediate query, and scalar-power decoder. -/
def correctionSource : LengthControlledOracleReduction Q.sourceEncoding F.encoding Q.sourceEncoding F.encoding
    (sourceValue u v) (scaledValue u v) :=
  Holant.LocalDrafts.Hardness.ControlledCap.controlledContextOfEq correctionPre (ScalarPower.correction F u)
    (scaledOutput u v F) (sourceValue u v) (by
      intro r
      change sourceValue u v r=scaledValue u v r*(u⁻¹)^occurrences 1 r.val
      rw [scaled_value,ScalarPower.cancel_scale_power u _ hu])

/-- The final endpoint is literal E, rather than uE. Both reductions use the same F bytes. -/
def source : LengthControlledOracleReduction Q.sourceEncoding F.encoding Q.targetEncoding F.encoding
    (sourceValue u v) (targetValue u v) :=
  Compose.composeControlled (correctionSource u v hu F) (scaledSource u v hu hv hinf F)

def outputs (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Q.targetEncoding F.encoding (targetValue u v) oracle) (r : Q.Input) :
    (source u v hu hv hinf F).reduction.machine.OutputsInTime oracle (Q.sourceEncoding.encode r)
      (F.encoding.encode (sourceValue u v r))
      ((source u v hu hv hinf F).reduction.time.eval (Q.sourceEncoding.encode r).length) :=
  (source u v hu hv hinf F).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientInterpolation
