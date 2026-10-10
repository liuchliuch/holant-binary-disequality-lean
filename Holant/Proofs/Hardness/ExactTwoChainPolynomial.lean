import Holant.Proofs.Hardness.ExactTwoChainQueries
import Holant.Proofs.BinaryInterpolation.RawPolynomial
import Holant.Complexity.BinaryInterpolation.WeightFormulas

/-! The actual four-port chain queries recover the all-E partition. Their
normalization is explicit: E+2^k B=2^k(B+2^(-k)E). The original serialized
E-count supplies the polynomial degree and every generated denominator is
nonzero in characteristic zero, including the zero-occurrence case. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainPolynomial
open Holant Holant.Complexity BinaryInterpolation FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity Input TargetInput value sample queries)
end Q
namespace RP
export Holant.LocalDrafts.BinaryInterpolation.RawPolynomial
  (pencil right polynomial polynomial_degree polynomial_eval polynomial_top replacement_same_arity recover)
end RP
namespace S
export ExactTwoSignatures (q E B spectral spectral_linear)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K : Type} [Field K] [CharZero K]

def targetSignatures (i : Fin 1) : Signature K (Q.arity i.val) := S.q
def sourceSignatures (i : Fin 2) : Signature K (Q.arity i.val) := if i.val=1 then S.E else S.q
def leftSignatures (i : Fin 2) : Signature K (Q.arity i.val) := if i.val=1 then S.B else S.q

def kernels (_ : Fin 1) : Kernel K := Signature.disequality

def sourceValue (r : Q.Input) : K :=
  (r.val.realize r.property sourceSignatures kernels).denote Fin.elim0

def targetValue (r : Q.TargetInput) : K :=
  (r.val.realize r.property targetSignatures kernels).denote Fin.elim0

def nodes (m : ℕ) := WeightFormulas.nodes true ((2 : K)⁻¹) m
def scales (m : ℕ) := WeightFormulas.scales (2 : K) m

theorem nodes_injective (m : ℕ) : Function.Injective (nodes (K:=K) m) := by
  intro i j hij
  apply ExactTwoChain.nodes_injective (K:=K) m
  change ((2 : K)⁻¹)^(i.val+1)=((2 : K)⁻¹)^(j.val+1) at hij
  simpa only [inv_pow,inv_inv] using congrArg Inv.inv hij

theorem scales_nonzero (m : ℕ) (i : Fin (m+1)) : scales (K:=K) m i≠0 :=
  pow_ne_zero _ (by norm_num)

theorem spectral_normalized (k : ℕ) : S.spectral ((2 : K)^k)=
    (2 : K)^k • (S.B+((2 : K)⁻¹)^k • S.E) := by
  rw [S.spectral_linear]
  funext x
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,inv_pow]
  have h : (2 : K)^k≠0 := pow_ne_zero _ (by norm_num)
  field_simp
  <;> ring

theorem local_identity (k : ℕ) (i : Fin 2) :
    (⟨(ExactTwoChainOccurrence.templates Q.arity 1 0 0 k i.val).boundary,
      ((ExactTwoChainOccurrence.templates Q.arity 1 0 0 k i.val).network
        (ExactTwoChainQueries.template_hypotheses k i.val i.isLt).1
        targetSignatures (kernels (K:=K))).denote⟩ : AnySignature K)=
      ⟨Q.arity i.val,(if i.val=1 then (2 : K)^k else 1) •
        RP.pencil sourceSignatures leftSignatures sourceSignatures 1 (((2 : K)⁻¹)^k) i⟩ := by
  fin_cases i
  · change (⟨4,((identityTemplate Q.arity 0).network
        (identityTemplate_wellFormed Q.arity (0 : Fin 1)) targetSignatures (kernels (K:=K))).denote⟩ : AnySignature K)=⟨4,(1 : K) • S.q⟩
    simp only [one_smul]
    apply congrArg (fun f : Signature K 4=>(⟨4,f⟩ : AnySignature K))
    exact identityTemplate_denote Q.arity (0 : Fin 1) targetSignatures kernels
  · change (⟨4,((ExactTwoChainRecords.explicitTemplate 0 0 k).network
        (ExactTwoChainRecords.valid Q.arity (0 : Fin 1) rfl (0 : Fin 1) k)
        targetSignatures (kernels (K:=K))).denote⟩ : AnySignature K)=
        ⟨4,(2 : K)^k • (S.B+((2 : K)⁻¹)^k • S.E)⟩
    apply congrArg (fun f : Signature K 4=>(⟨4,f⟩ : AnySignature K))
    exact (ExactTwoChainRecords.denote Q.arity (0 : Fin 1) rfl (0 : Fin 1) k
      (targetSignatures (K:=K)) kernels rfl rfl).trans (spectral_normalized k)

theorem query_value (r : Q.Input) (k : ℕ) :
    targetValue (Q.value (k,r))=(2 : K)^(k*occurrences 1 r.val)*
      (r.val.realize r.property
        (RP.pencil sourceSignatures leftSignatures sourceSignatures 1 (((2 : K)⁻¹)^k))
        kernels).denote Fin.elim0 := by
  obtain ⟨hq,he⟩ := RP.replacement_same_arity r.val r.property
    (RP.pencil sourceSignatures leftSignatures sourceSignatures 1 (((2 : K)⁻¹)^k))
    kernels 1 (ExactTwoChainOccurrence.templates Q.arity 1 0 0 k)
    (fun i hi=>(ExactTwoChainQueries.template_hypotheses k i hi).1)
    (ExactTwoChainQueries.template_arity k) targetSignatures ((2 : K)^k) (local_identity k)
  simpa only [targetValue,Q.value,ExactTwoChainOccurrence.raw_eq_replace,←pow_mul] using he

def values (r : Q.Input) (i : Fin (occurrences 1 r.val+1)) : K := targetValue (Q.sample ⟨r,i⟩)
def denominators (r : Q.Input) : Fin (occurrences 1 r.val+1) → K :=
  queryDenominator (nodes (occurrences 1 r.val)) (scales (occurrences 1 r.val))

theorem denominator_nonzero (r : Q.Input) : commonDenominator (denominators (K:=K) r)≠0 :=
  commonDenominator_ne_zero _ (queryDenominator_ne_zero _ _ (nodes_injective _) (scales_nonzero _))

theorem quotient_correct (r : Q.Input) :
    commonNumerator (denominators r) (values (K:=K) r)/commonDenominator (denominators r)=sourceValue r := by
  rw [denominators,←recover_normalized_common _ _ _ (nodes_injective _) (scales_nonzero _)]
  have hv : (fun i : Fin (occurrences 1 r.val+1)=>values (K:=K) r i/scales _ i^occurrences 1 r.val)=
      (fun i=>(r.val.realize r.property
        (RP.pencil sourceSignatures leftSignatures sourceSignatures 1 (nodes _ i)) kernels).denote Fin.elim0) := by
    funext i
    rw [values,Q.sample,query_value]
    simp only [nodes,scales,WeightFormulas.nodes,WeightFormulas.scales,ite_true,pow_mul]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (scales_nonzero _ i))
  rw [hv,RP.recover r.val r.property sourceSignatures leftSignatures sourceSignatures kernels 1 _ (nodes_injective _)]
  have hr : RP.right (s:=2) (arity:=Q.arity) (sourceSignatures (K:=K)) sourceSignatures 1=sourceSignatures := by
    funext i x
    simp [RP.right]
  rw [hr]
  rfl

theorem answers_order (r : Q.Input) : (Q.queries r).map (targetValue (K:=K))=List.ofFn (values r) := by
  simp only [Q.queries,Holant.Complexity.BinaryInterpolation.Chains.Compiler.Batch.samples,
    List.map_map,List.ofFn_eq_map,values,Function.comp_def]
  rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainPolynomial
