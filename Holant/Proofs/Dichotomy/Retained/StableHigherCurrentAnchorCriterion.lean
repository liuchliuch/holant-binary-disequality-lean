import Holant.Tractable.Anchor
import Holant.EightVertex.ProductAnchor.NetworksData

/-! A literal Eq4 rules out the four exceptional tractability clauses for
its entire ordinary family. The remaining positive endpoint is exactly one
common affine, product, or local-affine basis, shared by every retained row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorCriterion
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev eq4 : Signature AlgebraicComplex 4 := equalityFour

theorem eq4_nonzero : eq4 ≠ 0 := by
  intro h
  have hh := congrFun h (fun _ => false)
  simpa [eq4,equalityFour] using hh

theorem eq4_not_arityTwo :
    ¬ SourceTensorClosure (fun n (_ : Signature AlgebraicComplex n) => n=1 ∨ n=2) eq4 := by
  classical
  rintro (zero | ⟨D,small,exactValue⟩)
  · exact eq4_nonzero zero
  have atFalse : D.value (fun _ => false) ≠ 0 := by rw [exactValue]; simp [eq4,equalityFour]
  have atTrue : D.value (fun _ => true) ≠ 0 := by rw [exactValue]; simp [eq4,equalityFour]
  have factorFalse (i : Fin D.count) : D.factor i (fun _ => false) ≠ 0 := by
    intro hz
    apply atFalse
    have hp : (∏j, D.factor j (fun _ => false))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    simp [TensorDecomposition.value,hp]
  have factorTrue (i : Fin D.count) : D.factor i (fun _ => true) ≠ 0 := by
    intro hz
    apply atTrue
    have hp : (∏j, D.factor j (fun _ => true))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    simp [TensorDecomposition.value,hp]
  let block := (D.ports.symm (0 : Fin 4)).1
  have short : D.arity block < 4 := by rcases small block with h | h <;> omega
  have missing : ¬Function.Surjective (fun j : Fin (D.arity block) => D.ports ⟨block,j⟩) := by
    intro hs
    have hcard := Fintype.card_le_of_surjective _ hs
    simp only [Fintype.card_fin] at hcard
    omega
  unfold Function.Surjective at missing
  push_neg at missing
  obtain ⟨outside,missing⟩ := missing
  have otherBlock : (D.ports.symm outside).1 ≠ block := by
    intro he
    rcases h : D.ports.symm outside with ⟨i,j⟩
    simp only [h] at he
    subst i
    apply missing j
    rw [←h]
    exact D.ports.apply_symm_apply outside
  let x : Fin 4 → Bool := fun p => decide ((D.ports.symm p).1=block)
  have xFalse : x outside=false := by simp [x,otherBlock]
  have xTrue : x 0=true := by simp [x,block]
  have nonzero : D.value x ≠ 0 := by
    apply mul_ne_zero (Units.ne_zero D.scale)
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have ports : (fun j => x (D.ports ⟨i,j⟩))=fun _ => decide (i=block) := by
      funext j
      simp [x]
    rw [ports]
    by_cases hi : i=block
    · simpa [hi] using factorTrue i
    · simpa [hi] using factorFalse i
  apply nonzero
  rw [exactValue]
  apply if_neg
  intro constant
  have h := constant outside
  rw [xFalse,xTrue] at h
  contradiction

/-- The only two supported Eq4 words give its exact tensor-action formula. -/
theorem action_eq4 (A : Kernel AlgebraicComplex) (x : Fin 4 → Bool) :
    Signature.coordinateAction (fun _ => A) eq4 x=
      (∏i,A (x i) false)+(∏i,A (x i) true) := by
  classical
  have he : eq4=(fun y => (if y=(fun _ => false) then 1 else 0)+
      (if y=(fun _ => true) then 1 else 0)) := by
    funext y
    cases hy : y 0 <;> simp [eq4,equalityFour,funext_iff,Fin.forall_fin_succ,hy]
  rw [he]
  simp [Signature.coordinateAction,mul_add,mul_ite,Finset.sum_add_distrib]

private theorem sqrtTwo_four : sqrtTwo^4=(4 : AlgebraicComplex) := by
  rw [show (4 : ℕ)=2*2 by decide,pow_mul,sqrtTwo_sq]
  norm_num

private theorem inverse_eq4_false :
    sourceKBasis.symm.action eq4 (fun _ => false)=(1/2 : AlgebraicComplex) := by
  change Signature.coordinateAction (fun _ => KInverse) eq4 (fun _ => false)=_
  rw [action_eq4]
  norm_num [KInverse,Fin.prod_univ_succ,←pow_two,imaginaryUnit_sq,sqrtTwo_sq,
    div_mul_div_comm,inv_pow] <;> ring_nf <;> norm_num [imaginaryUnit_sq,inv_pow,sqrtTwo_sq,sqrtTwo_four]

private theorem inverse_eq4_true :
    sourceKBasis.symm.action eq4 (fun _ => true)=(1/2 : AlgebraicComplex) := by
  change Signature.coordinateAction (fun _ => KInverse) eq4 (fun _ => true)=_
  rw [action_eq4]
  norm_num [KInverse,Fin.prod_univ_succ,←pow_two,imaginaryUnit_sq,sqrtTwo_sq,
    div_mul_div_comm,inv_pow] <;> ring_nf <;> norm_num [imaginaryUnit_sq,inv_pow,sqrtTwo_sq,sqrtTwo_four]

private theorem inverse_eq4_hole :
    sourceKBasis.symm.action eq4 ![true,false,false,false]=0 := by
  change Signature.coordinateAction (fun _ => KInverse) eq4 ![true,false,false,false]=_
  rw [action_eq4]
  norm_num [KInverse,Fin.prod_univ_succ,←pow_two,imaginaryUnit_sq,sqrtTwo_sq,
    div_mul_div_comm,inv_pow] <;> ring_nf <;> norm_num [imaginaryUnit_sq,inv_pow,sqrtTwo_sq,sqrtTwo_four]

theorem eq4_not_matching (opposite : Bool) :
    ¬ SourceTensorClosure (matchingImage opposite) eq4 := by
  rintro (zero | tensor)
  · exact eq4_nonzero zero
  have nonzeroFalse : sourceKBasis.symm.action eq4 (fun _ => false) ≠ 0 := by
    rw [inverse_eq4_false]; norm_num
  have nonzeroTrue : sourceKBasis.symm.action eq4 (fun _ => true) ≠ 0 := by
    rw [inverse_eq4_true]; norm_num
  cases opposite with
  | false =>
      have t := tensor.map_action sourceKBasis.inverse matchingImage_inverse_false
      exact (Signature.tensorClosure_oneHot_full_support t nonzeroFalse nonzeroTrue
        ![true,false,false,false]) inverse_eq4_hole
  | true =>
      have t := tensor.map_action (sourceKBasis.comp bitFlipBasis).inverse matchingImage_inverse_true
      change Signature.TensorClosure (fun _ f => Signature.OneHot f)
        ((sourceKBasis.comp bitFlipBasis).symm.action eq4) at t
      have h0 : (sourceKBasis.comp bitFlipBasis).symm.action eq4 (fun _ => false) ≠ 0 := by
        simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action,bitFlipBasis_symm,
          bitFlipBasis_action,Bool.not_false] using nonzeroTrue
      have h1 : (sourceKBasis.comp bitFlipBasis).symm.action eq4 (fun _ => true) ≠ 0 := by
        simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action,bitFlipBasis_symm,
          bitFlipBasis_action,Bool.not_true] using nonzeroFalse
      have h := Signature.tensorClosure_oneHot_full_support t h0 h1 ![false,true,true,true]
      have complement : (fun i : Fin 4 => !(![false,true,true,true] i))=![true,false,false,false] := by
        funext i
        fin_cases i <;> rfl
      simp only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action,bitFlipBasis_symm,
        bitFlipBasis_action,complement] at h
      exact h inverse_eq4_hole

theorem eq4_exclusions {F : SignatureFamily AlgebraicComplex}
    (mem : (⟨4,eq4⟩ : AnySignature AlgebraicComplex) ∈ F) :
    ¬OneSidedAlternative F ∧ ¬SingleWeightAlternative F ∧
      ¬ArityTwoAlternative F ∧ ¬MatchingAlternative F := by
  have hm : (⟨4,sourceKBasis.symm.action eq4⟩ : AnySignature AlgebraicComplex) ∈ kCoordinates F :=
    ⟨⟨4,eq4⟩,mem,rfl⟩
  have h0 : sourceKBasis.symm.action eq4 (fun _ => false) ≠ 0 := by rw [inverse_eq4_false]; norm_num
  have h1 : sourceKBasis.symm.action eq4 (fun _ => true) ≠ 0 := by rw [inverse_eq4_true]; norm_num
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨positive | negative,_⟩
    · have h := positive _ hm (fun _ => false) h0
      norm_num [Holant.charge,Holant.weight] at h
    · have h := negative _ hm (fun _ => true) h1
      norm_num [Holant.charge,Holant.weight] at h
  · intro h
    obtain ⟨d,layer⟩ := h.1 _ hm
    have a := layer.weight_of_nezero h0
    have b := layer.weight_of_nezero h1
    norm_num [Holant.weight] at a b
    omega
  · intro h
    exact eq4_not_arityTwo (h _ mem)
  · rintro (h | h)
    · exact eq4_not_matching false (h _ mem)
    · exact eq4_not_matching true (h _ mem)

/-- One shared basis is selected outside the universal quantifier over all
family members, with the mandatory transformed ordinary edge certificate. -/
theorem tract_iff_one_common_basis {F : SignatureFamily AlgebraicComplex}
    (mem : (⟨4,eq4⟩ : AnySignature AlgebraicComplex) ∈ F) :
    Tract F ↔ CommonTransformable affineClass (preprocess F) ∨
      CommonTransformable productClass (preprocess F) ∨
      CommonTransformable localAffineClass (preprocess F) := by
  have he := eq4_exclusions (F:=preprocess F) ⟨mem,by norm_num,eq4_nonzero⟩
  constructor
  · rintro ⟨_,h⟩
    rcases h with h | h | h | h | h | h | h
    · exact (he.1 h).elim
    · exact (he.2.1 h).elim
    · exact (he.2.2.1 h).elim
    · exact (he.2.2.2 h).elim
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact ⟨h.1,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
    · exact ⟨h.1,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩
    · exact ⟨h.1,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorCriterion
end
