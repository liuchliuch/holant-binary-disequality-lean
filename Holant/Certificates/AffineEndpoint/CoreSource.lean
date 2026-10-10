import Holant.Certificates.AffineEndpoint.Cores

/-! Two-way identification with every literal eighth/fourth root in A.4's
source display, not just a generated subset of the eighteen cores. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem fourth_root_complete {r : AlgebraicComplex} (hr : r^4=1) :
    ∃k : Fin 4,imaginaryUnit^k.val=r := by
  obtain ⟨q,hq⟩ := fourthRootPhase_surjective_of_pow_four hr
  exact ⟨⟨q.val,q.val_lt⟩,hq⟩

 theorem eighth_root_complete {r : AlgebraicComplex} (hr : r^8=1) :
    ∃k : Fin 8,zetaEight^k.val=r := by
  have hsq : (r^4)^2=1 := by simpa only [←pow_mul] using hr
  rcases sq_eq_one_iff.mp hsq with hpos|hneg
  · obtain ⟨q,hq⟩ := fourth_root_complete hpos
    refine ⟨⟨2*q.val,by omega⟩,?_⟩
    change zetaEight^(2*q.val)=r
    rw [pow_mul,zetaEight_sq]
    exact hq
  · have hdiv : (r/zetaEight)^4=1 := by
      rw [div_pow,hneg,zetaEight_pow_four]
      norm_num
    obtain ⟨q,hq⟩ := fourth_root_complete hdiv
    refine ⟨⟨2*q.val+1,by omega⟩,?_⟩
    change zetaEight^(2*q.val+1)=r
    rw [pow_add,pow_mul,zetaEight_sq,pow_one,hq,div_mul_cancel₀ _ zetaEight_ne_zero]

 theorem eighth_power_one (k : Fin 8) : (zetaEight^k.val)^8=1 := by
  rw [←pow_mul,Nat.mul_comm,pow_mul,zetaEight_pow_eight,one_pow]
 theorem fourth_power_one (k : Fin 4) : (imaginaryUnit^k.val)^4=1 := by
  rw [←pow_mul,Nat.mul_comm,pow_mul,imaginaryUnit_pow_four,one_pow]

/-- The exact source union I,X; all eight roots; all four roots and both signs. -/
 def SourceCore (K : Matrix Bool Bool AlgebraicComplex) : Prop :=
  K=1 ∨ K=(fun a b => Signature.disequality a b) ∨
  (∃r : AlgebraicComplex,r^8=1 ∧ K=algMat 1 r 1 (-r)) ∨
  ∃u : AlgebraicComplex,u^4=1 ∧ ∃b : Bool,
    K=algMat 1 (u*(1+(if b then -sqrtTwo else sqrtTwo)))
      1 (u*(1-(if b then -sqrtTwo else sqrtTwo)))

 theorem coreMatrix_source (k : CoreIndex) : SourceCore (coreMatrix k) := by
  cases k with
  | inl i =>
    fin_cases i
    · exact Or.inl core_identity
    · exact Or.inr (Or.inl core_flip)
  | inr k =>
    cases k with
    | inl i => exact Or.inr (Or.inr (Or.inl ⟨zetaEight^i.val,eighth_power_one i,core_hadamard i⟩))
    | inr p => exact Or.inr (Or.inr (Or.inr
        ⟨imaginaryUnit^p.1.val,fourth_power_one p.1,p.2,core_mixed p.1 p.2⟩))

 theorem source_core_complete (K : Matrix Bool Bool AlgebraicComplex) (hK : SourceCore K) :
    ∃k : CoreIndex,coreMatrix k=K := by
  rcases hK with rfl|rfl|⟨r,hr,rfl⟩|⟨u,hu,b,rfl⟩
  · exact ⟨.inl 0,core_identity⟩
  · exact ⟨.inl 1,core_flip⟩
  · obtain ⟨k,rfl⟩ := eighth_root_complete hr
    exact ⟨.inr (.inl k),core_hadamard k⟩
  · obtain ⟨k,rfl⟩ := fourth_root_complete hu
    exact ⟨.inr (.inr (k,b)),core_mixed k b⟩

 theorem source_core_iff_mem (K : Matrix Bool Bool AlgebraicComplex) :
    SourceCore K ↔ K∈coreSet := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := source_core_complete K h
    exact Finset.mem_map.mpr ⟨k,Finset.mem_univ _,hk⟩
  · intro h
    obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp h
    exact coreMatrix_source k

 theorem source_core_count : {K : Matrix Bool Bool AlgebraicComplex | SourceCore K}.ncard=18 := by
  have he : {K : Matrix Bool Bool AlgebraicComplex | SourceCore K}=(coreSet : Set _) := by
    ext K
    exact source_core_iff_mem K
  rw [he,Set.ncard_coe_finset,coreSet_card]

end
end Holant.Certificates.AffineEndpoint
