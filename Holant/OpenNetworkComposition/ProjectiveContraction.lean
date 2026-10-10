import Holant.OpenNetworkComposition.ProjectiveContractionNormalize
import Holant.OpenNetworkComposition.ProjectiveContractionOrdinary
import Holant.OpenNetworkComposition.ProjectiveContractionWireClose
import Holant.OpenNetworkComposition.OfOpen
import Mathlib.Algebra.Field.Basic

/-! Projective native-X self-contraction in the existing OpenNetwork model.
The sole exceptional case is an isolated free/free circle. Its exact scalar is
2, so the witnessing network has multiplier 1/2; all other cases have multiplier
1. No supplied constant or unrepresented wire-only component is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition
namespace ProjectiveContraction
variable {K V F E : Type*} {n : ℕ}
variable [Field K]

def ContractResult (family : SignatureFamily K) (q : Signature K (n+2)) : Prop :=
  ∃c : K,(c=1 ∨ c=(2:K)⁻¹) ∧ c≠0 ∧
    Gadget.Realizes family .disequality (fun x => c*Signature.contract Signature.disequality q x)

theorem ContractResult.of_exact (family : SignatureFamily K) (q : Signature K (n+2))
    (h : Gadget.Realizes family .disequality (Signature.contract Signature.disequality q)) :
    ContractResult family q := by
  refine ⟨1,Or.inl rfl,one_ne_zero,?_⟩
  simpa using h

variable [Fintype V] [Fintype F] [Fintype E]

/-- When the first port is ordinary, any remaining free-to-ordinary stem is
normalized away; a free/free wire transfers the first port to its far boundary. -/
theorem finite_first_ordinary (N : FiniteNetwork K V F E (n+2))
    (p0 : Σv,Fin (N.shape.arity v)) (h0 : N.shape.boundary 0=.inl p0)
    (family : SignatureFamily K)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family)
    (he : ∀e,N.edge e=.disequality) : ContractResult family N.tensor := by
  apply ContractResult.of_exact
  cases h1 : N.shape.boundary 1 with
  | inl p1 => exact Ordinary.realizes_contraction N p0 p1 h0 h1 family hv he
  | inr f =>
    cases hop : N.shape.ends ((N.shape.freeEdge f).1,!(N.shape.freeEdge f).2) with
    | inl p1 =>
      let M := Normalize.network N f 1 p1 h1 hop
      have hm0 : M.shape.boundary 0=.inl p0 :=
        Normalize.network_boundary_ordinary N f 1 p1 h1 hop 0 p0 h0
      have hm1 : M.shape.boundary 1=.inl p1 := Normalize.network_boundary_at N f 1 p1 h1 hop
      have hm := Ordinary.realizes_contraction M p0 p1 hm0 hm1 family hv
        (Normalize.network_native N f 1 p1 h1 hop he)
      have ht : M.tensor=N.tensor := Normalize.network_tensor N f 1 p1 h1 hop he
      rwa [ht] at hm
    | inr g =>
      have hfg := Wire.free_ne N.shape f g hop
      have hj0 : N.shape.freeBoundary g≠0 := by
        intro hj
        have hh := N.shape.free_boundary g
        rw [hj,h0] at hh
        cases hh
      have hj1 : N.shape.freeBoundary g≠1 := by
        intro hj
        have hh := N.shape.free_boundary g
        rw [hj,h1] at hh
        exact hfg (Sum.inr.inj hh)
      obtain ⟨q,hq⟩ := (tailBoundary_range (N.shape.freeBoundary g)).mpr ⟨hj0,hj1⟩
      have hq' : N.shape.boundary q.succ.succ=.inr g := by
        simpa only [tailBoundary_apply] using (congrArg N.shape.boundary hq).trans (N.shape.free_boundary g)
      exact Wire.realizes_second N f g hop q h1 hq' family hv he

/-- Complete case dispatch on the actual two selected boundary kinds. -/
theorem finite_contract_with_scale (N : FiniteNetwork K V F E (n+2))
    (family : SignatureFamily K)
    (hv : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family)
    (he : ∀e,N.edge e=.disequality) (htwo : (2:K)≠0) : ContractResult family N.tensor := by
  cases h0 : N.shape.boundary 0 with
  | inl p0 => exact finite_first_ordinary N p0 h0 family hv he
  | inr f =>
    cases hop : N.shape.ends ((N.shape.freeEdge f).1,!(N.shape.freeEdge f).2) with
    | inl p0 =>
      let M := Normalize.network N f 0 p0 h0 hop
      have hm := finite_first_ordinary M p0 (Normalize.network_boundary_at N f 0 p0 h0 hop)
        family hv (Normalize.network_native N f 0 p0 h0 hop he)
      have ht : M.tensor=N.tensor := Normalize.network_tensor N f 0 p0 h0 hop he
      rwa [ht] at hm
    | inr g =>
      have hfg := Wire.free_ne N.shape f g hop
      have hj0 : N.shape.freeBoundary g≠0 := by
        intro hj
        have hh := N.shape.free_boundary g
        rw [hj,h0] at hh
        exact hfg (Sum.inr.inj hh)
      by_cases hj1 : N.shape.freeBoundary g=1
      · have h1 : N.shape.boundary 1=.inr g := by simpa only [hj1] using N.shape.free_boundary g
        let M := Wire.circleNetwork N f g hop h0 h1
        have hm : Gadget.Realizes family .disequality M.tensor :=
          Wire.realizes_network N f g hop 0 1 h0 h1 tailBoundary tailBoundary_range family hv he
        have ht : Signature.contract Signature.disequality N.tensor=fun x => 2*M.tensor x :=
          Wire.circle_tensor N f g hop h0 h1 he
        refine ⟨(2:K)⁻¹,Or.inr rfl,inv_ne_zero htwo,?_⟩
        have hm' : M.tensor=(fun x => (2:K)⁻¹*Signature.contract Signature.disequality N.tensor x) := by
          funext x
          rw [ht]
          simp [htwo,mul_assoc]
        rwa [←hm']
      · obtain ⟨q,hq⟩ := (tailBoundary_range (N.shape.freeBoundary g)).mpr ⟨hj0,hj1⟩
        have hq' : N.shape.boundary q.succ.succ=.inr g := by
          simpa only [tailBoundary_apply] using (congrArg N.shape.boundary hq).trans (N.shape.free_boundary g)
        exact ContractResult.of_exact family N.tensor (Wire.realizes_first N f g hop q h0 hq' family hv he)

end ProjectiveContraction

variable {K : Type*} [Field K] {n : ℕ}

/-- First-two-boundary self-contraction for arbitrary actual gadgets. The
witness multiplier is explicitly 1 or 1/2, according to whether a wire-only
circle was deleted. Both are nonzero under the stated characteristic condition. -/
theorem realizes_contract_with_scale (family : SignatureFamily K) (q : Signature K (n+2))
    (hq : Gadget.Realizes family .disequality q) (htwo : (2:K)≠0) :
    ∃c : K,(c=1 ∨ c=(2:K)⁻¹) ∧ c≠0 ∧
      Gadget.Realizes family .disequality (fun x => c*Signature.contract Signature.disequality q x) := by
  obtain ⟨N,hv,he,ht⟩ := hq
  have H := ProjectiveContraction.finite_contract_with_scale (FiniteNetwork.ofOpen N) family hv he htwo
  have hN : (FiniteNetwork.ofOpen N).tensor=q := (FiniteNetwork.ofOpen_tensor N).trans ht
  rwa [hN] at H

theorem realizes_contract (family : SignatureFamily K) (q : Signature K (n+2))
    (hq : Gadget.Realizes family .disequality q) (htwo : (2:K)≠0) :
    Gadget.RealizesUpTo family .disequality (Signature.contract Signature.disequality q) := by
  obtain ⟨c,_,hc,hg⟩ := realizes_contract_with_scale family q hq htwo
  exact ⟨c,hc,hg⟩

theorem contract_scale (c : K) (q : Signature K (n+2)) :
    Signature.contract Signature.disequality (fun x => c*q x)=
      fun x => c*Signature.contract Signature.disequality q x := by
  funext x
  simp [Signature.contract,mul_left_comm,mul_add]

/-- Projective input realizations also close, with all nonzero scalars retained. -/
theorem realizesUpTo_contract (family : SignatureFamily K) (q : Signature K (n+2))
    (hq : Gadget.RealizesUpTo family .disequality q) (htwo : (2:K)≠0) :
    Gadget.RealizesUpTo family .disequality (Signature.contract Signature.disequality q) := by
  obtain ⟨c,hc,hg⟩ := hq
  obtain ⟨d,hd,hr⟩ := realizes_contract family (fun x => c*q x) hg htwo
  refine ⟨d*c,mul_ne_zero hd hc,?_⟩
  rw [contract_scale] at hr
  simpa only [mul_assoc] using hr

end Holant.OpenNetworkComposition
