import Holant.OpenNetworkComposition.FactorFreeNormalization.Incidence
import Holant.OpenNetworkComposition.FactorFreeNormalization.Factors
import Holant.OpenNetworkComposition.OfOpen
import Mathlib.Algebra.Field.Basic

/-! An actual realization of a tensor with no isolated binary X factor has
an exact ordinary template over its original signature family. No literal-I
resource, extra scalar resource, or supplied ordinary realization is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.FactorFreeNormalization
variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- The exact isolated-wire factorization rules out every free/free edge. -/
theorem ordinaryMates_of_noXFactor {V F E : Type*}
    [Fintype V] [Fintype F] [Fintype E]
    (M : FiniteNetwork K V F E n) (he : ∀e,M.edge e=.disequality)
    (hf : NoXFactor M.tensor) : OrdinaryMates M := by
  intro f
  cases hop : M.shape.ends ((M.shape.freeEdge f).1,!(M.shape.freeEdge f).2) with
  | inl p => exact ⟨p,rfl⟩
  | inr g => exact (hf (hasXFactor_of_free_mate M he f g hop)).elim

/-- The sufficient semantic criterion yields an exact original-family template. -/
theorem exists_ordinary_of_noXFactor {V F E : Type*}
    [Fintype V] [Fintype F] [Fintype E]
    (M : FiniteNetwork K V F E n) (family : SignatureFamily K)
    (hv : ∀v,(⟨M.shape.arity v,M.vertex v⟩ : AnySignature K)∈family)
    (he : ∀e,M.edge e=.disequality) (hf : NoXFactor M.tensor) :
    ∃N : Network K n,
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote=M.tensor :=
  exists_ordinary M (ordinaryMates_of_noXFactor M he hf) family hv he

/-- Arbitrary actual source provenance suffices when the resulting tensor has
no binary X factor on two original boundary coordinates. -/
theorem realizes_exists_ordinary {family : SignatureFamily K} {h : Signature K n}
    (hh : Gadget.Realizes family .disequality h) (hf : NoXFactor h) :
    ∃N : Network K n,
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote=h := by
  obtain ⟨M,hv,he,hm⟩ := hh
  have heq : (FiniteNetwork.ofOpen M).tensor=h := (FiniteNetwork.ofOpen_tensor M).trans hm
  obtain ⟨N,hvN,heN,hN⟩ := exists_ordinary_of_noXFactor (FiniteNetwork.ofOpen M)
    family hv he (by rwa [heq])
  exact ⟨N,hvN,heN,hN.trans heq⟩

end Holant.OpenNetworkComposition.FactorFreeNormalization

namespace Holant.OpenNetworkComposition.FactorFreeNormalization
variable {K : Type*} [Field K] {n : ℕ}

/-- A nonzero projective multiplier cannot create an isolated X factor. -/
theorem NoXFactor.scale {h : Signature K n} (hf : NoXFactor h) {c : K} (hc : c≠0) :
    NoXFactor (fun x => c*h x) := by
  rintro ⟨i,j,hij,g,hg⟩
  apply hf
  refine ⟨i,j,hij,fun x => c⁻¹*g x,?_⟩
  intro x
  calc
    h x=c⁻¹*(c*h x) := by simp [hc]
    _=c⁻¹*(Signature.disequality (x i) (x j)*g (fun k => x k.val)) := congrArg (fun a => c⁻¹*a) (hg x)
    _=Signature.disequality (x i) (x j)*(c⁻¹*g (fun k => x k.val)) := by ac_rfl

/-- The projective scalar is retained exactly and adds no vertex resource. -/
theorem realizesUpTo_exists_ordinary {family : SignatureFamily K} {h : Signature K n}
    (hh : Gadget.RealizesUpTo family .disequality h) (hf : NoXFactor h) :
    ∃c : K,c≠0 ∧ ∃N : Network K n,
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote=(fun x => c*h x) := by
  obtain ⟨c,hc,hreal⟩ := hh
  exact ⟨c,hc,realizes_exists_ordinary hreal (hf.scale hc)⟩

end Holant.OpenNetworkComposition.FactorFreeNormalization
