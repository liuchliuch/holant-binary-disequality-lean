import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeOcticCommonBasis

/-! Whole ordinary obstruction supplies the four genuine class witnesses
needed by sparse CSP2 compatibility. A rejected basis is shared across the
entire family; no singleton criterion is substituted. No hardness claim is
made until the corresponding literal resource producers are composed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeClassWitnesses
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
namespace T
export StableHigherCurrentOrdinaryTerminal (Obstruction Test obstruction_iff AffineTest LocalTest)
end T
namespace C
export OrdinaryNegativeOcticCommonBasis (basis action phase edge_affine)
end C
namespace A
export StableHigherCurrentAnchorAffineBasisCandidates (common_transformable_iff_candidates)
end A
namespace L
export StableHigherCurrentAnchorLocalCriterion (common_transformable_iff_candidates)
end L
open StableHigherCurrentAnchorCriterion (eq4)
abbrev pin := StableHigherCurrentAnchorLocalBasis.pin
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable (H : SignatureFamily AlgebraicComplex)
variable (finite : H.Finite)
variable (h0 : (⟨1,pin false⟩ : AnySignature AlgebraicComplex)∈H)
variable (h1 : (⟨1,pin true⟩ : AnySignature AlgebraicComplex)∈H)
variable (heq : (⟨4,eq4⟩ : AnySignature AlgebraicComplex)∈H)
variable (negative : T.Obstruction H)

include finite h0 h1 heq negative in
/-- Any fixed affine-compatible edge basis has an actual rejected row. -/
theorem outside_affine (B : InvertibleKernel)
    (edge : Affine (kernelSignature (Kernel.pullback Signature.equality B.matrix))) :
    ∃f∈H,¬Affine (B.symm.action f.2) := by
  classical
  by_contra! all
  have common : CommonTransformable affineClass H := ⟨finite,B,edge,all⟩
  have test : T.AffineTest H := ((A.common_transformable_iff_candidates h0 h1 heq).mp common).2
  exact (T.obstruction_iff H).mp negative (Or.inl test)

include finite h0 h1 negative in
/-- The same conclusion for any fixed local-affine-compatible edge. -/
theorem outside_localAffine (B : InvertibleKernel)
    (edge : LocalAffine (kernelSignature (Kernel.pullback Signature.equality B.matrix))) :
    ∃f∈H,¬LocalAffine (B.symm.action f.2) := by
  classical
  by_contra! all
  have common : CommonTransformable localAffineClass H := ⟨finite,B,edge,all⟩
  have test : T.LocalTest H := ((L.common_transformable_iff_candidates h0 h1).mp common).2
  exact (T.obstruction_iff H).mp negative (Or.inr (Or.inr test))

theorem identity_local_edge :
    LocalAffine (kernelSignature (Kernel.pullback Signature.equality InvertibleKernel.identity.matrix)) := by
  have he : Kernel.pullback Signature.equality InvertibleKernel.identity.matrix=diagonal 1 1 := by
    funext x y
    cases x <;> cases y <;> simp [InvertibleKernel.identity,Kernel.pullback,
      Kernel.mul,Kernel.transpose,Signature.equality,diagonal]
  rw [he]
  exact localAffine_diagonal 1 1 one_ne_zero rfl

include finite h0 h1 heq negative in
theorem outside_A : ∃f∈H,¬Affine f.2 := by
  obtain ⟨f,hf,h⟩ := outside_affine H finite h0 h1 heq negative (C.basis false) (C.edge_affine false)
  refine ⟨f,hf,?_⟩
  simpa [C.action,C.phase] using h

include finite h0 h1 heq negative in
/-- The chosen ordinary diagonal basis multiplies every true coordinate by
zetaEight. Its literal native edge is included in the rejection argument. -/
theorem outside_Atwist : ∃f∈H,¬Affine ((C.basis true).symm.action f.2) :=
  outside_affine H finite h0 h1 heq negative (C.basis true) (C.edge_affine true)

include negative in
theorem outside_P : ∃f∈H,¬Product f.2 := negative.2.1

include finite h0 h1 negative in
theorem outside_L : ∃f∈H,¬LocalAffine f.2 := by
  obtain ⟨f,hf,h⟩ := outside_localAffine H finite h0 h1 negative
    InvertibleKernel.identity identity_local_edge
  refine ⟨f,hf,?_⟩
  simpa [InvertibleKernel.symm,InvertibleKernel.identity,InvertibleKernel.action,
    Signature.coordinateAction_equality] using h

structure Witnesses where
  affine : AnySignature AlgebraicComplex
  affine_member : affine∈H
  not_affine : ¬Affine affine.2
  twisted : AnySignature AlgebraicComplex
  twisted_member : twisted∈H
  not_twisted : ¬Affine ((C.basis true).symm.action twisted.2)
  product : AnySignature AlgebraicComplex
  product_member : product∈H
  not_product : ¬Product product.2
  localAffine : AnySignature AlgebraicComplex
  local_member : localAffine∈H
  not_local : ¬LocalAffine localAffine.2

/-- Every witness is chosen inside the same actual whole family. They may
coincide; neither four distinct rows nor a failed singleton test is required. -/
def choose : Witnesses H := by
  classical
  let a := outside_A H finite h0 h1 heq negative
  let t := outside_Atwist H finite h0 h1 heq negative
  let p := outside_P H negative
  let l := outside_L H finite h0 h1 negative
  exact ⟨a.choose,a.choose_spec.1,a.choose_spec.2,
    t.choose,t.choose_spec.1,t.choose_spec.2,
    p.choose,p.choose_spec.1,p.choose_spec.2,
    l.choose,l.choose_spec.1,l.choose_spec.2⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeClassWitnesses
end
