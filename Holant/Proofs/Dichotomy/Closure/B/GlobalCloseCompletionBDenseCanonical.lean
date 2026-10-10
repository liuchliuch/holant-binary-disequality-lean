import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBDenseAnchorX
import Holant.Proofs.Algorithms.QuaternaryEqualityTerminal

/-! Additive canonical dense-anchor producer. The successful actual gauge path
retains rotation order four, the eighth-root common weight, its chosen square
root, the exact Eq4 basis, and an actual representative becoming scalar X.
Existing existential anchor APIs are left unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBDenseCanonical
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.EightVertex.ProductAnchor
open StableDenseResidualGaugeCore
open Holant.Projective.CyclicDressing
open EightVertexGaugePhysicalOutcome EightVertexGaugeFamily EightVertexGaugeParity
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

structure Canonical (F : SignatureFamily AlgebraicComplex) : Type where
  weight : AlgebraicComplex
  weight_nonzero : weight≠0
  eighth : weight^8=1
  root : AlgebraicComplex
  root_nonzero : root≠0
  square : root^2=2*weight
  signature : Signature AlgebraicComplex 4
  actual : Gadget.Realizes F .disequality signature
  vertexScale : AlgebraicComplex
  vertex_nonzero : vertexScale≠0
  anchor_exact : (denseNormalization weight root weight_nonzero root_nonzero).action signature=
    fun x => vertexScale*equalityFour x
  binary : Signature AlgebraicComplex 2
  binary_actual : Gadget.Realizes F .disequality binary
  binaryScale : AlgebraicComplex
  binary_nonzero : binaryScale≠0
  binary_exact : (denseNormalization weight root weight_nonzero root_nonzero).action binary=
    fun x => binaryScale*kernelSignature Signature.disequality x

namespace Canonical
variable {F : SignatureFamily AlgebraicComplex} (C : Canonical F)
abbrev basis : InvertibleKernel := denseNormalization C.weight C.root C.weight_nonzero C.root_nonzero

def anchor : QuaternaryEqualityTerminal.AnchorStep F where
  signature := C.signature
  basis := C.basis
  edgeScale := 1
  vertexScale := C.vertexScale
  edge_ne_zero := one_ne_zero
  vertex_ne_zero := C.vertex_nonzero
  actual := C.actual
  edge_exact := by
    change Kernel.pullback Signature.disequality (normalizationInverse C.weight C.root)=_
    simpa only [one_mul] using normalization_edge C.weight C.root C.root_nonzero C.square
  anchor_exact := C.anchor_exact

theorem anchor_basis : C.anchor.basis=C.basis := rfl

theorem actual_transformed_X : Gadget.Realizes F .disequality C.binary ∧ C.binaryScale≠0 ∧
    C.anchor.basis.action C.binary=(fun x => C.binaryScale*kernelSignature Signature.disequality x) :=
  ⟨C.binary_actual,C.binary_nonzero,C.binary_exact⟩
end Canonical

structure Receipt (F : SignatureFamily AlgebraicComplex) (m : ℕ) : Type where
  order_four : m=4
  canonical : Canonical F

private theorem weighted_constant (c r : AlgebraicComplex) :
    weighted c (fun _ => r)=denseTensor c r (fun _ => false) := by
  funext x
  rw [weighted_value]
  have hp : (∏i : Fin 4,if x i then r else 1)=r^weight x := by
    calc
      _ = ∏i : Fin 4,r^(if x i then 1 else 0 : ℕ) := by
        apply Finset.prod_congr rfl
        intro i _
        cases x i <;> simp
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  simp [hp,denseTensor,bitSign]

private theorem normalized_zero : (normalized (fun _ => false) : Signature AlgebraicComplex 4)=equalityFour := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [normalized,equalityFour,weight,Fin.sum_univ_four,funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]

/-- All four phase-equalizing attachments are actual old-family binaries.
The same explicitly chosen canonical matrix also transforms a retained phase
representative into nonzero scalar X. -/
theorem canonical_of_fourths (F : SignatureFamily AlgebraicComplex)
    (reps : MonomialRepresentatives F 4) (a : AlgebraicComplex)
    (u : Fin 4 → AlgebraicComplex) (ha : a≠0) (hu : ∀i,u i≠0)
    (fourths : ∀i,u i^4=u 0^4) (eighth : u 0^8=1)
    (actual : Gadget.Realizes F .disequality (weighted a u)) : Nonempty (Canonical F) := by
  let t : Fin 4 → Phase 4 := fun i => ⟨u i/u 0,by
    change (u i/u 0)^4=1
    rw [div_pow,fourths i,div_self (pow_ne_zero 4 (hu 0))]⟩
  let c := a*∏i,reps.multiplier true (t i)*(t i).val
  have ht : ∀i,(t i).val≠0 := fun i => div_ne_zero (hu i) (hu 0)
  have hc : c≠0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr
    (fun i _ => mul_ne_zero (reps.multiplier_ne_zero true (t i)) (ht i)))
  have equalWeights : (fun i => u i/(t i).val)=(fun _ => u 0) := by
    funext i
    dsimp [t]
    field_simp [hu i]
  have matrices : (fun i => reps.matrix true (t i))=
      (fun i => scale (reps.multiplier true (t i)) (S (t i).val)) := by
    funext i
    simpa [standard] using reps.normal_form true (t i)
  have dressed := realizes_physicalDressing F (weighted a u)
    (fun i => reps.matrix true (t i)) actual (fun i => reps.actual true (t i))
  rw [matrices,EightVertexGaugeEqualityAnchor.dressing_value a u _ _ ht,equalWeights] at dressed
  obtain ⟨v,hv,hsq⟩ := exists_algebraic_normalizing_root (u 0) (hu 0)
  obtain ⟨binary,bs,bn,ba,bexact⟩ := GlobalCloseCompletionBDenseAnchorX.actual_scaled_X
    F reps (u 0) v (hu 0) hv hsq eighth
  refine ⟨⟨u 0,hu 0,eighth,v,hv,hsq,weighted c (fun _ => u 0),dressed,
    denseNormalizationScale c v (fun _ => false),
    denseNormalizationScale_ne_zero c v (fun _ => false) hc hv,?_,binary,ba,bs,bn,bexact⟩⟩
  rw [weighted_constant]
  change Signature.coordinateAction (fun _ => normalizationMatrix (u 0) v)
    (denseTensor c (u 0) (fun _ => false))=_
  rw [normalize_denseTensor c (u 0) v (hu 0),normalized_zero]

/-- The stronger receipt comes from precisely the successful branch of the
old finite physical tests. Rejected tests keep the same actual bad binary. -/
theorem weighted_or_bad {m : ℕ} (hm : 3≤m) (omega : ℂˣ) (primitive : IsPrimitiveRoot omega m)
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F) (reps : MonomialRepresentatives F m)
    (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex) (ha : a≠0) (hu : ∀i,u i≠0)
    (actual : Gadget.Realizes F .disequality (weighted a u)) :
    Nonempty (Receipt F m) ∨ BadBinary F m := by
  classical
  rcases EightVertexGaugePhaseInsertion.constraints_or_bad hm F hI reps a u ha hu actual with
    ⟨eighth,phases⟩ | bad
  · have hm4 := EightVertexGaugeEqualityAnchor.order_eq_four hm omega primitive phases
    subst m
    by_cases decks : ∀i : Fin 3,MonomialPhysicalDeck reps (row a u i)
    · obtain ⟨C⟩ := canonical_of_fourths F reps a u ha hu
        (physical_decks_fourths hm F reps a u ha hu decks) eighth actual
      exact Or.inl ⟨⟨rfl,C⟩⟩
    · obtain ⟨i,e,p,t,hn,ho,hr⟩ := escape_of_not_decks F hI reps a u actual decks
      exact Or.inr ⟨_,hn,fun hg => ho
        ((EightVertexGaugeRepresentativeLines.line_iff_group (by omega) F reps _).mpr hg),hr,
        physical_card_parity F reps _ (onPorts_even _ _ _ _ _ _ _) e p t⟩
  · exact Or.inr bad

theorem dense_or_bad {m : ℕ} (hm : 3≤m) (omega : ℂˣ) (primitive : IsPrimitiveRoot omega m)
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F) (reps : MonomialRepresentatives F m)
    (M : Signature AlgebraicComplex 4) (actual : Gadget.Realizes F .disequality M)
    (even : EvenSupport M) (dense : StableDenseParityAlgebra.Dense M)
    (products : StableDenseResidualAlgebra.Products M) : Nonempty (Receipt F m) ∨ BadBinary F m := by
  obtain ⟨u,hu,hM⟩ := StableDenseResidualGaugeExistence.algebraic_factor M even products
    dense.1 dense.2.1 dense.2.2.1 dense.2.2.2.1 dense.2.2.2.2.1
  apply weighted_or_bad hm omega primitive F hI reps (entries M).a u dense.1 hu
  simpa only [←hM] using actual


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBDenseCanonical
end
