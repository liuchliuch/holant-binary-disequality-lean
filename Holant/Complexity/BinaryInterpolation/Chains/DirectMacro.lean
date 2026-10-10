import Holant.Complexity.BinaryInterpolation.Chains.Template
import Holant.OpenNetworkComposition.FactorFreeNormalization.Reduction
import Holant.Projective.BoundedTorsion.Group

/-! The source assumes B is directly realizable over Γ, not that B is retained
as a Γ label. Infinite projective order excludes the sole binary free-wire
obstruction, so an actual original-Γ ordinary macro is derived without I.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.OpenNetworkComposition.FactorFreeNormalization
open Holant.Complexity.FixedGadgetSubstitution
noncomputable section
variable {K : Type*} [Field K]
set_option backward.isDefEq.respectTransparency false

theorem binary_hasXFactor_scalar (B : Binary (K := K)) (h : HasXFactor (binarySignature B)) :
    ∃ c : K, B = c • X := by
  obtain ⟨i,j,hij,g,hg⟩ := h
  have other_empty : IsEmpty (OtherPorts i j) := by
    refine ⟨fun p => ?_⟩
    rcases p with ⟨p,hpi,hpj⟩
    fin_cases i <;> fin_cases j <;> fin_cases p <;> simp_all
  letI := other_empty
  let c := g (fun _ => false)
  have he (x : Fin 2 → Bool) : binarySignature B x = Signature.disequality (x 0) (x 1) * c := by
    rw [hg]
    have hx : (fun p : OtherPorts i j => x p.val) = (fun _ => false) := Subsingleton.elim _ _
    rw [hx]
    change Signature.disequality (x i) (x j) * c = Signature.disequality (x 0) (x 1) * c
    congr 1
    fin_cases i <;> fin_cases j <;> simp_all [Signature.disequality,ne_comm]
  refine ⟨c,?_⟩
  ext a b
  have hh := he (![a,b] : Fin 2 → Bool)
  simpa [binarySignature,X,mul_comm] using hh

theorem infinite_noXFactor (B : Binary (K := K)) (hB : B ≠ 0)
    (hi : ¬ ProjectivelyFinite (B * X)) : NoXFactor (binarySignature B) := by
  intro hx
  obtain ⟨c,hc⟩ := binary_hasXFactor_scalar B hx
  have hcn : c ≠ 0 := by
    intro hz
    apply hB
    simpa [hz] using hc
  apply hi
  refine ⟨1,by decide,c,hcn,?_⟩
  rw [pow_one,hc,Matrix.smul_mul,X_mul_X]

/-- Source-direct provenance supplies the ordinary original-family witness;
the conclusion does not strengthen direct realizability to B membership. -/
theorem direct_ordinary (family : SignatureFamily K) (B : Binary (K := K)) (hB : B ≠ 0)
    (hi : ¬ ProjectivelyFinite (B * X))
    (hreal : Gadget.Realizes family .disequality (binarySignature B)) :
    ∃ N : Network K 2, Uses N family ∧ Native N ∧ N.denote = binarySignature B :=
  realizes_exists_ordinary hreal (infinite_noXFactor B hB hi)

theorem projective_direct_ordinary (family : SignatureFamily K) (B : Binary (K := K)) (hB : B ≠ 0)
    (hi : ¬ ProjectivelyFinite (B * X))
    (hreal : Gadget.RealizesUpTo family .disequality (binarySignature B)) :
    ∃ c : K, c ≠ 0 ∧ ∃ N : Network K 2,
      Uses N family ∧ Native N ∧ N.denote = c • binarySignature B :=
  realizesUpTo_exists_ordinary hreal (infinite_noXFactor B hB hi)

/-- All positive chain queries can therefore be expanded over Γ itself, with
the exact scalar c^t and exact copies of every normalized macro occurrence. -/
theorem original_family_chains (family : SignatureFamily K) (B : Binary (K := K)) (hB : B ≠ 0)
    (hi : ¬ ProjectivelyFinite (B * X))
    (hreal : Gadget.RealizesUpTo family .disequality (binarySignature B)) :
    ∃ c : K, c ≠ 0 ∧ ∃ N : Network K 2, Uses N family ∧ Native N ∧
      N.denote = c • binarySignature B ∧
      ∀ t : ℕ, 0 < t → ∃ C : Network K 2,
        C.shape.vertices = t * N.shape.vertices ∧
        C.shape.edges = t * N.shape.edges + (t - 1) ∧ Uses C family ∧ Native C ∧
        c ^ t ≠ 0 ∧ C.denote = c ^ t • binarySignature ((B * X) ^ t * X) := by
  obtain ⟨c,hc,N,hF,hX,hN⟩ := projective_direct_ordinary family B hB hi hreal
  exact ⟨c,hc,N,hF,hX,hN,fun t ht => positive_macro_chain N B family c hc hF hX hN t ht⟩

/-- An actual ordinary macro's every vertex receives a literal original-family
label. Choice is only over the fixed macro, never an input-dependent program. -/
def labellingOfUses {n s b : ℕ} (arity : ℕ → ℕ)
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (N : Network K n)
    (hN : Uses N (Set.range (fun i => (⟨arity i.val,signatures i⟩ : AnySignature K))))
    (edge : Fin b) : Labelling N.shape s b arity where
  vertex v := Classical.choose (hN v)
  vertex_arity v := congrArg Sigma.fst (Classical.choose_spec (hN v))
  edge _ := edge

theorem labellingOfUses_denote {n s b : ℕ} (arity : ℕ → ℕ)
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (N : Network K n)
    (hN : Uses N (Set.range (fun i => (⟨arity i.val,signatures i⟩ : AnySignature K))))
    (hX : Native N) (edge : Fin b) (kernels : Fin b → Bool → Bool → K)
    (hedge : kernels edge = Signature.disequality) :
    (((labellingOfUses arity signatures N hN edge).template).network
      (labellingOfUses arity signatures N hN edge).wellFormed signatures kernels).denote = N.denote := by
  apply Labelling.denote_template_of_labels
  · intro v x
    change signatures (Classical.choose (hN v))
      (fun i => x (Fin.cast (congrArg Sigma.fst (Classical.choose_spec (hN v))) i)) = N.vertex v x
    exact signature_cast_apply _ _ (Classical.choose_spec (hN v)) _ x
  · intro e a b
    exact congrFun₂ (hedge.trans (hX e).symm) a b

/-- The actual fixed ordinary template needed to remove the temporary B label
is derived from source realization and original labels, with its scale intact. -/
theorem original_labelled_macro {s b : ℕ} (arity : ℕ → ℕ)
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (edge : Fin b) (kernels : Fin b → Bool → Bool → K)
    (hedge : kernels edge = Signature.disequality)
    (B : Binary (K := K)) (hB : B ≠ 0) (hi : ¬ ProjectivelyFinite (B * X))
    (hreal : Gadget.RealizesUpTo
      (Set.range (fun i => (⟨arity i.val,signatures i⟩ : AnySignature K)))
      .disequality (binarySignature B)) :
    ∃ c : K, c ≠ 0 ∧ ∃ N : Network K 2, ∃ L : Labelling N.shape s b arity,
      (L.template.network L.wellFormed signatures kernels).denote = c • binarySignature B := by
  obtain ⟨c,hc,N,hN,hX,hd⟩ := projective_direct_ordinary _ B hB hi hreal
  refine ⟨c,hc,N,labellingOfUses arity signatures N hN edge,?_⟩
  exact (labellingOfUses_denote arity signatures N hN hX edge kernels hedge).trans hd

end
end Holant.Complexity.BinaryInterpolation.Chains
