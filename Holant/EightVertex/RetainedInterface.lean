import Holant.EightVertex.ProductAnchor.Source
import Holant.EightVertex.LocalAffineCollapse.Source
import Holant.Certificates.EqualityQuaternary.CoordinatePrimality
import Holant.Tractable.Conformal.CommonBasis
import Holant.Tractable.Downward
import Holant.Proofs.Algorithms.PrimalityInterfaces
import Holant.Proofs.Reductions.RootPreprocessing.Retained


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.EightVertex.RetainedInterface
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open scoped BigOperators
namespace RP
export Holant.LocalDrafts.Hardness.RootPreprocessing
  (signature Keep compact include_compact retained_exact included_kept count)
end RP
namespace FS
export Holant.LocalDrafts.Hardness.FactorSaturation
  (tree addedCount arity augmented entry augmented_family saturated finite_augmented
   entry_positive entry_nonzero lookup_old)
end FS

variable {F : SignatureFamily AlgebraicComplex} {q : Signature AlgebraicComplex 4}

theorem nonzero (he : EndpointEven q) : q≠0 := by
  intro hz
  exact he.1 (congrFun hz _)

theorem survives (hq : (⟨4,q⟩ : AnySignature AlgebraicComplex)∈F)
    (he : EndpointEven q) : (⟨4,q⟩ : AnySignature AlgebraicComplex)∈preprocess F :=
  ⟨hq,by norm_num,nonzero he⟩

theorem both_charges (hq : (⟨4,q⟩ : AnySignature AlgebraicComplex)∈F)
    (he : EndpointEven q) : BothChargeSigns F := by
  refine ⟨⟨⟨4,q⟩,hq,(fun _ => false),he.1,?_⟩,
    ⟨⟨4,q⟩,hq,(fun _ => true),he.2.1,?_⟩⟩ <;>
    norm_num [Holant.charge,Holant.weight]

theorem not_one_sided (hq : (⟨4,q⟩ : AnySignature AlgebraicComplex)∈F)
    (he : EndpointEven q) : ¬CommonOneSided F := by
  obtain ⟨⟨g,hg,x,hx,hn⟩,⟨f,hf,y,hy,hp⟩⟩ := both_charges hq he
  rintro (hs|hs)
  · exact (not_le_of_gt hn) (hs g hg x hx)
  · exact (not_le_of_gt hp) (hs f hf y hy)

theorem not_single_layer (he : EndpointEven q) : ¬∃d,Signature.SingleLayer q d := by
  rintro ⟨d,hd⟩
  have h0 : Holant.weight (fun _ : Fin 4 => false)=d := by
    by_contra hn
    exact he.1 (hd _ hn)
  have h1 : Holant.weight (fun _ : Fin 4 => true)=d := by
    by_contra hn
    exact he.2.1 (hd _ hn)
  norm_num [Holant.weight] at h0 h1
  omega

/-- These are exclusions of the FULL source clauses, with K cancelled on
the whole family. No basis is selected independently for each member. -/
theorem no_eo_clauses (hq : (⟨4,q⟩ : AnySignature AlgebraicComplex)∈F)
    (he : EndpointEven q) :
    ¬OneSidedAlternative (familyAction sourceKBasis F) ∧
    ¬SingleWeightAlternative (familyAction sourceKBasis F) := by
  constructor
  · intro h
    apply not_one_sided hq he
    simpa only [Conformal.kCoordinates_familyAction] using h.1
  · intro h
    have hl := h.1
    rw [Conformal.kCoordinates_familyAction] at hl
    exact not_single_layer he (hl _ hq)

/-- The genuine continuing decomposition is impossible even after arbitrary
recorded invertible port actions and a nonzero recorded scalar. This does
not claim such actions are legal physical changes of the native edge. -/
theorem no_dressed_factor (hp : TensorPrime q) (A B : Fin 4 → Mat)
    (hinv : ∀i,Kernel.mul (B i) (A i)=Signature.equality)
    (c : Scalar) (hc : c≠0) :
    ¬ProperFactor (c • Signature.coordinateAction A q) :=
  (prime_smul (prime_coordinateAction hp A B hinv) c hc).2

/-- The ordered two-binary decomposition's exact tensor identity, including
the original normalization unit, contradicts prime. -/
theorem not_two_weighted (hp : TensorPrime q) : ¬TwoWeightedEqualities q := by
  rintro ⟨⟨n,a,f,p,c⟩,hn,ha,hv,_,_⟩
  dsimp at hn ha hv
  subst n
  have hae : a=(fun _ : Fin 2 => 2) := funext ha
  subst a
  let e : (Fin 2 ⊕ Fin 2) ≃ (Σ i : Fin 2,Fin 2) := {
    toFun := Sum.elim (fun j => ⟨0,j⟩) (fun j => ⟨1,j⟩)
    invFun := fun x => if x.1=0 then .inl x.2 else .inr x.2
    left_inv := by intro x; cases x <;> simp
    right_inv := by rintro ⟨i,j⟩; fin_cases i <;> simp }
  apply hp.2
  refine ⟨2,2,by decide,by decide,e.trans p,(c:Scalar) • f 0,f 1,?_⟩
  rw [←hv]
  funext x
  simp [TensorDecomposition.value,Tensor.reindex,Tensor.tensor,e,
    Fin.prod_univ_two,smul_eq_mul,mul_assoc]

/-- This calls the existing product proof; no new classification result is
assumed. Its middle branch is removed using the ORIGINAL prime signature. -/
theorem product_prime_exit (he : EndpointEven q) (hp : TensorPrime q)
    (hP : CommonKPresentationInKCoordinates productClass {⟨4,q⟩})
    (actual : Gadget.Realizes F .disequality q) :
    PureEquality q ∨ HasEqualityAnchor F := by
  rcases source_product_transformable_eight_vertex q he hP with h|h|h
  · exact Or.inl h.1
  · exact (not_two_weighted hp h.1).elim
  · exact Or.inr (h.1.2 F actual)

section Catalogue
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
abbrev family := Set.range (fun i => (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex))

/-- The actual preprocessing table, not an unrelated saturation witness. -/
theorem retained_exact : Set.range (RP.signature G)=preprocess (family G) := by
  rw [RP.retained_exact]
  ext f
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,rfl⟩,hi⟩
  · rintro ⟨⟨i,rfl⟩,hi⟩
    exact ⟨i,hi,rfl⟩

abbrev nonzeroRoots : ∀i, (RP.signature G i).2≠0 := fun i => (RP.included_kept G i).2
abbrev positiveRoots : ∀i, 0<(RP.signature G i).1 := fun i => (RP.included_kept G i).1
abbrev forestArity := FS.arity (RP.signature G) (nonzeroRoots G)
abbrev forestTable := FS.augmented (RP.signature G) (nonzeroRoots G)
abbrev forestFamily := Set.range (fun i =>
  (⟨forestArity G i.val,forestTable G i⟩ : AnySignature AlgebraicComplex))

theorem retained_subset : preprocess (family G) ⊆ forestFamily G := by
  rw [←retained_exact G]
  intro f hf
  change f ∈ Set.range (fun i => (⟨FS.arity (RP.signature G) (nonzeroRoots G) i.val,
    FS.augmented (RP.signature G) (nonzeroRoots G) i⟩ : AnySignature AlgebraicComplex))
  rw [FS.augmented_family (RP.signature G) (nonzeroRoots G)]
  exact Or.inl hf
theorem forest_saturated : FactorSaturated (forestFamily G) :=
  FS.saturated (RP.signature G) (nonzeroRoots G)
theorem forest_finite : (forestFamily G).Finite := Set.finite_range _
theorem forest_preprocessed : Preprocessed (forestFamily G) := by
  intro f hf
  change f ∈ Set.range (fun i => (⟨FS.arity (RP.signature G) (nonzeroRoots G) i.val,
    FS.augmented (RP.signature G) (nonzeroRoots G) i⟩ : AnySignature AlgebraicComplex)) at hf
  rw [FS.augmented_family (RP.signature G) (nonzeroRoots G)] at hf
  rcases hf with ⟨i,rfl⟩|⟨j,rfl⟩
  · exact RP.included_kept G i
  · exact ⟨FS.entry_positive _ _ (positiveRoots G) j,FS.entry_nonzero _ _ j⟩

theorem q_in_forest (hq : (⟨4,q⟩ : AnySignature AlgebraicComplex)∈family G)
    (he : EndpointEven q) : (⟨4,q⟩ : AnySignature AlgebraicComplex)∈forestFamily G :=
  retained_subset G (survives hq he)

/-- The endpoint supplies the exact no-one-sided hypothesis of the existing
carrier theorem. Every proper STORED node gets an actual nonzero native-X
carrier without I; its background vertices remain in the original retained
family. This is a carrier for exposure, not a free realization of the factor. -/
theorem stored_factor_carrier
    (hq : (⟨4,q⟩ : AnySignature AlgebraicComplex)∈family G) (he : EndpointEven q)
    (j : Fin (FS.addedCount (RP.signature G) (nonzeroRoots G))) :
    Nonempty (Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralCarrierExistence.Witness
      (preprocess (family G)) (FS.entry (RP.signature G) (nonzeroRoots G) j).2) := by
  apply Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralCarrierExistence.factor_carrier
    (preprocess (family G)) (by norm_num)
    (Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralPowerExposure.mixedSupport_of_source
      (not_one_sided (survives hq he) he))
    (FS.entry_positive _ _ (positiveRoots G) j)
    _ (FS.entry_nonzero _ _ j)

/-- Downward inheritance uses the same K on the entire original retained
family. Internal nodes are not silently identified with original labels. -/
theorem nontractable_forest
    (hn : ¬Tract (familyAction sourceKBasis (family G))) :
    ¬Tract (familyAction sourceKBasis (forestFamily G)) := by
  intro ht
  have hpre := ht.mono_family (familyAction_mono sourceKBasis (retained_subset G))
  apply hn
  simpa only [Tract,Conformal.preprocess_familyAction,preprocess_idempotent] using hpre

/-- Any stored tree for an original prime is necessarily its literal leaf,
so use of the existing catalogue cannot replace q by a different factor. -/
theorem tree_is_leaf {K : Type*} [Field K] {f : AnySignature K}
    (hp : Prime f) (t : FactorTree f) : t=FactorTree.leaf f hp := by
  cases t with
  | leaf => rfl
  | split cut l r => exact (hp.2 ⟨_,_,⟨cut⟩⟩).elim

theorem stored_q_leaf (i : Fin (RP.count G))
    (hi : RP.signature G i=(⟨4,q⟩ : AnySignature AlgebraicComplex))
    (hp : TensorPrime q) :
    FS.tree (RP.signature G) (nonzeroRoots G) i =
      FactorTree.leaf (RP.signature G i)
        (hi.symm ▸ (PrimalityInterfaces.retained_equality_prime q).mpr hp) :=
  tree_is_leaf _ _
end Catalogue

/-- Actual source packets keep their original field. Mapping the SAME table
and the SAME labelled endpoint supplies the semantic AC theorem input; this
lemma does not identify the two answer codecs or change any physical edge. -/
theorem mapped_packet {L : Type} [Field L] {s : ℕ} {a : ℕ → ℕ}
    (φ : L →+* AlgebraicComplex) (G : (i : Fin s) → Signature L (a i.val))
    (q : Signature L 4)
    (hq : (⟨4,q⟩ : AnySignature L)∈Set.range
      (fun i => (⟨a i.val,G i⟩ : AnySignature L)))
    (hp : Prime (⟨4,q⟩ : AnySignature L))
    (h0 : q (fun _ => false)≠0) (h1 : q (fun _ => true)≠0)
    (hodd : ∀x,Holant.weight x%2=1 → q x=0) :
    let mapped := fun i => RingHomRealization.mapSignature φ (G i)
    let Q := RingHomRealization.mapSignature φ q
    (⟨4,Q⟩ : AnySignature AlgebraicComplex)∈family mapped ∧
      EndpointEven Q ∧ TensorPrime Q := by
  dsimp only
  refine ⟨?_,⟨?_,?_,?_⟩,?_⟩
  · obtain ⟨i,hi⟩ := hq
    exact ⟨i,congrArg (RingHomRealization.mapAny φ) hi⟩
  · exact (map_ne_zero φ).mpr h0
  · exact (map_ne_zero φ).mpr h1
  · intro x hx
    change φ (q x)=0
    rw [hodd x hx,map_zero]
  · apply (PrimalityInterfaces.retained_equality_prime _).mp
    exact (prime_mapSignature_iff φ _).mpr hp
end Holant.EightVertex.RetainedInterface
