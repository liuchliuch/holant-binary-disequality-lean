import Holant.Proofs.Hardness.EightVertexGaugeDenseOutcome
import Holant.Proofs.Closure.ClosureSourceRowsMonomial
import Holant.Proofs.Algorithms.RingHomDescent

/-! Current-family continuation of the dense gauge locus. The representatives
are the actual fixed source-field representatives of the current native-M
group. A bad new binary descends exactly to the original coefficient field;
complete-group membership rules out nonsingularity. Its preserved parity
then forces exactly one nonzero entry. Its original-G access is
constructed through the existing currentSignatureAccess compiler. Singularity
is retained as a preparation exit, never relabeled unconditional hardness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseGaugeCurrent
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.Certificates.EqualityQuaternary

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

/-- The existing representatives work already over the original current
ambient family. No retained extension or new normalized label is installed. -/
def representatives : MonomialRepresentatives (ClosureSourceRows.ambientFamily G P) N.m where
  matrix p t := ClosureSourceRows.representative G P torsion
    (ClosureSourceRows.monomialIndex G P torsion N p t).key
  multiplier p t := ClosureSourceRows.embedding G
    (ClosureSourceRows.monomialIndex G P torsion N p t).coefficient
  multiplier_ne_zero p t := (map_ne_zero (ClosureSourceRows.embedding G)).mpr
    (ClosureSourceRows.monomialIndex G P torsion N p t).nonzero
  actual p t := ClosureSourceRows.representative_actual G P torsion
    (ClosureSourceRows.monomialIndex G P torsion N p t).key
  normal_form p t := (ClosureSourceRows.monomialIndex G P torsion N p t).normal

theorem ambient_identity : RetainsIdentity (ClosureSourceRows.ambientFamily G P) := by
  refine ⟨⟨2,Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature⟩,
    P.retainsIdentity G,?_⟩
  change (⟨2,RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
    Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature⟩ :
      AnySignature AlgebraicComplex) = _
  congr 1
  funext x
  cases x 0 <;> cases x 1 <;>
    simp [RingHomRealization.mapSignature,
      Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature,Signature.equality]

/-- Exact source-field descent includes singular outputs and all disconnected
scalar components. The graph and native edge kinds are unchanged. -/
theorem binary_descends (B : Mat)
    (actual : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality
      (kernelSignature B)) :
    ∃ C : Binary (K := OI.K G),
      Gadget.Realizes P.family .disequality (binarySignature C) ∧
      C.map (ClosureSourceRows.embedding G) = B := by
  obtain ⟨V,hV,hW,ht⟩ := actual
  let W := RingHomDescent.descendNetwork (ClosureSourceRows.embedding G) V hV
  let C := Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix W.tensor
  have he : C.map (ClosureSourceRows.embedding G) = B := by
    ext x y
    have h := congrFun ((RingHomDescent.descend_tensor
      (ClosureSourceRows.embedding G) V hV).trans ht) ![x,y]
    simpa [C,W,Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix,
      RingHomRealization.mapSignature,kernelSignature,Matrix.map_apply] using h
  refine ⟨C,⟨W,RingHomDescent.descend_labels (ClosureSourceRows.embedding G) V hV,hW,?_⟩,he⟩
  exact (binarySignature_binaryMatrix W.tensor).symm

/-- A concrete original-field singular fixed-parity binary and its already
compiled current/original-G programmes. This is a resource receipt. -/
structure SingularReceipt where
  binary : Binary (K := OI.K G)
  nonzero : binary ≠ 0
  singular : Matrix.det binary = 0
  parity : EightVertexGaugeParity.BinaryParity binary
  actual : Gadget.Realizes P.family .disequality (binarySignature binary)
  access : CurrentSignatureAccess G P ⟨2,binarySignature binary⟩

theorem SingularReceipt.oneHot (r : SingularReceipt G P) :
    EightVertexGaugeParity.OneHot r.binary :=
  EightVertexGaugeParity.singular_oneHot r.binary r.parity r.nonzero r.singular

theorem singular_receipt (B : Mat) (nonzero : B ≠ 0) (outside : B ∉ groupM N.m)
    (realized : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality
      (kernelSignature B)) (parity : EightVertexGaugeParity.BinaryParity B) :
    Nonempty (SingularReceipt G P) := by
  obtain ⟨C,hC,hmap⟩ := binary_descends G P B realized
  have hn : C ≠ 0 := by
    intro hz
    apply nonzero
    rw [← hmap,hz]
    ext x y
    simp [Matrix.map_apply]
  have hd : Matrix.det C = 0 := by
    by_contra nonsingular
    have hm := ClosureSourceRows.actual_binary_groupM G P torsion N C ⟨hC,nonsingular⟩
    rw [hmap] at hm
    exact outside hm
  have hp : EightVertexGaugeParity.BinaryParity C := by
    rw [← hmap] at parity
    simpa [EightVertexGaugeParity.BinaryParity,Matrix.map_apply] using parity
  exact ⟨⟨C,hn,hd,hp,hC,currentSignatureAccess G P ⟨2,binarySignature C⟩ hC⟩⟩

private theorem mapped_conditions (q : Signature (OI.K G) 4)
    (even : EvenSupport q) (dense : StableDenseParityAlgebra.Dense q)
    (products : StableDenseResidualAlgebra.Products q) :
    let M := RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q
    EvenSupport M ∧ StableDenseParityAlgebra.Dense M ∧ StableDenseResidualAlgebra.Products M := by
  let M := RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x hx
    change ClosureSourceRows.embedding G (q x) = 0
    rw [even x hx,map_zero]
  · simpa [M,StableDenseParityAlgebra.Dense,entries,RingHomRealization.mapSignature] using dense
  · simpa [M,entries,RingHomRealization.mapSignature] using
      congrArg (ClosureSourceRows.embedding G) products.1
  · simpa [M,entries,RingHomRealization.mapSignature] using
      congrArg (ClosureSourceRows.embedding G) products.2.1
  · simpa [M,entries,RingHomRealization.mapSignature] using
      congrArg (ClosureSourceRows.embedding G) products.2.2

include torsion N in
/-- A dense even row actually realizable over the current palette either has
one affine basis including native X, or yields an original-field singular
binary with the existing charged current access. No new deck stability, new
coefficient field, free unary access, or terminal-hardness premise is input. -/
theorem row_basis_or_original_singular (q : Signature (OI.K G) 4)
    (actual : Gadget.Realizes P.family .disequality q)
    (even : EvenSupport q) (dense : StableDenseParityAlgebra.Dense q)
    (products : StableDenseResidualAlgebra.Products q) :
    (∃ B : InvertibleKernel, IsCommonKBasis affineClass
      {⟨4,RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q⟩} B) ∨
      Nonempty (SingularReceipt G P) := by
  let M := RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q
  have hactual : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality M :=
    RingHomRealization.realizes_map (ClosureSourceRows.embedding G) actual
  obtain ⟨heven,hdense,hproducts⟩ := mapped_conditions G q even dense products
  rcases EightVertexGaugeDenseOutcome.dense_basis_or_physical_escape N.range
    (ClosureSourceRows.ambientFamily G P) (ambient_identity G P)
    (representatives G P torsion N) M hactual heven hdense hproducts with
      basis | ⟨i,e,p,t,nonzero,outside,realized⟩
  · exact Or.inl basis
  · exact Or.inr (singular_receipt G P torsion N _ nonzero outside realized
      (EightVertexGaugeParity.physical_card_parity _ (representatives G P torsion N) _
        (EightVertexGaugeDenseOutcome.originalRow_even M heven hdense hproducts i) e p t))

include torsion N in
/-- The two-I test strengthens the positive branch to a common basis for
the row AND retained identity, with the same mandatory native-X edge. -/
theorem row_identity_basis_or_original_singular (q : Signature (OI.K G) 4)
    (actual : Gadget.Realizes P.family .disequality q)
    (even : EvenSupport q) (dense : StableDenseParityAlgebra.Dense q)
    (products : StableDenseResidualAlgebra.Products q) :
    (∃ B : InvertibleKernel, IsCommonKBasis affineClass
      {⟨4,RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q⟩,
       ⟨2,kernelSignature Signature.equality⟩} B) ∨ Nonempty (SingularReceipt G P) := by
  let M := RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q
  have hactual : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality M :=
    RingHomRealization.realizes_map (ClosureSourceRows.embedding G) actual
  obtain ⟨heven,hdense,hproducts⟩ := mapped_conditions G q even dense products
  rcases EightVertexGaugeDenseOutcome.dense_identity_basis_or_physical_escape N.range
    (ClosureSourceRows.ambientFamily G P) (ambient_identity G P)
    (representatives G P torsion N) M hactual heven hdense hproducts with
      basis | ⟨flip,i,e,p,t,nonzero,outside,realized⟩
  · exact Or.inl basis
  · exact Or.inr (singular_receipt G P torsion N _ nonzero outside realized
      (EightVertexGaugeParity.physical_card_parity _ (representatives G P torsion N) _
        (EightVertexGaugeDenseOutcome.selected_even M heven hdense hproducts flip i) e p t))

include torsion N in
/-- Simultaneous current-family conclusion for an explicitly selected
collection of actual dense residual rows. Other palette leaves are excluded
from the positive family until their compatibility is separately proved. -/
theorem family_basis_or_original_singular {ι : Type} (q : ι → Signature (OI.K G) 4)
    (base : ι) (actual : ∀ i, Gadget.Realizes P.family .disequality (q i))
    (even : ∀ i, EvenSupport (q i)) (dense : ∀ i, StableDenseParityAlgebra.Dense (q i))
    (products : ∀ i, StableDenseResidualAlgebra.Products (q i)) :
    (∃ B : InvertibleKernel, IsCommonKBasis affineClass
      (EightVertexGaugeDenseOutcome.originalFamily
        (fun i => RingHomRealization.mapSignature (ClosureSourceRows.embedding G) (q i))) B) ∨
      Nonempty (SingularReceipt G P) := by
  let M := fun i => RingHomRealization.mapSignature (ClosureSourceRows.embedding G) (q i)
  have hactual (i : ι) : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality (M i) :=
    RingHomRealization.realizes_map (ClosureSourceRows.embedding G) (actual i)
  have conditions (i : ι) := mapped_conditions G (q i) (even i) (dense i) (products i)
  rcases EightVertexGaugeDenseOutcome.dense_family_basis_or_physical_escape N.range
    (ClosureSourceRows.ambientFamily G P) (ambient_identity G P) (representatives G P torsion N)
    M base hactual (fun i => (conditions i).1) (fun i => (conditions i).2.1)
    (fun i => (conditions i).2.2) with basis | ⟨B,hn,ho,hr,hp⟩
  · exact Or.inl basis
  · exact Or.inr (singular_receipt G P torsion N B hn ho hr hp)

/-- The same derived basis also covers the ENTIRE current monomial binary
group. Its phase restriction is produced by actual one-port insertions into
the dense row, not supplied as an assumption. -/
theorem family_binary_basis_or_original_singular {ι : Type} (q : ι → Signature (OI.K G) 4)
    (base : ι) (actual : ∀ i, Gadget.Realizes P.family .disequality (q i))
    (even : ∀ i, EvenSupport (q i)) (dense : ∀ i, StableDenseParityAlgebra.Dense (q i))
    (products : ∀ i, StableDenseResidualAlgebra.Products (q i)) :
    (∃ B : InvertibleKernel, IsCommonKBasis affineClass
      (EightVertexGaugeDenseOutcome.originalFamily
        (fun i => RingHomRealization.mapSignature (ClosureSourceRows.embedding G) (q i)) ∪
       {f | ∃ C : Mat, C∈groupM N.m ∧ f=⟨2,kernelSignature C⟩}) B) ∨
      Nonempty (SingularReceipt G P) := by
  let M := fun i => RingHomRealization.mapSignature (ClosureSourceRows.embedding G) (q i)
  have hactual (i : ι) : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality (M i) :=
    RingHomRealization.realizes_map (ClosureSourceRows.embedding G) (actual i)
  have conditions (i : ι) := mapped_conditions G (q i) (even i) (dense i) (products i)
  rcases EightVertexGaugeDenseOutcome.dense_family_with_binaries_or_physical_escape N.range
    (ClosureSourceRows.ambientFamily G P) (ambient_identity G P) (representatives G P torsion N)
    M base hactual (fun i => (conditions i).1) (fun i => (conditions i).2.1)
    (fun i => (conditions i).2.2) with basis | ⟨B,hn,ho,hr,hp⟩
  · exact Or.inl basis
  · exact Or.inr (singular_receipt G P torsion N B hn ho hr hp)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseGaugeCurrent
end
