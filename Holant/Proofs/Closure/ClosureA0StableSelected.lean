import Holant.Proofs.Closure.ClosureA0StableSource
import Holant.Proofs.Closure.ClosureCompatibleAlignmentOneStep
import Holant.Proofs.Closure.ClosureProgramStability

/-! Internally selected original matching presentations for A0 root samples.
The coordinate action changes their matrices while preserving the literal port
matching. Higher-arity matching equality comes from the actual ORIGINAL deck. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureA0Stable
open Holant Holant.Tractable Holant.Algebraic Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge ClosureCompatibleAlignment
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.TwoCardLocalization Holant.Dihedral.EndpointParallelogram

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))

def sourceKernel (p : Bool) (t : Phase N.selected.m) : Binary (K:=OI.K G) :=
  X * actualRepresentative P.family torsion (index G P torsion N p t).key * X

variable {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4))) (p : Bool) (t : Phase N.selected.m)

structure SelectedCard where
  native : Presentation (OI.K G) (Fin (2*r+2))
  valid : native.Valid (actualTransfers P.family)
  scalar_nonzero : native.scalar≠0
  nativeEquation : Signature.contract (sourceKernel G P torsion N p t)
    (Tensor.reindex order.symm f)=native.tensor

set_option backward.isDefEq.respectTransparency false in
def selectCard
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g)
    (nonzero : rootCard G P torsion N f order p t≠0) : SelectedCard G P torsion N f order p t := by
  let key := DeckContraction.orderedKey P.family torsion order (index G P torsion N p t).key
  have rawNonzero : rawCard P.family torsion f key≠0 := by
    intro zero
    have h := ordered_card_raw_scalar G P torsion N f order p t
    change basis.symm.action (RH.mapSignature (algebraicEmbedding G)
      (rawCard P.family torsion f key))=_ at h
    rw [zero] at h
    have mappedZero : RH.mapSignature (algebraicEmbedding G) (0 : Signature (OI.K G) (2*r+2))=0 := by
      funext x; exact map_zero _
    rw [mappedZero,ClosureFactorTreeAction.action_zero] at h
    exact nonzero ((smul_eq_zero.mp h.symm).resolve_left (cardScalar_nonzero G P torsion N p t))
  have existsNative := (stable _ (Or.inr ⟨key,rfl⟩)).resolve_left rawNonzero
  let native := Classical.choose existsNative
  have spec := Classical.choose_spec existsNative
  refine ⟨native,spec.1,spec.2.1,?_⟩
  have rawIdentity : rawCard P.family torsion f key=
      Signature.contract (sourceKernel G P torsion N p t) (Tensor.reindex order.symm f) :=
    DeckContraction.rawCard_ordered P.family torsion f order (index G P torsion N p t).key
  exact rawIdentity.symm.trans spec.2.2

namespace SelectedCard
variable {G P torsion N f order p t}

def algebraic (S : SelectedCard G P torsion N f order p t) : Presentation Scalar (Fin (2*r+2)) :=
  { HistorySectorCards.matching (algebraicEmbedding G) basis S.native with
      scalar := (cardScalar G P torsion N p t)⁻¹ * algebraicEmbedding G S.native.scalar }

theorem member (S : SelectedCard G P torsion N f order p t) (e : Fin S.native.edges) :
    S.algebraic.matrix e ∈ groupM N.selected.m := safe_table_mem G P torsion N _ (S.valid e)

theorem coefficient_nonzero (S : SelectedCard G P torsion N f order p t) :
    S.algebraic.scalar≠0 := mul_ne_zero (inv_ne_zero (cardScalar_nonzero G P torsion N p t))
      ((map_ne_zero (algebraicEmbedding G)).mpr S.scalar_nonzero)

set_option backward.isDefEq.respectTransparency false in
theorem equation (S : SelectedCard G P torsion N f order p t) :
    rootCard G P torsion N f order p t=S.algebraic.tensor := by
  let c := cardScalar G P torsion N p t
  have hc : c≠0 := cardScalar_nonzero G P torsion N p t
  have bridge := ordered_card_raw_scalar G P torsion N f order p t
  rw [DeckContraction.rawCard_ordered] at bridge
  change basis.symm.action (RH.mapSignature (algebraicEmbedding G)
    (Signature.contract (sourceKernel G P torsion N p t) (Tensor.reindex order.symm f)))=
    c • rootCard G P torsion N f order p t at bridge
  rw [S.nativeEquation,HistorySectorCards.matching_tensor] at bridge
  have h := congrArg (fun q : Signature Scalar (2*r+2) => c⁻¹ • q) bridge
  simp only [smul_smul,inv_mul_cancel₀ hc,one_smul] at h
  rw [←h]
  funext x
  simp only [algebraic,Presentation.tensor,Holant.Certificates.MatchingContractionClosure.productValue,HistorySectorCards.matching,
    Pi.smul_apply,smul_eq_mul,mul_assoc]
  rfl

theorem edgeCount (S : SelectedCard G P torsion N f order p t) : S.native.edges=r+1 := by
  have h := Fintype.card_congr S.native.ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
  omega

def ports (S : SelectedCard G P torsion N f order p t) : (Fin (r+1) × Bool) ≃ Fin (2*r+2) :=
  (Equiv.prodCongr (finCongr S.edgeCount).symm (Equiv.refl Bool)).trans S.native.ports

def factors (S : SelectedCard G P torsion N f order p t) (e : Fin (r+1)) : Mat :=
  S.algebraic.matrix ((finCongr S.edgeCount).symm e)

theorem factors_member (S : SelectedCard G P torsion N f order p t) (e : Fin (r+1)) :
    S.factors e ∈ groupM N.selected.m := S.member _

theorem coefficient_product (S : SelectedCard G P torsion N f order p t) :
    rootCard G P torsion N f order p t=
      Holant.Dihedral.CompatibleClosure.productValue S.ports S.factors S.algebraic.scalar := by
  rw [S.equation]
  funext x
  apply congrArg (S.algebraic.scalar * ·)
  exact (Equiv.prod_comp (finCongr S.edgeCount).symm
    (fun e => S.algebraic.matrix e (x (S.native.ports (e,false))) (x (S.native.ports (e,true))))).symm

theorem pairing_native (S : SelectedCard G P torsion N f order p t) :
    (Pairing.ofPorts S.ports).mate=(presentationMatching S.native).mate := by
  funext u
  simp [ports,Pairing.ofPorts,presentationMatching,Holant.Pauli.ExoticKlein.Matching.mate]
  rfl

end SelectedCard

set_option backward.isDefEq.respectTransparency false in
theorem selected_matchings_equal (large : 2≤r)
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g)
    (p₀ p₁ : Bool) (t₀ t₁ : Phase N.selected.m)
    (S₀ : SelectedCard G P torsion N f order p₀ t₀)
    (S₁ : SelectedCard G P torsion N f order p₁ t₁) :
    (Pairing.ofPorts S₀.ports).mate=(Pairing.ofPorts S₁.ports).mate := by
  rw [S₀.pairing_native,S₁.pairing_native]
  have obstruction := ClosureProgramStability.stable_even_ordered_cards_not_different
    P.family torsion (P.retainsIdentity G) (by omega : 6≤2*r+2)
    (by exact ⟨r+1,by omega⟩ : Even (2*r+2)) f stable order
    (sourceKernel G P torsion N p₀ t₀) (sourceKernel G P torsion N p₁ t₁)
  have same : (presentationMatching S₀.native).mate=(presentationMatching S₁.native).mate := by
    by_contra different
    exact obstruction ⟨S₀.native,S₁.native,S₀.valid,S₁.valid,S₀.scalar_nonzero,S₁.scalar_nonzero,
      S₀.nativeEquation,S₁.nativeEquation,different⟩
  exact congrArg (fun e : Equiv.Perm (Fin (2*r+2)) => e.toFun) same

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureA0Stable
end
