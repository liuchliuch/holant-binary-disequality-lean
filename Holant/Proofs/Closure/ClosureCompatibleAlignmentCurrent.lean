import Holant.Proofs.Closure.ClosureCompatibleAlignmentMatching
import Holant.Proofs.Closure.ClosureSixPortCurrentAlgebraicCard
import Holant.Proofs.Closure.ClosureProgramStability

/-! Selected card products are constructed from the literal regenerated
CURRENT source deck.  Their native presentations are retained before scalar
normalization, so higher-arity matching equality is proved using the actual
source stability theorem rather than supplied as an alignment premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.TwoCardLocalization
open Holant.Dihedral.EndpointParallelogram

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

def currentKernel (p : Bool) (t : {t : Scalar // Roots N.m t}) : Binary (K:=OI.K G) :=
  X * actualRepresentative P.family torsion (ClosureSixPort.algebraicCardIndex G P torsion N p t).key * X

/-- Every normalized phase uses its actual ORIGINAL-field representative and
the ORIGINAL-field pivot multiplier.  There is no normalized-gadget oracle. -/
def currentRepresentatives : ActualRepresentatives (ClosureSourceRows.ambientFamily G P) N.m where
  binary := fun p t => ClosureSourceRows.representative G P torsion
    (ClosureSixPort.algebraicCardIndex G P torsion N p t).key
  multiplier := fun p t => ClosureSourceRows.embedding G
    (ClosureSixPort.algebraicCardCoefficient G P torsion N p t)
  multiplier_ne_zero := fun p t => (map_ne_zero _).mpr
    (ClosureSixPort.algebraicCardCoefficient_nonzero G P torsion N p t)
  actual := fun p t => ClosureSourceRows.representative_actual G P torsion
    (ClosureSixPort.algebraicCardIndex G P torsion N p t).key
  normalization := by
    intro p t
    funext u v
    have h := congrFun (congrFun (ClosureSixPort.algebraicCardKernel_exact G P torsion N p t) (!u)) (!v)
    simp only [Matrix.map_apply,ClosureSixPort.matrix_Xsandwich,Bool.not_not,
      Pi.smul_apply,smul_eq_mul] at h
    change ClosureSourceRows.embedding G
      (actualRepresentative P.family torsion (ClosureSixPort.algebraicCardIndex G P torsion N p t).key u v) = _
    simpa only [scale,← connection_entry p t.val (!u) (!v),Bool.not_not] using h

variable {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4)))
variable (p : Bool) (t : {t : Scalar // Roots N.m t})

def normalizedCurrentCard : Signature Scalar (2*r+2) :=
  Signature.contract (M p t.val) (Tensor.reindex order.symm
    (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f))

structure CurrentSelectedCard where
  native : Presentation (OI.K G) (Fin (2*r+2))
  valid : native.Valid (actualTransfers P.family)
  scalar_nonzero : native.scalar ≠ 0
  nativeEquation : Signature.contract (currentKernel G P torsion N p t)
    (Tensor.reindex order.symm f) = native.tensor

/-- A zero sample is a separate branch.  For a selected nonzero sample the
literal CURRENT deck itself supplies the source matching presentation. -/
def selectCurrentCard
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g)
    (nonzero : normalizedCurrentCard G P torsion N f order p t ≠ 0) :
    CurrentSelectedCard G P torsion N f order p t := by
  let key := DeckContraction.orderedKey P.family torsion order
    (ClosureSixPort.algebraicCardIndex G P torsion N p t).key
  have raw_nonzero : rawCard P.family torsion f key ≠ 0 := by
    intro zero
    have h := ClosureSixPort.ordered_algebraic_card_raw_scalar G P torsion N f order p t
    change RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
      (rawCard P.family torsion f key) = _ at h
    rw [zero] at h
    have mapped_zero : RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
        (0 : Signature (OI.K G) (2*r+2)) = 0 := by
      funext x
      exact map_zero _
    rw [mapped_zero] at h
    exact nonzero ((smul_eq_zero.mp h.symm).resolve_left ((map_ne_zero _).mpr
      (ClosureSixPort.algebraicCardCoefficient_nonzero G P torsion N p t)))
  have existsNative := (stable _ (Or.inr ⟨key,rfl⟩)).resolve_left raw_nonzero
  let native := Classical.choose existsNative
  have spec := Classical.choose_spec existsNative
  refine ⟨native,spec.1,spec.2.1,?_⟩
  have rawIdentity : rawCard P.family torsion f key =
      Signature.contract (currentKernel G P torsion N p t) (Tensor.reindex order.symm f) :=
    DeckContraction.rawCard_ordered P.family torsion f order
      (ClosureSixPort.algebraicCardIndex G P torsion N p t).key
  exact rawIdentity.symm.trans spec.2.2

namespace CurrentSelectedCard
variable {G P torsion N f order p t}

def algebraic (S : CurrentSelectedCard G P torsion N f order p t) :
    Presentation Scalar (Fin (2*r+2)) where
  edges := S.native.edges
  ports := S.native.ports
  matrix := fun e => (S.native.matrix e).map (ClosureSourceRows.embedding G)
  scalar := (ClosureSourceRows.embedding G
    (ClosureSixPort.algebraicCardCoefficient G P torsion N p t))⁻¹ *
      ClosureSourceRows.embedding G S.native.scalar

theorem algebraic_member (S : CurrentSelectedCard G P torsion N f order p t) (e : Fin S.native.edges) :
    S.algebraic.matrix e ∈ groupM N.m :=
  ClosureSixPort.current_safe_groupM G P torsion N _ (S.valid e)

theorem algebraic_scalar_nonzero (S : CurrentSelectedCard G P torsion N f order p t) :
    S.algebraic.scalar ≠ 0 :=
  mul_ne_zero (inv_ne_zero ((map_ne_zero _).mpr
    (ClosureSixPort.algebraicCardCoefficient_nonzero G P torsion N p t)))
      ((map_ne_zero _).mpr S.scalar_nonzero)

theorem algebraic_equation (S : CurrentSelectedCard G P torsion N f order p t) :
    normalizedCurrentCard G P torsion N f order p t = S.algebraic.tensor := by
  let c := ClosureSourceRows.embedding G (ClosureSixPort.algebraicCardCoefficient G P torsion N p t)
  have hc : c ≠ 0 := (map_ne_zero _).mpr
    (ClosureSixPort.algebraicCardCoefficient_nonzero G P torsion N p t)
  have bridge := ClosureSixPort.ordered_algebraic_card_raw_scalar G P torsion N f order p t
  rw [DeckContraction.rawCard_ordered] at bridge
  change RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
    (Signature.contract (currentKernel G P torsion N p t) (Tensor.reindex order.symm f)) =
      c • normalizedCurrentCard G P torsion N f order p t at bridge
  rw [S.nativeEquation] at bridge
  rw [← ClosureSixPort.algebraicPresentation_tensor G S.native] at bridge
  have h := congrArg (fun q : Signature Scalar (2*r+2) => c⁻¹ • q) bridge
  simp only [smul_smul,inv_mul_cancel₀ hc,one_smul] at h
  rw [← h]
  funext x
  simp only [algebraic,Presentation.tensor,Holant.Certificates.MatchingContractionClosure.productValue,
    ClosureSixPort.algebraicPresentation,Pi.smul_apply,smul_eq_mul,mul_assoc]
  rfl

theorem edgeCount (S : CurrentSelectedCard G P torsion N f order p t) : S.native.edges = r+1 := by
  have h := Fintype.card_congr S.native.ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
  omega

def ports (S : CurrentSelectedCard G P torsion N f order p t) : (Fin (r+1) × Bool) ≃ Fin (2*r+2) :=
  (Equiv.prodCongr (finCongr S.edgeCount).symm (Equiv.refl Bool)).trans S.native.ports

def factors (S : CurrentSelectedCard G P torsion N f order p t) (e : Fin (r+1)) : Mat :=
  S.algebraic.matrix ((finCongr S.edgeCount).symm e)

theorem factors_member (S : CurrentSelectedCard G P torsion N f order p t) (e : Fin (r+1)) :
    S.factors e ∈ groupM N.m := S.algebraic_member _

theorem coefficient_product (S : CurrentSelectedCard G P torsion N f order p t) :
    normalizedCurrentCard G P torsion N f order p t =
      Holant.Dihedral.CompatibleClosure.productValue S.ports S.factors S.algebraic.scalar := by
  rw [S.algebraic_equation]
  funext x
  apply congrArg (S.algebraic.scalar * ·)
  exact (Equiv.prod_comp (finCongr S.edgeCount).symm
    (fun e => S.algebraic.matrix e (x (S.native.ports (e,false))) (x (S.native.ports (e,true))))).symm

theorem pairing_native (S : CurrentSelectedCard G P torsion N f order p t) :
    (Pairing.ofPorts S.ports).mate = (presentationMatching S.native).mate := by
  funext u
  simp [ports,Pairing.ofPorts,presentationMatching,Holant.Pauli.ExoticKlein.Matching.mate]
  rfl

end CurrentSelectedCard

/-- Above six original ports, SAME native presentations have equal matching
involutions by CURRENT stability.  Subsequent algebraic normalization preserves
those exact ports, so no matching/alignment assumption enters this factory. -/
theorem current_selected_matchings_equal (large : 2 ≤ r)
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g)
    (p₀ p₁ : Bool) (t₀ t₁ : {t : Scalar // Roots N.m t})
    (S₀ : CurrentSelectedCard G P torsion N f order p₀ t₀)
    (S₁ : CurrentSelectedCard G P torsion N f order p₁ t₁) :
    (Pairing.ofPorts S₀.ports).mate = (Pairing.ofPorts S₁.ports).mate := by
  rw [S₀.pairing_native,S₁.pairing_native]
  have notDifferent := ClosureProgramStability.stable_even_ordered_cards_not_different
    P.family torsion (P.retainsIdentity G) (by omega : 6 ≤ 2*r+2)
    (by exact ⟨r+1,by omega⟩ : Even (2*r+2)) f stable order
    (currentKernel G P torsion N p₀ t₀) (currentKernel G P torsion N p₁ t₁)
  have same : (presentationMatching S₀.native).mate = (presentationMatching S₁.native).mate := by
    by_contra different
    exact notDifferent ⟨S₀.native,S₁.native,S₀.valid,S₁.valid,S₀.scalar_nonzero,S₁.scalar_nonzero,
      S₀.nativeEquation,S₁.nativeEquation,different⟩
  exact congrArg (fun e : Equiv.Perm (Fin (2*r+2)) => e.toFun) same

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
