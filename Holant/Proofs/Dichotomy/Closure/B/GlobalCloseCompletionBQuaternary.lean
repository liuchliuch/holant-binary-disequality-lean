import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBNativeSource
import Holant.Proofs.Closure.HistorySectorNormalizedDeck
import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenEOTransport
import Holant.Certificates.EqualityQuaternary.CoordinatePrimality

/-! Actual B-normalized prime quaternaries have parity/complement support.
A sparse row is converted by a one-q/literal-I native graph into an EO row in
exactly the family whose whole-current original-G source was constructed.
The dense parity case stays explicit. No transformed native Palette is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBQuaternary
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Marked.SupportAtlas Holant.Certificates.EqualityQuaternary
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace W
export GlobalCloseCompletionBWorkfield (K field table table_value mapped)
end W
namespace S
export GlobalCloseCompletionBNativeSource (arity table source old_signature identity_signature)
end S
namespace O
export GlobalCloseCompletionBOrdinarySource (oldLabel xLabel)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀ f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

abbrev normalized : Signature AlgebraicComplex 4 :=
  basisB.symm.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q)

include core literal in
theorem normalized_prime : TensorPrime (normalized G q) :=
  prime_coordinateAction (ClosureSourceRows.core_ambient_prime G P q core literal)
    (fun _ => basisB.inverse) (fun _ => basisB.matrix) (fun _ => basisB.matrix_inverse)

include core literal stable in
theorem safeDeck : SafeDeck N.selected.m 1 (complexTensor (normalized G q)) := by
  exact HistorySectorNormalized.safeWeightedDeck G P torsion basisB N.selected
    N.parameters rfl q (by trivial) core literal stable

include N core literal stable in
theorem parity_and_complement :
    ∃p : Bool,(∀x,normalized G q x≠0 → parity x=p) ∧
      (∀x,normalized G q (complement x)=0 ↔ normalized G q x=0) := by
  have deck := deckSupport_of_samples N.selected.range 1 one_ne_zero (by simp)
    (complexTensor (normalized G q)) (safeDeck G P torsion N q core literal stable)
  have nonzero := (normalized_prime G P q core literal).1
  obtain ⟨x,hx⟩ : ∃x,normalized G q x≠0 := by
    by_contra h
    push Not at h
    exact nonzero (funext h)
  have live : nonzeroBit (complexTensor (normalized G q) x)=true := by
    simp [complexTensor,hx]
  obtain ⟨p,hp,hc⟩ := classification deck ⟨x,live⟩
  refine ⟨p,?_,?_⟩
  · intro y hy
    apply hp y
    simp [complexTensor,hy]
  · intro y
    have he : nonzeroBit (complexTensor (normalized G q) (complement y))=false ↔
        nonzeroBit (complexTensor (normalized G q) y)=false := by rw [complement_eq deck y]
    simpa only [nonzeroBit_false,complexTensor,AlgebraicComplex.coe_eq_zero] using he

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin (P.count+1) =>
  RingHomRealization.mapAny (W.K G P).val.toRingHom ⟨S.arity G P i.val,S.table G P i⟩

theorem family_finite : (family G P).Finite := Set.finite_range _

theorem old_mapped (i : Fin P.count) :
    RingHomRealization.mapAny (W.K G P).val.toRingHom
      ⟨S.arity G P (O.oldLabel G P i).val,S.table G P (O.oldLabel G P i)⟩=
      (⟨P.arity i.val,basisB.symm.action (W.mapped G P i)⟩ : AnySignature AlgebraicComplex) := by
  rw [S.old_signature]
  apply congrArg (fun f : Signature AlgebraicComplex (P.arity i.val) =>
    (⟨P.arity i.val,f⟩ : AnySignature AlgebraicComplex))
  exact funext (W.table_value G P i)

include core literal in
theorem normalized_member : (⟨4,normalized G q⟩ : AnySignature AlgebraicComplex)∈family G P := by
  obtain ⟨j,hj⟩ := core.retained
  have hq : (⟨P.arity j.val,P.table j⟩ : AnySignature (OI.K G))=⟨4,q⟩ := hj.trans literal
  refine ⟨O.oldLabel G P j,(old_mapped G P j).trans ?_⟩
  exact congrArg (fun f : AnySignature (OI.K G) =>
    (⟨f.1,basisB.symm.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f.2)⟩ :
      AnySignature AlgebraicComplex)) hq

theorem identity_member : (⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)∈family G P := by
  refine ⟨O.xLabel G P,?_⟩
  dsimp only
  rw [S.identity_signature]
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases x 0 <;> cases x 1 <;> simp [RingHomRealization.mapSignature,kernelSignature,Signature.equality]

include core literal in
theorem flip_realizes (mask : Word) :
    Gadget.Realizes (family G P) .disequality (Flip.value (normalized G q) mask) :=
  Flip.actual _ _ (Gadget.realizes_of_mem _ .disequality _ (normalized_member G P q core literal))
    (Gadget.realizes_of_mem _ .disequality _ (identity_member G P)) mask

def FullParity (p : Bool) : Prop := ∀x,normalized G q x≠0 ↔ parity x=p

structure SparseOutput : Type 1 where
  mask : Word
  missing : normalized G q mask=0
  paritySupported : ∀x,normalized G q x≠0 → parity x=parity mask
  eo : DenseEOUnitLocal.EOSupport (Flip.value (normalized G q) mask)
  prime : TensorPrime (Flip.value (normalized G q) mask)
  actual : Gadget.Realizes (family G P) .disequality (Flip.value (normalized G q) mask)
  oneOriginal : (Finset.univ.filter (fun v : Fin (Flip.network (normalized G q) mask).shape.vertices =>
    (Flip.network (normalized G q) mask).shape.arity v=4)).card=1

include N core literal stable in
/-- The sparse alternative is a real native graph in the same normalized
whole-current family, whose value source already terminates at original G. -/
theorem sparse_or_full : (∃p,FullParity G q p) ∨ Nonempty (SparseOutput G P q) := by
  classical
  obtain ⟨p,supported,closed⟩ := parity_and_complement G P torsion N q core literal stable
  by_cases full : FullParity G q p
  · exact Or.inl ⟨p,full⟩
  · right
    have missing : ∃mask : Word,parity mask=p ∧ normalized G q mask=0 := by
      by_contra h
      push Not at h
      apply full
      intro x
      exact ⟨supported x,fun hx => h x hx⟩
    obtain ⟨mask,hp,hzero⟩ := missing
    have same : ∀x,normalized G q x≠0 → parity x=parity mask := fun x hx => (supported x hx).trans hp.symm
    exact ⟨⟨mask,hzero,same,
      StableCurrentEvenEOTransport.eo_of_missing_parity_word _ mask same hzero ((closed mask).mpr hzero),
      flip_prime (normalized_prime G P q core literal) mask,flip_realizes G P q core literal mask,
      Flip.quaternary_count _ _⟩⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBQuaternary
end
