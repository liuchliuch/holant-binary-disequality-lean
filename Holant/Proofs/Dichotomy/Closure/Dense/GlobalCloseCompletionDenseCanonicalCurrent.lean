import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBDenseCanonical
import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeAnchorContinuation

/-! Canonical dense receipts from the actual old native-M chart pipeline.
This is additive: the older anchor receipt remains available by forgetting
information, while the successful producer now retains the one basis and its
actual binary witness for literal X. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionDenseCanonicalCurrent
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.EightVertexNonexception hiding Word
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open GlobalCloseCompletionBDenseCanonical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

/-- Both chart parities use the same actual four-I flip network. The positive
branch retains the exact gauge choice used to construct its Eq4 and X. -/
theorem fullParity_or_bad {m : ℕ} (hm : 3≤m) (omega : ℂˣ)
    (primitive : IsPrimitiveRoot omega m) (F : SignatureFamily AlgebraicComplex)
    (hI : RetainsIdentity F) (reps : MonomialRepresentatives F m)
    (M : Signature AlgebraicComplex 4) (actual : Gadget.Realizes F .disequality M)
    (p : Bool) (full : ∀x,M x≠0 ↔ parity x=p) :
    Nonempty (Receipt F m) ∨ EightVertexGaugeFamily.BadBinary F m := by
  let mask : Word := ![p,false,false,false]
  have same : parity mask=p := by cases p <;> rfl
  have hi : Gadget.Realizes F .disequality (kernelSignature Signature.equality) :=
    Gadget.realizes_of_mem _ .disequality _ hI
  have chartActual := Flip.actual F M actual hi mask
  obtain ⟨even,dense⟩ := StableDenseGaugeChartAnchor.chart_conditions M p full mask same
  have chartFull : ∀x,Flip.value M mask x≠0 ↔ parity x=false := by
    intro x
    change M (xorWord x mask)≠0 ↔ _
    rw [full,parity_xorWord,same]
    cases parity x <;> cases p <;> decide
  rcases StableDenseGaugeChartAnchor.products_or_bad hm F hI reps
    (Flip.value M mask) chartActual chartFull even with products | bad
  · exact dense_or_bad hm omega primitive F hI reps
      (Flip.value M mask) chartActual even dense products
  · exact Or.inr bad

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

include torsion N in
theorem row_or_original_singular (q : Signature (OI.K G) 4)
    (actual : Gadget.Realizes P.family .disequality q) (p : Bool)
    (full : ∀x,q x≠0 ↔ parity x=p) :
    Nonempty (Receipt (ClosureSourceRows.ambientFamily G P) N.m) ∨
      Nonempty (StableDenseGaugeCurrent.SingularReceipt G P) := by
  let M := RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q
  have mappedActual : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality M :=
    RingHomRealization.realizes_map (ClosureSourceRows.embedding G) actual
  have mappedFull : ∀x,M x≠0 ↔ parity x=p := by
    intro x
    simpa [M,RingHomRealization.mapSignature] using full x
  rcases fullParity_or_bad N.range N.omega N.primitive
    (ClosureSourceRows.ambientFamily G P) (StableDenseGaugeCurrent.ambient_identity G P)
    (StableDenseGaugeCurrent.representatives G P torsion N) M mappedActual p mappedFull with
      canonical | bad
  · exact Or.inl canonical
  · obtain ⟨B,hn,ho,hr,hp⟩ := bad
    exact Or.inr (StableDenseGaugeCurrent.singular_receipt G P torsion N B hn ho hr hp)

/-- Existing clients can forget the strengthened data without changing the
anchor matrix, its actual graph, or the installed whole-current programme. -/
def forget (C : Canonical (ClosureSourceRows.ambientFamily G P)) :
    StableDenseGaugeAnchorContinuation.AnchorReceipt G P :=
  StableDenseGaugeAnchorContinuation.install G P C.anchor

inductive Outcome : Type 1 where
  | canonical (receipt : Receipt (ClosureSourceRows.ambientFamily G P) N.m)
  | singular (receipt : StableDenseGaugeCurrent.SingularReceipt G P)

def fromCurrent (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
    (literal : core.signature=⟨4,q⟩) (p : Bool)
    (full : ∀x,q x≠0 ↔ parity x=p) : Outcome G P torsion N := Classical.choice (by
  rcases row_or_original_singular G P torsion N q
    (Gadget.realizes_of_mem P.family .disequality _ (literal ▸ core.retained)) p full with
      canonical | singular
  · obtain ⟨C⟩ := canonical
    exact ⟨.canonical C⟩
  · obtain ⟨r⟩ := singular
    exact ⟨.singular r⟩)

def Outcome.forget (outcome : Outcome G P torsion N) : StableDenseGaugeAnchorContinuation.Outcome G P :=
  match outcome with
  | .canonical receipt => .anchor (GlobalCloseCompletionDenseCanonicalCurrent.forget G P receipt.canonical)
  | .singular receipt => .singular receipt


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionDenseCanonicalCurrent
end
