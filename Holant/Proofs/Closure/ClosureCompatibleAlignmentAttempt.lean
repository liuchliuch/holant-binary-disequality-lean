import Holant.Proofs.Closure.ClosureCompatibleAlignmentAnyPair
import Holant.Proofs.Closure.ClosureCompatibleAlignmentTags
import Holant.Proofs.Closure.ClosureCompatibleAlignmentCurrent

/-! The common-parity condition is tested on the real computed factor tables.
The producer returns an actual CompatibleCards object or a literal indexed
parity discrepancy; neither conclusion is a caller-selected success policy. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
open Holant.Dihedral.EndpointParallelogram

theorem common_parities_or_discrepancy {m r : ℕ} (positive : 0 < m)
    (A₀ A₁ : Fin (r+1) → Mat) (member₀ : ∀ e,A₀ e ∈ groupM m)
    (member₁ : ∀ e,A₁ e ∈ groupM m) :
    (∃ α : Fin (r+1) → Bool,(∀ e,HasParity (α e) (A₀ e)) ∧
      (∀ e,HasParity (α e) (A₁ e))) ∨
    (∃ e α,HasParity α (A₀ e) ∧ HasParity (!α) (A₁ e)) := by
  classical
  have first : ∀ e,∃ α,HasParity α (A₀ e) := fun e => group_hasParity positive (member₀ e)
  choose α parity₀ using first
  by_cases compatible : ∀ e,HasParity (α e) (A₁ e)
  · exact Or.inl ⟨α,parity₀,compatible⟩
  · right
    push_neg at compatible
    obtain ⟨e,notSame⟩ := compatible
    obtain ⟨β,parity₁⟩ := group_hasParity positive (member₁ e)
    have different : β ≠ α e := fun h => notSame (h ▸ parity₁)
    have opposite : β = !(α e) := by cases h : α e <;> cases β <;> simp_all
    exact ⟨e,α e,parity₀ e,by simpa only [opposite] using parity₁⟩

inductive AlignmentAttempt {m r : ℕ} {F : SignatureFamily Scalar}
    (G : ActualRepresentatives F m) (f : Signature Scalar (2*r+4))
    (sector : Bool → Bool) (phase : Bool → {t : Scalar // Roots m t})
    (p : Bool → (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (A : Bool → Fin (r+1) → Mat) (e : Fin (r+1))
  | compatible (cards : CompatibleCards G
      (Tensor.reindex (liftPair (protectedOrder (p false) e)).symm f))
      (sector_exact : cards.sector = sector) (phase_exact : cards.phase = phase)
      (factor_exact : ∀ b,cards.edgeFactor b = alignedTables p A b e)
  | parity (edge : Fin (r+1)) (α : Bool)
      (first : HasParity α (alignedTables p A false edge))
      (second : HasParity (!α) (alignedTables p A true edge))

/-- Actual chosen sample identities, not just matchings, are preserved in the
successful constructor.  A failed support-parity check returns its true table
index and both opposite-parity proofs for a protected-discrepancy consumer. -/
def attemptSelectedProducts {m r : ℕ} {F : SignatureFamily Scalar} (positive : 0 < m)
    (G : ActualRepresentatives F m) (f : Signature Scalar (2*r+4))
    (actual : Gadget.Realizes F .disequality f)
    (sector : Bool → Bool) (phase : Bool → {t : Scalar // Roots m t})
    (p : Bool → (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (A : Bool → Fin (r+1) → Mat) (κ : Bool → Scalar) (nonzero : ∀ b,κ b ≠ 0)
    (equation : ∀ b,Signature.contract (M (sector b) (phase b).val) f =
      productValue (p b) (A b) (κ b))
    (same : (Pairing.ofPorts (p false)).mate = (Pairing.ofPorts (p true)).mate)
    (member : ∀ b j,A b j ∈ groupM m) (e : Fin (r+1)) :
    AlignmentAttempt G f sector phase p A e := by
  classical
  have valid₀ : ∀ j,alignedTables p A false j ∈ groupM m := member false
  have valid₁ : ∀ j,alignedTables p A true j ∈ groupM m :=
    alignedFactor_group positive (p false) (p true) (A true) (member true)
  let branch := common_parities_or_discrepancy positive _ _ valid₀ valid₁
  by_cases compatible : ∃ α : Fin (r+1) → Bool,
      (∀ j,HasParity (α j) (alignedTables p A false j)) ∧
      (∀ j,HasParity (α j) (alignedTables p A true j))
  · let α := Classical.choose compatible
    have supports : ∀ b j,HasParity (α j) (alignedTables p A b j) := by
      intro b
      cases b
      · exact (Classical.choose_spec compatible).1
      · exact (Classical.choose_spec compatible).2
    let D := fromSelectedProductsAt G f actual sector phase p A κ nonzero equation same e α supports
    refine .compatible D rfl rfl ?_
    intro b
    change alignedTables (fun b => (p b).trans (protectedOrder (p false) e).symm) A b e = _
    rw [alignedTables_reindex]
  · have discrepancy := branch.resolve_left compatible
    let edge := Classical.choose discrepancy
    let data := Classical.choose_spec discrepancy
    let α := Classical.choose data
    have tags := Classical.choose_spec data
    exact .parity edge α tags.1 tags.2

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4)))
variable (sector : Bool → Bool) (phase : Bool → {t : Scalar // Roots N.m t})
variable (stable : ∀ g ∈ rawDeck P.family torsion f,
  Holant.Certificates.MatchingContractionClosure.MatchingOrZero (actualTransfers P.family) g)
variable (nonzero : ∀ b,normalizedCurrentCard G P torsion N f order (sector b) (phase b) ≠ 0)

def selectedCurrentPair (b : Bool) : CurrentSelectedCard G P torsion N f order (sector b) (phase b) :=
  selectCurrentCard G P torsion N f order (sector b) (phase b) stable (nonzero b)

/-- Closed CURRENT-deck specialization.  Both matching presentations, their
matching equality, original-field representative scalars, common-parity test
and the actual CompatibleCards factory are all derived internally. -/
def attemptCurrentPair (large : 2 ≤ r)
    (retained : (⟨2*r+4,f⟩ : AnySignature (OI.K G)) ∈ P.family) (e : Fin (r+1)) :
    AlignmentAttempt (currentRepresentatives G P torsion N)
      (Tensor.reindex order.symm (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f))
      sector phase
      (fun b => (selectedCurrentPair G P torsion N f order sector phase stable nonzero b).ports)
      (fun b => (selectedCurrentPair G P torsion N f order sector phase stable nonzero b).factors) e := by
  let S := selectedCurrentPair G P torsion N f order sector phase stable nonzero
  exact attemptSelectedProducts (by have := N.range; omega)
    (currentRepresentatives G P torsion N) _
    (realizes_reindex _ .disequality _
      (RingHomRealization.realizes_map (ClosureSourceRows.embedding G)
        (Gadget.realizes_of_mem P.family .disequality f retained)) order)
    sector phase (fun b => (S b).ports) (fun b => (S b).factors) (fun b => (S b).algebraic.scalar)
    (fun b => (S b).algebraic_scalar_nonzero) (fun b => (S b).coefficient_product)
    (current_selected_matchings_equal G P torsion N f order large stable
      (sector false) (sector true) (phase false) (phase true) (S false) (S true))
    (fun b j => (S b).factors_member j) e

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
