import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeEqualityAnchor
import Holant.Proofs.Dichotomy.Retained.StableDenseResidualCharts
import Holant.Certificates.EqualityQuaternary.PhysicalFlip

/-! The actual dense-parity endpoint, including originally odd support.
The existing finite Flip graph uses only the original row and retained I;
its compatible even chart reaches the equality anchor over that same palette. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseGaugeChartAnchor
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.EightVertexNonexception hiding Word
open Holant.LocalDrafts.RemoteWork.HardnessChainV1

theorem chart_conditions (M : Signature AlgebraicComplex 4) (p : Bool)
    (full : ∀ x, M x ≠ 0 ↔ parity x = p) (mask : Word) (same : parity mask = p) :
    EvenSupport (Flip.value M mask) ∧ StableDenseParityAlgebra.Dense (Flip.value M mask) := by
  have live (x : Word) (hx : parity x = false) : Flip.value M mask x ≠ 0 := by
    apply (full _).mpr
    rw [parity_xorWord,hx,same]
    exact Bool.false_xor p
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x odd
    by_contra hn
    have hp := (full (xorWord x mask)).mp hn
    have ho : weight x % 2 = 1 := by omega
    rw [parity_xorWord,same,(parity_weight x).mpr ho] at hp
    cases p <;> contradiction
  all_goals exact live _ (by decide)

/-- Only the newly constructed row's own actual deck is tested. A failed
test remains an actual parity-preserving binary over the same source. -/
theorem products_or_bad {m : ℕ} (hm : 3 ≤ m) (F : SignatureFamily AlgebraicComplex)
    (hI : RetainsIdentity F) (reps : MonomialRepresentatives F m)
    (M : Signature AlgebraicComplex 4) (actual : Gadget.Realizes F .disequality M)
    (full : ∀ x, M x ≠ 0 ↔ parity x = false) (even : EvenSupport M) :
    StableDenseResidualAlgebra.Products M ∨ EightVertexGaugeFamily.BadBinary F m := by
  classical
  by_cases physical : MonomialPhysicalDeck reps M
  · have safe := monomial_safeDeck hm reps M physical
    have hfull : ∀ x, complexTensor M x ≠ 0 ↔ parity x = false := by
      intro x
      simpa [complexTensor] using full x
    have hp := StableDenseResidualCharts.chart_products hm (complexTensor M) safe false
      hfull (fun _ => false) rfl
    have hh : (fun x => complexTensor M (xorWord x (fun _ => false))) = complexTensor M := by
      funext x
      exact congrArg (complexTensor M) (funext (fun i => Bool.xor_false (x i)))
    rw [hh] at hp
    refine Or.inl ⟨?_,?_,?_⟩
    · apply Subtype.ext
      simpa [entries,complexTensor] using hp.1
    · apply Subtype.ext
      simpa [entries,complexTensor] using hp.2.1
    · apply Subtype.ext
      simpa [entries,complexTensor] using hp.2.2
  · simp only [MonomialPhysicalDeck] at physical
    push Not at physical
    obtain ⟨e,p,t,hn,ho⟩ := physical
    exact Or.inr ⟨_,hn,fun hg => ho
      ((EightVertexGaugeRepresentativeLines.line_iff_group (by omega) F reps _).mpr hg),
      EightVertexGaugePhysicalOutcome.physical_card_realizes F hI M actual e _ (reps.actual p t),
      EightVertexGaugeParity.physical_card_parity F reps M even e p t⟩

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4)
include torsion N

/-- Full current dense-parity continuation. Chart access and complementary
products are derived from the actual old-family row, even on odd support. -/
theorem row_fullParity_anchor_or_original_singular
    (sourceActual : Gadget.Realizes P.family .disequality q) (p : Bool)
    (full : ∀ x, q x ≠ 0 ↔ parity x = p) :
    Holant.EightVertex.ProductAnchor.HasEqualityAnchor (ClosureSourceRows.ambientFamily G P) ∨
      Nonempty (StableDenseGaugeCurrent.SingularReceipt G P) := by
  let mask : Word := ![p,false,false,false]
  have same : parity mask = p := by cases p <;> rfl
  let M := RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q
  have actual : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality M :=
    RingHomRealization.realizes_map (ClosureSourceRows.embedding G) sourceActual
  have hi : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality
      (kernelSignature Signature.equality) :=
    Gadget.realizes_of_mem _ .disequality _ (StableDenseGaugeCurrent.ambient_identity G P)
  have chartActual := Flip.actual (ClosureSourceRows.ambientFamily G P) M actual hi mask
  have mappedFull : ∀ x, M x ≠ 0 ↔ parity x = p := by
    intro x
    simpa [M,RingHomRealization.mapSignature] using full x
  obtain ⟨even,dense⟩ := chart_conditions M p mappedFull mask same
  have chartFull : ∀ x, Flip.value M mask x ≠ 0 ↔ parity x = false := by
    intro x
    change M (xorWord x mask) ≠ 0 ↔ _
    rw [mappedFull,parity_xorWord,same]
    cases parity x <;> cases p <;> decide
  rcases products_or_bad N.range (ClosureSourceRows.ambientFamily G P)
    (StableDenseGaugeCurrent.ambient_identity G P)
    (StableDenseGaugeCurrent.representatives G P torsion N)
    (Flip.value M mask) chartActual chartFull even with products | bad
  · exact StableDenseGaugeEqualityAnchor.ambient_anchor_or_original_singular G P torsion N
      (Flip.value M mask) chartActual even dense products
  · obtain ⟨B,hn,ho,hr,hp⟩ := bad
    exact Or.inr (StableDenseGaugeCurrent.singular_receipt G P torsion N B hn ho hr hp)

theorem current_anchorStep_or_original_singular (core : MinimumCore P.family)
    (literal : core.signature = ⟨4,q⟩)
    (_stable : ∀ g ∈ rawDeck P.family torsion q,
      MatchingOrZero (actualTransfers P.family) g) (p : Bool)
    (full : ∀ x, q x ≠ 0 ↔ parity x = p) :
    Nonempty (QuaternaryEqualityTerminal.AnchorStep (ClosureSourceRows.ambientFamily G P)) ∨
      Nonempty (StableDenseGaugeCurrent.SingularReceipt G P) := by
  rcases row_fullParity_anchor_or_original_singular G P torsion N q
    (Gadget.realizes_of_mem P.family .disequality _ (literal ▸ core.retained)) p full
    with anchor | singular
  · exact Or.inl (QuaternaryEqualityTerminal.anchorStep_exists anchor)
  · exact Or.inr singular

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseGaugeChartAnchor
end
