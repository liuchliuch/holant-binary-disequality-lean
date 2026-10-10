import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenNativeM
import Holant.Proofs.Hardness.DenseEOUnitLocal

/-! Sparse native-M parity supports have an actual EO output. The mask is a
missing word in the proved supported parity, so the same exact one-q plus
literal-I graph kills both corners. Dense parity support is an explicit
alternative. The graph is descended and compiled over the original palette. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentEvenEOTransport
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.MainChain

private theorem zero_weight_word {n : ℕ} (x : Fin n → Bool) (zero : weight x = 0) :
    x = fun _ => false := by
  funext i
  have bound : (if x i then 1 else 0 : ℕ) ≤ weight x := by
    unfold weight
    exact Finset.single_le_sum (f := fun j : Fin n => if x j then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [zero] at bound
  cases hi : x i <;> simp_all

theorem eo_of_missing_parity_word (q : Signature AlgebraicComplex 4) (mask : Word)
    (paritySupported : ∀ x, q x ≠ 0 → parity x = parity mask)
    (missing : q mask = 0) (missingComplement : q (Holant.Marked.SupportAtlas.complement mask) = 0) :
    DenseEOUnitLocal.EOSupport (Flip.value q mask) := by
  intro x outside
  by_contra live
  have hp := paritySupported (xorWord x mask) live
  rw [parity_xorWord] at hp
  have even : parity x = false := by
    cases hx : parity x <;> cases hm : parity mask <;> simp_all
  have notOdd : weight x % 2 ≠ 1 := by
    intro odd
    have h := (parity_weight x).mpr odd
    rw [even] at h
    contradiction
  have bound := weight_le x
  have extremes : weight x = 0 ∨ weight x = 4 := by omega
  rcases extremes with zero | full
  · have word := zero_weight_word x zero
    subst x
    exact live (by simpa [Flip.value,xorWord] using missing)
  · have opposite : weight (Holant.Marked.SupportAtlas.complement x) = 0 := by
      have h := weight_compl_add x
      change weight (Holant.Marked.SupportAtlas.complement x) + weight x = 4 at h
      omega
    have word : x = fun _ => true := by
      have h := zero_weight_word (Holant.Marked.SupportAtlas.complement x) opposite
      funext i
      have hi := congrFun h i
      cases hx : x i <;> simp_all [Holant.Marked.SupportAtlas.complement]
    subst x
    exact live (by simpa [Flip.value,xorWord,Holant.Marked.SupportAtlas.complement] using missingComplement)

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature = ⟨4,q⟩)
variable (stable : ∀ g ∈ rawDeck P.family torsion q,
  MatchingOrZero (actualTransfers P.family) g)

abbrev embedded : Signature AlgebraicComplex 4 :=
  RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q

include P torsion N core literal stable in
/-- Both the supported parity and complementary closure come from the
actual retained physical deck; neither is a caller's EO hypothesis. -/
theorem parity_and_complement :
    ∃ p : Bool, (∀ x, q x ≠ 0 → parity x = p) ∧
      (∀ x, q (Holant.Marked.SupportAtlas.complement x) = 0 ↔ q x = 0) := by
  let reps := ClosureSourceRows.monomialRepresentatives G P torsion N q core literal
  have physical := ClosureSourceRows.monomial_sourceDeck G P torsion N q core literal stable
  have deck := deckSupport_of_samples N.range 1 one_ne_zero (by simp)
    (complexTensor (embedded G q)) (monomial_safeDeck N.range reps (embedded G q) physical)
  have nonzero : q ≠ 0 := by
    have h : Prime (⟨4,q⟩ : AnySignature (OI.K G)) :=
      (congrArg Holant.LocalDrafts.FinitePGL2.Stabilization.Prime literal).mp core.prime
    exact h.1
  obtain ⟨x,hx⟩ : ∃ x, q x ≠ 0 := by
    by_contra h
    push Not at h
    exact nonzero (funext h)
  have live : nonzeroBit (complexTensor (embedded G q) x) = true := by
    simp [embedded,complexTensor,RingHomRealization.mapSignature,hx]
  obtain ⟨p,hp,hc⟩ := classification deck ⟨x,live⟩
  refine ⟨p,?_,?_⟩
  · intro y hy
    apply hp y
    simp [embedded,complexTensor,RingHomRealization.mapSignature,hy]
  · exact StableCurrentEvenNativeM.current_complement_closed G P torsion N q core literal stable

/-- The actual missing-corner condition still needed in the dense parity
case. No vanishing corner is inferred merely from even support. -/
def FullParity (q : Signature (OI.K G) 4) (p : Bool) : Prop :=
  ∀ x, q x ≠ 0 ↔ parity x = p

theorem fullParity_card (p : Bool) (full : FullParity G q p) :
    ((Finset.univ : Finset Word).filter fun x => q x ≠ 0).card = 8 := by
  classical
  have exactSupport : (Finset.univ.filter fun x => q x ≠ 0) =
      (Finset.univ.filter fun x => parity x = p) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,full x]
  rw [exactSupport]
  cases p <;> decide

include literal in
theorem graph_uses (mask : Word) :
    ∀ v, (⟨(Flip.network (embedded G q) mask).shape.arity v,
      (Flip.network (embedded G q) mask).vertex v⟩ : AnySignature AlgebraicComplex) ∈
      RingHomRealization.mapFamily (ClosureSourceRows.embedding G) P.family := by
  intro v
  by_cases ancestor : v = Flip.ancestor (embedded G q) mask
  · rw [ancestor,(Flip.labels_exact (embedded G q) mask).1]
    exact ⟨⟨4,q⟩,literal ▸ core.retained,rfl⟩
  · rw [(Flip.labels_exact (embedded G q) mask).2 v ancestor]
    refine ⟨⟨2,binarySignature (Signature.equality : Binary (K:=OI.K G))⟩,P.equality,?_⟩
    unfold RingHomRealization.mapAny
    congr 1
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [RingHomRealization.mapSignature,binarySignature,kernelSignature,Signature.equality,h0,h1]

/-- The exact Flip graph, its literal original q/I labels, native-X edges,
one-q count and both charged source programmes are retained together. -/
structure SparseOutput : Type 1 where
  mask : Word
  missing : q mask = 0
  paritySupported : ∀ x, q x ≠ 0 → parity x = parity mask
  eo : DenseEOUnitLocal.EOSupport (Flip.value (embedded G q) mask)
  access : ClosurePhysicalBridge.NetworkGraphAccess G P (ClosureSourceRows.embedding G)
    (Flip.network (embedded G q) mask) (graph_uses G P q core literal mask)
  accessIdentity : access = ClosurePhysicalBridge.fromNetwork G P (ClosureSourceRows.embedding G)
    (Flip.network (embedded G q) mask) (graph_uses G P q core literal mask)
    (Flip.native (embedded G q) mask)
  oneOriginal : (Finset.univ.filter (fun v : Fin (Flip.network (embedded G q) mask).shape.vertices =>
    (Flip.network (embedded G q) mask).shape.arity v = 4)).card = 1

include P torsion N core literal stable in
/-- Closed source dispatch. The full-parity alternative records the exact
obstruction to this EO transport; the sparse alternative constructs all data. -/
theorem sparse_or_full : (∃ p, FullParity G q p) ∨ Nonempty (SparseOutput G P q core literal) := by
  classical
  obtain ⟨p,hp,hc⟩ := parity_and_complement G P torsion N q core literal stable
  by_cases full : ∀ x, parity x = p → q x ≠ 0
  · exact Or.inl ⟨p,fun x => ⟨hp x,full x⟩⟩
  push Not at full
  obtain ⟨mask,hmask,missing⟩ := full
  have paritySupported : ∀ x, q x ≠ 0 → parity x = parity mask :=
    fun x hx => (hp x hx).trans hmask.symm
  have eo := eo_of_missing_parity_word (embedded G q) mask
    (by intro x hx; exact paritySupported x (by simpa [embedded,RingHomRealization.mapSignature] using hx))
    (by simp [embedded,RingHomRealization.mapSignature,missing])
    (by simp [embedded,RingHomRealization.mapSignature,(hc mask).mpr missing])
  exact Or.inr ⟨⟨mask,missing,paritySupported,eo,
    ClosurePhysicalBridge.fromNetwork G P (ClosureSourceRows.embedding G)
      (Flip.network (embedded G q) mask) (graph_uses G P q core literal mask)
      (Flip.native (embedded G q) mask),rfl,Flip.quaternary_count (embedded G q) mask⟩⟩

namespace SparseOutput
variable (d : SparseOutput G P q core literal)
abbrev output : Signature (OI.K G) 4 := d.access.output
abbrev toOriginal := d.access.toOriginal
abbrev fromOriginal := d.access.fromOriginal

theorem mapped_output : RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
    (d.output G P q core literal) = Flip.value (embedded G q) d.mask :=
  d.access.mappedOutput.trans (Flip.denote (embedded G q) d.mask)

/-- Coefficient descent introduces no scale: the original-field output is
literally the original q evaluated at the bit-flipped ordered word. -/
theorem output_literal : d.output G P q core literal = fun x => q (xorWord x d.mask) := by
  funext x
  apply (ClosureSourceRows.embedding G).injective
  exact congrFun (d.mapped_output G P q core literal) x

theorem output_eo : DenseEOUnitLocal.EOSupport (d.output G P q core literal) := by
  intro x hx
  apply (ClosureSourceRows.embedding G).injective
  have h := congrFun (d.mapped_output G P q core literal) x
  rw [d.eo x hx] at h
  exact h.trans (map_zero _).symm
end SparseOutput

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentEvenEOTransport
end
