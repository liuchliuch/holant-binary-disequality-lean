import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenLocalOutcome
import Holant.Proofs.Hardness.EOBinaryPlaneTract

/-! Singleton EO tractability on a complement-closed quaternary row gives
actual affine or product membership. The source-backed sparse output retains
the same class after undoing its literal independent bit flips. No common
family basis, transformed-edge membership, or whole-family criterion is inferred. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentEvenEOTract
open Holant Holant.Tractable Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.MainChain
open FiveSupportEOOrdering (middleWord middleCoeff)

/-- Each missing middle word has the literal opposite middle index. -/
theorem middleWord_complement (i : Fin 6) :
    complementWord (middleWord i) = middleWord (5-i) := by
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

/-- The signed triple-support condition excludes all six middle words.
The positive sign fails at 0000; the negative sign fails at 1111. -/
theorem missing_middle_of_supports (M : Signature AlgebraicComplex 4)
    (eo : DenseEOUnitLocal.EOSupport M) (sign : EOSign)
    (supports : ∀ a b c, M a ≠ 0 → M b ≠ 0 → M c ≠ 0 →
      M (tripleXor a b c) ≠ 0 ∨ 0 < sign.value * charge (tripleXor a b c)) :
    ∃ i : Fin 6, middleCoeff M i = 0 := by
  classical
  by_contra full
  push Not at full
  cases sign with
  | positive =>
    have h := supports (middleWord 0) (middleWord 1) (middleWord 2)
      (full 0) (full 1) (full 2)
    have word : tripleXor (middleWord 0) (middleWord 1) (middleWord 2) =
        (fun _ : Fin 4 => false) := by decide
    rw [word] at h
    have zero := eo (fun _ => false) (by decide)
    norm_num [zero, EOSign.value, charge, weight, Fin.sum_univ_four] at h
  | negative =>
    have h := supports (middleWord 0) (middleWord 1) (middleWord 3)
      (full 0) (full 1) (full 3)
    have word : tripleXor (middleWord 0) (middleWord 1) (middleWord 3) =
        (fun _ : Fin 4 => true) := by decide
    rw [word] at h
    have zero := eo (fun _ => true) (by decide)
    norm_num [zero, EOSign.value, charge, weight, Fin.sum_univ_four] at h

/-- Reconstruct actual row membership in the very class used by its paired
restrictions, once complementary zero entries have been established. -/
theorem actual_class_of_opposite_zeros (M : Signature AlgebraicComplex 4)
    (eo : DenseEOUnitLocal.EOSupport M) (C : EOClass)
    (restrictions : ∀ p : OrientedPerfectPairing 4, C.Holds (p.restrict M))
    (i : Fin 6) (zero : middleCoeff M i = 0) (opposite : middleCoeff M (5-i) = 0) :
    C.Holds M := by
  have h := restrictions (EOBinaryPlaneTract.transportPairing
    (FiveSupportEOOrdering.orderAt i) EOBinaryPlaneCore.pairing)
  rw [EOBinaryPlaneTract.restriction_reindex, EOBinaryPlaneCore.restrict_eq] at h
  change C.Holds (EOBinaryPlaneCore.compress (EOBinaryPlaneCore.normalized M i)) at h
  cases C with
  | affine =>
    have lifted := EOBinaryPlaneTract.affine_lift h
    rw [EOBinaryPlaneCore.normalized_lift M eo i zero opposite] at lifted
    exact EOBinaryPlaneTract.affine_unreindex (FiveSupportEOOrdering.orderAt i) M lifted
  | product =>
    have lifted := EOBinaryPlaneTract.product_lift h
    rw [EOBinaryPlaneCore.normalized_lift M eo i zero opposite] at lifted
    exact EOBinaryPlaneTract.product_unreindex (FiveSupportEOOrdering.orderAt i) M lifted

/-- The singleton criterion selects a class of the actual EO signature.
Its chosen restriction class is retained, without asserting anything about
other rows or edge signatures. -/
theorem eoTract_actual_class (M : Signature AlgebraicComplex 4)
    (eo : DenseEOUnitLocal.EOSupport M)
    (closed : ∀ x, M (complementWord x) = 0 ↔ M x = 0)
    (tract : EOTract {⟨4,M⟩}) :
    ∃ C : EOClass, C.Holds M ∧
      ∀ p : OrientedPerfectPairing 4, C.Holds (p.restrict M) := by
  rcases tract with ⟨_,_,sign,C,supports,restrictions⟩
  have hs := supports ⟨4,M⟩ (by simp)
  have hr := restrictions ⟨4,M⟩ (by simp)
  obtain ⟨i,zero⟩ := missing_middle_of_supports M eo sign hs
  have opposite : middleCoeff M (5-i) = 0 := by
    rw [middleCoeff, ←middleWord_complement]
    exact (closed (middleWord i)).mpr zero
  exact ⟨C,actual_class_of_opposite_zeros M eo C hr i zero opposite,hr⟩

theorem eoTract_actual_membership (M : Signature AlgebraicComplex 4)
    (eo : DenseEOUnitLocal.EOSupport M)
    (closed : ∀ x, M (complementWord x) = 0 ↔ M x = 0)
    (tract : EOTract {⟨4,M⟩}) : Affine M ∨ Product M := by
  obtain ⟨C,member,_⟩ := eoTract_actual_class M eo closed tract
  cases C
  · exact Or.inl member
  · exact Or.inr member

theorem xorWord_involution (x mask : Word) : xorWord (xorWord x mask) mask = x := by
  funext j
  dsimp only [xorWord]
  cases x j <;> cases mask j <;> rfl

theorem xorWord_complement (x mask : Word) :
    xorWord (complementWord x) mask = complementWord (xorWord x mask) := by
  funext j
  dsimp only [xorWord,complementWord]
  cases x j <;> cases mask j <;> rfl

theorem xorWord_affine (mask : Word) :
    TwoTranslate.IsAffineMap (fun x => xorWord x mask) := by
  intro x y
  funext j
  simp only [xorWord, AffinePhase.xor, AffinePhase.origin]
  cases x j <;> cases y j <;> cases mask j <;> rfl

/-- Both source classes are preserved by the exact independent flips. -/
theorem class_flip (C : EOClass) (M : Signature AlgebraicComplex 4) (mask : Word)
    (member : C.Holds M) : C.Holds (Flip.value M mask) := by
  cases C with
  | affine => exact Affine.precompose member (fun x => xorWord x mask) (xorWord_affine mask)
  | product =>
    have h := EOBinaryPlaneTract.product_signed (fun j : Fin 4 => (j,mask j)) member
    have same : (fun x => M (EOBinaryPlaneTract.signedMap (fun j : Fin 4 => (j,mask j)) x)) =
        Flip.value M mask := by
      funext x
      apply congrArg M
      funext j
      dsimp only [EOBinaryPlaneTract.signedMap,xorWord]
      have bit : ∀ a b : Bool, (if b then !a else a) = (a ^^ b) := by decide
      exact bit (x j) (mask j)
    exact same ▸ h

theorem class_unflip (C : EOClass) (M : Signature AlgebraicComplex 4) (mask : Word)
    (member : C.Holds (Flip.value M mask)) : C.Holds M := by
  have h := class_flip C (Flip.value M mask) mask member
  have same : Flip.value (Flip.value M mask) mask = M := by
    funext x
    exact congrArg M (xorWord_involution x mask)
  exact same ▸ h

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
open StableCurrentEvenEOTransport StableCurrentEvenLocalOutcome

include P torsion N core literal stable in
/-- Complementary closure is transported from the actual retained raw deck
to the exact algebraic EO graph output. -/
theorem eoRow_complement_closed (d : SparseOutput G P q core literal) :
    ∀ x, eoRow G P q core literal d (complementWord x) = 0 ↔
      eoRow G P q core literal d x = 0 := by
  have closed := StableCurrentEvenNativeM.current_complement_closed
    G P torsion N q core literal stable
  intro x
  rw [eoRow_exact, Flip.value, Flip.value, xorWord_complement]
  simpa only [embedded,RingHomRealization.mapSignature,map_eq_zero] using closed (xorWord x d.mask)

include torsion N stable in
/-- The exact sparse output and the embedded original row belong to the same
affine/product class selected by singleton EO tractability. -/
theorem sparse_actual_class (d : SparseOutput G P q core literal)
    (tract : EOTract {⟨4,eoRow G P q core literal d⟩}) :
    ∃ C : EOClass, C.Holds (eoRow G P q core literal d) ∧
      C.Holds (embedded G q) := by
  obtain ⟨C,member,_⟩ := eoTract_actual_class (eoRow G P q core literal d)
    (eoRow_support G P q core literal d)
    (eoRow_complement_closed G P torsion N q core literal stable d) tract
  refine ⟨C,member,?_⟩
  rw [eoRow_exact] at member
  exact class_unflip C (embedded G q) d.mask member

include torsion N stable in
theorem sparse_actual_membership (d : SparseOutput G P q core literal)
    (tract : EOTract {⟨4,eoRow G P q core literal d⟩}) :
    Affine (embedded G q) ∨ Product (embedded G q) := by
  obtain ⟨C,_,member⟩ := sparse_actual_class G P torsion N q core literal stable d tract
  cases C
  · exact Or.inl member
  · exact Or.inr member

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentEvenEOTract
end
