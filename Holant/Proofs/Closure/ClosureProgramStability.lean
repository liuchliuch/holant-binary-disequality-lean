import Holant.Proofs.Closure.DeckContraction
import Holant.Proofs.Closure.ClosureMarkedReversal
import Holant.Proofs.Closure.ClosureSourceRowsC2GroupFacts
import Holant.Proofs.Closure.ClosureLocalizationObstruction
import Holant.Certificates.MatchingContractionClosure.SinglePair

/-! Once the actual CURRENT deck is matching, any nonempty saved safe
contraction program remains matching. In particular, a genuine different-card
six-port localization of a higher-arity ancestor is impossible. The radius-zero
six-port case is deliberately not eliminated by this theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureProgramStability
open Holant Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Dihedral.TwoCardLocalization
variable {L I : Type} [Field L]

/-- Native first-pair contraction is exactly the named residual-port operation. -/
theorem native_contract_matching {G : Set (Binary (K:=L))}
    (group : ProjectiveMatrixGroup G) (native : (X : Binary (K:=L)) ∈ G)
    (reversal : ReversalStable G) {n : ℕ} (C : Binary (K:=L))
    (safe : SafeBinary G C) (f : Signature L (n+2)) (matching : MatchingOrZero G f) :
    MatchingOrZero G (Signature.contract C f) := by
  have h := (contractPair_closed group native reversal (0 : Fin (n+2)) 1
    Fin.zero_ne_one C safe f matching).reindex
      (remainingOrder (0 : Fin (n+2)) 1 Fin.zero_ne_one).symm
  rw [contractPair_order] at h
  have orderIdentity : Holant.Dihedral.CompatibleClosure.pairOrder (0 : Fin (n+2)) 1 =
      Equiv.refl _ := by simp [Holant.Dihedral.CompatibleClosure.pairOrder]
  simpa [orderIdentity,Tensor.reindex] using h

theorem ordered_contract_matching {G : Set (Binary (K:=L))}
    (group : ProjectiveMatrixGroup G) (native : (X : Binary (K:=L)) ∈ G)
    (reversal : ReversalStable G) {n : ℕ} (C : Binary (K:=L))
    (safe : SafeBinary G C) (f : Signature L (n+2)) (matching : MatchingOrZero G f)
    (order : Equiv.Perm (Fin (n+2))) :
    MatchingOrZero G (Signature.contract C (Tensor.reindex order.symm f)) :=
  native_contract_matching group native reversal C safe _ (matching.reindex order.symm)

/-- All literal instructions, including zero-producing closed components, are
handled recursively on the actual program. No final matching oracle is used. -/
theorem program_core_matching {G : Set (Binary (K:=L))}
    (group : ProjectiveMatrixGroup G) (native : (X : Binary (K:=L)) ∈ G)
    (reversal : ReversalStable G) (C : I → Kernel L) (safe : ∀ i, SafeBinary G (C i))
    {n m : ℕ} (p : Program I n m) (f : Signature L (n+2))
    (matching : MatchingOrZero G f) : MatchingOrZero G (p.core C f) := by
  induction p with
  | done n => exact matching
  | step order i rest ih =>
    exact ih (outsideClose order (C i) f)
      (ordered_contract_matching group native reversal (C i) (safe i) f matching
        (outsideOrder order))

/-- Literal retained identity provides the literal native transfer X. -/
theorem actual_native (F : SignatureFamily L) (identity : RetainsIdentity F) :
    (X : Binary (K:=L)) ∈ actualTransfers F := by
  refine ⟨1,ClosureSourceRows.identity_actual F identity,1,one_ne_zero,?_⟩
  simp [transfer]

/-- Safe binary and actual-transfer membership differ by one right X; retained
identity and the actual multiplication law supply that factor explicitly. -/
theorem safe_mem_actual (F : SignatureFamily L) (identity : RetainsIdentity F)
    (C : Binary (K:=L)) (safe : SafeBinary (actualTransfers F) C) :
    C ∈ actualTransfers F := by
  have h := actualTransfers_mul safe (actual_native F identity)
  simpa only [SafeBinary,transfer,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using h

/-- The first nonempty step is a literal current raw-deck scalar copy; all
remaining steps use proved matching contraction closure in the SAME group. -/
theorem nonempty_program_matching (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (identity : RetainsIdentity F) (C : I → Kernel L)
    (safe : ∀ i, SafeBinary (actualTransfers F) (C i))
    {n m : ℕ} (p : Program I n m) (nonempty : 0 < p.length)
    (f : Signature L (n+2))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g) :
    MatchingOrZero (actualTransfers F) (p.core C f) := by
  cases p with
  | done n => simp [Program.length] at nonempty
  | step order i rest =>
    exact program_core_matching
      (actualTransfers_projectiveMatrixGroup F (actualTransfers_nonempty F) torsion)
      (actual_native F identity) (ClosureMarkedReversal.actualTransfers_reversal F)
      C safe rest (outsideClose order (C i) f)
      (DeckContraction.orderedClosure_matching F torsion identity f stable
        (outsideOrder order) (C i) (safe_mem_actual F identity (C i) (safe i)))

/-- The same first-step argument works after ANY initial original-port
permutation. The combined literal order is used in the original CURRENT deck;
no stability of a separately regenerated reindexed deck is assumed. -/
theorem nonempty_ordered_program_matching (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (identity : RetainsIdentity F) (C : I → Kernel L)
    (safe : ∀ i, SafeBinary (actualTransfers F) (C i))
    {n m : ℕ} (p : Program I n m) (nonempty : 0 < p.length)
    (f : Signature L (n+2))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g)
    (initialOrder : Equiv.Perm (Fin (n+2))) :
    MatchingOrZero (actualTransfers F) (p.core C (Tensor.reindex initialOrder.symm f)) := by
  cases p with
  | done n => simp [Program.length] at nonempty
  | step order i rest =>
    apply program_core_matching
      (actualTransfers_projectiveMatrixGroup F (actualTransfers_nonempty F) torsion)
      (actual_native F identity) (ClosureMarkedReversal.actualTransfers_reversal F)
      C safe rest (outsideClose order (C i) (Tensor.reindex initialOrder.symm f))
    exact DeckContraction.orderedClosure_matching F torsion identity f stable
      ((outsideOrder order).trans initialOrder) (C i)
      (safe_mem_actual F identity (C i) (safe i))

/-- A scalar-corrected same-program six-port output with different inherited
matchings forces the program to be empty. Radius zero remains a separate base. -/
theorem different_six_port_forces_empty (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (identity : RetainsIdentity F) (C : I → Kernel L)
    (safe : ∀ i, SafeBinary (actualTransfers F) (C i))
    {n : ℕ} (p : Program I n 4) (f : Signature L (n+2))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g)
    (scalar : L) (scalar_ne : scalar ≠ 0) (A₀ A₁ : Kernel L)
    (different : DifferentProducts (actualTransfers F) 4
      (Signature.contract A₀ (scalar • p.core C f))
      (Signature.contract A₁ (scalar • p.core C f))) : p.length = 0 := by
  by_contra hn
  have positive : 0 < p.length := Nat.pos_of_ne_zero hn
  have matching := ContinuationTransport.matching_smul
    (nonempty_program_matching F torsion identity C safe p positive f stable) scalar scalar_ne
  exact ClosureLocalizationObstruction.native_different_cards_not_matching
    (actualTransfers_projectiveMatrixGroup F (actualTransfers_nonempty F) torsion)
    (scalar • p.core C f) A₀ A₁ different matching

/-- This eliminates the actual different-matching localization branch strictly
above six source ports, without assuming a six-port rigidity theorem. -/
theorem no_different_six_port_above_six (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (identity : RetainsIdentity F) (C : I → Kernel L)
    (safe : ∀ i, SafeBinary (actualTransfers F) (C i))
    {n : ℕ} (above : 4 < n) (p : Program I n 4) (f : Signature L (n+2))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g)
    (scalar : L) (scalar_ne : scalar ≠ 0) (A₀ A₁ : Kernel L) :
    ¬ DifferentProducts (actualTransfers F) 4
      (Signature.contract A₀ (scalar • p.core C f))
      (Signature.contract A₁ (scalar • p.core C f)) := by
  intro different
  have empty := different_six_port_forces_empty F torsion identity C safe p f stable
    scalar scalar_ne A₀ A₁ different
  have ports := p.port_count
  omega

/-- The surviving length-zero endpoint has exactly six source ports. -/
theorem different_six_port_source_arity (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (identity : RetainsIdentity F) (C : I → Kernel L)
    (safe : ∀ i, SafeBinary (actualTransfers F) (C i))
    {n : ℕ} (p : Program I n 4) (f : Signature L (n+2))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g)
    (scalar : L) (scalar_ne : scalar ≠ 0) (A₀ A₁ : Kernel L)
    (different : DifferentProducts (actualTransfers F) 4
      (Signature.contract A₀ (scalar • p.core C f))
      (Signature.contract A₁ (scalar • p.core C f))) : n+2 = 6 := by
  have empty := different_six_port_forces_empty F torsion identity C safe p f stable
    scalar scalar_ne A₀ A₁ different
  have ports := p.port_count
  omega

/-- Above six source ports, two nonzero matching cards cannot have different
literal matchings. The residual program is CONSTRUCTED by the frozen finite
matching-surgery theorem using the actual safe native X kernel; no program or
six-port rigidity witness is an input to this result. -/
theorem stable_cards_not_different (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (identity : RetainsIdentity F) (r : ℕ) (positive : 0 < r)
    (f : Signature L (2*r+6))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g)
    (A₀ A₁ : Kernel L) :
    ¬ DifferentProducts (actualTransfers F) (2*r+4)
      (Signature.contract A₀ f) (Signature.contract A₁ f) := by
  intro different
  let group := actualTransfers_projectiveMatrixGroup F (actualTransfers_nonempty F) torsion
  obtain ⟨p,length,inherited⟩ := different_products_program (actualTransfers F)
    group (actual_native F identity) (ClosureMarkedReversal.actualTransfers_reversal F)
    X (safe_X group) r _ _ different
  have outputDifferent : DifferentProducts (actualTransfers F) 4
      (Signature.contract A₀ (p.core (fun _ => X) f))
      (Signature.contract A₁ (p.core (fun _ => X) f)) := by
    simpa only [Program.inherited_card] using inherited
  have matching := nonempty_program_matching F torsion identity (fun _ => X)
    (fun _ => safe_X group) p (by omega) f stable
  exact ClosureLocalizationObstruction.native_different_cards_not_matching group
    (p.core (fun _ => X) f) A₀ A₁ outputDifferent matching

/-- Same-ancestor card alignment is a theorem, independent of enumeration,
orientation and nonzero factor scalars. It does not assume a shared matching. -/
theorem stable_card_matchings_equal (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (identity : RetainsIdentity F) (r : ℕ) (positive : 0 < r)
    (f : Signature L (2*r+6))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g)
    (A₀ A₁ : Kernel L) (M₀ M₁ : Presentation L (Fin (2*r+4)))
    (valid₀ : M₀.Valid (actualTransfers F)) (valid₁ : M₁.Valid (actualTransfers F))
    (scalar₀ : M₀.scalar ≠ 0) (scalar₁ : M₁.scalar ≠ 0)
    (equation₀ : Signature.contract A₀ f = M₀.tensor)
    (equation₁ : Signature.contract A₁ f = M₁.tensor) :
    (presentationMatching M₀).mate = (presentationMatching M₁).mate := by
  by_contra different
  exact stable_cards_not_different F torsion identity r positive f stable A₀ A₁
    ⟨M₀,M₁,valid₀,valid₁,scalar₀,scalar₁,equation₀,equation₁,different⟩

/-- Every ordered deleted pair is covered by the SAME current raw-deck
hypothesis. The residual cards keep the selected original residual order. -/
theorem stable_ordered_cards_not_different (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (identity : RetainsIdentity F) (r : ℕ) (positive : 0 < r)
    (f : Signature L (2*r+6))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g)
    (order : Equiv.Perm (Fin (2*r+6))) (A₀ A₁ : Kernel L) :
    ¬ DifferentProducts (actualTransfers F) (2*r+4)
      (Signature.contract A₀ (Tensor.reindex order.symm f))
      (Signature.contract A₁ (Tensor.reindex order.symm f)) := by
  intro different
  let group := actualTransfers_projectiveMatrixGroup F (actualTransfers_nonempty F) torsion
  obtain ⟨p,length,inherited⟩ := different_products_program (actualTransfers F)
    group (actual_native F identity) (ClosureMarkedReversal.actualTransfers_reversal F)
    X (safe_X group) r _ _ different
  have outputDifferent : DifferentProducts (actualTransfers F) 4
      (Signature.contract A₀ (p.core (fun _ => X) (Tensor.reindex order.symm f)))
      (Signature.contract A₁ (p.core (fun _ => X) (Tensor.reindex order.symm f))) := by
    simpa only [Program.inherited_card] using inherited
  have matching := nonempty_ordered_program_matching F torsion identity (fun _ => X)
    (fun _ => safe_X group) p (by omega) f stable order
  exact ClosureLocalizationObstruction.native_different_cards_not_matching group
    (p.core (fun _ => X) (Tensor.reindex order.symm f)) A₀ A₁ outputDifferent matching

/-- Direct all-even-arity interface in the native minimum-core indexing m+2.
The actual input tensor and residual order are retained through the arithmetic
normalization; callers need not supply a localization radius or program. -/
theorem stable_even_ordered_cards_not_different (F : SignatureFamily L)
    (torsion : ResidualTorsion F) (identity : RetainsIdentity F)
    {m : ℕ} (large : 6 ≤ m) (even : Even m) (f : Signature L (m+2))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g)
    (order : Equiv.Perm (Fin (m+2))) (A₀ A₁ : Kernel L) :
    ¬ DifferentProducts (actualTransfers F) m
      (Signature.contract A₀ (Tensor.reindex order.symm f))
      (Signature.contract A₁ (Tensor.reindex order.symm f)) := by
  obtain ⟨r,positive,equation⟩ : ∃ r, 0 < r ∧ m = 2*r+4 := by
    obtain ⟨k,hk⟩ := even
    exact ⟨k-2,by omega,by omega⟩
  subst m
  exact stable_ordered_cards_not_different F torsion identity r positive f stable order A₀ A₁

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureProgramStability
