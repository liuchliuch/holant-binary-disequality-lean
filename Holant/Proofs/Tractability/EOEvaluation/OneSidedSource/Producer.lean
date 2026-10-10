import Holant.ChargeConservation
import Holant.Tractable.Downward
import Holant.Proofs.Algorithms.KSourceTransport
import Holant.Proofs.Reductions.RootPreprocessing.FieldTransport
import Holant.Proofs.Tractability.EOEvaluation.Source


namespace Holant.LocalDrafts.Tractability.EOEvaluation.OneSidedSource.Producer
open Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

abbrev native := KSourceTransport.nativeSignatures G
def central (i : Fin s) : Signature AlgebraicComplex (arity i.val) :=
  Signature.centralRestriction (native G i)
abbrev count := RootPreprocessing.count (central G)
abbrev targetArity := RootPreprocessing.targetArity (central G)
abbrev targetTable := RootPreprocessing.targetTable (central G)
abbrev Input := ExactSignatureTables.Input s 1 arity

theorem native_nonzero_original (i : Fin s) (hn : native G i ≠ 0) : G i ≠ 0 := by
  intro hz
  apply hn
  simp [native, KSourceTransport.nativeSignatures, InvertibleKernel.action, hz]

theorem central_nonzero_native (i : Fin s) (hc : central G i ≠ 0) : native G i ≠ 0 := by
  intro hz
  apply hc
  funext x
  simp [central, Signature.centralRestriction, hz]

theorem native_support_original (i : Fin s) (x : Fin (arity i.val) → Bool)
    (hx : native G i x ≠ 0) : G i ≠ 0 :=
  native_nonzero_original G i (fun hz => hx (congrFun hz x))

theorem nullary_charge (i : Fin s) (hi : arity i.val = 0)
    (x : Fin (arity i.val) → Bool) : Holant.charge x = 0 := by
  have hw : Holant.weight x = 0 := by
    have hle := Holant.weight_le x
    omega
  simp [Holant.charge, hw, hi]

variable (Gamma : SignatureFamily AlgebraicComplex)
    (hmem : ∀ i, (⟨arity i.val, G i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)

include hmem in
theorem native_member (i : Fin s) (hi : 0 < arity i.val) (hn : G i ≠ 0) :
    (⟨arity i.val, native G i⟩ : AnySignature AlgebraicComplex) ∈
      kCoordinates (preprocess Gamma) :=
  ⟨⟨arity i.val, G i⟩, ⟨hmem i, hi, hn⟩, rfl⟩

include hmem in
/-- One sign governs ALL original labels, including those removed by preprocess. -/
theorem common_sign (h : OneSidedAlternative (preprocess Gamma)) :
    ∃ ε : ℤ, ε ≠ 0 ∧
      ∀ i x, native G i x ≠ 0 → 0 ≤ ε * Holant.charge x := by
  rcases h.1 with hp | hn
  · refine ⟨1, by decide, ?_⟩
    intro i x hx
    by_cases hi : 0 < arity i.val
    · simpa only [one_mul] using hp _
        (native_member G Gamma hmem i hi (native_support_original G i x hx)) x hx
    · have hz : Holant.charge x = 0 := nullary_charge i (by omega) x
      simp only [hz, mul_zero, le_refl]
  · refine ⟨-1, by decide, ?_⟩
    intro i x hx
    by_cases hi : 0 < arity i.val
    · have hc := hn _
        (native_member G Gamma hmem i hi (native_support_original G i x hx)) x hx
      simpa only [neg_one_mul, neg_nonneg] using hc
    · have hz : Holant.charge x = 0 := nullary_charge i (by omega) x
      simp only [hz, mul_zero, le_refl]

def network (r : Input (s := s) (arity := arity)) : Network AlgebraicComplex 0 :=
  r.val.realize r.property (native G) KSourceTransport.nativeEdges

theorem native_edges (r : Input (s := s) (arity := arity)) :
    ∀ e, (network G r).edge e = Signature.disequality := fun _ => rfl

/-- Transport along the actual bounded label of each raw vertex. Keeping the
table abstract here avoids expanding its fixed K-coordinate arithmetic. -/
private theorem realize_common_sign {t b : ℕ} {a : ℕ → ℕ}
    (r : RawClosedNetwork) (hr : r.WellFormed t b a)
    (table : (i : Fin t) → Signature AlgebraicComplex (a i.val))
    (edges : Fin b → Kernel AlgebraicComplex) (ε : ℤ)
    (hs : ∀ i x, table i x ≠ 0 → 0 ≤ ε * Holant.charge x) :
    ∀ v y, (r.realize hr table edges).vertex v y ≠ 0 →
      0 ≤ ε * Holant.charge y := by
  intro v y hy
  exact hs (r.signatureLabel hr v) y hy

include hmem in
theorem network_common_sign (h : OneSidedAlternative (preprocess Gamma))
    (r : Input (s := s) (arity := arity)) :
    ∃ ε : ℤ, ε ≠ 0 ∧
      ∀ v y, (network G r).vertex v y ≠ 0 → 0 ≤ ε * Holant.charge y := by
  obtain ⟨ε, he, hs⟩ := common_sign G Gamma hmem h
  exact ⟨ε, he, realize_common_sign r.val r.property (native G)
    KSourceTransport.nativeEdges ε hs⟩

include hmem in
/-- Charge conservation on the original incidences forces each original local
word in a nonzero term onto its central layer, before any graph preprocessing. -/
theorem supported_word_central (h : OneSidedAlternative (preprocess Gamma))
    (r : Input (s := s) (arity := arity))
    (z : (Fin (network G r).shape.edges × Bool) → Bool)
    (hnz : (network G r).assignmentTerm Fin.elim0 z ≠ 0)
    (v : Fin (network G r).shape.vertices) :
    2 * Holant.weight ((network G r).shape.assignment Fin.elim0 z v) =
      (network G r).shape.arity v := by
  obtain ⟨ε, he, hs⟩ := network_common_sign G Gamma hmem h r
  exact (Holant.charge_eq_zero_iff _).mp
    ((network G r).charge_eq_zero_of_common_side_term
      (native_edges G r) ε he hs Fin.elim0 z hnz v)

include hmem in
theorem term_central (h : OneSidedAlternative (preprocess Gamma))
    (r : Input (s := s) (arity := arity))
    (z : (Fin (network G r).shape.edges × Bool) → Bool) :
    (network G r).centralRestriction.assignmentTerm Fin.elim0 z =
      (network G r).assignmentTerm Fin.elim0 z := by
  obtain ⟨ε, he, hs⟩ := network_common_sign G Gamma hmem h r
  exact (network G r).assignmentTerm_centralRestriction_of_common_side
    (native_edges G r) ε he hs Fin.elim0 z

include hmem in
theorem central_value_exact (h : OneSidedAlternative (preprocess Gamma))
    (r : Input (s := s) (arity := arity)) :
    (OriginalFamily.value (central G) KSourceTransport.nativeEdges r : AlgebraicComplex) =
      (KSourceTransport.nativeValue G r : AlgebraicComplex) := by
  rw [OriginalFamily.value_exact, OriginalFamily.value_exact]
  obtain ⟨ε, he, hs⟩ := network_common_sign G Gamma hmem h r
  exact congrFun ((network G r).denote_centralRestriction_of_common_side
    (native_edges G r) ε he hs) Fin.elim0

/-- A dependent signature equality avoids silently permuting or recasting ports. -/
theorem target_signature (j : Fin (count G)) :
    (⟨targetArity G j.val, targetTable G j⟩ : AnySignature AlgebraicComplex) =
      ⟨arity (RootPreprocessing.includeLabel (central G) j).val,
        central G (RootPreprocessing.includeLabel (central G) j)⟩ := by
  exact (Sigma.eta (FactorSaturation.OriginalCodec.rootLookup
    (RootPreprocessing.signature (central G)) j.val)).trans
      (FactorSaturation.OriginalCodec.rootLookup_old
        (RootPreprocessing.signature (central G)) j)

theorem target_preprocessed : Preprocessed (Source.signatureSet (targetTable G)) := by
  rintro f ⟨j, rfl⟩
  exact (congrArg (fun f : AnySignature AlgebraicComplex => 0 < f.1 ∧ f.2 ≠ 0)
    (target_signature G j)).mpr (RootPreprocessing.included_kept (central G) j)

include hmem in
theorem target_subset : Source.signatureSet (targetTable G) ⊆
    centralFamily (kCoordinates (preprocess Gamma)) := by
  rintro f ⟨j, rfl⟩
  let i := RootPreprocessing.includeLabel (central G) j
  have hk : 0 < arity i.val ∧ central G i ≠ 0 :=
    RootPreprocessing.included_kept (central G) j
  have hm : (⟨arity i.val, central G i⟩ : AnySignature AlgebraicComplex) ∈
      centralFamily (kCoordinates (preprocess Gamma)) :=
    ⟨⟨arity i.val, native G i⟩,
      native_member G Gamma hmem i hk.1
        (native_nonzero_original G i (central_nonzero_native G i hk.2)), hk.2, rfl⟩
  exact (congrArg (fun f : AnySignature AlgebraicComplex =>
    f ∈ centralFamily (kCoordinates (preprocess Gamma))) (target_signature G j)).mpr hm

/-- Sole EO-family producer: no free Family, backend, LP machine or value
identity is an input. EOTract's SAME outer sign/class survive the subset proof. -/
def family (h : OneSidedAlternative (preprocess Gamma)) :
    Source.Family (count G) (targetArity G) where
  signatures := targetTable G
  preprocessed := target_preprocessed G
  tract := h.2.mono_family (target_subset G Gamma hmem)

end
end Holant.LocalDrafts.Tractability.EOEvaluation.OneSidedSource.Producer
