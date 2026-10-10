import Holant.Proofs.FiniteGroups.Stabilization.RawRealization
import Holant.Proofs.FiniteGroups.Stabilization.FullRetainedDeck
import Holant.OpenNetworkComposition.OrdinaryNormalization.Reduction
import Holant.OpenNetworkComposition.DisjointTensor
import Holant.NetworkContraction
import Holant.NetworkAsGadget


namespace Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.OpenNetworkComposition
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {L : Type*} [Field L] {n m : ℕ}

abbrev RetainsIdentity (F : SignatureFamily L) : Prop :=
  (⟨2, OrdinaryNormalization.identitySignature (K := L)⟩ : AnySignature L) ∈ F

/-- Ordinary normalization preserves every scalar and every disconnected
component; the final native edge is added to two distinct port occurrences. -/
theorem realizes_contract_exact_of_identity (F : SignatureFamily L)
    (hI : RetainsIdentity F) (q : Signature L (n + 2))
    (hq : Gadget.Realizes F .disequality q) :
    Gadget.Realizes F .disequality (Signature.contract Signature.disequality q) := by
  obtain ⟨N, hv, he, hN⟩ := OrdinaryNormalization.realizes_exists_ordinary hI hq
  have hc := Gadget.realizes_network (N.contract Signature.disequality) F .disequality
    hv (by
      intro e
      refine Fin.cases ?_ (fun i => ?_) e
      · rfl
      · exact he i)
  rwa [Network.denote_contract, hN] at hc

/-- The closed scalar is physically realized over F, consuming its literal I
through ordinary normalization of the native X edge box. -/
theorem realizes_scalar_two (F : SignatureFamily L) (hI : RetainsIdentity F) :
    Gadget.Realizes F .disequality (fun _ : Fin 0 → Bool => (2 : L)) := by
  have hh := realizes_contract_exact_of_identity F hI
    (binarySignature (X : Binary (K := L))) (nativeX_actual F).1
  have hv : Signature.contract Signature.disequality
      (binarySignature (X : Binary (K := L))) = (fun _ : Fin 0 → Bool => (2 : L)) := by
    funext x
    norm_num [Signature.contract, Signature.disequality, binarySignature, X]
  rwa [hv] at hh

theorem realizes_twice (F : SignatureFamily L) (hI : RetainsIdentity F)
    (q : Signature L n) (hq : Gadget.Realizes F .disequality q) :
    Gadget.Realizes F .disequality (fun x => (2 : L) * q x) := by
  have hh := realizes_tensor F .disequality q (fun _ : Fin 0 → Bool => (2 : L))
    hq (realizes_scalar_two F hI)
  have hv : Signature.tensor q (fun _ : Fin 0 → Bool => (2 : L)) =
      (fun x => (2 : L) * q x) := by
    funext x
    simp [Signature.tensor_apply, mul_comm]
  rwa [hv] at hh

/-- Actual scalar compensation, not division of a gadget label. -/
theorem realizes_remove_half (F : SignatureFamily L) (hI : RetainsIdentity F)
    (htwo : (2 : L) ≠ 0) (q : Signature L n) (c : L)
    (hc : c = 1 ∨ c = (2 : L)⁻¹)
    (hq : Gadget.Realizes F .disequality (fun x => c * q x)) :
    Gadget.Realizes F .disequality q := by
  rcases hc with rfl | rfl
  · simpa only [one_mul] using hq
  · have hh := realizes_twice F hI _ hq
    simpa only [← mul_assoc, mul_inv_cancel₀ htwo, one_mul] using hh

theorem rawCard_realizes_exact (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hI : RetainsIdentity F) (htwo : (2 : L) ≠ 0)
    (f : Signature L (m + 2)) (hf : Gadget.Realizes F .disequality f)
    (k : RawCardKey m (completeGroup F hτ)) :
    Gadget.Realizes F .disequality (rawCard F hτ f k) := by
  obtain ⟨c, hc, _, hr⟩ := rawCard_realizes_with_scale F hτ f hf k htwo
  exact realizes_remove_half F hI htwo _ c hc hr

/-- Concrete ordinary graph for every raw key, including zero cards and
different scalar representatives of the same canonical key. -/
theorem rawCard_ordinary (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hI : RetainsIdentity F) (htwo : (2 : L) ≠ 0)
    (f : Signature L (m + 2)) (hf : Gadget.Realizes F .disequality f)
    (k : RawCardKey m (completeGroup F hτ)) :
    ∃ N : Network L m,
      (∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature L) ∈ F) ∧
      (∀ e, N.edge e = Signature.disequality) ∧ N.denote = rawCard F hτ f k :=
  OrdinaryNormalization.realizes_exists_ordinary hI
    (rawCard_realizes_exact F hτ hI htwo f hf k)

theorem fullDeckRoot_realizes (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hI : RetainsIdentity F) (htwo : (2 : L) ≠ 0)
    (f : Signature L (m + 2)) (hf : Gadget.Realizes F .disequality f)
    (i : FullDeckIndex F hτ f) :
    Gadget.Realizes F .disequality (fullDeckRoot F hτ f i).1.2 := by
  cases i with
  | inl q => exact (actualRepresentative_actual F hτ q).1
  | inr k => exact rawCard_realizes_exact F hτ hI htwo f hf k.1

/-- The exact selected raw graph and the normalization pivot are exposed
together. No assertion that the canonical table itself is a direct gadget. -/
theorem canonicalToken_ordinary_with_pivot (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (hI : RetainsIdentity F) (htwo : (2 : L) ≠ 0)
    (f : Signature L (m + 2)) (hf : Gadget.Realizes F .disequality f)
    (t : CanonicalToken F hτ f) :
    ∃ p : Fin m → Bool, selectedRawCard F hτ f t p ≠ 0 ∧
      ∃ N : Network L m,
        (∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature L) ∈ F) ∧
        (∀ e, N.edge e = Signature.disequality) ∧
        N.denote = selectedRawCard F hτ f t ∧
        N.denote = fun x => selectedRawCard F hτ f t p * t.1 x := by
  let g := selectedRawCard F hτ f t
  have hg : g ≠ 0 := selectedRawCard_nonzero F hτ f t
  obtain ⟨N, hv, he, hN⟩ := rawCard_ordinary F hτ hI htwo f hf
    (token_has_raw_card F hτ f t).choose
  refine ⟨firstWord g hg, firstWord_nonzero g hg, N, hv, he, hN, ?_⟩
  calc
    N.denote = g := hN
    _ = fun x => g (firstWord g hg) * t.1 x := by
      exact (recover_from_key g hg).trans
        (congrArg (fun z => g (firstWord g hg) • z) (selectedRawCard_key F hτ f t))

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
