import Holant.Proofs.FiniteGroups.Stabilization.FrozenDeck
import Holant.Proofs.FiniteGroups.Stabilization.MatchingRepresentatives


namespace Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
attribute [local instance] Classical.propDecidable
variable {L : Type*} [Field L]

abbrev NonzeroRawKey {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) :=
  {k : RawCardKey m (completeGroup F hτ) // rawCard F hτ f k ≠ 0}

abbrev FullDeckIndex {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) := completeGroup F hτ ⊕ NonzeroRawKey F hτ f

theorem actualRepresentative_signature_nonzero (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (q : completeGroup F hτ) : binarySignature (actualRepresentative F hτ q) ≠ 0 := by
  intro hz
  have hb : actualRepresentative F hτ q = 0 := by
    ext a b
    have h := congrFun hz ![a,b]
    change actualRepresentative F hτ q a b = 0 at h
    exact h
  exact (actualRepresentative_actual F hτ q).2 (by rw [hb, Matrix.det_zero])

def fullDeckRoot {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) : FullDeckIndex F hτ f → TreeOccurrence L
  | .inl q => ⟨⟨2, binarySignature (actualRepresentative F hτ q)⟩,
      (exists_factorTree _ (actualRepresentative_signature_nonzero F hτ q)).some⟩
  | .inr k => ⟨⟨m, rawCard F hτ f k.1⟩, (exists_factorTree _ k.2).some⟩

def fullDeckUniverse [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) : Finset (FullDeckIndex F hτ f) := by
  letI := completeGroup_finite F hτ
  letI := Fintype.ofFinite (FullDeckIndex F hτ f)
  exact Finset.univ

@[simp] theorem mem_fullDeckUniverse [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) (i : FullDeckIndex F hτ f) :
    i ∈ fullDeckUniverse F hτ f := by simp [fullDeckUniverse]

def fullRetainedDeck [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) : SignatureFamily L :=
  retainBatch F (fullDeckUniverse F hτ f) (fullDeckRoot F hτ f)

theorem fullRetainedDeck_retains [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) : F ⊆ fullRetainedDeck F hτ f :=
  retainBatch_retains F _ _

theorem fullRetainedDeck_finite [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hF : F.Finite) (hτ : ResidualTorsion F) (f : Signature L (m + 2)) :
    (fullRetainedDeck F hτ f).Finite := retainBatch_finite hF _ _

theorem fullRetainedDeck_saturated [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hF : FactorSaturated F) (hτ : ResidualTorsion F) (f : Signature L (m + 2)) :
    FactorSaturated (fullRetainedDeck F hτ f) := retainBatch_saturated hF _ _

theorem fullRetainedDeck_representative [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) (q : completeGroup F hτ) :
    (⟨2, binarySignature (actualRepresentative F hτ q)⟩ : AnySignature L) ∈ fullRetainedDeck F hτ f :=
  retainBatch_root F _ _ (mem_fullDeckUniverse F hτ f (.inl q))

theorem fullRetainedDeck_card [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) (k : RawCardKey m (completeGroup F hτ))
    (hk : rawCard F hτ f k ≠ 0) :
    (⟨m, rawCard F hτ f k⟩ : AnySignature L) ∈ fullRetainedDeck F hτ f :=
  retainBatch_root F _ _ (mem_fullDeckUniverse F hτ f (.inr ⟨k, hk⟩))

theorem fullRetainedDeck_leaf [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) (i : FullDeckIndex F hτ f)
    (a : AnySignature L) (ha : a ∈ (fullDeckRoot F hτ f i).2.leaves) :
    a ∈ fullRetainedDeck F hτ f :=
  retainBatch_leaf F _ _ (mem_fullDeckUniverse F hτ f i) ha

/-- Once the complete group is unchanged, the old frozen representatives
remain actual and cover every actual binary in the retained successor.
Thus the entire previously generated deck is still a complete choice of
the source deck, without re-choosing representatives mid-stratum. -/
theorem frozen_representatives_cover_retained {F G : SignatureFamily L}
    (hFG : F ⊆ G) (hF : ResidualTorsion F) (hG : ResidualTorsion G)
    (he : completeGroup G hG = completeGroup F hF) :
    (∀ q : completeGroup F hF, ActualNonsingular G (actualRepresentative F hF q)) ∧
      ∀ B, ActualNonsingular G B →
        ∃ q : completeGroup F hF, ∃ c : L, c ≠ 0 ∧ B = c • actualRepresentative F hF q := by
  refine ⟨fun q => ⟨(actualRepresentative_actual F hF q).1.mono hFG,
    (actualRepresentative_actual F hF q).2⟩, ?_⟩
  intro B hB
  obtain ⟨q, hq⟩ := actualRepresentative_covers G hG hB
  let r : completeGroup F hF := ⟨q.1, he ▸ q.2⟩
  have hc : projectiveClass (transfer B) = projectiveClass (transfer (actualRepresentative F hF r)) :=
    hq.symm.trans ((actualRepresentative_class G hG q).trans (actualRepresentative_class F hF r).symm)
  obtain ⟨c, hn, ht⟩ := projectiveClass_eq_iff.mp hc
  refine ⟨r, c, hn, ?_⟩
  have hh := congrArg (fun M : Binary (K := L) => M * X) ht
  simpa only [transfer, Matrix.smul_mul, Matrix.mul_assoc, X_mul_X, Matrix.mul_one] using hh

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
