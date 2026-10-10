import Holant.Proofs.FiniteGroups.Stabilization.FrozenDeck
import Holant.OpenNetworkComposition.ProjectiveContraction


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.OpenNetworkComposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {L : Type*} [Field L] {m : ℕ}

theorem update_second_word (a b c : Bool) (x : Fin m → Bool) :
    Function.update (Fin.cons a (Fin.cons b x) : Fin (m+2) → Bool) (1 : Fin (m + 2)) c =
      (Fin.cons a (Fin.cons c x) : Fin (m+2) → Bool) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · refine Fin.cases ?_ (fun i => ?_) k
    · simp
    · have hi : i.succ.succ ≠ (1 : Fin (m + 2)) := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_succ, Fin.val_one] at hv
        omega
      simp [Function.update_of_ne hi]

/-- Exact finite-sum identity, including both native wires and the original
ordered binary orientation.  No analytic linear-combination resource is used. -/
theorem close_splice_table (q : Signature L (m + 2)) (B : Binary (K := L)) :
    Signature.contract Signature.disequality (spliceTensor q (binarySignature B) 1) =
      Signature.contract (X * B * X) q := by
  funext x
  have hxb : ∀ (a b : Bool), ((X * B * X : Matrix Bool Bool L)) a b = B (!a) (!b) := by
    intro a b
    cases a <;> cases b <;> simp [X, Matrix.mul_apply, Signature.disequality]
  simp [Signature.contract, hxb, spliceTensor, binarySignature, update_second_word,
    Signature.disequality]
  <;> ring

theorem rawCard_realizes_with_scale (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) (hf : Gadget.Realizes F .disequality f)
    (k : RawCardKey m (completeGroup F hτ)) (htwo : (2 : L) ≠ 0) :
    ∃ c : L, (c = 1 ∨ c = (2 : L)⁻¹) ∧ c ≠ 0 ∧
      Gadget.Realizes F .disequality (fun x => c * rawCard F hτ f k x) := by
  have hd := dress_actual F hτ f hf k.1
  have hr := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality _ hd k.2.1
  have hb := realizes_orientBinary (actualRepresentative_actual F hτ k.2.2.1).1 k.2.2.2
  have hs := realizes_splice F _ _ hr hb (1 : Fin (m + 2))
  obtain ⟨c, hc, hn, hactual⟩ := realizes_contract_with_scale F _ hs htwo
  refine ⟨c, hc, hn, ?_⟩
  simpa only [close_splice_table, rawCard] using hactual

theorem rawCard_realizesUpTo (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) (hf : Gadget.Realizes F .disequality f)
    (k : RawCardKey m (completeGroup F hτ)) (htwo : (2 : L) ≠ 0) :
    Gadget.RealizesUpTo F .disequality (rawCard F hτ f k) := by
  obtain ⟨c, _, hc, ha⟩ := rawCard_realizes_with_scale F hτ f hf k htwo
  exact ⟨c, hc, ha⟩

theorem canonicalKey_realizesUpTo {n : ℕ} (F : SignatureFamily L) (g : Signature L n)
    (hg : g ≠ 0) (ha : Gadget.RealizesUpTo F .disequality g) :
    Gadget.RealizesUpTo F .disequality (canonicalKey g) := by
  obtain ⟨d, hd, hactual⟩ := ha
  refine ⟨d * g (firstWord g hg), mul_ne_zero hd (firstWord_nonzero g hg), ?_⟩
  have he : (fun x => d * g x) =
      (fun x => (d * g (firstWord g hg)) * canonicalKey g x) := by
    funext x
    have hx := congrFun (recover_from_key g hg) x
    simp only [Pi.smul_apply, smul_eq_mul] at hx
    rw [hx]
    ring
  rwa [he] at hactual

theorem canonicalToken_realizesUpTo (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) (hf : Gadget.Realizes F .disequality f)
    (t : CanonicalToken F hτ f) (htwo : (2 : L) ≠ 0) :
    Gadget.RealizesUpTo F .disequality t.1 := by
  rw [← selectedRawCard_key F hτ f t]
  exact canonicalKey_realizesUpTo F _ (selectedRawCard_nonzero F hτ f t)
    (rawCard_realizesUpTo F hτ f hf (token_has_raw_card F hτ f t).choose htwo)

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
