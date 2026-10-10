import Holant.Platonic.RankDeficientLocalization.Normalization.SourceWithoutIdentity
import Holant.Algebraic.OpenNetwork

/-! The displayed Λ,h middle family is an actual finite indexed family.
Every old signature is unchanged; the new entry is the literal original h. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Algebraic
open Holant.Platonic.RainbowLocalization.Physical
open Holant.OpenNetworkComposition.FactorFreeNormalization
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s n : ℕ} {arity : ℕ → ℕ}

def adjoinedArity (arity : ℕ → ℕ) (n : ℕ) : ℕ → ℕ := fun i => Nat.casesOn i n arity

def adjoinedSignatures (signatures : (i : Fin s) → Signature ℂ (arity i.val)) (h : Signature ℂ n) :
    (i : Fin (s+1)) → Signature ℂ (adjoinedArity arity n i.val) :=
  Fin.cases h signatures

theorem adjoined_family_exact (signatures : (i : Fin s) → Signature ℂ (arity i.val))
    (h : Signature ℂ n) :
    indexedRetainedFamily (adjoinedArity arity n) (adjoinedSignatures signatures h)=
      indexedRetainedFamily arity signatures ∪ {(⟨n,h⟩ : AnySignature ℂ)} := by
  ext t
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inr rfl
    · exact Or.inl ⟨j,rfl⟩
  · rintro (⟨i,rfl⟩|ht)
    · exact ⟨i.succ,rfl⟩
    · have he : t=(⟨n,h⟩ : AnySignature ℂ) := ht
      subst t
      exact ⟨0,rfl⟩

theorem adjoined_family_inclusion (signatures : (i : Fin s) → Signature ℂ (arity i.val))
    (h : Signature ℂ n) : indexedRetainedFamily arity signatures ⊆
      indexedRetainedFamily (adjoinedArity arity n) (adjoinedSignatures signatures h) := by
  rintro t ⟨i,rfl⟩
  exact ⟨i.succ,rfl⟩

theorem realized_signature_algebraic (signatures : (i : Fin s) → Signature ℂ (arity i.val))
    (halg : ∀i x,IsAlgebraic ℚ (signatures i x)) (h : Signature ℂ n)
    (hh : Gadget.Realizes (indexedRetainedFamily arity signatures) .disequality h) :
    ∀x,IsAlgebraic ℚ (h x) := by
  intro x
  apply realized_algebraic _ hh x
  rintro t ⟨i,rfl⟩ y
  exact halg i y

theorem adjoined_algebraic (signatures : (i : Fin s) → Signature ℂ (arity i.val))
    (halg : ∀i x,IsAlgebraic ℚ (signatures i x)) (h : Signature ℂ n)
    (hh : Gadget.Realizes (indexedRetainedFamily arity signatures) .disequality h) :
    ∀i x,IsAlgebraic ℚ (adjoinedSignatures signatures h i x) := by
  intro i
  refine Fin.cases ?_ (fun j => halg j) i
  exact realized_signature_algebraic signatures halg h hh

theorem realized_adjoined_access {m : ℕ} (signatures : (i : Fin s) → Signature ℂ (arity i.val))
    (halg : ∀i x,IsAlgebraic ℚ (signatures i x)) (h : Signature ℂ n)
    (hh : Gadget.Realizes (indexedRetainedFamily arity signatures) .disequality h)
    (q : Signature ℂ m) (hqalg : ∀x,IsAlgebraic ℚ (q x)) (p : Fin m → Bool) (hp : q p≠0)
    (hq : Gadget.RealizesUpTo (indexedRetainedFamily arity signatures) .disequality q)
    (hf : NoXFactor q) :
    EncodedProjectiveNativeAdjoin (adjoinedSignatures signatures h) (adjoined_algebraic signatures halg h hh) q := by
  have hq' : Gadget.RealizesUpTo
      (indexedRetainedFamily (adjoinedArity arity n) (adjoinedSignatures signatures h)) .disequality q := by
    obtain ⟨c,hc,hreal⟩ := hq
    exact ⟨c,hc,hreal.mono (adjoined_family_inclusion signatures h)⟩
  exact projectively_realized_encoded_without_identity (adjoinedSignatures signatures h)
    (adjoined_algebraic signatures halg h hh) q hqalg p hp hq' hf

end
end Holant.Platonic.RankDeficientLocalization.Normalization
