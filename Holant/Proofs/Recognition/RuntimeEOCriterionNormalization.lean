import Holant.Tractable.Criteria

/-! Logical normalization used by the runtime EO classifier. Central-domain,
triple and literal A/P pairing conditions may range over every original label:
zero/nullary labels satisfy them automatically. Nonzero central support forces
even arity, so a separate odd-arity failure channel is unnecessary. All source
conditions are retained exactly; this module supplies no decision oracle. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOCriterionNormalization
open Holant Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} (arity : Fin s → ℕ) (G : (i : Fin s) → Signature AlgebraicComplex (arity i))
def family : SignatureFamily AlgebraicComplex := Set.range (fun i => (⟨arity i,G i⟩ : AnySignature AlgebraicComplex))
def Domain : Prop := ∀i,Signature.CentralSupport (G i)
def Triples (sign : EOSign) : Prop := ∀i a b c,G i a≠0 → G i b≠0 → G i c≠0 →
  G i (tripleXor a b c)≠0 ∨ 0<sign.value*Holant.charge (tripleXor a b c)
def Classes (C : EOClass) : Prop := ∀i,∀p : OrientedPerfectPairing (arity i),C.Holds (p.restrict (G i))

theorem central_eo {n : ℕ} (f : Signature AlgebraicComplex n) (hne : f≠0)
    (h : Signature.CentralSupport f) : IsEO (⟨n,f⟩ : AnySignature AlgebraicComplex) := by
  have hex : ∃x,f x≠0 := by
    by_contra hn
    push_neg at hn
    exact hne (funext hn)
  obtain ⟨x,hx⟩ := hex
  have hn : n=2*Holant.weight x := by
    by_contra he
    exact hx (h x (Ne.symm he))
  exact ⟨⟨Holant.weight x,hn⟩,h⟩

theorem class_constant (C : EOClass) (n : ℕ) (c : AlgebraicComplex) :
    C.Holds (fun _ : Fin n → Bool => c) := by
  cases C
  · exact affine_constant n c
  · exact product_constant n c

theorem nullary_word {n : ℕ} (hn : n=0) (x y : Fin n → Bool) : x=y := by
  funext j
  exact (Nat.not_lt_zero j.val (by simpa only [hn] using j.isLt)).elim

theorem criterion_iff : EOTract (preprocess (family arity G)) ↔
    Domain arity G ∧ ∃sign : EOSign,∃C : EOClass,Triples arity G sign ∧ Classes arity G C := by
  constructor
  · rintro ⟨_,hd,sign,C,ht,hc⟩
    have kept (i : Fin s) (ha : 0<arity i) (hn : G i≠0) :
        (⟨arity i,G i⟩ : AnySignature AlgebraicComplex)∈preprocess (family arity G) :=
      ⟨⟨i,rfl⟩,ha,hn⟩
    constructor
    · intro i
      by_cases hn : G i=0
      · intro x hx
        rw [hn]
        rfl
      · by_cases ha : 0<arity i
        · exact (hd _ (kept i ha hn)).2
        · have hz : arity i=0 := by omega
          intro x hx
          have he : Holant.weight x=0 := by simp [Holant.weight,hz]
          exact (hx (by omega)).elim
    · refine ⟨sign,C,?_,?_⟩
      · intro i a b c ha hb hc'
        have hn : G i≠0 := fun hz => ha (by rw [hz]; rfl)
        by_cases hi : 0<arity i
        · exact ht _ (kept i hi hn) a b c ha hb hc'
        · have hz : arity i=0 := by omega
          left
          rw [←nullary_word hz a (tripleXor a b c)]
          exact ha
      · intro i p
        by_cases hn : G i=0
        · have he : p.restrict (G i)=(fun _ => (0 : AlgebraicComplex)) := by
            funext x
            simp only [OrientedPerfectPairing.restrict,hn,Pi.zero_apply]
          rw [he]
          exact class_constant C p.count 0
        · by_cases hi : 0<arity i
          · exact hc _ (kept i hi hn) p
          · have hz : arity i=0 := by omega
            have he : p.restrict (G i)=(fun _ => G i (fun _ => false)) := by
              funext x
              exact congrArg (G i) (nullary_word hz _ _)
            rw [he]
            exact class_constant C p.count _
  · rintro ⟨hd,sign,C,ht,hc⟩
    refine ⟨(Set.finite_range (fun i => (⟨arity i,G i⟩ : AnySignature AlgebraicComplex))).subset
      (fun _ h => h.1),?_,sign,C,?_,?_⟩
    · rintro _ ⟨⟨i,rfl⟩,_,hn⟩
      exact central_eo (G i) hn (hd i)
    · rintro _ ⟨⟨i,rfl⟩,_,_⟩
      exact ht i
    · rintro _ ⟨⟨i,rfl⟩,_,_⟩
      exact hc i

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOCriterionNormalization
