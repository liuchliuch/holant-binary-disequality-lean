import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionInteraction

/-! A nonconstant phase residual trivial through Hamming weight two has a
literal ternary monomial minor. The support and its three nonempty groups are
chosen internally by minimal cardinality; only identifications and false
constants are used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseMinor
open Holant Holant.Tractable
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace A
export AffinePhase (word)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def support (x : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => x i=true)

theorem word_support (x : Fin n → Bool) : A.word (support x)=x := by
  funext i
  cases h : x i <;> simp [A.word,support,h]

variable (g : Signature AlgebraicComplex n)

/-- Well-ordering chooses an actual residual support, not a supplied phase
obstruction or a promised successful extraction. -/
theorem exists_minimal (hg : ∃x,g x≠1) :
    ∃s : Finset (Fin n),g (A.word s)≠1 ∧
      ∀t : Finset (Fin n),t.card<s.card → g (A.word t)=1 := by
  have he : ∃k : ℕ,∃s : Finset (Fin n),s.card=k ∧ g (A.word s)≠1 := by
    obtain ⟨x,hx⟩ := hg
    exact ⟨(support x).card,support x,rfl,by simpa only [word_support] using hx⟩
  obtain ⟨s,hs,hg⟩ := Nat.find_spec he
  refine ⟨s,hg,?_⟩
  intro t ht
  by_contra hn
  exact Nat.find_min he (hs ▸ ht) ⟨t,rfl,hn⟩

def ports (s : Finset (Fin n)) (i j : Fin n) : Fin n → Bool ⊕ Fin 3 := fun k =>
  if k∈s then if k=i then Sum.inr 0 else if k=j then Sum.inr 1 else Sum.inr 2
  else Sum.inl false

theorem substituted_subset (s : Finset (Fin n)) (i j : Fin n) (z : Fin 3 → Bool) :
    support (T.substitute (ports s i j) z)⊆s := by
  intro k hk
  have h := (Finset.mem_filter.mp hk).2
  by_contra hs
  simp [T.substitute,ports,hs] at h

theorem substituted_full (s : Finset (Fin n)) (i j : Fin n) :
    T.substitute (ports s i j) ![true,true,true]=A.word s := by
  funext k
  by_cases h : k∈s
  · simp only [T.substitute,ports,h,ite_true,A.word,decide_true]
    split_ifs <;> rfl
  · simp [T.substitute,ports,A.word,h]

theorem substituted_proper (s : Finset (Fin n)) (i j k : Fin n)
    (hi : i∈s) (hj : j∈s) (hk : k∈s) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (z : Fin 3 → Bool) (hz : z≠![true,true,true]) :
    support (T.substitute (ports s i j) z)⊂s := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨substituted_subset s i j z,?_⟩
  intro he
  have h0 : z 0=true := by
    have h := (Finset.mem_filter.mp (he ▸ hi)).2
    simpa [T.substitute,ports,hi] using h
  have h1 : z 1=true := by
    have h := (Finset.mem_filter.mp (he ▸ hj)).2
    simpa [T.substitute,ports,hj,Ne.symm hij] using h
  have h2 : z 2=true := by
    have h := (Finset.mem_filter.mp (he ▸ hk)).2
    simpa [T.substitute,ports,hk,Ne.symm hik,Ne.symm hjk] using h
  apply hz
  funext a
  fin_cases a <;> assumption

/-- Three groups isolate exactly one nontrivial fourth-root monomial. -/
theorem exists_ternary_monomial (hsmall : ∀s : Finset (Fin n),s.card≤2 → g (A.word s)=1)
    (hg : ∃x,g x≠1) (hfour : ∀x,g x^4=1) :
    ∃p : Fin n → Bool ⊕ Fin 3,∃δ : AlgebraicComplex,δ^4=1 ∧ δ≠1 ∧
      ∀z : Fin 3 → Bool,g (T.substitute p z)=if z=![true,true,true] then δ else 1 := by
  obtain ⟨s,hbad,hmin⟩ := exists_minimal g hg
  have hs : 2<s.card := by
    by_contra hn
    exact hbad (hsmall s (by omega))
  obtain ⟨i,j,k,hi,hj,hk,hij,hik,hjk⟩ := Finset.two_lt_card_iff.mp hs
  refine ⟨ports s i j,g (A.word s),hfour _,hbad,?_⟩
  intro z
  by_cases hz : z=![true,true,true]
  · rw [ite_eq_left hz,hz,substituted_full]
  · rw [ite_eq_right hz,←word_support (T.substitute (ports s i j) z)]
    exact hmin _ (Finset.card_lt_card (substituted_proper s i j k hi hj hk hij hik hjk z hz))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseMinor
