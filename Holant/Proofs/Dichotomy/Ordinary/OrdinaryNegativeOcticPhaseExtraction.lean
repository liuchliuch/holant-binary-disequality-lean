import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeOcticPhaseCore
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicCore

/-! Exhaustive octic phase split. A trivial residual retains its actual
unary/pair factorization. A nonconstant residual supplies a literal ternary
monomial, and one, two, or four positive copies turn its phase into the cubic
sign. No tractability or hardness conclusion is attached to the trivial case. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticPhaseExtraction
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace C
export OrdinaryNegativeOcticPhaseCore
  (lowOrder residual residual_small residual_eight factorization_of_residual_one
    ports ports_value occurrences_ports_compose eight_dvd_occurrences_ports_compose)
end C
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle
  (evaluate evaluate_flatten evaluate_scale evaluate_compose)
end B
namespace M
export GeneralEOPairedFamilyExtractionPhaseMinor
  (exists_minimal ports substituted_full substituted_proper support word_support)
end M
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose)
end I
namespace O
export GeneralEOPairedFamilyExtractionPhaseOccurrences (occurrences occurrences_flatten)
end O
namespace A
export AffinePhase (origin word)
end A
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
open OrdinaryNegativeCubicCore (cubic)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def normalized (f : Signature AlgebraicComplex n) : Signature AlgebraicComplex n :=
  fun x => (f (A.origin n))⁻¹*f x

theorem normalized_origin (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0) :
    normalized f (A.origin n)=1 := inv_mul_cancel₀ (hf _)

theorem normalized_eight (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0)
    (height : ∀x,f x^8=f (A.origin n)^8) (x : Fin n → Bool) : normalized f x^8=1 := by
  rw [normalized,mul_pow,inv_pow,height x,inv_mul_cancel₀ (pow_ne_zero 8 (hf _))]

theorem denormalize (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0) :
    f=(fun x => f (A.origin n)*normalized f x) := by
  funext x
  simp only [normalized,←mul_assoc,mul_inv_cancel₀ (hf _),one_mul]

/-- Minimal cardinality extracts a literal ternary monomial without any
fourth-root assumption. Here the resulting phase is an actual eighth root. -/
theorem minimal_ternary (g : Signature AlgebraicComplex n)
    (hsmall : ∀s : Finset (Fin n),s.card≤2 → g (A.word s)=1)
    (hbad : ∃x,g x≠1) (height : ∀x,g x^8=1) :
    ∃p : Fin n → Bool ⊕ Fin 3,∃δ : AlgebraicComplex,
      δ^8=1 ∧ δ≠1 ∧ ∀z : Fin 3 → Bool,
        g (T.substitute p z)=if z=![true,true,true] then δ else 1 := by
  obtain ⟨s,hs,hmin⟩ := M.exists_minimal g hbad
  have hcard : 2<s.card := by
    by_contra hn
    exact hs (hsmall s (by omega))
  obtain ⟨i,j,k,hi,hj,hk,hij,hik,hjk⟩ := Finset.two_lt_card_iff.mp hcard
  refine ⟨M.ports s i j,g (A.word s),height _,hs,?_⟩
  intro z
  by_cases hz : z=![true,true,true]
  · rw [ite_eq_left hz,hz,M.substituted_full]
  · rw [ite_eq_right hz,←M.word_support (T.substitute (M.ports s i j) z)]
    exact hmin _ (Finset.card_lt_card (M.substituted_proper s i j k hi hj hk hij hik hjk z hz))

def basePorts (p : Fin n → Bool ⊕ Fin 3) : List (Fin n → Bool ⊕ Fin 3) :=
  C.ports.map (fun q => I.compose q p)

def repeatedPorts (p : Fin n → Bool ⊕ Fin 3) (k : ℕ) : List (Fin n → Bool ⊕ Fin 3) :=
  (List.replicate k (basePorts p)).flatten

def scale (f : Signature AlgebraicComplex n) {m : ℕ}
    (ps : List (Fin n → Bool ⊕ Fin m)) : AlgebraicComplex := f (A.origin n)^ps.length

/-- Exact structural split with the internally selected eighth-root phase
and original nonzero scalar. The left side makes only a factorization claim. -/
theorem phase_split (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0)
    (height : ∀x,f x^8=f (A.origin n)^8) :
    ((∀x,C.residual (normalized f) x=1) ∧
      ∀x,f x=f (A.origin n)*C.lowOrder (normalized f) x) ∨
    (∃p : Fin n → Bool ⊕ Fin 3,∃δ : AlgebraicComplex,
      δ^8=1 ∧ δ≠1 ∧ scale f (basePorts p)≠0 ∧
      ∀z : Fin 3 → Bool,B.evaluate f (basePorts p) z=
        scale f (basePorts p)*(if z=![true,true,true] then δ else 1)) := by
  have hg := normalized_eight f hf height
  by_cases hres : ∀x,C.residual (normalized f) x=1
  · left
    refine ⟨hres,?_⟩
    intro x
    have hv := C.factorization_of_residual_one (normalized f) hg hres x
    calc
      f x=f (A.origin n)*normalized f x := congrFun (denormalize f hf) x
      _=f (A.origin n)*C.lowOrder (normalized f) x := by rw [hv]
  · right
    obtain ⟨p,δ,hδ,hne,he⟩ := minimal_ternary (C.residual (normalized f))
      (C.residual_small (normalized f) (normalized_origin f hf) hg)
      (not_forall.mp hres) (C.residual_eight (normalized f) hg)
    refine ⟨p,δ,hδ,hne,pow_ne_zero _ (hf _),?_⟩
    intro z
    have hv : B.evaluate (normalized f) (basePorts p) z=
        if z=![true,true,true] then δ else 1 := by
      rw [basePorts,B.evaluate_compose,C.ports_value _ (normalized_origin f hf) hg,he]
    have hs := B.evaluate_scale (normalized f) (f (A.origin n)) (basePorts p) z
    rw [←denormalize f hf,hv] at hs
    exact hs

/-- Successive squaring selects a bounded positive exponent, retaining the
nontrivial phase rather than assuming its multiplicative order. -/
theorem eighth_root_negative_power (δ : AlgebraicComplex) (hδ : δ^8=1) (hne : δ≠1) :
    ∃k : ℕ,(k=1 ∨ k=2 ∨ k=4) ∧ δ^k = -1 := by
  have hfour : (δ^4)^2=1 := by
    calc
      _=δ^8 := by ring
      _=1 := hδ
  rcases sq_eq_one_iff.mp hfour with hf|hf
  · have htwo : (δ^2)^2=1 := by
      calc
        _=δ^4 := by ring
        _=1 := hf
    rcases sq_eq_one_iff.mp htwo with ht|ht
    · exact ⟨1,Or.inl rfl,by simpa using (sq_eq_one_iff.mp ht).resolve_left hne⟩
    · exact ⟨2,Or.inr (Or.inl rfl),ht⟩
  · exact ⟨4,Or.inr (Or.inr rfl),hf⟩

theorem repeatedPorts_length (p : Fin n → Bool ⊕ Fin 3) (k : ℕ) :
    (repeatedPorts p k).length=k*(basePorts p).length := by
  simp [repeatedPorts,List.length_flatten]

theorem evaluate_repeated (f : Signature AlgebraicComplex n)
    (p : Fin n → Bool ⊕ Fin 3) (k : ℕ) (z : Fin 3 → Bool) :
    B.evaluate f (repeatedPorts p k) z=B.evaluate f (basePorts p) z^k := by
  rw [repeatedPorts,B.evaluate_flatten]
  simp

theorem scale_repeated (f : Signature AlgebraicComplex n)
    (p : Fin n → Bool ⊕ Fin 3) (k : ℕ) :
    scale f (basePorts p)^k=scale f (repeatedPorts p k) := by
  rw [scale,scale,repeatedPorts_length,←pow_mul,Nat.mul_comm]

theorem occurrences_repeated (p : Fin n → Bool ⊕ Fin 3) (k : ℕ) (j : Fin 3) :
    O.occurrences (repeatedPorts p k) j=k*O.occurrences (basePorts p) j := by
  rw [repeatedPorts,O.occurrences_flatten]
  simp

theorem eight_dvd_occurrences_repeated (p : Fin n → Bool ⊕ Fin 3) (k : ℕ) (j : Fin 3) :
    8 ∣ O.occurrences (repeatedPorts p k) j := by
  rw [occurrences_repeated]
  exact dvd_mul_of_dvd_right (C.eight_dvd_occurrences_ports_compose p j) k

theorem even_occurrences_repeated (p : Fin n → Bool ⊕ Fin 3) (k : ℕ) (j : Fin 3) :
    Even (O.occurrences (repeatedPorts p k) j) := by
  rw [even_iff_two_dvd]
  exact dvd_trans (by decide : 2 ∣ 8) (eight_dvd_occurrences_repeated p k j)

theorem cubic_eq_ite (z : Fin 3 → Bool) :
    cubic (K := AlgebraicComplex) z=if z=![true,true,true] then -1 else 1 := by
  have hz : z=![true,true,true] ↔ (z 0 && z 1 && z 2)=true := by
    constructor
    · intro h; simp [h]
    · intro h
      simp only [Bool.and_eq_true] at h
      funext i
      fin_cases i <;> simp [h.1.1,h.1.2,h.2]
  simp only [cubic,hz]

/-- Exhaustive octic structural endpoint. The nonconstant branch supplies
an actual positive cubic bundle with even raw occurrences and its exact
nonzero original scale. The trivial branch is left as unary/pair structure. -/
theorem cubic_split (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0)
    (height : ∀x,f x^8=f (A.origin n)^8) :
    ((∀x,C.residual (normalized f) x=1) ∧
      ∀x,f x=f (A.origin n)*C.lowOrder (normalized f) x) ∨
    (∃p : Fin n → Bool ⊕ Fin 3,∃k : ℕ,(k=1 ∨ k=2 ∨ k=4) ∧
      scale f (repeatedPorts p k)≠0 ∧
      (∀z : Fin 3 → Bool,B.evaluate f (repeatedPorts p k) z=
        scale f (repeatedPorts p k)*cubic z) ∧
      ∀j : Fin 3,Even (O.occurrences (repeatedPorts p k) j)) := by
  rcases phase_split f hf height with h|⟨p,δ,hδ,hne,_,hv⟩
  · exact Or.inl h
  · right
    obtain ⟨k,hk,hnegative⟩ := eighth_root_negative_power δ hδ hne
    refine ⟨p,k,hk,pow_ne_zero _ (hf _),?_,even_occurrences_repeated p k⟩
    intro z
    rw [evaluate_repeated,hv,mul_pow,scale_repeated,cubic_eq_ite]
    by_cases hz : z=![true,true,true]
    · simp [hz,hnegative]
    · simp [hz]

/-- Direct consumer form when the actual normalized residual is nonconstant. -/
theorem cubic_of_nonconstant_residual (f : Signature AlgebraicComplex n) (hf : ∀x,f x≠0)
    (height : ∀x,f x^8=f (A.origin n)^8)
    (hbad : ∃x,C.residual (normalized f) x≠1) :
    ∃ps : List (Fin n → Bool ⊕ Fin 3),∃c : AlgebraicComplex,
      c≠0 ∧ (∀z : Fin 3 → Bool,B.evaluate f ps z=c*cubic z) ∧
      ∀j : Fin 3,Even (O.occurrences ps j) := by
  rcases cubic_split f hf height with ⟨h,_⟩|⟨p,k,_,hc,hv,he⟩
  · obtain ⟨x,hx⟩ := hbad
    exact False.elim (hx (h x))
  · exact ⟨repeatedPorts p k,scale f (repeatedPorts p k),hc,hv,he⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticPhaseExtraction
end
