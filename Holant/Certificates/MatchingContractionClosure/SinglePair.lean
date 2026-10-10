import Holant.Certificates.MatchingContractionClosure.Presentation

namespace Holant.Certificates.MatchingContractionClosure
open Holant
noncomputable section
variable {P E : Type*} [DecidableEq P] [DecidableEq E]

def sameMask (p : (E × Bool) ≃ P) (u : P) (d : E) : Bool :=
  if d=(p.symm u).1 then (p.symm u).2 else false
def crossMask (p : (E × Bool) ≃ P) (u v : P) (d : E) : Bool :=
  if d=(p.symm u).1 then !(p.symm u).2 else
    if d=(p.symm v).1 then (p.symm v).2 else false

theorem same_selected_ports (p : (E × Bool) ≃ P) (u v : P) (huv : u≠v)
    (he : (p.symm u).1=(p.symm v).1) :
    ((flipSlots (sameMask p u)).trans p) ((p.symm u).1,false)=u ∧
    ((flipSlots (sameMask p u)).trans p) ((p.symm u).1,true)=v := by
  have hb : (p.symm u).2 ≠ (p.symm v).2 := by
    intro hh
    exact huv (p.symm.injective (Prod.ext he hh))
  have hb' : (!(p.symm u).2)=(p.symm v).2 := by
    cases h₁ : (p.symm u).2 <;> cases h₂ : (p.symm v).2 <;> simp_all
  constructor
  · change p ((p.symm u).1,false ^^ sameMask p u (p.symm u).1)=u
    simp only [sameMask,ite_true,Bool.false_xor]
    exact p.apply_symm_apply u
  · change p ((p.symm u).1,true ^^ sameMask p u (p.symm u).1)=v
    simp only [sameMask,ite_true,Bool.true_xor,hb',he]
    exact p.apply_symm_apply v

theorem cross_selected_ports (p : (E × Bool) ≃ P) (u v : P)
    (he : (p.symm u).1≠(p.symm v).1) :
    ((flipSlots (crossMask p u v)).trans p) ((p.symm u).1,true)=u ∧
    ((flipSlots (crossMask p u v)).trans p) ((p.symm v).1,false)=v := by
  constructor
  · change p ((p.symm u).1,true ^^ crossMask p u v (p.symm u).1)=u
    simp only [crossMask,ite_true,Bool.true_xor,Bool.not_not]
    exact p.apply_symm_apply u
  · change p ((p.symm v).1,false ^^ crossMask p u v (p.symm v).1)=v
    simp only [crossMask,Ne.symm he,ite_false,ite_true,Bool.false_xor]
    exact p.apply_symm_apply v

variable {K : Type*} [Field K]

def orientedFactors (A : E → Binary (K := K)) (σ : E → Bool) : E → Binary (K := K) :=
  fun e => if σ e then (A e).transpose else A e

theorem orientedFactors_safe {G : Set (Binary (K := K))} (hrev : ReversalStable G)
    (A : E → Binary (K := K)) (σ : E → Bool) (hA : ∀ e, SafeBinary G (A e)) :
    ∀ e, SafeBinary G (orientedFactors A σ e) := by
  intro e
  unfold orientedFactors
  split
  · exact SafeBinary.transpose hrev (hA e)
  · exact hA e

/-- Every ordered pair of distinct original ports is covered. A closed cycle
may set the scalar to zero; no nonvanishing premise is imposed on the trace. -/
theorem contractPair_closed {G : Set (Binary (K := K))} (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := K)) ∈ G) (hrev : ReversalStable G)
    (u v : P) (huv : u≠v) (C : Binary (K := K)) (hC : SafeBinary G C)
    (F : Tensor K P) (hF : MatchingOrZero G F) : MatchingOrZero G (contractPair u v C F) := by
  rcases hF with rfl | ⟨M,hM,hκ,rfl⟩
  · exact Or.inl (contractPair_zero u v C)
  · let p := M.ports
    let A := M.matrix
    let e := (p.symm u).1
    let f := (p.symm v).1
    by_cases hef : e=f
    · let σ := sameMask p u
      let p' := (flipSlots σ).trans p
      let A' := orientedFactors A σ
      have hA' : ∀ d, SafeBinary G (A' d) := orientedFactors_safe hrev A σ hM
      have hp : productValue p' A' M.scalar=M.tensor := reorient_product p A M.scalar σ
      have ho := MatchingOrZero.of_product (deletePorts p' e) (fun d => A' d.val)
        (trace (A' e) C*M.scalar) (fun d => hA' d.val)
      rw [← contract_matched] at ho
      obtain ⟨hu,hv⟩ := same_selected_ports p u v huv hef
      change p' (e,false)=u at hu
      change p' (e,true)=v at hv
      rw [hu,hv,hp] at ho
      exact ho
    · let σ := crossMask p u v
      let p' := (flipSlots σ).trans p
      let A' := orientedFactors A σ
      have hA' : ∀ d, SafeBinary G (A' d) := orientedFactors_safe hrev A σ hM
      have hp : productValue p' A' M.scalar=M.tensor := reorient_product p A M.scalar σ
      have ho := MatchingOrZero.of_product (splicePorts p' e f) (spliceFactors C A' e f) M.scalar
        (spliceFactors_safe hG hX C A' e f hC hA')
      rw [← contract_cross p' A' M.scalar e f hef] at ho
      obtain ⟨hu,hv⟩ := cross_selected_ports p u v hef
      change p' (e,true)=u at hu
      change p' (f,false)=v at hv
      rw [hu,hv,hp] at ho
      exact ho

end
end Holant.Certificates.MatchingContractionClosure
