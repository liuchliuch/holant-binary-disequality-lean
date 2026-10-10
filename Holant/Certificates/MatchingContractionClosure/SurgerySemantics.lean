import Holant.Certificates.MatchingContractionClosure.PortSurgery

namespace Holant.Certificates.MatchingContractionClosure
open Holant
noncomputable section
variable {K P E : Type*} [Field K] [DecidableEq P] [Fintype E] [DecidableEq E]

/-- Closing a matched edge deletes its literal ports and multiplies the
global scalar by its trace. This includes a vanishing trace. -/
theorem contract_matched (p : (E × Bool) ≃ P) (A : E → Binary (K := K)) (κ : K)
    (e : E) (C : Binary (K := K)) :
    contractPair (p (e,false)) (p (e,true)) C (productValue p A κ)=
      productValue (deletePorts p e) (fun d => A d.val) (trace (A e) C*κ) := by
  funext x
  unfold contractPair
  rw [close_product_edge]
  let y := extendRemaining (p (e,false)) (p (e,true)) x
  have hp : (∏ d ∈ {e}ᶜ, A d (y (p (d,false))) (y (p (d,true))))=
      ∏ d : OtherEdges e, A d.val (x (deletePorts p e (d,false))) (x (deletePorts p e (d,true))) := by
    rw [Finset.prod_subtype (p := fun d : E => d≠e) {e}ᶜ (by intro d; simp)]
    apply Finset.prod_congr rfl
    intro d hd
    change A d.val (extendRemaining _ _ x (deletePorts p e (d,false)).val)
      (extendRemaining _ _ x (deletePorts p e (d,true)).val)=_
    rw [extendRemaining_apply,extendRemaining_apply]
  change trace (A e) C*(κ*∏ d ∈ {e}ᶜ, A d (y (p (d,false))) (y (p (d,true))))=_
  rw [hp]
  simp only [productValue,mul_assoc]

def spliceFactors (C : Binary (K := K)) (A : E → Binary (K := K)) (e f : E) :
    OtherEdges f → Binary (K := K) := fun d => if d.val=e then fuse C (A e) (A f) else A d.val

theorem splice_product (p : (E × Bool) ≃ P) (A : E → Binary (K := K)) (κ : K)
    (e f : E) (hef : e≠f) (C : Binary (K := K))
    (x : Remaining (p (e,true)) (p (f,false)) → Bool) :
    productValue (splicePorts p e f) (spliceFactors C A e f) κ x=
      fuse C (A e) (A f)
        (extendRemaining _ _ x (p (e,false))) (extendRemaining _ _ x (p (f,true))) *
      (κ*∏ d ∈ (Finset.univ.erase e).erase f,
        A d (extendRemaining _ _ x (p (d,false))) (extendRemaining _ _ x (p (d,true)))) := by
  let y := extendRemaining (p (e,true)) (p (f,false)) x
  let g : E → K := fun d => if d=e then fuse C (A e) (A f) (y (p (e,false))) (y (p (f,true)))
    else A d (y (p (d,false))) (y (p (d,true)))
  have hv (d : OtherEdges f) : spliceFactors C A e f d
      (x (splicePorts p e f (d,false))) (x (splicePorts p e f (d,true)))=g d.val := by
    rw [← extendRemaining_apply _ _ x (splicePorts p e f (d,false)),
      ← extendRemaining_apply _ _ x (splicePorts p e f (d,true))]
    rw [splicePorts_val,splicePorts_val]
    by_cases he : d.val=e <;> simp [spliceFactors,g,y,he]
  have hp : productValue (splicePorts p e f) (spliceFactors C A e f) κ x=
      κ*∏ d ∈ Finset.univ.erase f,g d := by
    simp only [productValue,hv]
    rw [Finset.prod_subtype (p := fun d : E => d≠f) (Finset.univ.erase f) (by intro d; simp)]
  rw [hp,← Finset.mul_prod_erase (Finset.univ.erase f) g (a := e) (by simp [hef])]
  have hp' : (∏ d ∈ (Finset.univ.erase f).erase e,g d)=
      ∏ d ∈ (Finset.univ.erase e).erase f,A d (y (p (d,false))) (y (p (d,true))) := by
    rw [Finset.erase_right_comm]
    apply Finset.prod_congr rfl
    intro d hd
    have he : d≠e := (Finset.mem_erase.mp (Finset.mem_erase.mp hd).2).1
    simp [g,he]
  rw [hp']
  simp only [g,ite_true]
  ring

/-- Cross-closing distinct original factors produces the actual fused matrix
on the two surviving original endpoints and leaves every other factor intact. -/
theorem contract_cross (p : (E × Bool) ≃ P) (A : E → Binary (K := K)) (κ : K)
    (e f : E) (hef : e≠f) (C : Binary (K := K)) :
    contractPair (p (e,true)) (p (f,false)) C (productValue p A κ)=
      productValue (splicePorts p e f) (spliceFactors C A e f) κ := by
  funext x
  unfold contractPair
  rw [close_product_two p A κ e f hef,splice_product p A κ e f hef]

theorem spliceFactors_safe {G : Set (Binary (K := K))} (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := K)) ∈ G) (C : Binary (K := K)) (A : E → Binary (K := K))
    (e f : E) (hC : SafeBinary G C) (hA : ∀ d, SafeBinary G (A d)) :
    ∀ d, SafeBinary G (spliceFactors C A e f d) := by
  intro d
  unfold spliceFactors
  split
  · exact SafeBinary.mul hG hX (SafeBinary.mul hG hX (hA e) hC) (hA f)
  · exact hA d.val

end
end Holant.Certificates.MatchingContractionClosure
