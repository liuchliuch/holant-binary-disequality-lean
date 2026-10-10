import Holant.Certificates.AffineEndpoint.WitnessChecker
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
open Holant.Certificates.OctahedralSeparator IntegerValues
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
 def CoefficientWitness (g : Fin 16 → Coeff) (h : Fin 612 → Fin 16 → Coeff) (w : ℕ) : Prop :=
  if hw : w<8 then g (oddCode ⟨w,hw⟩)≠zero else
  if w=8 then g 0=zero else
  if w=9 then g 15=zero else
  if w=10 then ∀i : Fin 6,g (centralCode i)=zero else
  let r : Fin 612 := ⟨(w-11)/6%612,Nat.mod_lt _ (by decide)⟩
  let p : Fin 6 := ⟨(w-11)%6,Nat.mod_lt _ (by decide)⟩
  let h := h r
  g (centralCode p)≠zero ∧ h (centralCode p)≠zero ∧
    (∀i : Fin 6,IntegerCoefficient.mul (g (centralCode i)) (h (centralCode p))=
      IntegerCoefficient.mul (g (centralCode p)) (h (centralCode i))) ∧
    IntegerCoefficient.mul (IntegerCoefficient.mul (g 15) (g 0))
        (IntegerCoefficient.mul (h (centralCode p)) (h (centralCode p)))=
      IntegerCoefficient.mul (IntegerCoefficient.mul (g (centralCode p)) (g (centralCode p))) (h 15)

 theorem coefficientWitness_sound (g : Fin 16 → Coeff) (h : Fin 612 → Fin 16 → Coeff)
    (hh : ∀r x,alg (h r x)=reference r (codeWord x)) (w : Nat)
    (hw : CoefficientWitness g h w)
    (hg : EndpointEven (fun x => alg (g (wordCode x)))) :
    EndpointNormalForm (fun x => alg (g (wordCode x))) := by
  let G : Signature AlgebraicComplex 4 := fun x => alg (g (wordCode x))
  have out (x : Fin 16) : alg (g x)=G (codeWord x) := by simp only [G,wordCode_codeWord]
  have out0 : alg (g 0)=G zeroWord := (out 0).trans (congrArg G zeroCode_word)
  have out1 : alg (g 15)=G oneWord := (out 15).trans (congrArg G oneCode_word)
  have outc (i : Fin 6) : alg (g (centralCode i))=G (centralWord i) :=
    (out _).trans (congrArg G (centralCode_word i))
  unfold CoefficientWitness at hw
  split_ifs at hw with hw8 h8 h9 h10
  · exact False.elim ((alg_ne_zero hw) ((out _).trans (hg.2.2 _ (oddCode_weight ⟨w,hw8⟩))))
  · exact False.elim (hg.1 (out0.symm.trans (by rw [hw,alg_zero])))
  · exact False.elim (hg.2.1 (out1.symm.trans (by rw [hw,alg_zero])))
  · apply endpoints_normal_form _ hg
    intro i
    exact (outc i).symm.trans (by rw [hw i,alg_zero])
  · let r : Fin 612 := ⟨(w-11)/6%612,Nat.mod_lt _ (by decide)⟩
    let p : Fin 6 := ⟨(w-11)%6,Nat.mod_lt _ (by decide)⟩
    change g (centralCode p)≠zero ∧ h r (centralCode p)≠zero ∧
      (∀i : Fin 6,IntegerCoefficient.mul (g (centralCode i)) (h r (centralCode p))=
        IntegerCoefficient.mul (g (centralCode p)) (h r (centralCode i))) ∧
      IntegerCoefficient.mul (IntegerCoefficient.mul (g 15) (g 0))
          (IntegerCoefficient.mul (h r (centralCode p)) (h r (centralCode p)))=
        IntegerCoefficient.mul (IntegerCoefficient.mul (g (centralCode p)) (g (centralCode p))) (h r 15) at hw
    obtain ⟨hgp,hhp,hcross,hend⟩ := hw
    have refc (i : Fin 6) : alg (h r (centralCode i))=reference r (centralWord i) :=
      (hh r _).trans (congrArg (reference r) (centralCode_word i))
    have ref1 : alg (h r 15)=reference r oneWord := (hh r _).trans (congrArg (reference r) oneCode_word)
    apply cross_products_normal_form G (reference r) hg (reference_endpoint_even r)
      (reference_affine r) (reference_origin r) (reference_support r) p
    · exact fun hz => alg_ne_zero hgp ((outc p).trans hz)
    · exact fun hz => alg_ne_zero hhp ((refc p).trans hz)
    · intro i
      have he := congrArg alg (hcross i)
      rw [alg_mul,alg_mul,outc i,refc p,outc p,refc i] at he
      exact he
    · have he := congrArg alg hend
      simp only [alg_mul] at he
      rw [out1,out0,refc p,outc p,ref1] at he
      simpa only [pow_two] using he
end
end Holant.Certificates.AffineEndpoint
